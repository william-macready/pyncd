# Reference-alignment prototype notes

## Scan group, dispatch 1 -- HISTORY (shapes 4 and 5); the "Final state" section at the end supersedes any status below

Status at the time: stopped at the turn budget (about 60 turns; the full `lake build` alone cost ~25 minutes of
wall clock and several turns of waiting). Commit 1 landed; shapes 6-10 were built by later dispatches.

### Environment trap (cost ~5 turns)
`lake` run from the worktree root (no `lean-toolchain`) resolves the elan DEFAULT toolchain (v4.34.1), not
the project's v4.30.0, and began rebuilding Batteries (and failed) -- overwriting ~109 Batteries oleans in the
worktree's `.lake`. Repaired with `rsync -a <primary>/leanncd/.lake/packages/batteries/ <worktree>/...` and a
rebuild (Aesop/Qq/ImportGraph/ProofWidgets/Plausible rebuilt; Mathlib itself was untouched). The working
invocation without `cd`: `lake +leanprover/lean4:v4.30.0 -d <worktree>/leanncd build <target>` (and
`... env lean <file>` for probes). `mutation-manifest.sh` is not executable: run it as `bash <script> --cd <leanncd> ...`.

### Commit 1: shapes 4 + 5 (`feat(leanncd): reference rejects base writes off the boundary and overlapping base writes`)
Location: `checkScanStructure @ LeanNCD/Eval/Scan.lean`, called from `evalScan` right before state allocation
("1. allocate each state tensor"), after the storage refusal, `noIterationAxis`, the unsized-axis check and the
`onlyAssignInSlice` check. Constructors in `LeanNCD/Eval/Error.lean` (flat, same names as the checked backend's
`ScanCompileError`), rendered by the sole `EvalError.render`.

| shape | constructor | payload | check |
|---|---|---|---|
| 4 | `baseWriteNotAtBoundary` | `(scan state : String) (baseIdx : Nat)` | `baseTouchesBoundary @ Scan.lean`: some scan-axis slot is `.iterAt _ 0`; a base that omits a scan axis from its LHS is skipped (checked `advancingAxisNotInLhs`, not in scope) |
| 5 | `baseWritesOverlap` | `(scan state : String) (firstBase secondBase : Nat)` | `baseDimsSeparate`/`baseDimOf @ Scan.lean`: dims separate iff both pinned with different literals, or both strided with equal positive scale and offsets differing mod scale; everything else (face vs pinned, face vs face, ...) never separates. Mirrors `writesCollide @ Plan/Scan.lean` (own code, not imported) |

Check order (documented in `checkScanStructure`'s doc comment, mirroring Compile.lean phases):
0. non-assign base (`baseMustBeAssign`, hoisted so it keeps precedence over the new checks);
1. `baseWriteNotAtBoundary` in `base` order; 2. `baseWritesOverlap`, states in first-base order, first pair `a<b`.
Future shapes slot in Compile.lean's order: duplicate state/scratch (6, 7) first, then per-state row/extent (9, 8),
then stateReadInBaseBlock (10), then 4, 5. NOTE: that is NOT yet how the function is ordered; when 6-10 are added,
put them BEFORE shapes 4/5 and update the doc comment.

Observed values (real runs):
- shape 4 lag-2 `h[l+1]:=h[l]+h[l-1]`, bases h0=1 @0 and h1=5 @1, L=4: REJECT `baseWriteNotAtBoundary "h" "h" 1`
  (old reference silently dropped the seed). ACCEPT with only the @0 base: `[1,1,2,3]`.
  2-D accept, single base `G[0,1]:=Y[0]` (r pinned 0, c pinned 1: touches boundary through r), 3x3:
  `[0,10,0, 0,0,10, 0,0,0]`.
- shape 5 2-D 3x3, `face0 = G[r,0]:=Z[r]` (Z=[1,2,3]), `row0 = G[0,c]:=Y[c]` (Y=[10,20,30]):
  corner overlap REJECT `baseWritesOverlap "G" "G" 0 1`; exact duplicate (face0,face0) REJECT same payload;
  ACCEPT disjoint face + point (`G[0,1]:=Y[0]`): `[1,10,0, 2,1,10, 3,2,1]`. The corner carries Z[0]=1 vs Y[0]=10, so
  last-wins and first-wins differ; refusal pins neither.
- Existing ScanTest strided pair `S[2*j,0]` / `S[2*j+1,0]` still ACCEPTED (residue rule).

Entry points covered: every scan reaches `evalScan` through `evalScheduled` (the only caller, Eval.lean ~l.142), so
all programs are covered at that one location. NOT covered: `evalStmtSliceSeeded` / `writeScanStmtSlice` called
directly (they see one statement, cannot see siblings); `Plan/` checked backend unchanged. I did not separately
probe `evalScheduled` end-to-end (only `evalScan` fixtures); the call graph shows it is a pass-through.

Deliberately flipped test: `test/Eval/ScanTest.lean` "Collision mutation" (dp, base `ROWFACE` face + colliding
point): BEFORE accepted with last-write-wins, `dp = [1,1,0,2]`; AFTER rejects `baseWritesOverlap "dp" "dp" 0 1`.
No other test changed: the full `lake build` (8673 jobs) is green, including PropertyOracle and Portfolio suites,
so no oracle generator produces a shape-4/5 fault.

Files touched: `LeanNCD/Eval/Error.lean`, `LeanNCD/Eval/Scan.lean`, `test/Eval/ScanTest.lean`
(+ `papers/ref_align_mutations.json`, this file, `papers/ref_align_patches/scan_group/`, untracked).
Fixtures added: 4 reject-or-accept `run_cmd` blocks (shape 4 lag-2 reject+accept, shape 4 2-D accept, shape 5
corner+duplicate reject + disjoint accept) = 7 assertions in 3 blocks, plus the flipped collision fixture.
Donors named in the fixture comments (shape 4: "COUPLED scan" fixture cloned to lag 2; 2-D fixtures have no donor).
Mutation cycles: 4 (RA-S4a, RA-S4b, RA-S5a, RA-S5b), all PASS (`mutation-manifest.sh --check` OK; all 4 run,
expect strings observed). RA-S4b needed its `expect` corrected after observation (the first assertion in the block
fails before the accept assertion is reached).

### Final state (all 11 shapes and the shape 2 fix landed)

- Shapes 4-10: `checkScanStructure` and its helpers in `LeanNCD/Eval/Scan.lean` (check order documented in its doc
  comment and pinned by the CHECK ORDER fixture block). Shapes 3/11: `checkNormMarkers` (`Eval/Nonlin.lean`; covers scatter
  arms and the scan-local scatter arm, not only `resolveNonlin`). Shape 1: `checkScatterFill` (`Eval/Eval.lean`; deliberately
  not in `evalScatter` or the scan-local arm). Shape 2: `evalScatter` takes `decls` and uses `combineFor`
  (`isPredicateDest` in `Eval/Contract.lean`); its `.sum` collision policy folds with Boolean OR on a predicate destination.
- All new fixtures are at the end of `test/Eval/ScanTest.lean`, including the marker and scatter ones. Mutation results for
  shapes 9 onward are in the commit message bodies; `papers/ref_align_mutations.json` has entries for shapes 4-8 only.
- Deviations from the checked path, accepted: shape 9's payload omits the checked coefficients/bias; shape 1 rejects EVERY
  top-level max/min scatter (including a `+`-joined two-term max), mirroring the checked rule.
- STILL ACCEPTED by the reference and refused by the checked path, deliberately untouched by this slice:
  (a) a scan-local scatter into a predicate-typed state (checked: `predicateScatterDest`; the reference is already
  dtype-aware there) — documented as a checked-path refusal; (b) a sum scatter with a non-zero fill (checked:
  `scatterOptsNotAdmitted`); (c) `S[j,l+1] := S[j,2*l]` (checked: `stateReadNotCausal`; reference returns `[1,1,0]`),
  deferred as a twelfth shape.
- The checked `predicateScatterDest` rejection is KEPT. Removing it needs: dropping the throw in `capabilityPreflight`
  and the constructor, flipping the three predicate-scatter fixtures in `CompileTest.lean` and the name arm in
  `DifferentialTest.lean`, and verifying the checked scatter runner's Boolean algebra and collision policies against
  the now-dtype-aware reference.
