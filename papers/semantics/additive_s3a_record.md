# S3a record: scatter collisions are summed (landed 2026-10-22)

Process weight: **Direct** (slice-plan §0): no plan document, no patches, no new manifest entries. The oracle (S2a/S2b)
already sums colliding scatter writes and errors on out-of-range writes, so it could see both behaviour changes. Branch
`worktree-s3a-scatter-additive`, base `823e2ddc`. Merge hash: see the final line.

## 1. What changed

- **Behaviour.** A top-level scatter now folds colliding writes with the destination's ⊕ (real `+`, predicate `Max`;
  empty fibre = 0_K = 0) in the reference `evalScatter` and the checked plan `runDenseScatterWith`
  (`algebra.reduceOp` from `reduceId`; f32 rides the same worker). Before, the default `rejectCollisions` raised an error.
- **Deleted API.** `CollisionReduce`, `ScatterOpts`, the 4th `Stmt.scatter` argument, `ScatterPlan.fill`/`reduce`,
  `PlanError.scatterReduceNotAdmitted`/`scatterFillNotIdentity` (plan-level), `checkScatterReduce`, `checkScanScatterOpts`,
  `StructuralCondition.scatterCollisionRejected` and its detection machinery in the differential.
- **Kept refusal (M2).** A top-level scatter whose RHS agg is not `.sum` (`maxreduce`/`minreduce`) is still refused, by one
  guard per backend (`checkScatterAgg`, `scatterAggOrFail`) reusing `EvalError.scatterFillNotIdentity` and
  `CapabilityError.scatterOptsNotAdmitted "{nm}: fill"`, because `SortedDifferential.confirmsSorted` matches those. Reason:
  accepting max/min scatter now would change tropical values twice, since S3b later changes ⊗ from × to +.
- **Oracle.** `admitAffineStatement` no longer reads options; the sorted-tropical refusal (`.unsupported .scatterPolicy`) stays.
- **Const-slot guard.** `lowerArith`'s `.scatter`-arm guard was deleted (T3c; a hand-built const-slot `.scatter` compiles and
  sums). The `.assign`-arm `overlappingScatter` guard stays (surface-only path, surface syntax cannot produce a const slot).

Commits (oldest first): `baf401d1` ref ⊕; `9e94e7da` checked ⊕; `49cd3562` agg guard; `261f105a`, `2f8464fd`, `5d694c00` oracle
cleanup; `f6d300fe` delete the types; `2a18947f`, `f6541b60` tests (Semantics, DSL/Eval); `27ffb960`, `dd16d6ac` const-guard fix;
`6131d3c3`, `bf3dc7c2`, `27fd0079` tests (Plan, Scan, Gen); docs commits.

## 2. Verification

Controller full `Tests` build on the branch before the final comment edits: 8823 jobs, no errors. Implementer mutation checks
(reported in the commit bodies): fold operator, initial value, bool fold, `reduceOp`, guards on and off, restored `.scatter`-arm
guard (fails exactly the four `fD'`/`fOriginC` guards). Whole-branch review (Opus, one lens: what option deletion silently
changed): APPROVE WITH FINDINGS, no Critical/Major (`s3a_review_final.md` summary below). No new mutation manifest was added
(Direct path).

## 3. Findings and their disposition

- **Found by a test, not the plan:** T3a turned a const-slot `.scatter` with `reduce := .sum` from compiling into
  `overlappingScatter` (the guard had read `opts.reduce`; deleting the field made it unconditional). My T3a brief said "keep the
  guard, parked"; that was wrong once the options vanished. Fixed in T3c. Lesson: when deleting a field, list every READ of it
  and decide each one, not only the writes.
- **F3 (parked):** the scan-local reference write (`writeScanStmtSlice`) still overwrites on a collision, so "collisions are
  summed" holds for top-level scatters only. Not traced whether `checkScanStructure` lets a colliding row through. Cost: 1 dispatch audit.
- **F4 (documented):** a direct `evalScatter` of a tropical scatter with a contracted source axis sums from 0 while the raw
  checked plan maxes from ∓∞. Unreachable through `compile`/`evalPlain`; S3b's territory. Doc added in `Dense.lean`.
- **F1, F7a (fixed, comments only):** stale docs on `PositionalInputError.scatterCollision` and `CompileError.overlappingScatter`.
- **Parked, tiny:** F5 no fixture pins the checked `.min` refusal (only `.max`); F6 no fixture with non-integer collision values
  (summation-order change would stay green); F7b the `scatterFillNotIdentity` render text still says "fills unwritten cells with
  a finite value" (rewording touches `confirmsSorted` matching); `EvalError.scatterCollision` and both other `scatterCollision`
  constructors have no producer (kept).

## 4. Parked by scope (CLAUDE.md Rule 14)

| Item | Cost |
| --- | --- |
| B6 out-of-range write error (reference + checked static corner check; surface-visible only for `0*x` slots) | ~8 fixtures, 5 cycles, own Direct slice |
| B5 multi-writer scatter (needs declared shape, collector with affine writers; flips 4 fixtures and `StructuralCondition.multiWriterScatter`) | Full path |
| Honouring the declared scatter shape in the checked plan | only B5 needs it |
| Delete the `.assign`-arm const guard | ~1 dispatch, low value |
| Rename `UnsupportedSource.scatterPolicy` (now means "sorted tropical scatter") | ~1 dispatch |
| Tropical sorts, casts, constants, multi-factor max-plus in production | S3b |
| **Landed manifests no longer run clean on this tree:** `papers/additive_s2a_mutations_post.json` has 5 entries whose `old` string is gone (T2-M3, T2-M4, P3b-M1, A1-M1, A1-M2) and about 22 entries with line-number `expect` strings against shifted test files; `papers/additive_s2b_mutations_post.json` T2-M2 `old` is gone from `Admission.lean`. Left as records, not edited. | rewrite if anyone re-runs them |

## 5. Cost and process notes

Measured with `token-report.py` on the session after the review (65.2M at that point; final figure on the close line below). Dispatch
turns vs the ~60 cap: audit 61, T1 81, T2 61, T3a 75, T3b-1 58 (+T3c), T3b-2 102. Rule 6 breaches for T1, T3a, T3b-2: mostly
waiting on builds and large mechanical arity edits; the split T3b-1/T3b-2 helped but T3b-2 (~14 files plus Gen/DifferentialTest
found by the full build) was still too big. The scatter audit (8.4M) shrank S3a from the decision note's ~150-175M outline to a
Direct slice: JAX has no scatter kernel, f32 shares the dense worker, the oracle already sums.
