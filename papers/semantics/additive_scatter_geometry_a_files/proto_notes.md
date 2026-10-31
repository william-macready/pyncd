# Scatter-geometry slice A: prototype notes (dispatch 1 of 2)

Ledger for the plan author. Branch `proto-scatter-geometry-a` on local main `efb5d319`. Commands use
`<wt>` for the worktree root and `<lncd>` for `<wt>/leanncd`. Single files:
`bash <lncd>/scripts/lean-file.sh <lncd> <path>`; builds: `bash <lncd>/scripts/lake-build.sh <lncd> LeanNCD Tests`.

## T1 — the M1 extent rule (commit d972d01f)

### What changed (identifiers @ file)
* `affineImageBounds (c0 : Int) (terms : List (Int × Nat)) : Int × Int` @ `DSL/Ast.lean`: the ONE corner
  formula (`min = c0 + Σ min 0 (c·(n-1))`, `max = c0 + Σ max 0 (c·(n-1))`), placed directly above
  `LHSSlot.outExtent` (Ast is upstream of Eval/Plan, so Check can reach it).
* `LHSSlot.outExtent` @ `DSL/Ast.lean`: new arm `| _ :: _ :: _ =>` after the single-axis stride arm:
  two or more distinct nonzero-coefficient axes give `((affineImageBounds c0 terms).2 + 1).toNat`
  where `terms` pairs each densified coefficient with its size; if any named axis has size 0 it keeps
  `legacy`. Single-axis stride-aligned arm, the `| _ => some legacy` fall-through (zero or no nonzero
  coefficient), the `.const` arm and the `none`-if-unsized rule are byte-for-byte unchanged.
* `scatterImageBounds` @ `Eval/Plan/Check.lean` is now `affineImageBounds bias (row.toList.zip srcShape.toList)`
  (its body was the corner fold; semantics identical, so B6 range checking is untouched).
* `derivedShape` @ `Semantics/Source/Differential.lean` (the oracle's STRUCTURAL-CONDITION PREDICTOR of
  production's derived extent) now calls `LHSSlot.outExtent` instead of restating `c0 + Σ c·n`.
  **This was not in the task brief and is the T1 surprise**: that predictor was a second extent
  formula. Under M1 alone every guard in the build stayed green (`conditionCount fF == 1` still passed,
  predicting 7 for `a+b` while production derives 6), so the stale copy is invisible until T2 lifts the
  checked refusal and `fF` becomes a four-leg candidate. Reusing `outExtent` removes the copy (it also
  fixes a latent `2a+3` divergence: stride-aligned 10 vs the predictor's 11, no fixture covered it).
  The constant arm (`f.2.isEmpty`, `c+1`) is kept.
* `lakefile.toml`: `Eval.Plan.ScatterGeometryTest` added to the `Tests` globs (new test file below).

### Guards re-pinned (each keeps its original intent)
* `ScatterCheckTest`: `(affine 1 [(2,I),(1,J)]).outExtent == some 11` -> `some 9` (reach `1+2*2+1*3 = 8`);
  `scatterDestExtent #[3,2] #[2,-1] 1 == some 5` -> `some 6`; the MAX-corner off-by-one
  `errOf (boxCheck #[2,-1] 1) == some (.scatterWriteOutOfRange 0 0 5 5)` -> `isOk (boxCheck #[2,-1] 1)`
  PLUS direct `scatterRangeViolation #[3,2] #[#[2,-1]] #[1] #[5] == some (0,0,5,5)` / `#[6] == none` and a
  min-corner `#[0] #[6] == some (0,-1,4,6)`. **Why direct**: `checkScatter`'s extent clause runs first and
  forces `destShape` to the derived value, and under M1 a 2-axis row's derived extent is always `max+1`,
  so the max-corner off-by-one can no longer be built through `checkScatter` at all (only single-axis
  degenerate rows still reach the range clause: `Out[-i]`, `Out[0*i+5]`, which stay pinned). The shared
  rule `scatterRangeViolation` takes an explicit `destShape`, so the corner test survives there.
  A comment on `isOk (boxCheck #[1,1] 0)` was updated (`i+j` extent 5 -> 4).
* `SourceDifferentialScatterTest`: donors `fD` (`snap 7` -> `snap 6`, cells `[1,12,123,234,340,400]`,
  no trailing 0) and `fN` (`snap 16` -> `snap 12`, the 4 trailing zeros removed); `conditionCount fF`
  1 -> 0 with new twin `fFbig` (`snap 7`, declared too big, keeps `== 1`).

**WRINKLE recorded (M1 widens acceptance):** a mixed-sign row with non-negative minimum, e.g.
`2a - b + 1` over `[3,2]` (image [0,5]) or `a - b + 2` over (4,3), had a legacy extent at or below its
reach (5, 3) and was a B6 error; under M1 the extent is the reach (6, 6) and the row is IN range. Hand-built
programs only (checked backend refuses at T1; the surface cannot spell a negative coefficient).

### Fixtures added
* `ScatterCheckTest` (extent table; direct `outExtent`, sizes `i:3 j:4 k:2`; observed with
  `lean-file.sh test/Eval/Plan/ScatterCheckTest.lean`, all guards pass): `i+j` 6; `i+j+3` 9; `4i+j` 12;
  `i+j+k` 7; `i+j+i` 8 (densified `2i+j`); `2i-j+3` 8 (legacy 5); `i-j` 3 (negative minimum, legacy 0);
  `-i-j` 1 (legacy 0); zero-size `i`: `i+j` 4 and `-i+j` 4 (legacy kept; the second kills a missing guard,
  since a corner of an empty box would add a spurious `+1`); unsized -> `none`; CONTROLS unchanged:
  `2i` 6, `2i+3` 8, `0i+j` 4, `3+0i+0j` 3, `.const 3` 4; and `scatterImageBounds #[3,4] #[1,1] 0 == (0,5)`,
  `scatterDestExtent #[3,4] #[1,1] 0 == 6`, `#[4,1] == 12` (one corner formula).
  Donors: `clone` the existing `extentI/extentJ` + guard block (`ScatterCheckTest` "Direct outExtent
  contract"), change the row; `extentK`, `tripleSizes`, `emptyAxisSizes`, `multiExtent` are new helpers.
* `test/Eval/Plan/ScatterGeometryTest.lean` (NEW file, imports `Eval.Plan.B5cSingleBoxTest` for the B5
  harness `scheduled/ref64/prep64/as64`): hand-built `conv` (`S[a+b] := A[a]*B[b]`, `|a|=4,|b|=3`, `k`
  unpinned) and `convWide` (`a+4b`). Donor: `clone B5BoundaryTest.twoAxes, drop the second writer and the
  pinned k, change the slot`. Guards: reference shape `[6]` / `[12]`, values `[1,12,123,234,340,400]`, and
  the checked leg STILL refuses with `.capability (.multiAxisScatterLhs "S: affine LHS slot")`.
* `SourceDifferentialScatterTest`: `legacyShape`/`oracleShape` helpers; `legacyShape fD == [6]`,
  `oracleShape fD == [6]`, same for `fN` with `[12]`; `mentions fD/fN "multiAxisScatterLhs ..."`.
  Donors: `clone legacyCells/oracleCells, change the projection to .shape`.

### Full build
`bash <lncd>/scripts/lake-build.sh <lncd> LeanNCD Tests` -> `Build completed successfully (8841 jobs)`.
(The final `ScatterCheckTest` guard `-i+j` on an empty axis was added after that run and re-checked with
`lean-file.sh`; the mutation cycles below rebuild it.)

### Mutation cycles, T1 (run after the T1 commit; `--task T1`)
`mutation-manifest.sh --check` unfiltered: `manifest OK: 9 entries` (later 16 with T2). Run:
`mutation-manifest.sh --task T1 --out <scratch>/t1-mut.md <lncd> papers/semantics/additive_scatter_geometry_a_mutations_post.json`
-> **9/9 killed, 0 survived.** Expect strings are the file prefix `error: test/Eval/Plan/ScatterCheckTest.lean:`
(a `#guard` failure prints `error: <file>:<line>:0: Expression ... did not evaluate to true`); T1-09 uses
`error: test/Semantics/SourceDifferentialScatterTest.lean:`. First cycle's observed failing lines (SGA-T1-01):
`ScatterCheckTest.lean:164, 197, 199, 201, 203, 205, 208, 211, 213, 233`.

| label | mutation | result |
|---|---|---|
| SGA-T1-01 | multi-axis arm returns `legacy` | killed |
| SGA-T1-02 | drop the `+ 1` | killed |
| SGA-T1-03 | use the MIN corner `.1` | killed |
| SGA-T1-04 | drop the zero-size-axis arm | killed (only by the `-i+j` empty-axis guard: the `i+j` empty-axis fixture alone would NOT kill it, because `max 0 (c*(0-1))` hides the spurious corner for a positive coefficient; that is why the negative-coefficient twin exists) |
| SGA-T1-05 | corner start `(0,0)` instead of `(c0,c0)` | killed |
| SGA-T1-06 | drop `max 0` on the positive corner | killed |
| SGA-T1-07 | drop `min 0` on the negative corner | killed |
| SGA-T1-08 | stride arm replaced by reach + 1 (control must hold) | killed |
| SGA-T1-09 | oracle predictor back to the sum formula | killed (`SourceDifferentialScatterTest`: `conditionCount fF`) |

(T1-04's note was reasoned from the arithmetic, not from a second observed run; the cycle itself is observed.)

### Things T1 surfaced for the plan author
* The oracle predictor `derivedShape` is a SECOND extent formula in a different directory
  (`Semantics/Source/Differential.lean`); no build guard failed when `outExtent` changed. The plan must
  keep the T1 edit to it and its `fF`/`fFbig` condition pair.
* Docs that may now describe the old rule (NOT audited line by line; left alone, T4 is docs, Rule 14):
  the doc comments on `scatterDestExtent`/`scatterPlacementSlot` in `Eval/Plan/Check.lean` ("legacy
  fallbacks"); `Eval/Plan/Error.lean` `multiAxisScatterLhs` doc (why the form is refused: after T2 only
  scan-local); the `Eval/Plan/AGENTS.md`, `Semantics/AGENTS.md`, `DSL/AGENTS.md` lines about the extent rule
  and the two refusals. A grep of `outExtent` in `test/` found only single-axis or zero-coefficient prose
  (`ScatterDenseTest`, `GraphDenseTest`), which M1 does not change.

## T2 — multi-axis admission at top level (the second commit on the branch; sha in `git log`, it carries this file)

### What changed (identifiers @ file)
* `checkScatterAffineExpr` @ `Eval/Plan/Compile.lean` (private) gained a first parameter
  `multiAxisAdmitted : Bool`; `.constant` still throws `scatterOrAffineLhs`, `.multiAxis` throws
  `multiAxisScatterLhs` only when the flag is false. `checkScatterLHSSlot` (top level) passes `true`;
  `checkScanScatterLHSSlot` passes `false` and so keeps BOTH refusals. Doc comments on the function,
  on `checkScatterLHSSlot`'s section and on `checkScanScatterLHSSlot` were updated to say so (the
  `.affine`-arm doc said "rejects exactly two shapes"; it is now one at top level). Nothing else in
  production changed: no `lowerArith`, `Collect`, kernel or plan edit was needed (consistent with P0).
* Tests: `CompileTest` (multi-axis preflight pin flipped to `isOk`; predicate-decl donor "fixture 11"
  re-donored from the two-axis slot to a constant-slot scatter `Out[3]`, expecting
  `scatterOrAffineLhs "Out: constant affine LHS slot"`; the standalone constant pin and the three
  scan-local pins at `scanScatterSched` were untouched and pass); `SourceDifferentialScatterTest`
  (below); `ScatterGeometryTest` (below).

### Observed values (all from real runs; command in brackets)
Differential classification `tag` (`#eval` in `lean-file.sh test/Semantics/SourceDifferentialScatterTest.lean`):
`fD` (scatter `a+b`, `|k|=6`) parity; `fF` (assign `a+b`, 6) parity; `fF'` (`a+4b`, 12) parity; `fN`
(scatter `a+4b`, 12) parity; `fD'` (constant slot) still `nativeFailure`; `fOriginC` still
`scatterOrAffineLhs "Z: constant affine LHS slot"` + `nativeFailure` (the existing pins pass unchanged).
No `known:extent` fires for the declared==derived fixtures: reason, the predictor now calls `outExtent`.
`fFbig` (declared 7, reach 6) is `known:extent`: both native legs publish `[6]` against the oracle `[7]`
(`scatterExtentOverridesDeclared ... 5 [6]`), by design (B5c D2 residual: production does not box a
multi-axis single writer; `declaredShapeWins` excludes it). `fSign` (`a-b`, `|k|=4`):
`refused:writeOutOfRange` (the oracle refuses first; admission cause `writeOutOfRange`). `fSignOk`
(`a-b+2`, 6): parity, cells `[100,210,321,432,43,4]` in oracle, legacy and checked.
`observe fF` checked cells `[1,12,123,234,340,400]` (shape `[6]`); `observe fF'` checked
`[1,2,3,4,10,20,30,40,100,200,300,400]` (shape `[12]`).

`ScatterGeometryTest` (`lean-file.sh test/Eval/Plan/ScatterGeometryTest.lean`, inputs `A=[1,2,3,4]`,
`B=[1,10,100]`, `S` over unpinned `k`):
* plan fields: `conv` (`S[a+b]`) -> `(outCoeffs, outBias, destShape, compute.outputShape) =
  (#[#[1,1]], #[0], #[6], #[4,3])`; `convWide` (`a+4b`) -> `(#[#[1,4]], #[0], #[12], #[4,3])`.
* `agree` (reference == checked f64 == checked f32 bit for bit): conv `[1,12,123,234,340,400]`; wide
  `[1,2,3,4,10,20,30,40,100,200,300,400]`; cross-correlation `a-b+2` `[100,210,321,432,43,4]`; max-plus
  conv (`agg max`) `[2,11,101,102,103,104]`.
* B6, mixed-sign `a-b` (reach -2..3, extent 4): reference `evalScheduled` error
  `scatterWriteOutOfRange "S" [-1] [0,1]`; checked `.shape (.scatterImageOutOfRange "S" 0 (-2) 3 4)`.
* f32: native scatter bits `#[1022739088, 1046562735, 1047233823, 1061830000, 1050253722, 1059145646]`
  on `A=[0.1,0.7,0.3,0.9]`, `B=[0.3,0.1,0.7]`, equal to the independent binary32 twin (assignment
  `T[a,b]` plus anti-diagonal sums in source order, `+0` seeds); the narrowed binary64 answer is
  `#[...087, ...734, 1047233823, ...001, 1050253722, 1059145646]` (differs in lanes 0, 1, 3), pinned
  as a carrier discriminator. These bits were read from `#eval nativeBits/twinBits/narrowedBits`, not
  derived by narrowing.
* constant slot still refused: `prepCause (convOf (.affine (.const 3))) ==
  some (.capability (.scatterOrAffineLhs "S: constant affine LHS slot"))`.
* multi-writer with a multi-axis writer: `sourceError convTwo == some (.multiWriterScatter "S")` (donor:
  `B5BoundaryTest.twoAxes`).
* boxed single multi-axis writer (`k` pinned 8) keeps the derived shape in all three legs
  `(some [6], some [6], some [6])`, and `B5cSingleBoxTest.groupsOf convBoxed == []`.
* `routeError conv == none`.
Donors, one per fixture: `convOf` clone B5BoundaryTest.twoAxes, drop writer 2, unpin `k`; `convWide` clone
`conv`, change the `b` coefficient to 4; `crossSlot` clone `sumSlot`, change bias to 2 and `b` coefficient
to -1; `convMax` clone `conv`, change `agg` to `.max`; `convTwo` clone `conv`, duplicate the statement and
pin `k = 6`; `convBoxed` clone `conv`, pin `k = 8`; `twin` clone `conv`, replace the scatter by a free-slot
assign into `T[a,b]`; `fSign`/`fSignOk`/`fFbig` clone `fF`, change the slot / `|k|`.
Not added (cost noted): a max-plus convolution in the FOUR-LEG differential: `agg .max` on a plain
`typedTensor .f64` snapshot is refused by oracle admission (`UnsupportedSource.nonSum`); it needs the
declared-sort machinery of `OracleSortRulesTest`/`SortedDifferential` (about one dispatch). The three-leg
`convMax` pin above covers the checked and reference legs.

### Full build
After the T2 commit and after the last mutation restore: `lake-build.sh <lncd> LeanNCD Tests` ->
`Build completed successfully (8841 jobs)`. Failing modules BEFORE the test edits (the full Tests build
after the production change): `Semantics.SourceDifferentialScatterTest` (7 guards) and the new
`Eval.Plan.ScatterGeometryTest` (the two T1 refusal pins); `Eval.Plan.CompileTest` was edited in
advance and passed. Nothing else in `Tests` moved (scan, route, B5, JAX experimental untouched).

### Mutation cycles, T2 (`--task T2`; run after the T2 commit): **7/7 killed**
| label | mutation | killed by (observed first failing module / lines) |
|---|---|---|
| SGA-T2-01 | top level refuses multi-axis again (`true` -> `false`) | `CompileTest` 100 AND `ScatterGeometryTest` 79-101 (my pins kill it alone) |
| SGA-T2-02 | scan-local admits multi-axis (`false` -> `true`) | `CompileTest` 192, 199 (existing scan pins) |
| SGA-T2-03 | constant slot admitted by the preflight | `CompileTest` 120, 188, 338 AND `ScatterGeometryTest` 118 |
| SGA-T2-04 | multi-writer group admits multi-axis (`boundedScatter` dropped in `checkWriterGroup`) | `B5BoundaryTest` 78, 79 (existing); my `convTwo` pin was NOT reached (see below) |
| SGA-T2-05 | boxed single writer collects multi-axis (`boundedScatter` dropped in `boxedSingleGroups`) | `B5cSingleBoxTest` 138 (existing); my `convBoxed` pins NOT reached |
| SGA-T2-06 | `scatterImageBounds` zips the REVERSED row | `B5NativeTest` 247 (existing); `ScatterGeometryTest` not reached |
| SGA-T2-07 | `declaredShapeWins` boxes multi-axis (`<= 1` -> `<= 2`) | `SourceDifferentialScatterTest` 171, 344 (the `fFbig` pair and `fF` conditions) |

**Caveat the plan author must read:** for 04, 05 and 06 an EARLIER test module that
`ScatterGeometryTest` imports (`B5cSingleBoxTest` -> `B5bBoxTest` -> `B5NativeTest`) fails first, so Lake
never builds `ScatterGeometryTest` and the manifest `expect` strings had to name the existing module
(first run of 04/05/06 with `expect` on `ScatterGeometryTest` FAILED for exactly that reason, then the
entries were corrected to the observed module and re-run). All three ARE killed, by pins that predate this
slice; I did NOT demonstrate that my own `convTwo`, `convBoxed` and f32 pins would also kill them. If the
plan wants that, `ScatterGeometryTest` should import `Eval.Plan.B5NativeTest` only (it uses
`B5cSingleBoxTest.groupsOf` once; inline `boxedSingleGroups s.env (declaredAxisSizes s.decls) s.stmts`
instead), which removes the dependency on the B5b/B5c modules but not on `B5NativeTest` (its harness
lives there with top-level guards).

### CASE x CLASS table (deliverable)
Predicates: SAC = `scatterAffineClass` (Ast); BS = `LHSSlot.boundedScatter` (Ast); CSAE =
`checkScatterAffineExpr`; CSLS = `checkScatterLHSSlot` (top level); CSSLS = `checkScanScatterLHSSlot`;
SBS = `slotsBecomeScatter` (Ast); COL = `LHSSlot.collapses` (Structural, `.assign` arm of `lowerArith`
only); ORA = oracle admission (`Admission.admitAffineOutput`) plus predictor (`derivedShape`,
`declaredShapeWins` in `Differential.lean`). Cell = what the code does today, then status:
REQ (required and pinned), FORB (forbidden and pinned), **SIL** (silently ignored: a predicate that
does not look at this cell, or looks and does nothing, with no pin or no diagnostic).

| slot class | top-level single (unboxed) | multi-writer group | boxed single (pinned decl) | scan-local |
|---|---|---|---|---|
| single-axis strided (`2*i`, `i+2`) | scatter, stride-aligned extent: REQ (many pins) | admitted by BS: REQ (B5 tests) | collected unless D5: REQ (B5c) | admitted by CSSLS: REQ (ScanCompileTest) |
| multi-axis (`a+b`) | admitted by CSLS since T2, M1 extent: REQ (this slice) | refused `multiWriterScatter` (BS false): FORB (B5BoundaryTest.twoAxes, convTwo) | NOT collected (BS false): derived shape wins, pinned `convBoxed`, B5c `multiAxisOne`; **SIL**: the pinned declaration is ignored with no diagnostic (oracle shows `known:extent`) | refused `multiAxisScatterLhs` by CSSLS: FORB for checked (ScanCompileTest 1247/2107/2178, CompileTest); **SIL**: the reference/legacy evaluators accept it and overwrite (F3), no guard there |
| constant (hand-built `.affine (.const n)`) | `.assign` arm: COL -> `overlappingScatter`: **SIL-stale** (a guard predating S3a, ORA and the reference define the write); `.scatter` arm: no lowerArith guard, CSLS refuses `scatterOrAffineLhs`: FORB checked (pinned), legacy/reference accept; surface `S[3]` is `.iterAt`, a scan base case, never a constant | refused `multiWriterScatter` (BS false): FORB (B5BoundaryTest.explicitConstant) | NOT collected, derived shape (n+1) wins; **SIL** as multi-axis (not pinned for a constant; slice B's fixture) | refused `scatterOrAffineLhs` by CSSLS: FORB (ScanCompileTest 843, 853, CompileTest 188) |
| zero-coefficient (`0*i`, `0*i+5`) | SAC `bounded`, accepted everywhere, every write out of range: B6 error in both backends: REQ (ScatterCompileTest S9/S9b/S9c) | BS true: REQ (B5NativeTest `zeroScale`, `emptySource`) | BS true, collected: not separately pinned; **SIL** (candidate: unpinned corner) | CSSLS admits (class bounded): REQ (ScanCompileTest `s6ZeroBase`) |
| diagonal (`Y[i,i]`) | SBS -> scatter, no `.affine` slot so SAC/CSAE/COL are never consulted: REQ (B5NativeTest `diagonal`) | `.scatter` after lowerArith, BS true (`.free`): REQ (`diagonal` two writers); a hand-built `.assign` diagonal would hit SBS -> `multiWriterScatter` | D5 excludes the repeated free slot: pinned `identityOne`/`transposeOne` | **SIL**: no pin found for a diagonal scatter inside a scan (`rg` of ScanCompileTest/ScanContractTest); CSSLS admits `.free`, nothing checks repetition |
| free (`Y[i]`) | plain assign, no class consulted: REQ | `.assign` bare groups (legacy positional agreement): REQ | collected as a one-writer group (`us.length == ls.length`): REQ | plain: REQ |

Predicate-by-predicate blind spots (one line each): SAC is never consulted for `.free`/diagonal slots
(by design, they have no `IdxExpr`); BS treats `.iterAt`/`.iterNext` as unbounded (`| _ => false`)
though CSSLS admits them (consistent only because scans never reach groups); COL guards only
`.assign` and only a literal `.const`, so a zero-coefficient or any multi-axis `.assign` slot passes (by
design) and a hand-built constant `.scatter` is unguarded (S3a); ORA admits every form in every
context (no class gating) and relies on production's native failure for group, scan and constant
refusals, so its `known:extent` prediction is the ONLY report of the boxed-single-multi-axis residual;
`declaredShapeWins` is a hand-copied mirror of `boxedSingleGroups`' exclusions (bounded + non-empty +
D5), a third place to keep in sync when slice B lets multi-axis/constant writers box.

### Candidate defects (silently-ignored cells; NOT fixed, Rule 14; rough cost in dispatches)
1. Pinned declaration silently ignored for a boxed single multi-axis or constant writer (derived shape,
   no diagnostic). Slice B (`boundedScatter` stops gating) closes it; 1 dispatch inside B.
2. Stale `overlappingScatter` guard on the `.assign` constant arm (COL): D5, planned T3; ~0.3 dispatch.
3. Reference/legacy evaluators accept scan-local multi-axis and constant scatters and OVERWRITE (F3)
   while the checked preflight refuses them; already parked as F3; a dedicated slice.
4. No pin for a diagonal scatter inside a scan, and none for a zero-coefficient writer under a boxed
   declaration; 0.3 dispatch each (two fixtures).
5. `declaredShapeWins` (oracle) mirrors `boxedSingleGroups` by hand; slice B must change both (a
   drift guard such as a shared predicate in `Ast.lean` would remove the copy; ~0.5 dispatch).
6. Docs still describing the legacy rule and the two refusals (list in the T1 section): T4.

### Decisions taken and why
* Unify the corner formula by moving it UP into `DSL/Ast.lean` (`affineImageBounds`) rather than having
  `outExtent` call `scatterImageBounds`: Ast is upstream of Eval/Plan, so the other direction is
  impossible; `scatterImageBounds` kept its name and signature so B6 callers and tests are untouched.
* `checkScatterAffineExpr` got a Bool parameter, not a second function: the constant refusal and the
  locator strings stay in one place and the scan arm's behaviour is byte-identical.
* The oracle predictor was changed in T1 (not T2): it is a second extent formula and a stale one
  fails no guard until a fixture reaches four-leg comparison.
* Re-pinned the B6 max-corner off-by-one at `scatterRangeViolation` with an explicit `destShape`
  (the brief's suggestion), because `checkScatter`'s extent clause makes it unreachable for 2-axis rows.
* `ScatterGeometryTest` is a NEW module (one lakefile glob) rather than appending to
  `B5cSingleBoxTest`/`ScatterCompileTest`: the B5 harness (`agree`, hard-coded output name `S`) is
  what makes the f64 + f32 + reference triple one-line; `ScatterCompileTest`'s `assertScatterParity`
  uses surface syntax, which cannot spell a multi-axis slot.

### Anything that blocks T3 (constant-slot work)
Nothing blocks it. Facts T3 needs: (a) the constant arm in `checkScatterAffineExpr` is shared with the
scan arm, so T3 must not delete it (the top-level arm stays per the refined design); (b) `fD'`
(`.scatter` constant, declared 4) and `fOriginC` are the differential fixtures that flip; their pins
sit next to the `tag fD'`/`fOriginC` lines and `legacyCells fD'`; (c) `derivedShape` keeps the constant arm
`(c+1)` and `declaredShapeWins` requires a non-empty form, both deliberate for T3/B; (d) `ScatterGeometryTest`
has the constant-slot refusal pin to flip; (e) CompileTest's re-donored "fixture 11" uses a constant slot
as the still-refused donor, so after T3 (which keeps the top-level constant arm) it still holds, but the
plan should name it as a donor to re-check.

### Budget
Far over the 60-turn brief: roughly 115 tool calls in total (breach, said plainly). Peak context
not measurable from inside the session; I believe it stayed under about 200k (large outputs were
cut or redirected to files), but that is an estimate. The two full rebuilds triggered by the `Ast.lean`
edit (about 8800 jobs each) dominated wall time, not context.


## T3 — constant-slot scatter (the third commit on the branch; sha in `git log`, it carries this file)

### What changed (identifiers @ file)
* `lowerConstSlots` (new) and `lowerArith` @ `DSL/Pipeline/Structural.lean`: every `.affine (.const n)` slot of a scatter-shaped `.assign` AND of a hand-built `.scatter` becomes `.affine (.affine n [(1, u)])` over a fresh synthetic axis `u` (UID from `freshNonZero`, name `"#const" ++ toString uid`), and `Decl.axis u (some 1)` is appended to the returned `decls`. A statement that carries an `iterAt`/`iterNext` slot is left untouched (scan-local keeps its constant refusal; see decisions). The `.assign` arm's `overlappingScatter` throw is deleted (D5). `LHSSlot.collapses` was DELETED: `rg` found no user besides that throw (only comments, updated). `CompileError.overlappingScatter` @ `Exec/Uid.lean` kept, producerless, comment says so.
* `constUnitPrefix`, `IdxExpr.isConstUnit`, `LHSSlot.boundedScatter` @ `DSL/Ast.lean`: `boundedScatter` now answers false for the rewritten constant (`!e.isConstUnit && ...`): the marker that keeps risks (i) and (ii) unchanged (below). `scatterAffineClass` and the checked preflight are untouched: the rewritten slot is single-axis `.bounded` there, so the top level admits it; the raw `.constant` arm of `checkScatterAffineExpr` stays (hand-built bypass, plus scan arm).
* Doc comments updated: `Eval/Plan/Compile.lean` (constant paragraph, `collapses` mention), `lowerArith` section header.
* Tests: new T3 section in `Eval/Plan/ScatterGeometryTest`; `DSL/Pipeline/StructuralTest` (collapsing-constant pin re-pinned to the lowering + new scan-slot-untouched pin); `Semantics/SourceDifferentialScatterTest` (`fD'`, `fI1`, `fI2`, `fMask`, `fOriginC` re-pinned); `Eval/Plan/CompileTest` (comment only; its constant-slot preflight pin is the bypass pin and passes unchanged); T2's constant-refusal pin in `ScatterGeometryTest` moved to the `bypass` pin.

### Phase-order finding and risks (i)/(ii)
Order is `assignUIDs, resolveDecls, reclassifyIterSlots, checkReadRanks, checkDtypes, checkScatterNonlin, lowerArith, finalizeScans, schedule` and collection (`collectDefinitions`, `writerGroups`, `boxedSingleGroups`, `checkWriterGroup`) runs on the SCHEDULED program, i.e. AFTER `lowerArith`. So a plain rewrite necessarily changes what `boundedScatter` sees (a bounded single-axis slot), which would admit a constant writer to groups and box it. The least machinery is a marker in the one gate both collector sites use: the synthetic axis name prefix, tested by `isConstUnit` inside `boundedScatter`. Baseline (T2 commit, probe run): `sourceError` of 2 constant `.scatter` writers, of a constant + conv writer, both orders, = `multiWriterScatter "S"`; boxed single constant (`k` pinned 8): `shapesOf = (some [4], none, none)` (checked legs refused), `groupsOf = []`. After T3: `multiWriterScatter "S"` unchanged for `.scatter` pairs, `.assign` pairs and constant+conv; boxed single constant `(some [4], some [4], some [4])` with `groupsOf = []` (derived shape wins, pin ignored: B5c D2 residual, now visible in three legs). Risks (i) and (ii) both resolved WITHOUT blocker. NOT done: the oracle (`declaredShapeWins`) needed no change (it works from the unlowered source constant).
A consequence to know (not a defect of T3): the differential now reports `known:extent` for a constant writer whose destination is DECLARED larger than `n+1` (`fI1`, `fI2`, `fMask`), the same class as `fFbig`; this is the residual slice B closes. Before T3 those compiled to `nativeFailure` (`overlappingScatter`).

### Observed values (all from real runs of `lean-file.sh test/Eval/Plan/ScatterGeometryTest.lean`, then pinned as `#guard`; inputs `A=[1,2,3,4]`, `B=[1,10,100]`)
* `S[3] := A[a]`, `.scatter` and `.assign` arms: reference == checked f64 == checked f32: shape `[4]`, cells `[0,0,0,10]`; plan fields `(outCoeffs, outBias, destShape, compute.outputShape) = (#[#[1,0]], #[3], #[4], #[1,4])` (columns are `[u, a]`). `scheduled.decls` gained exactly one entry, `.axis "#const4" (some 1)`. P0 source-level probe (`axis u = 1; Y[u+3] := X[a]`) gave the same `[0,0,0,10]`.
* `S[a,3] := A[a]` (dst `[a,k]`): `[4,4]`, column 3 = `A`, other cells 0 (both arms). `S[3,4] := A[a]` (dst `[k,m]`): `[4,5]`, one nonzero cell (index 19) = 10, plan `(#[#[1,0,0],#[0,1,0]], #[3,4], #[4,5], #[1,1,4])`. `S[3] := A[a]*B[b]`: `[0,0,0,1110]`. `S[0]`: shape `[1]`, `[10]`; `S[0]` with `agg max`: `[4]`; `S[3]` `agg max`: `[-inf,-inf,-inf,4]` (all three legs).
* f32 (`A=[2^24,1,1,1]`): native bits `[0,0,0,1266679808]`, independent twin `T[a] := A[a]` summed in f32 `1266679808`, narrowed binary64 `[0,0,0,1266679810]`.
* Boxed single (`k` pinned 8) `.scatter`/`.assign`: shapes `(some [4],some [4],some [4])`, `groupsOf = []`. Multi-writer: `multiWriterScatter "S"` x3. `routeError = none` both arms. `EvalWarning` count 0.
* Bypass: the `.scatter` constant handed straight to `prepareEvalPlan` (schedule rebuilt with the raw slot) is refused `.capability (.scatterOrAffineLhs "S: constant affine LHS slot")`.
* Differential (`lean-file.sh test/Semantics/SourceDifferentialScatterTest.lean`): `tag fD'` `parity` (checked cells `[0,0,0,10]`, equal oracle and legacy); `tag fI1` / `tag fI2` / `tag fMask [5,6]` `known:extent`; `tag fOriginC [5,6]` `parity`, no `scatterOrAffineLhs` in its report.
* Scan base case: `tlprog!{ iter l = 3  S[i, 0] := X[i]  S[i, l + 1] := S[i, l] }` elaborates `S[i, 0]` as `[.free i, .iterAt _ 0]` and compiles to a `ScanStmt.scan`.

### Full build
`bash leanncd/scripts/lake-build.sh leanncd LeanNCD Tests JaxExperiment`: green, 8843 jobs (before the StructuralTest scan pin was added; re-run at the end, see report).

### Mutation cycles, T3 (`--task T3`) and the amended T2 04-06
| id | change | result | killed by |
|---|---|---|---|
| T3-01 | synthetic axis pinned 2 | killed | ScatterGeometryTest |
| T3-02 | bias n+1 | killed | ScatterGeometryTest |
| T3-03 | rewrite skipped on `.assign` arm | killed | ScatterGeometryTest |
| T3-04 | rewrite skipped on `.scatter` arm | killed | ScatterGeometryTest |
| T3-05 | `overlappingScatter` throw re-added | killed | ScatterGeometryTest |
| T3-06 | unit coefficient 0 | killed | upstream B5BoundaryTest (explicitConstant) |
| T3-07 | `boundedScatter` marker removed | killed | upstream B5BoundaryTest (explicitConstant) |
| T3-08 | synthetic decl dropped | killed | ScatterGeometryTest |
| T3-09 | scan-slot statements rewritten too | killed | StructuralTest (new pin; first run of the manifest would have SURVIVED without it, the fixture was added for it) |
T2 04, 05, 06 amended: the earlier caveat holds but cannot be removed. `ScatterGeometryTest` imports `B5cSingleBoxTest`, which imports `B5BoundaryTest`/`B5NativeTest`, so any mutant those older pins catch fails THERE before the new module builds. They are re-targeted to the older pin by name (04: B5BoundaryTest `twoAxes`; 05: B5cSingleBoxTest `multiAxisOne`; 06: B5NativeTest B6 guards), re-run, killed. The new-module duplicates (`convTwo`, `convBoxed`, mixed-sign B6) are the same assertions and were NOT independently shown live by a mutant; same for T3 06/07 vs the new risk pins. Cost to do it properly: move the new pins into a module that does not import the old ones (about 0.3 dispatch).
T3-06/T3-07 first ran with `expect` naming ScatterGeometryTest and reported FAIL (the build broke at B5BoundaryTest); expects were corrected to the real killer and re-run.

### CASE x CLASS: the constant column after T3
| cell | before | after |
|---|---|---|
| top-level single (unboxed) | `.assign`: COL `overlappingScatter` (stale); `.scatter`: CSLS `scatterOrAffineLhs` | both arms lowered to `n+1·u`, admitted, extent `n+1` in reference and plan (REQ, ScatterGeometryTest T3) |
| multi-writer group | `multiWriterScatter` (BS false) | UNCHANGED, `multiWriterScatter`: marker `isConstUnit` keeps BS false (FORB, pinned for `.scatter`, `.assign`, constant+conv) |
| boxed single (pinned decl) | NOT collected, derived wins; SIL | UNCHANGED (derived wins), now pinned in all three legs (REQ, `groupsOf = []`); still SIL as a diagnostic: the oracle reports `known:extent` (`fI1`) |
| scan-local | `.assign` base: `overlappingScatter`; hand-built `.scatter`: CSSLS refusal | `.assign`+scan slot compiles to a raw-constant scatter (like a hand-built one), checked CSSLS refuses it; reference/legacy accept (F3 overwrite). StructuralTest pins the untouched slots |

### Decisions taken and why
* Marker in `boundedScatter` by axis-name prefix (not a new `IdxExpr` constructor, not a Decl lookup): `boundedScatter` has no env and both collector sites call it; a constructor would touch every exhaustive `IdxExpr` match. Costs one full rebuild (Ast edit).
* Scan statements skipped by `lowerConstSlots`: otherwise the scan-local preflight, which admits single-axis slots, would silently start admitting a constant inside a scan; slice A does not design a unit axis inside a scan body.
* Name `#const<uid>`: `#` is not an identifier character (no user axis collides), the uid suffix keeps two synthetic axes distinct; `Decl.axis` has no unused-axis diagnostic here (0 `EvalWarning`).
* `LHSSlot.collapses` deleted (sole user gone); `overlappingScatter` constructor kept.

### Side issues parked (Rule 14; rough cost)
1. Reference/legacy accept a scan-local constant `.assign` and overwrite (F3 family); before T3 it was a compile error. Cost 0.3 dispatch to refuse it in `lowerConstSlots`'s scan branch (throw `scatterOrAffineLhs`-equivalent) if wanted.
2. New-module pins not independently shown live (import order above): 0.3 dispatch.
3. Stale comments naming `overlappingScatter`/`collapses` may remain in docs/AGENTS (T4 doc sweep): 0.2 dispatch.
4. Slice B: the `isConstUnit` marker plus `declaredShapeWins` (oracle) are two places to unmark together when constants box (already candidate 5).

### Budget
About 60 tool turns (at the limit); peak context estimated well under 250k.

## T3b — refuse a constant slot in a scan statement (fourth commit; fail-loud regression repair)

### What changed (identifiers @ file)
* `lowerArith` (`.assign` arm) @ `DSL/Pipeline/Structural.lean`: inside `if slotsBecomeScatter slots`, a statement with a scan slot (`LHSSlot.isScanSlot`) AND a raw constant slot (`LHSSlot.isRawConst`) throws `CompileError.overlappingScatter nm` (exactly the pre-T3 result for those programs). The hand-built `.scatter` arm is unchanged (it reaches the checked preflight's `scatterOrAffineLhs` refusal; reference/legacy still accept it, F3, parked).
* New `LHSSlot.isScanSlot`, `LHSSlot.isRawConst` @ `Structural.lean`; `lowerConstSlots` now uses `isScanSlot` for its scan branch (behaviour unchanged). Doc comments of `lowerArith`'s section header and `lowerConstSlots` updated.
* `CompileError.overlappingScatter` @ `Exec/Uid.lean` has a producer again; its comment (T3 had written "COMPATIBILITY ONLY, no producer") now says so. `rg producerless` in `leanncd/LeanNCD`: only `scatterInScan` (a different constructor) remains. `Eval/Plan/Compile.lean`'s constant paragraph needed no change (it says a scan statement is left alone by `lowerConstSlots`, still true for a hand-built one).
* Tests @ `test/DSL/Pipeline/StructuralTest.lean`: the scan-slot-untouched pin now uses a non-constant slot (`.scale 2 j` next to `.iterAt l 0`; asserts the slots and decls are untouched); new `lowerArith` pin: `.assign "S" [.iterAt l 0, .affine (.const 3)]` -> `.error (.overlappingScatter "S")`; new whole-pipeline pins `scanSurfaceConst` (the surface scan program `tlprog!{ iter l = 3  S[i, 0] := X[i]  S[i, l + 1] := S[i, l] }` with the base statement's free slot replaced by `.affine (.const 3)`) -> `compileToScheduled` gives `overlappingScatter "S"`, and the accept-neighbour `scanSurface` (unmodified) compiles. The existing T3 fixtures are untouched (the non-scan constant pin still lowers).
* Surface syntax cannot spell a raw constant slot (`elabTLLHSSlot`: a numeral is always `.iterAt`), so the "surface-path" fixture is a surface program plus one `stmts.map`, not a `tlprog!` literal.

### CASE x CLASS: scan-local cell of the constant column after T3b
| cell | after T3 | after T3b |
|---|---|---|
| scan-local, `.assign` with a raw constant | compiled to a raw-constant scatter; checked CSSLS refuses, reference/legacy accept and overwrite (F3) | refused at compile: `overlappingScatter` (pre-T3 behaviour; REQ, StructuralTest) |
| scan-local, hand-built `.scatter` with a constant | CSSLS refusal (`scatterOrAffineLhs`), reference/legacy overwrite (F3) | UNCHANGED (F3 parked) |

### Build and mutation cycles (`--task T3b`: 3/3 killed)
Full build `lake-build.sh leanncd LeanNCD Tests JaxExperiment`: green, 8843 jobs. Manifest `--task T3b` (`mutation-manifest.sh`, 8494-job targeted builds): 3/3 PASS, files restored byte-identical.
| id | change | result | killed by |
|---|---|---|---|
| T3b-01 | the new throw removed | killed | StructuralTest (first failing module) |
| T3b-02 | throw on every statement with a scan slot | killed | StructuralTest (the non-constant scan pin) |
| T3b-03 | throw on every raw constant (the pre-T3 guard) | killed | StructuralTest: `error: test/DSL/Pipeline/StructuralTest.lean:244:0: constant LHS must lower, got ...overlappingScatter "Z"` |
Each `targets` entry is `DSL.Pipeline.StructuralTest`, which fails first (it imports only `DSL.Compile`; no older failing import hides it).

### Decisions
* Throw placed in `lowerArith`'s `.assign` arm, not inside `lowerConstSlots`: that function is shared by the `.scatter` arm, whose hand-built statements must keep their behaviour (the brief), and it has no statement name to report.
* `isScanSlot`/`isRawConst` as named predicates (two call sites each for `isScanSlot`, one named for the throw's readability).

### Side issues parked (Rule 14)
1. Reference/legacy still accept a hand-built scan-local constant `.scatter` and overwrite (F3): 1 dispatch (dedicated F3 slice).
2. `Eval/AGENTS.md` line about `lowerArith` "still rejects a constant-LHS `.assign` slot" is accurate only for scan statements now; T4 doc sweep owns it (0.1 dispatch).

## T5 — four-leg tropical fixtures (rows `3920038e`; mutation checks, the T3b pin and patches in the docs commit)

### Preconditions (checked)
`rg -n "affineImageBounds" leanncd/LeanNCD/DSL/Ast.lean` finds the definition; `leanncd/test/Eval/Plan/ScatterGeometryTest.lean` exists; worktree on the T3b commit, baseline build green.

### What changed (identifiers @ file)
`test/Semantics/SourceSortedDifferentialTest.lean`: new axes `o6`/`o13`/`o4` (uids 10/11/12), `snapG` (a copy of `snap` with a destination axis of declared extent `n`; `snap` untouched), rows `conv` (W1, `Y[a+b]`, extent 6), `conv23` (W2, `Y[2a+3b]`, extent 13), `constSc`/`constAs` (W3, `Y[3]` as `.scatter` / `.assign`, extent 4), each for `.max` and `.min`, asserting `yCore` and `classOf` with `#guard_msgs`. No existing row edited; no production change.

### Observed values (command: `lean-file.sh leanncd test/Semantics/SourceSortedDifferentialTest.lean`, then pinned; all classes `fourLegParity`; all equal the brief's hand cross-checks)
* `conv` max `[2, 11, 101, 102, 103, 104]`; min `[2, 3, 4, 5, 14, 104]`.
* `conv23` max `[2, -inf, 3, 11, 4, 12, 101, 13, 102, 14, 103, -inf, 104]`; min `[2, +inf, 3, 11, 4, 12, 5, 13, 102, 14, 103, +inf, 104]`.
* `constSc` and `constAs` (identical): max `[-inf, -inf, -inf, 4]`; min `[+inf, +inf, +inf, 1]`.

### Build
`lake-build.sh leanncd LeanNCD Tests JaxExperiment`: green, 8843 jobs.

### Mutation cycles, T5 (`--check` then `--task T5`, then re-run after the `expect` strings were replaced): 3/3 killed
Every cycle failed first in `Semantics.SourceSortedDifferentialTest` (no older import fails before it; the target's import closure does not contain `ScatterCheckTest`/`B5*Test`). Each mutant is killed by the `classOf` rows (the `yCore` rows read the Core leg, which these production changes do not touch); `expect` strings are substrings copied from the observed log.
| id | change | result | killed by | expect (copied) |
|---|---|---|---|---|
| T5-01 | `LHSSlot.outExtent` 2+-axis arm back to the legacy sum (`some legacy`) @ `DSL/Ast.lean` | killed | SourceSortedDifferentialTest, `classOf` rows of `conv` (W1) and `conv23` (lines 359, 363, 368, 372) | `error: test/Semantics/SourceSortedDifferentialTest.lean:359:0:`, ``Docstring on `#guard_msgs` does not match generated message:`` |
| T5-02 | top-level `checkScatterLHSSlot` refuses multi-axis again (`checkScatterAffineExpr false`) @ `Eval/Plan/Compile.lean` | killed | same module, same four rows (the checked leg refuses) | same two strings |
| T5-03 | constant placement bias `n + 1` @ `lowerConstSlots` in `DSL/Pipeline/Structural.lean` | killed | same module, the `classOf` rows of `constSc`/`constAs` (lines 378, 382, 386, 390) | `...Test.lean:378:0:` + the same docstring line |
The expect strings carry line numbers: a row inserted above them needs the manifest line updated.

### A regression T3b caused, found by the full T3 re-run, and its repair (a THIRD patch)
After T3b the `.assign` arm throws before `lowerConstSlots` sees a scan statement, so the scan skip in `lowerConstSlots` was no longer exercised: `SGA-T3-09` would have SURVIVED, and its `old` string also no longer matched (`lowerConstSlots` uses `LHSSlot.isScanSlot` now; the manifest entry was updated). Added a `lowerArith` pin in `StructuralTest`: a hand-built `.scatter "S" [.iterAt l 0, .affine (.const 3)]` keeps its raw constant, no synthetic decl. Commit `ac09b7e6`, patch `T3b-scan-pin.patch` (`3920038e..ac09b7e6`). `--task T3` re-run: 9/9 killed, T3-09 now by `StructuralTest.lean:292` ("hand-built scan scatter must keep its raw constant"). `--task T3b`: 3/3 killed (earlier run). Total manifest 31 entries, `--check` OK.

### Patches (`papers/semantics/additive_scatter_geometry_a_patches/`)
`T3b-scan-const.patch` (`d776a840..2be9b283`), `T5-tropical-fixtures.patch` (`2be9b283..3920038e`), `T3b-scan-pin.patch` (`3920038e..ac09b7e6`), each `git diff ... -- leanncd/`. In a scratch worktree of `d776a840`: `git apply --check T3b-scan-const.patch` clean; applying all three in order (`git apply -v`) clean; `git diff --stat ac09b7e6 -- leanncd/` empty (applied tree equals the commit's `leanncd/`). Scratch worktree removed.

## T4 (live docs sweep)

* Commit f73747d3c70014d2fac5b3d5ef437bb471be450b (docs only; patch `additive_scatter_geometry_a_patches/T4-docs.patch`, apply-check OK, applied tree equals the commit for every changed path).
* Files edited (7): leanncd/LeanNCD/Eval/Plan/AGENTS.md, Eval/AGENTS.md, DSL/AGENTS.md (new Pitfall), Semantics/AGENTS.md, Eval/Plan/Error.lean (doc of multiAxisScatterLhs only), papers/backend_missing_functionality.md, papers/scatter_affine_lhs_writes.md. Not edited because already correct (done by T1-T3b): Ast.lean, Structural.lean, Compile.lean, Uid.lean, additive_production_decision_note.md (group refusals still true; other hits historical), leanncd/AGENTS.md (no hits), papers/semantics/README.md (does not index slice notes).
* Stale claims before the edit: 6 (Plan/AGENTS L56, Eval/AGENTS L64, Semantics/AGENTS L172, Error.lean multiAxisScatterLhs doc, backend_missing L317, scatter_affine L772); after: 0. Raw pattern line-hits over the file set: 62 before, 67 after (the added hits are the new, correct prose). No remaining hit for the old extents (derives 7 / derives 16; the Error.lean '7' example was removed with its doc).
* Pitfalls sizes (DSL/AGENTS.md, header line included): about 1802 -> 2241 chars; Eval/Plan/AGENTS.md 2115 and Eval/AGENTS.md 1043 unchanged (under 3000). Semantics/AGENTS.md has no Pitfalls section.
* Build: lake-build.sh LeanNCD Tests JaxExperiment green, 8843 jobs.
* Left: Compile.lean/Structural.lean/Ast.lean docs were already current from earlier tasks; Error.lean line-232 enum comment ('scatter statements, affine LHS slots') left as is (still true for scan-local and bypass forms). Tool calls used: about 29 (slightly over the 28 stop line because of one wasted sleep and the finisher script).
