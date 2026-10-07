# Plan-signature modules under the flip (S3)

Measured with the S1 flip applied, one targeted build per module. Error counts are `^error: test/...`
lines (one per failing `#guard`/`run_cmd`), from scratchpad logs `s3_sig.log` and `s3_rest.log`.
"VERIFIED" = a targeted build after the fix succeeded.

| module | #failing | class | fix site | status |
|---|---|---|---|---|
| Eval.Plan.NonlinCompileTest | 48 (VERIFIED count) | (i) | `sourceCompileCauseOf`/`compiledEqB`/`reluProg`/`softmaxProg` use `p.explicitF64.compileToScheduled`; `axiswiseSched` decls via `explicitF64Decls`; the 3 `TLProgram.eval p` helper bodies (`legacyAccepts`, `legacyErrorOf`, `sourceEvalOf`) use `p.explicitF64` | FIXED, build green (two commits) |
| Eval.Plan.SignatureTest | 8 (lines 45, 90, 99, 109, 113, 137, 426, 443) | 90/99/109/113 (ii): pin `dtypeOfDecl (.tensor)`/`storageConstraintOfDecl (.tensor/.linear)`/`dtypeOfDecl (.linear)` to f64/float64 -> now f32/float32; 45 (ii)/(i): `ofDenseInputsForDecls [] conversionInputs` pins an UNDECLARED name over a Float carrier to an f64 signature -> now a `storageKindMismatch`, so either pin the error or declare `.typedTensor .f64 "X" []`; 137 (i): `gn2Prog` undeclared names + Float carrier (`InputSignatureBuildError.storageKindMismatch`); 443 (ii, read-only guess): `ofDenseInputs32ForDecls [.tensor "X" []]` pinned a rejection that is now an acceptance; 426 NOT examined | the guard lines named | NOT fixed |
| Eval.Plan.CompileTest | 71 | (i) expected (hand-built schedules + `ofDenseInputs`), NOT examined | likely the same helper pattern as Nonlin (143 `prepareEvalPlan`/`ofDenseInputs` sites) | NOT fixed |
| Eval.Plan.ScanCompileTest | 101 | (i) expected, NOT examined | 34 `ofDenseInputs`/`prepareEvalPlan` sites; the scan-state fallback is flipped, check `stateSigs` pins | NOT fixed |
| Eval.Plan.ScatterCompileTest | 48 | (i) expected, NOT examined | only 4 `prepareEvalPlan`/`ofDenseInputs` sites, so probably ONE helper (as in Nonlin) | NOT fixed |
| Eval.Plan.Scatter32OracleTest | 1 | NOT examined; message: "O1 strided, unary, carrier-discriminating contrast: binary64 signature rejected: ...InputSignatureBuildError" (the contrast builds a binary64 signature for names that are now f32 by default, so (i)/(ii)) | `Scatter32OracleTest.lean:241` | NOT fixed |

## Shared root cause (verified on Nonlin, expected elsewhere)

These tests build `tlprog!{..}` programs or hand-written `ScheduledProgram`s whose names are
UNDECLARED, then pair them with the binary64 carrier (`InputSignature.ofDenseInputs`, a `Float`
`DenseTensor` env, `runPreparedDense`, or the reference evaluator). Undeclared names are binary32
after the flip, so the plan expects f32 and the carrier is f64 (`storageKindMismatch`). The same
lever as slice 1 fixes it: `TLProgram.explicitF64` / `explicitF64Decls` (leanncd/test/Eval/ExplicitF64.lean,
`import Eval.ExplicitF64`). There is NO single helper shared across modules; each module has 1-3
local helper sites (compile wrapper, hand-built schedule constructor, legacy-evaluator wrapper) and
fixing those cuts nearly all assertions. NonlinCompileTest: 48 -> 12 after the compile wrappers +
`axiswiseSched`, 12 -> 0 after the three `TLProgram.eval` helper bodies.

## Class (iii) (production issue)

None observed. Only Nonlin (fully) and the SignatureTest pins were read; the 4 other modules were
not examined, so this is not a clean bill for them.

## Task 2 SignatureTest (VERIFIED classification)

Targeted build `Eval.Plan.SignatureTest` after Task 1 (default flipped): exactly 8 failing assertions,
at the lines the prototype named. Class (iii): none.

| line | assertion | what failed | class | fix |
|---|---|---|---|---|
| 45 | `ofDenseInputsForDecls [] conversionInputs` -> `X` is an `f64` signature | undeclared `X` is now `.float32`; the `Float` carrier is binary64, so the call is a `storageKindMismatch`. The fixture is the Float-buffer -> `f64`-signature conversion baseline (the third outcome beside bool and rejected) | (i) | declare `.typedTensor .f64 "X" []` so the f64 conversion pin stays; ADD the undeclared neighbour pinned to `.error (.storageKindMismatch "X" .float64 .float32)` (the new default, class (ii)) |
| 90 | `dtypeOfDecl (some (.tensor "X" [])) == .f64` | plain `tensor` is now binary32 | (ii) | re-pin `.f32`; comment that `.typedTensor .f64` is the binary64 spelling |
| 99 | `storageConstraintOfDecl (.tensor "X" []) == some .float64` | same | (ii) | re-pin `.float32` |
| 109 | `storageConstraintOfDecl (.linear "W" [] false) == some .float64` | same | (ii) | re-pin `.float32` |
| 113 | `dtypeOfDecl (some (.linear "W" [] false)) == .f64` | same | (ii) | re-pin `.f32` |
| 137 | `gn2Prog` `run_cmd`: `X` dtype `f64` via `ofDenseInputsForDecls sched.decls` over a Float env | `X` undeclared -> `.float32`, `storageKindMismatch "X" .float64 .float32` | (i) | compile `gn2Prog.explicitF64` (undeclared names declared `tensor f64`) |
| 426 | `ofDenseInputs32ForDecls [.typedTensor .f32 "X" [], .tensor "Z" []]` rejects `Z` with `(.float32, .float64)` | plain `tensor Z` is now binary32, so there is no disagreement over the f32 carrier | (i) | re-spell `.typedTensor .f64 "Z" []` at source (the fixture's point is an explicit binary64 declaration among f32 ones) |
| 443 | `ofDenseInputs32ForDecls [.tensor "X" []] soleInput32` rejects | plain `tensor X` is binary32, so the native Float32 buffer is accepted | (ii) | re-pin to ACCEPT (`f32` signature, shape `[2, 3]`); ADD the nearest still-rejecting neighbour `[.typedTensor .f64 "X" []]` -> `storageKindMismatch "X" .float32 .float64` |

## Task 3 scatter modules (VERIFIED classification)

Targeted builds after Task 1 (default flipped). `Eval.Plan.ScatterCompileTest`: exactly 48 failing
assertions (39 `#guard`, 9 `run_cmd` throws), one `lake` job failure. `Eval.Plan.Scatter32OracleTest`:
1 failing assertion. Class (iii): none. No fixture in `ScatterCompileTest` declares any tensor: every
program is `tlprog!{ Out[...] := X[...] }` with undeclared names, so all of them are now `.float32`
and meet the `Float` (binary64) carrier through `InputSignature.ofDenseInputs` -> `prepareEvalPlan`
rejects (`storageKindMismatch`). Fix is the lever at the two helper bodies that call
`compileToScheduled` (undeclared names, so `explicitF64`, not source re-spelling).

| module | lines | assertions | what failed | class | fix |
|---|---|---|---|---|---|
| ScatterCompileTest | 106, 112-131 (S1) | 11 `#guard` via `upsamplePrepared`/`upsampleScatter` (-> `preparedOf` -> `schedOf`) | `preparedOf` is `none`: `prepareEvalPlan` rejects the unwrapped schedule | (i) | `schedOf` compiles `p.explicitF64` |
| ScatterCompileTest | 143-145 (S2), 154-156 (S3), 169-172 (S4), 186-187 (S5), 208/212/214 (S6), 231-234 (S7), 261-268 (S8), 292-296 (S9) | 28 `#guard` via `preparedOf` | same | (i) | same (`schedOf`) |
| ScatterCompileTest | 133, 146, 157, 173, 190, 216, 235, 269, 297 | 9 `run_cmd` `assertScatterParity` ("prepareEvalPlan rejected a source-compiled scatter program") | helper calls `prog.compileToScheduled` directly, not through `schedOf` | (i) | `assertScatterParity` compiles `prog.explicitF64`; its `evalScheduled sched env` leg reuses that same `sched`, so no separate change |
| Scatter32OracleTest | 241-245 `run_cmd` (case O1, first failure; O5 shares the helper and would fail next) | 1 reported | `run64` builds a binary64 `InputSignature.ofDenseInputsForDecls` for the O1/O5 `contrast64` programs, whose plain `tensor A(i), ...` is now binary32: `storageKindMismatch "B" .float64 .float32` | (i) | re-spell `tensor f64` AT SOURCE in the two `contrast64` programs (O1 line 175, O5 line 236); f32 legs (`compile32`/`run32`, `tensor f32 ...`) untouched |

Site table (rg `ofDenseInputs|prepareEvalPlan|compileToScheduled|TLProgram.eval|evalScheduled|ScheduledProgram|runPreparedDense`;
feeds the Task 6 site table):

| module | line | site | changed? |
|---|---|---|---|
| ScatterCompileTest | 42 | `schedOf`: `p.compileToScheduled` | YES `p.explicitF64.compileToScheduled` |
| ScatterCompileTest | 50 | `preparedOf`: `prepareEvalPlan sched (ofDenseInputs env)` | no (sched comes from `schedOf`) |
| ScatterCompileTest | 72 | `assertScatterParity`: `prog.compileToScheduled` | YES `prog.explicitF64.compileToScheduled` |
| ScatterCompileTest | 75, 80, 83 | `prepareEvalPlan`/`runPreparedDense`/`evalScheduled` over that `sched` | no |
| ScatterCompileTest | 3, 15-19, 37-38, 201 | doc comments only | no |
| Scatter32OracleTest | 41, 44, 47, 55 | `compile32`/`run32` binary32 leg | no (`tensor f32` declared; default irrelevant) |
| Scatter32OracleTest | 103, 106, 109, 112 | `run64` binary64 leg | no code change; its inputs (the O1/O5 `contrast64` programs) now spell `tensor f64` |
| Scatter32OracleTest | 12, 98 | doc comments | line 98 "(ordinary declarations)" -> "(`tensor f64` declarations)" |

## Task 4a CompileTest (VERIFIED classification)

Targeted build `Eval.Plan.CompileTest` after Task 3 (default flipped), before any edit to the module:
exactly 71 failing assertions (`^error: test/Eval/Plan/CompileTest.lean` lines; 61 `#guard`, 10
`run_cmd` throws), the one `lake` job failure. Class (iii): none. The module is a hand-built-schedule
file: every fixture is its own `ScheduledProgram` literal, so there is no single compile wrapper (the
only `compileToScheduled` calls are `warnBaselinePrepared` and the `warnProg` `run_cmd`); the helper
level is the schedule definitions themselves. Many assertions share one schedule, so 71 failures
collapse to 20 groups. Split: class (i) 56 assertions (lever at the schedule definition), class (ii)
15 assertions (they pin the old default; 4b).

| group (fixture) | failing lines | n | what failed | class | 4a fix |
|---|---|---|---|---|---|
| `identitySched` (undeclared `X`/`Y`) | 481, 721, 728 | 3 | `prepareEvalPlan identitySched identitySig` rejects: `X` is `.float32`, the carrier is `Float` (`storageKindMismatch`); 721/728 then fail the same way rather than reach their Step-B cause. Their prose ("`X` is undeclared ... `dtypeOfDecl none = .f64`") is stale once `X` is declared `f64` | (i) | `explicitF64Sched` over the literal; prose rewrite is 4b |
| `f64PointwiseSched` (`identitySched` with a relu; "X/Y stay undeclared and default to `.f64`") | 1096, 1098, 1101 | 3 | inherits `identitySched`'s undeclared names | (i) now, prose stale (the plan's named `axI1` fixture) | none beyond `identitySched`; it becomes an explicit-`f64` control; prose rewrite is 4b |
| `contractSched` | 500, 528-533, 535 | 8 | undeclared `A`/`B`/`Y` over `Float` | (i) | `explicitF64Sched` |
| `multiReductionSched` | 563, 568, 570, 572, 574, 577, 581, 585 | 8 | same, `A`/`B`/`C`/`Y` | (i) | `explicitF64Sched` |
| `repeatSched` | 606, 610, 613 | 3 | same, `A`/`B`/`Y`/`Z` | (i) | `explicitF64Sched` |
| `repeatPredSched` (`repeatSched` + `predicate Y`) | 630, 639, 652, 659, 670, 681, 690, 694 | 8 | same, `A`/`B`/`Z`; `Y` is a predicate | (i) | `explicitF64Sched` over a literal decl list (it cannot append to an already-wrapped `repeatSched.decls`: duplicate `Y`) |
| `sameShapeSched` | 1405, 1408 | 2 | same, undeclared `A`/`B`/`Y` | (i) | `explicitF64Sched` |
| `extraCachedSched` (`sameShapeSched` donor) | 1459, 1461 | 2 | inherits | (i) | inherits |
| `orderedTwinSched` | 1555, 1557, 1561 | 3 | undeclared `A`/`B`/`Y`/`Z` over `Float` | (i) | `explicitF64Sched` |
| `warnProg` compile (`warnBaselinePrepared`, the warnings `run_cmd`) | 1607 | 1 | `X`/`Y` undeclared in the `tlprog!` source | (i) | `warnProg.explicitF64.compileToScheduled` at both calls |
| `cacheSchedWith` | 1661, 1663, 1665, 1666, 1673, 1700 | 6 | undeclared `X`/`Y` over `Float` | (i) | `explicitF64Sched` |
| `axShadowSched` (valid axis-shadow sibling) | 1746 | 1 | `A`/`B` undeclared; `evalScheduled` refuses (`unsupportedDtype`, declared `f32`) | (i) | `explicitF64Sched` (`Y` is a predicate: skipped) |
| `predSchedWith`, valid sibling | 1906 | 1 | plain `tensor A`/`B` now `f32` | (i) | re-spell `.typedTensor .f64` at source |
| `predRealDestSched`, control | 1928 | 1 | plain `tensor A`/`B`/`Y` | (i) | re-spell `.typedTensor .f64` at source |
| `scanPredSchedWith`, valid Boolean scan sibling | 2017 | 1 | plain `tensor X`/`A` | (i) | re-spell at source |
| read-rank valid sibling (`rankSched`) | 2185 | 1 | plain `tensor X`, undeclared `Y` | (i) | `explicitF64Sched` plus re-spell `X` |
| `rankScanSched` valid scan sibling | 2314 | 1 | plain `tensor A`/`S` | (i) | re-spell at source |
| `validAxisKindSched` (`plainAxisKindSched`) | 2442 | 1 | plain `tensor X`/`Y` | (i) | re-spell at source (helper's `X`, the valid sibling's `Y`) |
| `f32MixedDeclOrderSched` (declaration order: `Y` f32, `X` "ordinary") | 825 | 1 | plain `tensor X` is now f32: no mix, no rejection | (i) | re-spell `X` `.typedTensor .f64` (the point is used-name ORDER, not the default) |
| `f32MixedScatterReluProg` (FW2b, Step 0b before Step A) | 1326 | 1 | same, plain `tensor X` | (i) | re-spell `X` `.typedTensor .f64` |
| f32 identity "Control: the SAME program in the untyped (f64) spelling" | 786, 791 | 2 | plain `.tensor X/Y` pinned `.float64`/`admittedAlgebra`: now f32 | (ii) | 4b: re-pin to the new meaning (or spell `f64`), stale prose |
| `f32MixedUndeclaredSched` ("An undeclared external therefore stays f64") | 838 | 1 | undeclared `X` pinned as the f64 side of a mixed schedule: now f32, no conflict | (ii) | 4b: the mismatch direction inverts |
| `plainIdentitySched` vs `f64IdentitySched` | 865, 868, 870 | 3 | plain `.tensor` pinned equal to explicit `f64` | (ii) | 4b |
| `plainLinearSched` vs `f64LinearSched` ("untyped `linear` is unchanged") | 930, 931, 934, 935 | 4 | plain `.linear` pinned equal to explicit `linear f64` / `.float64` / `admittedAlgebra` | (ii) | 4b |
| `f32LinearMixedSched` (plain `.linear X` as "the f64 side") | 944 | 1 | plain `.linear` is f32: no mix | (ii) | 4b |
| `declaredBSched` ("`A` stays undeclared (expects `f64`)") | 1422, 1427, 1439, 1448 | 4 | undeclared `A`/`Y` + `f64` signature; Variant 2 pins `dtypeMismatch "A" .f64 .bool` | (ii) | 4b (the plan's named Boolean-validation fixture); 4a keeps `A`/`Y` undeclared by giving it its own decl list |

Counts: (i) 3+3+8+8+3+8+2+2+3+1+6+1+1+1+1+1+1+1+1+1 = 56; (ii) 2+1+3+4+1+4 = 15; total 71.

Fixtures that already PASS and stay untouched (rejection fixtures decided before the storage step, so the carrier
is never consulted): `dupDeclSched`, `predDupSched`, `predTwoStmtSched`, `predUnreadableSched`, the
`assertPredicateParity` rejection family, `selfReadSched`, `outOfOrderSched`, every `rank*` rejection
fixture and `rankScanDestinationSched`, `plainAxisKindSched`/`scanAxisKindSched` rejection fixtures.
They stay as written: wrapping them would change which pass reports the error (`rankProducedSched`'s
point is an UNDECLARED produced name).

### Task 4a CompileTest: result and the 4b input (VERIFIED by targeted build)

`Eval.Plan.CompileTest` builds: 71 failing assertions before (8518 jobs, one failing), 15 after
(8519 jobs: the added `Eval.ExplicitF64` import is the one new job). Every remaining failure is a
class (ii) pin from the classification table, no (i) left, none (iii). Lever added: one local helper
`explicitF64Sched` (`explicitF64Decls` over `sched.stmts.flatMap ScanStmt.sourceStmts`, the same body
`evalScheduledF64` uses), applied at the schedule definitions; `warnProg.explicitF64` at both
`compileToScheduled` calls. Plain `tensor` re-spelled `.typedTensor .f64` at source in
`predSchedWith`, `predRealDestSched`, `scanPredSchedWith`, `rankScanSched`, `plainAxisKindSched` (`X`),
`validAxisKindSched` (`Y`), `f32MixedDeclOrderSched`/`f32MixedScatterReluProg` (`X`), and the valid
read-rank sibling. One non-obvious fix: the warnings `run_cmd` APPENDS a statement writing `Z`
(undeclared, so binary32, beside the `f64` `X`): it failed with a mixed-precision capability error and
empty warnings, not an unsized axis, until `combined` itself went through `explicitF64Sched`.
`identitySched`/`identitySig`/`identityInputs`/`contractSched`/`repeatSched` keep their names (the
`Adapter32Test` donor uses `identitySched`, `identitySig`, `identityInputs`; it was NOT rebuilt here,
since Task 6 re-measures it, and `CompileTest` does not build clean until 4b).

**Residual failing assertions (the 4b input), 15, all class (ii).** Line numbers are at the 4a commit.

| fixture | lines | n | pinned to the old default | direction under the flip |
|---|---|---|---|---|
| f32 identity "Control: the SAME program in the untyped (f64) spelling" | 804, 809 | 2 | plain `.tensor X/Y` records `.float64` and `admittedAlgebra` | plain is f32: re-pin `.float32`/`admittedAlgebraF32`, or spell the control `f64` |
| `f32MixedUndeclaredSched` | 856 | 1 | undeclared `X` is the f64 side of a mixed schedule: `unsupportedDtype "Y: mixed ..."` | INVERTS: undeclared `X` is f32, no conflict; the mixing needs `X` declared `f64` (state the direction in the comment) |
| `plainIdentitySched` vs `f64IdentitySched` | 883, 886, 888 | 3 | plain `.tensor` equals explicit `f64` (`tensorSigs`, `storageKind`, step count) | plain is f32: pin equal to the `f32` spelling, keep an `f64` neighbour |
| `plainLinearSched` vs `f64LinearSched`/f32 | 948, 949, 952, 953 | 4 | plain `.linear` equals `linear f64`, `.float64`, `admittedAlgebra` | same as above for `linear` |
| `f32LinearMixedSched` | 962 | 1 | plain `.linear X` as "the f64 side" of a mixed schedule | plain is f32: no mix; use `.typedLinear .f64` (the second half already does) |
| `declaredBSched` family | 1443, 1448, 1460, 1469 | 4 | `A`/`Y` undeclared expect `f64`: baseline accept (`declaredBCorrectSig`, `A: f64`), `B`'s own `.bool` slot, `declaredBWrongSigB` and Variant 2 `dtypeMismatch "A" .f64 .bool` | undeclared `A` is f32; the `f64` `A` signature is a `dtypeMismatch`/`storageKindMismatch`; either declare `A`/`Y` `f64` (then the pins stand, prose changes) or re-pin to `.f32` |

Passing but STALE PROSE for 4b (comments that now say something false; no assertion change needed):
`#guard ... carrying a scatter destination "(an ordinary tensor, or undeclared, both yielding f64 under
dtypeOfDecl)"` (~line 454); the `badDtypeSig` comment "`X` is undeclared in `identitySched` ... `dtypeOfDecl
none = .f64`" (~733; `X` is now declared `f64` by `explicitF64Sched`); `f32MixedDeclOrderSched` doc
"`X` (ordinary, f64)" (~835) and the FW2b comment "(`X` ordinary, `Y` f32)" (~1335); the
`f64PointwiseSched` doc "`X`/`Y` stay undeclared and default to `.f64` (`dtypeOfDecl none = .f64`)"
(~1100, the plan's `axI1` fixture: it now runs on explicit `f64` declarations inherited from
`identitySched`, so it is a binary64 CONTROL; rewrite the prose, no re-pin); the `declaredBSched` doc
"`A` stays undeclared (expects `f64`)" (~1434, part of the residual above).

Site table (`rg -n "ofDenseInputs|prepareEvalPlan|compileToScheduled|TLProgram\.eval|evalScheduled|ScheduledProgram|runPreparedDense"`;
feeds the Task 6 site table). 235 matching lines at the 4a commit: 203 code, 32 comment/docstring
(a line can carry two tokens, so per-token counts below add to more than 235).

| helper / site family | code lines | disposition |
|---|---|---|
| `compileToScheduled` | 2 (`warnBaselinePrepared`, the warnings `run_cmd`) | WRAPPED: `warnProg.explicitF64` |
| `TLProgram.eval` | 0 | not applicable (this module never calls the legacy evaluator) |
| `ScheduledProgram` literals, wrapped (`explicitF64Sched`) | `identitySched`, `contractSched`, `multiReductionSched`, `repeatSched` (+ `repeatSchedRaw`), `repeatPredSched`, `sameShapeSched` (`extraCachedSched` inherits), `orderedTwinSched`, `cacheSchedWith` (`cacheUnsizedSched`), `axShadowSched`, the warnings `combined`, the valid read-rank sibling | WRAPPED |
| `ScheduledProgram` literals, `f64` re-spelled at source | `predSchedWith`, `predRealDestSched`, `scanPredSchedWith`, `rankScanSched`, `plainAxisKindSched` + `validAxisKindSched`, `f32MixedDeclOrderSched`, `f32MixedScatterReluProg` | WRAPPED AT SOURCE (not by the helper: they declare `f32`/predicates or name the plain tensor) |
| `ScheduledProgram` literals declaring `f32` (`f32*Sched`/`f32*Prog`, 17 defs) | all `f32*` fixtures | not needed: homogeneous f32, carrier is `DenseTensor32` or no inputs |
| `ScheduledProgram` literals pinning the default (class ii) | `f32MixedUndeclaredSched`, `plainIdentitySched`, `plainLinearSched`, `f32LinearMixedSched`, `declaredBSched` | NOT wrapped on purpose (F cell), 4b |
| rejection-only literals decided before the storage step | `acceptedSched` (preflight only), `unsizedSched`, `predicateSourceSched`/`predicateAggSched`, `outOfOrderSched`, `selfReadSched`, `dupDeclSched`, `predDupSched`/`predUnreadableSched`/`predTwoStmtSched`, `rank*Sched` rejection fixtures, `scanAxisKindSched`, `dtypeSourceOrderSched` | not needed: error precedes the carrier check, wrapping would change which pass reports it (S cell by nature, every one asserts an exact earlier cause) |
| `ofDenseInputs` (18 code lines) | `identitySig`, `contractSig`, `multiReductionSig`, `repeatSig`, `cacheSig`, `dupDeclSig`, the `topologyInputs`/`scanPredInputs`/`rankInputs`/`axisKindInputs` call sites | not needed: the carrier IS binary64, it is the side held fixed; the program side is declared `f64` |
| `prepareEvalPlan` (90 code lines) | one call per assertion over the schedules above | not needed: arguments are the wrapped/declared schedules (the 15 residual are the class (ii) rows) |
| `evalScheduled` (26 code lines) | the reference leg of `assertPredicateParity`/`assertScanPredicateParity`/`assertReadRankParity`/`assertAxisKindParity` and the valid siblings | not needed beyond the schedules: the valid siblings now evaluate (were `unsupportedDtype ... declared f32`) |
| `runPreparedDense` (3 code lines) | `orderedTwin` run_cmd, `cachePreparedWith 4` run_cmd | not needed (schedule wrapped) |

### Task 4b CompileTest: result (VERIFIED by build and two mutations)

`Eval.Plan.CompileTest` builds green (8519 jobs), 0 failing assertions; all 15 residuals re-pinned, none
class (iii), no change under `leanncd/LeanNCD/`.

## Task 5a ScanCompileTest (VERIFIED classification)

Targeted build `Eval.Plan.ScanCompileTest` after Task 4 (default flipped), before any edit: 101 `^error:
test/Eval/Plan/ScanCompileTest.lean` lines, of which 100 are failing assertions (60 `#guard` "Expression",
40 `run_cmd`/`Except` throws) and the 101st is Lean's `maximum number of errors (100)` marker. The count is
therefore a CAP, not a measurement: the true count is >= 100 (the last reported failure is line 2102 of
2139). Class (iii): none seen. The module is a `prepareEvalPlan`-over-hand-built-`ScheduledProgram` file:
there is no `compileToScheduled`/`TLProgram.eval`; every fixture declares only `iter`/`axis` decls and
leaves every tensor name undeclared, and the carrier is the binary64 `Float` `DenseTensor` env
(`InputSignature.ofDenseInputs`). Every failure is the same shared root cause: undeclared names are now
`.float32`, so the first reached check is `inputSignature.dtypeMismatch`/`storageKindMismatch`.

| group | failing lines (pre-edit) | n | what failed | class | 5a fix |
|---|---|---|---|---|---|
| acceptance fixtures through `withPrepared` (A selfRecur ... S-B two scans; T4.x, T5.3 checked path) | 178-2030 (the "expected acceptance, got inputSignature: ...dtypeMismatch" family) | ~39 | undeclared `X`/`S`/`A`/... vs `Float` carrier | (i) | `explicitF64Sched` in `prepared`/`withPrepared` and the `t4run`/`s6Accept` helper bodies |
| fixture 14 `scratchF32Sched` + its control `scratchUnusedF32Sched` | 372, 380 | 2 | plain `.tensor "S"` is now f32: the mixed f32/f64 point (T f32 beside S f64) is lost | (i) | re-spell `S` `.typedTensor .f64` at source (the point is the T-vs-S mix, not the default) |
| rejection playground `rej`/`rej2` (`rejSched`/`rej2Sched`), `rejScratchNope`, `{ rejSched ... with stmts }` one-offs, `partialSetSched`, `lateNopeSched`, ... | 733-1221 | ~48 | pinned scan/capability cause now preempted by the input-signature dtype check on the undeclared externals `S0`/`X`/`ROW` | (i) | wrap the constructors `rejSched`/`rej2Sched` and the direct `prepareEvalPlan` call sites |
| scatter (`s6*`) rejection family via `s6Cause` and the `s6Schedule` accept helpers | 2043-2102 (+ tail) | ~10 | same | (i) | wrap `s6Schedule` and direct call sites |
| T5.3 differential `t4diff` | the "source (reference) eval failed" family | 5 | `evalScheduled` over the undeclared source schedule: `unsupportedDtype` | (i) | `evalScheduledF64` |

Class (ii): none in the observed failures (the module pins no `dtypeOfDecl`/`stateSigs` of an undeclared
state name; its only dtype pins are explicit `.f64`/`.bool` signature entries of declared-by-the-fixture
state), so 5b has no class (ii) input unless the capped tail hides some. Fixtures that already pass and
stay untouched: the rejection fixtures decided before the carrier check.

### Task 5a ScanCompileTest: result and the 5b input (VERIFIED by targeted build)

`Eval.Plan.ScanCompileTest`: >= 100 failing assertions before (capped; 8514 jobs, one failing), 8 after
(8519 jobs: +5, the added `Eval.ExplicitF64` import's closure incl. `LeanNCD.Eval.Entry`). No class (iii) found.
Lever: one local helper `explicitF64Sched` (the `CompileTest` body: `explicitF64Decls` over
`sched.stmts.flatMap ScanStmt.sourceStmts`, so scan-body state names `X`/`S` are declared too), applied
at `prepared`, `withPrepared`, the `t4run`/`s6Accept`/assert helper bodies, the three constructors
`rejSched`/`rej2Sched`/`s6Schedule`, and the 11 direct `prepareEvalPlan <named sched>` call sites;
`t4diff`'s reference leg uses `evalScheduledF64`; `scratchF32Sched`/`scratchUnusedF32Sched` re-spell plain
`S` as `.typedTensor .f64` at source. Deviation to know for 5b/6: importing `Eval.ExplicitF64` pulls in
`LeanNCD.Eval.Entry`, hence the TL DSL syntax, which makes `bias` a KEYWORD token; every
`{ coeffs := .., bias := .. }` literal in this file (37 lines) is now written `«bias» :=`. Any other test
module that adds that import and builds `AffineMap` literals needs the same.

**Residual failing assertions (the 5b input), 8, all class (i), none class (ii).** Line numbers at the
5a commit. All 8 are rejection fixtures whose pinned error is raised from a MALFORMED LHS of the written
state `S`; `explicitF64Decls` infers `S`'s declaration from its first write, so the inferred declaration
disagrees with the malformed LHS and the source-invariant pass reports `rankMismatch "S" ..` (or, for
the capability fixture, `scatterOrAffineLhs` in place of `multiAxisScatterLhs`) BEFORE the pinned scan
or capability error. Fix is per-fixture (declare `S` by hand with the fixture's intended rank, or declare
only the external `S0`/`X`, and check which pass then reports), not a helper change.

| fixture | lines | pinned cause | observed under the wrapper |
|---|---|---|---|
| partial advancing result (`iterNext axL, iterNext axJ` recur) | 869 | `scan (partialAdvancingResult "sc" "S" 0 2 1)` | `sourceInvariant rankMismatch "S" ..` |
| duplicate context axis (`[axL, axL]`) | 1014 | `scan (duplicateContextAxis "sc" 0 axL.uid)` | not captured (same family) |
| pinned axis not context | 1038 | `scan (pinnedAxisNotContext "sc" "S" 0 axJ.uid)` | `rankMismatch` family |
| duplicate axis in LHS, base | 1052 | `scan (duplicateAxisInLhs "sc" "S" true 0 axL.uid)` | `rankMismatch` family |
| duplicate axis in LHS, recur | 1055 | `scan (duplicateAxisInLhs "sc" "S" false 0 axL.uid)` | `rankMismatch` family |
| inconsistent state rank | 1074 | `scan (inconsistentStateRank "sc" "S" false 0 1 2)` | `rankMismatch "S" 1 2` |
| capability before input validation (`capabilityBeforeInputScatter`, `emptySig`) | 1218, 2149 (duplicate guard) | `capability (multiAxisScatterLhs "S: affine LHS slot")` | `capability (scatterOrAffineLhs "S: affine LHS slot")` |

The per-fixture observed causes come from a temporary `dbgTrace` probe in `rej` (since removed); the
mapping of the seven `rankMismatch`/`scatterOrAffineLhs` lines to individual rows was not captured line
by line, so treat the "observed" column as the family, not a per-line pin. The `scatterOrAffineLhs`
vs `multiAxisScatterLhs` difference should be understood before 5b re-pins anything: it is a different
CAPABILITY constructor for the same scatter once its target name is declared, so check it is not a
production-side classification difference (class (iii)) rather than a test assumption.

Site table (`rg -n "ofDenseInputs|prepareEvalPlan|compileToScheduled|TLProgram\.eval|evalScheduled|ScheduledProgram|runPreparedDense"`;
feeds the Task 6 site table). 101 matching lines at the 5a commit (per-token line counts: `ScheduledProgram`
60, `prepareEvalPlan` 29, `ofDenseInputs` 15, `runPreparedDense` 7, `evalScheduled` 3, `compileToScheduled` 0,
`TLProgram.eval` 0).

| helper / site family | lines | disposition |
|---|---|---|
| `compileToScheduled`, `TLProgram.eval` | 0 | not applicable (hand-built `ScheduledProgram` module) |
| `ScheduledProgram` literals (about 45 named defs, 3 constructors `rejSched`/`rej2Sched`/`s6Schedule`) | 60 | WRAPPED at the consumer (`explicitF64Sched` at each `prepareEvalPlan`/helper call, or in the constructor): the literals themselves stay undeclared on purpose, `scratchF32Sched`/`scratchUnusedF32Sched` re-spelled `S` f64 |
| `prepareEvalPlan` | 29 (3 prose) | WRAPPED: `prepared`, `withPrepared`, the assert helpers, 11 direct sites, `rej`/`rej2`/`s6Cause` via the constructors; 8 fixtures still fail (residual above) |
| `ofDenseInputs` | 15 | not needed: the carrier IS binary64, the side held fixed; the program side is declared `f64` |
| `runPreparedDense` | 7 | not needed beyond the wrapped schedules (the run legs consume prepared plans) |
| `evalScheduled` | 3 | `t4diff` WRAPPED (`evalScheduledF64`); the `scratchThenPlainReadSched` `run_cmd` (line 986) not needed (cyclic-dataflow rejection decided before storage) |

Stale prose lines saying the old default: none found (`rg` for `undeclared|defaults? to|dtypeOfDecl|untyped`
hits only the new helper docstring at line 38 and unrelated "ordinary block slot" uses). Passing fixtures
left alone: every rejection fixture decided before the carrier check.

| residual | re-pin |
|---|---|
| f32 identity control (2) | plain `.tensor` over `f32IdentitySig` pinned `.float32`/`admittedAlgebraF32`; the binary64 control is kept as 2 new assertions on `.typedTensor .f64` over `identitySig` |
| `f32MixedUndeclaredSched` (1) | renamed `f32UndeclaredSched`: f32 `Y` + undeclared `X` is homogeneous, accepted `.float32`. The inverted mismatch is new `f64MixedUndeclaredSched` (declared `f64` `Y` + undeclared f32 `X`): `Y: mixed f32/f64` |
| `plainIdentitySched` (3) | plain pinned equal to `f32IdentityPrepared` (sigs, storageKind) and `.float32`; added plain != `f64` (tensorSigs) |
| `plainLinearSched` (4) | plain `.linear` over `f32LinearSig` equals `linear f32` (sigs, `.float32`, `admittedAlgebraF32`); `linear f64` pinned explicitly (sigs, algebra) and != plain (sigs, storageKind) |
| `f32LinearMixedSched` (1) | renamed `f32LinearPlainXSched`: plain `.linear X` + `linear f32 Y` is homogeneous `.float32`; plain X + `linear f64` Y is the (new) mismatch; the explicit `f64` X + f32 Y rejection is kept |
| `declaredBSched` (4) | `A`/`Y` stay undeclared and now expect `.f32`: signatures `A: f32`, Variant 2 `dtypeMismatch "A" .f32 .bool` |

Stale prose rewritten: lines ~452 (scatter dest), ~733 (`badDtypeSig`), ~850 (`f32MixedDeclOrderSched`), fixture 12 undeclared
comment, ~1148 (`f64PointwiseSched`: now an explicit-`f64` control), ~1383 (FW2b), `declaredBSched` doc.

Mutations (each restored by `git checkout --`, then rebuilt green):
- `dtypeOfDecl` `.tensor`/`.linear`/`none` arms back to `.f64`: CompileTest fails 15 assertions (lines 805, 810, 871,
  912, 917, 918, 920, 990, 991, 992, 1002, 1493, 1498, 1510, 1519), each "did not evaluate to `true`".
- `storageConstraintOfName?` undeclared arm back to `.float64` (Ast.lean): CAUGHT, 5 failures (871
  `f32UndeclaredSched`, 883 `f64MixedUndeclaredSched`, 1493/1498/1510 `declaredBSched`).

## Task 5b ScanCompileTest (VERIFIED by targeted build)

The 8 residual assertions (869, 1014, 1038, 1052, 1055, 1074, 1218, 2149 at `380bffc`) are all rejection
fixtures with a MALFORMED left-hand side of `S`. Probe of the candidate fixes (temporary `#eval`s, removed):

| `S` declaration | partial-advancing / inconsistent-rank / capability fixture result |
|---|---|
| `explicitF64Decls` (first-write rank) | `sourceInvariant rankMismatch "S" ..` |
| hand-declared `tensor f64` at rank 1, 2 or 3 | `rankMismatch "S" 1 2` / `2 1` / `3 1`: NO rank is consistent, because base and recurrence write `S` at different ranks (the malformation is the point) |
| `S` undeclared, `S0`/`X` declared `f64` | `capability (unsupportedDtype "S: mixed f32/f64 storage in one schedule")` |

So no binary64 declaration reaches the pinned error. Fix: these fixtures run UNWRAPPED (every name undeclared,
hence binary32) against a new all-`f32` signature `rejSigF32` (same shapes as `rejSig`) via `rejF32`
(`rejSchedRaw`, the unwrapped body of `rejSched`); the pinned errors are dtype-independent scan/capability
errors and every pin is unchanged. Capability fixture verdict: NOT class (iii). `capabilityBeforeInputScatter`
yields the pinned `multiAxisScatterLhs "S: affine LHS slot"` once `S` is not declared at a wrong rank and
there is no f32/f64 mix (the `scatterOrAffineLhs` seen in 5a came with the wrapper's declared `S`; not isolated further, since the
pinned form is reached again without it and the production code is untouched).
No `LeanNCD/` change.

Added pin (the plan expected a `stateSigs` pin; `stateSigs` is `private` to `Compile.lean` and 5a found none):
the playground with NO declarations compiles against `rejSigF32` and every compiled `tensorSigs` entry, the
scan state's included, is `.f32`.

Mutation (`dtypeOfDecl` `.tensor`/`.linear`/`none` arms back to `.f64`, restored by `git checkout --`): 8 failing
assertions in ScanCompileTest, each "did not evaluate to `true`": the new pin (769), its `rejF32` control (772),
and 6 of the 8 re-homed rejection fixtures (896, 1041, 1065, 1079, 1082, 1101). The two capability fixtures
(the 1218/2149 pair at `380bffc`) are default-insensitive (`emptySig`, capability decided first). Everything else in the module is
explicit `f64` after 5a, hence insensitive to the default by construction.

## Task 6a AdapterTest + Adapter32Test (VERIFIED classification, measured before any edit)

Targeted builds after Task 5 (default flipped), before any edit. Both modules are `run_cmd`/`throwError`
files: each failing `run_cmd` stops at its first throw, so the counts below are failing COMMANDS and a
fixed command may expose later throws inside it (re-measured after the fix). No `maximum number of
errors` cap hit. Total 13 failing, under the ~60 split threshold, so both modules are fixed in this
dispatch. No class (iii): no `storageKindMismatch` in AdapterTest (its all-predicate `predIdentityProg`
run_cmd, the Rule 14 parked item, passes), and the one `storageKindMismatch` in Adapter32Test is an
`InputSignature.ofDenseInputsForDecls` over an undeclared binary64 twin (class (i), not a default of
`deriveStorageKind`).

`Eval.Plan.AdapterTest` (8521 jobs, one failing): 9 failing `run_cmd`, every one
`inputSignature: dtypeMismatch "A" f32 f64` (undeclared names now f32 vs the binary64 `Float` env).

| group | failing lines | n | what failed | class | fix |
|---|---|---|---|---|---|
| `zeroCoeffProg` (round trip incl. unwrapped `TLProgram.eval`; six-fixture batch) | 95, 181 | 2 | undeclared `A`/`B`/`Y` | (i) | `.explicitF64` on the `tlprog!` def |
| `swapProg` | 294 | 1 | same | (i) | same |
| `warnProg` (incl. unwrapped `TLProgram.eval`) | 382 | 1 | same | (i) | same |
| `ScanCompileTest.scratchSched` fixtures (Checks 11, 12) | 454, 486 | 2 | undeclared scan names, carrier f64 | (i) | `ScanCompileTest.explicitF64Sched` at the call sites |
| `scanWarnSched` (incl. unwrapped `evalScheduled`) | 547 | 1 | same | (i) | wrap at the call sites (the public def stays undeclared: `DifferentialTest` reuses it) |
| Check 16 loop over scratch/coupled/multiBase/twoScans | 600 | 1 | same | (i) | wrap `sched` inside the loop |
| `logDomainProg` | 886 | 1 | undeclared `A`/`E` | (i) | `.explicitF64` on the def |

`Eval.Plan.Adapter32Test` (8522 jobs, one failing): 4 failing `run_cmd`, all class (i) in the BINARY64
TWIN legs (the f32 legs declare `tensor f32` and are green).

| failing line | fixture | what failed | class | fix |
|---|---|---|---|---|
| 265 | fixture 7 `warnProgF64`, unwrapped `TLProgram.eval` | undeclared `X`/`Y`: `unsupported dtype: tensor X is declared f32` | (i) | declare `tensor f64 X(i), Y(i, j)` at source |
| 331 | fixture 8 `f64ReductionProg` | plain `tensor B(j), Y()` is f32, `ofDenseInputsForDecls` over the f64 env: `storageKindMismatch` | (i) | `tensor f64 B(j), Y()` at source |
| 647 | fixture 2.10 `expOobProgF64` | undeclared twin vs f64 env: `dtypeMismatch` | (i) | declare `tensor f64 A(i), E(i)` |
| 765 | fixture 4.5 `f64AttnProg` | plain `tensor Q(q, d), K(s, d), A(q, s)` | (i) | `tensor f64 ...` |

Class (ii): none observed. The module pins no `.float64`-default (`dtypeOfDecl`/`storageKind` of an
undeclared name); every dtype pin it makes sits on an explicit `tensor f32` program. The CompileTest
donor (fixture 10) did not fail: Task 4's helper changes held.
