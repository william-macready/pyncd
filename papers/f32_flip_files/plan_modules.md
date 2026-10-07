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
