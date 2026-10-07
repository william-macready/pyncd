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
