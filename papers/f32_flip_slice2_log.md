# f32 flip slice 2 prototype log

- S1: applied the 4 one-line flips (Ast storageConstraintOfDecl tensor/linear + storageConstraintOfName? undeclared, Signature dtypeOfDecl tensor/linear/none, Compile.lean line 1410 stateSigs fallback) plus the old-default docstrings/comment. CLAIMED only, targeted build of LeanNCD pending (next entry).
- S1 VERIFIED: targeted `lake build LeanNCD` with the flip: "Build completed successfully (8546 jobs)".
- S2a (StructuralTest): CLAIMED edit only (b: untyped -> .float32, new b': explicit f64 -> .float64, d: B/C spelled f64); build pending.
- S2a VERIFIED: targeted build of DSL.Pipeline.StructuralTest succeeded with the flip.
- S2b first attempt FAILED (A/B/Y neighbour): `#eval neighbourFailures` showed only the `evalScan` cells (scan reads undeclared X, S => mixed after the flip). Fix: neighbour also declares X and S f64. VERIFIED: targeted build of DSL.ComplexElementTypeTest succeeded (rejectionFailures == [] and neighbourFailures == [] both hold; complex rejection assertions untouched).
- S3 measured (VERIFIED by targeted builds with the flip): failing assertions SignatureTest 8, CompileTest 71, ScanCompileTest 101, NonlinCompileTest 48, ScatterCompileTest 48, Scatter32OracleTest 1. Table in papers/f32_flip_files/plan_modules.md.
- S3 NonlinCompileTest: explicitF64 at the compile/eval helpers and axiswiseSched took 48 -> 12 -> 0 failures. VERIFIED green by targeted build of Eval.Plan.NonlinCompileTest (two commits).
- Stopped over the tool-call budget. NOT DONE: SignatureTest/CompileTest/ScanCompileTest/ScatterCompileTest/Scatter32OracleTest fixes, all of S4 (no full build; Adapter/Adapter32/DifferentialTest unmeasured, 3832/3832 and 17/17 NOT re-verified). See RESULTS.md.
- Plan authored from artifacts (no builds): leanncd/docs/superpowers/plans/2026-10-04-f32-flip-slice2.md plus papers/f32_flip_slice2_record.md; patch application onto 574a633 and all test-module counts remain unverified until execution.
