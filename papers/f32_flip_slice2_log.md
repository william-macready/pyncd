# f32 flip slice 2 prototype log

- S1: applied the 4 one-line flips (Ast storageConstraintOfDecl tensor/linear + storageConstraintOfName? undeclared, Signature dtypeOfDecl tensor/linear/none, Compile.lean line 1410 stateSigs fallback) plus the old-default docstrings/comment. CLAIMED only, targeted build of LeanNCD pending (next entry).
- S1 VERIFIED: targeted `lake build LeanNCD` with the flip: "Build completed successfully (8546 jobs)".
- S2a (StructuralTest): CLAIMED edit only (b: untyped -> .float32, new b': explicit f64 -> .float64, d: B/C spelled f64); build pending.
- S2a VERIFIED: targeted build of DSL.Pipeline.StructuralTest succeeded with the flip.
- S2b first attempt FAILED (A/B/Y neighbour): `#eval neighbourFailures` showed only the `evalScan` cells (scan reads undeclared X, S => mixed after the flip). Fix: neighbour also declares X and S f64. VERIFIED: targeted build of DSL.ComplexElementTypeTest succeeded (rejectionFailures == [] and neighbourFailures == [] both hold; complex rejection assertions untouched).
