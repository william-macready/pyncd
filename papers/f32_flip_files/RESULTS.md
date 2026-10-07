# f32 flip slice 2 prototype: results

Branch `f32-flip-slice2-proto` from main 574a633. Budget: stopped OVER the ~55 tool-call budget
(about 85 calls); S4 not started. Everything below marked VERIFIED was confirmed by a targeted build
of the named module(s) with the flip applied.

## Per step

- S1 DONE, VERIFIED (`lake build LeanNCD`: 8546 jobs, success). 4 production edits:
  `storageConstraintOfDecl` (.tensor/.linear -> .float32) and `storageConstraintOfName?` (none arm
  -> .float32) in leanncd/LeanNCD/DSL/Ast.lean; `dtypeOfDecl` (.tensor/.linear/none -> .f32,
  .axis/.iter stay .f64) in leanncd/LeanNCD/Eval/Plan/Signature.lean; scan-state fallback
  `stateDtypes.getD si .f32` at the `stateSigs` definition (Compile.lean ~line 1410; the identical
  sites at ~1225 and the `.f64` at ~1742 were left alone). Docstrings/comments updated.
- S2a DONE, VERIFIED. `DSL.Pipeline.StructuralTest`: untyped+predicate pin (b) now `.float32`; new (b')
  pins explicit `f64`+predicate = `.float64`; the mixed-name test (d) spells B and C `.typedTensor .f64`
  so it still produces `.error "B"`. Bool-only (c) unchanged (`.float64`).
- S2b DONE, VERIFIED. `DSL.ComplexElementTypeTest`: new `neighbour` helper = complex -> f64 plus
  explicit f64 declarations for the undeclared names A, B, Y, X, S (undeclared would be f32 and make
  the neighbour a mixed schedule). First attempt (A/B/Y only) failed ONLY on the `evalScan` cells (the
  scan reads X and writes S), found via a temporary `#eval neighbourFailures` (removed). Rejection
  assertions untouched; `rejectionFailures == []` and `neighbourFailures == []` hold.
- S3 PARTIAL. Classification table: papers/f32_flip_files/plan_modules.md. Measured failing
  assertions with the flip: SignatureTest 8, CompileTest 71, ScanCompileTest 101, NonlinCompileTest 48,
  ScatterCompileTest 48, Scatter32OracleTest 1 (total 277). NonlinCompileTest FIXED and VERIFIED green
  (class i, via `explicitF64`). SignatureTest read only partially. The other four modules were not
  examined beyond their counts. No class (iii) item seen.
- S4 NOT DONE. No full build was run; the 3 never-built modules (AdapterTest, Adapter32Test,
  DifferentialTest) are unmeasured; DifferentialTest 3832/3832 and the scan corpus 17/17 are NOT
  re-verified under the flip.
- S5 DONE (this file, patches).

## Decisions taken

- Only the `stateSigs` fallback (not 1225/1742) was flipped, as instructed.
- Stale prose changed only where it stated the old default: three docstrings and one comment block
  in `prepareEvalPlan` (its "UNDECLARED external is a real f64 tensor ... f32 graph reading one is
  mixed" sentence, inverted to f32/f64).
- StructuralTest: kept intent by pinning the new default AND adding the explicit-f64 pin.
- ComplexElementTypeTest: the neighbour declares f64 explicitly instead of weakening the acceptance
  check to tolerate `.other`.
- NonlinCompileTest: fixed at the helper level with the landed lever, not per fixture.

## Remaining work (task list)

1. SignatureTest (leanncd/test/Eval/Plan/SignatureTest.lean): (ii) update pins at lines 90, 99, 109,
   113 to `.f32`/`.float32` (and say `.typedTensor .f64` is the f64 spelling, already pinned at 96-97,
   106, 110); line 45: either pin the `storageKindMismatch` error for an undeclared name over the Float
   carrier or declare `.typedTensor .f64 "X" []`; line 137 (`gn2Prog` clone): declare f64 or use
   `explicitF64`; lines 426 (not examined) and 443 (`ofDenseInputs32ForDecls [.tensor "X" []]` now
   accepted).
2. ScatterCompileTest (48; 4 sites, likely one helper), Scatter32OracleTest (1, line 241),
   CompileTest (71), ScanCompileTest (101): apply the Nonlin recipe (`import Eval.ExplicitF64`,
   `open LeanNCD.Eval.ExplicitF64`, wrap `compileToScheduled`/`TLProgram.eval` helper bodies with
   `p.explicitF64`, hand-built `ScheduledProgram` decls via `explicitF64Decls decls [stmts]`; plain
   `tensor`/`linear` decls re-spelled `f64` AT SOURCE per the lever's decision). Examine each for
   class (ii) pins and class (iii) before assuming (i).
3. S4: full build with everything applied; measure AdapterTest (unwrapped `TLProgram.eval` on
   zeroCoeffProg/warnProg, `evalScheduled` on scanWarnSched), Adapter32Test (plain `tensor` decls),
   DifferentialTest (Gen programs, Gen's guard checks `p.explicitF64` but the test runs `p`);
   re-verify `accepted == 3832` and scan corpus 17/17.

## Evidence

Logs live in the scratchpad (not committed): s1.log, s2.log, s2b.log, s3_sig.log, s3_rest.log,
s3_nonlin.log, s3_nonlin2.log. The log of record is papers/f32_flip_slice2_log.md.
