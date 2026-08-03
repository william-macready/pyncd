import LeanNCD.Eval.Eval
import LeanNCD.DSL.Ast

namespace LeanNCD.PropertyOracle
open LeanNCD.Eval

/-- Exact tensor equality: same shape and bit-equal Float data. -/
def denseEq (x y : DenseTensor) : Bool :=
  x.shape == y.shape && x.data == y.data

/-- The tensor names a program produces (LHS of every `.assign`), in order, deduped. -/
def producedNames (p : LeanNCD.TLProgram) : List String :=
  (p.stmts.filterMap (fun | LeanNCD.Stmt.assign nm _ _ => some nm | _ => none)).eraseDups

/-- Structural evaluator-error equality for the property oracle. `EvalError` cannot derive
    `DecidableEq` because Lean's `Float` does not provide it, so the one floating payload is
    compared with the same `BEq Float` used for tensor data and every other payload is compared
    by its closed type's decidable equality. -/
def evalErrorEq : EvalError → EvalError → Bool
  | .compile a, .compile b => decide (a = b)
  | .shape a, .shape b => decide (a = b)
  | .unknownTensor sa na, .unknownTensor sb nb => decide (sa = sb ∧ na = nb)
  | .invalidSeed na ua va ba, .invalidSeed nb ub vb bb =>
      decide (na = nb ∧ ua = ub ∧ va = vb ∧ ba = bb)
  | .unaryDomain oa va ca, .unaryDomain ob vb cb =>
      decide (oa = ob ∧ ca = cb) && va == vb
  | .invalidNormAxis a, .invalidNormAxis b => decide (a = b)
  | .scatterCollision na oa fa sa, .scatterCollision nb ob fb sb =>
      decide (na = nb ∧ oa = ob ∧ fa = fb ∧ sa = sb)
  | .unsupportedScatterNonlin a, .unsupportedScatterNonlin b => decide (a = b)
  | .unsupportedRecurMorphism sa na, .unsupportedRecurMorphism sb nb =>
      decide (sa = sb ∧ na = nb)
  | .invalidScanNode a, .invalidScanNode b => decide (a = b)
  | _, _ => false

/-- Two complete evaluation outcomes agree on a set of names and on their diagnostics. Successful
    reports must have equal warning lists plus `denseEq`-equal produced tensors (extra environment
    keys — e.g. materialization intermediates — are ignored). Failures must have structurally equal
    fatal errors and warning lists, so source transformations cannot silently change diagnostics. -/
def evalAgreesOn (names : List String)
    (a b : Except EvalFailure EvalReport) : Bool :=
  match a, b with
  | .ok ra, .ok rb =>
      decide (ra.warnings = rb.warnings) &&
      names.all (fun n => match ra.env[n]?, rb.env[n]? with
        | some ta, some tb => denseEq ta tb
        | _, _ => false)
  | .error fa, .error fb =>
      evalErrorEq fa.error fb.error && decide (fa.warnings = fb.warnings)
  | _, _ => false

-- TESTS (fire on build):
private def t2 : DenseTensor := ⟨[2], #[1.0, 2.0]⟩
private def t2' : DenseTensor := ⟨[2], #[1.0, 2.0]⟩
private def t2diff : DenseTensor := ⟨[2], #[1.0, 9.0]⟩
private def t3 : DenseTensor := ⟨[3], #[1.0, 2.0, 3.0]⟩
private def okReport (env : Std.HashMap String DenseTensor)
    (warnings : List EvalWarning := []) : Except EvalFailure EvalReport :=
  .ok { env, warnings }
private def failed (error : EvalError) (warnings : List EvalWarning := []) :
    Except EvalFailure EvalReport :=
  .error { error, warnings }
#guard denseEq t2 t2'            -- equal
#guard ! denseEq t2 t2diff       -- differing data
#guard ! denseEq t2 t3           -- differing shape
#guard evalAgreesOn ["Y"]
  (okReport (({} : Std.HashMap String DenseTensor).insert "Y" t2))
  (okReport (({} : Std.HashMap String DenseTensor).insert "Y" t2'))
#guard ! evalAgreesOn ["Y"]
  (okReport (({} : Std.HashMap String DenseTensor).insert "Y" t2))
  (okReport (({} : Std.HashMap String DenseTensor).insert "Y" t2diff))
-- extra keys ignored (materialization adds intermediates):
#guard evalAgreesOn ["Y"]
  (okReport (({} : Std.HashMap String DenseTensor).insert "Y" t2))
  (okReport (((({} : Std.HashMap String DenseTensor).insert "Y" t2').insert "T1" t3)))
#guard ! evalAgreesOn ["Y"]
  (okReport (({} : Std.HashMap String DenseTensor).insert "Y" t2))
  (failed (.unknownTensor .gather "boom"))
#guard evalAgreesOn [] (failed (.unknownTensor .gather "e")) (failed (.unknownTensor .gather "e"))
#guard ! evalAgreesOn []
  (failed (.unaryDomain .log 0.0 (EvalContext.mk "A" [0])))
  (failed (.unaryDomain .log 0.0 (EvalContext.mk "B" [0])))
#guard ! evalAgreesOn []
  (okReport {} [.paddedAccess "X[i]" 3 2])
  (okReport {})
#guard ! evalAgreesOn []
  (failed (.unknownTensor .gather "e") [.paddedAccess "X[i]" 3 2])
  (failed (.unknownTensor .gather "e"))

end LeanNCD.PropertyOracle
