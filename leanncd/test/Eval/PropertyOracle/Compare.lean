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
  | .scatterWriteOutOfRange na oa sa, .scatterWriteOutOfRange nb ob sb =>
      decide (na = nb ∧ oa = ob ∧ sa = sb)
  | .unsupportedScatterNonlin a, .unsupportedScatterNonlin b => decide (a = b)
  | .unsupportedRecurMorphism sa na, .unsupportedRecurMorphism sb nb =>
      decide (sa = sb ∧ na = nb)
  | .invalidScanNode a, .invalidScanNode b => decide (a = b)
  | .unsupportedDtype a, .unsupportedDtype b => decide (a = b)
  | .baseWriteNotAtBoundary sa ta ia, .baseWriteNotAtBoundary sb tb ib =>
      decide (sa = sb ∧ ta = tb ∧ ia = ib)
  | .baseWritesOverlap sa ta fa ga, .baseWritesOverlap sb tb fb gb =>
      decide (sa = sb ∧ ta = tb ∧ fa = fb ∧ ga = gb)
  | .duplicateStateResult sa ta fa ga, .duplicateStateResult sb tb fb gb =>
      decide (sa = sb ∧ ta = tb ∧ fa = fb ∧ ga = gb)
  | .duplicateScratchProducer sa na fa ga, .duplicateScratchProducer sb nb fb gb =>
      decide (sa = sb ∧ na = nb ∧ fa = fb ∧ ga = gb)
  | .inconsistentStateExtent sa ta da ea aa, .inconsistentStateExtent sb tb db eb ab =>
      decide (sa = sb ∧ ta = tb ∧ da = db ∧ ea = eb ∧ aa = ab)
  | .scanWriteRowNotAdmitted sa na ba ia da, .scanWriteRowNotAdmitted sb nb bb ib db =>
      decide (sa = sb ∧ na = nb ∧ ba = bb ∧ ia = ib ∧ da = db)
  | .stateReadInBaseBlock sa ia ta, .stateReadInBaseBlock sb ib tb =>
      decide (sa = sb ∧ ia = ib ∧ ta = tb)
  | .unmarkedReductionAxis ta pa, .unmarkedReductionAxis tb pb => decide (ta = tb ∧ pa = pb)
  | .multipleMarkedReductionAxes ta fa sa, .multipleMarkedReductionAxes tb fb sb =>
      decide (ta = tb ∧ fa = fb ∧ sa = sb)
  | .inputIsDefined a, .inputIsDefined b => decide (a = b)
  -- Catches only cross-constructor pairs: every `EvalError` constructor has its own arm above, and
  -- the completeness check at the end of this file fails the build when a new one has none. Without
  -- an arm, two equal instances would silently compare unequal.
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

-- f32 Task 1, fixture 16: the new `EvalError.unsupportedDtype` constructor needs its OWN arm above
-- the catch-all. Without one it falls through to `| _, _ => false`, so two identical rejections
-- compare UNEQUAL and the oracle reports a spurious divergence; with an arm that ignores the name,
-- two rejections naming different tensors compare EQUAL and a real divergence is hidden. Both
-- directions are asserted.
#guard evalErrorEq (.unsupportedDtype "X") (.unsupportedDtype "X")
#guard ! evalErrorEq (.unsupportedDtype "X") (.unsupportedDtype "Y")
#guard evalAgreesOn [] (failed (.unsupportedDtype "X")) (failed (.unsupportedDtype "X"))
#guard ! evalAgreesOn [] (failed (.unsupportedDtype "X")) (failed (.unsupportedDtype "Y"))

-- B6: the out-of-range scatter write. Without its arm the `_ => false` catch-all makes two EQUAL
-- rejections compare unequal (a spurious oracle divergence); with an arm that ignored a field, two
-- different out-of-range writes would compare equal. Both directions, each field.
#guard evalErrorEq (.scatterWriteOutOfRange "Out" [-1] [0]) (.scatterWriteOutOfRange "Out" [-1] [0])
#guard ! evalErrorEq (.scatterWriteOutOfRange "Out" [-1] [0]) (.scatterWriteOutOfRange "Q" [-1] [0])
#guard ! evalErrorEq (.scatterWriteOutOfRange "Out" [-1] [0]) (.scatterWriteOutOfRange "Out" [5] [0])
#guard ! evalErrorEq (.scatterWriteOutOfRange "Out" [-1] [0]) (.scatterWriteOutOfRange "Out" [-1] [1])
#guard evalAgreesOn [] (failed (.scatterWriteOutOfRange "Out" [5] [0]))
  (failed (.scatterWriteOutOfRange "Out" [5] [0]))

-- The remaining `EvalError` constructors (the scan-structure refusals, the reduction-marker
-- refusals and `inputIsDefined`). Each needs its OWN arm in `evalErrorEq`: without one the
-- `| _, _ => false` catch-all makes two EQUAL errors compare unequal (a spurious oracle
-- divergence), and an arm that ignores a field makes two different errors compare equal. So every
-- row below is a base error and one variant per field, each differing in that field alone.
private def fieldVariants : List (EvalError × List EvalError) := [
  (.baseWriteNotAtBoundary "s" "S" 1,
    [.baseWriteNotAtBoundary "t" "S" 1, .baseWriteNotAtBoundary "s" "T" 1,
     .baseWriteNotAtBoundary "s" "S" 2]),
  (.baseWritesOverlap "s" "S" 0 1,
    [.baseWritesOverlap "t" "S" 0 1, .baseWritesOverlap "s" "T" 0 1,
     .baseWritesOverlap "s" "S" 2 1, .baseWritesOverlap "s" "S" 0 2]),
  (.duplicateStateResult "s" "S" 0 1,
    [.duplicateStateResult "t" "S" 0 1, .duplicateStateResult "s" "T" 0 1,
     .duplicateStateResult "s" "S" 2 1, .duplicateStateResult "s" "S" 0 2]),
  (.duplicateScratchProducer "s" "T" 0 1,
    [.duplicateScratchProducer "t" "T" 0 1, .duplicateScratchProducer "s" "U" 0 1,
     .duplicateScratchProducer "s" "T" 2 1, .duplicateScratchProducer "s" "T" 0 2]),
  (.inconsistentStateExtent "s" "S" 0 3 4,
    [.inconsistentStateExtent "t" "S" 0 3 4, .inconsistentStateExtent "s" "T" 0 3 4,
     .inconsistentStateExtent "s" "S" 1 3 4, .inconsistentStateExtent "s" "S" 0 5 4,
     .inconsistentStateExtent "s" "S" 0 3 5]),
  (.scanWriteRowNotAdmitted "s" "T" true 1 0,
    [.scanWriteRowNotAdmitted "t" "T" true 1 0, .scanWriteRowNotAdmitted "s" "U" true 1 0,
     .scanWriteRowNotAdmitted "s" "T" false 1 0, .scanWriteRowNotAdmitted "s" "T" true 2 0,
     .scanWriteRowNotAdmitted "s" "T" true 1 1]),
  (.stateReadInBaseBlock "s" 1 "S",
    [.stateReadInBaseBlock "t" 1 "S", .stateReadInBaseBlock "s" 2 "S",
     .stateReadInBaseBlock "s" 1 "T"]),
  (.unmarkedReductionAxis "Y" 0,
    [.unmarkedReductionAxis "Z" 0, .unmarkedReductionAxis "Y" 1]),
  (.multipleMarkedReductionAxes "Y" 0 1,
    [.multipleMarkedReductionAxes "Z" 0 1, .multipleMarkedReductionAxes "Y" 2 1,
     .multipleMarkedReductionAxes "Y" 0 2]),
  (.inputIsDefined "X", [.inputIsDefined "Y"])]

#guard fieldVariants.all fun (e, vs) =>
  evalErrorEq e e && vs.all fun v => !evalErrorEq e v && !evalErrorEq v e
-- Distinct constructors never agree, whichever order.
#guard fieldVariants.zipIdx.all fun ((e, _), i) =>
  fieldVariants.zipIdx.all fun ((f, _), j) => i == j || !evalErrorEq e f

-- Completeness: a new `EvalError` constructor fails this build until it is added to the list
-- below, which is the prompt to give it an `evalErrorEq` arm (and a `fieldVariants` row if it is
-- not one of the twelve constructors the guards above already pin individually).
open Lean Elab Command in
run_cmd do
  let info ← getConstInfoInduct ``LeanNCD.Eval.EvalError
  let covered : List Name :=
    [``EvalError.compile, ``EvalError.shape, ``EvalError.unknownTensor, ``EvalError.invalidSeed,
     ``EvalError.unaryDomain, ``EvalError.invalidNormAxis, ``EvalError.scatterCollision,
     ``EvalError.scatterWriteOutOfRange, ``EvalError.unsupportedScatterNonlin,
     ``EvalError.unsupportedRecurMorphism, ``EvalError.invalidScanNode,
     ``EvalError.unsupportedDtype, ``EvalError.baseWriteNotAtBoundary,
     ``EvalError.baseWritesOverlap, ``EvalError.duplicateStateResult,
     ``EvalError.duplicateScratchProducer, ``EvalError.inconsistentStateExtent,
     ``EvalError.scanWriteRowNotAdmitted, ``EvalError.stateReadInBaseBlock,
     ``EvalError.unmarkedReductionAxis, ``EvalError.multipleMarkedReductionAxes,
     ``EvalError.inputIsDefined]
  for c in info.ctors do
    unless covered.contains c do
      throwError "EvalError.{c} has no evalErrorEq coverage: add an arm in Compare.lean, a fieldVariants row, and list it here"
  unless info.ctors.length == covered.length do
    throwError "evalErrorEq coverage list names a constructor EvalError no longer has"

end LeanNCD.PropertyOracle
