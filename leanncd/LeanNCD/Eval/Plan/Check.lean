import LeanNCD.Eval.Plan.Error
import LeanNCD.Eval.Plan.Graph

/-!
# Wave C local checked construction (C2)

`checkAssign` is the only way to obtain a `CheckedAssignPlan`. Its constructor is `private mk ::`
— NOT a bare `structure … where private`, which compiles but leaves the anonymous constructor
public and silently defeats the boundary. Field projections remain public under `private mk ::`
(construction is blocked, reading is not), which is the intended design: build only through the
checker, read freely.

Graph availability and production order are deliberately NOT checked here — they are not local
properties. `checkPlan` (C3) adds them.
-/

namespace LeanNCD.Eval.Plan

/-- Evidence that one `AssignPlan` satisfies every local invariant. -/
structure CheckedAssignPlan where private mk ::
  raw : AssignPlan
  deriving Repr

/-- Trusted accessor for the validated payload. -/
def CheckedAssignPlan.plan (c : CheckedAssignPlan) : AssignPlan := c.raw

/-- Wave C admits exactly one algebra: real sum-product with binary64 identities. -/
def admittedAlgebra : ContractionAlgebra :=
  { factorOp := .mul, factorId := .f64 (Float.toBits 1.0)
  , reduceOp := .add, reduceId := .f64 (Float.toBits 0.0) }

/-- The extents this term projects onto the output, in `outputPos` order. -/
def TermPlan.outputProjection (t : TermPlan) : Array Nat :=
  t.outputPos.filterMap (fun p => t.iterationShape[p]?)

/-- The extents this term projects onto the surrounding context, in `contextPos` order. -/
def TermPlan.contextProjection (t : TermPlan) : Array Nat :=
  t.contextPos.filterMap (fun p => t.iterationShape[p]?)

/-- `contextPos ++ outputPos ++ reductionPos` must be a disjoint partition of every iteration-basis
    position.
    Checked by sorting the concatenation and comparing against `List.range`, which catches
    duplicates, omissions, and out-of-range positions in one comparison. -/
def TermPlan.positionsPartition (t : TermPlan) : Bool :=
  let all := (t.contextPos ++ t.outputPos ++ t.reductionPos).toList
  all.length == t.iterationShape.size && all.mergeSort (· ≤ ·) == List.range t.iterationShape.size

def constMatchesDtype : ScalarDType → ScalarConst → Bool
  | .f64,  .f64 _  => true
  | .f32,  .f32 _  => true
  | .bool, .bool _ => true
  | _, _ => false

/-- Validate one operation against the positional signature table. -/
def checkAssign (sigs : Array TensorSignature) (a : AssignPlan) :
    Except PlanError CheckedAssignPlan := do
  let destSig ← match sigs[a.destinationSlot]? with
    | some s => pure s
    | none => throw (.slotOutOfRange a.destinationSlot sigs.size)
  unless destSig.dtype == .f64 do
    throw (.dtypeNotAdmitted a.destinationSlot destSig.dtype)
  unless destSig.shape == a.outputShape do
    throw (.destinationShapeMismatch a.outputShape destSig.shape)
  unless a.algebra == admittedAlgebra do throw (.algebraNotAdmitted a.algebra)
  unless constMatchesDtype destSig.dtype a.algebra.factorId do
    throw (.constDtypeMismatch destSig.dtype a.algebra.factorId)
  unless constMatchesDtype destSig.dtype a.algebra.reduceId do
    throw (.constDtypeMismatch destSig.dtype a.algebra.reduceId)
  for h : ti in [0 : a.terms.size] do
    let t := a.terms[ti]
    unless t.positionsPartition do throw (.positionsNotPartition ti)
    unless t.outputProjection == a.outputShape do
      throw (.outputProjectionMismatch ti t.outputProjection a.outputShape)
    unless t.contextProjection == a.contextShape do
      throw (.contextProjectionMismatch ti t.contextProjection a.contextShape)
    for h2 : fi in [0 : t.factors.size] do
      let f := t.factors[fi]
      let srcSig ← match sigs[f.sourceSlot]? with
        | some s => pure s
        | none => throw (.slotOutOfRange f.sourceSlot sigs.size)
      unless srcSig.dtype == .f64 do throw (.dtypeNotAdmitted f.sourceSlot srcSig.dtype)
      unless srcSig.dtype == destSig.dtype do
        throw (.dtypeMismatch destSig.dtype srcSig.dtype)
      unless f.sourceShape == srcSig.shape do
        throw (.sourceShapeMismatch ti fi f.sourceShape srcSig.shape)
      unless f.oobPolicy == .zeroPad do throw (.policyNotAdmitted f.oobPolicy)
      unless f.map.coeffs.size == f.sourceShape.size && f.map.bias.size == f.sourceShape.size do
        throw (.affineRankMismatch ti fi f.sourceShape.size f.map.coeffs.size)
      for row in f.map.coeffs do
        unless row.size == t.iterationShape.size do
          throw (.affineWidthMismatch ti fi t.iterationShape.size row.size)
  return CheckedAssignPlan.mk a

-- `CheckedEvalPlan`/`checkPlan` used to live here (C3), but now that the outer graph can contain a
-- `.scan` step, both relocated to `EvalPlan.lean` — the only module that can see both the local
-- checker here and `Scan.lean`'s `checkScanPlan` without a circular import. See `EvalPlan.lean`.

end LeanNCD.Eval.Plan
