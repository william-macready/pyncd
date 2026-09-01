import LeanNCD.Eval.Plan.Kernel
import LeanNCD.Eval.Plan.Error
import LeanNCD.Eval.Nonlin

/-!
# Nonlinearity thread 4: raw types, checkers, and dense workers

New raw types `RawPointwisePlan` and `RawAxiswisePlan` for the `.pointwise` and `.axiswise`
`PlanStep` cases, with a shared geometry-check helper `checkNonlinIO` and checkers built on it
(Task 1), plus the dense workers `runDensePointwise`/`runDenseAxiswise` (Task 2). These are the
Plan-layer (UID-free, position-based) counterpart to the AST-layer `Nonlin` cases.
-/

namespace LeanNCD.Eval.Plan
open LeanNCD.Eval

-- Manual BEq instances for PointwiseFn and AxiswiseFn, built from their existing DecidableEq.
instance : BEq LeanNCD.PointwiseFn := ⟨fun a b => decide (a = b)⟩
instance : BEq LeanNCD.AxiswiseFn := ⟨fun a b => decide (a = b)⟩

/-- One pointwise (elementwise) nonlinearity operation. -/
structure RawPointwisePlan where
  sourceSlot      : TensorSlot
  destinationSlot : TensorSlot
  shape           : Array Nat
  fn              : LeanNCD.PointwiseFn
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One axiswise (reduction along one axis) nonlinearity operation. `axisPos` is the position
    (0-indexed) of the reduction axis within the tensor's shape. -/
structure RawAxiswisePlan where
  sourceSlot      : TensorSlot
  destinationSlot : TensorSlot
  shape           : Array Nat
  axisPos         : Nat
  fn              : LeanNCD.AxiswiseFn
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Geometry-checking errors for pointwise and axiswise operations. -/
inductive NonlinPlanError
  | slotOutOfRange           (slot : TensorSlot) (tableSize : Nat)
  | dtypeNotAdmitted         (slot : TensorSlot) (dtype : ScalarDType)
  | dtypeMismatch            (destination : ScalarDType) (source : ScalarDType)
  | sourceShapeMismatch      (declared : Array Nat) (signature : Array Nat)
  | destinationShapeMismatch (declared : Array Nat) (signature : Array Nat)
  | axisPositionOutOfRange   (position : Nat) (size : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Evidence that one `RawPointwisePlan` satisfies every local invariant. -/
structure CheckedPointwisePlan where private mk ::
  raw : RawPointwisePlan
  deriving Repr

/-- Evidence that one `RawAxiswisePlan` satisfies every local invariant. -/
structure CheckedAxiswisePlan where private mk ::
  raw : RawAxiswisePlan
  deriving Repr

/-- Shared geometry-check helper for both pointwise and axiswise operations.
    Validates rows 1-7 of §4's case×class table (slot range, dtype, shape agreement).
    Returns the validated source and destination signatures on success. -/
def checkNonlinIO (sigs : Array TensorSignature) (sourceSlot destinationSlot : TensorSlot)
    (shape : Array Nat) : Except NonlinPlanError (TensorSignature × TensorSignature) := do
  let destSig ← match sigs[destinationSlot]? with
    | some s => pure s
    | none => throw (.slotOutOfRange destinationSlot sigs.size)
  let srcSig ← match sigs[sourceSlot]? with
    | some s => pure s
    | none => throw (.slotOutOfRange sourceSlot sigs.size)
  unless destSig.dtype == .f64 do
    throw (.dtypeNotAdmitted destinationSlot destSig.dtype)
  unless srcSig.dtype == .f64 do
    throw (.dtypeNotAdmitted sourceSlot srcSig.dtype)
  unless srcSig.dtype == destSig.dtype do
    throw (.dtypeMismatch destSig.dtype srcSig.dtype)
  unless srcSig.shape == shape do
    throw (.sourceShapeMismatch shape srcSig.shape)
  unless destSig.shape == shape do
    throw (.destinationShapeMismatch shape destSig.shape)
  return (srcSig, destSig)

/-- Validate one pointwise operation against the positional signature table. -/
def checkPointwise (sigs : Array TensorSignature) (p : RawPointwisePlan) :
    Except NonlinPlanError CheckedPointwisePlan := do
  let _ ← checkNonlinIO sigs p.sourceSlot p.destinationSlot p.shape
  return CheckedPointwisePlan.mk p

/-- Validate one axiswise operation against the positional signature table. -/
def checkAxiswise (sigs : Array TensorSignature) (a : RawAxiswisePlan) :
    Except NonlinPlanError CheckedAxiswisePlan := do
  let _ ← checkNonlinIO sigs a.sourceSlot a.destinationSlot a.shape
  unless a.axisPos < a.shape.size do
    throw (.axisPositionOutOfRange a.axisPos a.shape.size)
  return CheckedAxiswisePlan.mk a

/-- Validate the positional store against the single source shape `checkNonlinIO` already validated,
    returning that source tensor. The exact `runDenseAssignAt`/`validateStore` (`Dense.lean`)
    discipline, narrowed to one slot: runtime values are a separate trust boundary from plan
    structure, so this is a value check, not a re-validation of the plan. Without it these workers
    would read `store` through `getD … placeholder` at their call sites and silently apply the
    function to an empty placeholder when a slot is missing or misshapen, rather than failing loud. -/
private def validateNonlinSource (sourceSlot : TensorSlot) (shape : Array Nat)
    (store : Array DenseTensor) : Except PositionalInputError DenseTensor := do
  match store[sourceSlot]? with
  | none => throw (.missingSlot sourceSlot store.size)
  | some d =>
      unless d.shape == shape.toList do
        throw (.shapeMismatch sourceSlot shape d.shape)
      unless d.data.size == shape.toList.foldl (· * ·) 1 do
        throw (.storageMismatch sourceSlot d.shape d.data.size)
      pure d

/-- Run one checked pointwise operation. Re-validates its source slot against the checked shape
    first (`validateNonlinSource`) — same runtime trust boundary `runDenseAssignAt` honors — then
    reuses `PointwiseFn.apply` (`LeanNCD.Eval.Nonlin`) — no new math. -/
def runDensePointwise (c : CheckedPointwisePlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  let src ← validateNonlinSource c.raw.sourceSlot c.raw.shape store
  return c.raw.fn.apply src

/-- Run one checked axiswise operation. Re-validates its source slot against the checked shape first
    (`validateNonlinSource`) — same runtime trust boundary `runDenseAssignAt` honors. `[]`/`none` for
    `axisUids`/`mask?`: a checked `RawAxiswisePlan` can never carry a mask or axis-UID — the
    Plan-layer `TensorSignature` is UID-free by design (§3). Reuses `AxiswiseFn.apply`
    (`LeanNCD.Eval.Nonlin`) — no new math. -/
def runDenseAxiswise (c : CheckedAxiswisePlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  let src ← validateNonlinSource c.raw.sourceSlot c.raw.shape store
  return c.raw.fn.apply c.raw.axisPos [] none src

/-- Temporary spike adapter: apply an optional UID-free positional mask, supplied separately from
    `RawAxiswisePlan`, against each entry's complete local output coordinate. -/
def applyPositionalAxiswise (evalMask : Array Int → PosBoolExpr → Except ε Bool)
    (a : RawAxiswisePlan) (mask? : Option PosBoolExpr)
    (src : DenseTensor) : Except ε DenseTensor := do
  let decisions ← DenseTensor.allCoords src.shape |>.mapM (fun c =>
    match mask? with
    | none => pure (c, true)
    | some mask => (evalMask (c.map Int.ofNat).toArray mask).map (fun b => (c, b)))
  return a.fn.applyIncluded a.axisPos
    (fun c => (decisions.find? (fun d => d.1 == c)).map (·.2) |>.getD false) src

end LeanNCD.Eval.Plan
