import LeanNCD.Eval.Plan.Kernel
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

/-- Run one checked pointwise operation. Reuses `PointwiseFn.apply` (`LeanNCD.Eval.Nonlin`) — no
    new math. -/
def runDensePointwise (c : CheckedPointwisePlan) (src : DenseTensor) : DenseTensor :=
  c.raw.fn.apply src

/-- Run one checked axiswise operation. `[]`/`none` for `axisUids`/`mask?`: a checked
    `RawAxiswisePlan` can never carry a mask or axis-UID — the Plan-layer `TensorSignature` is
    UID-free by design (§3). Reuses `AxiswiseFn.apply` (`LeanNCD.Eval.Nonlin`) — no new math. -/
def runDenseAxiswise (c : CheckedAxiswisePlan) (src : DenseTensor) : DenseTensor :=
  c.raw.fn.apply c.raw.axisPos [] none src

end LeanNCD.Eval.Plan
