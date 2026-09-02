import LeanNCD.Eval.Plan.Kernel
import LeanNCD.Eval.Plan.Coordinates
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
    (0-indexed) of the reduction axis within the tensor's shape. `mask`, when present, is a UID-free
    positional predicate over the LOCAL output coordinate (its non-seeded output basis) whose leaves
    are each `shape.size` wide (`checkAxiswise`'s mask width check); a coordinate the mask evaluates
    TRUE is INCLUDED in the reduction, one FALSE is excluded. There is no mask-axis-UID field: the
    positional width is exactly `shape.size`. -/
structure RawAxiswisePlan where
  sourceSlot      : TensorSlot
  destinationSlot : TensorSlot
  shape           : Array Nat
  axisPos         : Nat
  fn              : LeanNCD.AxiswiseFn
  mask            : Option PosBoolExpr := none
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Geometry-checking errors for pointwise and axiswise operations. -/
inductive NonlinPlanError
  | slotOutOfRange           (slot : TensorSlot) (tableSize : Nat)
  | dtypeNotAdmitted         (slot : TensorSlot) (dtype : ScalarDType)
  | dtypeMismatch            (destination : ScalarDType) (source : ScalarDType)
  | sourceShapeMismatch      (declared : Array Nat) (signature : Array Nat)
  | destinationShapeMismatch (declared : Array Nat) (signature : Array Nat)
  | axisPositionOutOfRange   (position : Nat) (size : Nat)
  | maskWidthMismatch        (expected : Nat) (actual : Nat)
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
  -- Mask width: each positional mask leaf must span exactly the local output basis (`shape.size`).
  -- A DISTINCT check from `checkAssign`'s Iverson-FACTOR width check — this one reports the mask.
  match a.mask with
  | none => pure ()
  | some m => match m.affineWidths.find? (· != a.shape.size) with
      | some w => throw (.maskWidthMismatch a.shape.size w)
      | none => pure ()
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
    (`validateNonlinSource`) — same runtime trust boundary `runDenseAssignAt` honors. Before building
    the `included?` predicate, re-checks the mask's (if any) leaf widths against the local output
    basis with the SAME cheap symbolic check `checkAxiswise` already ran (`affineWidths` vs
    `shape.size`, not a per-coordinate `evalPosBool` pass), mapping a mismatch into
    `PositionalInputError.predicateWidthMismatch` so this path fails loud rather than the fail-open
    `included? = true` a raw `.toOption.getD true` would give — an unreachable-in-practice error
    (`checkAxiswise`'s mask width check forbids the only failure mode), guarded here at leaf-count
    cost instead of coordinate-count cost. Once validated, builds the full-coordinate `included?`
    predicate from the mask (a `none` mask includes every coordinate, so an unmasked reduction is
    byte-for-byte the pre-mask behavior) and hands it to `AxiswiseFn.applyCore` — the SAME single
    softmax/normalize/L2 implementation the SOURCE `AxiswiseFn.apply` uses, differing only in which
    predicate language it evaluates. -/
def runDenseAxiswise (c : CheckedAxiswisePlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  let src ← validateNonlinSource c.raw.sourceSlot c.raw.shape store
  match c.raw.mask with
  | none => pure ()
  | some m => match m.affineWidths.find? (· != c.raw.shape.size) with
      | some w => throw (.predicateWidthMismatch c.raw.shape.size w)
      | none => pure ()
  let included? : List Nat → Bool := fun coord =>
    match c.raw.mask with
    | none => true
    | some m => (evalPosBool (coord.map (Int.ofNat ·)) m).toOption.getD true
  return c.raw.fn.applyCore c.raw.axisPos included? src

end LeanNCD.Eval.Plan
