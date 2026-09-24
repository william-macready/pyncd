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

**Both carriers (F32-B Task 3).** Checked evidence records the storage kind it was checked FOR, the
pattern `CheckedAssignPlan` already follows. One private core per checker, parameterized by that
kind, backs two public siblings: `checkPointwise`/`checkAxiswise` (binary64, today's behavior
exactly) and `checkPointwiseF32`/`checkAxiswiseF32` (native binary32, admitting `.f32` slots where
the binary64 checkers admit `.f64`). Each of the four workers — `runDensePointwise`/
`runDenseAxiswise` over a `DenseTensor` store and `runDensePointwise32`/`runDenseAxiswise32` over a
`DenseTensor32` store — checks the evidence's storage kind as its FIRST statement, before the store
is looked at, so wrong-precision evidence reports `storageKindMismatch` rather than whatever the
store happens to be missing.
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

/-- Evidence that one `RawPointwisePlan` satisfies every local invariant, for the storage kind it
    records. `storageKind` is the carrier the checker admitted the slots FOR (`checkPointwise`:
    `.float64`; `checkPointwiseF32`: `.float32`), exactly as `CheckedAssignPlan` records its own, so
    each worker can refuse evidence checked for the other carrier. -/
structure CheckedPointwisePlan where private mk ::
  raw         : RawPointwisePlan
  storageKind : LeanNCD.StorageKind
  deriving Repr

/-- Evidence that one `RawAxiswisePlan` satisfies every local invariant, for the storage kind it
    records (see `CheckedPointwisePlan`). -/
structure CheckedAxiswisePlan where private mk ::
  raw         : RawAxiswisePlan
  storageKind : LeanNCD.StorageKind
  deriving Repr

/-- The one real dtype a nonlinearity slot may carry, per graph carrier. -/
private def nonlinDtypeFor : LeanNCD.StorageKind → ScalarDType
  | .float64 => .f64
  | .float32 => .f32

/-- Shared geometry-check core for both pointwise and axiswise operations, for one carrier `kind`.
    Validates rows 1-7 of §4's case×class table (slot range, dtype, shape agreement), where the one
    admitted dtype is `nonlinDtypeFor kind`. Returns the validated source and destination
    signatures on success. -/
private def checkNonlinIOCore (kind : LeanNCD.StorageKind) (sigs : Array TensorSignature)
    (sourceSlot destinationSlot : TensorSlot) (shape : Array Nat) :
    Except NonlinPlanError (TensorSignature × TensorSignature) := do
  let destSig ← match sigs[destinationSlot]? with
    | some s => pure s
    | none => throw (.slotOutOfRange destinationSlot sigs.size)
  let srcSig ← match sigs[sourceSlot]? with
    | some s => pure s
    | none => throw (.slotOutOfRange sourceSlot sigs.size)
  unless destSig.dtype == nonlinDtypeFor kind do
    throw (.dtypeNotAdmitted destinationSlot destSig.dtype)
  unless srcSig.dtype == nonlinDtypeFor kind do
    throw (.dtypeNotAdmitted sourceSlot srcSig.dtype)
  unless srcSig.dtype == destSig.dtype do
    throw (.dtypeMismatch destSig.dtype srcSig.dtype)
  unless srcSig.shape == shape do
    throw (.sourceShapeMismatch shape srcSig.shape)
  unless destSig.shape == shape do
    throw (.destinationShapeMismatch shape destSig.shape)
  return (srcSig, destSig)

/-- The binary64 geometry check, `checkNonlinIOCore .float64`: both slots must be `.f64`. Kept
    public with its pre-binary32 behavior exactly. -/
def checkNonlinIO (sigs : Array TensorSignature) (sourceSlot destinationSlot : TensorSlot)
    (shape : Array Nat) : Except NonlinPlanError (TensorSignature × TensorSignature) :=
  checkNonlinIOCore .float64 sigs sourceSlot destinationSlot shape

private def checkPointwiseCore (kind : LeanNCD.StorageKind) (sigs : Array TensorSignature)
    (p : RawPointwisePlan) : Except NonlinPlanError CheckedPointwisePlan := do
  let _ ← checkNonlinIOCore kind sigs p.sourceSlot p.destinationSlot p.shape
  return CheckedPointwisePlan.mk p kind

/-- Validate one pointwise operation against the positional signature table, for binary64. -/
def checkPointwise (sigs : Array TensorSignature) (p : RawPointwisePlan) :
    Except NonlinPlanError CheckedPointwisePlan :=
  checkPointwiseCore .float64 sigs p

/-- Validate one pointwise operation for native binary32: the sibling of `checkPointwise` through
    the same core, admitting `.f32` slots and recording `.float32`. -/
def checkPointwiseF32 (sigs : Array TensorSignature) (p : RawPointwisePlan) :
    Except NonlinPlanError CheckedPointwisePlan :=
  checkPointwiseCore .float32 sigs p

private def checkAxiswiseCore (kind : LeanNCD.StorageKind) (sigs : Array TensorSignature)
    (a : RawAxiswisePlan) : Except NonlinPlanError CheckedAxiswisePlan := do
  let _ ← checkNonlinIOCore kind sigs a.sourceSlot a.destinationSlot a.shape
  unless a.axisPos < a.shape.size do
    throw (.axisPositionOutOfRange a.axisPos a.shape.size)
  -- Mask width: each positional mask leaf must span exactly the local output basis (`shape.size`).
  -- A DISTINCT check from `checkAssign`'s Iverson-FACTOR width check — this one reports the mask.
  match a.mask with
  | none => pure ()
  | some m => match m.affineWidths.find? (· != a.shape.size) with
      | some w => throw (.maskWidthMismatch a.shape.size w)
      | none => pure ()
  return CheckedAxiswisePlan.mk a kind

/-- Validate one axiswise operation against the positional signature table, for binary64. -/
def checkAxiswise (sigs : Array TensorSignature) (a : RawAxiswisePlan) :
    Except NonlinPlanError CheckedAxiswisePlan :=
  checkAxiswiseCore .float64 sigs a

/-- Validate one axiswise operation for native binary32: the sibling of `checkAxiswise` through the
    same core, admitting `.f32` slots and recording `.float32`. -/
def checkAxiswiseF32 (sigs : Array TensorSignature) (a : RawAxiswisePlan) :
    Except NonlinPlanError CheckedAxiswisePlan :=
  checkAxiswiseCore .float32 sigs a

/-- Validate the positional store against the single source shape `checkNonlinIO` already validated,
    returning that source tensor. Generic over the carrier, so the workers of both precisions share
    one copy. The exact `runDenseAssignAt`/`validateStore` (`Dense.lean`) discipline, narrowed to one
    slot: runtime values are a separate trust boundary from plan structure, so this is a value
    check, not a re-validation of the plan. Without it these workers would read `store` through
    `getD … placeholder` at their call sites and silently apply the function to an empty placeholder
    when a slot is missing or misshapen, rather than failing loud. -/
private def validateNonlinSourceOf {α : Type} (sourceSlot : TensorSlot) (shape : Array Nat)
    (store : Array (DenseTensorOf α)) : Except PositionalInputError (DenseTensorOf α) := do
  match store[sourceSlot]? with
  | none => throw (.missingSlot sourceSlot store.size)
  | some d =>
      unless d.shape == shape.toList do
        throw (.shapeMismatch sourceSlot shape d.shape)
      unless d.data.size == shape.toList.foldl (· * ·) 1 do
        throw (.storageMismatch sourceSlot d.shape d.data.size)
      pure d

/-- The axiswise workers' shared mask handling, one copy for both carriers. Re-checks the mask's (if
    any) leaf widths against the local output basis with the SAME cheap symbolic check
    `checkAxiswise` already ran (`affineWidths` vs `shape.size`, not a per-coordinate `evalPosBool`
    pass), mapping a mismatch into `PositionalInputError.predicateWidthMismatch` so this path fails
    loud rather than the fail-open `included? = true` a raw `.toOption.getD true` would give — an
    unreachable-in-practice error (`checkAxiswise`'s mask width check forbids the only failure
    mode), guarded here at leaf-count cost instead of coordinate-count cost. Once validated, builds
    the full-coordinate `included?` predicate from the mask (a `none` mask includes every
    coordinate, so an unmasked reduction is byte-for-byte the pre-mask behavior). -/
private def axiswiseIncluded (a : RawAxiswisePlan) :
    Except PositionalInputError (List Nat → Bool) := do
  match a.mask with
  | none => pure ()
  | some m => match m.affineWidths.find? (· != a.shape.size) with
      | some w => throw (.predicateWidthMismatch a.shape.size w)
      | none => pure ()
  return fun coord => match a.mask with
    | none => true
    | some m => (evalPosBool (coord.map (Int.ofNat ·)) m).toOption.getD true

/-- Run one checked pointwise operation over a binary64 store. **The storage-kind guard is the FIRST
    statement, before the store is looked at:** `.float32` evidence (from `checkPointwiseF32`) is
    refused as `storageKindMismatch .float64 .float32` even when the store is empty, rather than
    reporting the store's `missingSlot`. Then re-validates its source slot against the checked shape
    (`validateNonlinSourceOf`) — same runtime trust boundary `runDenseAssignAt` honors — and reuses
    `PointwiseFn.apply` (`LeanNCD.Eval.Nonlin`) — no new math. -/
def runDensePointwise (c : CheckedPointwisePlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  unless c.storageKind == .float64 do
    throw (.storageKindMismatch .float64 c.storageKind)
  let src ← validateNonlinSourceOf c.raw.sourceSlot c.raw.shape store
  return c.raw.fn.apply src

/-- Run one checked pointwise operation over a native binary32 store: the sibling of
    `runDensePointwise`, guarded `.float32` as its FIRST statement, sharing its source validation,
    and applying the native binary32 formula `PointwiseFn.apply32` — never binary64 math with a
    widen/narrow. -/
def runDensePointwise32 (c : CheckedPointwisePlan) (store : Array DenseTensor32) :
    Except PositionalInputError DenseTensor32 := do
  unless c.storageKind == .float32 do
    throw (.storageKindMismatch .float32 c.storageKind)
  let src ← validateNonlinSourceOf c.raw.sourceSlot c.raw.shape store
  return c.raw.fn.apply32 src

/-- Run one checked axiswise operation over a binary64 store. **The storage-kind guard is the FIRST
    statement, before the store is looked at**, exactly as in `runDensePointwise`. Then
    re-validates its source slot against the checked shape (`validateNonlinSourceOf`), builds the
    mask's `included?` predicate (`axiswiseIncluded`), and hands both to `AxiswiseFn.applyCore` —
    the SAME single softmax/normalize/L2 implementation the SOURCE `AxiswiseFn.apply` uses,
    differing only in which predicate language it evaluates. -/
def runDenseAxiswise (c : CheckedAxiswisePlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  unless c.storageKind == .float64 do
    throw (.storageKindMismatch .float64 c.storageKind)
  let src ← validateNonlinSourceOf c.raw.sourceSlot c.raw.shape store
  let included? ← axiswiseIncluded c.raw
  return c.raw.fn.applyCore c.raw.axisPos included? src

/-- Run one checked axiswise operation over a native binary32 store: the sibling of
    `runDenseAxiswise`, guarded `.float32` as its FIRST statement, sharing its source validation and
    mask handling, and applying the native binary32 row engine `AxiswiseFn.applyCore32`. -/
def runDenseAxiswise32 (c : CheckedAxiswisePlan) (store : Array DenseTensor32) :
    Except PositionalInputError DenseTensor32 := do
  unless c.storageKind == .float32 do
    throw (.storageKindMismatch .float32 c.storageKind)
  let src ← validateNonlinSourceOf c.raw.sourceSlot c.raw.shape store
  let included? ← axiswiseIncluded c.raw
  return c.raw.fn.applyCore32 c.raw.axisPos included? src

end LeanNCD.Eval.Plan
