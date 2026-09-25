import LeanNCD.Eval.Plan.Nonlin

/-!
# Nonlinearity thread 4 checker tests

Hand-built signature tables and fixtures, mirroring `GraphDenseTest.lean`'s style:
one minimal 2-slot table with `shape := #[2]`, fixtures per §4's case×class table rows,
mutation-tested except `dtypeMismatch` (structurally unreachable under the current single-valued
f64-only dtype vocabulary — same as `checkAssign`'s own precedent).
-/

namespace LeanNCD.Eval.Plan.NonlinCheckTest
open LeanNCD.Eval.Plan

/-- Baseline signature table: two f64 slots, each shaped #[2]. -/
def baselineSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }, { shape := #[2], dtype := .f64 } ]

/-- Baseline passing pointwise plan. -/
def baselinePointwise : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], fn := .relu }

/-- Baseline passing axiswise plan. -/
def baselineAxiswise : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], axisPos := 0, fn := .softmax }

-- ============================================================================
-- Passing baselines
-- ============================================================================

#guard (checkPointwise baselineSigs baselinePointwise).isOk
#guard (checkAxiswise baselineSigs baselineAxiswise).isOk

-- ============================================================================
-- Row 1: sourceSlot in range (slotOutOfRange)
-- ============================================================================

def pointwiseSourceSlotOob : RawPointwisePlan :=
  { sourceSlot := 99, destinationSlot := 1, shape := #[2], fn := .relu }

def axisiwiseSourceSlotOob : RawAxiswisePlan :=
  { sourceSlot := 99, destinationSlot := 1, shape := #[2], axisPos := 0, fn := .softmax }

#guard match checkPointwise baselineSigs pointwiseSourceSlotOob with
  | .error (.slotOutOfRange 99 2) => true
  | _ => false

#guard match checkAxiswise baselineSigs axisiwiseSourceSlotOob with
  | .error (.slotOutOfRange 99 2) => true
  | _ => false

-- ============================================================================
-- Row 2: destinationSlot in range (slotOutOfRange)
-- ============================================================================

def pointwiseDestSlotOob : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 99, shape := #[2], fn := .relu }

def axisiwiseDestSlotOob : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 99, shape := #[2], axisPos := 0, fn := .softmax }

#guard match checkPointwise baselineSigs pointwiseDestSlotOob with
  | .error (.slotOutOfRange 99 2) => true
  | _ => false

#guard match checkAxiswise baselineSigs axisiwiseDestSlotOob with
  | .error (.slotOutOfRange 99 2) => true
  | _ => false

-- ============================================================================
-- Row 3: source dtype == .f64 (dtypeNotAdmitted)
-- ============================================================================

def sourceBoolSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .bool }, { shape := #[2], dtype := .f64 } ]

def pointwiseSourceBoolDtype : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], fn := .relu }

def axisiwiseSourceBoolDtype : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], axisPos := 0, fn := .softmax }

#guard match checkPointwise sourceBoolSigs pointwiseSourceBoolDtype with
  | .error (.dtypeNotAdmitted 0 .bool) => true
  | _ => false

#guard match checkAxiswise sourceBoolSigs axisiwiseSourceBoolDtype with
  | .error (.dtypeNotAdmitted 0 .bool) => true
  | _ => false

-- ============================================================================
-- Row 4: destination dtype == .f64 (dtypeNotAdmitted)
-- ============================================================================

def destBoolSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }, { shape := #[2], dtype := .bool } ]

def pointwiseDestBoolDtype : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], fn := .relu }

def axisiwiseDestBoolDtype : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], axisPos := 0, fn := .softmax }

#guard match checkPointwise destBoolSigs pointwiseDestBoolDtype with
  | .error (.dtypeNotAdmitted 1 .bool) => true
  | _ => false

#guard match checkAxiswise destBoolSigs axisiwiseDestBoolDtype with
  | .error (.dtypeNotAdmitted 1 .bool) => true
  | _ => false

-- ============================================================================
-- Row 5: source dtype == destination dtype (dtypeMismatch)
-- NO FIXTURE — structurally unreachable: both guards above must pass
-- (both dtypes == .f64) before this check runs, making them trivially equal.
-- Left as an inline code-review check that the guard exists.
-- ============================================================================

-- ============================================================================
-- Row 6: source shape == declared shape (sourceShapeMismatch)
-- ============================================================================

def sourceShapeMismatchSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }, { shape := #[3], dtype := .f64 } ]

def pointwiseSourceShapeMismatch : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[3], fn := .relu }

def axisiwiseSourceShapeMismatch : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[3], axisPos := 0, fn := .softmax }

#guard match checkPointwise sourceShapeMismatchSigs pointwiseSourceShapeMismatch with
  | .error (.sourceShapeMismatch _ _) => true
  | _ => false

#guard match checkAxiswise sourceShapeMismatchSigs axisiwiseSourceShapeMismatch with
  | .error (.sourceShapeMismatch _ _) => true
  | _ => false

-- ============================================================================
-- Row 7: destination shape == declared shape (destinationShapeMismatch)
-- ============================================================================

def destShapeMismatchSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[2], dtype := .f64 } ]

def pointwiseDestShapeMismatch : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[3], fn := .relu }

def axisiwiseDestShapeMismatch : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[3], axisPos := 0, fn := .softmax }

#guard match checkPointwise destShapeMismatchSigs pointwiseDestShapeMismatch with
  | .error (.destinationShapeMismatch _ _) => true
  | _ => false

#guard match checkAxiswise destShapeMismatchSigs axisiwiseDestShapeMismatch with
  | .error (.destinationShapeMismatch _ _) => true
  | _ => false

-- ============================================================================
-- Row 8: axisPos < shape.size (axisPositionOutOfRange — axiswise only)
-- ============================================================================

def axisPositionOobSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }, { shape := #[2], dtype := .f64 } ]

def axisiwiseAxisPositionOob : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], axisPos := 2, fn := .softmax }

#guard match checkAxiswise axisPositionOobSigs axisiwiseAxisPositionOob with
  | .error (.axisPositionOutOfRange _ _) => true
  | _ => false

-- ============================================================================
-- Row 9: rank-0 (scalar) shape
-- ============================================================================

-- Rank-0 pointwise passes (harmless — elementwise map over a 1-element array).
def rank0PointwiseSigs : Array TensorSignature :=
  #[ { shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 } ]

def rank0Pointwise : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[], fn := .relu }

#guard (checkPointwise rank0PointwiseSigs rank0Pointwise).isOk

-- Rank-0 axiswise with axisPos := 0 is rejected by row 8's own guard (0 < 0 is false).
def rank0Axiswise : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[], axisPos := 0, fn := .softmax }

#guard match checkAxiswise rank0PointwiseSigs rank0Axiswise with
  | .error (.axisPositionOutOfRange _ _) => true
  | _ => false

-- ============================================================================
-- Row 10: mask leaf width == shape.size (maskWidthMismatch — axiswise only)
-- A DISTINCT check from the Iverson-FACTOR width check in `checkAssign`: this one lives on the
-- axiswise plan and reports the MASK, via its own `maskWidthMismatch` constructor.
-- ============================================================================

/-- A width-2 mask over the `#[2]`-shaped baseline: `coord·[0] + 0 = 0` (always true). Both leaves
    are width 1 = `shape.size`, so `checkAxiswise` admits it. -/
def wellSizedMask : PosBoolExpr :=
  .rel .eq (.affine ⟨#[0], 0⟩) (.affine ⟨#[0], 0⟩)

def axiswiseWellSizedMask : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], axisPos := 0, fn := .softmax
  , mask := some wellSizedMask }

#guard (checkAxiswise baselineSigs axiswiseWellSizedMask).isOk

/-- A mask whose FIRST leaf is width 3, over the `#[2]`-shaped (`shape.size = 1`) baseline. The
    checker must report the mask leaf's width mismatch, not any factor's. -/
def badWidthMask : PosBoolExpr :=
  .rel .eq (.affine ⟨#[0,0,0], 0⟩) (.affine ⟨#[0], 0⟩)

def axiswiseMaskWidthMismatch : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], axisPos := 0, fn := .softmax
  , mask := some badWidthMask }

#guard match checkAxiswise baselineSigs axiswiseMaskWidthMismatch with
  | .error (.maskWidthMismatch 1 3) => true
  | _ => false

-- ============================================================================
-- Mutation verification (development-time verification activity, not a test)
-- ============================================================================

-- Each guard in checkNonlinIO (rows 1-7) and checkAxiswise (row 8) was verified
-- load-bearing by removing it transiently during development, confirming the
-- corresponding fixture failed with the correct error, then restoring and
-- confirming all fixtures passed again. The Row-N assertions above provide
-- permanent proof that each guard is necessary; the transient removal steps are
-- complete. Row 5 (dtypeMismatch) is not mutation-tested — no fixture can reach
-- it given today's single-valued f64-only dtype vocabulary (same as
-- checkAssign's own precedent).

-- ============================================================================
-- F32-B Task 3: the binary32 checkers `checkPointwiseF32`/`checkAxiswiseF32`
-- ============================================================================

/-- Retag every `.f64` signature `.f32`, leaving `.bool` alone — the row sweep's one edit. -/
def retag32 (sigs : Array TensorSignature) : Array TensorSignature :=
  sigs.map fun s => if s.dtype == .f64 then { s with dtype := .f32 } else s

def storagePw : Except NonlinPlanError CheckedPointwisePlan → Option LeanNCD.StorageKind
  | .ok c => some c.storageKind | .error _ => none

def storageAx : Except NonlinPlanError CheckedAxiswisePlan → Option LeanNCD.StorageKind
  | .ok c => some c.storageKind | .error _ => none

-- Fixture 3.1: the retagged baseline is accepted by the binary32 checkers, as `.float32` evidence.
#guard storagePw (checkPointwiseF32 (retag32 baselineSigs) baselinePointwise)
  == some LeanNCD.StorageKind.float32
#guard storageAx (checkAxiswiseF32 (retag32 baselineSigs) baselineAxiswise)
  == some LeanNCD.StorageKind.float32

-- Control: the binary64 checkers on the untouched baseline record `.float64`, so the binary32
-- acceptance is not an implementation that stamps one kind on everything.
#guard storagePw (checkPointwise baselineSigs baselinePointwise) == some LeanNCD.StorageKind.float64
#guard storageAx (checkAxiswise baselineSigs baselineAxiswise) == some LeanNCD.StorageKind.float64

-- Fixture 3.2: the row sweep. Every row fixture above, `.f64` retagged `.f32`, through the binary32
-- checkers, gives the same constructor and payload (exact payloads here, where rows 6-8 above
-- match with wildcards).

-- Rows 1-2: slot range, both kinds.
#guard match checkPointwiseF32 (retag32 baselineSigs) pointwiseSourceSlotOob with
  | .error (.slotOutOfRange 99 2) => true
  | _ => false
#guard match checkAxiswiseF32 (retag32 baselineSigs) axisiwiseSourceSlotOob with
  | .error (.slotOutOfRange 99 2) => true
  | _ => false
#guard match checkPointwiseF32 (retag32 baselineSigs) pointwiseDestSlotOob with
  | .error (.slotOutOfRange 99 2) => true
  | _ => false
#guard match checkAxiswiseF32 (retag32 baselineSigs) axisiwiseDestSlotOob with
  | .error (.slotOutOfRange 99 2) => true
  | _ => false

-- Rows 3-4: a Boolean source / destination is still refused at its own slot.
#guard match checkPointwiseF32 (retag32 sourceBoolSigs) pointwiseSourceBoolDtype with
  | .error (.dtypeNotAdmitted 0 .bool) => true
  | _ => false
#guard match checkAxiswiseF32 (retag32 sourceBoolSigs) axisiwiseSourceBoolDtype with
  | .error (.dtypeNotAdmitted 0 .bool) => true
  | _ => false
#guard match checkPointwiseF32 (retag32 destBoolSigs) pointwiseDestBoolDtype with
  | .error (.dtypeNotAdmitted 1 .bool) => true
  | _ => false
#guard match checkAxiswiseF32 (retag32 destBoolSigs) axisiwiseDestBoolDtype with
  | .error (.dtypeNotAdmitted 1 .bool) => true
  | _ => false

-- Rows 6-7: shape.
#guard match checkPointwiseF32 (retag32 sourceShapeMismatchSigs) pointwiseSourceShapeMismatch with
  | .error (.sourceShapeMismatch #[3] #[2]) => true
  | _ => false
#guard match checkAxiswiseF32 (retag32 sourceShapeMismatchSigs) axisiwiseSourceShapeMismatch with
  | .error (.sourceShapeMismatch #[3] #[2]) => true
  | _ => false
#guard match checkPointwiseF32 (retag32 destShapeMismatchSigs) pointwiseDestShapeMismatch with
  | .error (.destinationShapeMismatch #[3] #[2]) => true
  | _ => false
#guard match checkAxiswiseF32 (retag32 destShapeMismatchSigs) axisiwiseDestShapeMismatch with
  | .error (.destinationShapeMismatch #[3] #[2]) => true
  | _ => false

-- Row 8: axis position.
#guard match checkAxiswiseF32 (retag32 axisPositionOobSigs) axisiwiseAxisPositionOob with
  | .error (.axisPositionOutOfRange 2 1) => true
  | _ => false

-- Row 10: mask width.
#guard match checkAxiswiseF32 (retag32 baselineSigs) axiswiseMaskWidthMismatch with
  | .error (.maskWidthMismatch 1 3) => true
  | _ => false

-- Block 6's extra row: an `f64` source in a direct binary32 check is refused at the SOURCE slot (the
-- destination guard ran first and passed), for both kinds.
def f64SourceSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f32 } ]
def sigmoid3 : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[3], fn := .sigmoid }

#guard match checkPointwiseF32 f64SourceSigs sigmoid3 with
  | .error (.dtypeNotAdmitted 0 .f64) => true
  | _ => false
#guard match checkAxiswiseF32 f64SourceSigs { baselineAxiswise with shape := #[3] } with
  | .error (.dtypeNotAdmitted 0 .f64) => true
  | _ => false

-- The legacy binary64 entries were not widened: on the retagged baseline they refuse the binary32
-- DESTINATION (checked first), `dtypeNotAdmitted 1 .f32`.
#guard match checkPointwise (retag32 baselineSigs) baselinePointwise with
  | .error (.dtypeNotAdmitted 1 .f32) => true
  | _ => false
#guard match checkAxiswise (retag32 baselineSigs) baselineAxiswise with
  | .error (.dtypeNotAdmitted 1 .f32) => true
  | _ => false

-- Fixture 3.3: the evidence constructors stay private, so evidence carrying a storage kind can come
-- only from a checker. Only observable ACROSS modules — inside `Nonlin.lean` the private
-- constructor is visible.
#check_failure (⟨baselinePointwise, .float32⟩ : CheckedPointwisePlan)
#check_failure (⟨baselineAxiswise, .float32⟩ : CheckedAxiswisePlan)

end LeanNCD.Eval.Plan.NonlinCheckTest
