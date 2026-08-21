import LeanNCD.Eval.Plan.Nonlin

/-!
# Wave C C2 nonlinearity checker tests

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

end LeanNCD.Eval.Plan.NonlinCheckTest
