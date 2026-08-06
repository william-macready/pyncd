import LeanNCD.Eval.Plan.Kernel

/-!
# Wave C plan-layer diagnostics (C2)

Closed families, no `unsupported String` escape hatch — the same discipline Wave E applied to
`EvalError`. `PlanError` is structural/semantic invalidity of a raw operation, raised by the
checker before execution. `PositionalInputError` is a runtime value-boundary failure raised by a
worker: the plan was valid, the tensors supplied to it were not.
-/

namespace LeanNCD.Eval.Plan

/-- A raw `AssignPlan` violates a local invariant. Indices identify the offending term/factor so a
    failure is locatable without re-deriving it. -/
inductive PlanError
  | slotOutOfRange           (slot : TensorSlot) (tableSize : Nat)
  | dtypeNotAdmitted         (slot : TensorSlot) (dtype : ScalarDType)
  | dtypeMismatch            (destination : ScalarDType) (source : ScalarDType)
  | affineRankMismatch       (termIndex : Nat) (factorIndex : Nat) (expected : Nat) (actual : Nat)
  | affineWidthMismatch      (termIndex : Nat) (factorIndex : Nat) (expected : Nat) (actual : Nat)
  | sourceShapeMismatch      (termIndex : Nat) (factorIndex : Nat)
                             (declared : Array Nat) (signature : Array Nat)
  | positionsNotPartition    (termIndex : Nat)
  | outputProjectionMismatch (termIndex : Nat) (projected : Array Nat) (declared : Array Nat)
  | constDtypeMismatch       (dtype : ScalarDType) (const : ScalarConst)
  | algebraNotAdmitted       (algebra : ContractionAlgebra)
  | policyNotAdmitted        (policy : OutOfBoundsPolicy)
  | destinationShapeMismatch (declared : Array Nat) (signature : Array Nat)
  | versionNotAdmitted       (version : Nat)
  | numericModeNotAdmitted   (mode : NumericMode)
  | duplicateInputSlot       (slot : TensorSlot)
  | inputSlotsNotOrdered     (atIndex : Nat)
  | inputSlotOverwritten     (slot : TensorSlot) (nodeIndex : Nat)
  | duplicateDestination     (slot : TensorSlot) (firstNode : Nat) (secondNode : Nat)
  | missingProduction        (slot : TensorSlot)
  | invalidForwardRead       (nodeIndex termIndex factorIndex : Nat) (slot : TensorSlot)
  | nodeError                (nodeIndex : Nat) (cause : PlanError)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A checked plan met a positional tensor store that does not conform to the shapes the checker
    validated. Distinct from `PlanError`: the plan is fine, the runtime values are not. -/
inductive PositionalInputError
  | missingSlot     (slot : TensorSlot) (provided : Nat)
  | shapeMismatch   (slot : TensorSlot) (expected : Array Nat) (actual : List Nat)
  | storageMismatch (slot : TensorSlot) (shape : List Nat) (dataSize : Nat)
  | arityMismatch   (expected : Nat) (actual : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

end LeanNCD.Eval.Plan
