import LeanNCD.Eval.Plan.Kernel
import LeanNCD.Eval.Error

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

/-- Wave C capability rejection (proposal §3.1/§3.2): which construct in the initial scan-free `f64`
    fragment boundary a source `ScheduledProgram` falls outside of, with the source-level context
    (statement/decl name, or a short description) that failed. Ported from C0's test-only
    `PlanContract.Classification` category names (`test/Eval/Plan/ContractTest.lean`) into a real,
    closed error type a real function can throw — no `unsupported : String` escape hatch (§3.2). -/
inductive CapabilityError
  | scanNode             (context : String)  -- ScanStmt.scan / .scanPre
  | scatterOrAffineLhs   (context : String)  -- scatter statements, affine LHS slots
  | unsupportedLhsSlot   (context : String)  -- freeNorm, iterAt, iterNext
  | unsupportedNonlin    (context : String)  -- pointwise/axiswise nonlinearities
  | maskOrPredicate      (context : String)  -- masks, predicates, Iverson factors
  | unaryFactor          (context : String)
  | unsupportedAgg       (context : String)  -- max/min aggregation
  | booleanOutput        (context : String)
  | unsupportedDtype     (context : String)  -- any dtype other than the declared f64 mode
  | dynamicShape         (context : String)  -- backend- or value-dependent shapes
  | recurrenceOrCallback (context : String)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A required signature is missing, malformed, or incompatible with the scheduled declarations
    (§5.5). Checked for every name in `sched.extNames` — by construction (`resolveDecls`,
    `Structural.lean`), every such name is read somewhere, so no separate "read before production"
    filter is needed here. -/
inductive InputSignatureError
  | missingSignature (name : String)
  | dtypeNotAdmitted (name : String) (dtype : ScalarDType)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- §5.5's sketch, verified as-is. Does NOT derive `Repr`: `ShapeError` (an existing sibling type)
    has no `Repr` instance — confirmed by observing the actual `synthInstanceFailed` error, not
    assumed — and `Repr` derivation requires every constructor's payload to support it, unlike
    `DecidableEq`/`Inhabited`, which don't have that all-or-nothing requirement the same way. -/
inductive PlanCompileCause
  | inputSignature (cause : InputSignatureError)
  | capability     (cause : CapabilityError)
  | shape          (cause : ShapeError)
  | invalidPlan    (cause : PlanError)
  deriving DecidableEq, BEq, Inhabited

/-- Same finding applies here: `EvalWarning` also has no `Repr`, so this likewise derives
    `DecidableEq, BEq, Inhabited` but not `Repr`. `#guard`-based equality testing is unaffected —
    `DecidableEq`/`BEq` are exactly what `==` needs, and both derive cleanly. -/
structure PlanCompileFailure where
  cause    : PlanCompileCause
  warnings : List EvalWarning
  deriving DecidableEq, BEq, Inhabited

/-- Everything `pack` can detect wrong with a `PreparedPlan.bindings.requiredInputs` array and the
    caller-supplied `env` it is asked to resolve against `plan.plan.raw.inputSlots`. The three
    "structural" constructors (`missingRequiredBinding`/`duplicateRequiredBinding`/
    `extraRequiredBinding`) are about `requiredInputs` itself failing to be a clean bijection onto
    `raw.inputSlots`; the two "runtime" constructors (`missingEnvBinding`/`shapeMismatch`/
    `storageMismatch`) are about the concrete tensor `env` supplies once a name IS resolved.
    "Extra" is about a `requiredInputs` entry naming a slot the plan doesn't need — NOT about `env`
    carrying unrelated extra names, which `unpack`'s own contract says is fine, not an error. -/
inductive InputBindingError
  | missingRequiredBinding   (slot : TensorSlot)
  | duplicateRequiredBinding (slot : TensorSlot) (firstName secondName : String)
  | extraRequiredBinding     (slot : TensorSlot) (name : String)
  | missingEnvBinding        (name : String)
  | shapeMismatch            (name : String) (slot : TensorSlot) (expected : Array Nat) (actual : List Nat)
  | storageMismatch          (name : String) (slot : TensorSlot) (shape : List Nat) (dataSize : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The runtime counterpart of `PlanCompileCause`: a `PreparedPlan` failed either at the named
    binding boundary (`pack`) or inside the positional worker (`runDensePlan`). Both
    `InputBindingError` and `PositionalInputError` derive `Repr` (unlike `PlanCompileCause`'s
    `ShapeError` sibling) — verified, not assumed by analogy — so `PlanRunCause` derives `Repr` too. -/
inductive PlanRunCause
  | binding   (cause : InputBindingError)
  | execution (cause : PositionalInputError)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Failure type of `runPreparedDense`. `warnings` is always `plan.warnings` (the preparation
    warnings `PreparedPlan` already carried) — never re-derived — so a binding or execution failure
    never silently drops an earlier shape-inference warning. NOT `Repr`: `EvalWarning` has none, so
    `List EvalWarning` blocks a derived `Repr` here exactly as it did for `PlanCompileFailure`. -/
structure PlanRunFailure where
  cause    : PlanRunCause
  warnings : List EvalWarning
  deriving DecidableEq, BEq, Inhabited

end LeanNCD.Eval.Plan
