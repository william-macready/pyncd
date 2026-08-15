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
  | contextProjectionMismatch (termIndex : Nat) (projected : Array Nat) (declared : Array Nat)
  | constDtypeMismatch       (dtype : ScalarDType) (const : ScalarConst)
  | algebraNotAdmitted       (algebra : ContractionAlgebra)
  | policyNotAdmitted        (policy : OutOfBoundsPolicy)
  | destinationShapeMismatch (declared : Array Nat) (signature : Array Nat)
  | numericModeNotAdmitted   (mode : NumericMode)
  | duplicateInputSlot       (slot : TensorSlot)
  | inputSlotsNotOrdered     (atIndex : Nat)
  | topLevelContextNotEmpty  (nodeIndex : Nat)
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
  | contextShapeMismatch (expected : Array Nat) (actual : List Int)
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

/-- Failure of `Prepared.lean`'s `checkBindings`: a candidate `requiredInputs` array does not align
    with a plan's `inputSlots` the way a `RequiredBindings` requires. `notAPermutation` covers a
    duplicate slot, an extra slot, or a missing slot alike — every one of those breaks
    `(bindings.map (·.slot)).toList.Perm inputSlots.toList`, so they all surface through this one
    constructor with the two slot lists that failed to match. `duplicateName` is a genuinely
    separate malformation: two different slots bound to the same source name, which slot-`Perm`
    alone cannot catch (two distinct slots can each legitimately appear once in the permutation
    while still sharing a name). Defined here, not in `Prepared.lean`, because `PlanCompileCause`
    (relocated to `EvalPlan.lean` — see the plain comment just below) needs it and `Error.lean` sits
    upstream of `Prepared.lean` in the CURRENT import graph (`Prepared → EvalPlan → Scan → Block →
    Dense → Check → Error`) — `TensorSlot`/`String` are both already available via `Kernel.lean`, so
    no `SlotBinding`-shaped payload is needed here to make that work. -/
inductive BindingsError
  | notAPermutation (expectedSlots observedSlots : Array TensorSlot)
  | duplicateName   (name : String)
  deriving DecidableEq, BEq, Repr, Inhabited

/- `PlanCompileCause`/`PlanCompileFailure` used to live here (§5.5's sketch), but `invalidPlan`'s
   payload is now `PlanStepError` (`EvalPlan.lean`), which itself depends on `ScanPlanError`
   (`Scan.lean`) — one layer downstream of where this file sits in the import graph (`Error` is
   imported by `Check`, which is upstream of `Dense → Block → Scan → EvalPlan`). So both types
   relocated to `EvalPlan.lean`, the first module downstream of everything they need to reference.
   See `EvalPlan.lean` for their current definitions. -/

/-- Everything `pack` can detect wrong with the concrete tensor `env` supplies once `requiredInputs`
    itself is already known-good (`PlanBindings.requiredInputs : RequiredBindings`, checked by
    `checkBindings` — a clean, name-unique bijection, but onto `RequiredBindings`' OWN stored
    `inputSlots` field, NOT — by anything the type system enforces — onto the enclosing
    `PreparedPlan`'s `plan.raw.inputSlots`; the two agree for every plan `prepareEvalPlan` produces
    only because it is the sole real-world producer that builds both together from the same array,
    a producer-discipline fact, not a type-level guarantee). If that coupling were ever broken by a
    hand-built `PreparedPlan`, `pack` still fails loud — a `.missingEnvBinding` naming the unmatched
    slot, not a silent wrong-tensor pack. The three constructors this type used to carry for that
    case, `missingRequiredBinding`/`duplicateRequiredBinding`/`extraRequiredBinding`, are gone:
    unreachable for every `RequiredBindings` `prepareEvalPlan` actually produces, since
    `checkBindings` already rejects those shapes at construction. What's left are genuine runtime
    concerns about the caller-supplied `env`: `missingEnvBinding` (a required name absent from
    `env`), `shapeMismatch`/`storageMismatch` (a name resolved, but its tensor doesn't conform to
    the plan's declared signature). -/
inductive InputBindingError
  | missingEnvBinding (name : String)
  | shapeMismatch     (name : String) (slot : TensorSlot) (expected : Array Nat) (actual : List Nat)
  | storageMismatch   (name : String) (slot : TensorSlot) (shape : List Nat) (dataSize : Nat)
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
