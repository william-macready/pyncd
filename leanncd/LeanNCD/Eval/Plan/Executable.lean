import LeanNCD.Eval.Plan.Check

/-!
# JAX evidence-indexed executable kernels — Stage A candidate types (Thread 5, Task 1)

Foundation for the JAX executable phase's private-constructor discipline, mirroring the pattern
already established for the checked phase in `Check.lean` (`CheckedAssignPlan`, `CheckedEvalPlan`).
This file adds the evidence index (`ExecutionEvidence`) and the public, pre-validation `Candidate`
types the pipeline runs through before a later task adds private, evidence-indexed `Executable`
constructors: `CheckedEvalPlan` → `PreparedPlan` → `JaxExecutableCandidate` → `JaxExecutable`.

No lowering logic lives here — `EvalPlanCodegen.lean`'s `einsumOnly`/`affineReference` modes
already exist and are untouched. This file is purely structural: types a later task will wrap with
validators and private constructors so that only `orderedAffineTable`-shaped candidates can ever
inhabit `orderedReference64` evidence, and only `einsum`-shaped candidates can ever inhabit
`optimizationExperiment` evidence.

Spec: `papers/jax_evalplan_architecture.md` §4.3, §7.1 rows 5–6, Appendix D.
-/

namespace LeanNCD.Eval.Plan

/-- Numerical claim an executable kernel is allowed to make.
    - `orderedReference64`: affine-table path, bit-exact ordered reference semantics
    - `optimizationExperiment`: einsum or other optimization, no reference claim
-/
inductive ExecutionEvidence where
  | orderedReference64 : ExecutionEvidence
  | optimizationExperiment : ExecutionEvidence
  deriving DecidableEq, BEq, Repr

/-- Safe index and validity mask for one factor coordinate.
    Part of the affine-table reference lowering (precomputed in Lean from checked plan).
-/
structure AffineTableReadCandidate where
  source : TensorSlot      -- which input slot
  safeIndex : Array Nat    -- one per iteration coordinate (size = iteration domain)
  validMask : Array Bool   -- one per iteration coordinate

/-- Ordered affine-table kernel candidate (public, not executable).
    Retains semantic source; no proof that tables are correct yet.
-/
structure OrderedAffineTableKernelCandidate where
  semanticAssignment : CheckedAssignPlan  -- the source this refines
  tables : Array (Array AffineTableReadCandidate)  -- one per term, then per factor

/-- Einsum experiment kernel candidate (public, not executable).
    Retains semantic source; no proof of projection-only restriction or label limits yet.
-/
structure EinsumExperimentKernelCandidate where
  semanticAssignment : CheckedAssignPlan  -- the source this refines
  destination : TensorSlot
  operands : Array (Array Nat)  -- one per term factor: source slot, axes (encoded as positions)
  outputAxes : Array Nat

/-- Union of kernel candidates. Evidence is derived, not indexed.
-/
inductive JaxKernelCandidate where
  | affineTable (kernel : OrderedAffineTableKernelCandidate) : JaxKernelCandidate
  | einsum (kernel : EinsumExperimentKernelCandidate) : JaxKernelCandidate

/-- Derive the evidence label from a candidate (pure inspection, no validation).
-/
def candidateEvidenceLabel : JaxKernelCandidate → ExecutionEvidence
  | .affineTable _ => ExecutionEvidence.orderedReference64
  | .einsum _ => ExecutionEvidence.optimizationExperiment

/-- Opaque witness that a candidate is well-formed (stub predicate).
    Real implementation: table lengths match iteration domain, indices are safe, etc.
-/
def JaxKernelWellFormed (candidate : JaxKernelCandidate) : Prop :=
  True  -- TODO: implement real validation after lowering is updated

/-- The stub predicate is unconditionally `True`, so it is trivially decidable. Real validation
    (after lowering is updated) will need a genuine `Decidable` instance derived from the actual
    checks; this stub instance is what lets `validateAndConstructKernel` branch on the predicate
    today without blocking on that future work.
-/
instance (candidate : JaxKernelCandidate) : Decidable (JaxKernelWellFormed candidate) :=
  .isTrue trivial

/-- Type-indexed kernel, only creatable by validator (`validateAndConstructKernel`).
    Evidence is fixed at construction and never changes: `aligned` ties the candidate's
    derived evidence label to the index `evidence`, so the private constructor cannot be
    used to mismatch the two even from within this file.
-/
structure JaxKernel (evidence : ExecutionEvidence) where private mk ::
  candidate : JaxKernelCandidate
  aligned : candidateEvidenceLabel candidate = evidence
  valid : JaxKernelWellFormed candidate  -- semantic: stub for now

/-- Existential witness hiding the evidence index.
-/
structure SomeJaxKernel where
  evidence : ExecutionEvidence
  kernel : JaxKernel evidence

/-- Validate a candidate and construct a private executable kernel.
    Returns `SomeJaxKernel` to hide evidence at the cost of unpacking later.
-/
def validateAndConstructKernel (candidate : JaxKernelCandidate) :
    Except String SomeJaxKernel := do
  -- Derive evidence label from candidate structure (not mutable).
  let evidence := candidateEvidenceLabel candidate
  -- Stub validation: real implementation checks table lengths, indices, etc.
  -- `throw`, not `return .error` — `return` in this `Except` do-block already performs the `.ok`
  -- wrap (`pure`), so `return .error x` would elaborate `.error` against the wrong expected type
  -- (`SomeJaxKernel`, not `Except String SomeJaxKernel`) and fail to resolve.
  unless decide (JaxKernelWellFormed candidate) do
    throw "Kernel validation failed"
  -- Construct private kernel only after validation passes.
  let kernel : JaxKernel evidence := {
    candidate := candidate
    aligned := rfl  -- evidence derivation is deterministic
    valid := trivial
  }
  return { evidence := evidence, kernel := kernel }

end LeanNCD.Eval.Plan
