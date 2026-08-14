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

end LeanNCD.Eval.Plan
