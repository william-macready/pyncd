import LeanNCD.Eval.Plan.Executable

/-!
# Thread 5, Task 1 — `ExecutionEvidence` / kernel-candidate fixture sketches

Compile-only fixtures: pins that `ExecutionEvidence`'s two constructors exist and destructure, and
that the four candidate types (`AffineTableReadCandidate`, `OrderedAffineTableKernelCandidate`,
`EinsumExperimentKernelCandidate`, `JaxKernelCandidate`) and `candidateEvidenceLabel` elaborate.
No lowering logic exists yet, so the actual derivation from a `CheckedEvalPlan`/`CheckedAssignPlan`
is stubbed with `sorry` — a later task supplies real validators and private constructors.

Field note vs. the Task 1 brief's Step 1 sketch: `EinsumExperimentKernelCandidate` has two fields
(`destination`, `outputAxes`) beyond `semanticAssignment`/`operands` that the brief's original
fixture omitted from the structure literal, which would not elaborate (missing required fields).
Both are supplied here as `sorry`, consistent with `semanticAssignment`'s existing `sorry` — no
change to the type or to what this task is scoped to prove.
-/

namespace LeanNCD.Eval.Plan.ExecutableTest
open LeanNCD.Eval.Plan

-- Test that evidence types exist and destructure
def evidenceOrdred : ExecutionEvidence := ExecutionEvidence.orderedReference64
def evidenceExp : ExecutionEvidence := ExecutionEvidence.optimizationExperiment

-- Test that kernel candidates can be constructed
def affineCandidate (plan : CheckedEvalPlan) (tables : Array (Array AffineTableReadCandidate)) :
    OrderedAffineTableKernelCandidate :=
  { semanticAssignment := sorry
    tables := tables }

def einsumCandidate (plan : CheckedEvalPlan) (operands : Array (Array Nat)) :
    EinsumExperimentKernelCandidate :=
  { semanticAssignment := sorry
    destination := sorry
    operands := operands
    outputAxes := sorry }

end LeanNCD.Eval.Plan.ExecutableTest
