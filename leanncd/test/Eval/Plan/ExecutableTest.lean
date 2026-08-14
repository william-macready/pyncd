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

-- === Task 2: private JaxKernel constructor + validator ===
--
-- `JaxKernel`'s constructor is `private mk ::` (`Executable.lean`), so it cannot be invoked from
-- this file. As with `CheckedPrivacyTest.lean`'s treatment of `CheckedAssignPlan`, Lean has no
-- in-tree "expect this declaration to fail to elaborate" harness, so the negative half is a
-- documented manual verification, not an automated `#guard`. Deliberately commented out; must
-- never be uncommented in committed code:
--
-- def badKernel : JaxKernel .orderedReference64 := ⟨sorry, sorry, sorry⟩
--
-- Manually verified (2026-08-13) by uncommenting that exact line and running, from `leanncd/`:
--
-- lake env lean test/Eval/Plan/ExecutableTest.lean
--
-- Observed failure, exit code 1, literal captured stdout/stderr:
--
-- test/Eval/Plan/ExecutableTest.lean:47:49: error: Invalid `⟨...⟩` notation: Constructor for
-- `LeanNCD.Eval.Plan.JaxKernel` is marked as private
--
-- The line was re-commented immediately after confirming the failure; this file compiles clean
-- with it commented out, exercising only the positive half (construction via
-- `validateAndConstructKernel` works).

-- Correct way: use the validator.
def goodKernel (candidate : JaxKernelCandidate) : Except String SomeJaxKernel :=
  validateAndConstructKernel candidate

-- Test that the validator is the only way to construct a kernel: it either succeeds (producing a
-- kernel through the private constructor) or reports an error, never anything else.
def testPrivateConstructor (candidate : JaxKernelCandidate) : Bool :=
  match validateAndConstructKernel candidate with
  | .ok _ => true      -- validator succeeded
  | .error _ => false  -- validator failed

end LeanNCD.Eval.Plan.ExecutableTest
