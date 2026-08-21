import LeanNCD.Eval.Plan.Executable

/-!
# Thread 5 (Tasks 1-5) — `ExecutionEvidence` / kernel-candidate / executable tests

Tests for `LeanNCD.Eval.Plan.Executable`'s full pipeline: `ExecutionEvidence`'s two constructors,
the candidate types (`AffineTableReadCandidate`, `OrderedAffineTableKernelCandidate`,
`EinsumExperimentKernelCandidate`, `JaxKernelCandidate`), `candidateEvidenceLabel`, private
constructor discipline (`JaxKernel`/`JaxExecutable`, Task 2/3), evidence aggregation, and the real
Task 5 validators (`validateAffineTable`/`validateEinsum`). No `sorry` anywhere in this file — every
fixture below is built through real `checkAssign`/`checkPlan`/`checkBindings` entry points, per
Task 5's guidance against literal `sorry` in test bodies (the earlier Task-1-era sketches that did
use `sorry` were removed once Task 5 supplied real fixtures over the same types).
-/

namespace LeanNCD.Eval.Plan.ExecutableTest
open LeanNCD.Eval.Plan

-- Test that evidence types exist and destructure
def evidenceOrdred : ExecutionEvidence := ExecutionEvidence.orderedReference64
def evidenceExp : ExecutionEvidence := ExecutionEvidence.optimizationExperiment

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

-- === Task 3: plan-level executable structures + evidence aggregation ===
--
-- Field note vs. the Task 3 brief's Step 1 sketch: the brief says "add at END of ExecutableTests
-- namespace" — no such (plural) namespace exists in this file. Same as Task 2's field note,
-- appended inside the existing (singular) `LeanNCD.Eval.Plan.ExecutableTest` namespace instead of
-- opening a new one.

-- `aggregateEvidenceList`: all ordered-ref → ordered-ref; any experiment → experiment; empty → the
-- identity for "all" (ordered-ref). `#guard`s (not just compile-only defs) verify the actual
-- expected outcome, matching `CompileTest.lean`'s convention elsewhere in this directory.
def testAggregateAll : ExecutionEvidence :=
  aggregateEvidenceList #[.orderedReference64, .orderedReference64]

def testAggregateMixed : ExecutionEvidence :=
  aggregateEvidenceList #[.orderedReference64, .optimizationExperiment]

def testAggregateEmpty : ExecutionEvidence :=
  aggregateEvidenceList #[]

#guard testAggregateAll == .orderedReference64
#guard testAggregateMixed == .optimizationExperiment
#guard testAggregateEmpty == .orderedReference64

-- `JaxExecutable`'s constructor is `private mk ::` (`Executable.lean`), same discipline as
-- `JaxKernel` in Task 2 — cannot be invoked from this file. Deliberately commented out; must
-- never be uncommented in committed code:
--
-- def badExecutable (candidate : JaxExecutableCandidate) : JaxExecutable candidate.evidence :=
--   ⟨candidate, rfl, sorry⟩
--
-- Manually verified (2026-08-13) by uncommenting that exact line and running, from `leanncd/`:
--
-- lake env lean test/Eval/Plan/ExecutableTest.lean
--
-- Observed failure, exit code 1, literal captured stdout/stderr:
--
-- test/Eval/Plan/ExecutableTest.lean:101:2: error: Invalid `⟨...⟩` notation: Constructor for
-- `LeanNCD.Eval.Plan.JaxExecutable` is marked as private
--
-- The line was re-commented immediately after confirming the failure; this file compiles clean
-- with it commented out, exercising only the positive half (construction via
-- `validateAndConstructExecutable` works).

-- A zero-step plan candidate: `aggregateEvidenceList #[] = .orderedReference64` (proved `by simp
-- [aggregateEvidenceList]` — neither `rfl` nor `decide` close it, see field note below), so
-- `evidence := .orderedReference64` is the only value that type-checks here.
--
-- Field note: unlike `JaxKernel`'s analogous `aligned := rfl` (Task 2, a direct match on the
-- candidate's constructor, which unifies definitionally), `aggregateEvidenceList` goes through
-- `Array.all`/`Array.map`, whose kernel-level whnf reduction gets stuck on `Array`'s
-- well-founded-recursion internals for both `rfl` (`Type mismatch ... ?m.4 = ?m.4`) and `decide`
-- (`did not reduce to isTrue or isFalse`, confirmed by building each). `simp
-- [aggregateEvidenceList]` unfolds the definition and simplifies `#[].all _`/`#[].map _` via simp
-- lemmas rather than kernel whnf, which does close the goal.
def emptyPlanCandidate (plan : PreparedPlan) : JaxExecutableCandidate :=
  { source := plan
    steps := #[]
    evidence := .orderedReference64
    aggregated := by simp [aggregateEvidenceList] }

-- Test that the plan-level validator is the only way to construct a `JaxExecutable`: it either
-- succeeds (producing an executable through the private constructor) or reports an error.
def testValidateExecutable (plan : PreparedPlan) : Bool :=
  match validateAndConstructExecutable (emptyPlanCandidate plan) with
  | .ok _ => true      -- validator succeeded
  | .error _ => false  -- validator failed

-- === Task 5: real table/candidate validation ===
--
-- A minimal real identity-copy fixture (`Y[i] := X[i]`, mirroring `KernelDenseTest.lean`'s
-- `identityPlan`): one term, one factor, iteration domain size 3, built through the real
-- `checkAssign`/`checkPlan`/`checkBindings` entry points — no `sorry` placeholders anywhere below,
-- per Task 5's guidance against literal `sorry` in test bodies. This file only imports
-- `LeanNCD.Eval.Plan.Executable` (a default-build production module), so it deliberately does NOT
-- exercise `EvalPlanCodegen.lean`'s new `loweringToAffineTableCandidate`/`loweringToEinsumCandidate`/
-- `lowerCheckPlanToCandidate` (those live in the non-default `JaxExperiment` library and are tested
-- there instead, inline in `EvalPlanCodegen.lean` itself) — candidates here are hand-built to the
-- same shape those lowering functions would themselves produce for this fixture.

def idSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 } ]

def idRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

def idAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[idRead] }]
  , algebra := admittedAlgebra }

def idRaw : RawEvalPlan :=
  { tensorSigs := idSigs, inputSlots := #[0]
  , steps := #[.assign idAssign] }

-- Well-formed affine-table candidate: the iteration domain has 3 coordinates (0, 1, 2), and the
-- identity read maps each straight through to the same-numbered source index, all in-bounds.
def testValidAffineCandidate : Bool :=
  match checkAssign idSigs idAssign with
  | .error _ => false
  | .ok checked =>
      let table : AffineTableReadCandidate :=
        { source := 0, safeIndex := #[0, 1, 2], validMask := #[true, true, true] }
      let kernel : OrderedAffineTableKernelCandidate :=
        { semanticAssignment := checked, tables := #[#[table]] }
      match validateAndConstructKernel (.affineTable kernel) with
      | .ok _ => true
      | .error _ => false

#guard testValidAffineCandidate

-- Deliberately malformed: `safeIndex`/`validMask` have the wrong length (2 entries, not the
-- iteration domain's 3) — `validateAffineTable` must reject a truncated table, not silently accept
-- it.
def testMalformedAffineCandidateRejected : Bool :=
  match checkAssign idSigs idAssign with
  | .error _ => false
  | .ok checked =>
      let badTable : AffineTableReadCandidate :=
        { source := 0, safeIndex := #[0, 1], validMask := #[true, true] }
      let kernel : OrderedAffineTableKernelCandidate :=
        { semanticAssignment := checked, tables := #[#[badTable]] }
      match validateAndConstructKernel (.affineTable kernel) with
      | .ok _ => false      -- must NOT validate
      | .error _ => true    -- correctly rejected

#guard testMalformedAffineCandidateRejected

-- Well-formed einsum candidate for the same fixture: the identity read is a pure projection
-- (coefficient row `#[1]`, zero bias) onto iteration position 0, so factor 0's operand row is
-- `#[sourceSlot, coveredPosition] = #[0, 0]`, and the single output position is `#[0]`.
def testValidEinsumCandidate : Bool :=
  match checkAssign idSigs idAssign with
  | .error _ => false
  | .ok checked =>
      let kernel : EinsumExperimentKernelCandidate :=
        { semanticAssignment := checked, destination := 1
        , operands := #[#[0, 0]], outputAxes := #[0] }
      match validateAndConstructKernel (.einsum kernel) with
      | .ok _ => true
      | .error _ => false

#guard testValidEinsumCandidate

-- Plan-level: a real `PreparedPlan` (via `checkPlan` + `checkBindings`, no `sorry`), wrapping the
-- single validated affine kernel above into a `JaxExecutableCandidate`; the plan-level validator
-- must accept it.
def testValidPlanCandidate : Bool :=
  match checkPlan idRaw with
  | .error _ => false
  | .ok checkedPlan =>
    match (checkedPlan.checkedNodes[0]? : Option CheckedPlanStepEvidence) with
    | none => false
    | some (.scan _) => false  -- unreachable: idRaw is scan-free by construction
    | some (.pointwise _) | some (.axiswise _) =>
        false  -- unreachable: idRaw never contains a nonlinearity step
    | some (.assign checkedAssign) =>
      match checkBindings #[0] #[{ name := "x", slot := 0 }] with
      | .error _ => false
      | .ok requiredInputs =>
        let prepared : PreparedPlan :=
          { plan := checkedPlan
          , bindings := { requiredInputs, materializedNames := #[{ name := "y", slot := 1 }] }
          , warnings := [] }
        let table : AffineTableReadCandidate :=
          { source := 0, safeIndex := #[0, 1, 2], validMask := #[true, true, true] }
        let kernel : OrderedAffineTableKernelCandidate :=
          { semanticAssignment := checkedAssign, tables := #[#[table]] }
        match validateAndConstructKernel (.affineTable kernel) with
        | .error _ => false
        | .ok someKernel =>
          let steps := #[someKernel]
          let candidate : JaxExecutableCandidate :=
            { source := prepared, steps
            , evidence := aggregateEvidenceList (steps.map (·.evidence))
            , aggregated := rfl }
          match validateAndConstructExecutable candidate with
          | .ok _ => true
          | .error _ => false

#guard testValidPlanCandidate

-- Same fixture and single well-formed affine kernel as `testValidPlanCandidate` above, but pinning
-- the resulting plan-level `.evidence` VALUE directly — `testValidPlanCandidate` only checks `.ok`,
-- never inspects `.evidence`. An all-affine (single-kernel) plan's aggregated evidence must be
-- `.orderedReference64`.
def testValidPlanCandidateEvidence : Bool :=
  match checkPlan idRaw with
  | .error _ => false
  | .ok checkedPlan =>
    match (checkedPlan.checkedNodes[0]? : Option CheckedPlanStepEvidence) with
    | none => false
    | some (.scan _) => false  -- unreachable: idRaw is scan-free by construction
    | some (.pointwise _) | some (.axiswise _) =>
        false  -- unreachable: idRaw never contains a nonlinearity step
    | some (.assign checkedAssign) =>
      match checkBindings #[0] #[{ name := "x", slot := 0 }] with
      | .error _ => false
      | .ok requiredInputs =>
        let prepared : PreparedPlan :=
          { plan := checkedPlan
          , bindings := { requiredInputs, materializedNames := #[{ name := "y", slot := 1 }] }
          , warnings := [] }
        let table : AffineTableReadCandidate :=
          { source := 0, safeIndex := #[0, 1, 2], validMask := #[true, true, true] }
        let kernel : OrderedAffineTableKernelCandidate :=
          { semanticAssignment := checkedAssign, tables := #[#[table]] }
        match validateAndConstructKernel (.affineTable kernel) with
        | .error _ => false
        | .ok someKernel =>
          let steps := #[someKernel]
          let candidate : JaxExecutableCandidate :=
            { source := prepared, steps
            , evidence := aggregateEvidenceList (steps.map (·.evidence))
            , aggregated := rfl }
          candidate.evidence == .orderedReference64

#guard testValidPlanCandidateEvidence

-- Deliberately malformed at plan level: zero step-kernels against a one-step source plan —
-- `JaxExecutableWellFormed`'s step-count/raw-step-count correspondence must reject this, not
-- silently accept a plan that dropped a step.
def testMalformedPlanCandidateRejected : Bool :=
  match checkPlan idRaw with
  | .error _ => false
  | .ok checkedPlan =>
    match checkBindings #[0] #[{ name := "x", slot := 0 }] with
    | .error _ => false
    | .ok requiredInputs =>
      let prepared : PreparedPlan :=
        { plan := checkedPlan
        , bindings := { requiredInputs, materializedNames := #[{ name := "y", slot := 1 }] }
        , warnings := [] }
      let steps : Array SomeJaxKernel := #[]
      let candidate : JaxExecutableCandidate :=
        { source := prepared, steps
        , evidence := aggregateEvidenceList (steps.map (·.evidence))
        , aggregated := rfl }
      match validateAndConstructExecutable candidate with
      | .ok _ => false      -- must NOT validate (steps.size = 0 ≠ source's 1 raw step)
      | .error _ => true    -- correctly rejected

#guard testMalformedPlanCandidateRejected

-- === Fix wave: mixed-kernel plan-level evidence (review finding 4) ===
--
-- A real two-step plan (`Y[i] := X[i]`, then `Z[i] := Y[i]`) whose step 0 gets a validated
-- AFFINE kernel and step 1 gets a validated EINSUM kernel instead — deliberately, to exercise
-- `aggregateEvidenceList` at the PLAN level with a genuine mix. `testAggregateMixed` (Task 3, above)
-- only exercises the aggregation function directly on a bare `Array ExecutionEvidence`; no existing
-- test built an actual `JaxExecutableCandidate` from two real, differently-evidenced kernels and
-- inspected the resulting `.evidence`.

def mixedSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 } ]

def mixedRead12 : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

-- `Z[i] := Y[i]`: reads slot 1 (`Y`, step 0's destination), writes slot 2.
def mixedAssign1 : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[mixedRead12] }]
  , algebra := admittedAlgebra }

-- Step 0 reuses `idAssign` (`Y[i] := X[i]`, slot 0 → slot 1) unchanged; step 1 is `mixedAssign1`
-- (`Z[i] := Y[i]`, slot 1 → slot 2).
def mixedRaw : RawEvalPlan :=
  { tensorSigs := mixedSigs, inputSlots := #[0]
  , steps := #[.assign idAssign, .assign mixedAssign1] }

def testMixedKernelPlanEvidence : Bool :=
  match checkPlan mixedRaw with
  | .error _ => false
  | .ok checkedPlan =>
    match (checkedPlan.checkedNodes[0]? : Option CheckedPlanStepEvidence),
          (checkedPlan.checkedNodes[1]? : Option CheckedPlanStepEvidence) with
    | some (.assign checkedAssign0), some (.assign checkedAssign1) =>
      match checkBindings #[0] #[{ name := "x", slot := 0 }] with
      | .error _ => false
      | .ok requiredInputs =>
        let prepared : PreparedPlan :=
          { plan := checkedPlan
          , bindings :=
              { requiredInputs
              , materializedNames := #[{ name := "y", slot := 1 }, { name := "z", slot := 2 }] }
          , warnings := [] }
        -- Step 0: affine-table kernel (`orderedReference64`), same table shape as `idAssign`'s
        -- other uses above (identity read, 3-entry iteration domain, all in-bounds).
        let affineTable : AffineTableReadCandidate :=
          { source := 0, safeIndex := #[0, 1, 2], validMask := #[true, true, true] }
        let affineKernel : OrderedAffineTableKernelCandidate :=
          { semanticAssignment := checkedAssign0, tables := #[#[affineTable]] }
        -- Step 1: einsum kernel (`optimizationExperiment`) for `Z[i] := Y[i]` — the identity read
        -- is a pure projection (coefficient row `#[1]`, zero bias) onto position 0, so the operand
        -- row is `#[sourceSlot, coveredPosition] = #[1, 0]`.
        let einsumKernel : EinsumExperimentKernelCandidate :=
          { semanticAssignment := checkedAssign1, destination := 2
          , operands := #[#[1, 0]], outputAxes := #[0] }
        match validateAndConstructKernel (.affineTable affineKernel),
              validateAndConstructKernel (.einsum einsumKernel) with
        | .ok someAffine, .ok someEinsum =>
          let steps := #[someAffine, someEinsum]
          let candidate : JaxExecutableCandidate :=
            { source := prepared, steps
            , evidence := aggregateEvidenceList (steps.map (·.evidence))
            , aggregated := rfl }
          match validateAndConstructExecutable candidate with
          | .ok _ => candidate.evidence == .optimizationExperiment
          | .error _ => false
        | _, _ => false
    | _, _ => false

#guard testMixedKernelPlanEvidence

end LeanNCD.Eval.Plan.ExecutableTest
