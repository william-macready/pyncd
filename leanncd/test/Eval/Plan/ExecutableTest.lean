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
def goodKernel (sigs : Array TensorSignature) (candidate : JaxKernelCandidate) :
    Except JaxKernelValidationError SomeJaxKernel :=
  validateAndConstructKernel sigs candidate

-- Test that the validator is the only way to construct a kernel: it either succeeds (producing a
-- kernel through the private constructor) or reports an error, never anything else.
def testPrivateConstructor (sigs : Array TensorSignature) (candidate : JaxKernelCandidate) : Bool :=
  match validateAndConstructKernel sigs candidate with
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
               , factors := #[.read idRead] }]
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
      match validateAndConstructKernel idSigs (.affineTable kernel) with
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
      match validateAndConstructKernel idSigs (.affineTable kernel) with
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
      match validateAndConstructKernel idSigs (.einsum kernel) with
      | .ok _ => true
      | .error _ => false

#guard testValidEinsumCandidate

-- === Task 5.1: candidate validators exclude Iverson factors ===
--
-- An Iverson predicate factor is not a read: `validateAffineTable`/`validateEinsum` must reject any
-- candidate whose term carries one. These plans are hand-built (source Iverson stays rejected) but
-- pass `checkAssign` (their predicate leaf has width 1 == `iterationShape.size`). The validator code
-- itself is unchanged in shape from a diff's view for a read-only term — these assertions are the
-- only regression guard that the `.read`-only restriction bites.
def iversonPred1 : PosBoolExpr :=
  .rel .lt (.affine { coeffs := #[0], bias := 0 }) (.affine { coeffs := #[0], bias := 1 })

def idAssignIverson : AssignPlan :=
  { idAssign with terms := #[{ idAssign.terms[0]! with
      factors := #[.read idRead, .iverson iversonPred1] }] }

-- `checkAssign` accepts the plan itself (the predicate leaf is correctly sized).
#guard (match checkAssign idSigs idAssignIverson with | .ok _ => true | .error _ => false)

-- `validateAffineTable` rejects: even with a correctly-lengthed table array (one entry per factor),
-- the second factor is an Iverson predicate, not a read.
def testIversonAffineCandidateRejected : Bool :=
  match checkAssign idSigs idAssignIverson with
  | .error _ => false
  | .ok checked =>
      let table : AffineTableReadCandidate :=
        { source := 0, safeIndex := #[0, 1, 2], validMask := #[true, true, true] }
      let kernel : OrderedAffineTableKernelCandidate :=
        { semanticAssignment := checked, tables := #[#[table, table]] }
      match validateAndConstructKernel idSigs (.affineTable kernel) with
      | .ok _ => false      -- must NOT validate
      | .error _ => true    -- correctly rejected

#guard testIversonAffineCandidateRejected

-- `validateEinsum` rejects: the operand-row count matches the factor count, but the second factor is
-- an Iverson predicate with no einsum operand.
def testIversonEinsumCandidateRejected : Bool :=
  match checkAssign idSigs idAssignIverson with
  | .error _ => false
  | .ok checked =>
      let kernel : EinsumExperimentKernelCandidate :=
        { semanticAssignment := checked, destination := 1
        , operands := #[#[0, 0], #[0]], outputAxes := #[0] }
      match validateAndConstructKernel idSigs (.einsum kernel) with
      | .ok _ => false      -- must NOT validate
      | .error _ => true    -- correctly rejected

#guard testIversonEinsumCandidateRejected

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
        match validateAndConstructKernel idSigs (.affineTable kernel) with
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
        match validateAndConstructKernel idSigs (.affineTable kernel) with
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
               , factors := #[.read mixedRead12] }]
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
        match validateAndConstructKernel mixedSigs (.affineTable affineKernel),
              validateAndConstructKernel mixedSigs (.einsum einsumKernel) with
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

-- === Task 4.5 fixture 10: exact einsum operand/output axis recomputation ===
--
-- A two-dimensional single-term identity candidate, cloned from `NonlinDenseTest.idNode22`
-- (`Y[i, j] := X[i, j]` over `#[2,2]`, coefficient rows `#[1,0]`/`#[0,1]`, `outputPos := #[0,1]`).
-- Rank 2 is what makes the mutations below observable at all: at rank 1 there is no distinct
-- permutation of `#[0]`, so the previous bounds-and-length checks and exact recomputation cannot be
-- told apart. All four candidates here are SAME-RANK and IN-RANGE — only exact recomputation from
-- the checked factor maps (`expectedEinsumOperandRow`) and exact `outputAxes == term.outputPos`
-- equality separate the one correct lowering from the three wrong ones.

def sigs22 : Array TensorSignature :=
  #[ { shape := #[2, 2], dtype := .f64 }, { shape := #[2, 2], dtype := .f64 } ]

def read22 : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[0, 0] }
  , sourceShape := #[2, 2], oobPolicy := .zeroPad }

def assign22 : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[2, 2]
  , terms := #[{ iterationShape := #[2, 2], contextPos := #[], outputPos := #[0, 1]
               , reductionPos := #[], factors := #[.read read22] }]
  , algebra := admittedAlgebra }

/-- Validate a 2-D einsum candidate with the given operand rows and output axes against the checked
    `assign22`. -/
def einsum22Accepted (operands : Array (Array Nat)) (outputAxes : Array Nat) : Bool :=
  match checkAssign sigs22 assign22 with
  | .error _ => false
  | .ok checked =>
      let kernel : EinsumExperimentKernelCandidate :=
        { semanticAssignment := checked, destination := 1, operands, outputAxes }
      match validateAndConstructKernel sigs22 (.einsum kernel) with
      | .ok _ => true
      | .error _ => false

-- Baseline: the exact operand row `#[sourceSlot, 0, 1]` and output axes `#[0, 1]` pass.
#guard einsum22Accepted #[#[0, 0, 1]] #[0, 1]

-- Only the operand axes are permuted (`#[1, 0]` instead of `#[0, 1]`): a transposed read, same rank,
-- both entries in range.
#guard !(einsum22Accepted #[#[0, 1, 0]] #[0, 1])

-- Only the output axes are permuted: a transposed result, same rank, both entries in range.
#guard !(einsum22Accepted #[#[0, 0, 1]] #[1, 0])

-- Only the output axes are duplicated: same rank, both entries in range, but not the term's
-- `outputPos`.
#guard !(einsum22Accepted #[#[0, 0, 1]] #[0, 0])


/-! ## Task 4.5 — JAX support policy, contextual validation, and plan authority

Every fixture below is ADMITTED by the checked backend (`checkAssign`/`checkPlan` succeed) and
rejected only by the experimental JAX gate — that is the whole point: these are semantics Dense
executes correctly and JAX cannot render at all, so they must fail loud before a candidate, an
`ExecutionEvidence` label, or an executable exists. The renderer/lowering halves of the same
fixtures (both rendering modes, both plan renderers, `buildAssignFixture`, the candidate
conversions, and the located outer-step index) live inline in
`experiments/jax_bridge/EvalPlanCodegen.lean`: this default-build module cannot import that
non-default experimental library. -/

/-- Reject/accept outcome of a candidate validator, keeping the CHECKED backend's own verdict
    separate: `.error e` means `checkAssign` itself refused the fixture (which would make a
    rejection guard pass for the wrong reason), `.ok none` means the JAX gate accepted, and
    `.ok (some e)` means it rejected with exactly `e`. -/
private def jaxOutcome (sigs : Array TensorSignature) (a : AssignPlan)
    (mkCandidate : CheckedAssignPlan → JaxKernelCandidate) :
    Except PlanError (Option JaxKernelValidationError) :=
  match checkAssign sigs a with
  | .error e => .error e
  | .ok checked =>
      match validateAndConstructKernel sigs (mkCandidate checked) with
      | .ok _ => .ok none
      | .error e => .ok (some e)

/-- The one correct affine table for a `#[3]`-wide identity read of slot 0. -/
def idTable3 : AffineTableReadCandidate :=
  { source := 0, safeIndex := #[0, 1, 2], validMask := #[true, true, true] }

private def affineOutcome (sigs : Array TensorSignature) (a : AssignPlan)
    (tables : Array (Array AffineTableReadCandidate)) :
    Except PlanError (Option JaxKernelValidationError) :=
  jaxOutcome sigs a (fun checked => .affineTable { semanticAssignment := checked, tables })

private def einsumOutcome (sigs : Array TensorSignature) (a : AssignPlan)
    (operands : Array (Array Nat)) (outputAxes : Array Nat) :
    Except PlanError (Option JaxKernelValidationError) :=
  jaxOutcome sigs a (fun checked =>
    .einsum { semanticAssignment := checked, destination := a.destinationSlot
            , operands, outputAxes })

/-- The checked backend accepted and the JAX gate rejected with exactly `expected`. -/
private def rejectedBy (expected : JaxKernelValidationError) :
    Except PlanError (Option JaxKernelValidationError) → Bool
  | .ok (some e) => e == expected
  | _ => false

/-- Wrap a checked raw plan into a real `PreparedPlan` (no `sorry`, real `checkBindings`). -/
private def preparedOf (raw : RawEvalPlan) (inputs materialized : Array SlotBinding) :
    Option PreparedPlan :=
  match checkPlan raw with
  | .error _ => none
  | .ok checkedPlan =>
    match checkBindings raw.inputSlots inputs with
    | .error _ => none
    | .ok requiredInputs =>
        some { plan := checkedPlan
             , bindings := { requiredInputs, materializedNames := materialized }
             , warnings := [] }

private def executableAccepted (prepared : PreparedPlan) (steps : Array SomeJaxKernel) : Bool :=
  let candidate : JaxExecutableCandidate :=
    { source := prepared, steps
    , evidence := aggregateEvidenceList (steps.map (·.evidence))
    , aggregated := rfl }
  match validateAndConstructExecutable candidate with
  | .ok _ => true
  | .error _ => false

/-- The single validated all-real identity kernel every authority attack below substitutes: it is
    genuinely well-formed under `idSigs`, which is exactly why only the plan-level context tie can
    reject it when it is placed against a plan whose own table is different. -/
private def idAffineKernel? : Option SomeJaxKernel :=
  match checkAssign idSigs idAssign with
  | .error _ => none
  | .ok checked =>
      match validateAndConstructKernel idSigs
          (.affineTable { semanticAssignment := checked, tables := #[#[idTable3]] }) with
      | .ok k => some k
      | .error _ => none

#guard idAffineKernel?.isSome

/-! ### Fixture 1 — a Boolean destination is rejected by both kernel validators and by executable
construction. `idRaw`'s clone changes exactly two things: destination slot 1's signature dtype and
the assignment algebra (both must change together, or `checkAssign` would reject the fixture for
algebra/dtype disagreement before the JAX gate ever ran). -/

def boolDestSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .bool } ]

def boolDestAssign : AssignPlan := { idAssign with algebra := admittedAlgebraBool }

def boolDestRaw : RawEvalPlan :=
  { tensorSigs := boolDestSigs, inputSlots := #[0], steps := #[.assign boolDestAssign] }

-- The CHECKED backend admits it (Task 4.2/4.3): this is a supported Dense semantics.
#guard (match checkAssign boolDestSigs boolDestAssign with | .ok _ => true | .error _ => false)
#guard (match checkPlan boolDestRaw with | .ok _ => true | .error _ => false)

#guard rejectedBy (.unsupported (.destinationDType 0 1 .bool))
  (affineOutcome boolDestSigs boolDestAssign #[#[idTable3]])
#guard rejectedBy (.unsupported (.destinationDType 0 1 .bool))
  (einsumOutcome boolDestSigs boolDestAssign #[#[0, 0]] #[0])

/-- Executable construction: no kernel can be validated for the Boolean-destination step at all, so
    the only way to attempt an executable is to substitute a kernel validated elsewhere — and the
    per-step context tie rejects that. -/
def testBoolDestExecutableRejected : Bool :=
  match preparedOf boolDestRaw #[{ name := "x", slot := 0 }] #[{ name := "y", slot := 1 }],
        idAffineKernel? with
  | some prepared, some k => !(executableAccepted prepared #[k])
  | _, _ => false

#guard testBoolDestExecutableRejected

/-! ### Fixture 2 (validator/executable half) — only the SOURCE signature becomes Boolean. The
checked plan accepts it (a `bool` source may feed an `f64` destination; the destination selects the
algebra), and the JAX gate rejects it with the exact located `.sourceDType 0 0 0 .bool`. -/

def boolSourceSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .bool }, { shape := #[3], dtype := .f64 } ]

def boolSourceRaw : RawEvalPlan :=
  { tensorSigs := boolSourceSigs, inputSlots := #[0], steps := #[.assign idAssign] }

#guard (match checkAssign boolSourceSigs idAssign with | .ok _ => true | .error _ => false)
#guard (match checkPlan boolSourceRaw with | .ok _ => true | .error _ => false)

-- The typed, context-bearing cross-module helper reports the exact locator directly.
#guard (match checkAssign boolSourceSigs idAssign with
  | .error _ => false
  | .ok checked =>
      match checkJaxAssignSupport boolSourceSigs 0 checked with
      | .error e => e == JaxSupportError.sourceDType 0 0 0 .bool
      | .ok _ => false)

#guard rejectedBy (.unsupported (.sourceDType 0 0 0 .bool))
  (affineOutcome boolSourceSigs idAssign #[#[idTable3]])
#guard rejectedBy (.unsupported (.sourceDType 0 0 0 .bool))
  (einsumOutcome boolSourceSigs idAssign #[#[0, 0]] #[0])

-- The Bool-valued validators and the contextual proposition agree with the constructor gate.
def boolSourceAffineCandidate? : Option JaxKernelCandidate :=
  match checkAssign boolSourceSigs idAssign with
  | .error _ => none
  | .ok checked => some (.affineTable { semanticAssignment := checked, tables := #[#[idTable3]] })

#guard (match boolSourceAffineCandidate? with
  | some c => !(kernelWellFormedBool boolSourceSigs c) && !(decide (JaxKernelWellFormed boolSourceSigs c))
  | none => false)

-- ... and the same candidate IS well-formed under the all-real table, proving the rejection is the
-- signature context talking, not a structural defect in the candidate's tables.
#guard (match checkAssign idSigs idAssign with
  | .error _ => false
  | .ok checked =>
      kernelWellFormedBool idSigs (.affineTable { semanticAssignment := checked
                                                , tables := #[#[idTable3]] }))

/-- Executable construction over the Boolean-source plan: same substitution attack as fixture 1. -/
def testBoolSourceExecutableRejected : Bool :=
  match preparedOf boolSourceRaw #[{ name := "x", slot := 0 }] #[{ name := "y", slot := 1 }],
        idAffineKernel? with
  | some prepared, some k => !(executableAccepted prepared #[k])
  | _, _ => false

#guard testBoolSourceExecutableRejected

/-! ### Fixture 3 — tropical max/min algebras are typed unsupported-algebra rejections, not silent
`orderedReference64`. Only the algebra changes; destination and source stay `f64`. -/

def maxAlgebraAssign : AssignPlan := { idAssign with algebra := admittedAlgebraMax }
def minAlgebraAssign : AssignPlan := { idAssign with algebra := admittedAlgebraMin }

#guard (match checkAssign idSigs maxAlgebraAssign with | .ok _ => true | .error _ => false)
#guard (match checkAssign idSigs minAlgebraAssign with | .ok _ => true | .error _ => false)

#guard rejectedBy (.unsupported (.unsupportedAlgebra 0 admittedAlgebraMax))
  (affineOutcome idSigs maxAlgebraAssign #[#[idTable3]])
#guard rejectedBy (.unsupported (.unsupportedAlgebra 0 admittedAlgebraMax))
  (einsumOutcome idSigs maxAlgebraAssign #[#[0, 0]] #[0])
#guard rejectedBy (.unsupported (.unsupportedAlgebra 0 admittedAlgebraMin))
  (affineOutcome idSigs minAlgebraAssign #[#[idTable3]])
#guard rejectedBy (.unsupported (.unsupportedAlgebra 0 admittedAlgebraMin))
  (einsumOutcome idSigs minAlgebraAssign #[#[0, 0]] #[0])

/-! ### Fixture 4 (validator half) — an inline unary read (`ReadPlan.unary`) is a located rejection.
`checkAssign` and Dense both implement it (`gatherFactor` applies the function after the OOB pad);
neither JAX lowering does. -/

def unaryRead : ReadPlan := { idRead with unary := some .exp }

def unaryAssign : AssignPlan :=
  { idAssign with terms := #[{ idAssign.terms[0]! with factors := #[.read unaryRead] }] }

#guard (match checkAssign idSigs unaryAssign with | .ok _ => true | .error _ => false)

#guard rejectedBy (.unsupported (.unaryFactor 0 0 0))
  (affineOutcome idSigs unaryAssign #[#[idTable3]])
#guard rejectedBy (.unsupported (.unaryFactor 0 0 0))
  (einsumOutcome idSigs unaryAssign #[#[0, 0]] #[0])

/-! ### Fixture 7 — declared support-check ORDER: a Boolean destination whose source is Boolean too
reports the DESTINATION, not the source. Without a declared order this fixture would be satisfied by
either error, which is exactly why fixture 1 (real source) and this one (Boolean source) are
separate. -/

def boolBothSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .bool }, { shape := #[3], dtype := .bool } ]

#guard (match checkAssign boolBothSigs boolDestAssign with | .ok _ => true | .error _ => false)

#guard rejectedBy (.unsupported (.destinationDType 0 1 .bool))
  (affineOutcome boolBothSigs boolDestAssign #[#[idTable3]])
#guard rejectedBy (.unsupported (.destinationDType 0 1 .bool))
  (einsumOutcome boolBothSigs boolDestAssign #[#[0, 0]] #[0])

/-! ### Fixture 11 — plan authority attacks (executable half)

(a) F4: a Boolean-source `PreparedPlan` plus a kernel validated under a same-shape ALL-REAL table.
The kernel is genuinely valid on its own terms and its assignment matches the plan's step exactly;
only the stored validation context differs, and that alone must sink executable construction —
otherwise "validated" would mean "validated against some table", not "against this plan's".
`testBoolSourceExecutableRejected` above is that attack; the guard below pins the two halves that
make it non-tautological: the substituted kernel really is valid under its own table, and the same
plan is accepted once its own table matches. -/

def testF4SubstitutionIsotropy : Bool :=
  match preparedOf idRaw #[{ name := "x", slot := 0 }] #[{ name := "y", slot := 1 }],
        idAffineKernel? with
  | some preparedAllReal, some k =>
      -- Same kernel, same assignment: accepted against the all-real plan, rejected against the
      -- Boolean-source plan (`testBoolSourceExecutableRejected`).
      executableAccepted preparedAllReal #[k]
  | _, _ => false

#guard testF4SubstitutionIsotropy

/-! (c) A two-step plan whose Boolean read is only at step 1: step 0 is a perfectly supported
identity assignment, so its kernel validates under the plan's own table. Re-using that cached,
validated step-0 kernel at step 1 must still fail — the per-step tie compares the candidate's
assignment against the checked assignment AT THAT INDEX, so a cached context/result cannot stand in
for a step that was never validated. -/

def step1BoolSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 }
   , { shape := #[3], dtype := .bool }, { shape := #[3], dtype := .f64 } ]

def boolRead2 : ReadPlan :=
  { sourceSlot := 2, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

/-- Step 1: `W[i] := V[i]` reading the Boolean external slot 2 into real slot 3. -/
def step1BoolAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read boolRead2] }]
  , algebra := admittedAlgebra }

def step1BoolRaw : RawEvalPlan :=
  { tensorSigs := step1BoolSigs, inputSlots := #[0, 2]
  , steps := #[.assign idAssign, .assign step1BoolAssign] }

#guard (match checkPlan step1BoolRaw with | .ok _ => true | .error _ => false)

-- Step 0 is supported under the plan's own table; step 1 is not, and names its own factor.
#guard (match affineOutcome step1BoolSigs idAssign #[#[idTable3]] with
  | .ok none => true | _ => false)
#guard rejectedBy (.unsupported (.sourceDType 0 0 0 .bool))
  (affineOutcome step1BoolSigs step1BoolAssign #[#[{ idTable3 with source := 2 }]])

/-- The cached step-0 kernel, validated under the two-step plan's OWN table (so the context tie
    cannot be what rejects it), re-used at step 1. -/
def testCachedStep0KernelRejectedAtStep1 : Bool :=
  match preparedOf step1BoolRaw #[{ name := "x", slot := 0 }, { name := "v", slot := 2 }]
          #[{ name := "y", slot := 1 }, { name := "w", slot := 3 }] with
  | none => false
  | some prepared =>
    match checkAssign step1BoolSigs idAssign with
    | .error _ => false
    | .ok checkedStep0 =>
      match validateAndConstructKernel step1BoolSigs
          (.affineTable { semanticAssignment := checkedStep0, tables := #[#[idTable3]] }) with
      | .error _ => false
      | .ok k0 =>
          -- Step 0's kernel is valid; the plan is still rejected, because step 1 is not step 0.
          !(executableAccepted prepared #[k0, k0])

#guard testCachedStep0KernelRejectedAtStep1

end LeanNCD.Eval.Plan.ExecutableTest
