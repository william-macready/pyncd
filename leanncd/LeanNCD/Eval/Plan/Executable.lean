import LeanNCD.Eval.Plan.Check
import LeanNCD.Eval.Plan.Prepared
import LeanNCD.Eval.Plan.Coordinates

/-!
# JAX evidence-indexed executable kernels — Stage A candidate/validator/executable types (Thread 5)

The JAX executable phase's private-constructor discipline, mirroring the pattern already
established for the checked phase in `Check.lean` (`CheckedAssignPlan`) and `EvalPlan.lean`
(`CheckedEvalPlan`, relocated there in Wave F F3 Task 4). This file owns the full pipeline from
public, pre-validation `Candidate` types through the private,
evidence-indexed `Executable` constructors that are the only way to build one:
`CheckedEvalPlan` → `PreparedPlan` → `JaxExecutableCandidate` → (`validateAndConstructExecutable`)
→ `JaxExecutable`. Real validators (`validateAffineTable`/`validateEinsum`, dispatched through
`kernelWellFormedBool`, plus the plan-level `JaxExecutableWellFormed`) back both private
constructors (`JaxKernel`/`JaxExecutable`) — a candidate whose tables don't match its own semantic
source, or whose einsum lowering silently dropped an axis or a nonzero affine bias, is rejected,
not merely shape-checked.

No lowering logic lives here — `EvalPlanCodegen.lean`'s `einsumOnly`/`affineReference` modes
already exist and are untouched, and so is the routing in that file's `loweringToAffineTableCandidate`
/`loweringToEinsumCandidate`/`lowerCheckPlanToCandidate`. This file only imports
`LeanNCD.Eval.Plan.Coordinates` for `validateAffineTable`'s own recomputation check (below), the
same shared row-major primitives `EvalPlanCodegen.lean`'s `buildFactorTable` composes — no
JAX/lookup-table/source-name/codegen concept is introduced here.

Spec: `papers/jax_evalplan_architecture.md` §4.3, §7.1 rows 5–6, Appendix D.

NOTE (Thread 5 Task 5, Step 6 grep gate — `grep -E '...' papers/jax_evalplan_architecture.md`,
run from the repo root over every identifier this file and `EvalPlanCodegen.lean`'s Task 5 section
introduce or touch): the doc names `ExecutionEvidence`, `JaxKernel`, `SomeJaxKernel`,
`JaxExecutableCandidate`, `JaxExecutable`, and `JaxExecutableWellFormed` verbatim (Appendix D). It
does NOT name `JaxKernelCandidate`, `AffineTableReadCandidate`, `OrderedAffineTableKernelCandidate`,
`EinsumExperimentKernelCandidate`, `SomeJaxExecutable`, `JaxKernelWellFormed`,
`candidateEvidenceLabel`, `validateAndConstructKernel`, `validateAndConstructExecutable`, or any of
`kernelWellFormedBool`/`validateAffineTable`/`validateEinsum`/`affineFactorTableValid`/
`affineTermTablesValid`/`recomputeAffineFactorTable` (this file) or `lowerCheckPlanToCandidate`/
`loweringToAffineTableCandidate`/`loweringToEinsumCandidate` (`EvalPlanCodegen.lean`) — this is
expected, not a gap: Appendix D is
explicitly this thread's Spec-line "non-copy-ready sketch needing translation to real types" (its
own dependent-type sketch uses parameters not present in this file's flat non-dependent
`JaxKernelCandidate`/table-array split), and the Plan Verification Checklist's own "No copy-paste from Appendix D: Translated
concepts, not code" line already anticipates exactly this kind of naming divergence for
Lean-real-type plumbing and internal validation helpers that Appendix D's sketch never spells out
at that granularity. One genuine drift worth flagging rather than silently translating: this file's
`aggregateEvidenceList` is the doc's `aggregateEvidence` (Appendix D, e.g. line ~1940) under a
different name — same fold-over-an-array-of-evidences concept (`List`-style suffix reflecting that
it takes an `Array`, not a single evidence), not a second, undocumented concept.
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

/-- Recompute the correct `(safeIndex, validMask)` pair for one factor against a given iteration
    basis, straight from the shared coordinate primitives (`Coordinates.lean`): enumerate the basis
    in row-major order (`allCoords`), apply the factor's own affine map (`applyAffine`), and either
    flatten to a safe index (`flatIndex`) when every source dimension is in range
    (`inBoundsPerDim`), or record `0`/`false`. Byte-for-byte the same fold as
    `EvalPlanCodegen.lean`'s `buildFactorTable` (the exact primitive `loweringToAffineTableCandidate`
    calls to build a candidate's table in the first place) — duplicated here, not imported, because
    `experiments/jax_bridge` depends on `LeanNCD`, not the reverse, so this production module cannot
    import that experimental one. This is the semantic source `validateAffineTable` below checks a
    candidate's stored table AGAINST, not merely a shape/bounds sanity check on the stored table
    itself. -/
def recomputeAffineFactorTable (iterationShape : Array Nat) (factor : ReadPlan) :
    Array Nat × Array Bool :=
  (allCoords iterationShape.toList).foldl
    (fun (acc : Array Nat × Array Bool) iter =>
      let (idxs, masks) := acc
      let src := applyAffine factor.map iter
      let shape := factor.sourceShape.toList
      if inBoundsPerDim shape src then
        (idxs.push (flatIndex shape (src.map Int.toNat)), masks.push true)
      else
        (idxs.push 0, masks.push false))
    (#[], #[])

/-- Whether one factor's precomputed table is the CORRECT table for its own term's iteration basis
    and its own source: the table's `source` matches the factor's own `sourceSlot`, and its stored
    `safeIndex`/`validMask` are exactly (`Array`'s derived `BEq`, i.e. equal length and pointwise
    equal) the pair `recomputeAffineFactorTable` derives independently from `factor` itself. A table
    with every `safeIndex` entry replaced by `0` (but otherwise the right length and in-bounds) used
    to still pass here before this check existed — length/bounds alone cannot tell a genuinely wrong
    gather from a right one; equality against the recomputed table can. -/
def affineFactorTableValid (iterationShape : Array Nat) (factor : ReadPlan)
    (table : AffineTableReadCandidate) : Bool :=
  let (expectedIndex, expectedMask) := recomputeAffineFactorTable iterationShape factor
  table.source == factor.sourceSlot &&
  table.safeIndex == expectedIndex &&
  table.validMask == expectedMask

/-- Whether one term's array of per-factor tables corresponds to that term's own factor list
    (one table per factor, `tables.size = term.factors.size`) and each table is individually valid
    (`affineFactorTableValid`) against that term's own iteration basis (`term.iterationShape`).
    An `.iverson` predicate factor is NOT a read: a term containing one has no valid affine-table
    lowering, so any such factor makes the whole candidate invalid (its `.read` extraction fails). -/
def affineTermTablesValid (term : TermPlan) (tables : Array AffineTableReadCandidate) : Bool :=
  tables.size == term.factors.size &&
  (term.factors.zip tables).all
    (fun (factor, table) => match factor with
      | .read r => affineFactorTableValid term.iterationShape r table
      | .iverson _ => false)

/-- Validate an affine-table kernel candidate against its own semantic source: one table array per
    term (`tables.size = semanticAssignment.plan.terms.size`, per `OrderedAffineTableKernelCandidate`'s
    doc comment "one per term, then per factor"), and every per-term table array individually valid
    (`affineTermTablesValid`). -/
def validateAffineTable (kernel : OrderedAffineTableKernelCandidate) : Bool :=
  let terms := kernel.semanticAssignment.plan.terms
  kernel.tables.size == terms.size &&
  (terms.zip kernel.tables).all (fun (term, tableRow) => affineTermTablesValid term tableRow)

/-- Validate an einsum kernel candidate against its own semantic source.
    `EinsumExperimentKernelCandidate` has one flat `operands`/`outputAxes` pair with no per-term
    dimension, so it can only faithfully represent a SINGLE-TERM `AssignPlan` (see
    `EvalPlanCodegen.lean`'s `loweringToEinsumCandidate` doc comment for the full ruling this
    reflects). Checks:
    - the semantic source has exactly one term
    - `destination` matches the semantic assignment's own `destinationSlot`
    - `operands.size` matches that term's factor count, one operand row per factor
    - each operand row's first entry is that factor's own `sourceSlot`
    - every axis position named in an operand row (after the leading slot) or in `outputAxes` is
      within the term's iteration basis (`< term.iterationShape.size`)
    - the factor's own affine map has zero bias in every row (`f.map.bias.all (· == 0)`) — a
      nonzero-bias read (e.g. `X[i+1]`) is rejected, matching `lowerFactor`'s (`EvalPlanCodegen.lean`)
      `.nonzeroAffineBias` rejection of the very same shape
    - the operand row's axis count (after the leading source-slot entry) equals the factor's own
      coefficient-row count (`f.map.coeffs.size`) — `loweringToEinsumCandidate` builds each operand
      row via `f.map.coeffs.filterMap rowProjectionTarget`, which silently DROPS any row that isn't a
      genuine single-`1` projection (e.g. `X[-i]`); a dropped row shrinks the operand row below the
      factor's own coefficient count, so this count check is exactly the projection-only restriction
      `lowerFactor`'s `.nonProjectionRow` rejection enforces, applied post hoc to the candidate's
      already-built (and otherwise unable to distinguish "genuine 1-D factor" from "3-D factor that
      lost two axes to `filterMap`") operand row.
    Without these last two checks this validator was strictly WEAKER than the pre-existing
    `lowerFactor`/`einsumOnly` path it lowers alongside: a candidate built from a nonzero-bias or
    non-projection read passed validation and was stamped `optimizationExperiment` evidence anyway,
    even though the corresponding `einsumOnly` lowering refuses to emit it at all. -/
def validateEinsum (kernel : EinsumExperimentKernelCandidate) : Bool :=
  let terms := kernel.semanticAssignment.plan.terms
  kernel.destination == kernel.semanticAssignment.plan.destinationSlot &&
  terms.size == 1 &&
  match terms[0]? with
  | none => false
  | some term =>
      let rank := term.iterationShape.size
      kernel.operands.size == term.factors.size &&
      (term.factors.zip kernel.operands).all (fun (factor, opRow) => match factor with
        | .iverson _ => false  -- a predicate factor has no einsum operand; not an einsum candidate
        | .read f =>
          opRow.size ≥ 1 && opRow.getD 0 0 == f.sourceSlot &&
          (opRow.extract 1 opRow.size).all (· < rank) &&
          f.map.bias.all (· == 0) &&
          opRow.size - 1 == f.map.coeffs.size) &&
      kernel.outputAxes.all (· < rank)

/-- Combined kernel-candidate validity check, real implementation (Task 5): dispatches to
    `validateAffineTable`/`validateEinsum` per candidate kind. Bool-valued (not `Prop`-valued via
    the `Bool → Prop` coercion the task brief's sketch used) so it can also be used directly inside
    `JaxExecutableWellFormed`'s `Array.all` below, which needs a `Bool`-returning predicate. -/
def kernelWellFormedBool : JaxKernelCandidate → Bool
  | .affineTable kernel => validateAffineTable kernel
  | .einsum kernel => validateEinsum kernel

/-- Real well-formedness predicate for a kernel candidate: `kernelWellFormedBool candidate = true`.
    `Decidable` follows automatically from `DecidableEq Bool` — no manual instance needed (the
    earlier stub instance that always answered `.isTrue trivial` regardless of the predicate's
    actual truth has been removed; leaving it would have silently defeated
    `validateAndConstructKernel`'s `decide` check now that this predicate can genuinely be false).
-/
def JaxKernelWellFormed (candidate : JaxKernelCandidate) : Prop :=
  kernelWellFormedBool candidate = true

/-- `Decidable (b = true)` for `b : Bool` should in principle resolve automatically from
    `DecidableEq Bool`, but instance search does not unfold a plain (non-`@[reducible]`) `def` like
    `JaxKernelWellFormed` to expose that shape — confirmed by trying without this instance first
    (`synthInstanceFailed`). `inferInstanceAs` forces the unfold via definitional equality at
    elaboration time (rather than instance-head matching), then delegates to the ordinary
    `Bool` `DecidableEq` instance. -/
instance (candidate : JaxKernelCandidate) : Decidable (JaxKernelWellFormed candidate) :=
  inferInstanceAs (Decidable (kernelWellFormedBool candidate = true))

/-- Type-indexed kernel, only creatable by validator (`validateAndConstructKernel`).
    Evidence is fixed at construction and never changes: `aligned` ties the candidate's
    derived evidence label to the index `evidence`, so the private constructor cannot be
    used to mismatch the two even from within this file.
-/
structure JaxKernel (evidence : ExecutionEvidence) where private mk ::
  candidate : JaxKernelCandidate
  aligned : candidateEvidenceLabel candidate = evidence
  valid : JaxKernelWellFormed candidate  -- real validation (Task 5): `validateAffineTable`/`validateEinsum`

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
  -- `if h : ... then ... else throw`, not `unless decide ... do throw` + a separate `trivial`
  -- proof: now that `JaxKernelWellFormed` does real (possibly-false) validation, `JaxKernel.valid`
  -- needs an actual proof term, not `trivial` (which only ever proves `True`). The `dite` form
  -- (`if h : P then ...`) is what hands that proof (`h`) to the `then`-branch.
  if h : JaxKernelWellFormed candidate then
    -- Construct private kernel only after validation passes.
    let kernel : JaxKernel evidence := {
      candidate := candidate
      aligned := rfl  -- evidence derivation is deterministic
      valid := h
    }
    return { evidence := evidence, kernel := kernel }
  else
    -- `throw`, not `return .error` — `return` in this `Except` do-block already performs the
    -- `.ok` wrap (`pure`), so `return .error x` would elaborate `.error` against the wrong
    -- expected type (`SomeJaxKernel`, not `Except String SomeJaxKernel`) and fail to resolve.
    throw "Kernel validation failed"

/-- Aggregate evidence across an array of kernel evidences.
    Returns `orderedReference64` only if ALL are; otherwise `optimizationExperiment`.
    `evidences.all (· == .orderedReference64)` is vacuously `true` for the empty array, so an
    empty step list aggregates to `orderedReference64` (the identity for the "all" fold).
-/
def aggregateEvidenceList (evidences : Array ExecutionEvidence) : ExecutionEvidence :=
  if evidences.all (· == .orderedReference64) then .orderedReference64
  else .optimizationExperiment

/-- Candidate JAX execution plan (public inspection, not executable).
    Retains the semantic source (`PreparedPlan`) and every step's kernel candidate for validation.
    `aggregated` ties the stored `evidence` to the derived aggregation over `steps`, so a
    `JaxExecutableCandidate` cannot be built claiming evidence its own steps don't support.
-/
structure JaxExecutableCandidate where
  source : PreparedPlan
  steps : Array SomeJaxKernel
  evidence : ExecutionEvidence
  aggregated : evidence = aggregateEvidenceList (steps.map (·.evidence))

/-- Validate an executable plan against its own semantic source, real implementation (Task 5):
    - step count matches the raw semantic plan's own step count (`candidate.source : PreparedPlan`,
      per the Task 5 ruling that corrected `JaxExecutableCandidate.source`'s type — see
      `EvalPlanCodegen.lean`'s `lowerCheckPlanToCandidate` doc comment for the full ruling)
    - every step's kernel candidate is itself well-formed (`kernelWellFormedBool`, not the
      `Prop`-valued `JaxKernelWellFormed` the task brief's sketch used directly inside
      `Array.all` — `Array.all` needs a `Bool`-returning predicate, and `Prop` cannot be
      implicitly used as `Bool`, so `Array.all` is applied to the `Bool`-valued helper instead,
      with the `= true` making the whole conjunct a `Prop` again)
    - the evidence-aggregation invariant, restated as the same proposition
      `JaxExecutableCandidate.aggregated` is itself a proof OF (`candidate.aggregated` names a
      proof TERM, not the proposition — the brief's sketch conjoined the term directly, which does
      not type-check as a `Prop`; restating the equality itself is the fix)
-/
def JaxExecutableWellFormed (candidate : JaxExecutableCandidate) : Prop :=
  candidate.steps.size = candidate.source.plan.raw.steps.size ∧
  candidate.steps.all (fun sk => kernelWellFormedBool sk.kernel.candidate) = true ∧
  candidate.evidence = aggregateEvidenceList (candidate.steps.map (·.evidence))

/-- Same rationale as `JaxKernelWellFormed`'s instance above: instance search does not unfold a
    plain `def` to expose the underlying (fully decidable) conjunction, so `inferInstanceAs` forces
    the unfold via definitional equality, then delegates to the ordinary `Nat`/`Bool`/
    `ExecutionEvidence` `DecidableEq` instances combined through `And`'s standard instance. -/
instance (candidate : JaxExecutableCandidate) : Decidable (JaxExecutableWellFormed candidate) :=
  inferInstanceAs (Decidable (candidate.steps.size = candidate.source.plan.raw.steps.size ∧
    candidate.steps.all (fun sk => kernelWellFormedBool sk.kernel.candidate) = true ∧
    candidate.evidence = aggregateEvidenceList (candidate.steps.map (·.evidence))))

/-- Type-indexed executable plan, only creatable by validator (`validateAndConstructExecutable`).
    Evidence is fixed at construction: `evidenceAligned` ties the candidate's own `evidence`
    field to the index `evidence`, mirroring `JaxKernel`'s `aligned` above.
-/
structure JaxExecutable (evidence : ExecutionEvidence) where private mk ::
  candidate : JaxExecutableCandidate
  evidenceAligned : evidence = candidate.evidence
  valid : JaxExecutableWellFormed candidate

/-- Existential witness hiding the executable's evidence index.
-/
structure SomeJaxExecutable where
  evidence : ExecutionEvidence
  executable : JaxExecutable evidence

/-- Validate a candidate and construct a private executable plan.
    Two checks, mirroring `validateAndConstructKernel`'s shape:
    - the aggregation invariant (`candidate.aggregated` already proves this holds for any
      well-typed candidate, so `decide` on the same equality can never actually fail here — the
      check is kept anyway so a bad aggregation surfaces as a reported error rather than a proof
      obligation silently discharged elsewhere, matching the brief's two-error-path shape);
    - the real `JaxExecutableWellFormed` predicate, via the same `if h : ... then ... else throw`
      (`dite`) shape `validateAndConstructKernel` uses — `JaxExecutable.valid` needs an actual
      proof term now that the predicate does real work, not `trivial` (which only proves `True`).
-/
def validateAndConstructExecutable (candidate : JaxExecutableCandidate) :
    Except String SomeJaxExecutable := do
  unless decide (candidate.evidence = aggregateEvidenceList (candidate.steps.map (·.evidence))) do
    throw "Executable aggregation invariant violated"
  if h : JaxExecutableWellFormed candidate then
    let evidence := candidate.evidence
    let exec : JaxExecutable evidence := {
      candidate := candidate
      evidenceAligned := rfl
      valid := h
    }
    return { evidence := evidence, executable := exec }
  else
    throw "Executable validation failed"

end LeanNCD.Eval.Plan
