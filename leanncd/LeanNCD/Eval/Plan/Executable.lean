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
already exist, and so is the routing in that file's `loweringToAffineTableCandidate`
/`loweringToEinsumCandidate`/`lowerCheckPlanToCandidate`. This file only imports
`LeanNCD.Eval.Plan.Coordinates` for `validateAffineTable`'s own recomputation check (below), the
same shared row-major primitives `EvalPlanCodegen.lean`'s `buildFactorTable` composes — no
JAX/lookup-table/source-name/codegen concept is introduced here.

Task 4.5 (Boolean/predicate outputs) added the SUPPORT half of the gate and the signature-context
ownership the completed spike selected (`papers/jax_signature_evidence_ownership_spike_results.md`,
decision GO B):

* `JaxSupportError`/`checkJaxAssignSupport` reject, with a located typed error, every assignment the
  checked backend admits but this experimental backend cannot render at all — a Boolean destination,
  a Boolean source, tropical max/min algebra, an inline unary read, and (Task 4.5 closure) a
  CONTEXTFUL assignment. Rejection happens BEFORE any candidate, evidence label, or Python emission.
* A standalone entry (`validateAffineTable`/`validateEinsum`/`kernelWellFormedBool`/
  `validateAndConstructKernel`, and the experimental renderers/conversions) takes ONE explicit
  complete `Array TensorSignature` and treats it as its semantic authority: `checkAssign` is re-run
  under it, so a structurally incompatible table fails as `invalidSignatureContext` instead of being
  silently consulted for dtype only. Plan-level entry points accept no such parameter; they derive
  `PreparedPlan.plan.raw.tensorSigs`.
* The raw candidate records store NO signatures. `JaxKernel` stores the validated table
  (`signatureContext`) together with `valid : JaxKernelWellFormed signatureContext candidate`, and
  `JaxExecutableWellFormed` requires every stored table to equal the prepared plan's own and every
  candidate assignment to equal the corresponding checked step.
* `candidateEvidenceLabel` and the context-free geometry helpers are private; the label is derived
  only inside `validateAndConstructKernel`, after validation.

Independently of that ownership question, `validateEinsum` recomputes every operand axis exactly
from the checked factor maps and requires exact `outputAxes = term.outputPos` equality, so a
same-rank, in-range permutation or duplicate is not a valid candidate. It also mirrors the emitter's
three TERM-level structural preconditions (`einsumTermRenderable`: non-empty factors, rank within
`einsumLabelLimit`, complete iteration-position coverage), so acceptance here implies the einsum
lowering actually renders — previously a factor-free, over-rank, or partially-covered candidate was
certified by the validator and then rejected by `lowerTerm`. `einsumLabelLimit` is the one
codegen-derived constant this file states (the emitter's subscript-alphabet size, mirrored not
imported for the dependency-direction reason below, and pinned by a `#guard` on the emitter's side).
Renderability alone is not the standard — agreement is: `einsumTermLabelExtents` additionally
requires every source extent to equal the iteration extent of the label it is emitted with, because
a zero-padded read shorter than its iteration basis renders perfectly well (`a->a`) and returns a
result of a different SHAPE than the checked plan means (`jnp.einsum` takes each label's extent from
the operand, the checked plan takes it from `iterationShape` and zero-pads the rest). That check is
PUBLIC and LOCATED, and the emitter's public `lowerAssign` calls it too rather than re-deriving it,
so the extent rule now rejects on both sides of the same recomputation — the validator refuses the
evidence and the lowering refuses to emit the program.

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

/-- The checked assignment a candidate of either kind refines. -/
private def candidateAssignment : JaxKernelCandidate → CheckedAssignPlan
  | .affineTable k => k.semanticAssignment
  | .einsum k => k.semanticAssignment

/-- Derive the evidence label from a candidate (pure inspection, no validation).

    PRIVATE (Task 4.5, spike selection GO B): a public pre-validation label is the direct bypass of
    the whole gate — a Boolean-source, tropical, or unary-read affine candidate could be handed this
    function and read `orderedReference64` off it before any validator ran. The label is now
    reachable only through `validateAndConstructKernel`'s validated `SomeJaxKernel.evidence`;
    `ExecutableTest` asserts its behavior through that nearest public validator instead of calling
    it directly. -/
private def candidateEvidenceLabel : JaxKernelCandidate → ExecutionEvidence
  | .affineTable _ => ExecutionEvidence.orderedReference64
  | .einsum _ => ExecutionEvidence.optimizationExperiment

/-! ## JAX support policy (Task 4.5)

The experimental JAX backend implements exactly ONE assignment semantics: a real `f64` destination
under real sum-product, gathering plain (non-unary) `f64` reads, at NO runtime context coordinate.
Boolean algebra, tropical max/min, a Boolean source, an inline unary read, and a contextful
assignment are all admitted by the CHECKED plan and executed by Dense, but have no JAX rendering at
all — so they must be rejected with a located, typed error BEFORE any Python is emitted, any
candidate is built, or any `ExecutionEvidence` is exposed. That is the fail-loud half of the
sibling-audit table in `papers/boolean_predicate_output_evalplan.md` §2.5: every "forbidden" cell is
a located rejection here, not a silently-stamped `orderedReference64`.

The supplied `Array TensorSignature` is the caller-facing SEMANTIC AUTHORITY for a standalone entry
point (spike decision GO B): `checkJaxAssignSupport` first re-establishes `checkAssign` for the same
raw assignment UNDER THAT TABLE — a structurally incompatible table is rejected as
`invalidSignatureContext`, not silently used for dtype only — and only then applies the support
policy. Plan-level entry points never accept a caller table; they derive
`PreparedPlan.plan.raw.tensorSigs`. -/

/-- Every located way the experimental JAX backend refuses an otherwise-checked assignment.

    Locators are the ones actually available at each rejection: the outer step index everywhere, the
    ORIGINAL all-factor term/factor indices for a per-factor rejection (never a reindexed
    read-only index), and the slot for the destination rejection. A source rejection carries its
    dtype rather than its slot — the slot is recoverable from the term/factor locator, and the
    4-tuple `nodeIndex termIndex factorIndex dtype` is what the fixtures pin exactly. -/
inductive JaxSupportError
  | destinationDType       (nodeIndex : Nat) (slot : TensorSlot) (dtype : ScalarDType)
  | unsupportedAlgebra     (nodeIndex : Nat) (algebra : ContractionAlgebra)
  -- Task 4.5 closure: the assignment is evaluated at a runtime context coordinate
  -- (`AssignPlan.contextShape` non-empty, every term binding it at its own `contextPos`), which
  -- this backend's kernels have no parameter for at all. Assignment-level, like
  -- `unsupportedAlgebra`: the outer step index is the only locator available, and the rejected
  -- `contextShape` is carried for the same reason that constructor carries its algebra.
  | contextualAssignment   (nodeIndex : Nat) (contextShape : Array Nat)
  | sourceDType            (nodeIndex termIndex factorIndex : Nat) (dtype : ScalarDType)
  | unaryFactor            (nodeIndex termIndex factorIndex : Nat)
  | invalidSignatureContext (nodeIndex : Nat) (cause : PlanError)
  deriving DecidableEq, BEq, Repr

/-- The support policy itself, over a raw assignment already known to check against `sigs`.
    PRIVATE: the context-free half is never a gate on its own — `checkJaxAssignSupport` below is the
    only way in, precisely so a caller cannot skip the `checkAssign` re-run and hand this function a
    table the assignment does not actually satisfy.

    Declared order, which fixtures pin: destination dtype, then algebra, then the context shape, then
    factors in original term/factor order (source dtype before unary within each factor). This
    mirrors `checkAssign`'s own coarse order (destination, algebra, per-term context projection,
    then factors), so the two agree on WHERE the context sits among the properties they both
    inspect. Consequences the fixtures pin in both directions: a Boolean-destination assignment
    whose source is ALSO Boolean reports the destination, a contextful assignment with a Boolean
    DESTINATION or a tropical algebra reports that (they precede), and a contextful assignment with
    a Boolean SOURCE or a unary read reports the CONTEXT (it precedes them).

    The context check reads `a.contextShape` alone; no parallel `terms.any (·.contextPos ≠ #[])`
    conjunct is coded on top of it, because that state is unreachable rather than merely unlikely.
    `checkAssign` — re-run under `sigs` by the gate below before any of this — forces
    `t.contextProjection == a.contextShape` (`contextProjectionMismatch`) and
    `t.positionsPartition`, and the latter puts every `contextPos` entry in range, so
    `contextShape = #[]` implies every term's `contextPos = #[]` for anything that can reach here. A
    term/assignment disagreement is therefore rejected by the `checkAssign` re-run as
    `invalidSignatureContext` carrying the checker's own `PlanError` — NOT conflated into this
    rejection — which the fixtures pin. Same judgement (and same reason: mutation cannot reach a
    conjunct nothing can construct the state for) that `einsumFactorLabelExtentsAgree` records for
    its own absent size tie. -/
private def jaxAssignSupported (sigs : Array TensorSignature) (nodeIndex : Nat) (a : AssignPlan) :
    Except JaxSupportError Unit := do
  match sigs[a.destinationSlot]? with
  | none => throw (.invalidSignatureContext nodeIndex (.slotOutOfRange a.destinationSlot sigs.size))
  | some destSig =>
      unless destSig.dtype == .f64 do
        throw (.destinationDType nodeIndex a.destinationSlot destSig.dtype)
  unless a.algebra == admittedAlgebra do
    throw (.unsupportedAlgebra nodeIndex a.algebra)
  unless a.contextShape.isEmpty do
    throw (.contextualAssignment nodeIndex a.contextShape)
  for h : ti in [0 : a.terms.size] do
    let t := a.terms[ti]
    for h2 : fi in [0 : t.factors.size] do
      match t.factors[fi] with
      | .iverson _ => pure ()  -- the existing located Iverson rejection owns this case
      | .read f =>
        match sigs[f.sourceSlot]? with
        | none => throw (.invalidSignatureContext nodeIndex (.slotOutOfRange f.sourceSlot sigs.size))
        | some srcSig =>
            unless srcSig.dtype == .f64 do
              throw (.sourceDType nodeIndex ti fi srcSig.dtype)
        unless f.unary.isNone do
          throw (.unaryFactor nodeIndex ti fi)

/-- The typed, context-bearing cross-module support gate: the supplied complete signature table is
    the assignment's semantic authority, so `checkAssign` is RE-RUN under it before the JAX support
    policy is applied. A table that is structurally incompatible with the same raw assignment (a
    different shape at a read slot, say) fails as `invalidSignatureContext` carrying the checker's
    own `PlanError`, rather than being used for its dtype tags alone.

    This is the one helper both the production validators here and the experimental renderers /
    candidate conversions in `experiments/jax_bridge/EvalPlanCodegen.lean` call; the latter maps its
    result into that module's own `JaxCodegenError` vocabulary. -/
def checkJaxAssignSupport (sigs : Array TensorSignature) (nodeIndex : Nat)
    (checked : CheckedAssignPlan) : Except JaxSupportError Unit := do
  match checkAssign sigs checked.plan with
  | .error e => throw (.invalidSignatureContext nodeIndex e)
  | .ok _ => pure ()
  jaxAssignSupported sigs nodeIndex checked.plan

/-- `Bool` view of the support gate, for the `Bool`-valued validators below. -/
private def jaxSupportOk (sigs : Array TensorSignature) (checked : CheckedAssignPlan) : Bool :=
  match checkJaxAssignSupport sigs 0 checked with
  | .ok _ => true
  | .error _ => false

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
private def recomputeAffineFactorTable (iterationShape : Array Nat) (factor : ReadPlan) :
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
private def affineFactorTableValid (iterationShape : Array Nat) (factor : ReadPlan)
    (table : AffineTableReadCandidate) : Bool :=
  let (expectedIndex, expectedMask) := recomputeAffineFactorTable iterationShape factor
  table.source == factor.sourceSlot &&
  table.safeIndex == expectedIndex &&
  table.validMask == expectedMask

/-- Whether one term's array of per-factor tables corresponds to that term's own factor list
    (one table per factor, `tables.size = term.factors.size`) and each table is individually valid
    (`affineFactorTableValid`) against that term's own iteration basis (`term.iterationShape`).
    An `.iverson` predicate factor is NOT a read: a term containing one has no valid affine-table
    lowering, so `hasIverson` rejects it explicitly up front — NOT relying on the size check alone,
    since `loweringToAffineTableCandidate`'s `filterMap` happens to shrink `tables` below
    `term.factors.size` whenever a factor is dropped, but that shrinkage is a coincidence of how the
    candidate is built today, not a guarantee this validator should lean on. -/
private def affineTermTablesValid (term : TermPlan) (tables : Array AffineTableReadCandidate) : Bool :=
  !term.hasIverson &&
  tables.size == term.factors.size &&
  (term.factors.zip tables).all
    (fun (factor, table) => match factor with
      | .read r => affineFactorTableValid term.iterationShape r table
      | .iverson _ => false)

/-- Validate an affine-table kernel candidate against its own semantic source AND against the
    caller-supplied complete signature table, which is this standalone entry's semantic authority
    (spike decision GO B): `checkJaxAssignSupport` re-runs `checkAssign` under `sigs` and applies the
    JAX support policy FIRST, so a Boolean-destination, Boolean-source, tropical, unary-read, or
    contextful assignment can never reach the structural table check and be stamped
    `orderedReference64`.
    Structurally: one table array per term (`tables.size = semanticAssignment.plan.terms.size`, per
    `OrderedAffineTableKernelCandidate`'s doc comment "one per term, then per factor"), and every
    per-term table array individually valid (`affineTermTablesValid`). -/
def validateAffineTable (sigs : Array TensorSignature)
    (kernel : OrderedAffineTableKernelCandidate) : Bool :=
  let terms := kernel.semanticAssignment.plan.terms
  jaxSupportOk sigs kernel.semanticAssignment &&
  kernel.tables.size == terms.size &&
  (terms.zip kernel.tables).all (fun (term, tableRow) => affineTermTablesValid term tableRow)

/-- Whether one `AffineMap` row is a pure single-`1` projection, and onto which iteration position.
    `none` covers every non-projection shape at once (a zero row, a non-unit coefficient, or more
    than one nonzero entry).

    Deliberately a PRIVATE, production-local copy of `EvalPlanCodegen.lean`'s `rowProjectionTarget`
    rather than an import of it: `experiments/jax_bridge` depends on `LeanNCD`, never the reverse, so
    importing the experimental recognizer here would invert the dependency direction. Same
    duplicate-for-dependency-direction rationale as `recomputeAffineFactorTable` above (which mirrors
    that module's `buildFactorTable`), and the same consequence: this copy is the SEMANTIC SOURCE
    `validateEinsum` recomputes a candidate's operand row from, not a re-use of the builder's own
    output. -/
private def rowProjectionPosition (row : Array Int) : Option Nat :=
  let nonzero := (List.range row.size).zip row.toList |>.filter (fun (_, c) => c != 0)
  match nonzero with
  | [(p, 1)] => some p
  | _ => none

/-- The iteration positions one checked read factor's coefficient rows project onto, in
    coefficient-row order — i.e. the labels `lowerFactor` (`EvalPlanCodegen.lean`) would emit for it.
    `none` — no valid einsum operand at all — when any coefficient row is not a pure single-`1`
    projection (`rowProjectionPosition`) or any bias entry is nonzero, exactly the two shapes that
    function rejects as `.nonProjectionRow`/`.nonzeroAffineBias`.

    Split out of `expectedEinsumOperandRow` below because the same recomputation answers two
    different questions the emitter asks: which row this factor must lower to, and which iteration
    positions it COVERS (`einsumTermRenderable`). -/
private def einsumFactorPositions (f : ReadPlan) : Option (Array Nat) :=
  if f.map.bias.all (· == 0) then
    f.map.coeffs.foldl
      (fun (acc : Option (Array Nat)) row => match acc, rowProjectionPosition row with
        | some ps, some p => some (ps.push p)
        | _, _ => none)
      (some #[])
  else
    none

/-- The EXACT einsum operand row one checked read factor must lower to: its own source slot,
    followed by the single projection target of EVERY coefficient row, in coefficient-row order
    (`einsumFactorPositions`). `none` exactly when that recomputation has no answer.

    This is a recomputation from the CHECKED factor, not an inspection of the candidate's stored row:
    `validateEinsum` compares the stored row against this one for exact equality, so a same-rank,
    in-range permutation (`#[slot, 1, 0]` for an identity read) or a duplicate (`#[slot, 0, 0]`) is
    rejected — neither is the row this factor means. -/
private def expectedEinsumOperandRow (f : ReadPlan) : Option (Array Nat) :=
  (einsumFactorPositions f).map (fun ps => #[f.sourceSlot] ++ ps)

/-- How many distinct subscript labels one einsum term may use: the size of the emitter's own
    subscript alphabet (`EvalPlanCodegen.lean`'s `labelTable`, `'a'`–`'z'`).

    Mirrored here rather than imported, for the same dependency-direction reason as
    `rowProjectionPosition`/`recomputeAffineFactorTable` (`experiments/jax_bridge` depends on
    `LeanNCD`, never the reverse) — but PUBLIC, unlike those two, precisely so the emitter can pin
    its own table against it (`#guard labelTable.size == einsumLabelLimit`) rather than letting the
    two drift apart silently. -/
def einsumLabelLimit : Nat := 26

/-- Every structural precondition `EvalPlanCodegen.lean`'s `lowerTerm` imposes on ONE checked term,
    over and above the per-factor row shape `expectedEinsumOperandRow` already recomputes. Each
    conjunct mirrors one located emitter rejection:

    * `factors` is non-empty — `.emptyTerm`. `checkAssign` genuinely admits a factor-free term
      (nothing in `Check.lean` requires a factor), Dense executes it as the algebra's factor
      identity, and the affine-table path renders it as `"factors": []`; einsum has no operand list
      to emit at all. This is the precondition whose absence let a factor-free candidate be
      certified `optimizationExperiment` for a lowering that rejects it.
    * `iterationShape.size ≤ einsumLabelLimit` — `.rankTooLarge`. This also covers the emitter's
      per-label `.labelTableExhausted`: `checkAssign` — re-run under `sigs` by the support gate
      before any of this runs — forces every coefficient row's width to equal `iterationShape.size`
      (`affineWidthMismatch`) and `positionsPartition` forces every `outputPos` entry below it, so
      no label position can exceed the limit once the rank does not.
    * every iteration position is covered by some factor's projection — `.uncoveredPosition`. An
      uncovered position is a free label appearing on no operand, which `jnp.einsum` cannot express
      at all, whereas the checked plan means a genuine repeat/reduction over that axis (which the
      affine-table path does honor). Recomputed from the CHECKED factors, like every other einsum
      check here, never read off the candidate's stored operand rows. -/
private def einsumTermRenderable (term : TermPlan) : Bool :=
  let covered := term.factors.foldl
    (fun (acc : Array Nat) factor => match factor with
      | .read f => match einsumFactorPositions f with
        | some ps => acc ++ ps
        | none => acc
      | .iverson _ => acc)
    #[]
  !term.factors.isEmpty &&
  term.iterationShape.size ≤ einsumLabelLimit &&
  (List.range term.iterationShape.size).all (fun p => covered.contains p)

/-- Per-term verdict on einsum LABEL EXTENTS: whether every read factor's SOURCE extents agree with
    the iteration extents of the labels it would be emitted with — source dimension `d`, whose
    coefficient row projects onto iteration position `p` (`einsumFactorPositions`), must satisfy
    `sourceShape[d] = iterationShape[p]`.

    This is a SEMANTIC precondition of the einsum lowering that no structural check can see:
    `jnp.einsum` derives every label's extent from the OPERAND array the label appears on, whereas
    the checked plan derives it from `iterationShape` and zero-pads (`oobPolicy = .zeroPad`, which
    `checkAssign` forces) every source coordinate that falls outside `sourceShape`. When the two
    disagree the rendered contraction does not merely lose precision, it computes a DIFFERENT-SHAPED
    result: `Y[i] := V[i]` with `sourceShape = #[2]` and `iterationShape = #[3]` is a valid checked
    assignment that Dense executes to three values (the third the zero-pad), and renders as `a->a`,
    which returns two. Requiring exact equality is what makes the zero-pad region empty, and only
    then does the rendered einsum mean the same function as the checked plan.

    PUBLIC and LOCATED, unlike the `Bool` conjuncts around it, because it has two consumers that must
    not drift: `validateEinsum` below (which only needs the yes/no) and `EvalPlanCodegen.lean`'s
    `lowerAssign` (which must REJECT the mismatch it would otherwise render happily, with a located
    error naming the offending factor/dimension/position). The emitter calls this recomputation
    rather than growing a third private copy of it — `experiments/jax_bridge` depends on `LeanNCD`,
    never the reverse, so that direction is the only one available and it is also the right one: one
    recomputation, one answer, no possibility of the validator and the emitter disagreeing about
    which candidates have compatible extents.

    `noOperand` is the fail-closed verdict for a factor that has no einsum operand at ALL — an
    `.iverson` predicate, a nonzero affine bias, a non-projection coefficient row, or fewer
    coefficient rows than source dimensions. There are no labels to compare extents for, and each of
    those shapes already has its own rejection on both sides (`validateEinsum`'s `hasIverson` and
    exact `expectedEinsumOperandRow` equality; `lowerTerm`'s `.iversonFactor` and `lowerFactor`'s
    located `.nonzeroAffineBias`/`.nonProjectionRow`), so this verdict never needs to invent one.

    No explicit `positions.size = sourceShape.size` tie is coded: the iteration is over the source
    dimensions, so a SHORT projection array already answers `noOperand` (`positions[d]? = none`), and
    a long one is unreachable — `checkAssign`, which both consumers re-run under their signature
    table before calling this, forces `map.coeffs.size = sourceShape.size` (`affineRankMismatch`).
    Coding the tie anyway would be dead logic no fixture can reach — confirmed by mutation rather
    than assumed: bypassing such a tie broke no guard, because nothing can construct the state it
    excludes. Same judgement `einsumTermRenderable` records for the emitter's
    `.labelTableExhausted`. -/
inductive EinsumLabelExtents
  | agree
  | noOperand (factorIndex : Nat)
  | mismatch  (factorIndex sourceDim position sourceExtent : Nat) (iterationExtent : Option Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The first label-extent disagreement in one checked term, in factor then source-dimension order;
    `.agree` when there is none. See `EinsumLabelExtents` for the full contract. `iterationExtent` is
    `none` exactly when the projected position lies outside the term's own iteration basis — a
    disagreement in its own right, reported here rather than silently skipped. -/
def einsumTermLabelExtents (term : TermPlan) : EinsumLabelExtents := Id.run do
  for h : fi in [0 : term.factors.size] do
    match term.factors[fi] with
    | .iverson _ => return .noOperand fi
    | .read f =>
      match einsumFactorPositions f with
      | none => return .noOperand fi
      | some positions =>
          for h2 : d in [0 : f.sourceShape.size] do
            match f.sourceShape[d]?, positions[d]? with
            | some extent, some p =>
                unless term.iterationShape[p]? == some extent do
                  return .mismatch fi d p extent (term.iterationShape[p]?)
            | _, _ => return .noOperand fi
  return .agree

/-- `Bool` view of `einsumTermLabelExtents` for `validateEinsum`'s conjunct chain: anything other
    than `.agree` — including every `noOperand` shape — is a rejection, exactly as the per-factor
    predicate this replaced was. -/
private def einsumTermLabelExtentsAgree (term : TermPlan) : Bool :=
  einsumTermLabelExtents term == .agree

/-- Validate an einsum kernel candidate against its own semantic source AND against the
    caller-supplied complete signature table, this standalone entry's semantic authority: as in
    `validateAffineTable`, `checkJaxAssignSupport` re-runs `checkAssign` under `sigs` and applies the
    JAX support policy before any structural check.
    `EinsumExperimentKernelCandidate` has one flat `operands`/`outputAxes` pair with no per-term
    dimension, so it can only faithfully represent a SINGLE-TERM `AssignPlan` (see
    `EvalPlanCodegen.lean`'s `loweringToEinsumCandidate` doc comment for the full ruling this
    reflects). Checks:
    - the semantic source has exactly one term (which also subsumes the emitter's `.emptyAssign`)
    - `destination` matches the semantic assignment's own `destinationSlot`
    - the term itself is renderable at all (`einsumTermRenderable`): non-empty factors, rank within
      the emitter's subscript alphabet, and complete iteration-position coverage — the three
      structural preconditions `lowerTerm` imposes (`.emptyTerm`/`.rankTooLarge`/
      `.uncoveredPosition`) that no per-factor row check can see
    - every factor's source extents agree with the iteration extents of the labels it is emitted
      with (`einsumTermLabelExtents`) — a zero-padded read whose source is shorter than the
      iteration basis renders a well-formed einsum string that returns a different-shaped result
      than the checked plan means
    - `operands.size` matches that term's factor count, one operand row per factor
    - each operand row is EXACTLY the row that factor's own affine map means
      (`expectedEinsumOperandRow`): the factor's `sourceSlot` followed by the single projection
      target of every coefficient row, in coefficient-row order. This subsumes the previous
      leading-slot, in-range, zero-bias, and row-count checks — a nonzero bias or a non-projection
      row has NO expected row at all, and a wrong axis order or a repeated axis is a different array
    - `outputAxes` is EXACTLY the checked term's own `outputPos`, not merely a same-rank in-range
      array
    The previous bounds-and-length form of these two checks was strictly weaker than exact
    recomputation: `#[slot, 1, 0]` (a transposed 2-D read), `outputAxes := #[1, 0]` (a transposed
    result), and `outputAxes := #[0, 0]` (a duplicated axis) are all same-rank and in-range, so all
    three passed and were stamped with evidence even though `einsumOnly` would emit a different
    contraction. Recomputing from the checked factor maps is what distinguishes them.

    Acceptance here implies `lowerAssign` renders, and every conjunct above is now mirrored by an
    emitter rejection: the support gate covers `requireJaxSupport`, `hasIverson` covers
    `.iversonFactor`, `einsumTermRenderable` covers `.emptyTerm`/`.rankTooLarge`/
    `.uncoveredPosition`, exact row recomputation covers the bias/projection pair, and the extent
    conjunct covers `.labelExtentMismatch` — which the emitter decides by calling this module's own
    `einsumTermLabelExtents`, not a copy of it. The extent case used to be the one deliberate
    DISAGREEMENT (the emitter rendered what this rejected, since the string it produces is
    well-formed einsum); the whole-branch review ruled that a public lowering entry must not return
    a semantically unsupported program at all, so the gate now sits on both sides of the same
    recomputation. -/
def validateEinsum (sigs : Array TensorSignature)
    (kernel : EinsumExperimentKernelCandidate) : Bool :=
  let terms := kernel.semanticAssignment.plan.terms
  jaxSupportOk sigs kernel.semanticAssignment &&
  kernel.destination == kernel.semanticAssignment.plan.destinationSlot &&
  terms.size == 1 &&
  match terms[0]? with
  | none => false
  | some term =>
      -- `hasIverson` is the real guard, not the `operands.size` coincidence below (see
      -- `affineTermTablesValid`'s doc comment for why the two must not be conflated).
      !term.hasIverson &&
      einsumTermRenderable term &&
      einsumTermLabelExtentsAgree term &&
      kernel.operands.size == term.factors.size &&
      (term.factors.zip kernel.operands).all (fun (factor, opRow) => match factor with
        | .iverson _ => false  -- a predicate factor has no einsum operand; not an einsum candidate
        | .read f => expectedEinsumOperandRow f == some opRow) &&
      kernel.outputAxes == term.outputPos
/-- Combined kernel-candidate validity check, real implementation (Task 5): dispatches to
    `validateAffineTable`/`validateEinsum` per candidate kind. Bool-valued (not `Prop`-valued via
    the `Bool → Prop` coercion the task brief's sketch used) so it can also be used directly inside
    `JaxExecutableWellFormed`'s `Array.all` below, which needs a `Bool`-returning predicate. -/
def kernelWellFormedBool (sigs : Array TensorSignature) : JaxKernelCandidate → Bool
  | .affineTable kernel => validateAffineTable sigs kernel
  | .einsum kernel => validateEinsum sigs kernel

/-- Real well-formedness predicate for a kernel candidate UNDER one complete signature table:
    `kernelWellFormedBool sigs candidate = true`. The table is part of the proposition, not an
    ambient assumption — that is what makes a validated kernel's evidence checkable later
    (`JaxExecutableWellFormed` compares each kernel's stored table against the prepared plan's own).
    `Decidable` follows automatically from `DecidableEq Bool` — no manual instance needed (the
    earlier stub instance that always answered `.isTrue trivial` regardless of the predicate's
    actual truth has been removed; leaving it would have silently defeated
    `validateAndConstructKernel`'s `decide` check now that this predicate can genuinely be false).
-/
def JaxKernelWellFormed (sigs : Array TensorSignature) (candidate : JaxKernelCandidate) : Prop :=
  kernelWellFormedBool sigs candidate = true

/-- `Decidable (b = true)` for `b : Bool` should in principle resolve automatically from
    `DecidableEq Bool`, but instance search does not unfold a plain (non-`@[reducible]`) `def` like
    `JaxKernelWellFormed` to expose that shape — confirmed by trying without this instance first
    (`synthInstanceFailed`). `inferInstanceAs` forces the unfold via definitional equality at
    elaboration time (rather than instance-head matching), then delegates to the ordinary
    `Bool` `DecidableEq` instance. -/
instance (sigs : Array TensorSignature) (candidate : JaxKernelCandidate) :
    Decidable (JaxKernelWellFormed sigs candidate) :=
  inferInstanceAs (Decidable (kernelWellFormedBool sigs candidate = true))

/-- Type-indexed kernel, only creatable by validator (`validateAndConstructKernel`).
    Evidence is fixed at construction and never changes: `aligned` ties the candidate's
    derived evidence label to the index `evidence`, so the private constructor cannot be
    used to mismatch the two even from within this file.

    `signatureContext` is the ONE complete table the validator actually used (spike decision GO B):
    the public raw candidate records deliberately store no signatures, so this validated witness is
    the single place a table becomes authority-bearing, and `valid` is indexed by it. Storing it
    here is what lets `JaxExecutableWellFormed` tie every step's validation context back to the
    prepared plan instead of trusting a kernel validated under some other table.
-/
structure JaxKernel (evidence : ExecutionEvidence) where private mk ::
  candidate : JaxKernelCandidate
  signatureContext : Array TensorSignature
  aligned : candidateEvidenceLabel candidate = evidence
  valid : JaxKernelWellFormed signatureContext candidate  -- real contextual validation (Task 4.5)

/-- Existential witness hiding the evidence index.
-/
structure SomeJaxKernel where
  evidence : ExecutionEvidence
  kernel : JaxKernel evidence

/-- Why `validateAndConstructKernel` refused to expose evidence for a candidate: either the JAX
    support policy rejected the assignment under the supplied context (retaining the exact located
    `JaxSupportError`), or the candidate's own tables/operands do not match its semantic source. -/
inductive JaxKernelValidationError
  | unsupported (cause : JaxSupportError)
  | invalidCandidate
  deriving DecidableEq, BEq, Repr

/-- Validate a candidate UNDER one complete signature table and construct a private executable
    kernel. Returns `SomeJaxKernel` to hide evidence at the cost of unpacking later.

    The support gate runs FIRST and returns its exact located cause; only then is structural
    well-formedness decided, and only then — inside the `then`-branch, after `h` exists — is the
    evidence label derived at all. An unsupported candidate therefore never reaches
    `candidateEvidenceLabel`, which is itself private for the same reason.
-/
def validateAndConstructKernel (sigs : Array TensorSignature) (candidate : JaxKernelCandidate) :
    Except JaxKernelValidationError SomeJaxKernel := do
  match checkJaxAssignSupport sigs 0 (candidateAssignment candidate) with
  | .error e => throw (.unsupported e)
  | .ok _ => pure ()
  -- `if h : ... then ... else throw`, not `unless decide ... do throw` + a separate `trivial`
  -- proof: now that `JaxKernelWellFormed` does real (possibly-false) validation, `JaxKernel.valid`
  -- needs an actual proof term, not `trivial` (which only ever proves `True`). The `dite` form
  -- (`if h : P then ...`) is what hands that proof (`h`) to the `then`-branch.
  if h : JaxKernelWellFormed sigs candidate then
    -- Derive the evidence label only after validation passed, and construct the private kernel
    -- with the very table the validation used.
    let evidence := candidateEvidenceLabel candidate
    let kernel : JaxKernel evidence := {
      candidate := candidate
      signatureContext := sigs
      aligned := rfl  -- evidence derivation is deterministic
      valid := h
    }
    return { evidence := evidence, kernel := kernel }
  else
    -- `throw`, not `return .error` — `return` in this `Except` do-block already performs the
    -- `.ok` wrap (`pure`), so `return .error x` would elaborate `.error` against the wrong
    -- expected type (`SomeJaxKernel`, not `Except JaxKernelValidationError SomeJaxKernel`) and
    -- fail to resolve.
    throw .invalidCandidate

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

/-- Why a candidate's own semantic source (`JaxExecutableCandidate.source : PreparedPlan`) does not
    tie its source-name bindings to its OWN checked raw plan (whole-branch review round 4).

    Every constructor reuses an existing typed failure rather than inventing a parallel vocabulary:
    `requiredInputs` carries `checkBindings`' own `BindingsError` (the very rule the required
    bindings were originally built by, re-applied against `raw.inputSlots`), and `materializedSlot`
    carries the `PlanError.slotOutOfRange` the shared `PlanBindings.materializedWith` path already
    raises everywhere else in this subsystem. `materializedNotPublished` is the one genuinely new
    shape — see `checkPreparedBindings` for what it asserts and why. -/
inductive PreparedBindingsError
  | requiredInputs           (cause : BindingsError)
  | materializedSlot         (cause : PlanError)
  | materializedNotPublished (index : Nat) (slot : TensorSlot)
  deriving DecidableEq, BEq, Repr

/-- Does this `PreparedPlan`'s `PlanBindings` describe THIS `PreparedPlan`'s own raw plan (Task 4.5
    closure, whole-branch review round 4)?

    `JaxExecutableWellFormed` used to ignore `source.bindings` entirely: it tied every STEP to the
    prepared plan (context table, checked assignment, contextual well-formedness) but nothing tied
    the source-name sidecar to anything. So a `PreparedPlan` carrying a materialized binding at slot
    99 over a two-slot plan, or a `requiredInputs` built by `checkBindings` against a DIFFERENT
    plan's `inputSlots`, received real executable evidence — evidence about a plan that cannot
    honour it, since `unpack`/`materializedSignatures` reject the first and `pack` cannot resolve
    the second.

    Three obligations, all decidable from `plan.raw` alone — no source AST, no fabricated name, no
    caller-supplied context:

    * **required tie.** `checkBindings raw.inputSlots requiredInputs.bindings` must succeed: the
      binding slots are a permutation of the raw plan's OWN `inputSlots` and no source name is bound
      twice. Deliberately the SAME rule (and the same error family) `RequiredBindings` was
      constructed by, just re-applied against `raw.inputSlots` instead of the `inputSlots` field the
      value happens to store — which is exactly the coupling `RequiredBindings`' doc comment says
      its own `aligned` proof does NOT establish. `Perm`, not positional equality, because `pack`
      resolves by NAME: a reordered `bindings` array is legal (`AdapterTest` Check 5 pins that) and
      stays legal here, while a missing, extra, duplicated, or out-of-plan slot is not.
    * **materialized in range.** Resolved through the shared `PreparedPlan.materializedSignatures`
      (i.e. `PlanBindings.materializedWith` over `raw.tensorSigs`) rather than a private re-check,
      so "this executable's bindings are valid" and "this plan's materialized signatures resolve"
      are the same statement, reported with the same `PlanError.slotOutOfRange` value.
    * **materialized publication order.** `prepareEvalPlan` publishes each materialized name at a
      FRESH destination slot allocated after every input slot and after every earlier publication
      (Step D allocates every input first, then pushes each destination at `tensorSigsAcc.size`), so
      the slot sequence is strictly increasing and disjoint from `raw.inputSlots`. Both halves are
      re-derivable from `raw` alone, so both are checked: an entry not strictly greater than every
      input slot and every previous materialized slot is `materializedNotPublished`, carrying its
      index and slot. That is what rejects an in-range materialized binding naming an INPUT slot
      (publishing an input's own tensor under an output name) or naming one destination twice. It
      constrains SLOTS, not names: a name legitimately reassigned by a later statement appears twice
      with two different, increasing slots (`materializedNames`' own doc comment), and stays valid.

    What is deliberately NOT checked, because it is not re-derivable here: WHICH name belongs to
    which slot. `raw` carries no source names at all, so a candidate that swaps two required
    bindings' names between two input slots, or renames a materialized binding, satisfies every
    obligation above. Establishing that would need the source AST (or a caller-supplied name table);
    fabricating either would be worse than the gap, because the name-to-slot association's authority
    is `prepareEvalPlan`, and this file must not invent a second one. -/
def checkPreparedBindings (source : PreparedPlan) : Except PreparedBindingsError Unit := do
  let raw := source.plan.raw
  match checkBindings raw.inputSlots source.bindings.requiredInputs.bindings with
  | .error e => throw (.requiredInputs e)
  | .ok _    => pure ()
  match source.materializedSignatures with
  | .error e => throw (.materializedSlot e)
  | .ok _    => pure ()
  -- The lower bound starts at the largest input slot (computed by fold rather than read off the end
  -- of `inputSlots`, so this does not silently depend on `checkStepGraph`'s ascending-order
  -- guarantee), then advances to each materialized slot in turn.
  let mut bound : Option TensorSlot :=
    raw.inputSlots.foldl (fun acc s => some (match acc with | some m => max m s | none => s)) none
  for h : i in [0 : source.bindings.materializedNames.size] do
    let b := source.bindings.materializedNames[i]
    match bound with
    | some m => unless m < b.slot do throw (.materializedNotPublished i b.slot)
    | none   => pure ()
    bound := some b.slot

/-- `checkPreparedBindings` as the decidable `Bool` `JaxExecutableWellFormed` conjoins. Defined in
    terms of that function, never re-deriving the rule, so the proposition and the error a caller
    receives cannot disagree about which candidates are valid. -/
def preparedBindingsTied (source : PreparedPlan) : Bool :=
  match checkPreparedBindings source with
  | .ok _    => true
  | .error _ => false

/-- Whether one validated kernel really is THIS prepared plan's step `stepIndex` (Task 4.5, spike
    decision GO B). Three obligations, all of which a plan-level caller must satisfy and none of
    which a kernel validated in isolation can supply on its own:

    * its stored validation context is exactly the prepared plan's own complete signature table — a
      kernel validated under some other (say, same-shape all-real) table is not evidence about this
      plan, even if its assignment matches;
    * its candidate's semantic assignment is exactly the checked assignment at that step index —
      re-using step 0's validated kernel at step 1 is rejected, which is what keeps a per-step
      support decision from being cached across steps; and
    * it is still well-formed under that stored table (the same contextual predicate the private
      constructor already required, restated here so the plan-level proposition is self-contained).

    A `.scan`/`.pointwise`/`.axiswise` step has no JAX kernel at all, so any candidate claiming one
    at that index fails the second obligation. -/
private def stepTiedToPreparedStep (prepared : PreparedPlan) (stepIndex : Nat)
    (sk : SomeJaxKernel) : Bool :=
  sk.kernel.signatureContext == prepared.plan.raw.tensorSigs &&
  (match prepared.plan.checkedNodes[stepIndex]? with
   | some (.assign checked) => checked.plan == (candidateAssignment sk.kernel.candidate).plan
   | _ => false) &&
  kernelWellFormedBool sk.kernel.signatureContext sk.kernel.candidate

/-- Validate an executable plan against its own semantic source, real implementation (Task 5,
    extended by Task 4.5):
    - step count matches the raw semantic plan's own step count (`candidate.source : PreparedPlan`,
      per the Task 5 ruling that corrected `JaxExecutableCandidate.source`'s type — see
      `EvalPlanCodegen.lean`'s `lowerCheckPlanToCandidate` doc comment for the full ruling)
    - every step's validated kernel is tied to the corresponding prepared step
      (`stepTiedToPreparedStep`: stored context = prepared table, candidate assignment = that
      step's checked assignment, and contextual well-formedness under the stored table). This
      replaces the previous context-free `kernelWellFormedBool` conjunct, which could accept a
      kernel validated under an unrelated all-real table, or the same kernel repeated at every step
    - the candidate's own semantic source ties its source-name bindings to its own raw plan
      (`preparedBindingsTied` — required bindings a name-unique permutation of `raw.inputSlots`,
      materialized bindings in range through the shared resolution path and in `prepareEvalPlan`'s
      own publication order). Without this conjunct the whole `PlanBindings` sidecar was
      unconstrained: a materialized slot 99 over a two-slot plan, or a `requiredInputs` checked
      against some other plan's `inputSlots`, still received evidence
    - the evidence-aggregation invariant, restated as the same proposition
      `JaxExecutableCandidate.aggregated` is itself a proof OF (`candidate.aggregated` names a
      proof TERM, not the proposition — the brief's sketch conjoined the term directly, which does
      not type-check as a `Prop`; restating the equality itself is the fix)
-/
def JaxExecutableWellFormed (candidate : JaxExecutableCandidate) : Prop :=
  candidate.steps.size = candidate.source.plan.raw.steps.size ∧
  (candidate.steps.mapIdx (fun i sk => stepTiedToPreparedStep candidate.source i sk)).all id = true ∧
  preparedBindingsTied candidate.source = true ∧
  candidate.evidence = aggregateEvidenceList (candidate.steps.map (·.evidence))

/-- Same rationale as `JaxKernelWellFormed`'s instance above: instance search does not unfold a
    plain `def` to expose the underlying (fully decidable) conjunction, so `inferInstanceAs` forces
    the unfold via definitional equality, then delegates to the ordinary `Nat`/`Bool`/
    `ExecutionEvidence` `DecidableEq` instances combined through `And`'s standard instance. -/
instance (candidate : JaxExecutableCandidate) : Decidable (JaxExecutableWellFormed candidate) :=
  inferInstanceAs (Decidable (candidate.steps.size = candidate.source.plan.raw.steps.size ∧
    (candidate.steps.mapIdx (fun i sk => stepTiedToPreparedStep candidate.source i sk)).all id
      = true ∧
    preparedBindingsTied candidate.source = true ∧
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

/-- Why `validateAndConstructExecutable` refused to expose evidence for a plan-level candidate.
    Mirrors `JaxKernelValidationError`'s shape one tier up, and replaces the three bare `String`
    messages this function used to throw — a caller could not tell an aggregation violation from a
    detached binding from a step mismatch without reading the message text.

    `invalidBindings` carries the located `PreparedBindingsError` (whole-branch review round 4), so
    the reason the source's own bindings do not describe its own raw plan survives to the caller
    instead of collapsing into `invalidCandidate`. -/
inductive JaxExecutableValidationError
  | aggregationMismatch
  | invalidBindings (cause : PreparedBindingsError)
  | invalidCandidate
  deriving DecidableEq, BEq, Repr

/-- Validate a candidate and construct a private executable plan.
    Three checks, mirroring `validateAndConstructKernel`'s shape:
    - the aggregation invariant (`candidate.aggregated` already proves this holds for any
      well-typed candidate, so `decide` on the same equality can never actually fail here — the
      check is kept anyway so a bad aggregation surfaces as a reported error rather than a proof
      obligation silently discharged elsewhere, matching the brief's two-error-path shape);
    - the binding tie (`checkPreparedBindings`), run BEFORE the whole predicate so its located
      cause reaches the caller — the predicate itself only conjoins the `Bool` view of the same
      function, which cannot say WHICH obligation failed;
    - the real `JaxExecutableWellFormed` predicate, via the same `if h : ... then ... else throw`
      (`dite`) shape `validateAndConstructKernel` uses — `JaxExecutable.valid` needs an actual
      proof term now that the predicate does real work, not `trivial` (which only proves `True`).
-/
def validateAndConstructExecutable (candidate : JaxExecutableCandidate) :
    Except JaxExecutableValidationError SomeJaxExecutable := do
  unless decide (candidate.evidence = aggregateEvidenceList (candidate.steps.map (·.evidence))) do
    throw .aggregationMismatch
  match checkPreparedBindings candidate.source with
  | .error e => throw (.invalidBindings e)
  | .ok _    => pure ()
  if h : JaxExecutableWellFormed candidate then
    let evidence := candidate.evidence
    let exec : JaxExecutable evidence := {
      candidate := candidate
      evidenceAligned := rfl
      valid := h
    }
    return { evidence := evidence, executable := exec }
  else
    throw .invalidCandidate

end LeanNCD.Eval.Plan
