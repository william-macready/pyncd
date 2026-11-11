# New-session brief: compare operational and complete-model semantics

## Bootstrap: read this from latest local main

A newly opened session worktree can predate this file. Start by reading the
primary-checkout copy:
`/Users/williammacready/code/python/pyncd/papers/semantics/categorical_operational_witness_comparison_handoff.md`.
Do not treat an unsuccessful search in a stale worktree as evidence that the
brief is missing everywhere. If necessary, inspect the committed copy with one
separate read-only command:

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd show main:papers/semantics/categorical_operational_witness_comparison_handoff.md
```

Then use `new-slice` to prepare an isolated worktree against latest **local**
main, not an old remote base. A tool waiting for approval is a permission
checkpoint, not proof work: surface it and wait for approval; do not bypass it.

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> disclose any breach.

## Copyable launch instruction

```text
Read
/Users/williammacready/code/python/pyncd/papers/semantics/categorical_operational_witness_comparison_handoff.md
from latest local main, even if the current worktree predates that file.
Prepare and verify one implementation plan, then execute it, for a compositional
comparison from the existing ranked operational category to the existing
complete-model witness category.

Audit the rank/termination/model bridge first. Reuse actual default execution,
completed_model, failed_has_no_model, ranked_default_terminal, componentSpan,
the existing span-isomorphism/category laws and the provenance-aware operational
source/target categories. Prove required domain/uniqueness consequences rather
than assuming success, model existence or execution agreement.

Construct a genuine comparison functor on the operational TARGET quotient,
not only a leaf theorem or a second interpretation of source syntax. It must
respect administrative wires/units, actual binary composition, exterior maps
and complete witness spans. Prove compatibility with the two existing source
interpretations through an explicit rank/provenance-forgetting source map,
or an equally precise verified common-source construction.

State exactly what the comparison forgets: event order, intermediate histories,
failure diagnostics and assembly provenance are not retained by witness spans.
Do not weaken the existing operational equality, erase complete-model private
stores, extend to arbitrary unranked programs or claim faithfulness/equivalence.

Keep the slice nondefault and additive. Preserve unrelated edits/worktrees,
use repository release gates, merge locally when green and reviewed, and do
not push. Report a load-bearing design or theorem blocker rather than silently
substituting output-only comparison or assuming quotient descent.
```

**Implementation process: Full.** A new categorical comparison and quotient
soundness surface require verified prototyping and a plan. This document is a
goal brief, **not an implementation plan or new proof receipt**.
The handoff session performed only a targeted read-only API audit; new
declarations, module splits, fixtures and mutation diagnostics remain to be
prototyped and measured by the next session.

## 1. Starting point and intended result

Two interpretations have landed:

- The unrestricted supplied-match source presentation interprets into
  `IndexedWitness`: metadata-bearing whole interfaces and spans of validated
  inputs with **complete model stores**, modulo span isomorphism.
- A distinct ranked/provenance-aware source interprets into
  `IndexedRankedOperationalCategory.Target`: full-observation equivalence of
  administrative wires and ranked computations, with fixed transports,
  exterior wires and original assembly provenance. Its connected `Realizes`
  bridge preserves actual inherited-state histories under explicit frame
  conditions.

The next result should connect these constructions, not re-prove units,
associativity, model gluing or the existing execution correspondence.

Read:

1. [Synthesis](categorical_tensor_logic_semantics.md), especially Proposed next
   steps, Sections 6.10-6.13 and 10.3, and Appendices A.9-A.12.
2. [Ranked operational record](categorical_ranked_operational_interpretation_record.md),
   final scope and Sections 8-9; historical intermediate gaps are superseded.
3. [Witness record](categorical_witness_semantics_record.md) and
   [source record](categorical_source_functor_record.md), for exact witness
   multiplicity, interface maps and categorical claims.
4. [Lean instructions](../../leanncd/AGENTS.md), then the targeted APIs below.

## 2. Candidate comparison: prototype before committing to it

The natural candidate sends:

- an operational object to its underlying metadata-bearing whole interface;
- an administrative wire to the existing graph span of its certified
  environment equivalence;
- a computational normal arrow to its complete-model component span,
  with both explicit exterior wires applied in the correct directions.

`Normal.source` already maps a normal arrow to an old witness-source term
by forgetting rank/provenance annotations and retaining its exterior wires.
This is a useful candidate representative map, **not an existing proof that
the map descends through operational agreement**.

The central missing theorem is:
operationally agreeing normal arrows have isomorphic rebased complete-model
spans, commuting with **both** exterior legs.
It must cover arbitrary admitted representatives of the operational quotient,
not just a chosen source term, a particular assembly tree or fixture.

A candidate commuting diagram has the existing ranked source functor followed
by the new comparison agree with source erasure followed by the existing
witness functor. Choose and prove functor equality when object maps permit it,
or an explicit natural isomorphism with its object/interface transports.
No new functor/type names are prescribed by this brief.

The exact comparison representation may change after the bounded audit, but
do not silently reduce the goal to source-level pointwise agreement.

## 3. Bounded audit and load-bearing proof obligations

### A. Derive the precise ranked model/domain bridge

The audited existing APIs provide:

- `completed_model`: actual checked success gives a full final store that
  satisfies `Models`, is the unique model on that input, and has the stated
  output denotation.
- `failed_has_no_model`: actual checked undefined failure excludes every
  complete model on that input.
- `ranked_default_terminal`: a matched ranked component on validated input has
  an actual default success or failure, not blocked/exhausted execution.

These are ingredients for proving success iff complete-model existence, failure
iff no complete model, and at-most-one complete models across all validated
inputs in this **matched ranked profile**. Derive the exact statements and
their hypotheses; do not describe the consequences as already implemented.
Ranking excludes blocking, not partial-primitive failure and not model absence.

If existing `AtMostOneModels`/injective-left machinery is used, prove its
required hypothesis from the audited ranked bridge or state a justified
narrower domain explicitly. Do not silently add an unexplained uniqueness,
totality, completion or execution-agreement premise.

### B. Descend from full operational agreement to complete witnesses

`ComputeAgrees` fixes a metadata transport, provenance/adapter equivalence and
full raw exterior squares before quantifying over every external input.
Exploit that structure and the actual final-state/model bridge.

Provide a bijection of the relevant all-input complete witnesses, with both
external legs commuting. Preserve **whole private model stores** in the
construction; merely equating outputs or existence propositions is insufficient
for an equality in the existing witness-span category.
An optional factorization through injective-left partial maps is acceptable
only after proving the required injectivity and exact span comparison.

The comparison need not preserve the operational provenance distinction:
an opaque and a joined origin of the same compiled program may map to the
same witness meaning. This is intentional forgetting in the new functor,
not permission to equate them in the operational category.

### C. Prove categorical structure with authoritative existing maps

Construct a genuine functor from the existing operational target quotient
to the existing witness category, including:

- well-definedness for every operational agreement case;
- administrative wire/identity images and inverse/composed-wire behavior;
- binary composition preservation using `composition_hom`,
  `compositeWiredIso`, original boundaries and explicit exterior maps;
- rank-certificate independence, with provenance handled as specified;
- compatibility with actual nested composition, without redoing the
  completed operational associativity or witness pullback proofs.

Do not use equal-cardinality or name-based identification of interfaces.
Empty interfaces remain metadata-bearing objects even when their environments
are singleton carriers.

### D. Connect the two SOURCE interpretations and actual outcomes

The ranked source and the old witness source have distinct object wrappers and
different generating relations. Construct an explicit source map dropping
rank/origin annotations, or a verified common-source interpretation, and check
every retained generator. Their quotients must not be identified by fiat.

Prove the comparison diagram on the actual source categories/functors, with
identity/composition and exterior coherence, not just syntax normalization.
Connect its component instance to actual `runChecked` and
`Program.Executor.run` outcomes through the existing correspondence.
Administrative arrows require no core program.

The main comparison can forget the inherited outside frame: component witness
stores belong to the component's owned declarations. State that boundary
explicitly. Do not reinterpret `Realizes` as running checked programs on
arbitrary prepopulated local private stores, or infer a new generic
cross-program reference-state transport theorem.

### E. Make information loss and scope explicit

Witness spans retain complete witnesses and exterior maps; they do not retain
ordered operational events, intermediate stores/ledger prefixes, failure tags
or assembly origins. Failed-input fibers have no complete witness, so distinct
strict failure diagnostics can be forgotten without converting failure into
successful execution.

The comparison is directed from the richer ranked operational interpretation
to witness meaning. Do not claim an inverse, faithfulness, categorical
equivalence or recovery of an operational history from an arbitrary span.
Unranked cyclic programs with hidden model multiplicity remain legitimate
witness examples outside the operational source restriction.

## 4. Discriminating acceptance goals

These are donor/delta requirements for plan authoring, **not observed new
fixtures or verified cycle counts**. The plan supplies exact instances,
measurements, nearest legal neighbors and intended mutation diagnostics.

| Goal | Existing donor and required distinction |
|---|---|
| Strict failure versus model domain | `consumerComponent` total/strict neighbors, `privateOrigin`, and private success/failure-A/B/C donors: visible output before private failure must not create a complete-model witness. |
| Success retains private complete stores | `privateRows`, `privateReferenceCuts` and actual private component histories: recover the entire model, not just the boundary value, and compare both exterior legs. |
| Administrative identity and nonconstant wires | Ranked `rotate`/`rotateDomain`, `wireObservation`/`wireControls`, and axis donors: identity gives the identity span; a nonidentity wire gives its actual graph span, with correct input/output direction. |
| Binary and nested composition | `privateLeft`, `privateRight`, `privateReassociation`, `privateInteriorUnit`: compare the two functor routes through actual joined provenance and both original boundaries. |
| Intentional loss of provenance | Instantiate `opaque_not_joined` on a legal ranked compiled donor; distinct operational origins should have the same complete-model image when the underlying component/exterior maps agree. This must not change operational equality. |
| Empty metadata and input presence | Existing empty component/source donors: keep distinct interface objects and explicit empty input presence despite singleton environment carriers. |
| No extension to hidden multiplicity | `hiddenZero`, `hiddenOne`, `hidden_witnesses_distinct`, `hidden_outputs_equal`, and `hidden_no_rank`: retain the old span's distinct witnesses; do not infer a general unique-model or executable-history interpretation. |

Use only certified operational arrows for comparison-functor instances.
`reorderedTripleRun` is a graph-only control without a component match; it is
not a ready-made legal operational representative.
If an extra information-loss example is needed, prefer the existing
opaque/joined distinction over inventing a scheduler theorem.

Controls should distinguish wrong exterior orientation, omitted private
store/model data, false success after strict failure, failure treated as a
zero-valued successful witness, dropped empty presence, unsound unranked
extension and accidental faithfulness/provenance claims.
Classify live-proof controls separately from type-valid runtime observations;
setup refusal and type errors are not runtime defect kills.

## 5. Targeted source map

All experiment paths below are under
[`leanncd/experiments/indexed_execution/`](../../leanncd/experiments/indexed_execution/).
Use `rg -n` and approximately 40-60-line windows around the identifiers.

| Identifiers @ file | Role |
|---|---|
| `completed_model`, `failed_has_no_model`, `ranked_not_blocked` @ `IndexedCompositionValidated.lean`; `complete_semantics`, `failed_no_model`, `ranked_actual_dichotomy` @ `IndexedCompositionSemanticResults.lean` | Actual graph/reference/model bridge |
| `ranked_default_terminal` @ `IndexedComponentExecutionRuns.lean`; `actualHistory`, `actualHistory_spec`, `actualObservation`, `Normal.source` @ `IndexedRankedOperationalCore.lean` | Rank-sensitive terminality, actual histories and candidate representative erasure |
| `ComputeAgrees`, `Agrees`, `ProvenanceIso`, `reindexExterior`, `normalSetoid`, `Target`, `targetCategory`, `opaque_not_joined` @ `IndexedRankedOperationalCategory.lean` | Existing fixed all-input operational quotient and source of descent obligations |
| `Object`, `Term`, `Rel`, `sound`, `semantics`, `source_assembly`, `bracket_sound` @ `IndexedRankedOperationalSource.lean` | Ranked/provenance-aware source and genuine operational functor |
| `Term.denote`, `sound`, `semantics` @ `IndexedSourceFunctor.lean`; `Term`, `Rel` @ `IndexedSourceSyntax.lean` | Existing unrestricted source and witness functor |
| `WholeInterface`, `inputEnv`, `envInput`, `inputEquiv`, `outputEquiv` @ `IndexedWitnessInterface.lean` | Metadata-bearing object and validated exterior environments |
| `Span`, `SpanIso`, `Span.identity`, `Span.pullback`, `componentSpan` @ `IndexedWitnessSpan.lean` | Complete all-input witness apexes, both legs and target equality |
| `Span.graph`, `graphHom`, `Span.rebase`, `SpanIso.rebaseGraphs`, `boundaryEnvEquiv`, `compositeInputEquiv`, `compositeOutputEquiv`, `compositeWiredIso`, `composition_hom` @ `IndexedWitnessComposition.lean` | Administrative and actual binary witness semantics |
| `AtMostOneModels` @ `IndexedComponentModelDenotation.lean`; `component_injective_iff`, `component_domain_iff`, `component_value`, `RestrictedHom.partialOption` @ `IndexedWitnessPartial.lean` | Optional proved injective-left/partial-map route; not an unrestricted uniqueness assumption |
| `Realizes`, `Frame.FreshInput`, `Coherent`, `source_history`, `semantics_history` @ `IndexedRankedOperationalInterpretation.lean`; `actualReferenceObservation` @ `IndexedRankedOperationalReference.lean` | Actual realization and frame/reference boundaries to preserve |
| Ranked donors @ `IndexedRankedOperationalTest.lean`; `hiddenZero`, `hiddenOne`, `hidden_witnesses_distinct` @ `IndexedWitnessTest.lean`; `hidden_no_rank` @ `IndexedComponentRankedExecutionFixtures.lean` | Legal comparison instances and negative multiplicity/rank controls |

## 6. Process, release gates and non-goals

Audit the exact rank/model and quotient-descent statements before drafting
implementation tasks. If a candidate comparison is not well-defined, record
the precise obstruction; do not work around it by assuming execution agreement
or reducing the deliverable to a successful-output theorem.

Use `slice-plan` and `new-slice`, warm Mathlib and the prescribed build wrappers.
Prototype on the real module split, then author one verified plan in a fresh
bounded context from compiled artifacts. Ship mechanically generated per-task
patches and mutation manifests with observed intended diagnostics. Keep the
live plan separate from its evidence record.

Use approximately three work items per dispatch. Split before approximately
60 turns or 250k peak context; authoring targets 50M cumulative input tokens
and execution caps at 175M. Run `token-report.py`; disclose unavailable
telemetry and any breach rather than declaring an unmeasured pass.

Keep new proof/test APIs nondefault under `IndexedExecutionExperiment`, with a
discoverable entry point and matching Lean instructions. Controller gates:
all unfiltered intended-diagnostic mutation cycles with restored builds and
source hashes, namespace/source proof audits, full
`LeanNCD Tests IndexedExecutionExperiment` wrapper build, and two final
whole-branch review lenses:

- comparison/descent soundness, complete witness bijections, both exterior
  legs, source-map/diagram coherence and exact uniqueness/domain hypotheses;
- actual graph/reference integration, strict private failure, empty metadata,
  administrative wires, provenance information loss and discriminating controls.

Update the synthesis only for implemented results. Preserve concurrent main
work; merge locally when green and reviewed, remove only owned worktrees and
branches, and do not push. Close-out states the actual comparison functor,
commuting diagram, input/model/failure hypotheses, intentionally forgotten
observations and remaining boundaries.

**Excluded:** frontend/backend refinement, numerical semantics, a bialgebraic
pilot, monoidal/PROP or broader interface development, generic unranked
operational semantics, solver/model search, new runner/core operators, new
operational observation quotients, arbitrary-frame execution or generic
reference-state transport, and re-proving existing category/gluing laws.
