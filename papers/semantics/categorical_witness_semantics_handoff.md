# New-session brief: explain and verify the landed witness-span interpretation

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

## Copyable launch instruction

```text
Read papers/semantics/categorical_witness_semantics_handoff.md on latest
local main. Explain and verify the existing Lean witness-span category,
its all-input component interpretation, composition and nested-bracket
coherence, and its restricted partial-map connection.

This formalization has already landed. Do not reimplement it, author a
replacement implementation plan, apply historical task patches, or replay
the completed seven-task plan. Use the existing APIs and tests. Preserve
all unrelated edits and worktrees; do not push.

Deliver a concise explanation and a verification report distinguishing
checks actually rerun from historical release evidence. State the exact
semantic profile and remaining source/process/backend boundaries. If a
load-bearing discrepancy is found, report it and stop rather than expanding
this read-only task into a repair or another categorical slice.
```

**Process weight:** read-only onboarding and verification, not a Full
implementation slice. No new implementation plan or mutation manifest.
Use direct targeted reads; do not dispatch parallel reimplementation work.

## 1. Starting state and reading order

The witness-span formalization merged to local main in `f2abbe8a`.
The completed synthesis is recorded in `11ca0fc1`. These are provenance,
not fixed starting HEADs: start from latest local main and check its APIs.
The previous version of this handoff's implementation instructions is
superseded; the target-category laws are no longer open.

Read:

1. [Synthesis](categorical_tensor_logic_semantics.md), Section 10,
   especially the progress ledger and remaining branches.
2. [Witness semantics record](categorical_witness_semantics_record.md),
   its current-status, completed-deliverable and release-evidence sections.
   The later design audit is explicitly historical.
3. [Lean instructions](../../leanncd/AGENTS.md), then the source windows
   listed below.
4. [Model-gluing record](component_model_gluing_record.md) only when the
   component comparison needs its underlying restriction/gluing argument.

The main checkout is `/Users/williammacready/code/python/pyncd`.
Its existing semantics-contents edits and other worktrees are protected.
The public denotational entry module is
[IndexedWitnessSemantics.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessSemantics.lean)
(`import IndexedWitnessSemantics`), namespace `IndexedWitness`.
It belongs to the nondefault `IndexedExecutionExperiment` target, not
the production `LeanNCD` import.

## 2. What has been formalized

- **Objects:** metadata-bearing `WholeInterface` values retain tensor UIDs,
  sorts, complete coordinate domains and exhaustive port rosters, including
  empty tensors. Interface objects are not quotiented by environment-carrier
  equivalence or matching extents.
- **Arrows and equivalence:** spans of interface environments, modulo an
  apex bijection commuting with both boundary legs. Different complete stores
  remain distinct witnesses, even if their outputs agree; proof terms do not
  create extra witnesses.
- **Composition and units:** compatible-pair pullbacks and identity spans.
  Span-isomorphism congruence, both unit laws and associativity descend to
  an ordinary `Category.{1} WholeInterface` instance.
- **Component meaning:** `componentSpan` pairs every validated
  `Program.Input` with every complete `Program.Models` store on that input.
  Its legs reconstruct the input environment and project whole outputs.
  Private values and actual contribution-definedness are retained.
- **Composition comparison:** `allInputWiredEquiv` and `compositeWiredIso`
  identify composite witnesses with compatible component witnesses, commuting
  with both exterior legs after explicit input/output reindexing.
  `composition_hom` includes the specified boundary environment transport.
- **Nested coherence:** both actual source bracketings map to one compatible
  complete-model triple. `bracketSpanIso` and `bracket_hom` compare them
  after interface transport, not by equal raw UIDs or source programs.
- **Partial maps:** injective-left spans admit quotient-invariant partial-map
  extraction. For components, injectivity is exactly `AtMostOneModels`;
  domain/value laws agree with authoritative admissibility and denotation.
  Successive component laws retain both at-most-one-model hypotheses.

The component interpretation is for the finite decidable `Declarations Unit`,
exact-rational, explicitly wired matched-component profile. Rational
environments and complete models are not thereby finite.
Objects and quotient homs live in `Type 1`, while environments and individual
apexes live in `Type 0`; do not claim same-universe local smallness.

## 3. Targeted source map

Locate identifiers with `rg -n`; read approximately 40-60-line windows.
No whole-file survey of large proof modules or unrelated backends.

| Check | Identifiers @ file |
| --- | --- |
| Interface metadata and input/output correspondence | `WholeInterface`, `WholeInterface.Env`, `inputEquiv`, `outputEquiv` @ [IndexedWitnessInterface.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessInterface.lean) |
| Quotient category and complete-model apex | `Span`, `SpanIso`, `WitnessHom`, `homComp`, `SpanIso.pullback`, `SpanIso.leftUnit`, `SpanIso.rightUnit`, `SpanIso.assoc`, `componentSpan` @ [IndexedWitnessSpan.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessSpan.lean) |
| All-input comparison and both boundary squares | `boundaryEnvEquiv`, `compositeInputEquiv`, `compositeOutputEquiv`, `allInputWiredEquiv`, `compositeWiredIso`, `composition_hom` @ [IndexedWitnessComposition.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessComposition.lean) |
| Actual nested component bracketings | `leftNestedBoundary`, `rightNestedBoundary`, `leftTripleEquiv`, `rightTripleEquiv`, `bracketSpanIso`, `bracket_hom` @ [IndexedWitnessCoherence.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessCoherence.lean) |
| Restricted domain and values | `RestrictedHom.partialOption`, `component_injective_iff`, `component_domain_iff`, `component_value`, `component_composite_value` @ [IndexedWitnessPartial.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessPartial.lean) |
| Underlying model gluing | `witnessesEquiv`, `outputProjection_transport` @ [IndexedComponentModelWitnesses.lean](../../leanncd/experiments/indexed_execution/IndexedComponentModelWitnesses.lean) |

Use the existing tests rather than inventing new acceptance cases:

- [IndexedWitnessTest.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessTest.lean):
  empty inputs, distinct hidden witnesses with equal outputs, namespace audits.
- [IndexedWitnessCompositionTest.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessCompositionTest.lean)
  and [IndexedWitnessCoherenceTest.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessCoherenceTest.lean):
  explicit transports, component comparisons and bracket-coherence audits.
- [IndexedWitnessPartialTest.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessPartialTest.lean):
  `strict_no_domain`, `total_domain`, `downstream_selection_not_unrestricted`.
- [IndexedWitnessObservationProbeTest.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessObservationProbeTest.lean)
  and [IndexedWitnessObservationParity.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessObservationParity.lean):
  discriminating copied observations and their separate generic parities.

## 4. Verification procedure and evidence

1. Record the actual local-main starting commit. Confirm the entry module,
   nondefault target registration and source declarations above.
2. For builds, use an isolated latest-local-main worktree and the `new-slice`
   skill. Run `prepare-worktree.sh` from that worktree without `--plan`;
   require its warm-Mathlib verification. Preserve existing edits and stop
   rather than cold-building Mathlib.
3. Run the existing full verification targets through the wrapper:

   ```bash
   bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD Tests IndexedExecutionExperiment
   ```

   This refreshes project-owned oleans before any single-file check.
   If fresh namespace-audit output is needed, use `lean-file.sh` on an
   existing test module, for example:

   ```bash
   bash <worktree>/leanncd/scripts/lean-file.sh <worktree>/leanncd experiments/indexed_execution/IndexedWitnessTest.lean
   ```

4. Explain the proof obligations from the actual declarations: quotient
   congruence and laws; complete all-input apex; both composition legs;
   transported nested bracketings; and the uniqueness restriction.
   Separate generic Lean proofs from fixture and mutation observations.
5. Consult the [integration receipt](categorical_witness_semantics_artifacts/integration_receipt.json),
   [release receipt](categorical_witness_semantics_artifacts/release_receipt.json),
   [mutation table](categorical_witness_semantics_artifacts/execution_verified_mutations.md),
   [soundness review](categorical_witness_semantics_artifacts/review_soundness.md)
   and [integration review](categorical_witness_semantics_artifacts/review_integration.md).
   They record the prior full build, ten unfiltered mutation controls and
   final reviews; they are not evidence that this new session reran them.

Do not replay historical patches, regenerate release receipts, or rerun the
mutation campaign by default. Report any failed, skipped or unavailable check
explicitly. Keep reads bounded; report any dispatch exceeding approximately
60 turns or 250k context rather than claiming unmeasured budget compliance.

## 5. Required report and exclusions

Deliver a concise explanation of objects, arrows, equivalence, composition,
units and laws, followed by the exact component-comparison transports,
complete-witness retention and restricted partial-map assumptions.
List the starting commit, commands actually run and their outcomes; label
historical evidence separately. State any discrepancy with its identifier
and proof impact.

The result is a **composition-preserving denotational interpretation**, not
yet a source functor. Source-category syntax/laws, event-sensitive process
units, rank stitching, phase/state/trace projection, and frontend/backend
refinement remain separate open work. Administrative graph spans are semantic
wires, not event-free core computations; input aliases violate
`output_defined`, and copies add execution events.

Do not weaken strict complete-array definedness, hide private models, assume
uniqueness implies existence, or extract a purported compositional partial map
from arbitrary multi-model spans. Do not change the core language, runners,
registry, interfaces or production imports. No broader St/Br/PROP, monoidal
or numerical/backend claims follow from the ordinary category laws.

Any follow-on implementation or repair requires a separately agreed scope.
