# Task 4 prototype: restricted partial witness semantics

Status: compiled, with focused fixtures; no commit. The only prototype source
files edited were `leanncd/experiments/indexed_execution/IndexedWitnessPartial.lean`
and `leanncd/experiments/indexed_execution/IndexedWitnessPartialTest.lean`.
The controller report is this file. The pre-existing modification to
`leanncd/lakefile.toml` and the peer's `IndexedWitnessCoherence.lean` were not
edited. No git index changes were made.

## Result and exact interfaces

`IndexedWitnessPartial.lean` imports `IndexedWitnessComposition` and
`IndexedComponentModelDenotation` and defines `IndexedWitness.Span.Domain`,
`Span.value`, `Span.partialOption`, `RestrictedSpan`, and the quotient
`RestrictedHom.partialOption`. Domain is existential witness occupancy; value
uses the unique witness on an inhabited domain; `Option.none` represents
absence, not an invented store or default output.

`SpanIso.injective_left_iff`, `SpanIso.domain_iff`,
`SpanIso.value_eq`, and `SpanIso.partialOption_eq` establish invariance
under apex equivalence and both leg commutations. `restrictedSetoid` and
`RestrictedHom.partialOption` make extraction well-defined on the restricted
quotient; `InjectiveLeftHom` and `partialDomain` record the corresponding
properties on the existing `WitnessHom` quotient. These constructions do
not extract a partial function from arbitrary spans.

`Span.identity_injective`, `Span.graph_injective`, and
`Span.pullback_injective` preserve the restriction.
`Span.pullback_domain_iff` and `Span.pullback_value` prove existential
composition-domain and successive-value equations without totality.
`component_injective_iff` identifies left injectivity with the authoritative
`IndexedComponentComposition.AtMostOneModels`;
`component_domain_iff` identifies the domain with
`Program.AdmInput` under that hypothesis; `component_value` identifies the
value with `Program.denotation`.

Under **both** `AtMostOneModels A` and `AtMostOneModels B`,
`wired_injective`, `wired_domain_iff`, and `wired_value` instantiate
the restricted pullback equations for the explicitly wired component spans.
`composite_rebased_injective`, `composite_rebased_domain_iff`, and
`composite_rebased_value` transport these laws through the pre-existing
`compositeWiredIso`, including its exterior adapters.
`composite_atMostOne`, `component_composite_domain`, and
`component_composite_value` separately connect the actual composite
program's domain and value to the authoritative
`admInput_restrictions_iff` and `denotation_successive`.
No source functor, process/event law, or totality theorem is asserted.

## Focused donors and differences

`IndexedComponentModelLocalFixtures.strict_no_model` and
`IndexedComponentModelLocalTest.strict_no_composite` supply a genuinely
empty domain: the fixture proves vacuous `AtMostOneModels` while
`strict_consumer_undefined` extracts `none`, distinguishing uniqueness from
existence. `IndexedComponentModelLocalTest.total_composite_model` supplies a
populated domain. The cyclic donors
`IndexedComponentModelCycleFixtures.cycle_upstream_zero_model`,
`cycle_upstream_not_admissible`, and
`IndexedComponentModelCycleTest.cycle_one_model`,
`cycle_composite_unique` supply a selection counterexample:
`downstream_selection_not_unrestricted` proves the composite has one
witness at the chosen input while its upstream span is **not**
injective-left. The new proofs concern span domains and quotient-respecting
extraction; they do not modify donor fixtures.

## Observed receipts and bounds

`bash /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-prototype/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-prototype/leanncd IndexedWitnessPartial`
completed successfully (2982 jobs). The same command with target
`IndexedWitnessPartialTest` completed successfully (8630 jobs).
`#audit_axioms IndexedWitness` audited 226 constants and
`#audit_axioms IndexedWitnessPartialTest` audited 8 constants using only
standard axioms; selected `#print axioms` outputs list only `propext`,
`Classical.choice`, and `Quot.sound` (or just `Classical.choice`).
No `sorry`, `admit`, `native_decide`, or nonstandard axioms remain.
Only those two named build targets were requested; no whole-experiment
build or source commit was performed.

Budget: approximately 70 individual tool invocations, including parallel
source-window reads and repeated targeted proof builds, exceeded the
requested hard limit of 60 actions if each tool invocation counts as an
action. Conversation turns were fewer than 40, and retained context was
below 250k. This breach is reported rather than silently ignored.

Remaining task-4 obligations: none within the requested restricted
prototype. Integration/whole-branch review and any broader experiment
build remain with the controller after peer work settles.
