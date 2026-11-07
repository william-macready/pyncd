# Static sealed composition: authoring and execution record

[Handoff](component_composition_handoff.md) |
[Interface design](categorical_tensor_logic_component_interfaces.md)

## Status

Prototype authoring is in progress. This is not a verified execution plan or
a completion claim. No composite match, split-fixture correspondence, ranked
phase theorem, model gluing or categorical law is claimed here yet.

## Scope and preparation

- Process weight: Full, because this adds a semantic construction and proof
  surface, not a localized guard change.
- Worktree: `pyncd.worktrees/follow-directions-component-composition`.
- Branch: `agents/follow-directions-component-composition`.
- Base: latest local main `16721af5` at preparation.
- The existing isolated worktree was clean and had no branch-only commits.
  `prepare-worktree.sh` fast-forwarded it from `91447658` to the base.
- Cache verification: 8,101 Mathlib oleans / 8,094 sources, 100%, and
  374 project oleans. No cold Mathlib build.
- Controller `lake-build.sh <worktree>/leanncd LeanNCD` passed.
- Controller baseline `lake-build.sh <worktree>/leanncd LeanNCD Tests` also
  passed, before composition integration.
- The instruction hook's Patterns and Global Pitfalls sections measured
  2,984 characters; no instruction trimming was required.
- Primary-checkout edits to the semantics contents and categorical synthesis
  are protected. Their SHA-256 hashes are retained in controller session
  evidence. Other worktrees are outside this task.
- The transport plan is completed prerequisite evidence, not this slice's
  execution plan.

## Controller foundation: declarative closure facts

Prototype commit `35c718d5` adds `IndexedComponentClosureFacts`.

- `ClosureFacts.of_close` extracts declarative invariants from actual accepted
  component closure.
- `ClosureFacts.close` proves those invariants sufficient for the existing
  `close` function to return the canonical graph.
- `mem_definedAddresses_iff` and `ClosureFacts.collector_iff` expose exact
  noninput coordinate coverage, including zero-writer fibers.
- The closure function, runners, validation order, registry and language
  partiality were not changed.
- Both the single-file wrapper and `check-snippet.sh` passed on the committed
  prototype bytes, with no warning or omitted proof.
- An additional namespace-audit import exposed a default-heartbeat timeout in
  the broad `simp_all` extraction proof. Commit `aef43d65` narrows extraction to
  its two relevant validation guards, without changing statements or runners.
  The source-copy snippet then compiled and audited 349 constants under
  `IndexedOpenComposition`, all with standard axioms; `ClosureFacts.close`
  uses only `propext`, `Classical.choice` and `Quot.sound`.

These facts are reusable proof infrastructure. They do not by themselves
prove that assembling two components satisfies the composite closure checks.
That derivation remains part of the in-progress prototype.

## Controller foundation: genuinely local acceptance donors

Prototype commit `de88993b` adds `IndexedComponentCompositionLocalFixtures`.
The producer's declaration universe is `Fin 1`, containing only `Pre`.
The consumer's universe contains exactly input `Pre`, output `Out` and
private `Audit`; its input has no standalone collector.

`producerMatch` and `consumerMatch other` independently supply their local
matches. The consumer retains the existing `squareBody`, `auditBody` and
`strictArray` expression helpers; this is not an independent interpreter
oracle. No four-occurrence composite match is authored in this fixture.

Final `check-snippet.sh` passed and observed:

| Local component | Outcome | Events | Last available coordinates |
| --- | --- | --- | --- |
| Producer | complete | 3 | `Pre = 0` |
| Consumer, `other = 0`, present `Pre = 0` | failed | 3 | `Pre = 0`, `Out = 0`, `Audit` absent |
| Consumer, `other = 4`, present `Pre = 0` | complete | 4 | `Pre = 0`, `Out = 0`, `Audit = 1/2` |

The required composite's six and seven events are not inferred by summing
these rows. They remain to be observed after construction and correspondence.
The source-copy namespace audit checked 65 local-fixture constants with only
standard axioms, including both local supplied matches.
The controller mechanically exported both foundation commits as
`closure_facts.patch` and `local_fixtures.patch` in
`component_composition_artifacts/`.

## Reobserved donor, not composite evidence

Controller single-file validation of `IndexedCompositionParityTest` passed.
The actual output reobserved:

- Strict and total terminal/event/intermediate parity: `(true, true, true)`.
- Event counts: `(6, 7, some 6, some 7)`.
- Strict failure retains the already-published `Out` but does not report
  complete success.
- Total completion retains private `Audit = 1/2`.

This is existing whole-program donor evidence only. Acceptance requires
observing these outcomes through the new constructor from genuinely local
producer and consumer matches.

## Accounting

`token-report.py 166c28b7-d291-45be-9935-ac49e19535cb` reported no supported
transcript. Measured cumulative-input-token compliance is therefore not
asserted. Prototype dispatches were given the handoff's 60-turn / 250k retained
context cap and instructed to report any breach.
The closure/priority prototype agent estimated approximately 90 assistant
action turns, exceeding its 60-turn cap by roughly 30. That count is not
instrumented and peak context was not measured. The breach is not silently
treated as compliance.
The scope/source/schedule prototype agent estimated approximately 80 action
turns against the same 60-turn cap. Its peak context was also unmeasured.
Subsequent dispatches were narrowed and instructed to return compiled partial
work at the checkpoint instead of extending past the cap.

## Scope/source/schedule prototype checkpoint

The three real-split foundation modules were committed in `083ea97c`;
`8739276d` registered the independently owned closure and local fixtures.
The scope agent reported the experiment green at registration, 8,621 jobs.

The controller subsequently built all five registered foundation modules and
ran the exact [foundation audit](component_composition_artifacts/foundation_audit.lean)
through `check-snippet.sh`. It checked 193 composition constants and 68
local-fixture constants, with only standard axioms. The occurrence/key
equivalences, closure/priority preservation and both local matches use only
`propext`, `Classical.choice` and `Quot.sound`.

The constructed source and schedule retain the disjoint tensor universe,
whole-port metadata, transported statements/valuations/guards and appended
complete duplicate-free tensor/key orders. No composite match is claimed by
this checkpoint.

## Closure/priority prototype checkpoint

The delegated prototype committed `74318cd9` and reported a warning-free
single-file check of `IndexedComponentCompositionClosure`. Its exports
transport writers, collector rows and steps, assemble upstream-first data,
and prove `close_assembled` and `canonicalSteps_assembled`.

`ClosureScope` retains five structural premises to be derived by the concrete
component construction: upstream input-role preservation, downstream defined
noninputs, complete defined-address image coverage, disjoint defined images,
and downstream input addresses belonging to upstream collectors. These are
not yet discharged by a constructed composite here.

Controller single-file validation against the refreshed closure foundation
passed. A source-copy audit also passed, checking 48 constants with only
standard axioms. The general closure/priority theorems use only `propext`,
`Classical.choice` and `Quot.sound`.

Concrete scope-premise derivation and composite match construction remain
pending. These foundation checks do not substitute for the release gates.

## Gates still required

Finish the bounded prototypes, verify discriminating fixtures and controls,
author a fresh execution plan from mechanically generated compiled patches,
review that plan, execute every verified task, run the controller's unfiltered
mutation checks and cycles, exact patch/probe checks and full three-target
build, then complete both whole-branch review lenses. Local-main integration
and cleanup are authorized only after those gates pass; no push is authorized.
