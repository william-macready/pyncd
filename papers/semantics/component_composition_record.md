# Static sealed composition: authoring and execution record

[Handoff](component_composition_handoff.md) |
[Interface design](categorical_tensor_logic_component_interfaces.md)

## Status

The static constructor and its composed correspondence instances are now
implemented and verified in the prototype. Authoring control verification is
in progress; this is not yet a verified execution plan or release completion.
Ranked phase execution, model gluing and categorical laws remain unproved.

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

## Concrete assembly checkpoint

Prototype `43a01ec9` adds `IndexedComponentCompositionAssemble`; its generated,
reverse-checked patch was committed in `cb298129`.

- `closureScope A B wire` derives all five generic structural premises.
- `contract`, `fragment` and `graph` instantiate the upstream-first assembly
  with the existing embeddings, checked even/odd identities and tensor order.
- `close_ok A B wire` proves actual closure acceptance with only the two
  matched components and their explicit boundary as arguments.
- `input_roles`, `tensor_order`, `outputs_exact`, `canonical_steps` and
  `graph_steps` supply the construction facts needed by the match proof.

The controller built the assembly module and recompiled the expanded
foundation audit. It checked 206 composition constants and 68 local-fixture
constants with only standard axioms, including actual closure acceptance and
exact downstream output-address coverage.

The assembly dispatch estimated 58 action turns: over its 40-turn target,
but within the 60-turn checkpoint. A genuine composite occurrence-to-writer
match and its local evaluation/priority proofs are still in progress.

## Constructed executable observations

The controller built `IndexedComponentCompositionTest` successfully
(2,991 jobs). These are executions of newly assembled graph/source data,
not applications of a completed composite match yet.

| Construction | Observed outcome and retained work |
| --- | --- |
| Scalar, `other = 0` | Six events: `+1`, `-1`, publish `Pre = 0`, square writer, publish `Out = 0`, undefined private `Audit`; failed, not completed |
| Scalar, `other = 4` | Seven events, including private `Audit = 1/2` and its publication; complete |
| Zero-writer producer, total consumer | Five events, beginning with publication of `Pre = 0` from its retained empty capability list, then all consumer work |
| Empty boundary and output | Present required empty external input completes with zero events; external input UID `20` and output-port UID `3` survive independently of the empty address list |
| Missing empty input | Rejected at tensor UID `20` |
| Simultaneous missing external input and unexpected downstream binding | Appended validation rejects UID `20`; reversed and UID-sorted orders reject UID `3`, distinguishing both faults and orders |

Both actual graph and source observations retained the strict/total scalar
values and event sequences. Their new graph IDs are tags `20`, `22`, `41`,
`61`, capabilities `202`, `204`, `403`, `603`, and tensor UIDs `0`, `3`, `5`.
The zero-writer contract contains collector `(0, [])` and exactly the two
consumer writers, not a forwarding writer.

The match prototype stopped at its approximately 60-action-turn checkpoint
with occurrence/writer equivalence, indexed writer equations, ordered reads
and all-partial-store evaluation agreement compiled. Defined-downstream
destination transport and priority remain separate narrower proof tasks.
No incomplete match is substituted for the required correspondence premise.

## Gates still required

Finish the bounded prototypes, verify discriminating fixtures and controls,
author a fresh execution plan from mechanically generated compiled patches,
review that plan, execute every verified task, run the controller's unfiltered
mutation checks and cycles, exact patch/probe checks and full three-target
build, then complete both whole-branch review lenses. Local-main integration
and cleanup are authorized only after those gates pass; no push is authorized.

## Constructed match and exact public premises

`IndexedComponentComposition.compose_match` takes two `MatchedComponent`
values over finite decidable `Declarations Unit` universes and a `Boundary`.
The boundary supplies a bijection of all downstream inputs to all upstream
outputs and a certified whole-domain adapter for each pair.
`compose` additionally packages the constructed data and exact whole ports
as a `MatchedComponent`, without a rank requirement.

The public constructors choose checked even/odd tensor, tag and capability
identities. No caller supplies composite closure, a composite match, collector
fiber agreement, selected actions, reached-store equality or execution
agreement.

| Match field | Derivation |
| --- | --- |
| `close_ok` | `ClosureFacts`, local accepted closures, derived `closureScope`, disjoint checked identities, and `close_assembled` establish actual canonical acceptance |
| `input_roles` | Upstream roles are retained; explicitly wired downstream inputs denote upstream defined outputs |
| `tensor_order` | Contract and schedule use the same complete Nodup upstream enumeration followed by filtered downstream defined tensors |
| `outputs_exact` | Transport downstream exact output-address coverage; separate whole-port metadata retains empty outputs |
| `sourceToWriter` | Actual occurrence equivalence, the two supplied local bijections, and mapped/concatenated writer-position equivalences |
| `writer_destination` | Both local destination equations followed by address transport, including the proved dependent downstream-domain cast identity |
| `writer_reads` | Local ordered list equality and footprint transport, preserving repeats and strict whole-array footprints |
| `eval_agrees` | Restrict every composite partial store by the appropriate address embedding, apply local agreement, and transport both evaluations |
| `priority` | Exact collector lookup transport, component full priority equations, appended key equivalence and canonical step append |

The final priority dispatch committed `9b038737` and its exact patch
`745c8b19`, reporting approximately 42 action turns against a 30-turn target
and 60-turn hard checkpoint. The previous collector-only priority dispatch
reported an action-cap breach and failed full/snippet checks while its
destination dependency was being edited; those were not counted as passes.
The repaired destination and final priority dependencies subsequently built.

The controller built the public constructor and
`IndexedComponentCompositionCorrespondenceTest`. Its strict, total, zero,
guarded-collision and unequal-axis instances apply the existing
`default_run_correspondence` to constructed matches. The empty instance
quantifies over every raw binding, including missing and unexpected bindings.
No four-occurrence composite match was independently authored.

## Additional discriminating controls

- Collision Pre has one statement and three valuations, with guards
  `[true, false, true]`; admitted valuations remain distinct and ordered
  `v2` then `v0`. Pre is `2`, exterior Out is `4`, and the independently
  retained private values are `7` and `5/2`.
- The supported unequal-axis adapter maps the nonpalindromic repeated
  footprint to `(2,0), (0,1), (2,0), (0,1)`; actual Out is `14`.
  The fixture's shared named first point permits a fixture-source mutation
  without invalidating its local source/writer agreement first.
- Typed controls accept downstream Out and the supplied `2x3`/`3x2`
  permutation, but prove that downstream input Pre is not a defined
  destination and that equal cardinality `6` cannot supply a `2x3`/flat-`6`
  axis adapter.
- A graph-only strict shortcut completes after seven events where the
  original constructed graph fails after six; it is not process-equivalent.
- A coherent graph-only omission of one equal contribution completes after
  eight events with Pre `1` and Out `1`, instead of the original Pre `2`,
  Out `4` and nine events.
- Dropping the zero-writer collector is rejected as `missingCollector`.
  Duplicating the boundary collector is rejected as `duplicateCollector`.

The graph-only altered data do not carry a forged composite match.
The new post-code mutation manifest distinguishes live proof controls,
fixture-source/binding controls, typed controls and graph-only counterexample
controls. Its unfiltered anchor check passed all 16 entries; actual failure
diagnostics and restored results are being observed before authoring the plan.

## Authoring mutation observations

The initial controller run passed 16/16 failure/restoration cycles, including
byte-identical source restoration. That first run deliberately had no
`expect` strings; it gathered diagnostics, not an intended-failure-certified
release receipt.

Inspection showed the first axis-point mutation stopped at local agreement
proofs because the source body still used the donor point directly. The
fixture was corrected to share its named point in the source body as well as
the writer body and read list. Its corrected cycle reached the executable
`axis.graph-only` check and restored green; no proof failure or aborted
evaluation is credited as that fixture's runtime kill.

The final manifest now contains observed, line-number-independent diagnostic
substrings for every entry. Seven controls stop at live proof/type obligations,
two are typed accept-neighbour controls, three change fixture source/bindings,
and four change graph-only counterexample computations. These are not
claimed as 16 live-production runner kills or per-assertion-complete coverage.
The controller is rerunning every entry without filters against those exact
diagnostic requirements before the fresh plan-authoring dispatch.
