# New-session brief: execution histories and operational associativity

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> disclose any breach.

## Copyable launch instruction

```text
Read papers/semantics/categorical_operational_associativity_handoff.md on
latest local main. Prepare and verify one implementation plan, then execute
it, for transport-aware execution histories and operational associativity
of the existing ranked sealed matched components.

Specify the observation relation first: preserve ordered events, strict
failures, whole-interface metadata and all normalized state observations,
including private values and ordered produced ledgers. Define compatible
history composition, prove transport/congruence and associativity laws,
and connect them to both actual nested compose executions.

Reuse compositeRankCertificate, compose_default_phases and
reference_default_phases. Do not replace the runner, assume execution
agreement, discard private work, or reprove denotational/source-category laws.
Prove success and failure in each of the three components, shared boundary
snapshots, explicit coordinate/identity transport and actual default budgets.

Defer units and the full process category. A core copy is not an event-free
identity. Preserve unrelated edits/worktrees; use repository release gates,
merge locally when green and reviewed, and do not push. Report a load-bearing
design, plan or theorem blocker rather than weakening the observations.
```

**Process weight for implementation: Full.** This adds generic operational
proof capabilities and an observation-equivalence soundness surface.
This is a goal brief, **not a verified implementation plan**. No new Lean
declaration, module split, fixture result or mutation diagnostic is claimed
verified here. The next session must prototype and verify those before
authoring its execution plan.

## 1. Starting point and intended next result

The finite decidable `Declarations Unit`, exact-rational, explicitly wired
sealed profile already has:

- Static `compose` and a constructed `SourceContractMatch`.
- Complete-model gluing, witness-span category laws, nested denotational
  coherence and a certified source-category witness functor.
- Constructed full-footprint composite ranks, actual default graph execution
  phases and normalized reference phase/state projections.

The remaining step is not to establish binary sequencing again. It is to
package the proved binary decomposition as a compositional observation of
execution and prove its coherence under actual reassociation.

Read:

1. [Synthesis](categorical_tensor_logic_semantics.md), Sections 6.11,
   10.1-10.3 and Appendix A.10.
2. [Ranked execution record](categorical_ranked_execution_record.md), for
   exact premises, state relations, failure normalization and release scope.
3. [Source record](categorical_source_functor_record.md), to distinguish
   existing denotational source laws from the new operational target.
4. [Lean instructions](../../leanncd/AGENTS.md), then the targeted APIs below.

This brief adopts the proposed staging discussed with the user:
**observation relation, compatible history composition, then operational
associativity; units later**. The synthesis leaves the precise observation
representation open. Its implementation must therefore justify that choice,
not describe a particular quotient as already established.

## 2. Observation contract: decide before implementation

Use the strongest transport-only comparison needed for this slice. Different
bracketings allocate different tensor UIDs, tags and capabilities; raw list
equality is not the goal. Compare through explicit coherent transports, not
through equality of final outputs or arbitrary event permutations.

The observation must retain:

- Metadata-bearing input/output interfaces, validated external input and
  explicit boundary/domain adapters, including empty tensor presence.
- Every ordered production, publication and undefinedness event, retaining
  occurrence ownership, tag/capability identity, destination and value as
  applicable to the existing event constructors.
- Every normalized snapshot's entire available/published store and ordered
  produced ledger, including private work and already completed phases.
- Success versus failure, the transported failing occurrence/tag and its
  terminal state. An undefined event must not acquire an extra failed-state
  snapshot.
- The reference relation's pending occurrences and accumulators when
  comparing reference observations, not only graph availability or outputs.

A candidate representation is histories compared after transport to a common
leaf-owned declaration/event space. Another explicit relational presentation
is acceptable if it proves the same observations and laws. Choose the simplest
one that works on the real module split. State the admissibility/compatibility
conditions for histories and what the relation deliberately does not forget.
Prove identity, inverse and composite transport laws, or their equivalent
relational reflexivity/symmetry/transitivity statements.

Do not:

- Merge distinct admitted occurrences or equal-valued contributions.
- Drop private events, intermediate stores, publication order or failure data.
- Match axes by names, equal extents or cardinality.
- Use unrestricted numeric renaming to hide a wrong leaf/occurrence mapping.
- Derive empty-input presence from address enumeration.
- Add a scheduler-independent reordering or stuttering quotient.

A bare relation defined to mean "these two chosen runs agree" is not a
compositional observation theory. Conversely, do not introduce a heavyweight
quotient category merely to state transported history equality.

## 3. Required algebra and actual-run obligations

### Compatible history composition

Define sequencing for well-formed compatible observations:

- After upstream success, obtain downstream input only from its whole
  completed boundary through `boundaryInput`/`boundaryFromOutput`.
- Splice ordered events without a wire/copy/boundary event.
- Glue snapshots at one shared boundary state, retaining the completed
  upstream private state and ledger throughout the suffix.
- Upstream failure absorbs the continuation: retain its history and failure
  without requiring a completed boundary or executing downstream work.

The operation may take a downstream continuation indexed by the completed
boundary rather than a preselected downstream history; do not require a
successful upstream output in the failure case.
Prove compatibility with the chosen transports/observation relation and
associativity for composable histories. Make these genuine reusable laws,
not fixtures or a new interpreter. Reuse the already proved binary run
decomposition to connect the algebra to actual executions.

### Both actual nested constructors

For matched `A`, `B`, `C`, supplied `ab : Boundary A B`,
`bc : Boundary B C`, three local rank certificates and validated input for
`A`, compare:

- `leftBracket`: compose `A` with `B`, then compose that result with `C`
  using `leftNestedBoundary`.
- `rightBracket`: compose `B` with `C`, then compose `A` with that result
  using `rightNestedBoundary`.

These are existing declarations in `IndexedWitnessCoherence`, not proposed
new constructor names. Reuse their static boundaries and interface squares;
their complete-model span isomorphism is **not** an operational proof.
Prefer proving missing operational transport lemmas without refactoring the
completed witness/source layer.

Construct both nested ranks with `compositeRankCertificate`. Lift the same
external input through the actual input maps. Derive coherent full-address,
occurrence, tag and capability transports; nested parity allocations are not
literally equal. Derive both original boundary equations at the history
level, preserving certified coordinate transport through both joins.

Prove equivalent complete observations for the actual default
`IndexedOpenComposition.runChecked` executions of both bracketings.
Use actual `Program.Executor.run` and `referenceSnapshots` for the
reference counterpart, transferring the full existing `Relation`.
Do not substitute `IndexedExecution.run` or the public graph `run`, which
revalidates/regenerates its graph.

Cover all four outcome branches: failure in `A`, failure in `B` after `A`
succeeds, failure in `C` after both predecessors succeed, and all succeed.
No execution-completion, model-existence, uniqueness, final-store agreement
or selected-action equality may be assumed. Private failure after visible
output must still stop all later phases.

### Snapshots, fuel and validation

For successful reached joins, prove explicit ordered phase cuts with no
duplicated boundary snapshot. Empty/vacuous phases may share a cut index;
do not require two distinct cuts or introduce snapshots to distinguish them.
In failed histories, preserve the existing undefined-event/no-extra-snapshot
normalization.

Prove the two actual nested default graph budgets agree with their constructed
step counts. With standalone counts `nA`, `nB`, `nC`, the target bound is
`nA + nB + nC + 1`, not the sum of three standalone defaults.
Reuse existing nonexhaustion/fuel results rather than assuming equal debug
fuel or changing the runner.

State the main theorem on validated input. Invalid raw inputs retain each
constructor's existing full-tensor validation order. Do not extend
associativity to arbitrary malformed bindings, assume both validators
report the same first error, or require now-internal boundary inputs.

## 4. Proposed discriminating acceptance goals

These are donor/delta requirements for plan authoring, **not newly executed
fixtures or measured results**. The verified plan must give exact fixture
and mutation counts, observed diagnostics and nearest legal neighbours.

| Goal | Existing donor and required delta/distinction |
| --- | --- |
| Three successful private phases; failure in each leaf | Use three port-fixture `consumerComponent` leaves and ranked-fixture `privateBoundary`/`privateInput`. Adapt the existing `4`/`0` total/strict neighbours so one leaf at a time fails privately after its visible output. Compare both actual bracketings and every reached snapshot/ledger, not just outcome kind. |
| Collection and zero writers before continuation | Use port-fixture `producerComponent` or `zeroProducerComponent`, then two consumer leaves. Retain both contributions and their separate publication, or the zero-writer publication, before either continuation starts. |
| Nonconstant coordinates through a nested join | Use axis-fixture `axisProducer`, `axisConsumer`, `axisBoundary`, then a scalar consumer with a new explicit boundary from the axis consumer's scalar output. Retain nonpalindromic repeated reads so reversed/flattened transport changes observations. |
| Guards, colliding local names and leaf ownership | Use collision-fixture `collisionProducer`, `collisionConsumer`, `collisionBoundary`, then another consumer. Retain admitted/rejected valuations and reused local tags/capabilities; wrong ownership or nested renaming must be distinguishable. |
| Coincident cuts and empty tensor metadata | Use `emptyProducerComponent` followed by two `emptyConsumerComponent` leaves; supply both explicit boundaries. Preserve the required empty external input and empty intermediate inputs. Observe that vacuous phases add neither events nor duplicate snapshots. |
| Observation is stronger than output equality | Adapt ranked-fixture `reorderedPrivateRun` and existing composition counterexamples. Retained private work, failure timing, event order or contribution multiplicity must distinguish the altered history even where visible boundary values agree. |

Use the existing rank certificates and graph/reference phase instances as
donors, not a separately authored composite match. Add generic theorem
instances and namespace axiom audits. Mutation controls must distinguish
wrong reassociation maps, omitted private work, reordered contributions,
dropped publication, failure fall-through, and duplicate/coincident cuts.
Do not count setup refusal, aborted evaluation or a type mismatch as an
intended runtime fixture observation; classify live-proof controls honestly.

## 5. Targeted source map

All Lean paths below are under
[`leanncd/experiments/indexed_execution/`](../../leanncd/experiments/indexed_execution/).
Use `rg -n`, then approximately 40-60-line windows around the identifiers.

| Identifiers @ file | Use |
| --- | --- |
| `compositeRankCertificate`, `rankOffset` @ `IndexedComponentCompositionRanks.lean` | Construct both nested certificates; rank bounds include inputs and empty address types |
| `PrefixRun`, `RunProjection`, `compose_default_phases` @ `IndexedComponentExecutionRuns.lean` | Actual binary default-run decomposition and residual budgets |
| `ReferenceStateProjection`, `reference_default_phases` @ `IndexedComponentExecutionReference.lean` | Full normalized reference phase projections and mapped events |
| `UpstreamState`, `DownstreamState`, `graph_steps_standalone`, `downstream_at_cut` @ `IndexedComponentExecutionPhase.lean`; `mapLedger`, `mapEvent`, `Projection` @ `IndexedComponentExecutionTransport.lean` | Ordered full-state retention, explicit transport and shared cuts |
| `stepFuel_add_of_not_exhausted`, `checked_eq_stepFuel` @ `IndexedComponentExecutionFuel.lean` | Existing actual entry-point/fuel bridge |
| `leftNestedBoundary`, `rightNestedBoundary`, `left_boundary_square`, `right_boundary_square`, `leftBracket`, `rightBracket`, their input/output equivalences @ `IndexedWitnessCoherence.lean` | Existing actual nesting and denotational interface transport; no history law follows automatically |
| `liftInput`, `boundaryInput`, `boundaryFromOutput` @ `IndexedComponentModelInputs.lean` | Authoritative input and whole-boundary maps |
| `State`, `Event`, `Outcome`, `Run`, `runChecked` @ `IndexedOpenComposition.lean`; `LedgerInvariant`, `Relation` @ `IndexedCompositionMatch.lean`; `referenceSnapshots`, `ExecutionCorrespondence` @ `IndexedCompositionCorrespondence.lean` | Existing observation payload and failure normalization |
| `privateBoundary`, `privateInput`, `consumerRank`, `privateSnapshots`, `reorderedPrivateRun` @ `IndexedComponentRankedExecutionFixtures.lean`; `Axis`, `Collision` @ `IndexedComponentRankedExecutionRankTest.lean`; graph/reference phase instances @ `IndexedComponentRankedExecutionTest.lean` | Acceptance/rank donors, not new fixture results |
| `consumerComponent`, `producerComponent`, `zeroProducerComponent`, empty components @ `IndexedComponentCompositionPortFixtures.lean`; axis/collision donors @ `IndexedComponentCompositionAxisFixtures.lean`, `IndexedComponentCompositionCollisionFixtures.lean`; graph-only controls @ `IndexedComponentCompositionCounterexampleTest.lean` | Local matched leaves and discriminating neighbours |

## 6. Scope, process and release gates

Use latest **local** main, not a stale remote base. Use `slice-plan` and
`new-slice`: prepare an isolated worktree, verify warm Mathlib, refresh
project-owned oleans and preserve all unrelated edits/worktrees.
Keep one verified plan for this slice, separate from its evidence record.
Suggested artifact prefix: `categorical_operational_associativity`.
New Lean names and module splits remain to be verified.

Prototype and verify first; author the plan from those artifacts in a fresh
bounded context. Ship mechanically generated per-task patches and mutation
manifests with observed intended diagnostics. Roughly three work items per
dispatch; split before approximately 60 turns or 250k peak context.
Authoring targets roughly 50M cumulative input tokens; execution caps at 175M.
Measure with `token-report.py`; disclose unavailable telemetry or overruns.

Keep the proof layer nondefault under `IndexedExecutionExperiment`, with a
discoverable entry module and matching Lean instructions. Controller gates:
all actual unfiltered mutation cycles, source/probe and namespace audits,
full `LeanNCD Tests IndexedExecutionExperiment` wrapper build, and two final
whole-branch review lenses: observation/transport/associativity soundness;
runner/state/failure/metadata/budget integration. Update synthesis status
only for results actually proved. Merge locally when green and reviewed;
remove only owned task worktrees/branches. Do not push without a new request.

**Excluded:** process units, an adjoined identity construction, a full process
category or new source functor, scheduler-independent equivalence, arbitrary
unranked/debug-fuel/invalid-input associativity, backend/numerical refinement,
broader interfaces, automatic matches and unrelated cleanup. No core language,
registry, scheduler, runner or completed denotational semantics changes.

A core copy adds events; input-as-output aliases violate the defined-output
rule. Do not weaken the observation contract to manufacture identities.
Call the result associative operational composition, not a category until
units are separately justified. A design/proof blocker that cannot meet this
contract must be reported rather than hidden by output-only equivalence,
extra premises or scope expansion.

Close-out must state the exact observation relation and retained information,
history algebra/congruence laws, actual nested graph/reference theorem
premises, four outcome branches, empty/coincident-cut behaviour, explicit
transports, budget/validation boundaries, executed evidence and remaining
unit/process-category/source-interpretation/backend work.
