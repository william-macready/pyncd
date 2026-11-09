# New-session brief: ranked component execution and phase projections

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

## Copyable launch instruction

```text
Read papers/semantics/categorical_ranked_execution_handoff.md on latest
local main. Prepare and verify one implementation plan, then execute it,
for ranked operational composition of the existing sealed matched components.

Construct a composite rank certificate from the two component certificates.
Prove upstream-first phase separation and state projections to the standalone
upstream and downstream executions, including private work, strict failures,
explicit boundary transport, normalized snapshots and default budgets.

Use the existing constructor, first-enabled scheduler, graph runner and
graph/reference correspondence. Do not add a runtime phase gate, assume
execution agreement, or redo the completed denotational/source-category work.
Keep generic trace algebra and event-sensitive process-category laws for a
later slice.

Preserve unrelated edits and worktrees. Use the repository release gates,
merge locally when green and reviewed, and do not push. Report a load-bearing
plan or theorem blocker rather than weakening the goal or expanding scope.
```

**Process weight for implementation: Full.** This adds generic operational
proof capabilities. This document is a goal brief, not a verified execution
plan: new proof declarations, module splits, compiled patches, fixtures and
mutation controls must still be authored and checked.

## 1. Starting point and exact scope

The denotational witness category and certified matched-component source
functor are complete for the finite decidable `Declarations Unit`,
exact-rational, explicitly wired sealed profile. Their completion does not
prove that a composed execution finishes upstream work before starting
downstream work.

Use latest **local** main, not a stale remote base. Read:

1. [Synthesis](categorical_tensor_logic_semantics.md), Sections 9.2 and
   10.2-10.3, distinguishing completed denotational and open process results.
2. [Component interfaces](categorical_tensor_logic_component_interfaces.md),
   Section 5, for the proposed rank/phase argument and its boundaries.
   The synthesis and actual APIs govern current proof status.
3. [Composition record](component_composition_record.md) and
   [correspondence record](categorical_tensor_logic_proof_record.md).
4. [Lean instructions](../../leanncd/AGENTS.md), then the targeted sources below.

For matched components `A`, `B`, a supplied `Boundary A B`, rank certificates
for both programs and validated upstream input, target the actual `compose`
constructor and its constructed schedule. Form composite input with
`liftInput`; obtain downstream input only from the completed upstream
boundary through `boundaryFromOutput`/`boundaryInput`.
No model-existence, uniqueness or assumed execution-completion premise.

The candidate runner is `IndexedOpenComposition.runChecked` on the existing
component contract/fragment, with its default budget. The reference is
`Program.Executor.run` on validated inputs, or `runValidated` when stating
the raw-input validation corollary. Do not substitute `IndexedExecution.run`.
Public graph `run` revalidates/regenerates its graph; it is not definitionally
the same entry point as `runChecked`.

## 2. Required proof obligations

### Composite rank certificate

Construct a `RankCertificate` for the composite, not an assumed certificate.
Its `dependencies` include every actual occurrence's full expression footprint,
not only designated-output dependencies.

The existing design supplies a candidate construction: choose `L` strictly
larger than every upstream address rank, including input ranks; finiteness
permits this even when there are no addresses. Retain upstream ranks and give
each embedded downstream defined address rank `L + r_B(a)`.
Prove the dependency cases through the actual embeddings and footprint
transport: upstream dependencies, downstream internal dependencies, and
boundary reads mapped into upstream coordinates. Audit the finite bound and
empty-coordinate case rather than assuming an inhabited maximum.

Do not weaken certified domain adapters or identify axes by name/equal extent.
Ranks justify readiness/progress, not totality of registered operations:
a ranked execution can still fail on a ready undefined body.

### Upstream phase and failure

The constructed key/step order places transported upstream actions before
downstream actions. **List order alone is not a phase barrier:** the runner
selects the first enabled action and can skip disabled upstream actions.

Derive an invariant relating the composite's pre-boundary states to reachable
standalone upstream states, with no downstream action yet performed.
If upstream is incomplete, use ranked progress and eligibility transport to
derive an enabled upstream action. Its priority excludes downstream selection.
Do not assume equality of selected actions, traces or runs as a premise.

Completion includes every upstream writer and collector, including private
nonoutputs and zero-writer publication, not just boundary availability.
If upstream evaluation fails, prove that the composite fails at the transported
upstream occurrence/tag and no downstream production or publication occurred,
even if all visible upstream outputs were already available.

### Boundary state and downstream phase

After upstream success, construct the valid downstream input from its **whole**
output interface through the specified boundary. Preserve empty-input tensor
presence using program/interface metadata; an address-only state cannot
recover an empty tensor's role by enumerating coordinates.

Prove that the downstream projection starts with transported input values,
no downstream produced capabilities and no downstream defined values.
The composite retains the completed upstream ledger and private values.
During the suffix, downstream transitions project to the standalone downstream
execution, and upstream data remain unchanged.

Track published/available values and produced ledgers, with order, capability
and tag renaming. When transferring to the reference machine, also account
for pending occurrences and accumulators through the existing relation.
Agreement of final outputs or complete models is insufficient.

Cover downstream success and downstream undefined failure after upstream
success. Use the rank and existing validation/correspondence results to exclude
blocking, mismatches and exhaustion under the stated premises; do not replace
those conclusions with assumptions or fabricated default values.

### Snapshots, events and budgets

State an explicit phase cut and the projection relation at all relevant
snapshots. There is one shared boundary snapshot, not two, and no synthetic
wire/copy/boundary execution event. For failed execution, use the existing
`referenceSnapshots` normalization: undefinedness records an event but not
an additional failed-state snapshot.

Prove only the event ownership/prefix facts needed to locate the phase cut,
exclude premature downstream work and identify failures. A general trace
concatenation API and process-category laws are not required in this slice.

The composite default graph budget is its own step count plus one, not the
sum of the two standalone default budgets. Reuse the match-derived budget
agreement and non-exhaustion results; prove any fuel-stability helper needed
to compare actual default runs. Arbitrary explicit debug fuel is excluded.

Invalid raw bindings retain the composite's existing full-tensor validation
order. Do not claim that validation is two standalone validations, require
the caller to supply now-internal boundary inputs, or conflate invalid input
with undefined evaluation. State the phase theorem first on validated input.

## 3. Discriminating acceptance goals

These are proposed, not newly executed fixtures or measured controls.
The verified plan must name exact donor/delta, fixture and mutation counts,
and observed diagnostics. Include nearest legal neighbours for refusals.

| Goal | Existing donor and required distinction |
| --- | --- |
| Private work after visible output; upstream success/failure | Adapt `consumerComponent 4` and `consumerComponent 0` from [port fixtures](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionPortFixtures.lean) into upstream position, with a new explicit boundary and valid external input. Their schedule publishes `Out` before private `Audit`; prove downstream waits for total private completion and never starts after private failure |
| Contribution collection and downstream failure | Use `producerComponent`, `consumerComponent 0` and its total neighbour `consumerComponent 4` from port fixtures; retain the two upstream contributions and separate publication so partial sums cannot act as boundary values |
| Zero writers and empty coordinates | Use `zeroProducerComponent`, `emptyProducerComponent`, `emptyConsumerComponent`, `emptyPresentInput` and `emptyMissingInput` from port fixtures; test zero publication, vacuous phases and required empty-input presence without synthetic events |
| Nonconstant coordinate transport and rank inequalities | Use `axisProducer`, `axisConsumer`, `axisBoundary` from [axis fixtures](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionAxisFixtures.lean), with the discriminating `Axis` observations in [witness composition tests](../../leanncd/experiments/indexed_execution/IndexedWitnessCompositionTest.lean); reversed/flattened transport must differ |
| Guarded occurrences and colliding local names | Use `collisionProducer`, `collisionConsumer`, `collisionBoundary` from [collision fixtures](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionCollisionFixtures.lean); retain guard-admitted occurrences and disjoint tag/capability embeddings in state projections |
| Why ranking is necessary | Use `hiddenUpstream`, `totalDownstream`, `hiddenBoundary` from [cycle fixtures](../../leanncd/experiments/indexed_execution/IndexedComponentModelCycleFixtures.lean). Propose and observe a run where ready downstream work proceeds while private upstream work is cyclically blocked; do not assign this case a rank or interpret blocking as absence of models |

Add generic certificate/phase/projection theorem instances and namespace
axiom audits. Plan controls that distinguish omitted private work, premature
boundary use, wrong renaming/coordinate transport and duplicate snapshots.
Do not count build/setup refusal as the intended mutation observation.

## 4. Targeted source map

Use `rg -n`, then approximately 40-60-line windows. Avoid broad backend surveys.

| Identifiers @ file | Use |
| --- | --- |
| `RankCertificate`, `dependencies`, `DefinedAddress` @ [Ranks.lean](../../leanncd/LeanNCD/Semantics/Ranks.lean); `ranked_progress`, `ranked_not_blocked` @ [Progress.lean](../../leanncd/LeanNCD/Semantics/Progress.lean) | Rank construction and reachable-state progress |
| `upstream`, `downstream`, `declarations`, `Boundary` @ [IndexedComponentCompositionScope.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionScope.lean); `upstream_footprint`, `downstream_footprint` @ [IndexedComponentCompositionProgram.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionProgram.lean) | Dependency partition and coordinate embeddings |
| `evalReady_transport`, `evalWith_transport` @ [IndexedComponentTransportEval.lean](../../leanncd/experiments/indexed_execution/IndexedComponentTransportEval.lean) | Readiness, definedness and evaluation transport |
| `keyEquiv`, `keyOrder`, `schedule` @ [IndexedComponentCompositionSchedule.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionSchedule.lean); `priority` @ [IndexedComponentCompositionPriority.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionPriority.lean) | Actual upstream-first priorities |
| `State`, `initial`, `producedValue`, `enabled`, `complete`, `stepFuel`, `runChecked` @ [IndexedOpenComposition.lean](../../leanncd/experiments/indexed_execution/IndexedOpenComposition.lean) | Existing executable transition/selection semantics |
| `LedgerInvariant`, `Relation` @ [IndexedCompositionMatch.lean](../../leanncd/experiments/indexed_execution/IndexedCompositionMatch.lean); `referenceSnapshots`, `ExecutionCorrespondence`, `eligible_key` @ [IndexedCompositionCorrespondence.lean](../../leanncd/experiments/indexed_execution/IndexedCompositionCorrespondence.lean) | State projection, eligibility and failed-snapshot normalization |
| `default_run_correspondence`, `accepted_no_mismatch`, `default_runs_not_exhausted`, `ranked_not_blocked` @ [IndexedCompositionValidated.lean](../../leanncd/experiments/indexed_execution/IndexedCompositionValidated.lean); `default_budgets_agree` @ [IndexedCompositionSelection.lean](../../leanncd/experiments/indexed_execution/IndexedCompositionSelection.lean) | Existing match-to-execution bridge and default budgets |
| `liftInput`, `restrictInput`, `boundaryInput`, `boundaryFromOutput` @ [IndexedComponentModelInputs.lean](../../leanncd/experiments/indexed_execution/IndexedComponentModelInputs.lean) | Authoritative input and boundary maps, not a substitute for execution proofs |

Use the public `stepFuel` proof surface where useful. Any necessary helper
extraction must preserve behaviour and expose a genuine proof interface,
not introduce another evaluator or runtime barrier.

## 5. New-session discipline and release gates

Use `slice-plan` and `new-slice`. Prepare an isolated latest-local-main
worktree with verified warm Mathlib, then refresh project-owned oleans through
`lake-build.sh`. Use `lean-file.sh` for single-file checks and
`check-snippet.sh` for every new Lean block. Do not run Lake from the repo root.
Protect the primary checkout's existing synthesis/contents edits and all
other worktrees.

Keep one verified plan for this operational slice; separate its live
instructions from records. Use a proposed `categorical_ranked_execution`
artifact prefix; verify new Lean names and real module splits during authoring.
Keep the proof layer nondefault under `IndexedExecutionExperiment`, with a
discoverable entry module and matching Lean instructions.

Prototype and verify first, then author the plan from artifacts in a fresh
bounded context. Ship mechanically generated per-task patches and populated
mutation manifests with observed diagnostics. Size tasks by fixtures/cycles,
roughly three work items per dispatch; split before approximately 60 turns
or 250k context. Authoring targets roughly 50M cumulative input tokens;
execution caps at 175M. Measure with `token-report.py`; disclose overruns or
unavailable accounting rather than claiming unmeasured compliance.

The controller runs actual unfiltered mutation manifests, source/probe checks,
namespace audits, and the full `LeanNCD Tests IndexedExecutionExperiment`
build through the wrapper. Complete two final whole-branch review lenses:
rank/progress/phase soundness, and runner/state/validation/budget integration.
Update proof-status documentation only for results actually proved.
After green gates and adjudicated findings, merge locally and remove only
the task's own branch/worktree. Do not push.

**Excluded:** general trace algebra, process identities/associativity,
event-exact source-category interpretation, backend/numerical refinement,
broader interfaces, automatic matches and unrelated coverage/accounting
repairs. Do not alter the core language, registry, scheduler, runners or
completed denotational/source-functor semantics.

Close-out must state the certificate construction, exact scheduling/input
premises, phase-cut and state-projection theorems, failure and empty-interface
behaviour, budget/validation boundaries, executed evidence and remaining
trace/process/backend work.
