# Complete-model restriction and gluing record

[Handoff](component_model_gluing_handoff.md) |
[Interface design](categorical_tensor_logic_component_interfaces.md)

## Scope and preparation

- Process weight: Full; new rank-independent semantic theorem and soundness surface.
- Task worktree: `pyncd.worktrees/follow-directions-component-model`.
- Task branch: `agents/follow-directions-component-model`.
- Prepared from latest local main `2212263c`; initial task branch had no
  branch-only commits or dirty files and fast-forwarded from `16721af5`.
- `prepare-worktree.sh` verified 8,101 Mathlib oleans / 8,094 sources
  (100%), and 374 project oleans. The nondefault composition modules
  still require building; cache warmth does not establish their availability.
- Protected primary-checkout files, not slice deliverables:
  - `papers/semantics/README.md`, initial SHA-256
    `467f94f6890675822e3972fc72d8d79ebdf3f661d48cdb7f5449606f4f568f25`.
  - `papers/semantics/categorical_tensor_logic_semantics.md`, initial SHA-256
    `81478c0ac0c34fef33e487503a41387f7573c224d11dd25174fb0cee4c7fb994`.
- Other worktrees are outside the task.

## Accounting

`token-report.py 7c2f3b25-15ad-41dd-b8a2-2d3910ed051c` reports no supported
transcript. Cumulative-input-token compliance is therefore unmeasured,
not asserted. Prototype dispatches target 40 turns with a checkpoint
before 60 turns / 250k retained context.

## Current status

The verified plan, all eight execution tasks, seven acceptance cases,
controller release checks, and both final whole-branch reviews are complete.
Local integration and task-only cleanup are the remaining step.

## Controller occurrence and collection prototype

`IndexedComponentModelTransport` is registered only in the nondefault
experiment. It proves `outcome_upstream`, `outcome_downstream`,
`admEnv_components`, `collect_upstream`, `collect_downstream`, and
`equations_components` for arbitrary complete composite stores.

- Body equality is the existing `interpret_transport` specialized through
  the existing source constructor.
- Defined tensors split into the existing upstream/downstream summands;
  every actual guard-admitted occurrence is retained.
- Each component's occurrence type at its embedded defined tensor is
  definitionally unchanged. `Finset.sum_congr` preserves its entire
  pushforward sum, rather than deduplicating equal contributions.
- Destination equality and `downstream_defined_address` preserve coordinates.
  All coordinate equations are included, including private and zero-writer
  tensors.
- Both `lake-build.sh ... IndexedComponentModelTransport` and the exact
  source-copy `check-snippet.sh` passed.
- `transport_audit.lean` passed: 231 composition constants use only standard
  axioms; both principal equivalences depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- An initial single-file attempt failed because the donor lacked nondefault
  composition oleans. Controller then built `IndexedExecutionExperiment`
  successfully (8,633 jobs), before checking new proofs.
- Equation-proof elaboration initially required canonical embedded subtype
  representatives and an explicit downstream address rewrite. Corrected
  proofs were rebuilt and rechecked; neither failure is mutation evidence.
- Baseline production refresh passed, replaying existing non-semantic
  `sorry` warnings. The new proof surface's namespace audit admits no `sorry`
  or native-decision axioms.

Operational phase/projection, rank stitching, runtime traces, categorical
associativity/identities, wider interfaces, and previous-slice coverage
repairs are excluded.

## Controller local complete-model donors

`IndexedComponentModelLocalFixtures` reuses `producer`, `consumer`,
and `zeroProducer` without modifying their source programs.

- Explicit `producer_model` retains the complete `Pre = 0` store.
- Explicit `total_model` retains `Pre = 0`, `Out = 0`, and private
  `Audit = 1/2`, including its actual occurrence-definedness proof.
- `strict_audit_undefined` and `strict_no_model` hold for every candidate
  consumer store at `other = 0`, independently of the satisfiable
  `strict_out_equation`.
- `zero_producer_forces_zero` constrains the unwritten scalar in every
  model; it is not an arbitrary boundary assignment.
- Exact observed store tuple: `(0, 0, 0, 1 / 2)`.
- Source-copy snippet, targeted Lake build (2,986 jobs), and namespace
  audit passed. All 20 fixture constants use only standard axioms.
- Concrete rational proofs use kernel `decide +kernel`, not
  `native_decide`. Initial normalizer/decision elaboration failures were
  corrected and are not mutation evidence.

## Cyclic donor checkpoint

Prototype `01e0082d` supplies two explicitly matched local component pairs.
See [cyclic donor report](component_model_gluing_artifacts/cycles_prototype.md).
The agent reports likely exceeding the 60-turn ceiling during proof debugging;
this breach is surfaced, with token usage unmeasured. Future fixture work
will be restricted to the already compiled donors and generic gluing APIs.

## Local mutation observations

The controller ran the unfiltered four-entry post-code manifest, restored
every file byte-identically, copied the actual diagnostic strings into
`expect`, checked the entire manifest without filters, and reran all four
cycles. See [observations](component_model_gluing_artifacts/prototype_local_mutations.md).

The nonzero producer candidate and corrupted private audit value are concrete
model-counterexample proof kills (`decide` rejects the witness equations).
Claiming the total neighbour undefined is a proof-elaboration kill at
`change`; claiming a nonzero unwritten coordinate is an equation
proof-elaboration kill at the generic collected equation. Neither latter
cycle is represented as a runtime observation or a completed-model execution.

## Patch execution preparation

A second task-owned detached worktree,
`pyncd.worktrees/component-model-gluing-replay`, is pinned to `2212263c`
for clean-base execution of the eventual verified patches. The preparation
helper verified a 100% Mathlib cache. Project build artifacts were then
synced from the already refreshed task checkout and `LeanNCD` rebuilt
successfully against the replay source. No pre-existing worktree was changed.

Commit `183071e1` includes the geometry prototype source/report because its
agent staged those files concurrently with the controller's mutation commit.
The source was retained; no commit was amended and no history was rewritten.
Subsequent prototype commits are controller-owned to avoid shared-index races.

## Empty and axis donor checkpoint

Geometry source in `183071e1` proves complete models for both existing
empty components and both existing unequal-axis components. See
[geometry report](component_model_gluing_artifacts/geometry_prototype.md).

The actual nonconstant producer values are `[1, 2, 3, 4, 5, 6]`.
The certified boundary yields selected downstream inputs `5, 2`;
wrong flattening yields `3, 4`. Both repeated-read output sums equal
`14`, but the input families are proved distinct. Output totals alone
would therefore miss this adapter defect.

Both donor modules built through the controller wrapper; namespace audits
checked 123 cycle constants and 51 geometry constants with only standard
axioms. The geometry agent estimates 20 interaction rounds, no cap breach;
the estimate is not token-report measurement.

The extended eight-entry post-code manifest has now run unfiltered with
observed `expect` strings and restored byte-identical controls. See
[donor mutation results](component_model_gluing_artifacts/prototype_donor_mutations.md).
Empty external/downstream binding erasure and private-store collapse
produce proof-elaboration kills. Wrong axis flattening is a coordinate
counterexample proof kill: the explicit selected-input values fail even
though the output total remains `14`.

These donor proofs are not yet the required composite gluing/round-trip
fixtures; those await the generic witness API.

## Validated input/store checkpoint

`a80099ee` persists the compiled `IndexedComponentModelInputs` API.
The controller built the registered module and checked its full composition
namespace: 255 constants, standard axioms only.
See [input/store report](component_model_gluing_artifacts/inputs_prototype.md).

`liftInput`/`restrictInput` are inverse on validated tensor bindings.
`boundaryInput` and `boundaryFromOutput` explicitly retain present empty
inputs. `glueStore` keeps the upstream summand and downstream defined values.
Its downstream restriction inverse requires exactly downstream
`InputAgreement`; restrictions of an arbitrary composite store satisfy
that agreement by `boundaryInput_restrictions`.

The agent estimates 30–40 action turns and 60–100k peak context; accounting
is unavailable and no measured compliance is asserted. Its 2,413 seconds
of elapsed time included baseline wait and is not evidence of a turn breach.

## Rank-independent theorem and composite fixture checkpoint

`IndexedComponentModelWitnesses` now proves `models_restrict_iff`,
`models_restrictInput_iff`, `models_glue_iff`, and the explicit dependent
whole-witness `witnessesEquiv`, with both inverse laws. It also transports
output indices and complete output projections, including empty outputs.
No rank, phase, existence, or uniqueness premise appears in this core.
The controller build, exact source-copy check, and whole composition
namespace audit passed: 289 constants with only standard axioms.
See [witness report](component_model_gluing_artifacts/witnesses_prototype.md).

The controller's `IndexedComponentModelLocalTest` compiles with no model
or compatible witness for the strict case, a complete total glued store
and witness round trips, and the composite zero-writer constraint.
The strict donor's no-model result was generalized to every validated
consumer input; definedness fails independently of its input agreement.
Observed total composite values are `(0, 0, 1 / 2)`.

`IndexedComponentModelGeometryTest` compiles with generic lifted/transported
empty-input presence, the empty output-index identity, complete empty
gluing, and nonconstant-axis component/composite models and store round trips.
Actual downstream restrictions are `(5, 2)` with output `14`; the
restricted family is explicitly unequal to wrong flattening.
The initial coordinate-test elaboration needed the named composite store
unfolded before rewriting its restriction; corrected source passed.

## Restricted denotation and cyclic composite checkpoint

`IndexedComponentModelDenotation` proves `admInput_lift_iff`,
`admInput_restrictions_iff`, and `denotation_successive`.
Both components must satisfy explicit `AtMostOneModels` on every validated
input. These hypotheses assert no existence. Domain equivalence covers
every validated composite input; the value theorem transports the successive
denotation on precisely that domain. See the
[denotation report](component_model_gluing_artifacts/denotation_prototype.md).

`IndexedComponentModelCycleTest` proves that only the upstream one-model
extends in the reciprocal case, and the composite has exactly one complete
store despite upstream non-admissibility. The uniqueness proof quantifies
over every composite candidate, not only two listed stores.
Both hidden upstream models extend to distinct composite stores with equal
whole final outputs and witness round trips. See the
[cyclic gluing report](component_model_gluing_artifacts/cycle_gluing_prototype.md).

The controller built `IndexedComponentModelTest` (8,628 jobs), which imports
the restricted denotation and all seven acceptance cases and audits:
294 composition constants, 20 local donor constants, 17 local composite-test
constants, 51 geometry donor constants, 16 geometry composite-test constants,
127 cycle donor/auxiliary constants, and 24 cycle composite-test constants.
All use only standard axioms. Exact source-copy checks passed for the final
denotation, cycle tests, and local tests.

The controller's [actual probes](component_model_gluing_artifacts/probes.lean)
observed `true`, `true` for lifted/transported empty input presence,
`(1, 1)` for the unique cyclic composite's private/output values, and
`(0, 1, 1, 1)` for the two hidden private values and equal outputs.
These are complete-store/body observations, not execution-completion claims.

The visible strict `Out = 0` equation is now explicitly satisfied by a
candidate composite store (`strict_visible_equation_satisfied`), while
`strict_no_composite` still excludes every complete model because the
private strict reciprocal is undefined.

## Controller case/class and call-site audit

| Surface | Mechanism and required invariant | Ignored work |
| --- | --- | --- |
| Occurrence/outcome/definedness | `outcome_upstream`, `outcome_downstream`, and `admEnv_components` quantify over each defined summand and every `Program.Occurrence`; `interpret_transport` preserves the whole strict body. | Guard-excluded valuations are not occurrences. No actual private occurrence is omitted. |
| Contribution/collection/equations | `collect_upstream`, `collect_downstream`, and `equations_components` retain the entire original finite occurrence type and use `Finset.sum_congr` at each coordinate. Distinct equal-valued contributions are never deduplicated. | Empty fibers still sum to zero; empty coordinate types have no coordinate equations. No private defined tensor is pruned. |
| Input validity | `liftInput`/`restrictInput` preserve tensor-level `ValidInput`; `boundaryInput` explicitly supplies `some` on every downstream input. | Noninputs are absent by their role, not because coordinates are empty. |
| Boundary/store inverses | `downstream_input_address` and `boundaryInput_restrictions` use the certified tensor/coordinate adapters. `restrictDownstream_glueStore` requires full downstream input agreement, supplied at model call sites. | No name/extent inference or arbitrary-pair inverse is admitted. |
| Witnesses/output indices | `witnessesEquiv` retains both full model subtypes in a dependent Sigma; store inverse laws and proof irrelevance handle the two inverses. `outputIndexEquiv` retains empty output identity separately from coordinates. | No store is quotiented by its output value. |
| Denotation | `AtMostOneModels` universally compares model stores without asserting existence. The domain iff and successive values use both component hypotheses before upstream output projection. | No unrestricted unique-model composition or phase/execution claim. |

The generic guard/duplicate obligations are proved, not represented as newly
observed dedicated guard/duplicate fixtures. The seven requested cases and
12 mutation cycles are reported separately; no silently ignored required
cell or extra runtime kill is invented.

## Verified authoring package

The fresh artifact-only writer finalized the one 490-line
[implementation plan](component_model_gluing_plan.md).
The controller reviewed its task inventories, actual shared-lakefile patch
ordering, exact domain/uniqueness premises, audit classes, and release gates.
Review caught a replay command referring to a manifest not copied by the
code patches; it now uses the existing manifest in the prototype checkout
while targeting replay source.

The final unfiltered 12-cycle authoring manifest passed with every observed
`expect` string and byte-identical restored controls.
See [final authoring mutations](component_model_gluing_artifacts/authoring_mutations.md).
M9's initial constant replacement accidentally dropped an inferred parameter;
the final replacement retains the parameter and multiplies transported values
by zero, so its observed failures exercise the actual boundary equations.
The obsolete diagnostic is not final mutation evidence.

`package.py --emit` mechanically exported eight task patches from compiled
source. After all mutation restoration, `--check` applied them in order to
an isolated index at `2212263c` and verified exact final tree/source hashes.
No current index or working source was reset. Its task-owned private temporary
indices are automatically removed. Real checkout execution remains separate.

Accounting remains unsupported. The controller's long exploration/prototype/
package conversation exceeded the approximately 60-action-turn guideline;
this process overrun is surfaced rather than treated as compliance.
The fresh writer estimates 24 tool rounds against its approximately 20-round
target, below its hard checkpoint. The earlier cyclic-donor breach also
remains recorded; cumulative authoring/execution tokens are unmeasured.

## Actual execution and controller task reviews

After the plan was verified and committed, the controller ran
`package.py --replay` in the prepared clean-base checkout. All eight
patches actually applied, built their named targets, passed exact
source-copy checks and per-task source hashes, and were committed.
[Execution checkpoints](component_model_gluing_artifacts/execution_replay.json)
record each real commit; the last is `cbd52ddf`.

Controller task reviews accepted the already reviewed prototype logic only
after its executed bytes matched exactly. These are controller reviews,
not eight additional independent agent reviews.

| Task | Controller review invariant | Execution checks |
| --- | --- | --- |
| Inputs | Present empty inputs; downstream inverse needs full boundary agreement | Build, snippets, source hashes pass |
| Transport | Every actual occurrence, private tensor, and finite collected fiber retained | Build, snippets, source hashes pass |
| Witnesses | Dependent whole-store pair, both inverses, empty output-index transport | Build, snippets, source hashes pass |
| Denotation | Both at-most-one component premises; domain and value laws, no existence in uniqueness | Build, snippets, source hashes pass |
| Local fixtures | Strict private failure despite visible equation; complete total neighbour; unwritten zero | Build, snippets, source hashes pass |
| Geometry fixtures | Empty bindings/metadata and actual nonconstant coordinates, not output-total-only equality | Build, snippets, source hashes pass |
| Cycle fixtures | Unique compatible extension among all candidates; hidden whole-store distinction retained | Build, snippets, source hashes pass |
| Discovery | Nondefault imports and full namespace audits; operational/categorical exclusions explicit | Build, snippets, source hashes pass |

The controller's full `LeanNCD Tests IndexedExecutionExperiment` build
passed (8,898 jobs). No required target was skipped. It retains the recorded
pre-existing non-semantic warnings; the new proof namespaces pass their
standard-axiom audits.
Actual replay release mutations/probes and the two final whole-branch
review lenses remain pending.

## Controller release gates and final adjudication

The controller ran the complete unfiltered 12-entry manifest on the actually
executed replay source, not just authoring prototypes or `--check`.
[Replay mutation results](component_model_gluing_artifacts/execution_mutations.md)
show every intended diagnostic, byte-identical restoration, and green
restored target. No cycle was filtered or skipped.

The full replay `LeanNCD Tests IndexedExecutionExperiment` build passed
(8,898 jobs), followed by the actual store/input probes:
`true`, `true`, `(1, 1)`, `(0, 1, 1, 1)`.
The original controller checkout's full build also passed 8,898 jobs.

Both required whole-branch reviews examined `e1553bb7`, whose parent includes
the actual eight execution commits and whose packaged source matches them:

- [Model-theorem soundness](component_model_gluing_artifacts/review_soundness.md):
  no load-bearing findings.
- [Integration/fixtures/claim fidelity](component_model_gluing_artifacts/review_integration.md):
  no actionable findings; independently reconstructed all patch, intermediate
  file, and checkpoint hashes and checked all seven fixtures.

Both findings sets are adjudicated clean. No Lean/source/package change
followed these reviews; close-out edits only record completed gates.

Immediately before integration, both protected primary-working-copy hashes
still match the initial values. The branch does not stage or commit either
draft. Cleanup inspection identified only the task-owned `.lake` caches and
eight generated replay logs as ignored files; no other task-worktree contents
are to be discarded.

The rank-independent witness bijection is complete without ranks, phases,
model existence, or component uniqueness. The denotation corollary separately
requires at-most-one complete-model stores for both components on every
validated input. All private work remains in those complete witnesses.
Rank stitching, runtime phase/projection/trace theorems, categorical laws,
wider interfaces, and prior-slice repairs remain explicitly outside this slice.
