# Complete-model restriction and gluing

**VERIFIED — EXECUTION READY.** Process: **Full**, because this adds a semantic
theorem and a soundness surface. One slice, based on local main `2212263c`.
Controller authoring gates in Section 7A passed: compiled source/probes,
12 observed mutation cycles, and final ordered package/index parity.
Actual checkout replay, full release build, final reviews, and integration
remain execution/release gates; none is claimed complete here.

## 1. Goal, premises, and exclusions

Construct an explicit bijection between composite **whole-store** model
witnesses and compatible component witnesses over the existing static
constructor `IndexedComponentComposition.program A B wire`.
For each validated upstream input, the downstream model family is indexed by
the upstream witness's transported boundary input. It is a dependent family,
**not a product of two fixed model sets**. Both inverse laws matter.
Different proofs certifying the same store do not create different witnesses;
proof irrelevance identifies certificates, not distinct private stores.

Exact scope: finite decidable tensor declarations `Declarations Unit`,
`MatchedComponent` values `A` and `B`, explicit certified `Boundary wire`,
and the constructor's fixed `RationalReference.Carrier`, registry, and
`RationalReference.ops`. No arbitrary sorts, alternative registry, or alternate
model semantics. `Models` includes input agreement, definedness of every
actual guard-admitted occurrence, and every defined coordinate's collected
equation, including private tensors and zero-writer fibers.

Derive domain correspondence and successive denotation **only under explicit
`AtMostOneModels A` and `AtMostOneModels B`**. This predicate asserts uniqueness
when models exist, not existence. No unrestricted unique-model composition
law: a consumer can select one of several producer models.

Excluded: core-theorem ranks, model-existence premises, operational completion,
phase/projection or spliced-trace theorems, composite rank certificates,
categorical associativity/identities, wider interfaces, automatic matching,
general parsing, prior-slice repairs, and token-accounting tooling.
Blocked cycles may have models; these proofs do not execute or solve cycles.

## 2. Evidence contract and protected scope

Authoring uses artifacts only: [handoff](component_model_gluing_handoff.md),
[controller record](component_model_gluing_record.md), and reports in
`component_model_gluing_artifacts/`: `inputs_prototype.md`,
`witnesses_prototype.md`, `denotation_prototype.md`, `cycles_prototype.md`,
`geometry_prototype.md`, and `cycle_gluing_prototype.md`.
Local/geometry composite checks are summarized in the record; their exact
identifier inventory below was supplied by the controller.
No Lean block is supplied here. Signatures below are report-backed prose;
execution applies mechanically exported compiled patches, never transcribed
report snippets. Geometry-report signatures are text, not uncompiled Lean blocks.

The updated record reports the aggregate build, namespace audits, source-copy
checks, and probes passing, with all seven cases using generic gluing.
Final controller evidence additionally confirms unfiltered 12/12 observed
mutation cycles with byte-identical restoration, followed by regenerated
package emission and passing isolated-index tree/source-hash parity.
See `component_model_gluing_artifacts/authoring_mutations.md` and
`task_patches.json`. Actual clean-base execution follows this verified plan.

Task checkout:
`/Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model`.
Clean-base replay checkout:
`/Users/williammacready/code/python/pyncd.worktrees/component-model-gluing-replay`.
The controller owns package generation, source-copy checks, manifests, probes,
execution, staging, and integration. The author owns this plan only.

Protected main-checkout files are excluded from every task commit:
`papers/semantics/README.md` and
`papers/semantics/categorical_tensor_logic_semantics.md`.
Preserve the record's exact initial SHA-256 values:

| Protected file | Initial SHA-256 |
| --- | --- |
| `README.md` | `467f94f6890675822e3972fc72d8d79ebdf3f661d48cdb7f5449606f4f568f25` |
| `categorical_tensor_logic_semantics.md` | `81478c0ac0c34fef33e487503a41387f7573c224d11dd25174fb0cee4c7fb994` |

Existing-document edits are limited to
`papers/semantics/categorical_tensor_logic_component_interfaces.md`,
`leanncd/AGENTS.md`, and the controller record. Do not replace protected
working copies or fix parked side issues. Never stage `.claude/settings.json`.

## 3. Execution protocol and dependency graph

Every dispatch begins with this harness preamble:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Use `identifier @ file` lists below, locate with `rg -n`, and read 40–60-line
windows. Do not whole-file-read large modules. Before editing under
`leanncd/AGENTS.md`, the controller verifies its injected
Pitfalls/Checks/Patterns/Context budget is approximately 3k characters or less.
At most three acceptance cases per dispatch; target 40 turns, checkpoint
before 50 turns/200k context here, and never silently breach 60 turns/250k.
Split anticipated overruns into production and fixture/cycle dispatches.

Source/semantic prerequisites, not a chain inferred from task numbering:
T1 and T2 are independent; T3 needs both; T4 needs T3.
T5–T7 each need T3 and their own existing donor modules, not one another.
T8 needs every preceding deliverable. The mechanical patches nevertheless form the sequential application chain
**T1 → T2 → T3 → T4 → T5 → T6 → T7 → T8**: each appends its registrations to
the shared Lake file produced by its predecessor. Do not apply them in parallel.
This packaging dependency does not change the source/semantic prerequisites.

Each task includes its required `leanncd/lakefile.toml` nondefault registration
in its mechanical patch. The controller executes the final indexed patches;
do not dispatch redundant implementers to recode already compiled source.
Apply only the final controller-indexed patch,
build the smallest named target, run assigned observed cycles, review the
task diff, adjudicate findings, and checkpoint in the record before advancing.
Checkpoint: files/API landed, checks actually run, failures corrected,
remaining gates, and accounting availability. Commit by explicit paths.

Earlier `task_02_transport.patch`, `task_05_local.patch`, and
`task_07_cycle-donors.patch` exports were preliminary. Use only the regenerated
index below, never those earlier bytes or an unindexed donor patch.

## 4. Tasks and exact identifier maps

All new module basenames below live under
`leanncd/experiments/indexed_execution/`; their full names begin
`IndexedComponentModel`. T1–T4 exports use namespace
`IndexedComponentComposition`. `component_model_gluing_artifacts/task_patches.json`
indexes exact patch files, files/targets, and source/patch hashes against
`2212263c`. Final `--emit`/`--check` after full mutation restoration passed.

| Task | Manifest/package task ID | Indexed patch under `component_model_gluing_artifacts/` |
| --- | --- | --- |
| T1 | `inputs` | `task_01_inputs.patch` |
| T2 | `transport` | `task_02_transport.patch` |
| T3 | `witnesses` | `task_03_witnesses.patch` |
| T4 | `denotation` | `task_04_denotation.patch` |
| T5 | `local-fixtures` | `task_05_local-fixtures.patch` |
| T6 | `geometry-fixtures` | `task_06_geometry-fixtures.patch` |
| T7 | `cycle-fixtures` | `task_07_cycle-fixtures.patch` |
| T8 | `discovery` | `task_08_discovery.patch` |

### T1 — Validated inputs and complete-store transport

Files: `IndexedComponentModelInputs.lean`; required Lake registration.
Prerequisite: existing static composition and transport APIs.

Identifiers @ `IndexedComponentModelInputs.lean`:
`liftInput`, `restrictInput`, `restrictInput_liftInput`,
`liftInput_restrictInput`, `boundaryInput`, `boundaryFromOutput`,
`boundaryInput_outputProjection`, `restrictUpstream`, `restrictDownstream`,
`glueStore`, `restrictUpstream_glueStore`, `restrictDownstream_glueStore`,
`glueStore_restrictions`, `inputAgreement_lift_iff`,
`inputAgreement_restrictions_iff`, `inputAgreement_glue_iff`,
`inputAgreement_boundary_iff`, `boundaryInput_restrictions`.

`liftInput` maps validated upstream input to composite input; `restrictInput`
is its inverse. `boundaryInput` takes an upstream complete store to validated
downstream input; `boundaryFromOutput` instead takes the upstream output.
Every downstream input is `some`, including an empty family; noninputs are
`none`. `glueStore` retains upstream values and downstream defined values,
without duplicating the boundary. `restrictDownstream_glueStore` requires
downstream `InputAgreement`; arbitrary incompatible stores have no such inverse.
Restrictions of any composite store have that agreement.

Review both input round trips and all store inverse premises. Build target
`IndexedComponentModelInputs`. Assigned observed cycles: M9/M10.

### T2 — Occurrences, admissibility, and collected equations

Files: `IndexedComponentModelTransport.lean`; required Lake registration.
Prerequisite: existing static composition/body/address transport.

Identifiers @ `IndexedComponentModelTransport.lean`: `outcome_upstream`,
`outcome_downstream`, `admEnv_components`, `collect_upstream`,
`collect_downstream`, `equations_components`.
Immediate donor map from the handoff:
`interpret_transport @ IndexedComponentTransportEval.lean`;
`definedEquiv`, `occurrenceEquiv`, `upstream_body`, `downstream_body`,
`upstream_destination`, `downstream_destination @ IndexedComponentCompositionProgram.lean`;
`downstream_defined_address @ IndexedComponentCompositionMatch.lean`.

Preserve/reflect definedness of every actual occurrence, not just exterior
writers. Transport complete finite sums without deduplicating equal terms;
guards exclude only non-occurrences. Preserve equations on every private and
zero-writer coordinate. The record reports `Finset.sum_congr` and unchanged
embedded occurrence types; controller source/probe evidence must substantiate
the final package's same claims. Build `IndexedComponentModelTransport`.
Review the Section 5 sibling audit, including call-site premises.

### T3 — Complete witnesses, explicit equivalence, and output transport

Files: `IndexedComponentModelWitnesses.lean`; required Lake registration.
Prerequisites: T1 and T2.

Identifiers @ `IndexedComponentModelWitnesses.lean`:
`models_restrict_iff`, `models_restrictInput_iff`, `models_glue_iff`,
`CompositeWitness`, `CompatibleWitnesses`, `witnessesEquiv`,
`downstreamOutputIndex`, `outputIndexEquiv`, `outputProjection_downstream`,
`liftOutput`, `outputProjection_transport`.

`models_restrict_iff` ranges over arbitrary complete composite stores on a
lifted input; `models_restrictInput_iff` handles every validated composite
input. `models_glue_iff` has the explicit downstream agreement premise.
`CompositeWitness` is a subtype of full composite model stores.
`CompatibleWitnesses` is the dependent Sigma of upstream and downstream
whole-model witnesses, indexed by the upstream boundary input.
`witnessesEquiv (η : A.program.Input)` is their explicit equivalence.
Review both inverse laws and proof irrelevance without collapsing stores.
`outputIndexEquiv` covers all output indices; projection transport retains
empty-output metadata. Build `IndexedComponentModelWitnesses`.

### T4 — Restricted partial-denotation domain and values

Files: `IndexedComponentModelDenotation.lean`; required Lake registration.
Prerequisite: T3.

Identifiers @ `IndexedComponentModelDenotation.lean`: `AtMostOneModels`,
`admInput_lift_iff`, `admInput_restrictions_iff`, `denotation_successive`.
`AtMostOneModels (A : MatchedComponent σA) : Prop` universally quantifies
validated input and two complete stores; their `Models` proofs imply equality.
Both `hA : AtMostOneModels A` and `hB : AtMostOneModels B` are explicit.
The lifted and unrestricted-input domain iff requires an admissible upstream
input and admissible downstream input obtained through `boundaryFromOutput`
of upstream `denotation`. `denotation_successive` takes composite `AdmInput`,
provides both intermediate admissibility proofs, and equates the composite
denotation with `liftOutput` of the successive downstream denotation.
No values are claimed outside the common domain. Build
`IndexedComponentModelDenotation`; review domain and values separately.

### T5 — Local strict, total, and zero-writer complete-model fixtures

Files: `IndexedComponentModelLocalFixtures.lean`,
`IndexedComponentModelLocalTest.lean`; required Lake registration.
Prerequisites: T3; `IndexedComponentCompositionPortFixtures` donors.

Identifiers @ `IndexedComponentModelLocalFixtures.lean`: `producer_model`,
`total_model`, `strict_audit_undefined`, `strict_no_model`,
`strict_out_equation`, `zero_producer_forces_zero`.
Identifiers @ `IndexedComponentModelLocalTest.lean`: `boundary_zero_input`,
`totalCompositeStore`, `total_downstream_model`, `total_composite_model`,
`totalPair`, `totalWitness`, `total_pair_roundtrip`, `total_witness_roundtrip`,
`total_store_values`, `strict_no_compatible`, `strictCandidateStore`,
`strict_visible_equation_satisfied`, `strict_no_composite`,
`zero_boundary_input`, `zero_composite_model`, `zero_composite_forces_zero`.
Cases 1–3 below are one bounded three-case dispatch. Prove strict composite
and compatible-witness nonexistence, total complete gluing/restriction and
witness round trips, and the composite zero-writer equation. The visible
`Out = 0` equation has an explicit satisfying candidate composite store;
`strict_no_composite` excludes every full model despite that candidate.
Build `IndexedComponentModelLocalTest`; cycles M1–M4.

### T6 — Empty metadata and nontrivial coordinate gluing

Files: `IndexedComponentModelGeometryFixtures.lean`,
`IndexedComponentModelGeometryTest.lean`; required Lake registration.
Prerequisites: T3; port/axis composition donors.

Identifiers @ `IndexedComponentModelGeometryFixtures.lean`, under its namespace:
`Empty.producer_model`, `Empty.consumer_model`, `Empty.lifted_input_present`,
`Empty.transported_input_present`, `Empty.missing_not_valid`,
`Empty.output_roles_and_identity`; `Axis.producer_model`,
`Axis.consumer_model`, `Axis.producer_admitted`, `Axis.consumer_admitted`,
`Axis.transported_distinguishing_values`, `Axis.coordinate_transport_distinct`,
`Axis.selected_sum_does_not_distinguish`.
Identifiers @ `IndexedComponentModelGeometryTest.lean`, under its namespace:
`Empty.lifted_input_present`, `Empty.boundary_input_present`,
`Empty.boundary_input_eq`, `Empty.compositeStore`, `Empty.downstream_model`,
`Empty.composite_model`, `Empty.empty_output_identity`, `Empty.input_roundtrip`,
`Empty.store_roundtrip`; `Axis.boundary_input_eq`, `Axis.compositeStore`,
`Axis.downstream_model`, `Axis.composite_model`, `Axis.restricted_values`,
`Axis.restricted_not_flattened`, `Axis.store_roundtrip`.
Cases 4–5: use the generic input/store/witness API, check empty output-index
identity and all store round trips, and distinguish actual downstream input
from flattening even when final sums agree.
Build `IndexedComponentModelGeometryTest`; cycles M5–M7.

### T7 — Cyclic selection and hidden whole-store multiplicity

Files: `IndexedComponentModelCycleFixtures.lean`,
`IndexedComponentModelCycleTest.lean`; required Lake registration.
Prerequisites: T3; existing static composition for the matched cycle donors.

Identifiers @ `IndexedComponentModelCycleFixtures.lean`: `cycleUpstream`,
`cycleDownstream`, `cycleBoundary`, `hiddenUpstream`, `totalDownstream`,
`hiddenBoundary`, `cycle_upstream_zero_model`, `cycle_upstream_one_model`,
`cycle_upstream_not_admissible`, `reciprocal_zero_no_model`,
`reciprocal_one_model`, `reciprocal_one_unique`, `hidden_boundary_equal`,
`hiddenStore_distinct`, `total_zero_model`.
Identifiers @ `IndexedComponentModelCycleTest.lean`:
`cycle_boundary_zero`, `cycle_boundary_one`, `cycle_zero_not_compatible`,
`cycle_zero_no_composite_extension`, `cycle_one_model`,
`cycle_one_restrictions`, `cycle_composite_unique`, `cycle_composite_admissible`,
`hidden_same_boundary_via_output`, `hidden_zero_model`, `hidden_one_model`,
`hidden_restrictions`, `hidden_witnesses_roundtrip`, `hidden_private_values`,
`hidden_stores_distinct`, `hidden_final_outputs_equal`, `hidden_final_value`,
`hidden_witnesses_distinct`.
Cases 6–7: quantify selection uniqueness over every composite store and
retain both hidden witnesses, not merely their equal outputs.
Build `IndexedComponentModelCycleTest`; assigned cycles M8/M11/M12.
All three assigned cycles have observed final controller evidence.
Other report-only mutation candidates are not evidence of a completed cycle.

### T8 — Discovery, complete audit, and scoped documentation

Patch files: `IndexedComponentModelTest.lean`, `leanncd/lakefile.toml`,
`leanncd/AGENTS.md`, and the interface design document.
Controller bookkeeping deliverables outside that code patch: record, this
plan, indexed package/manifest/probe artifacts, and execution checkpoints.
Prerequisites: T1–T7.
The aggregate imports LocalTest, GeometryTest, and CycleTest and audits all
new namespaces. Explicit proof entrypoint: `import IndexedComponentModelDenotation`
exposes Inputs/Transport/Witnesses and the restricted corollary.
`import IndexedComponentModelTest` exposes the test aggregate.
Register only in `IndexedExecutionExperiment`; do not add default `LeanNCD`
imports or rerun previous transport/composition slices.
Use scoped identifier/value `rg -n` sweeps, including the Section 6 values,
to check documentation fidelity; protected-file findings are parked, not edited.
Run complete source-copy/probe/manifest checks and release gates in Section 7.
Documentation sweep commands (controller runs these; inspect every match):

```text
rg -n --glob '*.md' 'AtMostOneModels|witnessesEquiv|AdmInput|whole.store|unique.model|rank|phase' /Users/williammacready/code/python/pyncd.worktrees/component-model-gluing-replay/papers/semantics /Users/williammacready/code/python/pyncd.worktrees/component-model-gluing-replay/leanncd/AGENTS.md
rg -n --glob '*.md' '1 / 2|1/2|14|10/10|8/8|7 cases|seven cases' /Users/williammacready/code/python/pyncd.worktrees/component-model-gluing-replay
```

## 5. Case × class audit

Controller deliverable: reconcile these requirements against every sibling
and its call-site premises, with exact identifiers in the record. Relevant
families: occurrence/outcome/`AdmEnv`, contribution/`collect`/equations,
input validity/boundary/store inverses, witnesses, output metadata, and
denotation domains. A required cell may never be silently ignored.

| Case × class | Required | Forbidden | Silently ignored |
| --- | --- | --- | --- |
| 1–2 × occurrence/private | Actual private audit body definedness and full equations | Output-only admission or bypassing strict private work | None permitted |
| All × guard | Every guard-admitted occurrence; excluded valuations remain excluded | Adding excluded valuations or dropping admitted private occurrences | Non-occurrences have no body obligation; justify this classification |
| All × duplicate | Every distinct occurrence's contribution in the finite sum | Deduplication of equal contributions | None permitted |
| 3 × zero-writer | Every unwritten defined coordinate equals additive zero | Arbitrary unwritten boundary/store values | None permitted |
| 4 × empty | Present input bindings, output roles/UIDs and index transport | Inferring absence/identity from lack of coordinates | Coordinate equations may be vacuous; tensor metadata is not ignored |
| 5 × wiring | Actual matched tensor plus certified coordinate equivalence | Name/extent/flattening substitution; output-total-only oracle | None permitted |
| 6 × model multiplicity | Both upstream stores, exact dependent compatibility, unique composite | Unrestricted unique-model composition or cyclic execution claim | None permitted |
| 7 × private multiplicity | Distinct full stores, inverse witnesses, equal boundary/final outputs | Quotienting models by output agreement | None permitted |

No new dedicated guard/duplicate fixture or mutation is established by the
current reports. The controller must supply the generic finite-sum/occurrence
audit and classify coverage honestly before readiness; do not invent controls.

## 6. Seven acceptance cases, donors, observations, and risk

Donor paths: port donors @ `IndexedComponentCompositionPortFixtures.lean`;
axis donors @ `IndexedComponentCompositionAxisFixtures.lean`;
cycle/hidden donors @ `IndexedComponentModelCycleFixtures.lean`.

| Case | Named donor and delta | Reported evidence to retain |
| --- | --- | --- |
| 1 strict internal audit | Reuse port `producerComponent`, `consumerComponent`, `scalarBoundary`; local `consumer` at `other = 0`; no source-program change | Complete producer `Pre = 0`; no consumer/compatible/composite model despite satisfiable `Out = 0` |
| 2 total neighbour | Clone case 1, change only `other` from `0` to `4` | Full consumer `Pre = 0`, `Out = 0`, private `Audit = 1/2`; observed donor tuple `(0, 0, 0, 1 / 2)`, composite `(0, 0, 1 / 2)` |
| 3 zero writer | Reuse `zeroProducerComponent`; inspect its unwritten scalar | `zero_producer_forces_zero` and composite equation constrain every model to zero |
| 4 empty | Reuse `emptyProducerComponent`, `emptyConsumerComponent`, `emptyValidatedInput`, `emptyBoundary`; add whole-store/generic round-trip proofs | Present empty inputs, invalid missing binding, true output roles with UIDs `0`/`1`; observed `(true, true)` |
| 5 coordinates | Reuse `axisProducer`, `axisConsumer`, `axisBoundary`; fill producer store from its actual six statement literals; compare boundary transport with `flattenedPre` | Producer `[1,2,3,4,5,6]`; actual `p=5,q=2`, wrong `p=3,q=4`, corners `1,6`; both sums `14`, families distinct |
| 6 selection | `cycleUpstream := upstreamComponent false`, `cycleDownstream := downstreamComponent true`, `cycleBoundary := scalarBoundary false true` | Private `t=t²`, output copies `t`; reciprocal consumer: both upstream models `0/1`, only `1` extends; composite `AdmInput`, upstream not `AdmInput` |
| 7 hidden multiplicity | Clone cycle producer with `hidden=true`: boundary body/read footprint becomes constant zero; consumer with `strict=false`: reciprocal becomes total `t+1`; use `hiddenBoundary` | Distinct upstream/composite private `0/1`, same boundary zero, same final output `1`, distinct dependent pairs and round trips |

Cycle donor observations are exactly `(some 0, some 1)`, `(none, some 1)`,
and `(0, 0, some 1)`. These are body/output evaluations, not runtime completion.
Model existence, impossibility, and uniqueness are theorem evidence.
The controller record also reports aggregate probes: `true`, `true` for
lifted/transported empty input presence, `(1, 1)` for cyclic composite
private/output values, and `(0, 1, 1, 1)` for hidden private values and both
outputs. These observations do not establish execution completion.

Current manifest: `component_model_gluing_mutations_post.json`, **12 entries**.
Observed tables: `prototype_local_mutations.md` (M1–M4),
`prototype_donor_mutations.md` (M1–M8), `prototype_all_mutations.md` (older M1–M10).
The older 10/10 table has `n/a` expected diagnostics for M9/M10; it is not final
verification. Final evidence is `authoring_mutations.md`: the controller ran
all 12 entries unfiltered, saw every expected diagnostic, restored each
control byte-identically, and rebuilt restored targets green.
Current M9 multiplies the upstream store read by zero, retaining `ρA`.
Final observed diagnostics include M9 ``Tactic `rfl` failed``,
M11 `Application type mismatch`, and M12 `Type mismatch`, exactly as recorded
in the JSON. Seven acceptance cases and 12 authoring cycles are verified;
release reruns remain required.

| Task | Acceptance cases | Current assigned manifest cycles | Risk/verification focus |
| --- | --- | --- | --- |
| T1 | 0 standalone; consumed by 4–5 | 2: M9/M10 | Empty presence, boundary values, private-store inverse premises |
| T2 | 0 standalone; generic audit required | 0 currently | All occurrences, guards, duplicate finite sums, private/zero equations |
| T3 | 0 standalone; exercised by 2,4,5,7 | 0 currently | Dependent witness indexing, both inverses, empty output indices |
| T4 | 0 standalone; restriction justified by 6–7 | 0 currently | Domain iff for every validated input; no hidden existence premise |
| T5 | 3 | 4: M1–M4 | Strict reject and total accept neighbour; zero constraint |
| T6 | 2 | 3: M5–M7 | Empty metadata and coordinate oracle, not final-total parity |
| T7 | 2 | 3: M8/M11/M12 | Universal composite uniqueness and retained hidden witnesses |
| T8 | 0 new cases | All 12; authoring passed, release rerun required | Discovery, all-namespace audit, package replay and claim fidelity |

Evidence labels: M1/M2 are concrete model-counterexample proof kills;
M3/M4 are proof-elaboration kills; M5/M6 are presence/validity
proof-elaboration kills; M7 is a coordinate-counterexample proof kill;
M8 and M10 are inverse/private-identity proof-elaboration kills.
M9 is a transport proof-elaboration kill; M11 is a value proof-elaboration
kill changing the hidden private value; M12 is a model proof-elaboration kill
incorrectly extending the zero cyclic producer by replacing the upstream
store in the glued candidate.
No mutation here is claimed to be a runtime-observation kill.

## 7A. Authoring readiness — verify the plan before execution

Checked against final controller authoring evidence and artifact reports.
Actual checkout replay is **not** an authoring prerequisite. Real-namespace
prototype compilation plus isolated-index tree/source parity establishes
patch fidelity without executing the implementation plan prematurely.

- [x] Controller confirms complete task identifier/file/import inventories
  against the final indexed package, including the supplied fixture exports.
- [x] All final source modules built; exact source-copy checks pass; no
  transcribed/reformatted Lean blocks need execution from this plan.
- [x] Eight final task patches mechanically generated from compiled source,
  with exact ordered file/hash index, required per-task Lake registration,
  complete probes, and final package emission after mutation restoration.
- [x] `package.py --check` applies all eight patches to an isolated index
  based on `2212263c` and verifies resulting tree/current compiled-source
  hashes. Any subsequent packaged source/docs edit invalidates this check.
- [x] Section 5 full case/class sibling and call-site audit complete; no
  required cell silently ignored.
- [x] Full namespace axiom/prohibited-shortcut audit, unfiltered probes, and
  manifest schema/unique replacement checks pass. New proofs admit no `sorry`,
  `sorryAx`, new/custom axiom, native-decision proof axiom, or `unsafe` shortcut;
  report standard dependencies without hiding pre-existing baseline warnings.
- [x] Revised M9 and every final entry have observed intended diagnostics,
  byte-identical restoration and green restored targets; actual unfiltered
  manifest run passes, not merely `--check` or a filtered task subset.
- [x] All seven cases checked through the generic whole-witness API;
  controller records seven cases, 12 cycles, and actual probe observations,
  not inherited totals.
- [x] Protected primary-file hashes unchanged; documentation claims swept;
  package scope excludes protected working copies and `.claude/settings.json`.

Only after Section 7A passes may the controller mark the plan verified and
begin actual implementation execution. Controller package commands:

```text
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/papers/semantics/component_model_gluing_artifacts/package.py --emit
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/papers/semantics/component_model_gluing_artifacts/package.py --check
```

## 7B. Execute the verified plan, then release

- [x] Controller executes `package.py --replay` in the task-owned clean-base
  checkout: actual ordered patch application/builds/exact source-copy checks
  and explicit per-task commits. `execution_replay.json` holds checkpoints.
  These execution results are distinct from isolated-index authoring parity.
- [x] Per-task reviews/checkpoints completed and findings adjudicated.
- [x] Controller runs full `LeanNCD Tests IndexedExecutionExperiment` build.
- [x] Two final whole-branch reviews completed: model soundness; and
  integration/fixtures/claim fidelity. Fix finding groups separately and
  rerun affected gates, then full build, before integration.
- [x] Protected primary-file hashes unchanged; staged scope excludes their
  working copies and `.claude/settings.json`; documentation claims swept.
- [x] After green release gates and adjudication, merge to local main and
  clean up only the task-owned branches/two worktrees; no push.

Controller commands use absolute checkout paths. For replay's manifest gates:

```text
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/papers/semantics/component_model_gluing_artifacts/package.py --replay /Users/williammacready/code/python/pyncd.worktrees/component-model-gluing-replay
bash /Users/williammacready/code/python/pyncd.worktrees/component-model-gluing-replay/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/component-model-gluing-replay/leanncd /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/papers/semantics/component_model_gluing_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/component-model-gluing-replay/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/papers/semantics/component_model_gluing_artifacts/execution_mutations.md /Users/williammacready/code/python/pyncd.worktrees/component-model-gluing-replay/leanncd /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/papers/semantics/component_model_gluing_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/component-model-gluing-replay/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/component-model-gluing-replay/leanncd LeanNCD Tests IndexedExecutionExperiment
```

Before readiness, the controller also runs the unfiltered authoring manifest
and compiled-source/probe checks in the prototype checkout; execution reruns
the release manifest/build gates in replay. Package `--check` is a fidelity
check, not a replacement for either compilation or mutation observations.
Record detailed results/findings/accounting in `component_model_gluing_record.md`,
not in an expanding live plan. Authoring target approximately 50M cumulative
input tokens; execution cap 175M. If token-report accounting is unavailable,
say so; report known breaches, including the recorded cyclic-donor turn overrun.

After green controller gates and adjudicated final reviews, integrate the
executed branch into **local main**, without overwriting protected edits.
Verify integration, delete only the task branch and any task-owned replay
branch, and remove only the two named task worktrees after inspecting their
contents. No force cleanup of other worktrees, shared history rewrite, or push.
Close-out distinguishes the unrestricted rank-independent witness bijection
from the explicitly restricted denotation law, preserves open operational and
categorical obligations, and states exactly what was verified or remains blocked.
