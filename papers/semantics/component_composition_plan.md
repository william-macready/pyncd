# Static sealed component composition — live execution plan

## 1. Authority, result and execution mode

Implement the full static sealed-composition slice from
[the handoff](component_composition_handoff.md), using the verified eight-patch
package, not another source/proof design dispatch. Process weight is Full.
The historical [record](component_composition_record.md) remains separate and
controller-owned. This plan contains no transcribed Lean or speculative probes.

The public result is `IndexedComponentComposition.compose_match A B wire`,
deriving `SourceContractMatch` for the constructed `program`, `schedule`,
`contract`, `fragment` and `graph`. `compose A B wire` packages those data and
whole ports as a `MatchedComponent (declarations A B)`.

Premises are local finite decidable `Declarations Unit` universes, the fixed
`RationalReference.Carrier`/`registry`/`ops`, two independently matched local
packages with exact Nodup port roles, and a `Boundary`: a bijection of **all**
B inputs with **all** A outputs, with certified whole-coordinate `Domain`
adapters. Checked even/odd identities are chosen and proved internally.
No caller allocator or composite acceptance premise is permitted.

The controller keeps the compiled implementation branch and its history.
Execution means applying the exact patches, in order, to a fresh **detached**
worktree at local main `16721af5`, with actual task builds and direct reviews.
It does not mean pretending to implement fresh code on the already-patched
branch. Keep this plan and the immutable patch package in the authoring
worktree; do not copy them into replay where added-file patches could collide.
Final release gates run again on the implementation merge candidate itself.

## 2. Immutable package and verified starting evidence

All artifact paths below are relative to `papers/semantics/`.

| Evidence | Exact meaning |
| --- | --- |
| `component_composition_artifacts/task_patches.json` | BASE `16721af5`; compiled HEAD `06d4e470a0c30f00ab5347e13f7c358e55593c17`; eight ordered patches; 27 covered files |
| `component_composition_artifacts/authoring_patch_replay.json` | Every hash/check/apply passed in order using a temporary index; covered-file diff empty against compiled HEAD |
| `component_composition_artifacts/authoring_verified_mutation_results.md` | Corrected 16/16 intended-diagnostic cycles; byte-identical restoration and restored target green |
| `component_composition_mutations_post.json` | Exact anchors, targets and observed line-independent `expect` substrings; do not rewrite |
| `component_composition_artifacts/foundation_audit.lean` | Compiled constructor/proof/fixture namespace audit; only standard axioms |
| `component_composition_record.md` | Exact premises, all nine match-field derivations, observations and honest historical accounting |

Controller evidence additionally establishes the full
`LeanNCD Tests IndexedExecutionExperiment` build and final targeted consumers/
snippets green. Main remains `16721af5`; the protected primary semantics
README and synthesis hashes match. These are authoring observations, not a
substitute for replay and candidate release receipts.

The manifest is authoritative for each exact Files list and patch hash:

| Task / patch suffix | SHA-256 |
| --- | --- |
| 1 `task_01_scope.patch` | `ca7e3b372803ed1ff9c0232c3092fb8fefa684ccbb4c398cad6d354c68a8c74b` |
| 2 `task_02_source-schedule.patch` | `c411eff37c5a090d0cec31349a93ffa0553017fcefa4efb73b5a63826c2c0716` |
| 3 `task_03_closure.patch` | `32e962c224a480f55f335970631119236c02b0344c5f37b24cf7b31b613aa485` |
| 4 `task_04_match.patch` | `f7c77859b11adf757534b595973a2502f7b3c39d349e037e3fab35b3db117410` |
| 5 `task_05_port-fixtures.patch` | `319969c023e9dd607fcc01141301f236e9fd72a4715453f5e92e4b73a3bdfa60` |
| 6 `task_06_advanced-fixtures.patch` | `80a872a87dc50bec115f37d2dd620ec1904e3a643cb080b9a021584b0cf29611` |
| 7 `task_07_correspondence-controls.patch` | `962fb591c453426f6b6619be1e08df8583a25e43b75aeec6c4057432c658ca20` |
| 8 `task_08_discovery.patch` | `9fc913130f00a619e53d1bbf792c8d4960298ea1049bab9186b185a6a21301e9` |

Do not regenerate patches, mutation code, or expected diagnostics. All paths
were verified in Git objects and ordered replay matches the compiled bytes.

## 3. Semantic acceptance audit

| Classification | Requirement or excluded premise | Acceptance evidence |
| --- | --- | --- |
| Required | Tensor universe exactly `A.Tensor ⊕ B.program.Defined` | `declarations`, embeddings, scope proofs, collision fixture |
| Required | B inputs alias wired A outputs; all private tensors retained | `Boundary`, `closureScope`, strict/private and collision observations |
| Required | Whole input/output tensor UID, sort and axes survive empty domains | `outputPorts`, empty fixture; output metadata not inferred from addresses |
| Required | Complete Nodup tensor/key orders; appended validation order | `tensor_order`, `keyEquiv`, simultaneous-fault controls |
| Required | Distinct admitted occurrences, repeated ordered reads, strict whole-array footprints | `occurrenceEquiv`, `writer_reads`, collision and unequal-axis controls |
| Required | Every noninput coordinate has exactly one collector, including empty capability fibers | `ClosureFacts`, `close_ok`, zero and collector-rejection controls |
| Required | Genuine nine-field match derived from the two local matches | `compose_match`, audit, six constructed correspondence instances |
| Required | Existing runner partiality and publication behavior | Strict failure after Out publication; graph/source observations |
| Forbidden | Composite close/match, execution agreement, reached-store, collector-fiber or rank premise | Inspect public constructors and their dependency axioms |
| Forbidden | Forwarding writer, private-tensor deletion, contribution deduplication | Exact writer/publication counts and graph-only counterexamples |
| Forbidden | Name/cardinality-only axis adaptation or UID-sorted validation | Certified `Domain`; typed adapter and fault-order controls |
| Forbidden | Production import widening or changed closure/runner/registry semantics | Nondefault registration and whole-branch integration review |
| Intentionally ignored | Mathematical equality of contributions as a deduplication signal | Two equal +1 contributions remain distinct occurrences |
| Intentionally ignored | Empty address lists as evidence of absent ports | Required input UID 20 and empty output metadata persist |
| Intentionally ignored | Equality of collector/fragment/tensor list order | Collision collectors and capability fibers deliberately differ |
| Intentionally ignored | Disabled steps as a global phase barrier | Upstream-first priorities; existing runner skips disabled steps |

Ranked phase execution, model gluing, associativity, units, arbitrary adapters,
residual inputs, fanout and open ports are excluded/unproved. Do not rerun the
transport plan or widen parked accounting and old per-fixture coverage.

## 4. Proof and donor map

Reuse verified donor infrastructure; applying patches is the implementation.
Review these changes, not an independently recreated proof.

| Derived match field | Donor → constructed change |
| --- | --- |
| `close_ok` | Local accepted closures → `ClosureFacts`, five derived `closureScope` premises, disjoint checked IDs and `close_assembled` |
| `input_roles` | Local exact roles → retain upstream inputs; downstream inputs become upstream defined outputs |
| `tensor_order` | Local complete schedules → upstream enumeration then downstream defined tensors, also used by contract |
| `outputs_exact` | Local downstream output coverage → mapped output addresses, separately retained whole output ports |
| `sourceToWriter` | Local bijections → `occurrenceEquiv` and mapped/concatenated writer-position equivalences |
| `writer_destination` | Local destination equations → transported addresses and proved dependent downstream-domain cast |
| `writer_reads` | Local ordered footprint equations → mapped lists preserving repetitions and strict footprints |
| `eval_agrees` | Local all-partial-store agreement → restriction by each embedding and transported evaluations |
| `priority` | Local full equations → collector lookup transport, appended keys and canonical steps |

Generic donors are `IndexedComponentTransport` (`Domain`, `Embedding`,
`pull`), its Expr/Eval transport lemmas, `IndexedOpenComposition` (`close`,
`runChecked`), `IndexedCompositionClosure`, `IndexedCompositionMatch`,
`IndexedCompositionFibers` and `default_run_correspondence`.
The whole-program `IndexedCompositionParityTest`/`suppliedMatch` are comparison
donors only. New `producerMatch` and `consumerMatch other` supply genuinely
local matches; consumer bodies reuse `squareBody`, `auditBody`, `strictArray`.
Never present shared expression helpers as an independent interpreter oracle.

Symbol routing (paths in `leanncd/experiments/indexed_execution/` unless
otherwise stated):

- `MatchedComponent`, `Port`, `Boundary`, `declarations`, `upstream`,
  `downstream`, `downstreamId` @ `IndexedComponentCompositionScope.lean`.
- `program`, `occurrenceEquiv`, `inputPorts`, `outputPorts` @
  `IndexedComponentCompositionProgram.lean`; `keyEquiv`, `tensorOrder`,
  `keyOrder`, `schedule` @ `IndexedComponentCompositionSchedule.lean`.
- `ClosureFacts.of_close`, `ClosureFacts.close`, `mem_definedAddresses_iff`,
  `ClosureFacts.collector_iff` @ `IndexedComponentClosureFacts.lean`.
- `ClosureScope`, `mapWriter`, `close_assembled`, `canonicalSteps_assembled`
  @ `IndexedComponentCompositionClosure.lean`; `closureScope`, `close_ok`,
  `outputs_exact`, `graph_steps` @ `IndexedComponentCompositionAssemble.lean`.
- `sourceToWriter`, `writer_destination`, `writer_reads`, `eval_agrees` @
  `IndexedComponentCompositionMatch.lean`; `collectorCapabilities_upstream`,
  `collectorCapabilities_downstream`, `priority` @
  `IndexedComponentCompositionPriority.lean`; `compose_match`, `compose` @
  `IndexedComponentComposition.lean`.
- `producerMatch`, `consumerMatch` @
  `IndexedComponentCompositionLocalFixtures.lean`; `producerComponent`,
  `consumerComponent`, `scalarBoundary`, `emptyBoundary` @
  `IndexedComponentCompositionPortFixtures.lean`; `emptyBothFaultsRaw` @
  `IndexedComponentCompositionTest.lean`.
- Guarded occurrence/order checks @
  `IndexedComponentCompositionCollisionFixtures.lean`; `firstPoint`,
  `axisMappedReads`, `axisMappedFootprint` @
  `IndexedComponentCompositionAxisFixtures.lean`.
- `strict_correspondence`, `total_correspondence`, `empty_correspondence` @
  `IndexedComponentCompositionCorrespondenceTest.lean`; `shortcut`,
  `omittedCapability` @ `IndexedComponentCompositionCounterexampleTest.lean`;
  `input_not_a_downstream_destination`,
  `equal_cardinality_is_not_an_axis_adapter` @
  `IndexedComponentCompositionInterfaceTest.lean`.

## 5. Replay protocol and bounded briefs

Controller instantiates `<AUTHOR>` as
`/Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-composition`,
`<PRIMARY>` as `/Users/williammacready/code/python/pyncd`, and chooses a fresh
absolute `<REPLAY>` path owned by this task. `<CANDIDATE>` is the existing
implementation worktree; it may equal `<AUTHOR>`. Angle-bracket paths below
are substitution instructions, not shell variables or literal shell syntax.
Resolve every placeholder before execution. Subagent briefs use plain,
separate commands: no `cd`, shell variables, command chaining, pipelines into
git, or root Lake. The controller-only preparation script must run with its
shell working directory set to replay, as already observed during preparation;
this does not change the chat workspace or require a workspace menu.

```sh
/usr/bin/git -C <PRIMARY> rev-parse main
/usr/bin/git -C <PRIMARY> worktree add --detach <REPLAY> 16721af5
```

Run the already-established `new-slice` preparation/cache-refresh procedure
for this detached worktree, without `--plan` copying; retain cache receipt.
Do not improvise a cold Mathlib build. Refresh and establish the baseline:

```sh
bash <REPLAY>/leanncd/scripts/lake-build.sh <REPLAY>/leanncd LeanNCD
bash <REPLAY>/leanncd/scripts/lake-build.sh <REPLAY>/leanncd LeanNCD Tests
```

For each row in the patch table, substitute its literal absolute patch path:

```sh
/usr/bin/shasum -a 256 <AUTHOR>/papers/semantics/component_composition_artifacts/<PATCH>
/usr/bin/git -C <REPLAY> apply --check <AUTHOR>/papers/semantics/component_composition_artifacts/<PATCH>
/usr/bin/git -C <REPLAY> apply <AUTHOR>/papers/semantics/component_composition_artifacts/<PATCH>
```

Require its exact SHA-256, then build only the task targets below. Review the
actual cumulative replay diff and the current task Files list; checkpoint
records patch/hash, build result, review adjudication and remaining gates.
No per-task source reimplementation or nested agents. Do not commit replay
changes merely to fabricate a fresh implementation history.

Each task brief is its section below plus this protocol, its exact patch row,
the semantic audit and relevant donor row. Read only the corresponding
manifest Files list and named declaration windows; use Read windows of at
most 60 lines, and `rg -n` for locating identifiers. No whole-patch reads or
production API rediscovery. Split review if a bounded objective would exceed
60 actions/250k retained context; target 30 actions. Do not silently overrun.

Patch application is serialized in the verified order `1 → 2 → … → 8`.
Semantic prerequisites are `1 → 2 → 3 → 4`, `3 → 5 → 6`,
`4 + 6 → 7 → 8`. The fixture observations do not depend on task 4's match;
task 7's correspondence instances do. Do not confuse serialization policy
with additional source-level premises.

Cycle ownership counts below are **deferred**: L/F/C/T targets include later
fixtures. Run the actual unfiltered manifest only after task 7. Tasks 1–4
checkpoint with kernel proofs and targeted builds, not future fixture kills.

### Task 1 — scope and early nondefault registration

Files (2):
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionScope.lean`
- `leanncd/lakefile.toml`

Donor/change: transport `Domain`/`Embedding` and finite declarations → exact
sum universe, checked even/odd tensor/tag/capability identities, upstream and
downstream embeddings, `MatchedComponent` and whole-port `Boundary`.
Register the real module split early in `IndexedExecutionExperiment`, never
production `LeanNCD`. Named windows: `declarations`, `downstreamId`, boundary
and embedding definitions/proofs; only composition registration in lakefile.
Fixtures: 0 new families/cases. Deferred cycles: 2, L1/L2.

```sh
bash <REPLAY>/leanncd/scripts/lake-build.sh <REPLAY>/leanncd IndexedComponentCompositionScope
```

Review: internal injectivity/disjointness proofs and complete boundary premises;
no caller allocation, erased empty metadata or phantom downstream input tensor.

### Task 2 — source and complete schedule

Files (2):
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionProgram.lean`
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionSchedule.lean`

Donor/change: local programs, guards and ordered schedules → transported
statements/valuations, exact admitted occurrences, downstream output ports,
upstream-plus-defined-downstream tensor/key order and equivalences.
Named windows: `program`, `outputPorts`, `occurrenceEquiv`, `keyEquiv`,
tensor enumeration and guard transport. Fixtures: 0. Deferred cycles: 3,
L5/L6/L7. Do not treat later empty/collision builds as current checkpoints.

```sh
bash <REPLAY>/leanncd/scripts/lake-build.sh <REPLAY>/leanncd IndexedComponentCompositionProgram IndexedComponentCompositionSchedule
```

Review: complete Nodup orders, exact guard/valuation retention and whole ports;
validation order is observable, not a convenient UID sorting operation.

### Task 3 — derived canonical closure and assembly

Files (4):
- `leanncd/experiments/indexed_execution/IndexedComponentClosureFacts.lean`
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionClosure.lean`
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionAssemble.lean`
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionAssemblyAudit.lean`

Donor/change: accepted local `close` and reusable closure facts → mapped writer
reads/bodies/destinations, collector rows and steps, appended assembly, then
all five structural `ClosureScope` premises derived concretely from A/B/wire.
Named windows: `ClosureFacts.of_close`, `ClosureFacts.close`,
`mem_definedAddresses_iff`, `collector_iff`, `closureScope`,
`close_assembled`, `canonicalSteps_assembled`, `close_ok`, `outputs_exact`.
Fixtures: 0. Deferred cycles: 2, L3/L4.

```sh
bash <REPLAY>/leanncd/scripts/lake-build.sh <REPLAY>/leanncd IndexedComponentCompositionClosure IndexedComponentCompositionAssemble IndexedComponentCompositionAssemblyAudit
```

Review: no residual structural premise at the public constructor; exact
collector fibers, including zero writers; ordered reads; downstream aliases
are upstream collectors, with disjoint defined images and no forward copy.

### Task 4 — genuine match and public package

Files (3):
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionMatch.lean`
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionPriority.lean`
- `leanncd/experiments/indexed_execution/IndexedComponentComposition.lean`

Donor/change: supplied local matches and generic transport/closure → all nine
fields in §4, including downstream destination cast and full priority.
Named windows: match field proofs, collector lookup transport, `compose_match`,
`compose`; inspect exact constructor premises and imports. Fixtures: 0.
Deferred cycles: 0; kernel proofs/audit, not invented mutation completeness.

```sh
bash <REPLAY>/leanncd/scripts/lake-build.sh <REPLAY>/leanncd IndexedComponentComposition
```

Review: `eval_agrees` for every partial store, not reached stores only;
priority equations rather than a general phase-barrier claim; no independently
authored composite match, hidden execution agreement, rank or fiber premise.

### Task 5 — scalar, zero and empty-port fixtures

Files (3):
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionLocalFixtures.lean`
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionPortFixtures.lean`
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionTest.lean`

Donor/change: clone `IndexedCompositionParityTest.reference`/`contract`/
`fragment`, changing declarations and roles into a producer `Fin 1` (Pre only)
and consumer input Pre/output Out/private Audit local matches; vary `other`,
producer capability fiber, empty domains/raw bindings and validation order.
For zero writers, clone the new local producer and set Pre statements to zero,
retaining its scalar collector with no capabilities. For empty domains, use
`ExecutableReferenceFixtures.emptyDeclarations`' zero-extent shape mechanism,
with two local tensors per component and explicit empty input/output roles.
Named windows: `producerMatch`, `consumerMatch`, `producerComponent`,
`consumerComponent`, `scalarBoundary`, empty port/binding definitions and
`emptyBothFaultsRaw`. Families: 3 (scalar/zero/empty); terminal cases: 8
(strict, total, zero, empty present, empty absent, three simultaneous-fault
orders). Graph/source observations mirror these, not additional families.
Deferred cycles: 2, F2/F3.

```sh
bash <REPLAY>/leanncd/scripts/lake-build.sh <REPLAY>/leanncd IndexedComponentCompositionTest
```

Review against §6: exact event/publication counts, strict retained Out and
absent Audit; zero collector without forwarding; empty-port metadata and both
faults. Local donor runs are not proof of constructed composite behavior.

### Task 6 — collision and unequal-axis discrimination

Files (2):
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionCollisionFixtures.lean`
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionAxisFixtures.lean`

Donor/change: clone the local producer, add private Audit literal 7 at old UID
2, and change Pre to one statement, three
valuations/guards, distinct equal contributions and nonmatching list orders;
pair it with `consumerComponent 4`, whose private Audit also has old UID 2.
Use the transport adapter donor for a certified 2×3/3×2 axis swap and nonpalindromic
repeated footprint: clone `IndexedComponentTransportTest.swapDomain`,
`srcShape`, `dstShape`, `p`, `q`, add the final q read, and supply a six-cell
literal producer. Named windows: guarded occurrence/order checks, collector
and capability checks, `firstPoint`, mapped reads and `axis.graph-only`.
Families/cases: 2/2 (collision, unequal-axis); mirrored source/graph checks
and structural assertions are not separately mutation-complete fixtures.
Deferred cycles: 1, F1.

```sh
bash <REPLAY>/leanncd/scripts/lake-build.sh <REPLAY>/leanncd IndexedComponentCompositionCollisionFixtures IndexedComponentCompositionAxisFixtures
```

Review: fixture `firstPoint` shared by source/writer/read list; corrected F1
must reach `axis.graph-only`, not local agreement failure or sorry-abort.

### Task 7 — correspondence, typed and graph-only controls; audit

Files (5):
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionCorrespondenceTest.lean`
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionInterfaceTest.lean`
- `leanncd/experiments/indexed_execution/IndexedComponentCompositionCounterexampleTest.lean`
- `papers/semantics/component_composition_mutations_post.json`
- `papers/semantics/component_composition_artifacts/foundation_audit.lean`

Donor/change: `default_run_correspondence` → six constructed instances
(strict/total/zero/empty/guarded collision/axis), empty quantified over every
raw binding. Existing graph bodies → altered graph-only data without forged
matches; `Defined`/`Domain` → typed negative cases with legal neighbours.
Named windows: `strict_correspondence`, `total_correspondence`,
`empty_correspondence`, remaining instance declarations, `shortcut`,
`omittedCapability`, typed claims and collector counterexamples.
New control families: 2 (typed/graph-only); cases: 8 (four typed accept/reject,
four graph-only). Six correspondence theorems reuse existing fixture families.
Deferred cycles owned here: 6, C1–C4/T1–T2; now run **all 16** unfiltered.

```sh
bash <REPLAY>/leanncd/scripts/lake-build.sh <REPLAY>/leanncd IndexedComponentCompositionCorrespondenceTest IndexedComponentCompositionInterfaceTest IndexedComponentCompositionCounterexampleTest
```

Controller reruns its verified unfiltered anchor checker and mutation runner
against the exact manifest, with its existing invocation rebound to replay.
Require every anchor unique, intended `expect` present, failure, byte-identical
restore and restored target green. Reuse existing wrappers/runner; do not author
a replacement mutation harness. Recompile the exact audit through the
controller's previously verified `check-snippet.sh` invocation on replay.

### Task 8 — discovery and separated record

Files (6):
- `leanncd/AGENTS.md`
- `papers/semantics/categorical_tensor_logic_component_interfaces.md`
- `papers/semantics/component_composition_record.md`
- `papers/semantics/component_composition_artifacts/authoring_verified_mutation_results.md`
- `papers/semantics/component_composition_artifacts/authoring_axis_control_results.md`
- `papers/semantics/component_composition_artifacts/authoring_mutation_results.md`

Donor/change: existing discovery/design status → actual static API, limitations
and honest separated receipts. Apply the verified patch to replay only;
the controller owns any subsequent record updates on the implementation branch.
Read bounded changed headings/status windows, not historical transport plans.
Fixtures/cycles: 0/0. Documentation checkpoint: exact Files list and scope
review; no additional source edits or documentation created by this task.

## 6. Measured observations and intended diagnostics

- Logical scalar example: three scalars, four writer occurrences, three
  publications. Constructed strict `other=0`: graph **and** source fail after
  six events, Out=0 already published, Audit absent. Total `other=4`: seven
  events complete, Audit=1/2. Tags 20/22/41/61, capabilities 202/204/403/603,
  tensor UIDs 0/3/5 are observed constructed identities.
- Zero producer + total consumer: five events, retained `(Pre, [])` collector
  publishes Pre=0; exactly two consumer writers, three publications.
- Empty external input UID 20 present: complete, zero events; absent: invalid
  20. Output port UID 3, sort Unit, axis UID 51 extent 0 survives despite
  `Contract.outputs=[]`. Tensor enumeration `[20,0,3]`; simultaneous missing 20
  and unexpected 3 rejects 20; reversed and UID-sorted alternatives reject 3.
- Collision: one statement, three valuations, guards TFT, admitted v2 then v0;
  two equal +1 contributions remain distinct. Private UID 4=7, UID 5=5/2;
  Pre=2/Out=4, five writers/four publications/nine events. Collector order
  `[privateAudit,Pre]` and Pre fiber `[102,101]` differ from fragment/tensor order.
- Axis: certified 2×3→3×2 swap; p/q/p/q maps to
  `(2,0),(0,1),(2,0),(0,1)`; Out=14. Not a palindromic reversal probe.
- Typed: forbid B input Pre as `Defined` destination, accept Out; forbid
  equal-cardinality flat-6 adapter, accept certified 2×3↔3×2.
- Graph-only shortcut: seven events complete versus original six-event failure.
  Coherent equal-contribution omission: eight events, Pre=1/Out=1 versus
  nine events, Pre=2/Out=4. Zero-collector drop: `missingCollector`;
  duplicate boundary collector: `duplicateCollector`.

Observed `expect` substrings are exact manifest data, not line-number oracles:
L1 `'change' tactic failed`; L2 `unsolved goals`; L3 `Type mismatch`;
L4 `could not unify`; L5/L7 `Application type mismatch`; L6 `Invalid field`,
each with its manifest module name. F1 `axis.graph-only`;
F2 `composite-empty-present: expected`; F3 both simultaneous-fault and
validation-order labels. C1/C2/C3/C4 use their manifest `composite-...` labels;
T1 `Type mismatch`, T2 `unsolved goals`, each with InterfaceTest module name.
Consume the full strings from JSON rather than copying this summary into code.
Coverage totals: 7 live proof/type, 3 fixture-source/binding, 2 typed neighbour,
4 graph-only counterexample cycles = 16. Not 16 live runner kills, nor
per-assertion-complete coverage. Initial no-expect receipt is historical only.

## 7. Controller release and integration gates

1. All eight replay hashes/applications/builds/task reviews pass. Compare the
   manifest's 27 paths between replay and the frozen reviewed candidate:
   exact bytes, no difference, before subsequent controller record updates.
   Preserve implementation history; do not overwrite candidate with replay.
2. On **candidate itself**, rerun the unfiltered exact manifest anchor check,
   all 16 intended-diagnostic/restoration cycles, and exact foundation snippet/
   namespace audit using the controller's already verified commands. Require
   standard axioms only; top `compose_match`/`compose` and all six correspondence
   instances use only `propext`, `Classical.choice`, `Quot.sound`.
3. Run the full release command on candidate, not just replay:

```sh
bash <CANDIDATE>/leanncd/scripts/lake-build.sh <CANDIDATE>/leanncd LeanNCD Tests IndexedExecutionExperiment
/usr/bin/git -C <CANDIDATE> diff --check 16721af5
/usr/bin/git -C <CANDIDATE> diff --stat 16721af5 HEAD
```

4. Two final whole-branch review lenses examine `16721af5..HEAD`:
   **soundness** — public premises, nine derivations, dependent casts, full
   partial-store/read/priority preservation, boundary/closure and axiom audit;
   **integration/observations** — exact files/registration, graph and source
   outcomes, counts, discriminating orders/axes, honest control classifications,
   existing correspondence/transport regressions and documented exclusions.
   Findings must be fixed or explicitly adjudicated; genuine unfixable or
   load-bearing plan defects stop execution, not silent scope substitution.
5. Verify main still at base, protected primary README/synthesis hashes unchanged,
   and candidate committed/clean. Stage only explicit intended paths; never
   `.claude/settings.json`, temporary indexes/build logs or others' changes.
   The verified patch package is an explicitly requested deliverable.
   Once all gates are green, merge the **implementation branch** locally:

```sh
/usr/bin/git -C <PRIMARY> merge --no-ff <IMPLEMENTATION_BRANCH>
/usr/bin/git -C <PRIMARY> worktree remove --force <REPLAY>
/usr/bin/git -C <PRIMARY> worktree remove <CANDIDATE>
/usr/bin/git -C <PRIMARY> branch -d <IMPLEMENTATION_BRANCH>
```

Remove only this task's implementation and detached replay worktrees/branch.
Preserve other original worktrees and both dirty primary files. The detached
replay is intentionally dirty: use its status and exact manifest comparison
to identify only this task's applied patches and owned build cache before the
authorized targeted `--force` removal. Do not force unknown changes or the
candidate; stop on anything outside that scope. Never push or offer permission
menus. Report local main ahead of origin.

## 8. Accounting and completion boundary

Authoring target: ≤30 actions; hard checkpoint 60 actions/250k retained context.
Execution briefs inherit bounded tasks and require breach disclosure.
The accounting script does not support this SDK transcript: no numerical
cumulative-token/retained-context compliance is claimed from that failure.
Historical prototype overruns remain in the separate record, not rewritten as
passes. Record measured totals only if actually available; otherwise say so.

This authoring dispatch stops after committing **only this live plan**.
The parent verifies it before execution. Completion of this plan is not
completion of replay, candidate release reviews or local-main integration.
