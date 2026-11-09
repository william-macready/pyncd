# Ranked component execution: verified implementation plan

**Full path:** new generic operational proof capabilities and a soundness surface.
This is the fresh second authoring phase, written from compiled prototype receipts,
the frozen package and the companion record; it introduces no transcribed Lean.
Proof implementation and prototype validation are complete. Frozen-source reviews,
clean replay, replay validation and local integration remain controller gates,
not accomplishments asserted by this plan.

## 1. Goal, premises and boundaries

For finite decidable `Declarations Unit`, exact-rational sealed matched components
`A`, `B`, their supplied `Boundary`, validated upstream input and two component
rank certificates:

- Construct `compositeRankCertificate` for the actual `compose` program.
- Derive upstream-first execution of actual default graph `runChecked`, including
  private work and strict undefined failure; list order alone is insufficient.
- Derive an explicit shared phase cut and entire graph/reference state projections,
  preserving ordered ledgers, private values, pending occurrences and accumulators.
- Derive downstream input from the completed whole upstream output interface, with
  explicit `boundaryFromOutput` equality and metadata-preserving empty input.
- Account for the actual composite default `nA + nB + 1`, not the leaf sum
  `(nA + 1) + (nB + 1)`.

No assumed execution agreement, model existence, uniqueness or completion premise.
Ranks establish progress, not primitive totality. Graph public `run` revalidates
and regenerates its graph; it is not substituted for `runChecked`.
Reference execution is `Program.Executor.run` on validated inputs. Existing
`default_run_correspondence` supplies the raw-input/`runValidated` boundary:
composite full-tensor validation order is unchanged, not two leaf validations,
and internal boundary tensors are not additional caller bindings.

Keep all additions nondefault under `IndexedExecutionExperiment`, discoverable
through `import IndexedRankedExecutionSemantics` and the task06 Lean instructions.
Do not change core language, registry, scheduler, runners, denotational category
or certified source functor. Exclude arbitrary unequal explicit debug fuel,
generic trace algebra, process identities/associativity, event-exact source-category
interpretation, broader interfaces, automatic matches and backend/numerical
refinement. No speculative recurring-defect repair or unrelated cleanup.

## 2. Frozen evidence and package contract

Authority: `categorical_ranked_execution_handoff.md` for goals;
`categorical_ranked_execution_record.md` for current exact API and measured evidence;
`categorical_ranked_execution_artifacts/package.json` for paths, targets and SHA256.
All three paths are under `papers/semantics/`.
Session-only receipts are `rank-prototype.md`, `phase-prototype.md`,
`phase-runs.md`, `reference-phase.md`, `fixture-prototype.md` under
`/Users/williammacready/.copilot/session-state/a285d1df-05fb-4a49-9f7e-23b13dcfa082/files/`.
Early receipts contain superseded pending-work statements; the current record and
controller evidence govern completion status.

The mechanical package contains six patches / 21 distinct exact files, based on
`a8568ddb9df27867bfd40d8c5a3fb590cfbab6d8`. Authoring verification passed
`package.py --check` (hashes and ordered temporary-index application); all 21
current source hashes also matched the metadata. Every packaged Lean file already
passed its named-module build and final-content `check-snippet.sh`.
Do not regenerate patches, retype proofs, or substitute an unverified source copy.

| Task patch | SHA256 |
| --- | --- |
| `01-ranks.patch` | `2c96758814dc0a5fabf36c4edfc7c78d7e39ecfdfa770db41f704700f26d7137` |
| `02-state-transport.patch` | `f10096806a66bd79043e0756ae061f911fa7d0e52ac243d742bfec85acae4909` |
| `03-graph-runs.patch` | `125679349db974fe81a8c1dceffceacfb89ff95b8a0ae04187f8cc7c2b6e482a` |
| `04-reference-runs.patch` | `3f842995bbb55478d4bdf0d0a6da7abf92345845ea05c8eb0d018fc0607385c5` |
| `05-acceptance.patch` | `4c219d322d1ea32b8cf6f0cb24932278a5bb135a86c4ceaddfaf8ba4bb89830a` |
| `06-documentation.patch` | `ed6f345167b03346c28f549facf9f7f132684d25570cffcd7f2566da3bc7d6a2` |

Task06 freezes three status/instruction documents plus the current companion
record. Compare their exact packaged bytes before controller close-out addenda.
Later review/replay/integration receipts appended to that record are explicitly
outside the immutable snapshot comparison, not permission for code drift.
Keep this live plan separate from that record.

## 3. Controller protocol and exact commands

Every brief starts with: plain separate shell commands; absolute paths; no shell
variable expansion, compound `cd`, pipelines into git, root-level Lake, commits
without controller ownership, or edits outside the reviewed task. Read only
40–60-line windows around the identifiers listed below. No fresh proof worker
or per-fixture worker is needed for frozen replay.

In command blocks replace these literal placeholders manually with absolute paths:
`<S>` is `/Users/williammacready/code/python/pyncd.worktrees/categorical-representation-semantics`;
`<P>` is `<S>/papers/semantics/categorical_ranked_execution_artifacts`;
`<W>` is a NEW, controller-owned replay worktree path;
`<L>` is `<W>/leanncd`; `<N>` is the completed task number, 1 through 6.
Do not use shell variables. Each displayed line is a separate command.
Scratch index storage stays inside the worktree and is automatically removed;
never use system temporary directories.

First complete two whole-branch frozen-source-plus-plan reviews:
(1) rank/progress/phase soundness; (2) runner/state/validation/budget integration.
Give reviewers these exact sections/identifiers, 60-line windows and bounded
budgets; persist findings incrementally in controller-owned record addenda.
Adjudicate findings before replay. A load-bearing unfixable finding blocks release;
do not weaken the theorem or silently rewrite the immutable package.

```sh
env TMPDIR=<S> python3 <P>/package.py --check
/usr/bin/git -C <S> worktree add --detach <W> a8568ddb9df27867bfd40d8c5a3fb590cfbab6d8
python3 -c 'import subprocess,sys; subprocess.run(["bash",sys.argv[1]+"/.claude/skills/new-slice/prepare-worktree.sh","--base","a8568ddb9df27867bfd40d8c5a3fb590cfbab6d8"],cwd=sys.argv[1],check=True)' <W>
/usr/bin/git -C <W> rev-parse HEAD
bash <L>/scripts/lake-build.sh <L> LeanNCD
```

The Python setup wrapper supplies the script's required working directory without
a compound shell command. Detached HEAD intentionally skips main fast-forwarding;
verify HEAD remains the pinned package base. Require the preparation script's warm
Mathlib check and refresh project-owned oleans before further validation.
Do not advance this replay to concurrent main before frozen-source verification.

For EACH task, substitute its patch filename and then its completed number:

```sh
/usr/bin/git -C <W> apply --check <P>/<task-patch>
/usr/bin/git -C <W> apply <P>/<task-patch>
python3 -c 'import hashlib,json,pathlib,sys; p=pathlib.Path(sys.argv[1]); w=pathlib.Path(sys.argv[2]); ts=json.loads(p.read_text())["tasks"][:int(sys.argv[3])]; h=lambda q:hashlib.sha256(q.read_bytes()).hexdigest(); assert all(h(p.parent/t["patch"])==t["sha256"] for t in ts), "patch hash mismatch"; assert all(h(w/f["path"])==f["sha256"] for t in ts for f in t["files"]), "replayed source mismatch"; print("cumulative patch/source hashes PASS")' <P>/package.json <W> <N>
```

Run each task's targeted build after byte verification. Serialize applications
01→02→03→04→05→06 regardless of conceptual independence.
Load-bearing proof dependencies are ranks + state/fuel/transport helpers → actual
graph induction → reference projection → acceptance; documentation describes all
of these. Application order is not itself a claim of proof dependence between
every neighboring task, nor a license to run incomplete registered libraries.
Task01 intentionally registers later modules; build only available named targets
until task05, never the full experiment earlier.

Checkpoint after each task: patch ID, cumulative byte verification, targeted build
result, adjudicated findings and remaining gates. Fail loud on any mismatch.

## 4. Six tasks and review boundaries

All Lean paths below are relative to `leanncd/experiments/indexed_execution/`.
Files lists are the exact package partition, not suggested locations.
Counts distinguish executable rows, proof instances and mutation cycles.

| Task | Files | Fixture / cycle count | Risk and bounded execution |
| --- | ---: | --- | --- |
| 01 ranks | 2 | 0 new executable rows / 0 cycles | Full occurrence footprint, input bound, empty addresses; one patch + named build |
| 02 helpers | 3 | 0 new executable rows / 0 cycles | Fuel equality, first-enabled selection, private/empty cut; one patch + three named targets |
| 03 graph runs | 1 | 0 new executable rows / 0 cycles | Actual induction and residual budget, not assumed agreement; one patch + named build |
| 04 reference | 2 | 0 new executable rows / 0 cycles | Shared normalized cut and full relation; one patch + two named targets |
| 05 acceptance | 9 | 9 executable rows + 12 phase proof definitions + 2 rank-test families / 25 cycles | Largest validation bundle; frozen reviewed patch and deterministic runners, no fresh 60-turn implementer |
| 06 docs/record | 4 | 0 fixtures / 0 cycles | Status/discoverability only; byte verification, no doctests |

### Task01 — constructed ranks and experiment registration

Files: `leanncd/lakefile.toml`; `IndexedComponentCompositionRanks.lean`.
Symbols in `IndexedComponentComposition`:
`rankOffset`, `rank_lt_offset`, `rankOffset_eq_one_of_isEmpty`,
`compositeRank`, `compositeRank_decreases`, `compositeRankCertificate`
@ `IndexedComponentCompositionRanks.lean`; experiment registration @
`leanncd/lakefile.toml`.

Accept only the actual composed program's certificate. Offset is the sum of ranks
of EVERY upstream address plus one, including input addresses; empty sum gives one.
Upstream ranks stay fixed; downstream defined ranks gain that offset.
Decrease covers actual guard-admitted occurrences' full footprints: upstream,
downstream-internal and supplied-boundary reads, through certified adapters.
Do not infer axis equality from names/extents or replace the certificate by a premise.

```sh
bash <L>/scripts/lake-build.sh <L> IndexedComponentCompositionRanks
```

### Task02 — fuel, transition transport and boundary-state helpers

Files: `IndexedComponentExecutionFuel.lean`,
`IndexedComponentExecutionTransport.lean`, `IndexedComponentExecutionPhase.lean`.
Symbols in `IndexedComponentExecution`:
`stepFuel_add_of_not_exhausted`, `stepFuel_eq_of_enough`, `checked_eq_stepFuel`
@ `IndexedComponentExecutionFuel.lean`;
`Projection`, `producedValue_projection`, `selected_projection`,
`projection_produce`, `projection_collect` @ `IndexedComponentExecutionTransport.lean`;
`UpstreamState`, `DownstreamState`, `graph_steps_standalone`, `initial_upstream`,
`downstream_at_cut`, `boundary_input_presence`, `boundary_input_exact`
@ `IndexedComponentExecutionPhase.lean`.

Fuel stability preserves the entire actual run, including snapshots.
Transport uses injective capability/tag embeddings and first lookup in an ordered
prefix-plus-local ledger. Selection uses actual first-enabled `List.find?`,
not mere concatenation of step lists. At the cut retain all upstream availability
and private ledger; downstream starts with transported input and fresh defined
values/produced capabilities. Empty tensor presence comes from interface metadata.
No new evaluator, runtime phase gate, transition or synthetic boundary event.

```sh
bash <L>/scripts/lake-build.sh <L> IndexedComponentExecutionFuel IndexedComponentExecutionTransport IndexedComponentExecutionPhase
```

### Task03 — actual default graph-run induction

File: `IndexedComponentExecutionRuns.lean`.
`PrefixRun`, `RunProjection`, `compose_default_phases`
@ `IndexedComponentExecutionRuns.lean`, namespace `IndexedComponentExecution`.

Use the constructed schedule, actual selection transport and ranked progress.
Incomplete upstream work cannot be skipped in favor of downstream actions.
Failure is at transported `upstreamId tag`, with only upstream events/states,
even when visible outputs preceded private failure.
Success derives the complete upstream store, actual shared cut and suffix
`RunProjection`, covering downstream success or transported strict failure.
All upstream availability and its ordered completed private ledger persist.
Exclude blocking, mismatch and exhaustion from existing accepted/ranked results,
not extra assumptions.

Budget obligations: `remaining + prefix.length = composite.graph.steps.length + 1`,
`prefix.length ≤ nA`, `nB + 1 ≤ remaining`.
The decreasing remaining-action measure proves the residual bound.
Separate fuel-stability helpers preserve whole actual runs when fuel increases.
The cut is one existing snapshot, not an inserted state.

```sh
bash <L>/scripts/lake-build.sh <L> IndexedComponentExecutionRuns
```

### Task04 — normalized reference projections and public proof entry

Files: `IndexedComponentExecutionReference.lean`, `IndexedRankedExecutionSemantics.lean`.
`ReferenceStateProjection`, `reference_default_phases`
@ `IndexedComponentExecutionReference.lean`, namespace `IndexedComponentExecution`;
entry imports @ `IndexedRankedExecutionSemantics.lean`.
Boundary equality: `boundaryInput_outputProjection` in the packaged proof layer.

Derive reference projections from task03 and existing `ExecutionCorrespondence`.
`ReferenceStateProjection` retains both graph witnesses, their phase relation,
both `LedgerInvariant`s and full `Relation`s: available/published values, produced
ledgers, pending occurrences and accumulators, not merely final outputs.
Normalized composite snapshots are `pre ++ cutRef :: suffix`;
upstream projects to `pre ++ [cutRef]`, downstream to `cutRef :: suffix`.
Undefinedness adds its event but no failed-state snapshot.
Use matched event maps and explicit renamings, not equality of dependent raw events.
Expose completed-output `boundaryFromOutput` equality; preserve task03 budget bounds.

```sh
bash <L>/scripts/lake-build.sh <L> IndexedComponentExecutionReference IndexedRankedExecutionSemantics
```

### Task05 — acceptance, axiom audits and all mutation controls

Files: `IndexedComponentRankedExecutionFixtures.lean`,
`IndexedComponentRankedExecutionRankTest.lean`, `IndexedComponentRankedExecutionTest.lean`,
`IndexedComponentRankedExecutionAudit.lean`;
under `papers/semantics/`: `categorical_ranked_execution_mutations.json`,
`categorical_ranked_execution_mutations_post.json`,
`categorical_ranked_execution_fixture_mutation_results.md`,
`categorical_ranked_execution_snapshot_mutation_results.md`,
`categorical_ranked_execution_inherited_mutation_results.md`.

Symbols: `consumerRank`, `privateRank`, `emptyRank`, `empty_rank_offset`,
`private_not_blocked`, `hidden_no_rank` @ `IndexedComponentRankedExecutionFixtures.lean`;
`Axis.certificate`, `Axis.offset_includes_unused_input`,
`Collision.certificate`, `Collision.private_full_footprint_decreases`
@ `IndexedComponentRankedExecutionRankTest.lean`;
phase-instance namespace `IndexedComponentRankedExecutionTest` @ its matching file;
namespace audits @ `IndexedComponentRankedExecutionAudit.lean`.

Replay the frozen acceptance patch, not fixture-by-fixture implementation.
Nine executable rows, six donor families instantiated as graph AND reference
phase proof-valued definitions (12), and axis/collision rank families are separate
counts. The cyclic counterexample is not a ranked theorem instance.
All new namespaces/theorems/instances were audited with only
`propext`, `Classical.choice`, `Quot.sound`.

#### Discriminating donor/delta and observed acceptance inventory

Donor modules below already exist in the same experiment directory.

| Executable row / family | Exact donor and delta | Observed distinction |
| --- | --- | --- |
| `ranked-private-success` | Clone port-fixture `consumerComponent 4` twice; put one upstream, explicitly wire downstream `Pre` to upstream `Out`, external `Pre = 3` | Upstream `Out = 9`, private `Audit = 7/2`; downstream `Out = 81`, private `Audit = 19/2`; 8 events / 9 snapshots; cut index 4, zero-based; every available vector and ordered ledger pinned |
| `ranked-private-upstream-failure` | Same boundary/input; upstream `consumerComponent 0`, total neighbour `consumerComponent 4` | Visible `Out = 9` before private tag 60 fails; no downstream production/publication; 3 events / 3 normalized snapshots |
| `ranked-private-downstream-failure` | Clone private success; change downstream `other` from 4 to 0 | Tag 61 fails after upstream private completion; upstream state retained; 7 events / 7 snapshots |
| `ranked-private-order-control` | Clone upstream failure; graph-only reorder of actual collector rows puts upstream Audit after both downstream rows | Graph still closes; downstream 81 and 19/2 precede upstream private failure; no supplied composite source match |
| `ranked-reference-snapshots-and-budgets` | Reuse the three private runs in actual reference execution | Success 8/9, upstream failure 3/3, downstream failure 7/7; composite budget 9 versus leaf budgets 5 and 5 |
| `ranked-complete-contribution-boundary` | Port-fixture `producerComponent`, `consumerComponent 4` and failing neighbour `consumerComponent 0`; retain both writers and publication | Contributions +1 then -1; boundary unavailable until separate publication of zero; success 7 events, strict failure 6 |
| `ranked-zero-writer-publication` | Port-fixture `zeroProducerComponent`, `consumerComponent 4`, `zeroBoundary` | Publish zero without writer, then downstream; 5 events / 6 snapshots; no wire event |
| `ranked-empty-metadata-and-validation` | Port-fixture `emptyProducerComponent`, `emptyConsumerComponent`, `emptyValidatedInput`, `emptyBoundary`; retain empty-present/missing distinction | Checked complete: 0 events / 1 snapshot / budget 1; boundary presence `some`; simultaneous missing external/unexpected internal binding rejects UID 20 before lower UID 0; valid neighbour completes |
| `ranked-unranked-counterexample` | Cycle-fixture `hiddenUpstream`, `totalDownstream`, `hiddenBoundary`; retain private self-cycle | Downstream produces/publishes 1 before blocking; 4 events / 5 snapshots; `hidden_no_rank` excludes certificate, not models |
| Axis rank/projection family | Axis-fixture `axisProducer`, `axisConsumer`, `axisBoundary`; use existing transport-test `p = (0,2,())`, `q = (1,0,())`, `swapDomain`; local producer rank `i + 3*j`, consumer read ranks 0/1, defined 2, unread input 100 | Swapped boundary ranks 2 versus 3; nonpalindromic repeated footprint `[2,3,2,3]`; offset strictly exceeds unread input rank 100 |
| Guard/collision rank/projection family | Collision-fixture `collisionProducer`, `collisionConsumer`, `collisionBoundary`; retain guards and disjoint embeddings, add local certificates | Admitted valuations 0/2, rejected 1; upstream literal footprints genuinely empty; downstream output AND private audit have singleton boundary-read footprint, read rank 0 |

Donor files: `IndexedComponentCompositionPortFixtures.lean`,
`IndexedComponentCompositionAxisFixtures.lean`,
`IndexedComponentTransportTest.lean`,
`IndexedComponentCompositionCollisionFixtures.lean`,
`IndexedComponentModelCycleFixtures.lean`.
Graph/reference phase families are private, collection, zero, empty, axis, collision.

#### Required / forbidden / silently-ignored invariant audit

This audits the goal's existing surfaces, not a newly invented defect family.
Inherited sibling controls remain necessary because an additive proof diff alone
cannot show unchanged constructor/runner behavior.

| Surface and sibling identifiers | Required | Forbidden | Silently ignored / scope treatment |
| --- | --- | --- | --- |
| Private work: `UpstreamState`, `DownstreamState`, `selected_projection`, actual `enabled`/`complete` | Full writer/collector completion and private ledger retention | Output-only completion, premature downstream action | Private nonoutputs are NOT ignored; graph-only reorder and unranked cycle deliberately lack matched/ranked premises |
| Empty/zero: `boundary_input_presence`, `boundaryInput`, `boundaryFromOutput`, full-tensor validation | Metadata presence, zero-writer publication, existing enumeration order | Address-only presence, dropped collectors, UID-sorted validation | Empty address quantification is vacuous; tensor presence and collector obligation are not |
| Strict failure: `evalReady_projection`, `compose_default_phases`, `referenceSnapshots` | Ready undefined body fails at renamed occurrence; one event/no new failed snapshot | Default value, failure bypass, downstream work after upstream failure | Rank does NOT silently imply primitive totality; arbitrary debug fuel is excluded |
| Guards: actual `dependencies`, `upstream_footprint`, `downstream_footprint` | Every admitted occurrence and complete footprint | Erased admitted guard or output-only dependency proof | Rejected valuations are intentionally outside occurrences; admitted literal bodies may have empty footprints |
| Coordinates/order: `downstream_input_address`, `producedValue_projection`, `mapLedger`, `mapEvent` | Supplied certified adapter, injective namespaces, duplicate ordered reads/ledger | Name/extent matching, flattened/reversed transport, capability/tag collision | Unread inputs still enter rank bound; only lookup-irrelevant disjoint prefix is abstracted |
| Reference cut: `ReferenceStateProjection`, `Relation`, `LedgerInvariant` | Shared normalized cut, pending occurrences/accumulators, whole private store | Final-output-only agreement, duplicate cut, synthetic boundary event | General trace algebra is deferred, not assumed; existing failed normalization remains explicit |

#### Mutation classification and exact replay

All 25 final controls already ran UNFILTERED with observed diagnostic requirements,
restored-green builds and byte-identical restoration. Preserve these distinctions:

- Seven post-code F1–F7 controls are fixture-source/binding and graph-only controls:
  external 3→2; coherent upstream/downstream total-neighbour substitution;
  remove discriminating graph reorder; reverse two-invalid-binding enumeration;
  coherent contribution omission; drop mandatory zero collector.
  Their observed diagnostics are respectively
  `indexed-reference ranked-private-success: expected`,
  `indexed-reference ranked-private-upstream-failure: expected`,
  `indexed-reference ranked-private-downstream-failure: expected`,
  `indexed-reference ranked-private-order-control: expected`,
  `indexed-reference ranked-empty-metadata-and-validation: expected`,
  `indexed-reference ranked-complete-contribution-boundary: expected`,
  `indexed-reference ranked-zero-writer-publication: expected`.
  Initial type-inconsistent F2/F3 attempts are NOT credited; coherent replacements
  reached the intended runtime strict-failure assertions.
- Two S1/S2 controls break live snapshot proof consumers. S1 additionally breaks
  independent `strict-failure-parity` and `total-neighbour-parity` assertions;
  S2 is live-proof-only. Manifest diagnostics include the observed proof-file
  `Application type mismatch`; do not relabel these as two runtime production kills.
- Sixteen inherited controls retain their original labels/classifications:
  L1–L7 live proofs (tensor/capability/tag separation, ordered writer reads,
  zero collectors, guards, output metadata, enumeration); C1–C4 graph-only
  controls; F1–F3 fixture source/binding; T1–T2 typed legal-neighbour controls.
  The checked manifest contains exact observed diagnostics; do not replace them
  with generic failure or count setup refusal as the intended observation.

Run these commands sequentially, with NO task/prefix filters and no parallel
mutations in one worktree. `--cd` is the runner's option, not shell `cd`.
Do not rewrite packaged result tables with replay `--out`; they are labelled
prototype evidence. Controller replay receipts belong in later record addenda.

```sh
bash <L>/scripts/lake-build.sh <L> IndexedComponentRankedExecutionAudit
bash <L>/scripts/mutation-manifest.sh --cd <W> --check <L> <W>/papers/semantics/categorical_ranked_execution_mutations_post.json
bash <L>/scripts/mutation-manifest.sh --cd <W> --check <L> <W>/papers/semantics/categorical_ranked_execution_mutations.json
bash <L>/scripts/mutation-manifest.sh --cd <W> --check <L> <W>/papers/semantics/component_composition_mutations_post.json
bash <L>/scripts/mutation-manifest.sh --cd <W> <L> <W>/papers/semantics/categorical_ranked_execution_mutations_post.json
bash <L>/scripts/mutation-manifest.sh --cd <W> <L> <W>/papers/semantics/categorical_ranked_execution_mutations.json
bash <L>/scripts/mutation-manifest.sh --cd <W> <L> <W>/papers/semantics/component_composition_mutations_post.json
rg -n --glob 'IndexedComponentCompositionRanks.lean' --glob 'IndexedComponentExecution*.lean' --glob 'IndexedComponentRankedExecution*.lean' --glob 'IndexedRankedExecutionSemantics.lean' '\b(sorry|admit|axiom|unsafe|native_decide)\b' <L>/experiments/indexed_execution
bash <L>/scripts/lake-build.sh <L> LeanNCD Tests IndexedExecutionExperiment
```

Inspect any source-probe hits; expected no forbidden proof shortcuts, with
`#audit_axioms`/standard-axiom audit output interpreted separately. A no-match
`rg` exit 1 is not a build failure. Repeat section 3 cumulative hash verification
with `<N> = 5` after cycles. This is about ten controller commands plus automatic
cycles, not 25 model dispatches. Do not silently skip a failed cycle or use only
`--check` as validation. Build/audit success cannot substitute for mutation replay.

### Task06 — current status, discoverability and frozen record

Files: `leanncd/AGENTS.md`;
`papers/semantics/categorical_tensor_logic_semantics.md`;
`papers/semantics/categorical_tensor_logic_component_interfaces.md`;
`papers/semantics/categorical_ranked_execution_record.md`.
Anchors: nondefault entry `IndexedRankedExecutionSemantics`, constructed certificate,
actual `compose_default_phases`, normalized `reference_default_phases`,
completed denotational versus deferred process interpretation.

Apply the exact documentation patch and verify cumulative hashes with `<N> = 6`.
No doctests or fresh documentation worker. Status prose must distinguish existing
proof completion from pending replay/integration gates and must not claim a process
category. No accepted-count capability change is claimed; do not invent a numeric
registry migration. Use the focused sweep to check current-status boundaries:

```sh
rg -n 'ranked|phase|trace|process|IndexedRankedExecutionSemantics' <W>/leanncd/AGENTS.md <W>/papers/semantics/categorical_tensor_logic_semantics.md <W>/papers/semantics/categorical_tensor_logic_component_interfaces.md <W>/papers/semantics/categorical_ranked_execution_record.md
env TMPDIR=<W> python3 <P>/package.py --check
/usr/bin/git -C <W> diff --check
```

Only after exact task06 comparison may controller record addenda be appended.
Do not regenerate package metadata to make an unreviewed change appear verified.

## 5. Release, preservation and accounting

Controller owns independent replay receipts, review adjudication, final whole-branch
review and final full `LeanNCD Tests IndexedExecutionExperiment` build through the
wrapper. Prior prototype green is evidence, not proof that clean replay happened.
After source-byte verification, any integration adaptation requires explicit review
and its own green validation; do not describe adapted code as immutable replay.
Stage only explicit task-owned paths; never `.claude/settings.json`.

Integration complication to RECORD, not solve here: local main concurrently advanced
to `c48293db` with five unrelated JAX MQA files, reported nonoverlapping task source.
The primary checkout has PREEXISTING dirty
`papers/semantics/README.md` and `papers/semantics/categorical_tensor_logic_semantics.md`.
Preserve both and all unrelated worktrees. The user explicitly authorized a
temporary stash of ONLY these two files after review/replay pass, followed by
local merge and restoration of their edits. Do not stash other paths, reset,
overwrite or discard unrelated changes. Verify restoration and surface any
conflict rather than silently losing either set of edits. Do not substitute
a merge/PR/push menu.

When all green/review gates pass and preservation is resolved, the controller
performs the authorized local-main integration, deletes only this task's own
branch/worktree and does not push. This authoring task performs no commit,
worktree creation, mutation replay, build or integration.

Budget: keep each dispatch below approximately 250k context and 60 turns; task05 is
controller automation, not an over-cap fresh implementer. No heavyweight docs
dispatch or new AGENTS hook-consuming implementation dispatch is needed.
The helper author reached 55 turns; its registration follow-up conservatively
exceeded the bound and was disclosed. Other proof dispatches report no known breach.
The fresh plan author reported 37 invocations including batched calls/wrappers
against its 35-invocation aim (13 tool-call rounds); this aim overrun is disclosed.
`token-report.py` for session `a285d1df-05fb-4a49-9f7e-23b13dcfa082` reported no
transcript: cumulative tokens/peak remain unmeasured. Do not claim verified
compliance with the roughly 50M authoring target or 175M slice cap.

Close-out record must identify certificate construction and exact premises,
graph/reference phase and state/event projections, strict/private/empty behavior,
boundary equality and default budget/validation limits; distinguish prototype
controls from actual replay receipts, list adjudicated findings and preservation
outcome, and retain the excluded trace/process/backend boundary. No file-line
citations, fabricated executed gates or silently parked load-bearing failures.
