# Transport-aware operational associativity — implementation plan

**Process: Full.** New reusable history algebra and actual-run observation
soundness require the Full gates. This is one slice, not a process-category plan.
Authoring (b) uses only the frozen prototype package and its receipts.

## 1. Execution contract

Execution worktree:
`/Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution`.
Execution branch: `agents/categorical-operational-associativity-execution`.
Frozen prototype/replay base: `8268da1f5761b839f1b16a03a6b3a799ef4a583f`.
Actual prepared latest-local-main execution base:
`0ea62a923626f1dcdee1eb28f24e357f3996daf2`.
The controller prepares this separate isolated worktree; never execute patches
in the authoring/handoff worktree or discard its prototype.
The only intervening change is the unrelated 153-line
`papers/semantics/jax_gqa_session_brief.md`; none of the 17 frozen files changed.
Preserve that concurrent document. Authoring (b) also private-index replayed all
five patches on `0ea62a92`: every forward `--check` passed, all 17 final hashes
matched, and the concurrent document's Git blob remained unchanged.

Every implementation/review brief opens with this preamble:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Paths in Files/symbol lists are repository-relative to that execution worktree.
Use `rg -n` to locate the listed identifiers, then read approximately 40–60
lines around each; no whole-source-module trace or re-prototyping is needed.
Apply the mechanically generated patches unchanged. There are no inline Lean
blocks to transcribe. Stop on a load-bearing mismatch rather than substituting
weaker observations, extra theorem premises, new code or a new interpreter.

Each task has at most three work items. Target at most 50 implementer rounds,
hard stop before approximately 60 rounds or 250k peak context. If unexpected
fixes need a split, retain the production checkpoint and use the repository's
split-handoff template for fixtures/controls; do not extend one dispatch silently.
Authoring targets 50M cumulative input tokens; execution caps at 175M.
Keep detailed receipts and budget disclosures in the record, not this plan.

## 2. Frozen evidence and exact scope

The package root is
`papers/semantics/categorical_operational_associativity_artifacts/`.
`package.py` defines four ordered source groups and a fifth documentation patch:

1. `history.patch`
2. `transport.patch`
3. `composition.patch`
4. `acceptance.patch`
5. `documentation.patch`

`package.json` records their hashes, the frozen base and all 17 final file
hashes. Its private-index replay passed in order. All 12 final source modules
match the successful `snippets.json` wrappers. The preserved
`prototype_full_build.log` ends in successful `LeanNCD Tests
IndexedExecutionExperiment` construction. These are prototype receipts, not
clean-execution or integration receipts.

The record reconciles the historical evidence: binary composition, common-leaf
structural associativity, concrete metadata laws, actual reference outcomes and
registered controller mutation cycles are CLOSED, despite earlier intermediate
reports listing them as remaining. Do not reopen those investigations.

**Count correction requiring explicit controller acknowledgement:** the brief
and earlier record say 19 History + 4 metadata + 5 composition kernel examples
= 28. The frozen `history.patch` actually contains **26 History examples**
(18 generic/transport, 4 concrete-state, 4 empty-metadata), plus 4 metadata-law
examples; composition contains 5. Thus the shipped total is **35**, not 28.
Preserve all of them. This is an evidence/count inconsistency, not permission
to remove seven tests or change the compiled package. If exactly 19/28 is an
acceptance condition rather than an estimate, stop for controller adjudication.

### Global semantic constraints

- Finite decidable `Declarations Unit`, exact-rational matched sealed components.
  Supply validated A input, original boundaries `ab` and `bc`, and three local
  rank certificates. Both composite ranks are constructed, not premises.
- `CompleteObservation.Agrees` retains ordered whole input/output ports,
  input roles, full Option-valued validated external input (including empty
  tensor presence), original boundary/domain adapters, every ordered event,
  every entire availability function and ordered produced ledger, and terminal
  success or the transported failing tag/state.
- Explicit typed tensor/domain/address and admitted-occurrence transports
  preserve leaf ownership. The same coherent identity recoding transports tags
  and capabilities: A `4*n → 2*n`, B `4*n+2 → 4*n+1`, C `2*n+1 → 4*n+3`.
  Axis names, extents or cardinality are never identity criteria.
- Successful compatible histories obtain suffix input from the completed
  whole boundary through `boundaryInput`/`boundaryFromOutput`. They share one
  full cut snapshot, retain completed private state/ledger in every suffix
  snapshot, and insert no wire event. Failure absorbs without constructing an
  unavailable suffix input/history. Undefinedness adds no second failed state.
- Actual default graph entry points are the two existing nested constructors'
  `runChecked` calls. Actual reference counterparts are `Program.Executor.run`
  and `referenceSnapshots`, retaining full `Relation`, pending occurrences,
  accumulators and graph ledger invariants.
- All four leaf outcomes, both original boundary inputs and ordered reached
  cuts are proved. Empty phases may share a cut index. Both actual defaults are
  `nA+nB+nC+1`, not three standalone defaults added together.
- No completion, model existence/uniqueness, execution agreement, chosen-action
  agreement or final-store agreement premise. No output-only, reordering,
  private-erasure or stuttering quotient.
- Invalid raw input retains each constructor's original validation order.
  Arbitrary debug fuels, unranked execution, units/full process category,
  broader source interpretation and backend/numerical refinement are excluded.
  A core copy is not an event-free identity.
- No changes to the core language, registry, scheduler, runner, completed
  witness/source/denotational proofs, or unrelated worktrees/primary edits.
  New modules remain nondefault under `IndexedExecutionExperiment`, discoverable
  through `IndexedOperationalSemantics` and the patched `leanncd/AGENTS.md`.

### Risk and verification accounting

Counts describe the actual frozen package, not independent runner-defect kills.

| Task | Work items | Kernel fixtures / full proof instances | Runtime coverage | Assigned mutation cycles |
|---|---:|---|---|---:|
| 1 History and concrete laws | 2 | 26 History + 4 metadata = 30; brief's 19 + 4 is stale | none | 7 live-proof (6 history, 1 metadata-neighbor) |
| 2 Actual transports/runs | 2 | generic proofs; no additional fixture examples | generic graph/reference proofs | 3 live-proof |
| 3 Structural composition/associativity/phases | 3 | 5 composition examples | generic four-branch/cut proofs | 11 live-proof (4 binary, 3 structural, 4 phase) |
| 4 Acceptance/audit | 3 | 15 proof-valued declarations retaining full propositions | 10 check groups over 9 matched triples + 1 graph-only control | 11 (8 observation corruptions, 2 donor/input substitutions, 1 graph control) |
| 5 Documentation/release handoff | 1 | no new fixtures | no new observations | 0 new; controller reruns all 32 |
| Total | | **35 kernel examples**; 15 separate full-proof declarations | 10 groups, not 10 matched triples | **32 = 11 + 21** |

### Observation-family audit (review beyond a single diff)

| Case/class and sibling APIs | Required | Forbidden / intentionally outside judgment |
|---|---|---|
| `mapState`, `upstreamState`, `downstreamState`, `state_A/B/C` | all addresses, private availability, ordered ledger prefixes | output-only state reconstruction |
| `mapEvent`, `event_A/B/C`, `RunRelated`, `StepRelated` | every production/publication/undefinedness payload and ordered selection | sorting, merging contributions, arbitrary identity permutation |
| `MetadataTransport.Agrees`, `nested_metadata` | whole ports/roles, Option presence, actual domain and boundary adapters | inferring empty input presence from addresses |
| `BinaryHistory`, `SharedSplice`, `TriplePhases` | failure absorption, one shared state, both original boundary equations | suffix/input requirement after predecessor failure; strict cut inequality |
| `nested_reference_runs`, `reference_cuts`, reference outcomes | full published/pending/accumulator relation and terminal identity | graph availability as a replacement for reference state |
| Raw-invalid/debug-fuel/units | explicitly excluded | silently treating these as validated/default/category laws |

No silently ignored field is allowed in the claimed profile. A field absent
after an unreached failure is deliberately not constructed, not discarded from
an existing observation. Review these sibling APIs together without broadening
into unrelated source-module audits.

## 3. Controller preflight — before Task 1

1. Confirm isolated execution branch/base and inventory existing changes.
   The controller must make this plan, record and frozen artifact package
   available at their same relative paths. Those authoring inputs are not
   unexplained production edits; snapshot their hashes and status separately.
   Abort if any of the 17 patch-owned files already differs from its frozen-base
   content; do not reject the acknowledged unrelated latest-main document.
   Do not copy the prototype source over the clean execution tree.

```bash
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution rev-parse HEAD
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution branch --show-current
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution status --short
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution worktree list --porcelain
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution diff --name-only 8268da1f5761b839f1b16a03a6b3a799ef4a583f 0ea62a923626f1dcdee1eb28f24e357f3996daf2
```

2. Check the package hashes against `package.json`; all five patch files and
   the 12 snippet receipts must exist. The controller's worktree preparation
   has verified warm Mathlib (8,101 oleans / 8,094 modules, 454 project oleans)
   and will refresh project-owned oleans before Task 1.
   No package installation or cold rebuild is warranted by the frozen evidence.
   Read the governing Lean instructions; there is no experiment child
   `AGENTS.md`. Frozen governing Patterns/Global Pitfalls sections total 2,976
   characters, within the approximately 3k injected-section budget; no trim is
   needed or authorized. Do not edit instructions speculatively.

```bash
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd LeanNCD
```

3. Static conflict scan: Tasks 1–4 incrementally edit the same explicit
   `IndexedExecutionExperiment` module list in `leanncd/lakefile.toml`.
   Execute sequentially; do not register all future modules at Task 1.
   Task 5 alone edits the two documentation files and two manifests.
   Ensure the frozen dependency imports need no source outside these tasks.
   Ordered private-index replays prove patch application from both the frozen
   base and acknowledged latest-main base; each task still runs its own forward
   `--check` before applying. Do not reset execution HEAD to the frozen base.
   Manifests target files added by later tasks: unfiltered validation belongs
   after Task 5, not against absent preflight sources.

4. Record the count correction above before dispatch. Agree that the frozen
   35 examples, all 10 executable groups, all 15 full-proof declarations and
   all 32 controls remain required. No package edit is part of this plan.

## 4. Task 1 — generic history and concrete observation laws

Prerequisite: preflight. Apply `history.patch`.

**Files (exact patch ownership):**
- `leanncd/lakefile.toml`
- `leanncd/experiments/indexed_execution/IndexedOperationalHistory.lean`
- `leanncd/experiments/indexed_execution/IndexedOperationalObservationLaws.lean`

**Window-read symbols:**
- `History`, `History.splice`, `History.success_cut`, `History.failure_absorbs`,
  `History.splice_assoc`, `Transport.apply_splice`, `GraphHistory.Admissible`,
  `GraphHistory.toRun_injective`, `GraphHistory.ranked_default_exists`,
  `GraphMetadata`, `MetadataTransport.Agrees`, `CompleteObservation.Agrees`,
  `ReferenceObservation.full_relations`, `Fixtures`
  @ `leanncd/experiments/indexed_execution/IndexedOperationalHistory.lean`.
- `Domain.symm`, `MetadataTransport.refl`, `MetadataTransport.symm`,
  `MetadataTransport.trans`, `MetadataTransport.agrees_congr`,
  `CompleteObservation.agrees_refl`, `CompleteObservation.agrees_symm`,
  `CompleteObservation.agrees_trans`, `CompleteObservation.agrees_congr`,
  `MetadataLawFixtures.absentEmptyMetadata`
  @ `leanncd/experiments/indexed_execution/IndexedOperationalObservationLaws.lean`.

**Two work items:** install generic history/admissibility/transport/splice
algebra; install laws for the exact concrete metadata/complete-observation
relations, not merely the generic `Observed` relation.

**Fixture donors/deltas:** `Fixtures.first`, `second`, `third` form the
three-phase history; clone `first` to an event-free initial phase and retain
one cut. `privateFailure` adds visible/private work followed by strict failure;
`swapping` changes explicit state/event/failure identities. `ledgerLeft` versus
`ledgerRight` reverses only ordered rows; `privateAvailable` changes availability.
`emptyMetadata` uses the existing empty-port donor. `absentEmptyMetadata`
removes input ports, roles and Option presence consistently, leaving outputs.
All address observations still coincide; full ports and Option presence must
separately reject agreement. Retain all 30 kernel examples.

```bash
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution apply --check /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/history.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution apply /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/history.patch
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd IndexedOperationalHistory IndexedOperationalObservationLaws
```

**Review checkpoint:** inspect only this task diff and listed sibling surfaces.
Confirm failure has no extra terminal snapshot, exact `toRun` information,
full-state transport, boundary sharing and concrete metadata laws. The six
history and one metadata-neighbor live-proof controls are required at release;
their prior intended diagnostics/restoration receipts are frozen, not new runtime
runner kills. Stage only these three explicit Files paths and commit after the
named build and review pass. Record findings/resolution before Task 2.

## 5. Task 2 — coherent actual transports and graph/reference runs

Prerequisite: Task 1. Apply `transport.patch`.

**Files:**
- `leanncd/lakefile.toml`
- `leanncd/experiments/indexed_execution/IndexedOperationalReassociation.lean`
- `leanncd/experiments/indexed_execution/IndexedOperationalRuns.lean`

**Window-read symbols:**
- `tensorEquiv`, `sourceOccurrenceEquiv`, `addressEquiv`, `embedding_address`,
  `address_A`, `address_B`, `address_C`, `initial_available`, `input_roles`,
  `output_roles`, `identityEquiv`, `identity_A`, `identity_B`, `identity_C`,
  `leftRank`, `rightRank`, `default_budgets`
  @ `leanncd/experiments/indexed_execution/IndexedOperationalReassociation.lean`.
- `StepRelated`, `steps_selected`, `stepFuel_transport`, `stateRelated_full`,
  `nested_steps`, `nested_default_runs`, `ranked_nested_default_runs`,
  `nested_reference_runs`, `ranked_nested_reference_outcomes`
  @ `leanncd/experiments/indexed_execution/IndexedOperationalRuns.lean`.

**Two work items:** install actual leaf-owned coordinate/occurrence/identity
squares and constructed ranks/budgets; install independently derived ordered
selection/evaluation/run transport plus actual full reference observations.
No new finite donor fixtures here: retain the generic statements, later
instantiated by Task 4's existing ranked donors.

```bash
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution apply --check /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/transport.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution apply /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/transport.patch
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd IndexedOperationalReassociation IndexedOperationalRuns
```

**Review checkpoint:** no assumed action agreement; actual input lifts and
default `runChecked` entry points; full address-space availability, ordered
events/ledgers and both actual `Executor.run` results, normalized snapshots and
reference terminal outcomes. The three release controls reverse events, reverse
states and substitute the wrong B identity proof; these are live-proof
sensitivity, not runtime runner-defect kills. Commit only the three Files after
build/review; record the checkpoint.

## 6. Task 3 — binary soundness, structural reassociation, actual phases

Prerequisite: Task 2. Apply `composition.patch`.

**Files:**
- `leanncd/lakefile.toml`
- `leanncd/experiments/indexed_execution/IndexedOperationalHistoryComposition.lean`
- `leanncd/experiments/indexed_execution/IndexedOperationalHistoryAssociativity.lean`
- `leanncd/experiments/indexed_execution/IndexedOperationalRunsPhases.lean`
- `leanncd/experiments/indexed_execution/IndexedOperationalAssociativity.lean`
- `leanncd/experiments/indexed_execution/IndexedOperationalSemantics.lean`

**Window-read symbols:**
- `SharedSplice.Splice`, `SharedSplice.associative_eq`, `downstreamState`,
  `BinaryHistory`, `BinaryHistory.sound`, `BinaryHistory.phase_cut`,
  `compose_history`, `boundaryInput_from_whole_output`, `left_nested_history`
  @ `leanncd/experiments/indexed_execution/IndexedOperationalHistoryComposition.lean`.
- `state_A`, `state_B`, `state_C`, `event_A`, `event_B`, `event_C`,
  `lift_A`, `lift_B`, `lift_C`, `right_input`, `boundary_C`, `shared_right`,
  `binary_associativity`, `right_nested_tree`, `actual_nested_histories`
  @ `leanncd/experiments/indexed_execution/IndexedOperationalHistoryAssociativity.lean`.
- `TriplePhases`, `TwoReached`, `triple_phases`, `original_bc_input`,
  `two_reached_right`, `two_reached_empty_B`, `reference_cuts`
  @ `leanncd/experiments/indexed_execution/IndexedOperationalRunsPhases.lean`.
- `nested_metadata`, `nested_observations`
  @ `leanncd/experiments/indexed_execution/IndexedOperationalAssociativity.lean`.
- Import list @ `leanncd/experiments/indexed_execution/IndexedOperationalSemantics.lean`.

**Three work items:**
1. Reusable compatible binary composition and arbitrary-witness soundness from
   existing `compose_default_phases`, with full private-state reconstruction.
2. Structural actual reassociation in the right constructor's full leaf-owned
   state/event space, applying `SharedSplice.associative_eq` directly.
3. Four actual outcomes, both original boundary equations, left/right/reference
   ordered/coincident cuts, native metadata observations and discoverable entry.

`binary_associativity` must not call `nested_default_runs`, `run_transport` or
`nested_histories` to substitute for structural equality. `BinaryHistory.sound`
identifies the already constructed right tree with its actual runner only after
structural equality is proved. `nested_observations` separately uses the
independently proved run transport to package native complete observations;
that legitimate second proof route does not replace the structural theorem.

**Fixture donors/deltas:** clone History's `first`, `second`, `privateFailure`
to shared successful cut, failure with no suffix, event-free coincident cut,
nonduplicated `[0,1,2]` snapshots, and incompatible start/finish rejection.
These are exactly five kernel examples, not five runtime triples.

```bash
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution apply --check /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/composition.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution apply /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/composition.patch
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd IndexedOperationalHistoryComposition IndexedOperationalHistoryAssociativity IndexedOperationalRunsPhases IndexedOperationalAssociativity IndexedOperationalSemantics
```

**Review checkpoint:** all three items are independently rejectable; inspect
their theorem signatures before proof windows. Failure in A requires no B/C
history/input; failure in B requires no C history/input; C may fail or succeed.
Retain every private value and prefix, allow coincident cuts, and preserve full
reference `Relation`. Eleven assigned live-proof controls are four binary,
three structural and four phase controls, including incompatible cut, private
state/ledger erasure, wrong identities, duplicate cut, strict order, wrong B
failure tag and changed BC input. Commit only the six Files after build/review.

## 7. Task 4 — private, donor, and reference/negative acceptance

Prerequisite: Task 3. Apply `acceptance.patch`.

**Files:**
- `leanncd/lakefile.toml`
- `leanncd/experiments/indexed_execution/IndexedOperationalAssociativityFixtures.lean`
- `leanncd/experiments/indexed_execution/IndexedOperationalAssociativityTest.lean`
- `leanncd/experiments/indexed_execution/IndexedOperationalAssociativityAudit.lean`

**Window-read symbols:**
- `privateComparison`, `privateCounts`, `privateRows`, `axisTailBoundary`,
  `emptyTailBoundary`, `collectionComparison`, `zeroComparison`, `axisComparison`,
  `collisionComparison`, `emptyObservation`, `referenceComparison`,
  `privateReferenceCuts`, `donorPrefixes`, `reorderedTripleRun`,
  `strongerThanFinalOutput`
  @ `leanncd/experiments/indexed_execution/IndexedOperationalAssociativityFixtures.lean`.
- `private_observations`, `empty_observations`, `private_reference`,
  `private_reference_outcomes`, `private_phases`, `empty_phases`
  @ `leanncd/experiments/indexed_execution/IndexedOperationalAssociativityTest.lean`.
- Namespace audits and printed theorem axioms
  @ `leanncd/experiments/indexed_execution/IndexedOperationalAssociativityAudit.lean`.

**Three acceptance shapes, shipped without redesign:**

| Shape / donor and delta | Observed discriminant to retain |
|---|---|
| Private: three `consumerComponent` leaves with `privateBoundary`/`privateInput`; profiles 4/4/4, 0/4/4, 4/0/4, 4/4/0; 0 is strict neighbor of total 4 | Complete 12 events/13 states; A/B/C failure 3/3, 7/7, 11/11. All transported event/snapshot/terminal comparisons agree. Thirteen full seven-coordinate snapshots and ordered prefixes are pinned. Success cuts 4 and 8 retain private values 7/2 and 19/2; final private value 163/2; outputs 9, 81, 6561. |
| Donor continuations: `producerComponent` or `zeroProducerComponent` plus two consumers; axis producer/consumer plus scalar consumer via `axisTailBoundary`; collision producer/consumer plus consumer; empty producer plus two empty consumers via both explicit boundaries | Collection +1/-1 remain separate before publication; zero-writer publication remains. Six nonconstant axis publications and nonpalindromic repeated reads produce 14 then 196. Guard-admitted occurrence ownership survives reused local names. Empty case complete, 0 events/1 state/budget 1, required external empty input present, coincident cuts allowed. |
| Reference/negative: actual `Executor.run` on the same nine triples; clone the ranked reordered-private graph control to reorder one collector in the total triple | Full published/pending/accumulator comparisons, two independently pinned reference cut rows. Donor reference events/states: collection 11/12, zero 9/10, axis 18/19, collision 13/14, empty 0/1. Altered graph has equal final availability but unequal ordered final ledger/events/snapshots; no match or rank is asserted for it. |

Exactly 10 executable groups: `operational-private-outcomes`,
`operational-private-full-observations`, `operational-donor-full-observations`,
`operational-empty-presence-coincident-cuts`, `operational-private-reference`,
`operational-donor-reference`, `operational-private-snapshots`,
`operational-reference-shared-cuts`, `operational-donor-event-order`,
`operational-observation-stronger-than-final-values`.

Retain all 15 full-proof declarations: six observation families, three reference
declarations (private runs, private outcomes, empty runs), six phase families.
Parameterized private declarations cover their profile family; do not replace
their propositions with Booleans or merely instantiate final-output equality.
The audit covers nine new proof/test namespaces, including metadata laws living
in `IndexedOperationalHistory`; printed axioms additionally cover concrete laws.

```bash
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution apply --check /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/acceptance.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution apply /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/acceptance.patch
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd IndexedOperationalAssociativityFixtures IndexedOperationalAssociativityTest IndexedOperationalAssociativityAudit
```

**Review checkpoint:** check the ten groups and fifteen declarations, complete
reference rows, exact payload/order checks and equal-output negative control.
Eleven manifest controls: O1–O8 corrupt observations; O9 substitutes a total
neighbor, O10 omits required empty raw input, O11 removes the graph reordering.
Their frozen expected diagnostics name the particular `indexed-reference
operational-...: expected` checks. None is an independent production-runner
defect kill. Commit only the four Files after build/review.

## 8. Task 5 — documentation and manifest handoff

Prerequisite: Task 4. This is one lightweight controller work item, not another
heavy implementation dispatch. Apply `documentation.patch`.

**Files:**
- `leanncd/AGENTS.md`
- `papers/semantics/categorical_tensor_logic_semantics.md`
- `papers/semantics/categorical_operational_associativity_mutations_post.json`
- `papers/semantics/categorical_operational_associativity_proof_mutations_post.json`

Read the operational entry paragraph @ `leanncd/AGENTS.md`, Sections 6.12/10.1
and adjacent status table @ `papers/semantics/categorical_tensor_logic_semantics.md`,
and `label`/`file`/`targets`/`expect` entries @ both manifest files.
No invented diagnostic or new control: the patch ships the verified 11/21
manifests. Observation and proof receipts remain separate.

```bash
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution apply --check /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/documentation.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution apply /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/documentation.patch
rg -n 'general trace algebra|general trace/process|operational associativity|process units|process category|nA.nB.nC' /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/AGENTS.md /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_tensor_logic_semantics.md
rg -n '19 kernel|nineteen kernel|28 kernel|thirty.two|32 cycles|21/21|11/11' /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics
```

**Review checkpoint:** prose claims match the frozen theorem APIs; units and
other boundaries remain explicit. Interpret historical counts in context:
record the 26/35 correction, do not rewrite old receipts as if they were new
measurements. After the following unfiltered `--check` commands pass, commit
only these four Files. Update execution checkpoints in the existing record;
never blanket-stage the artifact directory or another worktree's changes.

## 9. Mandatory controller release gates

The controller, not an implementer's report, runs all commands below. No task,
label-prefix or other filter is permitted. `--check` validates; it does not
replace executing each cycle. Use distinct new execution receipt files.

```bash
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_proof_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/observation_mutations_execution.md /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_artifacts/proof_mutations_execution.md /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/categorical_operational_associativity_proof_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd LeanNCD Tests IndexedExecutionExperiment
rg -n --glob 'IndexedOperational*.lean' '\bsorry\b|\badmit\b|^\s*axiom\b|\bunsafe\b' /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/leanncd/experiments/indexed_execution
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution diff --check
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution status --short
```

Require exactly 11/11 and 21/21 cycles, intended diagnostic in every broken
build, successful restored build and byte-identical restoration. All 21 proof
controls are classified as six history, four binary composition, three runner
transport, four phase, three structural associativity and one concrete metadata
neighbor. Audit only ordinary Lean axioms (`propext`, `Classical.choice`,
`Quot.sound` as applicable), no recovery `sorryAx` in restored final modules.
Do not treat `sorryAx` from intentionally rejected mutation logs as restored
source evidence, or silently waive an unexpected diagnostic.
Inspect source/probe scan hits in context; no-match exit 1 is expected for a
clean scan. Prose mentions are not admissions; actual new admitted/unsafe
proofs or a changed runner are release blockers.

Compare all 17 final files to `package.json`, five patches to their hashes,
and 12 module bytes to `snippets.json`. This verifies exact compiled-byte
delivery after cycles. Run this read-only check after the full build:

```bash
python3 -c 'import hashlib,json,pathlib; r=pathlib.Path("/Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution"); a=r/"papers/semantics/categorical_operational_associativity_artifacts"; p=json.loads((a/"package.json").read_text()); s=json.loads((a/"snippets.json").read_text()); assert len(p["sources"])==17 and len(p["patches"])==5 and len(s)==12; assert all(hashlib.sha256((r/f).read_bytes()).hexdigest()==h for f,h in p["sources"].items()); assert all(hashlib.sha256((a/e["path"]).read_bytes()).hexdigest()==e["sha256"] for e in p["patches"]); assert all(e["exit"]==0 and hashlib.sha256((r/"leanncd/experiments/indexed_execution"/(e["module"]+".lean")).read_bytes()).hexdigest()==e["source_sha256"] for e in s); print("PASS: 17 final files, 5 frozen patches, 12 final snippet-source identities")'
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution diff --exit-code 0ea62a923626f1dcdee1eb28f24e357f3996daf2 -- /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution/papers/semantics/jax_gqa_session_brief.md
```

Do not regenerate the frozen package in execution:
retain the original base/hash receipt. Any necessary source fix invalidates
the corresponding frozen-source receipt and requires targeted re-verification,
review and an explicit controller decision, not an unnoticed patch edit.

### Two final whole-branch review lenses

Use two independent bounded reviewers, one per lens; check available usage
headroom before launching them. Each stays within 40 rounds and 250k peak.
Both reviews use the complete diff from the frozen base, not only the last
commit. Also isolate changes since actual execution base `0ea62a92` so neither
review treats the concurrent GQA document as this slice's work. Open listed
identifiers in 40–60-line windows, append findings as they
are found to the existing record, and report usage headroom. Resolve real
findings in bounded groups; rerun affected checks and controller gates after
fixes. Clean per-task reviews do not replace either final review.

1. **Observation/transport/structural soundness:** strongest complete relation,
   concrete metadata laws, actual leaf ownership/domain maps, reusable binary
   compatibility and arbitrary-witness soundness; common-leaf state/event/input
   squares and direct `SharedSplice.associative_eq`; no run-isomorphism shortcut
   for structural associativity and no hidden execution-agreement premise.
2. **Runner/state/failure/metadata/budget integration:** actual default graph and
   reference entry points; all private values and ordered ledgers; complete
   reference published/pending/accumulator relation; all four branches, original
   boundary inputs, undefinedness normalization, ordered/coincident cuts,
   empty Option presence and `nA+nB+nC+1`; negative controls, nondefault wiring,
   namespace audits and scope/documentation agreement.

The controller records actual build/cycle/review receipts, exact retained
observations and theorem premises, failure/cut/validation scope, the count
correction, excluded units/category/source/backend work, and token telemetry.
No transcript means unavailable telemetry, not a measured budget pass; preserve
the initial runner prototype's possible small approximately-55-turn overrun.

## 10. Controlled integration — controller only, after gates

Authoring this plan authorizes no git write. During later execution, commit
each reviewed task's explicit Files and the controller's explicitly selected
plan/record/evidence deliverables; never use blanket staging or include
`.claude/settings.json`. Inspect every remaining untracked file before cleanup.

Only when the full build is green, all 32 cycles pass, both whole-branch lenses
are clean/adjudicated and final bytes/scope match: identify the primary checkout
from the preflight worktree list and confirm its branch is `main`. Preserve
primary edits; if they obstruct integration, stop rather than stash/reset them.
Check whether local main moved again from acknowledged execution base
`0ea62a92`; do not silently rebase or change the frozen package base. The
8268-to-0ea advance is already checked and does not require restarting the
prototype. Any further changed integration base requires controller adjudication
and revalidation on the resulting integration.

Merge the owned execution branch into local main with `--no-ff`, using
`/usr/bin/git -C` and the verified primary path. Verify main/branch content
equality and integration build before removing anything. Remove only
`/Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution`
and delete only `agents/categorical-operational-associativity-execution` after
accounting for its artifacts; prefer ordinary worktree removal, no forced
discard. Preserve the handoff worktree and every other branch/worktree.
No remote push. Report local integration and any ahead-of-origin state
truthfully; do not claim these later gates during authoring.
