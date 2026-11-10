# Operational associativity: authoring evidence

## Status

Authoring phase (a) is complete: the operational associativity implementation,
acceptance observations and controls have been compiled and verified.
This record is not an implementation plan or an integration receipt.
The controlling brief is
[the handoff](categorical_operational_associativity_handoff.md).
The Full process applies because the requested result adds an operational
observation-equivalence soundness surface.

Worktree: `/Users/williammacready/code/python/pyncd.worktrees/categorical-operational-handoff`.
Branch: `agents/categorical-operational-handoff`.
Frozen local-main base: `8268da1f`.
Controller session: `e513127c-9c86-44d6-9ad8-bf82d0bb54c1`.

## Preparation

The existing isolated worktree was clean before setup. `prepare-worktree.sh`
fast-forwarded it from `ca75138c` to local main `8268da1f`, synchronized
8,101 Mathlib oleans against 8,094 source modules, and found 454 project
oleans. The wrapper build of `LeanNCD IndexedExecutionExperiment` passed
before new Lean code was introduced. No other worktree or primary-checkout
file was changed; no remote operation was performed.

## Controller prototype: actual nested transports

`IndexedOperationalReassociation` was checked with `lean-file.sh` and then
as its own named Lake target. Both final checks passed without warnings.

The proved prototype declarations are:

- `tensorEquiv` and `addressEquiv`: explicit equivalences of the actual
  nested declaration and full-address spaces, preserving leaf ownership.
- `embedding` and `embedding_address`: the same transport as a typed
  declaration embedding.
- `address_A`, `address_B`, `address_C`: full-address commuting squares,
  including both supplied boundary domain adapters. Input and defined
  cases are proved separately; no axis matching by name, cardinality or
  equal extent is used.
- `initial_available`, `input_roles`, `output_roles`: the same validated
  external input through both actual input lifts, and transported role
  metadata, including tensors without any addresses.
- `identityEquiv`, `identity_A`, `identity_B`, `identity_C`: one explicit
  invertible recoding of nested parity identities. The leaf cases are
  `4*n -> 2*n`, `4*n+2 -> 4*n+1`, and `2*n+1 -> 4*n+3`.
  This transports both occurrence tags and capabilities; it is not an
  arbitrary numerical relabeling admitted as an extra theorem premise.
- `leftRank`, `rightRank`: both nested rank certificates constructed with
  `compositeRankCertificate`.
- `default_budgets`: each actual nested graph has default budget
  `nA+nB+nC+1`, where each `n` is the corresponding standalone step count.

`sourceOccurrenceEquiv` additionally constructs the typed, guard-admitted
occurrence equivalence from the existing component occurrence equivalences.
`tensor_uid` proves the full tensor UID recoding through the same leaf partition.
Actual-run and history results are recorded below rather than inferred from
these static transports.

## Controller prototype: measured actual-run acceptance observations

`IndexedOperationalAssociativityFixtures` uses actual `runChecked` of both
existing nested constructors, not the public graph wrapper. After resolving
elaboration errors, the single-file wrapper check passed. The new scalar
tail boundary for the axis donor and the second empty boundary were compiled
in the real module, not assumed.

The finite test encoding keeps every available coordinate in contract tensor
order, every ordered ledger row, each event's tag/capability or full publication
address and value, and the complete/failing terminal state and transported
failure tag. Coordinate enumeration is a test serialization only; the generic
transport is the typed `addressEquiv`. Non-complete/non-failed outcomes remain
explicitly distinguishable by kind and are rejected by the pinned expected
outcomes; this test encoding is not the proposed generic history definition.

### Private triple: all four branches

Donors: three `consumerComponent` leaves, `privateBoundary`, `privateInput`.
The nearest strict/total neighbors use profile `0`/`4`, respectively.
Both actual bracketings produced the following measured counts:

| Profiles A/B/C | Outcome | Events | Normalized snapshots |
|---|---|---:|---:|
| 4/4/4 | complete | 12 | 13 |
| 0/4/4 | failed in A | 3 | 3 |
| 4/0/4 | failed in B | 7 | 7 |
| 4/4/0 | failed in C | 11 | 11 |

Every transported event, full snapshot and terminal observation agrees between
the two constructors in all four cases. The success fixture additionally pins
all thirteen seven-coordinate snapshots and every ordered ledger prefix.
The leaf outputs are 9, 81, 6561; the private values are 7/2, 19/2, 163/2.
Measured shared cuts are snapshot indices 4 and 8.

Actual `Program.Executor.run` and `referenceSnapshots` were separately
evaluated for all four branches. Their full published vectors, occurrence
pending-membership observations and all defined-coordinate accumulators agree
under the same leaf transports. The counts above also hold for these
normalized reference histories. At both success cuts, completed private
accumulators remain present while later leaf occurrences remain pending.
The two full cut rows are pinned independently of cross-bracketing equality.

### Other donor triples

Full graph event/snapshot/terminal comparisons passed for all of:

- `producerComponent` followed by two consumer leaves: separate +1 and -1
  contributions precede their sum's publication.
- `zeroProducerComponent` followed by two consumer leaves: zero-writer
  publication precedes continuation.
- `axisProducer`, `axisConsumer`, scalar consumer: all six nonconstant
  publications and the repeated nonpalindromic transported reads remain
  observable; the middle output is 14 and the final output is 196.
- `collisionProducer`, `collisionConsumer`, another consumer: the admitted
  contribution order is retained despite reused local names.
- `emptyProducerComponent` and two `emptyConsumerComponent` leaves with both
  explicit boundaries: complete, zero events, one snapshot, budget one.
  The external empty input is still present. Both vacuous joins can share
  index zero; no snapshot or boundary event was inserted.

The donor event-order fixture pins exact payloads and publication coordinates,
not only counts or visible final outputs.

## Controls and release status

The final eleven-entry observation/donor manifest was executed unfiltered by
the controller, with intended diagnostics, restored builds and byte-identical
source restoration. Its purpose is to show that finite acceptance observations
detect wrong identity transport, private-state erasure, ledger/event reversal,
publication omission, duplicate snapshots, pending erasure and accumulator
erasure. Eight entries corrupt test observations; three substitute a total
neighbor, omit required empty raw input, or remove the graph-only reordered
collector control. These are not eleven mutations of the production runner.
The [results](categorical_operational_associativity_artifacts/observation_mutations_verified.md)
retain each executed receipt.

All twenty-one live-proof controls also passed the actual unfiltered repository
mutation runner, with intended diagnostics, restored builds and source hashes:
six history, four binary composition, three runner transport, four phase,
three structural associativity and one concrete metadata-neighbor control.
Their [results](categorical_operational_associativity_artifacts/proof_mutations_verified.md)
are proof/observation sensitivity evidence, not runtime runner-defect kills.

The final acceptance module has ten executable check groups over nine matched
triple cases and one graph-only control. Full reference observations were
measured for all nine matched cases. The collection, zero, axis, collision and
empty reference event/snapshot counts are respectively 11/12, 9/10, 18/19,
13/14 and 0/1. The graph-only reordered total triple has identical final
availability values, but different ordered final ledgers, events and snapshots;
no match or rank is asserted for that altered graph.

## Completed generic and actual proof surface

- `IndexedOperationalHistory`: lossless admissible histories, shared-state
  continuation algebra, transport laws, actual default-run existence and full
  reference observations. Its twenty-six kernel examples include ordered/private
  work, strict failure, empty metadata and incompatible-cut controls.
- `IndexedOperationalObservationLaws`: identity/inverse/composition and
  congruence for the exact concrete `MetadataTransport.Agrees` and
  `CompleteObservation.Agrees` relations, not a weaker substitute.
  Four kernel examples distinguish whole empty-port metadata and Option
  presence despite identical address observations.
- `IndexedOperationalHistoryComposition`: a structural `BinaryHistory`,
  reusable shared-cut algebra, full-state reconstruction, arbitrary-witness
  uniqueness/soundness and `compose_history` from the existing actual binary
  phase theorem. Its five kernel examples cover success, failure without a
  suffix, coincident cuts and incompatible starts.
- `IndexedOperationalHistoryAssociativity`: `binary_associativity` proves
  structural reassociation in the right constructor's full state/event space.
  Explicit `state_A/B/C`, `event_A/B/C`, `lift_A/B/C`, input/boundary squares
  and the shared cut derive the premises of `SharedSplice.associative_eq`.
  This proof does not invoke nested runner isomorphism as a shortcut.
  `actual_nested_histories` instantiates both actual constructors;
  `right_nested_tree` exposes the B-C subtree. Failure in A requires no B/C
  history or completed boundary; failure in B requires no C input/history.
- `IndexedOperationalRuns`: independently derives actual ordered step selection,
  evaluation and full-run transport. `nested_reference_runs` and
  `ranked_nested_reference_outcomes` compare actual `Executor.run` results and
  normalized snapshots with both complete existing `Relation` values.
- `IndexedOperationalRunsPhases`: `triple_phases` derives all four actual
  outcome branches, both original boundary inputs and ordered reached cuts.
  Full right-run and reference cuts retain private values, ledger prefixes,
  pending occurrences and accumulators. Empty B permits coincident cuts.
- `IndexedOperationalAssociativity`: `nested_metadata` preserves actual native
  port lists, full Option input and original adapters `(ab,bc)`;
  `nested_observations` gives the chosen complete observation agreement for
  both actual default runs.

The entry point is `import IndexedOperationalSemantics`, only under
`IndexedExecutionExperiment`. Fifteen proof-valued acceptance instances retain
the full generic propositions for the donor families. Namespace audits cover
all nine new proof/test namespaces and report only ordinary Lean axioms.
No new axiom, admitted proof, unsafe runner or production-language change was
introduced.

### Frozen authoring package

The controller's complete `LeanNCD Tests IndexedExecutionExperiment` wrapper
build passed. All twelve real-module final-source snippets passed
`check-snippet.sh`. `package.py` mechanically generated five ordered per-task
patches and replayed them in a private index from the frozen base; all seventeen
source/wiring/documentation/manifest files were byte-identical.
Receipts and hashes are in
[package.json](categorical_operational_associativity_artifacts/package.json),
[snippets.json](categorical_operational_associativity_artifacts/snippets.json),
and the preserved prototype full-build log.

Fresh bounded plan authoring, clean-worktree execution, both final whole-branch
review lenses, controller release revalidation and local integration remain
separate gates. No merge or remote push is claimed by this authoring record.

### Remaining semantic boundaries

The main actual theorem takes validated A input, three local rank certificates
and the two supplied original boundaries. Ranks are constructed for both
bracketings, whose own budgets are `nA+nB+nC+1`. No model existence, uniqueness,
completion or execution-agreement premise is added. Invalid raw inputs retain
their constructors' existing validation order; unequal debug budgets are not
reassociated by the main theorem.

Process units/full process category, broader source interpretation and backend
or numerical refinement remain outside this slice. A core copy still adds
events; no event-free identity is manufactured by weakening observations.

## Budget telemetry

`token-report.py e513127c-9c86-44d6-9ad8-bf82d0bb54c1` reported
`no transcript for session e513127c-9c86-44d6-9ad8-bf82d0bb54c1`.
This is unavailable telemetry, not a measured budget pass. Authoring and
execution limits remain in force; any dispatch-limit stop or overrun must
be disclosed separately.

The initial runner prototype dispatch reported approximately fifty-five rounds
and could not rule out a small turn-budget overrun. Subsequent phase, binary
composition, structural associativity and concrete metadata-law dispatches
reported completion within their fifty/fifty/fifty/forty-five-round limits.
No measured cumulative-token or peak-context pass is claimed.

## Controller preflight adjudication

The fresh plan correctly found seven indented `example` declarations omitted by
the earlier column-zero-only count. An indentation-aware recount gives 26
History + 4 concrete metadata + 5 composition = **35 kernel examples**.
The controller accepts this evidence correction; all compiled examples remain
required, and no source, patch, fixture or threshold is removed or weakened.

The clean execution worktree was prepared on latest local main `0ea62a92`.
Its only advance from frozen prototype base `8268da1f` is the unrelated
153-line GQA session brief. No patch-owned file overlaps; that document is
preserved. Warm Mathlib and project output were verified and the clean
execution baseline `LeanNCD` wrapper build passed before Task 1.

## Clean execution checkpoints

The five verified patches were applied sequentially in the separately prepared
execution worktree, never copied over its Lean sources. Every forward patch
check and each named task build passed before its checkpoint commit:

| Task | Commit | Verification and review checkpoint |
|---|---|---|
| History/concrete laws | `830e5823` | Both named modules passed; retained exact failure normalization, shared boundary and all 30 kernel examples |
| Actual transport/runs | `2b8c3310` | Both named modules passed; no action/execution agreement premise, complete native graph/reference projections |
| Composition/associativity/phases | `f2107792` | All five named modules passed; structural common-leaf equality, full private suffixes, four outcome branches and coincident cuts |
| Acceptance/audits | `98b3218d` | Three named targets passed; all ten executable groups, fifteen full-proposition instances and namespace audits |
| Documentation/manifests | `72f15ebd` | Both unfiltered manifest checks passed; entry-point scope and remaining units/backend boundaries retained |

The task-5 value-grep sweep found two additional stale global trace-algebra gap
sentences in the synthesis's source-result/A.8 summaries. The controller
corrected only those related paragraphs, regenerated the documentation patch
and package receipt explicitly, and reverified all five patches/seventeen file
identities in ordered private-index replay. The first four patches and all
twelve compiled Lean module bytes are unchanged. This is a declared,
documentation-only correction, not an unnoticed frozen-package source change.

Final controller execution mutation cycles, whole-build revalidation, both
independent whole-branch review lenses and integration follow below.

### Whole-branch review: observation/structural soundness

The independent soundness reviewer reported CLEAN with no high-confidence
findings. It verified all seventeen frozen file identities against committed
execution Git bytes, then reviewed the entire owned branch: concrete full
observations and laws, fixed leaf transports, binary soundness, structural
associativity, actual graph/reference bridges, fixtures, audits, manifests and
documentation. The reviewer used stable prototype/committed bytes rather than
the execution worktree's intentionally mutated sources and did not run builds.
Its detailed scope/limits are retained in
[review_soundness.md](categorical_operational_associativity_artifacts/review_soundness.md).
It reported completion within its forty-round limit; exact telemetry remains
unavailable. The second review and controller release checks remain separate.

### Controller clean-execution observation controls

The controller reran the entire eleven-entry observation/donor/graph manifest
without filters in the clean execution worktree. All 11/11 cycles passed:
each intended diagnostic was observed, the restored named build passed and
the source was byte-identical after restoration. These are fresh execution
receipts, not reuse of the prototype run:
[observation_mutations_execution.md](categorical_operational_associativity_artifacts/observation_mutations_execution.md).
The twenty-one live-proof controls were run separately, serially with
these source mutations to avoid cross-contamination.

### Controller clean-execution proof and full-build gates

The separate unfiltered live-proof run completed **21/21**, with every intended
diagnostic, restored named build and byte-identical source restoration:
[proof_mutations_execution.md](categorical_operational_associativity_artifacts/proof_mutations_execution.md).
Together the fresh clean-execution manifests passed all **32/32** classified
controls. No filter, setup refusal or silent skip was counted as a pass.

After both mutation runs restored their sources, the controller full
`LeanNCD Tests IndexedExecutionExperiment` wrapper build passed **8,942 jobs**.
The nine new namespace audits report only ordinary Lean axioms; source scanning
found no new admitted proof, axiom declaration or unsafe implementation.
Final delivery checks passed all seventeen source/wiring/documentation/manifest
hashes, five patch hashes and twelve compiled snippet-source identities.
The unrelated concurrent GQA document is unchanged. Whitespace/source diff
checks passed. The second independent review and integration remain pending.

### Whole-branch review: execution integration

The second independent reviewer reported CLEAN with no high-confidence bugs
across the entire owned `0ea62a92..72f15ebd` branch. It reviewed actual runner
entry points, full graph/reference states, strict failures, boundaries, ordered
and coincident cuts, empty metadata, default budgets, acceptance controls,
nondefault wiring and documentation. It used hash-verified stable committed
sources and did not interfere with mutation/build gates. Its detailed findings,
scope and limits are in
[review_integration.md](categorical_operational_associativity_artifacts/review_integration.md).
The reviewer reported twenty-five rounds, within its forty-round limit.

Both required whole-branch lenses are therefore clean, and all controller
release gates are green. No finding was silently waived. This checkpoint
authorizes the planned local integration; the actual integration receipt
follows only after the merge and integration build succeed.

### Integration preflight: concurrent primary documentation edits

Primary local main still points to the reviewed execution base `0ea62a92`, but
its working tree now has unrelated uncommitted edits to
`papers/semantics/README.md` and the shared synthesis. The synthesis changes add
a roadmap-stage column to the same progress ledger updated by this slice, in
addition to math-fence formatting edits. This is a genuine overlapping-documents
integration decision, not a theorem/build/review failure.

The controller has not changed, staged, stashed or discarded either primary
edit and has not attempted a conflicting merge. The fully verified slice and
its explicit evidence deliverables are committed on the owned execution branch.
Local integration/cleanup waits for user guidance or the concurrent edits'
completion; no push is authorized or performed.

## Fresh authoring (b): frozen-package implementation plan

The fresh bounded authoring phase produced
[`categorical_operational_associativity_plan.md`](categorical_operational_associativity_plan.md).
Full process, five sequential mechanically generated patch tasks; no new
Lean implementation, prototype, manifest, documentation patch or package edit.
Only the plan and this evidence append are deliverables of this phase.
No production source mutation, stage, commit, merge or push was performed.

### Frozen and actual execution bases

The prototype/package base remains
`8268da1f5761b839f1b16a03a6b3a799ef4a583f`.
The controller prepared the separately isolated execution worktree at
`/Users/williammacready/code/python/pyncd.worktrees/categorical-operational-associativity-execution`,
branch `agents/categorical-operational-associativity-execution`, then preparation
fast-forwarded to latest local main
`0ea62a923626f1dcdee1eb28f24e357f3996daf2`.
The controller reported cache counts 8,101/8,094/454 and will refresh execution's
`LeanNCD` baseline before Task 1. This is not a claim that authoring ran that build.

Read-only Git comparison confirmed the only intervening path is the unrelated
153-line `papers/semantics/jax_gqa_session_brief.md`; none of the 17 frozen
patch-owned files changed. The plan preserves this concurrent work and does
not reset execution to the prototype base.

### Authoring verification receipts

- Re-ran the unchanged `package.py`: `PASS: 5 ordered patches, 17 byte-identical
  files`. It replayed from the frozen base with each `git apply --cached --check`
  in its private index. All five patch hashes and all 17 source/wiring/docs/
  manifest hashes still match `package.json`.
- Additionally replayed those same five patches in a separate private index
  initialized at actual latest-main execution base `0ea62a92`. Every ordered
  forward `--check` and application passed. All 17 final hashes match the frozen
  receipt; the unrelated GQA document's Git blob was unchanged. The private
  index and its lock were removed; no working-tree source/index was modified.
- Ran both standard manifests unfiltered with `--check`, not actual mutations:
  `manifest OK: 11 entries, 11 selected, every old-string unique`;
  `manifest OK: 21 entries, 21 selected, every old-string unique`.
  The earlier controller's executed 11/11 and 21/21 receipts remain the
  mutation evidence; authoring (b) does not claim another execution.
- Checked all 12 snippet receipt entries against the exact final-source hashes.
  The frozen full-build log ends `Build completed successfully (8942 jobs)`.
  No new Lean block was authored; the plan ships only compiled patch bytes.
- Verified task/module/manifest paths and the incremental Lake-list patch
  windows. Governing Patterns and Global Pitfalls total 2,976 characters;
  no child experiment `AGENTS.md` exists and no instruction trim is required.
- Parsed the plan's 32 literal shell commands, checked their input paths
  against the frozen tree and output parent directories, checked the five
  task Files sets against patch ownership, and retained only Bash fences.
  The live plan is 536 lines, below the approximately 800-line limit.
  The two final unfiltered execution manifests, controller full build, exact
  17-file/5-patch/12-snippet identity check and two whole-branch review lenses
  are explicit later gates, not claimed authoring results.

### Fixture-count inconsistency, not a dropped obligation

The inherited “nineteen kernel examples” claim above and the authoring brief's
`19 + 4 + 5 = 28` do not match the frozen patch. Direct count and bounded
fixture-window inspection find **26** `example` declarations in
`IndexedOperationalHistory`: 18 generic/history-transport, four concrete-state
and four empty-metadata examples. `IndexedOperationalObservationLaws` has four;
`IndexedOperationalHistoryComposition` has five. The actual shipped kernel
total is therefore **35**, not 28. No example was removed or reclassified as
nonexistent to satisfy the stale count. The plan flags this discrepancy for
controller acknowledgement while retaining the entire compiled package.

The other exact counts agree: ten executable groups over nine matched triples
and one graph-only control; fifteen full-proof declarations; 32 cycles,
classified as eight observation corruptions, two donor/input substitutions,
one graph control and 21 live-proof controls (6 history, 4 binary, 3 runner
transport, 4 phase, 3 structural, 1 concrete metadata-neighbor).
Earlier intermediate semantic gap lists remain closed as reconciled above.
No load-bearing theorem/package replay defect was found.

### Authoring budget and remaining gates

This authoring dispatch remains below its 40-round limit; no known turn-budget
breach or context warning occurred. Exact token/peak telemetry is unavailable:
the prescribed token-report invocation again returned
`no transcript for session e513127c-9c86-44d6-9ad8-bf82d0bb54c1`.
No measured peak-context or cumulative-token pass is asserted. Preserve the
initial runner prototype's separately disclosed possible small turn overrun.

Clean execution, all controller release cycles/full build, both final
whole-branch review lenses and controlled local integration/owned-worktree
cleanup remain pending. Preserve all other worktrees and primary edits;
no remote push is authorized.
