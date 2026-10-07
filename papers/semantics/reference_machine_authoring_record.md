# Reference-machine plan authoring record

## Status and authorization

Artifact-only authoring on 2026-10-07 in the controller worktree.
The [live plan](reference_machine_plan.md) is **verified and execution-ready**.
Independent controller replay, actual mutations, full builds, and both final
review lenses are complete; the two command/artifact findings are corrected and
adjudicated below. This session publishes planning artifacts only, not the
candidate implementation. Future `reference_machine_execution_record.md` is
named but not created.

Prototype and initial authoring HEAD: `53bcbbd610a1791a5a769a40e33fd47b5a3abc7e`.
The write-up phase started with only supplied untracked reference-machine artifacts,
patches, and post-mutation manifest. No unrelated work was reverted.

## Evidence read and read-only checks

Read supplied [evidence](reference_machine_artifacts/evidence.json),
[replay audit](reference_machine_artifacts/replay-audit.json),
[emitter](reference_machine_artifacts/emit-patches.py),
all [three patches](reference_machine_patches),
and [post manifest](reference_machine_mutations_post.json) in windows no larger
than 60 lines. Read the [collection/model plan](collection_model_plan.md) as
structural precedent, plus bounded repository preparation/harness guidance.
Did not read prototype source separately or rediscover implementation.

Read-only checks actually performed during authoring:

- SHA-256 of all three supplied patches matches replay-audit exactly:
  `b864ebaca0846d85655431368c952d9c5c7cdcf0213c78bbabe6b17ba767446a`,
  `3f5b756c22416ee42a8bb380d3433eddf72845e56e4a931d54e62ddfa6e6f456`,
  `6dcdfaf1ef54cb6c8b9c80dc99dff3361cea43beb473c602fea10c4796c81935`.
- Base-to-HEAD diff over `leanncd` and the authority paper was empty.
- Donor model/collection/expression files, umbrella, lakefile, and execution
  infrastructure paths exist. Glob found none of the four generated
  Machine/Invariants/Soundness/ReferenceMachineTest outputs in the planning tree.
- Patch declarations and artifact counting rule agree on twelve constructions
  and 33 top-level named fixture theorem declarations, helpers/reachability
  witnesses included; no claim of 33 independent regressions.

These checks are NOT independent builds, actual mutation executions,
temporary-index replay, or semantic review verdicts.

## Prototype observations carried forward, with qualifications

Evidence reports targeted builds, four snippet checks, full default build
(8694 jobs), exact candidate-tree sequential replay, and accepted axiom
inventories. Seven generic results are compiled in the supplied prototype.
All such statements remain attributed prototype observations.

Twelve observed mutations were proof/type rejections, with twelve byte-identical
restores and restored green builds; ZERO runtime oracle kills. Populated final
expectations were matched against retained observed cycle segments, but not all
twelve cycles were rerun after population. Controller must independently execute
the populated manifest with `--out`, not merely `--check`.

Three fixture limitations are preserved explicitly:

1. Some duplicate/overwrite/erasure assertions check constructor eligibility
   premises rather than prove absence of a separately labeled transition.
2. The cyclic blocked state and model are proved, but that state's unrelated
   empty-fiber publication prefix has no separate reachability theorem.
3. Noncomputable state-update fixtures are kernel proofs; the readiness `#eval`
   observations do not supply an executable scheduler.

Evidence reports two unused-section-variable warnings and one unused-simp
fixture warning. Existing unrelated sorry warnings remain outside the new
inventories. Accepted new inventories contain only `propext`, `Classical.choice`,
`Quot.sound`; independent controller observation remains required.

## Inconsistencies and controller decisions

- Prototype budget accounting was inconsistent: an older manual 48-turn estimate
  and "no known breach" versus checkpoint 76 tool calls plus one persistence
  write. The checkpoint qualifies that tool calls and turns differ; if calls
  were the budget counter, 76 exceeded 60 by 16 before that write.
  No transcript was available to settle the counts or token peak/cumulative
  usage. The stale compliance phrase was corrected to defer to the checkpoint.
  Prototype budget compliance cannot be certified.
- Evidence's phrase "named theorem assertions" includes helper/reachability
  declarations. The plan uses the exact 33-declaration rule and explicitly
  declines independence claims.
- Emission/replay needs prototype commit objects and writes artifacts.
  Controller chooses an authorized disposable provenance-check location if
  reproducing emission; execution itself uses published patch bytes, never
  the candidate as a merge target or required HEAD.
- Controller must choose the later published local-main/compatible execution
  base, absolute checkout/result paths, and review actors. Any protected-source
  difference, occupied generated path, patch conflict, failed diagnostic
  expectation, or load-bearing review finding is a STOP/adjudication gate,
  not permission to redesign the replay.

## Independent controller verification

Preparation corrected the initial stale worktree to local main and verified
8,101 Mathlib oleans / 8,094 sources. Project imports were refreshed before Lean
checks. The initial prerequisite full build passed with 8,690 jobs.

While authoring, local main advanced through the unrelated f32 slice to
`2e850b14aa6eb91f05373a6a9afea98c55a6ed80`. The controller prepared a separate
replay checkout at that published main, confirmed all sixteen protected inputs
unchanged and all four generated outputs absent, and applied all three original
patches sequentially with successful `apply --check`.
The planning branch was fast-forwarded to the same compatible main; no unrelated
branch/worktree was edited or used as a build target.

The controller independently reproduced the patches and original-base tree
`f5ae8635700b025128567bc7c72eff32deedce6e`, checking the original observed mutation
segments. Exact patch digests remained unchanged. On advanced main, a temporary
index applied the same patches; every actual resulting working file matched that
index, including integration files containing unrelated main changes.
The independently replayed tree was
`f7a2f59ab5659a3b8c8436ff90edf2e58dfae946`.
The same exact comparison passed after all mutation restorations.
See [controller replay audit](reference_machine_artifacts/controller_replay_audit.json).

| Controller check | Observed result |
| --- | --- |
| Prepared advanced-main `LeanNCD` refresh | PASS, 8,555 jobs |
| Full candidate build, all default tests | PASS, 8,695 jobs |
| Original manifest schema/unique anchors | PASS, twelve entries |
| Actual populated production mutation suite | **12/12 PASS**, expected diagnostics, byte-identical restores, restored green builds |
| Fixture contrast discovery | **12/12 PASS**, one contrast per construction |
| Actual fixture suite after copying observed diagnostics into `expect` | **12/12 PASS**, expected diagnostics, byte-identical restores, restored green builds |
| Full candidate build after all restorations | PASS, 8,695 jobs |
| Full artifact-only planning-tree build | PASS, 8,691 jobs |
| Seven new generic theorem axiom inventories | Only `propext`, `Classical.choice`, `Quot.sound` |

Both retained result tables are part of the published package:
[production cycles](reference_machine_artifacts/controller_mutation_results.md)
and [fixture contrasts](reference_machine_artifacts/controller_fixture_mutation_results.md).
The final manifests are
[production controls](reference_machine_mutations_post.json) and
[fixture controls](reference_machine_fixture_mutations_post.json).
There are twelve production proof/type rejections plus twelve fixture contrasts,
not twenty-four implementation regressions or runtime oracle kills.
F01-F03 perturb expected duplicate/collision/empty-fiber values; F04-F06 change
legal/undefined/guard admission; F07-F09 distinguish unpublished dependencies,
readiness priority, and cyclic blocking; F10-F12 distinguish nonoutput completion,
valuation erasure, and supplied scalar input values. Each fails in the fixture
module for the pinned observed reason.

Observed readiness outputs were `["notReady", "notReady", "undefined"]` and
`["undefined", "notReady"]`. The imported collection donor observed
`[4, 9, 0, 0, 9, 5, 14, 3 / 4]`.
Noncomputable machine values and legal transitions are kernel theorem checks,
not scheduler executions. The seven public soundness results were checked with
their actual hypotheses, including witness-free success and reached-failure
exclusion. Existing categorical sorry warnings and the three new harmless lint
warnings remained visible; no new `sorryAx` appeared in the audited inventories.

Verbose builds, mutation logs, and incremental reviewer notes are retained in
the controller session's `files/` directory, not committed as temporary logs.
There are no Lean blocks in the live plan; the four real-module prototype
snippet checks and exact unchanged patch reproduction cover its code artifacts.
The artifact-level whitespace check flags five single-space blank context lines
inside the mechanically emitted integration patch. These are required diff
context prefixes, not trailing whitespace in the delivered files. Whitespace
checks pass for all non-patch artifacts and the actual replayed source; patch
bytes and their verified digests are intentionally preserved.

## Final reviews and adjudication

Both reviewers inspected the whole immutable prototype and the planning package,
with bounded prerequisite/authority reads. Their reviews cover all three task
groups. Later implementation still requires its own per-task and final gates.

1. **Semantic/proof fidelity: CLEAN.** Conservation, model preservation,
   successful model existence without a supplied model/rank witness, uniqueness
   among all complete models, denotation, and ready-failure exclusion accepted.
2. **Type/transition/fixture/discovery/artifact fidelity:** two Medium command
   findings, both corrected and adjudicated by the controller:
   - **RMB-01:** replace post-merge whole-tree equality with captured pre-merge
     main, ancestry checks for both histories, and topic-hunk/new-blob validation.
     Compatible main advances are preserved, not falsely rejected.
   - **RMB-02:** explicitly stage all three controller evidence files and require
     clean status after the artifact commit. The links and published tables are
     included above.

No open load-bearing finding remains. The controller also replaced the draft's
turn-specific authorization prose with the precise planning-only release boundary.
All changes after review are these bounded documentation/staging corrections and
the controller status record; no code patch or semantic contract changed.

**Readiness decision: approved for later guarded implementation replay.**
Ranked progress, finite termination, executable scheduling, source elaboration,
production/backend refinement, and cyclic solving remain excluded.
The premise-only eligibility assertions, unreached cyclic-blocked fixture, and
33-declaration counting qualification remain explicit limitations.

Only the artifact branch is approved for local main integration. The controller
records the actual commit/merge and own-worktree cleanup in session state.
No remote push is authorized or performed.

## Authoring budget

Requested approximately 25 turns / 100k peak context. Bounded-window artifact
authoring remained below approximately 25 assistant turns by manual accounting;
no observed authoring turn breach. This is not a host-verified usage metric.
Read-only token-report invocation for session
`c6866930-15ab-4eb1-8ab1-0ea2f842808e` returned
`no transcript for session`; measured peak and cumulative usage are unavailable.
Do not infer certified context-budget compliance from missing telemetry.

Controller token-report invocation also found no transcript, so the approximately
50M authoring target and peak-context limits cannot be certified or measured.
Final reviewer estimates were fourteen response rounds / approximately 50k peak
for the proof lens and twenty-one tool-bearing rounds for the boundary lens.
These are estimates, not aggregate token measurements. The prototype's possible
turn-budget overrun is surfaced above rather than silently reported as compliant.
