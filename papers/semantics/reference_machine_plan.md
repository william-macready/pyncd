# Relation-only reference machine, conservation, and reached-run soundness

## 1. Authority, process, and readiness boundary

**Full path:** one new machine/soundness capability, with THREE independently
rejectable task groups: machine; invariants and soundness; fixtures and integration.
Current authorization is **PREPARE AND VERIFY PLAN ONLY**, not implementation
release. Disposable prototype/replay builds, mutations, and reviews verify the
plan; only planning artifacts may be published by this session. See the separate
[authoring record](reference_machine_authoring_record.md) for the controller's
verification and readiness decision. The execution instructions below govern a
later implementation session, not permission to merge either prototype.

Authority is [tensor_logic_semantics.md](tensor_logic_semantics.md), Sections
24, 25, 26.1, 26.2, and 26.3, as located in
[evidence.json](reference_machine_artifacts/evidence.json).
The existing [collection/model plan](collection_model_plan.md) is a structural
precedent, not authority to inherit its completed validation or review claims.
The mechanically emitted patches are the implementation source of truth:
[01-machine](reference_machine_patches/01-machine.patch),
[02-invariants-soundness](reference_machine_patches/02-invariants-soundness.patch),
[03-fixtures-integration](reference_machine_patches/03-fixtures-integration.patch).
There are no Lean blocks in this plan. Replay, do not transcribe or redesign.

Provenance, NEVER merge targets or required future execution HEADs:

| Artifact | Exact provenance |
| --- | --- |
| Prototype base | `53bcbbd610a1791a5a769a40e33fd47b5a3abc7e` |
| Task 01 commit | `82eba635c9c25f39e0f94358b9d8d8893070ad62` |
| Task 02 commit | `e70aa2d9dfb8d723a0cabdae38dab2ac2aaa5240` |
| Task 03 commit | `1c99cf0fad676268961e6ba201d15fa718adc1bd` |
| Candidate tree | `f5ae8635700b025128567bc7c72eff32deedce6e` |
| Candidate branch | `reference-machine-soundness-proto` |

Execution starts on later published LOCAL main or a compatible descendant.
Unrelated main advancements are allowed when all 16 protected prerequisites
remain unchanged, generated outputs are absent, and original patches apply
cleanly. Do not describe an advanced main as artifact-only when it contains
other landed work; preserve that work, including integration-file edits.
Do not merge/check out the implementation candidate to establish readiness.
[emit-patches.py](reference_machine_artifacts/emit-patches.py) mechanically emits
commit diffs, checks sequential temporary-index replay FROM THE ORIGINAL BASE
and exact candidate-tree equality, protects 16 inputs, and counts fixture
declarations. That entire-tree equality is valid only for baseline replay. With
`--observations` it matches populated expectations to retained original log
segments. It WRITES patches/audit: do not use it as a normal execution dependency.
Controller provenance reproduction must compare the resulting patch digests;
the checked-in patch bytes, not regenerated output, govern implementation replay.
[replay-audit.json](reference_machine_artifacts/replay-audit.json) is prototype
evidence, not this controller's independent replay verdict.

Preserve the user's unrelated f32 branches/worktrees. Do not rebase, build in,
write into, remove, or use them as execution checkouts. Required preparation
cache discovery may enumerate registered worktrees read-only and copy a donor
cache into the new checkout; it must not build in or modify any donor.
If stronger cache restrictions arise, STOP for controller adjudication.
No remote push.

## 2. Exact scope and semantic contract

Deliver reference-machine transitions, tagged finite conservation, successful-run
existence and uniqueness of a COMPLETE model, and reached ready-undefined failure
excluding every model. Ranks, finite measure/termination, progress/maximal-run
completeness, executable scheduling, cyclic solving, source elaboration,
production/backends, precision refinement, and full categorical interpretation
are deferred. These are not prerequisites silently added to successful soundness.

`Running` has only published partial store, retained accumulators, and pending
tags. `Pending` is a dependent family: for EACH defined tensor, a finite set of
the existing `Occurrence` tags (statement tag plus guard-admitted valuation).
No quotient/deduplication by destination, body, value, or statement alone.
`History` is existential proof-only data in `StateInvariant`, never another
public runtime field or a required caller-supplied successful witness.

Algebra is ONLY an `AddCommMonoid` on each participating defined carrier.
`ScalarOps` remains independent explicit data. Do not identify its operations
with collection addition or add semiring/float/nonlinear commutation laws.
Existing `Program.collect` genuinely remains finite fiber pushforward, not an
imperative collector with a categorical sidecar. The successful proof explicitly
relates spent tagged sums to existing `collect` and `pushforward`.

### Initialization and rules

| Surface | Exact requirement |
| --- | --- |
| Input | Reuse validated `Program.Input`; exact tensor-level presence, even an empty input tensor; no supplied defined tensor binding |
| Initial published store | Supplied input cells only; defined cells unavailable |
| Initial accumulators / pending | Zero / all existing admitted occurrence tags |
| CONTRIBUTE | Running source, selected tag pending, `evalReady = evaluated (some v)`; add at its destination and erase exactly that tag, even when `v = 0`; published store unchanged |
| PUBLISH | Defined target coordinate, unpublished, destination fiber has no pending tags; publish retained accumulator, preserving pending and accumulators |
| UNDEFINED | Running source, selected tag pending, `evalReady = evaluated none`; failure records defined target, full statement/valuation occurrence, and the EXACT unchanged running snapshot |
| Failed state | Terminal: no transition of any rule |
| Complete | ALL pending sets empty AND EVERY declared address published, including defined nonoutputs, not merely outputs |
| Successful | Reachable from validated initialization AND Complete, with no rank or model premise |
| Blocked | Not Complete AND no outgoing Step; blocking is not undefinedness or model nonexistence |

Publication is explicit for zero-consumption/empty fibers, yielding available
zero. A populated accumulator is NOT readable before publication. Publication
cannot overwrite a published cell. Inputs and published values are immutable
along reachable transitions; publication extends the partial store.
Unavailable reads dominate primitive domain failure in the same strict body.
Guard-excluded undefined bodies have no admitted tag and cannot raise failure.
The noncomputable updates plus logical `Step`/`Reaches` are a relation-only
reference machine; fixtures are logical kernel proofs, not an executable scheduler.

### Invariant and exact public theorem hypotheses

Common parameters: `{K : S -> Type}`, `{sigma : Declarations S}`,
`{r : Registry K}`, `P : Program K sigma r`,
`ops : (s : S) -> ScalarOps (K s)`,
`[forall t : P.Defined, AddCommMonoid (K (sigma.signature t.val).sort)]`,
and validated `eta : P.Input`. No additional `ScalarOps` laws.

The invariant retains input values, requires every published defined fiber to
be exhausted and equal its retained accumulator, equates each accumulator with
the finite destination-filtered sum of consumed tagged values, and proves that
every consumed body still evaluates to its recorded value in any complete store
agreeing with published cells. `StateInvariant` existentially hides that history;
for failure it additionally retains the pending tag and ready-undefined equation.

All following identifiers are `Program` identifiers. New file paths are
deliverables named in Sections 5-7, deliberately absent before patch application.

| Theorem | Additional hypotheses | Exact conclusion |
| --- | --- | --- |
| `reachable_invariant` | `s : P.MachineState`; `reached : P.Reaches ops (.running (P.initial eta)) s` | `P.StateInvariant ops eta s` |
| `successful_model` | `c : P.Running`; `success : P.Successful ops eta c` | `P.Models ops eta (P.finalStore c success.2)` |
| `candidate_preserved` | `rho : Store K sigma`; `model : P.Models ops eta rho`; `s : P.MachineState`; same initial reachability to `s` | `P.CandidateAgreement rho s`: running published agreement, False for failure |
| `successful_unique` | `c : P.Running`; `success : P.Successful ops eta c` | `forall rho, P.Models ops eta rho -> rho = P.finalStore c success.2` |
| `successful_admInput` | `c : P.Running`; `success : P.Successful ops eta c` | `P.AdmInput ops eta` |
| `successful_denotation` | `c : P.Running`; `success : P.Successful ops eta c` | Existing `P.denotation ops eta (P.successful_admInput ops eta c success)` equals `P.outputProjection (P.finalStore c success.2)` |
| `failed_no_model` | `t : P.Defined`; `o : P.Occurrence t`; `c : P.Running`; reached `.failed t o c` from validated initial state | `not exists rho, P.Models ops eta rho` |

The candidate model is a hypothesis ONLY for the preservation lemma and the
universally quantified uniqueness competitor. It is NOT a witness needed to
derive successful-model existence, admissible input, or denotation.
Failure nonexistence applies to REACHED ready-undefined failure, not any
undefined body, arbitrary failed snapshot, or notReady/blocked state.

Axiom acceptance: all seven printed generic theorem inventories and the three
printed fixtures in evidence contain only `propext`, `Classical.choice`,
`Quot.sound`. Require the controller to observe these inventories independently.
No new `sorry`, `sorryAx`, axioms, `native_decide`, or unproved algebra instances.
Existing unrelated sorry warnings are reported, not repaired or used by these
new results. Evidence reports two unused-section-variable warnings and one
unused-simp fixture warning; do not silently claim a warning-free build.

## 3. Preparation, source protection, and replay guards

Controller owns authorization, preflight, actual mutation execution, full builds,
reviews, readiness declaration, and any later local integration.
Commands below are FUTURE execution templates. Replace every placeholder with
a literal absolute path or branch name; never compute shell variables.
Use plain separate commands, no compound shell, no pipelines into git.
The new execution session must already have the execution worktree as its cwd.

Create an isolated execution worktree from controller-selected published local
main/compatible descendant via the repository new-slice procedure (EnterWorktree).
Run preparation with the LOCAL base, not remote HEAD. Omit `--plan` because
published artifacts are already tracked; do not copy an older ignored plan over
them. Inspect each failure and STOP if Mathlib cache preparation is incomplete.

```bash
bash <execution-worktree>/.claude/skills/new-slice/prepare-worktree.sh --base <execution-base-branch>
/usr/bin/git -C <execution-worktree> status --short
/usr/bin/git -C <execution-worktree> merge-base --is-ancestor 53bcbbd610a1791a5a769a40e33fd47b5a3abc7e HEAD
/usr/bin/git -C <execution-worktree> diff --exit-code 53bcbbd610a1791a5a769a40e33fd47b5a3abc7e HEAD -- leanncd/LeanNCD/Semantics/Types.lean leanncd/LeanNCD/Semantics/Expr.lean leanncd/LeanNCD/Semantics/Interpret.lean leanncd/LeanNCD/Semantics/Readiness.lean leanncd/LeanNCD/Semantics/Completeness.lean leanncd/LeanNCD/Semantics/Collection.lean leanncd/LeanNCD/Semantics/Program.lean leanncd/LeanNCD/Semantics/Models.lean leanncd/test/Semantics/ExpressionTest.lean leanncd/test/Semantics/CollectionModelTest.lean papers/semantics/tensor_logic_semantics.md leanncd/scripts/lake-build.sh leanncd/scripts/lean-file.sh leanncd/scripts/mutation-manifest.sh leanncd/scripts/mutation-cycle.sh .claude/skills/new-slice/prepare-worktree.sh
/usr/bin/git -C <execution-worktree> rev-parse HEAD
test ! -e <execution-worktree>/leanncd/LeanNCD/Semantics/Machine.lean
test ! -L <execution-worktree>/leanncd/LeanNCD/Semantics/Machine.lean
test ! -e <execution-worktree>/leanncd/LeanNCD/Semantics/Invariants.lean
test ! -L <execution-worktree>/leanncd/LeanNCD/Semantics/Invariants.lean
test ! -e <execution-worktree>/leanncd/LeanNCD/Semantics/Soundness.lean
test ! -L <execution-worktree>/leanncd/LeanNCD/Semantics/Soundness.lean
test ! -e <execution-worktree>/leanncd/test/Semantics/ReferenceMachineTest.lean
test ! -L <execution-worktree>/leanncd/test/Semantics/ReferenceMachineTest.lean
shasum -a 256 <execution-worktree>/papers/semantics/reference_machine_patches/01-machine.patch <execution-worktree>/papers/semantics/reference_machine_patches/02-invariants-soundness.patch <execution-worktree>/papers/semantics/reference_machine_patches/03-fixtures-integration.patch
```

Ancestry alone is insufficient. Require clean status INCLUDING untracked files,
unchanged ALL 16 protected inputs (the explicit list above), absence of all FOUR
new outputs including dangling symlinks, and these exact patch digests.
The guard is NOT a blanket diff over leanncd: unrelated landed backends,
AGENTS guidance, and lakefile entries may differ from the prototype base.
Capture the prepared HEAD in controller session artifacts for hunk comparison;
after successful controller rehearsal, record its exact hash as rehearsal base.

| Patch | SHA-256 |
| --- | --- |
| 01 | `b864ebaca0846d85655431368c952d9c5c7cdcf0213c78bbabe6b17ba767446a` |
| 02 | `3f5b756c22416ee42a8bb380d3433eddf72845e56e4a931d54e62ddfa6e6f456` |
| 03 | `6dcdfaf1ef54cb6c8b9c80dc99dff3361cea43beb473c602fea10c4796c81935` |

If preparation leaves an untracked disposable ledger, inspect its resolved path.
Move only that named ledger into controller session artifacts, never stage it.
The following is conditional on that exact ledger existing and destination absent:

```bash
mv <execution-worktree>/.superpowers/sdd/reference_machine_plan <controller-session-artifacts>/reference_machine_preparation_ledger
/usr/bin/git -C <execution-worktree> status --short
```

With `--plan` omitted, do not assume a ledger was created. Keep tracking/review
notes in session artifacts. Do not delete unrelated untracked work to get green.
Repeat the ancestry/source/absence guards after preparation, before first build.
A protected-input mismatch, existing new output, nonempty status, changed patch digest,
or failed `apply --check` is a controller STOP, not permission to port/rebase,
edit the patch, weaken a theorem, or merge the prototype.

Then refresh project-owned oleans against the prepared sources:

```bash
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD
```

Never run lake from repository root. Stop on a Mathlib cold build; do not wait
through a mistaken cache setup. Check covering AGENTS hook-injected
Pitfalls/Checks/Patterns/Context sizes before execution and again after Task 03;
approximately 3k characters is the gate, not an inherited measured assertion.
If exceeded, controller adjudicates a bounded context remedy; do not silently
rewrite the compiled patch or widen this slice.

Apply/check in task order on the actual worktree, not all checks on the empty
base. Original-base temporary-index exact-tree replay is provenance, not a
substitute for actual-source `apply --check`. For a later-main rehearsal, validate
each patch's NEW/MODIFIED hunks against the captured prepared HEAD and preserve
all unrelated edits outside those hunks. Existing modified integration files
need not equal prototype blobs; their patch changes must land without dropping
other main changes. New module blobs must remain exactly the emitted results.
Neither later-main HEAD nor its entire resulting tree must equal the candidate.

After each patch, inspect only its relevant diff hunks; after all three, verify
these NEW file blobs with the following read-only commands:

```bash
/usr/bin/git -C <execution-worktree> diff <execution-base-commit> -- leanncd/LeanNCD/Semantics/Machine.lean leanncd/LeanNCD/Semantics/Invariants.lean leanncd/LeanNCD/Semantics/Soundness.lean leanncd/test/Semantics/ReferenceMachineTest.lean leanncd/LeanNCD/Semantics.lean leanncd/lakefile.toml leanncd/LeanNCD/Semantics/AGENTS.md leanncd/AGENTS.md
/usr/bin/git -C <execution-worktree> hash-object <execution-worktree>/leanncd/LeanNCD/Semantics/Machine.lean <execution-worktree>/leanncd/LeanNCD/Semantics/Invariants.lean <execution-worktree>/leanncd/LeanNCD/Semantics/Soundness.lean <execution-worktree>/leanncd/test/Semantics/ReferenceMachineTest.lean
```

Expected Git blob IDs, in command order: `9685fa7cb8e64dea41676e5f7e05f3a65e37cde3`,
`b52289195c0efac9f926b6257c6f6e57cbde4fff`,
`a8882d25f6626bd7e655b5631547967b7748b7fb`,
`9204a011f7ad5fc4966ffb3c4775678be550b4e8` (original patch index headers).
For per-task inspection narrow the diff path list to that patch's files.
Do not regenerate/re-author patches to erase compatible main advancements.

## 4. Brief discipline and risk budget

EVERY task/review/handoff brief begins with this preamble verbatim:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Use `rg -n` to locate the supplied identifiers; read approximately 40-60-line
windows, never whole large files. Patch windows below are at most 60 lines.
Donor paths exist in the baseline; generated machine/invariant/soundness/test
paths below are deliverables, absent on an artifact-only planning tree.
Do not rediscover prototype implementation from separate source reads.

| Group | Production theorem declarations | New constructions / fixture declarations | Mutation cycles | Main rejection risk |
| --- | ---: | ---: | ---: | --- |
| 01 machine | 2 support lemmas | 0 / 0 | 0 here | Three transition premises, dependent tags, complete-store boundary |
| 02 invariants + soundness | 16 including helpers; seven printed generic results | 0 / 0 | 12, run AFTER 02 | Conservation, read stability, uniqueness/failure implications |
| 03 fixtures + integration | 0 | 12 / 33, including helpers and reachability witnesses | 12 fixture contrasts; separate manifest | Fixture discriminators, eligibility versus absence, discovery/docs |

These are not 33 independent regressions or 12 runtime oracle kills.
All 12 ORIGINAL production mutation entries belong to `02-invariants-soundness` and target
`LeanNCD.Semantics.Soundness`; Task 03 fixtures are not needed for them.
The controller's separate Task 03 manifest adds 12 fixture contrast controls,
one per construction, targeting `Semantics.ReferenceMachineTest`. These are NOT
12 new implementation regressions. Keep prototype evidence/original manifest
at 12; controller results distinguish 12 production proof/type rejections from
12 fixture contrasts, rather than relabeling them as 24 independent regressions.
Budget Task 02 by TWELVE mutate/build/restore/rebuild cycles, not patch lines.
Recommend a production application/build/review/commit handoff, followed by
controller verification, to keep its implementer within 60 turns. This splits
execution responsibility, not the three-group patch design, and authorizes no
redesign. Task 03 is twelve constructions, 33 declarations, and TWELVE contrast
cycles, not 33 cycles. Hand off controller contrast verification after the
fixture target build if needed to keep the implementer within 60 turns.

Implementation dispatch target about 40 turns; absolute approximately 60 turns
and 250k context peak. If predicted over, hand off the exact committed sources,
identifiers, and pending gates; never run a second design pass. Slice execution
cap about 175M cumulative input tokens; authoring target about 50M.
This artifact-only authoring request is narrower: about 25 turns / 100k peak.
Measure with the repository token-report helper when supported; if unavailable,
report unavailable telemetry, not verified compliance. Report every breach.
Long builds should run attached in the background with completion notification,
not repeated polling. No agents are launched by this authoring turn.

Prototype budget evidence conflicts: checkpoint reports 76 tool calls plus one
checkpoint write, versus an earlier manual 48 assistant-tool-turn estimate.
The transcript helper found no transcript. Tool calls and turns differ; the
earlier estimate and "no known breach" field do not certify compliance. If tool
calls were the intended counter, 76 already exceeded 60 by 16 before the write.
Peak/cumulative prototype tokens are unavailable. Carry this qualification into
the authoring and eventual execution records rather than silently averaging it.

## 5. Task 01 -- relation-only machine

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Prerequisite: Section 3 passed, warm LeanNCD refresh. Files:
`leanncd/LeanNCD/Semantics/Machine.lean`, created by
[patch 01](reference_machine_patches/01-machine.patch).
Identifiers @ that file: `Accumulator`, `Pending`, `Running`, `MachineState`,
`initial`, `consume`, `publish`, `FiberEmpty`, `Step`, `Reaches`, `Complete`,
`Blocked`, `Successful`, `finalStore`, `failed_terminal`, `finalStore_published`.
Patch windows 1-50, 51-95; source windows 40-60 lines.
Prior art: `Program`, `Defined`, `Occurrence`, `body`, `destination` @
[Program.lean](../../leanncd/LeanNCD/Semantics/Program.lean);
`Input`, `ValidInput`, `Models` @
[Models.lean](../../leanncd/LeanNCD/Semantics/Models.lean);
`evalReady` @ [Readiness.lean](../../leanncd/LeanNCD/Semantics/Readiness.lean).
Immediate callers are Task 02's `Invariant`, `StateInvariant`,
`reachable_invariant`, and `successful_model`, not a new scheduler.

Three work items: replay typed running/failure representation and initialization;
replay the three rules and tagged updates; replay reachability/completion and
terminal/extraction support lemmas. Do not add history to Running.

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/reference_machine_patches/01-machine.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/reference_machine_patches/01-machine.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD.Semantics.Machine
```

Per-task review rejects: missing pending/readiness/publication premise,
input-write rule, automatic empty-fiber publication, destructive publish,
collapsed valuation tags, failure snapshot mutation, output-only completion,
model/rank success premise, or executable-scheduler claims.
Review must pass/adjudicate before explicit staging and commit:

```bash
/usr/bin/git -C <execution-worktree> add <execution-worktree>/leanncd/LeanNCD/Semantics/Machine.lean
/usr/bin/git -C <execution-worktree> commit -m "feat(semantics): define tagged reference machine" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## 6. Task 02 -- invariants and successful/failed-run soundness

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Prerequisite: 01 reviewed/committed. Files:
`leanncd/LeanNCD/Semantics/Invariants.lean` and
`leanncd/LeanNCD/Semantics/Soundness.lean`, created by
[patch 02](reference_machine_patches/02-invariants-soundness.patch).
Patch windows 1-55, 56-110, 111-165, 166-220, 221-275, 276-326.
Identifiers @ Invariants deliverable: `Extends`, `Agrees`, `agrees_of_extends`,
`evaluated_consistent`, `History`, `spent`, `record`, `spent_consume_same`,
`Invariant`, `initial_invariant`, `publish_extends`, `consume_invariant`,
`publish_invariant`, `StateInvariant`, `reachable_invariant`.
Identifiers @ Soundness deliverable: `finalStore_agrees`, `successful_model`,
`finished_accumulator`, `CandidateAgreement`, `candidate_preserved`,
`successful_unique`, `successful_admInput`, `successful_denotation`,
`failed_no_model`.
Unchanged callers/helpers: `ready_consistent`, `checkReads_iff` @
[Readiness.lean](../../leanncd/LeanNCD/Semantics/Readiness.lean);
`outcome`, `AdmEnv`, `contribution`, `collect` @
[Program.lean](../../leanncd/LeanNCD/Semantics/Program.lean);
`pushforward` @ [Collection.lean](../../leanncd/LeanNCD/Semantics/Collection.lean);
`Models`, `AdmInput`, `denotation_of_model` @
[Models.lean](../../leanncd/LeanNCD/Semantics/Models.lean).

Three work items: proof-only consumed-value conservation and stable interpretation;
initial/rule/reachability invariants; complete model plus preservation-derived
uniqueness/denotation and reached-failure exclusion. Preserve exact Section 2
hypotheses. No existential supplied model in the successful soundness input.

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/reference_machine_patches/02-invariants-soundness.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/reference_machine_patches/02-invariants-soundness.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD.Semantics.Soundness
```

Per-task proof review rejects weakened conservation, hidden history caller
premises, extra algebra, rank/model-premised success, uniqueness only of outputs,
failure exclusion without reachability/readiness, dependence on unrelated
sorry axioms, or replacing pushforward semantics. Accept only the axiom inventory
in Section 2. After production review, commit and hand off the SAME replay:

```bash
/usr/bin/git -C <execution-worktree> add <execution-worktree>/leanncd/LeanNCD/Semantics/Invariants.lean <execution-worktree>/leanncd/LeanNCD/Semantics/Soundness.lean
/usr/bin/git -C <execution-worktree> commit -m "feat(semantics): prove reference machine soundness" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

Controller verification brief also begins with Section 4's verbatim preamble.
Phase-two identifiers: `Step`, `consume`, `publish`, `Complete`, `initial` @
Machine deliverable; `consume_invariant`, `publish_invariant`,
`reachable_invariant` @ Invariants deliverable; `successful_model`,
`candidate_preserved`, `successful_unique`, `failed_no_model` @ Soundness
deliverable; `M01`-`M12` labels @
[post manifest](reference_machine_mutations_post.json).
No new fixtures/code are designed in this verification handoff.

```bash
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --check <execution-worktree>/leanncd <execution-worktree>/papers/semantics/reference_machine_mutations_post.json
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --out <controller-session-artifacts>/reference_machine_task02_mutation_results.md <execution-worktree>/leanncd <execution-worktree>/papers/semantics/reference_machine_mutations_post.json
/usr/bin/git -C <execution-worktree> diff --exit-code HEAD -- leanncd
/usr/bin/git -C <execution-worktree> status --short
```

Require all 12 selected and PASS: intended diagnostic, byte-identical restore,
restored green build; no prefix filter, missing entry, or silent skip.
`--check` validates anchors/schema only, NOT the actual suite.
Prototype populated `expect` strings match observed failure segments, but all
12 cycles were NOT rerun after population. Independent populated-manifest
execution is therefore essential. If anchors/expectations fail, STOP and report;
do not casually loosen expect strings or rewrite patches to manufacture green.

| Mutation | What the observed rejection establishes |
| --- | --- |
| M01 | Publication barrier premise is needed by invariant proof |
| M02 | No-overwrite premise is needed by invariant proof |
| M03 | Pending membership is needed for consumption conservation |
| M04 | Defined evaluation, not undefined evaluation, is required |
| M05 | Exact erasure is needed by spent conservation |
| M06 | Contributed value cannot silently become zero |
| M07 | Prior accumulator must be retained |
| M08 | Published value must equal accumulator |
| M09 | Publication retains accumulator invariant |
| M10 | notReady cannot replace ready failure |
| M11 | Output-only completion fails complete-store extraction/type boundary |
| M12 | Valuation filtering fails initial consumed-outcome invariant |

All TWELVE are proof/type rejections before fixture execution, with ZERO runtime
oracle kills. They test semantic/proof interfaces but are not twelve independent
fixture regressions; some are killed by proof applications to changed premises.

## 7. Task 03 -- fixtures, discovery, and bounded documentation integration

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Prerequisite: 02 production reviewed/committed AND controller actual cycles pass.
Controller supplies and publishes the separate
[fixture contrast manifest](reference_machine_fixture_mutations_post.json).
Its exact labels/anchors/observed diagnostics are controller-owned; this plan
does not invent them. Missing or unverified manifest is a readiness STOP.
Files from [patch 03](reference_machine_patches/03-fixtures-integration.patch):
new `leanncd/test/Semantics/ReferenceMachineTest.lean`;
existing [Semantics.lean](../../leanncd/LeanNCD/Semantics.lean),
[lakefile.toml](../../leanncd/lakefile.toml),
[semantic AGENTS.md](../../leanncd/LeanNCD/Semantics/AGENTS.md), and
[leanncd AGENTS.md](../../leanncd/AGENTS.md).
Patch windows 1-55, 56-110, 111-165, 166-220, 221-275, 276-330, 331-385,
386-400. Fixture namespace is `LeanNCD.Semantics.ReferenceMachineFixtures`.

Identifiers @ ReferenceMachineTest deliverable: ALL construction and theorem
identifiers in the following two tables, plus `emptyInput`, `dtag`, `dinput`,
`d0`-`d5`, `ctag`, `c012`, `c210`, `n0`, `n1`, `zo`, `z0`, `z1`, `bo`,
`binput`, `b0`, `e0`, `po`, `p0`-`p2`, `wo`, `w0`, `yinput`, `y0`-`y2`,
`cycleStore`, `r0`-`r2`, `vo`, `v0`, `v1`, `scalarDeclarations`,
`scalarInput`, `s0`, `s1`, `readinessLabel`.
Discovery identifiers: `LeanNCD.Semantics.Soundness` import @
[Semantics.lean](../../leanncd/LeanNCD/Semantics.lean);
`Tests.globs` / `Semantics.ReferenceMachineTest` @
[lakefile.toml](../../leanncd/lakefile.toml);
semantic validation / machine guidance @ both linked AGENTS files.
Existing umbrella reachability through
[LeanNCD.lean](../../leanncd/LeanNCD.lean) is preserved, not replaced.

Three work items: replay the twelve constructions/33 declarations; verify the
case-by-rule and construction discriminators with controller contrast controls
without overstating them; wire umbrella/default discovery and classify
documentation sweep hits.
Donor file key D is
[CollectionModelTest.lean](../../leanncd/test/Semantics/CollectionModelTest.lean).
Donor file key E is
[ExpressionTest.lean](../../leanncd/test/Semantics/ExpressionTest.lean).
Qualified `CollectionModelFixtures.*` donors are @ D; `Fixtures.*` donors @ E.
Do not invent a fixture beyond this compiled set without controller adjudication.

### Twelve constructions and discrimination

| Construction @ new fixture file | Explicit donor and change | Distinguishes / limitation |
| --- | --- | --- |
| `duplicate` | Clone `CollectionModelFixtures.duplicate` @ D with `Fixtures.ops/point` @ E; consume both statement tags, publish all three coordinates, compare reverse order | Equal bodies/destination still sum to 4; barrier after one consume; complete reached success derives model without witness |
| `collision` | Clone `CollectionModelFixtures.collision` @ D; orders 0,1,2 and 2,1,0 | Unequal values 2,7,5; destination zero is 9, not dedup/overwrite; accumulator equality, not separately reached full runs |
| `noStatements` | Clone `CollectionModelFixtures.noStatements` @ D; explicitly publish coordinate one | No consume exists; legal publication makes `some 0` |
| `zP` | Clone `CollectionModelFixtures.partialProgram true true` @ D | Ready zero still legally consumes and erases exact tag |
| `badP` | Clone `CollectionModelFixtures.partialProgram true false` @ D | Pending ready undefined: located unchanged-snapshot failure, tag retained, terminal, reached failure excludes models |
| `excludedP` | Clone `CollectionModelFixtures.partialProgram false false` @ D | Same undefined family but guard excluded: no admitted occurrence; no separate publication theorem |
| `dependentP` | Clone `CollectionModelFixtures.expressionProgram` @ D plus `Fixtures.direct` @ E; literal into zero, dependent read into one | Accumulator 2 while notReady, then explicit publication enables evaluated some 2; legal publication/contribution witnesses |
| `waitingBad` | Clone expressionProgram @ D with `Fixtures.direct` and `Fixtures.bad` @ E in ONE strict binary body | Both unavailable read and primitive failure present, so notReady must dominate undefined |
| `cycleP` | Clone expressionProgram @ D with `Fixtures.direct` @ E; self-read zero, publish unrelated empty fibers one/two | Blocked state AND complete zero model; NOT a separate reachability theorem for those publications |
| `roleProgram` | Clone `CollectionModelFixtures.roleProgram/supplied/presentEmpty` @ D; publish output then internal nonoutput | Output alone not complete; empty input presence supplied by validated donor, not vacuous cell agreement |
| `valuationP` | Adapt `CollectionModelFixtures.expressionProgram/duplicate` @ D to one statement/two admitted valuations, identical literal/destination | Erase valuation zero while valuation one remains; not dedup by statement/body |
| `scalarRole` | Clone roleProgram/roleDeclarations @ D; replace empty input shape with scalar, supply 7, publish defined scalar | Actual input cell immutable and `some 7`; defined cell initially none |

### Thirty-three top-level named theorem declarations

Each identifier below is @ the ReferenceMachineTest deliverable; conjunctions
count once. Helpers/reachability witnesses ARE included. Imported donor theorems,
`def` helpers, `#eval`, and `#print` commands are excluded.

| Construction | Named theorem declarations |
| --- | --- |
| duplicate (11) | `duplicate_pending_empty`, `duplicate_barrier`, `duplicate_erased`, `duplicate_sum`, `duplicate_order`, `duplicate_complete`, `duplicate_success`, `duplicate_model_without_witness`, `duplicate_unique_among_all_models`, `published_not_overwritable`, `publication_retains_accumulator` |
| collision (2) | `collision_order`, `collision_sum` |
| noStatements (2) | `empty_fiber_publication`, `unwritten_zero` |
| zP (1) | `zero_consumed` |
| badP (4) | `located_failure`, `failure_retains_tag`, `failure_terminal`, `failure_excludes_models` |
| excludedP (1) | `excluded_no_occurrence` |
| dependentP (4) | `dependent_waits`, `dependent_reads_published`, `dependent_publication`, `dependent_contribution` |
| waitingBad (1) | `unavailable_dominates_undefined` |
| cycleP (2) | `cycle_model`, `cycle_blocked` |
| roleProgram (2) | `nonoutput_required`, `empty_input_and_nonoutput_complete` |
| valuationP (1) | `valuation_multiplicity` |
| scalarRole (2) | `immutable_input`, `input_present_and_defined_absent` |

The duplicate barrier, erased-tag, and overwrite assertions test constructor
eligibility PREMISES, not separate labeled-transition absence theorems.
Legal Step witnesses and generic invariants pin their use; do not relabel those
premise checks as direct "no CONTRIBUTE"/"no PUBLISH" transition regressions.
`cycle_blocked` does directly quantify over all Step constructors, but the
particular `y2` blocked fixture is not separately proved reachable.

### Case x rule audit: required, forbidden, silently ignored

"Required" means the intended legal rule/obligation, not forced scheduling or
progress. Forbidden statements apply at the stated coordinate/tag and, for
exhausted published fibers, reachable invariant states. Audit unchanged
siblings, not just changed hunks: `Occurrence`/`outcome`/`AdmEnv`/`collect` @
[Program.lean](../../leanncd/LeanNCD/Semantics/Program.lean);
`ValidInput`/`Models`/`AdmInput` @
[Models.lean](../../leanncd/LeanNCD/Semantics/Models.lean);
strict `interpret` @ [Interpret.lean](../../leanncd/LeanNCD/Semantics/Interpret.lean);
`evalReady`/`checkReads` @ [Readiness.lean](../../leanncd/LeanNCD/Semantics/Readiness.lean);
existing expression/completeness and default Expression/Native/Contract tests.
Their APIs/contracts are preserved; legacy executors are not claimed to implement
this machine. Check rule premises at call sites as well as predicate definitions.

| Case | CONTRIBUTE | PUBLISH | UNDEFINED |
| --- | --- | --- | --- |
| Pending ready defined body | Required legal rule | Forbidden at pending destination fiber | Forbidden |
| First duplicate consumed | Required for remaining ready tag | Forbidden shared destination | Forbidden literal |
| Same consumed tag selected again | Forbidden | Depends on remaining tags | Forbidden consumed tag |
| Unwritten defined coordinate | Silently ignored: no occurrence | Required explicit available zero | Silently ignored: no occurrence |
| Already published coordinate | Forbidden exhausted fiber on reachable states | Forbidden overwrite | Forbidden exhausted fiber |
| Populated unpublished dependency | Forbidden dependent body | Required if dependency fiber exhausted | Forbidden: notReady |
| Ready zero body | Required exact-tag erasure | Forbidden before consume at destination | Forbidden |
| Pending ready undefined primitive | Forbidden | Forbidden at pending destination | Required located failure, unchanged snapshot |
| Unavailable read plus undefined primitive | Forbidden | Not an expression rule; unrelated eligible cells unaffected | Forbidden: unavailable dominates |
| Guard-excluded undefined body | Silently ignored: no admitted occurrence | Required empty-fiber publication where exhausted | Silently ignored: no admitted occurrence |
| Empty supplied input tensor | Silently ignored: no defined/input-write occurrence | Forbidden: input is not a defined target | Silently ignored: no coordinates |
| Unpublished defined nonoutput | Depends on body tags | Required for completion | Depends on pending ready failure only |
| Cyclic blocked state with model | Forbidden unavailable reads | Forbidden remaining cyclic destination | Forbidden: blocking is not undefinedness |
| Failed state | Forbidden | Forbidden | Forbidden |

Classify every additional silently ignored cell; do not silently widen scope.
The table is a semantic audit, not a claim that all cells have independent proofs.

### Replay, discovery, and documentation commands

The second manifest must select all 12 fixture contrasts, exactly one mapped to
each construction in the table, and target `Semantics.ReferenceMachineTest`.
Controller must observe each intended diagnostic and byte-identical restoration
plus restored green build. No label/prefix filter, silent skip, or claim that
generic production-proof kills validate these fixture constructions independently.
Contrasts may be rejected by fixture proofs/types; they are not runtime scheduler
tests or evidence of 12 additional implementation defects.

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/reference_machine_patches/03-fixtures-integration.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/reference_machine_patches/03-fixtures-integration.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd Semantics.CollectionModelTest Semantics.ReferenceMachineTest
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --check <execution-worktree>/leanncd <execution-worktree>/papers/semantics/reference_machine_fixture_mutations_post.json
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --out <controller-session-artifacts>/reference_machine_task03_fixture_contrast_results.md <execution-worktree>/leanncd <execution-worktree>/papers/semantics/reference_machine_fixture_mutations_post.json
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD Tests
rg -n '^theorem ' <execution-worktree>/leanncd/test/Semantics/ReferenceMachineTest.lean
rg -n 'LeanNCD.Semantics|LeanNCD.Semantics.Soundness' <execution-worktree>/leanncd/LeanNCD.lean <execution-worktree>/leanncd/LeanNCD/Semantics.lean
rg -n 'defaultTargets|name = "Tests"|Semantics.ReferenceMachineTest' <execution-worktree>/leanncd/lakefile.toml
rg -n '8686|8690|8694|8695|12.*construction|33.*(assertion|theorem|declaration)|12.*mutation|12.*contrast|24.*(mutation|regression)|zero.*runtime|runtime.*kill' <execution-worktree>/papers <execution-worktree>/leanncd
rg -n 'operational machines|publication.*deferred|reference.machine|ranks|termination|progress|scheduler|cyclic|unique.model|soundness' <execution-worktree>/papers <execution-worktree>/leanncd/AGENTS.md <execution-worktree>/leanncd/LeanNCD/Semantics/AGENTS.md
rg -n 'empty input|input presence|nonoutput|non-output|ScalarOps|AddCommMonoid|pushforward|categorical|backend|source elaboration' <execution-worktree>/papers <execution-worktree>/leanncd/LeanNCD/Semantics/AGENTS.md
```

Prototype observations, not permanent build-count requirements: historical full
default build 8694 jobs; donor collection evaluation `[4, 9, 0, 0, 9, 5, 14, 3 / 4]`;
new readiness labels `["notReady", "notReady", "undefined"]`, donor labels
`["undefined", "notReady"]`. State-update values are kernel-checked assertions,
not runtime scheduler traces. Verify actual outputs, declaration count 33,
umbrella reachability and default Tests inclusion, not just isolated targets.
Controller reports later-main full rehearsal at `2e850b1` passed with 8695 jobs
and unchanged sequential patches preserved unrelated advanced-main changes.
This reported observation does not fill the controller-owned status record or
complete the new contrast/review gates; controller records final verification.

Classify ALL documentation sweep hits, including values outside changed docs.
Historical collection/spike/readiness gaps remain historical, not rewritten as
current inventories. New scoped guidance may remove publication from current
deferrals, but must retain scheduling/progress/termination/cyclic-solver and
general model-existence exclusions. The patch does not change the authority
paper. Any necessary additional current-doc correction requires explicit
controller adjudication and review, not unrecorded patch rewriting or a new
heavyweight docs task.

Per-task review rejects missing donors/discriminators, counts described as
independent regressions, mutation claims as runtime kills, cyclic reachability
overclaims, empty input presence inferred only from no cells, missing nonoutput
completion, source/runtime confusion, stale current discovery claims, or
unqualified historical gaps. Require controller's actual second-manifest run
and 12/12 contrast mapping/restoration results, not `--check` alone, before
passing Task 03. Stage only these five task files after review:

```bash
/usr/bin/git -C <execution-worktree> add <execution-worktree>/leanncd/test/Semantics/ReferenceMachineTest.lean <execution-worktree>/leanncd/LeanNCD/Semantics.lean <execution-worktree>/leanncd/lakefile.toml <execution-worktree>/leanncd/LeanNCD/Semantics/AGENTS.md <execution-worktree>/leanncd/AGENTS.md
/usr/bin/git -C <execution-worktree> commit -m "test(semantics): cover reference machine and wire discovery" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## 8. Controller gates, final reviews, and local-only integration

This section names REQUIRED future controller work, not authoring achievements.
The controller independently verifies ordered patch applicability, protected
inputs, both manifests' populated expectations and separate classifications,
full/default discovery build,
observed fixture outputs/counts, and accepted axiom inventories in a disposable
replay checkout. Two final whole-branch reviews follow; both start with Section
4's preamble, receive exact identifiers/windows, and preserve findings
incrementally in controller session artifacts. Per-task reviews do not replace
these whole-branch reviews.

1. **Proof-semantic lens:** Section 2, Invariant/spent/consumed,
   successful_model/finished_accumulator/candidate_preserved, complete-model
   uniqueness and failure exclusion. Reject rank/model-premise weakening,
   extra algebra, loss of genuine pushforward, unproved conservation,
   output-only uniqueness, or confusing blocking with failed nonexistence.
2. **Transition/type/fixture/discovery lens:** Step/consume/publish/initial/
   Complete, Section 7 discriminators/audit, dependent tags and input presence,
   failure locator/snapshot/terminality, actual mutation diagnostics/restoration,
   import/default glob, docs and protected-source/absence guards. Reject
   premise-only assertions oversold as transition-absence proofs, unreachable
   cyclic fixture oversold as a reached-run theorem, missing discovery, or
   runtime-independence claims unsupported by kernel proof fixtures.

Stop on a load-bearing unfixable finding or patch/spec defect; do not improvise
outside the verified artifacts. Controller explicitly adjudicates every finding.
No author may predeclare either independent review complete.

At execution close-out the controller itself runs BOTH populated actual suites
again on the final branch, then the full build, with no skipped entries:

```bash
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --check <execution-worktree>/leanncd <execution-worktree>/papers/semantics/reference_machine_mutations_post.json
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --out <controller-session-artifacts>/reference_machine_final_mutation_results.md <execution-worktree>/leanncd <execution-worktree>/papers/semantics/reference_machine_mutations_post.json
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --check <execution-worktree>/leanncd <execution-worktree>/papers/semantics/reference_machine_fixture_mutations_post.json
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --out <controller-session-artifacts>/reference_machine_final_fixture_contrast_results.md <execution-worktree>/leanncd <execution-worktree>/papers/semantics/reference_machine_fixture_mutations_post.json
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd
/usr/bin/git -C <execution-worktree> diff --exit-code 53bcbbd610a1791a5a769a40e33fd47b5a3abc7e -- leanncd/LeanNCD/Semantics/Types.lean leanncd/LeanNCD/Semantics/Expr.lean leanncd/LeanNCD/Semantics/Interpret.lean leanncd/LeanNCD/Semantics/Readiness.lean leanncd/LeanNCD/Semantics/Completeness.lean leanncd/LeanNCD/Semantics/Collection.lean leanncd/LeanNCD/Semantics/Program.lean leanncd/LeanNCD/Semantics/Models.lean leanncd/test/Semantics/ExpressionTest.lean leanncd/test/Semantics/CollectionModelTest.lean papers/semantics/tensor_logic_semantics.md leanncd/scripts/lake-build.sh leanncd/scripts/lean-file.sh leanncd/scripts/mutation-manifest.sh leanncd/scripts/mutation-cycle.sh .claude/skills/new-slice/prepare-worktree.sh
/usr/bin/git -C <execution-worktree> diff --exit-code HEAD -- leanncd
/usr/bin/git -C <execution-worktree> status --short
```

The explicit protected-source command checks all 16 replay-audit inputs against
the base, including working-tree changes. It deliberately excludes the eight
authorized deliverables/integration files, NOT unrelated protected code.
Require empty tracked-source diff after mutations and clean status. Preserve
result tables in session artifacts and reference them in the execution record;
never commit disposable ledgers, temporary logs, or `.claude/settings.json`.

Controller writes future `papers/semantics/reference_machine_execution_record.md`
ONLY during execution; do not create it now. Record exact actual commands,
12 selected/PASS production proof/type cycles AND 12 selected/PASS fixture
contrasts with one-per-construction mapping; no new implementation-regression
claim, zero production runtime kills, and separate restoration verdicts;
fixture counts/outputs, axiom inventories, warnings, per-task/final review
dispositions, protected-input guards, successful rehearsal base and per-patch
hunk/new-blob validation, measured budget or unavailable telemetry, breaches,
and deferred limitations. Stage that resolved record explicitly if authorized.

PLAN-ARTIFACT integration is separate from implementation release. After the
controller's independent disposable replay verification, green full build, and
clean/adjudicated plan whole-branch reviews, it may publish ONLY artifacts on
this controller branch and integrate that artifact-only branch into local main.
Do not merge the implementation candidate. Explicit artifact stage list:

```bash
/usr/bin/git -C <controller-worktree> add <controller-worktree>/papers/semantics/reference_machine_plan.md <controller-worktree>/papers/semantics/reference_machine_authoring_record.md <controller-worktree>/papers/semantics/reference_machine_artifacts/evidence.json <controller-worktree>/papers/semantics/reference_machine_artifacts/replay-audit.json <controller-worktree>/papers/semantics/reference_machine_artifacts/emit-patches.py <controller-worktree>/papers/semantics/reference_machine_artifacts/controller_replay_audit.json <controller-worktree>/papers/semantics/reference_machine_artifacts/controller_mutation_results.md <controller-worktree>/papers/semantics/reference_machine_artifacts/controller_fixture_mutation_results.md <controller-worktree>/papers/semantics/reference_machine_patches/01-machine.patch <controller-worktree>/papers/semantics/reference_machine_patches/02-invariants-soundness.patch <controller-worktree>/papers/semantics/reference_machine_patches/03-fixtures-integration.patch <controller-worktree>/papers/semantics/reference_machine_mutations_post.json <controller-worktree>/papers/semantics/reference_machine_fixture_mutations_post.json
/usr/bin/git -C <controller-worktree> commit -m "docs(semantics): prepare reference machine soundness plan" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
/usr/bin/git -C <controller-worktree> status --short
```

Before artifact integration, rerun Section 3's base-source and new-output absence
guards on the controller branch, require only the explicit artifact changes in
the planning branch's own topic diff, and require a controller green full build
of its planning tree too. "Artifact-only" describes this branch's contribution,
not the receiving main or all commits since the original prototype base.
Preserve compatible landed main edits during local integration; do not demand
that the receiving main's whole leanncd tree equal the old prototype baseline.
Authoring record is the final status authority, not a guessed readiness sentence.

A later IMPLEMENTATION release requires completed task gates, controller final
actual suite/full build, and both whole-branch reviews clean/adjudicated. Only
then locally merge THAT execution branch to main under the repository finish
protocol. Template for either separately authorized integration, using its OWN
branch/worktree and primary checkout already on clean local main:

```bash
/usr/bin/git -C <primary-checkout> status --short
/usr/bin/git -C <primary-checkout> rev-parse main
/usr/bin/git -C <primary-checkout> merge --no-ff <completed-branch>
/usr/bin/git -C <primary-checkout> merge-base --is-ancestor <pre-merge-main-commit> main
/usr/bin/git -C <primary-checkout> merge-base --is-ancestor <completed-branch> main
/usr/bin/git -C <primary-checkout> diff --stat <pre-merge-main-commit> main
/usr/bin/git -C <completed-worktree> status --short
/usr/bin/git -C <primary-checkout> worktree remove <completed-worktree>
/usr/bin/git -C <primary-checkout> branch -d <completed-branch>
```

Record `rev-parse main` as `<pre-merge-main-commit>` before merging. Before
cleanup, verify the resulting topic hunks/new-file blobs against that captured
main and the accepted task artifacts, retaining unrelated main changes.
Ancestry checks establish integration of both histories; they do not replace
those content checks. Whole-tree equality with an older completed branch is
not required and would falsely reject compatible main advancements.

Exit the completed worktree/session with keep first. No force-removal of unknown
dirty files; inspect and preserve unrelated work. Never substitute the prototype
or an f32 branch/worktree. Do not push; report local main ahead of origin if so.
