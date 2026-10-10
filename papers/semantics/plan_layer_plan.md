# Part V Plan layer, slice 1: execution plan

Live plan. Records (authoring facts, close-out) go in `papers/semantics/plan_layer_record.md`.
Inputs this plan was written from, and the only sources it cites:
`papers/semantics/plan_layer_artifacts/{CHECKPOINT,a1_notes,a2_notes,a3a_notes,a3b_notes}.md`,
`papers/semantics/plan_layer_patches/manifest.json`, `papers/semantics/plan_layer_artifacts/evidence.json`.
Citations below read `a2 §Decision log 3` = `a2_notes.md`, section "Decision log", item 3.

**Process weight: Full path.** This slice adds a new subsystem (8 modules under
`leanncd/LeanNCD/Semantics/Plan/`, a new namespace, a new validity checker) and a soundness surface
(`checkPlan_sound`, the simulation relation R, Lemma 31.2, Theorem 31.3) that no existing
differential oracle sees: three schedule-invalid plans run to `done`, two with wrong values
(a3a §Defect audit N4), so a wrong checker is a silent wrong answer. Five tasks plus a docs sweep.
The prototype phase (A1-A3b) and per-task patch emission are already done; execution is
apply + build + commit per task (slice-plan §6).

## 1. Goal and scope

Land the slice-1 Plan layer of spec Part V: a concrete plan syntax over a program, a dense
slot memory with a published-only read view, singleton-command step kernels, a computable
checker `checkPlan` for Definition 31.1 (slice-1 form), and the proofs of Lemma 32.1
(`batch_execution`), step simulation (`step_R`, `step_failed`), progress (`step_not_stuck`), the
run lemma (`run_R`), Lemma 31.2 (`terminal_adequacy`) and Theorem 31.3 (`done_correct`,
`failed_correct`, `done_or_failed`, `done_of_model`, `done_iff_model`). Then restate the spec's
Definition 31.1 / relation R / Lemma 31.2 / Theorem 31.3 to match what is proved.

### Global Constraints (exact values)

- Namespace: `LeanNCD.Semantics.Program.Plan`. The plan structure is
  `_root_.LeanNCD.Semantics.Program.Plan` declared inside that namespace, so `P.Plan` and
  `π.ann` resolve (a1 §Decision log 1).
- Module files (manifest.json): `leanncd/LeanNCD/Semantics/Plan/{Syntax,Batch,Memory,Step,Simulation,Validity,Run,Correctness}.lean`,
  aggregator `leanncd/LeanNCD/Semantics/Plan.lean`, imported by `leanncd/LeanNCD/Semantics.lean`.
- Tests: 7 test modules `leanncd/test/Semantics/Plan{Batch,Memory,Step,Simulation,Validity,Run,Correctness}Test.lean`
  plus `leanncd/test/Semantics/PlanFixtures.lean`, all 8 named in the `Tests` globs of
  `leanncd/lakefile.toml` (counted from manifest.json T5 and the patched lakefile).
- Slice-1 profile (CHECKPOINT §2; a2 §Decision log 1-3):
  - singleton commands: `Singleton π`, every command is `[a]`; anything else steps to `stuck`;
  - transactional failure: `execAcc` evaluates every member on the read view, commits only if all
    succeed; a failure reports `failed o pc M` with the PRE-step memory;
  - one sort in the fixtures: the theorems are generic over the sort family `K : S → Type`
    (hypotheses: an `AddCommMonoid` per defined sort and `ops`); only the fixtures and the decision
    profile use one sort, the exact rational reference (donors from
    `Semantics.ExecutableReferenceTest`);
  - dense, non-reused buffers: one slot per address, `place` injective, no aliasing or retirement;
  - explicit `initZero`: no implicit materialisation; a slot is `none` until an `initZero`;
  - no implementation errors: the step result has `ok`, `stuck`, `semFail` only.
- Axioms: no `sorry`, `admit`, `axiom`, `native_decide` in any shipped file (evidence.json
  `forbidden_token_grep`: 18 files, 0 hits). Printed axiom sets are `[propext, Quot.sound]` or
  `[propext, Classical.choice, Quot.sound]`, the same set as `result_failure` (a1-a3b §`#print axioms`).
- Checker shape: `checkPlan` is one Bool per `Valid` clause in field order; only soundness
  (`checkPlan = true → Valid`) is proved; completeness is not (a3a §Decision log 2).

### What this slice does NOT do (owner: a later Plan-layer slice unless noted)

- Non-singleton (fused) commands; Order4 for fused commands must refer to expanded positions
  (a2 §Decision log 9). Owner: slice 2 (fusion).
- Fixtures over more than one sort, or numeric kernels other than the exact reference (the theorems
  themselves are already sort-generic); floating point (path doc §5.2).
- Buffer reuse, aliasing, retirement, liveness for scans (spec 30.3 retirement half).
- Implementation errors (allocation failure, kernel errors) and their matching.
- Checker completeness (`Valid → checkPlan = true`) (a3a §Decision log 2).
- Proving the A2 conjecture that per-step `AccOK`/`PubOK` imply the Nodup halves of
  Coverage1/2 (a2 §ValidityConditions; a3a §Decision log 6). `checkCov1Nodup`/`checkCov2Nodup` stay.
- Dropping `checkCov1Complete` (CHECKPOINT §3 decision 3; a3b §Decision log 7): kept; redundant
  at `checkPlan` (N6) but consumed by `complete_of_refState`; see Open items.
- Comparing failure occurrence or snapshot between plan and executor (D5).

## 2. Decisions (each cites its source)

| id | decision | source |
|---|---|---|
| D1 | R keeps reachability (R1); used via conservation (`acc_zero_of_unconsumed`, `dest_not_pub`) | a1 §Spec defects; a2 §Defect audit D1 |
| D2 | the layout view `SlotView π pc` depends on pc and commands only, not the reference state | a1 §Spec defects D2 |
| D3 | R2 stated as iff-equations (`o ∈ pending ↔ ¬Cons pc`, `isSome ↔ Pub pc`) | a1 §Spec defects D3 |
| D4 | "implements the annotations" is redundant: `refState_succ_single` and the step lemmas produce `refState (pc+1)` | a2 §Defect audit D4 |
| D5 | transactional failure: the matching segment is one `undefined` event from Conf for the same occurrence `o` (`step_failed`, `run_R`); Theorem 31.3 (b) claims only failure + no-model; the gap is the snapshot versus `Executor.run`'s own schedule (executor accumulator 2 vs plan 0 on failureAfter) | a2 §Defect audit D5; a3b §Decision log 4; review_fidelity F1 |
| D6 | Decode is partial; its success belongs to Lemma 31.2 (`decode_of_R`, `terminal_adequacy`) | a1 §Spec defects D6; a3b §Theorems |
| D9 | condition 1 covering follows from conditions 2 and 4: `accFlat_complete` (substantive), `cov1_of_cov2_pubOrder` (Valid-level corollary) | a2 §Defect audit D9; a3b §Theorems |
| D10 | `batch_execution` premises: `G.Nodup`, G ⊆ pending, readiness, per-member success; Nodup is the list form of "G is a set" | a1 §Spec defects D10 |
| N1 | every pub member must be materialised first, including empty fibers (`PubOK`: `x ∈ Mat pc`) | a1 §Spec defects N1; a2 §Defect audit N1 |
| N2 | initZero freshness (`InitOK`): no target published, no consumed occurrence targets it; safety-critical (`reinitMid`) | a2 §Defect audit N2; a3a §Defect audit N2 |
| N3 | condition 3 (footprint ⊆ Pub) is a progress premise only (`ready` field) | a2 §Defect audit N3; a3a §Decision log 4 |
| N4 | `runPlan` does not detect schedule-invalid plans; soundness rests on `checkPlan` | a2 §Defect audit N4; a3a §Defect audit N4 |
| N5 | A2 mutants b and e: no fixture or run outcome distinguishes them on `checkPlan`-valid plans (b: on all plans). `StepResult.semFail` carries no memory and `runFrom` reports the pre-step memory (`PlanOutcome.failed` does carry it); e needs `dest_not_pub`, `acc_slot_isSome`, so it fails on invalid plans (Open items 10) | a2 §Mutation controls; a2 §Defect audit N5; review_soundness F-1 |
| N6 | `cov2Complete ∧ pubOrder ⇒ cov1Complete`; proved substantively by `accFlat_complete` (singleton, all pubs listed, Order4 ⇒ `x ∈ accFlat`); `cov1_of_cov2_pubOrder (hv : Valid)` is the Valid-level corollary, trivial since `Valid` contains `coverage1` | a3a §Defect audit N6; a3b §Theorems; review_soundness F-3 |
| N7 | classify Definition 31.1 conditions by role: safety / progress / terminal | a3a §Defect audit N7; a3a §`Valid` field table |
| N8 | Definition 31.1 stated per command prefix (`Pub pc`, `Cons pc`, `Mat pc`) | a3a §Defect audit N8 |
| N9 | one-step simulation (`step_R`) is proved for `Conf = refState pc` only, not for every R-related Conf (it needs `hc : refState pc = some c`); the spec's Lemma 31.2 simulation statement is restated "as formalized" | review_fidelity F2; a3b §SPEC RESTATEMENT DRAFT |
| P1 | static sets are lists (`consList`/`pubList`/`matList`) wrapped as Props with computable `Decidable`; bounded quantifiers forced through `List.decidableBAll` | a1 §Decision log 2, 6 |
| P2 | Δ_G is a whole-accumulator sum of `Pi.single` increments (`single`, `delta`); permutation invariance is `List.Perm.sum_eq` | a1 §Decision log 4 |
| P3 | `refState η pc = foldlM postAnn (initial η) (prefixAnn pc)`, deterministic in pc | a1 §Decision log 5 |
| P4 | the plan carries `tensors` (`tensors_nodup`, `tensors_complete`); `validateInput` is a plan-side copy of `Executor.validate` | a2 §Decision log 2 |
| P5 | computable enumerations `occList`/`addrList` from the certified tensor list, not the noncomputable `definedFintype` route | a3a §Decision log 1 |
| P6 | `checkSteps` is vacuous on non-singleton commands; `checkSingleton` rejects them | a3a §Decision log 3 |
| P7 | Lemma 31.2 is one theorem about `runPlan`; completeness comes from `refState_R2` plus coverage (`complete_of_refState`) | a3b §Decision log 1-2 |
| P8 | Theorem 31.3 (a) also states the denotation; (c) is split into `done_or_failed` and `done_of_model` | a3b §Decision log 3, 5 |

## 3. Execution preamble (controller)

Every subagent brief opens with the shell-harness preamble in `.claude/skills/new-slice/SKILL.md`
("Subagent brief preamble"). Plain separate commands, absolute paths, `/usr/bin/git -C`, build only
with `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd [targets]`, `rg -n` and 40-60-line
windows, explicit stage paths, never stage `.claude/settings.json`.

### 3.1 Land the docs-only commits on local main, then create the execution worktree

The patches, notes, this plan, the mutation manifest and the record exist only on branch
`worktree-plan-layer-slice1`. That branch also carries prototype Lean commits and must NOT be
merged (CHECKPOINT §7). Gates before any `checkout` or `commit`: `branch --show-current` must print
`main` and `status --short` must print nothing (stop otherwise: a commit would land on another
branch or sweep up staged work). The docs-only landing set includes `papers/semantics/plan_layer_artifacts/`
with `review_fidelity.md`, `review_soundness.md` and `manifest_run.md`; these must already be
committed on `worktree-plan-layer-slice1` (the `checkout` copies committed content only). From the
primary checkout, copy the docs paths only:

```sh
/usr/bin/git -C /Users/williammacready/code/python/pyncd branch --show-current
/usr/bin/git -C /Users/williammacready/code/python/pyncd status --short
/usr/bin/git -C /Users/williammacready/code/python/pyncd checkout worktree-plan-layer-slice1 -- papers/semantics/plan_layer_plan.md papers/semantics/plan_layer_mutations_post.json papers/semantics/plan_layer_record.md papers/semantics/plan_layer_patches papers/semantics/plan_layer_artifacts
/usr/bin/git -C /Users/williammacready/code/python/pyncd diff --cached --stat
/usr/bin/git -C /Users/williammacready/code/python/pyncd commit -m "docs(plan): Plan-layer slice 1 plan, patches, mutation manifest and authoring artifacts" -m "Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

Gate: `diff --cached --stat` lists only paths under `papers/semantics/plan_layer_*`; no `.lean`,
no `lakefile.toml`. The commit message must end with the trailer
`Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`. Then run `new-slice` (`EnterWorktree`, then
`bash .claude/skills/new-slice/prepare-worktree.sh --base main --plan papers/semantics/plan_layer_plan.md`).
Call the new worktree `<exec>`. The prototype worktree stays untouched until close-out.

Base: LOCAL `main` at execution time. The patches were emitted against `0bf02e47`
(evidence.json `base`). If `main` has moved, `git apply --check` (below) decides; a failure is a
BLOCKED stop, not a hand-merge.

### 3.2 Per-task recipe (same for T1-T5)

```sh
shasum -a 256 <exec>/papers/semantics/plan_layer_patches/<NN-name>.patch
/usr/bin/git -C <exec> apply --check <exec>/papers/semantics/plan_layer_patches/<NN-name>.patch
/usr/bin/git -C <exec> apply --index <exec>/papers/semantics/plan_layer_patches/<NN-name>.patch
bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd <targets from the table>
/usr/bin/git -C <exec> diff --cached --stat
/usr/bin/git -C <exec> commit -m "<message from the task section>"
```

The sha256 must equal manifest.json `sha256` for that task. ONE commit per task, containing exactly
the task's Files list and nothing else; tasks in order T1 → T5. Patches are mechanical: no edits to
patched files during execution. A build failure after a clean `apply --check` is BLOCKED.

| task | patch | verification targets (evidence.json) | observed at emission |
|---|---|---|---|
| T1 | `01-syntax-batch.patch` | `LeanNCD.Semantics.Plan.Syntax LeanNCD.Semantics.Plan.Batch` | success, 2960 jobs |
| T2 | `02-memory.patch` | `LeanNCD.Semantics.Plan.Memory` | success, 2961 jobs |
| T3 | `03-step-simulation.patch` | `LeanNCD.Semantics.Plan.Step LeanNCD.Semantics.Plan.Simulation` | success, 2963 jobs |
| T4 | `04-validity-run-correctness.patch` | `LeanNCD.Semantics.Plan.Validity LeanNCD.Semantics.Plan.Run LeanNCD.Semantics.Plan.Correctness` | success, 2966 jobs |
| T5 | `05-aggregator-fixtures.patch` | default targets (no target argument) | success, 8784 jobs |

Job counts move with `main`; the gate is "Build completed successfully" with no `error` line.

## 4. Tasks

No task needs a two-dispatch split: the implementer applies a verified patch, builds, and commits
(evidence.json `boundary_moves: []`, `source_edits: none`). Each task's mutation cycles are in
`papers/semantics/plan_layer_mutations_post.json` (field `task`); they are run by the controller at
close-out (§8), not by the implementer. Fixtures all arrive in T5, because every test module
imports `PlanFixtures`, which imports the aggregator.

Briefs list symbols as `identifier @ file`; implementers window-read, never whole-file-read
(`Simulation.lean` is 26.4K characters).

### T1 — plan syntax and batched accumulation (Lemma 32.1)

Files: `leanncd/LeanNCD/Semantics/Plan/Syntax.lean`, `leanncd/LeanNCD/Semantics/Plan/Batch.lean`.
Patch: `01-syntax-batch.patch` (429 lines).
Symbols:
`OccRef`, `DefAddr`, `DefAddr.addr`, `DefAddr.addr_injective`, `Ann`, `Command`,
`_root_.LeanNCD.Semantics.Program.Plan`, `groups`, `blocks`, `inits`, `occKey`, `pubKey`, `keys`,
`occKey_injective`, `pubKey_injective`, `ann`, `prefixAnn`, `consList`, `pubList`, `matList`, `Pub`,
`Cons`, `Mat`, `prefixAnn_zero`, `not_cons_zero`, `not_mat_zero`, `pub_zero`, `accFlat`, `pubFlat`,
`flatKeys`, `Coverage1`, `Coverage2`, `keys_perm_aux`, `flatKeys_perm`, `coverage_iff_schedule` @ Syntax;
`Execution.append`, `Values`, `single`, `accumulateBatch`, `contributionEvents`, `delta`, `running_ext`,
`consume_accumulators`, `consume_pending`, `accumulateBatch_published`, `accumulateBatch_accumulators`,
`accumulateBatch_pending`, `accumulateBatch_perm`, `batch_execution`, `batch_execution_perm`,
`publishBlock`, `publicationEvents`, `publishBlock_accumulators`, `publishBlock_pending`,
`block_execution` @ Batch. (manifest.json also lists three `(pc` entries for Syntax: instance
binders the emitter mis-parsed; they are the `Decidable` instances for `Pub`/`Cons`/`Mat`.)

Rationale: defines the plan as data (annotations `initZero`/`acc`/`pub`, commands, prefixes and the
prefix sets) and proves the batch half of Part V independent of memory: a duplicate-free, pending,
ready group executes as a reference `Execution` to `accumulateBatch`, which adds Δ_G
(`batch_execution`, Lemma 32.1), in any enumeration order (`batch_execution_perm`); a block of
empty-fiber unpublished addresses publishes (`block_execution`). `coverage_iff_schedule` ties
Coverage1 ∧ Coverage2 to the executor's `Schedule.keys_nodup`/`keys_complete`. Boundary: nothing here
mentions slots, so a reviewer can accept Lemma 32.1 independently of the memory model.
Commit: `feat(semantics): Plan syntax and batched accumulation (Lemma 32.1)`.
Risk: low. Fixtures in task: 0 (its fixtures, `PlanBatchTest`, land in T5). Mutation cycles: 2 (A1-a, A1-b).
Pitfall: inside `Program.Plan`, bare `consume`/`publish` resolve to the noncomputable `Program`
versions; the code writes `Executor.consume`/`Executor.publish` (a1 §Decision log 7).

### T2 — dense memory, read view, Decode, relation R

Files: `leanncd/LeanNCD/Semantics/Plan/Memory.lean`. Patch: `02-memory.patch` (293 lines).
Symbols: `Slot`, `Memory`, `place`, `place_injective`, `Resource`, `SlotView`, `slotView_injective`,
`Start`, `start_noninput`, `readPub`, `Decode`, `decode_some`, `evalValue`, `evalValue_ready`, `postAcc`,
`postPub`, `postAnn`, `refState`, `postAnn_execution`, `foldlM_execution`, `refState_execution`,
`refState_reaches`, `R`, `R_start`, `readPub_eq`, `decode_of_R` @ Memory.

Rationale: fixes the concrete state (one `Option` slot per address via injective `place`), the
published-only read view `readPub`, the partial decoder `Decode` (never fills), the deterministic
logical post-state `refState`, and the relation R as a structure (`reach` R1, `pending`/`published`
R2, `pubSlot`/`accSlot` R3, `retain` R4; a1 §Decision log 9). Proves Lemma 31.2's initialisation
obligation (`R_start`) and that a successful `refState` is reachable (`refState_reaches`).
Boundary: the relation and decoder can be reviewed against spec 30.2/30.4 before any kernel exists.
Commit: `feat(semantics): Plan memory, read view, Decode and relation R`.
Risk: medium (R is the soundness interface; D1-D3, D6 live here). Fixtures in task: 0 (`PlanMemoryTest`
lands in T5). Mutation cycles: 4 (A1-c, A1-d, A1-e, A3b-3).
Note: `Layout` is already taken in the codebase; the spec's layout view is `SlotView`
(CHECKPOINT §7).

### T3 — step kernels and one-step simulation

Files: `leanncd/LeanNCD/Semantics/Plan/Step.lean`, `leanncd/LeanNCD/Semantics/Plan/Simulation.lean`.
Patch: `03-step-simulation.patch` (786 lines).
Symbols: `OccRef.dest`, `OccRef.target`, `OccRef.target_addr`, `StepResult`, `PlanOutcome`, `Singleton`,
`validateInput`, `validateInput_accepts`, `validateInput_error`, `startValidated`, `writeDef`, `execInit`,
`valueOn`, `valuesOn`, `scanGroup`, `addVal`, `addAt`, `execAcc`, `execPub`, `execAnn`, `stepCommand`,
`stepPlan`, `runFrom`, `runPlan` @ Step;
`prefixAnn_succ`, `cons_succ`, `pub_succ`, `mat_succ`, `slotView_pub`, `slotView_acc`, `InitOK`, `AccOK`,
`PubOK`, `AnnOK`, `StepOK`, `Order4`, `accFlat_complete`, `refState_succ`, `refState_succ_single`,
`publish_published_ne`, `publishBlock_published_not_mem`, `publishBlock_published_mem`,
`publishBlock_isSome`, `postAnn_bookkeeping`, `foldlM_bookkeeping`, `refState_R2`,
`acc_zero_of_unconsumed`, `dest_not_pub`, `writeDef_ne`, `writeDef_self`, `execInit_not_mem`,
`execInit_mem`, `addAt_some`, `commit_other`, `single_target`, `single_ne`, `commit_def`,
`scanGroup_ne_ok`, `scanGroup_none`, `scanGroup_semFail`, `evalValue_eq`, `step_init`, `step_acc`,
`step_pub`, `step_R`, `step_failed`, `step_failed_no_model` @ Simulation.

Rationale: defines the executable plan machine (kernels `execInit`/`execAcc`/`execPub`, `stepPlan`,
structural `runFrom`/`runPlan`, no fuel) and proves one-step simulation under the per-pc conditions
`StepOK` (`InitOK`, `AccOK`, `PubOK`), which are exactly what the proofs used (a2 §ValidityConditions):
`step_R` (R preserved, matching reference `Execution`, `refState (pc+1)` produced, D4) and
`step_failed`/`step_failed_no_model` (D5). Also D9 (`accFlat_complete`). Boundary: StepOK excludes
condition 3 and coverage, so this task proves safety only; progress and terminal adequacy are T4.
Commit: `feat(semantics): Plan step kernels and one-step simulation`.
Risk: highest proof volume (Simulation 26.4K characters) but mechanical apply. Fixtures in task: 0
(`PlanStepTest`, `PlanSimulationTest` land in T5). Mutation cycles: 5 (A2-a, A2-b equivalent,
A2-c, A2-e equivalent, A2-f).
Pitfall: `addVal` exists to fix the `AddCommMonoid` index at `x.1` (a2 §Decision log 4).

### T4 — checker, progress, run lemma, Lemma 31.2, Theorem 31.3

Files: `leanncd/LeanNCD/Semantics/Plan/Validity.lean`, `leanncd/LeanNCD/Semantics/Plan/Run.lean`,
`leanncd/LeanNCD/Semantics/Plan/Correctness.lean`. Patch: `04-validity-run-correctness.patch` (551 lines).
Symbols: `ReadyOK`, `Valid`, `Valid.stepOK`, `occList`, `mem_occList`, `addrList`, `mem_addrList`,
`checkSingleton`, `checkCov1Nodup`, `checkCov1Complete`, `checkCov2Nodup`, `checkCov2Complete`,
`checkInit`, `checkAccFresh`, `checkAccMat`, `checkReady`, `checkPubFresh`, `checkPubMat`,
`checkPubOrder`, `checkAnn`, `checkSteps`, `checkPlan`, `checkSteps_ann`, `target_eq`,
`checkInit_sound`, `checkAnn_acc_sound`, `checkAnn_pub_sound`, `checkPlan_sound` @ Validity;
`scanGroup_ne_stuck`, `foldlM_addAt_some`, `readPub_isSome`, `acc_slot_isSome`, `step_not_stuck`,
`run_R`, `runPlan_R`, `runPlan_not_stuck` @ Run;
`prefixAnn_length`, `Valid.order4`, `cov1_of_cov2_pubOrder`, `complete_of_refState`,
`terminal_adequacy`, `done_correct`, `failed_correct`, `done_or_failed`, `done_of_model`,
`done_iff_model` @ Correctness.

Rationale: packages Definition 31.1 (slice-1 form) as `Valid` with one computable check per field and
proves `checkPlan_sound`; proves progress (`step_not_stuck`: a valid, R-related state never steps to
`stuck`), the multi-step `run_R` (done with R at `m`, or failed with a matched reference failure; no
stuck disjunct), Lemma 31.2 (`terminal_adequacy`, first consumer of `coverage1`/`coverage2`) and
Theorem 31.3 (a)(b)(c). Boundary: the three files share one review question, "does an accepted plan
compute the reference result?"; splitting checker from theorems would leave a checker no theorem
consumes.
Commit: `feat(semantics): Plan validity checker, run lemma, Lemma 31.2 and Theorem 31.3`.
Risk: medium-high (checker fidelity is the soundness surface; §5 audit is this task's review
deliverable). Fixtures in task: 0 (`PlanValidityTest`, `PlanRunTest`, `PlanCorrectnessTest` land in T5).
Mutation cycles: 8 (A3a-a equivalent, A3a-b..f, A3b-1, A3b-2).

### T5 — aggregator, umbrella import, lakefile globs, all fixtures

Files: `leanncd/LeanNCD/Semantics/Plan.lean`, `leanncd/LeanNCD/Semantics.lean`, `leanncd/lakefile.toml`,
`leanncd/test/Semantics/PlanFixtures.lean` and the 7 `Plan*Test.lean` modules listed in §1.
Patch: `05-aggregator-fixtures.patch` (830 lines). Symbols: §6 fixture list (manifest.json T5).

Rationale: makes the subsystem reachable (`Plan.lean` imports the 8 modules; `Semantics.lean` gains
`import LeanNCD.Semantics.Plan`; `LeanNCD.lean` already imports `LeanNCD.Semantics`, verified in the
scratch tree) and lands every fixture: `#eval check` rows and kernel `decide`/`rfl` examples. Boundary:
fixtures need the aggregator (`PlanFixtures` imports it), so they cannot ship earlier.
Commit: `test(semantics): Plan aggregator, umbrella import and fixtures`.
Risk: low (no production code). Fixtures in task: 96, counted in the scratch tree as 50 `#eval check`
rows (Batch 8, Memory 7, Step 16, Simulation 1, Validity 10, Correctness 8) plus 46 top-level
`example`/`theorem` items (Batch 2, Memory 3, Simulation 16, Validity 15, Run 4, Correctness 6).
Mutation cycles: 1 (A2-d, the fixture-plan mutant); all 20 cycles become runnable after T5.
Exit: full default build green; forbidden-token grep empty:

```sh
rg -n "\b(sorry|admit|axiom|native_decide)\b" <exec>/leanncd/LeanNCD/Semantics/Plan <exec>/leanncd/LeanNCD/Semantics/Plan.lean <exec>/leanncd/test/Semantics --glob "Plan*"
```

### Risk table

| task | production files | fixtures in task | mutation cycles | split? | main risk |
|---|---|---:|---:|---|---|
| T1 | 2 | 0 | 2 | no | none beyond apply |
| T2 | 1 | 0 | 4 | no | R fidelity (review lens: spec 30.4) |
| T3 | 2 | 0 | 5 (2 equivalent) | no | build time of Simulation |
| T4 | 3 | 0 | 8 (1 equivalent) | no | checker fidelity; §5 table |
| T5 | 3 + 8 test | 96 | 1 | no | full-build time |

## 5. Section-2 audit (case × class)

Classes: **R** required (the plan must accept / the kernel must do it), **F** forbidden (must be
rejected), **I** SILENTLY IGNORED (no check or kernel reaction; a candidate defect), **OPEN** (no
fixture or mutant backs the cell). "Fixture" names come from §6; "mutant" ids from the manifest.

### 5.1 `checkPlan` checks and `Valid` fields

| check | `Valid` field | role (a3a §`Valid` field table) | F case and its fixture (first failing clause) | mutant | status |
|---|---|---|---|---|---|
| `checkSingleton` | `singleton` | progress (profile) | fused command: `fused` (`singleton`; run stuck 0) | A3a-e: `fused` flips | backed |
| `checkCov1Nodup` | `coverage1` (Nodup half) | diagnostic (a3b draft table) | occurrence in two groups: `dupGroup` (`cov1Nodup`, also `accFresh@2`; run done 4 `[0,16,0]`) | none (see `checkAccFresh`) | **PROVED redundant at `checkPlan`**: `checkPlan_nodup_redundant` (singleton and `checkSteps` imply it), and the converse `checkAccFresh_of_cov1Nodup` (it implies the freshness clause at every accumulate command) holds, so no singleton plan separates the pair (`dupGroup`, `dupWithin`) |
| `checkCov1Complete` | `coverage1` (covering half) | terminal, derivable (N6) | missing occurrence: `missingOcc` (`cov1Complete`, also `pubOrder@2`) | A3a-a: no fixture flips | **EQUIVALENT at `checkPlan`** (N6: `accFlat_complete` is the substantive reason; `cov1_of_cov2_pubOrder` is the trivial Valid-level corollary). Confirmed for all plans (soundness review Q4) |
| `checkCov2Nodup` | `coverage2` (Nodup half) | diagnostic | address in two blocks: `invalid-publish-twice-across-blocks`, `invalid-publish-twice-in-block` (`cov2Nodup` and `pubFresh@3` / `pubFresh@2`; runs done 4 and 3, `[0,14,0]`) | none (see `checkPubFresh`) | **PROVED redundant at `checkPlan`**: `checkPlan_nodup_redundant`, converse `checkPubFresh_of_cov2Nodup` (it implies the freshness clause at every publish command), so no singleton plan separates the pair (`pubTwice`, `pubDupIn`) |
| `checkCov2Complete` | `coverage2` (covering half) | terminal | unpublished defined address: `missingPub` (`(false, ["cov2Complete"])`; run done 3, Decode `none`) | A3b-1: `missingPub` flips; A3b-2: field unreachable | backed |
| `checkInit` (both halves) | `initFresh` | safety (N2) | re-init after consume: `reinitMid` (`initFresh@2`; run done 5 `[0,10,0]`) | A3a-d (drops both halves): only `reinitMid` flips | backed for the consumed-target half |
| `checkInit` (not-published half alone) | `initFresh` | safety | re-init of a published empty-fiber address: `invalid-reinit-after-publish` (`reinitPub`: `(false, ["initFresh@3"])`, no other clause; run done 4 `[0,14,0]`) | audit mutant B3 (drop only the not-published conjunct): the build stops in `checkInit_sound` before the fixtures are reached, so the flip itself was not observed | **backed at checker level**; the half affects no run outcome (a published address with a non-empty fiber is caught by the consumed-target half via `pubOrder`; an empty-fiber one gets 0 written over 0), so "safety" overstates its role |
| `checkAccFresh` | `accOK` | safety + progress | already-consumed member (across groups): `dupGroup` (`accFresh@2`, second clause); within-group duplicate: `dupWithin` (`invalid-duplicate-within-group`: `cov1Nodup`, `accFresh@1`; run done 3 `[0,16,0]`) | audit mutants C2a (drop Nodup half) and C2b (drop consumed half): both break `checkPlan_sound` first; under C2b `dupGroup` does not flip because `cov1Nodup` still rejects | **EQUIVALENT at `checkPlan`, paired with `checkCov1Nodup`** (proved: `checkAccFresh_of_cov1Nodup`; neighbour `accSplit` valid) |
| `checkAccMat` | `accOK` | safety + progress | unmaterialised target: `noInit` (`accMat@0`, also `pubMat@1`; run stuck 0) | audit mutant C3 (check always true): breaks `checkPlan_sound` first; no fixture flips | **EQUIVALENT at `checkPlan`**: no plan fails `accMat` alone (`invalid-acc-unmaterialised-attempts`: every attempt also trips `initFresh`, `pubMat` or `cov2Complete`); neighbour `lateEmptyInit` valid |
| `checkReady` | `ready` | progress only (N3) | read of unpublished address: `chainEarly` (`ready@1`; run stuck 1) | A3a-f: `chainEarly` flips | backed |
| `checkPubFresh` | `pubOK` | safety + progress | duplicate / already-published member: `pubTwice`, `pubDupIn` (see `checkCov2Nodup`) | audit mutant C1 (check always true): breaks `checkPlan_sound` first; no fixture flips | **EQUIVALENT at `checkPlan`, paired with `checkCov2Nodup`** (proved: `checkPubFresh_of_cov2Nodup`; neighbour `pubSplit` valid) |
| `checkPubMat` | `pubOK` | safety + progress (N1) | empty fibers not materialised: `partialInit` (`pubMat@2`; run stuck 2) | A3a-c: `partialInit` flips | backed |
| `checkPubOrder` | `pubOK` | safety (cond. 4) | publish before all contributions: `earlyStep` (`pubOrder@1`), `earlyHalf` (`pubOrder@2`); both run to done | A3a-b: both flip | backed |
| `checkSteps` on non-singleton | — | — | vacuous by design (P6); covered by `checkSingleton` | A3a-e | **I by design**, guarded |

Required (accept) column, all six valid plans give `checkPlan = true` with no failing clause and
every mutant leaves them true (a3a §Mutation controls): `plan`, `pPlan 2 reciprocalBody`,
`pPlan 2 failureAfterBody`, `sPlan true`, `sPlan false`, `chainPlan`.

Valid-field consumers (a3a §`Valid` field table; a3b §Theorems): `singleton` → `step_not_stuck`,
`run_R`; `coverage1`, `coverage2` → `complete_of_refState` (Lemma 31.2) only; `initFresh` →
`Valid.stepOK` → `step_init`; `accOK` → `step_acc`, `step_failed`, `step_not_stuck`; `pubOK` →
`step_pub`, `step_not_stuck`, `Valid.order4`; `ready` → `step_not_stuck` only. `checkCov1Complete`
has no proof consumer beyond `checkPlan_sound` building `coverage1.2` (N6).

### 5.2 Step and failure kernels

| kernel | case | class | evidence |
|---|---|---|---|
| `stepCommand` | singleton `[a]` | R: run `execAnn` | every valid fixture |
| `stepCommand` | fused command | R: `stuck`, never a wrong `ok` | `fused` (stuck 0) |
| `stepCommand` | empty command `[]` | R: `stuck` (by code: the catch-all case) | `step-empty-command-stuck`, `invalid-empty-command` (`emptyCmd`: `stepCommand []` stuck; `runPlan` stuck at pc 1; `singleton` fires); audit mutants B1, B1b flip the fixture |
| `stepPlan` | `pc ≥ m` | R: `stuck` | `step-plan-past-end` (pc 3 and 4 stuck, pc 2 steps; `runFrom` never reaches it structurally); audit mutant B2 flips the fixture |
| `execInit` | writes `0` to each member | R | `step-tagged-trace` pc 1 `[0,0,0]` |
| `execInit` | duplicate members in S | I by design (idempotent; a2 §ValidityConditions "S need not be duplicate-free") | none needed |
| `execInit` | target live (consumed contributions or published) | I at kernel; F by `checkInit` | `reinitMid` silently returns `[0,10,0]` (N2, N4) |
| `execAcc` | all members ready and defined | R: add every value, commit | `taggedOut` `[0,14,0]`; A2-a `[0,5,0]` |
| `execAcc` | member not ready on the published view | R: `stuck` (first such member in list order) | `invalid-read-unpublished` stuck 1; A2-f, A3b-3 |
| `execAcc` | member undefined | R: `semFail x`, nothing committed (transactional) | `failureAfter` failed pc 1, slot 0 `some 0` vs executor 2 (D5) |
| `execAcc` | destination slot uninitialised | R: `stuck` | `noInit` stuck 0 |
| `execAcc` | already-consumed member (reused across groups) | I at kernel; F by `checkAccFresh` | `dupGroup` runs to done 4 `[0,16,0]` |
| `execAcc` | duplicate member within one group | I at kernel; F by `checkAccFresh` | `dupWithin` runs to done 3 `[0,16,0]` (double-counts) |
| `execAcc` | commit values from raw vs published view | **EQUIVALENT** (A2-b, N5), all plans | no fixture can differ: footprint addresses are published after a successful scan (confirmed for all plans, valid or not; soundness review Q4) |
| `execAcc` | transactional vs sequential commit | **EQUIVALENT on `checkPlan`-valid plans only** (A2-e, N5) | `semFail` carries no memory; `readPub` hides prefix commits because destinations are unpublished and materialised (`dest_not_pub`, `acc_slot_isSome`); two invalid plans distinguish them (`a2e-seq-visible`, `a2e-failed-vs-stuck`: shipped `[0,3,1]` / `failed`, mutant `[0,3,4]` / `stuck`, the mutant values observed in a scratch run and not asserted by the build; Open items 10) |
| `execAcc` | which failing member is reported when several fail | not a requirement (31.3 (b) compares no-model only, D5) | **OPEN** by design: no fixture mixes a not-ready and an undefined member |
| `execPub` | every member slot initialised | R: `ok M`, writes nothing | A2-c gives `[0,0,0]` on tagged and chain |
| `execPub` | some member slot `none` | R: `stuck` | `partialInit` stuck 2 |
| `execPub` | already-published member | I at kernel; F by `checkPubFresh` | `pubTwice` runs to done 4 and `pubDupIn` to done 3, both `[0,14,0]` (silently re-publish) |
| `execPub` | contributions still pending | I at kernel; F by `checkPubOrder` | `earlyStep` runs to done 3, `refState 2 isSome = false` |
| `runFrom` | failure | R: `failed o pc M` with PRE-step memory (this comes from `runFrom`'s structure, since `semFail` carries no memory; the fixture does not test transactionality) | `step-failure-after` `("failed", 1, some (1, 0), [some 0, some 0, some 0])` |

Every kernel I cell is closed by a checker clause (N4: soundness rests on `checkPlan`); the OPEN
cells are listed in Open items with costs.

## 6. Fixtures

All in T5. Observed values are from the notes (each was printed by a build there). Donor programs
`tagged`, `program n body`, `reciprocalBody`, `failureAfterBody`, `scalarRole`, `routed`,
`taggedResult`, `noInput`, `declarations` are imported from `Semantics.ExecutableReferenceTest`
(a1 §Decision log 11; a3b §Observed comparison table).

### 6.1 Shared fixtures @ `leanncd/test/Semantics/PlanFixtures.lean`

| identifier | donor | observed |
|---|---|---|
| `taggedOut` | clone `tagged`, change `output := true` | four occurrences to point 1, values 2, 2, 5, 5 |
| `plan` | new: `[[initZero p0..p2], [acc group], [pub p0..p2]]` over `taggedOut` | `checkPlan = true`; done 3 `[0,14,0]` |
| `group`, `groupPerm` | `group` = the four occurrences; `groupPerm` clone `group`, permute | both give accRow `[0,14,0]` |
| `mem3`, `mem3Hole` | `mem3` = slots `[0,14,0]`; `mem3Hole` clone `mem3`, change one slot to `none` | decode pc 3: `some [0,14,0]` vs `none` |
| `unitPlan`, `scalarPlan`, `block`, `addr`, `occ`, `η0`, `start0`, `values`, `accRow`, `outT`, `decodeRow`, `T` | constructors and readers | — |

### 6.2 Test modules (identifier @ file, donor, observed)

| identifier @ file | donor | observed / distinguishes |
|---|---|---|
| batch checks @ `PlanBatchTest.lean` (`batched`, `batchedPerm`, `refRow`) | `plan`, `group`, `groupPerm` | accRow `[0,14,0]` (not overwrite `[0,5,0]`, not dropLast `[0,9,0]`); permuted `[0,14,0]`; published unchanged; pending card 0; vs `taggedResult` `([0,14,0], [some 0, some 14, some 0])` |
| `earlyPlan` @ `PlanBatchTest.lean` | clone `plan`, change order (pub before acc) | `refState` pc 2 `isSome = false` |
| `scalarSlot` and memory checks @ `PlanMemoryTest.lean` | `scalarRole true`, `plan` | place indices `[0,1,2]`; start-scalar `[some 7, none, none]`; start-tagged `[none,none,none]`; slotview-acc point 1 pc 0..3 `[false,true,true,false]`; slotview-pub `[false,false,false,true]`; decode `(none, none, some [0,14,0], none)` |
| `taggedRun`, `taggedTrace` @ `PlanStepTest.lean` | `plan` | `("done", 3, none, [some 0, some 14, some 0])`; trace `[none×3]`, `[0,0,0]`, `[0,14,0]`, `[0,14,0]` |
| `pPlan`, `pRun` @ `PlanStepTest.lean` | `program 2 reciprocalBody` / `failureAfterBody` | reciprocal done 3 view `[3/4, 0, 0]` (collect 1/2 + 1/4, not 1/(2+4) = 1/6); failure `("failed", 1, some (1, 0), [some 0, some 0, some 0])` |
| `sPlan`, `sRun`, `sDecode` @ `PlanStepTest.lean` | `scalarRole b` | bad: `("failed", 3, some 2, [some 7, some 2, some 0])`; good: `("done", 5, none, [some 7, some 2, some 3])`, Decode output 1 `some 2` |
| `startRow` @ `PlanStepTest.lean` | donor `runValidated` rows | `[("ok",99), ("error",0), ("error",1), ("error",0)]` |
| `chainPlan` @ `PlanStepTest.lean` | `routed` | `("done", 5, none, [0, 3, 4])` |
| `chainEarly` @ `PlanStepTest.lean` | clone `chainPlan`, change order (acc s1 before s0 published) | `("stuck", 1, none, [some 0, some 0, some 0])`; `ready@1` |
| `earlyStep` @ `PlanStepTest.lean` | clone `plan`, swap acc and pub | done 3 `[0,14,0]`, `refState 2 isSome = false`; `pubOrder@1` |
| `noInit` @ `PlanStepTest.lean` | clone `plan`, drop the initZero command | `("stuck", 0, none, [none, none, none])`; `accMat@0`, `pubMat@1` |
| `partialInit` @ `PlanStepTest.lean` | clone `plan`, change initZero to point 1 only | `("stuck", 2, none, [none, some 14, none])`; `pubMat@2` |
| `dupGroup` @ `PlanStepTest.lean` | clone `plan`, change: occ 0 0 also in a second group | done 4 `[0,16,0]`, `refState 3 isSome = false`; `cov1Nodup`, `accFresh@2` |
| `fused` @ `PlanStepTest.lean` | clone `plan`, change: two annotations in one command | `("stuck", 0, none, [none, none, none])`; `singleton` |
| `tagged_R_every_pc` @ `PlanSimulationTest.lean` (`m1`..`m3`, `ok0`..`ok2`) | `plan` | R at pc 0..3 by chaining `R_start`/`step_R`; m rows `[[0,0,0],[0,14,0],[0,14,0]]` |
| `failure_matched` @ `PlanSimulationTest.lean` | `pPlan 2 failureAfterBody` | `semFail` at pc 1 matched by a reference `undefined` segment; no model |
| `twice`, `twice_pub_complete`, `twice_order4`, `twice_not_disjoint` @ `PlanSimulationTest.lean` | clone `plan`, change: accumulate `group` twice | Coverage2-union and Order4 hold, `accFlat` not Nodup (D9 disjointness counterexample) |
| `clauseRow`, `verdict` @ `PlanValidityTest.lean` | — | verdict = (`checkPlan`, failing clauses in `checkPlan` order) |
| `missingOcc` @ `PlanValidityTest.lean` | clone `plan`, change: drop one occurrence from `group` | `cov1Complete`, `pubOrder@2` |
| `earlyHalf` @ `PlanValidityTest.lean` | clone `plan`, change: split `group`, pub after the first half | `pubOrder@2`; done 4 `[0,14,0]` |
| `reinitMid` @ `PlanValidityTest.lean` | clone `plan`, change: initZero again between the two halves of `group` | `initFresh@2`; done 5 **`[0,10,0]`** (correct 14) |
| `plan_valid`, `sPlan_bad_valid` @ `PlanRunTest.lean` | `checkPlan_sound (by decide)` | `Valid` instances |
| `tagged_run_R`, `scalar_bad_matched` @ `PlanRunTest.lean` | `plan`, `sPlan true` | R at pc 3 on the memory `runPlan` returns; failure at pc 3 on tensor 2 matched |
| `planRow`, `refRow`, `reciprocalRef`, `sRefOut`, `failureAccRef`, `plan_tagged_done` @ `PlanCorrectnessTest.lean` | valid fixtures vs executor `run` | `cmp-done-agree` `[true, true, true, true]`; failureAfter plan slot 0 `some 0` vs executor accumulator **2** (recorded, not asserted, D5) |
| `tagged_model_unique`, `scalar_bad_no_model`, `tagged_has_model` @ `PlanCorrectnessTest.lean` | `plan_valid`, `sPlan true` | 31.3 (a), (b), `done_iff_model` instances |
| `missingPub` @ `PlanCorrectnessTest.lean` | clone `plan`, change: drop one address from the pub block | done 3 slots `[0,14,0]`, Decode **`none`**; `(false, ["cov2Complete"])`; `checkCov1Complete = true` |

### 6.3 Requirements that need a distinguishing fixture

| requirement | candidate readings | distinguishing fixture |
|---|---|---|
| accumulation adds (Lemma 32.1) | add vs overwrite vs skip last | `taggedOut` values 2,2,5,5: `[0,14,0]` vs `[0,5,0]` vs `[0,9,0]` |
| collection before nonlinear read | sum of reciprocals vs reciprocal of sum | `pPlan 2 reciprocalBody`: 3/4 vs 1/6 |
| N2 initZero freshness | re-init allowed vs forbidden | `reinitMid`: `[0,10,0]` (accepted run) vs rejection `initFresh@2` |
| N1 materialise empty fibers | only targeted points vs all published | `partialInit`: stuck 2 vs done |
| Decode partial (D6) | partial vs zero-fill | Decode pc 0 `none` (zero-fill gives `some [0,0,0]`); `mem3Hole` `none` (zero-fill gives `some [0,14,0]`) |
| layout view Mat guard (D2) | `Mat ∧ ¬Pub` vs `¬Pub` | slotview-acc pc 0 `false` (mutant `true` while `Start` holds `none`) |
| read view only (cond. 3 dynamic) | published view vs raw memory | `chainEarly` / invalid-read-unpublished: stuck 1 vs done 4 `[0,3,1]` |
| place injective | index vs index / 2 | place-indices `[0,1,2]` |
| coverage2 at terminal (Lemma 31.2) | needed vs not | `missingPub`: every other clause holds, done 3, Decode `none` |
| transactional failure snapshot (D5) | transactional vs executor order | `failureAfter`: plan slot 0 = 0, executor 2; recorded, not a theorem requirement |
| checker clause order | first failing clause | diagnostic only; `missingOcc`, `dupGroup`, `noInit` violate two clauses at once and pin the full clause row |
| group enumeration order irrelevant | any order | `groupPerm` `[0,14,0]` |

## 7. Mutation cycles

Manifest: `papers/semantics/plan_layer_mutations_post.json`, 20 cycles, format of
`leanncd/scripts/mutation-manifest.sh` (`label`, `task`, `file` relative to `leanncd/`, `old`, `new`,
`targets`, `expect`). `--check` passed at authoring against the full shipped tree ("manifest OK: 20
entries, 20 selected, every old-string unique"). Per task: T1 2, T2 4, T3 5, T4 8, T5 1.

Validated: a full run on the shipped tree (commit `5f1101d0`) passes 20/20
(`plan_layer_artifacts/manifest_run.md`). The first full run was 18/20; only two `expect` strings
were corrected, A1-d and A2-d, which now carry the observed strings (A1-d: ``Tactic `split_ifs` failed``
at `decode_some`; A2-d: the `step-tagged-run` fixture failure in `PlanStepTest`, because the import
chain stops the build there before the `ok2` decide is elaborated). No other `expect` needed change
and no mutant compiled where the notes say it should fail.

Equivalent mutants, labelled `EQUIVALENT` in the manifest: A2-b and A2-e (N5), A3a-a (N6).
"Equivalent" means no fixture or run outcome distinguishes them (A2-e: on valid plans only, A2-b and
A3a-a: all plans); each still breaks a proof, so they FAIL the build and pass as cycles. They are not
evidence of a fixture. Two caveats from the run: the A1-d mutant is also ill-typed (`getD 0` has no
instance at `Decode`, which precedes the `AddCommMonoid` variable), so it breaks the build even
without the `decode_some` proof, and the intended `decode_some` failure is observed, so the cycle
pins that proof only weakly; A1-e has side errors, but the expected failure is present.
Fixture-level effects of the A3a and A3b-1 checker mutants were measured with the soundness proof
replaced by `sorry` (a3a §Mutation controls); the manifest reproduces only the proof-level failure.

Mutant-form rule (a3a §Mutation controls; a3b §Mutation cycles): a trivialised mutant keeps its `π`
parameter (`.all fun _ => true`), else the failure is syntactic ("Invalid field notation").

## 8. Documentation sweep (commands)

Run in `<exec>` after T5 commits, as one docs commit (`docs(semantics): ...`). The spec is a
protected input until here (CHECKPOINT §7). Locate every anchor with `rg -n` first; never edit by
line number.

### 8.1 Spec `papers/semantics/tensor_logic_semantics.md`

```sh
rg -n "^### (29\.3|30\.1|30\.2|30\.3|30\.4|31\.1|31\.2|31\.3|32\.1) " <exec>/papers/semantics/tensor_logic_semantics.md
rg -n "\*\*(Definition 31\.1|Lemma 31\.2|Theorem 31\.3|Lemma 32\.1)" <exec>/papers/semantics/tensor_logic_semantics.md
rg -n "^\| (Lemma 31\.2|Theorem 31\.3|Lemma 32\.1) " <exec>/papers/semantics/tensor_logic_semantics.md
rg -n "They also ensure the readiness|follows from the others|Failure matching|Before a kernel updates or reads" <exec>/papers/semantics/tensor_logic_semantics.md
```

Restatements, text from a3b §SPEC RESTATEMENT DRAFT (copy its bullets and table, adapting notation).
Every restatement is an **added** paragraph headed "As formalized (slice-1 profile: singleton commands,
dense non-reused storage, no retirement)". Nothing general is replaced: the 30.4 R, the Need_pub
argument and the five-condition Definition 31.1 stay, because Section 33 (buffer reuse) relies on them.

| edit | spec location (heading as it exists) | content |
|---|---|---|
| relation R | `### 30.4 The refinement relation and output decoder` | add an "as formalized (slice-1 profile)" paragraph after the general R, which stays (`SlotView` maps exactly `Pub pc` only because nothing is retired): R1 reach; R2 as iff-equations (D3); R3 at `place a` with `SlotView π pc` depending on pc only (D2); R4 retention; R1 kept because R2-R4 do not pin untouched accumulators (D1); Decode partial, succeeds iff every output coordinate is in `Pub pc` with an initialised slot, never fills (D6) |
| Definition 31.1 | `**Definition 31.1 (valid plan).**` under `### 31.1 Acceptance and explicit rejection` | Lean's `Valid` is purely static; the spec's semantic conditions 2-5 are, for the slice-1 kernels, the theorems `R_start` (2), `step_R` (3), `step_failed` (4), `step_not_stuck` (5). Per-command-prefix form (N8) with the role/consumer table (N7); initZero freshness (N2); pub `B ⊆ Mat pc` (N1); cond. 3 as progress (N3); cond. 1 covering listed as a consequence of cond. 2 covering + cond. 4 (N6, D9; cite `accFlat_complete`, not `cov1_of_cov2_pubOrder`, whose `Valid` hypothesis already contains cond. 1) and kept in `Valid` (redundant, consumed by `complete_of_refState`); Nodup halves of cond. 1 and cond. 2 are diagnostic (cond. 1 Nodup following from `AccOK` is an unproved conjecture); one sentence that runtime execution does not detect invalid plans, soundness rests on the checker (N4) |
| step simulation | `### 31.2 Initial states and successful-step simulation` | as formalized: the invariant is `R ∧ Conf = refState pc` (P3), premises singleton command and `AnnOK pc a`; simulation is proved for that reference state only, not every R-related Conf, since R2-R4 do not pin untouched accumulators (D1; N9); `R_start` is the initialisation obligation |
| Lemma 31.2 | `**Lemma 31.2 (terminal adequacy).**` (under `### 31.3`) | add an "as formalized (slice-1 profile)" paragraph after the general argument, which stays: in slice 1 the Need_pub step is trivial because at pc = m `Pub m = Addr_Σ` and nothing is retired (a3b draft, "New wording") |
| Theorem 31.3 | `**Theorem 31.3 (compiled correctness).**` | (a)(b)(c) as formalized; (b) as the spec states it (no model); error-free singleton profile stated |
| failure matching | `4. **Failure matching.**` in Definition 31.1 and the paragraph opening "If a related concrete state steps to PlanFailed" under `### 31.3` | proved with the same occurrence: `step_failed`/`runPlan_R` give `Conf →* Failed(o, …)` for the `o` the plan reports, by one `undefined` event from the related Conf (zero preceding contributions); `PlanFailed` carries the memory before the failing command. The matched snapshot is that Conf and may differ from `Executor.run`'s own schedule (fixture `failureAfter`; D5). On `checkPlan`-valid plans raw-vs-view and transactional-vs-sequential commit are unobservable (N5; `dest_not_pub`, `acc_slot_isSome`) |
| conditions by role | `### 29.3 Coverage and schedule certificates`, the sentence containing "They also ensure the readiness" | condition 3 is a progress premise, readiness is enforced dynamically by the read view (N3); classify conditions safety / progress / terminal (N7); materialisation of every published address including empty fibers (N1) |
| materialisation | `### 30.2 Resource views and live representations`, the sentence "Before a kernel updates or reads its physical" | it does not imply initZero freshness; add it (N2) and the pub materialisation (N1) |
| Lemma 32.1 | `**Lemma 32.1 (batched accumulation refines individual steps).**` under `### 32.1` | premises `G.Nodup` (list form of "G is a set"), G ⊆ pending, readiness, per-member success (D10); failure paragraph: proved only for the transactional singleton kernel (`step_failed`), wording per D5 |
| proof status | `### Proof status and numbered results` rows `Lemma 31.2`, `Theorem 31.3`, `Lemma 32.1` (currently "Not formalized.") | "Proved (slice-1 profile): `terminal_adequacy`, `complete_of_refState` (`Plan.Correctness`)."; "Proved (slice-1 profile): `done_correct`, `failed_correct`, `done_or_failed`, `done_of_model`, `done_iff_model` (`Plan.Correctness`); `runPlan_not_stuck` (`Plan.Run`)."; "Proved: `batch_execution`, `batch_execution_perm`, `accumulateBatch_accumulators`, `accumulateBatch_pending`, `accumulateBatch_published` (`Plan.Batch`); failure half for the transactional singleton kernel only (`step_failed`, `Plan.Simulation`)." |

Exit greps (each must print nothing):

```sh
rg -n "^\| (Lemma 31\.2|Theorem 31\.3|Lemma 32\.1) .*Not formalized" <exec>/papers/semantics/tensor_logic_semantics.md
rg -n "[A-Za-z]+\.lean:[0-9]+" <exec>/papers/semantics/tensor_logic_semantics.md
```

Manual check: `rg -n "mathrm\{Need\}" <exec>/papers/semantics/tensor_logic_semantics.md` (the spec
spells Need_pub as `\mathrm{Need}` with subscript `\mathrm{pub}`; 4 hits at authoring: `### 30.2`,
Lemma 31.2's argument under `### 31.3`, `### 33.3 Full-history outputs change the retention obligation`,
and the `## 35. Compact notation reference` table). All four stay unchanged; the slice-1 paragraph goes
after Lemma 31.2's argument.

### 8.2 Path doc `papers/semantics/lean_executable_semantics_path.md`

```sh
rg -n "No Part V result is formalized|Part V backend refinement|backend refinement +LATER|^### 4\.8 |^### 5\.2 |^## 5\. " <exec>/papers/semantics/lean_executable_semantics_path.md
```

- In the status diagram under `## 1. Purpose, authority, and current position`, replace the last row
  `compiled storage/backend refinement   LATER` with a `Part V slice-1 plan layer (singleton, dense) LANDED`
  row followed by a `general compiled storage/backend refinement LATER` row (keep the column alignment
  and the `|` connector lines).

- Add `### 4.9 Part V slice 1: the singleton-command plan layer` after section 4.8 (no renumbering of
  existing anchors). Content: modules and their roles (§4 task rationales, one line each), theorem
  table (`| Theorem | Mathematical conclusion | Spec result |`, the shape already used in section 4.6),
  the slice-1 profile, the "does NOT do" list of §1, and the fixture/mutation counts (96 fixtures,
  20 cycles, 3 equivalent).
- Update the two sentences found by the grep above ("No Part V result is formalized"; "not
  dense-storage simulation or Part V backend refinement") to point at 4.9; update `### 5.2` to say
  slice 1 landed and list the not-done items.
- Regenerate the TOC: add `  - [4.9 Part V slice 1: the singleton-command plan layer](#49-part-v-slice-1-the-singleton-command-plan-layer)`
  after the 4.8 entry, plus one indented TOC line for every `####` sub-heading 4.9 gets (4.6 and 4.7
  have them), or the count rule below breaks. Check counts:

```sh
rg -c "^#{2,4} " <exec>/papers/semantics/lean_executable_semantics_path.md
rg -c "^ *- \[" <exec>/papers/semantics/lean_executable_semantics_path.md
```

The second count is the first minus 1 (the `## Table of contents` heading itself); record both.

### 8.3 Intent layer

- New node `leanncd/LeanNCD/Semantics/Plan/AGENTS.md` (does not exist yet; CHECKPOINT §4.3: write it
  fresh in `<exec>`, not from the prototype). Sections: Purpose (one paragraph), Code map (the 8
  modules, one line each), Contracts (slice-1 profile; soundness rests on `checkPlan`, N4; `Valid`
  field roles), Pitfalls:
  - inside `Program.Plan` write `Executor.consume`/`Executor.publish`; bare names resolve to the
    noncomputable `Program` versions;
  - force `List.decidableBAll` for bounded quantifiers; instance search otherwise picks
    `Fintype.decidableForallFintype` through the noncomputable `definedFintype`;
  - `prefix` is a Lean keyword: the prefix is `prefixAnn`;
  - `Layout` is already taken: the spec's layout view is `SlotView`;
  - a trivialised mutant must keep its `π` parameter;
  - `StepResult` has no `DecidableEq`: R-at-every-pc fixtures are proofs by `rfl`, not `decide`;
  - not the checked backend: `Semantics/Plan` (`Program.Plan.checkPlan`, the Part V reference plan) is
    unrelated to `Eval/Plan` (`CheckedEvalPlan`, whose own `checkPlan` is in `Eval/Plan/EvalPlan.lean`);
    no theorem connects them.
- Size gate (injected sections ≤ ~3k characters):

```sh
wc -c <exec>/leanncd/LeanNCD/Semantics/Plan/AGENTS.md
rg -n "^## " <exec>/leanncd/LeanNCD/Semantics/Plan/AGENTS.md
```

  Measure Pitfalls + Checks + Patterns + Context together; trim to ≤ ~3000 characters.
- One line in `leanncd/LeanNCD/Semantics/AGENTS.md` under `## Current artifact`: the Plan layer
  (`LeanNCD.Semantics.Plan`, Part V slice 1) with a downlink to `Plan/AGENTS.md`; and in `## Scope`,
  extend the "validation layer covers" sentence with "the Part V slice-1 plan layer (singleton
  commands, dense non-reused storage)" and add buffer reuse and fused/batched plan commands to the
  "remain outside it" list.
- One line in `leanncd/AGENTS.md`: extend the `Semantic explorations` row of `### Subsystems` with
  "Part V slice-1 plan layer (`Semantics/Plan/`; not the `Eval/Plan` checked backend)" and add an
  `### Entry Points` row "Check or run a Part V reference plan (not `EvalPlan`) |
  `LeanNCD/Semantics/Plan/Validity.lean` (`checkPlan`), `Plan/Correctness.lean` (`done_correct`)".

### 8.4 Discoverability and stale-value sweep

`import LeanNCD` reaches the Plan modules: `LeanNCD.lean` imports `LeanNCD.Semantics`, and patch 05
adds `import LeanNCD.Semantics.Plan` to `LeanNCD/Semantics.lean` (verified in the scratch tree). A
new reader finds them from `leanncd/AGENTS.md` → `Semantics/AGENTS.md` → `Plan/AGENTS.md`, and from
path doc section 4.9.

```sh
rg -n "Not formalized|No Part V result|Part V backend refinement|not formalized" <exec>/papers <exec>/leanncd --glob "*.md"
rg -n "Lemma 31\.2|Theorem 31\.3|Lemma 32\.1" <exec>/papers <exec>/leanncd --glob "*.md"
rg -n "[A-Za-z]+\.lean:[0-9]+" <exec>/leanncd/LeanNCD/Semantics/Plan/AGENTS.md <exec>/papers/semantics/lean_executable_semantics_path.md
rg -n "no Lean proof|argued on paper|proposed contracts and proof targets|backend refinement +LATER" <exec>/papers <exec>/leanncd --glob "*.md"
```

Every hit of the first two is either updated or justified in the record; the third prints nothing.
The fourth finds statements the slice makes false (4 hits at authoring outside the `plan_layer_*`
files); edit each (spec unless noted):

- the intro sentence before `### Proof status and numbered results`, "compilation results have no Lean
  proof": say Lemma 31.2, Theorem 31.3 and Lemma 32.1 are proved for the slice-1 profile (see the table);
- the last paragraph of `### 31.4 The compiled-correctness theorem` ("argued on paper", "not a claim that
  a particular compiler or kernel has already been verified"): add that for the slice-1 kernels the
  generic steps and conditions 2-5 are kernel-checked (`step_R`, `step_failed`, `step_not_stuck`,
  `batch_execution`); other kernels keep the obligation;
- under `## 34. Refinement boundaries and formalization targets`, the list after "The compilation-layer
  proof targets are:" and the sentence "These are proposed contracts and proof targets, not
  kernel-checked results": mark the bullets with slice-1 results (annotations and validation, resource
  views and R, individual-kernel refinement, progress, terminal decoding and compiled correctness) as
  proved for the slice-1 profile; fused commands, sharing, and scan/buffer reuse stay targets;
- path doc status diagram: done by the §8.2 diagram edit.

## 9. Close-out (controller)

1. Full default build in `<exec>`: `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd`; record
   the job count and the forbidden-token grep (§4 T5 exit).
2. Run the mutation manifest itself, not only `--check`:

```sh
bash <exec>/leanncd/scripts/mutation-manifest.sh --check <exec>/leanncd <exec>/papers/semantics/plan_layer_mutations_post.json
bash <exec>/leanncd/scripts/mutation-manifest.sh --out <exec>/papers/semantics/plan_layer_mutation_results.md <exec>/leanncd <exec>/papers/semantics/plan_layer_mutations_post.json
/usr/bin/git -C <exec> status --short
```

   Every entry must PASS (mutated build fails, file restored byte-identical, every `expect` seen).
   An `expect` miss on a cycle the record flags as reconstructed is fixed in the manifest from the
   observed log (copy the actual line), noted in the record, and re-run; any other miss is a finding.
   `git status --short` must show only the intended results file.
3. Whole-branch review, two lenses in parallel, findings appended to a file as they go:
   (a) soundness: R, `Valid` and `checkPlan_sound`, theorem hypotheses of `run_R`,
   `terminal_adequacy`, `done_correct`, `failed_correct`, `done_of_model`; §5 tables as the checklist;
   (b) spec-Lean fidelity: §8.1 edits against the Lean statements (names above).
   One fix dispatch per finding group.
4. Fill `papers/semantics/plan_layer_record.md` §Close-out (build, manifest table, reviews, token
   total via `python3 .claude/skills/slice-plan/token-report.py <session-id>`).
5. Merge to local `main` (`ExitWorktree` keep; `/usr/bin/git -C /Users/williammacready/code/python/pyncd merge --no-ff <branch>`),
   delete the branch, remove `<exec>`. The prototype branch `worktree-plan-layer-slice1` was never
   merged, so first tag its head (`/usr/bin/git -C /Users/williammacready/code/python/pyncd tag plan-layer-slice1-proto worktree-plan-layer-slice1`);
   the tag is KEPT, so the prototype commit history stays reachable. Then remove the prototype
   worktree `.claude/worktrees/plan-layer-slice1` and delete the branch with `git branch -D` (an
   unmerged branch needs `-D`). `git worktree remove` refuses while untracked files exist: the
   review files and `manifest_run.md` are committed in the controller's landing commit (§3.1), so
   only stray files remain, and a refusal is a stop to inspect them, not a reason to `--force`.
   The scratch worktree `pyncd.worktrees/plan-layer-emit` is removed with `git worktree remove` once
   `<exec>` is built (it was created for this slice). CLAUDE.md Rule 13 authorizes deleting this
   slice's own branches and worktrees; other sessions' worktrees (`pyncd.worktrees/*` other than
   `plan-layer-emit`, `.claude/worktrees/agent-*`) are never touched.
   No push: leave `main` ahead of `origin/main` and say so.

## 10. Open items

1. **Proof-status rows live in the spec, not the path doc.** The brief for this plan placed the
   Lemma 31.2 / Theorem 31.3 / Lemma 32.1 rows in the path doc; `rg` finds them only in the spec's
   `### Proof status and numbered results` table ("Not formalized."). §8.1 edits them there; the path
   doc gets section 4.9 instead. Controller: confirm.
2. **`checkCov1Complete`: keep or drop** (CHECKPOINT §3 decision 3). Kept: redundant at `checkPlan`
   (N6) but not diagnostic, since `complete_of_refState` consumes `hv.coverage1.2` (a3b §Decision
   log 7). Dropping it would mean rerouting `checkPlan_sound`'s `coverage1.2` through
   `accFlat_complete`: a small Direct-path change later. Spec wording (§8.1, as executed) says
   "redundant but kept in `Valid`"; change it if the user drops the check.
3. **Audit cells (§5): closed by the audit-cells slice** (Direct path, tests only, commits
   `99b07bcf`, `a830be4c`, `316bc888`, `08c974b0`, `42dc4914`, `5a24ca59`; fixtures in
   `PlanValidityTest.lean` and `PlanStepTest.lean`, hand mutants reported in the commit bodies, no
   production change, no new manifest entries). Backed with fixtures: the `checkInit` not-published
   half, the empty command of `stepCommand`, `stepPlan` at `pc ≥ m`, the already-published `execPub`
   and the within-group duplicate `execAcc` rows. EQUIVALENT at `checkPlan` (no fixture flips; the
   hand mutants break `checkPlan_sound` first): `checkPubFresh` (paired with `checkCov2Nodup`),
   `checkAccFresh` (paired with `checkCov1Nodup`), `checkAccMat` (every plan that fails it also
   trips `initFresh`, `pubMat` or `cov2Complete`; observed on the fixtures, not proved). The
   `checkCov1Nodup` / `checkCov2Nodup` pair with the two freshness checks is PROVED in
   `Validity.lean` (`checkPlan_nodup_redundant`, `checkPlan_eq_core`, `checkAccFresh_of_cov1Nodup`,
   `checkPubFresh_of_cov2Nodup`, commits `88fed829`, `8b7cc508`). Remaining: the by-design `execAcc`
   failing-member-order row, and a proof (not a fixture) that `checkAccMat` is implied by the other
   clauses; parked.
4. **A3b-2 is single-site.** The prototype dropped the `coverage2` field and its `checkPlan_sound`
   component (two sites); the manifest format takes one site per entry, so the cycle renames the
   field instead. It still shows that only `Correctness` consumes `coverage2` by name; the semantic
   witness remains `missingPub`.
5. **Reconstructed mutant texts.** The notes record mutant descriptions, not source. Every `new`
   string was written at authoring from those descriptions; cycles whose text or `expect` location is
   not verbatim are listed in the record. Validated: the full run on the shipped tree is 20/20 (§7).
6. **CHECKPOINT §2 says "9 modules `Plan*Test.lean`"**; manifest.json and the lakefile have 7 test
   modules plus `PlanFixtures` (8 files). This plan uses 7 + 1.
7. **manifest.json symbol extraction** lists three `(pc` entries for Syntax (instance binders);
   harmless, not corrected here (the patches are authoritative).
8. **D4, D7, D8, D11, D12.** D4 is discharged in Lean but not in the docs-sweep findings list; §8.1
   covers it implicitly through the R/Definition 31.1 restatement. D7, D8, D11, D12 were recovered
   from the originating session's design review and are recorded in `plan_layer_record.md`
   (section "Spec defects recovered"): D7 (no implementation-error constructor; deferred), D8
   (undefined "output view" in Section 32.3; fixed by cross-reference to the Publish premise of Section 29.2),
   D11 (multi-sort K unaddressed), D12 (`In ∩ Out` open).
9. **Pushing `main`**: not done; push only on explicit request (CHECKPOINT §3 decision 4).
10. **A2-e outside the valid domain: built and run** (commit `db15f986`, `PlanStepTest.lean`). The
    "transactional vs sequential commit equivalent" claim (§5.2, N5) holds only on `checkPlan`-valid
    plans. Two invalid plans, derived by the soundness review, distinguish the A2-e mutant; both are
    now fixtures with observed values: `a2e-seq-visible` (`pubOrder@1`; shipped final memory
    `[0,3,1]`, mutant `[0,3,4]`) and `a2e-failed-vs-stuck` (`accMat@1`, `pubMat@2`; shipped `failed`,
    mutant `stuck`). The mutant values were observed in a scratch run, not asserted by the build (the
    mutant breaks a proof in `Plan/Simulation.lean`, which stops every module that imports the
    aggregator). Both plans are pinned `checkPlan`-invalid by `invalid-a2e-seq-visible` and
    `invalid-a2e-failed-vs-stuck` (`PlanValidityTest.lean`, with `decide` examples). The valid
    neighbours `chainPlan` and `pPlan 2 failureAfterBody` agree under both kernels (the mutant side
    from the scratch run). The A2-b and A3a-a equivalences were confirmed by the reviewer for all plans (Q4).
