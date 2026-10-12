# Part V slice 4: typed buffer reuse and alias safety

Status: compiled prototype is the implementation; remaining validation and
integration gates are **PENDING**. Base: local `main` at `4ffdc342`.
Approved contract: `docs/superpowers/specs/2026-10-11-buffer-reuse-aliasing-design.md`.
Execution evidence belongs in `plan_layer_slice4_record.md`, not this live plan.

## 1. Process and execution constraints

**Full path:** physical storage, placement, validity and refinement interfaces
change; this is a new soundness surface, not a localized guard addition.
This is the required fresh authoring dispatch after the compiled prototype.
The prototype used the real module split and namespace and already delivered
production and fixtures. Do not revert or reapply it to simulate fresh execution.
Mechanical per-task patches provide reproducibility; the controller is checking
ordered replay from the base with an isolated index, without changing live code.
Replay verification is pending until its result is recorded.

Worktree: `/Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan`.
Use plain separate shell commands, absolute paths and `/usr/bin/git -C` for git.
No shell variables, chained directory changes, pipelines into git, destructive
reset/checkout, or `.claude/settings.json` in a commit. Stage explicit paths only.
Build only through `leanncd/scripts/lake-build.sh` with the absolute Lean directory.
The controller owns mutation cycles and builds; concurrent readers must use the
immutable compiled snapshot while cycles temporarily mutate production files.

Authoring verification uses the `deb4fecd` archive under
`/Users/williammacready/.copilot/session-state/faaa5884-f669-4d5f-808f-1790f4b3e9db/files/slice4-snapshot/`.
Briefs name identifiers and files below; locate with `rg -n`, then read 40–60-line
windows around those symbols. Do not whole-file-read large modules.
Dispatch caps: authoring 35 turns / 250k context; other fresh work at most
60 turns / 250k, narrowed further by the controller. Split findings by group.
Historical cap breaches and unavailable cumulative usage are recorded separately.

## 2. Fixed contract and sibling audit

- `Allocation` has explicit complete duplicate-free finite buffers, computable
  equality, per-buffer sort/capacity and bounded sort-certified `locate`.
  `Allocation.canonical` retains one buffer per tensor as the default.
- `Slot` is `InputSlot P ⊕ BufferSlot A`; defined placement cannot target input
  storage. `Memory`, `Start`, `place`, `readSlot`, `Decode`, `StepResult`,
  `PlanOutcome` and `FOutcome` are allocation-indexed. `expand` keeps allocation.
- `SlotView` represents `Live` published resources and `Mat`-but-not-`Pub`
  accumulators. `LayoutOK` is injectivity on that domain, not global placement.
  `Valid.layout` quantifies over every boundary including the final one.
- `checkLayouts` enumerates resource pairs over `range (commands.length + 1)`.
  `checkPlan_iff` and `checkPlanF_iff` remain exact; fused checks use expansion.
- `step_init` needs post-layout; `step_acc` and `step_retire` need pre-layout;
  `step_R` carries both. Publication/failure add no layout premise.
- `R.dead` says **every unmapped physical slot is `none`**, including unused
  capacity. It does not say a retired address's former slot remains empty.
  `retPub` and ghost history remain; kernels/decoder cannot read ghosts.
- `execAnn_prefix`, `R_transport` and `decode_prefix_congr` require allocation
  equality and transport memory by the corresponding dependent cast.
- Kernels remain non-in-place; reads precede writes. No scan program/liveness,
  relocation/copy, dynamic allocation, input retirement, cross-sort reuse,
  snapshots, concrete fault sources or `Eval/Plan` connection is added.

Audit unchanged siblings, not only changed lines:

| Family / sibling | Required | Forbidden | Silently ignored / limit |
|---|---|---|---|
| `SlotView`, `checkLayoutAt`, `resourceList` | pub/pub, pub/acc and acc/acc separation | any co-live collision | inactive and retired resources reserve no slot |
| `checkLayouts`, `checkPlanF` | initial, final and expanded internal boundaries | checking only outer fused boundaries | `checkSteps` is vacuous for non-singletons; use `checkPlanF` |
| `execInit`, `execAcc`, `execPub`, `execRet` | zero freshness, pre-write reads, role change, exact clearing | clearing survivors or reading ghosts | unchecked aliases can finish with corrupt values |
| `readPub`, `Decode`, `R.dead`, `R.retPub` | Live-only reads, physical outputs, empty unused slots | decoding from history or default zero | ghost store retains retired values |
| `runFrom`, `runPlan`, `runFromE`, `runPlanE` | allocation preserved, fault/error-state R, no-fault parity | treating errors as semantic failure | no runtime alias detector; oracle is abstract |

## 3. Executed prototype tasks and mechanical patches

All patch names below are relative to `papers/semantics/plan_layer_slice4_patches/`.
They were generated mechanically from committed prototype code, not transcribed
into this document. Apply in order only in the controller's isolated replay.
Compilation is observed; mutation kills are not yet observed for this branch.

| Task | Prototype checkpoint | Patch |
|---|---|---|
| T1 storage/kernel foundations | `b6f05490` | `0001-feat-semantics-prototype-typed-physical-buffers-and-.patch` |
| T2 local simulation | `41cb1829` | `0002-feat-semantics-prove-alias-safe-plan-step-simulation.patch` |
| T3 checker/run/correctness | `c615fb9b` | `0003-feat-semantics-decide-boundary-local-layout-safety-e.patch` |
| T4 fused/fault wrappers | `832ad70d` | `0004-feat-semantics-carry-physical-reuse-through-fused-an.patch` |
| T5 canonical regressions | `763e5403` | `0005-test-semantics-preserve-canonical-plan-regressions-u.patch` |
| T6 actual-reuse regressions | `deb4fecd` | `0006-test-semantics-verify-real-buffer-reuse-and-alias-re.patch` |

### T1–T4 production verification windows

File names in this subsection are relative to `leanncd/LeanNCD/Semantics/Plan/`.
These are executed checkpoints; fix only concrete review or mutation findings.

- **T1:** `Allocation`, `Allocation.canonical`, `Plan.allocation`, `expand` @
  `Syntax.lean`; `InputSlot`, `BufferSlot`, `Slot`, `place`, `place_sort`,
  `place_injective`, `readSlot`, `Start`, `Decode`, `R`, `R_start` @ `Memory.lean`;
  `execInit`, `execAcc`, `execPub`, `execRet`, `StepResult`, `PlanOutcome`,
  `execAnn_prefix` @ `Step.lean`. Patch also contains the approved design.
  Risk: dependent sort/slot transports; 0 new fixtures here, S4-M6 control.
- **T2:** `LayoutOK`, `LayoutOK.ne`, `SlotView` @ `Memory.lean`;
  `step_init`, `step_acc`, `step_pub`, `step_retire`, `step_R`, `step_failed` @
  `Simulation.lean`. Verify pre/post premise placement and survivor writes.
  Risk: alias-sensitive refinement; 0 new fixtures here, S4-M5/M7 controls.
- **T3:** `resourceList`, `mem_resourceList`, `checkLayoutAt`,
  `checkLayoutAt_iff`, `checkLayouts`, `checkLayouts_iff`, `Valid.layout`,
  `Valid.layout_boundary`, `checkPlan_iff` @ `Validity.lean`; `step_not_stuck`,
  `run_R`, `runPlan_R` @ `Run.lean`; `terminal_adequacy`,
  `live_output_of_valid`, `done_iff_model` @ `Correctness.lean`.
  Risk: exact finite enumeration and last boundary; 0 new fixtures here,
  S4-M1–M4 controls.
- **T4:** `R_transport`, `execAnns_R`, `step_R_command`, `runPlan_agree` @
  `Fusion.lean`; `decode_prefix_congr`, `FValid`, `checkPlanF_iff`,
  `runFrom_R_F`, `terminal_adequacy_F`, `done_iff_model_F` @
  `FusionCorrectness.lean`; `FOutcome`, `runFromE`, `runPlanE_error_R`,
  `runPlanE_noFault`, `done_iff_model_FE` @ `Faults.lean`.
  Risk: dependent memory casts and expanded positions; 0 new fixtures here,
  inherited fusion/D7 controls are validated at T7.

### T5 canonical preservation

Files under `leanncd/test/Semantics/`: `PlanFixtures.lean`,
`PlanMemoryTest.lean`, `PlanStepTest.lean`, `PlanSimulationTest.lean`,
`PlanValidityTest.lean`, `PlanRunTest.lean`, `PlanCorrectnessTest.lean`,
`PlanFusionTest.lean`, `PlanFusionCheckerTest.lean`,
`PlanFusionCorrectnessTest.lean`, `PlanFaultsTest.lean`,
`PlanMultiSortTest.lean`, `PlanRetireTest.lean`.
Donors are each existing assertion in place: change only allocation-dependent
APIs/proofs, not expected outcomes. `PlanBatchTest.lean` stays unchanged.
Read `PlanFixtures.finalMemory`, then 40–60-line windows around each changed
consumer. Risk: losing oracle strength in migration; **281 preserved fixtures**
(149 `#eval check`, 132 top-level `example`/`theorem`), **54 inherited cycles**.
All 14 existing Plan test targets remain registered.

### T6 fixture dispatches (already executed separately)

Patch 6 includes three new test files and their registrations in
`leanncd/lakefile.toml`. Total **73 new fixtures**: core 26, storage 22, wrapper 25.
The three controls below test fixture discrimination; the seven production
controls instead fail at library proofs and are not fixture-level kill evidence.

| Dispatch | Files / donor transformations | Risk / counts |
|---|---|---|
| T6a core | `PlanReuseTest.lean`: clone `rtInitAfter` as `reuseGood`, change point 2 placement to retired point 0; `reuseBad` changes only placement to live point 1; `reusePubPair`/`reuseAccPair` use `unitPlan`, `cAddr`, `cOcc` and bad/separate allocations | actual overwrite, ghost separation, pair classes and final boundary; 26 fixtures, S4-F1/F2 |
| T6b storage | `PlanReuseStorageTest.lean`: `scalarRole`, `scalarPlan`, `rtScalar` donate the internal-to-output `reuse`; `PlanMultiSort.pl` donates `typed` with new physical banks; `emptyRole false` donates `emptyOutput` | tensor identity vs buffer identity, heterogeneous carriers, real outputs; 22 fixtures, 0 dedicated manifest controls |
| T6c wrappers | `PlanReuseWrapperTest.lean`: clone `reuseGood`, fuse retire-then-init as `reuseFused`; reverse only those annotations as `reuseFusedConflict`; use `faultAt`, `chainRowE`, `R_every_pc_F_of` from `PlanRetireTest` | internal boundary hidden by fusion, post-write error state; 25 fixtures, S4-F3 |

Open 40–60-line windows around `reuseGood_R_every_pc`,
`reuseGood_unused_dead_every_pc`, `reuseRoles`, `reuse_valid`, `typedDecode`,
`reuseFused_R_every_pc`, `reuseFused_fault_after_write`, `reuseFused_error_R`.
No claim that all 73 fixtures have individual mutation kills: dedicated controls
are only F1–F3; review must assess the uncovered storage/typed/retention oracles.

Measured compiled expectations (not newly executed by the author):

- Good singleton: accepted, `done 7`, raw logical-address slot row `[4,3,4]`,
  empty decode `[]`; shared physical slot at pc 4–7 is `[none,0,4,4]`;
  retired read `none`, ghost 0, new read 4; R at every boundary 0–7 and
  unused capacity/buffer `none`.
- Bad singleton: rejected, unchecked `done 7`, row `[none,1,1]`;
  live point 1 reads 1 while its logical ghost value is 3.
- Pair components distinguish bad/separate placement for pub/pub at pc 6,
  pub/acc at pc 4, acc/acc at pc 1. The final-boundary component is true at 0,
  false at 1 and false overall; its separate-placement neighbor is true.
- Cross-tensor: internal tensor 2 and output tensor 1 share workspace index 0,
  accepted `done 7`, decoded output 2 matches both canonical donors;
  old read `none`, ghost 3, spare capacity `none`. Retention conflicts reject.
- Typed: Bool logical sorts with ℤ/ℚ carriers and independent physical banks;
  accepted `done 3`, decode `(11,7/8)` matches canonical; unused capacity
  remains `none`. Empty output: `done 0`, zero capacity and successful decode.
- Fused good: accepted `done 6`, R at 0–6, expansion equals `reuseGood`.
  Bad order: all 7 outer layouts true, 8 expanded layouts false only at index 4;
  `checkPlanF = false`, unchecked `stuck 4`, row `[none,3,none]`.
- Fault after reused-slot write: `error` at command pc 5, row `[4,3,4]`,
  physical value 4 / old read `none` / ghost 0, with error-state R.
  No-fault parity and error-free model theorems remain proved.

## 4. Remaining execution tasks

### T7 controller mutation/replay gate — PENDING

Dependencies: T1–T6; ordered patch replay and byte-identical mutation restoration.
All inherited old strings are unique under unfiltered `--check` on the compiled
tree. New manifest: 10 entries, 7 library-proof controls + 3 fixture controls.
`expect` strings are manifest expectations, **not observed slice-4 failures**.
Run all five manifests unfiltered; do not substitute `--check` for actual cycles.
Results go under `papers/semantics/plan_layer_slice4_mutation_results/`.

```sh
bash /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/plan_layer_slice4_mutation_results/slice1.md /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/plan_layer_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/plan_layer_slice4_mutation_results/slice2.md /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/plan_layer_slice2_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/plan_layer_slice4_mutation_results/d7.md /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/plan_layer_d7_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/plan_layer_slice4_mutation_results/slice3.md /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/plan_layer_slice3_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/plan_layer_slice4_mutation_results/slice4.md /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/plan_layer_slice4_mutations_post.json
```

Risk: 64 cycles, inherited equivalent controls distinguished from kills.
Record actual failure diagnostics, caught-at-proof versus caught-at-fixture,
restoration hashes, equivalent adjudications and replay results. A failed
`expect` match is not success; repair only from observed diagnostics.

### T8 documentation/discoverability — authoring complete, controller review pending

Files: this plan and record; `tensor_logic_semantics.md`;
`lean_executable_semantics_path.md`; `leanncd/LeanNCD/Semantics/AGENTS.md`;
`leanncd/LeanNCD/Semantics/Plan/AGENTS.md`; approved design status/prototype facts.
Only "As formalized" paragraphs, proof-status rows and profile labels change
in the general specification. Preserve mathematical contract text and historical
slice records. Risk: stale claims / overclaiming; 0 fixtures, 0 mutation cycles.
Current count is **354 = 174 rows + 180 proof items**, baseline 281 preserved.
Seventeen Plan test targets are registered (14 old + 3 new); `PlanFixtures` is
a separate shared target. New tests are in default `Tests`; the library remains
reachable from `import LeanNCD`.

Run the value sweep, inspect hits and classify historical vs current:

```sh
rg -n -l --glob '*.md' '281|149|132|dense injective|never.?reused|no Lean.{0,30}reuse' /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan
rg -n --no-filename '281|149|132|dense injective|never.?reused|no Lean.{0,30}reuse|slice-1 to slice-3' /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/tensor_logic_semantics.md /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/papers/semantics/lean_executable_semantics_path.md /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd/LeanNCD/Semantics/AGENTS.md /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd/LeanNCD/Semantics/Plan/AGENTS.md
```

### T9 two fresh whole-branch reviews — PENDING

Dependencies: T7/T8; read the complete base-to-branch diff, not just patch 6.
Soundness lens: dependent allocation casts, all write kernels, `R.dead`,
resource-pair enumeration and boundary quantification, wrapper error states.
Fidelity lens: D1–D6, canonical assertion preservation, physical observations,
retained output decoding, final/internal discriminators and truthful scope.
Read 40–60-line windows; append findings incrementally to controller-owned
review artifacts. Limit each dispatch to 60 turns / 250k; narrow fixes by group,
then rerun affected tests/cycles. Both reviews must be clean or adjudicated.

### T10 controller final build and local integration — PENDING

Dependencies: T7–T9; after restoring all mutation files:

```sh
bash /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/implement-buffer-reuse-aliasing-plan/leanncd
```

The pre-cycle controller full build already passed 8796 jobs; its actual
`Semantics.AxiomAudit` build audited 5992 constants with standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`).
This is evidence, not a substitute for the final post-cycle gate. Four inherited
sorry warnings remain in Base/St, Base/Br, Core/Weave and Instances/StBr.
Require no new `sorry`, `admit`, `axiom` or `native_decide` in Plan production/tests.
Record results, skips, deviations and unavailable token accounting honestly.
Commit explicit deliverables; merge to local `main` only after all gates, then
remove this task's branch/worktree. No remote push.
