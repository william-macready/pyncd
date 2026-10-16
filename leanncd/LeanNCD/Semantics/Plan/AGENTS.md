# LeanNCD/Semantics/Plan

## Purpose
Owns: the Part V slices 1-5 plan layer (`LeanNCD.Semantics.Program.Plan`): commands (accumulate, publish, `initZero`, `retire`) over allocation-indexed memory, checked by `checkPlan`, run by `runPlan`, and related to the reference executor by `R`. Proves Lemma 32.1 (`batch_execution`), simulation (`step_R`, `step_failed`), Lemma 31.2 (`terminal_adequacy`) and Theorem 31.3 (`done_correct`, `failed_correct`, `done_or_failed`, `done_of_model`, `done_iff_model`), with fusion by expansion, retirement and typed static same-sort reuse. Slice 5 certifies bounded full-history scans with distinct retained buffers, all-command physical value retention and unconditional full typed output Decode.
Does not own: the reference executor (`../ReferenceExecutor.lean`, `../ExecutableState.lean`), the checked backend (`../../Eval/Plan/`), general scan recognition/two-buffer last-reader liveness, retiring inputs, copy/relocate, dynamic allocation, in-place kernels or cross-sort reuse.

Plan: `papers/semantics/plan_layer_plan.md`; current slice: `papers/semantics/plan_layer_slice5_plan.md` and `plan_layer_slice5_record.md`; spec Part V in `papers/semantics/tensor_logic_semantics.md` (29.3, 30.2-30.4, 31.1-31.4, 32.1, 33.1-33.4); path doc sections 4.9 and 5.2.

## Code Map
Reachable from `import LeanNCD` (`Semantics.lean` imports `Plan.lean`, which imports the eleven base modules below, then the scan umbrella).

| File | Owns |
|---|---|
| `Syntax.lean` | `Allocation` (finite buffers, sorts, capacities, typed `locate`), canonical default, `Command`, `Ann`, `Pub`/`Cons`/`Mat`/`Ret`/`Live`, `Coverage1`/`Coverage2`, allocation-preserving `expand` |
| `Batch.lean` | batched accumulation: `accumulateBatch`, `publishBlock`, `batch_execution` (Lemma 32.1), `block_execution` |
| `Memory.lean` | `Slot = InputSlot ⊕ BufferSlot`, allocation-indexed `Memory`/`Start`/`place`/`readSlot`/`Decode`, `SlotView`, `LayoutOK`, `layoutOK_of_canonical`, `readPub`, `refState`, `R` (unmapped-slot `dead`, `retPub`), `R_start`, `decode_of_R` |
| `Step.lean` | step kernels `execInit`/`execAcc`/`execPub`/`execRet`, `stepPlan`, `runFrom`, `runPlan`, `PlanOutcome` |
| `Simulation.lean` | `InitOK`/`AccOK`/`PubOK`/`RetOK`/`AnnOK`, `accFlat_complete`, `refState_R2`, `step_retire`, `readPub_le`, `step_R`, `step_failed` |
| `Validity.lean` | `Valid` (`retOK`, all-boundary `layout`), `resourceList`, `checkLayoutAt`/`checkLayouts` and exactness, `checkPlan_iff`, `checkPlan_of_canonical`, `checkRet`, `layout_boundary`, existing coverage/checker redundancy |
| `Run.lean` | `step_not_stuck`, `readPub_isSome` (over `Live`), `run_R`, `runPlan_R`, `runPlan_not_stuck` |
| `Correctness.lean` | `terminal_adequacy` (Lemma 31.2), `complete_of_refState`, `live_output_of_valid`, Theorem 31.3 (a)(b)(c) |
| `Fusion.lean` | `R_transport` (carries `Ret`/`Live`/`dead`/`retPub` along equal prefixes), fused-command fold lemmas `execAnns_R`, `step_R_command`, `step_failed_command`, `stepCommand_not_stuck` (the fold `execAnns` and `stepCommand` are in `Step.lean`, `execAnns_not_stuck` in `Run.lean`); run bridge `runFrom_agree`, `runPlan_agree` (`expand`/`offset` live in `Syntax.lean`, `execAnns` in `Step.lean`) |
| `FusionCorrectness.lean` | `FValid`, `checkPlanF`, `checkPlanF_sound`, `runFrom_R_F` (mid-run, any command boundary), `runPlan_R_F`, `runPlan_not_stuck_F`, `terminal_adequacy_F`, `done_correct_F`/`failed_correct_F`/`done_or_failed_F`/`done_of_model_F`/`done_iff_model_F` |
| `Faults.lean` | implementation errors (D7) as a wrapper: `ImplErr`, oracle `Faults`, `FOutcome = run \| error`, `runFromE`/`runPlanE` (kernels, `StepResult` and `PlanOutcome` untouched); `runFromE_noFault`, `runFromE_run`, `runFromE_error`; slice-1 `done_correct_E`, `failed_correct_E`, `runPlanE_not_stuck`; fused `done_correct_FE`, `failed_correct_FE`, `runPlanE_not_stuck_FE`; error-free profile `ErrorFreeRun`, `NoFaultsInPlan`, `errorFreeRun_of_noFaultsInPlan`, `done_or_failed_FE`, `done_of_model_FE`, `done_iff_model_FE`, `error_despite_model`; `R` at the error state `runFromE_error_R`, `runPlanE_error_R` |
| `ScanHistory.lean`, `ScanHistory/` | independent `history`; typed `RegisteredF`, Program/allocation/schedule; evaluation and collected-equation model bridge; Coverage1/2; all-phase prefixes; `plan_valid`, `plan_checkPlan`; actual `prefix_done_R`, `history_retained`/`history_retained_later`; unconditional `scan_done`, `scan_decode_history`, independent `scan_denotation_history` |

## Contracts
- A fused plan is valid iff its expansion is (`FValid := π.expand.Valid`); `done m` counts commands, not expanded annotations.
- Slice-1-4 profile: singleton or fused commands, typed static same-sort reuse, boundary-local layout injectivity, transactional failure and explicit `initZero`. Canonical allocation remains globally injective. Inputs are separate; outputs cannot be retired. Theorems are sort-generic (`K : S → Type`); `PlanMultiSortTest` and `PlanReuseStorageTest` use ℤ/ℚ with an empty registry (no cross-sort reads). Faults are an abstract wrapper.
- Slice-5 scan: any natural `d,N`, `AddCommMonoid V`, certified total unary same-sort array F in an existing registry, every validated input; H has shape `(d,N+1)` and is the sole output. One capacity-d buffer per time slice, no retire/reuse/copy. Entire previous-slice readiness and actual physical values are proved at every command boundary. Empty tensors still require input presence; typed Decode succeeds even when there are no coordinates.
- `runPlan` does not detect schedule-invalid plans. Soundness rests on `checkPlan` (`checkPlan_sound : π.checkPlan = true → π.Valid`); `checkPlan_complete` gives the converse (`checkPlan_iff`; fused: `checkPlanF_iff`), so the checker decides `Valid` exactly. `checkAccMat` is redundant given the other clauses (`checkAccMat_of_rest`), and is kept.
- `Valid` is purely static. The spec's semantic conditions 2-5 are the theorems `R_start`, `step_R` (only at `refState pc = some c`, next bullet), `step_failed`, `step_not_stuck`.
- `Pub` is the logical published set, `Live = Pub \ Ret` the readable one; a retired address stays in `Pub` and in `dom σ`.
- `step_R` needs `refState pc = some c` and pre/post `LayoutOK` besides `R`; init uses post-layout, acc/retire pre-layout, pub/failure add none. Simulation is not claimed for every R-related state.
- `R.dead` ranges over unmapped physical slots, not retired logical addresses' placements: a freed slot may later contain another resource. Prefix transports require allocation equality and dependent memory casts.
- Theorem 31.3 (b) claims failure and no model only; the failure snapshot may differ from `Executor.run`'s own schedule.

## Pitfalls
- Inside `Program.Plan` write `Executor.consume`/`Executor.publish`; bare names resolve to the noncomputable `Program` versions.
- Force `List.decidableBAll` for bounded quantifiers; instance search otherwise picks `Fintype.decidableForallFintype` through the noncomputable `definedFintype`.
- `prefix` is a Lean keyword: the prefix is `prefixAnn`.
- `Layout` is already taken: the spec's layout view is `SlotView`.
- A trivialised mutant must keep its `π` parameter.
- Reads go through `Live`, not `Pub`: `readPub pc M = c.published` is false after a retire; use `readPub_eq` (pointwise on `Live`) and `readPub_le`.
- `R` has a field `retPub` beyond the spec's R1-R5: a hand-built `R` (`R_start`, `R_transport`) needs both `dead` and `retPub`.
- The canonical invalid output-retire and second-retire fixtures still run to `done`; their rejection is static. With reuse, a second retire can clear a new occupant and make a later command `stuck`.
- `StepResult` has no `DecidableEq`: R-at-every-pc fixtures are proofs by `rfl`, not `decide`.
- Not the checked backend: `Semantics/Plan` (`Program.Plan.checkPlan`, the Part V reference plan) is unrelated to `Eval/Plan` (`CheckedEvalPlan`, whose own `checkPlan` is in `Eval/Plan/EvalPlan.lean`); no theorem connects them.
- Singleton `checkSteps` is vacuous on a fused command, and `checkSingleton` rejects non-singletons. Outer layouts alone miss internal collisions: use `checkPlanF`, soundness `checkPlanF_sound`.
- A fused `failed` reports the pre-command memory, and `PlanOutcome.Agree` ignores pc and failure memory.
- Mutation manifests: `plan_layer_mutations_post.json` (20), `plan_layer_slice2_mutations_post.json` (15), `plan_layer_d7_mutations_post.json` (9), `plan_layer_slice3_mutations_post.json` (10), `plan_layer_slice4_mutations_post.json` (10), all under `papers/semantics/`. Run unfiltered with `leanncd/scripts/mutation-manifest.sh`. All 64 controls are verified with failure-site anchors; results are under `plan_layer_slice4_mutation_results/`. Distinguish library-proof controls from fixture kills and inherited equivalence controls.
- Scan controls: `plan_layer_slice5_mutations_post.json`; measured classifications, exact anchors, duplicate-phase consolidation and actual final gates are in `plan_layer_slice5_record.md`. Historical prototype fixture kills are not current numeric kills behind generic-proof barriers.

## Fixtures
`test/Semantics/Plan*Test.lean`: 516 fixtures (239 `#eval check`, 277 top-level `example`/`theorem`). All 367 inherited fixtures are preserved. `PlanScanHistoryTest` adds 138 (47 evaluated, 91 proof), independent `PlanScanHistoryOracleTest` adds 11 (6 evaluated, 5 proof). Default `Tests` has 18 Plan test modules plus the shared `PlanFixtures` module (19 total). The three reuse modules retain 31 core, 26 storage and 25 wrapper fixtures.

`leanncd/scripts/buffer-fixture-probes.py` closes slice-3 O3 and the reuse probe gaps: all ten retirement substitutions and six reuse computational substitutions have independently observed component kills and clean controls. S4-M6 additionally kills an isolated copy of the unused-slot consumer. These 17 probes complement the three existing reuse fixture controls, covering all 20 buffer controls beyond library-proof barriers. Production proofs remain untouched; the source-copy probes are not claimed as whole mutated executor runs.
