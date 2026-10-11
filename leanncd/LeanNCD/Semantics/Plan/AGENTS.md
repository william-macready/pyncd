# LeanNCD/Semantics/Plan

## Purpose
Owns: the Part V slices 1-3 plan layer (`LeanNCD.Semantics.Program.Plan`): a plan is a list of commands (accumulate, publish, `initZero`, `retire`) over dense memory; it is checked by the computable `checkPlan`, run by `runPlan`, and related to the reference executor by relation `R`. Proves Lemma 32.1 (`batch_execution`), one-step simulation (`step_R`, `step_failed`), Lemma 31.2 (`terminal_adequacy`) and Theorem 31.3 (`done_correct`, `failed_correct`, `done_or_failed`, `done_of_model`, `done_iff_model`) for the slice-1 profile, and for fused commands by expansion (slice 2: `FValid`, `checkPlanF`, `*_F` theorems), and for retirement of defined published addresses (slice 3: `Ann.retire`, `Live`, `RetOK`, `step_retire`).
Does not own: the reference executor (`../ReferenceExecutor.lean`, `../ExecutableState.lean`), the checked evaluation backend (`../../Eval/Plan/`), buffer reuse and aliasing, scan liveness, retiring inputs, copy/relocate, cross-sort primitives in fixtures.

Plan: `papers/semantics/plan_layer_plan.md` (slice 3: `papers/semantics/plan_layer_slice3_plan.md`); spec Part V in `papers/semantics/tensor_logic_semantics.md` (29.3, 30.2-30.4, 31.1-31.4, 32.1, 33.2); path doc section 4.9.

## Code Map
Reachable from `import LeanNCD` (`Semantics.lean` imports `Plan.lean`, which imports the eleven modules below in this order).

| File | Owns |
|---|---|
| `Syntax.lean` | `Command`, `Ann` (incl. `retire`), occurrence/publication keys, `Pub`/`Cons`/`Mat`/`Ret`/`Live` per command prefix (`retList`), `Coverage1`/`Coverage2`, `coverage_iff_schedule` |
| `Batch.lean` | batched accumulation: `accumulateBatch`, `publishBlock`, `batch_execution` (Lemma 32.1), `block_execution` |
| `Memory.lean` | dense `Memory`, `place`, `SlotView`, `readPub`, partial `Decode`, `refState`, relation `R` (fields `dead`, `retPub`), `readPub_eq` (pointwise on `Live`), `R_start`, `decode_of_R` |
| `Step.lean` | step kernels `execInit`/`execAcc`/`execPub`/`execRet`, `stepPlan`, `runFrom`, `runPlan`, `PlanOutcome` |
| `Simulation.lean` | `InitOK`/`AccOK`/`PubOK`/`RetOK`/`AnnOK`, `accFlat_complete`, `refState_R2`, `step_retire`, `readPub_le`, `step_R`, `step_failed` |
| `Validity.lean` | `Valid`, computable `checkPlan` and its component checks, `checkPlan_sound`, `checkRet`, field `Valid.retOK`, `checkPlan_nodup_redundant` (the two Nodup checks follow from singleton + `checkSteps`) |
| `Run.lean` | `step_not_stuck`, `readPub_isSome` (over `Live`), `run_R`, `runPlan_R`, `runPlan_not_stuck` |
| `Correctness.lean` | `terminal_adequacy` (Lemma 31.2), `complete_of_refState`, `live_output_of_valid`, Theorem 31.3 (a)(b)(c) |
| `Fusion.lean` | `R_transport` (carries `Ret`/`Live`/`dead`/`retPub` along equal prefixes), fused-command fold lemmas `execAnns_R`, `step_R_command`, `step_failed_command`, `stepCommand_not_stuck` (the fold `execAnns` and `stepCommand` are in `Step.lean`, `execAnns_not_stuck` in `Run.lean`); run bridge `runFrom_agree`, `runPlan_agree` (`expand`/`offset` live in `Syntax.lean`, `execAnns` in `Step.lean`) |
| `FusionCorrectness.lean` | `FValid`, `checkPlanF`, `checkPlanF_sound`, `runFrom_R_F` (mid-run, any command boundary), `runPlan_R_F`, `runPlan_not_stuck_F`, `terminal_adequacy_F`, `done_correct_F`/`failed_correct_F`/`done_or_failed_F`/`done_of_model_F`/`done_iff_model_F` |
| `Faults.lean` | implementation errors (D7) as a wrapper: `ImplErr`, oracle `Faults`, `FOutcome = run \| error`, `runFromE`/`runPlanE` (kernels, `StepResult` and `PlanOutcome` untouched); `runFromE_noFault`, `runFromE_run`, `runFromE_error`; slice-1 `done_correct_E`, `failed_correct_E`, `runPlanE_not_stuck`; fused `done_correct_FE`, `failed_correct_FE`, `runPlanE_not_stuck_FE`; error-free profile `ErrorFreeRun`, `NoFaultsInPlan`, `errorFreeRun_of_noFaultsInPlan`, `done_or_failed_FE`, `done_of_model_FE`, `done_iff_model_FE`, `error_despite_model`; `R` at the error state `runFromE_error_R`, `runPlanE_error_R` |

## Contracts
- A fused plan is valid iff its expansion is (`FValid := π.expand.Valid`); `done m` counts commands, not expanded annotations.
- Slice-1-3 profile: singleton or fused commands, dense injective buffers (a retired slot is cleared, never reused), transactional failure, explicit `initZero`, no implementation errors. The theorems are generic over sorts (`K : S → Type`); the fixtures use rationals, except `PlanMultiSortTest` (ℤ and ℚ with per-sort `ScalarOps`, empty registry, so no cross-sort reads).
- `runPlan` does not detect schedule-invalid plans. Soundness rests on `checkPlan` (`checkPlan_sound : π.checkPlan = true → π.Valid`); `checkPlan_complete` gives the converse (`checkPlan_iff`; fused: `checkPlanF_iff`), so the checker decides `Valid` exactly. `checkAccMat` is redundant given the other clauses (`checkAccMat_of_rest`), and is kept.
- `Valid` is purely static. The spec's semantic conditions 2-5 are the theorems `R_start`, `step_R` (only at `refState pc = some c`, next bullet), `step_failed`, `step_not_stuck`.
- `Pub` is the logical published set, `Live = Pub \ Ret` the readable one; a retired address stays in `Pub` and in `dom σ`.
- `step_R` needs `refState pc = some c` besides `R`; simulation is not claimed for every R-related state.
- Theorem 31.3 (b) claims failure and no model only; the failure snapshot may differ from `Executor.run`'s own schedule.

## Pitfalls
- Inside `Program.Plan` write `Executor.consume`/`Executor.publish`; bare names resolve to the noncomputable `Program` versions.
- Force `List.decidableBAll` for bounded quantifiers; instance search otherwise picks `Fintype.decidableForallFintype` through the noncomputable `definedFintype`.
- `prefix` is a Lean keyword: the prefix is `prefixAnn`.
- `Layout` is already taken: the spec's layout view is `SlotView`.
- A trivialised mutant must keep its `π` parameter.
- Reads go through `Live`, not `Pub`: `readPub pc M = c.published` is false after a retire; use `readPub_eq` (pointwise on `Live`) and `readPub_le`.
- `R` has a field `retPub` beyond the spec's R1-R5: a hand-built `R` (`R_start`, `R_transport`) needs both `dead` and `retPub`.
- Retiring an output or retiring twice still runs to `done`: only `checkPlan` rejects it.
- `StepResult` has no `DecidableEq`: R-at-every-pc fixtures are proofs by `rfl`, not `decide`.
- Not the checked backend: `Semantics/Plan` (`Program.Plan.checkPlan`, the Part V reference plan) is unrelated to `Eval/Plan` (`CheckedEvalPlan`, whose own `checkPlan` is in `Eval/Plan/EvalPlan.lean`); no theorem connects them.
- Slice-1 `checkSteps` is vacuous on a fused command (slice-1 `checkPlan` rejects a fused plan only via `checkSingleton`): use `checkPlanF`, soundness `checkPlanF_sound`.
- A fused `failed` reports the pre-command memory, and `PlanOutcome.Agree` ignores pc and failure memory.
- Mutation cycles: `papers/semantics/plan_layer_mutations_post.json` (20 cycles) and `papers/semantics/plan_layer_slice2_mutations_post.json` (15 cycles) and `papers/semantics/plan_layer_d7_mutations_post.json` (9 cycles, all caught at the proofs of `Faults.lean`, not by `PlanFaultsTest`), and `papers/semantics/plan_layer_slice3_mutations_post.json` (10 cycles, all caught at library proofs), run with `leanncd/scripts/mutation-manifest.sh`; results in `papers/semantics/plan_layer_mutation_results.md` (slice 1), `plan_layer_slice2_mutation_results.md` and `plan_layer_slice3_mutation_results.md`.
