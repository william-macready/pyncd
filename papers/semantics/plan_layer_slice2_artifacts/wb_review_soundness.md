# Plan slice 2 (fusion): whole-branch SOUNDNESS review

Scope: `git diff 03a2372f 003080b2 -- leanncd` (T1-T4) and docs commit bc888183, against plan sections 1-2.
Findings of the authoring review (`review_soundness.md`, S-1..S-5) are not repeated. Read-only; no build
run (evidence by Read / `rg -n`). Findings appended incrementally.

Result: 0 Critical, 1 Important (docs), 5 Minor. No unsound Lean statement, no vacuous theorem, no checker hole
found; the Important finding is a false docs claim about the slice-1 checker.

## W-1 (Important, docs) path doc 4.9 says a mis-fused plan passes `checkPlan` and yields a wrong value

- File / identifier: `papers/semantics/lean_executable_semantics_path.md` lines 1121-1122 ("Fused commands (slice 2)").
- Claim: "The slice-1 `checkSteps` is vacuous on a fused command, so a mis-fused plan passes `checkPlan` and runs
  to `done` with a wrong value (`misfused-run-undetected`); `checkPlanF` rejects it."
- Evidence: (a) `checkPlan := checkSingleton && ... && checkSteps` (`Validity.lean:137-139`), and
  `checkSingleton` is `cmd.length == 1` for every command (`Validity.lean:91`), so NO fused plan passes
  `checkPlan`. The shipped fixture says so: `fusedcorr-misfused-verdicts` expects slice-1 verdict
  `(false, ["singleton"])` (`PlanFusionCorrectnessTest.lean:67-69`). Only `checkSteps` is vacuous
  (`misfused-slice1-checkSteps-vacuous`, `(true, false)`). (b) The cited fixture `misfused-run-undetected`
  expects `("done", 1, none, [3/4, 0, 0])` (`PlanFusionTest.lean:73-75`), the SAME memory as the valid
  `fused-reciprocal-all` (`PlanFusionTest.lean:25-26`); its own comment says "same value, `done`". The
  mis-fusion (pub before acc) is a pure role change at run time, so the value is correct. The silent
  wrong-value case is a5 (`t4-a5-reinitMid`, `[0,10,0]` vs 14). The spec's own sentence (31.1 slice-2
  paragraph, `tensor_logic_semantics.md:4249-4250`, "Runtime execution still does not detect an invalid
  fusion") is correct.
- Why it matters: the sentence tells a reader the slice-1 checker is unsound on fused plans (it is not:
  it rejects all of them) and that the cited fixture exhibits a wrong value (it does not).
- Suggested fix: "The slice-1 `checkSteps` is vacuous on a fused command (`checkPlan` rejects every fused plan
  only through `checkSingleton`), and the run does not detect a mis-fused plan: `misfused-run-undetected`
  runs to `done`, and `t4-a5-reinitMid` runs to `done` with a wrong value; `checkPlanF` rejects both."
- Second location, same error: `leanncd/LeanNCD/Semantics/Plan/AGENTS.md` Pitfalls bullet "Slice-1 `checkPlan` is
  vacuous on a fused command (`checkSteps` accepts it): use `checkPlanF`." `checkPlan` is not vacuous (it
  rejects every fused plan via `checkSingleton`); `checkSteps` is. Fix: "Slice-1 `checkSteps` is vacuous on a
  fused command (`checkPlan` rejects fused plans only through `checkSingleton`): use `checkPlanF`."

## W-2 (Minor) `step_failed_command` states less than the docs say

- File / identifier: `leanncd/LeanNCD/Semantics/Plan/Fusion.lean:step_failed_command` (and `execAnns_failed`).
- Claim (path doc 4.9 table, `lean_executable_semantics_path.md:1107`): "A failing fused command is matched by the
  reference run of its earlier annotations and then one `undefined` event for the same occurrence"; spec 31.3
  slice-2 paragraph (`tensor_logic_semantics.md:4330-4333`): "The reference runs the earlier annotations of the
  command and then fails with the same occurrence o ... the matched reference snapshot is the state after those
  earlier annotations"; docstring: "the reference runs the earlier annotations of the command and then fails on `o`".
- Evidence: the statement is `∃ c' events, Execution P ops events (.running c) (.failed o.1 o.2 c')`: the event
  list and `c'` are existential. The proof does build `ev ++ [.undefined o.1 o.2]` with `ev` from `step_R` of the
  earlier annotations (Fusion.lean:84-98), but the statement does not export that shape, unlike slice-1
  `step_failed`, which fixes `events = [.undefined o.1 o.2]` (Simulation.lean `step_failed`). Same occurrence `o`
  IS stated. No consumer is affected (`failed_correct_F` needs only reachability of `Failed(o, _)`, and it goes
  through `runPlan_R_F`, not this lemma). Not vacuous: an execution to `.failed o ...` still needs `o` to be a
  reachable undefined occurrence.
- Suggested fix: either weaken the two doc sentences to "is matched by a reference execution from the related
  state to `Failed(o, ...)` for the same occurrence (the proof runs the earlier annotations first)", or strengthen
  the statement to `∃ c₁ ev, Execution ev (.running c) (.running c₁) ∧ Execution [.undefined o.1 o.2]
  (.running c₁) (.failed o.1 o.2 c₁)` (the proof already has both pieces).

## W-3 (Minor) `runPlan_R_F` docstring / module header claim R at every command boundary; the statement gives it only at the end

- File / identifier: `leanncd/LeanNCD/Semantics/Plan/FusionCorrectness.lean:runPlan_R_F` (docstring lines 61-62) and
  module header lines 7-8 ("the slice-1 run lemma lifts to command boundaries (`runPlan_R_F`: ...)").
- Claim: "R holds at command boundaries, in particular at pc = number of commands when done."
- Evidence: the conclusion mentions `R` only at `π.commands.length` (lines 64-66); the failed disjunct carries no `R`.
  Slice-1 `run_R` (Run.lean:138) is stated from an arbitrary boundary `pc`; there is no fused analogue (`run_R_F`)
  from an intermediate boundary, and no theorem chains `step_R_command` along a fused run. `step_R_command` gives the
  one-step statement, but nothing proves that a fused run actually reaches each intermediate boundary with R
  (the run bridge relates only terminal outcomes via `Agree`).
- Suggested fix: docstring "R holds at the final command boundary (pc = number of commands) when done; one-step R at an
  intermediate boundary is `step_R_command`". Header: "lifts to the final command boundary".

## W-4 (Minor, fixture gap) "The empty command is accepted" by `checkPlanF` is asserted in docs but pinned by no fixture

- File / identifier: spec 31.1 slice-2 paragraph (`tensor_logic_semantics.md:4249`, "The empty command is accepted."),
  plan F12 ("accepted by `checkPlanF`"), plan table row a10.
- Evidence: `rg -n "fusedEmpty|emptyCmd" leanncd/test/Semantics` shows the plans with `[]` are used only in run
  fixtures (`fused-with-empty-commands`, `step-empty-command-noop`) and in the SLICE-1 verdict
  (`invalid-empty-command`: `(false, ["singleton"])`, `emptyCmd.checkPlan = false`). No fixture evaluates
  `checkPlanF`/`verdictF` on a plan containing `[]`, and no `*_F` theorem is instantiated on one. The claim is true
  by definition (`expand` maps `π.ann = commands.flatten`, so `emptyCmd.expand` has the same commands as
  `plan.expand`), so this is not unsound; but a checker edit that rejected empty commands (e.g. a
  `checkPlanF := expand.checkPlan && commands.all (· ≠ [])` guard) would break no fixture and no proof.
- Suggested fix (one line, T4 file): `#eval check "fused-empty-accepted" (verdictF fusedEmpty, verdictF emptyCmd)
  ((true, []), (true, []))`, optionally `example : fusedEmpty.FValid := fusedEmpty.checkPlanF_sound (by decide)`.

## W-5 (Minor, docs) path-doc row for `stepCommand_not_stuck` drops its R premise

- File / identifier: `lean_executable_semantics_path.md:1108`, theorem `Fusion.lean:stepCommand_not_stuck`.
- Claim: "A command of an `FValid` plan is never stuck".
- Evidence: the statement needs `hR : π.R ops η pc M c` and `hc : π.refState ops η pc = some c` besides
  `π.expand.Valid` (Fusion.lean:156-158); on an arbitrary memory a command of an FValid plan can be stuck (e.g. a
  `pub` over an uninitialised slot, `execPub`). The spec's own 31.2 sentence ("progress holds under `FValid`") is
  in the context of the R-related state and is fine.
- Suggested fix: "From an R-related state with `Conf = refState pc`, a command of an `FValid` plan is never stuck".

## W-6 (Minor, convention) new theorems documented in path doc 4.9 have no `#print axioms` line

- File / identifier: `Plan/Fusion.lean` (`execAnns_R`, `execAnns_failed`, `step_R_command`, `step_failed_command`,
  `stepCommand_not_stuck`, `runFrom_agree`), `Plan/Run.lean:execAnns_not_stuck`, `Plan/Step.lean:stepCommand_single`.
- Evidence: `rg -n "#print axioms"` over Fusion.lean / Step.lean / Syntax.lean finds none for these (Step.lean prints
  only `validateInput_*`; FusionCorrectness.lean prints `runPlan_agree` and the `*_F` theorems, which transitively
  cover `runFrom_agree`, `execAnns`-level lemmas used by them, but NOT `step_R_command`, `step_failed_command`,
  `stepCommand_not_stuck`, `execAnns_not_stuck`, which no printed theorem uses). Slice-1 modules print every
  documented theorem (e.g. Simulation.lean:601-611, Run.lean:197-200). `rg` finds no `sorry`/`native_decide` in the
  changed library files, so no hidden axiom is suspected; the gap is that three documented theorems
  (path doc 4.9 table rows 1106-1108) are not axiom-checked by the build.
- Additional evidence: `rg -n "step_R_command|step_failed_command|stepCommand_not_stuck"` over `leanncd/LeanNCD`
  and `leanncd/test/Semantics` finds only their definitions (plus `stepCommand_not_stuck` -> `execAnns_not_stuck`)
  and one test COMMENT (PlanFusionTest.lean:99). They are used by no theorem and instantiated by no fixture; the run
  theorems (`runPlan_R_F`, `*_F`) go through `runPlan_agree` + slice-1 `runPlan_R` on the expansion instead. Their
  hypotheses are satisfiable by inspection (R/refState at a boundary, `AnnOK` from `hv.stepOK` on the expansion),
  so they are not vacuous, but nothing in the build demonstrates it.
- Suggested fix: append `#print axioms` for `step_R_command`, `step_failed_command`, `stepCommand_not_stuck`,
  `runFrom_agree` (Fusion.lean) and `execAnns_not_stuck` (Run.lean); optionally one `example` instantiating
  `step_R_command` on `fused` at pc 0 (R from `R_start`).

## What was checked with no finding

- (1) `execAnns` (Step.lean:138-143) folds left-to-right on the running memory, `[] => .ok M`; `stepCommand` runs at
  `π.expand` positions `offset pc + j`; `runFrom` (Step.lean:179-185) reports the PRE-command `M` for both `failed`
  and `stuck`, so failure is transactional per command as documented; `stepCommand_single` has no hypotheses.
  `offset`/`prefixAnn_eq_expand`/`ann_getElem?_offset` are hypothesis-free and count `[]` as 0. All plan views
  (`consList`, `pubList`, `matList`, `accFlat`, `pubFlat`) are `flatten`-based (Syntax.lean:100-102, 184-185), so no
  view silently drops fused annotations.
- (2) `step_failed`/`step_failed_no_model` restatements are exactly the old statements at `cmd = [a]` (the old
  general form would be false for a fused `semFail` after earlier annotations). `FValid`, `checkPlanF_sound`,
  `runPlan_agree` (any plan, no hypothesis), `runPlan_R_F`, `terminal_adequacy_F` and the five `*_F` theorems are
  the slice-1 statements verbatim with `π.Valid` -> `π.FValid` and conclusions about the FUSED plan's `runPlan`,
  `refState`, `R`, `Decode` at `commands.length` (compared with Correctness.lean:63-142). Non-vacuity: `fused_fvalid`,
  `sFused_bad_fvalid` (an a3-shaped fused plan) and `fused_model_unique`/`scalar_bad_no_model_F` instantiate them.
  `Agree` is not trivial (two negative examples).
- (3) `checkPlanF = π.expand.checkPlan`; on the expansion every command is `[a]`, so `checkSteps`' `| _ => true` arm
  is unreachable and every annotation is checked at its expanded position; spec 32.3's fusion premise
  (publication after removing G) is exactly expanded `PubOK` order. No misfused plan accepted by `checkPlanF`
  outside the table found.
- (4) Every `#eval check` throws on mismatch (`ExecutableReferenceTest.lean:121-125`); the fallback arm of
  `fusedcorr-failed-agrees-on-occurrence` returns `(0,0,false)` and so can fail; the three changed slice-1
  fixtures are the forced ones. Column-1/column-2 equality of `verdictTrio` and the S2-M4 equivalence were
  adjudicated earlier (S-2, plan 2.2) and are not repeated.
- Not done: no build, no `#print axioms` evaluation, no mutation re-run.
