# Slice 2 plan: SOUNDNESS review

Reviewer scope: `plan_layer_slice2_plan.md` against the shipped prototype Lean (HEAD 4d893192) and `p1_notes.md`.
Read-only; no Lean edited; no build run (all evidence by Read / `rg -n`; axioms lines were not re-run, the
`#print axioms` lines in the files were not re-evaluated).
Result: no Critical and no Important finding. Four Minor findings. The eight soundness questions are answered at the end
(answers are evidence, not findings).

## S-1 (Minor) The a4 cell is pinned by a fixture that is not the described case

Claim (plan section 2, row a4): "later annotation reads an address only accumulated earlier ... runtime `readPub = none`";
pinned by `t4-a4-chainEarly`.
Evidence: `t4Unpub` in `PlanFusionCheckerTest.lean` is `[acc [cOcc 1], acc [cOcc 0]]`: the READER comes first, nothing is
accumulated earlier in the command. The case actually described ("accumulated earlier, not yet published") is
`t4ReadFirst` = `[acc0, acc1, pub1]`, which the plan files under row a3mis.
Failure scenario: a reader trusts the table to say that "accumulated-but-unpublished" and "not even accumulated" are two
cases that the checker tells apart; both are the same `ReadyOK` clause (`ready@n`) and the fixtures pin the clause, not
a difference. No wrong claim about the checker; the table promises one more distinguished cell than it has.
Fix: relabel a4 as "reader precedes producer" (pinned by `t4-a4-chainEarly`) and say a3mis is the
"accumulated, publication later" instance; or merge a3mis/a4 in the table. Text-only.

## S-2 (Minor) Table 2.1 header presents a definitional equality as an observation

Claim (2.1 header): "verdict `verdictF = verdict(expand) = verdict(donor)`", "All values observed".
Evidence: `verdictF π := (π.checkPlanF, (clauseRow π.expand).filterMap ...)` (`PlanFusionCorrectnessTest.lean`) and
`checkPlanF π := π.expand.checkPlan`, so the first two components of `verdictTrio` are equal by definition on every
plan. Only the third component (the singleton donor) carries independent information, and it is evidence only that the
donor and the fused plan have the same flat annotation sequence.
Failure scenario: none for soundness; weak overclaim of fixture strength (the "slice-1 checker on the expansion" column adds
nothing over the first).
Fix: say in 2.1 that column 1 = column 2 by definition and that the donor column is the independent check.

## S-3 (Minor) No fixture puts a reading annotation after an empty command

Claim: F12/a10 (empty command is a stutter, `offset` unchanged) pinned by `fused-with-empty-commands`
(`[[], [initZero, acc], [], [pub], []]`).
Evidence: that plan has no annotation that reads the published view (acc reads inputs only; pub reads no view), so a wrong
`offset` that counts empty commands (e.g. `offset := pc`-style) would not flip it. Correctness of `offset` with empties is
carried by the PROOF `prefixAnn_eq_expand` (holds for all `pc`, no emptiness hypothesis; `offset pc = (prefixAnn pc).length`,
and the flatten of `commands.take pc` counts 0 for each `[]`), which is sound. Plan a10 already lists the empty command as
having no mutant (O10); this adds that it also has no OFFSET-sensitive value fixture.
Failure scenario: an executor edits `offset`/`prefixAnn` so the proof still builds but empties shift positions: not caught
by a fixture. Low likelihood (the library proof would break first, as the plan itself says for all 14 mutants).
Fix (optional, one fixture): `[[init cAll], [], [acc0, pub1], [], [acc1 reading point 1], [pub]]` over `chainBody` expecting
`done` and slots `[0,3,4]`.

## S-4 (Minor) "two statement changes and nothing else" understates T1's proof edits

Claim (T1 regression gate): "the whole slice-1 Plan test set builds with the two statement changes of F10 and nothing else".
Evidence (patch `01-expand-step.patch`): besides the restated statements of `step_failed` / `step_failed_no_model`,
the PROOFS of `step_R` (`simp only [stepCommand_single] at h`, Simulation.lean) and `step_not_stuck` (three
`stepCommand` -> `stepCommand_single` rewrites, Run.lean) change; `run_R` text is untouched (its `hstep` closes by
unfolding `stepPlan`, still `rfl`-true). The plan's T1 "Files" paragraph does list the step_R and step_not_stuck edits
correctly; only the gate sentence and F10 ("keep their statements") are misleading about proofs.
Failure scenario: an executor who sees a diff in `step_R`'s proof concludes the patch diverged from the plan.
Fix: gate sentence -> "two statement changes (F10) plus the proof re-bases of `step_R`, `step_failed` and `step_not_stuck`".

## S-5 (Minor, docs) Slice-1 spec sentence on transactional vs sequential commit stays unqualified after T5

Evidence: spec 31.3 "As formalized" paragraph (`tensor_logic_semantics.md`, lines ~4308-4312 at HEAD) says transactional
versus sequential commit "are not told apart by any fixture on `checkPlan`-valid plans ... lists both as equivalent mutants".
The T5 row "31.3 (failure)" appends the fused rollback sentence but does not qualify the older one. The old sentence stays
literally true (a fused plan is never `checkPlan`-valid) but a reader of the combined paragraph would infer no fixture
anywhere distinguishes them, whereas `fused-failure-after` / `fused-scalar-bad` (rolled-back slots `none` / `0` where a
partial commit would show the earlier annotation's value) do.
Fix: append "(for singleton plans; for `FValid` fused plans the two are distinguished by `fused-failure-after`,
`fused-scalar-bad`)" in the same T5 row.

---

## Answers to the eight soundness questions

1. Expansion order with empties: sound. `expand := {π with commands := π.ann.map ([·])}`, `ann = (commands).flatten`
   so annotation order is the stated order; `offset pc := (prefixAnn pc).length` counts annotations of commands before
   `pc` (empties add 0); `prefixAnn_eq_expand : π.prefixAnn pc = π.expand.prefixAnn (π.offset pc)` is proved for ALL `pc`
   with no hypothesis (via `ann_eq_append` + `take_left'`); `execAnns n` advances `n.succ` per annotation;
   `runFrom_agree` uses `offset (pc+1) = offset pc + cmd.length`. `Plan` has no field other than `commands` that depends on
   commands (`tensors`, `tensors_nodup`, `tensors_complete`), so `{π with commands := ...}` cannot desynchronise anything.
   Fixture side: see S-3.
2. `Agree` ignores `done`'s pc and the failure memory: the lifted theorems are the spec's. `done_correct_F` /
   `done_iff_model_F` carry `Decode` and the model uniqueness; `failed_correct_F` concludes only `¬∃ρ, Models`; `runPlan_R_F`'s
   failed disjunct yields an `Execution ... failed o.1 o.2 c'` with the SAME `o` the fused run reports (via `Agree`'s
   occurrence clause), i.e. the spec 31.3 "same occurrence" content. `terminal_adequacy_F` pins `m = commands.length`
   (D5/F6); `done_correct_F` alone does not state `m = commands.length` (it is `terminal_adequacy_F`'s conjunct);
   the plan's F6/31.4 rows say what is not compared (pc, failure memory). Adequate.
3. Transactional failure: consistent. `runFrom` reports `.failed o pc M` with the memory BEFORE the command
   (Step.lean `runFrom`), and `step_failed_command` starts from `R pc M c` at that same pre-command `M`: the reference
   segment is `c ->* (earlier annotations) ->* Failed(o, ...)`. A failed fused run never claims `R` at the failed state
   (R is claimed only at command boundaries, and the failed outcome's memory is the boundary memory at `pc`), so no
   state is reported that R fails to relate. Matches spec 31.3 "related concrete state steps to PlanFailed(o)".
4. `stepCommand_single` (Step.lean) has no hypotheses on `π`, `pc` or `a`: `execAnn_prefix` + `prefixAnn_eq_expand`
   rewrite `π.expand.execAnn (offset pc)` to `π.execAnn pc`, so singleton behaviour equals the old `| [a] => execAnn pc M a`
   for ALL plans (valid or not, `a` not necessarily `commands[pc]`). Proof-changed slice-1 theorems per patch:
   `step_R` (one `simp only`), `step_not_stuck` (3 rewrites), `step_failed` (statement + `match a`), `step_failed_no_model`
   (statement only); `run_R` unchanged and its call to `step_failed` still typechecks (`hcmd : ... = some [a]` after
   `obtain ⟨a, rfl⟩ := hv.singleton`). `rg` shows no user of `step_failed`/`stepCommand` outside Plan/ and the tests. The plan lists
   all of these in T1 Files; wording gap = S-4.
5. Checker: `checkPlanF = expand.checkPlan`; `checkPlan_sound` applies since nothing was removed or changed in Validity.lean
   (`rg` shows `checkSingleton`, `checkCov1Complete`, `checkAccMat`, `checkPlan_nodup_redundant` all still there, and
   `expand_singleton` supplies the singleton premise of `nodup_prefixAnn_flatMap` / `checkPlan_nodup_redundant` for the expansion).
   No shadowing lemma is dropped; claims for expansion plans are the slice-1 claims on the expansion. `checkAccMat`
   remains an unproved-redundant clause (no theorem mentions it), unchanged.
6. Case x class table: no cell is labelled R/F whose fixture has coinciding readings, except the relabelling in S-1 (a4 vs a3mis,
   same `ReadyOK` clause) and row b (Order4) being the same fixture and same clause (`pubOrder@1`) as a2 (stated in the table).
   The "pre-command check" column is argued, not probed (plan says so: cell c, O5). Unlisted combinations I looked for:
   `[pub B, initZero B]` (pubMat order) is covered by S2-M12's a9 flip; double-violation fixtures do not exist but each
   clause is separately flipped (a5/a6/a7 verdicts are order-insensitive and the plan says so). No silently ignored cell
   found that the table omits; a fused command containing both a2 and a5 violations is not exercised (no soundness impact:
   the expansion checker is per-position).
7. The 3 changed slice-1 fixtures are each forced: `fused` (`[[init, acc],[pub]]`) previously `stuck` only because of the
   `| _ => .stuck` arm; `[]` now `execAnns [] = .ok M`; `invalid-empty-command` run half follows from the same. `rg` over
   `Plan*Test.lean` + `PlanFixtures.lean` finds exactly ONE non-singleton non-empty command and ONE `[]` outside the Fusion
   tests (`fused` and `emptyCmd`, both in PlanStepTest and reused by PlanValidityTest); the remaining `stuck` expectations
   (PlanValidityTest 187-190, PlanStepTest 136/177/182/230) are on singleton plans or on `stepPlan` past the end
   (`commands[pc]? = none` still `.stuck`). No other printed outcome is at risk.
8. Empty command: `execAnns [] = .ok M` is the identity; `runFrom` is structural on the command list so termination is trivial
   (spec 31.3's "every successful command advances pc, runs are finite" still true); `Order4` is about the expansion, which
   contains no entry for `[]`; `done`'s pc counts commands including empties (`runFrom_done_pc`), and `terminal_adequacy_F`
   states `m = commands.length`. F12/D16 claims only "accepted by `checkPlanF`, rejected by slice-1 `checkSingleton`":
   true (`checkSingleton` is `length == 1` for every command). No unsound claim found.

Not checked: axioms were not re-run; T2-T5 patches (02-04) were read only through the Lean they produce; the slice-1 mutation
manifest `expect` strings after T1 (plan O8, unverified by the plan itself); spec/AGENTS text outside 29.3/31.x.
