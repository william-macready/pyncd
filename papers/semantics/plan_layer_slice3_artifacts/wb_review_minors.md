# Whole-branch review: slice 3 deferred minors (main 72cf46c2 .. 6580e8f4)

### F1 [Minor] `rtMulti` comment claims the row discriminates a first-member-only CHECKER; it cannot
- Where: `leanncd/test/Semantics/PlanRetireTest.lean`, comment above `def rtMulti` ("a `retire` that only handled the first member (executor or checker) would differ here").
- What: both members of `[cAddr 0, cAddr 1]` are legal at that position, so a `checkRet` that checked only the first member still returns `true`; the row's verdict half cannot move. Only the executor half (point 1 would stay `some 3`) discriminates.
- Actual: the controller's own probe agrees: `checkRet` first-member-only fails only `retire-multi-second-unpublished` and its `example`, not `retire-multi-distinct`. The record's F2 row states this correctly.
- Fix: "an `execRet` that only cleared the first member would differ here (a first-member-only checker is caught by the next row)".

### F2 [Minor] `rtMultiBad` donor description does not match the plan
- Where: same file, comment above `def rtMultiBad` ("rtMulti with the SECOND member replaced by point 2").
- What: `rtMulti` retires `[cAddr 0, cAddr 1]`; `rtMultiBad` retires `[cAddr 1, cAddr 2]`. Replacing the second member of `rtMulti`'s block by point 2 would give `[cAddr 0, cAddr 2]`; the shipped block changes BOTH members (0->1 first, 1->2 second).
- Actual: the rest of the comment holds (first member point 1 is published, past its last reader occ 1, not retired, so a first-member-only checker accepts; point 2 is accumulated by occ 1 but unpublished; observed `(false, "stuck", 5, none, [some 0, none, none])`).
- Fix: "rtMulti with the block `[cAddr 1, cAddr 2]`: the first member (point 1) is legal, the second (point 2) is accumulated but not yet published"; or change the plan to `[cAddr 0, cAddr 2]` (would change the observed memory: point 1 stays `some 3`).

### F3 [Minor] "21 constructor-case sites" counts the constructor declaration itself
- Where: `docs/superpowers/specs/2026-10-11-buffer-retirement-design.md` (table row `Ann`, and the risk bullet "counted at HEAD with `rg -c` over `| .retire` arms"); record table row "now 21 (counted at HEAD)".
- What: `rg -n "\| \.?retire "` over `LeanNCD/Semantics/Plan/` gives 21 hits, one of which is `Syntax.lean` `| retire (B : List (DefAddr P))`, the constructor DECLARATION in `inductive Ann`, not a case site that "gains an arm".
- Actual: 20 case arms (Memory 2, Correctness 2, Step 1, Syntax 3, Run 1, Validity 7, Simulation 4) + 1 declaration; no other `retire` arm elsewhere in `LeanNCD` (checked with `rg "(\|.*retire|retire.*=>)"`). A reader re-running the stated method gets 21 and agrees; a reader counting sites gets 20.
- Fix: "20 constructor-case sites (21 `| .retire` hits including the declaration)".

### F4 [Minor] Section 34 progress / terminal-decoding bullets now claim the slice-1..3 profile but name only singleton theorems
- Where: `papers/semantics/tensor_logic_semantics.md` section 34 bullets "Concrete progress and termination" (`step_not_stuck`, `runPlan_not_stuck`) and "Terminal decoding and the compiled-correctness theorem" (`terminal_adequacy`, `done_correct`, `failed_correct`, `done_iff_model`).
- What: the profile (spec line 169 and 4798) includes fused commands by expansion. The fused half is proved (`runPlan_not_stuck_F`, `terminal_adequacy_F`, `done_correct_F`, `failed_correct_F`, `done_iff_model_F` all exist in `Plan/FusionCorrectness.lean`) but these two bullets do not cite it, unlike the edited validation bullet ("fused plans: `FValid`, ...") and the 31.2/31.3 table rows. Not an overclaim of truth; the cited evidence just does not cover the claimed scope.
- Fix: append "; fused plans: `runPlan_not_stuck_F`" and "; fused plans: `terminal_adequacy_F`, `done_correct_F`, `failed_correct_F`, `done_iff_model_F`".

## Verified clean
- (a) All four expected values equal the build-log `info:` lines (minors_t1.log 425-428). `rtMulti` = `rtNeighbour` with the retire moved after `acc occ1` and widened to `[0,1]` (donor exists, line 74). `rtEarly` = `sPlan false` (`PlanStepTest.lean`, `def sPlan`) with `retire t2` prepended before `initZero`; memory `[7,2,3]`, decode `some 2`. `retire-fault-fused-after-retire`: `rtFusedOk` commands are 0 init, 1 acc0, 2 pub1, 3 [acc1, retire1], 4 pub[0,2]; expanded position 5 = the last pub = command 4 (`faultAt n` matches the expanded index, `PlanFaultsTest.lean` `def faultAt`), so `error` at pc 4 with the memory after command 3 `[0, none, 4]`; donor `retire-fault-fused-at-retire` exists. `rtMultiBad` comment holds apart from F1/F2 wording.
- (b) `#eval check` per file sums to 143; `example|theorem` to 92; `PlanRetireTest` 21 rows, 14 items (13 examples + `rtChain_valid`); `| .?retire ` arms sum to 21 (see F3 for what they are); `Faults.lean` has no `retire`; `git log -- leanncd` head is `fe013f1b`, matching the path-doc snapshot.
- (c) Every theorem named in the two table rows and three section-34 bullets exists at HEAD (`Plan/Correctness`, `Run`, `Validity`, `Fusion`, `FusionCorrectness`), all quantified over `Plan` with the `retire` constructor, so they cover the profile (fused scope citation gap: F4).
- (d) New plan-table rows fill all six columns consistently with existing rows (the fused row likewise uses "no" for a yes/no pair); `checkRet` is `B.all` (Validity.lean `def checkRet`); runtime cells match observed values. Record section accurate; `git diff --stat main HEAD -- leanncd/LeanNCD` is empty; `runPlanE_noFault` exists (Faults.lean).
- (e) No `File.lean:NNN` citation in any added line; value-grep `228|\b28 are|17 rows|about 24|139|89` over the path doc, spec, design spec and all `leanncd/**/*.md` finds nothing live (only an unrelated "line 228" in a 2026-08-27 historical plan); AGENTS nodes carry no fixture counts.
