# Slice-2 plan review (read-only; 32 tool calls, skill sections not re-read for lack of quota)

Plan: leanncd/docs/superpowers/plans/2026-10-04-f32-flip-slice2.md. Worktree tip b2c31be; note the worktree
already CONTAINS the prototype flips (the patches' production hunks are applied here), so `rg` on
`leanncd/LeanNCD` shows post-flip text.

## Findings (ranked)

### F1 Important - Section 1 flip #4 / Task 5 (5b) mutation: the scan-state fallback is unreachable
Defect: Task 5 says "Mutation (5b): revert flip #4 and confirm a state-signature pin fails" and names
"pins of ... the scan-state fallback (flip #4: `stateDtypes.getD si` over an undeclared state)" as the
known class (ii) risk. The fallback is never taken. `stateDtypes` is pushed once per index of
`stateNames` (`Compile.lean`, `for h : si in [0 : stateNames.size]` ... `stateDtypes.push (dtypeOfDecl ...)`,
rg lines 1020-1022) and `stateSigs` maps over `Array.range stateNames.size` (rg line 1409), so
`getD si .f32` always hits the pushed value. The dtype of an undeclared state comes from `dtypeOfDecl`
(flip #3), not from the `.f32` default of flip #4. Same holds for the "deliberately not changed" `.f64`
sibling at rg line 1225. Consequence: flip #4 is cosmetic (a dead default), no assertion can pin it, and the
T5 mutation cannot go red; lens A's "scan-state fallback" item has nothing to review.
Fix: say in Section 1 that flip #4 is a consistency edit with an unreachable default; delete the T5
mutation and re-target it at flip #3 (a state-signature pin over an undeclared state fails when
`dtypeOfDecl none` is reverted); drop "scan-state fallback" from lens A.

### F2 Important - Task 1 / Section 2: the patch source is not on main, and the plan never says where to read it
Evidence: `git ls-tree -r 574a633 -- papers/f32_flip_files papers/f32_flip_slice2_log.md` is empty. The
execution worktree is "off main 574a633, NOT the proto branch", so `papers/f32_flip_files/patches/*`
(and the RESULTS/plan_modules that 0007 recreates) do not exist there. The implementer's first action
(`git apply --check <patch>`) has no stated path.
Fix: give the absolute patch directory of the proto worktree (or `git show f32-flip-slice2-proto:...`
into the scratchpad) in the T1 brief; keep the plan's `plan_modules.md` appends targeted at the file
that 0007 creates in the exec worktree.

### F3 Important - Section 1 last bullet vs Task 7: "nothing under `leanncd/LeanNCD/` after Task 1 except Error.lean docstring" is contradicted
Defect: Task 7 step 2 edits `leanncd/LeanNCD/DSL/AGENTS.md` and `leanncd/LeanNCD/Eval/Plan/AGENTS.md`
(both exist, verified by ls) which are under `leanncd/LeanNCD/`; step 1 says "fix every hit that states
the OLD default", and the value-grep is run over all of `leanncd`, so hits in other `.lean` docstrings
under `LeanNCD/` would also be fixed. A mechanical `git diff --stat -- leanncd/LeanNCD` check by a reviewer
would flag all of these.
Fix: reword to "no later task edits any `.lean` file under `leanncd/LeanNCD/` except the comment-only
Error.lean edit; AGENTS.md nodes are exempt", and say a stale hit in any other `.lean` file is reported,
not fixed (Rule 14).

### F4 Important - Task 7 item 3 / Task 8: ordering circularity
Defect: T7 (an implementer task, before T8) must add the `papers/f32_evalplan.md` completion blockquote
"when the slice merges ... Not before the Task 8 gate is green", and update 8676/11/accepted numbers "only
if Task 8 measured a different value". Task 8 steps 1-6 have no step that edits docs, and the merge is
step 6. As written the blockquote and any number update have no owner or time.
Fix: move T7 items 3 and the number updates into a T8 step (controller or a small dispatch) between step 4
and the merge, or make T7 run after the full build.

### F5 Minor - Sizing: T6 DifferentialTest option B contradicts the "corpus unchanged" rule
Option (B) edits `leanncd/test/Eval/PropertyOracle/Gen.lean` (the corpus generator; `enumPrograms` guard at
Gen.lean rg line 165 already uses `p.explicitF64`) while the same paragraph rejects "a fix that changes the
3832 corpus (Gen's generated programs)". Criterion (A) itself is unambiguous and protects the guard:
`total == 3832 && accepted == 3832 && rejCounts.isEmpty` is at DifferentialTest rg line 213 and is a
compile-time guard. State that B may only add declarations that leave `accepted`/program count unchanged.
Also the scan guard is literally `total == 17 && accepted == 17 && nonlin == 0 && agg == 0` (rg line 1033);
the plan's `total=17 accepted=17` is a paraphrase and omits `nonlin == 0 && agg == 0`.

### F6 Minor - Numbers: call-site counts do not match the plan's own commands
Plan says CompileTest ~143 and ScanCompileTest ~34 sites (from plan_modules.md, no command). Measured line
counts: `rg -c "prepareEvalPlan|ofDenseInputs"` gives 120 (CompileTest) / 33 (ScanCompileTest); with the
Section 3 pattern 231 / 99 (ScatterCompileTest 4 matches OK). 143/34 may be occurrence counts, not line
counts. State which command produced them or drop the "~".

### F7 Minor - Numbers: "277 failing assertions in 8 of them"
8+71+101+48+48+1 = 277 recomputed from plan_modules.md and the log: correct, but the 277 spans exactly SIX
modules (Signature, Compile, Scan, Nonlin, ScatterCompile, Scatter32Oracle). StructuralTest and
ComplexElementTypeTest have no measured count (not in 277), and the 3 downstream modules are unmeasured.
Fix the sentence: "277 in 6 of the 8 measured modules".

### F8 Minor - Task 1 commit count and Touches column
Heading says "four commits"; the table has 1a-1d plus the 0007 docs commit (5), and the size line says
"4-7 commits". Patches 0002, 0004 (and 0001, 0007) also modify `papers/f32_flip_slice2_log.md`; the Touches
column for 1b/1c omits that. (0003, 0005, 0006 do NOT touch the log, so only 0001/0002/0004/0007 form the
log chain; "check immediately before apply" is correct and the order 0001..0007 is stated and sufficient:
0001 creates the log, 0002/0004/0007 extend it with matching context, the test-file patches are disjoint.)

### F9 Minor - Section 1 wording on the "identical-looking fallback sites"
"the earlier one and the later `.f64`" is ambiguous: both siblings are `.f64` (Compile.lean rg lines 1225
`stateDtypes.getD si .f64` and 1742 `compiled.stateSigs.getD si {.. dtype := .f64}`). Name them by
enclosing function. (Moot for 1225 given F1.)

### F10 Minor - Hidden coupling T4 -> T6
`Adapter32Test.lean` line 3 `import Eval.Plan.CompileTest` ("fixture 10 reuses its `.float64` identity plan
as the wrong-carrier donor"). A T4 re-spell of that plan's decls can break Adapter32Test, unmeasured until
T6. Plan states only DifferentialTest/AdapterTest imports. Add this edge and tell T4 not to change that
donor plan's carrier.

### F11 Minor - Check 7
`rg -n "\.lean:[0-9]+|File\.lean"` hits only plan line 271 (prose "no `File.lean:NNN`", an instruction, not a
line number). No real line numbers in the plan.

## Checked, nothing found
1. EXISTENCE: every path the plan names exists (ExplicitF64.lean, the 11 test modules, Gen.lean,
   Harness.lean, split-handoff-template.md, token-report.py, lake-build.sh, prepare-worktree.sh, the 3
   AGENTS.md nodes, papers/f32_evalplan.md). Identifiers found in the file the plan says: storageConstraintOfDecl,
   storageConstraintOfName? (Ast.lean), dtypeOfDecl (Signature.lean), deriveStorageKind (Check.lean),
   scheduleStorageKind (ScheduledValidation.lean), explicitF64Decls, schedOf, conversionInputs, gn2Prog,
   axiswiseSched, reluProg, softmaxProg, legacyAccepts, legacyErrorOf, sourceEvalOf, sourceCompileCauseOf,
   compiledEqB, checkEntry, envOf, planAgrees, planAgreesForDecls (all in the plan's stated modules).
   Not confirmed by a `def`-pattern rg (only by use in Harness/Oracle/Gen): `TLProgram.explicitF64`, and
   `InputSignature.ofDenseInputsForDecls` / `ofDenseInputs32ForDecls` / `ofDenseInputs` definitions (my
   anchored pattern did not match; not re-checked for lack of quota - UNVERIFIED).
2. NUMBERS: 8546 (log, RESULTS), 8676/11/3832/17 (memory SLICE 1 bullet, unflipped baseline), 277 sum
   recomputed OK, 172 = 71+101 OK. 3832 and 17 guards exist in DifferentialTest.
3. PATCHES: `ls` matches the plan's seven names and order exactly. Touched files per `+++ b/`:
   0001 Ast/Compile/Signature + log; 0002 StructuralTest + log; 0003 ComplexElementTypeTest;
   0004 ComplexElementTypeTest + log; 0005, 0006 NonlinCompileTest; 0007 RESULTS.md + plan_modules.md + log.
   Agrees with the plan's task Files (log omission: F8).
4. CONSTRAINTS vs DECISIONS: agree (bool-only defaults not flipped, reference evaluator unchanged, no
   pragma, carriers unchanged, mixed rejected, four flips). The stale text "An undeclared external is a real
   f64 tensor" exists at LeanNCD/Eval/Plan/Error.lean:239 (rg), and the plan words that edit as docstring-only.
   The 0001 patch also edits a `--` comment in Compile.lean prepareEvalPlan (comment-only, covered by
   "plus docstrings").
5. SIZING: T4/T5 are split in two with turn estimates, T2/T3 single dispatches with counts and donor named
   for T3 (Task 1d diff); final review lenses A/B named; controller runs the full build (T8). Note T4b/T5b
   phase-2 lists are prose/derived from 4a's log, not `identifier @ file` (acceptable: modules unread;
   T3 "probably one helper" and T6 40-60 turns are guesses, flagged by the plan itself). Skill sections
   were not re-read (quota), so this check is against the task statement only.
6. COMPLETENESS: all items of the memory SLICE 2 inventory appear (4 flips, 8 modules, 3 downstream,
   Error.lean docstring, the master-plan blockquote, 3 AGENTS nodes). `defaultTargets = ["LeanNCD","Tests"]`
   and the `Tests` globs list all 11 modules; spikes are in no glob. No module outside the 11 imports a
   failing module (rg of imports: only Adapter32Test->CompileTest, AdapterTest->ScanCompileTest,
   DifferentialTest->ScanCompileTest/AdapterTest). The memory item (4) "6 other residue modules also call
   the evaluator unwrapped" is subsumed by class (i), not named separately.

Tool calls used: 32 (over the ~30 budget by 2, spent on writing and committing).
