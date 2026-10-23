# S3b plan review (independent, read-only)

Reviewer: Opus 5.5, 2026-10-23. Subject: `papers/semantics/additive_s3b_plan.md` (499 lines) and `additive_s3b_record.md` (183 lines) at slice tip `cf98d1f0`,
against `proto-s3b-p8` (`43e86c5d`), the design (§9), audit, p1..p8 findings, manifest report, mutation manifest and the 16 patches.
Severity: Critical (execution goes wrong or a false claim hides a soundness gap), Major (an executor or reviewer is misled; likely a stop or a wrong verdict), Minor (wording, precision).

## Findings

### F1 (Major): §3(iii) row R2 says `compileToScheduled` ACCEPTS a `tropicalNonlin` violation; the code rejects it there
Location: plan §3(iii) R2 (and the sentence after the table: "Every S above (R1, R2, R5, R6 cells) is by design").
What is wrong: `TLProgram.compileToScheduled` is `assignUIDs >=> resolveDecls >=> reclassifyIterSlots >=> checkReadRanks >=> checkDtypes >=> ...`,
and T4 adds `checkTropicalOutput` inside `checkDtypes`. So `compileToScheduled` REJECTS `tropicalNonlin` (it accepts only the two schedule-level
rules, `scanStateAlgebraMismatch` and `sortCastUnsupported`, which live in `validateScheduled`). p4 (d) observed acceptance only for a CAST violation
(`sortCastUnsupported "Y" "M"`); the plan generalised it to the nonlin rule.
Evidence: `git show proto-s3b-p8:leanncd/LeanNCD/DSL/Compile.lean` (`compileToScheduled` chain contains `checkDtypes`);
`git diff main proto-s3b-p8 -- leanncd/LeanNCD/DSL/Pipeline/Structural.lean` (the `checkTropicalOutput` arm inside `checkDtypes`); p4_findings.md line 57.
Risk: the per-task T4 reviewer ticks R2 against a claim the code contradicts; a final reviewer (b) asked "can a valid program be refused at each entry" works from a wrong table.
Fix: R2 row -> `| R2 | compileToScheduled (runs checkDtypes, not validateScheduled) | rejects (checkDtypes) | accepts (S: not run) | accepts (S: not run) | T4 surface fixture (compileToScheduled accepts the cast program, execution rejects sortCastUnsupported "Y" "M"); tropicalNonlin at this entry: same as R1 (StructuralTest checkDtypes rows) |`.
And the closing sentence -> "Every S above (the scan/cast cells of R1, R2, R6 and every R5 cell) is by design ...".
DISPOSITION: fixed in plan section 3(iii) (R2 row and the closing sentence); verified at proto-s3b-p8: the compileToScheduled chain runs checkDtypes, and checkTropicalOutput has exactly two call sites (checkDtypes, checkScheduledDtypes). Reviewer proposal taken as written, plus a sentence that tropicalNonlin has no S cell at R1-R4/R6.

### F2 (Minor): R6 "UNVERIFIED as an entry distinct from R1" can be resolved: it is NOT distinct
Location: plan §3(iii) R6.
Evidence: `TLProgram.compile` (`DSL/Compile.lean`) is `... checkDtypes ... schedule; route g`, and `tl!{...}` calls `TLProgram.compile`. The "surface route" is R1 (`compile = compileToScheduled >>= route`);
a bare `route` on a `ScheduledProgram` is R5.
Fix: R6 row -> `| R6 | surface route = TLProgram.compile / tl!{} (= compileToScheduled >>= route) | rejects via checkDtypes | accepts (S) | accepts (S) | same entry as R1 (verified: DSL/Compile.lean); no separate fixture needed |`.
DISPOSITION: fixed in plan section 3(iii) (R6 row, UNVERIFIED marker removed): TLProgram.compile runs checkDtypes then schedule; route, and tl! calls it, so the surface route is the same entry as R1.

### F3 (Major): mutation cycles and the next task share one working tree; the plan never says to serialize them
Location: plan §1 "Controller steps per task" and "Per task" step 1.
What is wrong: `mutation-cycle.sh` edits a production/test file in `<wt>/leanncd`, builds, restores it, rebuilds; it has no dirty-tree or lock check
(`rg -n "dirty|status|clean" leanncd/scripts/mutation-cycle.sh` finds only exit-status handling). A task's filtered run is 2 to 9 cycles at ~3 min each
(manifest_report (e)), i.e. 10-30 min, and the protocol has the controller run it "after the task's commit". Nothing forbids dispatching T(k+1)
while T(k)'s cycles run, and the per-task wall-time pressure (F4) invites exactly that. Overlap means `git apply --check` of T(k+1) can fail on a
mutated file, or worse, a mutated file gets staged into T(k+1)'s commit (`apply --index` stages only patched paths, but the implementer's
"plus any added files" and build results would be read against a mutated tree), and the cycle's restore-hash then fails or restores over T(k+1)'s edit.
Fix (add to §1, Controller steps): "The cycles run in the slice worktree and edit it. Do NOT dispatch T(k+1), and do not run any other build in
`<wt>`, until `--task Tk` has printed its summary table; then check `/usr/bin/git -C <wt> status --short` is empty (apart from `.claude/settings.json`) before T(k+1) starts."
DISPOSITION: fixed in plan section 1 (new Serialization paragraph; status-empty check before T(k+1)) and record section 4 (Status empty after column). mutation-cycle.sh has no dirty-tree guard (rg confirmed).

### F4 (Major): the schedule is not stated and nothing says what to skip when time is short; the "over an hour per cycle" premise contradicts the measured run
Location: plan §1 (Cost paragraph), §5.
What is wrong: (1) Total wall time is never added up. From the plan's own numbers: 8 full `Tests` builds after the tasks plus one after T9
(~25 min each when the change sits near the root, S2b) ~ 3.5-4 h, plus 48 filtered cycles ~ 2.5 h, plus 8 mid-tier reviews and two final reviews: well over
6 h of serial build time. (2) The claim "one such cycle took over an hour during authoring; not recorded in an artifact" is contradicted by the recorded run:
run 1 (53 cycles in ~2.5-3 h, manifest_report (e)) INCLUDED every plan-root mutation (`DSL/Ast.lean`: T4-M7b, T6-M7, T6-M8, T8-M5; `Eval/Contract.lean`:
T1-M1, T2-M6, T8-M3; `Eval/Plan/Dense.lean`: 8 entries). An unrecorded anecdote should not drive the protocol. (3) There is no fallback order.
Fix: replace the sentence "Builds of production-level mutations near the plan root ... (controller brief: one such cycle took over an hour ...)" with
"Measured: ~3 min per cycle averaged over run 1, which included every plan-root mutation (`DSL/Ast.lean`, `Eval/Contract.lean`, `Eval/Plan/Dense.lean`)." and add:
"Expected wall time: ~9 full builds (~25 min each) + 48 cycles (~2.5 h) = about 6-7 h of serial build time. If time is short, NEVER skip a task's full build
or the known-red comparison; defer cycles in this order and record each deferral in record §4: (1) entries already enforced in run 2 (T3-M3, T4-M3c, T6-M8,
T7-M1, T8-M1) are skipped first; (2) T8 (tests-only task, its cycles mutate production files already covered by T1/T5/T6 entries) next; (3) never skip the
T4/T5/T6 rejection and cast cycles (T4-M1..M7b, T5-M4b, T5-M5, T5-M11, T6-M11, T6-M12): they are the only evidence for the new REJECTIONS' accept-neighbours."
DISPOSITION: fixed in plan section 1 (measured cost, expected wall time with the arithmetic, deferral order) and record section 4 (Skipped column). Two deviations from the proposal: the deferral order follows the controller brief (T7-M5, T5-M11, T6-M12 sampled first, then the run-2 entries, then T8-M4/M6), and Dense.lean has nine manifest entries, not eight. The manifest report does not itself label any entry a probable cut (stated in the plan).

### F5 (Major): T9 omits `leanncd/LeanNCD/DSL/AGENTS.md`, the node that covers where `SortAlgebra`, `algebraOf` and two of the three rejections live
Location: plan §4 T9 steps 1-4 and 12; checklist "ten live docs".
What is wrong: T4/T6 add `SortAlgebra`, `Stmt.isSortNeutral`, `scanStateStmts` (`DSL/Ast.lean`), `scheduleAlgebras`/`checkSortCasts`/`CheckedScheduledProgram.algebras`/`algebraOf` and a new step in
`validateScheduled` (`DSL/Pipeline/ScheduledValidation.lean`), `checkTropicalOutput` (`DSL/Pipeline/Structural.lean`). `DSL/AGENTS.md` row "Whole-schedule validation
(`validateScheduled`, ...)" (`ScheduledValidation.lean`), the `Structural.lean` row ("predicate-output checks") and the Contracts bullet "`prepareEvalPlan` and `evalScheduled`
... require `validateScheduled`" all describe exactly these files and none is in T9. Step 2 puts "`SortAlgebra`/`algebraOf` live in `DSL/`" in `Eval/AGENTS.md`
instead, which is the wrong node for a reader opening `DSL/`. The slice-plan checklist item "discoverable ... mentioned in the AGENTS.md a reader would already open" fails.
Evidence: `rg -n "validateScheduled|predicateNonlin|tropical" leanncd/LeanNCD/DSL/AGENTS.md` (rows 27 and 57 describe the boundary; no sort or tropical rule).
Fix: add T9 step 4b: "`leanncd/LeanNCD/DSL/AGENTS.md`: `Ast.lean` row gains `SortAlgebra`, `Stmt.algebra`/`isSortNeutral`/`ownAlgebra?`, `scanStateAlgebra`/`scanStateStmts` (neutral writers adopt the state's sort);
`Structural.lean` row gains `checkTropicalOutput` (`tropicalNonlin`, called from `checkDtypes` AND `checkScheduledDtypes`); `ScheduledValidation.lean` row gains `scheduleAlgebras`/`checkSortCasts`/`algebraOf`;
the `validateScheduled` Contracts bullet states the observed precedence (§2) and that `compileToScheduled`/`route` do not run the two schedule-level rules." Add `DSL/AGENTS.md` (21.3k chars) to the step 11 size check and
the step 12 discoverability list; make the T9 checklist count "eleven live docs".
DISPOSITION: fixed in plan section 4 T9 (steps 3 and 13, node-by-node table; DSL/AGENTS.md added; twelve live docs). Also found and added: Eval/AGENTS.md still states unit1 = 1.0 for all four Combines and Combine.bool = min/max (stale after T1), which the review did not list.

### F6 (Minor): C21 "UNVERIFIED ordering" can be closed: no multi-writer set with a tropical writer survives `validateScheduled` on any ordering
Location: plan §2 parked table row "Multi-writer SOURCE name read by a bool statement", §3(i) C20/C21, record §5 A11, record §6.
Evidence: `validateScheduled` (ScheduledValidation.lean at `proto-s3b-p8`) always calls `collectDefinitions` -> `desugarMultiWriters`; `checkWriterGroup` (`Collect.lean`) throws
`multiWriterAlgebra` for EVERY `.assign` writer with `agg != .sum` (after `multiWriterScatter` for scatter writers); a scan-node writer is `multiWriterScan`. The only steps before collection
(`checkScheduledDtypes`, `scheduleAlgebras`, `checkSortCasts`, topology) can only add an EARLIER refusal, never an acceptance. So the C21 program is always refused; what is unpinned is only
WHICH constructor (`multiWriterAlgebra` vs an earlier one), not soundness. Lens 4(b) follows: the backends never see a multi-writer name of a tropical sort; surviving multi-writer sets are
real-sum or predicate, whose declaration sort is exactly what the reference (`isPredicateDest`) and the plan (slot dtype) use; private `T#k` clones carry the cloned declaration. Remaining caveat
(speculation, not traced): `writerGroups` skips a name with a `.recurMorphism` writer, which every entry rejects on its own terms.
Fix: C21 row Class -> "R (backstop, total): refused by collection (`multiWriterAlgebra`/`multiWriterScatter`/`multiWriterScan`) on every ordering; the constructor that wins is unpinned";
the §2 parked row -> drop "(UNVERIFIED that no ordering lets it through)", keep "no fixture pins which refusal wins; fold into S3b-ii"; record §5 A11 and §6 accordingly.
DISPOSITION: fixed in plan section 2 parked row and section 3 C21 row, record sections 5 (A11) and 6. Closed as unreachable for plain .assign/.scatter writer sets (checkWriterGroup and scanWriterConflict? verified by grep at proto-s3b-p8); the .recurMorphism residual (writerGroups skips such a name) is kept as stated, not traced.

### F7 (Major): stale Lean docstrings still describe the max-TIMES algebra at `proto-s3b-p8`; T9's greps are `*.md`-only, so nothing catches them
Location: plan §4 T9 steps 0, 8, 9 (all `rg ... --glob "*.md"`); §0 anti-goals.
What is wrong: after all 16 patches, production docstrings still state the old meaning:
`leanncd/LeanNCD/Eval/Contract.lean` (docstring of `evalAssignDtypedSeeded`): "`agg = .max` ⇒ tropical `(×, max, −∞)`";
`leanncd/LeanNCD/DSL/Target.lean` (`maxreduce` constructor comment): "tropical max contraction (×, max, −∞)". Test headers that are now false:
`test/Eval/Plan/Scatter32OracleTest.lean` module doc ("... never touches ... `scatterAggOrFail`" (deleted in T3) and "any tropical destination (source syntax admits only
sum-product scatter ...)", false since T3); `test/Eval/Plan/ScatterCheckTest.lean` "Acceptance 4: tropical max-product" (name of the algebra is wrong now; value unchanged).
Evidence: `/usr/bin/git -C <wt> grep -n -e "max-times" -e "(×, max" -e "max-product" proto-s3b-p8 -- leanncd/LeanNCD leanncd/test` and
`/usr/bin/git -C <wt> grep -n -e scatterAggOrFail proto-s3b-p8 -- leanncd/test/Eval/Plan/Scatter32OracleTest.lean`. Step 8 only spot-checks `Eval/Scan.lean` and the T7 files.
Fix: T9 step 0 add a second command over Lean sources:
`rg -n "max-times|max-product|min-product|\(×, max|\(×, min|scatterAggOrFail|checkScatterAgg|scatterFillNotIdentity|scatterOptsNotAdmitted|admits only\s+sum-product" leanncd/LeanNCD leanncd/test --glob "*.lean"`;
every production hit is rewritten (then `lake-build.sh <wt>/leanncd LeanNCD`), every test hit is either a dated "before S3b" history comment (keep) or a present-tense claim (rewrite; then build the touched test
module). Name the four known sites above in step 8. Because T9 then edits Lean files, its build target becomes `LeanNCD` plus each touched test module, and record §1 row T9 should say so.
DISPOSITION: fixed in plan section 4 T9 (new step L: a comments-only Lean commit with exact old/new text for 8 edits in 7 files, build and diff verification, KEEP list; step 0 grep extended). Added beyond the review: ScatterDenseTest, ScatterDense32Test and ExecutableTest max-product comments and the minreduce constructor comment. Build target changed from LeanNCD-plus-modules to the full Tests build (it covers both; recorded in T9 and record section 1).

### F8 (Minor): T2's symbol list names `gatherCast`, which T5 introduces
Location: plan §4 T2 "Symbols" (`gatherCast @ Eval/Gather.lean`) and §2 identifier table row (`T2 (cast T5)`).
Evidence: `rg -n "gatherCast" papers/semantics/additive_s3b_files/patches/T2-01-production.patch` finds nothing; `T5-01-production.patch` adds `def gatherCast` and rewrites `gather` as its identity-cast wrapper.
A T2 reviewer told to `rg` the symbol at the T2 tip finds no definition.
Fix: T2 Symbols -> "`gatherRead` (new `pad` parameter), `gather` (now `gather zero one ...`) @ `Eval/Gather.lean`"; T5 Symbols already lists `gatherCast`. §2 row -> "`gather zero one` (T2); `gatherCast` core with `gather` as its identity-cast wrapper, `gatherRead` trailing `cast` (T5)".
DISPOSITION: fixed in plan T2 Symbols and section 2 identifier table (gatherCast belongs to T5).

### F9 (Minor): record §2 says a `ScatterCheckTest` comment was rewritten in T3; no patch touches that file
Location: record §2, T3 row "`ScatterDenseTest.lean`, `ScatterDense32Test.lean`, `ScatterCheckTest.lean` | raw tropical plans ... a comment ... rewritten"; plan T3 checklist (d).
Evidence: `rg -c ScatterCheckTest papers/semantics/additive_s3b_files/patches/` (no hit); p3_findings.md (b) table: "ScatterCheckTest untouched".
Fix: record row -> "`ScatterDenseTest.lean` (comment rewritten), `ScatterDense32Test.lean` (fixture 1.6c added), `ScatterCheckTest.lean` (untouched; its 'max-product' wording goes to T9, see F7)".
Plan T3 checklist (d) -> "`ScatterDenseTest`/`ScatterDense32Test`/`ScatterCheckTest` raw plan VALUES unchanged ...; `ScatterCheckTest` is not edited".
DISPOSITION: fixed in record section 2 (T3 rows split) and plan T3 checklist (d); the ScatterCheckTest comment fix moved to T9 step L.

### F10 (Minor): C24 claims the cast is pinned on all four `residualizeAssignment` callers, but two of the four have no mutation cycle and no observation
Location: plan §3(i) C24; T5 "Cycles".
Evidence: T5-01 passes `isBoolSlot` at four call sites (`compileScan` base, `compileScan` recurrence step, `prepareEvalPlan` scatter compute half, `prepareEvalPlan` plain assign);
the manifest has T5-M7 (scan base) and T5-M9 (scatter) only; manifest_report (c) lists T5-M8/T5-M10 (step, plain) as pruned "twins", NOT run ("the same four d1..d4 fixtures cover all four callers" is asserted, not observed).
Plain is indirectly covered by a1/a2 and GN4 (T5-M1/M2 kill the shared Dense path, not the caller flag). The scan-STEP caller's flag has no killing observation.
Fix: C24 Pinned-by -> "T5 d1/d2 (scatter), d3/d4 (scan base + step), a1/a2 (plain); cycles T5-M7 (base), T5-M9 (scatter); step and plain caller cycles (T5-M8, T5-M10) pruned, never run: the step-caller kill is UNOBSERVED".
Optionally add T5-M8 to the manifest (one cycle, `Eval/Plan/Compile.lean`, target `Eval.Plan.BoolCastTest`); otherwise list it in §2's parked table.
DISPOSITION: fixed in plan section 3 C24 and section 2 parked table (T5-M8/T5-M10 never run; step-caller kill UNOBSERVED); manifest not edited; record section 6 row added.

### F11 (Minor): a single `git apply --check` over several patches fails spuriously; say "one patch per invocation"
Location: plan §1 "two plain commands" per patch.
Evidence: `/usr/bin/git -C <wt> apply --check T1-01 T2-01` (both paths in ONE call) reports "patch failed: leanncd/LeanNCD/Eval/Plan/Check.lean:73" although the chain is correct:
a blob-id walk over all 16 patches (each hunk's preimage `index` equals the previous patch's postimage or the base blob) ends exactly at the `proto-s3b-p8` `leanncd/` tree (reviewer script, all 16 files,
"CHAIN OK"); `T1-01` alone passes `--check --index` on the current tip. A controller trying to pre-check the whole series in one call would see a false failure and STOP.
Fix: append to §1: "Check and apply ONE patch per `git apply` call, in order; passing several patches to one call fails on any file two patches touch (verified 2026-10-23), it is not evidence of a base mismatch.
The series was verified by blob-id chain: base `740bd4f8` + 16 patches = `proto-s3b-p8` under `leanncd/`."
DISPOSITION: fixed in plan section 1 (one patch per apply call, blob-chain statement).

### F12 (Minor): the known-red comparison checks a COUNT of SSDT sites; the exact site set is known and should be the check
Location: plan §1 known-red table and step 3 ("any other `#guard_msgs` site count is a finding").
What is wrong: a count can stay at 19 while one site is fixed and another breaks. `SourceSortedDifferentialTest` is not edited before T7, so its line numbers are stable T1..T6 and the findings
record them: T1/T2 sites `104,106,191,193,196,242,262,264,266,269,272` (p1 (b)); T3..T6 sites `104,106,108,188,191,193,196,201,204,206,209,227,228,242,262,264,266,269,272` (p3 (b)). No command is given to extract them.
Fix: add to §1 step 3: "Extract with `rg -o "SourceSortedDifferentialTest.lean:[0-9]+" <log>` (dedup by line); the set must EQUAL the table's line set (T1-T2: the 11 lines above; T3-T6: the 19 lines above).
GN4: `rg -n "GnnScatterTest.lean:" <log>` shows only the GN4 site." (These are build-log locators for the controller, not shipped text, so the line-number ban does not apply.)
DISPOSITION: fixed in plan section 1 step 3 (exact failing-line set with extraction command; sources p1_findings.md (b) and p3_findings.md (b)). For T4-T6 only the count is recorded in the findings, so set equality there is marked UNVERIFIED line by line.

### F13 (Minor): small wording and citation nits
- §3(iv) W1 "min L66/L108" is a `File:NNN`-style citation in a committed document (checklist bans them in shipped text): use the fixture names.
- §2 / T8 checklist (a) "the single `#guard` in DualityTest pins the counts": DualityTest adds 12 `#guard`s (16 in T8-02, of which 4 are in CollectTest/CollectEvalTest); say "one `#guard` (over `runAll`) pins all the counts; the others are `dualEqOf` self-tests, the grid pins and the parked pin".
- T4 checklist (e): `physicalizeOne`, `splitNonlins` are functions, not files; use `/usr/bin/git -C <wt> diff --stat HEAD~1 -- leanncd/LeanNCD/DSL/Pipeline/RouteFragments.lean leanncd/LeanNCD/DSL/Pipeline/Lowering.lean` (must be empty).
- §2 parked row "JAX/Python ... `README` of `experiments/jax_bridge`": the path is `leanncd/experiments/jax_bridge/README.md`. (Checked: `Executable.lean` refuses every scan step and every non-real algebra, so the new `ReadPlan.boolToTropical` and `StateSlot.initValue` fields, which JAX codegen ignores, cannot reach JAX; `JaxExperiment` is outside `Tests`, so nothing in the plan builds it: one explicit `lake-build.sh <wt>/leanncd JaxExperiment` at the final build would confirm it still compiles.)
- Record §5: A12 is listed before A11.
- T9 step 11, measured at base (headings matching Pitfalls/Checks/Patterns/Context): `Eval` 1384, `Eval/Plan` 1931, `DSL` 1779, `Semantics` 0, `leanncd/AGENTS.md` 2953 characters. All are under ~3k, but `leanncd/AGENTS.md`
  has ~50 characters of headroom: T9 step 4's S3b status line must go outside its Patterns/Global Pitfalls sections (or be paired with a trim). Say so in step 4.
DISPOSITION: fixed. W1 now names CV5od/CV5ud; DualityTest wording corrected (12 guards: one over runAll, five dualEqOf, four grid, two parked; checked at proto-s3b-p8); T4 checklist (e) uses the diff --stat command over RouteFragments.lean and Lowering.lean (both verified to hold physicalizeOne/splitNonlins); jax_bridge path corrected; JaxExperiment build added to section 5; record A11/A12 order fixed; hook headroom for leanncd/AGENTS.md stated in T9 step 5 (measured 2984 by heading split vs reviewer 2953; no status line exists to add).

## Verified without finding (sample, for the controller's confidence)
- Patch chain: base `740bd4f8` + the 16 patches, by blob ids, equals `proto-s3b-p8` under `leanncd/` (script, all files); `T1-01` passes `apply --check --index` on the tip; `git diff --stat main -- leanncd` is empty; `8cf5052a..740bd4f8` touches nothing under `leanncd/`.
- Every manifest entry's `old` text occurs exactly once in its file at its task's prototype tip (`proto-s3b-pK`), 48/48; per-task counts T1 6, T2 6, T3 6, T4 7, T5 9, T6 7, T7 2, T8 5; every target module is in the `Tests` globs; no entry of T1..T6 targets an inherited red module.
- Added `#guard*` per test patch equal the risk table (47, 65, 12, 22, 7, 7, 6+26, 3+16); every task's Files list equals the patch's `+++` paths.
- Identifiers at `proto-s3b-p8`: `CompileError.tropicalNonlin/scanStateAlgebraMismatch/sortCastUnsupported` (`Exec/Uid.lean`), `checkTropicalOutput` with exactly two call sites, `scheduleAlgebras`/`checkSortCasts`/`algebraOf`, `validateScheduled` order as stated in §2,
  `ReadPlan.boolToTropical : Bool := false`, `StateInit`, `StateSlot.initValue := .zero`, `PlanError.castNotAdmitted (termIndex factorIndex)`, `ScanPlanError.stateInitNotAdmitted (stateIndex init dtype)`, `ScalarKernelOps.isTrue` (`!= 0`, f32 `!= +0` so `-0` is false),
  f32 constants `0xff800000`/`0x7f800000`, `Combine.bool = ⟨minNaN, maxNaN, 0.0, 1.0⟩`, `Combine.tropical = ⟨+, op, zero, 0.0⟩`, `Stmt.isSortNeutral` admits `read` and `unaryFn` (`Factor.read?`), `residualizeAssignment` takes `isBoolSlot` with no default at four call sites.
- Deleted names: no `.lean` file under `leanncd/LeanNCD` names any of them; `Differential.Classification.knownContractDifference` survives; 99 `oobPolicy` lines in 16 test files at base (100 in 17 at p8, the new one is BoolCastTest).
- Lens 4(a): reference (`Eval/Scan.lean`) and plan (`compileScan`) both apply `scanStateStmts` to the same collected scan and both derive init from `scanStateAlgebra` over `base ++ recur`; scratch names get the same rewrite on both sides; f32 init is the decoded bit pattern. Consistent.
- Lens 4(c): `relu` uses `NonlinOps.max` (`Eval/Nonlin.lean`, untouched), not `ScalarBinOp.max`, so `relu(NaN) = +0` is unchanged; the NaN change reaches only algebra folds (bool, max-plus, min-plus).
- Lens 4(e): T3's `Plan/Dense.lean` hunk is doc-only (K16 "unchanged code" holds); T4 touches only `DSL/` and `Exec/Uid.lean` (no evaluation code); T8 touches no `LeanNCD/` file.
- Lens 4(d): the deleted `EvalError.scatterFillNotIdentity` and `CapabilityError.scatterOptsNotAdmitted` have no producer after T3 and no non-test, non-record consumer outside the T7 file set
  (repo-wide `git grep` at p8 outside `*.md`/`*.json`: only test comments and dated `papers/` patches). The `Eval/Plan/AGENTS.md` pitfall conflict is surfaced (record §3 call 6, T7 checklist (e)) and resolved in T9; acceptable.

## Verdict

APPROVE WITH FINDINGS. The patch series is sound and reproducible (blob chain verified end to end; 48/48 mutation `old` strings unique at their task tips; fixture and file counts exact),
and the semantic core (constants, casts, neutral-writer rewrite, NaN folds) is consistent between the reference and the checked plan in everything I sampled. No Critical finding.
Counts: Critical 0, Major 5 (F1, F3, F4, F5, F7), Minor 8 (F2, F6, F8-F13).
Fix first:
1. F3: serialize the per-task mutation cycles before the next task starts (shared worktree, no dirty-tree guard in `mutation-cycle.sh`).
2. F1 (+F2): correct §3(iii) R2/R6: `compileToScheduled` and the surface `route` run `checkDtypes`, so they REJECT `tropicalNonlin`; only the scan/cast rules are execution-only.
3. F7 + F5: extend T9 to Lean docstrings (two production docstrings still say `(×, max, −∞)`) and to `DSL/AGENTS.md`, the node covering `SortAlgebra`/`algebraOf` and the new rejections.
Then F4 (state the ~6-7 h schedule and a cycle-deferral order) before dispatching T1.
