# Part V Plan layer, slice 2 (fusion): record

Record, not the live plan (`plan_layer_slice2_plan.md`). Authoring facts and the checklist below; the
close-out and review sections are filled by the controller at the end of execution.

## Authoring dispatches

Tool-use counts are HARNESS counts (agents' self-reports ran about 1.6x low).

| phase | output | harness tool uses | cap | self-report |
|---|---|---:|---:|---:|
| P1 audit, design, core prototype | `Fusion.lean`, `PlanFusionTest.lean`, `p1_notes.md` | 52 | | |
| P2a in-place `stepCommand`, `execAnns_not_stuck`, T2 fixtures, M1-M4 | Syntax/Step/Simulation/Run edits, `p2a_notes.md` | 91 | 55 | about 56 |
| P2b run bridge, `FusionCorrectness`, T3 fixtures, M5-M11 | `p2b_notes.md` | 71 | 45 | about 37 |
| P2c case x class checker fixtures, M12-M14 | `PlanFusionCheckerTest.lean`, `p2c_notes.md` | 76 | 40 | about 45 |
| P2d proof-free probes S2-M1..M4 (O5) | `ScratchProbeP2d.lean` (uncommitted), this record | about 62 (own tally; harness count not measured) | 30 | |
| P3 patch emission | `plan_layer_slice2_patches/`, `manifest.json`, `evidence.json`, `emit-patches.py` | 50 | 45 | |
| Phase B write-up | `plan_layer_slice2_plan.md`, this file | about 45 (own count at commit; harness count not measured) | 50 | |

Breaches stated, not hidden: P2a, P2b, P2c and P3 exceeded their caps on the harness count (P2a 91 vs 55,
P2b 71 vs 45, P2c 76 vs 40, P3 50 vs 45). Authoring total (all sessions) is to be measured by the controller:
`python3 .claude/skills/slice-plan/token-report.py <session-id>`; Rule 6 authoring target <= ~50M. Measured (this session, `token-report.py`, 2026-10-10): 44.8M total = controller 6.9M
(54 turns, peak 187k) + dispatches P1 3.5M, P2a 6.4M, P2b 6.6M, P2c 6.3M, P2d 2.8M, P3 2.5M, Phase B 4.1M, fidelity review 1.4M,
soundness review 2.8M, fix 1.5M; every dispatch peaked <= 189k context and <= 55 turns (Rule 6 per-dispatch limits met, although
harness tool uses exceeded the caps set in the briefs).

## S2-M1..M4 proof-free probes (P2d)

P2d breached its cap (about 62 vs 30; the probe needed four elaboration repairs: `declarations`/`registry`
are concrete fixture names, so the scratch defs are generic in `σ r` with `[DecidableEq σ.Tensor]`). Technique as P2c:
scratch file `leanncd/test/Semantics/ScratchProbeP2d.lean` (importing `Semantics.PlanFusionCheckerTest`, registered
temporarily in `lakefile.toml`; both removed before the commit; copy kept in the controller scratchpad). Mutated
functions under new names: `execAnnsM1`, `execAnnsM3`, a generic `runFromG` taking the step function and the
failure-memory function; the same plan and input as each fixture, re-run with the shipped `runPlan` and each
mutant; 19 fused runs (every fused-plan run of PlanFusionTest, PlanFusionCorrectnessTest `fused`, PlanStepTest
`fused`, and all `t4-*` runs). The scratch file built with no error.

| mutant | library break | fixture flips | flipping fixtures: mutated vs shipped |
|---|---|---|---|
| S2-M1 right-to-left | `stepCommand_single` "No goals to be solved" | yes | `fused-reciprocal-all` stuck@0 vs done@1 `[3/4,0,0]`; `fused-failure-after` stuck@0 vs failed@0; `fused-with-empty-commands` stuck@1 vs done@5; `fused-runs-in-slice-2` stuck@0 vs done@2; `misfused-run-undetected` stuck@0 vs done@1; `t4-a3-chainPlan` done@3 `[0,3,1]` vs `[0,3,4]`; `t4-a5-reinitMid` done@4 `[0,14,0]` vs `[0,10,0]`; `t4-a9-lateEmptyInit` stuck@2 `[none,14,none]` vs done@3 `[0,14,0]`. Unchanged: `fused-scalar-good/bad`, `fused-two-acc-different-tensors(-bad)`, `fused-reciprocal-acc-pub`, `fused-failure-after-ap`, `t4-a3split`, `t4-a3mis`, `t4-a4`, `t4-a6`, `t4-a7` |
| S2-M2 partial memory on failure | `run_R` "Application type mismatch" | yes (slots only) | `fused-failure-after` `[0,0,0]` vs `[none,none,none]`; `fused-scalar-bad` and `fused-two-acc-different-tensors-bad` `[7,2,0]` vs `[7,0,0]`; `fused-failure-after-ap` unchanged (the failing accumulate is the first annotation); kinds, pc, occurrence unchanged |
| S2-M3 pre-command memory | `stepCommand_single` "Tactic `rfl` failed" | yes | every run whose first ok annotation is followed by a dependent command: `fused-scalar-good` stuck@1 `[7,none,none]` vs done@2 `[7,2,3]`; `fused-reciprocal-acc-pub` stuck@1 vs done@2; `fused-two-acc-different-tensors` stuck@1 vs done@3; `-bad` stuck@1 vs failed@1; `fused-failure-after-ap` failed@1 `[none,none,none]` vs `[0,0,0]`; `t4-a3split` stuck@1 vs done@4; `t4-a3` stuck@1 vs done@3; `t4-a3mis`, `t4-a4` stuck@1 `[none,none,none]` vs `[0,0,0]`; `t4-a5`, `t4-a6`, `t4-a7`, `t4-a9` stuck@1 vs done. Unchanged: `fused-failure-after` (fails at command 0) |
| S2-M4 `offset` + 1 | `prefixAnn_eq_expand` "Tactic `rewrite` failed" | NO (equivalent at fixture level) | none of the 19 runs changes. Run-equivalent by argument: `execAnn` reads the plan only via `Pub pc`; `prefixAnn (offset + 1 + k)` adds only the annotation being executed, which is an `initZero`/`acc` (no publication) or a `pub` (reads no view). Not a missing fixture; differs from S2-M14 (offset smaller, loses earlier publications: `t4-a3split-chainPlan` flips) |

Notes: S2-M1 does not flip `fused-scalar-good`, the fixture P2a named as its intended detector (observed, cause
not investigated). The S2-M1 mutant of the manifest folds the whole command right-to-left; the probe copies the manifest text.
Cell c of plan table 2 (the pre-command checker column) was NOT probed in P2d; it stays argued (plan O5).

## Authoring facts (measured)

- Patch base `4570a794`; prototype code head `b554437f`; last task commit `cc97e062` (T4); replay PASS: per-patch
  temporary-index `git apply --cached` equals each task commit tree; fresh BASE checkout, `apply --check` then `apply` in
  order, `git diff --cached --stat PROTO -- leanncd` empty (evidence.json `replay`).
- Per-task emission builds (evidence.json), all "Build completed successfully":

| task | patch (lines) | build target | jobs | warnings |
|---|---|---|---:|---:|
| T1 | `01-expand-step` (241) | the 8 slice-1 Plan test targets | 2977 | 13 |
| T2 | `02-fold-lemmas` (363) | `Semantics.PlanFusionTest` | 2973 | 13 |
| T3 | `03-fused-run-theorems` (455) | `LeanNCD` + `Semantics.PlanFusionCorrectnessTest` | 8606 | 62 |
| T4 | `04-checker-fixtures` (132) | `Semantics.PlanFusionCheckerTest` | 2980 | 13 |

- Forbidden-token grep over the patched files: 0 hits (evidence.json `forbidden_token_grep`).
- Mutation manifest: 14 cycles (T1 0, T2 4, T3 7, T4 3); `--check` unfiltered "manifest OK: 14 entries, 14 selected, every old-string
  unique"; `--task T3` 7/7 PASS and `--task T4` 3/3 PASS at emission; `--task T2` not recorded in the notes (the P2a notes list the four
  observed `expect` strings). The full manifest was NOT run on a shipped tree at authoring; the slice-1 manifest was NOT re-run after
  T1's edits (plan O8).
- Fixture counts (measured at the prototype head `cd79028d` with the commands of plan 4(d)): `#eval check` rows 101, `example`/`theorem`
  items 70, total 171. The same two commands on main `4570a794` give 68 and 61 = 129, the slice-1 figure. New in slice 2: PlanFusionTest
  18 + 0, PlanFusionCorrectnessTest 7 + 9, PlanFusionCheckerTest 8 + 0 = 42 (129 + 42 = 171). Three slice-1 fixtures change outcome
  (plan T1), none added or removed.
- Library facts: every new theorem prints axioms `[propext, Classical.choice, Quot.sound]` (p2b); no `sorry`.
- Reachability: `Plan.lean` imports `Plan.Fusion` and `Plan.FusionCorrectness` (`rg -n "^import" leanncd/LeanNCD/Semantics/Plan.lean`);
  `LeanNCD.lean` imports `LeanNCD.Semantics` (line 155) which imports `LeanNCD.Semantics.Plan`.
- Per-task fixtures that were MISSING and added by P2c (inventory by `rg`): a4, a5, a6, a7, a9 plus a3 trio, a3split, a3mis.

## Spec defects D13-D16 (continuing slice 1's D1-D12; spec text NOT edited)

- **D13.** 31.2 "A fused command must justify the same intermediate logical barriers as its annotation sequence" has no formal
  content: `R_Pi` is only defined at command boundaries (30.4) and "intermediate states exist only in its proof" has no relation.
  Formalised choice: `R` at expanded positions of `π.expand`, claimed only at command boundaries (plan F5).
- **D14.** A failed fused command: 30.1/31.3 pin neither the concrete memory after `PlanFailed(o)` nor the snapshot of the matching
  `Failed(o, sigma', alpha', U')`, so transactional vs partial rollback of earlier annotations of the same command is unspecified
  (extends D5). Chosen: transactional (pre-command memory); the matching reference segment includes the earlier annotations (F4).
- **D15.** 29.3 conditions 3 and 4 say "before" without saying it is the expanded order for same-command annotations (the 29.3 header
  sentence says so once). Intra-command read-after-publish (a3) is legal by the text but 32.3 only discusses acc+pub fusion; a kernel
  that reads a pre-command snapshot would violate condition 3 at runtime while the static check passes (implementation obligation,
  "respected internally").
- **D16.** 29.3 says nothing on an empty command (`[]`); harmless no-op, rejected by slice-1 `checkSingleton`, accepted by `checkPlanF`.
- Parked, not spec defects: 32.3 "concurrent updates within a kernel" and aliasing arguments (outside the exact-model scope).

## Authoring checklist (`.claude/skills/slice-plan/SKILL.md`, final checklist)

| item | status | how verified |
|---|---|---|
| Every Lean block compiled via `check-snippet.sh` | N/A: the plan holds no Lean beyond 10 one-line signatures | each line checked as a verbatim `+` line of the four patches by script (0 missing); the patches themselves were built per task (evidence.json) |
| Lean blocks edited after the drafter's verification re-verified | N/A: the signature lines were copied, not edited | same script |
| Every asserted fixture value observed from a real run | yes | values come from p1 §4, p2a, p2b, p2c (`check` throws on mismatch) and from the T1 patch diff (old and new rows); the plan adds no hand-derived value |
| Every regression/parity fixture mutation-tested, both observations recorded | SATISFIED, with one labelled equivalent (S2-M4) | flips observed by proof-free probes: M5-M14 (p2b/p2c) and M1-M3 (P2d, section above); S2-M4 flips none of 19 fused runs and is EQUIVALENT at fixture level (argued; killed only by its library proof; S2-M14 is the observed offset mutant); only the cell-c pre-command-checker column stays argued, not probed |
| Index/locator/order requirement has a fixture that could fail and distinguishes the readings; order claims need a fixture violating both at once | PARTIAL | `t4-a3split-chainPlan` is the sole catcher of the `offset` mutant (observed); a3/a3mis/a4/misfused pin order by separate fixtures; a fixture violating the ready-order AND the pub-order condition at once does not exist (a3mis fails `ready@2` only, the P2b misfused fixture fails `pubOrder@1` only): not satisfiable without new Lean, parked |
| Every prose claim ("X reuses Y", "both reachable from W") checked | yes | `rg` on `Plan.lean` imports, `LeanNCD.lean` import of `Semantics`, `stepCommandF`/`runPlanF` absent from the tree (`rg` no hit), `Fusion.lean` imports `Plan.Run`; counts by `rg -c` and a script over the test files |
| Every file path ls-verified; Files lists derived from the deliverable's location | yes | script over every `leanncd/`/`papers/` path in the plan: 0 missing except the three outputs this commit or later execution creates; per-task file lists come from manifest.json |
| Inherited known gaps re-derived against the tree | yes | the P2a missing-import concern: closed (`Fusion.lean` imports `Plan.Run`); `checkAccMat` implication: no theorem found by `rg`, restated as open; D7/D11/D12 unchanged; lakefile whitespace oddity present (line with `Semantics.PlanFusionCheckerTest`) |
| Value-grep of the moved numbers across the repo | yes, run; dispositions by file category | commands and per-pattern dispositions in plan 4(d) (129 fixtures: 2 hits, 20 mutation cycles: 1, 20 cycles: 4, Slice-1 profile and slice-1 profile hits located); unrelated-vocabulary hits of `singleton`/`fused` (about 90 and 100 files) are classified by tree, not listed one by one, the executor fills the per-file column |
| No `File.lean:NNN` in shipped text | yes | `rg`/script over the plan: 0 hits; the manifest `expect` strings carry positions but are data, not shipped docs text |
| Case x class table with silently-ignored cells; siblings named | yes | plan section 2 (cells a1-a10, b-e; SILENTLY IGNORED cells marked I in two columns); sibling checks named: `checkSteps`, `checkSingleton`, `Order4`, `AnnOK`, `StepOK` |
| Every required fixture names its donor | yes for T4 (plan 2.1); N/A for T2/T3 | T2/T3 fixtures ship inside patches, no implementer writes them |
| Task boundaries pass the reviewer test; tiny pure-addition tasks merged | yes | T4 is tests-only but carries 3 mutation cycles and 8 fixtures, kept separate (its subject is the table); no other tiny task |
| Each risk entry states fixture and cycle counts | yes | plan risk table (T1 0/3 changed/0, T2 18/4, T3 16/7, T4 8/3) |
| Global constraints state exact values and the does-not-do list with owners | yes | plan sections 0-1 |
| New subsystem made discoverable | yes | plan F13 and 4(c): `Plan.lean` imports, `Plan/AGENTS.md` and `Semantics/AGENTS.md` edits, path doc 4.9 |
| Briefs list symbols as `identifier @ file` plus window-read instruction | yes | plan section 3 intro and per-task symbols |
| AGENTS.md injected sections <= ~3k characters | yes (gate) | measured now: Pitfalls 997 bytes, whole file 3978; plan 4(c) measures before and after |
| Mutations in `papers/<plan>_mutations.json` with observed `expect`, `--check` passes | yes | `plan_layer_slice2_mutations_post.json`, evidence.json: "manifest OK: 14 entries" |
| Close-out/authoring records in the record, live plan <= ~800 lines | yes | plan is about 510 lines after review round 1 (`wc -l` below 600) |
| Docs sweep as commands, no heavyweight dispatch | yes | plan section 4; T5 run by the controller |
| Any task expected > ~60 turns marked for split | N/A | the largest estimate is about 40 turns (estimate, not measured) |
| Authoring ran as two dispatches (prototype/verify, then write-up from artifacts); verified code ships as per-task patches that `git apply` cleanly in order onto the base | yes | evidence.json `replay`: the four patches applied in order onto base `4570a794` and built per task (T1..T4 job counts above); patch sha256 values in `plan_layer_slice2_patches/manifest.json` |
| Reviewer and fixer briefs give window sizes and exact functions/sections; reviewers write findings incrementally; fixes one dispatch per group | yes for the review round 1 briefs (both lenses wrote `review_soundness.md` / `review_fidelity.md` as files; one fix dispatch applied all adjudicated findings, the findings being text-only edits of one plan and record); N/A for the whole-branch review, which runs at execution | see "Review round 1" below |

## Lessons

- (a) Library mutants die at library proofs: every one of the 14 mutants breaks a proof before any fixture is evaluated, so
  `mutation-manifest.sh` passing proves only that a proof depends on the mutated definition. Fixtures need proof-free probes (mutated
  function under a new name, fixture re-evaluated) to show a flip; M5-M14 and M1-M3 have them (P2d closed M1-M3 after Phase B;
  M4 is equivalent at fixture level).
- (b) A changed-statement audit (p1 §1) found three slice-1 fixtures that asserted `stuck` for fused or empty commands; they had to
  change with T1, in the same commit as the kernel, and the plan lists old and new outcomes.
- (c) Agents' self-reports under-count harness tool uses by about 1.6x (P2a 56 vs 91, P2b 37 vs 71, P2c 45 vs 76): size caps on the
  harness count.
- (d) A mutant's task tag follows where its `targets` first exist, not where its `old` text first exists (S2-M1/M3/M4 are tagged T2).
- (e) A mutant caught by a single fixture (S2-M14, `t4-a3split-chainPlan`) is a signal to ask which other mutants have exactly one catcher.

## Review round 1 (controller fills)

Plan review (before execution), two lenses, files under `papers/semantics/plan_layer_slice2_artifacts/`. The whole-branch review
files (`wb_review_*.md`) are written at execution, not here.

| id | lens | severity | finding | disposition |
|---|---|---|---|---|
| F-1 | fidelity (`review_fidelity.md`) | Important | 3.1 step 8 deleted the branch before removing the worktree that has it checked out | applied in fix dispatch (worktree first, then branch; exec branch same; consistent with `new-slice` "Finishing the slice") |
| F-2 | fidelity | Important | 31.3 failure row cited `failed_correct_F` for the same occurrence | applied in fix dispatch (`step_failed_command` / `runPlan_R_F`; snapshot is after the earlier annotations) |
| F-3 | fidelity | Important | Lemma 32.1 row "unchanged" contradicted the new 32.1 sentence | applied in fix dispatch (sentence softened: `step_failed_command` is a per-command fused statement, the 32.1 failure half stays `step_failed`; row unchanged) |
| F-4 | fidelity | Minor | 31.2 row omitted the hypotheses (`AnnOK` per expanded position, `FValid`) | applied in fix dispatch |
| F-5 | fidelity | Minor | 4(d) said O8 for the `Step.lean` header comment | applied in fix dispatch (O6) |
| F-6 | fidelity | Minor | `--out` result files unstaged; no command to read the manifest sha256 | applied in fix dispatch |
| F-7 | fidelity | Minor | redundant `--plan` in 3.1 step 2 | applied in fix dispatch (`--plan` is optional in the script usage) |
| F-8 | fidelity | Minor | checklist lacked the last two SKILL.md items | applied in fix dispatch (two rows above) |
| S-1 | soundness (`review_soundness.md`) | Minor | row a4 described a case that a3mis exhibits | applied in fix dispatch |
| S-2 | soundness | Minor | 2.1 presented `verdictF = verdict(expand)` as observed | applied in fix dispatch (by definition; donor column independent) |
| S-3 | soundness | Minor | no fixture puts a reading annotation after an empty command | parked as plan O11 (the controller's "O9" is taken by the closed P2a import item) |
| S-4 | soundness | Minor | T1 gate "two statement changes and nothing else" | applied in fix dispatch |
| S-5 | soundness | Minor | slice-1 transactional-vs-sequential sentence unqualified | applied in fix dispatch (in the 31.3 failure row) |
| P2d-M4 | P2d probes (already above) | Minor | S2-M4 run-equivalent at fixture level | applied in fix dispatch: plan 2.2, risk table, section 5 and the manifest label say "equivalent at fixture level"; equivalent count 3 + 1 |

Harness tool-use counts (self-reports are lower, about 1.6x): fidelity review 41, soundness review 48, P2d 64, Phase B 73; this fix
dispatch 52 (harness count; past its 30 budget; text-only edits located by `rg` plus one manifest `--check`). P2d's harness count is 64
(own tally 62). P3 50, P2c 76, P2b 71, P2a 91, P1 52.
- Fix dispatches (one per finding group): one (this), commit `docs(plan-slice2): apply review round 1 (F-1..F-8, S-1..S-5; S-3 parked)`.

## Value-grep dispositions (controller fills the per-file column after T5)

| pattern | hit files (plan 4(d)) | disposition | commit |
|---|---|---|---|
| `129 fixtures` | path doc, `plan_layer_record.md` | path doc edited (171, "+ 42"); record historical: keep | docs sweep |
| `20 mutation cycles` / `20 cycles` | path doc, `Plan/AGENTS.md`, `plan_layer_artifacts/docs_sweep_results.md` | first two edited (34 / 20+14); historical records keep | docs sweep |
| `singleton` / `non-singleton` / `fused` | spec, path doc, `Semantics/AGENTS.md`, `Plan/AGENTS.md` | re-read; edited where stale (spec lines 170, 4699-4715 and the nine paragraphs; `Semantics/AGENTS.md` scope line "fused plan commands remain outside it" removed); other trees unrelated vocabulary | docs sweep + review fix |
| `Slice-1 profile` / `slice-1 profile` / `slice-1 plan layer` | spec (9 headings), path doc (4 further spots: roadmap diagram, 4.x summaries, fixtures table), `Plan/AGENTS.md` | edited; `plan_layer_*` records and `Plan/*.lean` doc comments keep | docs sweep |
| `invalid-fused` / `step-empty-command-stuck` / `invalid-empty-command` | `PlanValidityTest.lean`, historical patches/notes | no stale document hit; `step-empty-command-stuck` has no hit | docs sweep |
| measured fixture total (`#eval check` + `example`/`theorem`) | | 101 + 70 = 171, as expected | docs sweep |

## Close-out (controller fills)

- Execution worktree / branch: `.claude/worktrees/plan-layer-slice2-exec` / `worktree-plan-layer-slice2-exec`.
- Base `main` SHA at execution (docs-only landing commit): 03a2372f (docs landed on main before the worktree; main was 4570a794 before it).
- Per-task commits and builds (patch sha256 matched `manifest.json`, `apply --check` clean): T1 187e9d15 (jobs 2977), T2 89ee8513 (2973),
  T3 6ed8dc9e (8606), T4 003080b2 (2980). Patches applied by the controller directly (mechanical), no implementer dispatches.
- Docs-sweep commit: bc888183 ; whole-branch review fixes: the commit after it, `docs(semantics): adjudicate whole-branch review ...`.
- Full default build: 8789 jobs, "Build completed successfully", no `error` line; forbidden-token grep: no hits (exit 1).
- Mutation manifest, whole file: 14/14 PASS, files restored byte-identical: yes (all 14); slice-1 manifest regression: 18/20 as shipped, 20/20 after repair ;
  `expect` repairs: A2-e `Simulation.lean:577` -> `578`, A2-f `583` -> `584` (pure line shift from T1; same error kinds, re-run 2/2 PASS), Direct path, in the docs-sweep commit.
- S2-M1..M4 fixture-flip probes: observed at authoring (P2d: M1-M3 flip, M4 equivalent at fixture level); at execution the manifest runs T2 4/4, T3 7/7 and the unfiltered 14/14 passed.
- Measured fixture total: 171 (101 + 70, as expected) ; TOC counts before/after of the path doc: 38/37 -> 39/38 ; Plan/AGENTS.md Pitfalls bytes before/after: 997 / 1273 (whole file 3978 -> about 4.9k).
- Execution session total tokens (`token-report.py 3a4c384e-...`; Rule 6 budget <= ~175M): 16.9M (controller 8.8M, peak 182k, 72 turns; two review dispatches 4.1M + 3.9M, 36 and 33 turns).
  Authoring tokens (target <= ~50M): 44.8M. Any overrun explained: none.
- Whole-branch reviews (opus): soundness 0 Critical / 1 Important / 5 Minor; fidelity 0 / 2 / 6. Adjudication: the shared Important (path doc and `Plan/AGENTS.md` said a mis-fused plan
  "passes `checkPlan` with a wrong value"; actually `checkSteps` is vacuous and `checkSingleton` rejects, and `misfused-run-undetected` yields the right value, `t4-a5-reinitMid` the wrong one),
  the stale spec passages (lines 170, 4699-4715), the `step_failed_command` / `stepCommand_not_stuck` description strength, the 30.4/29.3 position wording, the D13 pointer and the
  `Plan/AGENTS.md` omissions were FIXED in docs. PARKED (Lean files, patched, not touched): W-3 `runPlan_R_F` docstring says "at command boundaries" but states R only at the end; W-4 no
  fixture runs `checkPlanF` on a plan containing `[]`; W-6 no `#print axioms` lines for `step_R_command`, `step_failed_command`, `stepCommand_not_stuck`, `execAnns_not_stuck`, `runFrom_agree`
  (axioms of the file's other theorems are `[propext, Classical.choice, Quot.sound]`; no `sorry`/`native_decide` in the changed files). Review files: `plan_layer_slice2_artifacts/wb_review_{soundness,fidelity}.md`.
- Merge SHA on local `main`: see git log (`Merge branch 'worktree-plan-layer-slice2-exec'`); prototype branch tagged `plan-layer-slice2-proto` before deletion: yes (done at integration);
  branches and worktrees removed: prototype and exec (done at integration); not pushed (`main` ahead of `origin/main`): yes.
- Parked (plan section 5): O1 D13-D16 spec-text fixes, O2 lakefile whitespace, O4 mid-run `run_R_F`, O6 `Step.lean` header comment, O10 empty-command
  mutant, O11 no fixture reads after an empty command; carried over: D7, D11, D12, buffer reuse/retirement, checker completeness, `checkAccMat`.
