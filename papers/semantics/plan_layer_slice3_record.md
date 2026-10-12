# Part V slice 3 (buffer retirement): record

Authoring record for `papers/semantics/plan_layer_slice3_plan.md` (the live plan). Facts here are measured or quoted from the artifacts in `papers/semantics/plan_layer_slice3_artifacts/` and `papers/semantics/plan_layer_slice3_patches/`; nothing is hand-derived. The close-out at the end is empty: the execution controller fills it.

## What was prototyped (Phase A, branch `worktree-plan-retire-proto`, base `main` 69214c64)

| dispatch | scope | result (from the notes) |
|---|---|---|
| A1 | `Plan/{Syntax,Memory,Step,Simulation}.lean` | `Build completed successfully (2963 jobs).` for `LeanNCD.Semantics.Plan.Simulation`; no `sorry`; no new axiom. Two tiny proof fixes only (`Function.update_of_ne` argument order, a closed second `split_ifs` goal); `live_input` needed only `simp_all`; R5 cost about one turn per step kernel |
| A2a | `Plan/{Validity,Run,Correctness}.lean` | 2964, 2965, 2966 jobs for `Validity`, `Run`, `Correctness`; `checkRet_sound`, `checkRet_complete`, `live_output_of_valid` use `propext`/`Quot.sound` only; `terminal_adequacy` adds `Classical.choice`. One proof fix: the `.2` projection goes on `(hv.retOK i B hc x hxz).2` |
| A2b | `Plan/{Fusion,FusionCorrectness,Faults}.lean`, whole library, test survey | `Fusion` 2966, `FusionCorrectness` 2968, `Faults` 2969, `LeanNCD` 8598, default targets 8792 then 8793 with the new test. `Faults.lean` needed no change; no theorem statement changed; four pre-existing `declaration uses sorry` warnings only |
| A3a | `test/Semantics/PlanRetireTest.lean`, `lakefile.toml` | `Semantics.PlanRetireTest` 2982 jobs; 10 plans, 17 `#eval check` rows, 10 `example ... := by decide` verdicts, 1 theorem (`rtChain_valid`); default targets 8793 jobs |
| A3b | mutation manifest | `plan_layer_slice3_mutations_post.json`, 10 cycles, `--check`: `manifest OK: 10 entries, 10 selected, every old-string unique`; full run `10/10 cycles passed`, each rebuild `Build completed successfully (2982 jobs).` |
| A4 | per-task patches (`emit-patches.py`) | four patches, sha256 equal to `manifest.json`; replay PASS (temporary-index `git apply --cached` per patch, then a scratch worktree at the base with `apply --check` and `apply` in order; the `leanncd` tree equals the prototype's) |

Overall non-papers diff: `14 files changed, 786 insertions(+), 63 deletions(-)` (evidence.json `overall_numstat_non_papers`). Patches: 01-core 655 lines, 02-validity-run-correctness 239, 03-fusion 55, 04-fixtures 188. `evidence.json` base `69214c6426aa1fb06c9db4c5bc11a27d3c98a2c4`, code head `e452e970`.

Fixtures by row (observed values in `a3a_notes.md`): `retire-valid-chain`, `retire-valid-chain-donor`, `retire-valid-scalar`, `retire-valid-scalar-decode`, `retire-read-after`, `retire-neighbour-other-address`, `retire-output`, `retire-unpublished`, `retire-fused-after-read`, `retire-fused-before-read`, `retire-twice`, `retire-dup-in-block`, `retire-fault-none`, `retire-fault-at-retire`, `retire-fault-after-retire`, `retire-fault-fused-at-retire`, `retire-fault-fused-none` (17 rows).

## Mutation results (from `plan_layer_slice3_mutation_results.md`)

10 entries, 10 killed, 0 equivalent, every file restored byte-identical. Every mutant dies at a library PROOF, so lake never reaches `PlanRetireTest` in a mutated build (same shape as the D7 manifest).

| label | killed at (identifier) |
|---|---|
| S3-M1 `execRet` is the identity | `execRet_not_mem`, `execRet_mem` (`change` tactic failed) |
| S3-M2 `execRet` leaves the first member (`B.tail`) | same two |
| S3-M3 `checkRet` always true | `checkRet_sound`, `checkRet_complete` (type mismatch) |
| S3-M4 `checkRet` drops the live clause | same two (first attempt dropped `π` and died on a type-level artefact; the committed mutant keeps `π.Live` via `\|\| true`) |
| S3-M5 `checkRet` drops the not-an-output clause | same two |
| S3-M6 `checkReady` over `Pub` | `checkAnn_acc_sound`, `checkAnn_acc_complete` |
| S3-M7 `SlotView .pub` over `Pub` | `Memory.lean` projections and `readPub_eq` |
| S3-M8 `ReadyOK` over `Pub` | `checkAnn_acc_sound`, `checkAnn_acc_complete` |
| S3-M9 `readPub` over `Pub` | `readPub_eq` (`rw [if_pos ha]` fails) |
| S3-M10 `RetOK` drops the not-an-output conjunct | `checkRet_sound`, `checkRet_complete` |

Row-level kills were NOT run by the manifest. They were observed by hand in A3a with the broken proofs temporarily `sorry`'d (mutated files restored, `git status --short` clean): M1 fails 12 rows; M3 fails `retire-output`, `retire-unpublished`, `retire-twice` (each with its `example`); M6 fails `retire-read-after` and `retire-fused-before-read` (each with its `example`; the runs of both are unchanged, only the verdict flips). M2, M4, M5, M7-M10 were not row-probed.

## Deviations from the design spec (all go into the spec by plan task T5(b))

1. `R` gets a sixth field `retPub : forall a, Ret pc a -> Pub pc a` (R6), not in the spec. Needed by `step_pub` (a freshly published member is `Live`) and by `step_init`/`step_acc` (a retired address is not an unpublished write target); `R` has no memory of earlier steps' `RetOK` (a1_notes).
2. `readPub_eq` is restated pointwise on `Live` (the function equality is false once a retired address keeps its ghost value); new helper `readPub_le`; `step_acc` and `step_failed` reach readiness through `evalReady_of_le`, per-member values through `delta_congr`; `decode_of_R`'s hypothesis `outs` is over `Live` (a1_notes).
3. `ret_succ` is in `Simulation.lean` beside `pub_succ`, not in `Syntax.lean`; extra lemmas `live_zero`, `Live.pub`, `pub_succ_of`, `ret_succ_of`, `live_succ_of` (a1_notes).
4. The spec predicted the retire-of-an-unpublished-accumulator row to end `done`; observed: checkPlan false and the run is `stuck` at the LATER `pub` (the clear does happen). A plan that never publishes the retired address would end `done` (a3a_notes).
5. The spec called `readPub` ignoring `Ret` an equivalent mutant; it is not (S3-M9 is killed at `readPub_eq`). The spec's planned mutants "R5 weakened" and "`step_retire` omitted from `execAnns_R`" were not run; the manifest instead has S3-M6..S3-M10. Count 10, spec said about 8.
6. A retire of an output runs to `done` with `Decode` returning `none` (a3a_notes): the clause is terminal, and the static check is the only guard.

## Findings of the plan authoring (not in the notes)

- **Slice-1 manifest regression is already broken at the `old` string.** `mutation-manifest.sh --check` on the prototype tree: `plan_layer_slice2_mutations_post.json` (15 entries) OK, `plan_layer_d7_mutations_post.json` (9) OK, `plan_layer_slice3_mutations_post.json` (10) OK, `plan_layer_mutations_post.json` (20) FAILS at entry 5 (`A3b-3 readPub ignores Pub`): `old` string occurs 0 times in `Memory.lean` (the guard is now `π.Live`). `--check` stops reporting at the first problem it prints, so a second broken entry could hide behind it; the plan's T4b runs the whole manifest. The `expect` strings of the 35 slice-1/2 entries all carry a `File.lean:L:C` location and 32 of them mutate a file the patches edit, so a re-run is expected to need repairs (slice 2 saw 18/20 as shipped, 20/20 after repair at its own landing). The prototype never ran the old manifests; this is the largest unmeasured cost of the slice.
- **No "As formalized" note exists in spec 30.3 or 33.2.** The brief says the headers of the 30.2, 30.3, 30.4, 31.1 and 33.2 notes say "no retirement"; actually 30.3 and 33.2 have no note, and eight further notes (29.3, 31.2, 31.3, 32.1 and the 31.4 variants) plus the preamble and closing Part V sentences also carry "no retirement". The plan creates the 30.3 and 33.2 notes and edits all 12 hit lines (value-grep: `rg -n "no retirement"` has 12 hit lines at authoring).
- **Statements in the spec that became false**, found by reading the 30.4, 31.1, 31.3 notes: "Because nothing is retired, `SlotView` maps exactly the addresses of Pub"; R3 and the `Decode` bullet over `Pub`; the footprint row of the 31.1 table (`Pub` instead of `Live`); the Lemma 31.2 paragraph "nothing is retired ... needs no Need_pub argument". All rewritten in T5(a).
- **Fixture count discrepancy.** By the `rg -c` method of slice 2 (`^#eval check` plus `^(example|theorem)\b` over `leanncd/test/Semantics --glob "Plan*Test.lean"`), the prototype head has 139 + 89 = 228, of which 28 are `PlanRetireTest` (17 rows, 10 `example`s, 1 theorem: `PlanRetireTest.lean` has 17 and 11). Without it: 200. The path doc and spec say 180 (composition 129 + 47 + 4), which predates D7's `PlanFaultsTest` (12 rows + 7 items = 19); 200 - 19 = 181, one unexplained. The plan's doc edit uses the measured total and says how it was counted; the executor re-measures after T4.
- **Mutation count in the path doc.** It says 35 (20 + 15) and omits the D7 manifest (9); by `rg -c '"label"'` the four manifests hold 20, 15, 9, 10 entries (54). The path doc edit states all four.
- **Intermediate commits are not whole-library green.** After T1 the library stops at `Validity` (a1_notes), after T2 at `Fusion`; green from T3 (`LeanNCD`, 8598 jobs) and the default targets from T4 (8793). Stated in the plan as a bisect caveat; same cut as the prototype.
- **Prototype branch carries Lean commits and must not be merged**; only the docs-only artifacts land on `main` first (slice 2 procedure).
- `Faults.lean` needed no change (a2b_notes). `evidence.json`'s `mutation_rows` list has a malformed last element (a table-parsing artefact of the S3-M4 note: label `S3-M4`, cycle `library proofs`); the first ten rows are right. The plan does not rely on that element.

## Authoring facts (measured at authoring)

- `shasum -a 256` of the four patches equals `manifest.json` and `evidence.json`.
- `git rev-parse main` = `69214c6426aa1fb06c9db4c5bc11a27d3c98a2c4` (unchanged since the base).
- Pitfalls section of `leanncd/LeanNCD/Semantics/Plan/AGENTS.md`: 1483 bytes (the only hook-injected section); whole file 6151 bytes.
- `lean_executable_semantics_path.md` and the spec headers: grep results quoted in plan section (a) and (c).
- Plan length: see the commit message and the report (<= ~800 lines).

## Authoring checklist (`.claude/skills/slice-plan/SKILL.md`, final checklist)

- [x] Lean blocks: none in the plan (patches hold the code; identifiers only). Patches compiled in the prototype and replayed.
- [x] Fixture values observed from real runs (a3a_notes); the plan transcribes none by hand.
- [x] Mutation fixtures: row-level kills observed for M1, M3, M6; the others are proof-killed only, stated as such (plan T4, O3).
- [x] Index/locator/order claims: fused retire order has a fixture pair (`retire-fused-after-read` / `-before-read`) whose two readings differ (verdict and run kind differ).
- [x] Prose claims about code checked with `rg -n` in the prototype tree (identifiers listed in the plan header note).
- [x] Every path `ls`-checked (tools, docs, Plan modules; the one new file is created by T4).
- [x] Inherited gap lists re-derived: slice 2's open "buffer reuse/retirement" is split (retirement is this slice; reuse stays); the `Step.lean` "slice-1 profile" comment of slice 2's O6 was not found in `Step.lean` (plan O7).
- [x] Value-grep of moved numbers written as commands (plan T5(e)); `no retirement` grep is part of the exit check.
- [x] No `File.lean:NNN` in the plan or record (exit grep run).
- [x] Case x class table: plan Review Focus.
- [x] Risk table states fixture and mutation-cycle counts per task.
- [x] Global Constraints give exact values and name what is not done and who owns it.
- [x] Discoverability: no new subsystem; `Plan.lean` imports all Plan modules.

## Lessons

- Applying pre-built patches needs no implementer; the controller applies, builds and commits.
- Check older manifests with `--check` at authoring time: it is free (no build) and found a hard failure the prototype missed.
- A brief's "section X has a note that says Y" needs a grep before it is repeated: 30.3 and 33.2 had no note at all.

## Review round 1

Both lenses ran on the most capable model (`fable`), in parallel, writing to `plan_layer_slice3_artifacts/wb_review_soundness.md` and `wb_review_fidelity.md`.

- Soundness lens: 0 Critical, 0 Important, 4 Minor (about 22 turns). Verified clean: every `Valid` clause is consumed or a labelled diagnostic and `checkRet` is exactly `RetOK`; `dead`/`retPub` preservation sound (`retPub` is derived from `RetOK`, not assumed); no use of the old function equality `readPub_eq`; fused plans carry the new fields through `R_transport`; `Faults.lean` unchanged is justified; no `sorryAx` in the new theorems. Findings: F1 (case x class table lacks the cell "retire before `initZero` is a run-time no-op; run ends `done`, only the checker rejects"), F2 (no fixture retires two or more distinct addresses in one block), F3 (the two `-at-retire` fault rows cannot tell a no-op `execRet`; the two `-none` rows repeat `runPlanE_noFault`), F4 (`RetOK` docstring called the whole `Live` clause "the safety half").
- Fidelity lens: 0 Critical, 0 Important by its grading, 9 Minor (about 54 turns). Every identifier and count in the changed hunks checked clean (228 = 139 + 89, 28 in `PlanRetireTest`, 54 = 20 + 15 + 9 + 10 cycles). Findings: F1 "ten modules" (eleven), F2 path-doc "Plan modules" list missed, F3 path-doc header quote for 30.3/33.2, F4 29.3/31.1 sets omit `Ret`/`Live`, F5 stale `Decode`/`Valid` docstrings, F6 "reading a retired slot is stuck" omits `Decode`, F7 wrong results-file pointer, F8 design spec said `retPub` is consumed by `step_init`/`step_acc` and `delta_congr` by `step_failed`, F9 design spec's account of the old "180".
- Adjudication (ledger Rulings): fidelity F1-F4, F6-F9, F5 and soundness F4 re-graded Important (a false or stale statement in a shipped document or docstring that a reader would act on) and fixed in ONE pass, commit `4a9916aa`. Verified by exact-count asserted edits, exit greps (no `File.lean:NNN`), `git diff --numstat` (each Lean file exactly 1/1 lines: no line shift, so no manifest `expect` moved), TOC 40/39, full default build 8793 jobs green, slice-3 manifest rerun 10/10 on the final tree. Prose has no failing-test form, so no RED step applies.
- Deferred minors: soundness F1, F2, F3 (test-strength and table completeness; the library proofs already catch the mutants), and the fidelity "declined to judge" items (proof-status labels "Proved (slice-1 profile)" with a "Slice 3" suffix; design-spec estimate "about 24" constructor-case sites, actual 21).

## Value-grep dispositions (after T5)

`bash scratchpad/value_grep.sh <exec>` over the patterns of plan section (e), excluding `plan_layer_slice3_*`:

| pattern | file | disposition |
|---|---|---|
| "180 fixtures", "35 mutation", "35-cycle", "readPub = c.published" | none | no hits after T5 |
| "no retirement" | design spec (2), `plan_layer_slice2_plan.md` (3), `plan_layer_plan.md` (1), `plan_layer_artifacts/review_fidelity.md` (2), `plan_layer_slice2_artifacts/wb_review_fidelity.md` (1) | keep: historical plans/reviews and the design spec's own statement of the pre-slice profile |
| "nothing is retired" | `tensor_logic_semantics.md` (1) | keep: scoped "In slices 1-2" sentence in 31.3, true; `plan_layer_plan.md` (2), `a3b_notes.md`, `review_fidelity.md`: historical |
| "non-reused" | `tensor_logic_semantics.md` (1, section 34 bullet) | EDIT (done in T5); the other hits are historical plans/records/reviews: keep |
| "slices 1-2" | `lean_executable_semantics_path.md` (1), `tensor_logic_semantics.md` (1) | keep: intentional scoped text ("35 of slices 1-2", "In slices 1-2 that step is trivial"); `plan_layer_slice2_plan.md` (2): historical |
| "slice-1 and slice-2" | design spec (1), `plan_layer_slice2_plan.md` (1) | keep: design spec edit instruction text; historical |
| "slice 1-2 plan layer" | `plan_layer_slice2_plan.md` (1) | keep: historical |

Measured fixture total after T4: 228 (139 + 89); `PlanRetireTest`: 17 rows + 11 items (10 `example` + 1 `theorem`).
Path doc TOC counts before / after (`^#{2,4} ` and `^ *- \[`): 39 / 38 -> 40 / 39 (the second count is the first minus 1).
`Plan/AGENTS.md` Pitfalls bytes before / after: 1483 / 2049 (gate <= ~3000); whole file 6151 / 7427.
Parked, not moved by this slice (Rule 14): the path-doc snapshot said "ten modules" and `Plan/AGENTS.md` said "the ten modules below" while eleven exist; both were corrected in the review fix pass because the branch re-shipped the sentence.

## Close-out

- Execution worktree / branch: `.claude/worktrees/plan-retire-exec` / `worktree-plan-retire-exec`.
- Base `main` SHA at execution (docs-only landing commit): `097ebeff` (on top of the spec commit `69214c64`).
- Per-task commits and builds (sha256 matched the manifest, `apply --check` clean, no hand-merge): T1 `327f4b30`, gate `Plan.Simulation` 2963 jobs; T2 `11d90dde`, `Plan.Correctness` 2966; T3 `dc698955`, `Plan.FusionCorrectness` 2968, then `LeanNCD` 8598; T4 `f3210475`, `Semantics.PlanRetireTest` 2982, 17 rows printed, recount 17 / 11.
- T4b: slice-1 manifest as shipped: validation FAILED before any cycle (entry `A3b-3` `old` string gone); after repairing that entry's `old`/`new` to the `Live` form it ran 5 / 20 (all 20 mutants still broke their build; 15 `expect` locations stale); after repairing those 15 locations (message text kept, except `A3b-3`: now a `rewrite` failure at the pointwise `readPub_eq`, and `A3b-2`: dies in `Validity.lean` before `Correctness`) 20 / 20. Slice-2: 3 / 15 as shipped (12 stale locations, all mutants still died) -> 15 / 15 after repair. D7: 9 / 9 untouched. Repair commit `966f38f7`. The controller did the repairs itself (mechanical, scripted from the observed first errors) instead of the one-fixer-per-manifest dispatch the plan allowed.
- New manifest: `--check` OK (10 entries, every old-string unique); full run 10 / 10 (twice: on the T4 tree and again on the final tree after the review fixes); files restored byte-identical.
- Docs-sweep commit `ca512754` (spec 17 asserted edits + 2 more for section 34; design spec 8; path doc 12; AGENTS 18); whole-branch review fix commit `4a9916aa`.
- Full default build on the final tree: `Build completed successfully (8793 jobs).`; four pre-existing `declaration uses sorry` warnings only; forbidden-token grep (`sorry|admit|axiom|native_decide`) over `Plan/*.lean`, `Plan.lean` and `Plan*Test.lean`: nothing.
- Session tokens (`token-report.py 0381d9c1-...`, the whole session including brainstorming, authoring and execution): 66.4M total, of which subagents 34.1M (authoring dispatches A1 4.7M, A2a 1.6M, A2b 2.8M, A3a 5.5M, A3b 5.3M, Phase B 5.7M = 25.6M; the two review lenses 2.1M + 6.5M = 8.6M) and the controller 32.1M (peak context 376k, 137 turns) covering brainstorming, authoring coordination and execution. The authoring-versus-execution split of the controller's 32.1M was not measured; combined, the session is far under Rule 6's execution budget (<= ~175M) and the authoring dispatches alone (25.6M) are under the ~50M authoring target. The controller's peak context is above the 250k dispatch rule, which applies to dispatches, not the controller. Harness tool uses ran above self-reports again (A3a 85 vs "about 50", A3b 75 vs 45).
- Whole-branch reviews: soundness 0 Critical / 0 Important / 4 Minor; fidelity 0 / 0 / 9 by their grading (8 re-graded Important plus F5 and soundness F4, all fixed).
- Merge SHA on local `main`: `06f44c2d` (`--no-ff` of `worktree-plan-retire-exec`; `git diff --stat worktree-plan-retire-exec HEAD` was empty). `git diff --stat worktree-plan-retire-proto HEAD -- leanncd` showed only the three AGENTS nodes (T5(d)) and the three one-line docstring fixes of the review pass, as expected. Prototype tagged `plan-layer-slice3-proto` before deletion (local only). Both worktrees and both branches removed (`worktree-plan-retire-proto` with `-D`, unmerged, the tag keeps its history). NOT pushed: `main` is 12 ahead of `origin/main`.
- Parked (plan open items): O1 later slices (reuse and aliasing starts from `dead`; scan liveness; retiring inputs; copy/relocate), O2 lakefile missing space, O3 row probes for S3-M2, M4, M5, M7-M10, O4 `dead`/`retPub` have no fixture, O5 mutation-manifest `--task` validation gap, O6 fixture-count reconciliation (200 vs 180), O7 stale "slice-1 profile" comments; plus the deferred minors above.

## Deferred minors resolved (post-merge follow-up, Direct path, branch `worktree-retire-minors`)

The user asked for all five deferred minors of the whole-branch reviews to be fixed. Test-first (rows written with predictions, all four held on the first real run), then a hand mutation probe per row (the broken library proofs were temporarily `sorry`ed in a scratch edit, the files restored with `git checkout --`, the tree verified clean; no Lean library file differs from `main`).

| deferred minor | resolution |
|---|---|
| soundness F1: plan case table lacked "retire before `initZero`" | row added to the table in `plan_layer_slice3_plan.md` (now three YES cells: retire an output, retire twice, retire before `initZero`) and pinned by the new fixture `retire-before-init` (`checkPlan` false, run `done`, every value correct, decode `some 2`). Probe: `checkRet` without its live clause flips its verdict |
| soundness F2: no retire block with two or more distinct addresses | fixtures `retire-multi-distinct` (`done`, `[none, none, some 4]`) and `retire-multi-second-unpublished` (`checkPlan` false only through the second member; run `stuck` at the later `pub`). Probes: `execRet` clearing only the first member fails both; `checkRet` checking only the first member fails the second row and its `example` |
| soundness F3: the `-at-retire` fault rows cannot tell a no-op `execRet` | row `retire-fault-fused-after-retire` (fault at the last `pub`, after the fused command that contains the retire; memory `[some 0, none, some 4]`). Probe: a no-op `execRet` fails it (and 13 other rows). The `-none` rows stay: they are cheap controls of the proved `runPlanE_noFault` |
| fidelity declined: proof-status labels "Proved (slice-1 profile)" | the Lemma 31.2 and Theorem 31.3 rows and three section 34 bullets (validation, progress, terminal decoding) now say "slice-1 to slice-3 profile" (the "Slice 3" suffix already stated the extension) |
| fidelity declined: design-spec "about 24" constructor-case sites | now 20 arms (21 `rg` hits at HEAD, one of them the constructor declaration) and the risk bullet no longer claims `Faults` needed arms (`Faults.lean` needed none) |

Counts after the follow-up (`rg -c` method): `PlanRetireTest` 21 `#eval check` rows + 13 `example`s + 1 theorem = 35 (was 28); `Plan*Test.lean` total 143 rows + 92 items = 235 (was 228); the path doc and its snapshot SHA (`fe013f1b`, the fixtures commit) were updated. The T4 numbers elsewhere in this record and in the plan (17 rows, 28 fixtures, 228) describe the patch as shipped and are left as the historical measurement. Nothing else is deferred from the reviews; the other parked items (O2, O3, O4, O5, O6, O7) are unchanged.

Follow-up review (one fresh lens, `wb_review_minors.md`): 0 Critical, 0 Important, 4 Minor, all wording or citation: F1 and F2 comments in `PlanRetireTest.lean` misdescribed what `retire-multi-distinct` pins (executor side only) and how `rtMultiBad` differs from `rtMulti`; F3 the constructor-case count (20 arms; 21 `rg` hits include the constructor declaration); F4 two section 34 bullets named only singleton theorems. Re-graded by effect (a reader would wrongly believe the checker half is pinned by `retire-multi-distinct`) and fixed in one pass; the module rebuild printed all 21 retire rows. No deferred review items remain.

## Cosmetic follow-up (parked items O2, O6, O7 closed)

Direct path, one commit, branch `worktree-cosmetic-nits`; no review dispatch (whitespace, six one-line comment edits and prose numbers; the controller read the diff and `git diff --numstat` shows each file changed by the lines named, no line shifted, so no manifest `expect` location moved).

- O2: `leanncd/lakefile.toml` now has a space after `"Semantics.PlanRetireTest",`.
- O7: the stale "slice-1 profile" comments now say "slice-1 to slice-3 profile" in `Memory.lean` (module header and the `R` docstring), `Correctness.lean` and `Simulation.lean` headers, `Step.lean` header ("slice-1/2"), and `Syntax.lean` header (which now lists block retire). Kept on purpose: `Step.lean`'s docstring of `Singleton` and `Validity.lean`'s `singleton` field, which describe the singleton-command condition that really is the slice-1 profile.
- O6 reconciled: at the commit that wrote the path doc's "180" (`4d72aa03`), `rg -c` gives 110 `#eval check` rows + 71 `example`/`theorem` items = 181, so the doc was off by one; `PlanFaultsTest` (12 rows + 7 items = 19) was added afterwards, giving the 200 before slice 3. The path doc and the design spec now say so.
- Not touched (not cosmetic): the mutation-manifest `--task` validation gap (a functional gap in `mutation-manifest.sh`), and O3/O4 (test gaps: row probes for S3-M2, M4, M5, M7-M10; no fixture for `dead`/`retPub`).

## `--task` gap correction (O5 was stale)

The plan and the cosmetic follow-up above list the mutation-manifest `--task` validation gap as an open, functional item. That was a stale claim carried from a memory note dated 2026-10-03 ("validates every entry over the WHOLE manifest before applying `--task`/label filters"). It was fixed on 2026-10-10 by `a2b5d50f` ("validate only selected mutation manifest files") and four follow-up commits (`d42172e1`, `e75fc7ac`, `84927816`, `0396532f`), all ancestors of `main`; the script header documents the scope ("File existence and old-string uniqueness are checked only for selected entries").

Re-measured on current `main` (the first time this session actually looked): a scratch manifest with task 1 on a real file and task 2 on a file that does not exist yet gives `--check --task 1` exit 0 ("1 outside the selection not validated"), unfiltered `--check` exit 125 and `--check --task 2` exit 125 ("no such file"); `bash leanncd/scripts/mutation-manifest-selftest.sh` reports `119 checks passed`. Nothing to fix in `mutation-manifest.sh`. The statements above (plan "Global Constraints" table, O5, and the "Parked" and "Not touched" lines of this record) are left as written for history and are superseded by this section. Lesson: re-verify an inherited "still open" claim against the tree before scheduling work on it.

## R regression net (step 1 of the post-slice order; parked item O4 closed)

Direct path, branch `worktree-r-net`; test-only (no Lean library file differs from `main`). `dead` (R5) and `retPub` (R6) only appeared inside the step proofs; the buffer-reuse slice will reshape `R`, so they are now instantiated on concrete plans at every command boundary, in the pattern of `PlanSimulationTest.tagged_R_every_pc` but with the per-step side conditions taken from `Valid.stepOK` instead of hand proofs.

Added to `PlanRetireTest.lean` (section 9): `chainMem` (the memory after the first `n` commands of the actual run); the generic lemmas `R_every_pc_of` (valid singleton plan) and `R_every_pc_F_of` (valid fused plan, command boundaries, via `step_R_command`); the instances `rtChain_R_every_pc`, `rtMulti_R_every_pc`, `rtFusedOk_R_every_pc`; `rtChain_retired_slot_free`, `rtMulti_retired_slots_free` (both members of a two-address block) and `rtFusedOk_retired_slot_free`, which read `retPub` and `dead` off the intermediate states (retired address is published, not live, slot free); and independent computed checks that do not go through `R`: five `rfl` examples (retired slots `none`, a live neighbour `some 0`) and three `#eval check` rows (`retire-net-*-live-neighbour`, the live slot holding `some 4`; `= 3 + 1` in exact rationals, which kernel `rfl` cannot normalise). All new theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

Hand mutation probes (library proofs `execRet_not_mem`/`execRet_mem` temporarily `sorry`ed in a scratch edit, files restored with `git checkout --`, tree verified clean, library diff vs `main` empty): `execRet` a no-op kills four of the new `rfl` examples; clearing only the first member kills exactly the `rtMulti` second-member example; wiping the whole memory kills the `rtChain` point-0 `some 0` example, the three `retire-net-*-live-neighbour` rows and the three `*_R_every_pc` instances (their `hstep` goals). Honest limit: the `R` conclusions themselves follow from the general lemmas (a sorried `step_retire` still yields `R`), so they stop compiling only if `R`'s shape or the step lemmas' signatures change. The net can fail on its own through (i) the `hstep` side goals of the instances (`interval_cases k <;> rfl`: every step of the actual run must return `ok`; the wipe-everything probe killed all three original `*_R_every_pc` instances this way, the later `pub` getting stuck), (ii) validity by `decide`, and (iii) the independent computed checks.

Counts (`rg -c` method), final after the review follow-up below: `PlanRetireTest` 27 `#eval check` rows + 24 `example`s + 17 theorems = 68 (was 35); `Plan*Test.lean` total 149 rows + 119 items = 268 (was 235). The path doc counts and snapshot SHA (`7932c87b`, the last Lean-bearing commit) are updated; the T4 numbers elsewhere in this record describe the patch as shipped. Not done here (not requested): the Nodup conjecture for coverage conditions 1 and 2.

R-net review (one fresh lens, `wb_review_rnet.md`): 0 Critical, 1 Important, 2 Minor. The net itself was verified sound (the `hn`/`hstep` hypotheses are not vacuous or circular, `chainMem` follows the actual run, `step_R_command` is used at command boundaries only, pc indices and addresses match, axioms clean).
- F1 (Important, fixed): `dead` and `retPub` are trivially true until something is retired (`Live = Pub ∧ ¬ Ret`), and in the three original net plans the retire was followed only by a `pub`, so only `step_pub` was exercised; no `acc` or `initZero` ran after a retire, which is exactly the shape the reuse slice introduces. Added `rtNeighbour` (an existing plan with an `acc` after its retire) to the net and the new plan `rtInitAfter` (`initZero [p2]` after `retire [p0]`, row `retire-init-after-retire`, `done`, `[none, some 3, some 4]`), instances `rtNeighbour_R_every_pc`, `rtInitAfter_R_every_pc`, `dead`/`retPub` read after the later `acc` and after the later `initZero` and `acc`, and independent computed checks (p0 stays `none`; p2 holds `some 0` right after the `initZero`, proving it ran; p2 ends `some 4`). Probe: a no-op `execRet` kills the new row and three of the new `rfl` examples. A no-op `execInit` is NOT attributable to this module: it breaks the earlier `PlanStepTest` fixtures first, so the build never reaches `PlanRetireTest`.
- F2 (Minor, fixed): the "Honest limit" paragraph overstated what a reuse-slice change to `R` would break and understated the net's own computed checks; rewritten above. F3 (Minor, fixed): the probe naming (the killed example is the point-0 `some 0` one, not the `retire-net-*` rows) is corrected above.

## Nodup conjecture (spec 31.1 / path doc "does not do" item) closed

Direct path, branch `worktree-nodup-prop`. Re-checked before working: the conjecture was already PROVED at the checker level (`checkPlan_nodup_redundant`, the parked-items pass of slice 1, 2026-10-10), so the spec and path doc were stale about it; what was missing was the plain statement the doc asks about. Added, as a pure 40-line append to `Plan/Validity.lean` (no existing line moved, so no manifest `expect` location can shift): `accFlat_nodup_of_accOK` (singleton plan, `AccOK` at every `acc` command), `pubFlat_nodup_of_pubOK` (`PubOK` at every `pub` command) and `Valid.coverage_nodup_of_steps`; axioms `propext`, `Quot.sound` only. They reuse the generic `nodup_prefixAnn_flatMap` (no second induction).

Tests (`PlanValidityTest.lean`, 11 theorems): the valid neighbours `accSplit`/`pubSplit` get both Nodup halves from `Valid.coverage_nodup_of_steps`; the invalid plans `dupWithin` (repeat inside one group), `dupGroup` (repeat across two groups, the `¬ Cons` half of `AccOK`) and `pubTwice` (repeat in the publication image) have non-duplicate-free images (`checkCov1Nodup`/`checkCov2Nodup` false) and the theorem then refutes the per-step hypothesis (`dupWithin_accOK_fails`, `dupGroup_accOK_fails`, `pubTwice_pubOK_fails`), so the hypotheses are neither vacuous nor always true. Docs: spec 31.1 (the two Nodup rows now say derivable; the "conjecture, not proved" sentence now states the result), path doc (theorem row added, the "does not do" bullet and the not-yet-done mention removed, counts 279 = 149 rows + 130 items, snapshot SHA), `Plan/AGENTS.md` Validity row. Not changed: the Nodup rows stay "diagnostic" (derivable, consumed by no theorem) and `Valid` keeps the two Nodup fields (removing them would be a separate refactor, not requested).
