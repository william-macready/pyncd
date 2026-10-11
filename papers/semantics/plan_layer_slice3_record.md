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

## Review round 1 (controller fills)

- Soundness lens: findings and adjudication:
- Fidelity lens: findings and adjudication:

## Value-grep dispositions (controller fills the per-file column after T5)

| pattern | file | disposition (EDIT / keep: reason) |
|---|---|---|
| | | |

Measured fixture total after T4: ___ (expected 228 = 139 + 89); `PlanRetireTest`: ___ rows + ___ items (expected 17 + 11).
Path doc TOC counts before / after (`^#{2,4} ` and `^ *- \[`): ___ / ___ -> ___ / ___.
`Plan/AGENTS.md` Pitfalls bytes before / after: 1483 / ___ ; whole file 6151 / ___.

## Close-out (controller fills)

- Execution worktree / branch: ___
- Base `main` SHA at execution (docs-only landing commit): ___
- Per-task commits and builds (sha256 matched, `apply --check` clean): T1 ___ (2963 expected), T2 ___ (2966), T3 ___ (2968; `LeanNCD` 8598), T4 ___ (2982; default 8793).
- T4b: slice-1 manifest as shipped ___ / 20, after repair ___ / 20 (`expect` and `old` repairs listed: ___); slice-2 ___ / 15 -> ___ / 15; D7 ___ / 9. Commit ___.
- New manifest: `--check` ___; full run ___ / 10; files restored byte-identical: ___.
- Docs-sweep commit: ___; whole-branch review fix commits: ___.
- Full default build: ___ jobs; forbidden-token grep: ___.
- Execution session total tokens (`token-report.py <session-id>`; Rule 6 <= ~175M): ___. Authoring tokens (target <= ~50M): ___. Any overrun explained: ___.
- Whole-branch reviews: soundness ___ Critical / ___ Important / ___ Minor; fidelity ___ / ___ / ___. Adjudication: ___.
- Merge SHA on local `main`: ___; prototype tagged `plan-layer-slice3-proto` before deletion: ___; branches and worktrees removed: ___; not pushed (`main` ahead of `origin/main`): ___.
- Parked (plan open items): O1 later slices, O2 lakefile space, O3 row probes, O4 `dead`/`retPub` no fixture, O5 `--task` validation gap, O6 fixture-count reconciliation, O7 stale "slice-1 profile" comments.
