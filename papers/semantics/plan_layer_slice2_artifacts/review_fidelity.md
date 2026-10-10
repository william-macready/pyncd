# Slice 2 plan: spec-Lean fidelity and executability review

Reviewer budget note: 40 harness tool uses were used (the cap); findings were written in ONE write at the end, not incrementally,
because the budget left no room for per-finding appends. Read-only on the repo except this file. Nothing committed.

## Checks that PASSED (evidence)

- Fixture totals: `rg -c "^#eval check|^(example|theorem) "` over `Plan*Test.lean` at HEAD sums to 171 (Fusion 18, Batch 10, Memory 10,
  Validity 53, Checker 8, FusionCorrectness 16, Simulation 17, Run 4, Step 21, Correctness 14). `git grep -c` at 4570a794 sums to 129
  (the seven slice-1 files). Delta 42 = 18 + 16 + 8 as the record states.
- Mutation manifest: `mutation-manifest.sh --check` prints "manifest OK: 14 entries, 14 selected"; task tags are T2 x4, T3 x7, T4 x3.
  `--check --task T1` exits 125 "no manifest entries selected: unknown task 'T1'; available tasks: 'T2', 'T3', 'T4'"; plan 3.1 step 4
  states that T1 has none and that `--task T1` is an empty-selection error, so a controller is warned.
- Patch line counts 241 / 363 / 455 / 132 equal `wc -l`. Patch paths are `a/leanncd/...`, so `git -C <exec> apply` is the right cwd.
- Signatures: every identifier of the plan's verbatim block and of 4(a) exists under `leanncd/LeanNCD/Semantics/Plan/` (rg of
  `def|theorem|abbrev`); `Plan.lean` lines 9-10 import `Plan.Fusion` and `Plan.FusionCorrectness`; lakefile line 88-89 registers the three
  new test modules.
- Spec anchors: 9 "As formalized (slice-1 profile" hits (29.3, 30.2, 30.4, 31.1, 31.2, 31.3 x2, 31.4 two-line variant, 32.1) as the plan says;
  quotes "Expand fused annotations in their stated order" (29.3, spec line 3926) and "same intermediate logical barriers" (31.2) are accurate.
- D13-D16 against the spec: D13 (31.2 barriers sentence, 30.4, "states exist only in its proof" at spec line 3879), D14 (30.1 `PlanFailed(o)`
  carries no memory; 31.3 `Failed(o, sigma', alpha', U')`), D15 ("before" in 29.3 conditions 3-4, header sentence), D16 are accurately described.
- No `File.lean:NNN` in plan or record (rg: 0 hits). Plan/AGENTS.md is 3978 bytes, Semantics/AGENTS.md 12060, as the plan states for the former.
- Rules 13/14: plan never pushes, merges locally, scope is fusion only, parked items listed with owners. No widening found.

## F-1 (Important) 3.1 step 8: `branch -D` before `worktree remove` fails

Claim: the shell block runs `git tag ...`, then `git branch -D worktree-plan-layer-slice2`, then `git worktree remove .../plan-layer-slice2`.
Evidence: plan lines 342-344. Git refuses to delete a branch that is checked out in any worktree ("Cannot delete branch ... checked out at").
The prototype worktree on that branch is exactly the one removed on the next line. Why it matters: the controller hits an error at close-out
and may improvise (`-D` with force flags, `worktree remove --force`) on a branch holding the only copy of the prototype history.
Fix: order `tag`, `worktree remove <prototype worktree>`, then `branch -D`. Same order for the exec branch ("also delete the exec branch
and remove its worktree": say worktree first).

## F-2 (Important) 4(a) 31.3 (failure) row cites `failed_correct_F` for "fails with the same occurrence"

Claim in the row: "the reference runs the earlier annotations and then fails with the same occurrence (`step_failed_command`, `failed_correct_F`)".
Evidence: `failed_correct_F` (FusionCorrectness) concludes only `¬ ∃ ρ, P.Models ops η ρ`; its own docstring says "neither the failing occurrence nor
the pre-command memory is compared". Only `step_failed_command` has `Execution ... (.failed o.1 o.2 c')` with the same `o`. The plan's 31.4
row says "part (b) compares failure and absence of a model only", so the two rows contradict each other.
Fix: cite `step_failed_command` alone for the same occurrence; keep `failed_correct_F` in the 31.4 row. Also add that, unlike slice-1
`step_failed` ("no preceding contributions, matched snapshot is that related Conf", the paragraph the sentence is appended to), the fused matched
snapshot is the state AFTER the earlier annotations of the command.

## F-3 (Important) Lemma 32.1 proof-status row left "unchanged" contradicts the new 32.1 sentence

Evidence: spec line 204 reads "failure half for the transactional singleton kernel only (`step_failed`, `Plan.Simulation`)". Plan 4(a) 32.1 row
appends "The failure half holds for the transactional fused kernel" and the proof-status text says "`Lemma 32.1` row unchanged".
`step_failed` is still singleton-only (F10: `hcmd : ... = some [a]`); the fused statement is `step_failed_command` (Plan.Fusion).
Why: after T5 the spec says "singleton only" in the table and "fused kernel holds" in section 32.1.
Fix: either append "; fused: `step_failed_command` (`Plan.Fusion`)" to the row 204 or soften the 32.1 sentence to name `step_failed_command`.

## F-4 (Minor) 4(a) 31.2 row omits the hypotheses of the proved statements

`step_R_command` needs `hc : refState pc = some c`, `hcmd`, and `ok : ∀ j a, cmd[j]? = some a → π.expand.AnnOK (π.offset pc + j) a`;
`stepCommand_not_stuck` needs `hv : π.expand.Valid`. The draft sentence says only "from `R ∧ Conf = refState pc`, `stepCommand = ok` gives R ..." and
"progress is `stepCommand_not_stuck`" with no validity/AnnOK premise. The slice-1 paragraph it extends (`step_R` "assumes ... `AnnOK pc a`") does
state its premise, so the appended sentence should too ("for AnnOK at each expanded position; progress under `FValid`"). The spec's own
31.2 sentence "must justify the same intermediate logical barriers" is not tied to anything in the 31.2 row (it is discharged by `FValid`, 31.1 row);
one clause pointing to D13 would close it.

## F-5 (Minor) Wrong open-item id in 4(d)

Plan line 456 says the stale `Step.lean` header comment is "(O8: stale after T1, parked)". Section 5 has it as O6 (line 486); O8 is the unrun
slice-1 manifest (line 488). The record (line 137) uses O6 correctly.

## F-6 (Minor) Per-task `--out` result files are never committed or gated

3.1 step 4 writes `plan_layer_slice2_mutation_results_T<k>.md` and the final `plan_layer_slice2_mutation_results.md` into `<exec>/papers/semantics/`.
Nothing says to stage them (or delete the per-task ones), while each task commit is "only the task's files" with a `diff --cached --stat` gate
and the record's close-out expects the results. Add: stage the final results file with the docs-sweep commit; per-task files are scratch.
Also 3.1 step 3 says the sha256 "must equal manifest.json `sha256`" without a command to read it (I did not open manifest.json; unchecked).

## F-7 (Minor) `--plan` in 3.1 step 2 is redundant

`prepare-worktree.sh` documents `--plan` as copying a gitignored plan ("Defaults: --base main, no plan copy"). The slice-2 plan and record are
committed to main by step 1, so the copy is not needed; harmless if the script tolerates an already-present file (not tested: the script was not run).

## F-8 (Minor) Record checklist lacks two SKILL.md items

The last two items of the `slice-plan` checklist ("Authoring ran as two dispatches ... patches `git apply` cleanly in order onto the base";
"Reviewer and fixer briefs give window sizes ...") have no row in the record's 22-row table (record lines 68-91). The first is supported by
evidence.json `replay` (per the record); add the rows. The ticks that exist are supported by what I could check: the "NOT SATISFIED" and "PARTIAL"
rows are honest, "plan is 490 lines" is true, "Pitfalls 997 bytes / whole file 3978" matches `wc -c` for the whole file (the 997 section split not
re-measured).

## Could not check (budget)

- Plan section 3 per-task text (lines 163-272), risk table, plan 4(b) path-doc edits, plan section 5 beyond O6/O8.
- `manifest.json` sha256 fields and `evidence.json` job counts (2977 / 2973 / 8606 / 2980) against the plan/record.
- Fixture names of table 2 (a1-e) against `Plan*Test.lean` by individual `rg` (only the counts and totals were verified).
- Whether `prepare-worktree.sh` tolerates `--plan` for a tracked file; `lakefile.toml` glob at line 88-89 vs "one line per task".
- Replay of `git apply` onto 4570a794 (not run; evidence.json claims PASS).
