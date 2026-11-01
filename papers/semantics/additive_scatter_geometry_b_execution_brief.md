# Brief: execute scatter geometry slice B

You are the EXECUTOR of an already-verified, patch-driven plan. You do not design, retype code, or improve
the patches. Everything you need is committed on local `main` of the repo at
`/Users/williammacready/code/python/pyncd` (HEAD `7f632e50` or a descendant that only adds papers). Read
the repo `CLAUDE.md` first (its Rules 12-14 govern you), then the plan, then start.

## Read, in this order
1. `papers/semantics/additive_scatter_geometry_b_plan.md` (517 lines). It is binding. Sections 1 (execution
   contract), 2 (decisions and exclusions), 4 (tasks T1-T6), 7 (hash table, builds, manifest) are what you act
   on. Section 5 is the audit the review lenses re-check. Section 8 is your close-out checklist.
2. `papers/semantics/additive_scatter_geometry_b_design.md` (the approved design; the plan restates it).
3. Only if something is unclear: `additive_scatter_geometry_b_plan_record.md` (why things are the way they
   are, the review adjudication) and `additive_scatter_geometry_b_files/proto_notes.md` (prototype ledger).

## What you are doing
Apply six patches in `papers/semantics/additive_scatter_geometry_b_patches/` (`T1-engine`,
`T2-engine-fixtures`, `T3-surface`, `T4-surface-fixtures`, `T5-docs`, `T6-review-fixes`, in that order) in a
new worktree, verify each against the plan's blob-hash table and builds, run the mutation manifest, run two
review lenses, adjudicate, and merge to LOCAL `main`. Slice B lets constant and multi-axis scatter slots
join multi-writer groups and boxed single writers, deletes the `#const` name marker, and adds the surface
syntax `S[a + b]` and `S[=3]`.

## Hard rules (a violation is a failure even if the build is green)
- **Patches are the code.** Run `git apply --check <absolute patch path>` in the worktree root, then apply,
  one commit per patch (six commits), staging by explicit path. Never retype Lean from the plan, never
  hand-edit a patch, never loosen or delete a fixture to get green. A failing fixture is a finding.
- **BLOCKED rule.** If a patch does not apply, a blob hash in plan section 7 differs after the owning task,
  a build is red, or a manifest verdict is FAIL: STOP, leave the tree as is, and report the exact command and
  output. Do not repair around it. Also stop for a review finding that is real, load-bearing and unfixable
  within the plan.
- **Do not push.** Merge to local `main` is authorized (CLAUDE.md Rule 13); pushing is not. Leave `main` ahead
  of `origin/main` and say so.
- **Do not touch** the existing worktree `/Users/williammacready/code/python/pyncd/.claude/worktrees/proto-scatter-geometry-b`
  or its branch `worktree-proto-scatter-geometry-b` (the authoring prototype; keep it as is, do not delete it).
- **Scope (Rule 14).** Side issues you find are not part of the task: write them in the record as parked with a
  one-line cost. Do not start them.
- **Report faithfully (Rule 12).** Anything skipped, red, retried or not observed is stated as such. Do not
  write "tests pass" for a run you did not do. Do not claim more than the manifest shows (plan section 7(a):
  only `SGB-T1-07` is killed by the new T2 fixtures; the other engine mutants are killed by older upstream
  guards).

## Shell and build rules
Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command, no pipelines into git. Use
absolute paths and `/usr/bin/git -C <worktree>`. Build ONLY with
`bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD Tests JaxExperiment` (or a module
list a task names); never run `lake` from a worktree root (it clobbers `.lake`). `lake` is not on `PATH`.
Run long builds in the background and wait for completion instead of polling. Read file windows of 40-60
lines and use `rg -n`; never read a whole file over about 20k characters. Never commit
`.claude/settings.json`.

## Sequence (plan section 1 has the exact commands; this is the order)
1. Worktree: `git worktree add /Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec -b scatter-geometry-b-exec main`
   from the primary checkout, then `bash .claude/skills/new-slice/prepare-worktree.sh` from inside it. It must
   report Mathlib at 100%. If any build starts compiling Mathlib, STOP (a cold build takes hours). Then build
   `LeanNCD` once to refresh project oleans.
2. For T1..T6 in order: `git apply --check`, apply, commit, check the plan's hash rows for that task, build.
   Expected full-build job counts: 8843 after T1 and T2; 8844 after T4, T5 and T6 (the `+1` is the new
   `ScatterSurfaceTest`). T1 ends with the full build (an `Ast.lean` edit recompiles about 8800 jobs); a red
   module hides its dependents, so read the FIRST error, not the last.
3. Manifest, only after all six patches: `bash leanncd/scripts/mutation-manifest.sh --check
   <worktree>/leanncd <worktree>/papers/semantics/additive_scatter_geometry_b_mutations_post.json` unfiltered
   (expect `manifest OK: 18 entries`), then the REAL run, not only `--check`, one task at a time, each in the
   background with `--out <scratch file>`: `--task T1` (9 entries), `--task T3` (8), `--task T6` (1). This takes
   hours; each entry rebuilds. `git status` must be clean after each run. Every verdict must be PASS.
4. Two review lenses over `git diff <base>..<branch head>` plus plan sections 3 and 5, in SEPARATE contexts
   (use sub-agents if your harness has them, otherwise two fresh passes), each appending findings to its own
   file as it goes, not at the end: lens 1 `additive_scatter_geometry_b_review_siblings.md`, lens 2
   `additive_scatter_geometry_b_review_surface.md` are taken by the authoring-time review, so name yours
   `additive_scatter_geometry_b_exec_review_siblings.md` and `additive_scatter_geometry_b_exec_review_surface.md`.
   Lens briefs are in plan section 6. Window reads only. Give every finding a verdict (fix now, park with
   cost, reject with reason). A finding that needs a design decision (not a fix inside the plan) goes to the
   owner: stop and report it, do not decide.
5. Close-out: write `papers/semantics/additive_scatter_geometry_b_record.md` with every field listed in plan
   section 8, from real runs. Add the completion note to the design note and the Slice B row to the master
   plan documents as section 8 says. Then merge: from the primary checkout
   `/usr/bin/git -C /Users/williammacready/code/python/pyncd merge --no-ff scatter-geometry-b-exec`, confirm
   `git diff --stat main scatter-geometry-b-exec` is empty, remove the worktree, delete the branch. Do not push.

## Budgets
At most three substantive work items per dispatch, 60 turns and 250k peak context per dispatch; if you will
breach, stop at a clean commit and say so. Measure total tokens from your own usage telemetry
(`session.usage_record`, deduplicated) and name the method; the Rule 6 slice-execution ceiling is about 175M.
`token-report.py` is Claude-only and does not apply.

## Final message to the owner
Base and final commit hashes and the six commit hashes; per-task `git apply --check` results; the hash-table
result; per-task build results and final job count; manifest results (killed/total per task, and which kills
are by new fixtures vs upstream guards); review findings and adjudication; parked items with cost; measured
tokens and method; every skipped step; the confirmation that nothing was pushed and how far `main` is ahead
of `origin/main`.
