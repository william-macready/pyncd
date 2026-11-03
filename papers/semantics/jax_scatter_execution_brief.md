# Brief: execute the JAX scatter slice

You are the EXECUTOR of an already-verified, patch-driven plan. You do not design, retype code, or improve
the patches. Everything you need is committed on local `main` of the repo at
`/Users/williammacready/code/python/pyncd` (HEAD `7cd0540e` or a descendant that only adds papers). Read the
repo `CLAUDE.md` first (its Rules 12-14 govern you), then the plan, then start.

## Read, in this order
1. `papers/semantics/jax_scatter_plan.md` (about 530 lines). It is binding. Act on section 1 (execution
   contract), 3 (fixed semantics), 4 (deliberately NOT done), 5 (tasks T1-T7 with per-task hash tables),
   6 (final hash table), 7 (placeholders, pre-flight A and B, ordering, commands) and 10 (close-out and stop
   point). Section 8 is the audit table the fixtures pin; section 9 is the documentation sweep.
2. `papers/semantics/jax_scatter_files/FINDINGS.md` (what the prototype observed; the numbers you should see).
3. Only if something is unclear: `papers/semantics/jax_scatter_plan_record.md` (authoring and review record).

## What you are doing
Apply seven patches from `papers/semantics/jax_scatter_patches/` (`T1`..`T7`, in that order) in a new
worktree, verify each against the plan's blob-hash tables and builds, run both mutation manifests and the
verifiers, write the record, and STOP for review. The slice lets JAX render and run scatter steps (and B5
multi-writer groups) in `affineReference`: an ordered fold that is bit-identical to the Lean dense worker (the
default) and an opt-in `scatter_mode="fast"` fold (`.at[].add`, tolerance-compared). It changes only
`leanncd/experiments/jax_bridge/`, one additive function in `LeanNCD/Eval/Plan/Executable.lean`, one
`ExecutableTest.lean` guard pair, and two Markdown nodes.

## Hard rules (a violation is a failure even if everything is green)
- **Patches are the code.** In the worktree root run `git apply --check <absolute patch path>`, then apply,
  then commit with the exact subject in plan section 5, staging by explicit path. One commit per patch (seven).
  Never retype code, never hand-edit a patch, never use `--3way` or `--reject`, never edit a manifest, a
  tolerance, a count or an `expect` string, never loosen or delete a fixture to get green. A failing fixture
  or surviving mutant is a finding to report.
- **BLOCKED rule.** If pre-flight fails, a patch does not apply, a blob hash differs after the owning task, a
  build is red, a manifest verdict is FAIL, or a mutant survives or is not restored: STOP, leave the tree as
  is, and report the exact command and output. Do not repair around it.
- **Do NOT merge, do NOT push.** Unlike earlier slices, this plan ends at "READY FOR WHOLE-BRANCH REVIEW":
  commit the record on your branch, leave the worktree and branch in place, and report the branch tip. The
  owner's controller session reviews and merges. `main` stays ahead of `origin/main`.
- **Do not touch** the worktree `/Users/williammacready/code/python/pyncd/.claude/worktrees/jax-scatter-plan`
  or its branch `worktree-jax-scatter-plan` (the authoring prototype: it already contains the code the patches
  add; never merge it, never delete it, never copy from it).
- **Out of scope (plan section 4).** `route`, diagram rendering, `Bridge/`, the Python diagram stack and
  `tsncd` are NOT part of this slice and have no owner. Do not edit the stale `papers/` sentences listed in
  plan section 9; run the value-grep it describes and report hits in the record. Side issues you find: write
  them in the record as parked with a one-line cost, do not start them (Rule 14).
- **Report faithfully (Rule 12).** Anything skipped, red, retried or not observed is stated as such. State
  "not measured" rather than guessing tokens or timings.

## Shell and build rules
Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command, no pipelines into git. Use
absolute paths and `/usr/bin/git -C <worktree>` (plain `git` may be refused by a guard in some harnesses).
Build Lean ONLY with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [targets]`; never run
`lake` from the worktree root. `lake` is not on `PATH`. Python and JAX come from
`bash <worktree>/leanncd/experiments/jax_bridge/setup-python.sh` (needs network for `pip`; offline failure is
BLOCKED). Run long builds and the corpus in the background and wait for completion instead of polling. Never
run two of {a Lake build, a mutation manifest, a verifier, the corpus} at the same time: both mutation
runners edit tracked files in place. Read file windows of 40-60 lines and use `rg -n`; never read a whole
file over about 20k characters. Never commit `.claude/settings.json`.

## Sequence (plan sections 1, 5 and 7 have the exact commands; this is the order)
1. Pre-flight A (plan section 7): `main` is `2cf92209` or a descendant that only adds `papers/semantics/`
   files, and the package commit (`docs: JAX scatter slice package`) is on `main`.
2. Worktree: `/usr/bin/git -C /Users/williammacready/code/python/pyncd worktree add
   /Users/williammacready/code/python/pyncd/.claude/worktrees/jax-scatter-exec -b jax-scatter-exec main`, then
   `bash <worktree>/.claude/skills/new-slice/prepare-worktree.sh` from inside it. It must report Mathlib at or
   above 95% built; if any build starts compiling Mathlib, STOP (hours). Then pre-flight B, then build
   `LeanNCD` once to refresh project oleans, then `setup-python.sh` once.
3. T1 to T7 in order: `git apply --check`, apply, commit, check that task's blob rows, run that task's verify
   step. T1 build: `LeanNCD Eval.Plan.ExecutableTest JaxExperiment`. Do NOT run the Lean mutation manifest
   before T3 (its `expect` line numbers are valid only from T3). Do NOT run the Python mutation runner before
   T6. T7 is Markdown only.
4. After T7, the final verification in the plan's section 7 order, strictly serial: full build (expect
   `Build completed successfully (8844 jobs)`), `check-lean-drivers.sh`, `run-evalplan-scatter.sh` (10 f64 + 5
   f32 bit-identical, plus the fast-mode lines), Python mutation manifest (16 `PASS`), Lean mutation manifest
   (`--check` then the real run, 6/6; do not pass `--out`), the three older verifiers
   (`run-evalplan-affine.sh`, `run-evalplan-affine32.sh`, then `run-evalplan-affine-corpus.sh`, 3,832 cases,
   10+ minutes, background, nothing else running; the prototype did NOT run the corpus after T6, so this is
   the first measurement), a final full build, `git status` empty, the plan section 6 hash table once more.
5. Value-grep and close-out: plan section 9 (value-grep, report only) and section 10 (the record's twelve
   fields). Write `papers/semantics/jax_scatter_record.md` from real runs, commit it
   (`docs: JAX scatter slice record`), and STOP at "READY FOR WHOLE-BRANCH REVIEW".

## Budgets
At most three substantive work items per dispatch, 60 turns and 250k peak context per dispatch. Plan section 1
suggests two dispatches: (1) pre-flight, worktree, T1-T3 and the Lean mutation manifest; (2) T4-T7, every
verifier, the record. If you will breach a budget, stop at a clean commit and say so. Measure total tokens from
your own usage telemetry (`session.usage_record`, deduplicated) and name the method; the Rule 6
slice-execution ceiling is about 175M. `token-report.py` is Claude-only and does not apply.

## Final message to the owner
Base commit (`main` hash you started from) and the branch tip; the seven commit hashes and subjects; per-task
`git apply --check` results; the hash-table result per task and at the end (11 files); per-task build results
and the final job count; the scatter differential lines (fixture counts and every fast-mode line, quoted); the
Lean (6) and Python (16) mutation tables with the `--check` line; the last line of each of the three older
verifiers plus the corpus case count and duration; the `check-lean-drivers.sh` last line; the value-grep count
and its stale-live list; parked items with cost; measured tokens and method; every skipped step or STOP; and
the confirmation that nothing was pushed or merged and the branch `jax-scatter-exec` is waiting for review.
