# Brief: execute the JAX pointwise/axiswise slice

You are the EXECUTOR of an already-verified, patch-driven plan. You do not design, retype code, or improve
the patches. Everything you need is committed on local `main` of the repo at
`/Users/williammacready/code/python/pyncd` (base `f2616f54`, or a descendant that only adds new files under
`papers/semantics/`). Read the repo `CLAUDE.md` first (its Rules 6, 12, 13 and 14 govern you), then the plan,
then start.

## Read, in this order
1. `papers/semantics/jax_nonlin_plan.md` (about 640 lines). It is binding. Act on section 1 (execution
   contract), 2 (exact values), 3 (fixed semantics), 4 (deliberately NOT done), 5 (tasks T1-T6: the literal
   five-step procedure and the per-task hash tables), 6 (final hash table), 7 (placeholders, pre-flight A and
   B, commands, final order) and 10 (close-out and stop point). Section 8 is the audit table the fixtures pin;
   section 9 is the documentation value-grep (report only).
2. `papers/semantics/jax_nonlin_files/FINDINGS.md` (what the prototype observed; the numbers you should see).
3. Only if something is unclear: `papers/semantics/jax_nonlin_plan_record.md` (authoring and review record).
   The donor slice, already executed once the same way, is `papers/semantics/jax_scatter_record.md`.

## What you are doing
Apply six patches from `papers/semantics/jax_nonlin_patches/` (`T1`..`T6`, in that order) in a new worktree,
verify each against the plan's blob-hash tables and builds, run both mutation manifests (the Lean one once,
right after T1's build; the Python one after T5) and every verifier, write the record, and STOP for review.
The slice lets JAX `affineReference` render and run `.pointwise` (relu, sigmoid, tanh, gelu, leakyrelu) and
`.axiswise` (softmax, normalize, l2normalize, masked or not) steps in both precisions, compared to the Lean
dense workers WITHIN A MEASURED TOLERANCE (not bit for bit), so the repo's single-layer transformer runs
through Lean and JAX. It changes only `leanncd/experiments/jax_bridge/`, one additive public function in
`LeanNCD/Eval/Plan/Nonlin.lean`, one Plan `AGENTS.md` bullet, and two `papers/` sentences. `Executable.lean`
is NOT touched.

## Hard rules (a violation is a failure even if everything is green)
- **Patches are the code.** For each task run, as separate plain commands: `git apply --check <patch>`,
  `git apply <patch>`, `git hash-object` for each path in the task table, `git add <explicit paths>`,
  `git commit -m "<exact subject in plan section 5>" -m "Applies <patch name>"` (plus the attribution trailer
  your environment requires). One commit per patch (six). Never retype code, never hand-edit a patch, never
  use `--3way` or `--reject`, never edit a manifest, a tolerance, a count or an `expect` string, never loosen
  or delete a fixture to get green. A failing fixture or a surviving mutant is a finding to report.
- **BLOCKED rule.** If pre-flight fails, a patch does not apply, a blob hash differs after the owning task, a
  build is red, a manifest verdict is FAIL, or a mutant survives or is not restored: STOP, leave the tree as
  is, and report the exact command and output. Do not repair around it.
- **Do NOT merge, do NOT push.** The plan ends at "READY FOR WHOLE-BRANCH REVIEW": commit the record on your
  branch (`docs: JAX pointwise slice record`), leave the worktree and branch `jax-pointwise-exec` in place,
  and report the branch tip. The owner's controller session reviews and merges. `main` stays ahead of
  `origin/main`.
- **Do not touch** the worktree `/Users/williammacready/code/python/pyncd/.claude/worktrees/jax-pointwise-plan`
  or its branch `worktree-jax-pointwise-plan` (the authoring prototype: it already contains the code the
  patches add; never merge it, never delete it, never copy from it). If `jax-pointwise-exec` or its directory
  already exists, STOP and report; do not delete or reuse it.
- **Out of scope (plan section 4).** Unary reads on JAX (a LayerNorm with eps), scan, the evidence path,
  tropical/Boolean steps, `route`, diagram rendering, `Bridge/`, GPU runs have no owner here. Do not edit the
  stale `papers/` sentences section 9 lists (the controller fixes them after landing); run the value-grep it
  describes and report hits in the record. Side issues you find: write them in the record as parked with a
  one-line cost, do not start them (Rule 14).
- **Report faithfully (Rule 12).** Anything skipped, red, retried or not observed is stated as such. State
  "not measured" rather than guessing tokens or timings. Several figures in the plan are marked "reported" or
  "first observation" (for example the `check-lean-drivers.sh` line `all six drivers ran clean`, and the
  corpus after this slice): quote what YOU observe, and say when it differs.

## Shell and build rules
Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command, no heredocs, no pipelines into
git. Use absolute paths and `/usr/bin/git -C <worktree>` (plain `git` may be refused by a guard in some
harnesses). `prepare-worktree.sh` must run with the shell's working directory set to the worktree (plan
section 1 gives the exact way). Build Lean ONLY with
`bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [targets]`; never run `lake` from the
worktree root. `lake` is not on `PATH`. Python and JAX come from
`bash <worktree>/leanncd/experiments/jax_bridge/setup-python.sh` (needs network for `pip`; offline failure is
BLOCKED). The FIRST Lean build after T1 recompiles thousands of jobs (it edits a core file): run it in the
background and wait for the notice. Run long builds, the manifests and the corpus in the background and
wait for completion instead of polling. Never run two of {a Lake build, a mutation manifest, a verifier,
`check-lean-drivers.sh`, the corpus} at the same time: both mutation runners edit tracked files in place.
Read file windows of 40-60 lines and use `rg -n`; never read a whole file over about 20k characters. Never
commit `.claude/settings.json`.

## Sequence (plan sections 1, 5 and 7 have the exact commands; this is the order)
1. Pre-flight A (plan section 7): `merge-base --is-ancestor f2616f54 main` exits 0, read the name-status diff
   `f2616f54..main` (only added files under `papers/semantics/`, none of the 12 section-6 files), and the
   package commit is on `main`.
2. Worktree: `/usr/bin/git -C /Users/williammacready/code/python/pyncd worktree add
   /Users/williammacready/code/python/pyncd/.claude/worktrees/jax-pointwise-exec -b jax-pointwise-exec main`,
   then `prepare-worktree.sh` with that worktree as the working directory. It must report Mathlib at or above
   95% built and a base equal to `main`; if any build starts compiling Mathlib, STOP (hours). Then pre-flight
   B, build `LeanNCD` once, run `setup-python.sh` once.
3. T1 to T6 in order, each with the five-step procedure and its verify step. After T1's build run the Lean
   mutation manifest (`--check`, then the real run, no `--out`; expect `8/8 cycles passed.`) once; it is not
   repeated later. Do NOT run the Python manifest before T5. T6 is documentation and one script text change:
   check it with `git diff --check`, `bash -n` and the greps in its section.
4. After T6, the final verification in plan section 7's order, strictly serial: full build (expect
   `Build completed successfully (8844 jobs).`), `check-lean-drivers.sh`, `run-evalplan-nonlin.sh` (15 + 15
   fixtures plus the pin lines), the Python nonlin manifest (17 `PASS`), `run-evalplan-scatter.sh`, the
   scatter Python manifest (16 `PASS`), `run-evalplan-affine.sh`, `run-evalplan-affine32.sh`, then
   `run-evalplan-affine-corpus.sh` (3,832 cases, about 11 minutes, background, nothing else running; the
   prototype did NOT run the corpus after this slice, so this is the first measurement), a final full build,
   `git status` empty, the plan section 6 hash table once more (12 files).
5. Value-grep and close-out: plan section 9 (value-grep plus the multi-line pattern, report only) and
   section 10 (the record's fields). Write `papers/semantics/jax_nonlin_record.md` from real runs, commit it,
   and STOP at "READY FOR WHOLE-BRANCH REVIEW".

## Budgets
At most three substantive work items per dispatch, 60 turns and 250k peak context per dispatch; stop at a
task or step boundary near 55 turns. Plan section 1 suggests two dispatches: (1) pre-flight, worktree, T1
with the Lean manifest, T2, T3; (2) T4, T5, T6, every final-order step, the value-grep, the record. Measure
total tokens from your own usage telemetry (`session.usage_record`, deduplicated) and name the method; the
Rule 6 slice-execution ceiling is about 175M. `token-report.py` is Claude-only and does not apply.

## Final message to the owner
Base commit (the `main` hash you started from) and the branch tip; the six commit hashes and subjects;
per-task `git apply --check` results; the hash-table result per task and at the end (12 files); per-task
build results and the final job count; the nonlinearity differential lines (15 + 15 fixtures, every pin line
quoted for both precisions); the Lean (8) and Python (17) mutation tables with the `--check` line, and the
scatter manifest's 16; the last line of each of the three older verifiers plus the corpus case count and
duration; the `check-lean-drivers.sh` last line; the value-grep count and its stale-live list; parked items
with cost; measured tokens and method; every skipped step or STOP; and the confirmation that nothing was
pushed or merged and the branch `jax-pointwise-exec` is waiting for review.
