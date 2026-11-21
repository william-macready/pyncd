# Brief: execute the JAX Boolean-reachability slice

You are the EXECUTOR of an already-verified, patch-driven plan. You do not design, retype code, or improve
the patches. Everything you need is committed on local `main` of the repo at
`/Users/williammacready/code/python/pyncd` (source baseline `b305b363`, or a descendant that only adds new
files under `papers/semantics/`). Read the repo `CLAUDE.md` first (its Rules 6, 12 and 14 govern you; Rule 13's
standing permission to merge is the OWNER's, not yours: see "Do NOT merge" below), then the plan, then start.

## Read, in this order
1. `papers/semantics/jax_boolean_reach_plan.md` (about 860 lines). It is binding. Act on section 1 (scope),
   2 (decisions D1-D7), 3 (exact values), 4 (the case x class audit the fixtures pin), 5 (execution protocol:
   setup, the per-task loop, stop conditions), 6-10 (tasks T1-T5, one patch each) and 11 (final
   verification). Section 12 lists risks and parked items: they are NOT yours to fix.
2. `papers/semantics/jax_boolean_reach_files/authoring_evidence.md` (what the prototype observed: the numbers
   you should see, and which ones were never observed).
3. Only if something is unclear: `papers/semantics/jax_boolean_reach_plan_record.md` (authoring and review
   record) and `papers/semantics/jax_boolean_reach_files/preflight/REPORT.md`.
If this brief and the plan disagree, the plan wins EXCEPT for the "Do NOT merge, do NOT push" rule below.

## What you are doing
Apply five patches from `papers/semantics/jax_boolean_reach_patches/` (`01`..`05`, in that order) in a new
worktree, verify each against `verify_package.py` and the plan's per-task checks, run the mutation manifests
and every verifier in plan section 11, write the execution record, and STOP for review. The slice lets JAX
`affineReference` render and run Boolean reachability over the REAL carrier (no native Boolean arrays): a new
render profile `JaxRenderProfile.booleanReach` (a superset of `.maxPlus`), Boolean-algebra nodes (min factor
fold seeded 1, max reduction fold seeded 0, Lean's tie rules), Iverson factors lowered ONLY in Boolean-algebra
nodes through static `include` tables that Lean decides, and the six reachability fixtures run through
named/positional x eager/JIT x float64/float32 against an independent BFS oracle. Patches 01-04 are code and
tests (the new manifests ship inside them); patch 05 is documentation plus comment-only fixes and two
manifest `expect` refreshes. `evalplan_affine_runtime.py` and `EvalPlanCodegen.lean` are NOT touched by T4.

## Hard rules (a violation is a failure even if everything is green)
- **Patches are the code.** For each task run, as separate plain commands, exactly the six steps of plan
  section 5 "Per task N": `verify_package.py --task <N-1>`, `git apply --check <patch>`, `git apply <patch>`,
  `verify_package.py --task <N>`, the task's verification commands from sections 6-10, then stage exactly that
  task's `touched_files` and commit once with the subject below (plus any attribution trailer your environment
  requires). Never retype code, never hand-edit a patch, a manifest, a count, a fixture or an `expect`
  string, never use `git apply --3way` or `--reject`, never loosen or delete a fixture to get green. A failing
  fixture or a surviving mutant is a finding to report.
- **Commit subjects (one commit per patch, five, plus the record):**
  | Task | Subject |
  |---|---|
  | T1 | `feat(jax): admit the .booleanReach render profile in the JAX gate` |
  | T2 | `feat(jax): emit Boolean nodes and Lean-decided Iverson include tables` |
  | T3 | `feat(jax): execute ordered_boolean_v1 nodes and pin raw Boolean fixtures` |
  | T4 | `test(jax): run the six reachability fixtures on JAX against the BFS oracle` |
  | T5 | `docs(jax): document Boolean reachability on JAX` (one-line body as in plan section 10) |
  | record | `docs(jax): record Boolean-reachability execution` |
- **BLOCKED rule.** If pre-flight fails, a patch does not apply, `verify_package.py` fails, a count differs
  from the plan, a build is red, a manifest verdict is FAIL, a mutant survives or is not sha-restored, a
  pre-existing pin goes red, Mathlib would cold-build, or any command exits non-zero (the ONE documented
  exception: `mutation-manifest.sh --check` on `papers/f32_jax_mutations_post.json` WITHOUT a label filter
  exits 125 because of five stale entries, plan section 12; and `rg` exiting 1 because NOTHING matched, which is
a result to record, not a failure: it applies only to the stale-claim greps and to read-only searches): STOP,
leave the tree as it is, and report the
  exact command and output. Do not repair around it.
- **Do NOT merge, do NOT push.** Plan section 11 ends with an "Integration" step list: that is the OWNER's
  after review. You do only its step 1 (commit the execution record, `git status --short` empty), then STOP
  at "READY FOR WHOLE-BRANCH REVIEW". Leave the worktree and the branch `jax-boolean-reach-exec` in place
  (and the extra `boolean-reach-mut-py` worktree if you created one) and report the branch tip. Local `main`
  stays ahead of `origin/main`.
- **Do not touch** the prototype branch `proto-boolean-reach` or its worktree
  `/Users/williammacready/code/python/pyncd/.claude/worktrees/boolean-reach-preflight`: it already contains
  the code the patches add (tip `b46cef9d`). Never merge it, delete it, check it out, or copy from it. If the
  branch `jax-boolean-reach-exec` or the directory
  `/Users/williammacready/code/python/pyncd/.claude/worktrees/boolean-reach-exec` already exists, STOP and
  report; do not delete or reuse it.
- **Out of scope** (plan sections 1 and 12): Iverson lowering in real or max-plus nodes, `realToBool`,
  min-plus, traceback, nested scans, gradients, the XLA jit `-0` seed limitation (known and pinned), the
  stale entries J4/J5/J13/J14/J15 in `papers/f32_jax_mutations_post.json`, and parked items K1-K6. Side issues
  you find: write them in the record as parked with a one-line cost; do not start them (Rule 14).
- **Report faithfully (Rule 12).** Anything skipped, red, retried or not observed is stated as such; say
  "not measured" rather than guessing tokens or timings. The plan marks several figures as unobserved or
  derived (the driver and runner results at the T1 and T2 boundaries, the full-build job count, the first
  observation of the 33-entry Python manifest, the first cycle of the re-anchored entries `MAX-L-SCAN`,
  `MAX-L-DEFAULT`, `JS-L-g2`, `JS-L-e3`..`e5`, `JS-L-c1`). Quote what YOU observe and say when it differs.

## Shell and build rules
Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command, no heredocs, no pipelines into
git. Use absolute paths and `/usr/bin/git -C <worktree>`. Placeholders such as `<worktree>`, `<primary>`,
`<jax-python>` in the plan are literal paths you substitute. Build Lean ONLY with
`bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd <targets>`; never run `lake` from the
repository root; the scripts `check-lean-drivers.sh`, `run-evalplan-*.sh` and `run-evalplan-maxplus.py` are the
documented exceptions that call `lake` themselves (plan section 5). `lake` is not on `PATH`
(`~/.elan/bin/lake`). Python and JAX come from `bash <worktree>/leanncd/experiments/jax_bridge/setup-python.sh`
(needs network for `pip`; an offline failure is BLOCKED). Do NOT probe the `PYTHON` variable (`printenv
PYTHON` exits 1 when it is unset, which is the good case and is NOT a BLOCKED condition): instead prefix every
shell runner command (`run-evalplan-affine.sh`, `-affine32.sh`, `-nonlin.sh`, `-scatter.sh`, `-logic.sh`)
with `env -u PYTHON`, which is harmless whether or not it is set (plan section 5, Setup step 4). The first build after T1
recompiles many jobs (it edits a core file, `Executable.lean`): run long builds, runners and manifests in the
background with output redirected to a file under `<worktree>/.cache/`, and wait for completion instead of
polling. Never run two of {a Lake build, a mutation manifest, a verifier, `check-lean-drivers.sh`, a runner} at
the same time in one worktree: the mutation runners edit tracked files in place. Read file windows of 40-60
lines and use `rg -n`; never read a whole file over about 20k characters. Never commit `.claude/settings.json`.

## Sequence (plan sections 5, 6-10 and 11 have the exact commands; this is the order)
1. Pre-flight: `/usr/bin/git -C /Users/williammacready/code/python/pyncd merge-base --is-ancestor b305b363 main`
   exits 0; `/usr/bin/git -C /Users/williammacready/code/python/pyncd diff --name-status b305b363 main` shows
   only added (`A`) files under `papers/semantics/` whose names start with `jax_boolean_reach_`; the primary
   checkout `git status --short` is empty and its branch is `main`.
2. Worktree (plan section 5, Setup 1-3): `git worktree add -b jax-boolean-reach-exec
   /Users/williammacready/code/python/pyncd/.claude/worktrees/boolean-reach-exec main`, then
   `prepare-worktree.sh` with that worktree as the working directory. It must report Mathlib at or above 95%
   built; if any build starts compiling Mathlib, STOP (hours).
3. Setup 4-5: `setup-python.sh` once, then `verify_package.py --task 0` (expect `Package OK: 5 ordered
   patches, task 0 boundary; index unchanged.`).
4. T1..T5 in order with the per-task loop. Run the full suites (`check-lean-drivers.sh` and the five
   real-path runners) at the T1, T2 and T3 boundaries and once at the end, not after every edit (plan
   section 5, Efficiency rules). At the T4 boundary run the three `BR-T4-*` controls from the filtered
   manifest copy exactly as plan section 9 gives it. T5 is documentation plus comment-only fixes: check it with
   the commands in plan section 10 (`git diff --check` before staging, and a build); the stale-claim greps
   are in plan section 11.
5. After T5, the final verification in plan section 11 order, strictly serial in the one worktree (or the
   documented parallel layout): `verify_package.py --task 5`, the full build, `check-lean-drivers.sh`
   (expect `all eight drivers ran clean`), the max-plus runner (expect both precisions `62 checked views, 58
   refusals, 52 source views, 5 gradient input points, 20 point-forward views, 20 gradient views`), the five
   real-path runners, `git diff --check main`; then the mutation Group L and Group P. Expected kills: Boolean
   Lean manifest 9/9, max-plus Python 18/18, grad 8/8, Boolean Python 33/33 (30 `T3` per-precision + 3 `T4`
   controls), `J3` and `JS-L-g1` PASS, the other re-anchored entries PASS.
6. Stale-claim value-grep (plan section 11: report only, do not edit stale text outside the patches) and the
   execution record (plan section 5 "Execution record"): create `papers/semantics/jax_boolean_reach_record.md`
   from your real runs (do NOT overwrite `jax_boolean_reach_plan_record.md`), commit it, and STOP.

## Budgets
At most three substantive work items per session, about 60 turns and 250k peak context per session; stop at
a task or step boundary near 55 turns. Suggested split: (1) pre-flight, worktree, setup, T1 and T2 with their
boundary suites; (2) T3, T4, T5 with their boundary checks; (3) the final verification, the value-grep and
the record. Measure total tokens from your own usage telemetry and name the method; the Rule 6
slice-execution ceiling is about 175M. `token-report.py` under `.claude/skills/slice-plan/` is for another
tool's transcripts and does not apply to you.

## Final message to the owner
Base commit (the `main` hash you started from) and the branch tip; the five commit hashes plus the record's,
with subjects; per-task `git apply --check` results and `verify_package.py` outputs; per-task verification
results and the boundary suite results (T1, T2, T3) with counts; the final full-build result and job count;
the driver-check last line; the max-plus runner counts for both precisions; the five real-path runners' exit
codes and last lines; the mutation tables (Boolean Lean 9, max-plus Lean post, the six selected scan entries,
`J3`, Boolean Python 33, max-plus Python 18, grad 8) with each `--check` line and each cycle's killed and
restored status; the value-grep hit list with live-versus-historical classification; parked items with cost;
measured tokens and method; every skipped step or STOP; and the confirmation that nothing was pushed or
merged and the branch `jax-boolean-reach-exec` is waiting for review.
