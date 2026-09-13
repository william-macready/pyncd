# SDD ledger — plan: leanncd/docs/superpowers/plans/2026-09-12-lhs-scatter-in-scans.md

Worktree: /Users/williammacready/code/python/pyncd.worktrees/implement-lhs-scatter-sol-1m
Branch: agents/implement-lhs-scatter-sol-1m (fast-forwarded to local main @ 945b55e)
.lake synced from /Users/williammacready/code/python/pyncd (8101/8094 mathlib oleans, no cold build needed)
Prepared by: .claude/skills/new-slice/prepare-worktree.sh

## Task 1 — complete

- Implementation identifier: `feat(leanncd): align affine scatter extents` (this Task 1 commit).
- `LHSSlot.outExtent` now resolves all raw terms, computes the legacy boundary, normalizes
  coefficients by UID with `idxDensify`, and uses `c*n + floor(b/c)*c` only for the exact positive
  one-axis/nonnegative-bias/nonzero-extent case.
- Added all 14 §3.1 direct guards. Rebaselined shifted stride in
  `ScatterCheckTest`, `ScatterDenseTest`, and `ScatterCompileTest`; added `SA9` and pinned
  `scatterPrograms.length == 9`.
- Mutation evidence (each changed `Ast.lean`, exited 1 at the intended guard, restored all seven
  Task 1 file hashes, then rebuilt successfully):
  - M1 `c*n+aligned(b) → c*n+b`: shifted check/dense/compile fixtures failed; focused rerun observed
    `SCATTER PARITY CORPUS (S-A Task 6) FAILED`; restored builds: 8,527 and 8,524 jobs.
  - M2 `idxDensify cf us → cf.map (·.1)`: duplicate and cancelling UID guards failed; restored
    `ScatterCheckTest`: 8,492 jobs.
  - M3 raw-size precheck → `true`: zero-coefficient unsized-axis guard failed; restored
    `ScatterCheckTest`: 8,492 jobs.
  - M4 remove `n > 0`: zero-source-extent fallback guard failed; restored `ScatterCheckTest`:
    8,492 jobs.
- Final gates, all through `/Users/williammacready/.elan/bin/lake`:
  - `build Eval.Plan.ScatterCheckTest Eval.Plan.ScatterDenseTest Eval.Plan.ScatterCompileTest` —
    pass, 8,520 jobs.
  - `build Eval.Plan.DifferentialTest` — pass, 8,524 jobs; generated `3,832/3,832`, scan
    `17/17`, curated scatter count `9`.
  - `build LeanNCD` — pass, 8,544 jobs (replayed pre-existing warnings/sorries outside Task 1).
  - `build JaxExperiment` — pass, 8,514 jobs.
- No Task 1 stop condition occurred. Task 2 not started.
