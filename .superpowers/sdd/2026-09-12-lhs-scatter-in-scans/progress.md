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

## Task 2 — complete

- Added `WriteRowKind.strided outputPos scale offset` in classifier order after `.advancing` and
  `.free`, requiring an output-half position, positive scale, and nonnegative offset.
- Base and step geometry now share ordered free/strided output-position coverage and exact
  output-row extent checking. Base writes explicitly reject `.advancing` rows and reject
  `.strided` rows on advancing dimensions.
- Strided extents delegate to `scatterDestExtent`; pinned range checking is unchanged. Equal
  positive scales with distinct offset residues are the only new proven-disjoint collision case.
- The compiler now reuses `baseWriteTouchesBoundary`. All nine exhaustiveness tripwires were
  extended, including the frozen 9-value / 81-pair / 972-case clause-1 agreement oracle.
- Added classifier witnesses, base/step acceptance and execution, base/step extent mismatches,
  forbidden dimension classes, four collision cases, and the exhaustive 102,400-case finite-image
  soundness check.
- Mutation evidence used only
  `/Users/williammacready/code/python/pyncd/leanncd/scripts/mutation-cycle.sh`; every listed cycle
  reported `mutation_exit=1 restore_hash_exit=0 restored_build_exit=0` and `PASS`:
  - M1 positive-scale guard: negative-scale classifier and base geometry guards failed.
  - M2 nonnegative-offset guard: negative-offset classifier guard failed.
  - M3 output-half guard: context-position classifier and step-geometry guards failed.
  - M4 strided cover arm: the behavior-level mutation returned `none` for `.strided`; base/step
    acceptance, execution, extent diagnostics, and the 972-case agreement oracle failed.
  - M5 base `.advancing` prohibition: the synthetic base-row rejection failed.
  - M6 advancing-dimension `.strided` prohibition: the isolated dimension-class rejection failed.
  - M7 strided extent equality: predicate plus base/step plan-level mismatch fixtures failed.
  - M8 modular disjointness: the even/odd disjointness guard failed.
  - M9 compiler boundary predicate reuse: `ScanCompileTest` boundary locator guards failed.
  - M10 `.advancing` bias requirement: look-ahead and classifier closure witnesses failed.
  - M11 `.free` bias requirement: shifted-unit-stride and classifier closure witnesses failed.
- Gates:
  - `build Eval.Plan.ScanTest Eval.Plan.ScanCompileTest`: pass, 8,515 jobs.
  - `build LeanNCD`: pass, 8,544 jobs.
  - After an unsafe `lake --dir` probe selected Lean 4.33.1, an explicit Lean 4.30.0 targeted build
    restored dependencies and passed at 8,515 jobs. A scripted M11 rerun then restored the source
    hashes and rebuilt `LeanNCD` successfully at 8,544 jobs. Its mutated `LeanNCD` target survived,
    as expected because that target excludes `ScanTest`; it is not counted as mutation evidence.
- Soundness-focused review: CLEAN. No Task 2 stop condition occurred.

## Task 3 — complete

- `evalStmtSliceSeeded` now computes scan scatters as dense assignments over the first-seen,
  non-seeded LHS source-axis basis. RHS-only axes remain contractions.
- `scanStateShape` retains declared history extents for iteration slots and delegates every other
  slot to `LHSSlot.outExtent`.
- `writeScanStmtSlice` evaluates the original LHS expressions only after dense slice computation and
  overlays base contributions in source order. Ordinary assignment slices retain their prior basis.
- Scatter-shaped recurrence scratch is rejected before its RHS is evaluated.
- Added complete shape/data fixtures for strided base, strided recurrence, even/odd base interleave,
  dense contraction before placement, and a non-trailing scan dimension.
- Scripted mutation evidence, all through
  `/Users/williammacready/code/python/pyncd/leanncd/scripts/mutation-cycle.sh`, with
  `mutation_exit=1 restore_hash_exit=0 restored_build_exit=0`:
  - M1 wrote dense source coordinates directly: all five S-B value fixtures failed.
  - M2 included RHS-only axes in the source basis: the contraction fixture failed.
  - M3 reinitialized before each base contribution: interleave and existing multi-base fixtures
    failed.
  - M4 dropped affine bias: recurrence, interleave, and non-trailing-position fixtures failed.
- Gates:
  - Each restored focused cycle rebuilt `Eval.ScanTest` successfully at 8,488 jobs.
  - An M4 rerun against `Tests` failed at the intended fixtures, then the restored `Tests` build
    passed at 8,661 jobs. Generated corpus remained 3,832/3,832 and scan corpus 17/17.
- Reference-semantics review: CLEAN. No Task 3 stop condition occurred.
