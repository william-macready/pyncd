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

## Task 4 — complete

- The independent unroller now preserves scatter statement parts, derives non-advancing state
  geometry with its own aligned-extent implementation, and emits dense private assignments followed
  by top-level scatter leaves.
- Base contributions have source-indexed names, independently enumerated destinations, explicit
  overlap rejection, and canonical zero-filled merge leaves before recurrence evaluation.
- Every contribution, merge, and step leaf is shape-checked against oracle-local state-slice extents;
  reconstruction uses the actual advancing-dimension positions.
- Synthetic slice-axis UIDs are minted above every UID appearing in explicit sizes, declarations,
  scan axes, LHS slots, RHS reads, predicates, and masks. The contraction fixture leaves its RHS-only
  axis unpinned and gives it the old size-only fresh UID, directly guarding this requirement.
- Added five exact structural/value fixtures: even/odd interleave, strided recurrence, RHS
  contraction, non-trailing advancing dimension, and two affine non-advancing dimensions. Feature
  guards require source and emitted scatters, assignment-then-scatter adjacency, contribution merge,
  private-name exclusion, and exact reconstructed histories.
- Scripted mutation evidence, all through
  `/Users/williammacready/code/python/pyncd/leanncd/scripts/mutation-cycle.sh`, with
  `mutation_exit=1 restore_hash_exit=0 restored_build_exit=0`:
  - M1 restored `c*n+b`: shifted interleave failed oracle-local shape validation.
  - M2 collapsed contribution names: interleave history and structural name guards failed.
  - M3 removed base-to-canonical merges: recurrence reads failed on missing canonical leaves.
  - M4 dropped affine bias: interleaved contributions overlapped and structural guards failed.
  - M5 assumed trailing advancing dimensions: the non-trailing history fixture failed.
  - Review R1 restored size-map-only UID freshness: the inferred contraction axis conflicted with
    the synthetic slice axis (`uid 8106`, extents 2 versus 6).
  - Review R2 disabled overlap rejection: the direct overlapping-base fixture was accepted.
- Gate: `build Eval.PropertyOracle.ScanUnroll Eval.PropertyOracle.ScanOracle` passed at 8,505 jobs.
- Independence review initially found the UID-freshness blocker and missing overlap coverage; both
  were fixed and mutation-tested. Follow-up review: CLEAN. No forbidden production helper is used.

## Task 5 — complete

- Removed `checkScatterNoScan` and all three chain sites: direct `TLProgram.compile`,
  `compileToScheduled`, and `RouteWeaveTest`'s logical pipeline. `CompileError.scatterInScan`
  remains producerless for compatibility.
- Scan block capability now admits iteration slots plus free and normalized single-axis affine
  scatter placement, while retaining typed rejection for constant/multi-axis forms, nonlinear
  scatters, non-default reduction, and nonzero fill.
- Capability postflight traverses `ScanStmt.sourceStmts`, covering plain statements and scan
  base/recurrence lists for predicate destinations and unlowered scatter-shaped assignments.
- Route diagnostic case 11 now reaches `missingBaseCase`; a complete base-plus-recurrence scatter
  scan compiles and remains one opaque route fragment without production route changes.
- Added separate base/recurrence reachability, predicate/nonlinear/options/form negatives,
  dual-defect precedence, post-pass traversal, and routed-opacity fixtures.
- Scripted mutation evidence:
  - M1 restored the direct compile guard inline: the complete route fixture failed with
    `scatterInScan`.
  - M2 restored the scheduled compile guard inline: independent base and recurrence reachability
    guards failed.
  - M3 restored the test-local logical-route guard inline: the logical/physical route fixture failed.
  - M4 filtered scan nodes out of the capability post-pass: predicate-destination and unlowered
    assignment scan fixtures failed.
  - Review R1 moved option checks before nonlinearity: the dual-defect precedence fixture failed.
  - Each cycle used `/Users/williammacready/code/python/pyncd/leanncd/scripts/mutation-cycle.sh` and
    reported `mutation_exit=1 restore_hash_exit=0 restored_build_exit=0`.
- Combined gate
  `DSL.Pipeline.StructuralTest DSL.Pipeline.RouteWeaveTest
  DSL.Pipeline.RouteFragmentDiagnosticTest Eval.Plan.CompileTest Eval.Plan.ScanCompileTest LeanNCD`
  passed at 8,549 jobs.
- Capability/reachability review: CLEAN. No routed representation change or Task 5 stop condition
  occurred.

## Task 6 — complete

- `compileScan` now accepts scan-local assignments and scatters through a dedicated destructurer,
  preserving ordinary top-level assignment handling.
- Dense output bases come from normalized LHS index expressions in first-seen LHS order, excluding
  only context-role slots. Scan-local scatters are presented to global size inference as assignments
  so placement shapes cannot constrain persistent-state reads.
- State geometry validates every placement row before cross-placement extent comparison, locates
  advancing dimensions by context-role slots, and delegates non-context extents to
  `LHSSlot.outExtent`.
- Base and recurrence lowering feed only the dense output basis to `residualizeAssignment`, then
  share one affine placement-row builder. Emitted block steps remain `.assign`; affine placement
  exists only in `StateWriteMap`.
- Added typed source errors for inadmissible write rows, scatter-shaped recurrence scratch, and
  context axes used as affine outputs. Original base/recur statement indices are retained.
- Added eight acceptance fixtures, ten rejection fixtures, and three locator/order fixtures. The
  two-affine fixture reverses LHS order relative to RHS/UID order and pins dense basis order.
- All eight planned mutation cycles used
  `/Users/williammacready/code/python/pyncd/leanncd/scripts/mutation-cycle.sh`, verified the three-file
  restore manifest, and reported `mutation_exit=1 restore_hash_exit=0 restored_build_exit=0`:
  source basis, context prefix, affine bias, state extent, phase selection, source locator, scratch
  rejection, and dense-before-placement.
- Compiler review found invalid rows could be masked by an extent mismatch. Row admission now runs
  before extent comparison; review mutation R1 skips that precedence and fails the mixed
  valid-base/invalid-recurrence fixture.
- Independent geometry review found no soundness defect and identified one basis-order coverage gap.
  The reversed two-affine fixture closes it; review mutation R2 reverses basis extraction and fails.
- Final wrapper gate
  `Eval.Plan.ScanCompileTest Eval.Plan.ScanTest Eval.Plan.AdapterTest LeanNCD` passed at 8,547 jobs.
  Both required reviews are adjudicated; no Task 6 stop condition occurred.

## Task 7 — complete

- Added exactly seven source-generated S-B differential programs covering strided base, strided
  recurrence, even/odd base interleave, dense contraction before placement, a non-trailing advancing
  dimension, two affine non-advancing dimensions, and two scans with one S-B node.
- The corpus compares exact environment key inventories, tensor shapes and values, ordered warning
  payloads, unchanged external inputs, and scratch-name privacy across checked, legacy, and independent
  oracle legs. Explicit expected environments prevent three-way agreement on the same wrong result.
- Added direct legacy-versus-independent checks for the five Task 4 isolation cases.
- Global checked/legacy sizing now presents scan-local scatters as assignments, so placement extents do
  not constrain persistent-state reads. The oracle independently derives sizes from declarations and
  current inputs rather than cached `ScheduledProgram.explicitSizes`.
- Soundness review found canceled LHS coefficients diverged across the three legs. Legacy source bases
  and oracle placement bases now use normalized nonzero coefficients; the oracle also normalizes
  residual placement expressions before ordinary scatter evaluation.
- Follow-up review found global first-seen collection could let a canceled occurrence reserve an axis
  position before a later live occurrence. Legacy extraction now normalizes and filters within each
  slot before global first-seen deduplication. Regressions cover direct basis order, three-way cross-slot
  parity, canceled RHS contraction, and unsized canceled-LHS-only UIDs.
- Active capability, pipeline, test-portfolio, design, roadmap, tutorial, and IR documentation now
  describes the shipped bounded S-B subset. Historical measurements are retained only with explicit
  supersession markers.
- Scripted mutation evidence, all through
  `/Users/williammacready/code/python/pyncd/leanncd/scripts/mutation-cycle.sh`, with
  `mutation_exit=1 restore_hash_exit=0 restored_build_exit=0` and final `PASS`:
  - M1 dropped an odd base write.
  - M2 restored the oracle's old shifted extent.
  - M3 weakened environment comparison to values only.
  - R1 restored legacy placement-based size inference.
  - R2 restored cached oracle sizes.
  - R3 retained a canceled axis in the legacy dense basis.
  - R4 emitted an unnormalized oracle residual placement.
  - R5 retained raw per-slot axes before global first-seen deduplication.
- Final whole-branch soundness and semantic-independence review found one stale active-documentation
  family and no implementation defect. The active pipeline descriptions and `BlockStep` representation
  comment were corrected; remaining references are explicitly historical, superseded, or seed material.
- Final wrapper gate passed all 8,665 jobs:
  `Eval.Plan.ScatterCheckTest Eval.Plan.ScatterDenseTest Eval.Plan.ScatterCompileTest Eval.ScanTest
  Eval.Plan.ScanTest Eval.Plan.ScanCompileTest Eval.Plan.AdapterTest Eval.PropertyOracle.ScanUnroll
  Eval.PropertyOracle.ScanOracle Eval.Plan.DifferentialTest Tests LeanNCD JaxExperiment`.
- No Task 7 or final-integration stop condition occurred.
