# Brief: four-leg tropical fixtures for multi-axis and constant-slot scatter

**Superseded (2026-10-31).** This work now ships as Task 4 of the slice A plan
([additive_scatter_geometry_a_plan.md](additive_scatter_geometry_a_plan.md)) as the verified patch
`additive_scatter_geometry_a_patches/T4-tropical-fixtures.patch`. Kept as the specification the patch
was built from; execute the plan, not this brief.

For the executor. Self-contained: read this file, `CLAUDE.md` (repo root) and
`papers/semantics/additive_scatter_geometry_design.md` sections 1-5 (read only; its decisions D1-D6 are
approved). You cannot ask questions mid-run: where this brief says STOP, stop and report.

**Process weight: Direct** (fixtures only, no production change, three work items). One test-first
dispatch, one commit per work item, no plan document, no patches, no new mutation-manifest entries. Mutation
checks are done by hand and reported in each commit body.

## 1. Goal

Scatter-geometry slice A lets the checked backend run multi-axis (`Y[a+b]`) and constant-slot (`Y[3]`)
scatters. Its tests prove max-plus for these shapes on three legs (reference, checked f64, checked f32,
in `test/Eval/Plan/ScatterGeometryTest.lean`) but NOT on the oracle's four-leg differential, because the
real harness `compareSource` refuses `agg max`/`min` (`nonSum`). The four-leg harness for tropical programs
is the sibling `Source.SortedDifferential.compareSortedSource`. This task adds three rows to it, so the
independent oracle also vouches for the new geometries: oracle, Core leg, legacy native leg, checked native
leg must report `SortedClassification.fourLegParity`.

## 2. Preconditions (check first; STOP and report if any fails)

1. Base is local `main` AFTER slice A (T1-T4) has merged. Check: `rg -n "affineImageBounds" leanncd/LeanNCD/DSL/Ast.lean`
   finds a definition; `leanncd/test/Eval/Plan/ScatterGeometryTest.lean` exists; `rg -n "throw .*overlappingScatter" leanncd/LeanNCD/DSL/Pipeline/Structural.lean`
   finds exactly one throw, inside the scan branch of `lowerConstSlots` (slice A deletes the stale guard
   for ordinary constant slots and keeps it only for a constant inside a scan statement).
2. `bash leanncd/scripts/lake-build.sh <your worktree>/leanncd LeanNCD Tests JaxExperiment` is green BEFORE you edit.

## 3. Setup

Work in a new git worktree from LOCAL `main` (not `origin/main`, which is stale), e.g.
`git worktree add .claude/worktrees/tropical-geometry-fixtures -b tropical-geometry-fixtures main`, then from
inside it run `bash .claude/skills/new-slice/prepare-worktree.sh` (it syncs the built `.lake` so Mathlib is
not rebuilt; never let a build compile Mathlib from scratch, stop if one starts). Build only through
`bash leanncd/scripts/lake-build.sh <worktree>/leanncd [target...]`, typecheck one file with
`bash leanncd/scripts/lean-file.sh <worktree>/leanncd <path relative to leanncd>`; never run `lake` from the
repository root. Do not push. Read files in windows of about 60 lines (`rg -n` first); do not read a file over
about 20k characters whole.

## 4. Where and how (measured facts)

* File: `leanncd/test/Semantics/SourceSortedDifferentialTest.lean` (already in the `Tests` globs). Add a new
  section at the end; edit no existing row's expectation.
* Helpers there: `snap`, `snap2`, `rhs`, `carrierOf`, `run`, `yCore`, `classOf`, `tagOf`, and the donor
  fixture `collide` (a tropical `.scatter` with `Out[2*a]`). Rows are `#guard_msgs in #eval ...` with the
  expected text in an `/-- info: ... -/` docstring, the file's existing convention. Existing axes: `a` (uid 7, 4),
  `b` (uid 8, 3), `k` (uid 9, 8); inputs `X[a]=[1,2,3,4]`, `W[b]=[1,10,100]`, `Z[a,b]`; output `Y` is declaration 6;
  call the harness with order `(some [6])`.
* `snap` hard-codes extents by axis uid (`if ax.uid = 7 then 4 else if ax.uid = 8 then 3 else 8`) and the
  destination declaration comes from `yAxes`. A destination of extent 6, 13 or 4 therefore needs NEW axes
  (suggest uids 10, 11, 12) and a copy of `snap` (or a parameter) that knows their extents; do not change
  what `snap` does for the existing uids.
* The destination extent production derives is the exact reach (slice A decision M1): `Y[a+b]` over
  (4,3) is 6; `Y[2*a+3*b]` is 13; `Y[3]` is 4. Declare the output axis with exactly that extent, as the
  existing `strided` rows do (extent 8 for `2*a`).
* The tropical profile admits finite integer inputs within 2^20 and treats `+inf`/`-inf` as their own class
  (empty cells are `-inf` for max-plus, `+inf` for min-plus). `⊗` is `+`, `⊕` is `max`/`min`.
* Do not use `compareSource` (it refuses `max`/`min`). f32 tropical comparison is out of scope (parked).

## 5. Work items (three commits, in order)

For each item: write the rows first, run them, assert the OBSERVED output (the hand-derived values below are
only a cross-check: if an observed value differs from them, STOP and report both, do not edit either).
Each item also needs one accept-neighbour (the nearest program that was already legal: the existing
`collide`/`strided` rows must stay passing, untouched) and the hand mutation check named.

**W1: max-plus and min-plus convolution.**
`snap` over output axis extent 6 with
`.scatter "Y" [.affine (.affine 0 [(1, a), (1, b)])] (rhs agg [[.read "X" [.axis a], .read "W" [.axis b]]])`
for `agg` in `.max`, `.min`. Assert `yCore` (the Core leg's `Y` cells) and `classOf = fourLegParity`.
Hand cross-check: max-plus `[2, 11, 101, 102, 103, 104]`; min-plus `[2, 3, 4, 5, 14, 104]`. The row must fail
under max-times semantics (cell 1 would be 10, not 11): say so in a comment, as the file's existing S3b rows do.
Mutation check: revert `LHSSlot.outExtent`'s 2+-axis arm (`leanncd/LeanNCD/DSL/Ast.lean`) to the old sum
`c0 + Σ c·n`, rebuild this module, the rows must fail (derived 7 vs declared 6); restore, rebuild green.

**W2: collisions and empty fibres with two coefficients.**
Output axis extent 13, `Y[2*a + 3*b]`: `.affine 0 [(2, a), (3, b)]`, same RHS and both aggs. Cells 1 and 11 are
never written (empty fibres) and cell 6 collides (`a=3,b=0` and `a=0,b=2`). Hand cross-check max-plus
`[2, -inf, 3, 11, 4, 12, 101, 13, 102, 14, 103, -inf, 104]`; min-plus
`[2, +inf, 3, 11, 4, 12, 5, 13, 102, 14, 103, +inf, 104]`. Assert `yCore` and `classOf`.
Mutation check: re-add the `multiAxisScatterLhs` throw for top-level scatters in `checkScatterLHSSlot`
(`leanncd/LeanNCD/Eval/Plan/Compile.lean`; the scan arm keeps its own refusal): the checked leg refuses and the
class becomes `nativeFailure`; restore.

**W3: constant slot.**
Output axis of extent 4 (a NEW axis, not `a`), statements `.scatter "Y" [.affine (.const 3)] (rhs agg [[.read "X" [.axis a]]])`
and the same as `.assign` (the `.assign` form compiles only because slice A deleted the stale
`overlappingScatter` guard). Hand cross-check: max-plus `[-inf, -inf, -inf, 4]`, min-plus `[+inf, +inf, +inf, 1]`.
Assert `yCore` and `classOf` for both arms and both aggs. This is the only independent check of slice A's
constant-slot lowering: the oracle reads the raw constant, production rewrites it to a placement over a
synthetic size-1 axis in `lowerArith`.
Mutation check: change the rewrite's bias in `lowerArith` (`leanncd/LeanNCD/DSL/Pipeline/Structural.lean`) from `n`
to `n + 1`: the rows must fail; restore.

## 6. If something differs from the brief

* A row classifies as anything other than `fourLegParity`: that is a finding, not a pin. Do NOT assert it.
  Record the full classification (the legs' results) and STOP after committing the rows that did pass.
* A precondition or a named identifier does not exist: STOP and report, do not improvise.
* Production code edits are out of scope. A needed production change is a blocker to report, not something to do
  (CLAUDE.md Rule 14: side issues are parked with a one-line cost, not started).

## 7. Done when, and the report

Three commits on the branch (subject style of the repo, e.g. `test(oracle): four-leg tropical convolution on multi-axis scatter`),
each body listing the mutation check, what it changed, and the observed failing line. Run
`bash leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD Tests JaxExperiment` at the end and report the job
count and result. Each mutation check must have been restored (verify `git diff` is empty of production files).
Budget: 60 turns and 250k peak context; say so if breached. Report in at most 15 lines: commit shas, the observed
values per row, the three mutation outcomes, the build result, anything parked. Do not merge and do not push;
leave the branch for review.
