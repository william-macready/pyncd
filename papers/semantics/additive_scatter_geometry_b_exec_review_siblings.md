# Slice B execution review — Lens 1 (siblings)

Review range: `fd922285..f7c731f4146c6fab1e481e79dfe0273c2770748a`.
Execution checkout: `/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec`.

Read the plan's sections 2, 3, 5 and 6 and the execution brief's hard rules.
Read-only review of production/tests; this report is the only permitted edit.
Three work items: sibling admission/marker removal, oracle mirrors, re-pinned intent.
Rank-0 and zero-coefficient-group probes and the 18 mutation cycles are intentionally not repeated.
Builds are reserved to the parent; no build or mutation result is claimed here.

## Progress

- Review opened; findings will be appended as each work item completes.

## 1. Sibling admission and marker removal — complete

No new finding in this work item.

- Re-grepped all Lean production callers. `LHSSlot.collectable` has exactly the two intended
  consumers (`Collect.lean`); it rejects raw `.const` by constructor and scan slots, without
  inspecting names, unit extents, coefficient positions, or synthetic-axis shape.
- `Ast.lean`: `slotsBecomeScatter` still recognizes every affine slot and repeated
  free UID; `outExtent` remains the shared extent implementation, including normalized multi-axis reach.
- Read unchanged callers: Structural read-rank/nonlinearity checks (`source window`);
  `lowerArith` (`source window`); collector `needsB5`, basis selection, boxed D5, and admission
  (`Collect.lean`); route classification/physicalization
  (`RouteFragments.lean`); checked unlowered-assign refusal
  (`Eval/Plan/Compile.lean`). No newly accepted form bypasses the common slot rule.
- `lowerConstSlots` (`Structural.lean`) rewrites raw constants on both source statement
  arms, with fresh UID and pinned extent 1; scan-containing statements remain untouched.
- `scatterAffineClass` (`Ast.lean`) and checked top-level/scan checks
  (`Eval/Plan/Compile.lean`) distinguish constructors and normalized coefficients,
  not names: top-level multi-axis passes; scan-local multi-axis and raw constant remain refused.
- Searches for `constUnitPrefix`, `isConstUnit`, `reservedAxisName`, `checkReservedAxisNames`,
  `#const`, and `startsWith` found no production marker consumer. The only production `#const`
  occurrences are its display-name construction/comment in `Structural.lean`.
  Historical test commentary is not an executable consumer. No forgeable-marker survivor found.

## 2. Oracle mirrors — complete

No new finding; one already-parked disagreement confirmed by code inspection.

### L1-K1 — medium (test-side oracle only), known parked; verdict: park, about 0.3 dispatch

`test/Semantics/OracleSortRules.lean` still returns the legacy sum for normalized
multi-axis forms. For `a+b` with sizes `(4,3)`, it predicts 7; production
`Ast.lean` returns exact reach 6. The widened `bounded` (`OracleSortRules.lean`)
makes this reachable through `predictShaped` (`source window`): a pinned destination of extent 6
with that writer is predicted `writerExtentExceedsBox`, although its realized extent fits.
This is the explicit section-2 parked cell, not a new finding or a production defect.
No new probe or build was run. Proposed future repair remains the parked extent-predictor
update plus a boundary fixture (box exactly equal to multi-axis reach); no redesign is needed.

### Other covered mirrors

- Read `nonBareWrite`, `derivedShape`, `declaredShapeWins`, `detectConditions`
  (`Semantics/Source/Differential.lean`) and re-grepped callers. Derived affine extents
  call `LHSSlot.outExtent`; raw constants use `n+1`, matching source constant lowering.
  The D5 exclusion tests all syntactically mentioned UIDs, including identity and zero-coefficient
  axes, matching production rather than normalizing away those mentions.
- Checked source form construction (`Semantics/Source/Admission.lean`): affine forms
  preserve `idxAffineForm` terms; no independent normalization loses D5 evidence.
- Read test `bounded`, `basis`, `needsB5`, `predict`, `pinnedBox`, `singleBoxed`,
  `predictedExtent`, `predictShaped` (`OracleSortRules.lean`).
  Accepting raw source constants in `bounded` correctly mirrors their subsequent lowering;
  it is not permission to accept a raw hand-built schedule. `singleBoxed` retains nonempty
  destination, pinned declarations, nonpredicate, and D5 checks. `pinnedBox`'s iter handling
  remains explicitly exercised by unchanged hand rows.
- Re-grepped predictor consumers and read concrete-C1 and hand SHAPED staging
  (`OracleSortRulesTest.lean`): existing boundary staging does not isolate K1's
  exact-reach edge. The oracle D5 identity-slot isolation gap is already acknowledged in
  plan section 5; no new disagreement established.
- Rank-0 unreachability and zero-coefficient-group parity were accepted from the stated
  prior evidence and deliberately not re-probed. Shared-predicate refactoring, degenerate
  validation, and narrowing D5 remain the owner's parked decisions.

## 3. Re-pinned intent — complete

### L1-N1 — low (test blind spot), new re-pin weakness; verdict: fix-now, about 0.1 dispatch

The new acceptance guards `sourceError p == none` can pass when source compilation FAILS.
`B5NativeTest.lean` maps any `compileToScheduled` error to `scheduled p = none`;
`sourceError` (`source window`) then binds over that option and also returns `none`.

The refusal-to-acceptance re-pins at `B5BoundaryTest.lean` (`twoAxes`,
`explicitConstant`) and `ScatterGeometryTest.lean` (`convTwo`, the constant
writer pairs/mixed pair) therefore lose the ability to detect an earlier compilation refusal:
before the re-pin, compilation failure could not satisfy the expected `some (.multiWriterScatter ...)`;
now it satisfies `none`, contradicting the new comments' source-admission intent.

The helper's lossy encoding predates this branch; making these formerly negative guards positive
without requiring scheduling success is new. This is separate from the parked independent
mutation-kill power of F1–F6. It is not evidence that current compilation fails: real value/shape
fixtures cover the broader feature, so severity is low and it is not BLOCKED.

Proposed surgical repair: for these acceptance pins, also require `(scheduled p).isSome`
(or explicitly match successful scheduling followed by successful validation). Keep the existing
validation assertion; do not broaden production changes or weaken fixtures. No mutation or build
was run to establish this deterministic `Option.bind` path.

### Remaining re-pins covered

- `StructuralTest:241-256`: removing the name-prefix assertion leaves explicit success/error
  handling, exact lowered constructor/coefficient, one pinned size-1 declaration, and axis equality.
  The semantic lowering intent survives; the intentionally deleted naming convention is not needed.
- `ScatterGeometryTest:124-139,237-250,277-290,383-414`: apart from N1, boxed shapes are
  compared against explicit `some [8]` in all three legs, group membership against `["S"]`,
  synthetic declaration extents against an explicit list, and former reserved names against
  success in BOTH compile chains plus bitwise native/reference values. `None == None` cannot
  satisfy these shape/value/success pins.
- `B5cSingleBoxTest:79-81,134-145`: the membership re-pin now requires the formerly excluded
  multi-axis/constant entries to be `["S"]`; compilation failure returns `[]` and fails the assertion.
  Other D5/unpinned/predicate/scalar exclusions remain in the same list.
- `SourceDifferentialScatterTest:156-188,354-357`: parity tags require actual four-leg parity,
  not merely absence of an extent condition; independent zero-condition guards for `fFbig` and
  `fI2` still detect a stale `declaredShapeWins` even when its condition cannot be confirmed.
  The condition helper uses 99 on source failure, so failure cannot masquerade as zero.
- `OracleSortRulesTest:88-130,213-230,364-370,446-452,500-516,569-621,637-643`:
  counts remain over the same generated corpus and are accompanied by class-specific production
  agreement, strict constructor coverage, exact supplementary expectations and statement sorts,
  concrete-stage disagreement checks, and exact exceed-box histogram. Dropping
  `multiWriterScatter` from C1 does not drop its strict predicate-row coverage.
- `OracleMixedRefusalTest:18-28,137-155,162-197` and
  `OracleMixedDifferential:75-90`: the new `"none"` pins require both native legs to be observed,
  not a failed/absent run. Removing the obsolete false-`nativeFailure` contrast is appropriate:
  those geometries are no longer refusals. The replacement cast/vote split still uses two genuine
  refusals with different constructors and an equal-leg parity control. Its intent is constructor
  agreement (the existing classifier does not compare the predicted destination string), unchanged
  by the donor swap.
- Read the remaining branch diff, including all new surface fixtures, parser pins, registration,
  error-comment and documentation changes. The surface D5 R1/R2 pair explicitly compares all three
  shapes and concrete cells, rather than silently accepting equality of failed runs.

## Result and verification limits

All three work items completed. **One new low-severity test finding (N1), one known parked
test-predictor disagreement (K1); no new production correctness/design blocker found.**
N1's proposed verdict is fix-now; K1 stays parked. Final adjudication and builds belong to the parent.

Reviewed HEAD was verified as `f7c731f4146c6fab1e481e79dfe0273c2770748a`.
No production/test edits, commits, builds, new probes, or mutation cycles were performed.
Only this report was edited by this reviewer; other working-tree paper/report changes appeared
concurrently and were not altered.

Usage measurement attempted with the repository's `token-report.py` and the supplied Copilot
session ID `69471b59-4948-4b98-bd3a-aa925cdbc8f1`. It reported
`no transcript for session 69471b59-4948-4b98-bd3a-aa925cdbc8f1`: the script reads Claude
JSONL transcripts, not this Copilot agent's usage. Exact cumulative input and peak context are
therefore unavailable; the 250k peak cannot be independently certified by that method.
Review completed in fewer than 45 assistant turns, with no known budget breach and no nested agents.
