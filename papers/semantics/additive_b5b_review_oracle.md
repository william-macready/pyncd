# B5b independent review — oracle independence

- Base: `f0dd2d78`
- Snapshot: `411c2a11b432ff87ba4ac28ab9c23e1601bf68fb`
- Lens: independent reviewer B; declaration-pinned box oracle, realized-fit prediction, SHAPED observation, four-leg execution, staged row census, and C1 rename stability.
- Scope: whole committed diff; authority is `additive_b5b_plan.md` §§2, 5–7 and design §§3–4. No source mutations, builds, commits, nested agents, or reliance on the other review.

## Review log

- Review initialized; authority and committed diff inspection pending.
- Read plan §§2, 5–7 and design §§3–4 before inspecting implementation. HEAD exactly matches the requested snapshot.
- `OracleSortRules.lean:163–179,260–319`: `declaredAxes`, `basis`, `coefficients`/`normalized`, and `predictedExtent` are test-side implementations. `pinnedBox` searches declarations for each declared UID, accepting `.axis … (some _)` or `.iter`; it does not call `declaredAxisSizes`, `collectorShapeObligations`, or production extent helpers. Fit checks equal rank and `actual <= basis`, using independent extents.
- `OracleSortRules.lean:323–352`: SHAPED observation performs checked preparation, retains a distinct `writerExtentExceedsBox`, retains raw `sizeConflict`, and surfaces unmodelled diagnostics. Its existing `sizeConflict` allowance applies only to predicted exact mismatches, not boxed fit/accept predictions.
- `OracleSortRulesTest.lean:463–493`: staged census is explicitly guarded at eleven rows/seven predicted accepts; C1 is guarded at 81 observations, all `writerExtentExceedsBox`. Tracing actual mixed four-leg execution and fixture values next.
- `OracleMixedRefusalTest.lean:85–99,120–137`: box rows call `compareMixedSource` without `doctor` or `feed`; `valueParity` requires exactly `.fourLegParity`, both statement sorts, explicit oracle values, and explicit Core values. No fallback to three legs or manufactured parity.
- Traced `OracleMixedDifferential.lean:231–292,308–399`: Core uses `admitSourceSorted`/`coreTensorsAt`, its own earlier outputs, and default identity feed. Classification requires a completed Core leg, Core/oracle comparison, accepted native observations and both bit comparisons. `NativeLegs.lean:216–280` independently invokes reference evaluation and checked preparation/execution. Mixed value evaluation (`OracleMixedEval.lean:142–235`) computes directly over the declared/specification box, not production collector/scratch helpers.
- Independently recalculated overlap values from `OracleMixedFixtures.lean:46–47`: Z rows sum to `[-12,18,48,78]`, maxima `[-3,7,17,27]`, minima `[-5,5,15,25]`, with X `[20,2,3,40]`. Combining at even coordinates yields real `[8,20,51,118]`, max `[20,7,17,40]`, min `[-5,2,3,25]`. Extent 10 leaves odd cells and cells 8–9 at the corresponding zero identity. All three explicit expected lists match.
- Precision checked separately: mixed four-leg rows are f64 (UInt64 bit comparison in `SortedDifferential.lean:51–54,102–113`); the claimed f32 coverage is real checked-f32 execution in `B5bBoxTest.lean:53–71`, through `B5NativeTest.agree:158–166`, which compares `Float32.toBits`. Tropical `±inf` and trailing holes are pinned there. No claim that the mixed Source/Core harness itself runs f32 is needed.
- Recounted staged rows directly: plain+scatter (1 accept); the two extent-8 affine donors in box 4 (2 refusals); box12 pair (2 accepts); extent8 pair (2 accepts); rectangular diagonal twice (2 refusals); de-marked square twins twice (2 accepts). Total 11 = 7 accepts + 4 refusals. The rectangular second extent is 4 against box 3; square extents are `[4,4]`.
- Independent C1 source-eligibility recount: shape-5 neutral writer paired with allowed non-neutral writers gives 60 ordered rows; shape-5/shape-0 neutral pairs give 14; shape-5/shape-5 gives 7. Total 81; triples contain no shape-5 writer. Every candidate includes realized extent `2*4 + floor(1/2)*2 = 8`, exceeding the pinned Y extent 4. The base-to-snapshot diff changes the histogram from 81 `sizeConflict` to 81 `writerExtentExceedsBox`, not to acceptance.
- Read the whole committed diff (22 files) and immediate oracle helpers, including the independent test-side neutrality implementation. `git diff --check f0dd2d78 411c2a11b432ff87ba4ac28ab9c23e1601bf68fb` passes. Independent Python arithmetic reproduced all three extent-10 expected lists without importing repository helpers.

## Findings

**High-confidence correctness bugs: 0.** No within-plan correctness adjudication required for this lens.

Nonblocking documentation observation: `OracleSortRulesTest.lean:483` calls the accepted plain+scatter row “bool”, but its definition at lines 306–308 uses max-plus on f64 Y. This does not affect the census or execution; optionally change that one word to “max-plus” during within-plan close-out. It is not evidence of Boolean box coverage.

## Limitations and exclusions

- Full build is running independently; this review will not start a build.
- Explicit exclusions: single-writer declaration asymmetry, M4 actual-image fit, inferred-size boxes, route/JAX widening, predicate/multi-axis/constant scatter, and F3 alone.
- This is a static committed-diff review plus independent arithmetic, not a new Lean build/mutation run. Existing `#guard` execution awaits the separately running full build; no controller conclusions or other reviewer report were read.
- `.iter` pinning is implemented independently in `pinnedBox`, but the staged SHAPED helper `sizesOf` (`OracleSortRulesTest.lean:413–414`) gathers `.axis` sizes only, and the eleven rows contain no `.iter` example. This limits fixture coverage, not the inspected declaration rule. A dedicated iter-pinned row could be a small future test addition; it is not necessary to resolve an observed bug.
- The new late-dimensional pins (`B5bBoxTest.lean:74–81`) cover reference/f64 checked paths, not f32. The B6 negative-writer pins (`B5bBoxTest.lean:84–89`) cover reference/f32 checked preparation, not checked f64. Other box acceptance/refusal and tropical holes cover f32 as noted above.
- No unrelated issue was opened or pursued.

## Completion

Review complete for the requested snapshot. Findings: **0 correctness bugs**, **1 optional comment correction**, plus the stated coverage limitations. Budget cap: 60 turns / approximately 250k peak context; no breach observed (under 25 reviewer turns and well below 250k peak). No source edits, builds, commits, or nested agents; the only write is this report.

## Same-review precision clarification / adjudication

Re-read only committed `B5bBoxTest.lean` using `git show 411c2a11b432ff87ba4ac28ab9c23e1601bf68fb:leanncd/test/Eval/Plan/B5bBoxTest.lean` while production mutations were running. The clarification is warranted: `planCause` (lines 45–50) schedules the original f32 program and obtains its signature with `InputSignature.ofDenseInputs32ForDecls s.decls in32`; therefore the negative-writer B6 guard is checked **f32 preparation**. `refError` converts the program with `as64`, so its companion guard is reference f64 evaluation. The late-dimensional guards remain reference/f64 checked.

The prior grouped precision limitation was incorrect and is corrected above. This is a report-only factual correction, not a second review or a new code finding; the correctness findings count remains zero. No builds, mutations, source edits, or other reviewer-file reads were performed. The same-review follow-up remains below 60 turns / 250k peak context; no budget breach observed.
