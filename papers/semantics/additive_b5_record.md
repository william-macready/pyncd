# B5 bounded multi-writer scatter: execution record

## Authority and scope

The owner requested implementation on 2026-10-27, superseding the planning-only
restriction in [the plan](additive_b5_plan.md) and
[its authoring record](additive_b5_plan_record.md). Base:
`d62c885707fe10e0679d85b8cdbcf8d7d6e1e9a9`.
Process: Full. The controller applies the four verified patches directly;
separate reviewer contexts cover the two required whole-branch lenses.

B5 admits bounded top-level real/max-plus/min-plus scatter groups with exact
post-inference shape equality. All-bare groups keep UID agreement. Predicate,
explicit-constant and multi-axis groups remain refused. No raw checker,
arithmetic, carrier, Core evaluator, scan capability or JAX kernel is widened.

## Preflight and task evidence

- Isolated worktree prepared using `new-slice`, fast-forwarded to local main.
- Mathlib cache: 8101 built / 8094 sources; 347 project oleans before refresh.
- Refreshed `LeanNCD`: green.
- Package verification: four ordered patches / 23 files, exact final code tree
  `45b78959139948adea38bb9e557858574be263e1`.
- Base pre-manifest check: all eight selected old strings unique.
- T1 API review: UID-normalized coefficients; only syntactic `.const` is excluded
  as constant. Existing extent arithmetic is unchanged. `LeanNCD` green.
- T2a review: obligations retain original writer order; source declarations
  rebuild cached environments; both writer constructors rename/rewrite;
  `compile_eq_physical_route` keeps its statement with the new refusal case.
  Native targeted gate (`LeanNCD`, `DSL.Pipeline.CollectTest`,
  `Eval.CollectEvalTest`, `Eval.Plan.CollectPlanTest`): green.
- T2b review: predictors restate coefficients, basis and extent independently;
  production preparation is confined to observation functions. Six value rows
  require actual `fourLegParity` and pinned running sorts. No blanket
  multi-writer allowance remains. Targeted oracle gate and combined
  `Tests JaxExperiment`: green.

Build and mutation logs live in the execution session's `files/` directory,
not in the repository. No failure, skipped target or mutation survival is
counted as success.

## Current acceptance measurements

SOURCE C1: 505 total, 222 with no predicted refusal, 195 with one, 88 with
multiple. Empty SOURCE refusal lists do not establish concrete acceptance.
The 216 scatter-bearing rows split into 117 multi-axis rows outside B5 and
99 shape5-only rows: 81 SOURCE-admitted rows are SHAPED-refused with
`sizeConflict`; 18 retain SOURCE refusals. Nine hand SHAPED rows comprise five
accepts and four shape refusals. `markedSquare` passes shape prediction but
still refuses its normalization marker at preparation.

Six mixed oracle rows compare global fibers, reference f64, checked f64 and
stratified Core values. Native f32 remains a separate exact-bit gate, not a
fifth oracle leg. Undeclared fallback is checked-native f32 evidence, not
reference f64 evidence. `fG` remains `scanAxisNotIter "a"` with zero conditions;
its equal-extent stride twin has actual four-leg parity.

## Fixture and recurring-defect audit

The case-by-class table in [plan section 4](additive_b5_plan.md#4-recurring-defect-audit-case--class)
is retained as the required/forbidden matrix. Its entry preconditions matter:
`writerGroups` includes only top-level plain assign/scatter groups;
`scanWriterConflict?` rejects scan/plain conflicts first, and
`validateScheduled` rebuilds the source environment before collecting.
Static rank equality precedes shape obligations. No new silently-ignored cell
is intended. The two final reviewers must check the unchanged siblings as well.

All 32 plan fixture families have compiled on the exact final code snapshot:

| Families | Observed gate / retained intent |
|---|---|
| F01-F06 | Three native legs: interleave, overlap, tropical holes, mixed both orders, diagonal; undeclared fallback only checked f32 |
| F07-F09 | Three native shape paths: exact mismatch payload, inference priority, writer 3 / dimension 1 |
| F10-F13 | Normalized cancellation, genuine two-axis/constant/predicate refusal, explicit-scatter fallback exclusion, B6 zero-scale vs empty source |
| F14-F17 | f64 `[2,0]` vs actual f32 `[1,0]`; scratch privacy; tropical cast; explicit route refusal |
| F18 | Four historical undeclared guard migrations, retaining scan-conflict priority |
| F19-F23 | SOURCE counts, 81 SHAPED corpus refusals, nine hand rows, marker honesty and independently restated extents |
| F24-F26 | Six mixed four-leg rows, true-refusal doctors, old fG refusal and stride twin parity |
| F27-F28 | Existing all-bare/single-writer, vote/cast, scan, storage and nonlinear controls green in combined Tests |
| F29 | Actual checked scatter/scatter/assign graph; `lowerPlan` and `generateForward` both refuse node 0 |
| F30-F32 | Inferred and unsized basis/source, read-free constants, predicate-neutral max/min casts, isolated undeclared fallback rank |

T3 native/boundary/JAX targeted gate is green. Before prose-only documentation
edits, every one of the 23 implemented source files matched its final snapshot
SHA-256. Both unfiltered manifest checks passed (8 pre / 16 post).
The early oracle run killed all four O01-O04 rows, each with expected failure,
byte-identical restoration and restored-green build.

## Documentation sweep

Literal plan commands produced 1858 numeric hits, 161 typed-error hits, 922
boundary-vocabulary hits and 15 discoverability hits before documentation edits;
complete outputs are retained as execution-session logs.

- Current boundary guidance updated in DSL, Eval, Eval/Plan and Semantics
  instruction nodes, plus the top-level leanncd entry map and backend inventory.
- `CollectorShape` is reachable through existing `Eval.Eval` and plan compiler
  imports from `LeanNCD`; no extra umbrella import was added.
- The production decision note now states bounded B5, preserving S1/S3 history.
  Oracle design/plan/facts/record, S2 design and B6 record carry supersession
  links rather than rewriting historical observations.
- Old C1 141/258/106 claims occur in the oracle history/ledgers and the B5
  design's base recount. They remain historical, with current measurements in
  this record and the oracle record's supersession banner. Unrelated numeric
  hits include IEEE bit patterns/16777216, values, commit IDs, section/line
  references, earlier mutation counts, budgets and prior build job totals;
  they do not represent C1 acceptance claims and are left unchanged.
- Current numbers retain the SOURCE/SHAPED distinction and `markedSquare`
  limitation. Neither the 216 scatter-bearing rows nor the 81 source-admitted
  rows is described as concrete native acceptance.

## Final validation gates

- Both final manifests passed on guard-fixed source: **8/8 pre, 16/16 post**.
  Every actual mutation failed with its required `expect` strings, restored
  byte-identically and rebuilt green. Both stock commands exited 0; final fix
  checkout clean. [Per-row results](additive_b5_mutation_results.md).
- The original activation's 24 cycles and early four oracle cycles also passed;
  repeated observations are not counted as new distinct mutants.
- Controller final `Tests JaxExperiment`: green, 8839 jobs.
- Controller default full build: green, 8838 jobs.
- Exact source comparison: integrated `b5028559` matches the final mutation
  checkout's `8a8505d1` throughout `leanncd/`. No mutated source remained.
- Two whole-branch review lenses completed; oracle approved without findings,
  shape's sole P2 finding was reproduced, fixed, mutation-tested and adjudicated
  by the controller's complete two-file delta review.
- Whitespace and local document-link checks passed. No target/guard silently
  skipped and no unresolved load-bearing finding or parked B5-reachable issue.

All implementation gates are satisfied. Local integration follows the standing
merge authorization; no remote push is authorized. Git history records the
actual local merge, rather than predicting its hash in this pre-merge record.

## Final review checkpoint

The shape/acceptance reviewer completed the whole-branch sibling audit and
reported one P2 finding: a direct B5 schedule can mix a proper scatter with a
top-level `.assign` carrying an iteration slot. The B5 early return bypasses the
legacy ordinary-bare slot guard; the extent obligation can then describe a
different shape from reference assignment materialization. This is within B5's
exact-shape contract, not an invitation to widen scan support.

A separate isolated fix checkout is being prepared for a test-first reproduction,
ordinary-bare assignment guard and accept-neighbor/mutation checks. Original
24-row mutation runs continue sequentially on the implementation checkout; the
read-only reviewers use a separate immutable committed snapshot. No mutation
success or final approval is inferred from this static finding.

The independent oracle/false-success whole-branch review approved `7432b162`
with no high-confidence findings. It audited the independent predictor,
SOURCE/SHAPED limits, actual four-leg rows, refusal doctors, native precision
and payload controls, JAX pre-emission rejection, unchanged immediate
preconditions and all 24 mutation entries. It did not rerun or claim the pending
controller cycles. The shape finding still requires its isolated fix and
review-delta adjudication before integration.

### Shape finding adjudicated

Fix commit `8a8505d19d7242d3a1c62aa13d0a2fbb86b02307` observed the actual
reference truncation `[11,22]` from inputs containing a third value `99`;
checked preparation instead reported an iteration-slot capability refusal.
The reachable `iterNext` sibling had an extent mismatch, not truncation.
New tests first failed, then passed with exact `multiWriterScatter "S"`
compile/source-invariant errors in both native entries.

The controller reviewed the complete two-file fix delta: only B5 assignment
writers gain the ordinary-free/freeNorm precondition, while the existing
unlowered affine/diagonal refusal remains. An all-assignment neighbor retains
`writerShapeMismatch "S" 2 0`; legal direct free/freeNorm neighbors compare exact
bits `[11,22]` / `[10.25,20.75]`. Native/boundary targets passed, and the stock
`B5-assignment-ordinary-slots` cycle removed only the new predicate, failed only
the new guards, restored both source hashes and rebuilt green.

The finding is adjudicated as fixed, without changing standalone iteration or
scan policy. Both original manifests still pass unfiltered applicability checks
on this fixed source. The controller is rerunning all 24 entries on the fixed
commit in its separate exclusive checkout; original activation runs are
retained as intermediate evidence, not substituted for final-tree validation.
No new manifest entry was added for this Direct-path guard fix.

## Measured execution budget and process deviations

SDK `session.usage_record` accounting at final-validation close-out measured
**13,430,961 cumulative input tokens (13.431M)** across this controller and
three child contexts, well below the execution ceiling of approximately 175M.
`inputTokens` already includes cache tokens; caches were not added again.
The Claude transcript script found no transcript, so SDK events were used.
The separate authoring record's measured 33.46M is not folded into this execution
figure. Administrative record/commit/merge calls after this checkpoint add a
small further amount and are not represented as already measured.

| Context / SDK source session | API calls at checkpoint | Cumulative input | Peak input |
|---|---:|---:|---:|
| Controller `867b0edd-6fc7-4048-8541-11d89d3e347e` | 60 | 7,463,066 | 178,929 |
| Child `3e9b516f-3c21-47e9-a5fa-1e6a4478b3bf` | 30 | 2,668,174 | 156,402 |
| Child `2bb2ebe2-7989-4649-83c7-9adeab49f000` | 25 | 1,659,222 | 115,583 |
| Child `3c185c6f-5ebe-4e02-ab0b-b17eabbbc2fc` | 34 | 1,640,499 | 64,312 |

Reviewers reported 25 and 28 tool-call turns; the bounded fixer reported 37
assistant messages, all within their 45-turn budgets. SDK calls and reported
tool/message counts have different denominators. All measured contexts are below
250k. The controller reaches the approximately 60-call target at this checkpoint
and exceeds it modestly during administrative close-out; that process overrun is
explicit, not hidden. Long compiler invalidations and sequential mutations were
waited on rather than converted into speculative passes.

The controller replayed verified patches directly instead of spending separate
implementer contexts reapplying them. Final reviews ran on an immutable detached
snapshot while mutation runs owned their separate source checkout. The required
Direct guard fix used a third isolated checkout; final manifests were fully rerun
there and the controller proved source equality with the integration checkout.
These scheduling changes preserve all semantic, mutation and final build gates.
