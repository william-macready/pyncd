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

## Remaining execution gates

All 24 controller-run mutation rows;
two whole-branch reviews; final `Tests JaxExperiment` and default full build;
measured accounting and local integration. No push is authorized.
