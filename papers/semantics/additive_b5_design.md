# B5: bounded multi-writer scatter

Historical design baseline. The owner subsequently authorized implementation;
see [the B5 execution record](additive_b5_record.md) for current behavior.

**Recommendations approved by the owner on 2026-10-27; not an implementation plan.**
Approval authorizes writing the B5 plan, not executing it. Read against local main
`d62c8857` on 2026-10-27. No production changes, prototype, or Lean runs accompany
this note. Current-behavior claims below come from the linked source; the C1
recount is a Python enumeration of its writer product and independently restated
vote/refusal rules, matching the existing count guards.

## 1. Options and recommendation

Overwrite, destination-sort collection, tropical max-plus/min-plus, B6 errors,
and cast decision A are settled. The choice is the admission boundary:

| Option | Newly accepted groups | Tradeoff |
| --- | --- | --- |
| Real-only first | Supported scatter geometry, real destination, exact shape agreement | Smaller value matrix, but repeats the collector/oracle work for tropical sorts |
| **Bounded B5 (recommended)** | Real, max-plus, min-plus; scatter + scatter, affine + affine, affine + bare, and diagonal writers, subject to the rules below | Reuses existing arithmetic/checkers; changes collection, shape validation, and oracle predictions together |
| Declared shape is an arbitrary containing box | Also accepts writers whose derived extents differ, provided all writes fit the declaration | Departs from S3's equality rule; requires changing raw plan extent validation and inference, not just collection |
| All scatter forms/backends | Also predicate, constant-slot, multi-axis rows, routed bridge and JAX execution | Several independent capability extensions; not one bounded B5 slice |

Recommend **one real-and-tropical slice**, not a real implementation followed by
a tropical port: the workers already implement both. Split predicate scatter,
multi-axis/constant-slot admission, arbitrary containing shapes, and executable
JAX scatter into later owner-approved slices. Do not write their plans now.

### Exact proposed scope

- Only top-level groups of plain statements, after ordinary source lowering.
  An affine source assignment becomes a scatter; an explicit scatter with bare
  slots is also eligible.
- Allowed scatter slots: bare/free slots and affine expressions other than the
  explicit `.const` constructor, with at most one nonzero source-axis coefficient
  **after coefficient normalization**, matching the existing checked scatter
  geometry. In particular, keep the existing syntactic distinction between
  `.const` and `0*a`: the latter reaches B6, not a constant-slot capability
  rejection. Repeated free axes in a writer (diagonal placement) are allowed.
  These are geometry permissions, not an exemption from range checking.
- The destination is real, max-plus, or min-plus, with one agreed running sort.
  Different input tensor sorts remain legal under the existing cast table;
  conflicting writer votes do not become a heterogeneous destination.
- Keep `multiWriterScatter` for groups outside this bounded geometry, including
  predicate destinations and explicit-constant/multi-axis placements. Share the production
  geometry classification with the existing preflight rather than maintaining
  two subtly different predicates.
- Existing all-bare groups keep their UID-agreement rule. Existing single-writer
  programs are unchanged, including their backend-specific capabilities.
  Keep scan-node conflicts, in-scan collection, nonlinear scatter, unlowered
  direct-schedule scatter-shaped assignments, mixed storage, and complex storage
  refused at their existing boundaries.

Evidence: [checkWriterGroup / desugarMultiWriters](../../leanncd/LeanNCD/DSL/Pipeline/Collect.lean),
[lowerArith / reclassifyLHSSlot](../../leanncd/LeanNCD/DSL/Pipeline/Structural.lean),
[checkScatterLHSSlot / capabilityPreflight](../../leanncd/LeanNCD/Eval/Plan/Compile.lean).
The brief's `scatterInScan` wording needs one qualification:
[CompileError.scatterInScan](../../leanncd/LeanNCD/Exec/Uid.lean) is now a
**producerless compatibility constructor**, not a blanket live guard. Retain it
and all current scan capability refusals; do not ban already-admitted scan
placements or implement F3.

## 2. Shape rule: strict S3 equality, scoped to newly admitted groups

For a B5 group defining T:

1. If T has a tensor-bearing declaration, its axes, in declaration order,
   provide the collector's coordinate basis. Their UIDs must be pairwise distinct:
   repeated declaration axes would make the collector diagonal rather than a
   full-domain assignment. Refuse that case in B5; diagonal *writers* can instead
   target a square tensor declared on two distinct axes of equal extent.
2. Otherwise use the first **ordinary bare assign writer**, in schedule order,
   as the collector basis. An explicit `.scatter`, even with bare slots, is not
   an assign for this purpose.
3. If there is no declaration and no such assign, raise the proposed
   `CompileError.multiWriterNeedsDeclaredShape T`. A declaration means an axis
   basis, not new syntax: its sizes may be pinned or inferred. An unresolved
   extent remains a sizing error, never a default.
4. After sizing, let D be the extents of the collector basis. Each writer must
   have exactly that rank and shape: a bare assign's slot sizes equal D; a
   scatter's per-slot `LHSSlot.outExtent` equals D, position by position.
   Compare concrete extents, **not source-axis UID equality**, for these groups.
5. No union of extents, truncation, broadcast, or padding to a larger declared
   box. Equal shape does not imply full coverage: holes contain the agreed
   sort's `0_K`. Every actual write must still be in range.

This adopts [decision note B5/S3](additive_production_decision_note.md)'s shape
proposal, with an explicit bounded collector-basis restriction. It deliberately
does not retrofit declared-size checks onto existing all-bare/single-writer
programs. A larger declared containing box is the alternative above, not an
unstated interpretation of "agreement."

Today [scatterOutputShapes / inferAxisSizesCore](../../leanncd/LeanNCD/Eval/SizeInfer.lean)
propagate scatter shapes through reads, but ordinary assignment outputs are not
shape sources. Collector reads can expose some conflicts as `sizeConflict`;
they are **not a substitute** for an explicit post-inference comparison of every
writer and the declaration. Preserve source-group shape obligations through the
desugar, and discharge the same obligations in reference evaluation and plan
preparation before execution/emission. Add a typed extent-mismatch diagnostic
carrying public tensor, 1-based writer, dimension, expected and actual extent;
do not overload the old UID-based `writerShapeMismatch` meaning. Existing
inference failures may occur first; do not promise a new global error priority.

## 3. Collector, sorts, and B6

Keep the current mechanism: writer k computes private `T#k`; insert one ordinary
bare collector after the last writer; readers wait for all publications; hide
all private results. Change the rename arm to handle **both** assign and scatter,
and build the collector from the selected basis, not the first writer's affine
slots (`collectorStmt` currently uses `producerSlots` and `toReadIdx`, which
cannot manufacture a destination basis from affine slots).

Each scratch is a complete tensor of shape D, with the destination's storage
and agreed running algebra. A scatter scratch is zero-filled with `0_K` and
performs its own source-coordinate collision fold before collection. It needs
its own placement and range check, not just a collector check. Clone declared
destination metadata as today; retain group shape obligations also for the
undeclared mixed case.

Strict equality means the scratch's existing derived extent must already be D.
There is **no need to override `ScatterPlan.destShape` or relax
`checkScatterCore`**. Honoring the declaration here means rejecting disagreement,
not making every single-writer scatter use declared extents.
[evalPlain / evalScheduled](../../leanncd/LeanNCD/Eval/Eval.lean) and
[scatterPlacementOrFail / prepareEvalPlan](../../leanncd/LeanNCD/Eval/Plan/Compile.lean)
are the two post-sizing orchestration surfaces.

Keep B6 intact: [evalScatter](../../leanncd/LeanNCD/Eval/Scatter.lean) errors on an
actual out-of-range write; [checkScatterCore](../../leanncd/LeanNCD/Eval/Plan/Check.lean)
checks every extent before its corner-range pass, with an empty source box
vacuously in range. A zero coefficient is not permission to drop a bad write.
Diagnostics from private writers should identify the public tensor and writer.

**Votes and casts carry over as rules, not unchanged plumbing.**
[writerVotes / writerSort? / Stmt.isSortNeutral](../../leanncd/LeanNCD/DSL/Ast.lean)
already handle scatter statements. Non-neutral writers vote; neutral writers
abstain beside them; an all-neutral group votes by non-sum annotations. Keep
the current neutrality predicate, including its non-neutral multi-axis-slot
case. Rewrite an abstaining scatter's agg as well as an assign's: this changes
its constants, padding and bool-to-tropical read interpretation.

[scheduleAlgebras](../../leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean)
currently gathers only `.assign` writers for a multi-writer tropical entry.
Include admitted scatter writers so the **original writers and later readers**
are cast-checked under the group's sort. Keep decision A's direct-read
max-plus/min-plus and tropical-to-bool refusals, unary exemption and real-copy
bypass. Do not re-cast private scratch reads in the synthetic collector as if
they were new user casts; their values already have the agreed interpretation.

Real floating collection retains the current nested order: source-coordinate
fold per writer, then writer/schedule-order collection. Do not claim bitwise
invariance under writer permutations or equivalence to a flattened fold.

## 4. Backend boundary

| Surface | Required B5 work / unchanged refusal |
| --- | --- |
| Reference f64 | Scatter rename, agreed-agg rewrite, canonical collector, shared post-sizing shape obligations. Existing scatter worker already folds with destination algebra and B6 errors. Reference f32 refusal stays. |
| Checked f64 and f32 | Same collection/shape rule before plan emission; scratch signatures must equal D. Preserve `checkScatter`/`checkScatterF32` and all existing placement guards. |
| f32 algebra tables and dense workers | No new tables or arithmetic: [admittedAlgebraF32Max/Min](../../leanncd/LeanNCD/Eval/Plan/Check.lean) already carry tropical identities; [runDenseScatterWith](../../leanncd/LeanNCD/Eval/Plan/Dense.lean) serves both precisions. Add native f32 value/order pins, not f64-as-f32 evidence. |
| Routed DAG / categorical bridge | **Explicitly refuse newly enabled B5 groups at `route` for this cut.** [tensorAxes / slotWeave / toBrBaseP](../../leanncd/LeanNCD/DSL/Pipeline/Lowering.lean) omit affine output axes, deduplicate diagonal axes and label every scatter simply `.scatter`; [weaveToArrayType / realizeBrBaseP](../../leanncd/LeanNCD/Bridge/Realize.lean) use real dtype and an op string. Removing the shared refusal alone is not faithful bridge support. A B5-specific route gate is required safety work, not a general bridge redesign. |
| JAX / generated Python | Keep explicit unsupported-step/algebra errors; no kernel work. [lowerPlan / renderAffineNodesArray](../../leanncd/experiments/jax_bridge/EvalPlanCodegen.lean) reject scatter nodes, and tropical assignments are outside its support policy. [Python affine runtime](../../leanncd/experiments/jax_bridge/evalplan_affine_runtime.py) executes output-driven real tables, not scatter placement. Test refusal before Python emission. |

"Lockstep" means shared admission/shape/cast rules and value parity on the
supported native intersection, with explicit refusal elsewhere, not pretending
every backend gains executable scatter.

## 5. Oracle impact: an acceptance change, not a deleted refusal check

[OracleSortRules.predict](../../leanncd/test/Semantics/OracleSortRules.lean)
currently predicts `multiWriterScatter` for any multi-writer group containing
an explicit scatter, a non-bare slot, or repeated free UIDs. Its tropical entry
rule also excludes explicit scatter groups. Replace these with independently
stated B5 rules:

- A destination has one running sort from the existing independent vote rule.
- Eligible groups obey section 1's normalized geometry and section 2's
  declaration/bare-assign basis selection, distinct collector UIDs, rank and
  concrete extent equality. Predict missing-declaration and extent failures;
  retain `multiWriterScatter` only outside the bounded scope.
- An agreed tropical B5 group publishes its sort for source and destination cast
  checks, including explicit scatter writers. Do not call production's
  eligibility, extent, vote, collection, or shape-validation helpers.

The independent extent calculation must state the current stride-aligned
one-axis convention (including zero/empty cases), not use a naive maximum
written index or the legacy linear formula for every bias. Give the predictor
concrete axis/signature information for shape-stage checks. The current
`productionVerdict` observes only compilation plus `validateScheduled`; extend
the **observation**, using actual corpus input signatures and plan preparation,
to see post-inference shape failures. Do not compare a full acceptance
prediction against a source-only success.

### Recount and expected migrations

| Current pins | Consequence under the recommendation |
| --- | --- |
| Historical four guard sites: `CollectTest.c5`, `priorityError false`; `CollectEvalTest.j3`; `CollectPlanTest.nbScat` | All are **undeclared all-scatter**, so become `multiWriterNeedsDeclaredShape`, not accepted unchanged. Preserve these negative donors; add declared, correctly stored/data-bound acceptance twins. Keep `priorityError true`'s scan conflict. |
| `OracleMixedRefusalTest.d7Scatter`, `d7TwoAffine`, `d7AffineBare` | **All three are shape-correct acceptance candidates**: the affine donors declare extent 8 on `k`, not extent 4 on `a`. Move to value parity; update three typed-path `falseNativeFailure` contrasts and rebase doctored/split-leg refusal controls onto genuine remaining refusals. |
| `OracleSortRulesTest` C3's three D7 hand rows | Only plain + bare-slot scatter is shape-correct as written. The two affine rows declare `Y[a]` of extent 4 but produce extent 8: become shape refusals; add extent-8 acceptance twins. |
| Two supplemental diagonal rows in `OracleSortRulesTest` | Their declaration is 4 by 3, but placement is 4 by 4. Become shape refusals, not accepted unchanged; add square declarations on distinct destination UIDs. |
| C1: 505 programs, currently 141/258/106 with zero/one/multiple predicted refusals | **216** programs contain shape 4 or 5; **117** contain multi-axis shape 4 and stay outside this cut. The other **99** contain shape 5 without shape 4 and lose the blanket refusal, but their declared extent is 4 versus realized 8. None is automatically a new value row. Retain other applicable vote/nonlinearity refusals, recompute strict/member counts, `modelled`, strict coverage and C4 vacuity guards; add geometry-correct positive products. |
| `SourceDifferentialScatterTest.fG` | Not a clean B5 acceptance donor: its second slot is `.shift a 1`, which `reclassifyLHSSlot` refuses as `scanAxisNotIter`; its writer extents also disagree. Replace the B5 positive with equal-extent stride donors; pin the old syntax refusal honestly. |

Sources: [collector pins](../../leanncd/test/DSL/Pipeline/CollectTest.lean),
[reference pins](../../leanncd/test/Eval/CollectEvalTest.lean),
[three-native-leg pins](../../leanncd/test/Eval/Plan/CollectPlanTest.lean),
[mixed refusal rows](../../leanncd/test/Semantics/OracleMixedRefusalTest.lean),
[C1/C3/supplemental guards](../../leanncd/test/Semantics/OracleSortRulesTest.lean),
[fG](../../leanncd/test/Semantics/SourceDifferentialScatterTest.lean).
Thus "four fixtures flip" is not a current acceptance inventory.

Retire the blanket
[StructuralCondition.multiWriterScatter / detectConditions / confirms](../../leanncd/LeanNCD/Semantics/Source/Differential.lean)
allowance and its [NumericalProfile constructor](../../leanncd/LeanNCD/Semantics/Source/NumericalProfile.lean)
when migrating the real differential. Its confirmation currently matches
`scanAxisNotIter`, not the live collection refusal. Accepted B5 rows must reach
value comparison, never a known-difference shortcut. Remaining unsupported
programs need explicit refusal evidence. Leave the separate **single-writer**
`scatterExtentOverridesDeclared` condition and its existing scope alone.

For positive Source rows,
[compareMixedSource](../../leanncd/test/Semantics/OracleMixedDifferential.lean)
must predict acceptance and then compare **four value legs**: independent
`runMixed` global fibers, reference f64, checked f64, and stratified Core.
[runMixed](../../leanncd/test/Semantics/OracleMixedEval.lean) already combines
all writers by destination sort and checks write images against declared shapes;
[admitSourceAffine / admitSourceSorted](../../leanncd/LeanNCD/Semantics/Source/Admission.lean)
already admit sorted scatter structure. Expect reuse, not a new evaluator.
Require explicit `fourLegParity` assertions and independently pinned running
sorts. Core consumes predicted sorts and does not check cross-target scheduling;
non-finite intermediates can stop it. Choose finite dependencies, with tropical
holes only in final outputs, so three-leg/profile-excluded rows cannot satisfy
the B5 acceptance bar. f32 remains a separate native test leg, not a fifth
mixed-oracle leg. Source bool/unary/Iverson/affine-read/scan widening stays parked.

## 6. Verification bar, process and cost

**Full path** under [slice-plan section 0](../../.claude/skills/slice-plan/SKILL.md):
new accepted programs, shape authority and an independently predicted refusal
boundary. This note is the decision gate, not permission to start that pipeline.

Budget roughly **24-32 fixture families and 16-22 mutation rows**, with twins
sharing a family. A future plan must measure and finalize these counts:

| Rule to pin | Distinguishing fixture / mutation |
| --- | --- |
| Group shape authority | Declared all-scatter, missing declaration, undeclared scatter + bare in both orders; remove declaration requirement or select writer 1 instead of the first bare assign |
| Exact equality, not containment | Smaller and larger declaration; same-extent/different-UID mixed writers; rank mismatch and late-dimension mismatch; skip a writer/declaration comparison or accept `<=` |
| Full collector domain | Square diagonal writers, repeated declaration-UID refusal, sparse stride holes; reuse affine/diagonal writer slots for collector or drop an output dimension |
| Two collision levels and identities | Overlapping writers **and** contracted RHS source axes, max-negative/min-positive cases and holes; overwrite a scratch collision, drop a writer, sum a tropical collector, seed a hole with real zero |
| Neutrality and casts | Neutral affine copy beside a non-neutral tropical writer, both orders; conflicting non-neutral voters; tropical group readers; predicate-input casts in native tests; omit scatter rewrite or sort-map entry |
| B6 and empty domains | Bad zero coefficient / negative hand placement, in-range neighbors and empty source; suppress range error, use the wrong source box or reverse extent/range priority |
| Precision, order, visibility, refusal safety | Native f32 twins, order-sensitive real floats, a reader between source writers, private-name hiding/freshness, all-bare/single-writer controls, route/JAX refusal; reverse folds, publish early, leak scratch, remove a backend gate |
| Oracle actually tests acceptance | Three migrated mixed D7 shapes plus real/max/min overlap donors; doctored sort/refusal/value and Core-feed controls; retain blanket predictor refusal, bypass comparison, or feed Core from oracle |

Keep non-neutral sum/tropical and max/min conflicts, scan conflicts/local
duplicate producers, nonlinear scatter, unsupported placement/predicate
scatter, direct unlowered assignment, storage and cast refusals pinned. Test
each new diagnostic with its nearest accepted neighbor; do not weaken existing
raw-plan/B6 guards to make collection pass.

Suggested task boundaries, **not an execution plan**:

1. Shape/basis obligations and bounded eligibility, with shape/refusal donors.
2. Scatter desugar, neutral rewrite and sort-map integration, with native value
   donors and route safety gate. Shape and collection are one acceptance feature;
   neither should land alone as a language widening.
3. Independent predictor and staged corpus observation, begun alongside the
   production work; split predictor/corpora from four-leg value migrations if
   either exceeds three substantive work items per dispatch.
4. Precision/range/order fixtures and mutation completion; docs value/count
   sweep; two whole-branch review lenses (acceptance/shape, oracle independence).

Planning/prototype/authoring estimate **12-20M** cumulative input tokens;
implementation and fixtures **55-85M**; mutation/review/controller close-out
**15-25M**: **82-130M total**, explicitly an estimate, below the ~175M execution
ceiling. This is larger than an ~8.4M audit, but avoids spending another
oracle-sorts-sized (~95M) effort on new carriers/evaluators. New bridge/JAX
kernels or arbitrary containing extents invalidate this estimate. Keep
dispatches below ~60 turns/~250k peak context; split fixtures from production
when necessary. The eventual final gate is controller-run full `Tests` and
`JaxExperiment` builds through `bash leanncd/scripts/lake-build.sh
<checkout>/leanncd [target]`, all planned mutation cycles, and both whole-branch
reviews. No builds are needed for this documentation-only decision gate.

Parked: general bridge scatter shape/algebra fidelity is not needed beyond the
B5 refusal gate (roughly an audit plus its own Full slice); predicate or
multi-axis scatter and JAX kernels each need a separately sized capability
slice. In-scan collection/F3 remain separate; no repair is included here.

## 7. Owner decisions (approved 2026-10-27)

1. Bounded **real + both tropical** B5, retaining the other scatter
   capability refusals; not the real-only cut.
2. **Strict realized-shape equality**, declaration required only without
   a bare assign basis, and distinct collector-axis UIDs; no arbitrary containing
   declared box in this slice.
3. **Native execution plus four-leg oracle coverage**, with explicit
   route/bridge and JAX/Python refusals rather than new executable backends.

Next: author the one B5 implementation plan. Execution remains a separate step.
