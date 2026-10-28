# B5 bounded multi-writer scatter — implementation plan

Execution authorized by the owner's 2026-10-27 implementation request.
The planning-status text below records the original handoff; current execution
evidence is in [the execution record](additive_b5_record.md).

**PLANNING ONLY. Execution is not authorized by this document.**
The owner approved the three recommendations in [the design](additive_b5_design.md)
on 2026-10-27, authorizing this plan, not implementation, commits, merge or push.
Base: `d62c885707fe10e0679d85b8cdbcf8d7d6e1e9a9`.
Authoring verification is complete; evidence and honest intermediate failures live
in [the record](additive_b5_plan_record.md). The package is execution-ready, not
execution-authorized.

**Process: Full** — new accepted programs and a shape-authority soundness surface
require an independent staged oracle. No new carrier, evaluator or backend.
One slice, four tasks; T2 has two bounded dispatches but ONE atomic integration unit.
The approved recommendations are fixed; a load-bearing contradiction blocks execution.

## 1. Execution contract

Every implementation, review and fix brief must open with this shell preamble:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use view for windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

- New execution worktree only, using `new-slice` and `prepare-worktree.sh`.
  This public planning checkout is NOT the execution worktree.
- Resolve `<worktree>` to its actual absolute path in every brief before dispatch.
  Each command below is a template, not an instruction to run in the planning checkout.
- Read symbols with `rg -n`; open 40–60-line, question-driven source windows.
  No whole-file reads of large modules. Read only the task's patch and symbols.
- Maximum three substantive work items per dispatch, ≤60 turns, peak ≤250k.
  Report actual usage and any breach. No nested delegation.
- Independent SOURCE/SHAPED verification is scheduled at T2b, before final native
  regression closure; do not postpone oracle work to documentation.
- Apply patches in order with `git apply --check` before `git apply`. The assets
  are mechanically split from code compiled in real modules/namespaces; don't
  transcribe Lean from prose. This plan has no Lean code fences.
- No production implementation is applied to public `leanncd/` during authoring.
  Replay/mutation work must wait for the controller's exclusive-checkout handoff.
- No admissions, changed language rule, relaxed raw-plan check or changed arithmetic
  is an acceptable way to obtain green.

## 2. Fixed semantics and exclusions

1. Newly admit top-level plain multi-writer groups after source lowering, for real,
   max-plus and min-plus destinations with one agreed running sort.
2. Share production `scatterAffineClass`/`LHSSlot.boundedScatter` with checked
   geometry: normalize coefficients by UID; at most one nonzero coefficient.
   Explicit syntactic `.const` is excluded; zero-coefficient affine syntax remains
   source-eligible and reaches unchanged B6 checks. Bare/free and diagonal writers
   are eligible. Source eligibility is not full backend acceptance.
3. Keep `multiWriterScatter` for predicate destinations, explicit constants,
   multi-axis placements, and direct unlowered scatter-shaped `.assign`.
4. A tensor-bearing declaration supplies the ordered collector basis. Its UIDs must
   be distinct, else `multiWriterRepeatedBasis T`. Without one, use the first
   ordinary bare ASSIGN in schedule order, not an explicit bare-slot scatter.
   If none exists: `multiWriterNeedsDeclaredShape T`.
5. After inference, every writer's rank/realized extents must equal the basis,
   positionwise; no containing box, padding, truncation or union rule.
   Static rank uses existing `rankMismatch`; shared `checkCollectorShapes` uses
   existing `LHSSlot.outExtent`. Retain obligations across desugaring in
   `CheckedScheduledProgram.shapeObligations`.
6. New typed `ShapeError.writerExtentMismatch T writer dimension expected actual`:
   writer is 1-based schedule order; dimension is 0-based. Existing inference
   failures can win first; no new global diagnostic-priority promise.
7. Rename assign AND scatter writers to private `T#k`, clone metadata, rewrite
   neutral scatter aggregation, then insert one full-domain bare collector after
   the last writer. Hide private results; readers wait for all publications.
8. Each scratch folds its own collisions, then the collector folds writers in
   schedule order with the agreed algebra. Holes use its additive identity.
   Preserve nested floating-point order; no permutation/flattening claim.
9. Include scatter groups in source `scheduleAlgebras`, so original writer/reader
   casts use agreed tropical sorts. Keep all cast decision A rules.
10. Reference f64 and checked f64/f32 execute the supported intersection.
    Undeclared fallback evidence is checked-native f32: reference storage defaults
    do not permit f64 fallback evidence. Adding a declaration would change the case.
11. Public `route` explicitly refuses newly enabled B5. Preserve the statement of
    `Bridge.Agreement.compile_eq_physical_route` with a real new match case.
    JAX/Python keep unsupported-step/algebra refusals, before emission.

Unchanged: all-bare UID agreement; single-writer rules; raw `ScatterPlan` extent/
range checks; dense workers and algebra tables; cast decisions; storage policy;
scan conflicts/local duplicate producers; unsupported nonlinear scatter.
`scatterInScan` is a producerless compatibility constructor, not a new blanket
scan guard. Do not implement F3 or change existing accepted scan placements.
No Core/carrier/mixed-evaluator changes; no f32 fifth oracle leg; no Source
bool/unary/Iverson/nonlinear/affine-read/scan-value widening.
The separate single-writer `scatterExtentOverridesDeclared` condition stays.

## 3. Assets and replay

Paths are relative to `papers/semantics/additive_b5_patches/`:

| Order | Asset | Files | SHA-256 |
|---|---|---:|---|
| 1 | [T1-api.patch](additive_b5_patches/T1-api.patch) | 2 | `be88761570db8a477d590cad687f606867fc6982d48dd6fa82cfb07f2c231bf5` |
| 2 | [T2a-native-activation.patch](additive_b5_patches/T2a-native-activation.patch) | 11 | `b503bbad4d22c6ebbc60acd42a96ee8abe59e9eb738f26cc5afafb019c684dec` |
| 3 | [T2b-independent-oracle.patch](additive_b5_patches/T2b-independent-oracle.patch) | 6 | `9ea0b90d88286e6bd67f154d568668d1810e520665c03371b3f2c6b0549b1509` |
| 4 | [T3-native-boundary-tests.patch](additive_b5_patches/T3-native-boundary-tests.patch) | 4 | `a3b596f7cc3f477ed2859e639b92503be9bceb84c543831842370813eec1025d` |

[snapshots.json](additive_b5_patches/snapshots.json) is authoritative for exact
file lists, input artifact hashes, intermediate tree IDs and final per-file hashes.
[assemble.py](additive_b5_patches/assemble.py) uses a dedicated index and object
snapshots: no public source checkout or ordinary index writes. Its ordered replay
checks each patch and exact final tree, not compilation of intermediate stages.
Final code tree: `45b78959139948adea38bb9e557858574be263e1`,23 files.
Closure and isolated fallback-rank increments were applied after boundary
registration before mechanically generating T3, including its JAX fixture path.

Preflight package verification, in a checkout containing this package and the base:

```text
python3 <worktree>/papers/semantics/additive_b5_patches/assemble.py --verify
/usr/bin/git -C <worktree> diff --check
```

Final manifests are [additive_b5_mutations.json](additive_b5_mutations.json)
(8 unchanged base mutation sites) and
[additive_b5_mutations_post.json](additive_b5_mutations_post.json)
(16 new/changed sites). All24 rows have observed semantic `expect` strings.
Unfiltered stock checks passed pre on base, and pre/post on the exact final replay.
M16-FIX replaces the initial surviving M16; it is not an additional row.
Never count a setup failure, survival, provisional instrumented cycle or mere
old-string uniqueness as a killed mutation.

## 4. Recurring-defect audit: case × class

Legend: **R** required semantics/check; **F** forbidden, fail loudly;
**S** silently ignored (unacceptable if introduced); **N** not applicable because
the case has already stopped. Source column is before lowering; direct is after
`validateScheduled` on the original schedule; shape is after inference.
R/F describe required behavior, not a claim that every hypothetical combination
has already been run. Retain the table with actual fixture/cycle evidence at T3.

| Case / class | Source `.assign` | Source `.scatter` | Direct schedule | Post-infer native | route | JAX |
|---|---|---|---|---|---|---|
| Ordinary all-bare / single writer | R legacy | R legacy single scatter | R legacy, no B5 obligations | R legacy | R legacy capability | R legacy policy |
| Bounded affine or diagonal B5 | R lower to scatter | R bounded group | R scatter; F unlowered scatter-shaped assign | R exact equality, own B6 | F B5 gate | F scatter step |
| Explicit bare-slot scatter B5 | N | R with basis | R; NOT fallback assign | R equality | F B5 | F scatter step |
| Declared distinct basis | R declaration order | R declaration order | R rebuild source env, retain obligations | R each writer/slot | F B5 | F B5 |
| Undeclared mixed ordinary bare assign | R first bare assign, either order | R beside that assign | R distinguish statement constructors | R checked f32; F reference f32 | F B5 | F unsupported policy |
| Undeclared all-scatter | F missing declaration | F missing declaration | F missing declaration | N | F | N |
| Repeated basis UIDs / rank mismatch | F basis/rank | F basis/rank | F basis/rank | N | F | N |
| Predicate / explicit const / >1 normalized axis B5 | F outside B5 | F outside B5 | F `multiWriterScatter` | N | F | N |
| Canceled coefficients / zero affine coefficient | R normalized / B6 | R normalized / B6 | R same shared class | R range, empty-domain rules | F B5 | F scatter |
| Nonlinear affine/diagonal placement | F source nonlin gate | F source nonlin gate | F checked preflight; F reference scatter worker | N, never drop nonlin | F physicalization/B5 | F unsupported |
| Neutral copy / explicit tropical writer | R preserve votes | R rewrite abstainer | R original sort map/casts | R tropical fill and two folds | F B5 | F scatter/algebra |
| Conflicting non-neutral voters | F algebra | F algebra | F algebra | N | F | N |
| User cast vs synthetic scratch read | R decision A | R decision A | R source casts, not a second user cast | R agreed scratch interpretation | F B5 | F unsupported |
| Scan/plain conflict or scan-local duplicate | F existing gates | F existing gates | F existing gates | N | F existing gates | F existing policy |
| Uniform f32 / mixed / complex storage | R native f32; F mixed/complex | same | R native f32; F reference f32/mixed/complex | R native32 only | F B5 | F storage/step policy |
| Private result / user freshness collision | R hide / F collision | same | R both rename arms | R hide both precisions | F B5 | N |

No newly introduced S cell is permitted. An audit discovery is recorded with its
entry/call-site preconditions, not patched speculatively. A genuine pre-existing
side issue not required by B5 is parked with cost; a B5-reachable silent cell is
load-bearing and blocks close-out.

Sibling functions to audit, not just changed hunks:
`slotsBecomeScatter`, `producerSlots`, `Stmt.withAgg`, `writerVotes`,
`Stmt.isSortNeutral` @ `leanncd/LeanNCD/DSL/Ast.lean`;
`checkScatterNonlin`, `lowerArith`, `checkScheduledDtypes`, `checkScheduledReadRanks`
@ `leanncd/LeanNCD/DSL/Pipeline/Structural.lean`;
`checkWriterGroup`, `collectorStmt`, `desugarMultiWriters` @
`leanncd/LeanNCD/DSL/Pipeline/Collect.lean`;
`scheduleAlgebras`, `checkSortCasts`, `validateScheduled` @
`leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean`;
`evalPlain`, `evalScheduled` @ `leanncd/LeanNCD/Eval/Eval.lean`;
`evalScatter` @ `leanncd/LeanNCD/Eval/Scatter.lean`;
`checkStmt`, `checkScanBlockStmt`, `capabilityPreflight`, `prepareEvalPlan`
@ `leanncd/LeanNCD/Eval/Plan/Compile.lean`;
`checkScatterCore` @ `leanncd/LeanNCD/Eval/Plan/Check.lean`;
`route` @ `leanncd/LeanNCD/DSL/Pipeline/Lowering.lean`;
`physicalizeForRoute` @ `leanncd/LeanNCD/DSL/Pipeline/RouteFragments.lean`;
`lowerPlan`, `renderAffineNodesArray` @
`leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`.
The shared native geometry does not license oracle calls to production helpers.

## 5. Fixture ledger and risk units

A family groups twins sharing a semantic purpose/build cycle, not individual
guards. The final inventory is **32 families** below; inherited controls are
distinguished from new B5 rows. All closure observations and pins are compiled
in the exact final replay; no extra fixture gate remains pending.
Native symbols are in `leanncd/test/Eval/Plan/B5NativeTest.lean` unless noted.

| ID | Family; donor → change | Required observation / retained intent |
|---|---|---|
| F01 | `CollectEvalTest.j3` / `CollectPlanTest.nbScat` → declared `interleave` | all three native legs `[-5,-7,-2,-3]` |
| F02 | `interleave` → same `2*i` placements, `overlap` | `[-12,0,-5,0]`, not overwrite |
| F03 | `overlap` → contracted `tropical`, max→min `tropMin` | max `[-5,-inf,-2,-inf]`; min `[-7,+inf,-3,+inf]` |
| F04 | `interleave` → second bare writer `mixed`; reverse | `[5,20,28,40]` both orders |
| F05 | `mixed` → remove S declaration; reverse | checked f32 same values; NOT reference f64 evidence |
| F06 | `overlap` → square `diagonal`; repeat declared UID | `[-12,0,0,-5]`; repeated-basis constructor |
| F07 | `mixed` → independent bare j=3, `bareMismatch` | `writerExtentMismatch "S" 2 0 4 3`, three native legs |
| F08 | `interleave` → declared k=5, `declaredMismatch` | existing `sizeConflict 2 5 4` wins, three legs |
| F09 | `mixed` → two equal matrix scatters then bare matrix, `lateMismatch` in boundary module | `writerExtentMismatch "S" 3 1 3 2`, three legs |
| F10 | `overlap` → canceled coefficients `cancellation`; make two genuine axes `twoAxes` | normalized acceptance vs geometry refusal, boundary module |
| F11 | `overlap` → explicit `.const`; `interleave` → predicate destination | both `multiWriterScatter`, boundary module |
| F12 | undeclared `mixed` → explicit bare scatter `bareScatterFallback` | missing declaration, boundary module |
| F13 | zero-scale donor → `zeroScale`, then source size0 `emptySource` | unchanged B6 failure vs empty success |
| F14 | `overlap` → three cancellation-sensitive contributions `orderPin` | f64 `[2,0]`, actual f32 `[1,0]` |
| F15 | `interleave` / existing `CollectPlanTest.h1` hiding donor; change checked privacy helper to `ref64` in `referenceScratchPrivate` | private slots stay private, materialize only S; repaired M16 isolated reference privacy |
| F16 | `tropical` → min reader `badCast`; retain cast decision A controls | `sortCastUnsupported "R" "S"`; don't weaken unary/real-copy neighbors |
| F17 | `interleave` → `routeError` | `multiWriterScatter "S"` at route, not fake bridge parity |
| F18 | four old guard sites; leave source undeclared | missing-declaration migration; `priorityError true` unchanged |
| F19 | `OracleSortRulesTest` C1 writer product | SOURCE counts 222/195/88, total505 |
| F20 | C1 shape5-only source-admitted subset | 81 SHAPED `sizeConflict`; 18 other SOURCE refusals retained |
| F21 | C3 affine donors / rectangular diagonal donors → extent8/square twins | 9 SHAPED hand rows: 5 accepts +4 shape refusals |
| F22 | square free/freeNorm donor `markedSquare` → de-mark second slot | shape passes but marked identity later refuses `unmarkedReductionAxis "Y#1" 1` |
| F23 | oracle stride2 extent donor → offsets1/3, cancellation, missing raw axis, zero coefficient | `[some 8,some 10,some 8,none,some 0]` |
| F24 | mixed three D7 donors + overlap real/max/min clones | six actual four-leg value/sort rows, section7 |
| F25 | D7 former refusal controls → true `multiAxis`/`constant` donors | preserve doctored refusal/cast and split-leg controls |
| F26 | `SourceDifferentialScatterTest.fG` → stride2 `fGStride` | old actual syntax refusal, 0 conditions; stride values `[1,1,2,2,3,3,4,4]` |
| F27 | existing all-bare `h1` → single `h1s`, predicate `h3` twins | legacy collection/single-writer behavior unchanged |
| F28 | retain `CollectPlanTest.nbMM/nbMMr`, `nbSM/nbMS`, `scanPlusMax`, `mixedUndeclY/mixedDeclF32Y`; `Eval.ScatterTest.f32Program` identity→relu storage twins | keep algebra, scan, storage, unsupported nonlinear boundaries |
| F29 | `interleave` geometry → local `b5ScatterScheduled` in JAX codegen fixture file | public preparation yields scatter/scatter/assign; lowerPlan AND generateForward refuse `.unsupportedStep 0` before Python |
| F30 | `interleave` → `inferredBasis`; `overlap` → read-free `constantWriters` → unpin i, then k | inferred basis three-leg values unchanged; constants `[2,0,2,0]`; typed unsized source/basis, no default0 |
| F31 | `tropical` / `tropMin` → predicate B input, `predicateNeutral` / `predicateNeutralMin` | three actual native legs `[0,-inf,-2,-inf]` / `[0,+inf,2,+inf]` |
| F32 | `undeclare mixed` → double ONLY affine writer slots, retain bare rank1 fallback, `fallbackRankMismatch` | `rankMismatch "S" 1 2`; named pin isolates B5 basis-rank check, no declared-rank masking |

Retained B6 evidence was re-audited, not assumed: `ScatterCheckTest.boxCheck`
pins negative placement and nonempty/empty source boxes. Its two-dimensional
extent7/range-negative donor violates BOTH rules and pins dimension1 extent
failure before dimension0 range failure; its corrected-extent neighbour pins
the range error. `ScatterCompileTest.upsampleScatter`, `zeroCoeffProg`,
`zeroCoeffBiasProg`, and `ScatterTest.b6Run` retain source-box, stride and B6
payload controls. Exact constructions/observations are in the record.
Declared `rankMismatch` is only an inherited/source-rank neighbour; F32 is the
new B5-specific isolated rank proof. No enlarged global-priority claim is made.

| Task | Families / risk | Mutation rows | Dispatch work items |
|---|---|---:|---|
| T1 API | API support; no independent new fixture family | 0 now; geometry rows exercised after T3 | 1 |
| T2a native activation | F18 + production enabling F01–F17, F27–F28 | deferred to T3 targets | 3 |
| T2b independent oracle | F19–F26: 8 families; 81 corpus rows,9 hand rows,6 value rows within them | 4 oracle | 3 |
| T3 native/boundary closure | F01–F17,F29–F32:21 families +F27–F28 inherited review | 20 native/closure/rank | 3 |
| T4 controller close-out | all32 families; no residual authoring gate | all24 re-run, no double count | 3 light/controller items |

The final total is **24 distinct observed killed mutation rows**:
17 native (repaired M16 replaces its survivor) +4 oracle +2 closure +1 rank.
This is3 more than the initial concrete21, and2 above the design's16–22 range.
The increase closes measured unsized/JAX/rank gaps, not capability scope.
Immutable-base classification gives8 pre /16 post, verified by stock checks.
Full assembled manifest reruns remain mandatory during implementation close-out.
F19/F20 counts do not imply 505 full-preparation or value successes.

## 6. Task briefs and dependencies

### T1 — additive API support

Prerequisite: execution authorization, prepared isolated worktree, base conflict
scan and green refreshed `LeanNCD`. Authoring verification gates are discharged.
Apply `T1-api.patch`. Files: precisely `DSL/Ast.lean`, `Exec/Uid.lean` under
`leanncd/LeanNCD/`. No collection admission yet.

One work item: shared geometry classification and typed compile diagnostics.
Symbols: `idxAffineForm`, `idxDensify`, `ScatterAffineClass`,
`scatterAffineClass`, `LHSSlot.boundedScatter` @
`leanncd/LeanNCD/DSL/Ast.lean`; `CompileError` @
`leanncd/LeanNCD/Exec/Uid.lean`.
Open 40–60-line windows around these identifiers only.

Validate:
```text
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD
```
Review the additive API and syntactic constant distinction. T1 is not an
acceptance feature or license to change raw extent arithmetic.

### T2 — atomic activation, two bounded dispatches

Dependency: T1. T2a and T2b are sequential on one integration worktree; their
reviews can reject one patch independently, but the activation MUST NOT land
without both. Never promise full Tests green between them.

#### T2a — production + historical pin migration

Apply `T2a-native-activation.patch`; exact eleven paths in snapshots.
Three substantive work items:
1. Bounded collection, ordered basis, retained obligations and neutral scatter
   rewrite — one coupled change, not separately landable admission/shape phases.
2. Shared post-inference discharge in reference/preparation, source sort map,
   route refusal and proof case.
3. Migrate only the four historical missing-declaration guard sites; preserve
   their negative source donors and the true scan-priority guard.

Symbols:
- `WriterGroup.needsB5`, `Decl.tensorAxes?`, `writerGroupBasis`,
  `CollectorShapeObligation`, `collectorShapeObligations`, `checkWriterGroup`,
  `collectorStmt`, `desugarMultiWriters` @ `DSL/Pipeline/Collect.lean`.
- `CheckedScheduledProgram`, `scheduleAlgebras`, `validateScheduled` @
  `DSL/Pipeline/ScheduledValidation.lean`.
- `checkCollectorShapes` @ `Eval/CollectorShape.lean`;
  `ShapeError`, `ShapeError.render` @ `Eval/Error.lean`;
  `evalScheduled` @ `Eval/Eval.lean`;
  `checkScatterAffineExpr`, `prepareEvalPlan` @ `Eval/Plan/Compile.lean`.
- `route` @ `DSL/Pipeline/Lowering.lean`;
  `compile_eq_physical_route` @ `Bridge/Agreement.lean`.
- `c5`, `priorityError` @ `test/DSL/Pipeline/CollectTest.lean`;
  `j3` @ `test/Eval/CollectEvalTest.lean`;
  `nbScat`, `refusedBy` @ `test/Eval/Plan/CollectPlanTest.lean`.

These task-local paths are relative to `leanncd/LeanNCD/` for production and
`leanncd/` for `test/`. Use 40–60-line windows, not whole-file reads.

Targeted gate:
```text
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD DSL.Pipeline.CollectTest Eval.CollectEvalTest Eval.Plan.CollectPlanTest
```
The native-only prototype's full Tests failed ONLY the two unmigrated oracle
targets. That is evidence of coupling, not a green baseline or acceptable final
failure. Do not register B5NativeTest/B5BoundaryTest until T3.
Review shape obligations, cached source-env rebuilding, and bridge proof without
changing theorem statements. Hand off precise tree/hash and targeted result.

#### T2b — independent oracle, early verification

Dependency: T2a. Apply `T2b-independent-oracle.patch`, exactly six paths.
At most three substantive work items:
1. Independently stated SOURCE and concrete SHAPED predictor + corpus migration.
2. Six mixed four-leg value/sort rows and true unsupported refusal controls.
3. Retire only the blanket Source allowance; pin fG refusal and fGStride parity.

Phase-2 symbols, with paths relative to `leanncd/`:
- `coefficients`, `normalized`, `bounded`, `declaredAxes`, `basis`, `needsB5`,
  `predict`, `predictedExtent`, `predictShaped`, `productionVerdict`,
  `productionShapedVerdict`, `agreesShaped` @ `test/Semantics/OracleSortRules.lean`.
- `sizesOf`, `signatureOf`, `shapedProblems`, `concreteC1`, `stagedRows`,
  `markedSquare` @ `test/Semantics/OracleSortRulesTest.lean`.
- `mixed`, `valueParity`, `overlap`, `multiAxis`, `constant`, `d7Scatter`,
  `d7TwoAffine`, `d7AffineBare` @ `test/Semantics/OracleMixedRefusalTest.lean`.
- `StructuralCondition` @ `LeanNCD/Semantics/Source/NumericalProfile.lean`;
  `detectConditions`, `confirms` @ `LeanNCD/Semantics/Source/Differential.lean`;
  `fG`, `fGStride` @ `test/Semantics/SourceDifferentialScatterTest.lean`.

Open 40–60-line windows. Do NOT read native checker internals to implement the
oracle; use the approved rules and independently observed fixtures. Review the
patch for forbidden calls to production eligibility/extent/vote/shape helpers.
Observation functions may invoke production preparation; prediction may not.

```text
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd Semantics.OracleSortRulesTest Semantics.OracleMixedRefusalTest Semantics.SourceDifferentialScatterTest
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd Tests JaxExperiment
```
Run four oracle manifest rows when the finalized manifest is available, with
actual `expect` checks. T2 integration closes only when both phases' targeted
and combined full gates pass. Do not hide a failure as a known difference.

### T3 — native precision, geometry and mutation closure

Dependency: complete T2. Apply `T3-native-boundary-tests.patch`. Files:
`leanncd/test/Eval/Plan/B5NativeTest.lean`,
`leanncd/test/Eval/Plan/B5BoundaryTest.lean`, `leanncd/lakefile.toml`,
`leanncd/experiments/jax_bridge/EvalPlanCodegen.lean` (fixtures only).
Register both modules together. The boundary module imports native helpers;
therefore it cannot precede B5NativeTest.

Three substantive work items:
1. Replay native value/shape/precision families, including original-order and
   reversed fallback, two collision levels, true f32 and private visibility.
2. Verify compiled boundary/payload, inferred/unsized/rank, bool-cast and JAX
   pre-emission pins; retain the inherited B6 order/source-box discriminators.
3. Run finalized20 native/closure/rank rows; restore/hash-check every mutation,
   adjudicate any setup failure/survival and require intended failure evidence.

Symbols: `interleave`, `overlap`, `tropical`, `tropMin`, `mixed`, `undeclare`,
`reverseWriters`, `diagonal`, `repeatedBasis`, `bareMismatch`, `declaredMismatch`,
`orderPin`, `zeroScale`, `zeroPlanCause`, `emptySource`, `agree`, `planShape32`,
`routeError`, `badCast` @ `leanncd/test/Eval/Plan/B5NativeTest.lean`;
`cancellation`, `twoAxes`, `explicitConstant`, `predicateDest`,
`bareScatterFallback`, `lateMismatch` @
`leanncd/test/Eval/Plan/B5BoundaryTest.lean`.
`inferredBasis`, `constantWriters`, `closureUnsizedSource`, `closureUnsizedBasis`,
`predicateNeutral`, `predicateNeutralMin`, `predicateAgree`,
`referenceScratchPrivate`, `fallbackRankMismatch`, `fallbackRankRejected` @
`leanncd/test/Eval/Plan/B5NativeTest.lean`;
`b5ScatterScheduled`, `b5ScatterPrepared`, `b5ScatterRejectedBeforeEmission` @
`leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`.
Use 40–60-line windows. Mutation sites and exact replacements are in manifests,
not rediscovered by the implementer.

```text
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd Eval.Plan.B5NativeTest Eval.Plan.B5BoundaryTest JaxExperiment
```

Payload witnesses: `bareMismatch` distinguishes extent from UID equality;
`lateMismatch` distinguishes writer3 from1/2 and dimension1 from0.
`cancellation` distinguishes normalized/raw axis counts; `bareScatterFallback`
distinguishes assign/scatter fallback. `orderPin` distinguishes native32 from
f64 and a changed fold order. No value-only row substitutes for these.
`declaredMismatch` demonstrates existing inference priority; it is NOT evidence
for every conceivable doubly-invalid ordering claim.

### T4 — controller documentation sweep and final gates

Dependency: T3 and finalized manifests; authoring coverage gates are adjudicated.
Controller work, not a heavyweight docs dispatch; three items:
1. Discoverability/ABI/proof documentation and value/count sweep below.
2. Two independent whole-branch review lenses over base-to-head plus the table:
   shape/acceptance soundness; oracle independence and false-success controls.
3. Controller-run manifests/full builds and measured close-out record.

Reviewer briefs carry this preamble, exact sections/symbols and 40–60-line
windows. Require incremental findings in the execution session workspace.
Fixes are one bounded dispatch per finding group, not a re-exploration of the
whole plan. Both reviewers must examine unchanged sibling call-site preconditions.
No final merge authorization is conferred by this authoring task.

## 7. Oracle acceptance bar and smoke criteria

SOURCE predictor remains `predict` / `productionVerdict`; SHAPED is the distinct
`predictShaped` / `productionShapedVerdict` / `agreesShaped` stage with concrete
sizes/signatures. It is not a universal model of full preparation.
C1:505 total; SOURCE 222/195/88. Scatter-bearing216 = multi-axis117 outside
the cut + shape5-only99. Of99,81 source-admit then SHAPED-refuse `sizeConflict`;
18 retain independent SOURCE refusals. Do not call all216 new accepts.
Hand SHAPED:9=5 accepts+4 shape refusals; markedSquare is a separate honesty pin.

Actual four-leg rows, each comparing independent global fibers, reference f64,
checked f64 and Core with finite dependencies:

| Row | Running sort | Observed final Y (oracle = Core, all four legs parity) |
|---|---|---|
| d7Scatter | maxPlus | `[9,8,17,27]` |
| d7TwoAffine | maxPlus | `[20,-inf,2,-inf,3,-inf,40,-inf]` |
| d7AffineBare | maxPlus | `[20,0,2,3,4,5,40,7]` |
| overlap sum | real | `[8,0,20,0,51,0,118,0]` |
| overlap max | maxPlus | `[20,-inf,7,-inf,17,-inf,40,-inf]` |
| overlap min | minPlus | `[-5,+inf,2,+inf,3,+inf,25,+inf]` |

Require actual `fourLegParity` assertions and independently pinned running sorts;
profile exclusion, three-leg runs or native failure cannot satisfy acceptance.
Keep Core feed/value-doctor controls and rehome refusal doctors onto genuine
multi-axis/constant donors. No Core output fed from the oracle.
The fG native refusal is `scanAxisNotIter "a"`, conditions0, not a B5 success.
fGStride is actual four-leg parity, conditions0.

Native smoke acceptance: declared interleave/overlap, max/min holes, diagonal,
mixed both orders and checked-f32 undeclared fallback with exact output bits.
Smoke rejection: missing basis; repeated basis; unsupported geometry/predicate;
bare mismatch typed payload; bad tropical cast; B6 zero-scale; route gate and
pre-Python JAX refusal. Reference zero-scale names private `S#1`; native32 uses
existing `invalidPlan (assign (nodeError 0 (scatterWriteOutOfRange 0 0 0 0)))`.
Do not promise an unprototyped typed B6 public-owner/writer payload.

## 8. Documentation commands and discoverability

Run literal value-greps from the execution worktree; exit1/no matches is a search
result, not a build failure. Inspect occurrences, not only file names:

```text
rg -n '141|258|106|222|195|88|216|117|99|81' <worktree>/papers <worktree>/leanncd --glob '*.md' --glob '*.lean'
rg -n 'multiWriterScatter|multiWriterNeedsDeclaredShape|multiWriterRepeatedBasis|writerExtentMismatch' <worktree> --glob '*.md' --glob '*.lean'
rg -n 'multi-writer|all.scatter|D7|fG|scatterExtentOverridesDeclared|SOURCE|SHAPED' <worktree>/papers <worktree>/leanncd --glob '*.md' --glob '*.lean'
rg -n 'CollectorShape|B5NativeTest|B5BoundaryTest' <worktree>/leanncd --glob '*.lean' --glob '*.toml' --glob 'AGENTS.md'
```

Update current boundary/count claims in directly related semantics notes and
DSL/Eval/Plan instruction nodes. Preserve historical records as history:
annotate supersession/link current measurements, don't rewrite old outcomes.
Record actual `rg` dispositions for numeric hits, including unrelated numbers.
Keep SOURCE/SHAPED distinction and the markedSquare limitation in current docs.
New `Eval/CollectorShape.lean` must be discoverable through existing public imports
(`LeanNCD` → `Eval.Eval` and plan compiler) and in Eval/Plan AGENTS guidance.
No unnecessary explicit umbrella import if the existing transitive path suffices.
Hook sections were measured below3k in DSL/Eval/Plan; no trimming task is needed.
T4 prose changes do not belong in the mechanically replayed implementation tree.

## 9. Final commands, budget and stop rules

Use the unmodified stock mutation wrappers already exercised during authoring;
do not instrument a custom harness or replace manifest cycles with hand edits.
Build commands use the wrapper policy in section1.

Unfiltered schema/site checks and actual cycles (absolute paths after substitution):

```text
bash <worktree>/leanncd/scripts/mutation-manifest.sh --check <worktree>/leanncd <worktree>/papers/semantics/additive_b5_mutations.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh --check <worktree>/leanncd <worktree>/papers/semantics/additive_b5_mutations_post.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh --out <execution-session>/b5-pre-results.md <worktree>/leanncd <worktree>/papers/semantics/additive_b5_mutations.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh --out <execution-session>/b5-post-results.md <worktree>/leanncd <worktree>/papers/semantics/additive_b5_mutations_post.json
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd Tests JaxExperiment
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd
/usr/bin/git -C <worktree> diff --check
```

Check pre-manifest on base at authoring/preflight and both on final tree before
cycles. Run mutations sequentially with exclusive source ownership; never build
one checkout while another controller mutates it. Retain per-row intended error,
mutated failure/restored-green result and byte-identical hashes in the record.
No skipped guard/target; no replacement of manifest runs by `--check`.

Design estimate:82–130M total =12–20M authoring +55–85M implementation/fixtures
+15–25M mutation/review/controller. These are estimates, not measured outcomes.
Authoring checkpoint29.736M exceeded12–20M, below the skill's50M target.
The long combined design/plan controller reached265,081 context, exceeding
~250k; all specialist dispatches stayed below60 turns/250k. The record explains
the breach and final controller accounting must include later verification.
Execution ceiling ~175M;
every dispatch ≤60 turns/250k peak. This authoring dispatch was extended from
45 to a55-call target, hard60, for measured closure/replay verification.
Use SDK `session.usage_record` accounting if token-report has no transcript;
inputTokens already includes cache tokens. Keep records separate from this plan.

Stop for a load-bearing failed/missing guard, invalid task compile dependency,
unfixable review finding, mutation survivor without adjudication or broadened
language/backend proposal. No silent skip, fictitious success or automatic
implementation authorized by plan approval. Park independent bridge/JAX kernels,
predicate/multi-axis support, containing extents and F3; each needs its own
owner-approved scope, not this slice's cleanup budget.
