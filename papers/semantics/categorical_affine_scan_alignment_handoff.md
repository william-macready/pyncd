# New-session brief: certified affine reads in single-clock Lean scans

## Bootstrap: use latest local main

A new session worktree can predate this file. Read the primary-checkout copy:
`/Users/williammacready/code/python/pyncd/papers/semantics/categorical_affine_scan_alignment_handoff.md`.
If needed, inspect the committed copy with one separate read-only command:

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd show main:papers/semantics/categorical_affine_scan_alignment_handoff.md
```

Then prepare an isolated worktree against latest **local** main with
`new-slice`. An unsuccessful search in a stale worktree is not proof that the
brief is absent. If a tool needs approval, surface that checkpoint and wait;
do not bypass permissions or silently describe the wait as proof work.

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> disclose any breach.

## Copyable launch instruction

```text
Read
/Users/williammacready/code/python/pyncd/papers/semantics/categorical_affine_scan_alignment_handoff.md
from latest local main, even if the current worktree predates it.
Prepare and verify one implementation plan, then execute it, for a Lean-only
bridge from actual checked single-clock scan access/write tables to admitted
affine reads and a constructed ranked semantic component.

Keep the profile bounded: one persistent history H[i,t], canonical full base
H[i,0]=Z[i], complete writes H[i,t+1], integer-affine spatial/external reads,
captured-state time reads t-k for k>=0, real zero padding and ordered
sum/product read expressions without contractions or nonlinear/partial ops.
Use actual AffineMap/ReadPlan/RawScanPlan/CheckedScanPlan data, not a second
scan IR or separately handwritten coefficient tables.

Prove raw-coordinate, per-dimension bounds, zero-padding and ordered-footprint
agreement. Construct the semantic Program, its source-contract match and
decreasing address rank; establish its whole-history recurrence/model meaning
and instantiate the existing operational/witness interpretations.
Include compiler-produced certified examples, not just hand-built plans.

Do not broaden administrative Domain wires, change the existing scan checker,
claim floating-point runDenseScan correctness, infer a general St/Br functor,
or assert arbitrary temporal reindexing/prefix laws.

Preserve unrelated edits/worktrees; use the Full process and repository release
gates, merge locally when green and reviewed, and do not push. Stop for a
load-bearing profile/extraction/matching blocker rather than replacing the
main result with fixture parity or assumed semantic agreement.
```

**Implementation process: Full.** This adds generic admission, causality and
semantic-alignment proof capabilities. This document is a goal brief,
**not a verified implementation plan**. The handoff session has only read
existing interfaces; it has not verified new declaration names, a module split,
profile extraction, a match construction, fixtures or mutation diagnostics.

## 1. Why this slice, and what it does not claim

Lean already has:

- symbolic integer-affine `StMat` geometry, without finite-coordinate bounds;
- concrete positional affine reads and checked scan plans with padding,
  captured-state causality and immutable-pre-step execution;
- generic admitted reads, occurrence footprints and address-rank semantics;
- ranked operational and complete-witness categories and their comparison.

The missing connection is from the **actual checked scan tables** to those
semantic reads/dependencies and a legal categorical component.
Do not mistake abstract representability for this connection already being
proved. The default semantic source admission still refuses affine read syntax
and scan slots; this slice need not extend that general admission path.

This is exact access/recurrence semantics, **not an equivalence between rational
values and binary32/binary64 execution**. Interpret the admitted real
sum/product operations over exact rationals for the semantic bridge. Existing
storage-kind/algebra fields remain authoritative metadata; extracting their
real sum/product structure does not convert arbitrary Float data into rationals
or prove a rounding theorem. No new dense executor is requested.

Read first:

1. [Synthesis](categorical_tensor_logic_semantics.md), Sections 2, 3.3, 6.13-6.14,
   7.4 and Appendices A.12-A.13.
2. [Ranked operational record](categorical_ranked_operational_interpretation_record.md)
   and [comparison record](categorical_operational_witness_comparison_record.md),
   for the actual categorical API and retained frame/domain restrictions.
3. [Checked scan design](../wave_f_scanplan_proposal.md) and
   [restricted scan-history proof record](plan_layer_slice5_record.md).
   Neither is a general affine-scan categorical alignment theorem.
4. [Lean instructions](../../leanncd/AGENTS.md), then the targeted sources below.

## 2. Freeze this profile before authoring the plan

| Surface | Required scope |
|---|---|
| Clock and state | Exactly one persistent history tensor with one spatial axis and one advancing time axis, presented semantically as `H[i,t]` |
| Extents | Concrete finite spatial extent `d` and recurrence count `N`; history has time extent `N+1`, and the step context has extent `N` |
| Base | The complete slice at time zero is the supplied external vector `Z`; establish this from actual base captures/computation/write fields |
| Recurrence | One sum/product assignment produces the complete next spatial slice; no scratch chain, contraction/reduction positions, masks, casts or nonlinear steps |
| Spatial state reads | Integer-affine coordinates, including shifts, striding, reversal and dependence on the current clock; noninjectivity is allowed |
| Temporal state reads | Exactly own-clock coefficient one and bias `-k`, with `k>=0`, matching `causalAdvancingRow` |
| External reads | Integer-affine rows over the actual term's spatial/context basis, with existing source shapes and real zero-padding behaviour |
| Placement | Canonical complete base and successor writes; no strided/scattered spatial writes or overlapping writers |
| Policies | Complete history, existing initialized boundary policy and immutable-pre-step state capture |
| Boundary cases | Require zero recurrence steps. Audit zero spatial extent and pin its actual checker/compiler behaviour; no vacuous unsupported-case theorem may count as acceptance |

Use the real term `contextPos`/`outputPos` classification, not a guessed matrix
column order. With no reduction positions, the admitted basis has just the
context and output coordinates, in whatever certified positions are present.
Preserve factor order, repeated reads and multiplicity.

In the existing Lean compiler's fixtures, `iter l = 1` can mean a history extent
of one and hence **zero** recurrence steps. Parameterize the theorem from
`historyExtents` and `stepExtents`; do not import a different frontend's
convention for what an iteration bound counts.

The prototype must select concrete field-level conditions, including the
permitted base passthrough/identity-assignment form and storage/algebra door.
These conditions may narrow the implementation to this stated profile, but
must not assume the semantic alignment being proved. If an agreed case cannot
be represented under the unchanged checker, report the exact obstruction
before freezing the plan; do not silently widen or reduce the slice.

## 3. Required deliverables and theorem strength

### A. A profile certificate on the existing checked representation

Consume an actual `CheckedScanPlan`, its signature table and the appropriate
checker-origin evidence. Establish the needed matrix dimensions, capture roles,
term basis, arithmetic, placement, extents and closed policies from its fields.
The profile recognizer/certification API must distinguish unsupported plans
explicitly and leave the existing checker and its acceptance set unchanged.

A private constructor does not by itself supply arbitrary logical invariants
absent from its fields. Prove the required consequences of actual checker
success or retain direct structural certificates, rather than assuming them.
Prove that certified compiler-produced donors inhabit the profile.

### B. A certified affine-access bridge

Construct admitted semantic reads from existing `AffineMap`/`ReadPlan` tables.
Prove agreement on:

- each raw integer coordinate, including signs, offsets and mixed spatial/time rows;
- rank/width and per-dimension bounds, **before** flattening;
- the exact source address for an in-bounds access;
- the constant-zero outcome for a real out-of-bounds read;
- the ordered footprint, retaining repeated admitted addresses while padded
  constant reads contribute no nonexistent dependency.

An out-of-bounds padded read is not an unavailable in-bounds state read.
Do not identify either with an undefined arithmetic primitive or a zero-valued
successful witness of a failed computation.

This may introduce a small certified zero-pad read helper if prior art is
insufficient. It must remain a bridge for existing data, not a competing
affine-map or scan representation.

### C. A constructed ranked semantic component

Construct the finite semantic `Program` for certified base/step tables, with
occurrences for each actual base/successor destination and the certified body.
Construct its graph, priority/source-contract match and address rank; callers
must not supply a new whole-program matching or execution-agreement premise.

Prove every actual dependency decreases: for a state read at `t-k`, an
in-bounds dependency is earlier than the write at `t+1`; negative-time padding
has no state dependency. External inputs are a distinct role. Use every
spatially transformed read in the footprint, not only an output representative.

Checked plans are positional/UID-free. Any fresh semantic identities must be
assigned consistently through an explicit slot/signature interpretation.
Do not claim to reconstruct original source UIDs from equal extents, array
positions or names. Compiler-donor connections must retain their actual
slot/signature association.

### D. Exact whole-history alignment

State an exact rational recurrence meaning using the **same admitted plan
tables**, supplied rational external data and canonical base/write geometry.
Prove the constructed semantic component denotes that whole recurrence,
including every materialized coordinate and padded boundary case, not just
the final slice.

Connect its actual default semantic execution, model and categorical arrow
through existing rank/correspondence/comparison results. Do not stop after
constructing a `Program` or showing two independently authored toy examples
agree. Reuse existing completion/uniqueness results rather than postulate them.

Distinguish a mathematical interpretation of plan tables from a new competing
scan executor. The slice does **not** prove that Float `runDenseScan` returns
the same values as the rational interpretation. State this boundary in the
main theorem and close-out, not only in a footnote.

### E. Actual compiler applicability

Provide certified examples obtained from the existing preparation/compiler
path and its returned checked scan evidence. The bridge must consume those
returned tables, not manually replace them with a hand-normalized equivalent.
Use meaningful wrong-map controls so compiler applicability is not vacuous.
No general parser correctness or universal source-to-plan theorem is required.

## 4. Laws deliberately not asserted

Administrative `Domain` transports remain certified extent-preserving axis
correspondences. General affine gathers are computations, not those wires.
Do not broaden the administrative category to make the alignment convenient.

Raw affine composition alone does not justify finite padded-gather fusion.
For example, shifting to form a finite intermediate and shifting back can
introduce boundary padding even when the raw matrices compose to identity.
Retain this distinction as a negative control.

Temporal decimation/reversal and spatial reindexing do not automatically
commute with scans. This slice proves access interpretation and causality,
not arbitrary scan naturality, fold fusion or resampling laws. In particular,
do not derive a partial-computation prefix law from value-level restriction:
complete-array evaluation cannot erase later demanded undefined work.
Partial primitives themselves are outside this first profile.

## 5. Discriminating acceptance goals for plan authoring

These are donor/delta requirements, **not newly measured fixture values or
verified cycle counts**. The plan must name exact fixtures, nearest legal
neighbors, observed outputs and intended diagnostics.

| Goal | Existing donor and required delta/distinction |
|---|---|
| Baseline and actual compiler tables | `selfRecurSched`, `selfRecurCheck`, `checkerAgrees`: adapt to the selected spatial/time state shape and certify actual preparation output |
| Spatial affine reads | Existing read-map/compiler donors: introduce nonconstant spatial shift, striding and reversal; assert per-address reads and whole histories, not just dimensions |
| Mixed spatial/time access | A spatial row using both `i` and `t`, with a distinct external/source shape; choosing the wrong basis column must change the observed accesses |
| Deep history and padding | `deepHistorySched`, `deepHistoryCheck`, `deepHistoryScan`: adapt to the stated spatial/time profile and retain the actual `t-2` read table and negative-index zero outcome |
| Zero recurrence steps | `extentOneSched`/`extentOneCheck`: base only, history time extent one, no spurious step or missing base |
| Spatial empty boundary | Inspect actual zero-extent admission; provide an inhabited supported certificate and metadata check, or report its explicit existing rejection before plan freeze |
| Causality boundary | Existing source/checker look-ahead, scaled-time and wrong-context donors; profile refusal must agree with the established state-read contract, with legal look-back neighbors |
| Bounds before flattening | Existing affine/dense coordinate donors: use an invalid multidimensional coordinate that could alias a valid flat offset |
| No invalid gather fusion | Two finite zero-padded shifts whose raw affine composite is identity but whose staged access differs at a boundary |
| Constructed match/rank/category | Generic certificate and actual compiler-donor instances must retain the full theorem, not only a Boolean parity result; audit all new namespaces |

Classify runtime/decidable observations separately from live-proof controls.
Mutations should distinguish sign/bias errors, wrong context columns, omitted
spatial dependencies, collapsed repeated reads, missing padding, a future-state
dependency, wrong base/successor extent and invented empty-case acceptance.
Do not count setup refusal or a type error as an intended runtime defect kill.

## 6. Targeted source map

All paths below are relative to `leanncd/`. Use `rg -n`, then approximately
40-60-line windows around the identifiers; do not reread whole large modules.

| Identifiers @ file | Role |
|---|---|
| `IdxExpr`, `idxAffineForm`, `idxDensify` @ `LeanNCD/DSL/Ast.lean` | Actual source integer-affine syntax and shared normalization |
| `StMat`, `StMat.comp` @ `LeanNCD/Base/St.lean` | Raw geometry; not finite-read admissibility or padding |
| `AffineMap`, `ReadPlan`, `TermPlan`, `AssignPlan`, `readFactorsIndexed` @ `LeanNCD/Eval/Plan/Kernel.lean` | Existing positional data and ordered read/basis authority |
| `applyAffine`, `inBoundsPerDim`, `flatIndex` @ `LeanNCD/Eval/Plan/Coordinates.lean`; `gatherFactorWith` @ `LeanNCD/Eval/Plan/Dense.lean` | Coordinate/padding execution contract; dense worker is not the rational theorem target |
| `CaptureSource`, `StateSlot`, `StateWriteMap`, `RawScanPlan`, closed policies @ `LeanNCD/Eval/Plan/RawStep.lean` | Actual capture, placement and history data |
| `CheckedScanPlan`, `checkScanPlan`, `writeRowKinds`, `baseWriteRowsOk`, `stepWriteRowsOk`, `causalAdvancingRow`, `stateReadCausal`, `runDenseScanWith` @ `LeanNCD/Eval/Plan/Scan.lean` | Existing acceptance and execution choices to preserve |
| `compileScan`, `prepareEvalPlan` @ `LeanNCD/Eval/Plan/Compile.lean`; `checkAssignCore` @ `LeanNCD/Eval/Plan/Check.lean` | Actual emitted tables and checked term/shape/arithmetic conditions |
| `AdmittedRead`, `ReadPolicy`, `RawCoord`, `Coord` @ `LeanNCD/Semantics/Types.lean`; `Expr` @ `LeanNCD/Semantics/Expr.lean` | Semantic read admission and typed expressions |
| `Program`, `Occurrence`, `destination` @ `LeanNCD/Semantics/Program.lean`; `dependencies`, `RankCertificate` @ `LeanNCD/Semantics/Ranks.lean` | Finite scalar occurrence semantics and strict dependency ranking |
| `readIndices`, `outputIndices` @ `LeanNCD/Semantics/Source/Admission.lean` | Existing broader source-admission exclusions; not implicitly changed |
| `RegisteredF`, `directRead`, `priorSlice`, `destination` @ `LeanNCD/Semantics/Plan/ScanHistory/Core.lean`; `history_retained` @ `LeanNCD/Semantics/Plan/ScanHistory/Correctness.lean` | Prior restricted scan proof; not a generic existing affine bridge |
| `MatchedComponent`, `SourceContractMatch`, `actualHistory`, `Normal` @ `experiments/indexed_execution/IndexedComponentCompositionScope.lean`, `IndexedCompositionMatch.lean`, `IndexedRankedOperationalCore.lean` | Required constructed component/match and existing categorical consumer |
| Existing source/checker donors @ `test/Eval/Plan/ScanCompileTest.lean`, `test/Eval/Plan/ScanTest.lean`; affine worker donors @ `test/Eval/Plan/KernelDenseTest.lean` | Acceptance and nearest-neighbor starting points; verify exact donor names |

Private helpers listed here are reading targets, not a demand to make all of
them public. Reuse/extract only the smallest shared mechanism actually needed.

## 7. Scope and release gates

**Lean only.** No Python implementation or Python parity work is part of this
slice. Excluded: multiple advancing axes, coupled persistent states,
strided/scattered writes, contractions/reductions, masks/casts, nonlinear and
partial primitives, arbitrary temporal resampling, general scan naturality,
new administrative wires, full St/Br functors, bialgebraic machinery,
floating-point/JAX/backend refinement and physical-storage correctness.
Do not rename affine-in-state optimization claims into affine-index theorems.

Use `slice-plan` and `new-slice`; verify warm Mathlib and refresh project-owned
oleans through the prescribed wrapper. Prototype the actual profile extraction,
read bridge and match construction on the real module split before drafting
tasks. Use a fresh bounded context to author the verified plan from artifacts.
Ship mechanically generated per-task patches and mutation manifests with
observed intended diagnostics; separate live plan and evidence record.

Use roughly three work items per dispatch. Split before approximately 60 turns
or 250k peak context; authoring targets 50M cumulative input tokens and execution
caps at 175M. Run `token-report.py`; disclose unavailable telemetry and breaches.
If the profile/extraction/match proof cannot fit this bounded slice, surface the
precise issue before execution instead of widening scope or accepting parity.

Keep the categorical bridge nondefault under `IndexedExecutionExperiment`,
with a discoverable entry point and matching Lean instructions. Controller
release gates: all unfiltered intended-diagnostic mutation cycles with restored
builds/source hashes; namespace/source axiom audits; full
`LeanNCD Tests IndexedExecutionExperiment` wrapper build; two final whole-branch
reviews covering (1) affine admission/footprint/rank/match/whole-model soundness,
and (2) actual checked/compiler tables, boundary policies, order, empty/zero
cases and the exact-arithmetic versus Float nonclaim.

Update synthesis status only for results actually proved. Preserve concurrent
main changes, merge locally when green and reviewed, clean up only owned task
branches/worktrees and do not push. Close-out states exactly which checked
plans the certificate covers, how original table data reaches the semantic
component, which execution/model/category theorems are derived, and which
numerical or scan-transformation claims remain unproved.
