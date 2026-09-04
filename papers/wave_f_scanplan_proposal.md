# Wave F proposal: checked scans in `EvalPlan`

## Status and purpose

**Status:** design draft, 2026-08-07. F0 (executable scan contract) landed 2026-08-08; F1 (contextual
local kernel) landed 2026-08-08 — see `papers/restructure_suggestions.md`'s wave-progress table. F2
(checked plan-block vertical slice) is next, per §13's ordering.

This document proposes Wave F: extending Wave C's checked, backend-neutral `EvalPlan` with explicit
scan state and a general Dense scan worker. It is modeled on
[`wave_c_evalplan_proposal.md`](wave_c_evalplan_proposal.md), but starts from the architecture Wave C
actually shipped:

- `RawEvalPlan` is freely constructible and never executable;
- `CheckedEvalPlan` is privately constructed by `checkPlan`;
- local tensor work is expressed by positional `AssignPlan` values;
- `prepareEvalPlan` specializes a `ScheduledProgram` and `InputSignature`;
- `runPreparedDense` implements the named-to-positional boundary; and
- `evalScheduled` remains the independent source-level oracle (the existing evaluator that executes
  a `ScheduledProgram` directly, without compiling it into `RawEvalPlan`/`CheckedEvalPlan`; agreement
  with this separate path tests the new checked-plan compiler and worker together).

Wave C deliberately rejected every `ScanStmt.scan` and `ScanStmt.scanPre`. That was the correct
boundary: the source scan node stores parallel statement lists, while important state, geometry,
snapshot, boundary, and causality rules are still reconstructed by the legacy evaluator. Wave F must
make those rules checked plan data rather than teaching a backend to reverse-engineer `ScanStmt`.

The proposal has two goals:

1. define one general, explicit-order `ScanPlan` semantics that Dense, PyTorch, and JAX can share; and
2. provide an implementation sequence whose intermediate slices are independently checkable and
   executable.

Throughout, **"general" describes the execution model, not the breadth of accepted source programs.**
The worker's four-phase semantics ([§9](#9-general-dense-scan-semantics)) applies uniformly to any
checked `ScanPlan`, with no specialized case for one-axis, coupled, or n-dimensional scans. The
*accepted source fragment* is deliberately narrow — one-axis and rectangular uniform recurrences only,
base writes that are pairwise disjoint across a state's boundary — and stays that way until later
plan-kernel and scan-structure waves broaden it ([§5.1](#51-accepted-source-fragment), summarized in
the capability table in [§1](#1-executive-summary)).

Wave F is **not** the JAX `lax.scan` wave. A one-axis `lax.scan` lowering, nested-scan recognition,
parallel prefix, final-carry-only execution, and other optimized implementations follow only after
the general checked scan semantics has an independent differential gate.

## Table of contents

- [1. Executive summary](#1-executive-summary)
- [2. Landed Wave C boundary](#2-landed-wave-c-boundary)
- [3. Current scan representation and semantics](#3-current-scan-representation-and-semantics)
- [4. Problems Wave F must remove](#4-problems-wave-f-must-remove)
- [5. Wave F scope and fixed policies](#5-wave-f-scope-and-fixed-policies)
- [6. Checked plan language](#6-checked-plan-language)
- [7. Checking and failure ownership](#7-checking-and-failure-ownership)
- [8. Source residualization](#8-source-residualization)
- [9. General Dense scan semantics](#9-general-dense-scan-semantics)
- [10. Correctness laws](#10-correctness-laws)
- [11. Evidence and test strategy](#11-evidence-and-test-strategy)
- [12. Backend lowering boundary](#12-backend-lowering-boundary)
- [13. Implementation slices](#13-implementation-slices)
- [14. Definition of done and stop conditions](#14-definition-of-done-and-stop-conditions)
- [15. Wave C planning lessons applied](#15-wave-c-planning-lessons-applied)
- [16. Literature-derived design patterns](#16-literature-derived-design-patterns)
- [17. References](#17-references)

## Glossary

Terms below recur across many sections; each is fully defined at its first section reference, and
restated here only as a lookup aid.

| Term | Meaning | Defined in |
|---|---|---|
| State | One persistent, feedback-carrying tensor a scan maintains across iterations. | §6.3 |
| Base write / step write | The boundary-initializing write for a state, vs. the per-iteration next-state write. | §6.5 |
| Block (`PlanBlock`) | A local, acyclic, context-parameterized dataflow graph — the base block or the step block. | §6.2 |
| Capture | A block input bound to either an outer graph slot (external) or a persistent state (state capture). | §6.4 |
| Snapshot / commit | The immutable pre-step state exposed to a block, vs. the simultaneous write of next-state results after it runs. | §5.3, §9.3 |
| History extent / step extent | Full stored-history length per axis, vs. the derived recurrence-domain size (`extent - 1`). | §1, §6.6 |
| Mixed-radix rank | The traversal order over multi-axis recurrence coordinates (axis zero fastest). | §6.6 |
| Causality certificate | Checker-produced evidence that every feedback read is defined by padding, base init, or an earlier producer. | §7.4 |
| Materialization policy | Which values a scan actually returns (currently: complete state histories only). | §6.3 |

## 1. Executive summary

At a high level, Wave C evaluates a source program by specializing it into a small, checked,
positional assignment graph (assignments refer to tensor inputs and outputs by integer slots rather
than by source names or axis UIDs):

Here, **`EvalPlan` names the intermediate plan language and its compile/check/execute boundary**; it
is not a separate executable record alongside the concrete types below. Within that language:

- an **`AssignPlan`** describes one local, stateless tensor operation: its source slots, one
  destination slot, output and reduction iteration structure, affine reads, and algebra;
- a **`RawEvalPlan`** is the freely constructible program-level **dataflow graph**. Each `AssignPlan`
  is a node; a producer-to-consumer edge is implicit whenever a later assignment reads the tensor
  slot written by an earlier assignment. Input slots are the graph's roots. The record stores nodes
  in proposed execution order rather than storing a separate edge list, and `checkPlan` verifies that
  this order is a valid topological order. This is called the **outer graph** to distinguish it from
  the local base/step graphs nested inside a future scan node. Its version, positional tensor
  signatures, input slots, ordered `AssignPlan` steps, and numeric mode have not yet been trusted; and
- a **`CheckedEvalPlan`** is the private evidence-bearing result of `checkPlan`. It retains the raw
  graph together with locally checked assignment nodes and guarantees graph-wide slot availability,
  production order, uniqueness, and admitted policy. It is the only form accepted by the Dense plan
  worker.

Thus an `AssignPlan` is one operation, `RawEvalPlan` is an unchecked graph of those operations, and
`CheckedEvalPlan` is the validated executable graph. “EvalPlan” refers to this family and
architecture as a whole.

```text
source program
    ↓ specialize using input signatures
RawEvalPlan: raw positional AssignPlan graph
    ↓ validate
CheckedEvalPlan: checked assignment graph
    ↓ bind runtime tensors
Dense execution
    ↓ restore source names
result environment
```

Each Wave C assignment is stateless: it reads already available tensor slots, computes one complete
destination tensor, and inserts that tensor into the positional store. Raw plans cannot execute, and
the Dense worker neither sees source syntax nor rediscovers shapes, names, dependency order, or
affine-read policy.

A scan does not fit that single-assignment model. It repeatedly applies a transition such as
`H[k + 1] = step(k, H)` and may update several coupled states together. That requires initialization,
persistent feedback, per-step scratch, traversal order, state-write geometry, causality, and atomic
next-state commit—concepts that an `AssignPlan` does not contain.

Wave F therefore retains this pipeline but changes the type of every program-level graph node. In
Wave C, `RawEvalPlan.steps` is an `Array AssignPlan`, so each outer node is directly an assignment.
In Wave F, `RawEvalPlan.steps` becomes `Array PlanStep`:

```text
PlanStep
  | assign AssignPlan
  | scan   RawScanPlan
```

Thus Wave F graph nodes are uniformly `PlanStep` values; an ordinary node contains an `AssignPlan`,
while a scan node contains a `RawScanPlan`. They are not peer node types in the same array.
`RawEvalPlan` stores this unchecked graph; `CheckedEvalPlan` stores its validated executable meaning,
with `CheckedAssignPlan` or `CheckedScanPlan` evidence corresponding to each step. Wave F does
**not** add scan-shaped optional fields to `AssignPlan`. During
[source residualization](#8-source-residualization) (compiling away static source details into a
lower-level plan that retains only runtime work), scan names and syntax are replaced by positional
states, captures, blocks, write maps, extents, and policies. The layered checkers validate the local
assignments, acyclic base/step blocks, scan geometry and causality, and finally outer graph
dependencies; the resulting representation is detailed in the
[checked plan language](#6-checked-plan-language).

The `PlanStep.scan` constructor is a multi-output stateful graph node with ordered persistent states;
explicit base and step blocks; explicit mappings from block results into complete state tensors;
static full-history extents; closed traversal, boundary, and snapshot policies; complete-history
materialization; and checker-produced causality evidence.

`CheckedEvalPlan` and `CheckedScanPlan` validate different scopes. A `CheckedEvalPlan` represents the
entire program-level dataflow graph and contains one checked meaning for each outer `PlanStep`. When
that step is `PlanStep.scan`, its checked meaning is a `CheckedScanPlan`, which validates only that
one scan's states, captures, base/step blocks, write geometry, policies, and causality. Thus a
`CheckedEvalPlan` may contain several `CheckedScanPlan` values alongside ordinary checked
assignments; a `CheckedScanPlan` is not a complete executable program by itself.

At runtime, ordinary assignment nodes retain their Wave C meaning. The validated form of a
`PlanStep.scan` inside `CheckedEvalPlan`, backed by a `CheckedScanPlan`, is executed by the general
Dense scan worker in four sequential phases:

```text
allocate complete state tensors
execute and commit checked base writes
for each iteration coordinate in the declared order:
  expose one immutable pre-step state snapshot
  execute the checked step block
  commit all designated next-state slices simultaneously
return complete state histories
```

The completed histories are inserted into the outer positional store so later assignment or scan
nodes can consume them. Section [9](#9-general-dense-scan-semantics) gives the full worker semantics.

The architectural boundary is unchanged: static specialization still precedes execution; raw plans
still cannot run; checked semantic data remains positional and backend-neutral; names remain boundary
metadata; failures remain typed; and `evalScheduled` remains an independent source-level oracle.
Wave F adds explicit checked state-transition nodes rather than a second evaluation pipeline.

The source compiler initially admitted scans only when every base and step operation was already
representable by the checked Wave C local kernel: `f64`, real sum-product, identity nonlinearity,
plain read factors, affine reads, and zero padding. That initial scope already covered linear
recurrences, coupled recurrences, external per-step reads, contractions in a recurrence, and
rectangular uniform n-dimensional scans with advancing dimensions in arbitrary tensor positions.

> **Nonlinearity-thread update — 2026-08-29.** Thread 4 Task 4 widened this: pointwise and axiswise
> nonlinearities in scan `base` and `recur` blocks are now **structurally admitted** by
> `checkNonlinScanBlock` and lowered by `compileScan` (`Eval/Plan/Compile.lean`), identically to the
> top-level admission (`Eval/AGENTS.md`). `RawPlanBlock`'s element type is `BlockStep`
> (`.assign`/`.pointwise`/`.axiswise`), and the differential's `enumScanCases` corpus now splits
> **17 accepted / 0 `unsupportedNonlin` / 0 `unsupportedAgg`** (was 9 / 4 / 4 at F4 authoring time,
> then 13 / 0 / 4 after thread 4 admitted nonlinear scans; `DifferentialTest.lean`). The remaining
> §5.1 restrictions on Boolean factors, `.scanPre`, etc. are unchanged; max/min aggregation and unary
> factors are now admitted too (max/min compiles to the tropical algebras `evalScheduled` evaluates;
> unary factors lower to a `ReadPlan.unary` field applied after the out-of-bounds pad).

Historically, the "no nonlinearities" limit belonged to Wave C's checked `EvalPlan`, not to the
broader source language or legacy `evalScheduled` evaluator. Source programs can contain pointwise or
axiswise nonlinearities, Boolean factors and predicates, unary factors, and max/min aggregation, and
the legacy path supports relevant cases. As of thread 4, `prepareEvalPlan` **admits and residualizes**
pointwise and axiswise nonlinearities (both at top level and inside scan blocks), the
max/min-aggregation thread additionally **admits** max/min aggregation (compiled to the tropical
algebras), and the unary-factor thread **admits** unary factors (`log`/`exp`/…, lowered to a
`ReadPlan.unary` field); the remaining rejections above still return typed `CapabilityError` values
because `AssignPlan` cannot represent their semantics. Wave F does not broaden the local kernel further
merely because such constructs also occur inside current scan examples. They remain orthogonal
plan-kernel extensions and retain typed source rejection on the checked-plan path.

**Functionality still missing after Wave F lands.** Completing Wave F will **not** make
`CheckedEvalPlan` feature-equivalent to the source language or `evalScheduled`. The following remain
outside the checked-plan path:

| Missing capability | Consequence after Wave F |
|---|---|
| Pointwise and axiswise nonlinearities | **Admitted** (thread 4): top-level (`checkNonlinTopLevel`) and inside scan `base`/`recur` blocks (`checkNonlinScanBlock`), residualized into a two-step `assign → pointwise/axiswise` chain. `unsupportedNonlin == 0` in the `DifferentialTest.lean` scan corpus. |
| Masks, predicates, and Iverson factors | **Admitted** (Slice 5, `predicate_boolean_backend_parity.md`): a positional UID-free predicate IR (`PosBoolExpr`) plus an ordered `FactorPlan` (`read | iverson`); `checkAssign` width-checks predicate leaves and Dense evaluates them per contraction coordinate (`true` ⇒ `1.0`, `false` annihilates). Source `BoolExpr` lowers via `lowerFactorPredicate`; axiswise `where=` masks via `RawAxiswisePlan.mask` + `lowerMaskPredicate`. `maskOrPredicate`/`maskedAxiswiseNotSupported` retained producer-less. |
| Boolean/predicate declared outputs | **Admitted** (Task 4, `boolean_predicate_output_evalplan.md`): `ScalarDType.bool` is a semantic algebra/signature tag over the unchanged Float-backed storage, not a native carrier. A predicate destination selects `admittedAlgebraBool` (factor `min`/identity `true`, reduction and term `max`/identity `false`, mirroring the reference `Combine.bool`); a `bool` source may feed an `f64` destination and vice versa, since the DESTINATION selects the algebra and gathering is dtype-blind. Scan state, scratch, and published histories carry full `TensorSignature`s (`CompiledScan.stateSigs`) and `checkWrites` enforces write-dtype equality (`ScanPlanError.writeDtypeMismatch`). `booleanOutput` retained producer-less. `f32` stays rejected; no native `Array Bool`, no truth-value validation, and no JAX Boolean execution (the experimental backend REJECTS Boolean semantics, see below). |
| Unary factor functions | **Admitted** (unary-factor thread): `checkFactor` admits `.unaryFn`; `residualizeAssignment` lowers it to a `ReadPlan` with a new `unary : Option UnaryOp` field, and Dense's `gatherFactor` applies the function after the `zeroPad` out-of-bounds pad (so an OOB read contributes `f(0)`). The math lives once in `UnaryOp.applyChecked`, shared with the reference `applyUnaryFn`; `log`/`sqrt`/`recip` fail loud (`PositionalInputError.unaryDomain`). |
| Max/min aggregation | **Admitted** (max/min-aggregation thread): `checkAggOp` admits `.max`/`.min`; the compiler selects the tropical algebra (`algebraForAgg`) `AssignPlan` already had the reduction slot for, and Dense reduces with `max`/`min` seeded at `−∞`/`+∞`. `unsupportedAgg == 0` in the `DifferentialTest.lean` scan corpus. |
| Scatter and affine LHS writes | Wave D source semantics are not yet represented by checked `EvalPlan`. |
| Dtypes beyond the admitted concrete `f64` mode and dynamic shapes | Still rejected at the checked-plan preparation boundary. |
| `.scanPre`, callbacks, and predicate-dispatch scan bodies | Still rejected even though `PlanStep.scan` exists (nonlinear scan bodies themselves are now admitted — see the first row). |
| General n-dimensional recurrence geometry and arbitrary state writes | The first checked scan remains the rectangular uniform all-axis `+1` fragment. |
| Multi-face full-boundary writes — a state initialized by two or more *free-axis* faces (the standard n-D tabulation-DP pattern, e.g. row-0-plus-column-0) — and genuinely overlapping writes with no declared precedence | Neither is achievable in this version. Both need the same missing capability: an offset/restricted-range or conflict-resolving base-write geometry beyond pin-plus-full-free. **Known defect**: an earlier draft of this proposal incorrectly claimed the first case was accepted; see the corrected limit in [§5.1](#51-accepted-source-fragment) and the narrower geometry actually admitted in [§6.5](#65-write-geometry). Only a main free-axis face plus disjoint fully-pinned point overrides is admitted here. |
| PyTorch/JAX execution and optimized `lax.scan`, compact-carry, wavefront, or parallel-prefix lowering | Dense remains the only general checked worker delivered by Wave F. |

The next semantic-expansion work after Wave F should be a named **checked local-kernel capability
wave**: extend `AssignPlan`, its checker, and Dense interpretation one operation family at a time,
then use the same checked operation inside `CheckedPlanBlock`. That ordering makes each new operation
available to both ordinary assignments and scans without reopening scan state semantics. Wave F does
not choose the order of those operation families, but F5 must preserve this table in the capability
manifest and handoff rather than allowing the typed rejections to disappear from the roadmap.

The first scan plan preserves the existing LeanNCD scan evaluator's extent meaning: a declared scan
extent counts the number of state values stored along that scan axis in each output state
tensor—the initial base slice plus one stored slice for each recurrence invocation, not the number
of recurrence invocations directly. `historyExtents` records these stored-history lengths;
`stepExtents` derives the actual recurrence domain. See [§6.6](#66-scan-node-and-outer-graph) for the
exact derivation and the mixed-radix traversal order, and [§7.4](#74-causality-certificate) for the
structural causality recognizer that admits non-positive constant look-back while rejecting
look-ahead.

Adding a stateful plan constructor changes the Lean type of the plan language itself, which is also
why Wave F removes `RawEvalPlan.version` and `admittedVersion` rather than bumping the field — see
[§2.3](#23-remove-the-unused-in-memory-version-tag) for the full argument.

## 2. Landed Wave C boundary

### 2.1 What Wave F inherits

Wave C's checked path is documented in
[`wave_c_capability_manifest.md`](wave_c_capability_manifest.md) and implemented under
[`Eval/Plan/`](../leanncd/LeanNCD/Eval/Plan/). Its load-bearing boundaries are:

1. **Semantic data is positional.** `AssignPlan`, `RawEvalPlan`, and their checked wrappers contain no
   source names, axis UIDs, callbacks, backend values, or unordered semantic maps.
2. **Raw values do not execute.** `checkAssign` and `checkPlan` are the only constructors of the
   private checked wrappers accepted by Dense workers.
3. **The source compiler and worker are independent.** `Plan/Dense.lean` imports neither
   `Plan/Compile.lean` nor the legacy `Gather`/`Contract` evaluator.
4. **Failures are closed and typed.** Capability, source-signature, plan-validation, binding, and
   positional-runtime failures have distinct owners.
5. **Static specialization precedes execution.** `prepareEvalPlan` resolves shapes, UIDs, names,
   affine maps, slots, and policies before a worker sees tensor values.
6. **The named environment is a boundary sidecar.** `PlanBindings` owns names; checked semantic data
   does not.
7. **The legacy evaluator is an oracle, not a helper.** Bit-exact differential agreement is meaningful
   because the two paths do not share their execution implementation.

Wave F preserves all seven.

### 2.2 Why a scan is not an `AssignPlan`

An `AssignPlan` has one destination and no feedback. A scan:

- produces several persistent states atomically;
- invokes one block repeatedly;
- distinguishes persistent state from per-step scratch;
- exposes previous state while withholding next state until commit;
- writes slices into complete tensors through explicit geometry; and
- needs ordering and causality evidence.

Representing those facts as conventions around an array of ordinary assignments would recreate the
implicit protocol Wave F is intended to remove.

### 2.3 Remove the unused in-memory version tag

Wave C's `RawEvalPlan.version = 1` and `admittedVersion` check identify only the one in-memory plan
type compiled into the same binary. They do not protect a persisted artifact, wire protocol, plugin
boundary, or independently deployed consumer. Wave F already changes `steps : Array AssignPlan` to a
closed sum of plan steps, so Lean source that builds the old record must be recompiled and migrated
regardless of the number in the record.

Wave F should therefore remove the `version` field, `admittedVersion`, and
`PlanError.versionNotAdmitted`. This follows the Wave C decision not to build canonical
representation infrastructure without a consumer. A later codec should introduce an explicit format
or protocol version at the serialization boundary, where old and new representations can actually
coexist.

### 2.4 Relationship to roadmap E2

The roadmap's E2 sketch proposed a source-side `CoreStmt` with an explicit `Recurrence`, replacing
parallel base/recur lists before both legacy evaluation and routing. Wave F takes the execution-side
principle—explicit state and transitions—into checked `EvalPlan`, but does not first migrate the
source pipeline or legacy evaluator. F4 residualizes the existing `ScheduledProgram` into positional
scan data.

This ordering is deliberate: changing `evalScheduled` before the new scan worker passes its
differential gate would weaken the independent oracle. A later source-side `CoreStmt` migration may
target the checked semantics established here, but it is not a Wave F prerequisite.

### 2.5 Roadmap patterns that bear on Wave F

Several patterns in [`restructure_suggestions.md`](restructure_suggestions.md) apply directly, but
at different layers:

| Roadmap pattern | Wave F use | Timing |
|---|---|---|
| Spike 4f / Spike 5 semantic decomposition | Separate scan classification, base initialization, recurrence execution, and state commit; make each phase explicit checked data rather than a legacy evaluator convention. | F0-F4 |
| E2 closed typed IR | Apply the principle at the execution boundary with `PlanStep.scan`, `CheckedPlanBlock`, and private checked evidence. Preserve the source AST until the independent differential gate exists. | F2-F4 |
| E4 residualization and worker/wrapper | Specialize names, UIDs, shapes, slots, affine maps, and policies once; keep the worker positional and source-free. Treat a future compact carry as a representation refinement of complete-history semantics. | F4; carry later |
| E6 property and metamorphic oracles | Compare source evaluation, checked execution, and independent unrolling; require alpha-renaming, traversal, snapshot-binding, and geometry mutations. | F0-F5 |
| E7 validation applicative | Useful only if independent scan-checker failures can be accumulated without obscuring failure ownership or precedence. Closed error families matter now; applicative accumulation does not. | Optional after F3 |
| E10 staging | Use an explicit static/dynamic binding-time split for `prepareEvalPlan`, not a generic staging framework. | F4 |
| E14 checked rewriting | Compile-time unrolling may later rewrite a checked plan, but the production transform must remain independent from the source-level unrolling oracle. | Post-Wave-F |

E3's semiring abstraction becomes relevant if a later numeric mode certifies algebraic scan
optimizations. E14 and affine/polyhedral scheduling become relevant for unrolling or wavefront
execution only after the general worker is established. E5, E8, E9, E11, E12, and E13 do not shape
the first scan semantics. The common design rule is **phase separation with evidence**: close the
semantic vocabulary, validate once, and let consumers rely on checked facts rather than repeat
classification or infer execution policy.

## 3. Current scan representation and semantics

### 3.1 `ScanStmt` is scheduled source, not an execution plan

[`ScanStmt`](../leanncd/LeanNCD/DSL/Pipeline/Types.lean) currently has:

```text
plain   : Stmt
scan    : representative name
          -> ordered advancing axes
          -> base statements
          -> recurrence and scratch statements
          -> isAffine hint
scanPre : representative name -> axis -> ThreadedComposed
```

For `.scan`, the representative name is not the state interface. The evaluator discovers state names
from base-statement LHS names. The two statement lists do not say which values are persistent, which
are scratch, which outputs commit state, or which external inputs a block captures.

`.scanPre` remains rejected throughout source compilation and evaluation because its callback-like
payload does not have a checked execution meaning. Wave F does not admit it.

### 3.2 Source-to-schedule lowering

The current source pipeline:

1. elaborates numeric base slots as placeholder `iterAt` slots and `l + 1` as an affine shift;
2. assigns axis UIDs;
3. requires advancing axes to be declared with `iter`;
4. recovers a base slot's real iteration axis from a same-name recurrence slot at the same position;
5. groups recurrence statements by connected components of iteration-axis UIDs;
6. pulls transitively dependent non-iteration statements into the recurrence list as scratch;
7. rejects cross-component scratch, heterogeneous coupled axis sets, missing bases, direct positive
   look-ahead shifts, and scan-axis projections;
8. splits nonlinearities while preserving the scan wrapper; and
9. topologically schedules scan nodes as atomic top-level nodes.

[`finalizeScans`](../leanncd/LeanNCD/DSL/Pipeline/Structural.lean) therefore performs real semantic
work, but the resulting node still leaves execution rules implicit.

### 3.3 Legacy `evalScan`

[`evalScan`](../leanncd/LeanNCD/Eval/Scan.lean) implements:

1. resolve every advancing-axis extent, failing loudly if any is absent;
2. set `stateNames` to the deduplicated LHS names of all base statements;
3. zero-allocate one complete tensor per base assignment;
4. execute base statements in list order and write their slices into those tensors;
5. enumerate recurrence coordinates with `cartesianList`;
6. initialize `stepEnv` from the current `work` environment at each coordinate;
7. execute recurrence and scratch statements in source order;
8. classify an output as state or scratch by `stateNames.contains name`;
9. write each state slice immediately into `work`; and
10. return only tensors whose names occur in `stateNames`.

The implementation correctly captures much current behavior, including zero-default boundaries,
full-history state reads, coupled scans, contractions inside scans, and n-dimensional cartesian
traversal. It is deliberately a reference interpreter, not a checked positional contract.

### 3.4 Current extent and boundary convention

For full-history extents `L₁ ... Lₙ`, the recurrence loop enumerates:

```text
[0 .. L₁ - 2] × ... × [0 .. Lₙ - 2]
```

and writes `+1` in every advancing dimension. The first advancing axis varies fastest. Complete state
tensors start as zero. Explicit bases overwrite selected slices; uncovered boundary cells remain
zero.

This differs from older prose that described `N` transitions producing a history of length `N + 1`.
Wave F follows the executable Lean convention: the declared extent is the complete history length.

### 3.5 Coupling and snapshot behavior

Coupled scans are grouped by connected iteration-axis components. Recurrence statements retain source
order. The intended semantic model is Jacobi-style simultaneous state update, but the current worker
mutates `work` after each state statement and places that updated tensor in `stepEnv`.

Ordinary predecessor reads still observe old values because an earlier state writes coordinate
`q + 1` while a later state normally reads coordinate `q`. The implementation does not, however,
make an immutable old-state snapshot structural. A constant or sufficiently general affine state
read could observe a just-written value. Wave F fixes the semantics to immutable snapshot plus
simultaneous commit and rejects source scans for which the legacy implementation could distinguish
the two.

### 3.6 Deep history

A read such as `G[l - 2]` currently addresses the complete state tensor. Negative coordinates use the
same zero-padding semantics as other reads. The recurrence still starts at `q = 0`; there is no
inferred history depth, delayed start, or requirement for multiple bases.

Wave F makes that behavior explicit: non-positive constant look-back is admitted, out-of-range
history reads are zero padded, and execution still begins at the first recurrence coordinate.

## 4. Problems Wave F must remove

This table names the *type* of explicit data that replaces each current implicit rule. The concrete
*value* each replacement takes (e.g., which boundary policy, which traversal order) is fixed once in
[§5.3](#53-fixed-first-version-policies); it is not restated here. [§6.8](#68-producer-checker-and-consumer-matrix)
then traces each field to its producer/checker/consumer.

The checked plan must not depend on these current implicit rules:

| Current rule | Why it is unsuitable | Explicit Wave F data |
|---|---|---|
| State names are inferred from base LHS names. | Name matching survives into execution. | Ordered `StateSlot` array. |
| Base and recurrence pair by equal strings. | Pairing is neither positional nor checked. | Explicit state index on each write. |
| Scratch is inferred transitively by names. | Scope and lifetime are implicit. | Block-local input, scratch, and result slots. |
| Iteration axes come from the first recurrence. | Other state orderings can disagree. | One ordered scan context and per-state dimension map. |
| Base axes are recovered by slot position. | Geometry is reconstructed from source syntax. | Explicit checked base write maps. |
| State versus scratch is decided at runtime. | A worker interprets source naming conventions. | Distinct block outputs and designated state writes. |
| Inner dependencies use source order. | No checked block production order exists. | `CheckedPlanBlock`. |
| State commits occur during step evaluation. | Jacobi semantics is accidental. | Immutable snapshot policy and simultaneous commit. |
| Cartesian order is only a helper implementation. | Backends could choose different orders. | Closed `IterationOrder`. |
| Boundary behavior is allocation plus list effects. | Zero/default/base precedence is not one policy. | Closed `ScanBoundaryPolicy` plus ordered checked bases. |
| `isAffine` is a Boolean hint. | It proves neither causality nor associativity. | Opaque checker-produced certificates. |
| Full histories happen to be returned. | Output policy is not stated. | Explicit state materialization policy. |

Wave F is complete only when none of these rules needs to be rediscovered by a worker.

## 5. Wave F scope and fixed policies

### 5.1 Accepted source fragment

Wave F initially accepts a `.scan` when:

- there is at least one advancing axis;
- every advancing extent is statically known and at least one;
- state and external tensors are concrete `f64`;
- all base, scratch, and state-result assignments fit the existing real sum-product `AssignPlan`
  fragment;
- state reads satisfy the structural affine causality rule in Section 7.4;
- each persistent state has one or more base results, whose written regions are pairwise disjoint,
  and exactly one next-state result;
- every base write is in range, touches a boundary, and shares no coordinate with any other base
  write for the same state;
- every state has the same ordered advancing-axis context, though those axes may occupy different
  tensor dimensions;
- step-block dependencies are acyclic and production ordered; and
- complete state histories are the scan's materialized outputs.

This includes:

- one-axis self recurrence;
- coupled one-axis recurrence;
- external reads at the current iteration coordinate;
- contractions inside a recurrence;
- constant non-positive look-back;
- rectangular uniform all-axis `+1` recurrences, where every advancing axis writes `q + 1`;
- coupled rectangular uniform all-axis `+1` recurrences;
- iteration dimensions in arbitrary tensor positions; and
- a state boundary written as one free-axis face write plus one or more disjoint fully-pinned
  point overrides elsewhere (see the worked example and the limit below — this is narrower than it
  sounds).

This is an ordered lattice recurrence, not a general n-dimensional prefix scan.

> **Known defect, deferred, not fixed here.** An earlier draft of this section claimed that a state's
> boundary could be split across two *disjoint free-axis faces* — e.g. row `0` and column `0` of a
> 2-D table, the standard tabulation-DP boundary pattern. That claim does not hold and has been
> removed. See the limit below for why, and the deferred-capability table in
> [§1](#1-executive-summary) for where the fix belongs.

**The actual limit: two full free-axis boundary faces of one state are never disjoint.** Each base
write pins some axes to a literal and leaves the rest `.free` — and `.free` always ranges over an
axis's *entire* declared size, starting at `0`; there is no source or plan construct for "free,
starting at an offset" (`LHSSlot` has `.free`, `.iterAt` (a single literal point), `.iterNext`, and
`.affine` — the general one, which `checkLHSSlot`/`checkStmt` reject unconditionally as
`CapabilityError.scatterOrAffineLhs`, since arbitrary affine LHS writes remain a deferred, separate
capability). Since every write required to "touch a boundary" must pin at least one axis to `0`, and
every *other* axis it leaves free necessarily includes `0` in its range, any two such writes overlap
wherever every axis either write pins to zero is simultaneously zero — for a 2-D table with one write
pinning row and one pinning column, that intersection is exactly the corner `(0,0)`. This is not
specific to the row/column example; it holds for any two distinct free-axis face writes of one state.

**What multiple base writes are useful for in this version**, given that limit: at most one write per
state may leave any axis free (a single "main" face); additional writes must pin *every* axis to a
specific literal, landing on isolated points the main face's free range doesn't already cover. A
worked pair:

```text
-- accepted: one face write, plus a fully-pinned point override that the face doesn't cover
dp[0, j] = j        for all j     -- pins row = 0, free over column
dp[1, 0] = 1                      -- fully pinned (row = 1, column = 0); row = 1 is outside the face

-- rejected: two free-axis faces — both regions include (0, 0)
dp[0, j] = j        for all j
dp[i, 0] = i        for all i
```

Disjointness is checked over written index regions only, never over RHS values: the rejected pair
above is rejected even though both writes assign `dp[0,0] = 0` and therefore agree. The checker only
looks at which coordinates each base write's declared range touches, not at what the two RHS
expressions evaluate to; proving that two arbitrary RHS expressions agree wherever their ranges
intersect is a distinct, materially harder feature (symbolic equality of affine/sum-product terms,
not a checked policy value) and is not planned.

Writing a state's boundary as two or more full opposing free-axis faces — the common n-dimensional
tabulation-DP pattern (row-0-plus-column-0, and its higher-dimensional analogues) — is **not
achievable in this version** for the structural reason above, and is deferred alongside genuinely
overlapping writes with no declared precedence (e.g. writing row `0` and column `0` both unrestricted,
so both claim `(0,0)`, as in the rejected pair above). Both gaps share the same underlying missing
capability — some form of offset/restricted-range or conflict-resolving base-write geometry beyond
pin-plus-full-free — and are recorded together in the capability table in
[§1](#1-executive-summary).

### 5.2 Typed source rejection

Wave F continues to reject:

- `.scanPre` and callback-bearing recurrence payloads;
- zero-length scan extents in the first plan version;
- pointwise and axiswise nonlinearities;
- masks, predicates, Iverson factors, and Boolean state;
- scatter or affine LHS writes inside a scan block;
- unsupported state-write geometry;
- source scans with ambiguous state/base/result pairing;
- source scans whose snapshot behavior is not equivalent to immutable Jacobi update;
- specialized parallel or backend-specific scan requests; and
- `.scan` nodes declaring an empty advancing-axis list, under a `noAdvancingAxis`-named
  `CapabilityError` category (a new constructor F2 will need to add).

Some are plan-kernel capabilities deferred from Wave C; others are scan-structure capabilities.
Syntactically visible cases have closed `CapabilityError` constructors. Cases that require concrete
shapes or lowered affine maps have closed `ScanCompileError` constructors after specialization. A
generic `unsupportedScan : String` constructor in either family is not acceptable.

### 5.3 Fixed first-version policies

These are the concrete values for the checked-data types named in [§4](#4-problems-wave-f-must-remove);
[§6.8](#68-producer-checker-and-consumer-matrix) traces each one to its producer, checker, and
consumer.

| Concern | Wave F policy |
|---|---|
| Extent meaning | `historyExtents` is the full history shape; `stepExtents = historyExtents.map (· - 1)` is derived. |
| Minimum extent | `1`; `0` is typed rejection. |
| Extent `1` | Base block runs; step block runs zero times. |
| Traversal | Increasing mixed-radix rank over `stepExtents`, scan axis zero fastest. |
| Snapshot | Immutable pre-step state for every state read. |
| Commit | All designated next-state slices commit simultaneously after the step block. |
| Boundary | Zero-initialize complete states, then apply checked base writes in declared order. |
| Base placement | In-bounds, boundary-touching, non-overlapping in the first version. |
| History reads | Constant non-positive look-back; out-of-range coordinates zero pad. |
| Outputs | Complete state histories only; block scratch is not materialized. |
| Numeric mode | `reference64`, preserving declared factor/reduction order. |
| Optimization authority | None in `isAffine`; only separate checked evidence may select a fast path. |

These are semantic values, not backend defaults.

## 6. Checked plan language

The concrete Lean spelling should be finalized in each slice plan and every Lean snippet in those
plans must be compiled before the plan ships. The records below are conceptual ownership, not
copy-ready Lean.

### 6.1 Generalize local assignments to an explicit context

The existing `AssignPlan` iteration basis contains output and reduction coordinates. A scan step also
has an outer scan coordinate. Wave F should generalize the local kernel once rather than create a
second near-copy:

```text
AssignPlan
  contextShape
  destinationSlot
  outputShape
  terms
  algebra

TermPlan
  iterationShape
  contextPos
  outputPos
  reductionPos
  factors
```

`contextPos`, `outputPos`, and `reductionPos` must form an ordered, disjoint partition of the term
basis. Each term's context projection must equal `AssignPlan.contextShape`; each output projection
must equal `AssignPlan.outputShape`.

The Dense primitive becomes `runDenseAssignAt(checkedAssign, contextCoordinate, store)`. Existing
top-level assignments use empty context and `runDenseAssign` remains a thin wrapper passing `[]`.
This is the only change to Wave C assignment meaning.

Base `iterAt` pins are not runtime context coordinates. Before constructing a base assignment's term
basis, the source compiler substitutes every validated pin into every normalized RHS affine
expression: each pinned coefficient contributes `coefficient * pin` to the affine bias, then the
pinned UID is removed. Pinned UIDs are excluded from output and reduction positions. The pin remains
separately represented in the base `StateWriteMap`.

### 6.2 Plan blocks

A `RawPlanBlock` is a positional, context-parameterized, acyclic local graph:

```text
RawPlanBlock
  contextShape
  tensorSignatures
  inputs
  steps           -- Array BlockStep = .assign | .pointwise | .axiswise
  outputs
```

Block slots are local to the block. Inputs explicitly identify what one invocation receives; outputs
explicitly identify what the surrounding scan may commit. Scratch slots are produced and consumed
inside the block and disappear after invocation. As of thread 4 Task 4, `steps` is `Array BlockStep`
— i.e. the block admits `.assign`, `.pointwise`, and `.axiswise` step kinds (was `Array AssignPlan`
in the initial F3 proposal).

`CheckedPlanBlock` has a private constructor. `checkPlanBlock` composes `checkAssign`,
`checkPointwise`, and `checkAxiswise`, validates local input availability and production order, and
verifies that every declared output exists with its declared signature. One additional block-local
obligation has no outer-graph analogue: a `.pointwise`/`.axiswise` step's source must be a
preceding `.assign` step's destination.

The base block has empty context. The step block's context is the scan recurrence domain
`stepExtents`, derived from `historyExtents.map (· - 1)`. `checkScanPlan` establishes these exact
equalities; they are not worker
assumptions.

This gives the plan a synchronous normal form. A checked block is the acyclic combinational graph for
one logical instant; persistent state captures are delayed inputs; base writes initialize those
delays; designated state results form the next-state tuple; and simultaneous commit is the clock
edge. This analogy motivates the separation but does not introduce clocks, streams, or a general
synchronous-dataflow runtime.

### 6.3 State interface

Each ordered `StateSlot` records:

- the outer graph destination slot for the complete state history;
- the tensor dimensions occupied by advancing axes, in scan-context order; and
- the materialization policy, initially `completeHistory`.

The state index, not a source name, identifies the state inside base and step capture/write maps.
The outer signature table is authoritative: the checker resolves the destination slot to its
`TensorSignature`, and checked accessors may expose that validated pair without duplicating the
signature in raw state data.

### 6.4 Block captures

Base and step blocks need explicit positional inputs:

- an external capture maps an already-available outer graph slot to a block input slot;
- a state capture maps a persistent state index to a block input slot; and
- state captures are permitted in the step block but rejected in the first-version base block.

The step worker binds every state capture to the same immutable pre-step snapshot. A block cannot
name or access the mutable state accumulator directly.

### 6.5 Write geometry

`StateWriteMap` associates:

- one block output slot;
- one persistent state index; and
- one `AffineMap` from scan-context-plus-slice coordinates to complete state coordinates.

Base writes have empty scan context and may insert literal boundary coordinates. A state's
`baseWrites` may contain more than one `StateWriteMap`, provided their target regions are pairwise
disjoint; `checkScanPlan` ([§7.3](#73-scan-structural-checks)) owns that disjointness check across
the whole list, not just between a pair. In practice this geometry admits at most one write per state
that leaves any axis `.free`; additional writes must pin every axis to a specific literal (see
[§5.1](#51-accepted-source-fragment) for why two free-axis writes for one state can never be
disjoint). Step writes use the current recurrence coordinate and add one in each advancing state
dimension. Non-advancing state dimensions are an order-preserving projection of the result slice.

The raw representation may use the existing general `AffineMap`; the first checker admits only the
canonical base and step geometries above. This keeps the plan language extensible without making the
first worker prove arbitrary scatter injectivity.

### 6.6 Scan node and outer graph

Conceptually:

```text
RawScanPlan
  states
  baseBlock
  baseCaptures
  baseWrites
  stepBlock
  stepCaptures
  stepWrites
  historyExtents
  iterationOrder
  boundaryPolicy
  snapshotPolicy

PlanStep
  assign AssignPlan
  scan RawScanPlan
```

`RawEvalPlan.steps` becomes `Array PlanStep`. Every step exposes a uniform checked graph interface:

- `sourceSlots`: outer graph tensors that must already exist;
- `destinationSlots`: outer graph tensors the step produces; and
- `checkedMeaning`: either one `CheckedAssignPlan` or one `CheckedScanPlan`.

A scan has several destination slots. Internal state feedback is not an outer graph forward read; it
is contained inside the validated `PlanStep.scan` and its `CheckedScanPlan`.

`historyExtents` is semantic input data. The checker derives
`stepExtents = historyExtents.map (· - 1)` after rejecting zero extents. For a recurrence coordinate
`q` and `D = stepExtents`, first-axis-fastest order is increasing mixed-radix rank:

```text
rank_D(q) = sum_i q[i] * product_{j < i} D[j]
```

The enumerator must provide the corresponding inverse on the domain:
`unrank_D(rank_D(q)) = q`. This equation, not a library cartesian-product convention, defines
`IterationOrder.axisZeroFastest`.

### 6.7 Checked scan evidence

`CheckedScanPlan` has a private constructor and retains:

- checked base and step blocks;
- validated external and state captures;
- validated state signatures and dimension maps;
- validated base and step write maps;
- unique state-result coverage;
- admitted policies; and
- an opaque `CausalityCertificate`.

Workers inspect trusted accessors but cannot construct this evidence.

### 6.8 Producer, checker, and consumer matrix

This is the third and final view of the same policy set introduced in
[§4](#4-problems-wave-f-must-remove) (what replaces each implicit rule) and
[§5.3](#53-fixed-first-version-policies) (the concrete value each policy takes): here, who builds,
validates, and reads each field. No conceptual field is admitted without all three roles:

| Data | Source compiler producer | Checker owner | Dense consumer |
|---|---|---|---|
| Assignment context shape/positions | Base/step affine lowering | `checkAssign` | `runDenseAssignAt` coordinate placement |
| Block signatures and inputs | Base/step block construction | `checkPlanBlock` | Block store initialization |
| Block captures | Name-to-slot/state classification | `checkScanPlan` (including exact block-input coverage) | Base/step input binding |
| Ordered block assignments | Scheduled base/recur order | `checkPlanBlock` | Sequential block execution |
| Block outputs | Designated base/state-result classification | `checkPlanBlock` for production; `checkScanPlan` for exact write coverage | Write-source lookup |
| State destination slots | State-name-to-outer-slot allocation | `checkScanPlan` and `checkPlan` | Complete-state allocation and final store insertion |
| State advancing dimensions | LHS slot-position analysis | `checkScanPlan` | Causality and write-coordinate interpretation |
| Base write maps | `iterAt` LHS lowering | `checkScanPlan` | Base slice commit |
| Step write maps | `iterNext` LHS lowering | `checkScanPlan` | Simultaneous next-state commit |
| History extents / derived step extents | Signature-driven axis-size resolution | `checkScanPlan` | State allocation and recurrence-domain enumeration |
| Iteration order | Fixed compiler tag | `checkScanPlan` | Coordinate enumeration |
| Boundary policy | Fixed compiler tag | `checkScanPlan` | State initialization and base phase |
| Snapshot policy | Fixed compiler tag | `checkScanPlan` | State capture binding and commit timing |
| Materialization policy | Fixed compiler tag | `checkScanPlan` | Final outer-slot insertion |
| Causality certificate | Constructed only by `checkScanPlan` | `checkScanPlan` | Trusted precondition; no runtime rediscovery |

If implementation reveals a field with no real producer or consumer, remove it rather than add a
placeholder. If a worker needs information absent from this table, revise the design before adding a
fallback convention.

## 7. Checking and failure ownership

### 7.1 Local assignment checks

`checkAssign` retains all Wave C checks and adds:

- context/output/reduction positions partition the term basis;
- term context projection equals assignment context shape.

No scan-specific state rule belongs in `checkAssign`. The coordinate supplied later is a runtime
value: `runDenseAssignAt` validates its rank and bounds against the checked context shape before
execution. `checkPlan` separately requires every top-level `PlanStep.assign` to have empty context,
because `runDenseAssign` invokes it with `[]`; `checkPlanBlock` requires every block assignment to
match that block's declared context.

### 7.2 Block checks

`checkPlanBlock` owns:

- input-slot range, uniqueness, and ordering;
- disjoint input and assignment-destination slots, so no block step can overwrite an input;
- assignment destination uniqueness;
- source availability and production order;
- local `checkAssign` composition;
- context-shape agreement across every assignment;
- output-slot range and uniqueness; and
- output production and signature agreement.

This is the local-graph analogue of `checkPlan`, not a special evaluator convention.

### 7.3 Scan structural checks

`checkScanPlan` owns:

- non-empty states and advancing axes;
- history extents at least one and derived step extents;
- state destination slots in range and unique;
- complete state signatures consistent with advancing-dimension maps;
- block capture range, uniqueness, signature agreement, and permitted source kind;
- a bijection between each block's declared input slots and its capture targets, so every input is
  bound exactly once and no capture targets a non-input slot;
- exact base-block context `#[]` and exact step-block context
  `stepExtents`;
- one or more base writes and exactly one step write per state;
- every write source is a declared output of its corresponding block;
- a bijection between each block's declared outputs and its write sources, so no output is discarded
  or committed twice — for a state with several base writes, each is a distinct block output bound to
  a distinct `StateWriteMap`, not one output replayed at several coordinates;
- write-result signature agreement with the unpinned state dimensions;
- admitted base and step geometry;
- boundary-touching base writes, pairwise disjoint across the full `baseWrites` list for one state
  (not just checked pairwise between two arbitrarily chosen writes); disjointness is a check over
  each write's declared index region alone — it never inspects or compares RHS values, so ranges
  that happen to agree at a shared coordinate are still rejected;
- admitted traversal, boundary, snapshot, and materialization policies; and
- causality of every persistent-state read.

`checkPlan` owns only outer composition: every source outer slot is available, no scan destination
overwrites an input or earlier destination, and every non-input outer slot is produced exactly once.

### 7.4 Causality certificate

`CausalityCertificate` means schedule legality, not allegiance to one affine pattern. For every
persistent-state read `r` at consumer coordinate `q`, exactly one of these cases must hold:

1. `r` is out of bounds and the checked zero-padding policy defines it;
2. `r` is in the initialized boundary region and checked base initialization defines it; or
3. `r` has a unique recurrence producer `p`, and `rank(p) < rank(q)` under the checked order.

The first checker proves this contract conservatively. For every advancing state dimension, the read
row must have coefficient `1` for the corresponding scan-context position, coefficient `0` for every
other context, output, and reduction position, and non-positive bias. With canonical writes at
`q + 1`, an interior read has producer `p = r - 1`, which is strictly earlier under the admitted
rank. The checker should test this implication directly over the canonical geometry rather than
leaving it as worker folklore.

The recognizer admits `G[l]`, `G[l - k]`, and `G[r, c]` when writing
`G[r + 1, c + 1]`. It rejects look-ahead, scale-dependent coordinates, cross-axis permutations in
state dimensions, and slice-dependent state-history addressing. A later affine-dependence checker
may admit more plans while producing the same opaque certificate. Workers must not grow fallback
semantics or rediscover legality.

External reads are not feedback and need no causality certificate, but their affine maps remain
subject to ordinary checked ranks and zero-padding policy.

### 7.5 Error families

Use four layers:

- `CapabilityError` for syntactically visible unsupported source found before shape inference;
- `ScanCompileError` for source scan pairing, specialized geometry, block dependency, or causality
  failures discovered after shapes and affine maps are available;
- `PlanError.scanError(stepIndex, ScanPlanError)` for malformed raw scan data; and
- `PositionalInputError` for runtime tensor shape/storage failures at external captures.

`ScanPlanError` should have one constructor per checker branch, including context for state, block,
capture, write, and factor indices. In particular, the base-write-overlap branch must carry the state
index and the *pair* of colliding write indices, since a state may now have more than two base
writes and "which two collided" is load-bearing for the error message. Do not flatten it to rendered
strings. A worker may report a genuine resource failure, but it must not rediscover malformed geometry, missing state results,
causality, or block production order.

`PlanCompileCause.scan` owns `ScanCompileError` and preserves warnings already produced by shape
inference. A compiler-generated raw scan reaches `checkScanPlan` only after this source-facing
validation; a later checker rejection is therefore an internal compiler bug wrapped as
`PlanCompileCause.invalidPlan`. Raw plans constructed directly still receive the corresponding
`ScanPlanError`.

Failure precedence remains:

```text
capability preflight
input signature validation
shape inference
scan source specialization
raw plan construction
local assignment checking
block checking
scan checking
outer graph checking
runtime binding
runtime execution
```

The first failure in source order wins within each phase.

## 8. Source residualization

### 8.1 Preparation boundary

The public boundary remains:

```text
(ScheduledProgram, InputSignature)
  -> Except PlanCompileFailure PreparedPlan
```

`prepareEvalPlan` still performs no tensor arithmetic.

| Static during preparation | Dynamic during plan execution |
|---|---|
| signatures and `historyExtents` | tensor elements and state-history contents |
| state, capture, write, and outer slots | current recurrence coordinate |
| affine coefficients and base-pin substitutions | affine-map evaluation |
| context, output, and reduction roles | local reductions |
| traversal, boundary, snapshot, materialization, and numeric policies | block invocation and state commit |

This is one explicit specialization boundary, not a request for a generic staging framework. For a
supported scan, preparation:

1. runs total scan-aware syntactic capability preflight;
2. validates required external signatures;
3. includes plain, base, recurrence, and scratch statements in shape inference;
4. allocates outer slots for external inputs and complete state outputs;
5. chooses the ordered scan context from the scheduled node and validates every state against it;
6. substitutes validated base pins into RHS affine biases, removes those UIDs from term bases, and
   compiles the resulting assignments into an empty-context block;
7. compiles recurrence and scratch assignments into a scan-context block;
8. replaces state/external names with explicit captures;
9. replaces base/result names and LHS slots with explicit state write maps;
10. lowers affine reads over `context ++ output ++ per-term reduction` bases;
11. validates source pairing, block dependencies, specialized geometry, and causality, returning a
    typed `ScanCompileError` for an unsupported or ill-formed scheduled scan;
12. constructs `RawScanPlan`, then calls `checkScanPlan`;
13. inserts `PlanStep.scan` into the outer raw graph;
14. calls `checkPlan`; and
15. records only persistent state names in `materializedNames`.

The compiler is expected to generate a plan accepted by its checker after source-facing scan
specialization succeeds. A checker rejection at that point is an internal compiler bug wrapped as
`PlanCompileCause.invalidPlan`, not a user capability outcome.

### 8.2 Source ordering

The compiler preserves:

- scheduled top-level node order;
- ordered state order from the scan node;
- base statement order;
- recurrence and scratch statement order inside the block;
- factor and term order;
- reduction coordinate order;
- advancing-axis order; and
- source declaration/read order at the external boundary.

No sorting by state name or UID is permitted.

### 8.3 State and scratch classification

The compiler, not the worker, classifies:

- persistent states: same-name base statement(s) — one or more — paired with a recurrence result
  selected by the scheduled scan;
- step results: designated recurrence assignments for those states;
- scratch: every other recurrence-list destination; and
- externals: reads not produced by the block and present before the outer scan node.

Compiler-generated nonlinearity scratch is now handled directly: thread 4 Task 4 admitted
`.pointwise` and `.axiswise` as **plan operations** (both at the outer `PlanStep` level and inside
`RawPlanBlock`'s `BlockStep` element type), and `compileScan` residualizes each nonlinear scan-block
statement into an internal `.assign` scratch step immediately followed by the real `.pointwise`
or `.axiswise` step. That scratch is block-local by construction — the residualizer emits it inside
the scan block — so it never becomes state merely because a generated name appears in a base list.
(The initial F3 draft of this section framed nonlinearities as "not yet plan operations"; that is
the historical, pre-Thread-4 scope.)

### 8.4 Base compilation

A base LHS's `iterAt` positions become literal components of its `StateWriteMap`. Its remaining free
positions form the base result slice. The first version requires each base write to touch at least one
advancing dimension at coordinate zero. A state's boundary may be split across several base
statements sharing its name — each compiles to its own `StateWriteMap` — provided the compiler
records them as an ordered list rather than assuming a single result; `checkScanPlan` then rejects
any pairwise-overlapping regions across that list.

The same pins also seed RHS evaluation. For each normalized read row with affine constant `b`,
coefficients `cᵤ`, and pin map `p`, base compilation computes:

```text
b' = b + sum(cᵤ * p[u]) for every pinned UID u
```

and removes every pinned UID before densifying the remaining row. Per-term contracted UIDs are
computed only after that removal, so a pinned axis is never accidentally contracted. This is the
plan-compilation counterpart of the legacy evaluator's `baseCoord := freeCoords inserted into seed`;
write geometry alone is insufficient to preserve base RHS semantics.

Base reads from persistent state are rejected initially. This prevents initialization order from
creating a second implicit state machine. Base blocks may read external inputs and earlier block-local
scratch if the block checker establishes production order.

### 8.5 Step compilation

Every advancing UID becomes a context coordinate. `iterNext` positions disappear from the result
slice and become `+1` rows in the step write map. RHS index expressions may refer to scan-context,
slice-output, and contracted axes; the compiler lowers all three into one affine basis.

All state captures bind the same pre-step snapshot. Step state-result slots are distinct from
persistent state-input slots. This makes simultaneous commit representable rather than conventional.

### 8.6 Named runtime boundary

`pack` remains responsible only for external named tensors. Scan states are produced, not supplied,
under the current source language. `unpack` inserts every materialized complete state history at its
final source name and preserves unrelated original inputs exactly as it does for plain plans.

Warnings from shape inference survive successful scan execution and any later binding or execution
failure.

## 9. General Dense scan semantics

*General* here means: this worker executes any checked `ScanPlan` the same way, with no
one-axis/coupled/n-dimensional special case. It does not mean the accepted source fragment is broad —
that remains the narrow set fixed in [§5.1](#51-accepted-source-fragment).

### 9.1 Worker independence

The checked scan worker must not import or call:

- `Eval.evalScan` or `evalScheduled`;
- `evalStmtSliceSeeded`;
- `evalAssignSeeded` or `evalAssignDtypedSeeded`;
- legacy `Gather`, `Contract`, `Nonlin`, or `Slots` helpers;
- `ScanStmt` accessors;
- `finalizeScans`; or
- the legacy `cartesianList` and `writeSliceAtMulti`.

Those functions define the independent oracle and depend on source names, UIDs, AST values, or
unchecked writes. The Plan worker should implement the checked policies directly. Deliberate
independence here is more valuable than deduplicating a small coordinate enumerator.

### 9.2 Allocation and bases

For each state, allocate a `DenseTensor.zeros` with its checked complete shape. Execute the base block
once with empty context. Apply every base write for that state, in declared order, through checked
geometry — a state may have several, one per disjoint boundary face. Because `checkScanPlan` has
already established that they are pairwise disjoint, declaration order does not affect the result in
this version; it is retained in the worker semantics only so a later relaxation to genuinely
overlapping regions has an unambiguous order to define its resolution policy against, not because
order is observable here.

The worker performs no bounds recovery or default geometry. Every produced base slice must have the
checked signature, and every generated write coordinate is in bounds by construction.

### 9.3 Iteration

Enumerate `stepExtents` by increasing checked mixed-radix rank. Rank/unrank belongs to the scan
worker and is intentionally independent from the local assignment kernel's coordinate enumerator.
At each coordinate:

1. freeze the current complete state array as `oldState`;
2. bind all state captures from `oldState`;
3. bind external captures from the outer positional store;
4. execute the checked step block with `runDenseAssignAt`;
5. collect every designated state-result slice;
6. derive all checked write coordinates; and
7. commit all slices to the mutable state accumulator only after every result succeeds.

If one block assignment fails, no state write from that coordinate is committed.

### 9.4 Return and outer composition

After the recurrence domain is exhausted, place every complete state tensor in its outer destination
slot. Block scratch and state-result slices are discarded. `runDensePlan` then continues with the
next outer `PlanStep`, so later plain or scan nodes may read the materialized histories.

## 10. Correctness laws

Wave C's laws continue to govern scan-free steps. Wave F extends their domains and makes the scan law
operational.

### Law 1: source residualization

For an accepted schedule and conforming inputs:

```text
prepareEvalPlan(schedule, signature) = ok prepared

implies

runPreparedDense(prepared, namedInputs)
  =obs evalScheduled(schedule, namedInputs)
```

For scans, `=obs` includes complete environment keys, complete state tensors, warnings, typed
success/failure structure, and bit-exact `reference64` data.

The law applies only to the source fragment whose checked Jacobi semantics is observationally equal
to the legacy worker. A source scan outside that fragment must be rejected before plan execution.

### Law 2: checked construction

Successful local, block, scan, and outer checks imply every documented worker precondition:

```text
checkAssign(rawAssign) = ok checkedAssign
checkPlanBlock(rawBlock) = ok checkedBlock
checkScanPlan(rawScan) = ok checkedScan
checkPlan(rawPlan) = ok checkedPlan
```

Each checker composes the layer below it rather than duplicating its validation.

### Law 3: backend interpretation agreement

Dense, PyTorch, and JAX interpretations of one checked plan have the same result under the
plan's numeric mode. Wave F establishes the Dense meaning; later waves add other interpretations.

### Law 4: boundary representation agreement

Packing external named inputs, running a scan-containing checked plan, and unpacking persistent state
outputs preserves the complete source-visible environment and warnings. Block-local scratch cannot
appear at this boundary.

### Law 5: scan refinement

Let `runGeneralScan` be the explicit-order semantics in Section 9. A specialized implementation may
run only when a separate checker recognizes its required evidence:

```text
runGeneralScan(scanPlan, state, inputs)
  =mode runSpecializedScan(scanPlan, state, inputs)
```

One-axis `lax.scan`, bounded-history carries, nested scans, compile-time unrolling, and parallel
prefix are instances of this law, not alternative definitions of `ScanPlan`.

For a specialized representation such as a bounded carry, equality is discharged by a simulation
relation, not by assuming that compact carry and complete history are isomorphic:

1. initialized complete histories relate to the specialized initial carry plus empty emitted prefix;
2. one general step and one specialized step preserve the relation; and
3. the final carry plus emitted slices reconstructs the complete materialized histories.

An optimization-specific certificate may strengthen these obligations. It may not weaken the
observable complete-history result.

### Law 6: snapshot independence

For a checked scan coordinate, permuting the order in which designated state-result slices are
committed cannot change any result computed by that coordinate. This follows because every state
capture is bound from one immutable pre-step snapshot and no state destination is readable through a
block-local result slot.

This law distinguishes the intended Jacobi semantics from ordered Gauss-Seidel mutation.
Within the first causal fragment, an early commit at `q + 1` is not observable through an admitted
state read at `q + b`, `b <= 0`; therefore this law is checked structurally through capture/result
separation and worker inspection, not claimed as a value-level mutation test. Adversarial source
reads that could observe the distinction are rejected before plan construction.

## 11. Evidence and test strategy

### 11.1 Existing evidence

Current scan evidence includes:

- direct one-axis, nonlinear, coupled, slice-level predicate-dispatch, and rejection cases in
  [`ScanTest.lean`](../leanncd/test/Eval/ScanTest.lean);
- one-, two-, and three-axis recurrence examples in
  [`RecurrenceTest.lean`](../leanncd/test/Eval/Portfolio/RecurrenceTest.lean);
- coupled, scratch-heavy, state-space, contraction, and rejection fixtures across the Portfolio
  suite; and
- 17 generated scan cases, an independent general one-axis unroller, and one template-specific
  `2 x 2` grid unroller under
  [`PropertyOracle/`](../leanncd/test/Eval/PropertyOracle/).

These establish useful behavior but do not yet cover the checked plan path.

### 11.2 Coverage gaps Wave F must close

Hand-written fixtures are required for:

- adversarial source reads that could distinguish Jacobi from ordered mutation, which must receive a
  typed source rejection;
- asymmetric multi-axis extents such as `2 x 3`;
- coupled multi-axis states;
- iteration axes in different tensor positions;
- state dimension/order disagreement;
- extent `1` and typed rejection of extent `0`;
- non-positive deep history and early zero padding;
- zero and nonzero multidimensional base-pin substitution in RHS reads;
- general affine look-ahead rejection;
- future reads hidden through scratch;
- base/result slice-signature mismatch;
- duplicate or missing state writers;
- interior-only base writes (touching no boundary);
- a main free-axis face write plus a disjoint fully-pinned point override for one state, accepted
  (F0 requires an actual compiled/run `evalScan` fixture for this, not a hand-derived trace — see
  [§13](#13-implementation-slices));
- two free-axis face writes for one state (e.g., row `0` and column `0`, both left fully free) —
  rejected, since two free-axis writes for one state are never disjoint (see [§5.1](#51-accepted-source-fragment));
  include the sub-case where the two RHS expressions would evaluate to equal values at the shared
  corner, to confirm the checker never inspects RHS values when deciding disjointness;
- block forward reads and cycles;
- arbitrary scan-axis positions;
- rank/unrank inversion for asymmetric `2 x 3`, `3 x 2`, and extent-one shapes;
- exact axis-zero-fastest mixed-radix traversal; and
- scratch non-materialization.

The generated corpus must not be credited with dimensions it does not vary.

### 11.3 Test layers

| Layer | Primary evidence |
|---|---|
| Contract | Capability and policy matrices; observed legacy fixtures; mutation pairs. |
| Contextual kernel | Empty-context parity; context-sensitive affine reads; rank/bounds mutations. |
| Block | Chains, fan-out, scratch lifetime, output interface, forward-read mutations. |
| Scan checker | One mutation per `ScanPlanError`; constructor privacy tests. |
| General worker | Hand-computed self, coupled, history, asymmetric n-D, boundary, and base-only cases. |
| Compiler/boundary | Source-to-plan state/capture/write mapping; base-pin substitution; alpha-renaming; warning preservation. |
| Differential | `runPreparedDense` versus `evalScheduled` and independent unrolling. |
| Audit | Import graph, semantic-field inventory, capability manifest, full build. |

### 11.4 Mutation discipline

Every regression fixture must be demonstrated to fail under a targeted mutation before it is relied
upon. Required test-the-tester mutations include:

- redirect a state capture to a step-result slot, which the block/scan checker must reject;
- bind a state capture from a deliberately different accumulator rather than the supplied immutable
  snapshot in the worker's pure input-binding helper;
- reverse the mixed-radix rank order;
- change one step-write `+1` bias;
- drop one state write;
- shrink one of a state's several disjoint base writes so it now shares a coordinate with another,
  which `checkScanPlan` must reject;
- turn one causal bias from `0` to `+1`;
- leak one scratch result into materialized outputs; and
- alter one context coefficient.

The implementation plan for each slice must record both observations: the mutation fails, and the
restored implementation passes.

### 11.5 Independent unrolling

The existing one-axis unroller assumes trailing iteration positions and immediate-predecessor reads;
the template-specific `2 x 2` unroller is narrower still. Neither currently covers deep history,
arbitrary advancing-dimension positions, or scratch-heavy recurrence blocks. Generalize the
independent one-axis oracle for those dimensions and add a rectangular uniform all-axis `+1` explicit unroller
whose representation and traversal implementation are independent of `runGeneralScan`. Do not reuse
either implementation inside the worker. Pin exact generated-case counts and report
accepted/rejected categories.

Keep three implementations distinct:

| Artifact | Purpose | Must not share |
|---|---|---|
| Source-level explicit unroller | Independent oracle | General worker coordinate/write implementation |
| Checked general worker | Reference plan semantics | Legacy evaluator and source unroller |
| Future checked-plan unroller | Production optimization | Source-oracle implementation |

## 12. Backend lowering boundary

### 12.1 One-axis `lax.scan`

A checked one-axis plan may later lower to `lax.scan` when its state capture and write geometry can be
represented by a fixed-shape carry. Immediate-predecessor recurrences may carry current slices;
deeper-history recurrences need a bounded-history window or complete fixed-shape state.

This choice is backend lowering metadata. It does not change complete-history `ScanPlan` meaning.

### 12.2 Multi-axis lowering

The first backend implementation should flatten the checked cartesian order and carry complete
fixed-shape states. Nested scans are a later recognized optimization and must agree with the flat
general worker.

### 12.3 Parallel prefix

Neither `ScanStmt.isAffine`, absence of a nonlinearity, nor use of sum-product is sufficient evidence
for parallel prefix. A future `ParallelScanPlan` needs a checked associative summary operation and
identity under the active `NumericMode`, such as a recognized affine-transformation composition.
Mathematical associativity over reals does not establish operational associativity for
`reference64`: reassociation may change binary64 rounding and violate bit-exact agreement.

### 12.4 Wavefront scheduling

The rectangular all-axis `+1` fragment may later admit wavefront execution. Coordinates on the same
legal dependence frontier can run together when a checker establishes schedule legality and
disjoint writes. This is distinct from parallel prefix: it preserves each cell's arithmetic order
and needs dependence/disjointness evidence, not an associative summary operation. The explicit total
order remains the Wave F reference semantics.

### 12.5 Compile-time unrolling

Small static scans may eventually use a separate checked-plan unrolling transform as an optimization.
It must satisfy Law 5 against the general worker while the source-level unroller remains an
independent oracle. Promoting the oracle implementation itself would make optimizer/oracle agreement
tautological.

## 13. Implementation slices

Wave F should be implemented one slice at a time. Write the next slice's detailed implementation plan
only after the previous slice lands. Every plan-level Lean block must be compiled via the repository's
`slice-plan` discipline before that plan is dispatched.

### F0 - executable scan contract

**Production changes:** none. F0 produces no new Lean types — not even stubs. "Checked data" below
means the concrete value each policy takes and the fixture that observed it, written down in the
plan/spec and validated against the legacy evaluator; the corresponding `RawScanPlan`,
`CheckedScanPlan`, and checker types are F2-F3 production changes that must agree with these
observed values, not anticipate them.

Deliver:

- an exhaustive source rejection matrix for `.scan` and `.scanPre`, assigning every case to either
  pre-shape `CapabilityError` or post-shape `ScanCompileError`;
- the concrete value and an observed fixture for every policy in Section 5.3;
- observed legacy fixtures for self, coupled, external-read, contraction, history, and homogeneous
  diagonal n-D scans;
- zero and nonzero multidimensional base-pin fixtures whose RHS reads depend on the pinned UID;
- explicit accepted/rejected outcomes for extent zero/one, bases (including a face-plus-point-override
  multi-write accepted, and two free-axis face writes for one state rejected — see
  [§5.1](#51-accepted-source-fragment)), geometry, scratch, and causality;
- an actual compiled, run `evalScan` fixture — not a hand-derived trace — for two same-named base
  statements in the accepted face-plus-point-override shape, confirming allocate-then-fill
  accumulation behaves as expected, since no existing test exercises this pattern (only
  different-named coupled states, e.g. `ScanTest.lean`'s `G`/`H` case, are currently covered); pair it
  with the collision mutation from §11.4 to observe the *legacy* path's silent last-write-wins
  behavior at a shared coordinate, for contrast with the checked path's unconditional rejection;
- a typed-rejection fixture for source reads that could observe ordered state mutation, plus
  fixture/mutation pairs for traversal, boundary, and materialization semantics; and
- an exact inventory of existing generator coverage.

**Gate:** no Wave F policy depends on prose, `getD`, name order, or an untested helper. Every expected
value has been observed from the real evaluator, and every regression fixture fails under its named
mutation.

This is a substantial contract slice, not a tiny test append: it fixes the semantic decisions every
later checker and worker implements.

**F0 completion record (2026-08-08).** Landed as `Eval.Plan.ScanContractTest` (compiler-checked
classifier over bare `ScanStmt`s, `classifyScanStmtF` etc.) plus mechanical legacy-behavior fixtures
appended to `Eval.ScanTest`, registered in the default build target; `lake build` green (8,640 jobs).

§5.3 policy-value inventory:

| §5.3 policy | Already observed by |
|---|---|
| Extent meaning (full history, `stepExtents = extent - 1`) | `ScanTest.lean`'s linear-scan fixture (`l` size 3 → 2 recurrence steps writing positions 1–2) |
| Traversal (mixed-radix, axis zero fastest) | `RecurrenceTest.lean` RC6/RC8 (2-D/3-D grids; row/plane-major write order matches declared axis order) |
| Boundary (zero-init, then base overlay) | RC6: "boundary cells (r=0 or c=0) keep their zero-default... except where an explicit base stmt pins a slice" |
| Base placement (in-bounds, boundary-touching) | RC6/RC8's base statements, all pinning to literal `0` |
| History reads (non-positive look-back, zero pad) | `ScanTest.lean`'s deep-history fixture added by F0 (`k=2` look-back, zero-padded out-of-range reads) |
| Outputs (complete histories only) | every `evalScan` fixture in this file and in `RecurrenceTest.lean` (`evalScan`'s own final `return stateNames.filterMap ...`, `Scan.lean:115`) |
| Numeric mode (`reference64`, declared order) | implicit in every existing fixture's exact-value assertions; no distinct fixture needed |
| Snapshot / commit (immutable pre-step state, simultaneous commit) | **not soundly observed — the Jacobi/Gauss-Seidel snapshot-safety fixture added by F0 shows the current implementation is NOT structurally safe; this is what Wave F's checked worker will fix** |

Generator-coverage inventory (the last Deliver bullet above):

`test/Eval/PropertyOracle/ScanGen.lean`'s `enumScanCases` is a curated (not combinatorial) family of
exactly 17 cases (`#guard enumScanCases.length == 17`), built from 6 templates:

| Template | Varies | Wave F relevance |
|---|---|---|
| 1: linear self-scan | scan length `L`, coefficient sign | in Wave F's admitted kernel |
| 2: nonlin self-scan (`relu`) | `L`, coefficient sign | **outside** Wave F's admitted kernel (pointwise nonlin) |
| 3: coupled 2-state (`G`/`H`) | scan length `L ∈ {2, 3}` | in Wave F's admitted kernel; `c.base.length > 1` here means two **differently-named** states' base statements, not one state's multiple base writes — F0's multi-base-write fixture is the first test of the latter |
| 4: state + external read at current coordinate | `L ∈ {2, 3}` | in Wave F's admitted kernel; differential/property-oracle-layer counterpart to F0's Contract-layer external-read fixture |
| 5: tropical aggregator (`maxreduce`/`minreduce`) | `L ∈ {2, 3}`, aggregator (max vs. min) | **outside** Wave F's admitted kernel (only real sum-product is admitted) |
| 6: 2-D grid-DP | fixed | in Wave F's admitted kernel; single base write per state, not multi-write |

`ScanOracle.lean` compares each case against `ScanUnroll.lean`'s independent unroller. *As surveyed
at F0* that unroller was the pair `unrollScan1D`/`unrollScan2D` — 1-D and one fixed 2×2 template
only, with no deeper n-D, deep-history, or multi-base-write support, which is part of why F0's own
fixtures were needed. **F4 Task 5 deleted both**, replacing them with a single `unrollScanNode`/
`independentRun` over `ScheduledProgram` that handles arbitrary advancing-dimension positions and
order, affine deep history, several base writes per state, and block-local scratch; see the F4
completion record below. The corpus surveyed here is unchanged either way — none of the 17 generated
cases exercises: deep history (`k > 1` look-back), a
constant/non-loop-relative state read, extent zero or one, or more than one base write for a single
state — every one of those is new coverage from F0's fixtures, not already present in this corpus.

### F1 - contextual local kernel

Generalize `AssignPlan`/`TermPlan`, `checkAssign`, and the Dense local worker with explicit context.
Keep `runDenseAssign` as the empty-context wrapper.

Deliver:

- context shape and context-position data;
- partition and projection checks;
- `runDenseAssignAt`;
- empty-context structural and bit-exact parity over all Wave C kernel fixtures; and
- context-sensitive affine-read fixtures and checker mutations.

**Gate:** every existing Wave C plan test remains green; top-level assignment semantics and raw graph
ordering are unchanged; the contextual worker introduces no DSL, UID, name, or legacy-evaluator
dependency.

**F1 completion record (2026-08-08).** Landed with `runDenseAssignAt` (context-indexed primitive),
`PositionalInputError.contextShapeMismatch` (runtime context validation), `validateContext` (private
helper), updated `runDenseAssign` (empty-context wrapper), and context-sensitive fixtures in
`Eval.Plan.KernelDenseTest`; `lake build` green (8,640 jobs). `checkPlan` rejects any top-level step
with non-empty context (`PlanError.topLevelContextNotEmpty`) — a policy a future F2 slice will need
to relax when it introduces blocks with real, non-empty context.

This slice is separate because it changes existing production code with many dependents and is a
natural rollback unit.

### F2 - checked plan-block vertical slice

Add `RawPlanBlock`, its private checked wrapper, block errors, `checkPlanBlock`, and `runDenseBlock`.
Do not yet add a scan constructor to `RawEvalPlan`.

Deliver:

- local block checking;
- input range/order and input/destination disjointness checks;
- checked context-parameterized block execution;
- private-constructor compile-failure checks; and
- one mutation per reachable new error branch.

**Gate:** every `CheckedPlanBlock` is executable; malformed raw block data cannot reach
`runDenseBlock`; checked block data contains no names, UIDs, functions, callbacks, backend objects,
or unordered maps.

**F2 completion record (2026-08-14).** Landed as `Eval.Plan.Block` (`RawPlanBlock`, `BlockError`,
`CheckedPlanBlock`/`checkPlanBlock`, `runDenseBlock`) plus context-indexed positive/mutation
fixtures in `Eval.Plan.BlockTest`; `Block.lean` is reachable from `import LeanNCD`, `BlockTest`'s
fixtures are registered in the default `Tests` build target (not reachable via the `import LeanNCD`
chain); `lake build` green (8,646 jobs). Reuse happens at the leaf level, not the loop level:
`checkPlanBlock` calls `checkAssign` per node, `runDenseBlock` calls `runDenseAssignAt` per node
(pulling in `Coordinates.lean`'s coordinate-math primitives transitively), and every `BlockError`
case that duplicates a `PlanError` case is wrapped as `.wiring (...)` rather than reimplemented as a
freestanding lookalike — none of these leaf primitives were reimplemented. The two wiring/store
loops themselves are NOT shared, contrary to an earlier draft of this record: `checkPlanBlock`'s
availability/production-order loop is a structural copy of `checkPlan`'s outer-graph loop
(`Check.lean`), and `runDenseBlock`'s store-initialization loop is a structural copy of
`runDensePlan`'s (`Dense.lean`) — both differ from their originals only by field renames
(`inputSlots`→`inputs`, `steps`→`assignments`) and, for the checker, `.wiring (...)` error wrapping.
No shared, parameterized helper exists for either loop. Two items are known and deliberately
deferred, not fixed here, for two different reasons: (1) the wiring-loop and store-init-loop
duplication above is deferred because factoring either into a shared helper requires editing
`Check.lean`/`Dense.lean`, which this plan's Global Constraints place out of F2's additive-only
scope — a candidate for a future reuse-cleanup slice; (2) `runDenseBlock` returning the full local
store rather than a value projected to `raw.outputs` is deferred for an unrelated reason — this
plan adds no scan constructor, so no caller yet exists to consume projected block outputs, and
projecting now with zero callers would be speculative rather than scope-driven; F3 (the
scan-constructor slice) is what should decide the output-projection contract.

### F3 - checked scan graph vertical slice

Add `RawScanPlan`, `PlanStep`, private checked scan evidence, scan checking, outer graph integration,
and the four-phase worker in Section 9 as one executable vertical slice. Migrate `RawEvalPlan.steps`
to the closed sum, remove the unused in-memory version tag, and update scan-free compilation to emit
`PlanStep.assign` only when both `PlanStep` constructors have Dense interpretations.

Deliver:

- scan structural, capture, geometry, and causality checking;
- pairwise base-write disjointness checking across a state's full `baseWrites` list (not a
  two-write special case);
- multi-output outer graph availability/production checking;
- checked allocation/base application, including applying more than one base write per state;
- independent rank/unrank and explicit-order enumeration;
- immutable snapshots;
- a pure step-input binding helper tested directly to bind every state capture from the supplied
  `oldState` array rather than the mutable accumulator;
- checked block invocation;
- simultaneous state commit;
- complete-history output;
- hand-computed self, coupled, history, base-only, asymmetric rectangular all-axis `+1`, and
  face-plus-point-override multi-base-write fixtures; and
- one mutation per reachable scan and outer-graph error branch.

**Gate:** malformed raw scan data cannot reach a worker; every checked `PlanStep` is executable;
capture-to-step-result, order, and geometry mutations fail at their owning checker or value fixture;
runtime shape/storage mismatches are typed; scan-free plans retain Wave C behavior; the
worker imports no DSL, `Plan.Compile`, or legacy Eval execution module.

The source compiler still rejects scans at the end of this slice. Manual checked plans prove the
language and worker before source residualization is introduced.

**F3 completion record (2026-08-15).** Landed as three new modules — `Eval.Plan.RawStep`
(`RawPlanBlock` relocated here from `Block.lean`, `RawScanPlan`, `PlanStep` — `.assign`/`.scan` —
so `Graph.lean`'s `RawEvalPlan` can reference a scan node without a circular import), `Eval.Plan.Scan`
(the write-geometry classifier `WriteRowKind`/`writeRowKinds`, `baseWriteRowsOk`/`stepWriteRowsOk`/
`writesCollide`, the causality certificate `causalAdvancingRow`/`stateReadCausal`,
`checkScanPlan`/`CheckedScanPlan`, mixed-radix rank/unrank, and the four-phase dense worker
`runDenseScan`), and `Eval.Plan.EvalPlan` (outer-graph `checkPlan`/`CheckedEvalPlan`/`runDensePlan`,
generalized from `AssignPlan`-only steps to `PlanStep`, dispatching `checkAssign`/`checkScanPlan` per
node without re-deriving either's own obligations, plus `PlanCompileCause`/`PlanCompileFailure`
relocated here from `Error.lean` for the same acyclic-import reason `PlanStep`'s own home moved) —
plus edits to `Check.lean`/`Dense.lean` (lost their relocated definitions, left one-line pointers),
`Error.lean` (lost the relocated compile-failure types and Task 1's temporary interim placeholder
constructor), `Compile.lean`/`Adapter.lean`/`Prepared.lean`/`Executable.lean`/`Graph.lean`/
`Block.lean` (import/reference updates only), `LeanNCD.lean` (+3 imports), and `lakefile.toml` (+1
test target). Tests: a new `test/Eval/Plan/ScanTest.lean` (1,309 lines across six parts — structural
geometry (Task 1), the causality certificate (Task 2), and the dense worker (Task 3), each with its
own mutation fixtures), a new `test/Eval/Plan/EvalPlanTest.lean` (outer-graph accept/forward-read/
duplicate-destination/scan-failure-surfacing fixtures, including the multi-destination-scan fixture
added during Task 4's review fix round), and migrations of five pre-existing files off the old
`RawEvalPlan` shape (`GraphCheckTest.lean`, `GraphDenseTest.lean`, `KernelCheckTest.lean`,
`ExecutableTest.lean`, `CompileTest.lean`). `lake build` (default targets) green at **8,651 jobs**.

Four real bugs — three load-bearing, one a misleading doc comment — were found and fixed during this
slice, not merely documented: (1) Task 3 found that `commitWrite` (the plan's own worked design) only
ever committed element 0 of a write's block output, silently dropping every other coordinate for any
write with a genuine free output position (a "face" write) — fixed to iterate every coordinate of the
write's own output shape, verified as a strict generalization (scalar-output writes unaffected) and
confirmed by rebuilding the two required fixtures that exist specifically to exercise free-position
face writes as genuine free writes, not the point-override workaround first tried while isolating the
bug; (2) Task 1's review found `multipleStepWritesForState`'s locator arguments were hardcoded
(`si 0 1`) rather than derived from the actual colliding write indices, masked by the single test case
exercised — fixed to thread real write indices through `checkWrites`'s `rowsByState` grouping; (3)
Task 4's review found that generalizing `checkPlan`'s forward-read availability check to route
through the new generic `PlanStep.sourceSlots` accessor would hardcode `invalidForwardRead`'s `ti`/`fi`
locators to `0 0` for every `.assign`-step failure — a real regression from Wave C's original
per-term/per-factor precision, masked because every existing fixture's bad read happened to sit at
term 0/factor 0 — fixed by keeping a direct per-term/per-factor loop for `.assign` steps outside the
generic accessor (`checkPlan`'s own doc comment now states this explicitly as a design rule, not just
an implementation detail); (4) the same review round also caught and fixed a misleading doc comment:
`PlanStepError.assign`'s docstring read as if `.assign` meant "the failing step was itself an
assignment," when it actually means "this is a graph-level `PlanError`, regardless of which step kind
failed" — a scan step's own capture/destination collision correctly surfaces as `.assign (...)`, not
`.scan`; corrected in place, no rename.

This task (F3's close-out) also applied one fix deferred from Task 4's own review: `checkPlan`'s
`.assign`-branch check order had drifted from Wave C's original order (context-check →
destination-check → source-check → `checkAssign`) to source → destination → context → `checkAssign`
during the `PlanStep` generalization — a real, if silent, regression that Task 4's fix round
correctly diagnosed but a controller drafting mistake left unapplied to the actual file (no
accept/reject outcome ever changed; only which of 2+ simultaneous defects is reported first, an
untested edge case). Restored to Wave C's exact order in `LeanNCD/Eval/Plan/EvalPlan.lean`'s
`checkPlan`, verified by a clean `lake build` (unchanged job count, 8,651).

**Final whole-branch review (2026-08-15), one fix wave.** The review found one further Critical
soundness gap, fixed here: `checkWrites` verified a `.free` write row's POSITION and RANK against the
block output (`baseWriteRowsOk`/`stepWriteRowsOk` compare free positions to `List.range
outputShape.size`, a COUNT) but never its EXTENT against the state's own dimension — precisely the
"write-result signature agreement with the unpinned state dimensions" obligation §7.3 names. A
`RawScanPlan` whose base write declared a shape-`[5]` face into a size-`2` state dimension was
accepted by `checkScanPlan`, after which `runDenseScan` wrote through `flatIndex` into cells
belonging to other rows, or out of the tensor entirely. Fixed by a new `freeExtentsAgree` predicate
(`Scan.lean`, beside `baseWriteRowsOk`/`stepWriteRowsOk`) and a new
`ScanPlanError.writeFreeExtentMismatch (isBase) (writeIndex stateIndex) (stateShape outputShape)`,
thrown from `checkWrites` after geometry admission; `ScanTest.lean` gains the reproducing fixture
(`freeExtentMismatchScan`, a two-field mutation of Fixture 5) asserting the exact error, plus two
`#guard`s pinning the predicate on Fixture 5's own rows. Every pre-existing accepted fixture was
re-checked and none regressed — each was built from consistent data, so its free rows already agreed.
The review's Important/Minor findings were fixed in the same wave: `commitWrite` now documents the
bounds obligation it relies on (see the residual item below); `CheckedScanPlan` gains the
`private mk ::` compile-failure privacy test this project requires of every checked type (§15),
matching `CheckedPrivacyTest.lean`/`BlockTest.lean`'s manual-verification pattern with the literal
captured compiler error; `Eval/AGENTS.md`'s `Check.lean`/`Error.lean` rows no longer contradict the
new `EvalPlan.lean` row about who owns `checkPlan`/`CheckedEvalPlan`/`PlanCompileCause`/
`PlanCompileFailure`; the stale `checkScanPlan` "omits causality" docstring is corrected (flagged by
three prior reviews); an orphaned block comment describing a `CausalityCertificate` type that was
never declared is replaced by an accurate note on `CheckedScanPlan` explaining why no separate
certificate type or field exists; three surviving stale relocation references
(`Graph.lean`/`Block.lean` on `checkPlan`, `Adapter.lean` on `runDensePlan`) now name `EvalPlan.lean`;
and `ScanTest.lean`'s `commitWriteLocal` comment no longer claims to reimplement `commitWrite`'s
equation, stating plainly that it is the scalar-output-only specialization (it embeds the pre-fix
single-coordinate read) valid only for the scalar fixtures that use it.

**Sibling gap closed in the same wave (2026-08-15): an out-of-range PINNED base-write literal.**
Found while writing `commitWrite`'s bounds doc comment above, independently reproduced by a second
reviewer, and NOT closed by the free-extent fix — the same failure class one row-kind over. Geometry
admission recognizes a row as `.pinned lit` without ever inspecting `lit`'s VALUE: `stepWriteRowsOk`
admits no pinned rows at all, but `baseWriteRowsOk` requires only that SOME advancing dimension be
pinned to `0`, leaving every other pinned literal unconstrained. A hand-built base write
`dp[5, 0] := ONE` on a `[2,2]` state was accepted by `checkScanPlan`, after which `commitWrite`
reached `Array.set!` out of range (`lean_array_set_panic`, confirmed reproduced) or committed
silently to the wrong cell. Fixed by a new `pinnedLiteralsInRange` predicate (`Scan.lean`, beside
`freeExtentsAgree`) requiring `0 ≤ lit` and `lit < stateShape[d]` on every pinned row, and a new
`ScanPlanError.writePinnedLiteralOutOfRange (isBase) (writeIndex stateIndex) (stateShape)`, thrown
from `checkWrites` immediately after the free-extent check; `ScanTest.lean` gains the reproducing
fixture (`pinnedOutOfRangeScan`, a one-field mutation of Fixture 5's `pointWrite`: dim-0 bias
`1 -> 5`) asserting the exact error, plus `#guard`s pinning the predicate on Fixture 5's own rows
(in-range true, out-of-range false, negative literal false) and two showing the mutated write is
still admitted by `baseWriteRowsOk`/`writesCollide` — i.e. that no earlier check catches it. The
fixture was verified to discriminate, as this file's other mutation fixtures are: with the new
`checkWrites` guard commented out the build FAILS on that fixture (`checkScanPlan` returned `.ok`),
with it restored the full build is green (8,651 jobs, unchanged). No pre-existing accepted fixture
regressed — `ScanTest.lean` holds all 60 `checkScanPlan` call sites in the suite (`EvalPlanTest.lean`
names it only in prose), 13 of which assert acceptance, and every one still builds: each was built
from real, consistent data whose pinned literals were already in range.
`commitWrite`'s bounds doc comment, which recorded this as a genuinely open obligation, is updated to
state the closure.

Known follow-ups, deliberately not fixed here:

- `papers/wave_c_capability_manifest.md` §1 is now stale — it still documents `admittedVersion = 1`
  and `PlanError.versionNotAdmitted`, both removed by this slice. Updating it is F5's own job per
  §13's F5 deliverables ("updated capability manifest recording removal of the unused in-memory
  version tag"); recorded here only so it is not silently forgotten.
- No fixture distinguishes `multipleStepWritesForState`'s locator behavior for a 3rd conflicting step
  write or writes not at raw index 0/1 — the Task 1 fix is correct by code inspection and an
  independent re-review, but only reasoning, not a dedicated assertion, proves the general case
  (deferred since Task 1's re-review).
- Task 3's 3 `commitWrite` mutation-test functions each duplicate ~20 lines of `runDenseScan`'s own
  body — unavoidable without changing `commitWrite`'s visibility, since the function under test is
  `private` (ruled non-blocking during Task 3's review, consistent with the file's existing
  mutation-copy pattern elsewhere; the final review's fix wave corrected their misleading comment but
  did not remove the duplication).
- `checkWrites` never validates a write's `AffineMap` rank (`w.map.coeffs.size`/`w.map.bias.size`)
  against the state's own rank — the same kind of check `checkAssign` already makes for read plans
  via `affineRankMismatch` (`Check.lean`), but with no write-side counterpart. `writeRowKinds` pads a
  short map via `getD`; `commitWrite`'s `applyAffine` (`Coordinates.lean`) zips and silently truncates
  a mismatched one instead. A hand-built repro (state `#[2,2]`, `map := { coeffs := #[#[]], bias :=
  #[1] }` — one row short) is admitted by every existing check (`baseWriteRowsOk`,
  `freeExtentsAgree`, and now `pinnedLiteralsInRange` all pass), and `commitWrite` then computes the
  wrong flat coordinate — cell `(0,1)` instead of the intended `(1,0)`. Unlike the two bugs this
  record already covers, this one stays within the target's total storage size (no
  `lean_array_set_panic`, no read/write outside the tensor) — it silently commits to the wrong
  in-bounds cell, a correctness gap rather than a memory-safety one. Found and confirmed via
  independent trace during the pinned-literal-bounds fix's own review (not fixed there — correctly
  scoped out as a new, adjacent finding rather than expanding that diff); left here as a known,
  characterized follow-up rather than chased through a fourth fix round.

`JaxExperiment` — the non-default target whose lone glob is `experiments/jax_bridge/
EvalPlanCodegen.lean` — fails to build under this slice, exactly as Task 4's brief predicted and
confirmed. `EvalPlanCodegen.lean` directly iterates `checkedNodes` assuming a bare
`CheckedAssignPlan` element (now `CheckedPlanStepEvidence`), and separately still constructs a
`RawEvalPlan` with the pre-Task-1 shape (`version :=`, bare `AssignPlan` steps) in its own `idRaw`
doctest fixture — two independent breakages, not one:
```
error: experiments/jax_bridge/EvalPlanCodegen.lean:176:49: Invalid field `plan`: ...
error: experiments/jax_bridge/EvalPlanCodegen.lean:316:91: Invalid field `plan`: ...
error: experiments/jax_bridge/EvalPlanCodegen.lean:458:14: Application type mismatch: ... Array CheckedPlanStepEvidence ... expected ... Array CheckedAssignPlan ...
error: experiments/jax_bridge/EvalPlanCodegen.lean:488:4: `version` is not a field of structure `RawEvalPlan`
error: experiments/jax_bridge/EvalPlanCodegen.lean:489:15: Application type mismatch: ... AssignPlan ... expected ... PlanStep ...
```
`EvalPlanAffineSmoke.lean`/`EvalPlanAffineCorpus.lean` are not part of the `JaxExperiment` lake
target at all (they're driver files `run-evalplan-affine{,-corpus}.sh` compile ad hoc via `lake env
lean --run`, per `lakefile.toml`'s own comment on the `JaxExperiment` target) but both
`import EvalPlanCodegen`, so both
runner scripts fail transitively the moment `lake build JaxExperiment` does (`set -euo pipefail`);
`EvalPlanAffineCorpus.lean` additionally has its own direct `checkedNodes`-shape assumption
(`plan.plan.checkedNodes.flatMap ...`, three call sites) that will need the same fix regardless, once
`EvalPlanCodegen` compiles again. `JaxExperiment` is not in `defaultTargets`, so none of this gates
`lake build` or this slice — it is a deliberate, unfixed consequence recorded here for whoever picks
up the JAX bridge next. That is thread **5** in `papers/jax_evalplan_architecture.md`'s §7.6
("compact/evidence-indexed kernels for JAX", status **Done**), which has no further work scheduled —
NOT thread 3, which is "Continue Wave F (F4)" and is open/next-recommended; this repair is unscheduled
because thread 5 is finished, not because it was dropped from a scheduled thread. One further latent
trap for whoever revives it: `Executable.lean`'s `JaxExecutableWellFormed` invariant silently changed
MEANING under this slice — it encodes a 1:1 step-to-kernel correspondence that predates scan support,
so a `.scan` step now counts as "one step" with no JAX-kernel meaning at all. No production caller
reaches this today (`Executable.lean` is consumed only by `JaxExperiment`), so nothing is broken now,
but the invariant no longer says what its name suggests.

### F4 - source compiler, adapter, and differential gate

Teach syntactic capability preflight and `prepareEvalPlan`'s post-shape scan-specialization phase to
admit the declared scan fragment and compile it to the already executable checked language.

Deliver:

- state/scratch/external classification;
- base and step block compilation;
- base-pin substitution in RHS affine maps and contraction bases;
- the explicit static/dynamic binding-time split from Section 8.1;
- capture and write-map construction;
- scan-aware bindings and complete-environment unpacking;
- warning-preserving source execution;
- alpha-renaming checks;
- exact differential counts against `evalScheduled`; and
- independent one- and n-dimensional unrolling agreement.

**Gate:** every supported generated and hand-written scan agrees bit-for-bit with the legacy evaluator
and independent unroller; every unsupported scan fails before `runDensePlan`; compiler-generated raw
plans always pass their checker.

**F4 completion record (2026-08-19).** Landed on one branch, in plan order, as `755354e` (Task 1),
`ece56ce` (Task 2), `78b8c57` + `e86d7eb` (Task 3), `ecb0604` (Task 4), `35bd1db` (Task 5's oracle),
and the documentation commit carrying this record — six implementation/test commits plus this one,
on top of the two plan-authoring commits that precede them.

*Two F3 prerequisite soundness fixes* (`755354e`, `LeanNCD/Eval/Plan/Scan.lean`). (1) `checkWrites`
never validated a write's `AffineMap` rank against the state's rank — F3's own recorded, deliberately
deferred follow-up. Two new constructors, `ScanPlanError.writeCoeffRankMismatch` /
`writeBiasRankMismatch`, now run before `writeRowKinds` (which pads a short map with `getD` and
ignores a long one's excess rows). (2) `runDenseScan` built `baseExternalInputs`/`stepInputs` by
mapping over `raw.baseCaptures`/`raw.stepCaptures` in their own stored order, while `runDenseBlock`
consumes them positionally against `block.inputs` — the sorted, deduped array `checkPlanBlock`
produces. `checkCaptures` validates the capture array only as a SET, so a plan whose captures are
stored in any other order bound every block input to the wrong tensor. Both now map over
`raw.*Block.inputs` and resolve each slot through `find?` on `inputSlot`. Found independently this
slice, not previously recorded anywhere. `test/Eval/Plan/ScanTest.lean` gains Part 7 (+292 lines),
including a `runDenseScanOldCaptureOrder` mutation copy that reproduces the pre-fix binding and shows
a coupled Fibonacci scan silently freezing `H` at its base value.

*Shared lowering extraction* (`ece56ce`). `residualizeAssignment` (`Compile.lean`) is now the one
per-statement lowering core used by the plain, base, and step callers alike. It BUILDS an
`AssignPlan` and deliberately does not mutate the caller's name environment — publication policy
belongs to each caller, which is what lets a coupled scan lower one state's next value without
shadowing the immutable state capture a later sibling still needs (§4.2). Wave C's scan-free
behavior is unchanged, proven by `CompileTest.lean` and the pre-existing 3,832-case scan-free sweep.

*The source scan compiler* (`78b8c57`, `e86d7eb`). `prepareEvalPlan` now compiles a `ScanStmt.scan`
node into a `PlanStep.scan`; `CapabilityError.scanNode` has no producer left. New surface: a closed
24-constructor `ScanCompileError` (`Error.lean`) covering §4.2 pairing, block dependency order,
context-axis and per-state geometry, §5.1 base-write placement, and §7.4 causality — every
constructor carrying source locators, no `String` escape hatch; `PlanCompileCause.scan`
(`EvalPlan.lean`); `CapabilityError.noAdvancingAxis`; and the six-phase `compileScan`. `.scanPre`
reuses the existing `recurrenceOrCallback` rather than adding a second constructor.
`.iterAt`/`.iterNext` are admitted ONLY inside a scan node's own base/recur lists — `checkLHSSlot` is
untouched, so a genuinely plain statement still rejects both. Phase order is preserved exactly as
§4.1 requires (preflight → signature → shape inference over plain+base+recur in source order →
source-ordered scan specialization → `checkScanPlan` then `checkPlan` → runtime packing).
`test/Eval/Plan/ScanCompileTest.lean` (1,008 lines) holds nine acceptance schedules covering twelve
lettered shapes (self-recurrence asserted as a whole `RawScanPlan`; coupled states with
`advancingDims = #[0,2]` and a PERMUTED `#[1,0]`; scratch; contraction plus current-coordinate
external read; constant deep look-back with zero padding; extent one; a non-trailing advancing
dimension; duplicate-pinned-UID bias substitution plus a face-plus-point multi-base write; two scans
plus a plain consumer of both histories), 60 typed-rejection `#guard` fixtures (`rej`/`rej2`, counted
in the file) pinning exact error values, and precedence fixtures for simultaneous defects.

*Named boundary and legacy parity* (`ecb0604`). No adapter production change was needed or made,
exactly as §4.7 predicted. `DifferentialTest.lean`'s `scanParityCheck` runs an execution matrix over
each fixture, and `AdapterTest.lean` gains Checks 11-16 (full named round trip with scratch asserted
ABSENT from the unpacked env; missing input at a base-block and at a step-block capture; shape and
storage mismatch at a capture with full payloads pinned; two-warning order-and-payload preservation
on the success and `pack`-failure paths).

*The independent oracle and the three-way gate* (`35bd1db`). `test/Eval/PropertyOracle/
ScanUnroll.lean` was rewritten (540 lines) around `unrollScanNode`/`reconstructHistory`/
`independentRun`, replacing the immediate-predecessor one-axis unroller and the single fixed 2x2
template §11.5 calls out. A scan node becomes a scan-free leaf program: one leaf per (state, history
coordinate), one per (scratch name, step iteration), and one zero leaf per state for every coordinate
neither a base write nor a step reaches. Each state's dimension mapping is resolved from its
recurrence RESULT statement, so advancing dimensions need not trail, be contiguous, or follow context
order; base regions may pin a context axis or leave it free (§5.1's boundary face); history reads may
be any affine expression that reduces to a literal coordinate; out-of-range and never-written reads
route to the zero leaf. Emission order — zero leaves, base writes in declared order, then step
iterations lexicographically — both satisfies every read and yields §9's immutable-pre-step (Jacobi)
snapshot for free, because a step at `u` reads only coordinates `<= u` and writes only `u + 1`.
Complete histories are reassembled with `DenseTensor.ofFn`, with a completeness check so a lost or
misplaced leaf cannot be absorbed by the zero default. `independentRun` walks the whole schedule, so
a plain statement downstream of a scan sees the reconstructed history.

Per §11.5's independence requirement, the file no longer names `runDenseScan`, `evalScan`,
`writeRowKinds`, `applyAffine`, any compiler residualization helper, or any scan-worker write helper.
The predecessor's `sliceTensorAtMulti` — defined as "the inverse of `LeanNCD.Eval.writeSliceAtMulti`"
and round-trip-tested against that worker helper directly — is deleted along with the
`LeanNCD.Eval.Scan` import: reconstruction from per-coordinate leaves needs no slicing. The one
evaluator entry point used is `evalScheduled`, always on an all-`ScanStmt.plain` program. The one
shared DSL accessor reused is `idxAffineForm` (`DSL/Ast.lean`), a five-constructor destructuring of
`IdxExpr` used by both the compile path and the eval size solver — an AST reader, not an
implementation under comparison; a second copy would have been duplication for its own sake.

*Exact counts.* The curated `enumScanCases` corpus splits **17 total / 17 accepted / 0
`unsupportedNonlin` / 0 `unsupportedAgg`**, pinned by `#guard` and by which capability constructor
each rejection produces (was 9 accepted / 4 `unsupportedNonlin` / 4 `unsupportedAgg` at F4
authoring time; thread 4 Task 4 admitted pointwise/axiswise scan-block nonlinearities and moved
four cases into the accepted column, and the max/min-aggregation thread admitted `.max`/`.min` and
moved the final four). All accepted programs pass the three-way
gate — hand-written schedules together with the accepted generated cases — and agree bit-for-bit
across `prepareEvalPlan -> runPreparedDense`, `evalScheduled`, and the independent unrolling; no
checked-versus-legacy divergence arose, so nothing needed classifying under Law 1. Warnings are
compared between the first two legs only: the unrolling replaces every scan-axis index with a
literal, so which reads are STATICALLY out of extent legitimately changes while the values may not.
Because count alone is not coverage, `DifferentialTest.lean` also asserts a structurally derived
feature table — deep look-back and zero padding, coupled states, scratch, external reads,
contraction, extent one, more than one scan axis, several base writes for one state, a non-trailing
advancing dimension, more than one scan in a schedule, and a plain consumer of a published history
— each checked against the gated schedules themselves rather than by fixture name.
`ScanOracle.lean` additionally runs the two-way law (legacy versus independent unrolling) over all
seventeen generated cases, including the eight F4 rejects, by carrying nonlinearity and aggregation
through the rewrite unchanged. Full `lake build` green at **8,652 jobs**; the pre-existing 3,832-case
scan-free sweep is unchanged.

*Oracle mutation observations (fail-before / pass-after), each applied to the tree, built, observed
RED, and reverted.*

| Mutation | Site | Observed RED |
|---|---|---|
| Drop a state read's affine bias, so every history read selects the immediate predecessor | `rewriteRead`, `ScanUnroll.lean` | `F/deepHistory: THREE-WAY DIFFERENTIAL FAILURE ... plan=[1,1,1,2] unrolled=[1,2,4,8]` |
| Resolve a same-step scratch read to iteration 0's scratch leaf | `rewriteRead`, `ScanUnroll.lean` | `C/scratch: ... plan=[1,2,6] unrolled=[1,2,2]`, and the same on the alpha-renamed fixture |
| Assume the advancing dimensions TRAIL during reconstruction (the predecessor oracle's actual assumption) | `reconstructHistory`, `ScanUnroll.lean` | `B/coupled: ... plan shape [3,2,3] vs unrolled shape [2,3,3]` |
| Pin every base `iterAt` literal to 0 | `baseRegion`, `ScanUnroll.lean` | `I-J/multiBase: ... plan=[1,2,3,7,1,2,0,7,1] unrolled=[1,2,3,0,1,2,0,0,1]` |
| Bind every step-block local input slot to the LAST capture's source | `Compile.lean`'s `stepCaptures` (production) | on `C/scratch`, leg 1 gives `S = [1,4,9]` while legs 2 and 3 BOTH give `[1,2,6]` — the two independent paths agree with each other and disagree with the plan |

Two of those were sharpened after earlier attempts went red for the wrong reason, recorded because
the distinction is the point of the exercise.

The state-dimension-placement mutation took **three** attempts, each rejected by a different guard.
(a) Written into `buildGeom` as "the advancing dimensions are the last `|axes|` dimensions", it was
rejected by `buildGeom`'s own free-slot check — `B/coupled: the independent scan-free unrolling
failed: G: dimension 0 is neither advancing nor a plain free axis (…iterNext r…)` — a structural
refusal, not a differential. (b) Rewritten as `advDim.reverse`, which keeps every position a genuine
`iterNext` slot, it was caught one guard earlier still, by `baseRegion`'s axis-identity check:
`template6 unroll failed: base write for G: dimension 1 pins c, expected r`. (c) Moved into
`reconstructHistory`, it finally produces the intended shape/value disagreement on `B/coupled` — and
that is also the precise §11.5 deficiency being retired ("comparison assumes trailing scan
dimensions"), so it is the right site for this mutation regardless.

The production capture mutation was first attempted as a step-write bias change (`1 -> 0`), which
`checkScanPlan` correctly rejected as `writeGeometryNotAdmitted` on all nine acceptance fixtures — a
checker doing its job, not evidence about the oracle. The capture rebinding survives F3 checking
wherever the two captures share a signature; it was measured on a standalone `lake env lean` probe
with the fixture inlined, because `ScanCompileTest`'s whole-`RawScanPlan` assertion and `AdapterTest`
Check 11 both catch it earlier in the ordinary build, and neutering those far enough to reach
`DifferentialTest` would have changed too much to be trustworthy evidence.

*Controller ruling recorded so it need not be re-derived.* §4.2's "every base destination is a state
candidate" appeared to conflict with §8.4's "base blocks may read external inputs and earlier
block-local scratch". Resolved in favour of §4.2 after reading `LeanNCD/DSL/Pipeline/Structural.lean`
directly: `finalizeScans` filters `baseStmts` to `!s.iterInfo.isEmpty && isBase s`, and an
intermediate (`isInter`) goes only into `recurStmts`, so **base-block scratch is structurally
unreachable from source**. §8.4 describes a checked-plan-language capability, not a source-compiler
obligation, and the oracle rejects a base-block scratch or state read for the same reason.

*Documentation corrected alongside the code.* `Prepared.lean`'s `materializedNames` doc comment (one
entry per persistent OUTPUT, not per scheduled statement — a coupled scan step publishes one per
state); `Eval/AGENTS.md` (the parity matrix is eight points, plus a row for the independent oracle
and its §4.8 forbidden list); `papers/eval_ir.md` (the compiler no longer "emits only
`PlanStep.assign` and rejects source scans during capability preflight"); §F0 above (its survey of
`ScanUnroll.lean` described the deleted `unrollScan1D`/`unrollScan2D` pair in the present tense); and
`papers/jax_evalplan_architecture.md` §7.6, which asserted that "`PlanStep`, distinct slot namespaces,
and snapshot/next-state types genuinely don't exist in any form yet" and that thread 3 still owed
Stage A items 1, 7 and 8. Re-checked against the code: `PlanStep` has existed since F3
(`RawStep.lean`) and item 8 is built (`PlanStep.sourceSlots`/`destinationSlots`, `EvalPlan.lean:39`
and `:45`); items 1 and 7 really are still open as TYPE-level refinements — `TensorSlot` is a bare
`abbrev … := Nat` shared by outer and block slots, and `runDenseScan`'s snapshot/next-state values
are plain `Array DenseTensor` locals despite the behavior being correct and checked. Thread 3's
status is now Done for its stated F4 scope, explicitly noting that F5 has not started.

Known follow-ups, deliberately not fixed here:

- `partialAdvancingResult`'s payload is degenerate in a third sub-case: a result that advances the
  right NUMBER of context axes but the wrong SET reports `declared = n, expected = n`. No fixture
  covers that sub-case.
- `duplicateAxisInLhs` is the one both-blocks `ScanCompileError` constructor lacking the `isBase`
  flag its siblings carry, so two different programs failing in two different blocks assert
  byte-identical expected values (`ScanCompileTest.lean:849` and `:852`).
- `blockReadNotAvailable` collapses three distinct user errors — unknown name, read before its
  producer, and self-read — into one constructor discriminated only by `isBase`;
  `ScanCompileTest.lean:776` and `:795` assert identical values.
- A wrong-arity read confined to NON-advancing dimensions inside a scan block surfaces as
  `invalidPlan` ("internal compiler bug") rather than as a source-level diagnostic — but the gap is
  **unreachable from real source**, narrower than an earlier draft of this entry recorded. That
  draft blamed `SizeInfer`'s missing read-arity check; the final whole-branch review verified the
  belief and found the arity check simply lives elsewhere. `TLProgram.compileToScheduled`
  (`LeanNCD/DSL/Compile.lean:37`) runs `checkReadRanks`
  (`LeanNCD/DSL/Pipeline/Structural.lean:686-720`) as its fourth phase, and — critically — it runs
  **pre-grouping**, walking the flat `rp.stmts` list before `finalizeScans` partitions it into base
  and recurrence blocks. A scan's base and recurrence statements are therefore arity-checked exactly
  like plain ones (against `DeclEnv` for declared tensors, against the first read site for
  externals, against `stmtLhsRank` for produced-but-undeclared intermediates), throwing
  `.rankMismatch`. The gap is reachable only from a hand-built `ScheduledProgram` that never went
  through the front end — which is what every `ScanCompileTest` fixture is. §7.5's "a later checker
  rejection is therefore an internal compiler bug" claim is **intact for real source**: no §7.5
  change is owed, and F5 should not act on the earlier, wider premise.
- `checkScanPlan` never checks a state destination slot's **dtype**. It reads the state's signature
  (`Scan.lean:332`, and again per write at `:276`) purely for `.shape`, so §5.1's "state and external
  tensors are concrete `f64`" has a sub-case the checker skips: a write-only state whose `destSlot`
  signature says `.f32` is admitted, and `runDenseScan` (`:472-474`) then allocates `Float` data
  under an `f32` label. Contained downstream and therefore cosmetic — `checkAssign`
  (`Check.lean:81`) rejects a non-`f64` source, so nothing can read it as `f32`, and a state that is
  captured is covered by `captureSignatureMismatch` (`Scan.lean:233-235`), which compares the whole
  `TensorSignature` including dtype. Recorded because it is another instance of the shape this
  branch keeps finding: a spec sentence whose checker enforces only part of it.
- `ScanPlanError.causalityFailure` (`Scan.lean:186`) carries `(stateIndex, termIndex, factorIndex)`,
  but the loop that throws it (`Scan.lean:370-381`) iterates `ai` over `stepBlock.assignments` and
  discards it. Two different step assignments failing at the same term/factor position therefore
  produce byte-identical payloads. The source-level sibling `ScanCompileError.stateReadNotCausal`
  (`Error.lean:126`) *does* carry `stmtIndex` — the two families disagree on locator precision.
  Pre-existing from F3.
- `requiredInputs : RequiredBindings` is asserted in only one acceptance fixture (A); the multi-scan
  fixture K/L, where slot allocation interleaves, asserts `materializedNames` but not it.
- `compileScan` is roughly 375 lines in a single `do` block with about fifteen mutable accumulators;
  phases 2, 3 and 5 would extract cleanly.
- `DifferentialTest.lean`'s `scanCorpusSplit` is computed twice — once for a `run_cmd` diagnostic and
  once for the `#guard` — re-running the full execution matrix over the nine accepted cases a second
  time for no functional benefit.
- The legacy-side scratch-privacy assertion has no dedicated mutation demonstrating it can fail; only
  the compiled-side privacy check got real RED evidence.
- `PlanRunCause.execution` remains unreachable through `runPreparedDense` (`pack` re-validates
  presence, shape and storage with the same predicates `runDensePlan` re-applies), so "warnings
  preserved on execution failure" is pinned by construction plus a positive
  `pack`-succeeds-implies-`runDensePlan`-succeeds check over four scan shapes, not by a live failure.
- The independent oracle's `rewriteRead` performs no causality check of its own: it evaluates a state
  read's advancing indices at the current step tuple and routes the result by range and liveness
  alone. A positive-bias (non-causal) read would therefore be unrolled rather than rejected — reading
  a leaf the emission order has not produced yet (a loud but unhelpfully-worded `unknownTensor`), or,
  if that coordinate happens to be base-covered, a value that is merely wrong. Not a live defect:
  `compileScan`'s `stateReadNotCausal` rejects such a source before the oracle ever sees it, and F3
  rejects it again at the plan level. Recorded as a consistency gap — the oracle rejects every OTHER
  out-of-fragment construct explicitly — not as a bug.
- `DifferentialTest.lean`'s `scanFeatures` "extent one" predicate tests only that the schedule
  DECLARES some `.iter _ 1`; it does not check that the axis so declared is one the scan actually
  advances over. Every other row in that table is derived from the scan node itself. Adequate for
  today's fixtures (`extentOneSched` declares exactly one iter axis, of extent 1) but the weakest
  row, and the one most likely to pass vacuously if a future fixture declares an unrelated
  extent-one axis.
- The two-way leg's `advScratch` support (the `%nl` shape `splitNonlins` manufactures for a nonlinear
  recurrence) exists only because the four `relu` generated cases produce it. Nothing asserts its
  presence the way `scanFeatures` asserts the others, so if those templates change it silently loses
  coverage.

### F5 - adversarial audit and handoff

Audit the whole branch rather than adding new architecture.

Deliver:

- complete checker/error mutation matrix;
- import-direction audit;
- semantic-field inventory;
- generator-coverage attribution audit;
- discoverability from `import LeanNCD` and subsystem documentation;
- updated capability manifest recording removal of the unused in-memory version tag and the explicit
  post-Wave-F checked-kernel and scan-capability backlog from the executive summary;
- exact full-build job count; and
- a Wave F completion record including final-review fixes.

**Gate:** Laws 1, 2, 4, and the general side of Law 5 hold for the admitted scan fragment; Wave G can
consume checked scan APIs without importing source compilation or legacy execution.

Specialized PyTorch/JAX scan lowerings remain a later wave.

**F5 completion record (2026-08-20).** Landed on one branch, in plan order, as `f69c2b0` (Task 1),
`82c2175` (Task 2), `dc29155` (Task 3), and `7bb51dc` + `f791989` + the commit carrying this record
(Task 4) — six documentation/fix commits, on top of the plan-authoring commit `59fd796` that precedes
them.

*Three under-specified error payloads sharpened* (`f69c2b0`, Task 1). `ScanPlanError.causalityFailure`
(`Scan.lean`) gained a `stmtIndex` field between `stateIndex` and `termIndex`, so two different step
assignments failing at the same term/factor position no longer collide on one payload.
`ScanCompileError.duplicateAxisInLhs` gained `isBase : Bool`, so a duplicate axis in a base statement
and one in a step statement are distinguishable. `ScanCompileError.blockReadNotAvailable` gained a new
`ReadUnavailableCause` (`unknownName`/`forwardReference`/`selfRead`), so an unresolvable name, a
forward reference to a later scratch producer, and a self-read are three distinguishable rejections
instead of one. Every call site (`Compile.lean`'s two `duplicateAxisInLhs` throws, three
`blockReadNotAvailable` throws, `Scan.lean`'s one `causalityFailure` throw) and every test fixture
(`ScanTest.lean`, `ScanCompileTest.lean`) was updated to the new arity; a whole-tree grep for all
three constructor names, re-run independently in this task (Step 4), confirmed no stale
three-/four-argument construction survives anywhere in `leanncd/`.

*Remaining named mutation-matrix gaps closed* (`82c2175`, Task 2). `ScanCompileTest.lean` gained a
`partialAdvancingResult` fixture for the degenerate sub-case (a result advancing the right NUMBER of
context axes but the wrong SET, reporting `declared = n, expected = n`) that F4's completion record
had left uncovered. `DifferentialTest.lean`'s `scanFeatures` "extent one" predicate was tightened to
require the extent-one axis be a member of some scan node's own `axes` list, rather than merely
declared somewhere in the schedule — the coverage gate still passed, confirming `extentOneSched`'s
axis genuinely is its own scan's advancing axis. `ScanOracle.lean` gained an explicit assertion that
the two-way sweep's `advScratch` support is non-empty for at least one analyzed case, closing the
silent-coverage-loss risk F4's record had named. `DifferentialTest.lean`'s duplicated
`scanCorpusSplit` computation (once for a `dbg_trace`, once for the `#guard`) was merged into one
`run_cmd` block, removing the redundant second execution of the corpus matrix.

*Documentation corrected* (`dc29155`, Task 3). `DSL/AGENTS.md`'s claim that `Eval/*` never imports
`Pipeline.Structural`/`Lowering` directly was false as of F4: `Eval/Plan/Compile.lean` imports
`Pipeline.Lowering` directly, reusing `idxToRow` to lower a scan's affine reads exactly as
`Lowering.lean` itself does. The claim now states that one exception explicitly.

*Capability manifest published, stale cross-references corrected, final gate run* (`7bb51dc`,
`f791989`, Task 4). `papers/wave_f_capability_manifest.md` is new, mirroring
`papers/wave_c_capability_manifest.md`'s section shape: accepted/rejected scan constructs, the
three-way differential gate's counted result, the missing-capability backlog reproduced from §1, and
the import-graph/documentation audit findings below. `papers/wave_c_capability_manifest.md`'s §1 no
longer claims `checkPlan` rejects a `RawEvalPlan.version` other than `1` — it now states the removal
and points to the new manifest. `leanncd/LeanNCD/Eval/AGENTS.md`'s `Plan/` pointer sentence now names
the new manifest alongside the two existing documents.

*Whole-branch review (Step 4), performed for real.* Grepped every call site of `causalityFailure`,
`duplicateAxisInLhs`, and `blockReadNotAvailable` across the whole `leanncd/` tree: every production
call site and every test fixture matches the new arity (declaration, throw site, and `#guard`/`==`
assertion in each case), no stale construction remains. Confirmed no file outside this plan's own File
Structure lists was touched across all four tasks: the eight files changed since `59fd796` by Tasks
1-3 (`LeanNCD/Eval/Plan/{Scan,Error,Compile}.lean`, `test/Eval/Plan/{ScanTest,ScanCompileTest,
DifferentialTest}.lean`, `test/Eval/PropertyOracle/ScanOracle.lean`, `LeanNCD/DSL/AGENTS.md`) are
exactly the union of Tasks 1-3's own Files lists; Task 4 itself touched exactly its own four named
files.

*Exact counts, re-derived independently this task from the current tree, not copied from this plan's
own prose.* `CapabilityError` (`Error.lean`): **12** constructors (Wave C's 11 plus `noAdvancingAxis`,
added in F2) — unchanged by Tasks 1-3. `ScanCompileError` (`Error.lean`): **24** constructors,
unchanged in count by Tasks 1-3 (three constructors gained fields; none was added or removed). The
curated scan corpus (`enumScanCases`, `DifferentialTest.lean`'s `scanCorpusSplit`): **17** total, split
**9 accepted / 4 `unsupportedNonlin` / 4 `unsupportedAgg`**, pinned by that file's own `run_cmd`
assertion, re-observed in this task's own build run (`DifferentialTest scan corpus: total=17
accepted=9 unsupportedNonlin=4 unsupportedAgg=4`). *[Wave F-era counts. The nonlinearity plan's
Task 4 later moved all four `unsupportedNonlin` cases into the accepted column, and the
max/min-aggregation thread moved all four `unsupportedAgg` cases too; the assertion now
reads `total == 17 && accepted == 17 && nonlin == 0 && agg == 0`, and the `lake build` figure below
is likewise the pre-Task-4 baseline. The numbers in this paragraph are what F5 observed, not what
the tree says today.]* The three-way differential gate: **21** total scan
programs (12 hand-written + 9 accepted generated) agree bit-for-bit across the compiled checked path,
`evalScheduled`, and the independent unrolling. The pre-existing Wave C scan-free sweep remains
**3,832** entries, 100% accepted, 100% bit-exact — unchanged by this slice. Full `lake build`, run by
this task: **`Build completed successfully (8652 jobs)`** — exactly the pre-F5 baseline, since no task
in this plan added a new module.

*Wave F's own Definition of Done ([§14.1](#141-definition-of-done), 11 items), closing status.* All 11
hold today, for the admitted scan fragment the capability manifest describes — none holds for the
missing-capability table's contents (`papers/wave_f_capability_manifest.md` §5), which is recorded
precisely because it is NOT done:

1. **Explicit checked data** (state, blocks, captures, writes, extents, traversal, boundary, snapshot,
   materialization, causality) — holds; see the manifest's §2/§3.
2. **Raw scan data cannot reach any worker** — holds; `checkScanPlan`/`checkPlan` gate every
   `RawScanPlan` before `runDenseScan` runs, unchanged by this plan.
3. **General Dense scan execution uses no source names, UIDs, AST values, callbacks, or unordered
   maps** — holds, per F4's own semantic-field inventory; this plan added no new field to
   `runDenseScan`.
4. **Scan-free plans preserve Wave C behavior** — holds; the pre-existing 3,832-case sweep is still
   green at the same job count.
5. **Supported source scans residualize and agree with `evalScheduled` under `=obs`** — holds for the
   admitted fragment: 12 hand-written + 9 generated = 21 programs agree bit-for-bit (manifest §4).
6. **The independent unroller agrees with the general worker over its declared corpus** — holds, over
   the same 21-program three-way gate.
7. **Unsupported scan constructs fail before worker execution**, syntactic cases via `CapabilityError`,
   post-shape cases via `ScanCompileError`, `ScanPlanError` reserved for directly constructed malformed
   raw plans — holds; manifest §3's 12- and 24-constructor tally has no `String` escape hatch, and
   Task 1 sharpened three existing payloads without introducing one.
8. **Block scratch never escapes unless a later plan version explicitly materializes it** — holds; the
   scratch-privacy checks in every gated scan program's parity check (`scanParityCheck` points 6b/6c)
   pass for all 21.
9. **Complete state histories and warnings survive the named boundary** — holds; `AdapterTest.lean`
   Checks 11-16, untouched by this plan.
10. **The Plan worker imports neither source compilation nor legacy execution** — holds, and is now the
    capability manifest's own stated resolution (§6): `Eval.Plan.EvalPlan`/`Eval.Plan.Scan` do not
    import `Eval.Plan.Compile`; only `Eval.Plan.Adapter` and `Eval.Plan.Compile` pull in the source
    compiler. (Both leaves do transitively reach `DSL.Ast` via `Eval.Error`, but only for its AST type
    definitions — no compiler, no evaluator; the manifest's §6 corrects an earlier, narrower claim that
    this closure excluded `DSL.Ast` entirely.)
11. **The full default Lean build passes with no skipped test module** — holds; `8652` jobs, green,
    from this task's own run.

## 14. Definition of done and stop conditions

### 14.1 Definition of done

Wave F is complete only when:

1. scan state, blocks, captures, writes, history/step extents, traversal, boundary, snapshot,
   materialization, and causality are explicit checked data;
2. raw scan data cannot reach any worker;
3. general Dense scan execution uses no source names, UIDs, AST values, callbacks, or unordered maps;
4. scan-free plans preserve Wave C behavior;
5. supported source scans residualize and agree with `evalScheduled` under `=obs`;
6. the independent unroller agrees with the general worker over its declared corpus;
7. unsupported scan constructs fail before worker execution: syntactic cases use
   `CapabilityError`, post-shape/source-specialization cases use `ScanCompileError`, and
   `ScanPlanError` is reserved for directly constructed malformed raw plans;
8. block scratch never escapes unless a later plan version explicitly materializes it;
9. complete state histories and warnings survive the named boundary;
10. the Plan worker imports neither source compilation nor legacy execution; and
11. the full default Lean build passes with no skipped test module.

### 14.2 Stop and revise this proposal if

- a worker needs a source tensor name or axis UID;
- state versus scratch must be rediscovered during execution;
- `checkScanPlan` duplicates rather than composes `checkPlanBlock`/`checkAssign`;
- the source compiler cannot derive state captures and writes without worker-time syntax inspection;
- supported exact agreement requires changing legacy `evalScheduled`;
- two backends need different meanings for one scan field;
- a checked state read cannot justify its causality certificate;
- arbitrary write geometry is needed merely to support the declared first fragment;
- zero-length behavior cannot be made one typed policy;
- nonlinearities or max/min algebra are required merely to validate the scan architecture; or
- a specialized lowering is needed before the general worker passes its gate.

These are design failures or scope changes, not reasons for optional fields, fallback execution, or
silent defaults.

## 15. Wave C planning lessons applied

Wave C's retained C0-C4/C6 implementation plans and its retrospective establish process constraints
for Wave F:

1. **Contract before types.** C0 caught semantic ambiguities before production code. F0 does the same
   for snapshot, order, bases, history, and zero length.
2. **Inside-out vertical slices.** C2 and C3 made the checked language executable before C4 added the
   source compiler. F1-F3 similarly produce a manually executable scan before F4 residualizes source.
3. **Private constructors need compile-failure tests.** `private mk ::` is required; prose about a
   checked type is not access control.
4. **Every checker branch needs a mutation.** Unreachable branches are named and justified rather
   than forced through misleading pipeline fixtures.
5. **Fixture values must be observed.** Plausible Lean and hand-derived binary64 results are not
   evidence until compiled and run.
6. **Differential tests need test-the-tester mutations.** A passing sweep may be tautological or may
   omit the capability it is credited with.
7. **Coverage claims are bounded by generators.** Hand fixtures, not file names, establish dimensions
   absent from a generated corpus.
8. **Task boundaries follow review independence.** F1, F2, F3, and F4 can each be rejected while the
   previous slice stands. Tiny type-only and two-guard tasks should be merged into their consumer.
9. **The whole-branch review is mandatory.** Wave C's most important defects were relationships among
   individually clean tasks.
10. **Discoverability is part of delivery.** A subsystem is not handed off until public imports,
    architecture docs, and capability manifests expose it.
11. **Do not build infrastructure without a consumer.** Version `2` is required by real scan
    semantics; canonical bytes, hashing, and wire codecs remain deferred.

## 16. Literature-derived design patterns

The literature supports the proposal's boundaries more strongly than it suggests new machinery:

1. **Synchronous normal form.** LUSTRE's separation of instantaneous acyclic equations from delayed
   state motivates `CheckedPlanBlock` plus explicit state capture/commit. Wave F uses that finite
   first-order pattern, not a clock calculus or coinductive stream type.
2. **Uniform recurrence and legal schedule.** Karp, Miller, and Winograd's dependence-vector view,
   and later affine dependence analysis, motivate defining causality as producer-before-consumer
   schedule legality. The first identity-plus-bias recognizer remains deliberately narrower than a
   polyhedral solver.
3. **Scan versus accumulation.** For one axis, complete-history semantics resembles `scanl`: the base
   is part of the returned history. `mapAccumL` and JAX's fixed carry become appropriate only for a
   later compact-carry worker/wrapper. The n-dimensional node remains an ordered lattice recurrence.
4. **Worker/wrapper and representation independence.** A compact carry is justified by an
   initialization/step/reconstruction simulation, not by changing semantic state or output policy.
5. **Partial evaluation.** F4 consumes static signatures, extents, slots, policies, and affine
   substitutions while residualizing dynamic coordinates and tensor values. A general staging
   framework would add no Wave F capability.
6. **Ghost checked evidence.** Private checked constructors let workers consume validation evidence
   without carrying source syntax or rebuilding proofs. The certificate establishes its documented
   invariant only; it is not a proof of compiler correctness or numerical equivalence.
7. **Metamorphic and differential evidence.** Unrolling, alpha-renaming, and targeted mutations test
   semantic relations, but shared implementations can make agreement tautological. The source
   oracle, checked worker, and future optimizer therefore remain independent.
8. **Operational algebra.** Prefix algorithms require associativity and identity under the active
   numeric semantics. Real-number equations do not authorize binary64 reassociation in
   `reference64`.

Several attractive patterns are intentionally rejected for Wave F: a guarded-recursion type system,
generic recursion-scheme or stream-fusion IR, full polyhedral dependence engine, nested-data-parallel
flattening, generic staging, compact semantic state, and parallel semantics without separate
evidence. They address wider problems but would obscure the first executable checked recurrence
boundary. Future wavefront scheduling, checked-plan unrolling, compact carries, and parallel prefix
remain refinements governed by Law 5.

## 17. References

### Repository

- [Wave C checked-plan proposal](wave_c_evalplan_proposal.md)
- [Wave C capability manifest](wave_c_capability_manifest.md)
- [Restructuring roadmap](restructure_suggestions.md)
- [Current scheduled scan type](../leanncd/LeanNCD/DSL/Pipeline/Types.lean)
- [Current scan grouping and validation](../leanncd/LeanNCD/DSL/Pipeline/Structural.lean)
- [Current scan evaluator](../leanncd/LeanNCD/Eval/Scan.lean)
- [Wave C plan kernel](../leanncd/LeanNCD/Eval/Plan/Kernel.lean)
- [Wave C raw graph](../leanncd/LeanNCD/Eval/Plan/Graph.lean)
- [Wave C checkers](../leanncd/LeanNCD/Eval/Plan/Check.lean)
- [Wave C Dense worker](../leanncd/LeanNCD/Eval/Plan/Dense.lean)
- [Wave C source compiler](../leanncd/LeanNCD/Eval/Plan/Compile.lean)
- [Multi-axis scan design](../leanncd/docs/superpowers/specs/2026-07-08-multi-axis-scans-design.md)
- [Multi-axis scan implementation plan](../leanncd/docs/superpowers/plans/2026-07-08-multi-axis-scans.md)
- [Historical scan-lowering investigation](../leanncd/docs/superpowers/plans/2026-06-26-scan-lowering-fix.md)
- [Scan-axis declaration design](../docs/superpowers/specs/2026-07-30-scan-axis-declaration-spike.md)
- [Scan property generator](../leanncd/test/Eval/PropertyOracle/ScanGen.lean)
- [Independent scan oracle](../leanncd/test/Eval/PropertyOracle/ScanOracle.lean)
- [Scan unrolling implementation](../leanncd/test/Eval/PropertyOracle/ScanUnroll.lean)

### External

- Richard S. Bird,
  [An Introduction to the Theory of Lists](https://doi.org/10.1007/978-3-642-87374-4_1), 1987.
- Nicolas Halbwachs, Paul Caspi, Pascal Raymond, and Daniel Pilaud,
  [The Synchronous Data Flow Programming Language LUSTRE](https://doi.org/10.1109/5.97300), 1991.
- Richard M. Karp, Raymond E. Miller, and Shmuel Winograd,
  [The Organization of Computations for Uniform Recurrence Equations](https://doi.org/10.1145/321406.321418),
  1967.
- Paul Feautrier,
  [Dataflow Analysis of Array and Scalar References](https://doi.org/10.1007/BF01407931), 1991.
- Neil D. Jones, Carsten K. Gomard, and Peter Sestoft,
  [Partial Evaluation and Automatic Program Generation](https://www.cambridge.org/core/books/partial-evaluation-and-automatic-program-generation/500C671429CC993BE6A5E30C261B943F),
  1993.
- Andrew Gill and Graham Hutton,
  [The Worker/Wrapper Transformation](https://people.cs.nott.ac.uk/pszgmh/wrapper.pdf), JFP 2009.
- John C. Mitchell,
  [Representation Independence and Data Abstraction](https://doi.org/10.1145/512644.512669), 1986.
- Matt Noonan,
  [Ghosts of Departed Proofs](https://doi.org/10.1145/3242744.3242755), Haskell Symposium 2018.
- Koen Claessen and John Hughes,
  [QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs](https://doi.org/10.1145/351240.351266),
  2000.
- Tsong Yueh Chen et al.,
  [Metamorphic Testing](https://doi.org/10.1145/3143561), ACM Computing Surveys 2018.
- David Goldberg,
  [What Every Computer Scientist Should Know About Floating-Point Arithmetic](https://doi.org/10.1145/103162.103163),
  1991.
- Haskell 2010,
  [`scanl` and `mapAccumL`](https://www.haskell.org/onlinereport/haskell2010/haskellch20.html).
- [JAX `lax.scan`](https://docs.jax.dev/en/latest/_autosummary/jax.lax.scan.html).
- Guy E. Blelloch,
  [Prefix Sums and Their Applications](https://www.cs.cmu.edu/~guyb/papers/Ble93.pdf).
- Richard E. Ladner and Michael J. Fischer,
  [Parallel Prefix Computation](https://doi.org/10.1145/322217.322232), 1980.
