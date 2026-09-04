# Backend Eval IR

## Table of contents

- [1. Pipeline overview](#1-pipeline-overview)
  - [1.1 DSL pipeline fork](#11-dsl-pipeline-fork)
  - [1.2 Common evaluator boundary](#12-common-evaluator-boundary)
  - [1.3 Dense backend evaluator](#13-dense-backend-evaluator)
  - [1.4 Experimental JAX path](#14-experimental-jax-path)
- [2. Plan preparation](#2-plan-preparation)
  - [2.1 `prepareEvalPlan` interface](#21-prepareevalplan-interface)
  - [2.2 `prepareEvalPlan` input: `ScheduledProgram`](#22-prepareevalplan-input-scheduledprogram)
  - [2.3 `prepareEvalPlan` input: `InputSignature`](#23-prepareevalplan-input-inputsignature)
  - [2.4 `prepareEvalPlan` output: `PreparedPlan`](#24-prepareevalplan-output-preparedplan)
  - [2.5 Guarantees after successful preparation](#25-guarantees-after-successful-preparation)
- [3. Backend execution and results](#3-backend-execution-and-results)
  - [3.1 Evaluation stages](#31-evaluation-stages)
    - [3.1.1 Backend lowering](#311-backend-lowering)
    - [3.1.2 Runtime binding](#312-runtime-binding)
    - [3.1.3 Positional execution](#313-positional-execution)
    - [3.1.4 Output materialization](#314-output-materialization)
    - [3.1.5 Result reporting](#315-result-reporting)
  - [3.2 Evaluation data structures](#32-evaluation-data-structures)
    - [3.2.1 Prepared and checked plans](#321-prepared-and-checked-plans)
    - [3.2.2 Backend executable](#322-backend-executable)
    - [3.2.3 Named runtime tensors](#323-named-runtime-tensors)
    - [3.2.4 Positional tensor store](#324-positional-tensor-store)
    - [3.2.5 Named runtime results](#325-named-runtime-results)
    - [3.2.6 Reports, warnings, and failures](#326-reports-warnings-and-failures)
  - [3.3 Backend mappings](#33-backend-mappings)
    - [3.3.1 Dense evaluator](#331-dense-evaluator)
    - [3.3.2 Experimental JAX evaluator](#332-experimental-jax-evaluator)

## 1. Pipeline overview

### 1.1 DSL pipeline fork

The DSL pipeline reaches `ScheduledProgram` and then forks into two different paths:
```text
TLProgram
  -> compileToScheduled
ScheduledProgram
  |-> route
  |     -> ThreadedComposed        categorical routing path
  |
  `-> + InputSignature
        -> prepareEvalPlan
        -> PreparedPlan            backend evaluation path
```
Here `route` is the DSL's categorical-routing phase, not backend runtime execution. It converts the
scheduled program into `ThreadedComposed`, where scan bodies have been collapsed into routed
categorical steps. Backend Eval IR does not consume that representation: `compileToScheduled`
deliberately stops before `route`, leaving the plain statements and scan base/recurrence bodies in
`ScheduledProgram` so `prepareEvalPlan` can compile them into explicit positional operations.

### 1.2 Common evaluator boundary

[`PreparedPlan`](#24-prepareevalplan-output-preparedplan) is the common source-facing input to
evaluators. The Dense path executes it directly. The experimental JAX code contains two partially
separate consumers: candidate lowering and validation, and direct Python generation:
```text
PreparedPlan
  |-> runPreparedDense
  |     -> Dense execution -> EvalReport
  |
  `-> experimental JAX
        |-> lowerCheckPlanToCandidate
        |     -> JaxExecutableCandidate
        |     -> validateAndConstructExecutable
        |     -> SomeJaxExecutable
        |
        `-> direct Python/JAX code generation
```
These paths begin at the same semantic boundary but perform different work:
`runPreparedDense` is an evaluator, while `lowerCheckPlanToCandidate` is only the first lowering step
of an intended JAX path. The conceptual peer of `runPreparedDense` would be a complete JAX
lowering-validation-execution path, not `lowerCheckPlanToCandidate` alone. No such path is currently
wired end to end.

### 1.3 Dense backend evaluator

After successful preparation, the current Dense backend evaluator runs the resulting plan as follows:
```text
PreparedPlan + named runtime tensors
  -> runPreparedDense
       -> pack
            named tensors -> positional Array DenseTensor
       -> runDensePlan
            checked positional execution
       -> unpack
            positional results -> NamedDenseEnv
       -> attach warnings
            NamedDenseEnv -> EvalReport
```
> **Named runtime tensors:** The caller supplies a `NamedDenseEnv`, which maps source tensor names to
> concrete tensor values, including the actual numerical tensor data:
> ```lean
> abbrev NamedDenseEnv := HashMap String DenseTensor
>
> structure DenseTensor where
>   shape : List Nat
>   data  : Array Float
> ```
> An application, test, loader, or bridge constructs this environment and passes it to
> `runPreparedDense`. Eval IR validates, packs, and evaluates the supplied tensors; it does not load
> or generate them.

Thus checked positional execution and named-result reconstruction are part of the Eval IR path.
[`runPreparedDense`](../leanncd/LeanNCD/Eval/Plan/Adapter.lean) composes `pack`, `runDensePlan`, and
`unpack`. `runDensePlan` dispatches all four checked step variants: assignments, scans, pointwise
operations, and axiswise operations. Future backends may lower the same checked semantic plan into
different executable forms.

### 1.4 Experimental JAX path

The experimental JAX path is designed to preserve the same separation: lowering consumes
`PreparedPlan`, while the generated Python function `forward(inputs)` consumes runtime values. Its
`inputs` argument is a Python dictionary of type `dict[str, jax.Array]`, mapping source tensor names
to runtime JAX arrays; it returns another Python dictionary mapping materialized result names to JAX
arrays. The plan's bindings perform the name-to-slot and slot-to-name correspondence.

This is currently a target architecture rather than a working end-to-end evaluator. The checked
graph contains assignment, scan, pointwise, and axiswise steps, but the non-default JAX experiment
still assumes assignment-only checked nodes and does not build against that representation. See
[Section 3.3.2](#332-experimental-jax-evaluator) for the status of each component.

## 2. Plan preparation

### 2.1 `prepareEvalPlan` interface

As shown in [Section 1](#1-pipeline-overview), the source-facing preparation boundary for Backend
Eval IR is:
```lean
prepareEvalPlan
  (sched : ScheduledProgram)
  (sig : InputSignature) :
  Except PlanCompileFailure PreparedPlan
```
This boundary takes a compiled, scheduled program together with static metadata about its external
inputs. It does not take runtime tensor values. Plan preparation resolves source names, axis UIDs,
shapes, and source index expressions into a checked positional plan before any execution backend sees
the tensors' element values.

### 2.2 `prepareEvalPlan` input: `ScheduledProgram`

The structure is defined in
[`LeanNCD/DSL/Pipeline/Types.lean`](../leanncd/LeanNCD/DSL/Pipeline/Types.lean):
```lean
structure ScheduledProgram where
  decls         : List Decl
  stmts         : List ScanStmt
  env           : DeclEnv
  extNames      : Finset String
  explicitSizes : HashMap UID Nat
```
Its fields have the following meanings.

#### 2.2.1 `decls : List Decl`

`decls` is the source declaration list after axis UIDs have been assigned consistently. Declarations
include tensor, predicate, linear-parameter, ordinary-axis, and iteration-axis declarations. `Decl`
is a closed inductive type rather than a record:
```lean
inductive Decl
  | tensor    : String -> List AxisSpec -> Decl
  | predicate : String -> List AxisSpec -> Decl
  | linear    : String -> List AxisSpec -> (bias : Bool) -> Decl
  | axis      : AxisSpec -> Option Nat -> Decl
  | iter      : AxisSpec -> Nat -> Decl
```
The first three constructors declare a named tensor-like value and its axes; `linear` additionally
records whether it has a bias. `axis` declares an ordinary axis with an optional pinned extent, while
`iter` declares a natural-number scan iteration axis whose extent is required. Each `AxisSpec`
contains the axis's source name, canonical `UID`, and kind (`real` or `nat`).

The `assignUIDs` phase, described in
[Section 2.2.6](#226-construction-and-producer-invariants), establishes the producer invariant for
axis identity:

- every distinct source axis name is assigned one fresh, nonzero `UID`;
- equal axis names receive equal UIDs throughout the program;
- distinct axis names receive distinct UIDs.

These facts are properties of values produced by `assignUIDs`; the `List Decl` field itself does not
encode a proof of freshness or uniqueness.

#### 2.2.2 `stmts : List ScanStmt`

`stmts` contains the scheduled source statements in topological order. `ScanStmt` is:
```lean
inductive ScanStmt
  | plain   : Stmt -> ScanStmt
  | scan    : String -> List AxisSpec -> List Stmt -> List Stmt -> Bool -> ScanStmt
  | scanPre : String -> AxisSpec -> ThreadedComposed -> ScanStmt
```
A `plain` node contains an ordinary source statement. A `scan` node retains its iteration axes, base
statements, recurrence statements, and affine-scan flag. A `scanPre` node is the programmatic
pre-routed recurrence escape hatch.

`Stmt` is the source AST for one tensor-producing statement:
```lean
inductive Stmt
  | assign        : String -> List LHSSlot -> RHSExpr -> Stmt
  | scatter       : String -> List LHSSlot -> RHSExpr -> ScatterOpts -> Stmt
  | recurMorphism : String -> AxisSpec -> ThreadedComposed -> Stmt
```
`assign` is an ordinary tensor assignment; `scatter` writes through an affine or potentially
colliding LHS under explicit fill/collision options; `recurMorphism` is the programmatic escape hatch
for a pre-built recurrence morphism. A `Stmt` appears either in `ScanStmt.plain` or in a
`ScanStmt.scan` node's base and recurrence lists.

For `assign` and `scatter`, the computational content of the statement is carried by its
[`RHSExpr`](../leanncd/LeanNCD/DSL/Ast.lean):
```lean
structure RHSExpr where
  body   : SumExpr
  nonlin : Nonlin
  agg    : AggOp := .sum
```
These fields separate three parts of the source computation:

- `body` is a sum-of-products expression. Each product contains `Factor`s, which can read an indexed
  tensor, evaluate a Boolean condition as an Iverson factor (`1` when true and `0` when false), or
  apply an inline unary function such as `log`, `exp`, `sin`, `cos`, `sqrt`, or reciprocal to a
  tensor read.
- `nonlin` describes the operation applied after evaluating the body. It is either `identity`, a
  pointwise function (`relu`, `sigmoid`, `tanh`, `gelu`, or `leakyrelu`), or an axiswise function
  (`softmax`, `normalize`, or `l2normalize`). An axiswise function may carry an optional Boolean mask;
  its reduction axis is the output axis marked by an `LHSSlot.freeNorm` slot.
- `agg` determines how contraction terms are combined: ordinary summation, maximum, or minimum.

Boolean conditions are represented explicitly by `BoolExpr`:
```lean
inductive BoolExpr
  | rel : RelOp -> PredArith -> PredArith -> BoolExpr
  | and : BoolExpr -> BoolExpr -> BoolExpr
  | or  : BoolExpr -> BoolExpr -> BoolExpr
  | not : BoolExpr -> BoolExpr
  | ieq : PredArith -> PredArith -> BoolExpr
```
They can therefore occur in two places inside an `RHSExpr`: as an Iverson factor in `body`, or as the
mask attached to an axiswise `nonlin`. This is distinct from `Decl.predicate` in
[Section 2.2.1](#221-decls--list-decl): that constructor declares the name and axes of a
predicate-valued tensor, whereas `BoolExpr` contains a coordinate-level Boolean formula used while
computing a value.

For example, the following helper accesses the `RHSExpr` of the first scheduled statement when that
statement is an ordinary assignment:
```lean
structure RHSDetails where
  name   : String
  body   : SumExpr
  nonlin : Nonlin
  agg    : AggOp

def firstPlainAssignmentRHS? (sched : ScheduledProgram) : Option RHSDetails :=
  match sched.stmts[0]? with
  | some (ScanStmt.plain (Stmt.assign name _slots rhs)) =>
      some {
        name   := name
        body   := rhs.body
        nonlin := rhs.nonlin
        agg    := rhs.agg
      }
  | _ => none
```
The access path is therefore `sched.stmts`, followed by pattern matching on `ScanStmt` and `Stmt`,
and then ordinary field projection from `rhs`. Given the returned `RHSDetails`, tensor reads and
Iverson predicates are found by iterating through `details.body.terms` and each term's `factors`; an
Iverson predicate appears as `Factor.iverson predicate`. An axiswise mask is found by matching
`details.nonlin` against `Nonlin.axiswise function (some predicate)`. For a `ScanStmt.scan`, the same
`Stmt` matching is applied to the statements in its base and recurrence lists instead of to a
`ScanStmt.plain` payload.

A source statement carrying a non-identity `RHSExpr.nonlin` is lowered into two plan steps at
the plan-preparation boundary rather than in the compile pipeline. `compileToScheduled`
(`Compile.lean`) emits one `ScanStmt` per source statement — no generated `%nl…` names, and no
`splitNonlins` (the former phase survives only as a regression-only helper, off the production
chain; `Pipeline/Lowering.lean`). The pre-activation / nonlinearity separation happens in one of
two places: for the routed artifact, in a private `physicalizeForRoute`
(`Pipeline/RouteFragments.lean`) at the `route` boundary; for the checked plan, in
`prepareEvalPlan`, which lowers the source statement into an internal `PlanStep.assign` whose
result publishes no name, immediately followed by a `PlanStep.pointwise` or `PlanStep.axiswise`
step that publishes the statement's one materialized name. For axiswise operations, only the
second step carries the `LHSSlot.freeNorm` marker that identifies the reduction axis. So one
nonlinear source statement currently yields two plan steps (assign → pointwise/axiswise), and its
appearance in the schedule is a single source-level statement.

`prepareEvalPlan` lowers the following source fragment:

- A top-level `ScanStmt.plain` assignment may contain ordinary tensor-read factors, `sum`
  aggregation, and an identity, pointwise, or unmasked axiswise nonlinearity. A pointwise or axiswise
  statement becomes an internal `PlanStep.assign` followed by `PlanStep.pointwise` or
  `PlanStep.axiswise`; the nonlinear step publishes the statement's result.
- An axiswise statement must have exactly one `LHSSlot.freeNorm` marker. Preparation resolves that
  source marker to `RawAxiswisePlan.axisPos`, after which the checked graph no longer retains an axis
  UID. A missing or duplicate marker, a marker on a non-axiswise statement, or an axiswise mask
  produces a typed `NonlinCompileError`.
- A `ScanStmt.scan` becomes a `PlanStep.scan` when its base and recurrence statements use ordinary
  tensor-read factors, `sum` aggregation, and either identity nonlinearity or an admitted
  pointwise/axiswise nonlinearity (Thread 4 Task 4 admits and lowers the latter through `compileScan`
  — see `LeanNCD/Eval/Plan/Compile.lean` `checkNonlinScanBlock` and the accepted-fixture rationale in
  `test/Eval/Plan/DifferentialTest.lean`). A `RawPlanBlock`'s element type is `BlockStep`
  (`.assign`/`.pointwise`/`.axiswise`) with the block's `steps : Array BlockStep`
  (`LeanNCD/Eval/Plan/RawStep.lean`), not the earlier assignment-only element type.

Capability preflight returns a typed `CapabilityError` for predicate declarations and Iverson
factors, scatters or affine LHS writes, `scanPre` nodes,
and scans with no advancing axis. Nonlinear scan-block statements and normalized-axis slots inside
scan blocks are **now structurally admitted** at this boundary — Thread 4 Task 4 shifted them out
of the rejection set; `max`/`min` aggregation (the max/min-aggregation thread) and unary factors
(`log`/`exp`/…, the unary-factor thread) are likewise **now admitted** — with any residual
obligations reported as `ScanCompileError` instead.
Constructs rejected at this boundary do not appear in the `CheckedEvalPlan` inside the
[`PreparedPlan`](#24-prepareevalplan-output-preparedplan).

Scan admission is narrower than capability preflight alone. The additional obligations need inferred
sizes and lowered affine maps and therefore are reported as a `ScanCompileError` rather than a
`CapabilityError`. `ScanCompileError` (`LeanNCD/Eval/Plan/Error.lean:98-139`) has 24
constructors, which that file enumerates and groups; the obligations they enforce **include**
exactly one all-axis `+1` recurrence result per base destination; base writes that are in range,
pairwise disjoint, and boundary-touching; no state read in a base block; no forward read of
block-local scratch; a nonzero extent for every scan axis; and a non-positive bias on every state
read's advancing rows. That is a sample, not the whole set. Constructors not named above cover, among
others, the scan's context axes (no duplicate context axis, no `iterAt` in a step block or
`iterNext` in a base block, no pinned axis that is not context, no context axis reappearing as a
free output), per-state geometry consistency (state rank, advancing dimension, and extent must agree
across all of a state's placements), and result/producer well-formedness (a scan with no persistent
state, an orphan base state, an orphan advancing result, a duplicate state result, a duplicate
scratch producer, a duplicate axis in an LHS, an advancing axis missing from an LHS). Consult
`Error.lean` rather than this paragraph for the authoritative list. Unavailable block reads identify
whether the name is unknown, a forward reference, or a self-read. A rejection by the checked-plan
validator (`checkScanPlan`) on compiler output is neither a capability nor a scan-compilation
rejection; it is an internal compiler bug and surfaces as `PlanCompileCause.invalidPlan`.

#### 2.2.3 `env : DeclEnv`

`DeclEnv` is:
```lean
abbrev DeclEnv := HashMap String Decl
```
The `String` key is the source name declared by a tensor-like `Decl`: the name carried by a
`tensor`, `predicate`, or `linear` constructor. See
[Section 2.2.1](#221-decls--list-decl) for the definition of `Decl`.
`resolveDecls` builds the map from these declarations; ordinary `axis` and `iter` declarations are
excluded because their names identify axes rather than tensor-like values.

The environment supports declaration lookup during later checks and compilation. It is a source
environment, not a runtime tensor environment: it contains declarations rather than `DenseTensor`
values.

#### 2.2.4 `extNames : Finset String`

`extNames` is the set of tensor names that are read but never produced by a statement in the source
program. An undeclared read is intentionally treated as an external input rather than as a declaration
error.

> **`Finset`:** Lean's `Finset String` represents a finite collection of strings with no duplicate
> members and decidable membership. It is used here because `extNames` answers a set question--whether
> a name is external--and should not contain the same name more than once. Source order is deliberately
> not part of this field; plan preparation derives deterministic input order separately from the
> scheduled statement traversal.

At scheduling time this set is filtered to names actually read by the scheduled statements. Plan
preparation records those external names in first-seen-read order.

#### 2.2.5 `explicitSizes : HashMap UID Nat`

`explicitSizes` contains statically pinned axis extents:

- `axis a = n` contributes `a.uid -> n`;
- `iter a = n` contributes `a.uid -> n`.

UIDs are canonical by the time this map is constructed. The map is the initial seed for
signature-driven axis-size inference. It does not claim that every axis is already sized; remaining
sizes may be inferred from input tensor signatures. An unresolved required axis is a typed shape
error during plan preparation rather than a default extent.

#### 2.2.6 Construction and producer invariants

Before constructing `ScheduledProgram`, `compileToScheduled` runs the following phases:

1. `assignUIDs` gives source axes canonical identities.
2. `resolveDecls` constructs the declaration environment and classifies external names.
3. `reclassifyIterSlots` recognizes an offset-by-one write as a recurrence only when its axis was
   declared with `iter`.
4. `checkReadRanks` checks tensor-read arities against known declarations and producers.
5. `checkDtypes` checks source axis and tensor datatype compatibility.
6. `checkScatterNonlin` rejects nonlinear scatter writes whose semantics are not defined.
7. `checkScatterNoScan` rejects scatter-shaped writes in scan iteration slots.
8. `lowerArith` lowers source index arithmetic and classifies affine or diagonal writes as scatters.
9. `finalizeScans` groups matching base and recurrence statements into `ScanStmt.scan` nodes.
10. `schedule` topologically orders the result and rejects cyclic dataflow.

Neither the compile chain nor the resulting `ScheduledProgram` runs `splitNonlins` or introduces
generated `%nl…` names: a source statement carrying a nonlinearity remains a single `ScanStmt` in
the schedule, and the pre-activation / nonlinearity separation is performed only later, privately
inside `route` (`Pipeline/RouteFragments.lean` `physicalizeForRoute`) or inside `prepareEvalPlan`.
The former `splitNonlins` phase (`Pipeline/Lowering.lean`) survives only as a regression-only
helper, off the production chain.

Consequently, a compiler-produced `ScheduledProgram` satisfies important producer invariants:

- internal producers precede their consumers;
- a cycle is rejected with `CompileError.cyclicDataflow`, rather than represented in source order;
- scans retain their base and recurrence bodies;
- recurrence slots have already been distinguished from ordinary shifted writes;
- the earlier rank, dtype, scatter/nonlinearity, and scatter/scan checks have succeeded.

`ScheduledProgram` is not proof-carrying: its public structure can also be constructed manually.
Consumers that require these properties either rely on `compileToScheduled` as the producer or must
validate equivalent conditions themselves.

### 2.3 `prepareEvalPlan` input: `InputSignature`

The signature structures are defined in
[`LeanNCD/Eval/Plan/Types.lean`](../leanncd/LeanNCD/Eval/Plan/Types.lean):
```lean
inductive ScalarDType
  | f64
  | f32
  | bool

structure TensorSignature where
  shape : Array Nat
  dtype : ScalarDType

structure InputSignature where
  tensors : HashMap String TensorSignature
```
An `InputSignature` maps source-facing external tensor names to concrete shape and storage-dtype
metadata. It is specialization input, not runtime data:

- `shape` records one concrete extent per tensor dimension;
- `dtype` records the proposed scalar storage type;
- no tensor elements, device choices, backend schedules, or positional plan slots appear here.

The structure is intentionally open. By itself, an `InputSignature` does **not** guarantee:

- that every external name required by a particular schedule is present;
- that it has no entries unused by that schedule;
- that a signature's rank agrees with every source read;
- that all source axis sizes can be solved;
- that its dtype is supported by the current plan worker;
- that a later runtime tensor's storage length matches its shape.

Those obligations are established at later boundaries.

#### 2.3.1 Validation relative to a schedule

`prepareEvalPlan` validates the signature against its `ScheduledProgram` in deterministic
first-seen-read order:

1. every required external name must have a `TensorSignature`;
2. every required external tensor must have an ADMITTED dtype (`f64` or `bool`; `f32` is rejected as
   `InputSignatureError.dtypeNotAdmitted`) that also EQUALS the dtype its source declaration commits
   the name to — a name declared `predicate` is `bool`, every other declaration or none at all is
   `f64`. A contradicting explicit signature is rejected as `InputSignatureError.dtypeMismatch`,
   never silently rewritten;
3. `inferAxisSizesFromSignature` combines `explicitSizes` with external tensor shapes and the source
   statements to solve axis extents;
4. any required output or contracted axis that remains unsized produces a typed `ShapeError`;
5. the resulting shapes are compiled into positional `TensorSignature` entries in `RawEvalPlan`.

Extra signature entries are permitted because preparation consults only names required by the
schedule. `ScalarDType.f32` remains a reserved tag with no worker; `bool` is live (Task 4,
[`boolean_predicate_output_evalplan.md`](boolean_predicate_output_evalplan.md)) as a **semantic
algebra/signature tag over the unchanged Float-backed storage**, not a native carrier: a `bool`
destination selects the Boolean min/max algebra (`admittedAlgebraBool`), a `bool` source may feed an
`f64` destination and vice versa, and `DenseTensor` still stores `Array Float` throughout.

#### 2.3.2 Derivation from runtime inputs

When concrete Dense inputs already exist,
`InputSignature.ofDenseInputs` constructs an `InputSignature` by copying each tensor's shape and
assigning dtype `f64`:
```lean
def InputSignature.ofDenseInputs
    (inputs : HashMap String DenseTensor) : InputSignature
```
`InputSignature.ofDenseInputsForDecls` is its declaration-aware sibling: it copies the same shapes
but labels each name from the validated declaration environment (`buildDeclEnv`), so a name declared
`predicate` gets `bool` and every other name `f64`. Preparation derives the same dtype from the same
declarations, so the two agree by construction; `ofDenseInputs` remains the all-`f64` compatibility
helper and is correct exactly when no tensor-bearing name is declared `predicate`.

This is a convenience for callers and tests. It does not collapse preparation and execution into one
phase: only shape and dtype metadata enter `prepareEvalPlan`; the `DenseTensor` values are later
resolved by name, checked against the prepared positional signatures, and packed for execution.

### 2.4 `prepareEvalPlan` output: `PreparedPlan`

The result type is `Except PlanCompileFailure PreparedPlan`. On success, `prepareEvalPlan` returns a
[`PreparedPlan`](../leanncd/LeanNCD/Eval/Plan/Prepared.lean):

> **`Except`:** `Except E A` has two constructors: `.error e`, where `e : E`, and `.ok a`,
> where `a : A`. Thus this function returns either `.error failure` with
> `failure : PlanCompileFailure`, or `.ok plan` with `plan : PreparedPlan`.
```lean
structure PreparedPlan where
  plan     : CheckedEvalPlan
  bindings : PlanBindings
  warnings : List EvalWarning
```
Its three fields separate semantic computation from the source-facing boundary:

- `plan` is the validated, positional, backend-neutral semantic graph. `prepareEvalPlan` first
  assembles a freely constructible `RawEvalPlan`, then passes it to `checkPlan`, which validates graph
  wiring and each assignment, scan, pointwise, or axiswise step. Only on success can the checker call
  the module-private `CheckedEvalPlan.mk`; other modules may read the resulting value but cannot
  construct one directly. The outer `checkPlan` and scan-block `checkPlanBlock` checkers share
  `checkStepGraph`, which enforces their common input ordering, availability, forward-read,
  destination, and complete-production rules while leaving each step's local validation to its
  specific checker.
- `bindings` is a `PlanBindings` sidecar (auxiliary data stored alongside, but outside, the semantic
  graph) containing checked `requiredInputs` and an ordered `materializedNames` array. Both use
  `{ name : String, slot : TensorSlot }` entries: this is name-to-slot metadata, not tensor data.
  The caller's `NamedDenseEnv` separately maps names to actual `DenseTensor` values. During `pack`,
  bindings determine the compact positional input sequence from which `runDensePlan` populates the
  full store; during `unpack`, they determine which positional results receive source names.
  `RequiredBindings` proves that its entries are a permutation of its own stored `inputSlots` array
  and rejects duplicate names. `prepareEvalPlan` constructs that array and
  `plan.raw.inputSlots` together, but the public `PreparedPlan` type does not itself prove that they
  agree. For a compiler-produced plan, `materializedNames` has one entry per persistent scheduled
  output in schedule order. An identity statement publishes its `PlanStep.assign` destination. A
  pointwise or axiswise statement publishes only its trailing nonlinear step's destination; the
  internal assignment introduced by plan compilation has no name. `compileToScheduled` emits no
  generated `%nl…` names — the pre-activation is minted only as the internal `PlanStep.assign`
  inside `prepareEvalPlan`'s two-step chain (`Eval/Plan/Compile.lean`) and publishes no name; the
  regression-only `splitNonlins` helper (`Pipeline/Lowering.lean`) is the only remaining source of a
  `%nl…` name, and it does not run on the production chain. A scan publishes one entry per
  persistent state, so a coupled scan contributes several entries from a single step. Block-local
  scan scratch is never an entry.
  Repeated materialized names are retained so the final publication wins.
- `warnings` preserves nonfatal warnings produced during static shape inference and preparation.

Within `plan`, the underlying `plan.raw.steps` graph is an array of `PlanStep`s, and
`plan.checkedNodes` carries corresponding `CheckedPlanStepEvidence`:
```lean
inductive PlanStep
  | assign    (a : AssignPlan)
  | scan      (s : RawScanPlan)
  | pointwise (p : RawPointwisePlan)
  | axiswise  (a : RawAxiswisePlan)
```
Several step kinds may appear in one graph. A plain identity statement produces one assignment step;
a plain nonlinear statement produces an assignment followed by a pointwise or axiswise step; and an
admitted source scan produces one scan step whose published histories may be read by later steps.

The assignment-side data structures form the following hierarchy:
```text
AssignPlan
  -> Array TermPlan
    -> Array ReadPlan
      -> AffineMap
```
An `AssignPlan` describes one destination tensor and the contraction algebra used to compute it. Its
`contextShape` supports block-local execution inside scans. Its `TermPlan`s describe product terms and
classify their iteration coordinates as context, output, or reduction positions. Each factor is a
`ReadPlan`, which names a positional `sourceSlot` and records how those iteration coordinates select
a coordinate from that source tensor. A `ReadPlan` may also carry a `unary : Option UnaryOp` — an
inline transcendental function (`log`/`exp`/`sin`/`cos`/`sqrt`/`recip`) that Dense's `gatherFactor`
applies to the gathered value *after* the out-of-bounds zero-pad, so an out-of-bounds read contributes
`f(0)`. The math and its domain partiality live once in `UnaryOp.applyChecked` (shared with the
reference `applyUnaryFn`); `log`/`sqrt`/`recip` fail loud on a domain violation as
`PositionalInputError.unaryDomain`.

That coordinate transformation is represented explicitly by
[`AffineMap`](../leanncd/LeanNCD/Eval/Plan/Kernel.lean):
```lean
structure AffineMap where
  coeffs : Array (Array Int)
  bias   : Array Int
```
Semantically, it computes:
```text
sourceCoordinate = coeffs * iterationCoordinate + bias
```
There is one coefficient row and one bias value for each source-tensor dimension. During plan
preparation, supported source index expressions are converted into these rows and stored in
`ReadPlan.map`; the original axis names and UIDs are no longer needed. For example, a one-dimensional
read indexed by `2 * i + j - 1` becomes a row with coefficients `[2, 1]` and bias `-1`, relative to
the term's iteration-coordinate basis. These are read-side affine maps used to gather factor values.
Affine LHS writes and scatters remain outside the source fragment currently admitted by
`prepareEvalPlan`.

Pointwise and axiswise steps contain no term, factor, or affine-map structure. Both name one source
slot, one destination slot, and one concrete shape. A pointwise step additionally stores a
`PointwiseFn`; an axiswise step stores an `AxiswiseFn` and the resolved zero-based reduction-axis
position. Their checked forms prove slot, dtype, and shape agreement, and an axiswise plan also proves
that its axis position is in range.

On failure, `prepareEvalPlan` returns:
```lean
structure PlanCompileFailure where
  cause    : PlanCompileCause
  warnings : List EvalWarning
```
> **Failures and warnings:** `PlanCompileCause` distinguishes input-signature, capability, shape,
> source-scan compilation, checked-plan validation, binding, and nonlinearity-compilation failures.
> `PlanCompileFailure` pairs one such cause with warnings accumulated before failure. `EvalWarning`
> currently has one case,
> `paddedAccess source maxIndex dimension`: the access may exceed that dimension, but execution
> remains valid because out-of-range reads are zero-padded.

### 2.5 Guarantees after successful preparation

If `prepareEvalPlan sched sig` returns a `PreparedPlan`, then, for the currently admitted source
fragment:

- every required external input has a concrete admitted signature;
- every axis needed by the compiled plan has a concrete extent;
- source names and UIDs have been eliminated from the checked semantic graph;
- graph data is positional and backend-neutral;
- name-to-slot information survives only in the separate `PlanBindings` boundary sidecar;
- the generated `RawEvalPlan` has passed `checkPlan`;
- no runtime tensor values have yet been consumed.

Runtime execution is therefore responsible for values and storage agreement, while preparation is
responsible for static source specialization and semantic-plan validity.

## 3. Backend execution and results

The [`PreparedPlan` produced in Section 2.4](#24-prepareevalplan-output-preparedplan) is the common
source-facing input to backend evaluators. It carries the checked backend-neutral computation,
name-to-slot bindings, and preparation warnings, but no runtime tensor data. Each backend combines
this prepared static information with caller-supplied tensor values.

### 3.1 Evaluation stages

Backend evaluation separates static backend preparation from runtime numerical evaluation.
`lowerBackend` answers how a prepared plan will execute on a chosen backend: it consumes static plan
information, produces or selects a reusable backend executable, and does not consume tensor values.
`runBackend` answers what that executable produces for a particular set of inputs: it accepts the
actual runtime tensors, binds them to slots, performs the computation, and materializes named results.
Lowering can therefore happen once before running the same executable with multiple input sets.

Conceptually, a backend supplies two operations:
```text
lowerBackend :
  PreparedPlan
  -> BackendLoweringResult BackendExecutable

runBackend :
  BackendExecutable
  -> NamedRuntimeTensors
  -> BackendRunResult NamedRuntimeResults
```
These names describe a common model rather than literal Lean definitions shared by every backend.
`BackendLoweringResult` and `BackendRunResult` stand for each evaluator's own success-or-failure
mechanism, such as Lean's `Except` or a generated Python exception.
An interpreting backend may use the checked plan directly and have no separate lowering artifact; a
compiled backend may produce and validate a backend-specific executable.

The five stages below refine this two-operation model. Backend lowering is the work represented by
`lowerBackend`. Runtime binding, positional execution, and output materialization together make up
`runBackend`. Result reporting is cross-cutting rather than belonging exclusively to either
operation: lowering can report a failure before runtime begins, while binding or execution can report
a failure after runtime inputs have been supplied.

The flow common to backend evaluators has five stages:

1. **Backend lowering.** Translate the `PreparedPlan`, or use its `CheckedEvalPlan` directly
   (available in the `PreparedPlan.plan` field), to obtain an executable form for the chosen backend.
2. **Runtime binding.** Accept a backend-specific mapping from source tensor names to actual runtime
   tensor values. `PreparedPlan.bindings.requiredInputs` determines how each value is represented
   positionally for the evaluator.
3. **Positional execution.** Execute the checked operations supported by the evaluator using
   positional tensor slots. Source names do not participate in the numerical computation.
4. **Output materialization.** Use `PreparedPlan.bindings.materializedNames` to associate selected
   positional results with source-level result names.
5. **Result reporting.** Return the named runtime results and communicate lowering or execution
   failures. Preparation warnings remain available from the originating `PreparedPlan`; whether they
   are included in the backend's result wrapper is backend-specific.

In short, the common model has the following semantic shape:
```text
PreparedPlan + named runtime values
  -> optional backend lowering
  -> name-to-slot binding
  -> positional computation
  -> slot-to-name materialization
  -> named runtime results
```
#### 3.1.1 Backend lowering

Backend lowering turns the checked, backend-neutral plan into the form a particular evaluator can
execute. This may be the original `CheckedEvalPlan`, as in Dense, or a separately validated and
compiled artifact, as intended for JAX. Runtime tensor values are not consumed at this stage.

Its responsibilities are:

- Translate the semantic plan into the backend's executable representation.
- Validate the translated form against backend-specific constraints.
- Construct the reusable executable artifact.

An interpreting backend may fulfill these responsibilities by treating the already checked semantic
plan as its executable.

#### 3.1.2 Runtime binding

Runtime binding is the stage at which actual tensor data first enters evaluation. It accepts the
caller's named tensor values and uses
`PreparedPlan.bindings.requiredInputs` to produce the evaluator's positional input representation.
This is where source-facing names cross into the backend's positional runtime representation.

Its responsibilities are:

- Validate that the named runtime inputs satisfy the required binding interface.
- Resolve each required source name to its `TensorSlot`.
- Arrange the corresponding runtime values in the evaluator's positional input representation.

#### 3.1.3 Positional execution

Positional execution evaluates the checked operations supported by the particular evaluator against
its tensor store. The backend-neutral plan vocabulary contains assignments, scans, pointwise
operations, and axiswise operations, but that does not imply that every evaluator implements every
variant. Operations address tensors by `TensorSlot`; source names have already been removed from the
numerical computation.

Its responsibilities are:

- Validate that the positional inputs agree with the executable's tensor requirements.
- Initialize or populate the evaluator's runtime tensor store.
- Dispatch each supported checked operation in graph order.
- Write each computed value to its destination slot.

#### 3.1.4 Output materialization

Output materialization uses `PreparedPlan.bindings.materializedNames` to read selected positional
slots and associate their values with source-level names. This converts backend-internal results into
the named result environment expected by the caller.

Its responsibilities are:

- Traverse the ordered materialized-name bindings.
- Read each selected value from its positional slot.
- Insert that value into the result environment under its source name.

#### 3.1.5 Result reporting

Result reporting returns the materialized runtime values or a structured lowering, binding, or
execution failure. Preparation warnings remain attached to the originating `PreparedPlan`; each
backend decides whether and how to include them in its result wrapper.

Its responsibilities are:

- Classify any lowering, binding, or execution failure at the boundary where it occurs.
- Attach or preserve the applicable preparation warnings.
- Return the evaluator's success value or failure representation.

### 3.2 Evaluation data structures

The stages above describe evaluation as a process. The complementary data-structure view follows the
static plan, runtime tensors, positional storage, and reported results as they cross the boundaries of
that process. The following subsections introduce those structures; later revisions can expand each
one without changing the stage model.

#### 3.2.1 Prepared and checked plans

`PreparedPlan` is the source-facing static package supplied to an evaluator. Its
`plan : CheckedEvalPlan` field carries the validated positional computation, while `bindings` retains
the metadata needed to cross between source names and tensor slots. The structures were defined in
[Section 2.4](#24-prepareevalplan-output-preparedplan); here their relevant role is to provide the
computation and boundary metadata consumed by backend execution.

#### 3.2.2 Backend executable

`BackendExecutable` is a conceptual name for whatever a backend can execute. It is not one shared
Lean type: Dense uses `CheckedEvalPlan` directly, whereas a compiling backend can introduce a
validated backend-specific representation and generated code.

#### 3.2.3 Named runtime tensors

Named runtime tensors supply the actual tensor data absent from `PreparedPlan`. Their container is
backend-specific, but its keys are source tensor names that
`PreparedPlan.bindings.requiredInputs` maps to positional input slots.

#### 3.2.4 Positional tensor store

The positional tensor store is the backend's runtime collection of tensor values addressed by
`TensorSlot`. It contains bound inputs and intermediate or materialized outputs, allowing numerical
execution to proceed without source-name lookup.

#### 3.2.5 Named runtime results

Named runtime results associate selected computed tensor values with source-level names. They are
constructed from the positional store according to `PreparedPlan.bindings.materializedNames` and use
a backend-specific tensor type and container.

#### 3.2.6 Reports, warnings, and failures

The reporting structures describe more than tensor values: they communicate whether lowering,
binding, or execution succeeded and preserve relevant diagnostics. Preparation warnings originate in
`PreparedPlan`; concrete evaluators determine the successful result wrapper and the failure
representation used at later boundaries.

### 3.3 Backend mappings

The discussion thus far has treated the stages and data structures as a backend-independent
conceptual model. In a concrete evaluator, their representations, boundaries, and even whether a
stage produces a separate artifact depend on the particular evaluator. The following mappings show
how the Dense interpreter and experimental JAX compiler realize the common roles differently.

#### 3.3.1 Dense evaluator

The Dense evaluator interprets the checked semantic plan directly rather than constructing a separate
compiled executable.

| Common stage | Dense implementation |
|---|---|
| Backend lowering | No separate artifact; use `PreparedPlan.plan : CheckedEvalPlan` directly |
| Named runtime tensors | `NamedDenseEnv = HashMap String DenseTensor` |
| Runtime binding | `pack` |
| Positional execution | `runDensePlan` |
| Output materialization | `unpack` |
| Result | `Except PlanRunFailure EvalReport` |

[`runPreparedDense`](../leanncd/LeanNCD/Eval/Plan/Adapter.lean) composes the runtime stages:
```lean
pack
  (plan : PreparedPlan)
  (env : NamedDenseEnv) :
  Except InputBindingError (Array DenseTensor)

runDensePlan
  (c : CheckedEvalPlan)
  (inputs : Array DenseTensor) :
  Except PositionalInputError (Array DenseTensor)

unpack
  (bindings : PlanBindings)
  (env : NamedDenseEnv)
  (result : Array DenseTensor) :
  NamedDenseEnv

runPreparedDense
  (plan : PreparedPlan)
  (env : NamedDenseEnv) :
  Except PlanRunFailure EvalReport
```
`pack` returns positional inputs, `runDensePlan` returns the complete positional store, and `unpack`
returns the original named environment updated with materialized results.
On success, `EvalReport.env` contains the original named environment updated with every materialized
result, and `EvalReport.warnings` contains the preparation warnings. On failure, `PlanRunFailure`
records the binding or positional-execution cause together with those warnings.

#### 3.3.2 Experimental JAX evaluator

The experimental JAX path is intended to compile the prepared semantic plan before runtime
execution.

> **Current implementation status:** The table below maps the intended JAX architecture to the code
> that presently exists; it does not describe a working end-to-end evaluator. The experiment still
> assumes assignment-only checked nodes. It has not been migrated to the current assignment, scan,
> pointwise, and axiswise `CheckedPlanStepEvidence` variants and therefore does not build.

| Common stage | Experimental JAX implementation | Current status |
|---|---|---|
| Backend lowering | `lowerCheckPlanToCandidate` | Source exists, but assumes assignment-only checked nodes and does not compile against the current graph |
| Executable validation | `validateAndConstructExecutable` | Checks step count, assignment-kernel well-formedness, and evidence aggregation; no scan or nonlinearity representation |
| Backend executable | `SomeJaxExecutable`, containing `JaxExecutable evidence` | Types and validator are implemented, but code generation is not wired to consume this executable |
| Named runtime tensors | Python `dict[str, jax.Array]` | Interface emitted by the assignment-only generator; not currently available end to end |
| Runtime binding | Generated or interpreted name-to-slot initialization | Implemented for scan-free plans; experiment currently does not build |
| Positional execution | Generated `jnp.einsum` or Python interpretation of emitted affine tables | Assignment paths exist; scan, pointwise, and axiswise lowering and execution are not implemented |
| Output materialization | Generated or interpreted slot-to-name construction | Implemented for scan-free plans; experiment currently does not build |
| Result | Python `dict[str, jax.Array]` | Intended generated-function result; no currently buildable end-to-end path |

Two partially separate paths currently exist in the experiment. Candidate-lowering code is intended
to produce data for `validateAndConstructExecutable`, while Python generation reads `PreparedPlan`
directly. No current step takes the resulting `SomeJaxExecutable` and generates Python/JAX code from
its validated `JaxExecutable`.

The source-facing experiment also has two explicit lowering modes. `einsumOnly` emits a Python
function containing restricted projection-only `jnp.einsum` contractions. `affineReference` instead
emits static safe-index and validity-mask tables, which
[`evalplan_affine_runtime.py`](../leanncd/experiments/jax_bridge/evalplan_affine_runtime.py)
interprets with ordered factor, reduction, and term folds. Both modes read `PreparedPlan` directly
and are incompatible with the current multi-variant checked graph. The function form below applies
specifically to `einsumOnly`:
```python
def forward(inputs):
    ...
    return outputs
```
When that path is restored, `inputs` will be a Python dictionary mapping source names to actual JAX
arrays. The generated function will place those arrays into positional slots, evaluate the supported
operations, and return a Python dictionary mapping materialized result names to JAX arrays.

The intended distinction remains that Dense interprets `CheckedEvalPlan`, while JAX lowers it before
runtime. Both are meant to preserve the `PreparedPlan` boundary's name-to-slot,
positional-computation, and slot-to-name structure; only the Dense path currently realizes that
structure end to end.
