# Wave C proposal: a checked backend-neutral `EvalPlan`

## Status and purpose

`EvalPlan` denotes the proposed backend-neutral execution intermediate-representation (IR) design
for LeanNCD. This document proposes the architecture and implementation sequence for Wave C, the
minimal `EvalPlan` milestone described in
[`restructure_suggestions.md`](restructure_suggestions.md). It is intended to stand alone: it
explains the current evaluator, the problem Wave C solves, the proposed types and phase boundaries,
the role of external literature, the deliberate deferral of scans, and the acceptance criteria for
calling Wave C complete.

The proposal is intentionally narrower than the terminal backend project. Wave C should establish
one checked, canonical, backend-neutral execution plan and a Lean `DenseTensor` worker for the
scan-free real sum-product fragment. Here `DenseTensor` means the reference evaluator's concrete
dense tensor value: a shape plus a flat array of binary64 values. PyTorch, JAX, scatter,
nonlinearities, and scans should consume or extend that boundary in later waves; they should not be
pulled into Wave C merely to demonstrate that a backend can run one example.

Two concrete representations implement the `EvalPlan` design:

- `RawEvalPlan` is freely constructible or decoded plan data and is never executable;
- `CheckedEvalPlan` is a validated `RawEvalPlan` whose constructor is private and is the only plan
  representation accepted by a worker.

A plan is **backend-neutral** when every constructor has one mathematical meaning shared by all
workers; **canonical** when it has one deterministic semantic encoding; and **checked** when its
structural and semantic preconditions have been validated before execution. A **worker** is an
interpreter or lowerer that executes a `CheckedEvalPlan` over one tensor representation.

The central recommendation is:

`TLProgram` is the existing source-language program representation. `ScheduledProgram` is the
source-independent, topologically ordered output of compiling a `TLProgram`. `TensorSignature` is a
concrete tensor shape and scalar dtype without element values, and `InputSignature` maps required
source input names to those signatures.

> Treat `CheckedEvalPlan` as a residual program produced by specializing a `ScheduledProgram` to a
> concrete `InputSignature`. Compile names, UIDs, shape inference, affine expressions, and semantic
> choices out of the runtime worker. Validate the resulting first-order positional program once,
> execute only checked plans, and retain the existing scheduled evaluator as an independent oracle.

This is more precise than describing the whole change as "worker/wrapper." Gill and Hutton's
worker/wrapper theory is valuable at representation boundaries, especially runtime packing and
eventual scan carry conversion. It does not by itself justify the compiler pass from
`(ScheduledProgram, InputSignature)` to `CheckedEvalPlan`.

## Table of contents

- [Executive summary](#1-executive-summary)
- [Current architecture and semantic obligations](#2-current-architecture-and-semantic-obligations)
- [Initial Wave C scope and capability boundary](#3-initial-wave-c-scope-and-capability-boundary)
- [Four phases that must not be conflated](#4-four-phases-that-must-not-be-conflated)
- [Plan IR boundary and conceptual types](#5-plan-ir-boundary-and-conceptual-types)
- [Shape inference and plan specialization](#6-shape-inference-and-plan-specialization)
- [Compiling names, UIDs, and affine reads](#7-compiling-names-uids-and-affine-reads)
- [Contraction and numeric semantics](#8-contraction-and-numeric-semantics)
- [Canonical encoding, versioning, and hashing](#9-canonical-encoding-versioning-and-hashing)
- [Correctness framework](#10-correctness-framework)
- [Design influences and their exact applications](#11-design-influences-and-their-exact-applications)
- [Delayed scan phasing](#12-delayed-scan-phasing)
- [Testing and evidence](#13-testing-and-evidence)
- [Frameworks that are attractive but wrong for this phase](#14-frameworks-that-are-attractive-but-wrong-for-this-phase)
- [Implementation plan and concrete artifact inventory](#15-implementation-plan-and-concrete-artifact-inventory)
- [Final recommendation](#16-final-recommendation)
- [Appendix A: detailed Wave C implementation plan](#appendix-a-detailed-wave-c-implementation-plan)
- [References](#17-references)

## 1. Executive summary

### 1.1 The current problem

The current reference evaluator is deliberately direct and inspectable. It accepts a
[`ScheduledProgram`](../leanncd/LeanNCD/DSL/Pipeline/Types.lean), infers concrete axis sizes from
input tensors, and evaluates statements in topological order. For every output coordinate and every
contracted coordinate, however, it constructs or extends a `HashMap UID Int`, where `UID` is the
source-level identity of an axis. Each index expression then looks up its axes in that map. In
[`Gather.evalIdx`](../leanncd/LeanNCD/Eval/Gather.lean), a missing UID silently defaults to zero.

That representation is appropriate for a small reference interpreter, but it is the wrong contract
for compiled array backends:

- UIDs and tensor names are source identities, not efficient runtime coordinates.
- Concrete shapes and reduction domains must be static for JAX and useful for PyTorch compilation.
- Function-valued records such as the current `Combine` contraction-operations record cannot be
  serialized or interpreted exhaustively by another language.
- Backend workers need closed policies for padding, reductions, dtype, scatter, and scans.
- A backend should not repeat shape inference or decide what an unresolved source construct means.

### 1.2 Proposal vocabulary and boundary

The remaining quantities first used in the pipeline below have these meanings:

- `PlanBindings` maps source tensor names to numeric tensor slots at the API boundary.
- `PlanFingerprint` is the hash of the canonical semantic encoding of a `CheckedEvalPlan`.
- `PreparedPlan` packages a `CheckedEvalPlan`, its `PlanBindings`, preparation warnings, and its
  derived `PlanFingerprint`.
- `PlanCompileFailure` packages a closed plan-preparation error with warnings accumulated after
  capability and input-signature preflight.

Section 5 gives their conceptual Lean definitions and invariants.

The proposed pipeline is:

```text
TLProgram
  | source compilation
  v
ScheduledProgram
  | plan compilation, specialized to InputSignature
  v
PreparedPlan
  |- CheckedEvalPlan       semantic, positional, name-free kernel
  |- PlanBindings          source names <-> numeric tensor slots
  |- warnings              diagnostics produced during preparation
  `- fingerprint           PlanFingerprint derived from CheckedEvalPlan
       |
       |- DenseTensor plan worker       Wave C
       |- PyTorch lowering/worker       later
       `- JAX lowering/worker           later
```

The honest preparation boundary is:

```text
(ScheduledProgram, InputSignature) -> Except PlanCompileFailure PreparedPlan
```

It is not merely `ScheduledProgram -> CheckedEvalPlan`, because plan preparation needs concrete
input shapes and dtypes, and returns source-facing bindings and warnings in addition to the
executable plan.

### 1.3 What Wave C removes

Wave C removes two dictionary protocols from the new worker, at different phases:

1. **Axis UIDs leave during plan compilation.** Every accepted UID is resolved to a coordinate
   position. Every source index-expression AST (`IdxExpr`) is lowered to an integer-affine map over
   an ordered coordinate vector. The worker uses `Array Int` coordinates and matrix/vector
   arithmetic, not `HashMap UID Int`.
2. **Tensor names leave at runtime adaptation.** `PlanBindings` packs named input tensors into
   numeric slots before invoking the worker and unpacks materialized slots into the named report
   afterward. The worker reads and writes slot numbers, not `HashMap String DenseTensor`.

The existing evaluator keeps both maps. That independence is useful: it prevents the new worker and
its oracle from sharing the same likely implementation mistake.

### 1.4 What Wave C deliberately does not do

Wave C does not claim that scans are unimportant or outside the final `EvalPlan` design. The initial
Wave C compiler should instead reject scan nodes with a `CapabilityError` that identifies the scan
capability and source context. `CapabilityError` is the closed family of valid-but-unsupported
plan-compilation cases defined in Section 5.5. The existing `evalScheduled` continues to evaluate
scans.

This deferral avoids freezing the current incidental scan encoding - parallel lists of base and
recurrence statements matched partly by names - into a versioned wire format before recurrence and
the four scan execution phases have been given explicit plan-level types.

## 2. Current architecture and semantic obligations

### 2.1 Source compilation already has a real boundary

Wave E separated source compilation from scheduled execution:

```text
TLProgram.eval
  -> compileToScheduled
  -> evalScheduled
  -> EvalReport or EvalFailure
```

[`Eval.Entry`](../leanncd/LeanNCD/Eval/Entry.lean) owns the source compiler dependency.
[`Eval.evalScheduled`](../leanncd/LeanNCD/Eval/Eval.lean) consumes only a
`ScheduledProgram`, concrete `DenseTensor` inputs, and evaluator workers. It returns:

```lean
structure EvalReport where
  env : HashMap String DenseTensor
  warnings : List EvalWarning
```

On failure, `EvalFailure` preserves both the fatal typed error and warnings produced before the
failure. This diagnostic behavior is observable and must survive plan execution.

### 2.2 What a `ScheduledProgram` still contains

[`ScheduledProgram`](../leanncd/LeanNCD/DSL/Pipeline/Types.lean) is compiled source, but it is not a
backend execution IR. It still contains:

- source tensor names and a declaration environment keyed by names;
- `AxisSpec` values and UIDs;
- `Stmt` and `ScanStmt` source-level constructors;
- `IdxExpr` syntax;
- nonlinearities and aggregation choices in AST form;
- explicit axis-size seeds, but not all inferred concrete shapes;
- scan groups represented as axis lists plus base/recur statement lists.

It is an appropriate input to plan compilation because source parsing, name resolution, structural
validation, scan grouping, nonlinearity splitting, scheduling, and topological ordering have already
occurred. It is not appropriate as the shared Python/JAX/PyTorch contract because too many semantic
questions remain implicit.

### 2.3 The reference evaluator semantics that the plan must preserve

Wave C must preserve these behaviors for its accepted fragment:

- statements execute in scheduled producer-before-consumer order;
- the successful environment contains original inputs and every computed intermediate, not only
  declared final outputs;
- each product term contracts only the axes mentioned by that term;
- factors are combined in source order;
- terms are combined in source order;
- reduction coordinates follow the reference cartesian order;
- out-of-range reads, including negative indices, produce zero;
- missing or contradictory shapes fail loudly;
- empty factor products and reduction domains use explicit identities;
- diagnostics remain typed and warnings remain outcome data.

These are documented in
[`Eval/AGENTS.md`](../leanncd/LeanNCD/Eval/AGENTS.md) and implemented primarily by
[`Contract.lean`](../leanncd/LeanNCD/Eval/Contract.lean),
[`Gather.lean`](../leanncd/LeanNCD/Eval/Gather.lean), and
[`SizeInfer.lean`](../leanncd/LeanNCD/Eval/SizeInfer.lean).

## 3. Initial Wave C scope and capability boundary

Wave C should be ambitious enough to test the real plan architecture but small enough that every
accepted program can be understood and compared exactly. Fixing this boundary before defining the
IR prevents optional fields for constructs that have no Wave C producer or consumer.

### 3.1 Accepted capabilities

The first checked fragment should support:

- scan-free `.plain` assignment steps;
- ordinary free LHS axes only;
- concrete `f64` tensor signatures;
- identity nonlinearity;
- real sum-product contraction;
- plain tensor read factors;
- integer-affine reads, including shifts, scales, and multi-axis affine expressions;
- multiple factors per term;
- multiple terms per assignment;
- per-term contracted axes;
- chained scheduled steps and intermediate tensors;
- zero-padded out-of-bounds reads;
- zero/one dimensions if their semantics are explicitly validated;
- the current full-environment observation through `PlanBindings`.

This fragment exercises the hard parts that justify a plan: positional slots, affine maps,
per-term reduction scope, concrete shape specialization, scheduling, padding, and deterministic
execution.

### 3.2 Typed capability rejection

The first compiler should reject, before worker execution:

- `ScanStmt.scan` and `ScanStmt.scanPre`;
- scatter statements and affine LHS slots;
- `freeNorm`, `iterAt`, and `iterNext` LHS slots;
- pointwise and axiswise nonlinearities;
- masks, predicates, and Iverson factors;
- unary factors;
- max/min aggregation;
- Boolean/predicate outputs;
- any dtype other than the declared initial `f64` mode;
- backend- or value-dependent shapes;
- any recurrence or callback-bearing payload.

Each category needs a closed constructor with the relevant source context. A supported program that
fails to compile is a bug. An unsupported program that reaches the worker is also a bug.

### 3.3 Rejection is staging, not terminal semantics

Typed rejection means "this plan version/capability set does not yet represent the construct." It
must not be confused with declaring that the language construct has no backend meaning. Later waves
must add plan constructors for nonlinearities, scatter, predicates, and scans because those payloads
are part of LeanNCD semantics.

## 4. Four phases that must not be conflated

The most important architectural clarification is that four different transformations occur. They
have different inputs, outputs, error types, and correctness arguments.

| Phase | Input | Output | Resolves | Must not do |
|---|---|---|---|---|
| Source compilation | `TLProgram` | `ScheduledProgram` | parsing/elaboration, declarations, UIDs, structural checks, scan grouping, scheduling | inspect backend tensors or select backend algorithms |
| Plan compilation | `(ScheduledProgram, InputSignature)` | `PreparedPlan` | concrete shapes, slots, affine maps, reduction positions, closed policies, capability checks | execute tensor arithmetic or depend on JAX/PyTorch values |
| Runtime adaptation | named runtime tensors + `PreparedPlan` | indexed worker inputs, then named report | validate signature, pack slots, invoke worker, unpack results, attach diagnostics | infer shapes or reinterpret source syntax |
| Backend lowering/execution | `CheckedEvalPlan` + indexed arrays | indexed result arrays | implement closed plan constructors using Dense/JAX/PyTorch operations | invent fallback semantics for unsupported constructors |

### 4.1 Source compilation

Source compilation answers language questions. Examples include whether an identifier is declared,
whether a recurrence axis was declared with `iter`, whether a read has the declared rank, whether a
dataflow cycle exists, and which scheduled step produces a tensor.

Its errors remain `CompileError`. Wave C should not move these checks into backend code.

### 4.2 Plan compilation

Plan compilation answers execution-IR questions using static source information plus a concrete
input signature. It should:

1. preflight the entire schedule against the declared Wave C capability;
2. validate that the `InputSignature` is complete and structurally compatible with the schedule;
3. run or reuse shape inference from shapes rather than tensor contents;
4. assign deterministic numeric tensor slots;
5. resolve every relevant axis UID into an ordered coordinate basis;
6. lower each accepted index expression to a dense affine map;
7. preserve term and factor boundaries;
8. record ordered per-term reduction positions;
9. replace function-valued semantics with closed operation tags and identities;
10. build a raw plan;
11. validate the raw plan into `CheckedEvalPlan`;
12. canonically encode and fingerprint the checked semantic kernel.

This phase is where the semantic need for `HashMap UID Int` ends.

Capability and input-signature preflight should precede warning-producing shape inference. An
unsupported schedule or invalid signature then has one deterministic error and no preparation
warnings; once both preflights pass, every warning produced by shape inference must survive any later
plan-construction, validation, or execution failure.

### 4.3 Runtime adaptation

Runtime adaptation is intentionally small. Given a prepared plan and a named tensor environment, it
should:

1. look up each required input by the name in `PlanBindings`;
2. verify its concrete shape and dtype against the plan signature;
3. pack it into the corresponding numeric slot;
4. call the selected plan worker;
5. reconstruct the named environment from output/materialized slot bindings;
6. preserve extra original inputs if the source API continues to expose them;
7. attach preparation warnings and backend diagnostics.

It should not perform shape inference, walk `IdxExpr`, allocate UID maps, choose contraction
semantics, or decide how padding works.

### 4.4 Backend lowering and execution

A Dense, PyTorch, or JAX consumer interprets the same closed plan. A backend may choose different
algorithms, but not different mathematics. For example, a generic contraction and an `einsum` fast
path may coexist, but both must implement the plan's affine maps, reduction positions, identities,
padding policy, and operation order policy.

The governing rule from the roadmap remains:

> If JAX and PyTorch require different meanings for an `EvalPlan` constructor, that constructor is
> underspecified.

Backend-specific optimization metadata may exist outside the semantic fingerprint. Backend-specific
mathematical meaning may not.

## 5. Plan IR boundary and conceptual types

The exact Lean syntax should be finalized while implementing the first real consumer. The following
types define the required separation, not a demand to create every record before it is used.

### 5.1 Scalar, signature, slot, and policy vocabulary

Plan compilation needs input metadata, not input values:

```lean
inductive ScalarDType
  | f64 | f32 | bool

structure TensorSignature where
  shape : Array Nat
  dtype : ScalarDType

structure InputSignature where
  tensors : HashMap String TensorSignature

abbrev TensorSlot := Nat

inductive NumericMode
  | reference64

inductive OutOfBoundsPolicy
  | zeroPad

inductive ScalarConst
  | f64  (bits : UInt64)
  | f32  (bits : UInt32)
  | bool (value : Bool)

inductive ScalarBinOp
  | add | mul | min | max | logicalAnd | logicalOr

structure ContractionAlgebra where
  factorOp : ScalarBinOp
  factorId : ScalarConst
  reduceOp : ScalarBinOp
  reduceId : ScalarConst

abbrev PlanFingerprint := ByteArray
```

`ScalarDType` is the closed scalar-type vocabulary. `TensorSlot` is an index into the plan's
`tensorSigs` array and the worker's parallel tensor store. `NumericMode` selects cross-backend
numeric conventions; Wave C has only `reference64`, defined precisely in Section 8.4.
`OutOfBoundsPolicy` is the read policy; Wave C has only `zeroPad`. `ScalarConst` stores a scalar
literal in a dtype-preserving canonical form. `ScalarBinOp` is the closed set of binary scalar
operations, and `ContractionAlgebra` records the operation and identity used within factor products
and across reductions/terms. `PlanFingerprint` is the digest byte string produced by the versioned
hash algorithm selected by the canonical codec; that codec validates the algorithm's exact digest
length, and callers otherwise compare the bytes opaquely.

`InputSignature` is named because it is consumed at a source-facing boundary. The checked semantic
plan is positional and need not retain these names.

Initially plan compilation admits only `ScalarDType.f64`; `f32` and `bool` are reserved closed tags
for later plan capabilities. A valid but unsupported dtype is a capability error, not a
malformed-plan error.

### 5.2 Raw and checked plans

Deserialization and construction should not make an arbitrary value executable:

`checkPlan` is the validating constructor, and `PlanError` is its closed family of raw-plan
violations, detailed in Section 5.5.

```text
RawEvalPlan --checkPlan--> Except PlanError CheckedEvalPlan
```

`RawEvalPlan` is the public record of plan fields accepted from the compiler or codec.
`CheckedEvalPlan` is a private wrapper around that same payload plus the invariant that `checkPlan`
has established every condition below. Every worker accepts only `CheckedEvalPlan`; trusted accessors
may expose its validated payload without exposing its constructor.

The checker should establish at least:

- plan version is supported;
- tensor-slot references are in bounds;
- step inputs refer only to plan inputs or earlier materialized slots;
- shapes and ranks agree across slots, affine-map rows, and iteration domains;
- affine-map coefficient and bias dimensions are exact;
- all reduction positions are in bounds, ordered, and semantically classified;
- every term's output positions project the same extents, in the same order, as its
  `AssignPlan.outputShape`;
- term/factor arrays obey the representation's nonempty/empty conventions;
- scalar constants match the declared dtype;
- operation tags and identities form an admitted algebra;
- every output/materialized slot is produced exactly as the plan format requires;
- no unsupported constructor can be smuggled through a malformed encoding.

This makes worker preconditions a theorem or invariant of checked construction rather than repeated
defensive checks in every inner loop.

### 5.3 A minimal semantic kernel

For the first fragment, a plan can remain small. Conceptually:

```lean
structure AffineMap where
  coeffs : Array (Array Int)  -- source-rank rows over the term coordinate basis
  bias   : Array Int

structure ReadPlan where
  sourceSlot  : TensorSlot
  map        : AffineMap
  sourceShape : Array Nat
  oobPolicy   : OutOfBoundsPolicy

structure TermPlan where
  iterationShape : Array Nat
  outputPos       : Array Nat
  reductionPos    : Array Nat
  factors         : Array ReadPlan

structure AssignPlan where
  destinationSlot : TensorSlot
  outputShape     : Array Nat
  terms           : Array TermPlan
  algebra         : ContractionAlgebra

structure RawEvalPlan where
  version     : Nat
  tensorSigs  : Array TensorSignature
  inputSlots  : Array TensorSlot
  steps       : Array AssignPlan
  numericMode : NumericMode

structure CheckedEvalPlan where private
  raw : RawEvalPlan
```

This sketch leaves room to factor common iteration domains or maps if actual duplication appears.
Wave C should not create a general graph-IR framework, optional-field mega-record, or backend class
hierarchy before a second use justifies it.

`AssignPlan.outputShape` and the output projection of each `TermPlan.iterationShape` are deliberately
redundant at the raw-data boundary: the checker requires exact agreement, so checked plans have no
precedence rule or ambiguity between them.

### 5.4 Bindings and prepared plans

Source names are necessary for API compatibility and diagnostics, but they should be sidecar data:

```lean
structure SlotBinding where
  name : String
  slot : TensorSlot

structure PlanBindings where
  requiredInputs    : Array SlotBinding
  materializedNames : Array SlotBinding

structure PreparedPlan where
  plan        : CheckedEvalPlan
  bindings    : PlanBindings
  warnings    : List EvalWarning
  fingerprint : PlanFingerprint
```

`materializedNames` includes every produced tensor currently observable in `EvalReport.env`,
including compiler-generated intermediates if they are currently exposed. The runtime wrapper starts
from the original input environment and inserts these materialized results. That preserves extra
input entries that are not semantically consumed by the plan.

The semantic plan and its fingerprint do not need source names. `PlanBindings` can be replaced for
an alpha-renamed source program - one whose tensor names are changed consistently without changing
dependencies or source order - without changing the indexed computation. The `fingerprint` field is
derived data: preparation computes it from `plan`, and decoding recomputes rather than trusts a
persisted digest.

### 5.5 Error families

Wave C introduces error producers that did not exist in Wave E, so it is now appropriate to define
new closed families:

- `InputSignatureError`: a required signature is missing, malformed, or incompatible with the
  scheduled declarations;
- `InputBindingError`: a runtime named input is missing or differs from its prepared shape/dtype;
- `CapabilityError`: a valid scheduled construct is outside the declared plan fragment;
- existing `ShapeError`: shape inference could not derive one consistent concrete shape assignment;
- `PlanError`: a raw plan violates a structural or semantic invariant;
- `PlanCodecError`: canonical encoding/decoding failure or unsupported wire version;
- later, `BackendError`: a checked plan failed at a backend boundary, carrying plan fingerprint and
  backend context.

These should remain nested causes rather than flattened strings. As with Wave E diagnostics, there
should be no `unsupported String` escape hatch.

Conceptually:

```lean
inductive PlanCompileCause
  | inputSignature (cause : InputSignatureError)
  | capability     (cause : CapabilityError)
  | shape          (cause : ShapeError)
  | invalidPlan    (cause : PlanError)

structure PlanCompileFailure where
  cause    : PlanCompileCause
  warnings : List EvalWarning
```

`PlanCompileFailure` is the failure type of `prepareEvalPlan`. Signature and capability preflight
occur before warning-producing shape inference, so those causes carry `warnings := []`. Once
preflight succeeds, warnings produced while inferring shapes or constructing a plan survive a later
`ShapeError` or `PlanError`, analogously to `EvalFailure`. `PlanCodecError` belongs to encode/decode
APIs rather than `prepareEvalPlan`; `pack` reports `InputBindingError`; `BackendError` belongs to
later backend execution APIs.

## 6. Shape inference and plan specialization

### 6.1 Why `InputSignature` is required

[`inferAxisSizes`](../leanncd/LeanNCD/Eval/SizeInfer.lean) derives axis extents from:

- explicitly pinned axis sizes;
- concrete shapes of external tensors;
- affine read positions;
- inferred scatter output shapes;
- a fixpoint over dependencies.

Consequently a scheduled program alone does not determine one concrete execution plan. The same
schedule may be specialized to different input shapes, and JAX compilation caches will also
distinguish those shapes.

### 6.2 Separate shape metadata from `DenseTensor`

Wave C should add a shape-signature entry to size inference rather than parameterizing the entire
evaluator over a hypothetical generic tensor interface. The size solver needs shape metadata, not
tensor reads. This keeps Wave E's pure `SizeSolve` boundary and avoids inventing a backend abstraction
before a second worker needs one.

The existing `DenseTensor` entry can become a thin projection:

```text
named DenseTensor inputs -> InputSignature -> inferAxisSizesFromSignature
```

### 6.3 Preparation warnings

The fully-known affine padded-access warning depends on shapes and index maps, so it belongs to plan
preparation. It should be attached to `PreparedPlan` and preserved through any later runtime or
backend failure.

Warnings are not semantic instructions and should not affect the plan fingerprint. A change to
warning text must not invalidate a compiled-kernel cache.

## 7. Compiling names, UIDs, and affine reads

### 7.1 Tensor names become slots

[`buildExtIndex`](../leanncd/LeanNCD/DSL/Pipeline/Lowering.lean) and
[`buildNameToStep`](../leanncd/LeanNCD/DSL/Pipeline/Lowering.lean) already demonstrate deterministic
name-to-index assignment for routing. Wave C should reuse the ordering policy where its contract is
appropriate rather than inventing a second nondeterministic traversal.

Plan compilation assigns:

- required external tensors to input slots;
- each produced intermediate/output to one destination slot;
- each factor read to a source slot.

The worker receives an indexed tensor store. Name lookup occurs once while packing and once while
unpacking, not inside every factor read.

### 7.2 Axis UIDs become coordinate positions

Axis identity remains UID-based while compiling. Names must never be used to decide whether two axes
are equal. For each term, plan compilation constructs an ordered coordinate basis:

```text
retained output axes ++ that term's contracted axes
```

In the conceptual `TermPlan`, `iterationShape` gives the extent of that basis and `outputPos` and
`reductionPos` classify its positions. The minimal compiler may always place output positions first
and reduction positions second; keeping the classification explicit makes the worker and checker
state the rule rather than rediscover it from affine coefficients.

Every `IdxExpr` is then densified over that basis. Let `iterationCoordinate : Array Int` be one
coordinate in this term basis, let `sourceCoordinate : Array Int` be the coordinate read from the
factor's source tensor, let `r` be the term-basis rank, and let `s` be the source-tensor rank. The
read map has:

```text
coeffs : s x r integer matrix
bias   : s-vector
```

At runtime:

```text
sourceCoordinate = coeffs * iterationCoordinate + bias
```

No UID is required after this lowering.

### 7.3 Reuse the existing affine primitive

[`idxAffineForm`](../leanncd/LeanNCD/DSL/Ast.lean) is already the shared sparse affine
normalization primitive. [`idxToRow`](../leanncd/LeanNCD/DSL/Pipeline/Lowering.lean) and
[`ScanStmt.elaborateReindexings`](../leanncd/LeanNCD/DSL/Pipeline/Lowering.lean) already densify
those forms into well-formed `StMatP` matrices over a deterministic degree basis.

Wave C should reuse those functions or extract the smallest genuinely shared helper. It should not
write a third affine parser. However, the routed artifact is not by itself an execution plan:

- `elaborateReindexings` groups reads at step scope;
- execution must preserve source term and factor boundaries;
- contracted axes are scoped per term, not across the entire assignment;
- operation identities and padding behavior are not carried by `StMatP`;
- the execution plan needs concrete shapes and numeric tensor slots.

Therefore Wave C can reuse the affine artifact without routing execution through `BrBaseP`.

### 7.4 Do not infer reduction axes from matrix coefficients

A syntactically mentioned axis may densify to a zero coefficient after normalization. It still
belongs to the term's iteration/reduction domain and therefore affects multiplicity. For example, a
factor that mentions an axis with coefficient zero can still be repeated once for every coordinate
of that contracted axis under the current source semantics.

Reduction positions must be compiled from the term's UID occurrence and scoping rules, then resolved
to basis positions. They must not be reconstructed later by asking which affine-map columns contain
nonzero coefficients.

## 8. Contraction and numeric semantics

### 8.1 Defunctionalize `Combine`

The current [`Combine`](../leanncd/LeanNCD/Eval/Contract.lean) stores Lean functions:

```lean
structure Combine where
  mul     : Float -> Float -> Float
  combine : Float -> Float -> Float
  unit0   : Float
  unit1   : Float
```

That is convenient inside one Lean interpreter but cannot be serialized or interpreted
exhaustively by Python. Wave C instead uses the closed `ScalarBinOp`, `ScalarConst`, and
`ContractionAlgebra` types defined in Section 5.1. Its only admitted value is real sum-product:

```text
factorOp = mul, factorId = f64(bitPattern(1.0))
reduceOp = add, reduceId = f64(bitPattern(0.0))
```

Here `bitPattern(x)` means the IEEE-754 binary encoding of the displayed binary64 value `x`, matching
the `ScalarConst.f64` representation from Section 5.1.

The remaining operation tags are reserved for later plan capabilities. They become admissible only
when the checker, every relevant worker, and dtype rules implement the same backend-independent
meaning.

This is an instance of Reynolds-style **defunctionalization**: a finite family of functions is
replaced by a first-order tag plus an interpreter. The important benefit is not the terminology but
the exhaustive, serializable semantic contract.

`reduceOp` and `reduceId` intentionally serve both the reduction over one term's contracted
coordinates and the fold that combines completed terms into the output. This exactly mirrors the
current `Combine.combine`/`unit0` protocol; the proposed format does not silently permit different
operations at those two layers.

### 8.2 Preserve term boundaries

For every output coordinate:

1. iterate terms in source order;
2. for one term, iterate only its contracted coordinates;
3. begin each factor fold at `factorId`;
4. gather and combine factors in source order;
5. begin the term's reduction at `reduceId`;
6. reduce product values in the declared coordinate order;
7. combine the completed term with the output accumulator in source order.

Flattening all factors and contracted axes into one equation-wide reduction changes programs such as:

```text
Y[i] := A[i] + P[i,j]
```

The `A[i]` term must be added once, not once per `j`.

### 8.3 Preserve maps, not just flattened offsets

Zero-padding validity is defined per source dimension. A backend may compute a flat storage offset
only after it has checked:

```text
0 <= sourceCoordinate[d] < sourceShape[d]
```

for every source-dimension position `d`. Flattening the affine map directly to one offset can alias distinct
invalid coordinates to an apparently valid flat address and lose the padding semantics.

The plan should therefore retain one affine coordinate row per source dimension. Backends may derive
strides and flat offsets as a checked optimization.

### 8.4 Numeric modes and ordering

`NumericMode.reference64` means:

- Lean `Float`/binary64 inputs and outputs;
- source statement, term, factor, and reduction traversal order preserved;
- Lean scheduled evaluator versus Lean plan worker compared bit-for-bit.

Later PyTorch/JAX agreement should use an explicit tolerance policy because vectorized reductions or
compiler transformations may reassociate floating-point operations. That later tolerance must not
weaken the Lean-to-Lean Wave C oracle, where both workers can preserve the same order.

## 9. Canonical encoding, versioning, and hashing

### 9.1 Canonical data first

`CheckedEvalPlan` should have one canonical encoding with:

- explicit wire-format version;
- fixed constructor tags;
- deterministic array order;
- fixed integer and scalar encodings;
- no map iteration whose order depends on hashing;
- no backend object, callback, closure, or host pointer;
- no redundant fields whose disagreement would require a precedence rule.

Decode into `RawEvalPlan`, then validate. Never deserialize directly into an executable checked
value.

### 9.2 Semantic fingerprint

The fingerprint should change when any semantic element changes:

- tensor shapes or dtypes;
- step order and dependency slots;
- affine coefficients or biases;
- output iteration shapes;
- term/factor/reduction order;
- operation tags and identities;
- constants;
- padding, scatter, scan, or exceptional-row policies;
- numeric mode;
- plan wire/semantic version when it changes interpretation.

It should not change for:

- alpha-renaming source tensor names;
- diagnostic display names;
- warning text or warning ordering;
- backend device choice;
- backend-specific optimization hints that cannot change meaning.

This identifies the unbound indexed kernel. A runtime cache key may extend it with:

```text
(planFingerprint, backend, backendVersion, deviceKind, numericMode)
```

Alpha-renaming invariance depends on deterministic first-seen/source-stable scheduling and slot
assignment, never lexical sorting by tensor name. Fingerprint tests should pin that property so a
future scheduling change cannot make names semantic accidentally.

### 9.3 Canonicalization is not optimization

Canonicalization should remove representation ambiguity, not silently reorder floating-point
programs. Sorting terms or factors because an algebra is mathematically commutative can alter
binary64 results and destroy exact differential testing. Keep source-prescribed order in the
semantic encoding.

## 10. Correctness framework

The proposal is governed by five explicit laws. The notation used by all five is:

- `prepareEvalPlan(sched, sig)` prepares a `ScheduledProgram` `sched` for an `InputSignature` `sig`;
- `pack(bindings, namedInputs)` validates and converts the source-name-keyed tensor environment
  `namedInputs` into a tensor store indexed by `TensorSlot`;
- `runDensePlan(plan, slotInputs)` executes `CheckedEvalPlan` `plan` with the Dense worker;
- `unpack(bindings, namedInputs, slotOutputs)` inserts every bound materialized result from
  `slotOutputs` into the original `namedInputs` environment;
- `runPreparedDense(prepared, namedInputs)` is the complete runtime adapter:
  `pack`, `runDensePlan`, `unpack`, and attachment of `prepared.warnings`;
- `x =obs y` means that two source-visible outcomes have equal typed success/failure structure,
  equal warnings, equal environment keys, and tensors equal under the active numeric mode.

For `NumericMode.reference64`, tensor equality inside `=obs` is bit-for-bit equality.

### Law 1: residualization

Let `sched` be a schedule accepted by capability preflight, `sig` an accepted input signature, and
`namedInputs` a tensor environment conforming to `sig`. If:

```text
prepareEvalPlan(sched, sig) = ok prepared
```

then:

```text
runPreparedDense(prepared, namedInputs)
  =obs evalScheduled(sched, namedInputs)
```

This is the principal compiler correctness claim.

### Law 2: checked construction

```text
checkPlan(raw) = ok checked
  implies every documented worker precondition holds for checked
```

Here `raw : RawEvalPlan`, `checked : CheckedEvalPlan`, and `checkPlan` is the sole validating
constructor described in Section 5.2. Workers may still report runtime resource failures, but they
must not rediscover malformed ranks, out-of-range slot references, unresolved shapes, or unknown
operation tags.

### Law 3: backend interpretation agreement

For each later backend `B`, define `runBPlan` as its interpretation of `CheckedEvalPlan` and
`=mode` as tensor equality under the plan's `NumericMode`. For the same checked plan and logically
equal inputs represented in each backend:

```text
runDensePlan(plan, denseInputs)
  =mode runPyTorchPlan(plan, torchInputs)
  =mode runJaxPlan(plan, jaxInputs)
```

Wave C establishes the Dense side and the observation protocol. Later waves add the other
interpreters without changing plan meaning.

### Law 4: boundary representation agreement

For every valid `PlanBindings` value, `pack` places each required named input in exactly its bound
slot. Given worker outputs that satisfy the checked plan's slot signatures, `unpack` preserves every
entry of the original named environment and adds or replaces exactly the names in
`materializedNames`. The complete `runPreparedDense` adapter also preserves preparation warnings and
typed failure causes. These properties isolate source-facing representation correctness from the
plan compiler correctness asserted by Law 1.

### Law 5: scan refinement

When scans are added, `ScanPlan` will denote a checked positional node that explicitly records
states, base and step blocks, traversal order, write placement, boundary behavior, and causality.
Let `runGeneralScan` denote its explicit-order interpreter and `runSpecializedScan` an optimization
admitted only when its checker recognizes the required certificate. For the same checked
`scanPlan`, state, and inputs:

```text
runGeneralScan(scanPlan, state, inputs)
  =mode runSpecializedScan(scanPlan, state, inputs)
```

One-axis `lax.scan`, nested scans, parallel prefix, or compile-time unrolling are optimizations only
after this law is tested or proved for their recognized capability.

## 11. Design influences and their exact applications

This section retains only ideas that determine an immediate Wave C design choice or an explicitly
planned extension. Every subsection states the usable idea, the concrete application, and the phase
boundary beyond which the idea does not justify additional work. `C0` through `C6` refer to the
implementation phases in Section 15: contract tests, signature preparation, checked plan types,
plan compilation, Dense execution, codec/fingerprint, and final audit, respectively. `Wave F` is
the later scan-decomposition wave; `Wave G` is the later PyTorch/JAX backend wave.

### 11.1 Partial evaluation: plan compilation produces a residual program

**Usable idea.** Jones, Gomard, and Sestoft's
[*Partial Evaluation and Automatic Program Generation*](https://www.cambridge.org/core/books/partial-evaluation-and-automatic-program-generation/500C671429CC993BE6A5E30C261B943F)
separates an interpreter's inputs into static data known during specialization and dynamic data left
for the residual program. For LeanNCD, the static data is `(ScheduledProgram, InputSignature)`:
scheduled syntax, declarations, shapes, dtypes, explicit sizes, operations, and policies. The
dynamic data is tensor element values.

**Concrete application.** `prepareEvalPlan` specializes the scheduled evaluator's control and
indexing decisions into `CheckedEvalPlan`; `runDensePlan` accepts only indexed tensor values. This
directly determines the plan-compilation/runtime-adaptation split in Section 4 and Law 1:

```text
prepareEvalPlan(sched, sig) = ok prepared
runPreparedDense(prepared, namedInputs)
  =obs evalScheduled(sched, namedInputs)
```

**Phase boundary.** C1 makes shapes available as static signatures; C3 performs the explicit
specialization; C4 tests the residual program against the unspecialized evaluator. Wave C does not
build a general partial evaluator or rely on the Futamura projections as a correctness proof.

### 11.2 Worker/wrapper: convert representations at the worker boundary

**Usable idea.** Gill and Hutton's
[*The Worker/Wrapper Transformation*](https://people.cs.nott.ac.uk/pszgmh/wrapper.pdf) changes the
representation used by a recursive computation. Let `A` be the original representation, `B` the
worker representation, `fix` the least-fixed-point operator, `body : A -> A` the recursive body,
`comp = fix body`,
`unwrap : A -> B` the representation function, and `wrap : B -> A` the abstraction function. From:

```text
wrap . unwrap = id_A
fix(g . f) = g(fix(f . g))
```

where `id_A` is the identity on `A` and `f` and `g` are composable functions, the paper derives:

```text
work = fix(unwrap . body . wrap)
comp = wrap work
```

It also permits the weaker body-specific or fixed-point-specific assumptions:

```text
wrap . unwrap . body = body
fix(wrap . unwrap . body) = fix body
```

It does not require `unwrap . wrap = id_B` for every worker-representation value.

**Concrete application.** At the nonrecursive Wave C boundary, `unwrap` corresponds to
`pack(PlanBindings, namedInputs)`, the worker is `runDensePlan`, and `wrap` corresponds to `unpack`.
This determines the thin runtime adapter and Law 4: source names and dictionaries are converted once,
not inside contraction loops. In the future recursive scan boundary, `A` will be the source-visible
named scan state, `B` a fixed-shape positional carry, `work` the plan-level recurrence, and `wrap`
the reconstruction of complete state tensors.

**Phase boundary.** C4 applies the representation-boundary discipline to pack/run/unpack. Wave F
and later scan lowering may use the formal recursive theorem once `ScanPlan` defines the state
transition and a valid-state relation. Worker/wrapper does **not** prove
`(ScheduledProgram, InputSignature) -> CheckedEvalPlan`; that transformation changes syntax and
specializes static data, so Law 1 remains the relevant obligation.

### 11.3 MLIR Linalg: keep iteration, indexing, and scalar work explicit

**Usable idea.** The [MLIR Linalg dialect](https://mlir.llvm.org/docs/Dialects/Linalg/) represents
structured array operations with shaped operands, an explicit iteration space, affine indexing maps,
iterator classifications such as parallel/reduction, and a scalar payload.

**Concrete application.** This decomposition directly determines the C2 records:

- `TermPlan.iterationShape` is the explicit iteration space;
- `TermPlan.outputPos` and `TermPlan.reductionPos` classify iteration positions;
- `ReadPlan.map` is an affine indexing map;
- `ReadPlan.sourceShape` and `AssignPlan.outputShape` are shaped operands/results;
- `ContractionAlgebra` is the closed scalar payload.

It also explains why the plan retains multidimensional affine maps rather than lowering immediately
to flat offsets, opaque loops, or `einsum`.

**Phase boundary.** C2 defines and checks this structure; C3 lowers source expressions into it; C4
interprets it generically. Later backends may lower checked nodes to MLIR or StableHLO, but those are
derived artifacts, not alternative sources of LeanNCD semantics.

### 11.4 Defunctionalization: semantic choices cross the boundary as closed data

**Usable idea.** Reynolds'
[*Definitional Interpreters for Higher-Order Programming Languages*](https://dl.acm.org/doi/10.1145/800194.805852)
introduced the transformation now called defunctionalization: replace a finite family of function
values with first-order constructor tags and an interpreter for those tags.

**Concrete application.** C2 replaces function-valued `Combine` fields with `ScalarBinOp`,
`ScalarConst`, and `ContractionAlgebra`. Each worker exhaustively interprets those tags. Later plan
versions apply the same rule to nonlinearities, scatter collision operations, exceptional-row
policies, and scan boundary/order policies. No Lean closure, Python callback, or backend callable is
part of canonical plan data.

**Phase boundary.** Wave C implements only the real sum-product tags it consumes. Future tags become
admissible only when the checker and every relevant worker implement one shared meaning; the
reference does not justify speculative constructors without a producer and consumer.

### 11.5 Checked construction: evidence belongs at the raw/executable boundary

**Usable idea.** Noonan's
[*Ghosts of Departed Proofs*](https://arxiv.org/abs/1808.00351) shows how evidence can constrain data
at construction time without imposing the same proof representation on runtime computation.

**Concrete application.** C2 decodes or compiles freely constructible `RawEvalPlan` values, validates
them with `checkPlan`, and exposes only a privately constructible `CheckedEvalPlan` to workers.
Structural evidence may be stored as Lean propositions or established by executable checks and then
erased; the serializable payload remains ordinary first-order data. This determines Law 2 and the
rule that codecs decode to `RawEvalPlan`, never directly to an executable value.

**Phase boundary.** C2 introduces the checked constructor and worker API; C5 applies the same
boundary to decoding. The proposal deliberately avoids indexing every array with a dependent proof
when a private checked wrapper provides the required safety with a simpler codec and worker.

### 11.6 Translation validation: validate each artifact, then test semantic agreement

**Usable idea.** Pnueli, Siegel, and Singerman's
[*Translation Validation*](https://doi.org/10.1007/BFb0054170) validates the result of each compiler
run instead of relying only on a once-for-all proof of the compiler implementation.

**Concrete application.** `checkPlan` validates every compiled or decoded raw artifact before
execution. Separately, the C4/C6 differential matrix executes the independently organized
`evalScheduled` and `runPreparedDense` paths on the same generated programs. The former establishes
structural validity; the latter attacks semantic lowering mistakes.

**Phase boundary.** C2 implements structural artifact validation; C4 and C6 implement differential
semantic validation. `checkPlan` is not claimed to prove source/plan equivalence, and differential
testing is not claimed to be a theorem. A future compiler proof may strengthen Law 1 without
replacing either practical check.

### 11.7 Representation independence: each backend must preserve one plan relation

**Usable idea.** Mitchell's
[*Representation Independence and Data Abstraction*](https://doi.org/10.1145/512644.512669)
characterizes correctness across different concrete representations through a relation preserved by
operations.

**Concrete application.** Law 3 relates Dense tensors, PyTorch tensors, and JAX arrays by declared
shape, dtype, element values, and `NumericMode`. Every plan constructor receives a per-constructor
conformance test showing that related inputs produce related outputs. Backend-specific fast paths
must also relate to the generic interpretation of the same checked node.

**Phase boundary.** C4 establishes the Dense interpretation and observation relation. Wave G adds
PyTorch and JAX interpretations one constructor at a time. The principle rules out backend-specific
mathematical meanings and silent fallback to another worker.

### 11.8 `mapAccumL`: the general scan is an explicit state transition

**Usable idea.** Haskell's
[`mapAccumL`](https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Data-List.html#v:mapAccumL)
gives a sequential scan the type:

```text
step : State -> StepInput -> (State, StepOutput)
```

where `State` is the loop-carried value, `StepInput` the input at one iteration, and `StepOutput` the
value recorded for that iteration.

**Concrete application.** The eventual `ScanPlan.stepBlock` denotes this transition over positional
state slots. `iterationOrder` determines the ordered sequence of `StepInput` coordinates, while
`writeGeometry` determines how `StepOutput` slices materialize in complete state tensors. This is
the semantic model for `runGeneralScan` in Law 5.

**Phase boundary.** Wave F exposes the transition currently hidden inside `evalScan`; the later
`ScanPlan` compiler and Dense scan worker implement it. This model does not imply parallel
execution.

### 11.9 JAX `lax.scan`: a specialized one-axis lowering

**Usable idea.** JAX's
[`lax.scan`](https://docs.jax.dev/en/latest/_autosummary/jax.lax.scan.html) implements a transition
of the same general shape as `mapAccumL`, but requires the carry to keep a fixed tree structure,
shape, and dtype. A **pytree** is JAX's nested tuple/list/dictionary structure whose leaves are
arrays.

**Concrete application.** A checked one-axis `ScanPlan` whose dependencies fit a bounded
fixed-shape carry lowers coupled state slices to one pytree carry and emitted history slices to scan
outputs. Immediate-predecessor scans need only current slices; deeper-history scans must carry the
required bounded history or full fixed-shape state tensors.

**Phase boundary.** This is a post-Wave-F JAX lowering guarded by Law 5. It does not shape the
initial scan-free Wave C representation, and it does not define general multi-axis semantics.

### 11.10 Blelloch prefix scan: parallelization requires separate algebraic evidence

**Usable idea.** Blelloch's
[*Prefix Sums and Their Applications*](https://www.cs.cmu.edu/~guyb/papers/Ble93.pdf) parallelizes
prefix computation when the step summaries form an associative operation with an identity.

**Concrete application.** A future optimization checker may produce a `ParallelScanPlan`, meaning a
`ScanPlan` paired with evidence that its step summaries have a specific associative composition and
identity. For affine recurrences, the summaries may be affine transformations and the operation
function composition; absence of a nonlinearity alone is not sufficient evidence. Law 5 requires
the optimized result to agree with `runGeneralScan`.

**Phase boundary.** This optimization follows the general Dense and backend scan implementations.
It must not be selected from today's `isAffine` flag alone and introduces no Wave C constructor.

## 12. Delayed scan phasing

### 12.1 Scans are part of the final plan

The terminal plan must support:

- one or more ordered state tensors;
- base initialization;
- coupled recurrence statements;
- external reads;
- one or more advancing axes;
- explicit cartesian traversal order;
- zero-default boundary behavior;
- complete state outputs;
- causality evidence;
- fixed shape/dtype carry for JAX-compatible lowerings.

Typed rejection in initial Wave C is temporary capability staging.

### 12.2 Why not encode the current `ScanStmt` immediately

The current
[`ScanStmt.scan`](../leanncd/LeanNCD/DSL/Pipeline/Types.lean) stores:

```text
name, axes, base statements, recurrence statements, isAffine
```

The current [`evalScan`](../leanncd/LeanNCD/Eval/Scan.lean) derives additional semantics at runtime:

1. state names are inferred from base-statement names;
2. full zero state tensors are allocated from base slots;
3. base statements update the evolving `work` environment in order;
4. each recurrence tuple starts from one snapshot `stepEnv := work`;
5. recurrence intermediates live only in `stepEnv`;
6. actual state writes are classified by membership in `stateNames`;
7. state slices are committed into full tensors in `work`;
8. only state tensors are returned.

Those are real semantics, but not yet explicit data. Serializing the two statement lists would make
backends reverse-engineer the same rules and would preserve name matching inside a supposedly
positional IR.

### 12.3 Recommended sequence

As defined for Law 5, `ScanPlan` is the future checked positional scan node. It is not part of the
initial scan-free `RawEvalPlan`.

```text
Wave C: checked stateless EvalPlan + Dense plan worker
   |
typed recurrence representation (roadmap item E2: explicit state and transition data)
   |
Wave F: decompose current evalScan around the plan-level transition
   |
ScanPlan + general Dense scan worker
   |
one-axis PyTorch/JAX scan lowering
   |
flattened explicit-order multi-axis lowering
   |
proved/tested specialized scan optimizations
```

Wave F follows the plan boundary because its helpers should expose the semantics needed by
`ScanPlan`, not merely rearrange the current dictionary implementation.

### 12.4 Eventual `ScanPlan`

The conceptual fields use these quantities:

- `StateSlot` identifies one persistent state by `TensorSlot` and `TensorSignature`, and records
  whether the complete state history is materialized as a result.
- `CheckedPlanBlock` is a privately constructible, validated sequence of plan steps with explicit
  input and output slots; `baseBlock` initializes states and `stepBlock` computes one transition.
- `IterationOrder` is a closed traversal tag; the general first version has only the
  reverse-lexicographic cartesian order implemented by today's
  [`cartesianList`](../leanncd/LeanNCD/Eval/Scan.lean), which enumerates one coordinate list from
  per-axis ranges.
- `StateWriteMap` identifies a state slot and carries the `AffineMap` from iteration-plus-slice
  coordinates to coordinates in that state's complete tensor.
- `ScanBoundaryPolicy` is a closed boundary tag; the first value means zero-initialize complete
  states and then apply explicit base writes.
- `CausalityCertificate` is opaque checker-produced evidence that every state read used by
  `stepBlock` precedes its corresponding write under `iterationOrder`. It proves ordering safety,
  not associativity.

Conceptually:

```lean
structure ScanPlan where
  states          : Array StateSlot
  baseBlock       : CheckedPlanBlock
  stepBlock       : CheckedPlanBlock
  iterationShape  : Array Nat
  iterationOrder  : IterationOrder
  writeGeometry   : Array StateWriteMap
  boundaryPolicy  : ScanBoundaryPolicy
  causality       : CausalityCertificate
```

The plan should state:

- which slots are persistent states;
- which step values are ephemeral intermediates;
- which values are external per-step reads;
- where base slices are written;
- how current iteration coordinates map to next-state write coordinates;
- whether all coupled updates read the same pre-step state snapshot;
- the exact traversal order for multi-axis scans;
- what happens at boundary and zero-length axes;
- which outputs expose full histories versus final carry.

### 12.5 General semantic lowering first

The general scan worker should mirror the current four-phase semantics:

```text
allocate states
apply bases
for coordinate in explicit order:
  oldState = state snapshot
  evaluate step block from oldState
  commit designated state slices simultaneously
return complete states
```

For an immediate-predecessor one-axis scan, coupled current-state slices can form a fixed pytree
carry for `lax.scan`; emitted slices form the history. A one-axis recurrence that reads deeper
history must carry the required bounded history or a full fixed-shape state tensor instead. For
multiple axes, the first backend lowering should flatten the explicit cartesian traversal and carry
full fixed-shape states. Nested scans are a later recognized fast path.

### 12.6 Scan packing boundary

The future scan runtime adapter applies Section 11.2's worker/wrapper assignment directly: the
source-visible named scan state is packed into positional fixed-shape state slots, the recurrence
worker executes `stepBlock`, and complete state tensors are unpacked afterward. The valid-state
relation must establish source observations, while the separate `ScanPlan` compiler remains subject
to the residualization and scan-refinement laws.

### 12.7 Parallel prefix requires evidence

Do not select Blelloch/associative scan solely from `isAffine`, the current `ScanStmt` Boolean hint
that its recurrence is affine, or from absence of a nonlinearity. A specialized parallel lowering
needs one of:

- a closed associative operation and identity already represented in the plan;
- a recognized lifting, such as affine transformations under composition, with a checked
  construction;
- a `ParallelScanPlan` produced by the future optimization checker described in Section 11.10.

Until then, the explicit sequential order is the semantics.

## 13. Testing and evidence

### 13.1 Independent oracle

The existing `evalScheduled` remains unchanged as the reference oracle during Wave C. Do not
implement the plan worker by calling the old evaluator or share its per-cell UID map. The useful
comparison is between two differently organized implementations.

### 13.2 Existing generated corpus

[`PropertyOracle/Gen.lean`](../leanncd/test/Eval/PropertyOracle/Gen.lean) already generates a bounded
scan-free corpus covering:

- affine reads;
- multiple factors and terms;
- chained producer/consumer steps;
- genuine contractions;
- per-term contraction differences;
- materialized intermediates.

It is a strong initial differential corpus. Wave C should add explicit coverage guards for every
accepted plan constructor and rejection category rather than assume the existing enumeration happens
to cover them.

### 13.3 Differential matrix

For every accepted generated case:

1. compile source to `ScheduledProgram`;
2. derive `InputSignature`;
3. prepare and check the plan;
4. execute `evalScheduled`;
5. execute the Dense plan worker;
6. compare all bound materialized tensors bit-for-bit;
7. compare warning lists and typed failures;
8. round-trip the canonical plan encoding and rerun it;
9. verify the fingerprint is stable across round-trip.

For every rejected case:

1. source compilation succeeds;
2. plan preparation returns the expected `CapabilityError`;
3. no plan worker is invoked;
4. capability preflight occurs before shape inference, so no preparation warning is produced.

### 13.4 Mutation tests

The test suite should be able to detect at least:

- missing UID interpreted as coordinate zero;
- tensor slot off by one;
- clipping rather than zero fill;
- negative index wrapping;
- equation-wide rather than per-term contraction;
- reduction axes inferred from nonzero coefficients;
- wrong `factorId` or `reduceId`;
- reordered factors/terms;
- omitted intermediate in the unpacked report;
- name changes perturbing the semantic fingerprint;
- warnings perturbing the semantic fingerprint;
- a raw malformed plan reaching execution.

If deliberately introducing one of these changes does not fail a test, the evidence is too weak.

### 13.5 Later backend evidence

Wave G should extend the matrix in explicit tiers:

```text
emit -> import -> eager -> compiled/jit -> reference agreement
     -> generic/optimized agreement -> cross-backend -> device -> export
```

"Generated code ran" is not the same claim as "generated code agrees with Lean."

## 14. Frameworks that are attractive but wrong for this phase

### 14.1 Tagless-final as the serialized plan

Tagless-final is useful for embedding languages in one host type system. A versioned plan must cross
process and language boundaries, be hashed, decoded, inspected, rejected, and replayed. Closed
first-order data is the appropriate source of truth. Backend interpreters can still be written in a
tagless style internally.

### 14.2 Free monads

Wave C needs a small structured array IR, not a generic effect language. A free monad adds
indirection without solving shape, affine-map, reduction, or serialization semantics.

### 14.3 Hidden state-monad scans

Encoding recurrence as an opaque state computation hides iteration geometry, boundary policy, write
maps, and causality from validation and backend lowering. `ScanPlan` should expose those fields.

### 14.4 Worker/wrapper as the compiler proof

Worker/wrapper helps at representation boundaries. It does not replace Law 1 for a compiler that
specializes and lowers syntax.

### 14.5 Premature polyhedral scheduling

Affine maps make polyhedral techniques tempting. Wave C should first establish correct explicit
iteration and reduction semantics. Tiling, fusion, loop interchange, and dependence analysis are
later optimizations guarded by plan-level agreement tests.

### 14.6 Backend fallback

A JAX or PyTorch consumer must not silently send an unsupported node back to the Lean evaluator or
another backend. That creates mixed semantics, hides capability gaps, and makes plan fingerprints
misleading. Unsupported checked-plan capability should fail before execution.

### 14.7 Routing through `BrBaseP` or a neural-network layer IR

The routed artifact proves and serializes categorical wiring properties but currently drops
execution payloads. A layer-oriented Python IR cannot express all LeanNCD contractions, affine
reads, predicates, scatter policies, and scans. Translating through either would create a second,
semantically incomplete execution IR.

## 15. Implementation plan and concrete artifact inventory

### 15.1 Concrete artifact inventory

The following list assigns every Wave C artifact to the first phase that needs it. **IR** means data
that defines executable plan semantics and therefore participates in checking and canonical
encoding. **Boundary data** carries source-facing metadata but is not part of the semantic IR.
**Function** means an implementation boundary whose behavior must be tested independently.

| Phase | Kind | Artifact | Concrete responsibility |
|---|---|---|---|
| C0 | Contract | capability matrix | Enumerates every accepted and rejected source constructor for the first scan-free `f64` fragment. It is a test/documentation artifact, not a runtime registry. |
| C0 | Contract | observation and ordering laws | Fixes full-environment output, warning preservation, source statement/term/factor order, reduction-coordinate order, and bit-exact `reference64` equality. |
| C1 | Enum | `ScalarDType` | Closed dtype vocabulary. Wave C executes only `f64`; reserved `f32` and `bool` tags remain rejected capabilities. |
| C1 | Structure | `TensorSignature` | Carries one tensor's concrete `shape : Array Nat` and `dtype : ScalarDType`, without values. |
| C1 | Structure | `InputSignature` | Maps required source names to `TensorSignature` values for plan specialization. |
| C1 | Error enum | `InputSignatureError` | Reports missing, malformed, or schedule-incompatible static signatures before warning-producing inference. |
| C1 | Failure structure | `ShapeInferenceFailure` | Couples the existing `ShapeError` with warnings emitted before inference failed; the legacy evaluator and plan compiler map it into their own outer failure types. |
| C1 | Function | `inferAxisSizesFromSignature` | Reuses size inference from signatures alone and returns the same sizes, `ShapeError`, and warnings as the Dense-input path. |
| C2 | Index type | `TensorSlot` | Numeric index into `RawEvalPlan.tensorSigs` and the worker tensor store. |
| C2 | Policy enums | `NumericMode`, `OutOfBoundsPolicy` | Close over numeric-ordering and read-boundary semantics; Wave C admits only `reference64` and `zeroPad`. |
| C2 | Scalar enums | `ScalarConst`, `ScalarBinOp` | Represent dtype-preserving constants and the finite operation tags workers interpret exhaustively. |
| C2 | Structure | `ContractionAlgebra` | Records factor and reduction operations with their identities; Wave C checks only real sum-product. |
| C2 | IR structure | `AffineMap` | Stores one integer coefficient row per source dimension plus a bias vector. |
| C2 | IR structure | `ReadPlan` | Identifies a source slot, its affine coordinate map and shape, and its bounds policy. |
| C2 | IR structure | `TermPlan` | Defines one term's ordered iteration shape, output positions, reduction positions, and factors. |
| C2 | IR structure | `AssignPlan` | Defines one destination slot, output shape, ordered terms, and contraction algebra. |
| C2 | Raw IR | `RawEvalPlan` | Freely constructible or decoded plan payload: version, positional signatures, input slots, assignment steps, and numeric mode. It is never executable. |
| C2 | Checked IR | `CheckedEvalPlan` | Private wrapper constructible only after every structural and semantic invariant has passed validation. It is the sole worker input. |
| C2 | Error enum | `PlanError` | Closed explanation of why a `RawEvalPlan` is not executable: bad slots, ranks, maps, order classifications, algebras, or production dependencies. |
| C2 | Function | `checkPlan` | Translation validator from `RawEvalPlan` to `Except PlanError CheckedEvalPlan`. |
| C2 | Digest type/function | `PlanFingerprint`, canonical semantic encoder | Produces deterministic name-free bytes and their opaque digest for a checked plan. C5 later freezes the external wire codec. |
| C3 | Boundary structures | `SlotBinding`, `PlanBindings` | Map required and materialized source names to slots for packing and unpacking; they do not affect the semantic fingerprint. |
| C3 | Boundary structure | `PreparedPlan` | Packages `CheckedEvalPlan`, `PlanBindings`, preparation warnings, and the derived fingerprint. |
| C3 | Error enums | `CapabilityError`, `PlanCompileCause` | Distinguish valid-but-unsupported source constructs from signature, shape, and invalid-plan failures. |
| C3 | Failure structure | `PlanCompileFailure` | Couples a closed preparation cause with every warning accumulated after preflight. |
| C3 | Function | `prepareEvalPlan` | Specializes `(ScheduledProgram, InputSignature)` into a checked, positional `PreparedPlan`. |
| C4 | Error enum | `InputBindingError` | Reports missing runtime inputs or runtime tensors that disagree with their prepared shape/dtype. |
| C4 | Failure structure | `PlanRunFailure` | Couples an `InputBindingError` with the preparation warnings that must survive a runtime packing failure. |
| C4 | Adapter functions | `pack`, `unpack`, `runPreparedDense` | Convert named tensors to slots once, invoke the worker, reconstruct the source-visible environment, and preserve warnings/errors. |
| C4 | Worker function | `runDensePlan` | Interprets every admitted `CheckedEvalPlan` constructor over indexed `DenseTensor` storage without names or UIDs. |
| C5 | Error enum | `PlanCodecError` | Reports malformed canonical bytes, unsupported wire versions, and invalid decoded raw plans. |
| C5 | Codec functions | `encodePlan`, `decodePlan` | Encode checked semantic data canonically; decode only to `RawEvalPlan`, call `checkPlan`, and recompute fingerprints. |
| C6 | Evidence | mutation and differential corpus | Demonstrates checker coverage, codec robustness, alpha-renaming stability, and `=obs` agreement with `evalScheduled`. |
| C6 | Contract | capability/version handoff | Records the exact completed fragment and named extension points for later scatter, nonlinearity, scan, PyTorch, and JAX work. |

Only `AffineMap`, `ReadPlan`, `TermPlan`, `AssignPlan`, `RawEvalPlan`, and
`CheckedEvalPlan` are the Wave C semantic IR. Signatures are specialization inputs;
`PlanBindings`, warnings, fingerprints, and `PreparedPlan` are boundary or derived data. This
distinction prevents source names and diagnostics from leaking into kernel identity.

The future `ScanPlan`, `StateSlot`, `CheckedPlanBlock`, `IterationOrder`, `StateWriteMap`,
`ScanBoundaryPolicy`, and `CausalityCertificate` are intentionally absent from this Wave C
inventory. Section 12 defines their later contract, but C6 must not add placeholder constructors
without real producers and consumers.

### 15.2 Phase sequence

#### Phase C0: freeze the minimal contract

Write tests and type sketches that fix:

- accepted and rejected capability tables;
- source-visible environment observations;
- `reference64` ordering and equality;
- preparation warnings;
- deterministic tensor-slot and axis-basis ordering;
- raw/checked construction boundary;
- name-free fingerprint rule.

**Gate:** every accepted/rejected category has a typed expected result; no backend code is required.

#### Phase C1: introduce signatures and shape-only preparation

Add `ScalarDType`, `TensorSignature`, `InputSignature`, `InputSignatureError`,
`ShapeInferenceFailure`, and a shape-driven entry to size inference. Derive signatures from current
Dense inputs for the legacy boundary.

Do not genericize all tensors or evaluator workers.

**Gate:** signature-based inference returns the same sizes, warnings, and failures as Dense-input
inference over the full existing shape test corpus.

#### Phase C2: define raw/checked plan data

Add:

- minimal positional tensor signatures and slots;
- affine read maps;
- per-term reduction positions;
- closed real sum-product algebra;
- raw plan;
- privately constructible checked plan;
- canonical semantic encoder and fingerprint function;
- `PlanError` and `checkPlan`.

Implement `checkPlan` before the worker.

**Gate:** malformed-plan tests cover every checker invariant, and no worker API accepts `RawEvalPlan`.

#### Phase C3: compile supported schedules

Implement:

```text
prepareEvalPlan :
  ScheduledProgram -> InputSignature ->
  Except PlanCompileFailure PreparedPlan
```

Reuse the existing deterministic scheduling and affine normalization primitives. Preserve source
term/factor order. Compile per-term reduction positions by resolving
[`termAxisUIDs`](../leanncd/LeanNCD/Eval/Contract.lean) - the existing collector of every UID
syntactically mentioned by one product term - into basis positions, not by inspecting affine-map
columns for nonzero coefficients.
Build the `PreparedPlan` fingerprint with C2's canonical semantic encoder.

Add `SlotBinding`, `PlanBindings`, `PreparedPlan`, `CapabilityError`, `PlanCompileCause`, and
`PlanCompileFailure`. Reject every unsupported `ScanStmt`/`Stmt`/factor/nonlinearity/dtype with a
closed capability error.

**Gate:** all generated supported cases prepare successfully; every unsupported category fails
before worker execution; no UID or source name remains in the checked semantic kernel.

#### Phase C4: implement the Dense plan worker

Implement a simple worker over:

- indexed tensor slots;
- array coordinates;
- affine matrix/vector evaluation;
- explicit per-dimension bounds masks;
- explicit contraction identities and ordered folds.

Add `InputBindingError`, `PlanRunFailure`, and the `pack`, `unpack`, `runDensePlan`, and
`runPreparedDense` boundaries listed in Section 15.1.

Prefer clarity over vectorization. Do not reuse the legacy `gather` or its UID-map protocol.

**Gate:** bit-exact differential agreement with `evalScheduled` for every accepted generated and
handwritten case, including warnings and all materialized names after unpacking.

#### Phase C5: canonical codec and fingerprint

Add `PlanCodecError`, `encodePlan`, and `decodePlan`. Complete the external codec around C2's
canonical semantic encoder: decode through `RawEvalPlan`, validate on decode, and verify that
persisted fingerprints are recomputed from the checked semantic encoding rather than trusted from
input.

**Gate:**

- encode/decode/check/run preserves results;
- fingerprints survive round-trip;
- alpha-renaming changes bindings but not fingerprint;
- shapes, affine maps, operations, policies, or order change the fingerprint;
- warnings and diagnostic names do not change it.

#### Phase C6: adversarial audit and handoff

Run mutation tests, malformed codec tests, and the bounded exhaustive corpus. Document the exact
capability version and the extension points required by Wave D/F/G work.

Do not add a placeholder `ScanPlan`; record its required semantics in this proposal and introduce it
when typed recurrence and the decomposed scan transition provide real producers/consumers.

**Gate:** the Wave C claim is true. For every `sched : ScheduledProgram` and
`sig : InputSignature` in the declared scan-free `reference64` fragment, preparation has exactly one
of these outcomes:

```text
prepareEvalPlan(sched, sig) = ok prepared

and, for every namedInputs conforming to sig:

runPreparedDense(prepared, namedInputs)
  =obs evalScheduled(sched, namedInputs)

or prepareEvalPlan(sched, sig) returns a typed PlanCompileFailure before
plan execution.
```

Because the fragment has only `NumericMode.reference64`, tensor equality within `=obs` is
bit-for-bit equality.

## 16. Final recommendation

Proceed with Wave C as a compiler-and-reference-worker milestone, not as an early JAX demo and not
as a broad evaluator refactor.

The decisive architectural choices are:

1. `(ScheduledProgram, InputSignature)`, not `ScheduledProgram` alone, is the preparation input.
2. `CheckedEvalPlan` is closed, concrete-shape, first-order, positional, canonical, and backend
   neutral.
3. `PlanBindings` and warnings are sidecars; source names and warning text do not define kernel
   identity.
4. UIDs are resolved during plan compilation; names are resolved during runtime packing; neither
   appears in worker inner loops.
5. The current scheduled evaluator remains an independent oracle.
6. The first fragment is scan-free real sum-product with genuine affine reads and per-term
   contractions, not a trivial elementwise toy.
7. Unsupported valid language constructs fail with typed capability errors.
8. Raw decoded data is never executable until checked.
9. Gill-Hutton worker/wrapper guides pack/run/unpack and eventual scan carry design, while
   residualization and differential validation justify plan compilation.
10. Scans are delayed only until their state, transition, geometry, boundary, order, and causality
    become explicit `ScanPlan` data; they remain mandatory in the terminal architecture.

This sequence creates the smallest boundary that is simultaneously useful to DenseTensor, PyTorch,
and JAX. It removes the runtime dictionary protocol without weakening source semantics, gives later
backends one auditable contract, and leaves scan optimization until there is a general scan
semantics against which specialized implementations can be judged.

## Appendix A. Detailed Wave C implementation plan

This appendix turns Sections 3-15 into an implementation sequence against the current Lean tree. It
is intentionally specific about module boundaries, API signatures, test ownership, and stop
conditions. Exact constructor spelling may change during implementation, but changing a semantic
field, phase owner, or gate requires updating this document first.

### A.1 Definition of done

Wave C is complete only when all of the following hold:

1. `prepareEvalPlan` accepts exactly the declared scan-free `f64` fragment and rejects every other
   valid scheduled construct with a typed `CapabilityError` before shape inference.
2. Every accepted schedule produces a privately constructed `CheckedEvalPlan` containing no source
   tensor names, axis UIDs, functions, callbacks, or backend objects.
3. `runPreparedDense` agrees with `evalScheduled` under `=obs`, including the complete environment,
   warning order, typed failures, empty products/domains, zero extents, and bit-exact Float data.
4. Raw and decoded plans cannot reach a worker without `checkPlan`.
5. Canonical bytes and fingerprints are deterministic, name-independent, versioned, and covered by
   round-trip and mutation tests.
6. The legacy `evalScheduled`/`Gather`/`Contract` path remains independent; the plan worker does not
   call it or reuse its UID-map inner loop.
7. The full default Lean build passes with no skipped test module:

   ```bash
   cd leanncd && "$HOME/.elan/bin/lake" build
   ```

### A.2 Production module layout and dependency direction

Create a narrow `LeanNCD/Eval/Plan/` subtree:

| Module | Owns | May import |
|---|---|---|
| `Types.lean` | signatures, slots, closed scalar/policy tags, and freely constructible raw semantic IR | `Std` |
| `Error.lean` | signature, capability, checker, binding, and codec error enums plus preparation causes | `Plan.Types`, existing `Eval.Error` |
| `Check.lean` | `RawEvalPlan.Valid`, `checkPlan`, private `CheckedEvalPlan` constructor/accessors | `Plan.Error` |
| `Canonical.lean` | canonical semantic encoder and SHA-256 fingerprint construction | `Plan.Check` |
| `Prepared.lean` | bindings, `PreparedPlan`, `PlanCompileFailure`, `PlanRunFailure`, and other warning-preserving boundary outcomes | `Plan.Check`, `Plan.Error`, `Plan.Canonical`, existing `Eval.Error` |
| `Signature.lean` | Dense-to-signature projection and shape-only preparation adapter | `Plan.Error`, `Eval.Tensor`, `Eval.SizeInfer` |
| `Compile.lean` | preflight, deterministic slot/basis allocation, affine lowering, `prepareEvalPlan` | `Plan.Prepared`, `Plan.Signature`, `Eval.Contract`, DSL pipeline artifacts |
| `Dense.lean` | `pack`, positional Dense interpreter, `unpack`, `runPreparedDense` | `Plan.Prepared`, `Eval.Tensor`, neutral `Eval.Report` |
| `Codec.lean` | external wire envelope, decode-to-raw, validation, persisted-fingerprint checks | `Plan.Canonical`, `Plan.Check`, `Plan.Error` |
| `Plan.lean` | public umbrella only | the stable modules above |

Keep the dependency graph acyclic:

```text
Types -> Error -> Check
  |        |       |
  |        |       +-> Canonical -> Prepared -> Compile
  |        +----------> Signature ----^          |
  +----------------------------------------------> Dense
                         Canonical --------------> Codec
```

`Eval.SizeInfer` must not import the plan compiler. Its reusable core accepts the explicit UID-size
seed plus name-to-shape metadata; `Plan.Signature` converts `InputSignature` to that metadata, and
`prepareEvalPlan` passes `ScheduledProgram.explicitSizes` unchanged as the seed. Move the existing
`EvalReport` record, unchanged, from `Eval/Eval.lean` to a new neutral `Eval/Report.lean` leaf
imported by both evaluators. This prevents `Dense.lean` from importing `Eval.Eval` and transitively
regaining the legacy `Gather`/`Contract` worker. `Dense.lean` must not import `Compile.lean`: a
worker consumes checked data and remains independent of source lowering. After C4 stabilizes the
public API, add `LeanNCD.Eval.Plan` to the root `LeanNCD.lean` imports.

Keep plan-specific diagnostics in `Plan/Error.lean`, despite the older evaluator's centralized
`Eval/Error.lean`. Importing plan types into that established leaf would reverse its dependency
direction. Update `Eval/AGENTS.md` to document the two non-overlapping owners: legacy evaluator
diagnostics in `Eval/Error.lean`, plan-boundary diagnostics in `Eval/Plan/Error.lean`.

Do not reuse `LeanNCD.Base.DType`: it belongs to the symbolic math tower, carries `SizeExpr`, and
does not represent concrete backend scalar storage. `ScalarDType` is executable-plan vocabulary.

### A.3 Test module layout

Add these modules to the existing explicit `Tests.globs` list in `leanncd/lakefile.toml`:

```text
Eval.Plan.SignatureTest
Eval.Plan.TypesTest
Eval.Plan.CheckTest
Eval.Plan.CanonicalTest
Eval.Plan.CompileTest
Eval.Plan.DenseTest
Eval.Plan.CodecTest
Eval.Plan.DifferentialTest
```

Use current `#guard`/`run_cmd` conventions; do not introduce a new test runner. Extend
`test/Eval/PropertyOracle/Gen.lean` only for missing semantic coverage, and keep plan-specific
comparison logic in `DifferentialTest` so the existing transformation oracle remains independent.

Every phase first runs its targeted modules, then the full default build. A phase is not complete
when only a scratch file or non-default target passes.

### A.4 C0 - freeze executable contracts

**Production changes:** none.

**Tasks:**

1. Write one capability table whose rows cover every `ScanStmt`, `Stmt`, `LHSSlot`, `Factor`,
   `Nonlin`, `AggOp`, declaration dtype, and numeric mode constructor.
2. Fix deterministic rejection order: schedule capability, input-signature structure, shape
   inference, raw-plan construction, then `checkPlan`.
3. Fix canonical ordering and name rebinding:
   - external slots follow declaration order filtered to actually required external names;
   - destination slots follow scheduled statement order;
   - reads resolve against the most-recent preceding slot for their tensor name;
   - assigning a name again allocates a new destination slot, updates the compiler name environment,
     and makes the final binding point to the last write, matching `evalScheduled`;
   - term and factor arrays preserve source order;
   - each term basis is retained LHS UIDs in slot order followed by that term's first-occurrence
     contracted UIDs;
   - output positions are the basis prefix and reduction positions its suffix.
4. Decide empty semantics explicitly: empty factor products use `factorId`; empty term arrays and
   reductions containing a zero-extent axis use `reduceId`; a term with no reduction axes evaluates
   exactly once because the cartesian product of no ranges is `[[]]`; zero output extents produce
   empty data.
5. Record hand-written cases absent from the generator: negative shifts, multi-axis affine rows,
   zero coefficients that still mention a contracted UID, empty products, empty reductions, zero
   dimensions, unused extra inputs, and per-term contraction asymmetry.

**Gate:** every source constructor has exactly one accepted or typed-rejected classification and
every ordering rule needed by encoding or Float evaluation is written without reference to map
iteration order.

### A.5 C1 - signatures and shape-only inference

**Production files:** `Plan/Types.lean`, `Plan/Error.lean`, `Plan/Signature.lean`,
`Eval/Error.lean`, and `Eval/SizeInfer.lean`.

**Tasks:**

1. Define `ScalarDType`, `TensorSignature`, `InputSignature`, `InputSignatureError`, and
   `ShapeInferenceFailure`.
2. Extract the body of `inferAxisSizes` into a shape-driven core that accepts the existing
   `HashMap UID Nat` explicit-size seed and whose only tensor dependency is a lookup of `List Nat`
   by source name.
3. Preserve the old `inferAxisSizes` signature as a thin adapter from `DenseTensor.shape`.
4. Implement `inferAxisSizesFromSignature` by converting the signature's `Array Nat` shapes to the
   existing shape representation.
5. Derive a Dense input signature with dtype `f64`; validate `DenseTensor.data.size =
   DenseTensor.sizeOf shape` at the runtime boundary rather than assuming the unchecked invariant.
6. Preserve warnings inside `ShapeInferenceFailure`; map that failure to existing `EvalFailure` in
   the legacy path and later to `PlanCompileFailure.shape` in the plan path.

**Tests:**

- shape/signature conversion and malformed-signature constructors;
- parity of sizes, warning order, and `ShapeError` over every existing shape test;
- parity over every `PropertyOracle.enumPrograms` input after compiling each source program to its
  `ScheduledProgram` and passing that schedule's `explicitSizes`;
- an axis sized only by `ScheduledProgram.explicitSizes`;
- a pinned size conflicting with an input shape, preserving the same `ShapeError.sizeConflict`;
- warnings preserved when a later shape constraint fails.

**Gate:** `evalScheduled` is behaviorally unchanged, and signature-driven inference is exactly equal
to Dense-driven inference for the same shapes and explicit-size seed.

### A.6 C2 - semantic IR and checked construction

**Production files:** `Plan/Types.lean`, `Plan/Error.lean`, `Plan/Check.lean`, and
`Plan/Canonical.lean`.

**Tasks:**

1. Define the C2 artifacts listed in Section 15.1 with `DecidableEq`/`Repr` where their fields permit.
   `ScalarConst.f64` stores `Float.toBits : UInt64`, never `Float`, so NaNs and signed zero have
   exact equality and canonical bytes.
2. Keep `RawEvalPlan` freely constructible. Store the validated raw payload and its validity evidence
   behind a private `CheckedEvalPlan` constructor.
3. Make C2 canonical rather than merely valid:
   - `inputSlots` are unique and ordered;
   - every tensor slot is either an input or produced exactly once;
   - step reads refer only to inputs or earlier destinations;
   - `outputPos` is `[0, ..., outputRank-1]`;
   - `reductionPos` is the remaining ordered suffix;
   - those arrays partition every `iterationShape` position exactly once.
4. Validate every affine dimension: coefficient row count and bias length equal source rank; each row
   length equals term-basis rank; `ReadPlan.sourceShape` equals the source slot signature.
5. Validate output projection, destination shape, dtype-compatible constants, exact Wave C
   sum-product algebra, `zeroPad`, and `reference64`.
6. Allow the C0-approved empty arrays and zero extents; reject malformed representations, not valid
   identity cases.
7. Expose read-only checked accessors needed by workers and codecs, never the constructor.
8. Freeze the canonical semantic field order and implement the name-free encoder and SHA-256
   fingerprint needed by `PreparedPlan`. The SHA-256 dependency decision described in A.9 is a C2
   entry condition, not work that may wait until after C3.

**Tests:** construct one minimal valid raw plan, then mutate each field independently to hit every
`PlanError` constructor. Include forward reads, duplicate destinations, missing production,
rank/map mismatches, bad position partitions, wrong identities, unsupported tags, and malformed
empty cases.

**Gate:** `CheckTest` demonstrates every checker branch, and a worker signature cannot be written
against `RawEvalPlan` without an explicit unsafe escape hatch.

### A.7 C3 - scheduled-program specialization

**Production files:** `Plan/Prepared.lean` and `Plan/Compile.lean`.

**Tasks:**

1. Implement a total, source-order capability preflight. Return the first typed `CapabilityError`;
   do not run shape inference or emit warnings when preflight fails.
2. Validate required static signatures next. Distinguish missing names, invalid dimensions/dtypes,
   declaration incompatibility, and unexpected required-input ambiguity.
3. Run shape inference with `sched.explicitSizes` as the seed and preserve its warnings. This is
   required both for axes sized only by declarations and for pinned-size/input-shape conflict parity.
4. Allocate slots deterministically:
   - derive required external names from declaration order, filtered to names read before their first
     scheduled production, not `Finset` traversal;
   - assign external slots first;
   - walk assignments in schedule order with a current name-to-slot environment;
   - resolve every factor read before allocating that statement's destination;
   - allocate one fresh destination slot, then update the name environment, so later reads and final
     materialization observe the most recent write;
   - keep one `materializedNames` entry per name, ordered by first production but pointing to its
     final destination slot.
5. For each assignment, derive output UIDs from ordinary free LHS slots and concrete output extents
   from inferred sizes.
6. For each term, compute `termAxisUIDs term |>.eraseDups`, remove retained UIDs, and append the
   remaining UIDs to the retained basis. Never infer this set from nonzero affine columns.
7. Lower each `.read` index with `idxAffineForm` plus `idxDensify` over that term basis. Preserve one
   row per source dimension and reject rank mismatch before constructing raw IR.
8. Build `ReadPlan`, `TermPlan`, and `AssignPlan` arrays in source order; use exact binary64 bit
   patterns for zero and one.
9. Build `RawEvalPlan`, call `checkPlan`, compute bindings and warnings, derive the fingerprint from
   canonical semantic bytes, and return `PreparedPlan`.

**Tests:**

- one focused accepted case for every admitted capability;
- one typed rejection for every C0 rejected row;
- deterministic slot and term-basis golden assertions;
- alpha-renamed schedules produce equal raw semantic plans/fingerprints and different bindings;
- zero-coefficient contracted-axis regression;
- repeated assignment followed by a read observes the most recent preceding write;
- warnings survive a later `PlanError`.

**Gate:** all supported generated programs prepare; unsupported programs fail before a worker;
inspection of `CheckedEvalPlan` finds no `String` tensor names or `UID` axis identities.

### A.8 C4 - independent Dense worker and adapter

**Production files:** `Eval/Report.lean`, `Eval/Eval.lean`, and `Plan/Dense.lean`.

**API shape:**

```text
NamedDenseEnv    := HashMap String DenseTensor
pack             : PreparedPlan -> NamedDenseEnv -> Except InputBindingError (Array DenseTensor)
runDensePlan     : CheckedEvalPlan -> Array DenseTensor -> Array DenseTensor
unpack           : PlanBindings -> NamedDenseEnv -> Array DenseTensor -> NamedDenseEnv
runPreparedDense : PreparedPlan -> NamedDenseEnv -> Except PlanRunFailure EvalReport
```

`pack` orders tensors by `CheckedEvalPlan.inputSlots`, checks shape and storage-size invariants, and
does not discard unrelated original environment entries. `runDensePlan` creates its internal slot
store, executes steps in order, and returns the complete produced store. `unpack` starts from the
original environment and inserts every `materializedNames` binding.

**Worker algorithm:**

1. Enumerate output and reduction coordinates with `DenseTensor.allCoords`.
2. Evaluate `sourceCoordinate = coeffs * iterationCoordinate + bias` using `Int`.
3. Check every source dimension before flattening; any invalid dimension contributes padded zero.
4. Fold factors, reduction coordinates, terms, and statements in the exact orders fixed by C0.
5. Use only closed scalar tags and identities. Do not call `Gather.gather`, `evalAssign*`, or create
   `HashMap UID Int`.

**Tests:**

- direct worker unit cases for affine maps, padding, products, reductions, and chains;
- packing failures preserve `PreparedPlan.warnings` in `PlanRunFailure`;
- unpacking preserves unused inputs and materializes all scheduled intermediates;
- differential execution over every `PropertyOracle.enumPrograms` case;
- for each generator entry, call `p.compileToScheduled |>.run 0`, derive the `InputSignature` from
  the Dense inputs, and compare `runPreparedDense` with `evalScheduled` on that exact schedule;
- targeted C0 cases, comparing complete key sets and bit-equal tensors, not only final names;
- test-the-tester mutations: reorder a fold, drop a term, or alter a coefficient and require failure.

**Gate:** every accepted generated and hand-written case satisfies Law 1 bit-for-bit, and the new
worker has no dependency on legacy contraction/gather execution.

### A.9 C5 - canonical codec and fingerprint

**Production file:** `Plan/Codec.lean`.

**Encoding contract, frozen initially by `Plan/Canonical.lean` in C2 and consumed by the external
codec in C5:**

- fixed magic bytes and independent wire/semantic versions;
- fixed constructor tags;
- length-prefixed arrays;
- unsigned canonical encoding for `Nat`, signed canonical encoding for `Int`;
- explicit big-endian binary64 bit patterns;
- no `HashMap` iteration, names, warnings, bindings, or backend metadata;
- reject non-minimal integer encodings and trailing bytes.

Hash the canonical semantic bytes with SHA-256. Domain-separate the hash with a fixed plan marker and
semantic-version prefix inside the hashed bytes; `PlanFingerprint` remains the opaque 32-byte digest.
Do not use Lean's host `Hashable`: its output is not the cross-version wire contract. The repository
currently has no established SHA-256 utility, so C2 begins with an explicit dependency decision:
either approve one small audited Lean dependency or add a local pure implementation verified against
published SHA-256 test vectors. Do not silently substitute an unstable or weaker hash. C5 reuses
this implementation; it does not select a second algorithm.

`decodePlan` must parse to `RawEvalPlan`, reject malformed bytes with a path/offset-bearing
`PlanCodecError`, invoke `checkPlan`, and recompute rather than trust a persisted fingerprint.

**Tests:** golden bytes for a minimal plan, every admitted constructor round trips, reserved known
tags decode to raw data and are rejected by `checkPlan`, unknown tags fail decoding,
truncation/trailing-byte and non-canonical integer failures, SHA-256 standard vectors, semantic
mutation changes, alpha-renaming stability, and decode/check/run agreement.

**Gate:** canonical bytes are pinned, round trips preserve checked semantics, and no malformed or
unchecked payload is executable.

### A.10 C6 - adversarial audit and handoff

1. Run the full malformed-plan mutation matrix and ensure every mutation is rejected or changes
   semantics/fingerprint as specified.
2. Extend the bounded corpus only where coverage guards prove a missing dimension; keep it below its
   explicit size cap.
3. Audit imports to confirm:
   - `Dense.lean` does not import `Compile.lean`;
   - plan execution does not import legacy `Gather`/`Contract` workers;
   - `SizeInfer.lean` does not import plan modules;
   - codecs expose no unchecked constructor.
4. Search semantic IR definitions for `String`, `UID`, function fields, backend types, and unordered
   maps. Any occurrence requires removal or a documented nonsemantic sidecar.
5. Update `Eval/AGENTS.md`, root architecture documentation, and `LeanNCD.lean` public imports.
6. Run the complete build from `leanncd/` through Elan and report any skipped module as a failure.

**Gate:** the Section 15 C6 claim holds for the complete declared corpus, the module graph matches
Section A.2, and later Wave F/G work can depend only on checked plan APIs.

### A.11 Dependency and landing sequence

Land the work in reviewable vertical commits:

```text
C0 contract/tests
  -> C1 shape metadata extraction
  -> C2 raw types + checker + canonical fingerprint
  -> C3 compiler + preparation
  -> C4 Dense worker + differential matrix
  -> C5 external wire codec
  -> C6 audit + documentation
```

Do not combine C2-C4 into one change: checker defects, compiler defects, and worker defects need
independent tests. Do not begin Wave F scan decomposition or Wave G backend work until C4's
differential gate passes. C5 may be developed after C2 in parallel only after canonical field order
is frozen; it must merge after C3/C4 tests establish that the encoded fields are semantically
complete.

### A.12 Implementation-time stop conditions

Stop and revise the proposal rather than improvising if any of these occur:

- an accepted program needs source names or UIDs during worker execution;
- the compiler cannot determine a concrete shape from `InputSignature`;
- two backends would assign different meanings to one closed tag;
- the checker cannot state a worker precondition without executing tensor arithmetic;
- canonical encoding requires a precedence rule between redundant fields;
- exact Dense agreement requires changing `evalScheduled`;
- a scan, scatter, predicate, unary factor, or nonlinearity appears necessary merely to make the
  initial plan architecture usable.

Those are architecture failures or scope changes, not reasons to add a fallback, optional field, or
silent default.

## 17. References

### Repository

- [LeanNCD restructuring roadmap](restructure_suggestions.md)
- [Backend analysis and proposed differential matrix](copilot_code_analysis.md)
- [Scheduled pipeline types](../leanncd/LeanNCD/DSL/Pipeline/Types.lean)
- [AST and shared affine normalization](../leanncd/LeanNCD/DSL/Ast.lean)
- [Lowering and affine reindexing artifacts](../leanncd/LeanNCD/DSL/Pipeline/Lowering.lean)
- [Reference scheduled evaluator](../leanncd/LeanNCD/Eval/Eval.lean)
- [Reference contraction semantics](../leanncd/LeanNCD/Eval/Contract.lean)
- [Reference gather and padding semantics](../leanncd/LeanNCD/Eval/Gather.lean)
- [Shape inference](../leanncd/LeanNCD/Eval/SizeInfer.lean)
- [Current scan semantics](../leanncd/LeanNCD/Eval/Scan.lean)
- [Scan-free property generator](../leanncd/test/Eval/PropertyOracle/Gen.lean)
- [Independent scan-unrolling oracle](../leanncd/test/Eval/PropertyOracle/ScanUnroll.lean)

### External

- Andrew Gill and Graham Hutton,
  [The Worker/Wrapper Transformation](https://people.cs.nott.ac.uk/pszgmh/wrapper.pdf), JFP 2009.
- Neil D. Jones, Carsten K. Gomard, and Peter Sestoft,
  [Partial Evaluation and Automatic Program Generation](https://www.cambridge.org/core/books/partial-evaluation-and-automatic-program-generation/500C671429CC993BE6A5E30C261B943F).
- [MLIR Linalg dialect](https://mlir.llvm.org/docs/Dialects/Linalg/).
- John C. Reynolds,
  [Definitional Interpreters for Higher-Order Programming Languages](https://dl.acm.org/doi/10.1145/800194.805852),
  1972.
- Matt Noonan, [Ghosts of Departed Proofs](https://arxiv.org/abs/1808.00351), 2018.
- Amir Pnueli, Michael Siegel, and Eli Singerman,
  [Translation Validation](https://doi.org/10.1007/BFb0054170), TACAS 1998.
- John C. Mitchell,
  [Representation Independence and Data Abstraction](https://doi.org/10.1145/512644.512669),
  POPL 1986.
- [Haskell `mapAccumL`](https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Data-List.html#v:mapAccumL).
- [JAX `lax.scan`](https://docs.jax.dev/en/latest/_autosummary/jax.lax.scan.html).
- Guy E. Blelloch,
  [Prefix Sums and Their Applications](https://www.cs.cmu.edu/~guyb/papers/Ble93.pdf).
