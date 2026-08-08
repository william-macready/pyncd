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

The split gives a clear trust boundary:

- plan compilers, codecs, tests, and external tools may construct `RawEvalPlan`;
- `checkPlan` validates that raw data and reports a typed `PlanError` on failure;
- only successful validation can construct `CheckedEvalPlan`; and
- Dense, PyTorch, and JAX workers accept only `CheckedEvalPlan`.

`CheckedEvalPlan` is not a second serialized IR. It is validation evidence over the same semantic
data.

A plan is **backend-neutral** when every constructor has one mathematical meaning shared by all
workers; **canonical** when it has one deterministic semantic encoding; and **checked** when its
structural and semantic preconditions have been validated before execution. A **worker** is an
interpreter or lowerer that executes a `CheckedEvalPlan` over one tensor representation.

`TLProgram` is the existing source-language program representation. `ScheduledProgram` is the
source-independent, topologically ordered output of compiling a `TLProgram`. `TensorSignature` is a
concrete tensor shape and scalar dtype without element values, and `InputSignature` maps required
source input names to those signatures.

The central recommendation is to treat `CheckedEvalPlan` as a **residual program** (the program left
after specializing a more general program or interpreter with respect to information already
known). Plan compilation specializes the scheduled evaluator with the static
`(ScheduledProgram, InputSignature)` pair, leaving a `CheckedEvalPlan` that still accepts dynamic
tensor element values at runtime. Names, UIDs, shape inference, affine expressions, and semantic
choices are compiled out of the runtime worker; the resulting first-order positional program is
validated once, only checked plans are executed, and the existing scheduled evaluator remains an
independent oracle.

This is more precise than describing the whole change as "worker/wrapper." Gill and Hutton's
worker/wrapper theory is valuable at representation boundaries, especially runtime packing and
eventual scan carry conversion. It does not by itself justify the compiler pass from
`(ScheduledProgram, InputSignature)` to `CheckedEvalPlan`.

## Table of contents

**Problem and boundary**

- [Executive summary](#1-executive-summary)
- [Current architecture and semantic obligations](#2-current-architecture-and-semantic-obligations)
- [Initial Wave C scope and capability boundary](#3-initial-wave-c-scope-and-capability-boundary)
- [Pipeline phases and conceptual workstreams](#4-pipeline-phases-and-conceptual-workstreams)

**One checked-plan architecture**

- [Checked plan language and invariants](#5-checked-plan-language-and-invariants)
- [Boundary layer: shape specialization](#6-boundary-layer-shape-specialization)
- [Graph layer: slots, UIDs, and affine wiring](#7-graph-layer-slots-uids-and-affine-wiring)
- [Kernel layer: local tensor semantics](#8-kernel-layer-local-tensor-semantics)

**Interpretation, representation, and evidence**

- [Representation layer: canonical data and transformations](#9-representation-layer-canonical-data-and-transformations)
- [Interpretations and commuting correctness laws](#10-interpretations-and-commuting-correctness-laws)
- [Design justification and external influences](#11-design-justification-and-external-influences)
- [Guarded stateful extension: scans](#12-guarded-stateful-extension-scans)
- [Evidence organized by laws](#13-evidence-organized-by-laws)
- [Scope discipline and deferred machinery](#14-scope-discipline-and-deferred-machinery)

**Delivery**

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
- `PreparedPlan` packages a `CheckedEvalPlan`, its `PlanBindings`, and preparation warnings.
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
  `- warnings              diagnostics produced during preparation
       |
       |- DenseTensor plan worker       Wave C
       |- PyTorch lowering/worker       later
       `- JAX lowering/worker           later

CheckedEvalPlan
  `- canonical encoding -> PlanFingerprint   downstream representation
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

Each category needs a closed constructor with the relevant source context. Concretely, one
constructor per rejected category above, in the same `String`-context convention as the existing
[`CompileError`](../leanncd/LeanNCD/Exec/Uid.lean):

```lean
inductive CapabilityError
  | scanNode             (context : String)  -- ScanStmt.scan / .scanPre
  | scatterOrAffineLhs   (context : String)  -- scatter statements, affine LHS slots
  | unsupportedLhsSlot   (context : String)  -- freeNorm, iterAt, iterNext
  | unsupportedNonlin    (context : String)  -- pointwise/axiswise nonlinearities
  | maskOrPredicate      (context : String)  -- masks, predicates, Iverson factors
  | unaryFactor          (context : String)
  | unsupportedAgg       (context : String)  -- max/min aggregation
  | booleanOutput        (context : String)
  | unsupportedDtype     (context : String)  -- any dtype other than the declared f64 mode
  | dynamicShape         (context : String)  -- backend- or value-dependent shapes
  | recurrenceOrCallback (context : String)
```

This closes the obvious escape hatch: nothing above should permit an `unsupported : String`
catch-all constructor, which would silently reopen the stringly-typed error surface Wave E removed.
A supported program that fails to compile is a bug. An unsupported program that reaches the worker
is also a bug.

### 3.3 Rejection is staging, not terminal semantics

Typed rejection means "this plan version/capability set does not yet represent the construct." It
must not be confused with declaring that the language construct has no backend meaning. Later waves
must add plan constructors for nonlinearities, scatter, predicates, and scans because those payloads
are part of LeanNCD semantics.

## 4. Pipeline phases and conceptual workstreams

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

### 4.5 Five workstreams within the phases

The four phases describe **when information is available**. A second, orthogonal decomposition
describes **which semantic concern owns it**:

| Workstream | Owns | Categorical reading | Practical payoff |
|---|---|---|---|
| Local tensor kernel | affine reads, term-local iteration, products, reductions, numeric order | pullback of reads, pointwise product, pushforward over reduction fibres | local semantics can be checked and tested without names or scheduling |
| Typed plan graph | tensor slots, production order, reuse, destinations, checked composition | typed acyclic open hypergraph | wiring bugs are separated from contraction bugs |
| Source-facing boundary | signatures, names, bindings, warnings, packing/unpacking | representation change with a valid-input retraction | source compatibility stays outside kernel identity |
| Backend interpretation | Dense, later PyTorch/JAX meanings of checked constructors | semantics-preserving interpretations of one plan language | new backends cannot redefine plan mathematics |
| Canonical representation | encoding, fingerprints, later relational views and rewrites | chosen presentation of a checked morphism | persistence and optimization remain downstream of semantics |

These workstreams are not new runtime abstractions. Section 15 and Appendix A turn them into
inside-out vertical slices: first validate and interpret one local operation, then compose checked
operations into a graph, then attach the source-facing compiler and adapter, and only afterward
freeze canonical representation. Local tensor meaning, graph composition, boundary adaptation,
backend interpretation, and representation should not be debugged as one undifferentiated compiler
pass.

## 5. Checked plan language and invariants

The exact Lean syntax should be finalized while implementing the first real consumer. The following
types define the required separation, not a demand to create every record before it is used.

Sections 5-8 describe one checked-plan architecture from four views. This section defines the shared
language and its raw/checked boundary; Section 6 specializes source-facing metadata; Section 7
builds the typed graph and affine wiring; Section 8 gives the local tensor kernel its mathematical
meaning. None is a competing IR.

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
  | add | mul

structure ContractionAlgebra where
  factorOp : ScalarBinOp
  factorId : ScalarConst
  reduceOp : ScalarBinOp
  reduceId : ScalarConst
```

`ScalarDType` is the closed scalar-type vocabulary. `TensorSlot` is an index into the plan's
`tensorSigs` array and the worker's parallel tensor store. `NumericMode` selects cross-backend
numeric conventions; Wave C has only `reference64`, defined precisely in Section 8.4.
`OutOfBoundsPolicy` is the read policy; Wave C has only `zeroPad`. `ScalarConst` stores a scalar
literal in a dtype-preserving canonical form. `ScalarBinOp` is the closed set of binary scalar
operations, and `ContractionAlgebra` records the operation and identity used within factor products
and across reductions/terms.

`ScalarBinOp` holds exactly the operations Wave C's checker and worker implement — `min`, `max`
(needed for max/min aggregation), and `logicalAnd`/`logicalOr` (needed for predicate/Boolean
outputs) are deliberately absent, not merely unreachable: both source capabilities are rejected by
`CapabilityError` before a plan is built (Section 3.2), so today no producer could ever construct
them and no worker implements their semantics. Adding a constructor to this closed enum is itself a
semantic-version change (Section 9.2), so each later capability wave adds its own tag deliberately,
rather than pre-declaring tags a checker must defensively reject with no compile-time-checked
reason to.

`InputSignature` is named because it is consumed at a source-facing boundary. The checked semantic
plan is positional and need not retain these names.

Initially plan compilation admits only `ScalarDType.f64`; `f32` and `bool` are reserved closed tags
for later plan capabilities. A valid but unsupported dtype is a capability error, not a
malformed-plan error.

### 5.2 Raw and checked plans

Deserialization and construction should not make an arbitrary value executable:

Validation occurs at two compositional boundaries. `checkAssign` validates one operation node against
the positional tensor-signature table; `checkPlan` validates the open graph, including node-local
validity and production order. `PlanError` is their shared closed family of violations, detailed in
Section 5.5.

```text
AssignPlan  --checkAssign(tensorSigs)--> Except PlanError CheckedAssignPlan
RawEvalPlan --checkPlan----------------> Except PlanError CheckedEvalPlan
```

`CheckedAssignPlan` is a private wrapper establishing the local pullback-product-pushforward
preconditions of one operation. `RawEvalPlan` is the public graph record accepted from the compiler
or codec. `CheckedEvalPlan` privately contains the validated graph and its checked operations.
`runDenseAssign` accepts only `CheckedAssignPlan`; whole-plan workers accept only
`CheckedEvalPlan`. Trusted accessors may expose validated payloads without exposing either
constructor. The local wrapper is checker evidence, not an additional serialized IR.

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

structure CheckedAssignPlan where private mk ::
  raw : AssignPlan

structure CheckedEvalPlan where private mk ::
  raw : RawEvalPlan
```

The `private mk ::` constructor name is not decorative: Lean only rejects external `⟨...⟩`
construction when the constructor is explicitly named and marked private this way. A bare
`structure Foo where private` (no named constructor) compiles but leaves the anonymous constructor
public — verified against this toolchain by a two-module test where that form let an external file
construct a value with no error. Since Law 2 and the entire raw/checked boundary in Section 5.2
depend on `CheckedAssignPlan`/`CheckedEvalPlan` being unconstructible outside `Check.lean`, C2/C3
must include a compile-time negative test (an external module attempting `⟨...⟩` on either type
fails to elaborate), not merely that `checkAssign`/`checkPlan` return `Except`.

The exact storage of checked operations inside `CheckedEvalPlan` is an implementation choice; the
important contract is that `checkPlan` reuses `checkAssign` rather than reimplementing local
validation. This sketch leaves room to factor common iteration domains or maps if actual duplication
appears. Wave C should not create a general graph-IR framework, optional-field mega-record, or
backend class hierarchy before a second use justifies it.

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
  plan     : CheckedEvalPlan
  bindings : PlanBindings
  warnings : List EvalWarning
```

`materializedNames` is exactly every name produced by a `sched.stmts` entry — this is not an
approximation to pin down later: `evalScheduled` ([`Eval.lean`](../leanncd/LeanNCD/Eval/Eval.lean))
starts `env` at `inputs` and, with no filtering, inserts every `.plain`/`.scan` statement's produced
name(s) in schedule order, so `EvalReport.env` is already exactly `inputs ∪ {every scheduled
statement's output}`. `materializedNames` must reproduce that same set from `RawEvalPlan.steps`
(each `AssignPlan.destinationSlot`) with no separate notion of "exposed" to define. The runtime
wrapper starts from the original input environment and inserts these materialized results; that
preserves extra input entries that are not semantically consumed by the plan.

`requiredInputs` is a slot map, not an implicit parallel-array convention. `pack` walks
`CheckedEvalPlan.inputSlots` and requires exactly one matching `requiredInputs` entry for each slot;
missing, duplicate, or extra required-input bindings are typed `InputBindingError` values. It emits
the resulting tensor array in `inputSlots` order. This prevents two equal-shaped inputs from being
silently swapped merely because a binding array was reordered.

The semantic plan and its fingerprint do not need source names. `PlanBindings` can be replaced for
an alpha-renamed source program - one whose tensor names are changed consistently without changing
dependencies or source order - without changing the indexed computation. `fingerprintPlan` is a
downstream canonical-representation function on `CheckedEvalPlan`, not a field required to execute
`PreparedPlan`. A codec recomputes rather than trusts any persisted digest.

### 5.5 Error families

Wave C introduces error producers that did not exist in Wave E, so it is now appropriate to define
new closed families:

- `InputSignatureError`: a required signature is missing, malformed, or incompatible with the
  scheduled declarations;
- `InputBindingError`: a runtime named input is missing or differs from its prepared shape/dtype;
- `PositionalInputError`: a Dense worker input slot is absent or its runtime shape/storage differs
  from the signature against which its checked operation was validated;
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
APIs rather than `prepareEvalPlan`; `pack` reports `InputBindingError`; `runDenseAssign` and
`runDensePlan` report `PositionalInputError` rather than using unchecked array access. The runtime
counterpart nests either cause with the preparation warnings already carried by `PreparedPlan`:

```lean
inductive PlanRunCause
  | binding   (cause : InputBindingError)
  | execution (cause : PositionalInputError)

structure PlanRunFailure where
  cause    : PlanRunCause
  warnings : List EvalWarning
```

`PlanRunFailure` is the failure type of `runPreparedDense` (Section 4.3, Law 4). `BackendError`
belongs to later backend execution APIs.

## 6. Boundary layer: shape specialization

The boundary layer is where source-facing metadata becomes a concrete execution context. It owns
signatures, explicit-size seeds, warnings, and the later name/slot adapter, but it does not define
tensor arithmetic. Categorically, it is best understood as selecting a concrete fibre of plans
indexed by shape and dtype, not as applying a graph rewrite or searching for a plan.

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

## 7. Graph layer: slots, UIDs, and affine wiring

Ignoring scalar payloads momentarily, a checked plan is a typed acyclic open hypergraph: tensor slots
are wires, assignment steps are operation nodes, reads are incidences, and input/materialized slots
form the open boundary. Composition connects produced slots to later reads; reuse of a tensor is
explicit fan-out. The concrete arrays remain the implementation representation—Wave C does not need
a categorical graph library—but this viewpoint cleanly separates wiring validity from local
contraction semantics.

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

## 8. Kernel layer: local tensor semantics

For one term, let `O` be its finite output-coordinate set, `K_t` its finite contracted-coordinate
set, and `B_t = O x K_t` its iteration space. Each factor `f` has a partial affine read map
`a_f : B_t -> S_f` into its source-coordinate set `S_f`; out-of-bounds coordinates map to padded
zero. If `pi_t : B_t -> O` projects away contracted coordinates, the term has the schematic meaning:

```text
term_t(inputs) = (pi_t)_! (product_f (a_f)^* inputs[f])
```

Here `(a_f)^*` means gather/pullback along the affine map, pointwise `product_f` combines factors,
and `(pi_t)_!` means the ordered reduction over each projection fibre. This
pullback-product-pushforward decomposition is not additional runtime machinery: it explains why
`TermPlan` must keep iteration shape, affine rows, factor boundaries, and output/reduction positions
explicit.

Under exact algebra these operations may satisfy familiar monoid or semiring laws. Under
`NumericMode.reference64`, Float addition is not associative, so Wave C preserves the declared fold
orders rather than quotienting plans by algebraic equations that are false observationally.

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

`ScalarBinOp` has no other tags in Wave C's plan version (Section 5.1): `min`/`max`/`logicalAnd`/
`logicalOr` are added only in the later plan version that gives max/min aggregation and
predicate/Boolean outputs a real producer and consumer, not pre-declared now.

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

## 9. Representation layer: canonical data and transformations

Semantic plan data, its canonical bytes, and possible relational or rewrite-oriented views are
different representations of one checked computation. Wave C chooses a compact nested first-order
representation as the source of truth. A representation is useful only if its conversion preserves
the checked plan meaning established in Sections 5-8.

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

```lean
abbrev PlanFingerprint := ByteArray
```

`PlanFingerprint` is the opaque digest byte string produced from the versioned canonical semantic
encoding. The codec validates the selected algorithm's exact digest length; other callers only
compare fingerprints for equality.

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

### 9.4 Attributed C-sets and DPO rewriting are downstream views

An EvalPlan-specific attributed C-set could represent tensor slots, assignment nodes, terms, reads,
iteration dimensions, and their incidence maps as one categorical database instance. Such a view
would support generic relational queries, schema migration, and later graph transformation. The
relevant model is described by Patterson, Lynch, and Fairbanks'
[*Categorical Data Structures for Technical Computing*](https://arxiv.org/abs/2106.04703) and
Spivak's [*Functorial Data Migration*](https://doi.org/10.1016/j.ic.2012.05.001).

Likewise, a later plan optimization can be described by a double-pushout rule
`L <- K -> R`: `L` is the matched subplan, `K` is the input/output interface kept fixed, and `R` is
the replacement. This makes the "keep" interface useful for fusion, affine-map composition, or scan
specialization after observational equivalence has been established.

Neither perspective should replace the initial nested IR. A C-set schema alone does not establish
rank agreement, acyclicity, numeric order, or affine bounds semantics, and DPO rewriting does not
prove that `R` computes the same Float result as `L`. Wave C first fixes checked semantics and a
reference interpretation; relational views and rewrite systems may then consume that boundary.

## 10. Interpretations and commuting correctness laws

Dense, PyTorch, and JAX should be treated as interpretations of one checked plan language. In
categorical terms, the design target is functorial: signatures map to backend tensor spaces, checked
composition maps to backend composition, and each plan constructor retains one meaning. Wave C does
not claim that these functors are already formalized in Lean; the viewpoint determines the
commuting tests and prevents backend-specific semantics.

The complete source-facing claim is the commuting boundary:

```text
named inputs --pack--> positional inputs --runDensePlan--> positional outputs --unpack--> named report
     |                                                                            |
     +-------------------------- evalScheduled ----------------------------------+
```

The five laws below separate failures in specialization, checked construction, local
interpretation, representation adaptation, and future scan optimization instead of treating
end-to-end agreement as one opaque property.

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

### Law 2: checked construction and composition

```text
checkAssign(tensorSigs, rawAssign) = ok checkedAssign
  implies every documented local-kernel precondition holds for checkedAssign

checkPlan(raw) = ok checked
  implies every operation is locally checked and every documented graph-worker
  precondition holds for checked
```

Here `rawAssign : AssignPlan`, `checkedAssign : CheckedAssignPlan`, `raw : RawEvalPlan`, and
`checked : CheckedEvalPlan`. The two validating constructors are described in Section 5.2;
`checkPlan` must call the local checker rather than duplicate it. Workers may still report runtime
resource failures, but they must not rediscover malformed ranks, out-of-range slot references,
unresolved shapes, unknown operation tags, or invalid production order.

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

## 11. Design justification and external influences

This section retains only ideas that determine an immediate Wave C design choice or an explicitly
planned extension. Every subsection states the usable idea, the concrete application, and the phase
boundary beyond which the idea does not justify additional work. `C0` through `C6` refer to the
implementation slices in Section 15: executable contracts, static signatures, local kernel,
checked graph, source boundary, canonical representation, and final audit, respectively. `Wave F`
is the later scan-decomposition wave; `Wave G` is the later PyTorch/JAX backend wave.

The categorical organization above is a synthesis of these influences, not a new implementation
dependency. In particular, the terminology in the Topos Institute overview
[*AI Planning with C-Sets*](https://topos.institute/blog/2022-09-20-ai-planning-csets/) provides a
helpful but limited analogy:

| Categorical planning term | Wave C analogue |
|---|---|
| planning problem | `(ScheduledProgram, InputSignature)` |
| planner | `prepareEvalPlan` |
| plan | `CheckedEvalPlan` |
| plan consumer | a backend interpretation |

The analogy stops there. Automated planning searches for an action sequence reaching a goal; Wave C
deterministically specializes a computation whose actions and dependencies are already specified.
There is no goal-state search, action applicability search, or backtracking. C-sets and DPO rewriting
therefore inform possible plan representations and later transformations, while partial evaluation
and compiler correctness remain the right account of `prepareEvalPlan`.

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

**Phase boundary.** C1 makes shapes available as static signatures; C4 performs the explicit
specialization and tests the residual program against the unspecialized evaluator. Wave C does not
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

**Phase boundary.** C2 defines, checks, and interprets the local operation structure; C3 composes
those operations into a checked graph; C4 lowers source expressions into it. Later backends may
lower checked nodes to MLIR or StableHLO, but those are derived artifacts, not alternative sources
of LeanNCD semantics.

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
[*Ghosts of Departed Proofs*](https://doi.org/10.1145/3242744.3242755) shows how evidence can constrain data
at construction time without imposing the same proof representation on runtime computation.

**Concrete application.** C2 validates freely constructible `AssignPlan` values into private
`CheckedAssignPlan` nodes; C3 validates a freely constructible `RawEvalPlan` into a private
`CheckedEvalPlan` graph. Structural evidence may be stored as Lean propositions or established by
executable checks and then erased; the serializable payload remains ordinary first-order data. This
determines Law 2 and the rule that compilers and codecs produce raw data, never an unchecked
executable value.

**Phase boundary.** C2 introduces the local checked constructor; C3 introduces the graph checked
constructor and whole-plan worker; C5 applies the same boundary to decoding. The proposal
deliberately avoids indexing every array with a dependent proof when private checked wrappers
provide the required safety with a simpler codec and worker.

### 11.6 Translation validation: validate each artifact, then test semantic agreement

**Usable idea.** Pnueli, Siegel, and Singerman's
[*Translation Validation*](https://doi.org/10.1007/BFb0054170) validates the result of each compiler
run instead of relying only on a once-for-all proof of the compiler implementation.

**Concrete application.** `checkPlan` validates every compiled or decoded raw artifact before
execution. Separately, the C4/C6 differential matrix executes the independently organized
`evalScheduled` and `runPreparedDense` paths on the same generated programs. The former establishes
structural validity; the latter attacks semantic lowering mistakes.

**Phase boundary.** C2 validates local operations; C3 validates graph composition; C4 and C6
implement differential semantic validation. `checkPlan` is not claimed to prove source/plan
equivalence, and differential testing is not claimed to be a theorem. A future compiler proof may
strengthen Law 1 without replacing either practical check.

### 11.7 Representation independence: each backend must preserve one plan relation

**Usable idea.** Mitchell's
[*Representation Independence and Data Abstraction*](https://doi.org/10.1145/512644.512669)
characterizes correctness across different concrete representations through a relation preserved by
operations.

**Concrete application.** Law 3 relates Dense tensors, PyTorch tensors, and JAX arrays by declared
shape, dtype, element values, and `NumericMode`. Every plan constructor receives a per-constructor
conformance test showing that related inputs produce related outputs. Backend-specific fast paths
must also relate to the generic interpretation of the same checked node.

**Phase boundary.** C2 establishes local Dense interpretation, C3 establishes graph interpretation,
and C4 establishes the complete source observation relation. Wave G adds PyTorch and JAX
interpretations one constructor at a time. The principle rules out backend-specific mathematical
meanings and silent fallback to another worker.

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

## 12. Guarded stateful extension: scans

The initial plan graph is acyclic. A scan adds explicit state feedback: one step has the conceptual
shape `State x StepInput -> State x StepOutput`, and iteration feeds the next state back into the
same checked transition. This resembles traced or iterative monoidal structure, but LeanNCD needs a
**guarded, causal** form rather than arbitrary feedback. `CausalityCertificate` is therefore evidence
that the declared traversal order makes every feedback read well founded; it is not merely an
optimization hint.

This viewpoint justifies delaying scans without treating them as exceptional. Wave C first fixes the
stateless morphisms, graph composition, boundaries, and interpretations that a future `ScanPlan`
will reuse. Wave F then exposes the state transition and the guarded feedback data that cannot be
reconstructed safely from today's parallel statement lists.

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

## 13. Evidence organized by laws

Tests should follow the same conceptual decomposition as the architecture:

| Evidence group | Primary question | Main law |
|---|---|---|
| Local kernel | Do affine pullback, padding, products, and fibre reductions match reference semantics? | Laws 1 and 3 |
| Typed graph | Are slots, production order, reuse, and checked composition valid? | Law 2 |
| Boundary | Does pack/run/unpack preserve the complete source-visible outcome? | Law 4 |
| Representation | Do canonical encode/decode and fingerprints preserve checked meaning? | Laws 1 and 2 |
| Stateful extension | Does every specialized scan agree with explicit ordered feedback? | Law 5 |

The end-to-end differential matrix remains essential, but these groups make a failure attributable:
a wrong affine row is not diagnosed as a generic compiler failure, and a missing unpacked
intermediate is not confused with a contraction error.

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

## 14. Scope discipline and deferred machinery

The layer organization is deliberately conceptual. It does not license a framework for each layer.
Wave C needs small first-order records, executable checks, and one independent Dense interpretation.
The following approaches either collapse concerns that must remain distinct or build machinery
before a real producer and consumer exist.

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

### 14.8 Making C-sets or DPO rewriting the initial runtime

An attributed C-set can be a useful relational view of a checked plan, and DPO rules can later
describe interface-preserving plan transformations. Neither should be the Wave C execution source
of truth. The initial worker needs ordered arrays, direct affine arithmetic, exact Float folds, and
typed errors; translating through a categorical database before those semantics are stable adds a
second representation and a second validator. Likewise, applying graph rewrites before Law 1 is
established only moves unverified compiler logic into a rewrite engine.

## 15. Implementation plan and concrete artifact inventory

### 15.1 Planning principle: build the semantic spine inside out

The implementation should not complete one conceptual layer in isolation and then hope the layers
compose. Each phase is a **vertical slice** with four parts:

1. first-order data for one new semantic boundary;
2. a validator that turns raw data into private checked evidence;
3. a Dense interpretation of only that checked boundary; and
4. focused evidence before the next boundary is added.

The order follows semantic dependency rather than source-program chronology:

```text
local operation
  -> checked operation
  -> checked open graph
  -> source specialization and pack/unpack
  -> canonical representation
```

This changes the old implementation order in one important way. The Dense interpretation is brought
up with the local kernel and graph, before `prepareEvalPlan`. The source compiler therefore targets
an already executable checked language. Canonical bytes and hashing come last because they are a
representation of established semantics, not a prerequisite for execution.

The categorical vocabulary guides the boundaries but introduces no categorical runtime library:

- C2 implements one pullback-product-pushforward operation;
- C3 composes checked operations as a typed acyclic open graph;
- C4 implements the source-facing representation change and residual compiler;
- C5 chooses canonical bytes for the already checked graph.

### 15.2 Concrete artifacts by semantic owner

**Semantic IR** is the first-order data whose fields determine execution and canonical bytes.
**Checked evidence** is private data produced by validation and is not separately serialized.
**Boundary data** contains names, warnings, or source-facing metadata and is excluded from the
semantic fingerprint.

| Owner | First slice | Kind | Artifact | Responsibility |
|---|---|---|---|---|
| Static boundary | C1 | enum | `ScalarDType` | Closed concrete-storage dtype vocabulary; only `f64` is admitted initially. |
| Static boundary | C1 | structure | `TensorSignature` | Concrete shape and dtype without tensor values. |
| Static boundary | C1 | structure | `InputSignature` | Source-name-keyed specialization input. |
| Static boundary | C1 | function | `inferAxisSizesFromSignature` | Runs the existing sizing semantics from shapes plus `ScheduledProgram.explicitSizes`; reuses existing `ShapeError` — no new C1-scoped failure mode exists. |
| Local kernel | C2 | index/policies | `TensorSlot`, `NumericMode`, `OutOfBoundsPolicy` | Positional storage, exact numeric-order policy, and padded-read policy. |
| Local kernel | C2 | scalar data | `ScalarConst`, `ScalarBinOp`, `ContractionAlgebra` | Closed, dtype-preserving factor/reduction operations and identities. |
| Local kernel | C2 | semantic IR | `AffineMap`, `ReadPlan`, `TermPlan`, `AssignPlan` | One complete local tensor operation with explicit iteration, pullback maps, product, and ordered pushforward. |
| Local kernel | C2 | checked evidence | `CheckedAssignPlan` | Private evidence that one `AssignPlan` satisfies every local shape, rank, map, position, algebra, and policy invariant. |
| Local kernel | C2 | validator/interpreter | `checkAssign`, `runDenseAssign` | Validate and interpret one operation independently of source names, UIDs, and graph scheduling; fail loudly on nonconforming positional tensors. |
| Typed graph | C3 | semantic IR | `RawEvalPlan` | Freely constructible versioned tensor-signature table, input boundary, ordered operation nodes, and numeric mode. |
| Typed graph | C3 | checked evidence | `CheckedEvalPlan` | Private checked graph whose nodes are locally checked and whose wiring is typed, acyclic, and production ordered. |
| Typed graph | C3 | error/validator | `PlanError`, `checkPlan` | Report local or graph violations and compose `checkAssign` across the graph. |
| Dense interpretation | C3 | worker | `runDensePlan` | Execute the checked graph over positional `DenseTensor` storage by invoking `runDenseAssign` in order. |
| Dense interpretation | C2-C3 | runtime error | `PositionalInputError` | Reject absent positional tensors or runtime shape/storage that disagrees with checked source signatures. |
| Source boundary | C4 | sidecars | `SlotBinding`, `PlanBindings`, `PreparedPlan` | Pair a checked graph with source names and preparation warnings without changing semantic identity. |
| Source boundary | C4 | errors | `CapabilityError`, `InputSignatureError`, `PlanCompileCause`, `PlanCompileFailure`, `InputBindingError`, `PlanRunFailure` | Preserve typed preflight, specialization, binding, and runtime-adapter failures. `InputSignatureError`'s real producer is `prepareEvalPlan`'s signature-completeness check (§4.2 step 2) — moved here from C1, which has no producer for it. |
| Source boundary | C4 | compiler | `prepareEvalPlan` | Residualize `(ScheduledProgram, InputSignature)` into a checked positional plan plus boundary sidecars. |
| Source boundary | C4 | adapter | `pack`, `unpack`, `runPreparedDense` | Implement the worker/wrapper boundary and preserve complete source-visible observations. |
| Representation | C5 | derived data | `PlanFingerprint` | Opaque SHA-256 digest of domain-separated canonical semantic bytes. |
| Representation | C5 | functions | `encodePlan`, `fingerprintPlan`, `decodePlan` | Canonically encode checked semantics; decode to raw data and revalidate before execution. |
| Representation | C5 | error | `PlanCodecError` | Report malformed bytes, noncanonical encodings, unsupported versions, and invalid decoded plans. |
| Evidence | C0-C6 | tests/contracts | capability table, law matrix, mutation corpus, handoff manifest | Pin scope, local semantics, graph composition, source agreement, representation integrity, and completed capability. |

The Wave C semantic IR is exactly `AffineMap`, `ReadPlan`, `TermPlan`, `AssignPlan`, and
`RawEvalPlan`, together with the closed scalar and policy tags they contain. `CheckedAssignPlan` and
`CheckedEvalPlan` are validation evidence over that data. Signatures are specialization inputs;
bindings, warnings, prepared wrappers, fingerprints, and codec envelopes are boundary or derived
representations.

The future `ScanPlan`, `StateSlot`, `CheckedPlanBlock`, `IterationOrder`, `StateWriteMap`,
`ScanBoundaryPolicy`, and `CausalityCertificate` remain absent. Section 12 defines their later
contract, but C6 must not add placeholder constructors without real producers and consumers.

### 15.3 Vertical-slice sequence

| Slice | New executable claim | Principal law | Gate |
|---|---|---|---|
| C0 - executable contract ✅ DONE 2026-08-05 | The accepted fragment, observation relation, ordering, and rejection order are unambiguous. | all laws' premises | Every source constructor and edge case has one expected classification or observation. |
| C1 - static boundary | Concrete shapes can be inferred from signatures without tensor values. | Law 1 premise | Signature- and Dense-driven inference have identical sizes, warnings, and failures. |
| C2 - local kernel | One checked operation has one Dense meaning. | Law 2 locally; Dense-side premise of Law 3 | Hand-computed pullback/product/pushforward cases pass; malformed local nodes and nonconforming positional tensors are rejected. |
| C3 - typed graph | Checked local operations compose into one deterministic Dense graph. | Law 2 compositionally; Dense-side premise of Law 3 | Manual graph cases cover chains, fan-out, re-reads, single production, and invalid production order. |
| C4 - source boundary | Supported schedules residualize to that graph, and pack/run/unpack preserves source observations. | Laws 1 and 4 | Every accepted generated case agrees bit-for-bit with `evalScheduled`; rejected capabilities fail before execution. |
| C5 - canonical representation | Bytes and fingerprints preserve, but do not define, checked meaning. | Laws 1 and 2 under round-trip | Encode/decode/check/run agrees; alpha-renaming preserves fingerprints; semantic mutations change them. |
| C6 - audit and handoff | The declared Wave C claim holds without hidden fallback or dependency inversion. | all applicable laws | Full build, mutation matrix, import audit, and capability manifest pass. |

The critical path is:

```text
C0 -> C1
  \-> C2 -> C3 -> C4 -> C5 -> C6
        \-------------^
```

C1 and the early C2 kernel work may proceed independently after C0. C4 requires both. C5 may not
freeze bytes until C4 has shown that the checked graph contains all semantics needed for
source-level agreement. This prevents serialization from fossilizing an incomplete IR.

### 15.4 Final Wave C gate

For every `sched : ScheduledProgram` and `sig : InputSignature` in the declared scan-free
`reference64` fragment, preparation has exactly one of these outcomes:

```text
prepareEvalPlan(sched, sig) = ok prepared

and, for every namedInputs conforming to sig:

runPreparedDense(prepared, namedInputs)
  =obs evalScheduled(sched, namedInputs)

or prepareEvalPlan(sched, sig) returns a typed PlanCompileFailure before
plan execution.
```

Additionally, every successful canonical round-trip must return a checked plan with the same
semantic bytes, fingerprint, and Dense behavior. Because the fragment has only
`NumericMode.reference64`, tensor equality within `=obs` is bit-for-bit equality.

> **Deferred 2026-08-07, see A.9.** The canonical-round-trip clause above depends on C5's
> `Plan/Canonical.lean`/`Plan/Codec.lean`, which are deferred — no consumer inside this process's
> own lifetime needs fingerprint stability or serialized bytes. Until C5 is actually built, this
> gate holds only for its first clause (`prepareEvalPlan`/`runPreparedDense` agreement with
> `evalScheduled`, or a typed rejection) — already demonstrated by C4's differential sweep. C6's own
> Gate ("Section 15.4 holds") should be read against this reduced form, not the full text above.

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

This appendix is a fresh implementation plan derived from the five semantic workstreams. It does
not preserve the earlier "define all IR, then compile, then execute" order. Instead, each checked
boundary receives a Dense consumer and evidence before the next boundary is introduced.

Exact constructor spelling may change during implementation. Changing semantic ownership, adding a
new admitted capability, or weakening a gate requires updating this proposal first.

### A.1 Definition of done

Wave C is complete only when:

1. the local `AssignPlan` kernel is independently checkable and executable;
2. `checkPlan` composes those checked nodes into a typed, acyclic, production-ordered graph;
3. `prepareEvalPlan` accepts exactly the declared scan-free `f64` fragment and rejects every other
   valid scheduled construct with a typed `CapabilityError` before tensor execution;
4. every accepted checked graph contains no source tensor names, axis UIDs, functions, callbacks,
   backend objects, or unordered semantic maps;
5. `runPreparedDense` agrees with `evalScheduled` under `=obs`, including complete environments,
   warning order, typed failures, empty products/domains, zero extents, and bit-exact Float data;
6. raw and decoded operations or graphs cannot reach workers without `checkAssign` or `checkPlan`;
7. the plan worker does not call or import the legacy `Gather`/`Contract` execution path; and
8. the full default Lean build passes with no skipped test module:

   ```bash
   cd leanncd && "$HOME/.elan/bin/lake" build
   ```

> **Deferred 2026-08-07, see A.9.** The original bullet 7 here — "canonical bytes and fingerprints
> are deterministic, name-independent, versioned, and downstream of checked semantics" — is removed
> from Wave C's completion criteria, not silently dropped. No consumer inside this process's own
> lifetime needs either a stable fingerprint across restarts or serialized plan bytes; the one
> plausible future need (a live cross-process JAX/PyTorch backend) would contradict the
> ahead-of-time codegen pattern `torch_compile/` already establishes for backend integration. C5
> (A.9) is deferred until a concrete need actually specifies its shape, rather than being built
> speculatively now.

### A.2 Production modules and dependency direction

Create `LeanNCD/Eval/Plan/` with modules named for semantic ownership:

| Module | Owns | Explicit non-ownership |
|---|---|---|
| `Types.lean` | concrete signatures, slots, dtype, scalar, and policy tags | no source syntax, tensor values, or codecs |
| `Kernel.lean` | `AffineMap`, `ReadPlan`, `TermPlan`, `AssignPlan` | no graph scheduling, names, UIDs, or Dense operations |
| `Graph.lean` | `RawEvalPlan` and its open input/output slot presentation | no checked constructors or execution |
| `Error.lean` | plan-specific signature, capability, validation, binding, and codec errors | no renderer or generic-string escape hatch outside the existing diagnostic convention |
| `Check.lean` | private `CheckedAssignPlan`/`CheckedEvalPlan`, `checkAssign`, `checkPlan`, read-only accessors | no source compilation or tensor arithmetic |
| `Dense.lean` | `runDenseAssign` and `runDensePlan` over positional stores | no names, UIDs, source lowering, codec, or legacy evaluator calls |
| `Signature.lean` | Dense-to-signature projection and shape-only inference adapter | no plan construction |
| `Prepared.lean` | `SlotBinding`, `PlanBindings`, `PreparedPlan`, and warning-preserving boundary failures | no canonical bytes or fingerprint field |
| `Compile.lean` | capability preflight, slot/basis allocation, affine lowering, `prepareEvalPlan` | no Dense execution or canonical encoding |
| `Adapter.lean` | `pack`, `unpack`, `runPreparedDense` | no shape inference or source traversal |
| `Canonical.lean` | canonical semantic bytes, SHA-256, `PlanFingerprint`, `fingerprintPlan` | no names, warnings, bindings, or backend metadata |
| `Codec.lean` | versioned wire envelope, decode-to-raw, revalidation | no unchecked execution |
| `Plan.lean` | stable public umbrella | no implementation logic |

The final dependency graph is:

```text
Types -> Kernel -> Graph
  |        |        |
  +------> Error ---+-> Check -> Dense

Types + Error + Eval.SizeInfer/Eval.Tensor -> Signature
Check + Error + Eval.Error -> Prepared
Prepared + Signature + Graph + Check + Error + DSL/Eval source helpers -> Compile
Prepared + Dense + Check + Error + Eval.Report -> Adapter

Check + Graph -> Canonical
Canonical + Graph + Check + Error -> Codec
```

`Canonical.lean` needs `Graph` directly, not only `Check`: `CheckedEvalPlan` privately wraps
`RawEvalPlan`, so encoding it means walking `RawEvalPlan`-shaped fields (themselves built from
`Kernel`'s types), which requires `Graph`'s type declarations in scope. `Check.lean`'s trusted
accessors (Section 5.2) may expose that payload — e.g. an accessor returning the underlying
`RawEvalPlan` structure by value — without exposing either private constructor; they do not remove
`Canonical.lean`'s need to import `Graph` for the type itself.

`Check.lean` may add `checkAssign` in C2 before adding `checkPlan` in C3; `Dense.lean` similarly adds
the node interpreter before the graph interpreter. This incremental growth is intentional.

Keep the following boundaries strict:

- [`SizeInfer.lean`](../leanncd/LeanNCD/Eval/SizeInfer.lean) must not import plan modules. Its
  reusable core accepts the explicit UID-size seed plus name-to-shape metadata.
- `Dense.lean` must not import `Compile.lean`, `Canonical.lean`, `Gather.lean`, or `Contract.lean`.
- `Compile.lean` must not import `Dense.lean`.
- `Canonical.lean` consumes only checked semantic data, not `PreparedPlan`.
- `Codec.lean` decodes to `RawEvalPlan`, then calls `checkPlan`.

Move `EvalReport`, unchanged, from [`Eval.lean`](../leanncd/LeanNCD/Eval/Eval.lean) to a neutral
`Eval/Report.lean` leaf shared by the old evaluator and `Adapter.lean`. Keep plan diagnostics in
`Plan/Error.lean`; importing plan types into the existing leaf `Eval/Error.lean` would reverse that
module's established dependency direction.

Do not reuse `LeanNCD.Base.DType`: it belongs to the symbolic math tower and carries `SizeExpr`.
`ScalarDType` describes concrete executable storage.

### A.3 Test organization and law ownership

Add these modules to the explicit `Tests.globs` list in `leanncd/lakefile.toml`:

```text
Eval.Plan.ContractTest
Eval.Plan.SignatureTest
Eval.Plan.KernelCheckTest
Eval.Plan.KernelDenseTest
Eval.Plan.GraphCheckTest
Eval.Plan.GraphDenseTest
Eval.Plan.CompileTest
Eval.Plan.AdapterTest
Eval.Plan.DifferentialTest
Eval.Plan.CanonicalTest
Eval.Plan.CodecTest
```

Use existing `#guard`/`run_cmd` conventions; do not add a test runner. Keep plan-specific
comparisons outside `PropertyOracle` so the existing oracle remains independent. Extend
[`Gen.lean`](../leanncd/test/Eval/PropertyOracle/Gen.lean) only when an explicit coverage guard
demonstrates a missing semantic case.

| Test group | Owns | Must not be used to excuse |
|---|---|---|
| `Kernel*` | local affine pullback, padding, factor product, ordered reduction, identities | graph wiring or compiler defects |
| `Graph*` | slot typing, production order, fan-out, node sequencing | source name/UID lowering |
| `Signature`/`Adapter` | static shape parity and pack/unpack representation laws | kernel arithmetic |
| `Compile`/`Differential` | residualization and complete source observations | malformed raw-plan acceptance |
| `Canonical`/`Codec` | representation uniqueness and revalidation | semantic equivalence of an untested graph |

Every slice runs its targeted modules and then the full default build. Passing a scratch target is
not a gate.

### A.4 C0 - executable contract and fixtures

**Production changes:** none.

1. Build one capability matrix covering every `ScanStmt`, `Stmt`, `LHSSlot`, `Factor`, `Nonlin`,
   `AggOp`, and declaration dtype constructor. `NumericMode` has no admitted values to enumerate
   yet — it is a `Plan/Types.lean` type introduced in C1/C2, not something C0 can classify against;
   record its Wave C value (`reference64`, the only one) as a one-line comment, not a classifier.
2. Fix failure precedence: capability preflight, signature validation, shape inference, raw
   construction, local checking, graph checking, runtime binding.
3. Fix source-to-graph ordering:
   - external slots follow declaration order filtered to required external names;
   - operations follow scheduled statement order;
   - reads resolve to the most recent preceding slot for their tensor name;
   - every assignment allocates a fresh destination slot;
   - the final materialized binding for a repeated name points to its last write;
   - term and factor arrays retain source order;
   - each term basis is retained LHS UIDs followed by first-occurrence contracted UIDs;
   - output positions are the basis prefix and reduction positions the suffix;
   - `materializedNames` is exactly every `sched.stmts` destination name (Section 5.4) — the same
     set `evalScheduled` inserts into `env`, with no separate filtering rule.

   Only some of these bullets have observable behavior yet: "most-recent-preceding-slot" and
   "final materialized binding" are pinned in C0 against the *current* `evalScheduled` (repeated
   assignment and fan-out already exhibit this — there is no `TensorSlot` to test against). "Fresh
   destination slot" and "term basis order" name concepts that don't exist as data until C4's
   compiler allocates them; for those, C0's job is done by this bullet list itself, and C4's own
   plan pins them for real once `Compile.lean` exists.
4. Fix empty and zero semantics — these are two distinct cases, both needing a fixture:
   - an empty factor product uses `factorId`;
   - an empty term array (no terms at all) uses `reduceId`;
   - a *non-empty* term whose contracted axis has size 0 — a zero-extent reduction *domain*, not an
     empty term array — also uses `reduceId`, over zero folded coordinates;
   - no reduction axes means one reduction coordinate, `[[]]`;
   - a zero output extent produces empty tensor data.
5. Add hand-written fixtures for negative shifts, multi-axis maps, zero coefficients that still
   mention a contracted UID, empty products/reductions, zero dimensions, unused extra inputs,
   fan-out, and repeated assignment. Per-term contraction asymmetry is already pinned by the
   existing `EC15 per-term-contraction` case in
   [`EdgeCaseTest.lean`](../leanncd/test/Eval/Portfolio/EdgeCaseTest.lean) — cite it, do not
   duplicate it.
6. Define mutation expectations: each malformed mutation must either be rejected by its owning
   checker or, if still valid, change the expected result. Every fixture's expected value must be
   independently verified against the real evaluator before being written down, not hand-guessed.

**Gate:** every capability and edge case has one typed expectation, and all iteration/fold orders
are defined independently of `HashMap`/`Finset` traversal.

**Detailed plan:** [`docs/superpowers/plans/2026-08-05-wave-c-c0-executable-contract.md`](../docs/superpowers/plans/2026-08-05-wave-c-c0-executable-contract.md).

> **✅ DONE 2026-08-05.** `leanncd/test/Eval/Plan/ContractTest.lean` implements items 1-6 above:
> exhaustive classifiers over every listed constructor, the checked `PreflightPhase` total order,
> and ten hand-verified fixture/mutation pairs. Full `lake build` green (8,619 jobs, up from the
> 8,618 baseline). **One real gap found and fixed by the final whole-branch review, not anticipated
> by this section:** `classifyStmt`'s first draft never inspected `RHSExpr.agg`, so it classified a
> `agg := .max`/`.min` statement as accepted even though item 1's own `classifyAggOp` correctly
> rejects `.max`/`.min` — a direct internal contradiction between two functions in the same file,
> caught only once all six tasks' content sat together. Fixed before merge; the capability matrix
> now checks `agg` as part of `classifyStmt`'s composed precedence chain.

### A.5 C1 - static signature boundary

**Production files:** `Plan/Types.lean`, `Plan/Signature.lean`, and
[`SizeInfer.lean`](../leanncd/LeanNCD/Eval/SizeInfer.lean). **Not `Plan/Error.lean`** — C1
introduces no new error type (see item 1's note), so the module has nothing to hold yet; C2
creates it for `PlanError`.

1. Define `ScalarDType`, `TensorSignature`, and `InputSignature`; reuse the existing `ShapeError`
   (Section 5.5) for shape-inference failures rather than introducing a second shape-failure type.
   **Do not define `InputSignatureError` here.** `evalScheduled`'s `inputs : HashMap String
   DenseTensor` parameter is always the raw external-input map (never the accumulating `env`), so a
   signature-based shape lookup misses a name under exactly the same circumstances the current
   env-based lookup does — no new failure mode exists yet. `InputSignatureError`'s real producer is
   C4's `prepareEvalPlan` step 2 ("validate that the `InputSignature` is complete and structurally
   compatible with the schedule", Section 4.2) — define it there, where it has one.
2. Extract the body of `inferAxisSizes` into a shape-driven core whose inputs are:
   - the existing `HashMap UID Nat` explicit-size seed; and
   - a source-name-to-`List Nat` shape lookup.
3. Preserve `inferAxisSizes` as a thin adapter from `DenseTensor.shape`.
4. Add `inferAxisSizesFromSignature`; `prepareEvalPlan` will pass
   `ScheduledProgram.explicitSizes` unchanged.
5. Derive `InputSignature` from Dense inputs with dtype `f64`.
6. Preserve warnings on shape failure exactly as the current `EvalFailure` path does.
7. Keep concrete storage validation at runtime; a signature does not prove
   `DenseTensor.data.size = DenseTensor.sizeOf shape`.

**Tests:**

- signature conversion and malformed signatures;
- sizes, warning order, and `ShapeError` parity over existing shape tests;
- parity across the bounded property-oracle corpus;
- an extent known only through `explicitSizes`;
- a pinned-size/input conflict;
- warnings retained when a later shape constraint fails.

**Gate:** the legacy evaluator is behaviorally unchanged, and the two inference adapters return
identical outcomes for equal shape metadata.

**Detailed plan:** [`docs/superpowers/plans/2026-08-05-wave-c-c1-static-signature-boundary.md`](../docs/superpowers/plans/2026-08-05-wave-c-c1-static-signature-boundary.md).

> **✅ DONE 2026-08-05.** `Plan/Types.lean` and `Plan/Signature.lean` add the
> `ScalarDType`/`TensorSignature`/`InputSignature` vocabulary and `inferAxisSizesFromSignature`;
> `SizeInfer.lean` was refactored to extract `inferAxisSizesCore`, with `inferAxisSizes` kept as a
> thin `DenseTensor`-based adapter so its call sites needed no change. `leanncd/test/Eval/Plan/SignatureTest.lean`
> implements all six test bullets above (signature conversion, adapter parity on an existing shape
> case, adapter parity on two hand-written corpus fixtures, an `explicitSizes`-only extent, a
> pinned-size/input conflict, and warning preservation across a later failure). Full `lake build`
> green (8,622 jobs, up from the 8,619 C0 baseline). **Two deviations from this section's plan
> text, recorded here since this document is the permanent record of what C1 actually did:**
>
> - The parity helper's natural formulation, `decide (e1.error = e2.error)`, does not compile:
>   `EvalError` has no `DecidableEq` (its `.unaryDomain` constructor carries a `Float` field, which
>   has none either — the same reason `test/Eval/PropertyOracle/Compare.lean` carries a
>   hand-written `evalErrorEq`). The test compares via `toString e1.error = toString e2.error`
>   instead, sound here because `inferAxisSizesCore` only ever throws `ShapeError`'s `.shape`
>   variants (which do derive `DecidableEq`) over this test's fixtures.
> - Test bullet 3's suggestion to reuse cases from `test/Eval/PropertyOracle/Gen.lean`'s corpus
>   turned out to be blocked: every named sub-list feeding that file's generator
>   (`contractPrograms`, `yDepPrograms`, `contractMultiTermPrograms`, etc.) is `private`, and only
>   the bulk `enumPrograms` is public. Two hand-written `tlprog!` fixtures (a multi-factor
>   contraction and a chained two-statement program) were used instead of corpus slicing.
>
> Commits: `ee54e00^..dcd16c2`.

### A.6 C2 - checked local kernel vertical slice

**Production files:** `Plan/Types.lean`, `Plan/Kernel.lean`, `Plan/Error.lean`,
`Plan/Check.lean`, and `Plan/Dense.lean`.

#### C2.1 Define only the local operation language

Add `TensorSlot`, `NumericMode`, `OutOfBoundsPolicy`, `ScalarConst`, `ScalarBinOp`,
`ContractionAlgebra`, `AffineMap`, `ReadPlan`, `TermPlan`, and `AssignPlan`.
`ScalarConst.f64` stores `Float.toBits : UInt64`, never `Float`, so equality distinguishes signed
zero and preserves NaN payloads.

Do not add `RawEvalPlan`, source bindings, fingerprints, or codecs in this slice.

#### C2.2 Validate one operation

Implement:

```text
checkAssign :
  Array TensorSignature -> AssignPlan ->
  Except PlanError CheckedAssignPlan
```

The private checked node establishes:

- destination/source slots are in the signature table;
- source and destination dtypes are admitted and agree;
- coefficient row count and bias length equal source rank;
- every coefficient row has term-basis rank;
- `ReadPlan.sourceShape` equals its source-slot signature;
- output and reduction positions are ordered, disjoint, and partition the iteration basis;
- output projection equals `AssignPlan.outputShape`;
- all terms have the same output projection;
- constants match dtype;
- algebra, `zeroPad`, and `reference64` are admitted;
- C0-approved empty arrays and zero extents remain valid.

Graph availability and production order are deliberately not local checks.

#### C2.3 Interpret one checked operation

Implement the direct Dense interpretation with a typed runtime boundary:

```text
runDenseAssign :
  CheckedAssignPlan -> Array DenseTensor ->
  Except PositionalInputError DenseTensor
```

1. before reading a source slot, verify that it exists and that its runtime shape and storage size
   agree with the `ReadPlan.sourceShape` validated by `checkAssign`;
2. enumerate output coordinates, then reduction coordinates, in C0 order;
3. form each iteration coordinate;
4. compute each source coordinate as `coeffs * iterationCoordinate + bias` using `Int`;
5. test every source dimension before flattening and use padded zero if any dimension is invalid;
6. for each term, fold its factors from `factorId`, then fold that term's reduction coordinates from
   `reduceId`; after each term result is complete, fold term results from `reduceId` in term-array
   order. Do not flatten the inner reduction fold and outer term fold.

`CheckedAssignPlan` need not retain the complete signature table: each checked read already retains
the source shape needed to validate its runtime tensor, and the checked assignment retains its
destination shape. The function may use small positional-store helpers, but it must not call
`Gather.gather`, `evalAssign*`, construct `HashMap UID Int`, or use unchecked array access on
caller-provided data.

**Tests:**

- hand-computed identity, transpose, shift, stride, and multi-axis affine pullbacks;
- zero padding at lower and upper boundaries;
- multiple factors, terms, and contracted axes;
- per-term contraction differences;
- empty products/reductions and zero extents;
- exact fold-order cases sensitive to binary64 reassociation;
- missing, wrong-shape, and malformed-storage positional inputs return `PositionalInputError`;
- one mutation for every local `PlanError`;
- a cross-module compile-time check that external `⟨...⟩` construction of `CheckedAssignPlan` is
  rejected (Section 5.3) — not merely that `checkAssign` returns `Except`.

**Gate:** every local checker branch is covered, every valid fixture has a hand-computed Dense
result, and there is no worker accepting raw `AssignPlan`.

**Detailed plan:** [`docs/superpowers/plans/2026-08-05-wave-c-c2-checked-local-kernel.md`](../docs/superpowers/plans/2026-08-05-wave-c-c2-checked-local-kernel.md).

> **✅ DONE 2026-08-06.** `Plan/Kernel.lean` adds `AffineMap`/`ReadPlan`/`TermPlan`/`AssignPlan`;
> `Plan/Error.lean` adds `PlanError`/`PositionalInputError`; `Plan/Check.lean` adds the
> private-constructor `CheckedAssignPlan` and `checkAssign`; `Plan/Dense.lean` adds the direct Dense
> interpreter `runDenseAssign`. Tests: `Eval.Plan.KernelCheckTest` (15 `#guard`s — the reference
> plan's acceptance plus one mutation per reachable `checkAssign` throw site, with the three
> structurally unreachable branches — `dtypeMismatch`, `constDtypeMismatch`, `policyNotAdmitted` —
> named directly and explained inline instead of forced); `Eval.Plan.KernelDenseTest` (16 `#guard`s
> — the reference contraction plus identity, transpose, lower- and upper-boundary zero-padding,
> multi-axis affine, multiple terms, the `u[]·a[i] + W[i,k]·v[k]` per-term contraction asymmetry,
> empty factor product, empty term array, a zero-extent reduction domain, zero output extent, a
> fold-order fixture, and the three `PositionalInputError` cases); `Eval.Plan.CheckedPrivacyTest`
> (1 `#guard` plus the documented manual compile-failure check for `CheckedAssignPlan`'s private
> constructor). 32 `#guard`s in total across the three modules.
> All three modules registered in the default build target. Full `lake build` green (8,629 jobs, up
> from the 8,622 C1 baseline — the 4 new library modules and 3 new test modules this slice adds,
> matching this section's own arithmetic exactly). **One numeric fixture required a real execution
> to pin, not hand derivation alone:** the fold-order-sensitivity case (`1e16, 1.0, -1e16` folded in
> that array order) predicted `0.0` by hand — reasoning that binary64's round-ties-to-even rounds
> `1e16 + 1.0` back down to `1e16` at that magnitude's ULP of 2 — and the actual run confirmed
> `0.0` on first try, ruling out the reassociation that would cancel the two `±1e16` terms before
> adding `1.0` (which would yield `1.0` instead). No other deviations from this section's plan text.
>
> Commits: `b6de149^..e809064` (Task 1's `Plan/Kernel.lean`, Task 2's `Plan/Error.lean` +
> `Plan/Check.lean`, and Task 3's `Plan/Dense.lean` + all three test-module registrations).

### A.7 C3 - checked graph vertical slice

**Production files:** `Plan/Graph.lean`, `Plan/Error.lean`, `Plan/Check.lean`, and
`Plan/Dense.lean`.

#### C3.1 Add the graph data and checker

Define `RawEvalPlan` with version, tensor signatures, ordered input slots, ordered `AssignPlan`
nodes, and numeric mode. Implement:

```text
checkPlan : RawEvalPlan -> Except PlanError CheckedEvalPlan
```

`checkPlan` must call `checkAssign` for every node and additionally establish:

- version and numeric mode are admitted;
- input slots are in range, unique, and ordered;
- every non-input destination is produced exactly once;
- every read is from an input or earlier destination;
- each destination signature agrees with its checked local operation;
- no operation overwrites an existing positional slot;
- checked-node order is exactly raw graph order.

Store or derive the checked-node array behind the private graph constructor so `runDensePlan` does
not repeat local validation. Canonical serialization later uses raw semantic fields, not proof
representation.

#### C3.2 Interpret graph composition

Implement:

```text
runDensePlan :
  CheckedEvalPlan -> Array DenseTensor ->
  Except PositionalInputError (Array DenseTensor)
```

The input array is ordered by `CheckedEvalPlan.inputSlots`. `runDensePlan`:

1. checks input arity, then places positional inputs into the graph's declared input slots;
2. invoking `runDenseAssign` for each checked node in order;
3. inserting each result at its destination slot; and
4. returning the complete positional store required by output bindings.

This worker is the Dense interpretation of graph composition. It does not know source names or
compiler UIDs. Runtime shape/storage checks are value-boundary checks, not repeated validation of
plan structure. The untrusted named entry remains C4's adapter.

**Tests:**

- one node, chains, diamonds/fan-out, independent branches, and unused inputs;
- invalid forward read, duplicate input, duplicate destination, missing production, bad slot, and
  local error propagated with node context;
- wrong positional input arity, shape, or storage returns `PositionalInputError` without panic;
- manual sequential composition agrees with `runDensePlan`;
- reordering independent nodes preserves results only when dependencies permit it;
- reordering Float-sensitive terms inside a node is not treated as graph equivalence;
- a cross-module compile-time check that external `⟨...⟩` construction of `CheckedEvalPlan` is
  rejected (Section 5.3) — not merely that `checkPlan` returns `Except`.

**Gate:** manual checked graphs execute without source compiler support; all graph violations are
rejected before execution; `Dense.lean` has no source or legacy-worker dependency.

> **✅ DONE 2026-08-06.** `Plan/Graph.lean` adds `RawEvalPlan`; `Plan/Check.lean` adds the
> private-constructor `CheckedEvalPlan` and the graph-wiring checker `checkPlan`; `Plan/Error.lean`
> adds `PositionalInputError.arityMismatch`; `Plan/Dense.lean` adds the graph interpreter
> `runDensePlan`, composing `runDenseAssign` once per checked node rather than re-implementing
> node-level execution at the graph level. Tests: `Eval.Plan.GraphCheckTest` (16 `#guard`s — the
> chain and diamond/fan-out-with-unused-input reference graphs' acceptance, one mutation per
> `checkPlan` wiring-invariant throw site (including the in-node destination-slot and factor-source
> `slotOutOfRange` sites, both wrapped in `.nodeError` for node context), the single-valued
> `numericModeNotAdmitted` named directly since `NumericMode` has exactly one constructor, and the
> `CheckedEvalPlan` privacy check folded in per A.3's module list rather than split into its own
> module); `Eval.Plan.GraphDenseTest` (20 `#guard`s — one node, the chain, the diamond with
> fan-out/convergence/an unused input, an independent-node-reordering case, a manual
> sequential-composition-agreement check calling `checkAssign`/`runDenseAssign` directly instead of
> `checkPlan`/`runDensePlan`, a restatement of C2's non-associative-float fold-order fixture wrapped
> in a trivial one-node graph, the four `PositionalInputError` cases — too-few arity, too-many
> arity, wrong shape, and malformed storage — and an unread-input-still-validated case confirming an
> unused input slot's declared signature is enforced). 36 `#guard`s in total across the two modules,
> both registered in the default build target. Full `lake build` green (8,632 jobs, up from the 8,629 C2
> baseline — the 1 new library module (`Plan/Graph.lean`) and 2 new test modules this slice adds;
> `Error.lean`/`Check.lean`/`Dense.lean` are modified, not added, so they don't change the job count
> — matching this section's own arithmetic exactly). No deviations from this section's plan text.
>
> Commits: `f3cae27^..0ea2fa0` (Task 1's `Plan/Graph.lean` + `checkPlan` + `GraphCheckTest.lean`,
> Task 2's `PositionalInputError.arityMismatch` + `Plan/Dense.lean`'s `runDensePlan` +
> `GraphDenseTest.lean` + lakefile registration of both test modules, and the final-review fix wave
> that validated unused input slots and wrapped the in-node `slotOutOfRange` sites in `.nodeError`
> for node context — both already folded into the counts and description above, not a separate
> deviation).

### A.8 C4 - source compiler and representation boundary

**Production files:** `Eval/Report.lean`, `Eval/Eval.lean`, `Plan/Prepared.lean`,
`Plan/Compile.lean`, and `Plan/Adapter.lean`.

#### C4.1 Compile source metadata to the checked graph

Implement:

```text
prepareEvalPlan :
  ScheduledProgram -> InputSignature ->
  Except PlanCompileFailure PreparedPlan
```

In order:

1. run total source-order capability preflight; unsupported constructs produce the first typed
   `CapabilityError` before shape inference;
2. validate all required static signatures;
3. infer sizes from signatures using `sched.explicitSizes`, preserving warnings;
4. allocate external slots from declaration order, filtered to names read before production;
5. walk statements in schedule order with a current name-to-slot environment;
6. resolve all reads before allocating the statement's fresh destination slot;
7. update repeated-name bindings only after the operation is built;
8. derive retained output UIDs and concrete extents;
9. for each term, use `termAxisUIDs term |>.eraseDups`, remove retained UIDs, and append the
   remaining contracted UIDs; never inspect nonzero affine columns to infer occurrence;
10. lower indices with `idxAffineForm` and `idxDensify` over that term basis;
11. preserve statement, term, factor, and coordinate order;
12. construct `RawEvalPlan`, call `checkPlan`, and return it with bindings and warnings.

This is the phase where UIDs disappear. `PreparedPlan` contains no fingerprint; C5 derives one from
the checked graph without changing execution.

#### C4.2 Add pack/run/unpack

Use the source-facing API:

```text
NamedDenseEnv    := HashMap String DenseTensor
pack             : PreparedPlan -> NamedDenseEnv -> Except InputBindingError (Array DenseTensor)
unpack           : PlanBindings -> NamedDenseEnv -> Array DenseTensor -> NamedDenseEnv
runPreparedDense : PreparedPlan -> NamedDenseEnv -> Except PlanRunFailure EvalReport
```

`pack` walks `CheckedEvalPlan.inputSlots`, resolves exactly one binding and source name for each
slot, and emits tensors in that slot order; it does not trust `requiredInputs` array position.
Missing, duplicate, or extra required-input bindings fail with `InputBindingError`. It validates
shape, dtype, and Dense storage size using the helper shared with `runDenseAssign`, so named and
positional entry points cannot drift. `unpack` starts from the original environment, preserves
unrelated inputs, and inserts every materialized name at its final bound slot.
`runPreparedDense` nests either `InputBindingError` or `PositionalInputError` in `PlanRunFailure`
and preserves preparation warnings on success and on later binding/execution failure.

Move `EvalReport` to the neutral leaf without changing its fields or legacy behavior.

#### C4.3 Establish residualization and boundary laws

**Tests:**

- one accepted and rejected case for every C0 capability row;
- deterministic slots and term bases;
- zero-coefficient contracted-axis regression;
- repeated assignment followed by a read uses the most recent preceding write;
- alpha-renamed schedules produce equal raw semantic graphs but different bindings;
- two same-shape, different-value inputs remain correctly slotted when `requiredInputs` entries are
  presented in a different order; duplicate, missing, and extra slot bindings fail loudly;
- packing failures preserve warnings;
- unpacking preserves unused inputs and all materialized intermediates;
- differential execution over every `PropertyOracle.enumPrograms` case;
- for each generator entry, compile its actual schedule, derive its signature from the paired Dense
  inputs, and compare `runPreparedDense` with `evalScheduled`;
- test-the-tester mutations: change one coefficient, drop a term, or reorder a Float-sensitive fold
  and require differential failure.

**Gate:** every supported generated and hand-written case satisfies Laws 1 and 4 bit-for-bit; every
unsupported construct fails before `runDensePlan`; checked semantic data contains no `String` or
`UID`.

> **✅ DONE 2026-08-06.** `Plan/Compile.lean` adds `capabilityPreflight` and `prepareEvalPlan`;
> `Plan/Prepared.lean` adds `SlotBinding`/`PlanBindings`/`PreparedPlan`; `Plan/Adapter.lean` adds
> `pack`/`unpack`/`runPreparedDense`; `Eval/Report.lean` moves `EvalReport` to the neutral leaf
> (fields/behavior unchanged); `Plan/Error.lean` adds `CapabilityError`/`PlanCompileCause`/
> `PlanCompileFailure`/`InputBindingError`/`PlanRunCause`/`PlanRunFailure`; `Eval/Eval.lean` is
> touched only for the `Report.lean` move. Tests: `Eval.Plan.CompileTest` (29 `#guard`s — one
> accepted and one rejected case per C0 capability row, deterministic slots/term bases, the
> zero-coefficient contracted-axis regression, repeated assignment, and — the direct demonstration
> of the Gate's "every unsupported construct fails before `runDensePlan`" clause, since the
> differential sweep below never rejects a single `enumPrograms` entry and so cannot exercise it —
> `prepareEvalPlan` itself rejecting a `.scan` schedule with a `.capability`-tagged
> `PlanCompileFailure`); `Eval.Plan.AdapterTest` (3
> `run_cmd` blocks covering the 9 checks documented in-file — the full pack/unpack/`runPreparedDense`
> round trip cross-checked against the legacy evaluator, an unpack preserving an unrelated extra
> input, `requiredInputs` order-independence against an asymmetric-roles contraction fixture,
> duplicate/missing/extra/structurally-missing binding failures, and warning preservation on both
> the success path and a later binding failure); `Eval.Plan.DifferentialTest` (the alpha-renaming law
> — equal raw semantic graphs, unequal bindings, confirmed by a real run — the full
> `PropertyOracle.enumPrograms` differential sweep, 3 test-the-tester mutations, a rank-2 output case
> (`Y[i,j] := A[i]·B[j]`) exercising the multi-retained-axis surface at the value level, and a
> repeated-assignment program run through the full `prepareEvalPlan → runPreparedDense` pipeline
> confirming the last write wins — the latter two added by the final whole-branch review, which
> independently confirmed the compiler algorithm correct but found these two value-level paths
> untested by anything else in the slice). **Real observed sweep counts (not estimated): total =
> 3,832, accepted = 3,832, rejected = 0, 0 rejection categories — 100% bit-exact agreement between
> `runPreparedDense` and `evalScheduled` on every entry, both indexed environment values AND
> preparation warnings compared (the latter comparison also added by the final review — the original
> sweep compared only `.env`)**, pinned by a `#guard` on the exact triple. All 3 test-the-tester
> mutations (coefficient change, dropped term, reversed Float-sensitive fold order) were confirmed by
> executing both the original and mutated program through `evalScheduled` to actually break
> agreement, not assumed from the mutation's description. All three test modules registered in the
> default build target. Full `lake build` green (8,639 jobs, up from the 8,632 C3 baseline — the 4
> new library modules (`Eval/Report.lean`, `Plan/Prepared.lean`, `Plan/Compile.lean`,
> `Plan/Adapter.lean`) and 3 new test modules (`CompileTest`, `AdapterTest`, `DifferentialTest`) this
> slice adds; `Plan/Error.lean` and `Eval/Eval.lean` are modified, not added, so they don't change
> the job count — matching this section's own arithmetic exactly, unchanged by the final-review fix
> wave since it only added `#guard`/`run_cmd` lines to already-registered modules). One deviation
> from this section's plan text: the differential sweep's Gate claim ("every unsupported construct
> fails before `runDensePlan`") originally rested on the sweep's own consistency check, which the
> real `enumPrograms` corpus never exercises (0 of 3,832 entries are rejected) — the final review
> caught this and the Task 1 `#guard` above now directly demonstrates the claim instead.
>
> Commits: `1aab71e^..1790db8` (Task 1's `capabilityPreflight` and capability-row `CompileTest`
> fixtures, Task 2's `prepareEvalPlan` and `Plan/Prepared.lean` and the deterministic-slot/repeated-
> assignment `CompileTest` additions, Task 3's `pack`/`unpack`/`runPreparedDense` and
> `Eval/Report.lean` and `AdapterTest`, Task 4's alpha-renaming law and differential sweep and
> mutations and `DifferentialTest` and the three test-module lakefile registrations, and the
> final-review fix wave closing the four coverage gaps and one stale `AGENTS.md` reference above).

### A.9 C5 - canonical representation and codec

**Production files:** `Plan/Canonical.lean` and `Plan/Codec.lean`.

Only after C4 freezes semantic completeness, define canonical encoding:

- fixed magic bytes and independent wire/semantic versions;
- fixed constructor tags and semantic field order;
- length-prefixed arrays;
- unsigned canonical `Nat` and signed canonical `Int`;
- explicit big-endian binary64 bit patterns;
- preserved operation, term, factor, coordinate, and slot order;
- no names, warnings, bindings, proof objects, unordered maps, or backend metadata;
- rejection of nonminimal integers and trailing bytes.

Hash domain-separated semantic bytes with SHA-256. `PlanFingerprint` is an opaque 32-byte digest;
never use host `Hashable`. **Decide at the C4-to-C5 handoff** (A.11), before any A.9 work begins,
whether to take a small audited Lean SHA-256 dependency or implement it locally against published
test vectors — not as an implicit choice made by whoever happens to start C5. Do not silently choose
another algorithm.

`decodePlan` parses a wire envelope to `RawEvalPlan`, reports path/offset-bearing `PlanCodecError`,
calls `checkPlan`, and recomputes rather than trusts any persisted fingerprint.

**Tests:**

- golden bytes for a minimal plan and all admitted tags;
- standard SHA-256 vectors;
- encode/decode/check/run agreement;
- unknown/reserved tags, truncation, trailing bytes, and noncanonical integers;
- local and graph-invalid decoded payloads rejected by their owning checker;
- alpha-renaming changes bindings but not semantic bytes or fingerprint;
- every semantic field mutation changes bytes and normally the fingerprint;
- warnings, names, and backend metadata cannot enter the encoder.

**Gate:** representation round-trip preserves the already established Dense meaning, and no
malformed or unchecked payload is executable.

> **⏸️ DEFERRED 2026-08-07.** No consumer inside this process's own lifetime needs either fingerprint
> stability across restarts or serialized plan bytes — both were speculative future-proofing with no
> concrete consumer, surfaced and discarded during C5 plan authoring rather than built and later
> found unused. `PlanFingerprint`'s only real requirement — an in-process cache key — would be
> satisfied by `deriving Hashable` directly on the checked types (once verified to compile across
> the nested `RawEvalPlan`/`AssignPlan`/`TermPlan`/`ReadPlan`/`AffineMap` tree), with no new module,
> no canonical byte layout, and no SHA-256-vs-alternative decision needed at all — that `Hashable`
> addition is not landed either, absent an actual consumer to justify it now. `Plan/Codec.lean`'s
> wire envelope has no current consumer either: the one plausible reason (a live cross-process
> JAX/PyTorch backend needing serialized plans) would contradict `torch_compile/`'s already-
> established ahead-of-time codegen pattern for backend integration — if that architecture is ever
> adopted instead, Codec.lean's real shape should be driven by that boundary's actual requirements,
> not guessed here in advance. Wave C proceeds directly from C4 to C6 (A.10); this section is
> retained as a design record, not resurrected without a concrete triggering need.
>
> **Why the codec above was structured this way, for whoever revisits it.** Every structural rule
> in this section serves one of two goals, and neither goal disappears just because nothing
> currently needs the codec built — they're worth restating so a future reader doesn't have to
> re-derive them: **(1) canonical encoding** — one semantic value must produce exactly one byte
> sequence, which is what made a byte-derived fingerprint meaningful in the first place. Fixed
> constructor tags, fixed field order, length-prefixed arrays, and rejecting nonminimal integers
> all exist so no value has two valid encodings. Explicit big-endian float bit patterns exist so
> the same `Float` doesn't serialize differently on different machines — the wire-level analogue of
> why `ScalarConst.f64` already stores `UInt64` bits rather than a `Float` in memory. Preserving
> operation/term/factor/coordinate/slot order (never reordering "for convenience," per §9.3) exists
> because binary64 addition isn't associative — sorting terms because the underlying algebra is
> commutative would silently change results, the same failure mode the fold-order test fixtures
> throughout this Wave exist to catch. Excluding names/warnings/bindings/backend metadata from the
> encoder is what makes alpha-renaming invariant: two plans differing only in variable names must
> encode identically. Magic bytes plus independent wire/semantic versions exist so a decoder
> recognizes a format mismatch immediately rather than parsing garbage, and so a layout change and
> a vocabulary change are never conflated into one version bump. **(2) the raw/checked boundary
> discipline applied at the wire** — `decodePlan` calling `checkPlan` and recomputing rather than
> trusting a persisted fingerprint is the same rule C2's `checkAssign` and C3's `checkPlan` already
> enforce in memory (nothing executes without going through its checker), just extended to bytes
> that arrived from outside the process, which are untrusted input by construction. If C5 is ever
> revisited, preserve both goals even if the concrete encoding details change.

### A.10 C6 - adversarial audit and handoff

1. Run the complete local, graph, compiler, adapter, and codec mutation matrices.
2. Add corpus cases only where coverage guards show a missing dimension.
3. Audit imports:
   - `Dense.lean` imports neither `Compile` nor legacy `Gather`/`Contract`;
   - `Compile.lean` does not import `Dense` or `Canonical`;
   - `SizeInfer.lean` imports no plan module;
   - `Canonical.lean` imports no boundary module;
   - codecs expose no unchecked constructor.
4. Search semantic IR for `String`, `UID`, functions, callbacks, backend types, proof representation,
   and unordered maps.
5. Confirm every validator has a corresponding mutation test and every admitted constructor has a
   Dense interpretation test.
6. Update `Eval/AGENTS.md`, root architecture documentation, and `LeanNCD.lean` public imports.
7. Run the complete build through Elan and report a skipped test module as failure.
8. Publish a capability manifest naming:
   - the exact semantic/wire versions;
   - accepted and rejected source constructs;
   - Law 1 corpus coverage;
   - extension points for scans and later backends.

**Gate:** Section 15.4 holds; the module graph matches A.2; Wave F and Wave G can consume checked
plan APIs without importing source compilation or legacy execution.

> **✅ DONE 2026-08-07.** Closed 5 real test-coverage gaps found by this task's own audit:
> `InputBindingError.storageMismatch` (new `AdapterTest.lean` fixture), `PlanCompileCause.shape`
> exercised through `prepareEvalPlan` (new `CompileTest.lean` fixture), non-empty warnings surviving
> a later failure (new `CompileTest.lean` fixture, a second statement's unsized-axis failure
> carrying the first statement's warnings forward unchanged), `PlanRunCause.execution` documented
> and exercised directly (confirmed unreachable via the full `pack -> runPreparedDense` pipeline by
> 3 real construction attempts during plan authoring, not merely asserted), and 4
> `CapabilityError` sub-cases (`iterAt`/`iterNext`/`axiswise`/`min`) newly tested through the real
> `capabilityPreflight` rather than only through the C0-era test-only classifier. Documented, rather
> than closed, 2 confirmed dead-code findings: `ScalarConst.f32`/`.bool` and 4 `Compile.lean` helper
> branches (`plainStmtOrFail`/`assignPartsOrFail`/`freeUidOrFail` and the `.iverson`/`.unaryFn`
> factor-loop arms) are unreachable post-preflight by construction, now with doc comments explaining
> why rather than left silently unexplained. Made `Eval/Plan/` discoverable: `Eval/AGENTS.md` and
> `AGENTS.md` both gained a `Plan/` subsystem entry, and `LeanNCD.lean` gained
> `import LeanNCD.Eval.Plan.Adapter` (plus a header mention) so `import LeanNCD` alone now reaches
> the checked-plan API — full `lake build` after that change reported exactly 8,639 jobs, matching
> the C4 baseline exactly (confirming the added import path creates no new compilation job, only a
> second route to already-compiled artifacts). Published
> [`wave_c_capability_manifest.md`](wave_c_capability_manifest.md): the exact semantic/wire versions
> (`admittedVersion = 1`; no wire version, C5 deferred), the accepted/rejected source constructs (all
> 11 `CapabilityError` categories, with `unsupportedDtype`/`dynamicShape` confirmed structurally
> unreachable from the current AST — no dtype field on `Decl`, no value-dependent-shape constructor
> on `IdxExpr` — not merely unimplemented), the real counted Law 1 corpus coverage (3,832 entries,
> 3,832 accepted, 0 rejected, 100% bit-exact agreement on both indexed environment values and
> preparation warnings, pinned by `DifferentialTest.lean`'s `#guard`), and the extension points
> (scans, other backends, C5) stated as what is not yet supported and why rather than as a roadmap
> commitment. The manifest also records the two audit findings this task's own work confirmed clean:
> the module import graph matches A.2 exactly (`Dense.lean` imports neither `Compile.lean` nor legacy
> `Gather`/`Contract`; `Compile.lean` does not import `Dense.lean`; `SizeInfer.lean` imports no plan
> module), and the checked semantic IR (`AffineMap`/`ReadPlan`/`TermPlan`/`AssignPlan`/`RawEvalPlan`/
> `CheckedAssignPlan`/`CheckedEvalPlan`) carries no `String`, `UID`, callback/function, or
> unordered-map field anywhere — confirmed by reading every one of those types directly, not assumed
> by analogy. Full `lake build` green (**8,639 jobs**, unchanged from the C4 baseline: this slice
> adds no new production or test modules, only doc comments, test fixtures inside already-registered
> modules, `AGENTS.md`/`LeanNCD.lean` documentation edits, and this papers update, none of which
> register a new compilation unit). **Section 15.4's Gate holds in its reduced form**, per its own
> A.9 deferral note: `prepareEvalPlan`/`runPreparedDense` agreement with `evalScheduled` (or a typed
> rejection) is demonstrated for the whole declared fragment by the differential sweep above; the
> canonical-round-trip clause remains out of scope until C5 is built. This completes Wave C
> (C0-C4, C6; C5 deferred, see A.9).
>
> Commits: `8761328^..ded704c` (Task 1's 5 coverage-gap fixtures and 2 dead-code doc comments, Task
> 2's `Plan/` discoverability edits, and Task 3's capability manifest).

### A.11 Landing sequence and review boundaries

Prefer these reviewable commits:

```text
C0  contract fixtures and law matrix
C1  signature-driven shape inference
C2a local kernel data + checkAssign
C2b runDenseAssign + hand-computed kernel tests
C3a raw graph + checkPlan
C3b runDensePlan + manual composition tests
C4a source specialization + typed preflight
C4b pack/unpack + end-to-end differential matrix
C6  audit, manifest, and documentation
```

(C5a/C5b — canonical bytes + fingerprint, codec + malformed-input tests — are omitted: C5 is
deferred, see A.9.)

C1 may proceed beside C2 after C0. Otherwise land in dependency order. Do not combine C2 through C4:
local semantics, graph composition, and source residualization need distinct reviews and distinct
failure localization. Do not begin Wave F or Wave G until C4's differential gate passes. C5 is
deferred (A.9), so C6 follows C4 directly.

### A.12 Implementation-time stop conditions

Stop and revise this proposal if:

- a local operation needs a source name or UID to execute;
- `checkPlan` cannot compose `checkAssign` and instead duplicates local validation;
- graph execution needs to reinterpret source syntax;
- `prepareEvalPlan` cannot determine concrete shapes from `InputSignature`;
- two backend interpretations would assign different meanings to one closed tag;
- exact Dense agreement requires changing `evalScheduled`;
- canonical encoding needs a precedence rule between contradictory redundant fields;
- representation concerns must be imported by the compiler or worker;
- a scan, scatter, predicate, unary factor, or nonlinearity is needed merely to make the initial
  architecture usable.

These are architecture failures or scope changes, not reasons to add fallback execution, optional
mega-record fields, or silent defaults.

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
- Topos Institute,
  [AI Planning with C-Sets](https://topos.institute/blog/2022-09-20-ai-planning-csets/), 2022.
- Evan Patterson, Owen Lynch, and James Fairbanks,
  [Categorical Data Structures for Technical Computing](https://arxiv.org/abs/2106.04703), 2022.
- David I. Spivak,
  [Functorial Data Migration](https://doi.org/10.1016/j.ic.2012.05.001), 2012.
- Neil D. Jones, Carsten K. Gomard, and Peter Sestoft,
  [Partial Evaluation and Automatic Program Generation](https://www.cambridge.org/core/books/partial-evaluation-and-automatic-program-generation/500C671429CC993BE6A5E30C261B943F).
- [MLIR Linalg dialect](https://mlir.llvm.org/docs/Dialects/Linalg/).
- John C. Reynolds,
  [Definitional Interpreters for Higher-Order Programming Languages](https://dl.acm.org/doi/10.1145/800194.805852),
  1972.
- Matt Noonan, [Ghosts of Departed Proofs](https://doi.org/10.1145/3242744.3242755), 2018.
- Amir Pnueli, Michael Siegel, and Eli Singerman,
  [Translation Validation](https://doi.org/10.1007/BFb0054170), TACAS 1998.
- John C. Mitchell,
  [Representation Independence and Data Abstraction](https://doi.org/10.1145/512644.512669),
  POPL 1986.
- [Haskell `mapAccumL`](https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Data-List.html#v:mapAccumL).
- [JAX `lax.scan`](https://docs.jax.dev/en/latest/_autosummary/jax.lax.scan.html).
- Guy E. Blelloch,
  [Prefix Sums and Their Applications](https://www.cs.cmu.edu/~guyb/papers/Ble93.pdf).
