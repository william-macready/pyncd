# Genuine binary32 execution on extensible typed-tensor foundations

**Status:** implementation plan; not yet implemented.

This is one reviewable vertical slice and the first consumer of an extensible dtype foundation: a
source program can declare a homogeneous
binary32 tensor graph, compile scan-free identity assignments into a checked `EvalPlan`, execute
sum/max/min contractions with Lean 4.30's native `Float32`, and receive native `Array Float32`
materialized outputs through a named adapter. It is deliberately not a plan for every operation
that currently works with Float64 storage, nor does it implement complex execution. The source,
storage, and adapter shapes introduced here must nevertheless admit later `complex64` and
`complex128` extensions without adding a parallel AST constructor and full adapter stack per dtype.

## 1. Decision and slice boundary

### 1.1 The non-negotiable semantic decision

An `f32` signature means **IEEE-754 binary32 storage and an independently rounded binary32 result at
every primitive arithmetic operation**. It never means “run the existing binary64 `Float` worker and
round only its final output.” In this slice:

- stored values are `Float32`, not `Float`;
- scalar constants are decoded from `ScalarConst.f32 UInt32` with `Float32.ofBits`;
- factor multiplication and reduction/term addition, minimum, and maximum execute directly through
  `Float32` operations;
- zero padding and Iverson values are native binary32 zero/one;
- equality in tests is by `Float32.toBits`, not `BEq Float32` (which has IEEE NaN and signed-zero
  behavior and is not propositional equality);
- the existing Float-backed `DenseTensor`, reference evaluator, and `runPreparedDense` remain
  binary64/Float-backed-Boolean APIs and must reject, not reinterpret, an `f32` checked plan.

Lean 4.30 does provide a native `Float32` carrier, arithmetic, comparisons, bit conversion,
`Float.toFloat32`/`Float32.toFloat`, and the transcendental functions needed by later slices. Its
operations are opaque to kernel reduction and execute through native runtime primitives. That is
sufficient for this executable backend, whose existing `Float` operations have the same runtime
character; it does mean fixture values must be observed through compiled execution rather than
proved by `rfl`.

### 1.2 Exact admitted fragment

The slice admits a program only when all non-Boolean tensors used by the scheduled graph select one
real precision. Boolean tensors are semantic tags over the graph's selected real carrier, not a
third independently chosen carrier:

| Mode | Source declarations | Runtime carrier | Admitted operations in this slice |
|---|---|---|---|
| Float64 storage (unchanged) | `tensor`, `linear`, undeclared external, plus optional `predicate` | `Array Float` (`bool` is a semantic tag) | all currently admitted operations |
| Float32 storage | `tensor f32 ...` for every real external and produced name, plus optional `predicate` | `Array Float32` (`bool` is a semantic tag) | scan-free, non-scatter `.assign`; identity nonlinearity; plain reads and Iverson factors; real `sum`/`max`/`min`; Boolean min/max algebra; affine reads and zero padding |

A graph is **single-real-precision by construction** in this slice. It may contain f64 plus Boolean
tensors or f32 plus Boolean tensors, but never both f64 and f32. Boolean declarations do not select
the precision: they use `Float` values in an f64 graph and `Float32` values in an f32 graph, retaining
the current min/max algebra and exact zero/one identities in the selected carrier. Existing Boolean
tensors are not validated or coerced to binary values—values such as `0.25` and `0.75` continue to
flow through literal min/max. A bool-only graph defaults to f64, preserving current behavior. The
compiler rejects a graph whose used real external/produced names contain both f32 and f64 as
`CapabilityError.unsupportedDtype`; it never inserts a cast. Unused declarations do not select
precision. An undeclared external defaults to f64, as today, so every real external in an f32 graph
must be declared `tensor f32`.

The source spelling is `tensor f32 X(i, j), Y(i)`. Add a source-layer `TensorElementType` and the
single extensible AST constructor `Decl.typedTensor TensorElementType String (List AxisSpec)`;
this slice adds only `TensorElementType.f32`. The existing `Decl.tensor` constructor and
`tensor X(i, j)` syntax retain their meaning. Later complex slices extend `TensorElementType`
rather than adding `tensorComplex64`, `tensorComplex128`, and another exhaustive `Decl` migration
for each type.

`Decl.typedTensor .f32` is tensor-bearing everywhere `Decl.tensor` is: declaration environments,
rank checking, UID traversal, scheduling, and routed categorical compilation. The categorical branch
may erase the `.f32` annotation because it changes real-number representation, not the expression's
scalar domain. That erasure rule is explicitly **not** generalized to future complex declarations:
complex values are not real-valued storage variants, so a later complex slice must either extend the
categorical scalar semantics or reject complex declarations before categorical lowering.

The following valid source constructs are rejected specifically for binary32 in this slice:

- pointwise and axiswise nonlinearities;
- inline unary factors;
- top-level scatter;
- every scan form, including scan-local scatter;
- any used f64/implicit-f64 tensor in the same graph.

Those restrictions are checked before plan construction. Hand-built raw plans receive the same
protection: the f32 graph checker accepts assignment steps only; the existing block, scan, scatter,
and nonlinearity checkers retain their current Float-backed admission rules.

### 1.3 Explicitly deferred slices

This plan does **not** claim complete f32 support. F32-B, F32-C, F32-D, and F32-JAX are required
follow-on slices; “deferred” describes sequencing and review boundaries, not optional project scope.
Only mixed-real-precision conversion remains contingent because the project invariant says f32 and
f64 tensors do not coexist in one graph.

1. **F32-B — unary and nonlinear math.** Add native `Float32.log/exp/sin/cos/sqrt`, pointwise
   functions, and axiswise row algorithms. This needs a binary32 domain-error payload and separate
   numerical fixtures for each approximation/order; routing through current `Float` helpers would
   be false f32.
2. **F32-C — scans and scan-state scatter.** Add native binary32 block and scan stores, snapshots,
   base overlays, state writes, and histories. This is separate because scan storage and write paths
   have their own checker/evidence and recurring geometry-risk surface.
3. **F32-D — top-level scatter.** Add native binary32 fill and placement execution, after defining
   a binary32 oracle independent of the legacy binary64 scatter evaluator.
4. **F32-E — contingent explicit conversions.** No f32↔f64 plan step is planned under the
   single-real-precision invariant. If that invariant changes, conversions require a separate slice;
   mixed precision remains rejected rather than converted implicitly. Boolean tensors already follow
   the graph's real carrier and need no precision conversion merely to coexist with f32 or f64.
5. **F32-JAX.** Add a new evidence label and `jnp.float32` artifact/runtime only with bit-level
   differential evidence. The current experimental JAX boundary remains reference64-only and
   rejects f32 before candidate construction or Python emission.
6. **Complex-A — executable scalar contract.** Extend `TensorElementType`, `ScalarDType`,
   `ScalarConst`, and `TensorStorageKind` with `complex64` (two binary32 components) and
   `complex128` (two binary64 components). The installed Mathlib `Complex` is a pair of mathematical
   `Real`s, not a native machine-complex carrier, so define explicit executable `ComplexF32`/
   `ComplexF64` carriers. Admit sum-product first; complex min/max and ordering remain rejected until
   they receive explicit semantics. Decide separately whether Boolean tensors in a complex graph use
   real Boolean storage or the complex carrier's exact `0+0i`/`1+0i`; this plan's precision-neutral
   Boolean rule covers real f32/f64 graphs only.
7. **Complex-B — JAX and conversions.** Add dtype-indexed evidence and payloads (`UInt32` component
   pairs for `jnp.complex64`, `UInt64` component pairs for `jnp.complex128`), decide whether
   component-level bit equality is enforceable under XLA fusion/reassociation, and add explicit
   real/complex and precision conversions. `complex128` requires JAX x64; `complex64` does not.

Dynamic/value-dependent shapes and `recurMorphism`/`.scanPre` remain out of scope independently of
dtype. No plan codec exists, so there is no f32 wire-format work in this slice. The separate
Acset/Bridge route serializes and realizes the categorical presentation, not `EvalPlan` runtime
buffers; no claim of binary32 execution is added there.

## 2. Re-derived current boundary

The following was measured from the current tree rather than copied from an earlier plan.

### 2.1 Source and signatures

- `Decl` has `tensor`, `predicate`, `linear`, `axis`, and `iter`; there is no source dtype annotation.
  The surface grammar similarly has only `tensor ...` and `predicate ...`.
- `Decl.name`, `Decl.traverseAxes`, `buildDeclEnv`/declared-rank classification, and route-fragment
  declaration naming all match tensor-bearing constructors explicitly. A new constructor must be
  added to each exhaustive match; treating it as an axis declaration would silently remove it from
  rank and external-name authority.
- `ScalarDType.f32` and `ScalarConst.f32 UInt32` already exist. `TensorSignature` already carries
  `dtype`, and `PreparedPlan.materializedSignatures` already exposes complete ordered output
  signatures.
- `dtypeOfDecl` maps only predicates to `bool` and everything else to `f64`.
  `InputSignature.ofDenseInputs` is all-`f64`; its declaration-aware sibling changes only predicates
  to `bool`.
- `prepareEvalPlan` validates explicit input dtypes against declaration-derived dtypes, propagates
  complete signatures, and selects a destination algebra. Its `.f32` algebra arm currently falls
  back to the f64 algebra but is unreachable because signature admission rejects f32 first.
- `CapabilityError.unsupportedDtype` has no producer today. `CapabilityError` has sixteen
  constructors and `capabilityPreflight` currently has nine live producer families:
  `scatterOrAffineLhs`, `unsupportedLhsSlot`, `unsupportedNonlin`, `recurrenceOrCallback`,
  `noAdvancingAxis`, `multiAxisScatterLhs`, `scatterOptsNotAdmitted`, `predicateScatterDest`, and
  `unloweredScatterAssign`. Making binary32's deliberately deferred forms fail there makes
  `unsupportedDtype` the tenth live family and leaves six producer-less or structurally unreachable
  constructors.

### 2.2 Checking, constants, and execution

- `dtypeAdmitted` admits `f64` and Float-backed `bool`; `checkAssign` rejects f32 at the destination
  and every read. `admittedAlgebrasFor .f32` is empty.
- `constMatchesDtype` already recognizes matching `ScalarConst.f32`, but no checked algebra can carry
  one.
- `CheckedAssignPlan` stores only the raw assignment. Once an f32 checker exists, the evidence must
  also remember its execution mode so passing that evidence to the old Float worker cannot silently
  execute it as binary64.
- `DenseTensor` is exactly `shape : List Nat` plus `data : Array Float`. The local assignment,
  scatter, block, scan, nonlinearity, outer graph, named adapter, and `EvalReport` paths all use it.
  Replacing it globally with a sum would unnecessarily rewrite the independent legacy oracle;
  parameterizing the carrier while retaining `DenseTensor` as a Float alias avoids that sum and
  preserves current APIs.
- `constFloat` in `Eval/Plan/Dense.lean` decodes f64/bool and defaults every other constructor to
  `0.0`; its f32 arm is
  currently unreachable. The fold and gather functions are concretely typed to `Float`.
- Nonlinearity helpers and `UnaryOp.applyChecked` are concretely typed to `Float`. Scan state and
  scratch are also `DenseTensor`, and scatter allocates `Array Float`.
- `pack` validates shape/storage only because the concrete carrier is fixed today. `unpack` and
  `EvalReport` have no dtype-bearing runtime payload. Their container shells can be parameterized,
  but each public adapter still needs a storage-kind guard so no carrier is relabeled as another.

### 2.3 Experimental JAX boundary

The experimental JAX backend is explicitly reference64-only:

- `ExecutionEvidence.orderedReference64` is the only reference claim;
- support validation rejects a non-f64 destination or source, unsupported algebra, unary factor,
  context, and unsupported plan step before evidence;
- generated fixtures and Python runtimes encode `UInt64` bits and assert `np.float64`/`jnp.float64`;
- no JAX scan, scatter, nonlinearity, predicate, or f32 implementation exists.

After the f32 checker lands, JAX validation must revalidate an f32 assignment with the
storage-aware
checker and then report its existing located destination-dtype rejection. It must not misclassify
the plan as an invalid signature context, expose `orderedReference64`, generate `UInt64` payloads,
or emit Python.

### 2.4 Native Lean 4.30 evidence and discriminating values

The installed `leanprover/lean4:v4.30.0` source defines `Float32` as IEEE-754 binary32 and exposes
native add/subtract/multiply/divide, comparisons, min/max instances, transcendental functions,
`Float32.ofBits`, `Float32.toBits`, `Float.toFloat32`, and `Float32.toFloat`.

Two compiled probes through `.claude/skills/slice-plan/check-snippet.sh` observed:

| Expression | Native binary32 observation | Binary64 control |
|---|---:|---:|
| `16777216 + 1` | bits `1266679808` (`16777216`) | value `16777217` |
| left fold `((16777216 + 1) + -16777216)` | bits `0` (`+0`) | bits `4607182418800017408` (`1`) |
| `4097 × 4097` | bits `1266683904` (`16785408`) | exact integer `16785409` |
| `−1 / 0`, `1 / 0`, `−0` | `4286578688`, `2139095040`, `2147483648` | n/a |

These are the required numerical fixtures. A final-only cast cannot pass the reduction-order case:
binary64 computes `1`, whose conversion to binary32 is still `1`, while native per-add binary32
computes `+0`.

## 3. Architecture and invariants

### 3.1 Source dtype authority

Define `TensorElementType` and `TensorStorageKind` in `DSL/Ast.lean`, where both the source pipeline
and evaluator layers can depend on them without a reverse import. Add `TensorElementType.f32` and
`Decl.typedTensor`. Extend only the existing tensor-bearing cases:

`TensorElementType` derives `DecidableEq`, `Repr`, `Lean.ToExpr`, and `Inhabited`, matching the
requirements imposed by `Decl` and `tlprog!` quotation. `TensorStorageKind` derives
`DecidableEq`, `BEq`, `Repr`, and `Inhabited` because it appears in checked evidence and closed
diagnostics.

- syntax/elaboration produces it from `tensor f32`;
- UID traversal preserves it;
- declaration environment and rank checks classify it exactly like `tensor`;
- route-fragment naming and the categorical compiler preserve the same shape/routing semantics;
- `dtypeOfDecl` maps `.typedTensor .f32` to `ScalarDType.f32`;
- the legacy reference entry rejects a scheduled graph that uses it before allocating or evaluating
  any tensor.

Define a reusable per-name `storageConstraintOfDecl : Option Decl → Option TensorStorageKind` in
`DSL/Ast.lean` next to `TensorStorageKind`:
ordinary/linear/undeclared real names contribute `.float64`, `.typedTensor .f32` contributes
`.float32`, and predicates contribute no constraint. Build the schedule-wide analysis over
`orderedExternalNames sched.stmts` followed
by every name in `sched.stmts.flatMap ScanStmt.writes` (not `ScanStmt.outputs`, which omits
recurrence-only scratch) in `DSL/Pipeline/ScheduledValidation.lean`. In this slice it has
`.float64` and `.float32`
cases; later complex slices add `.complex64` and `.complex128`. Real declarations contribute a
constraint: `.typedTensor .f32 → some .float32`, while `tensor`, `linear`, and undeclared real names
contribute `some .float64`. `predicate` contributes no precision constraint. The first conflicting
pair of real constraints is rejected; no real constraint means `.float64`, preserving bool-only
behavior. Unused declarations do not participate. `prepareEvalPlan` and `evalScheduled` consume this
schedule-wide derivation. Direct legacy entries (`evalAssignDtypedSeeded`, `evalPlain`,
`evalStmtSliceSeeded`, and `evalScan`) have no complete `ScheduledProgram`; they apply the shared
per-name classifier to their destination/read/write names through the already available declaration
environment rather than importing `ScheduledValidation.lean`. This placement is required because
`ScheduledValidation → Structural → Eval.Contract`; importing it from `Eval/Contract.lean` would
create a cycle. Carrier-specific signature constructors also have no schedule and
therefore consume the shared per-name constraint directly against their explicitly selected carrier;
in particular, a predicate-only Float32 input map is valid rather than defaulting itself to Float64.
Do not duplicate declaration classification in the compiler and adapter.

The legacy rejection is enforced at every dtype-aware public door, not only at `evalScheduled`.
`evalScheduled` performs the storage-kind check immediately after `validateScheduled` and before shape
inference or environment lookup. `evalAssignDtypedSeeded` checks the destination and every named
read factor before gathering; `Combine` selection is total and has no observable ordering claim.
`evalAssignDtyped`, `evalPlain`, and scheduled
execution inherit that deepest guard. Test both an f64 destination reading an f32-declared source
and an f32 destination reading an f64 source; a predicate alongside either precision is not a
conflict. A dual-invalid scheduled fixture that contains f32 and is also unsized/missing-input must
report the dtype error, making the “before shape or environment lookup” order observable.

The binary32 capability pass traverses top-level scheduled statements in source order. A scan or
scatter is rejected as an unsupported outer step kind; this plan makes no claim about precedence
against an independently invalid body. Within a plain assignment, nonlinearity is checked before
factors (unary). The dual-invalid fixture `f32BadOrderProg`
contains a pointwise destination and an inline unary read in the same plain assignment; it must
report the nonlinearity. The fixture distinguishes the two outcomes, so the ordering claim is
testable.

Use these stable payloads rather than ad hoc prose at each throw:

| Boundary | Required error |
|---|---|
| first used real name differing from the graph's selected precision | `CapabilityError.unsupportedDtype "{name}: mixed f32 and f64 tensor precision"` |
| f32 scan or scatter | `unsupportedDtype "{name}: f32 scan"` / `"{name}: f32 scatter"` |
| f32 nonlinearity | `unsupportedDtype "{name}: f32 nonlinearity"` |
| f32 inline unary | `unsupportedDtype "{name}: f32 unary factor {termIndex}:{factorIndex}"`, where `factorIndex` is the original all-factor index |
| direct raw f32 unary assignment | new `PlanError.unaryNotAdmittedForDtype termIndex factorIndex .f32` |
| direct raw mixed signature table | new `PlanError.mixedStorageKinds slot firstDtype actualDtype` |
| direct raw f32 non-assignment step | new `PlanStepError.f32UnsupportedStep stepIndex kind`, with a closed `PlanStepKind` rather than a string |
| direct raw f32 block, including zero-step/all-input | new `BlockError.storageKindNotAdmitted .float32` |
| wrong worker | new `PositionalInputError.storageKindMismatch expected actual` |
| wrong named input adapter | new `InputBindingError.storageKindMismatch expected actual` |
| wrong result adapter / prepared runner | new `PlanRunCause.storageKindMismatch expected actual` |
| plan-level JAX evidence | new `JaxExecutableValidationError.unsupportedStorageKind actual` |
| plan-level JAX rendering | new `JaxCodegenError.unsupportedStorageKind actual` |
| legacy source evaluator | new `EvalError.unsupportedDtype name` |

For Task 2 fixture 12 below, used-name order is `X` (ordinary/undeclared, hence f64) then `Y` (f32),
so the required mixed-storage payload names `Y`; reversing a declaration-list scan would name `X`
and fail. For Task 2 fixture 4, an Iverson precedes the unary read, so the required factor index is
1 rather than the filtered-read index 0.

### 3.2 Checked evidence and algebra

Refactor the assignment checker around one private core parameterized by storage kind:

- existing public `checkAssign` retains the Float-backed policy and still rejects f32;
- new public `checkAssignF32` requires the graph storage kind `.float32`; permits `.f32` and `.bool`
  destinations/sources; requires an f32 algebra for an f32 destination or the existing Boolean
  algebra for a bool destination; and rejects inline unary;
- both preserve the current shape, partition, affine, policy, and all-factor index checks unchanged;
- `CheckedAssignPlan` records `storageKind`, set only by those two checkers.

Add f32 sum-product and tropical algebras using `ScalarConst.f32` constants:

| Algebra | factor op/id | reduction and term op/id |
|---|---|---|
| sum | multiply / `0x3f800000` | add / `0x00000000` |
| max | multiply / `0x3f800000` | max / `0xff800000` |
| min | multiply / `0x3f800000` | min / `0x7f800000` |

The compiler selects the f32 version from destination dtype and aggregation. For a Boolean
destination it retains `admittedAlgebraBool`; the selected scalar runtime decodes
`ScalarConst.bool` as native Float32 zero/one in an f32 graph and as Float zero/one in an f64 graph.
`constMatchesDtype` remains the final defense against cross-tag identities.

At graph level, define `storageConstraintOfDtype` and `deriveStorageKind` explicitly:

- `.f64 → some .float64`;
- `.f32 → some .float32`;
- `.bool → none`, so Boolean signatures inherit rather than select the graph carrier;
- an empty or bool-only signature table defaults to `.float64`;
- a table with f64 plus bool is `.float64`;
- a table with f32 plus bool is `.float32`;
- a table containing f32 and f64 is a located `PlanError.mixedStorageKinds` carrying the first
  conflicting real slot and both concrete real dtypes.

Add successful raw `[f64, bool]` and `[f32, bool]` graph fixtures so an implementation that compares
concrete dtypes, or permanently maps bool to Float64 storage, breaks a fixture. Keep storage
classification separate from operation capability: future complex dtypes can share generic tensor
plumbing while rejecting operations such as min/max that have no declared complex semantics.

`checkPlan` records this storage kind in `CheckedEvalPlan`. For `.float32` it accepts only `.assign`
and calls `checkAssignF32`; any other step reports `PlanStepError.f32UnsupportedStep` with the
original outer step index and step kind. `f32UnsupportedStepOrder` is a two-step fixture with a
valid f32 assignment followed by a pointwise node; it must report index 1, distinguishing original
graph indexing from a filtered assignment index.

The closed `PlanStepKind` diagnostic payload derives `DecidableEq`, `BEq`, `Repr`, and
`Inhabited`, matching `PlanStepError`'s existing derived interfaces.

The existing `checkAssign`, `checkPlanBlock`, `checkScatter`, `checkScanPlan`, and nonlinearity
checkers remain Float-backed. This is intentional: it keeps direct block/scan/scatter construction
from acquiring evidence for an operation with no f32 worker. No global relaxation of
`dtypeAdmitted` is allowed.

### 3.3 Native binary32 worker

Refactor only the carrier shell to `DenseTensorOf α` with `shape : List Nat` and
`data : Array α`, preserving `DenseTensor` as an alias for `DenseTensorOf Float`, then add
`DenseTensor32` as an alias for `DenseTensorOf Float32`. Existing Float callers and behavior remain
source-compatible. Because a Lean `abbrev` does not create aliases for the original structure's
generated names, explicitly preserve `DenseTensor.mk` as a forwarding abbreviation and
`DenseTensor.shape`/`DenseTensor.data` as forwarding definitions whose `self` parameter is explicitly
typed as `DenseTensor` (an abbreviation of the generic projection is not usable through field
notation). Existing direct constructor/projection users must compile unchanged.

Inside `Eval/Plan/Dense.lean`, extract a narrow explicit, fallible, **private**
`ScalarKernelOps α` record and a private assignment-only shared traversal. The record owns constant
decoding, zero/one, application of an **admitted**
`ScalarBinOp`, and a carrier-specific unary callback. It is data passed to the worker, not a global
typeclass. Unsupported operations return a typed error; the interface is not a total
`ScalarBinOp → α → α → α` that would force a future complex carrier to invent min/max semantics.

Instantiate it separately for `Float` and `Float32`. The Float unary callback delegates to the
existing `UnaryOp.applyChecked` and preserves its UInt64 diagnostic payload. The Float32 callback is
fail-loud if reached, while checked f32 evidence makes unary reads unreachable in this slice. Define
private `denseValueAtWith ops` in the same module, retain the existing private Float
`denseValueAt` wrapper used by scatter, and define the public checked-only local entries
`runDenseAssignAt32`/`runDenseAssign32` there beside their Float siblings. No raw `AssignPlan` plus
arbitrary scalar-ops entry is exported. `Eval/Plan/Dense32.lean` contains only the graph-level
`runDensePlan32`, dispatching through `runDenseAssignAt32`; this module split avoids both duplicated
traversal and a new unchecked public execution door. A future complex slice extends the private
kernel seam in `Dense.lean` and exposes only checked carrier-specific workers, so it can provide
add/multiply and complex unary operations selectively without implementing min/max.

Both operation records decode `ScalarConst.bool` into their own carrier's exact zero/one. Thus a
Boolean destination/source in an f32 graph never forces a Float buffer or a conversion; it uses the
same `DenseTensorOf Float32` store as the graph's real tensors.

The binary32 instantiation must:

1. validate source shape and storage size;
2. gather a native `Float32`, using native zero for out-of-bounds;
3. convert an Iverson predicate directly to native one/zero;
4. fold factors left-to-right with native multiplication;
5. fold reduction coordinates left-to-right in existing row-major order with the selected native
   add/min/max;
6. fold terms left-to-right with that same reduction operation;
7. return `Array Float32`.

Coordinate enumeration and affine integer mapping are shared from `Coordinates.lean`; arithmetic
implementations and constant decoders remain explicit per carrier. Task 2 already made the existing
deepest public entries `runDenseAssignAt` and `runDensePlan` require `.float64` before allowing f32
evidence to exist. This task adds the symmetric requirement that `runDenseAssignAt32` and
`runDensePlan32` receive `.float32`; `runDenseAssign32` and `runDenseAssign` are empty-context
wrappers over their guarded entries. Guarding only wrappers is insufficient because direct callers
can invoke `runDenseAssignAt`.

Add an assignment-only `runDensePlan32` in the outer graph module. It requires the checked plan's
stored kind to be `.float32`, validates input arity/shape/storage against the checked signature table,
accepts `.f32` and `.bool` signatures in that store, dispatches only `.assign` evidence, and writes
native f32 tensors into the positional store. The existing `runDensePlan` requires `.float64` and
continues to accept `.f64` and `.bool` signatures. Both fail before reading an input on
storage-kind mismatch.

Do not generalize nonlinearities, scans, scatter, or all evaluator APIs in this slice. Only the
shape/storage carrier, assignment traversal, and named-environment/report shells become parametric.
This is the minimum shared layer justified by the known f32/f64/complex64/complex128 family; the
arithmetic records remain concrete and reviewable.

### 3.4 Named input and materialized output

Add `NamedDenseEnvOf α := HashMap String (DenseTensorOf α)` and `EvalReportOf α`, preserving
`NamedDenseEnv` and `EvalReport` as Float aliases. Define `NamedDenseEnv32` and `EvalReport32` as
Float32 aliases, then add binary32 `pack32`, `unpack32`, and `runPreparedDense32`. Reuse checked
prepared bindings and materialized-name/signature resolution; do not duplicate name/slot ordering
logic. Explicitly preserve `EvalReport.mk`, `EvalReport.env`, and `EvalReport.warnings` as forwarding
members because changing a structure to an alias does not synthesize those old names: `mk` may be an
abbreviation, while the projection wrappers must be definitions with an explicit `EvalReport`
parameter so field notation continues to elaborate.

The existing Float-backed `pack`, `unpack`, and `runPreparedDense` also gain an explicit
`.float64` storage-kind check before shape, storage, result-arity, or publication work. Otherwise a
direct caller could pair an f32 prepared plan with `Array Float` values and relabel those buffers
through the old adapter without invoking a numeric worker. The f32 siblings perform the symmetric
`.float32` check.

`pack32` requires every required input signature to be f32 or bool and validates shape and native
buffer length. `unpack32` requires the result-store arity to equal the plan signature table and every
materialized signature to be f32 or bool before publishing anything. The result starts from the
original f32-carrier environment and applies materialized bindings in schedule order, preserving
the existing last-write-wins behavior for repeated names. Warnings survive success and every
failure exactly as in `runPreparedDense`.

Add `InputSignatureBuildError` in `Eval/Plan/Signature.lean` with
`declaration (cause : CompileError)` and
`storageKindMismatch (name : String) (expected actual : TensorStorageKind)`. Change
`InputSignature.ofDenseInputsForDecls` and add `InputSignature.ofDenseInputs32ForDecls`, both
returning `Except InputSignatureBuildError InputSignature`. Each rebuilds the duplicate-safe
declaration environment **before** examining input carriers, preserving
`CompileError.duplicateTensorDecl` under `.declaration` as the first error for a dual-invalid call.
`InputSignatureBuildError` derives `Repr`, `DecidableEq`, `BEq`, and `Inhabited`; `Repr` is
load-bearing for the existing `repr e` call sites in `DifferentialTest` and `AdapterTest`, which
remain source-compatible and are compiled by Task 4's targeted/regression gates.
The Float constructor accepts ordinary/linear/undeclared real names and predicates but rejects a
supplied name declared `.typedTensor .f32` as expected `.float32`, actual `.float64`. The Float32
constructor requires every supplied real name to resolve to `.typedTensor .f32`, also accepts
predicates, and rejects ordinary/linear/undeclared real names as expected `.float64`, actual
`.float32`. Successful results carry `.f64`/`.f32` or `.bool` signatures according to the
declaration.
There is no widening constructor from `DenseTensor` and no narrowing constructor from arbitrary
`Float`: callers construct `Float32` values (preferably from canonical bits) explicitly.

### 3.5 Sibling audit: every execution door

This change is not in the recurring write-geometry family: it changes no write-map predicate.
It does create a new recurring risk family—checked f32 evidence reaching a Float worker—so Tasks
1–5 must collectively complete this case × entry-point table from the implemented call graph:

| Checked case | Float local/graph worker | f32 local/graph worker | Float/f32 named adapter | JAX candidate/render | Legacy evaluator |
|---|---|---|---|---|---|
| f64/bool assignment in an f64 graph | required | forbidden | Float required / f32 forbidden | existing policy | required |
| f32/bool assignment in an f32 graph | forbidden | required | Float forbidden / f32 required | forbidden | forbidden |
| f32 pointwise/axiswise | no evidence | no evidence | no prepared plan | no candidate | forbidden |
| f32 scatter | no evidence | no evidence | no prepared plan | no candidate | forbidden |
| f32 block/scan | no evidence | no evidence | no prepared plan | no candidate | forbidden |
| mixed f32 and f64 signatures (bool ignored for precision selection) | no evidence | no evidence | no prepared plan | no candidate | forbidden |

Every “forbidden” execution cell has a fail-loud fixture. No cell may silently convert or be
classified only by a caller convention. Audit these sibling entry points even when they
do not appear in a task diff: `runDenseAssignAt`, `runDenseAssign`, `runDenseScatter`, `runDenseBlock`,
`runDensePointwise`, `runDenseAxiswise`, `runDenseScan`, `runDensePlan`, `pack`, `unpack`,
`runPreparedDense`, `evalAssignDtypedSeeded`, `evalAssignDtyped`, `evalPlain`,
`evalStmtSliceSeeded`, `evalScan`, `evalScheduled`, `validateAffineTable`, `validateEinsum`,
every plan-level candidate conversion, `renderInputConstants`, and both experimental render modes.

The JAX gate is plan-level as well as per-assignment. Every candidate and renderer entry checks
`CheckedEvalPlan.storageKind = .float64` before iterating nodes. This is load-bearing for an
all-input, zero-step f32 plan: per-node support checks are vacuous, and the current empty evidence
fold yields `orderedReference64`. A dedicated empty-plan fixture must reject before candidate
construction, evidence aggregation, or Python emission. Expressing the gate in storage/dtype terms,
rather than as an f32 special case, gives future complex plans the same fail-loud boundary until
dtype-indexed JAX evidence exists.

## 4. Implementation tasks

Task boundaries follow independent rejection/rollback surfaces: source/legacy admission, checked
evidence and specialization, native execution, the named adapter, and external support gates/docs.

### Task 1 — Add explicit source f32 and close the legacy evaluator boundary

**Files**

- `leanncd/LeanNCD/DSL/Ast.lean`
- `leanncd/LeanNCD/DSL/Syntax.lean`
- `leanncd/LeanNCD/DSL/Elab.lean`
- `leanncd/LeanNCD/DSL/TraverseAxes.lean`
- `leanncd/LeanNCD/DSL/Pipeline/Types.lean`
- `leanncd/LeanNCD/DSL/Pipeline/Structural.lean`
- `leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean`
- `leanncd/LeanNCD/DSL/Pipeline/RouteFragments.lean`
- `leanncd/LeanNCD/Eval/Error.lean`
- `leanncd/LeanNCD/Eval/Eval.lean`
- `leanncd/LeanNCD/Eval/Scan.lean`
- `leanncd/LeanNCD/Eval/Contract.lean`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/LeanNCD/Eval/Plan/Signature.lean`
- `leanncd/test/DSL/AstTest.lean`
- `leanncd/test/DSL/SyntaxTest.lean`
- `leanncd/test/DSL/ParseProgramTest.lean`
- `leanncd/test/DSL/Pipeline/StructuralTest.lean`
- `leanncd/test/DSL/TraverseAxesEquiv.lean`
- `leanncd/test/DSL/TraverseAxesSpike.lean`
- `leanncd/test/DSL/Pipeline/RouteFragmentCorpusTest.lean`
- `leanncd/test/Eval/EntryTest.lean`
- `leanncd/test/Eval/ContractTest.lean`
- `leanncd/test/Eval/ScanTest.lean`
- `leanncd/test/Eval/Plan/ContractTest.lean`
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`
- `leanncd/test/Eval/Plan/SignatureTest.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean`
- `leanncd/test/Eval/PropertyOracle/Compare.lean`

**Implementation**

1. Add `TensorElementType.f32`, `Decl.typedTensor`, and `tensor f32` syntax. Update every exhaustive
   tensor-bearing declaration match. Preserve all existing `Decl.tensor` construction and `tensor`
   elaboration results byte-for-byte. Keep dtype parsing centralized so future complex types extend
   `TensorElementType` rather than `Decl`.
2. Add `storageConstraintOfDecl` in `DSL/Ast.lean` and the schedule-wide storage-kind derivation in
   `DSL/Pipeline/ScheduledValidation.lean`. Invoke the schedule-wide form from `prepareEvalPlan` to
   reject mixed f32/f64 schedules and from `evalScheduled` to reject every f32 schedule. Direct
   legacy evaluator entries use the per-name classifier and their declaration environment, avoiding
   the existing `ScheduledValidation → Structural → Eval.Contract` dependency cycle. Preserve
   unused-declaration behavior, make predicates precision-neutral, and retain the undeclared-real
   and bool-only f64 defaults.
   Homogeneous f32 is not admitted by checked compilation in this task: immediately after storage
   derivation, `prepareEvalPlan` reports the temporary
   `CapabilityError.unsupportedDtype "f32 execution not yet admitted"` before capability preflight,
   signature validation, specialization, or plan construction. Task 2 removes this broad stop only
   after checked evidence and Float-worker guards exist. The schedule-level stop is required even
   when an f32 destination has no real external input for Step B to inspect.
3. Reject f32 at `evalScheduled` before shape/environment work and at
   `evalAssignDtypedSeeded` before algebra selection/gathering. `evalAssignDtyped` and
   `evalPlain`'s assignment arm inherit that deepest guard. Add entry guards to `evalPlain`,
   `evalStmtSliceSeeded`, and `evalScan` as well: their scatter/scan paths otherwise bypass
   `evalAssignDtypedSeeded`, and each public entry must reject before its own nonlinearity,
   shape, scan-structure, or environment work.
4. Update `checkDecl` in `Eval/Plan/Compile.lean` so adding the constructor does not break the
   compiler. Update `dtypeOfDecl` in `Eval/Plan/Signature.lean` so
   `.typedTensor .f32` maps to `.f32`; consequently `ofDenseInputsForDecls` emits an f32 signature
   rather than silently constructing an f64 checked plan. The temporary schedule-level stop above
   is the fail-loud interim contract Task 2 replaces with checked f32 admission. Update the local
   exhaustive reference functions in `TraverseAxesEquiv`,
   `TraverseAxesSpike`, and `Eval/Plan/ContractTest`, and add an f32 route-fragment fixture so
   omission from categorical naming is observable. `DSL/Pipeline/TraverseTest` is a build-only
   regression target, not an edited Task 1 file.

**Numbered fixture groups: 16; planned mutation cycles: 14**

1. Clone `ParseProgramTest`'s ordinary single-tensor declaration; insert `f32` and add a second
   comma-separated tensor in the same declaration; require two `Decl.typedTensor .f32` values with
   unchanged axis order.
2. Clone `SyntaxTest`'s ordinary tensor parser fixture; remove `f32`; require the original
   `Decl.tensor`, proving the old spelling did not change.
3. Extend `TraverseAxesEquiv`'s `Decl.mapUID_eq_ref` tensor case and clone its direct declaration
   traversal shape for `.typedTensor .f32`; require the same UID rewrite and retained element type.
4. Clone `StructuralTest`'s “tensor declaration lands in env” fixture; use `.typedTensor .f32`;
   require the same rank and duplicate-name behavior.
5. Clone `StructuralTest`'s declaration-environment donor; pass its declarations through the new
   storage-kind classifier. Require an f32-plus-predicate used graph to select `.float32`, an
   f64-plus-predicate graph to select `.float64`, a bool-only graph to default to `.float64`, and
   an f32-plus-f64 graph to reject at the first conflicting real name.
6. Clone `RouteFragmentCorpusTest`'s ordinary tensor metadata fixture; change only the declaration to
   `.typedTensor .f32`; require the same routed shape/name result. This is the fixture that can fail when
   route naming omits the new constructor.
7. Clone `EntryTest`'s accepted identity program; make declarations f32 and also omit an input/extent;
   require `EvalError.unsupportedDtype` before the shape or environment error.
8. Construct a direct `evalAssignDtypedSeeded` call from `Eval/ContractTest`'s accepted
   masked-aggregation
   fixture (same declarations, environment, sizes, destination, slots, and RHS, plus an empty seed);
   make only destination `Y` f32. Require exact `EvalError.unsupportedDtype "Y"`, and require
   `evalAssignDtyped` to inherit it.
9. Clone fixture 8; restore `Y` to f64, make read source `X` f32, and simultaneously remove `X` from
   the environment. Require exact `EvalError.unsupportedDtype "X"` rather than the missing-input
   gather error, and require `evalAssignDtyped` to inherit it.
10. Clone `Eval/ContractTest`'s accepted identity assignment; make destination `Y` and every read source
    f32. Direct `evalAssignDtypedSeeded` and `evalAssignDtyped` must report exact
    `EvalError.unsupportedDtype "Y"` for the homogeneous f32 assignment, proving an implementation
    that rejects only mixed modes is insufficient.
11. Copy the `base` scatter statement from `ScanTest`'s “S-B 1: a strided base” fixture, call it
    directly through `evalPlain`, and explicitly construct `Decl.typedTensor .f32` declarations for
    `X` and `S` (the donor itself passes `decls := []`). Remove the output-axis size simultaneously;
    require dtype rejection before `scatterOutShape`, making the ordering observable.
12. Copy that same S-B 1 `base` statement and call it directly through `evalStmtSliceSeeded`, again
    with explicitly constructed `Decl.typedTensor .f32` declarations for `X` and `S`; give it a
    non-identity scatter nonlinearity. Require dtype rejection before `unsupportedScatterNonlin`,
    proving the scatter arm cannot bypass the public-entry guard.
13. Clone the complete S-B 1 `evalScan` fixture, replace its empty declaration list with explicit
    `Decl.typedTensor .f32` declarations for `X` and `S`, and remove the scan iteration axis `l` from
    `sizes`. Require dtype rejection before
    `EvalError.shape (.unsizedAxis l.uid (.scanIteration l.name))`. This pins the public `evalScan`
    door with a competing error raised by `evalScan` itself, before any still-guarded
    `evalStmtSliceSeeded` call.
14. Clone `ScanCompileTest.scratchSched`; keep its published state `S` f64, declare its
    recurrence-only scratch `T` (present in `ScanStmt.writes` but absent from `ScanStmt.outputs`) as
    f32, and require mixed precision rejection naming `T`. As a control, add an unrelated f32
    declaration that is neither external nor written and require the otherwise-f64 program to remain
    accepted.
15. Clone `SignatureTest.conversionInputs`; pin
    `dtypeOfDecl (.typedTensor .f32 ...) = .f32` and require `ofDenseInputsForDecls` to emit an f32
    signature. Then exercise the temporary schedule stop with two homogeneous f32 programs: clone
    `CompileTest.acceptedSched` once with a matching concrete f32 input, and once using its admitted
    Iverson-only assignment shape (no real external input) with an f32 destination. Both must fail
    as `PlanCompileCause.capability
    (CapabilityError.unsupportedDtype "f32 execution not yet admitted")`. Together they prove that
    explicit f32 cannot reach specialization or the existing Float worker merely because Step B has
    no f32 external signature to inspect.
16. Extend `PropertyOracle.evalErrorEq` with
    `.unsupportedDtype a, .unsupportedDtype b => decide (a = b)` above its catch-all. Add direct
    guards requiring equal names to compare true and different names to compare false. This closes
    the catch-all consumer that otherwise compiles silently while treating identical new errors as
    unequal.

Mutations and expected observations:

- omit `.typedTensor .f32` from UID traversal, declaration/rank classification, and route naming,
  one cycle each: fixtures 3, 4, and 6 fail; restore passes;
- map `.typedTensor .f32` to `.float64` in `storageConstraintOfDecl`: fixtures 5, 7, and 8 fail;
  restore passes;
- map `.typedTensor .f32` to `.f64` in `dtypeOfDecl`: fixture 15 constructs an f64 signature/plan
  instead of the required f32 signature; restore emits `.f32`;
- remove the temporary homogeneous-f32 schedule stop: fixture 15's external-input case reports the
  later Step-B error and its Iverson-only case constructs a plan; restore gives both the exact early
  capability rejection;
- make `predicate` contribute a fixed `.float64` constraint: fixture 5's f32-plus-predicate case
  rejects and fails; restore lets bool inherit `.float32`;
- move the scheduled guard after shape inference: fixture 7 reports the shape/input error and fails;
  restore reports dtype first;
- remove the deepest `evalAssignDtypedSeeded` guard: fixture 9 executes
  dtype-blind and fails; restore rejects.
- remove the `evalPlain` scatter guard: fixture 11 reports its unsized-output error and fails;
  restore reports dtype first;
- remove the `evalStmtSliceSeeded` and `evalScan` entry guards independently (two cycles): fixtures
  12 and 13 respectively report their later nonlinearity/unsized-iteration errors and fail; restore
  reports dtype first.
- derive scheduled names from `ScanStmt.outputs` instead of `ScanStmt.writes`: fixture 14's scratch
  case is wrongly accepted while its unused-declaration control still passes; restore rejects the
  scratch and continues to ignore the unused declaration.
- remove the `EvalError.unsupportedDtype` equality arm: fixture 16 compares two identical errors as
  unequal and fails; restore makes equal/different names distinguish correctly.

### Task 2 — Add checked binary32 evidence and compiler specialization

**Files**

- `leanncd/LeanNCD/Eval/Plan/Types.lean`
- `leanncd/LeanNCD/Eval/Plan/Error.lean`
- `leanncd/LeanNCD/Eval/Plan/Signature.lean`
- `leanncd/LeanNCD/Eval/Plan/Check.lean`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/LeanNCD/Eval/Plan/Dense.lean`
- `leanncd/LeanNCD/Eval/Plan/Block.lean`
- `leanncd/LeanNCD/Eval/Plan/EvalPlan.lean`
- `leanncd/test/Eval/Plan/SignatureTest.lean`
- `leanncd/test/Eval/Plan/KernelCheckTest.lean`
- `leanncd/test/Eval/Plan/GraphCheckTest.lean`
- `leanncd/test/Eval/Plan/ScatterCheckTest.lean`
- `leanncd/test/Eval/Plan/ScanTest.lean`
- `leanncd/test/Eval/Plan/KernelDenseTest.lean`
- `leanncd/test/Eval/Plan/GraphDenseTest.lean`
- `leanncd/test/Eval/Plan/BlockTest.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean`

**Implementation**

1. Reuse the source-layer `TensorStorageKind`, add `storageConstraintOfDtype`, the three f32 algebras, and
   storage-kind-bearing private checked assignment/plan evidence. Keep `dtypeAdmitted` and public
   `checkAssign` Float-backed; add `checkAssignF32` through one shared private core.
2. Preserve the existing Float-backed relationship between `.f64` and `.bool`; compare storage
   kinds, not dtype constructors, when deriving a raw graph's carrier.
3. Before removing Task 1's temporary homogeneous-f32 schedule stop, add `.float64` storage-kind
   guards to the deepest existing Float entries `runDenseAssignAt` and `runDensePlan`; their wrappers
   inherit those guards. Then replace the temporary stop with storage-aware signature validation,
   f32 operation capability, algebra selection, and the appropriate graph checker. Mixed precision
   remains rejected by the source storage-kind analysis before plan construction. Thus this task may
   produce f32 evidence, but no committed public Float worker can consume it.
   Task 1 already makes `unsupportedDtype` live for mixed precision; this task extends that producer
   to f32 operations deliberately deferred from this slice. Do not delete any error constructor.
4. Update `Dense.lean`'s `constFloat` documentation when the f32 algebra row becomes nonempty: its
   `.f32` fallback remains unreachable through this Float worker because ordinary `checkAssign`
   rejects f32 and the new storage-kind guards reject f32 evidence, not because
   `admittedAlgebrasFor .f32` is still empty. In `Check.lean`, also replace the stale
   `dtypeAdmitted` claim that no binary32 worker exists and the `checkAssign` claim that
   `PlanError.dtypeMismatch` is deliberately producer-less; document instead that the public
   Float checker remains f64/bool-only while the shared private core and `checkAssignF32` own f32
   source equality.
5. Ensure direct raw-plan construction cannot acquire f32 evidence for non-assignment steps, a
   mixed-storage signature table, or a Float-only local block. `checkPlanBlock` derives storage from
   its complete signature table before output/node wiring, wraps a mixed table through
   `BlockError.wiring (.mixedStorageKinds ...)`, and rejects `.float32` as
   `BlockError.storageKindNotAdmitted .float32`. This block-level check is load-bearing for an
   all-input, zero-step block, where per-node `checkAssign` calls are vacuous. Preserve original
   all-factor and outer-step indices.

**Numbered fixture groups: 19; planned mutation cycles: 23**

1. Clone `KernelCheckTest.goodPlan`; change every signature to f32 and the algebra to f32
   sum-product; require `checkAssignF32` success and `.float32` storage-kind evidence.
2. Clone fixture 1; change only one read source to f64; require the exact revived
   `PlanError.dtypeMismatch .f32 .f64`. Reverse destination/source roles through ordinary
   `checkAssign`; require its existing earlier `dtypeNotAdmitted` for the f32 source, proving the
   Float-backed checker's diagnostic order did not change.
3. Pin `constMatchesDtype` directly: `.f32` accepts an `.f32` payload and rejects exact `.f64` and
   `.bool` payloads. Do not claim `checkAssignF32` reaches `constDtypeMismatch` for a locally altered
   algebra: algebra membership is checked first, so that donor must report
   `algebraNotAdmitted` with the complete malformed algebra payload.
4. Clone `KernelDenseTest.unaryPlan`'s unary read shape into `KernelCheckTest`; make it all-f32;
    require the new located
   unary-for-dtype rejection at the original term/factor index. Put an Iverson factor before the
   unary read, so the required factor index is 1 while a filtered-read index would be 0.
5. Clone the pre-existing destination-f32 guard and keep calling ordinary `checkAssign`; it must
    still return `dtypeNotAdmitted`, proving the legacy entry was not widened.
6. Construct a one-node plan from `GraphCheckTest.chainPlan` by retaining only
    `.assign (idNode 1 0)` and the first two signatures; make both signatures and the algebra f32,
    and require `checkPlan` success with `.float32` storage-kind evidence. In a second case, clone
    `chainPlan`, append one unused fourth signature without adding it to `inputSlots`, and set the
    signature dtypes to `[f32, f32, f64, f64]`; require
    `mixedStorageKinds 2 .f32 .f64`. The two trailing mismatches distinguish first offending slot
    from last offending slot; the four-entry signature table also makes the reported slot `2`
    distinct from the table-size count `4`. The unused non-input slot also makes the plan
    wiring-invalid (`missingProduction`), deliberately pinning that storage derivation runs before
    outer graph wiring.
7. Construct two mixed real/Boolean graphs from `GraphCheckTest.chainPlan`. For the f64 case, change
   only input slot 0's signature to `.bool`; its f64 destination nodes may read that Boolean source.
   For the f32 case, use signatures `[f32, bool, f32]`, change node 1 to the Boolean algebra and node
   2 to the f32 sum algebra, so both f32→bool and bool→f32 reads occur. Require `.float64` and
   `.float32` storage respectively and acceptance. These cases fail if the implementation compares
   concrete dtypes or permanently assigns bool to Float64 storage.
8. Clone `GraphCheckTest.nonlinFailPlan`, correct its deliberately mismatched pointwise shape from
    `#[3]` to `#[2]`, make both signatures f32, and require `f32UnsupportedStep` at its original
    step index. The corrected shape makes the non-assignment node structurally valid apart from the
    f32 capability boundary.
9. Clone `ScatterCheckTest.upSigs` and its valid scatter; make all signatures/constants f32; direct
    `checkScatter` must still reject f32.
10. Clone `ScanTest.linearScan`; make its state/captures/results f32; direct `checkScanPlan` must
    retain `stateDtypeNotAdmitted`.
11. Clone `CompileTest.acceptedSched`; use f32 declarations and matching f32 signatures; require f32
    tensor signatures, f32 sum algebra, one assignment step, and `.float32` checked storage kind.
12. Clone fixture 11; leave `X` as ordinary `tensor`; require `unsupportedDtype` naming the first
    differing used name `Y` with the exact mixed-storage payload above. Repeat with `X` undeclared to
    pin the established f64 default and the same used-name order.
13. Clone fixture 11; supply an f64 input signature for f32-declared `X`; require
    `InputSignatureError.dtypeMismatch "X" .f32 .f64`.
14. Build `f32BadOrderProg` from fixture 11 by adding both pointwise nonlinearity and a unary read;
    require the nonlinearity `unsupportedDtype` payload. Build `f32UnsupportedStepOrder` from
    `GraphCheckTest`'s chain donor with a valid assign before a pointwise node; require step index 1.
15. Clone `CompileTest.acceptedSched` four times to make otherwise-valid homogeneous f32 source
    programs containing respectively a top-level scatter, a scan, an axiswise nonlinearity, and an
    inline unary factor. Call `prepareEvalPlan` and require the exact source-level
    `CapabilityError.unsupportedDtype` payload for each form before raw plan construction. The unary
    donor places an Iverson first so its reported all-factor index is 1.
16. Use fixture 8's shape-corrected pointwise node as the pointwise case, and construct structurally
    valid raw scatter, scan, and axiswise plans with homogeneous f32 signatures. Call outer
    `checkPlan` directly and require
    `PlanStepError.f32UnsupportedStep` with the exact closed `PlanStepKind` and original outer index
    for each. Together with fixture 8 these exhaust every non-assignment `PlanStep` constructor.
17. Clone fixture 11 into a two-statement f32 source program whose first plain assignment has an
    inline unary and whose second has a pointwise nonlinearity. Require the first statement's unary
    payload. This distinguishes top-level source order from a whole-program pass that prioritizes
    nonlinearity categories regardless of statement position.
18. Pass fixture 1's checked f32 assignment with an empty, otherwise-invalid Float store directly to
    `runDenseAssignAt` and `runDenseAssign`; require
    `PositionalInputError.storageKindMismatch .float64 .float32` before context, missing-slot, or
    storage validation. Pass fixture 6's checked f32 graph with wrong-arity Float inputs to
    `runDensePlan`; require the same storage-kind mismatch before arity. These are the fail-loud
    Float-side doors that must land before Task 1's temporary schedule stop is removed.
19. Clone `BlockTest.stepBlock` as an all-input, zero-step block: retain one f32 signature, make that
    slot both the sole input and output, and set `steps := #[]`. Direct `checkPlanBlock` must report
    `BlockError.storageKindNotAdmitted .float32`; the empty step list ensures no per-assignment dtype
    check can accidentally provide the rejection. Add a second wiring-valid zero-step case with
    `tensorSigs := #[f32, f64]` and both slots listed as inputs/outputs; require exact
    `BlockError.wiring (PlanError.mixedStorageKinds 1 .f32 .f64)`.

Mutations and expected observations:

- use the f64 algebra for f32 destinations: fixtures 1 and 11 fail; restore passes;
- remove the f32 arm from `constMatchesDtype`, then separately admit one non-f32 payload (two cycles):
  fixture 3 fails in the corresponding direction; restore passes;
- admit one mixed-source direction at a time (two cycles): the corresponding half of fixture 2
  fails; restore passes;
- remove unary rejection: fixture 4 changes from rejection to acceptance; restore passes;
- let ordinary `checkAssign` admit f32: fixture 5 fails; restore passes;
- compare concrete dtypes rather than storage kinds: fixture 7 rejects the existing f64/bool graph;
  restore passes;
- make `.bool` contribute a fixed `.float64` storage constraint: fixture 7's f32/bool graph rejects;
  restore lets bool inherit `.float32`;
- filter graph nodes before locating unsupported f32 steps: fixture 14 reports 0 instead of 1 and
  fails; restore passes;
- continue after the first mixed-signature conflict and report the last conflicting slot: fixture 6
  reports slot 3 instead of slot 2 and fails; restore stops at slot 2;
- swap nonlinearity/factor capability order: `f32BadOrderProg` reports unary and fails; restore
  passes;
- remove each source capability arm for scatter, scan, axiswise, and unary independently (four
  cycles): the corresponding fixture 15 case reaches plan construction or reports a later error;
  restore reports its exact source capability payload;
- remove each raw-plan dispatch arm for scatter, scan, and axiswise independently (three cycles):
  the corresponding fixture 16 case reaches the legacy checker or reports the wrong kind; restore
  reports its exact original index and closed step kind.
- traverse top-level source statements in reverse or by unsupported-feature category: fixture 17
  reports the second statement's nonlinearity and fails; restore reports the first statement's unary.
- remove the local and graph Float-worker storage guards independently (two cycles): the
  corresponding half of fixture 18 reaches Float validation/execution with f32 evidence and reports
  a later error or value; restore rejects at each deepest public boundary.
- remove the block-level storage-kind check: fixture 19 changes from the exact rejection to
  successful checked evidence; restore rejects the zero-step f32 block.

### Task 3 — Implement native binary32 local and graph execution

**Files**

- `leanncd/LeanNCD/Eval/Tensor.lean`
- `leanncd/LeanNCD/Eval/Plan/Dense.lean`
- `leanncd/LeanNCD/Eval/Plan/EvalPlan.lean`
- `leanncd/LeanNCD/Eval/Plan/Error.lean`
- new `leanncd/LeanNCD/Eval/Plan/Dense32.lean`
- new `leanncd/test/Eval/Plan/KernelDense32Test.lean`
- new `leanncd/test/Eval/Plan/EvalPlan32Test.lean`
- `leanncd/lakefile.toml`

**Implementation**

1. In `Eval/Plan/Dense.lean`, refactor the carrier shell to `DenseTensorOf α`, preserving
   `DenseTensor` as its `Float` alias,
   `DenseTensor.mk` as an abbreviation, and explicitly typed projection definitions. Add the
   `DenseTensor32` alias, the private narrow fallible `ScalarKernelOps α` record (including
   carrier-specific unary handling), private `denseValueAtWith`, native f32 constant decode and
   admitted operations, and the public checked-only `runDenseAssignAt32` plus its empty-context
   `runDenseAssign32` wrapper. Keep the existing private Float `denseValueAt` wrapper for scatter;
   neither the generic ops record nor a raw-plan generic traversal may escape the module.
   `Eval/Plan/Dense32.lean` owns only the graph-level f32 worker described below. Do not generalize
   nonlinearity, scan, or scatter execution.
2. Reuse Task 2's runtime storage-kind-mismatch diagnostics and Float-side guards. Add symmetric
   `.float32` guards at the deepest public f32 local and graph entries before validation, gathering,
   or input allocation.
3. Add assignment-only `runDensePlan32`, retaining the existing graph step order, input-slot
   placement, destination replacement, shape/storage checks, and exact store arity.
4. Update the execution-door audit table from the actual callers for the source/legacy and
   Float/f32 worker columns. If any route can pass f32 evidence to `Dense.lean`, or Float-backed
   evidence to `Dense32.lean`, fix it in this task. Mark the named-adapter and JAX columns as pending
   Tasks 4 and 5 rather than claiming the table is complete.
5. Register `Eval.Plan.KernelDense32Test` and `Eval.Plan.EvalPlan32Test` in the explicit `Tests`
   module list in `lakefile.toml` before running their targeted build names.

**Numbered fixture groups: 16; planned mutation cycles: 14**

1. New fixture `f32Identity`, cloned from `KernelDenseTest.identityPlan`; use native f32 buffers
   containing `+0`, `-0`, and the least positive subnormal. Require output bits `[0, 0, 1]`: the
   sum-product worker's `+0` reduction seed normalizes the `-0` lane to `+0`. Separately pin native
   `.f32 0x80000000` constant decoding to `Float32.toBits = 0x80000000`; do not claim the seeded
   identity assignment preserves negative zero.
2. New fixture `f32ReductionRounding`, cloned from `KernelDenseTest.contractPlan`; reduce the
   one-factor vector with bits for `[16777216, 1, -16777216]`. Require output bits `0`; run the
   existing Float donor with the same numeric values and require binary64 value `1`.
3. New fixture `f32MultiplicationRounding`, cloned from `KernelDenseTest.identityPlan`; add a second
   scalar factor and inputs `4097`, `4097`. Require bits `1266683904` (`16785408`). The binary64
   product is the exact integer `16785409`; narrowing that one product also yields the correct f32,
   so fixture 11 additionally consumes the rounded intermediate and is the test that distinguishes
   native/store-per-step f32 from a whole-graph binary64 implementation.
4. Clone `KernelDenseTest.factorOrderPlan`; use factor bits
   `[3252982345, 3252982345, 3276275712]`. Require the declared left fold to produce
   `3357503572`; the right-associated mutation produces `3357503571`.
5. Clone `KernelDenseTest.efpPlan`; change it to f32 and require factor identity bits `1065353216`.
6. Clone `KernelDenseTest.zerdPlan`; change it to f32 and require reduction identity bits `0`.
7. Clone `KernelDenseTest.maxContractPlan` with `KernelDenseTest.storeNegB`; change both to f32 and
   require output bits `[3240099840, 3267887104, 3296329728, 3323740160]` for
   `[-10, -100, -1000, -10000]`, with `0xff800000` as the load-bearing seed.
8. Clone `KernelDenseTest.minContractPlan` with `KernelDenseTest.storeAB`; change both to f32 and
   require output bits `[1092616192, 1120403456, 1148846080, 1176256512]` for
   `[10, 100, 1000, 10000]`, with `0x7f800000` as the load-bearing seed.
9. Clone `KernelDenseTest.oobMaxPlan`; change to f32 and require zero-pad to win over all-negative
   valid values as f32 `+0`.
10. Clone an existing Iverson assignment donor from `KernelDenseTest`; change its numeric signatures
    and algebra to f32 and require native one/zero bits.
11. Clone `GraphDenseTest.chainSigs`/chain plan as `f32ProductChain`: first materialize
    `P := 4097 × 4097`, then `Y := P + (-16785408)`. Require `P` bits `1266683904` and `Y` bits `0`.
    A whole-graph binary64 execution with final-only narrowing produces `Y = 1`, so this fixture
    distinguishes the competing implementations.
12. Clone fixture 2 with three separately stored terms whose chosen bits distinguish the declared
    left fold from a right-associated term fold: use `[16777216, 1, -16777216]`, whose compiled
    Lean 4.30 results are left-fold bits `0` and right-associated bits `1065353216` (`1`).
13. Pass fixture 2's f64 donor with an empty, therefore invalid, native f32 store directly to
    `runDenseAssignAt32` and `runDenseAssign32`; require storage-kind mismatch rather than context,
    missing-slot, or storage error.
14. Pass fixture 11's f64 donor with wrong-arity native f32 inputs to `runDensePlan32`; require
    storage-kind mismatch rather than arity, shape, or storage errors.
15. Add compile-time compatibility checks for `DenseTensor.mk`, `DenseTensor.shape`, and
    `DenseTensor.data`, and retain the existing direct constructor/projection uses in
    `KernelDenseTest`, `GraphDenseTest`, `NonlinDenseTest`, and
    `Portfolio.ScatterNonlinRejectTest`. Repo-wide grep for those three generated names supplies the
    complete caller list. This fixture distinguishes a real compatibility shim from an `abbrev`
    that preserves only the type name.
16. Clone `KernelDenseTest.trueFalseTermsBool`, `conjNonBinaryBool`, and `nonBinaryStore`, changing
    the real signatures and every buffer to f32 while keeping the destination `.bool` and
    `admittedAlgebraBool`; require `0.75` bits `1061158912` for the term max and `0.25` bits
    `1048576000` for the factor min. Add the reverse one-step identity case with an f32 destination
    reading a bool source containing `0.25`, again requiring bits `1048576000`. Together they pin
    f32→bool and bool→f32 execution in one Float32 store without silently coercing Boolean-tagged
    data to exact zero/one.

Mutations and expected observations:

- widen the worker/store to binary64 and narrow only materialized results: fixtures 2 and 11 return
  f32 bits for `1` instead of `0` and fail; restore returns `0`;
- replace native multiplication with addition: fixture 3 fails; restore returns product bits
  `1266683904`;
- swap factor, reduction, or term fold order, one cycle each: fixtures 4, 2, and 12 fail
  respectively; restore passes;
- change each f32 identity (`1`, `0`, `−∞`, `+∞`) independently: fixtures 5–8 fail; restore passes;
- change zero-pad to the reduction identity: fixture 9 fails; restore passes;
- remove the local and graph f32-worker deepest storage guards independently (two cycles): fixtures
  13 and 14 reach validation/execution instead of failing at their own public boundary; restore
  reports storage kind first.
- remove one old-namespace `DenseTensor` forwarding abbreviation: fixture 15 fails to elaborate;
  restore passes without migrating callers.
- decode `ScalarConst.bool true` as Float32 zero, or otherwise remove Float32 Boolean decoding:
  fixture 16's exact bits fail; restore passes.

### Task 4 — Add the named f32 boundary and guard the legacy adapter

**Files**

- new `leanncd/LeanNCD/Eval/Plan/Adapter32.lean`
- `leanncd/LeanNCD/Eval/Plan/Adapter.lean`
- `leanncd/LeanNCD/Eval/Plan/Error.lean`
- `leanncd/LeanNCD/Eval/Plan/Signature.lean`
- `leanncd/LeanNCD/Eval/Report.lean`
- `leanncd/LeanNCD.lean`
- `leanncd/lakefile.toml`
- new `leanncd/test/Eval/Plan/Adapter32Test.lean`
- `leanncd/test/Eval/Plan/AdapterTest.lean`
- `leanncd/test/Eval/Plan/SignatureTest.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean`

**Implementation**

1. Parameterize the named environment and report shells as `NamedDenseEnvOf α` and
   `EvalReportOf α`, preserving the existing names as Float aliases plus an `EvalReport.mk`
   abbreviation and explicitly typed projection definitions. Add declaration-aware native f32
   signature construction and
   Float32 aliases plus the named f32 adapter. Factor common shape/storage/binding/publication
   traversal into carrier-polymorphic helpers used by both public wrappers; do not copy the whole
   adapter for each carrier. Reuse `checkPreparedBindings` and `materializedSignatures`; keep native
   buffers all the way through. Update every existing `SignatureTest` expectation for
   `ofDenseInputsForDecls`'s error type: its three duplicate-declaration guards and their comments
   must now match `.declaration (.duplicateTensorDecl ...)`, while successful `.ok` cases remain
   unchanged.
2. Add explicit storage-kind guards to existing `pack`, `unpack`, and `runPreparedDense` before
   shape/storage/result-arity/publication work; add symmetric guards to the f32 entries. Do not rely
   on the caller having chosen the correct adapter.
3. Import `Adapter32` from `LeanNCD.lean` and register the new tests in the existing `Tests` target.
4. Update the execution-door audit table's named-adapter column from the implemented call graph,
   leaving only the JAX column pending Task 5.

**Numbered fixture groups: 17; planned mutation cycles: 17**

1. Clone `SignatureTest.conversionInputs`; construct native f32 tensors and f32 declarations;
   require `ofDenseInputs32ForDecls` to return f32 shapes/signatures.
2. Clone fixture 1; make one declaration ordinary `tensor`; require a located declaration/storage
   mismatch instead of silently marking it f32.
3. Clone `AdapterTest`'s named identity round trip; use the f32 source program and native adapter;
   require exact input/output bits and materialized f32 signature.
4. Clone `CompileTest`'s repeated-assignment schedule; make it homogeneous f32; require repeated
   materialized names in schedule order and last-write-wins native bits.
5. Clone `AdapterTest`'s malformed-storage fixture; shorten an f32 input buffer; require storage
   mismatch before execution.
6. Clone `AdapterTest`'s wrong-result-arity fixture against `unpack32`; append an extra validly shaped
   slot so every materialized binding remains in range. Require the exact store-arity error; removing
   the arity guard must change this fixture to success, making the guard observable.
7. Clone `AdapterTest`'s warning-preservation success and failure donors; require the same warnings in
   `EvalReport32` and in the f32 execution failure.
8. End-to-end `f32ReductionProgram`, donated by `CompileTest.acceptedSched`: change it to a rank-1
   reduction with a pinned extent of three, f32 declarations, and native inputs
   `[16777216, 1, -16777216]`; require materialized `Y` bits `0`. Run the separately constructed
   ordinary-tensor control through `runPreparedDense`; require binary64 `Y = 1`.
9. Reconstruct end-to-end f32 max/min programs from the source shapes of the private
   `DifferentialTest.maxPlainProg`, `minPlainProg`, and `plainAggInputs` donors (they cannot be
   referenced across modules); require max bits `[1077936128, 1084227584]`, min bits
   `[1065353216, 1065353216]`, and f32 materialized signatures.
10. Call existing `pack` and `unpack` directly with an f32 prepared plan. Give `pack` malformed Float
    storage and `unpack` wrong arity simultaneously; both must report storage-kind mismatch first.
    The corresponding `pack32`/`unpack32` calls on a Float-backed plan must reject symmetrically.
11. Clone `AdapterTest`'s `runPreparedDense` failure donor; pass a `.float32` prepared plan with a
    well-shaped Float environment. Require the adapter-level storage-kind failure before
    `packChecked` or `runDensePlan`. Removing only `runPreparedDense`'s own guard must instead reach
    the worker and report an execution storage-kind cause, so this fixture observes the independent
    guard.
12. Add compile-time compatibility checks for `EvalReport.mk`, `EvalReport.env`, and
    `EvalReport.warnings`, and retain the current construction/projection uses in `EntryTest` and
    `AdapterTest`. This catches an alias-only refactor that removes the old generated names.
13. Clone fixture 3 with one `predicate` input and one f32 tensor input, both represented as native
    Float32 buffers carrying non-binary Boolean-tagged values `0.25` and `0.75`. Require `pack32`,
    `runPreparedDense32`, and `unpack32` to accept the bool signature, preserve exact bits
    `1048576000` and `1061158912` without truth-value coercion, and publish the expected f32 and bool
    signatures.
14. Call existing `InputSignature.ofDenseInputsForDecls` with a Float tensor whose used declaration
    is `.typedTensor .f32`, and call `ofDenseInputs32ForDecls` with a native Float32 tensor whose
    declaration is ordinary `tensor`. Require the symmetric exact
    `InputSignatureBuildError.storageKindMismatch` payloads naming the input.
15. Clone `SignatureTest`'s duplicate-declaration failure twice. For the Float constructor use
    duplicated `.typedTensor .f32` declarations with a Float input; for the Float32 constructor use
    duplicated ordinary `tensor` declarations with a native Float32 input. Each call therefore
    violates both declaration uniqueness and carrier compatibility, and each must report
    `.declaration (.duplicateTensorDecl ...)` before storage-kind mismatch.
16. Mirror fixture 11 through `runPreparedDense32`: pass a `.float64` prepared plan with a
    well-shaped native Float32 environment and require the adapter-level storage-kind failure before
    `packChecked32` or `runDensePlan32`.
17. Clone fixture 1 as a predicate-only native Float32 input map with no real-valued input names.
    `ofDenseInputs32ForDecls` must accept it and emit a `.bool` signature, proving that an explicitly
    chosen Float32 constructor applies per-name constraints rather than the schedule-wide bool-only
    default.

Mutations and expected observations:

- replace the native adapter execution leg with widen-inputs → `runDensePlan` → narrow-outputs:
  fixture 8 returns f32 bits for `1` instead of `0` and fails; restore returns `0`;
- hard-code f32 signatures to f64: fixtures 1 and 3 fail; restore passes;
- skip declaration checking in the f32 signature constructor: fixture 2 changes to success and
  fails; restore passes;
- deduplicate materialized names or publish in reverse order: fixture 4 fails; restore passes;
- remove input storage validation: fixture 5 reaches execution and reports a different error; restore
  reports storage mismatch;
- remove the result-arity guard: fixture 6 changes to success and fails; restore reports arity;
- remove the Float-backed `pack` and `unpack` storage-kind guards independently: the corresponding
  halves of fixture 10 report storage/arity or publish Float buffers and fail; restore reports
  storage kind first.
- remove only `runPreparedDense`'s storage-kind guard: fixture 11 reports the later worker execution cause
  and fails; restore reports the adapter-level storage-kind cause.
- remove one old-namespace `EvalReport` forwarding abbreviation: fixture 12 fails to elaborate;
  restore passes without migrating callers.
- reject `.bool` in the Float32 adapter's signature compatibility check: fixture 13 fails; restore
  lets Boolean tensors share the selected Float32 carrier.
- coerce Boolean-tagged Float32 inputs to zero/one: fixture 13's exact non-binary bits fail; restore
  preserves the values;
- remove the Float and Float32 declaration/carrier guards independently (two cycles): the
  corresponding half of fixture 14 silently mislabels the buffer; restore reports the named
  storage-kind mismatch;
- inspect carriers before rebuilding the declaration environment: fixture 15 reports storage kind
  instead of the duplicate declaration and fails; restore reports the declaration error first;
- remove only `runPreparedDense32`'s own guard: fixture 16 reaches the f32 pack/worker path and fails
  with a later cause; restore reports the adapter-level storage-kind cause.
- call the schedule-wide storage derivation from `ofDenseInputs32ForDecls`: fixture 17 defaults the
  predicate-only map to Float64 and fails; restore uses the shared per-name constraint and accepts it.

### Task 5 — Preserve JAX truthfulness and close capability documentation

**Files**

- `leanncd/LeanNCD/Eval/Plan/Executable.lean`
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`
- `leanncd/test/Eval/Plan/ExecutableTest.lean`
- `leanncd/LeanNCD/Eval/AGENTS.md`
- `leanncd/LeanNCD/DSL/AGENTS.md`
- `papers/backend_missing_functionality.md`
- `papers/wave_f_capability_manifest.md`
- `papers/eval_ir.md`
- `papers/wave_c_capability_manifest.md`
- `papers/f32_evalplan.md`

**Implementation**

1. Revalidate standalone JAX assignment entries with the mode-appropriate checker, then retain the
   existing located rejection of binary32. Keep `orderedReference64`, `UInt64` transport, Python
   runtime, and operation renderings unchanged.
2. Add a plan-level `.float64` storage-kind gate to `lowerCheckPlanToCandidate`, `lowerPlan`,
   `generateForward`, `renderAffinePlanPositional`, `renderAffinePlanNamed`, `generateNamed`, and
   `renderInputConstants` before node iteration, binding/input validation, evidence aggregation, or
   Python emission, using `JaxCodegenError.unsupportedStorageKind`. Also make
   `validateAndConstructExecutable` reject a manually built candidate whose source plan is binary32,
   using `JaxExecutableValidationError.unsupportedStorageKind` before binding validation and the
   whole-candidate predicate. Do not claim observable precedence over the aggregation equality:
   `JaxExecutableCandidate.aggregated` already proves that equality for every constructible
   candidate. This must reject an all-input, zero-step f32 plan; per-node support checks alone are
   vacuous for that case.
3. Update the two AGENTS maps so a reader starting at the documented entry points can find the native
   f32 runtime.
4. Update current capability documents. `unsupportedDtype` becomes the tenth live family out of
   sixteen, leaving six producer-less/unreachable. Split the old combined “f32; dynamic shapes” row:
   this slice closes only the bounded f32 assignment fragment, while dynamic shapes remain
   foundational and wholly open. Add a separate future-complex row that records the unresolved
   scalar-domain, machine-carrier, operation-admission, conversion, and JAX-parity work; JAX's ability
   to store complex arrays must not be reported as Tensor Logic support. Preserve completed
   historical records as historical. In every documentation file this task edits, replace existing
   `File.lean:NNN` source-line citations with stable identifiers while touching the surrounding
   capability text; do not ship new source-line citations.
5. Change this plan's status from implementation plan to completed record and append the observed
   mutation fail/restored-pass results, targeted/full build results, and both final-review
   adjudications. Do not rewrite planned claims as completed unless their evidence is recorded.
6. Complete the execution-door audit table from the final implemented call graph, including every
   experimental candidate/renderer entry and the all-input zero-step case. No cell may remain marked
   pending at slice completion.

**Numbered fixture groups: 6; planned mutation cycles: 7**

The production and experimental halves live in different libraries and must rebuild equivalent
fixtures locally. Assertions for `validateAndConstructExecutable` belong in `ExecutableTest.lean`,
where `preparedOf` is private and `emptyPlanCandidate` is a local test helper. Assertions for
`lowerCheckPlanToCandidate`, generators, renderers, and `renderInputConstants` belong inline in
`EvalPlanCodegen.lean` under the non-default `JaxExperiment` library, with an equivalent prepared
plan rebuilt through that module's own local checked-plan/binding helper.

1. Clone `ExecutableTest.boolDestAssign`; extend its signature table by one slot, move the
   destination from slot 1 to slot 2, substitute a valid checked f32 assignment, and call the
   standalone validator with node index 7; require both deliberately changed locators and
   require `JaxSupportError.destinationDType 7 2 .f32`, not `invalidSignatureContext`.
2. In `EvalPlanCodegen.lean`, rebuild fixture 1 as a nonempty prepared plan and feed it to every
   plan-level candidate/generator/renderer entry. Require
   `JaxCodegenError.unsupportedStorageKind .float32` before the node-level located
   destination-dtype error. This is the ordering discriminator: a gate after node iteration reports
   the located node error instead.
3. Build equivalent all-f32, all-external, zero-step prepared plans independently in both modules:
   clone `ExecutableTest.idRaw` locally, make both slots external, and remove its only step.
   In `EvalPlanCodegen.lean`, `lowerCheckPlanToCandidate` must return
   `JaxCodegenError.unsupportedStorageKind .float32`. In `ExecutableTest.lean`, build valid bindings
   with its private `preparedOf`, wrap the result with its local `emptyPlanCandidate`, and require
   `validateAndConstructExecutable` to return
   `JaxExecutableValidationError.unsupportedStorageKind .float32`.
4. Rebuild the same dual-invalid candidate separately in each module: retain `.float32` storage but
   replace its materialized binding with the existing out-of-range-slot attack (`slot := 99`).
   Feed the production copy to `validateAndConstructExecutable` and the experimental copy to every
   prepared-plan generator/renderer; require storage-kind rejection before `invalidBindings`. This
   is the observable binding-precedence fixture.
5. In `EvalPlanCodegen.lean`, wrap its local fixture 3 plan in valid prepared bindings and feed it to
   both named/positional plan renderers, `generateForward`, `generateNamed`, and
   `renderInputConstants`; require
   `JaxCodegenError.unsupportedStorageKind .float32` and no Python/constants text.
6. Retain an empty Float-backed control plan; require its existing behavior so the new gate does not
   become an accidental blanket ban on empty graphs.

Mutations and expected observations:

- route standalone f32 validation through ordinary `checkAssign`: fixture 1 reports
  `invalidSignatureContext` and fails; restore reports the located destination dtype;
- remove the `lowerCheckPlanToCandidate` gate: fixture 3 acquires `orderedReference64` and fails;
  restore rejects before evidence;
- remove the independent `validateAndConstructExecutable` gate: fixture 3 constructs an
  `orderedReference64` executable and fails; restore rejects;
- remove the plan-level renderer/generator gate: fixtures 2 and 5 emit Python or report a later
  node/binding error and fail; restore emits nothing;
- apply the gate after node iteration: fixture 2 reports the located destination-dtype error instead
  of the plan storage-kind error and fails; restore rejects before visiting the node;
- move the gate after prepared-binding validation: fixture 4 reports `invalidBindings` and fails;
  restore reports storage kind first;
- remove `renderInputConstants`'s independent gate: fixture 5 emits `UInt64`/Float64 constants and
  fails; restore emits nothing.

## 5. Dependency graph and risk sizing

Task 1 is the only root. Task 2 depends on Task 1's source dtype authority. Task 3 depends on Task
2's checked mode and f32 algebra. Task 4 depends on Task 3's native graph worker. Task 5 depends on
Task 4 so its documentation closes the actual public boundary rather than a projected one.

| Task | Main reviewer question | Fixture groups | Mutation cycles | Risk |
|---|---|---:|---:|---|
| 1 — source/legacy | Does the extensible typed declaration survive every source traversal, does bool inherit rather than select precision, does every homogeneous f32 graph hit the temporary stop, and can any legacy dtype-aware evaluator execute an f32 graph as Float? | 16 | 14 | High: `Decl` exhaustiveness and rejection order |
| 2 — checked evidence | Can source specialization and direct raw-plan checking disagree, reject a valid real/bool graph, let f32 evidence reach an existing Float worker, or admit an f32 zero-step block? | 19 | 23 | High: algebra, storage derivation, locator order, interim worker safety |
| 3 — native worker | Does the shared carrier/traversal preserve Float behavior while every f32/bool intermediate rounds in binary32, and do the new f32 entries reject Float-backed evidence? | 16 | 14 | High: numerical truthfulness and shared-worker dispatch |
| 4 — named adapter | Do generic adapter/report shells preserve current APIs, f32-backed Boolean values, and warnings without letting either wrapper relabel another carrier? | 17 | 17 | High: public API and publication order |
| 5 — JAX/docs | Can any f32 plan—including an empty one—obtain reference64 evidence or Python, and are capability claims re-derived? | 6 | 7 | High: evidence boundary and stale capability prose |

These tasks are intentionally not split into “add a type” or “add two guards” sub-tasks: those
pieces have no independent success condition and share their neighbor's mutation cycle. The five
boundaries are independently rejectable: source propagation may stand while checked evidence is
reworked; checked evidence may stand while numerical execution is rejected; the local worker may
stand while the public adapter is rejected; and the native backend may stand while JAX/documentation
closure is corrected.

## 6. Validation

### 6.0 Review cadence

After each of Tasks 1–5, and before starting its dependent task:

1. commit the task's implementation and test changes as one reviewable unit;
2. run an independent review of that task's complete commit against its implementation requirements,
   numbered fixture groups, mutation observations, targeted commands, and the task-specific reviewer
   question in the risk table;
3. inspect unchanged sibling entry points named by the execution-door audit when the task changes a
   shared dtype, checker, worker, adapter, or evidence boundary—a task diff alone is not sufficient;
4. resolve or explicitly adjudicate every finding, rerun every affected mutation and targeted gate,
   and obtain a clean re-review before starting the next task.

These five task reviews do not replace the two independent whole-branch reviews in Section 6.4.
The per-task reviews validate each incremental boundary; the final reviews inspect interactions and
unchanged-code blind spots across the complete branch.

### 6.1 Per-task targeted commands

From `leanncd/`, after building every edited dependency before checking its consumers:

- Task 1: `"$HOME/.elan/bin/lake" build DSL.AstTest DSL.SyntaxTest DSL.ParseProgramTest
  DSL.Pipeline.StructuralTest DSL.Pipeline.TraverseTest DSL.TraverseAxesEquiv
  DSL.TraverseAxesSpike DSL.Pipeline.RouteFragmentCorpusTest Eval.EntryTest Eval.ContractTest
  Eval.ScanTest Eval.Plan.ContractTest Eval.Plan.ScanCompileTest Eval.Plan.SignatureTest
  Eval.Plan.CompileTest Eval.PropertyOracleTest`
- Task 2: `"$HOME/.elan/bin/lake" build Eval.Plan.SignatureTest Eval.Plan.KernelCheckTest
  Eval.Plan.GraphCheckTest Eval.Plan.ScatterCheckTest Eval.Plan.ScanTest Eval.Plan.KernelDenseTest
  Eval.Plan.GraphDenseTest Eval.Plan.BlockTest Eval.Plan.CompileTest`
- Task 3: `"$HOME/.elan/bin/lake" build Eval.TensorTest Eval.Plan.KernelDenseTest
  Eval.Plan.KernelDense32Test Eval.Plan.GraphDenseTest Eval.Plan.NonlinDenseTest
  Eval.Plan.EvalPlan32Test Eval.Portfolio.ScatterNonlinRejectTest`
- Task 4: `"$HOME/.elan/bin/lake" build Eval.Plan.SignatureTest Eval.Plan.CompileTest
  Eval.Plan.AdapterTest Eval.Plan.Adapter32Test Eval.EntryTest`
- Task 5: `"$HOME/.elan/bin/lake" build Eval.Plan.ExecutableTest JaxExperiment`

Run every planned one-file mutation with `leanncd/scripts/mutation-cycle.sh`, record the failing
fixture and observed wrong value/error, then record the restored pass. A build failure unrelated to
the named fixture does not count as a successful mutation.

### 6.2 Existing regression gates

Before each task lands, also run:

- `"$HOME/.elan/bin/lake" build Eval.Plan.DifferentialTest`
- `"$HOME/.elan/bin/lake" build Eval.PropertyOracleTest Eval.PropertyOracleScanTest`
- `"$HOME/.elan/bin/lake" build Eval.Portfolio.Harness`
- the existing route-fragment corpus target `DSL.Pipeline.RouteFragmentCorpusTest`

The current 3,832-case scan-free corpus and 17-case scan corpus remain binary64 reference gates;
their accepted counts and bit results must not change. They are regressions, not f32 evidence.

### 6.3 Documentation and stale-value sweep

Before declaring documentation complete:

1. re-read every edited capability statement against the implemented throw sites and worker entry
   points;
2. run a broad, case-insensitive repo-wide search for every occurrence of `f32` or `binary32` and
   classify each current documentation/comment hit; do not search only exact prose phrases, because
   Markdown backticks, punctuation, and rewording must not hide stale claims. Separately value-grep
   the stale copied counts `4 live`/`four live`/`8 producer-less`/`eight producer-less` and the
   measured pre-slice counts `9 live`/`nine live`/`7 producer-less`/`seven producer-less`, allowing
   arbitrary Markdown punctuation or whitespace between the number/word and `live` or
   `producer-less`. Any current documentation file found by these sweeps becomes a Task 5 file even
   if it was not known when this list was written;
3. classify each hit as current documentation to update or immutable historical record to leave with
   an explicit historical status;
4. grep `Array Float`, `Float.toBits`, `orderedReference64`, `jnp.float64`, and `np.float64` under
   Plan, tests, and the JAX experiment, and confirm each remaining occurrence belongs to a
   Float-backed-only path;
5. update `backend_missing_functionality.md`'s “last re-derived” date and counts from actual code,
   not from this plan.

No shipped documentation text should cite source line numbers; use identifiers and paths.

### 6.4 Full gate and independent reviews

Run `"$HOME/.elan/bin/lake" build` from `leanncd/`. No skipped/default-excluded target may be reported
as covered; `JaxExperiment` is separate and must already have passed.

Then run two independent whole-branch reviews:

1. **Numerical/evidence lens:** trace every f32 value from source declaration and input bits through
   each primitive fold to materialized bits; actively search for a Float conversion, final-only
   rounding, wrong identity, or JAX `orderedReference64` escape.
2. **Boundary/exhaustiveness lens:** inspect the whole diff plus unchanged sibling checkers/workers;
   verify every new `Decl`/mode case, every direct raw-plan door, diagnostic locator/order fixture,
   adapter publication rule, documentation count, and deferred-operation rejection.

Resolve findings, rerun affected mutations and targeted gates, then rerun the full build. The slice
is not complete until both whole-branch reviews are clean or every finding is explicitly
adjudicated.

## 7. Success criteria and stop conditions

The slice is complete only when all of the following are true:

- `tensor f32` elaborates to `Decl.typedTensor .f32` and survives the normal source pipeline;
- the source AST has one extensible typed-tensor constructor rather than one constructor per dtype;
- `DenseTensorOf`, `NamedDenseEnvOf`, and `EvalReportOf` preserve the existing Float aliases while
  allowing later native complex carriers without another container hierarchy;
- storage-kind classification is separate from per-dtype operation admission;
- a homogeneous f32 identity/contraction program prepares to f32 signatures and f32 algebras;
- f32 graphs may contain Boolean signatures and execute both f32→bool and bool→f32 reads in the
  Float32 carrier, while f64/bool and bool-only behavior remains unchanged;
- native `Float32` inputs produce native `Float32` materialized outputs;
- the reduction discriminator produces bits `0` while its binary64 control produces `1`; the
  multiplication fixture pins product bits `1266683904` while binary64 computes exact `16785409`,
  and the two-step product-chain fixture is the discriminator that turns that intermediate
  difference into f32 output `0` versus binary64 output `1`;
- sum/max/min identities are `ScalarConst.f32` with the exact bits in this plan;
- mixed f32/f64 precision and every deferred f32 operation fail before execution with the specified
  typed, located error;
- existing Float-backed checkers/workers and the legacy evaluator cannot execute f32 evidence;
- JAX rejects f32 before candidate construction, evidence, or Python output;
- all 74 numbered fixture groups and 75 mutation cycles have the recorded fail/restored-pass
  observations;
- targeted builds, `JaxExperiment`, full `lake build`, documentation sweep, and two final reviews
  pass.

Stop and revise this plan rather than improvising if Lean 4.30 native arithmetic does not reproduce
the measured bit patterns on the supported build target; if making `Decl.typedTensor .f32` tensor-bearing
requires changing categorical meaning rather than only preserving existing tensor routing; if a
checked f32 value can reach any Float-backed worker without a typed rejection; if parameterizing the
carrier or adapter changes an existing Float API or numerical result; or if the homogeneous-storage
restriction prevents a complete external-to-materialized assignment program. Complex support must
also stop for a separate semantic decision if it would require silently erasing a complex scalar
domain into the current real-valued categorical route, inventing an ordering for min/max, or claiming
bit-exact JAX parity without measuring XLA's operation order.

## 8. Authoring verification record

- Re-derived the current AST, signature, checker/compiler, Dense assignment, nonlinearity,
  scan/scatter, adapter/materialization, legacy evaluator, and experimental JAX boundaries from the
  current files.
- Re-derived the live `CapabilityError` count and stale-value search targets from current throw
  sites/documents. Independent review caught the draft's inherited 4/8 count; direct enumeration of
  all sixteen constructors and current throw sites corrected the boundary to 9 live / 7
  producer-less before this slice and 10 / 6 after it.
- Read Lean 4.30's installed `Init/Data/Float32.lean`; native binary32 is available, so no emulation
  or mislabeled binary64 fallback is proposed.
- Inspected Mathlib's `Data/Complex/Basic.lean`: its `Complex` carrier contains mathematical `Real`
  components and is noncomputable in the ways relevant here; it is not a machine `Complex Float32`
  or `Complex Float` runtime. Future complex64/complex128 execution therefore requires explicit
  component carriers and cannot be inferred merely from JAX support.
- Compiled a Lean 4.30 alias-compatibility probe. A direct abbreviation of a generic projection is
  not usable through legacy field notation; a forwarding definition with an explicit legacy-alias
  parameter is. The `DenseTensor`/`EvalReport` compatibility requirements above use the verified
  latter shape. The probe was removed after the successful check.
- Warm-started this worktree with plain `rsync -a` from a sibling checkout, verified that the
  Mathlib cache rose from 349 to 8,101 oleans, and rebuilt all 8,544 `LeanNCD` jobs before the final
  design check. This prevents a cold Mathlib build and, importantly, refreshes project-owned oleans
  against this worktree rather than trusting the donor's copies.
- Compiled one integrated Lean 4.30 design probe containing `TensorElementType`,
  `TensorStorageKind`, `Decl.typedTensor`, Boolean-neutral first-conflict storage derivation,
  `DenseTensorOf`/`EvalReportOf` with all legacy constructor and projection names, fallible
  `ScalarKernelOps`, carrier-specific unary dispatch, and the assignment traversal's separate
  factor/reduction/term left folds. Its guards accepted f32+bool as `.float32`, f64+bool and
  bool-only as `.float64`, located `[f32, bool, f64, f64]` at slot 2, decoded Boolean constants to
  native Float32 zero/one, and reproduced reduction result bits `0`.
- Compiled a follow-up boundary probe after the final review additions. It verified that
  `InputSignatureBuildError` can wrap the existing `CompileError`, that the two signature
  constructors can share the proposed `Except InputSignatureBuildError InputSignature` result, and
  that `orderedExternalNames` plus `ScanStmt.writes` elaborates as the used-name inventory. The first
  check attempt used `==` on the new error without providing `BEq`; the corrected guard matched the
  exact located constructor directly and compiled, avoiding an unnecessary equality instance in the
  proposed API.
- Compiled a final deriving-obligations probe against Lean 4.30. It verified
  `TensorElementType` with `Lean.ToExpr`, `TensorStorageKind` and `PlanStepKind` with the complete
  checked-diagnostic instances, and `InputSignatureBuildError` with
  `Repr`/`DecidableEq`/`BEq`/`Inhabited`, including `repr` of its wrapped
  `CompileError.duplicateTensorDecl`.
- Mutation-tested the two integrated storage-derivation discriminators available before production
  implementation. Making `.bool` contribute `.float64` caused the f32+bool and mixed-order guards
  to fail; restoring precision-neutral `.bool` compiled. Reporting `slot + 1` caused only the
  first-conflict locator guard to fail; restoring `slot` compiled. The probe was removed after the
  final restored compile.
- Ran two incremental Float32 probes with `check-snippet.sh`. The first corrected probe established
  the reduction discriminator and conversion APIs; the second established multiplication,
  infinities, and signed-zero bits. Both compiled and produced the values recorded in Section 2.4.
- A separate final-review probe established the factor-order discriminator recorded in Task 3:
  input bits `[3252982345, 3252982345, 3276275712]` produce left-fold bits `3357503572` and
  right-associated bits `3357503571`.
- A final term-order probe established that `[16777216, 1, -16777216]` produces left-fold bits `0`
  and right-associated bits `1065353216`, as recorded in Task 3.
- A final exact-output probe established the max/min arrays recorded in Tasks 3 and 4:
  `[-10, -100, -1000, -10000]` maps to
  `[3240099840, 3267887104, 3296329728, 3323740160]`,
  `[10, 100, 1000, 10000]` maps to
  `[1092616192, 1120403456, 1148846080, 1176256512]`, and the end-to-end max/min outputs map to
  `[1077936128, 1084227584]` and `[1065353216, 1065353216]`.
- A Float32 Boolean-carrier probe established `0.25` bits `1048576000` and `0.75` bits
  `1061158912`, used to ensure f32-backed Boolean algebra preserves the current non-binary
  min/max behavior rather than coercing values to zero/one.
- The initial probe attempted `import LeanNCD` before this worktree's library objects were present
  and failed immediately with “unknown module prefix”; it was removed, replaced with the minimal
  Lean 4.30 imports, rerun successfully, and removed separately. No probe file remains.
- This final document contains no Lean fenced code blocks, so there is no transcribed or reformatted
  Lean text in the plan itself to recheck. The numerical probes and the integrated interface probe
  described above were compiled as whole files rather than copied fragments.
- Every existing path in the task file lists was verified in this checkout. `Dense32.lean`,
  `Adapter32.lean`, `KernelDense32Test.lean`, `EvalPlan32Test.lean`, and `Adapter32Test.lean` are
  explicitly new files whose parent directories were verified.
- A fresh objective reference audit corrected stale donor descriptions, symbol qualification, and
  ambiguous subcase counting. Subsequent independent checklist reviews found and drove closure of
  source/raw rejection coverage, recurrence-scratch precision selection, symmetric input-carrier
  errors, independent worker guards, non-binary Boolean adapter behavior, source-order
  discriminators, and Task 4's diagnostic-file scope. A later end-to-end review returned no
  blocking finding but identified four remaining clarity/coherence observations; those were batched
  into the private-kernel placement, named-adapter audit column, robust documentation sweep, and
  test-file/donor wording now present in this revision. Section 8 records the frozen-revision
  reviews only after both independent lenses have inspected this exact text.
- The five tasks contain 74 numbered fixture groups: 16/19/16/17/6 by task. A group is one named
  test fixture and may contain several assertions or paired controls; this is the unit counted in
  the task headers and risk table. Their mutation lists expand to 14/23/14/17/7 = 75 independently
  applied and restored source changes. The two authoring-time storage-derivation mutations above
  have observed fail/restored-pass results; the 75 implementation-dependent cycles are completion gates, not
  claims about code that does not yet exist, and must record both observations while each task is
  implemented.
