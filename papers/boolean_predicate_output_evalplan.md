# Task 4 — Boolean / predicate outputs in the checked `EvalPlan` backend

**Status:** implementation plan, preflight-verified against the tree at commit `429673f`; not
implemented.
This closes the current checked-backend rejection of `Decl.predicate` by
`CapabilityError.booleanOutput`. It does not add native Boolean storage or JAX Boolean execution.

This plan supersedes the Task 4 sketch in
[`predicate_boolean_backend_parity.md`](predicate_boolean_backend_parity.md). That sketch correctly
identified the Float carrier and most signature plumbing, but current inspection found three
additional requirements: direct `ScheduledProgram` inputs must defensively re-establish predicate
source invariants and external-name classification, the independent scan unroller must copy predicate
declarations onto generated leaf tensors, and JAX's standalone candidate APIs need explicit signature
context before they can distinguish Boolean sources. It also found existing JAX support-gate siblings
(tropical algebras and unary reads) that must be rejected alongside Boolean semantics rather than
silently receiving `orderedReference64` evidence.

## 1. Re-derived current boundary

### 1.1 Proven from the current tree

- `Decl.predicate` already exists in `LeanNCD/DSL/Ast.lean`; surface elaboration, UID traversal,
  rank checking, scheduling, and reference evaluation already carry it.
- `capabilityPreflight` visits declarations before statements and short-circuits on the first error.
  Its only Boolean-output rejection is `checkDecl (.predicate n _)`, which throws
  `booleanOutput n`.
- `CapabilityError` currently has **12 constructors**. Static throw-site inspection finds **5 live
  producer families**: `scatterOrAffineLhs`, `unsupportedLhsSlot`, `booleanOutput`,
  `recurrenceOrCallback`, and `noAdvancingAxis`. The other **7** constructors are retained or
  structurally unreachable. Removing the `booleanOutput` producer therefore leaves **4 live
  families** and **8 producer-less/unreachable constructors**, without changing the enum size.
- `ScalarDType.bool` and `ScalarConst.bool` are reserved but live plan values do not produce or
  consume them. `ScalarBinOp.min`/`max` and the three ordered folds already exist.
- `DenseTensor` stores `Array Float`; `NamedDenseEnv`, `EvalReport`, scan histories, and adapter
  transport all carry that same value. The reference `Combine.bool` is `min` within a term and `max`
  across reductions/terms, with `1.0`/`0.0` identities. It does not validate values as binary.
- `checkAssign` currently requires every source and destination to be `f64` and equal. This blocks
  both Boolean destinations and Boolean-tagged predicate inputs.
- `resolveDecls` excludes axis/iteration declarations, but silently overwrites repeated tensor-bearing
  names. `combineFor` instead scans all declarations and can let an earlier same-named axis hide a
  later predicate. Boolean admission cannot tolerate either disagreement.
- `compileScan` records only `stateShapes` and hard-codes `f64` at state captures, base/recurrence
  results, scratch results, and published histories. `checkCaptures` already compares complete
  `TensorSignature`s, but `checkWrites` compares only shape/geometry and can accept a block output
  whose dtype differs from the state destination.
- `PreparedPlan.bindings.materializedNames` preserves schedule order and repeated names.
  `EvalReport` has no dtype channel.
- `prepareEvalPlan` trusts `ScheduledProgram.extNames`; an omitted external read is not allocated and
  later source resolution defaults to slot zero. A direct schedule can therefore bypass predicate
  signature validation or alias a same-shaped input unless preparation re-derives external names.
- `ScanUnroll.independentRun` preserves the original declaration list while generated `%Z_`, `%U_`,
  and `%T_` leaf names are undeclared. A predicate state would therefore use real sum-product in the
  independent oracle unless predicate declarations are generated for its leaves.
- No implemented codec serializes `RawEvalPlan`, `CheckedEvalPlan`, or `PreparedPlan`.
  `Acset`/`Bridge` serialize the separate routed categorical branch, and `Bridge/Realize.lean`
  explicitly hard-codes routed array dtype to reals. That is not on the checked-backend path.
- Experimental JAX rendering has no Boolean algebra implementation. Its validators also do not inspect
  assignment algebra or `ReadPlan.unary`; today a hand-built tropical or unary candidate can be
  stamped with reference evidence even though rendering implements neither semantic. This is the
  same fail-loud support-gate family as Boolean admission.

### 1.2 Exact semantic boundary to implement

`ScalarDType.bool` is a **semantic algebra/signature tag over Float-backed storage**, not a native
runtime carrier.

1. A predicate destination uses `min`, identity `1.0`, for factor conjunction and `max`, identity
   `0.0`, for both contracted-coordinate and term disjunction.
2. An `f64` or `bool` source may feed an `f64` or `bool` assignment. The destination selects the
   algebra; source dtype does not change gathering.
3. Runtime values are not restricted to `0.0` and `1.0`. Non-binary values must retain the reference
   evaluator's literal `min`/`max` behavior.
4. `f32` remains rejected.
5. Declarations and scheduled statements are authoritative: predicate means `bool`; tensor, linear,
   and undeclared external mean `f64`, and external names are reads not produced by any scheduled
   statement. `ScheduledProgram.env` and `ScheduledProgram.extNames` are cached pipeline products, not
   trusted preparation inputs.
6. An explicit input signature that contradicts the declaration-derived dtype is rejected, not
   silently rewritten.
7. Predicate outputs still require identity nonlinearity and sum syntax. The DSL already enforces
   both through `checkDtypes`; the public plan-preparation boundary must re-establish them for a
   hand-built `ScheduledProgram` before capability preflight or shape inference.
8. The same rules apply to top-level outputs, scan state, scan scratch, and downstream reads.
   A scan changes coordinate context and materialization, not Boolean algebra.

### 1.3 Deliberate non-goals

- No native `Array Bool`, bit-packing, truth-value validation, coercion step, or Boolean-specific
  runtime environment.
- No `logicalAnd`/`logicalOr` `ScalarBinOp`; existing Float `min`/`max` are the reference semantics.
- No `f32`, dynamic shapes, scatter support, callback morphisms, or nonlinear predicate outputs.
- No change to source `BoolExpr`, positional predicate IR, Iverson lowering, or mask lowering.
- No dtype field in shared `EvalReport`; dtype is queried from the prepared plan.
- No JAX Boolean, tropical, unary, or contextful execution. This slice makes unsupported semantics
  fail before candidate evidence or Python emission; no context parameter or runtime context support
  is added to the JAX kernels.
- No Acset/Bridge dtype implementation. That routed branch is a separate capability gap and must not
  be implied closed by this checked-backend slice.
- No deletion or renaming of `CapabilityError.booleanOutput`; retain it as a compatibility
  constructor with no producer.

## 2. Architecture and invariant changes

### 2.1 One source declaration authority

Extract a shared tensor-declaration environment builder in
`LeanNCD/DSL/Pipeline/Structural.lean`. It must:

- ignore `.axis` and `.iter`;
- insert `.tensor`, `.linear`, and `.predicate`;
- reject the second tensor-bearing declaration with
  `CompileError.duplicateTensorDecl name`;
- preserve the current reads-minus-produced external-name calculation.

`resolveDecls` and `prepareEvalPlan` both use this builder. Preparation derives the environment from
`sched.decls`; it does not trust a manually assembled `sched.env` for dtype. `combineFor` in
`LeanNCD/Eval/Contract.lean` must search only tensor-bearing declarations, so a same-named axis cannot
hide a predicate. This is one source classification rule with two consumers, not two independent
name filters.

Extract the existing reads-minus-produced external-name calculation over `ScanStmt`s and use it in
both `schedule` and `prepareEvalPlan`. Preserve first-seen scheduled-read order for bindings, but do
not filter that traversal through `sched.extNames`. A direct schedule with a missing or extra cached
external name must behave exactly like the structurally equivalent source-produced schedule. Keep
`ScheduledProgram.extNames` for compatibility; this slice stops treating it as authority.

Extract the predicate-output part of `checkDtypes` into a shared pure check and run it:

- from the existing source pipeline, preserving its statement order and existing
  `CompileError.predicateAgg`/`predicateNonlin` results;
- defensively over `plain` statements and each scan's `base ++ recur` in `prepareEvalPlan`.

Add `PlanCompileCause.sourceInvariant (cause : CompileError)` and the `BEq` support required by its
existing derived instances. For direct schedules, source-invariant validation runs before capability
preflight. Its per-statement order remains nonlinearity before aggregation, matching current
`checkDtypes`. A schedule violating both reports `predicateNonlin`; neither shape inference nor input
signature validation runs.

This keeps invalid source combinations out of `CapabilityError`: predicate max/min and predicate
nonlinearity are invalid source, not valid-but-unsupported backend capabilities.

### 2.2 Static signatures and public result meaning

In `LeanNCD/Eval/Plan/Signature.lean`, add one declaration-aware constructor:
`InputSignature.ofDenseInputsForDecls`. It takes the validated `DeclEnv`, copies Dense shapes, and
labels declared predicates `bool`, all other names `f64`. Keep `ofDenseInputs` unchanged as the
all-`f64` compatibility helper. Import `LeanNCD.DSL.Pipeline.Types` to name `DeclEnv`; this is a new
one-way dependency and creates no import cycle.

During preparation:

- accept only `f64` and `bool` external signature tags;
- require the supplied tag to equal the declaration-derived tag;
- add `InputSignatureError.dtypeMismatch name expected actual`;
- copy the complete validated signature into the positional table rather than rebuilding it as
  `f64`;
- derive every produced signature from the destination declaration.

Add `PreparedPlan.materializedSignatures : Array (String × TensorSignature)`. It follows
`materializedNames` in stored order, looks each slot up in `plan.raw.tensorSigs`, and preserves
repeated names. Do not alter `runPreparedDense`, `unpack`, or `EvalReport`.

### 2.3 Boolean assignment evidence and Dense execution

Add `admittedAlgebraBool` in `LeanNCD/Eval/Plan/Check.lean`:

- factor operation `min`, constant `.bool true`;
- reduction/term operation `max`, constant `.bool false`.

Make algebra admission destination-specific:

| Destination dtype | Admitted assignment algebras |
|---|---|
| `f64` | real sum-product, tropical max, tropical min |
| `bool` | Boolean min/max only |
| `f32` | none |

For reads, admit `f64` and `bool`, reject `f32`, and deliberately remove source/destination equality
as an assignment obligation. Retain `PlanError.dtypeMismatch` as a producer-less compatibility
constructor; nonlinearity checking still uses its separate `NonlinPlanError.dtypeMismatch`.
`CheckedAssignPlan` remains private-constructor evidence around the checked raw assignment; no second
Boolean checked type is needed.

Extend `Dense.constFloat` with `.bool true => 1.0` and `.bool false => 0.0`. `applyOp`,
`factorFold`, `reductionFold`, `termFold`, gathering, store validation, and the positional Float store
otherwise remain unchanged.

### 2.4 Top-level and scan compilation

Use one compiler-local `dtypeForName` over the validated declaration environment. Apply it to every
external and produced signature.

At top level, identity predicate statements allocate one Boolean destination and use the Boolean
algebra. Source nonlinear validation guarantees that pointwise/axiswise chains remain `f64`; do not
create Boolean preactivation or nonlinear slots.

Replace private `CompiledScan.stateShapes` with complete `stateSigs`. Thread those signatures through:

- outer state destinations and published complete histories;
- base assignment results;
- recurrence assignment results;
- state captures;
- predicate or real scratch results;
- any internal preactivation/result allocation, which remains `f64` because predicate nonlinearities
  were rejected before compilation.

The scan worker still allocates zero-filled Float arrays and `commitWrite` still copies Floats.
Boolean false is already represented by `0.0`.

Extend `ScanPlanError` with
`writeDtypeMismatch (isBase, writeIndex, stateIndex, expected, actual)`. In `checkWrites`, perform the
dtype comparison after validating state/output slot existence but before write rank, geometry,
extent, and literal checks. This is a semantic write invariant; do not change
`classifyWriteRow`, `baseWriteRowsOk`, `stepWriteRowsOk`, `freeExtentsAgree`,
`pinnedLiteralsInRange`, `writesCollide`, or causality.

### 2.5 Independent oracle and JAX support boundary

Extend `ScanUnroll.Unrolled` with generated tensor-bearing declarations, or an equivalent explicit
sidecar used by `independentRun`. Every generated state/scratch leaf inherits predicate-versus-tensor
kind from the source destination it replaces and uses that leaf's retained axes. Evaluate the
scan-free leaf schedule with those declarations installed. Do not call checked-plan dtype helpers,
Boolean algebra constants, or Dense plan workers from the oracle.

Before either experimental JAX rendering mode or candidate construction:

1. visit checked nodes in outer step order;
2. reject a non-`f64` destination;
3. reject any algebra other than real sum-product;
4. reject a contextful assignment — non-empty `AssignPlan.contextShape` (added by the Task 4.5
   closure finding: JAX assignment kernels support only context-free assignments, and both lowerings
   previously rendered a contextful one context-free and stamped it with evidence);
5. visit factors in original term/factor order and reject a non-`f64` read or a unary read;
6. retain the existing located Iverson and unsupported-step rejections.

Add typed `JaxCodegenError` cases for unsupported dtype, algebra, unary factor, and structurally
incompatible standalone signature context with available step/term/factor/slot locators. The
completed [signature/evidence ownership spike](jax_signature_evidence_ownership_spike_results.md)
selected validator-supplied context (**GO B**):

- raw affine/einsum candidates retain no signature table;
- standalone renderers, candidate conversions, and validators take one explicit complete
  `Array TensorSignature`, re-run `checkAssign` under it, and treat it as their semantic authority;
- plan-level paths accept no parallel table and derive only
  `PreparedPlan.plan.raw.tensorSigs`;
- private `JaxKernel` stores the validated complete table with
  `JaxKernelWellFormed table candidate`;
- executable well-formedness ties every stored table and semantic assignment to the corresponding
  prepared checked step; and
- the pre-validation evidence-label helper and context-free semantic helpers are private.

Independently of the signature-support policy, einsum validation recomputes every exact operand axis
from the checked factor maps and requires exact output-axis equality with the checked term. Same-rank,
in-range permutations or duplicates are invalid candidates.

Thus `orderedReference64` is exposed only after source dtype and all existing structural checks pass.

The required sibling-audit artifact is this completed table, populated from implemented code:

| Assignment feature | Dense checked plan | JAX render | JAX candidate evidence |
|---|---|---|---|
| `f64`, real algebra, plain read | required | required | required |
| `f64`, tropical max/min | required | forbidden | forbidden |
| `bool`, Boolean algebra | required | forbidden | forbidden |
| `bool` source into real destination | required | forbidden | forbidden |
| unary read | required | forbidden | forbidden |
| Iverson factor | required | forbidden | forbidden |
| contextful assignment (non-empty `contextShape`) | required | forbidden | forbidden |

Every forbidden cell needs a located test. No cell may be silently ignored.

## 3. Implementation tasks

Task boundaries pass the reviewer-rejection test: declaration authority, local checked execution,
source-facing top-level compilation, scan state/write semantics, and experimental backend/docs each
have an independent failure mode and rollback surface.

The backend inventory's Task 4 is split into five independently reviewable implementation tasks,
numbered 4.1–4.5.

### Task 4.1 — Make declaration and source-invariant authority coherent

**Files**

- `leanncd/LeanNCD/Exec/Uid.lean`
- `leanncd/LeanNCD/DSL/Pipeline/Structural.lean`
- `leanncd/LeanNCD/Eval/Contract.lean`
- `leanncd/LeanNCD/Eval/Plan/EvalPlan.lean`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/test/DSL/Pipeline/StructuralTest.lean`
- `leanncd/test/Eval/ContractTest.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean`
- `leanncd/test/Eval/Plan/AdapterTest.lean`
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`
- `leanncd/experiments/jax_bridge/EvalPlanAffineSmoke.lean`

**Deliverable**

Implement the shared duplicate-safe declaration builder, tensor-only reference lookup, shared
predicate-output invariant check, authoritative scheduled external-name derivation, and
`sourceInvariant` preparation failure. Update every exhaustive `PlanCompileCause` renderer in the
same task, including the non-default JAX renderer. Do not admit predicate declarations at capability
preflight yet; this task can land with the old Boolean-output rejection. Since `resolveDecls` becomes
fallible, update its “never throws” production doc comment and the matching StructuralTest message.

**Fixtures: 11; planned mutation cycles: 6**

1. Clone StructuralTest's “a `tensor` decl lands in env” fixture; append a second
   `.tensor "A" []`; require `duplicateTensorDecl "A"`.
2. Clone the same fixture; replace both declarations with `.predicate "A" []`; require the same
   error.
3. Clone the same fixture twice; use tensor-then-predicate and predicate-then-tensor declarations
   named `A`; require the same error in both orders.
4. Clone StructuralTest's declared-read wrong-rank fixture; add duplicate `W` tensor declarations
   while retaining the bad read rank; require duplicate declaration, distinguishing the new
   resolve-before-rank order.
5. Clone ContractTest's scalar real-versus-Boolean contraction; insert an earlier `.axis` whose axis
   name is `Result` before `.predicate "Result" []`; require the Boolean result `1.0`, proving the
   axis cannot hide the predicate.
6. Clone MaxReduceTest's `checkDtypes` predicate-aggregation rejection into StructuralTest; make the
   same statement also pointwise; require `predicateNonlin`, distinguishing
   nonlinearity-before-aggregation.
7. Clone CompileTest's `acceptedSched`; build a direct predicate-output schedule violating both
   aggregation and nonlinearity, change its LHS to the existing affine-LHS capability donor, and omit
   a required input signature; require
   `sourceInvariant predicateNonlin` with empty warnings, distinguishing source validation from
   capability and signature phases.
8. Clone CompileTest's direct predicate-output schedule from fixture 7; restore identity
   nonlinearity but retain max aggregation; require `sourceInvariant predicateAgg`.
9. Clone CompileTest's `contractSched` two-input donor, give both real inputs the same shape, and
   remove `B` from `sched.extNames`. Require distinct ordered input bindings and verify the second
   read resolves to `B`'s slot rather than slot zero. Repeat with one extra unused cached external
   name and require the same prepared bindings. Keep this Task 4.1 fixture all-real so it lands before
   Boolean preflight/read admission; Task 4.3 fixture 4 adds the predicate-signature variant.

Mutation cycles must temporarily restore last-wins insertion, let axis declarations participate in
`combineFor`, swap predicate aggregation/nonlinearity check order, and skip each defensive direct-
schedule check, including authoritative external-name derivation. Each named fixture must fail under
its mutation and pass after restoration. Build `Eval.Plan.CompileTest`, `Eval.Plan.AdapterTest`,
`Eval.Plan.ScanCompileTest`, and non-default `JaxExperiment` before this task is considered
independently landable. Also run the 3,832-case scan-free corpus, the 17-case scan corpus, Portfolio,
and RouteWeave coverage before landing; confirm no current program declares one tensor-bearing name
twice. A count change is a blocker to investigate, not an expected consequence of duplicate safety.

### Task 4.2 — Admit Boolean local assignments and Float-backed Dense execution

**Files**

- `leanncd/LeanNCD/Eval/Plan/Types.lean`
- `leanncd/LeanNCD/Eval/Plan/Check.lean`
- `leanncd/LeanNCD/Eval/Plan/Dense.lean`
- `leanncd/test/Eval/Plan/KernelCheckTest.lean`
- `leanncd/test/Eval/Plan/KernelDenseTest.lean`

**Deliverable**

Add the Boolean algebra, destination-specific algebra admission, mixed `f64`/`bool` reads, and Boolean
constant decoding. Keep `f32` rejected and keep nonlinear checkers unchanged.

**Fixtures: 12; planned mutation cycles: 7**

1. Clone `KernelCheckTest.goodPlan`; change only destination signature and assignment algebra to
   `bool`/Boolean; require acceptance.
2. Clone `goodPlan`; change only source slot 0 to `bool`; retain `f64` destination; require acceptance.
3. Clone fixture 1; restore source slot 0 to `f64`; require acceptance into the Boolean destination.
4. Clone fixture 1; restore the assignment algebra to `admittedAlgebra`; require
   `algebraNotAdmitted`.
5. Clone the existing destination-`f32` and source-`f32` guards; keep their one-field mutations and
   exact `dtypeNotAdmitted` slot payloads.
6. Clone `KernelDenseTest.efpPlan`; change destination signature and algebra to Boolean; require an
   empty factor product to evaluate to `1.0`.
7. Clone `KernelDenseTest.zerdPlan`; change destination signature and algebra to Boolean; require the
   zero-extent reduction to evaluate to `0.0`.
8. Clone `KernelDenseTest.contractPlan`; use two completed true terms at one output coordinate,
   change destination/algebra to Boolean, and require `1.0`, not numeric sum `2.0`.
9. Clone `contractPlan`; place a zero-valued source factor in one term, use Boolean algebra, and
   require that term to contribute `0.0`.
10. Clone fixture 8 with non-binary factor values `0.25` and `0.75`; require literal Float
    min/max behavior rather than rejection or truth coercion.
11. Clone the existing direct `PlanError.dtypeMismatch` constructor guard; update its comment to state
    that assignment checking intentionally no longer produces it, while nonlinear checking retains
    its separate dtype-equality error.

Mutate Boolean `reduceOp` to `add`, Boolean identities independently, `.bool` constant decoding, the
mixed-source admission, and each `f32` rejection. Record observed values and the restored pass.

### Task 4.3 — Admit top-level predicate outputs and expose signatures

**Files**

- `leanncd/LeanNCD/Eval/Plan/Signature.lean`
- `leanncd/LeanNCD/Eval/Plan/Prepared.lean`
- `leanncd/LeanNCD/Eval/Plan/Error.lean`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/test/Eval/Plan/SignatureTest.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean`
- `leanncd/test/Eval/Plan/AdapterTest.lean`
- `leanncd/test/Eval/Plan/DifferentialTest.lean`

**Deliverable**

Add strict declaration-aware input signatures, derive all top-level destination dtypes, select the
destination algebra, expose ordered materialized signatures, and turn `checkDecl`'s predicate arm
into admission. Retain `booleanOutput` without producers.

**Fixtures: 12; planned mutation cycles: 7**

1. Clone SignatureTest's `conversionInputs`; add a predicate declaration for `X` to its environment
   and call `ofDenseInputsForDecls`; require `X` to be `bool`.
2. Clone the same fixture with no declaration; require `f64`, and retain the existing
   `ofDenseInputs` guard unchanged.
3. Clone GnnScatterTest GN2; compile its schedule and construct the declaration-aware signature;
   require `edge : bool` and `X : f64`.
4. Clone Task 4.1 fixture 9, declare `B` as predicate while keeping it absent from cached
   `sched.extNames`, then run two variants: change only `B`'s explicit signature to `f64`, then only
   `A`'s to `bool`; require exact `InputSignatureError.dtypeMismatch` expected/actual payloads. The
   `B` variant proves authoritative external-name derivation reaches declaration-aware Boolean
   validation.
5. Clone DifferentialTest's RL1 entry; add `predicate I(i, j)` and retain the identity output;
   require checked/reference agreement and the existing identity matrix.
6. Clone ContractTest's scalar Boolean contraction as a source program with a declared predicate
   destination; require `1.0` where real sum-product yields `2.0`.
7. Clone fixture 6; replace factors with non-binary `f64` sources `0.25` and `0.75`; require the
   reference and checked paths both produce `0.75` and do not add a runtime truth check.
8. Clone CompileTest's `repeatSched`; declare `Y` as predicate and leave `Z` real; require
   `materializedSignatures` to be `[Y:bool, Y:bool, Z:f64]` in that exact repeated-name order.
9. Clone AdapterTest's zero-coefficient named round trip; replace its program with fixture 5 and use
   declaration-aware signatures; require `pack -> runDensePlan -> unpack` to preserve the Float data
   and expose `I:bool` through the prepared accessor.
10. Clone CompileTest's current `booleanOutput` guard; require preflight success after changing no
    field except the expected result.
11. Clone that guard, append the existing scatter statement donor, and require
    `scatterOrAffineLhs "Out"`; this distinguishes “predicate admitted, next source-order statement
    checked” from accidentally skipping statement preflight.

Mutation cycles must hard-code produced or external signatures to `f64`, use source dtype instead of
destination dtype for algebra, accept contradictory explicit signatures, deduplicate materialized
names, reintroduce `booleanOutput`, and add a 0/1 runtime check. Each mutation has a fixture above that
fails independently.

### Task 4.4 — Preserve Boolean state and scratch semantics through scans

**Files**

- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/LeanNCD/Eval/Plan/Scan.lean`
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`
- `leanncd/test/Eval/Plan/ScanTest.lean`
- `leanncd/test/Eval/PropertyOracle/ScanGen.lean`
- `leanncd/test/Eval/PropertyOracle/ScanUnroll.lean`
- `leanncd/test/Eval/PropertyOracle/ScanOracle.lean`
- `leanncd/test/Eval/Plan/DifferentialTest.lean`

**Deliverable**

Replace shape-only compiler state metadata with full signatures, enforce write dtype equality, and
make the independent leaf oracle preserve predicate declarations. Do not alter write geometry or
causality.

**Fixtures: 8; planned mutation cycles: 11**

1. Clone `PropertyOracle.ScanGen.template4`; add `predicate S(l)`, set every `X` element to `1.0`,
   and retain the two recurrence terms `S[l] + X[l]`; keep the clone inside `ScanGen.lean` because
   `template4` is private. Require a history of all `1.0`, distinguishing Boolean disjunction from
   numeric accumulation.
2. Clone public `PropertyOracle.ScanGen.template3`; declare only `G` as predicate and retain `H` as
   real; require both published histories to agree across checked, reference, and unrolled legs.
   Observe and record the values from the real run before placing them in a completion record.
3. Clone ScanCompileTest's `scratchSched`; declare its scratch destination predicate while leaving
   persistent state real, and make a later recurrence assignment read it; require scratch signature
   `bool` and checked/reference agreement.
4. Clone `ScanTest.linearScan` into an accepted Boolean raw donor. Change the outer seed/state,
   recurrence capture/result, and recurrence algebra to Boolean. Replace the base block's
   input-is-output shortcut with separate Boolean input and output slots plus a Boolean identity
   assignment from the captured seed; point the base write at that output slot. Require
   `checkScanPlan` and `runDenseScan` success.
5. Clone fixture 4; change the base block output dtype to `f64` and its assignment algebra to admitted
   real sum-product while leaving the state destination Boolean; require `writeDtypeMismatch true`
   with the exact write/state/dtype payload. Changing both fields keeps block checking valid so the
   fixture reaches write checking.
6. Clone fixture 4; make the same paired dtype/algebra change only in the step block; require
   `writeDtypeMismatch false` with the exact payload.
7. Clone fixture 5 and also corrupt its write-map coefficient rank; require the dtype error, proving
   dtype checking precedes rank/geometry. This fixture distinguishes the stated order because the
   block remains valid and either write check would fail on its own.
8. Clone ScanUnroll's existing `template1` leaf-name assertion using fixture 1's predicate state;
   require generated `%Z_S` and every `%U_S_*` declaration to be predicate, then register and run the
   three-way oracle in `DifferentialTest.lean`; `ScanOracle.lean` remains the two-way leg. Temporarily
   omit generated predicate declarations and observe the real-sum disagreement.

Mutation-test each actual former compiler `f64` allocation independently: base assignment,
pointwise, and axiswise results; the state capture; step assignment, pointwise, and axiswise results
(shared by recurrence and scratch according to later classification); and the published complete
history in `prepareEvalPlan` (eight cycles). There is no separate state-signature allocation site:
the state dtype and published history are established together. Also mutate base and step write dtype
checks and generated oracle declarations (three cycles), for **11 planned mutation cycles** total. A
single endpoint test is not sufficient.

Because dtype is newly live in `checkWrites`, Task 4.4 must append a row to the existing write
case-by-class audit. Re-read unchanged siblings `baseWriteRowsOk`, `stepWriteRowsOk`,
`freeExtentsAgree`, `pinnedLiteralsInRange`, `writesCollide`, and their call sites. Record every cell
as required, forbidden, or intentionally ignored. If any geometry predicate changes, stop and expand
to the full recurring write-geometry audit before continuing.

### Task 4.5 — Close experimental backend gates, corpus, and documentation

**Files**

- `leanncd/LeanNCD/Eval/Plan/Executable.lean`
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`
- `leanncd/experiments/jax_bridge/EvalPlanAffineCorpus.lean`
- `leanncd/test/Eval/Plan/ExecutableTest.lean`
- `leanncd/test/Eval/Plan/DifferentialTest.lean`
- `papers/backend_missing_functionality.md`
- `papers/predicate_boolean_backend_parity.md`
- `papers/leanncd.md`
- `papers/wave_c_capability_manifest.md`
- `papers/wave_f_capability_manifest.md`
- `papers/wave_f_scanplan_proposal.md`
- `papers/eval_ir.md`
- `papers/jax_evalplan_architecture.md`
- `leanncd/LeanNCD/Eval/AGENTS.md`
- `leanncd/AGENTS.md`
- `leanncd/experiments/jax_bridge/README.md`
- `leanncd/docs/test_portfolio.md`

**Deliverable**

Implement the completed §8 spike's validator-supplied signature/support context across every public
renderer and candidate/evidence entry point, extend the separate predicate differential corpus with
Boolean outputs without changing the 3,832 affine corpus, remeasure all boundary counts, and update
current-state documentation.

Before threading the new context, close the pre-existing einsum exact-axis recomputation weakness
recorded by the spike. `validateEinsum` must recompute each expected operand row from the checked
term as the factor's source slot followed by the exact single-projection target of every coefficient
row, and require exact equality with the candidate row. It must likewise require
`kernel.outputAxes == term.outputPos`, not merely that every stored position is in range. Add a
private production-local projection-target helper in `Executable.lean`; do not import the
experimental `rowProjectionTarget` against the dependency direction, and do not change the raw
candidate record. Establish this sound validator baseline before applying the Variant B API changes.

The spike selected these exact public signatures (line breaks abbreviated):

```text
lowerAssign sigs nodeIndex checked
renderAffineAssign sigs checked
loweringToAffineTableCandidate sigs nodeIndex checked
loweringToEinsumCandidate sigs nodeIndex checked
validateAffineTable sigs candidate
validateEinsum sigs candidate
kernelWellFormedBool sigs candidate
JaxKernelWellFormed sigs candidate
validateAndConstructKernel sigs candidate
```

`lowerPlan`, `generateForward`, both plan renderers, `generateNamed`, and
`lowerCheckPlanToCandidate` derive the checked/prepared table and retain no context parameter.
`lowerFactor`, `lowerTerm`, `renderTermLine`, `renderNodeLines`, affine factor/term/node/array
renderers and affine table recomputation helpers are private. Add private `jaxAssignSupported` and
make the new `checkJaxAssignSupport` the typed, context-bearing cross-module helper.
`candidateEvidenceLabel`, currently public in `Executable.lean`, becomes private; adapt its direct
`ExecutableTest` coverage to assert through the nearest public validator. Raw candidate records
remain unchanged; `JaxKernel` gains the validated table.

**Fixtures: 11; planned mutation cycles: 11**

1. Clone `ExecutableTest.idRaw`; change destination signature and assignment algebra to Boolean;
   require both kernel validators and executable construction to reject it.
2. Clone `idRaw`; change only the source signature to `bool`; require checked-plan acceptance and
   exact `.sourceDType 0 0 0 .bool` rejection. Exercise the public signatures listed above plus
   `lowerPlan`, `generateForward`, both `generateNamed` modes, both plan renderers,
   `EvalPlanCodegen.buildAssignFixture`, `lowerCheckPlanToCandidate`, `JaxExecutableWellFormed`, and
   executable construction. Test private helpers through their nearest public caller.
3. Clone `idRaw` twice; change only its algebra to `admittedAlgebraMax` and
   `admittedAlgebraMin`; require typed unsupported-algebra rejection.
4. Clone `idRaw`; change only `idRead.unary` to `some .exp`; require a located unary rejection from
   both rendering modes and both candidate validators.
5. Clone `EvalPlanCodegen`'s `idIversonRaw`; retain its factor at original factor index 1 and keep the
   existing `iversonFactor 0 0 1` result.
6. Clone `ExecutableTest.mixedRaw`; make only step 1's destination/algebra Boolean; require the JAX
   rejection to name step 1, distinguishing outer index from “first assignment” index 0.
7. Clone fixture 1 and make its source Boolean too; require destination-dtype rejection before source
   traversal, distinguishing the declared support-check order.
8. Extend DifferentialTest's existing `predicatePrograms` from its six current entries with Task 4.3
   fixtures 3, 5, 6, and 7; pin the new exact length and run every entry through checked/reference
   agreement plus its observed value. Do not add them to `PropertyOracle.enumPrograms`.
9. Add Task 4.4 fixtures 1 and 2 to the curated three-way scan set; require checked, reference, and
   independent-unroll equality.
10. Clone `NonlinDenseTest.idNode22` into `ExecutableTest` as a single-term two-dimensional identity
    candidate. Require the exact operand row `#[sourceSlot, 0, 1]` and output axes `#[0, 1]` to pass.
    From that baseline, change only the operand axes to `#[1, 0]`, then only the output axes to
    `#[1, 0]`, then only the output axes to `#[0, 0]`; require all three same-rank, in-range candidates
    to fail. These mutations distinguish exact semantic recomputation from the current
    bounds-and-length checks.
11. Retain the spike's authority attacks: (a) F4, a Boolean-source `PreparedPlan` plus a same-shape
    all-real table, must have no caller-table plan API and a manually substituted validated kernel
    must fail executable construction; (b) a standalone all-real table with mismatched shapes must
    fail the re-run `checkAssign`; (c) a two-step plan whose Boolean read is only at step 1 must reject
    at step 1 when step 0's valid context/result is cached or reused.

Run eleven mutation cycles: replace exact einsum operand/output equality with the previous
bounds-and-length checks; bypass source dtype across every public path; reverse destination/source
support order; bypass algebra; bypass unary; construct evidence before contextual validation; add a
caller-selectable all-real plan table; remove the per-step context/assignment tie (including cached
step-0 context); rotate context removal through every surviving public entry and skip standalone
`checkAssign`; hard-code outer locator 0; and drop the new Boolean corpus entries. Record every
failing and restored observation.

## 4. Risk sizing

| Task | Main risk | Fixtures | Mutation cycles | Reviewer rejection boundary |
|---|---|---:|---:|---|
| 4.1 | declaration ambiguity, external-name authority, diagnostic precedence | 11 | 6 | Source semantics can be rejected while all plan execution work stands |
| 4.2 | wrong Boolean identities/algebra or accidental type tightening | 12 | 7 | Local checker/Dense semantics can be rejected independently |
| 4.3 | signature authority, top-level allocation, result metadata | 12 | 7 | Public top-level boundary can fail while raw execution is correct |
| 4.4 | one missed scan `f64`, unsound write dtype, oracle self-mismatch | 8 | 11 | Scan semantics and write evidence are a separate soundness surface |
| 4.5 | exact einsum axes, JAX context authority, unsupported semantics stamped as reference, stale boundary docs | 11 | 11 | Experimental backend evidence/docs can be rejected without rolling back Dense |
| **Total** |  | **54** | **42** |  |

The fixture count, not expected production-line count, makes Tasks 4.2–4.4 high-review work. Do not
split tiny type additions from the checker/compiler that produces them; they have no independent
failure mode. Do not merge Task 4.4 into Task 4.3: a reviewer can approve top-level Bool while
rejecting scan write evidence or oracle independence.

## 5. Diagnostics, order, and mutation requirements

The following order claims each have a distinguishing fixture:

- duplicate declarations before rank checking: Task 4.1 fixture 4;
- source predicate nonlinearity before predicate aggregation and before plan capability/signature
  checks: Task 4.1 fixtures 6–8;
- first-seen external binding order without cached-`extNames` filtering: Task 4.1 fixture 9;
- declaration admission followed by normal statement preflight: Task 4.3 fixture 11;
- scan write dtype before rank/geometry: Task 4.4 fixture 7;
- exact einsum operand/output axes rather than same-rank in-range substitutes: Task 4.5 fixture 10;
- JAX outer step index and destination-before-source support checks: Task 4.5 fixtures 6–7;
- original all-factor index for Iverson remains pinned by Task 4.5 fixture 5.

All failure assertions compare full constructors and payloads, not only `.isError`. Any new index is an
index into the original unfiltered source array. No new diagnostic in this plan needs a declaration
index; duplicate declaration errors intentionally name the duplicated tensor only.

For every regression/parity fixture, the implementer records:

1. baseline pass;
2. the exact named mutation;
3. failure at the intended fixture (and whether other targeted tests fail);
4. restored pass.

Expected numeric values not already present in a donor must be copied from an actual reference run
before being asserted. Hand-derived prose is not evidence.

## 6. Capability and documentation sweep

After implementation, remeasure rather than copy:

- `CapabilityError`: 12 constructors, expected 4 live producer families and 8 retained/unreachable
  families after this slice; verify throw sites rather than trusting this expectation;
- `CompileTest`'s current “9 top-level rejection categories” claim and assertion; record the new
  count after predicate-output admission;
- scan-free `enumPrograms`: currently source-pinned at 3,832 accepted of 3,832 and intentionally
  unchanged;
- `predicatePrograms`: currently 6 entries; record its actual new total;
- `enumScanCases`: currently source-pinned at 17 accepted of 17 with zero unsupported nonlinearity
  and aggregation cases; record whether the curated generator itself changed;
- the curated three-way scan fixture count;
- JAX support-feature counts and affine corpus count;
- full Lake build job count.

Value-grep the whole repository for the old values and split strings: `3832`, `3,832`, `17 accepted`,
`accepted == 17`, `predicatePrograms`, `booleanOutput`, “Boolean declared outputs”, “f64-only”, and
“only f64”. Classify each hit as current, historical/frozen, or stale. Rewrite
`wave_c_capability_manifest.md`'s opening claim that it describes what is accepted “today” so the
whole document is explicitly a historical Wave C snapshot; do not partially modernize its table.

Update current-state docs to say:

- predicate factors/masks and declared predicate outputs are admitted by Dense;
- Boolean values remain Float-backed and unvalidated;
- source declarations determine static signature/algebra;
- JAX explicitly rejects Boolean, tropical, unary, contextful, Iverson, nonlinear, and scan
  semantics it does not implement;
- Acset/Bridge routed dtype remains a separate gap.

Update `papers/leanncd.md`'s semantic-compilation section so it no longer says all predicate
evaluation is deferred; distinguish admitted reference/checked Dense semantics from the still-real
routed `BrBaseP` dtype gap.

Historical plans remain historical unless they claim the current boundary. Pre-classify
`test/Eval/Plan/ContractTest.lean`'s Wave C capability rows as historical/frozen: its predicate,
Iverson, max, and min classifications are intentionally not a current capability table.

## 7. Validation and review

From `leanncd/`, invoke Lake through `"$HOME/.elan/bin/lake"`. Build every edited production module
before direct test-file checks so stale `.olean` files cannot produce false evidence.

### Targeted validation

1. Build the edited production modules:
   `LeanNCD.DSL.Pipeline.Structural`, `LeanNCD.Eval.Contract`,
   `LeanNCD.Eval.Plan.Check`, `LeanNCD.Eval.Plan.Dense`,
   `LeanNCD.Eval.Plan.Signature`, `LeanNCD.Eval.Plan.Prepared`,
   `LeanNCD.Eval.Plan.Compile`, `LeanNCD.Eval.Plan.Scan`,
   `LeanNCD.Eval.Plan.Executable`.
2. Run the affected default test modules:
   `DSL.Pipeline.StructuralTest`, `Eval.ContractTest`,
   `Eval.Plan.KernelCheckTest`, `Eval.Plan.KernelDenseTest`,
   `Eval.Plan.NonlinCheckTest`, `Eval.Plan.NonlinDenseTest`,
   `Eval.Plan.SignatureTest`, `Eval.Plan.CompileTest`,
   `Eval.Plan.AdapterTest`, `Eval.Plan.ScanCompileTest`,
   `Eval.Plan.ScanTest`, `Eval.PropertyOracle.ScanUnroll`,
   `Eval.PropertyOracle.ScanOracle`, `Eval.Plan.DifferentialTest`,
   and `Eval.Plan.ExecutableTest`.
3. Build non-default `JaxExperiment`, then directly elaborate
   `experiments/jax_bridge/EvalPlanAffineCorpus.lean`. Run
   `experiments/jax_bridge/run-evalplan-affine.sh` and
   `experiments/jax_bridge/run-evalplan-affine-corpus.sh`; supported all-real corpus behavior must
   remain unchanged and Boolean/tropical/unary fixtures must fail in Lean before Python emission.
4. Run every mutation cycle listed in the task that introduced its fixture.

### Full validation

- Run the full `lake build` from `leanncd/`; no skipped target is a green build.
- Rerun the corpus/count commands and stale-value grep after the full build.
- Confirm `git diff --check`, no generated cache/artifact files, and no production imports from
  `experiments/jax_bridge`.

### Final whole-branch reviews

Run two independent reviews over the entire branch, not task diffs:

1. **Semantic parity and boundary lens:** source declaration authority, mixed source/destination
   dtype policy, authoritative external-name derivation, Boolean `min`/`max` and identities,
   non-binary Float behavior, top-level versus scan parity, result signature visibility, independent
   oracle separation, and Acset/Bridge non-claims.
2. **Soundness and fail-loud lens:** checker private-constructor evidence, all scan signature
   allocation/capture/write sites, write dtype order and locators, unchanged geometry/causality
   siblings, direct-schedule source invariants, exact einsum operand/output recomputation, JAX
   support table, original factor/step indices, and mutation-test integrity.

Any real finding is fixed, targeted mutations rerun, full build rerun, and both lenses repeated or
explicitly adjudicated before landing.

## 8. Risky unknowns / follow-up spikes

### Resolved before Task 4.5 — JAX signature/evidence ownership

The mandatory spike is complete:
[results and mutation record](jax_signature_evidence_ownership_spike_results.md). Decision:
**GO B — validator-supplied complete context**.

Both candidates-in-context and validator-supplied context passed the Boolean-support,
plan-authority, locator, evidence, and all-real probes. Candidate-owned context did not satisfy the
full standalone fail-loud/helper-privacy criterion: its renderer/candidate-conversion entry gates
did not re-run `checkAssign` against structurally incompatible context, and three geometry helpers
remained public. B alone passed every selection criterion. It preserves the raw candidate record
shapes and stores the complete table only in the validated `JaxKernel`, while standalone APIs
receive one explicit table and plan APIs derive the sole authority from
`PreparedPlan.plan.raw.tensorSigs`. The exact signatures, private-helper decisions, fixtures, and
eleven production mutation cycles are now in Task 4.5 above.

### No other architecture spike is warranted

Static inspection settles the risky semantic questions:

- carrier/storage: every evaluator and adapter uses `DenseTensor.data : Array Float`;
- algebra: reference `Combine.bool` explicitly supplies `min`, `max`, `0.0`, and `1.0`;
- source mixing: gathering ignores source declaration kind and performs no truth check;
- scan behavior: the same `evalAssignDtypedSeeded` is called by plain and scan reference paths;
- serialization: no checked-plan codec exists, and the routed Acset branch is separate;
- oracle gap: generated leaf names are visibly absent from the preserved declaration list.

These are known engineering changes, not experiments.

The ownership spike also found the pre-existing einsum exact-axis recomputation weakness. Task 4.5
now closes it before threading Variant B context, using a non-symmetric two-dimensional fixture and
an explicit regression mutation. Its failure mode and direct repair are known, so it warrants
implementation and mutation testing rather than another spike.

Two additional values remain unknown because they exist only after implementation, but neither
justifies a spike:

| Unknown | Why static inspection cannot settle it | Decision blocked | Bounded experiment | Expected artifact/result | Must precede implementation? |
|---|---|---|---|---|---|
| Exact new corpus/build counts | Counts depend on final fixture additions and Lake's compiled target graph | Final documentation numbers only | Run targeted corpus commands and full `lake build`, capture printed counts/jobs, then value-grep old values | Completion-record command log and updated current-state docs | No; run before Task 4.5 documentation is finalized |
| New fixture values for coupled Bool/real scans | Several iterations and Float `min`/`max` folds make hand transcription unsafe | Expected-value assertions only | Run the unmodified reference evaluator on each final source donor, then run checked and independent legs | Recorded reference tensors followed by three-way equality | No; run while implementing Tasks 4.3–4.4 before assertions are committed |

If either measurement contradicts the semantic contract—rather than merely changing a count—stop.
Do not redesign storage, coerce values, weaken checker evidence, or broaden JAX execution inside this
slice.

## 9. Authoring verification record

- All paths named in task file lists and every fixture donor were re-verified present on commit
  `429673f`.
- The `ae00fcc..429673f` production drift was inspected. Commit `c8ed102` added indexed read-factor
  helpers and Iverson rejection wiring but did not change the declaration, Boolean allocation,
  scan-write, or geometry surfaces this plan relies on.
- The current boundary was re-derived from `CapabilityError` and every throw site in
  `Eval/Plan/Compile.lean`; no inventory count was inherited.
- Current corpus values were read from active source guards: 3,832 scan-free cases, 6 separate
  predicate/mask entries, and 17 scan cases. The worktree then rsynced a complete Mathlib cache from
  the primary checkout (8,101 built oleans for 8,094 sources), refreshed `LeanNCD`, and completed a
  warm full `lake build`: 8,659 jobs, 3,832/3,832 scan-free cases accepted, and 17/17 scan cases
  accepted with zero unsupported nonlinearity or aggregation cases.
- Relevant history inspected: the original reserved plan dtype/algebra commits, reference predicate
  contraction, shared scan dtype dispatch, max/min admission, nonlinearity admission, and Slice 5
  predicate/mask commits. The Mathlib `Bool` XOR-ring history is not reused: this plan executes
  explicit Float `min`/`max`, not `HAdd Bool`.
- Inherited gaps were rechecked. Predicate factors and axiswise masks are admitted; declared
  predicate outputs are the only Boolean row still rejected by preflight. The independent scan
  unroller and JAX support siblings above are current, newly re-derived couplings.
- Independent high-reasoning reviews caught and the assembled plan corrected unreachable scan dtype
  fixtures, exhaustive error-renderer omissions, stale external-name authority, incomplete
  documentation surfaces, and the JAX signature/evidence unknown, which the linked mandatory spike
  subsequently resolved as GO B.
- This document contains no Lean code block, so `check-snippet.sh` is not applicable.
- At original plan authoring, no implementation code was changed; this spike branch likewise retains
  documentation only after reverting every temporary Lean prototype.
