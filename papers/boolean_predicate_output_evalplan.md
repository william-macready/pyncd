# Task 4 — Boolean / predicate outputs in the checked `EvalPlan` backend

**Status:** Complete. Tasks 4.1–4.6 were implemented, mutation-tested, independently reviewed, and
merged into local `main` by merge commit `eb37836` on 2026-09-06. Task 4.6's two shared validation
boundaries landed in `0160f59` and `06604f2`; subsequent whole-branch findings and final test-oracle
repairs were closed through `1950da1`. See §10 for the implementation and validation record. The
prospective task text below is retained as the reviewed execution specification.

The completed work closes the checked-backend rejection of `Decl.predicate` by
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

### Task 4.6 — Consolidate scheduled-program and prepared-binding validation boundaries

#### Why this closure task exists

Tasks 4.1–4.5 established the intended Boolean semantics, but the final whole-branch reviews found
one recurring architectural defect rather than another Boolean-algebra defect: public,
hand-constructible values can reach several consumers, and those consumers independently
re-establish only the subset of invariants they happen to need. The result is a moving bypass
surface:

- `prepareEvalPlan` and `evalScheduled` do not currently share one whole-schedule check;
- declared source read ranks are checked, but declared destination ranks are not;
- `evalScheduled` does not reject a direct schedule whose producer appears after its consumer;
- `pack`, `unpack`, metadata queries, named JAX emission, and executable construction do not share
  one exact `PreparedPlan.bindings` check;
- current materialization validation accepts a strictly increasing subsequence even when it omits a
  real publication, and positional raw IR alone cannot recover the publication names to compensate.

Do not add another caller-specific guard. This task introduces exactly two shared validation
boundaries and routes every public consumer through them. Keep the two work packages as separate,
independently reviewable commits: either validator can be rejected without rolling back the other.

#### Verified files

**Scheduled-program boundary**

- `leanncd/LeanNCD/DSL/Pipeline/Structural.lean`
- `leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean` (new neutral module)
- `leanncd/LeanNCD/DSL/Pipeline/Lowering.lean`
- `leanncd/LeanNCD/Eval/Eval.lean`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/test/DSL/Pipeline/StructuralTest.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean`

**Prepared-binding boundary**

- `leanncd/LeanNCD/Eval/Plan/Error.lean`
- `leanncd/LeanNCD/Eval/Plan/Prepared.lean`
- `leanncd/LeanNCD/Eval/Plan/Adapter.lean`
- `leanncd/LeanNCD/Eval/Plan/Executable.lean`
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`
- `leanncd/experiments/jax_bridge/EvalPlanSmoke.lean`
- `leanncd/experiments/jax_bridge/EvalPlanAffineSmoke.lean`
- `leanncd/experiments/jax_bridge/EvalPlanAffineCorpus.lean`
- `leanncd/test/Eval/Plan/AdapterTest.lean`
- `leanncd/test/Eval/Plan/ExecutableTest.lean`
- `leanncd/test/Eval/Plan/NonlinCompileTest.lean`
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`

**Documentation and validation surfaces**

- `leanncd/LeanNCD/Eval/AGENTS.md`
- `leanncd/LeanNCD/DSL/AGENTS.md`
- `leanncd/experiments/jax_bridge/README.md`
- `leanncd/test/Eval/Plan/DifferentialTest.lean`

All paths above except the explicitly new `ScheduledValidation.lean` exist at `ce1a0f7`. Do not
broaden the task into private constructors for `PlanBindings` or `PreparedPlan`: their public
construction remains useful for authority-attack fixtures, and public validation remains necessary
at deserialization or foreign-function boundaries even if constructors are restricted later.

#### Landed-validation preservation and migration

Task 4.6 starts from `ce1a0f7`; it does not reopen the behavior established by the preceding
review-fix commits. Treat the current validators and their fixtures as the migration baseline:

| Invariant already enforced at `ce1a0f7` | Current authority | Task 4.6 treatment |
|---|---|---|
| Duplicate-safe declarations | `Structural.buildDeclEnv`, called independently by preparation and direct evaluation | Reuse unchanged inside the shared scheduled validator; remove only duplicate call sequences |
| Declared and external source-read ranks | `Structural.checkScheduledReadRanks`, called independently by both direct boundaries | Preserve checks, payloads, and traversal order; extend the same structural boundary with declared destination ranks |
| Predicate-output identity/sum rules | `Structural.checkPredicateOutputs`, called independently by both direct boundaries | Reuse unchanged inside the shared scheduled validator |
| Declaration-derived explicit sizes | `Structural.declaredAxisSizes`, independently recomputed by both direct boundaries | Compute once in the shared result and consume that value; never restore trust in the schedule cache |
| Ordered external names | `Lowering.orderedExternalNames`, re-derived by `prepareEvalPlan` | Preserve the current first-read order and expose it through the shared result; direct evaluation need not allocate positional slots but must validate the same schedule |
| Producer-before-consumer order | `Lowering.isTopoOrdered`, re-established by `prepareEvalPlan` only | Move the neutral predicate into `ScheduledValidation.lean`, preserve its verdict, intentionally migrate preparation's boundary-specific message to one shared payload, and add the missing direct-evaluation consumer |
| Materialized slot bounds and store-size checks | `PlanBindings.materializedWith`, `PreparedPlan.materializedSignatures`, and `Adapter.unpack` | Retain the shared bounds helper and adapter store-size diagnostics after the new exact binding check; do not replace their typed payloads with a generic failure |
| Required-input tie and increasing materialized slots | `Executable.checkPreparedBindings` | Move the general check to `Prepared.lean`; preserve its required-input cause, then strengthen materialization from increasing slots to exact publication equality |
| JAX semantic/context/evidence gates | `Executable.lean` and `EvalPlanCodegen.lean` | Leave semantic validation in place; run the general prepared-binding check before it rather than folding JAX support into the shared validator |

The implementation review must compare behavior before and after each move. A landed validator may
disappear from its old caller only in the same commit that wires that caller to the shared result.
Do not temporarily weaken a public boundary, rewrite an existing semantic check, or delete its
fixture because a stronger aggregate fixture exists. Task 4.6 adds only three new invariant
classes: declared destination rank, topology at direct evaluation, and exact prepared publication
slots. Everything else is relocation, reuse, or public-consumer coverage. Two malformed-value
diagnostic migrations are intentional and must be fixture-pinned: direct preparation's
boundary-specific topology string becomes the shared neutral topology string, and malformed
prepared bindings precede consumer-specific environment/store/JAX errors. Existing payloads remain
unchanged whenever the new earlier check succeeds.

#### Work package A — one scheduled-program invariant result

1. Extend the shared `Stmt`-level structural rank routine used by both `checkReadRanks` and
   `checkScheduledReadRanks`; do not add a scheduled-only destination pass. Preserve its existing
   three read-validation passes and their diagnostic order, then traverse destinations in source
   order. For a declared `.assign` or `.scatter`, require the raw syntactic LHS `slots.length` to
   equal `Decl.axisCount` and report `CompileError.rankMismatch lhsName expected actual`.
   Deliberately do not use `stmtLhsRank`: its deduplicated/scatter-sensitive value describes the
   published rank of an undeclared intermediate, not whether a declared LHS contains the declared
   number of syntactic positions. Exclude `.recurMorphism`; skip undeclared scratch destinations.
   For scheduled scans, flatten `.plain`, then each `.scan`'s `base ++ recur`, and ignore
   `.scanPre` exactly as the current shared traversals do.
2. Create neutral `DSL/Pipeline/ScheduledValidation.lean`; do not make `Eval.lean` import all of
   `Lowering.lean` and thereby acquire routing/target dependencies just to validate a schedule.
   Move `ScanStmt.writes`, `ScanStmt.reads`, private `eligible`, `topoSortFuel`, `topoSort`,
   `isTopoOrdered`, and `orderedExternalNames` together into this module: the sorter and validators
   depend on the shared accessors/eligibility predicate, so moving only the public validation
   functions would either fail to compile or duplicate their authority. Export `topoSort` for
   `schedule`; keep implementation helpers private. Have `Lowering.lean`, `Eval.lean`, and
   `Eval/Plan/Compile.lean` import the neutral module; remove `Compile.lean`'s broader
   `Lowering.lean` import if no separately used symbol remains after the move.
3. Define an unforgeable checked context `CheckedScheduledProgram` with a private constructor and
   public projections for the original `ScheduledProgram`, duplicate-safe `DeclEnv`,
   declaration-derived explicit sizes, and authoritative ordered external names. Define
   `validateScheduled : ScheduledProgram → Except CompileError CheckedScheduledProgram`. It runs,
   in order: `buildDeclEnv`; all scheduled read passes followed by declared destination ranks;
   `checkPredicateOutputs`; `isTopoOrdered`. Its topology failure is exactly
   `CompileError.cyclicDataflow "scheduled program: statements are not in producer-before-consumer order"`.
4. `prepareEvalPlan` must consume that checked context for declarations, explicit sizes, external
   input allocation, and statements. Map validator failure to
   `PlanCompileCause.sourceInvariant` with `warnings := []`. `evalScheduled` must consume the same
   context for declarations, explicit sizes, and statements, mapping failure to `EvalError.compile`
   with `warnings := []`. Neither caller may trust `ScheduledProgram.env`,
   `ScheduledProgram.explicitSizes`, or `ScheduledProgram.extNames`.
5. The neutral topology string intentionally replaces preparation's current
   `"prepareEvalPlan: statements are not in producer-before-consumer order"` payload so the two
   direct boundaries report the identical `CompileError`. Update that exact fixture; all other
   landed diagnostic constructors, payloads, and precedence remain unchanged.
6. Audit and classify every public `ScheduledProgram` consumer. `prepareEvalPlan` and
   `evalScheduled` are the two execution/preparation boundaries that must require
   `CheckedScheduledProgram`. `capabilityPreflight`, `orderedExtNames`,
   `elaborateAffineReindexings`, `routeCore`, `routeNameInventory`, `physicalizeRaw`,
   `physicalizeForRoute`, and `route` are phase-local or routing APIs: do not silently force the
   EvalPlan validator into them. Record for each whether it operates before scheduling invariants
   exist, consumes a schedule already produced by `schedule`, or enforces a distinct route-specific
   contract. The completion record must contain this inventory rather than claiming that every
   function accepting the structure is an execution boundary. Also classify
   `PropertyOracle.independentRun`: it remains an independent test oracle with a valid-source
   precondition and reaches the shared validator only through its scan-free `evalScheduled` calls;
   do not couple its independent unrolling logic to checked-plan preparation.

**Scheduled-program fixture matrix — 10 fixture groups**

| Fixture | Donor and distinguishing change | Required observation |
|---|---|---|
| Plain destination under-rank | Clone the valid one-dimensional direct rank fixture in `CompileTest`; declare the destination with two axes while retaining a one-index LHS and a valid RHS | Source checking, preparation, and direct evaluation report the same destination `rankMismatch`; no later shape error substitutes |
| Plain destination over-rank | Clone the same fixture; declare one destination axis and write two LHS indices | The three boundaries reject with the inverse expected/actual rank payload |
| Read-before-write precedence | Clone the under-rank fixture and also remove one RHS read index | The pre-existing source read `rankMismatch` wins at every boundary, pinning read passes before the new destination pass |
| Scan-base destination rank | Clone `rankScanBase`/`rankScanSched`; change only the base destination's index count | Source checking, preparation, and direct evaluation reject the base statement |
| Scan-recurrence destination rank | Clone `rankScanRecur`/`rankScanSched`; change only the recurrence destination's index count | The same three boundaries reject the recurrence statement |
| Scan traversal order | Clone `rankScanSched`; make both base and recurrence destination ranks invalid in distinguishable ways | The base diagnostic wins, pinning `base ++ recur` rather than recurrence-first or a filtered traversal |
| Direct consumer-before-producer | Reuse `outOfOrderSched`, but provide a same-shaped caller value for the future-produced name so accidental external treatment would otherwise execute | Both `prepareEvalPlan` and `evalScheduled` reject producer order; the supplied environment cannot turn the future producer into an input |
| Producer-first valid sibling | Clone `outOfOrderSched` and swap only the two statements | Both direct boundaries accept and direct evaluation agrees with the prepared Dense run |
| Topology-before-consumer failures | Clone `outOfOrderSched` twice: omit its required `InputSignature` entry for preparation, and give direct evaluation an input that would produce a later shape/runtime failure | The shared topology error wins at both boundaries, proving validation occurs before consumer-specific work rather than merely eventually rejecting |
| Shared invariant parity | Reuse the existing duplicate-declaration, direct read-rank, predicate-output, stale-size, and stale-external-name fixtures in `StructuralTest`/`CompileTest` | Each failure or success remains identical through source compilation where applicable, preparation, and direct evaluation; this row prevents consolidation from dropping an older check |

Observe the valid sibling's actual tensors through both evaluators before fixing the expected value.
The order fixtures are invalid if their two candidate traversals produce the same diagnostic; keep
their ranks and names distinct enough to prove which pass or statement won.

**Scheduled-program mutation cycles — 4**

1. Disable only declared-destination rank validation; the five destination-only fixture groups fail,
   while the combined read/write-invalid fixture still fails through the older read check.
2. Disable only the shared producer-order check; the out-of-order fixture fails while its valid
   sibling stays green.
3. Bypass the shared result at `prepareEvalPlan`; at least the direct out-of-order and stale-cache
   preparation fixtures fail.
4. Bypass the shared result at `evalScheduled`; the matching direct-evaluation fixtures fail.

Run each cycle with `mutation-cycle.sh` against
`Eval.Plan.CompileTest` and `DSL.Pipeline.StructuralTest`; include the narrow direct-evaluator target
if it remains separate after implementation.

**Commit**

`refactor(eval-plan): share scheduled invariant validation`

#### Work package B — one exact prepared-binding validator

1. Move the neutral `PreparedBindingsError` data type from `Executable.lean` to `Error.lean`, which
   is already upstream of `Prepared.lean` and the adapter error types. Keep
   `.requiredInputs (cause : BindingsError)` and `.materializedSlot (cause : PlanError)`, and replace
   `.materializedNotPublished` with
   `.publicationSlots (expected actual : Array TensorSlot)`. Move the validator itself and the raw
   publication derivation to `Prepared.lean`; executable construction remains a consumer.
2. Define an unforgeable `CheckedPreparedBindings` view with a private constructor and projections
   for the checked required bindings and materialized bindings. Define
   `checkPreparedBindings : PreparedPlan → Except PreparedBindingsError CheckedPreparedBindings`.
   Public entry points validate once, then pass this checked view to private/internal workers rather
   than rerunning the check along one call path. The validator uses a private raw slot-resolution
   helper; it must not call public `materializedSignatures`, which itself calls the validator.
   Replace public `PlanBindings.materializedWith` with a checked-view resolver or make the raw helper
   private so callers cannot retain an unchecked lower-level bypass.
3. Add one pure raw-plan publication-slot derivation in `Prepared.lean`. Traverse `raw.steps` by
   index:
   - for `.assign a`, append `a.destinationSlot` unless the immediately following step is
     `.pointwise p` or `.axiswise p` with `p.sourceSlot == a.destinationSlot`;
   - for `.pointwise p` or `.axiswise p`, append `p.destinationSlot`;
   - for `.scan s`, append `s.states.map (·.destSlot)` in stored state order.
   `AssignPlan` has no identity/nonlinearity tag, so do not describe or implement the raw rule as
   “identity assignment.” The adjacent consuming step is the only derivable distinction. A
   hand-built checked raw plan with the same adjacent shape receives the same interpretation because
   raw IR carries no compiler-provenance bit. Preserve array order without sorting or deduplication.
   Compiler-produced repeated output names have distinct publication slots; do not claim that a
   checked plan permits repeated destination slots.
4. The shared validator runs in this exact order:
   - rerun `checkBindings raw.inputSlots requiredInputs.bindings`, preserving its name-unique
     **slot-multiset permutation** semantics; binding-array reorder remains legal;
   - resolve every materialized slot against `raw.tensorSigs`, preserving
     `.materializedSlot (.slotOutOfRange slot tableSize)`;
   - compare `materializedNames.map (·.slot)` with the raw-derived publication array by full array
     equality and report `.publicationSlots expected actual`.
   This proves attachment to raw input slots and exact output slots, length, order, and repetition.
   It does not impose positional equality on required bindings.
5. Specify the public error migrations:
   - `PreparedPlan.materializedSignatures` returns
     `Except PreparedBindingsError (Array (String × TensorSignature))`;
   - `InputBindingError` gains `.invalidPreparedBindings (cause : PreparedBindingsError)`, used by
     `pack` before consulting the environment;
   - `PlanRunCause` gains `.invalidBindings (cause : PreparedBindingsError)`, used by direct
     `unpack` before result-store arity; `runPreparedDense` maps `pack` failure through its existing
     `.binding` wrapper and relies on the checked adapter workers rather than validating twice;
   - `JaxCodegenError` gains `.invalidBindings (cause : PreparedBindingsError)`;
   - `JaxExecutableValidationError.invalidBindings` retains the same cause type after its move.
6. Route every public `PreparedPlan` consumer through the validator before consumer-specific work:
   `PreparedPlan.materializedSignatures`, `Adapter.pack`, direct `Adapter.unpack`,
   `generateForward`, `renderAffinePlanNamed`, `generateNamed`,
   `lowerCheckPlanToCandidate`, and executable validation. `runPreparedDense` delegates through
   checked adapter workers; do not add a third redundant check. Prescribe the adapter flow:
   public `pack` validates then calls private `packChecked`; public `unpack` validates then calls
   private `unpackChecked`; `runPreparedDense` obtains the checked view on its pack-side path,
   maps validator failure through `.binding (.invalidPreparedBindings cause)`, and passes the same
   view to `unpackChecked`. Public `materializedSignatures` validates and then uses the same private
   raw resolver as the validator without recursion.
7. Replace public raw/bare-binding render helpers with a checked boundary:
   `renderShapeCheckLine`, `renderSlotInitLines`, `renderOutputLines`, and `renderBindingList` become
   private/internal helpers over a checked view. Replace the public
   `renderInputConstants raw requiredInputs inputs` surface with a plan-level wrapper that accepts a
   `PreparedPlan`, validates it, then calls a private raw renderer. Update `EvalPlanSmoke` to use that
   wrapper. Make `EvalPlanAffineSmoke.renderInputsDict` and `renderExpectedDict` private unless an
   actual external caller is found; the private `EvalPlanAffineCorpus` helpers remain behind their
   validated caller. Classify `EvalPlanAffineCorpus.featureMask` as binding-independent checked-plan
   metadata and either make it private or narrow its argument to `CheckedEvalPlan`; it must not
   remain a public `PreparedPlan` consumer that appears to have passed binding validation.
8. Malformed prepared bindings precede caller environment lookup, direct-unpack result-store arity,
   JAX semantic lowering, kernel/evidence construction, and executable aggregation validation.
   These precedence changes for malformed hand-built plans are intentional. When bindings are
   valid, preserve the existing store-arity, environment shape/storage, JAX support, aggregation,
   and warning payloads. Pin every precedence claim with a fixture violating both conditions.
9. State the deliberate limit precisely in code documentation and the completion record:
   positional `RawEvalPlan` can derive required and publication **slots**, but cannot recover source
   or publication **names**. This task therefore proves structural slot identity and
   required-binding name uniqueness; it neither invents a caller-supplied name table nor claims that
   an arbitrary materialized name is source-authentic. Names produced by `prepareEvalPlan` remain
   authoritative.
10. Migrate `EvalPlanCodegen.rejectsLocatedAt1` rather than changing its expected error. Its
    hand-built prepared plans currently use an empty publication list and will be intercepted by
    exact binding validation. Give the pointwise, axiswise, and masked-axiswise cases publication
    slot `#[2]`, and the scan case slots `#[3, 2]`, matching their raw step order. Preserve every
    existing `.unsupportedStep 1` assertion so the new binding gate does not erase the landed JAX
    locator coverage.

**Prepared-binding fixture matrix — 10 fixture groups**

| Fixture | Donor and distinguishing change | Required observation |
|---|---|---|
| Extra/missing/wrong required input | Reuse `ExecutableTest.bindingsWith`; construct each `RequiredBindings` legally with `checkBindings` against a different input-slot array, then pair it with the target plan | Every prepared-plan boundary rejects with `.requiredInputs`; the fixture must not attempt to bypass the private `RequiredBindings` constructor |
| Reordered required inputs | Reuse `AdapterTest`'s asymmetric name-based permutation fixture | Reordering the binding array remains valid and produces the observed contraction result; exact means slot-multiset permutation, not positional equality |
| Input published as output | Clone `zeroCoeffProg`'s prepared plan; replace its `Y` publication slot with input slot zero | Metadata, `unpack`, full adapter execution, named JAX emission, and executable validation all report expected versus actual publication slots |
| Missing publication | Clone `mixedVerdict`'s valid prepared plan; omit one real publication while leaving the remaining slots increasing | Rejected everywhere; this is the distinguishing fixture against the old increasing-subsequence rule |
| Extra in-range publication | Reuse `NonlinCompileTest.pointwiseIsolatedPrepared`; insert the internal assign destination before the real nonlinear publication | Rejected by exact equality although both slots are in range and increasing; an out-of-range append is only a bounds fixture |
| Reordered and duplicated publication | Reuse the corresponding `mixedVerdict` attacks in `ExecutableTest` | Both reject by exact sequence equality, not by separate ad hoc order predicates |
| Unauthenticated names | Clone `mixedVerdict`'s valid slot sequence and change only materialized names | Deliberately accepted by structural validation; raw IR cannot authenticate names, and the test prevents the implementation from claiming otherwise |
| Identity valid sibling | Use `zeroCoeffProg` unchanged | Every consumer accepts; metadata and runtime still publish `Y` |
| Nonlinear publication sequence | Reuse `pointwiseIsolatedPrepared` and `axiswiseIsolatedPrepared` in `NonlinCompileTest`; strengthen them to assert publication slots `#[2]` and exclusion of internal slot `1`, not merely names and step kinds | Both raw assign-plus-nonlinearity pairs pass exact validation |
| Scan and repeated-name sequence | Reuse `ScanCompileTest`'s two-state persistent-order fixture, its scratch-exclusion sibling, and `CompileTest.repeatPredPrepared` | Scan states publish in stored state order, scratch is absent, and repeated output names with distinct slots remain legal; unpack's later name insertion still wins |

For precedence, extend the extra-required-input fixture with a missing environment binding, the
input-as-output fixture with a wrong-sized result store, one unsupported-Boolean named JAX fixture
with invalid bindings, and an executable candidate with both invalid aggregation and invalid
bindings. Each must report the boundary's typed invalid-binding wrapper. Retain the existing
out-of-range materialized fixture to prove `.materializedSlot (.slotOutOfRange ...)` precedes exact
sequence comparison. Add a malformed-binding failure over `AdapterTest.warnProg` so warning
preservation is observed with a nonempty warning list. The valid compiler-produced repeated-name
sibling prevents an implementation from satisfying the attacks by rejecting duplicate names.

**Prepared-binding mutation cycles — 10**

1. Weaken exact required-input equality to subset or in-range membership.
2. Replace exact publication equality with the old strictly-increasing-after-inputs approximation.
3. Bypass the shared validator in `PreparedPlan.materializedSignatures`.
4. Bypass it in `Adapter.pack`.
5. Bypass it in direct `Adapter.unpack`.
6. Bypass it in `generateForward`; exercise `generateNamed .einsumOnly` through the same public
   route.
7. Bypass it in `renderAffinePlanNamed`; exercise `generateNamed .affineReference` through the same
   public route.
8. Bypass it in direct `lowerCheckPlanToCandidate`.
9. Bypass the validating plan-level input-constant renderer used by `EvalPlanSmoke`.
10. Bypass it in executable validation.

Run adapter/executable mutations against `Eval.Plan.AdapterTest`,
`Eval.Plan.ExecutableTest`, `Eval.Plan.CompileTest`, `Eval.Plan.NonlinCompileTest`, and
`Eval.Plan.ScanCompileTest`; run named-codegen mutations against
`experiments.jax_bridge.EvalPlanCodegen` and the smoke driver target. Do not add redundant
`runPreparedDense` or `generateNamed` mutations when those wrappers demonstrably delegate to the
already-mutated public boundary. A mutation counts only when the named fixture fails under the
mutation and passes after restoration. Record before/after hashes with the mutation runner.

**Commit**

`refactor(eval-plan): validate prepared bindings once`

#### Completion gate

- Execute the two work packages through separate implementation-agent contexts. After each package,
  run its targeted tests and mutations, commit it, and give that complete commit to a fresh
  read-only reviewer before starting the next package. Do not split either package into tiny
  type-only and caller-only dispatches: their correctness is the end-to-end validator migration.
- The two commits receive separate per-work-package reviews.
- One final invariant matrix lists every public scheduled-program consumer and every public
  prepared-binding consumer, the shared validator it calls, and the fixture proving the edge.
- Run the scan-free and scan differential corpora after both work packages; the validators may
  reject malformed authority attacks but must not alter accepted-program values.
- Run the full `lake build`.
- Run two independent whole-branch reviews with different lenses:
  1. source/direct-evaluator parity, diagnostic precedence, and import layering;
  2. prepared-binding authority, publication derivation, adapter/JAX bypasses, and mutation strength.
- Integrate locally only when both reviews are clean or every finding is explicitly adjudicated.

## 4. Risk sizing

| Task | Main risk | Fixtures | Mutation cycles | Reviewer rejection boundary |
|---|---|---:|---:|---|
| 4.1 | declaration ambiguity, external-name authority, diagnostic precedence | 11 | 6 | Source semantics can be rejected while all plan execution work stands |
| 4.2 | wrong Boolean identities/algebra or accidental type tightening | 12 | 7 | Local checker/Dense semantics can be rejected independently |
| 4.3 | signature authority, top-level allocation, result metadata | 12 | 7 | Public top-level boundary can fail while raw execution is correct |
| 4.4 | one missed scan `f64`, unsound write dtype, oracle self-mismatch | 8 | 11 | Scan semantics and write evidence are a separate soundness surface |
| 4.5 | exact einsum axes, JAX context authority, unsupported semantics stamped as reference, stale boundary docs | 11 | 11 | Experimental backend evidence/docs can be rejected without rolling back Dense |
| 4.6 | duplicated schedule/binding authority and consumer bypasses | 20 fixture groups | 14 | Either shared validator can be rejected without rolling back the other |
| **Total** |  | **54 pre-4.6 fixtures plus 20 reused/extended/new 4.6 groups** | **56** |  |

The fixture count, not expected production-line count, makes Tasks 4.2–4.6 high-review work. Do not
split tiny type additions from the checker/compiler that produces them; they have no independent
failure mode. Do not merge Task 4.4 into Task 4.3: a reviewer can approve top-level Bool while
rejecting scan write evidence or oracle independence. Task 4.6 remains one closure task, but its two
validator work packages are separate commits and review units because either can be rejected while
the other stands.

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
- original all-factor index for Iverson remains pinned by Task 4.5 fixture 5;
- source read ranks before declared destination ranks: Task 4.6's combined read/write-rank fixture;
- scan base before recurrence destination ranks: Task 4.6's dual-invalid scan fixture;
- shared scheduled-program checks before preparation/evaluation: Task 4.6's out-of-order direct
  fixture with a same-shaped caller value;
- prepared-binding validity before caller environment, result-store, or JAX support failures:
  Task 4.6's three dual-invalid binding fixtures;
- exact publication sequence rather than increasing-subsequence admission: Task 4.6's missing
  middle publication fixture.

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
   `LeanNCD.DSL.Pipeline.Structural`, `LeanNCD.DSL.Pipeline.ScheduledValidation`,
   `LeanNCD.DSL.Pipeline.Lowering`,
   `LeanNCD.Eval.Eval`, `LeanNCD.Eval.Contract`,
   `LeanNCD.Eval.Plan.Check`, `LeanNCD.Eval.Plan.Dense`,
   `LeanNCD.Eval.Plan.Signature`, `LeanNCD.Eval.Plan.Prepared`,
   `LeanNCD.Eval.Plan.Adapter`, `LeanNCD.Eval.Plan.Compile`, `LeanNCD.Eval.Plan.Scan`,
   `LeanNCD.Eval.Plan.Executable`.
2. Run the affected default test modules:
   `DSL.Pipeline.StructuralTest`, `Eval.ContractTest`,
   `Eval.Plan.KernelCheckTest`, `Eval.Plan.KernelDenseTest`,
   `Eval.Plan.NonlinCheckTest`, `Eval.Plan.NonlinDenseTest`,
   `Eval.Plan.NonlinCompileTest`,
   `Eval.Plan.SignatureTest`, `Eval.Plan.CompileTest`,
   `Eval.Plan.AdapterTest`, `Eval.Plan.ScanCompileTest`,
   `Eval.Plan.ScanTest`, `Eval.PropertyOracle.ScanUnroll`,
   `Eval.PropertyOracle.ScanOracle`, `Eval.Plan.DifferentialTest`,
   and `Eval.Plan.ExecutableTest`.
3. Build non-default `JaxExperiment`, then directly elaborate
   `experiments/jax_bridge/EvalPlanCodegen.lean`,
   `experiments/jax_bridge/EvalPlanSmoke.lean`, and
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
   oracle separation, shared scheduled-program validation, destination-rank/read-rank precedence,
   producer order at both direct boundaries, and Acset/Bridge non-claims.
2. **Soundness and fail-loud lens:** checker private-constructor evidence, all scan signature
   allocation/capture/write sites, write dtype order and locators, unchanged geometry/causality
   siblings, direct-schedule source invariants, exact einsum operand/output recomputation, JAX
   support table, original factor/step indices, exact prepared publication derivation,
   adapter/metadata/named-JAX/executable consumer coverage, and mutation-test integrity.

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

## 10. Implementation and validation record

### 10.1 Landed architecture

- Tasks 4.1–4.5 implement Boolean Dense algebra, predicate output signatures and allocation, Boolean
  scan state/scratch/history behavior, exact JAX axis recomputation, and Variant B's explicit
  signature-table policy.
- Task 4.6 Work Package A landed in `0160f59`. The neutral
  `DSL/Pipeline/ScheduledValidation.lean` boundary now re-derives declaration, explicit-size,
  external-name, rank, dtype/LHS-axis-kind, predicate-output, and producer/publication-order
  invariants for both checked preparation and direct scheduled evaluation.
- Task 4.6 Work Package B landed in `06604f2`. `CheckedPreparedBindings` now authenticates the exact
  required-input permutation and exact publication slots before metadata, adapter, named-JAX,
  candidate, or executable consumers proceed.
- Whole-branch review fixes distinguish scan-local writes from external publications (`e15dce1`),
  preserve predicate-leaf retained axes and three-way parity (`a62af0b`, `6d3a02b`), tie executable
  evidence to prepared bindings (`9046107`), and validate scheduled LHS axis kinds (`75a57b3`).
- Final boundary fixes validate JAX fixture tensor shape and storage before rendering (`f2929ba`) and
  make the independent scan-mask and retained-predicate oracles non-vacuous (`1950da1`).
- The completed branch was merged locally into `main` as `eb37836`. It was not pushed as part of this
  work.

### 10.2 Final verification

The final implementation passed:

- all planned Task 4.6 mutation cycles, plus the review-driven mutations for publication order,
  retained predicate axes, executable/binding evidence, scheduled LHS axis kinds, JAX fixture
  shape/storage, free-base-axis mask substitution, retained predicate declarations, and warning
  preservation;
- targeted Task 4/4.6 production and test builds;
- the scan-free differential corpus: **3,832/3,832 accepted**;
- the scan corpus and independent unroll: **17/17 accepted**;
- the JAX EvalPlan smoke;
- the curated JAX affine suite: **20/20 fixtures**;
- the JAX affine corpus: **3,832 cases, 0 eager mismatches, 65 JIT checks**;
- the final full `lake build`: **8,660 jobs**;
- `git diff --check` and a clean worktree.

Both Task 4.6 work packages received independent commit reviews. Whole-branch semantic and
soundness reviews were completed with every actionable finding fixed or explicitly adjudicated. The
last consolidated test-harness repair received one isolated-diff review and was clean; no further
open-ended whole-branch review cycle was required.
