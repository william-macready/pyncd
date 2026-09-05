# Predicate and Boolean parity for the checked `EvalPlan` backend

**Status (2026-09-03): BOTH items are now implemented and landed.** Item 5 (masks, predicates,
Iverson factors) landed from this document's own Slice 5 tasks. Item 4 (Boolean/predicate tensors)
landed from the SEPARATE executable slice plan
[`boolean_predicate_output_evalplan.md`](boolean_predicate_output_evalplan.md), which **supersedes
§5 and §7 of this document**: that plan's preflight against the tree found three additional
requirements this design did not anticipate (direct `ScheduledProgram` inputs must defensively
re-establish predicate source invariants and external-name classification; the independent scan
unroller must copy predicate declarations onto generated leaf tensors; JAX's standalone candidate
APIs need explicit signature context before they can distinguish Boolean sources), plus the
existing JAX support-gate siblings — tropical algebras and unary reads — that must be rejected
alongside Boolean semantics rather than silently receiving `orderedReference64` evidence. Read §5/§7
below as the original design intent, not as the shipped boundary.

This document covers items 5 and 4 of
[`backend_missing_functionality.md`](backend_missing_functionality.md), in that implementation
order:

1. masks, predicates, and Iverson factors;
2. Boolean/predicate tensors.

This is an architecture and task-division document, not one executable SDD slice plan. Execution
should use two sequential slice plans, one for each item, so each slice can be implemented, built,
reviewed as a whole, and landed before the next plan is finalized.

The disposable
[`predicate-coordinate-parity spike plan`](../docs/superpowers/plans/2026-08-31-predicate-coordinate-parity-spike.md)
tested the coordinate policies behind item 5 before production migration. Its
[`measured results`](predicate_coordinate_parity_spike_results.md) confirm the common positional
predicate representation and the distinct Iverson/mask lowering policies, and motivate the
eliminated-`.freeNorm` fixture plus the explicit `ScanUnroll` fragment boundary in Tasks 5.3-5.4.

No corpus total, build-job count, JAX artifact measurement, or fixture value is predicted here.
Every such value must be measured when the corresponding slice plan is authored and again after
implementation.

## Contents

- [1. Decision summary](#1-decision-summary)
- [2. Three different meanings of "predicate"](#2-three-different-meanings-of-predicate)
- [3. Existing machinery to reuse](#3-existing-machinery-to-reuse)
- [4. Item 5 design: positional predicates](#4-item-5-design-positional-predicates)
- [5. Item 4 design: Boolean tensors](#5-item-4-design-boolean-tensors)
- [6. Slice 5 tasks](#6-slice-5-tasks)
- [7. Slice 4 tasks](#7-slice-4-tasks)
- [8. Dependency and parallelism plan](#8-dependency-and-parallelism-plan)
- [9. Required sibling audits](#9-required-sibling-audits)
- [10. Mutation matrix](#10-mutation-matrix)
- [11. Documentation and capability-count sweep](#11-documentation-and-capability-count-sweep)
- [12. Verification and completion gates](#12-verification-and-completion-gates)
- [13. Explicit non-goals](#13-explicit-non-goals)
- [14. Stop conditions](#14-stop-conditions)

## 1. Decision summary

| Question | Decision |
|---|---|
| What already lowers today? | Surface `[condition]` already elaborates to `Factor.iverson BoolExpr`; `where=` already lives on `Nonlin.axiswise`. Item 5 adds the later lowering from UID-bearing source expressions to UID-free checked-plan data. |
| Slice order | Land item 5 completely, then item 4. Item 5 changes the factor representation that item 4's checker must consume. |
| Source predicate AST | Keep `PredArith`, `BoolExpr`, `Factor.iverson`, and axiswise `Option BoolExpr` unchanged. |
| Positional predicate IR | Add only positional arithmetic, positional Boolean, and an ordered factor sum. Reuse `RelOp`; do not retain `AxisSpec`, UID, kind, or name in checked plans. |
| Factor representation | Change `TermPlan.factors` from `Array ReadPlan` to ordered `Array FactorPlan`, with `read` and `iverson` cases. Never split reads and predicates into parallel arrays. |
| Predicate affine leaves | Store one coefficient array plus one integer bias. Do not misuse the vector-valued `AffineMap` or synthesize fake `AxisSpec`s. |
| Assignment lowering | Reuse `termAxisUIDs`, `idxToRow`, `substitutePins`, and the existing `context ++ output ++ reduction` basis. |
| Axiswise mask lowering | Use the local output-tensor basis. In scans, match the current reference behavior exactly: seeded/context UIDs are absent and therefore evaluate as coordinate zero. |
| Lowering API | Keep one private recursive core, but expose separate `lowerFactorPredicate` and `lowerMaskPredicate` entry points so callers cannot silently exchange factor context/pins with the mask basis. Do not add coordinate metadata to `ScheduledProgram` or persistent plan IR. |
| Nonlinear math | Generalize the existing row implementation around a coordinate-inclusion callback. Keep one implementation of softmax, normalize, and L2 normalize. |
| Boolean contraction | Reuse `ScalarBinOp.min/max`, `ScalarConst.bool`, `ContractionAlgebra`, and the existing Dense folds. Add no logical-operation constructors. |
| Boolean carrier | Match the reference interpreter: Boolean is an algebra/signature tag over Float storage, not native Boolean storage. Admit f64 and Bool reads into either f64 or Bool assignments; keep f32 rejected. |
| Runtime 0/1 validation | Do not add it in these slices. The reference path does not enforce it, so doing so would create a new checked/reference divergence. |
| Duplicate tensor declarations | Reject duplicate tensor-bearing declaration names in the source pipeline before building `DeclEnv`. Today `resolveDecls` is last-wins while `combineFor` is first-wins, so conflicting tensor/predicate declarations have no coherent dtype. Axis/iteration declarations remain a separate namespace. |
| Predicate destination with max/min | Continue treating this as invalid source. Backend parity in these slices is for schedules satisfying the DSL pipeline's existing `checkDtypes` invariant; add the same typed rejection at the direct `ScheduledProgram` boundary. |
| Input signatures | Keep `InputSignature.ofDenseInputs` as its existing f64 compatibility helper. Add a separate declaration-aware helper. |
| Result dtype | Keep shared `EvalReport` unchanged. Expose materialized name/signature pairs from `PreparedPlan`. |
| JAX | Reject Iverson factors, masked axiswise operations, and Bool algebra/dtypes explicitly. Do not implement JAX predicate semantics in these slices. **As shipped** (Task 4.5 and its reviews): the rejection is a located typed gate (`JaxSupportError`/`checkJaxAssignSupport`) covering a Boolean destination, a Boolean source, tropical max/min algebra, an inline unary read, and a CONTEXTFUL assignment (non-empty `AssignPlan.contextShape`, `contextualAssignment` — neither lowering has a kernel parameter for the runtime context coordinate), applied at every public renderer, lowerer, candidate conversion, and validator before Python or evidence exists. Iverson factors keep their own located `iversonFactor`, and `einsumOnly` additionally rejects a zero-padded read whose source extent disagrees with its own iteration extent (`labelExtentMismatch`, decided by the validator's own `einsumTermLabelExtents`). |
| Capability errors | Retain `maskOrPredicate`, `maskedAxiswiseNotSupported`, and `booleanOutput` as producer-less compatibility constructors after their last producer is removed. |

## 2. Three different meanings of "predicate"

These capabilities share syntax and values but are different compiler paths.

### 2.1 Iverson factors

`[condition]` is already elaborated by `DSL/Elab.lean` to
`Factor.iverson : BoolExpr -> Factor`. It is a coordinate-dependent scalar factor inside a product:
it contributes `1.0` when true and `0.0` when false. It reads no tensor, creates no graph edge, and
has no tensor slot or dtype of its own.

The reference path already evaluates it through `Eval/Gather.lean`'s `evalPred`, `evalBool`, and
`gather`. The checked backend still rejects it in both `checkFactor` and the defensive
`residualizeAssignment` arm.

### 2.2 Axiswise `where=` masks

`softmax(where ...)(...)`, `normalize(where ...)(...)`, and
`l2normalize(where ...)(...)` already carry `Option BoolExpr` on `Nonlin.axiswise`. A mask is
evaluated against output coordinates after the assignment has produced the preactivation tensor.
It is not a `TermPlan` factor and creates no tensor dependency.

The reference path already applies masks in `Eval/Nonlin.lean`. The checked compiler rejects them in
`resolveNonlinAxis`, and `RawAxiswisePlan` has no mask field.

### 2.3 Predicate tensors

`Decl.predicate` marks a named tensor whose destination assignment uses Boolean conjunction and
existential/disjunctive reduction. Unlike an Iverson factor, a predicate tensor:

- owns a tensor signature and slot;
- may be an external input or a produced value;
- creates normal read and graph dependencies;
- may be scan state, scratch, a capture, or a published history.

The DSL pipeline already distinguishes predicate destinations and forbids non-identity
nonlinearities and non-sum aggregation on them. The reference evaluator already selects
`Combine.bool`. The checked compiler currently rejects every predicate declaration before it can
distinguish external, produced, or unused declarations.

## 3. Existing machinery to reuse

### 3.1 Source and shape machinery that remains unchanged

- `PredArith`, `BoolExpr`, `RelOp`, `Factor.iverson`, and `Nonlin.axiswise` in `DSL/Ast.lean`.
- Predicate elaboration in `DSL/Elab.lean`.
- `PredArith.traverseAxes`, `BoolExpr.traverseAxes`, `Factor.traverseAxes`,
  `Nonlin.traverseAxes`, and `RHSExpr.traverseAxesWithMask` in `DSL/TraverseAxes.lean`.
- UID assignment, relabeling, canonicalization, and schedule traversal in `DSL/Pipeline/`.
- `Factor.read?`, `Stmt.readFactors`, and `Stmt.readNames`: Iverson and masks read no tensor.
- `termAxisUIDs`: it already includes Iverson axes, including axes mentioned by no tensor read.
- `readAxisUIDs`: it includes factor predicates but deliberately excludes nonlinearity masks.
- Existing size inference. A predicate-only contraction axis still needs an explicit size because
  tensor reads are what generate shape constraints.

### 3.2 Assignment-plan machinery to reuse

- `ReadPlan` remains the complete representation of a tensor read, including unary factors.
- `AffineMap` remains the vector-valued source-coordinate map for `ReadPlan`.
- `idxToRow` remains the source `IdxExpr` to dense affine-row conversion.
- `substitutePins` remains the base-scan pin residualizer.
- `TermPlan.iterationShape`, `contextPos`, `outputPos`, and `reductionPos` remain unchanged.
- Factor, reduction, and term folds remain ordered left folds.
- `runDenseAssignAt` remains the one Dense assignment execution choke point.

### 3.3 Boolean machinery to reuse

- `ScalarDType.bool` and `ScalarConst.bool` already exist.
- `ScalarBinOp.min` and `.max` already execute over Float values.
- `ContractionAlgebra` already separates factor and reduction operations and identities.
- `Combine.bool` already specifies the reference semantics:
  - factor conjunction: `min`, identity `1.0`;
  - reduction/term disjunction: `max`, identity `0.0`.
- `DenseTensor` already supplies the carrier used by both reference and checked execution.
- Scan captures already compare complete `TensorSignature`s.

### 3.4 Nonlinearity machinery to reuse

`Eval/Nonlin.lean` already owns:

- row grouping along any axis position;
- survivor-only softmax maximum;
- masked denominator handling;
- exact-zero output for masked entries;
- exact-zero output for all-masked and zero-denominator rows;
- softmax, L1 normalize, and L2 normalize formulas.

The checked path should adapt predicate evaluation to this implementation rather than copy any
formula.

## 4. Item 5 design: positional predicates

### 4.1 Why source `BoolExpr` must not be stored in a checked plan

Source `BoolExpr` contains `PredArith`, whose leaves contain `IdxExpr`, whose axis references contain
`AxisSpec` names, kinds, and UIDs. Keeping it would violate `Eval/Plan/Kernel.lean`'s positional,
name-free, UID-free boundary. It would also make alpha-equivalent plans compare differently and
force execution and codegen to reconstruct a UID environment.

The rejected alternatives are:

1. **Store source `BoolExpr`:** violates the checked-plan boundary.
2. **Construct synthetic positional `AxisSpec`s:** leaves meaningless names/kinds in equality and
   abuses a source type as an execution type.
3. **Precompute a truth table in the plan:** UID-free but potentially Cartesian/exponential in plan
   size.
4. **Parameterize the source AST over its leaf type:** elegant but unnecessarily churns elaboration,
   traversal proofs, `ToExpr`, and every existing source consumer.

### 4.2 Minimal new data

Add three types beside `ReadPlan` and `TermPlan` in `Eval/Plan/Kernel.lean`:

- `PosPredArith`
  - affine leaf: `Array Int` coefficients and `Int` bias;
  - multiplication;
  - integer absolute value.
- `PosBoolExpr`
  - relation using the existing `RelOp`;
  - conjunction;
  - disjunction;
  - negation;
  - integer equality.
- `FactorPlan`
  - tensor read carrying `ReadPlan`;
  - Iverson carrying `PosBoolExpr`.

`RelOp` is already UID-free and should be reused directly. Add only the `BEq` support needed by the
new derived plan types; do not introduce a second relation enum.

An affine predicate leaf is scalar-valued, whereas `AffineMap` is vector-valued with one row per
source-tensor dimension. A small scalar leaf is clearer and avoids one-element-array conventions.

### 4.3 Preserve one ordered factor sequence

Change `TermPlan.factors` to `Array FactorPlan`. Reads and predicates must remain interleaved in
source order because:

- the Dense factor fold is ordered;
- Float NaN, infinity, and signed-zero behavior can make reordering observable;
- checker and causality diagnostics carry original factor indices.

Every filtered traversal must retain `(originalFactorIndex, read)` rather than reindexing the
filtered reads.

### 4.4 Assignment predicate residualization

Add one private recursive lowering core in `Eval/Plan/Compile.lean`. It receives an ordered basis
and pin map, but is not the API used directly by compiler call sites. Expose a named
`lowerFactorPredicate` entry point that receives `contextUids`, `outputUids`, pins, the term, and
the predicate; it derives that term's reductions and invokes the private core.

For each embedded `IdxExpr`:

1. use `idxToRow` over the ordered basis;
2. use `substitutePins`;
3. store the residual coefficient array and bias.

The basis remains exactly the one `residualizeAssignment` already computes:

`contextUids ++ outputUids ++ perTermReductionUids`.

This gives the required behavior without a second axis-discovery implementation:

- retained output axes precede contracted axes;
- scan context coordinates remain leading positions;
- base `iterAt` values are folded into affine biases;
- axes mentioned only in an Iverson factor become contracted axes through `termAxisUIDs`;
- identity is by UID, never by axis name.

Do not add an `AssignmentCoordinateScope` or other coordinate-context field to `ScheduledProgram`
or checked plan IR. The explicit arguments already exist at the three assignment construction
sites, and the coordinate-parity spike's disposable implementation needed only the two named
wrappers. If production wiring reveals repeated derivation at two or more call sites, the
implementation may extract a private compiler-local helper or structure, but only when it removes
measured duplication. The separate factor/mask entry points and their policies remain the public
shape inside `Compile.lean`; callers must not reach a generic basis-and-pins entry point.

### 4.5 Checked validation and Dense execution

For `FactorPlan.read`, preserve every existing check and runtime behavior.

For `FactorPlan.iverson`:

- recursively require each affine leaf's coefficient width to equal
  `TermPlan.iterationShape.size`;
- report the original term and factor indices on a mismatch;
- evaluate directly against the already-built iteration coordinate;
- return `1.0` or `0.0`;
- perform no tensor-store validation.

Source-slot collection, graph availability, captures, and causality inspect only read factors.
Their behavior for reads must not otherwise change.

### 4.6 Axiswise mask representation and lowering

Add `mask : Option PosBoolExpr := none` to `RawAxiswisePlan`.

Lower it through a separate `lowerMaskPredicate` entry point that accepts only the local output
basis and predicate. It supplies an empty pin map internally, so a caller cannot accidentally pass
factor context or base pins to a mask.

Its basis is the axis order of the local tensor:

- top level: retained output UIDs;
- scan base: non-seeded output UIDs;
- scan recurrence: non-seeded output UIDs.

This deliberately matches the reference scan path. `evalStmtSliceSeeded` passes only `sliceUids` to
`applyNonlin`; a mask reference to a seeded/context UID is missing from that map and `evalIdx`
therefore reads it as zero. The checked compiler should densify that UID out of the output basis,
which gives the same constant-zero coordinate. Broadening mask visibility to scan context is a
separate semantic change.

`checkAxiswise` recursively checks every mask affine width against `shape.size`.

### 4.7 Share nonlinear formulas through a coordinate predicate

Generalize the private row implementation in `Eval/Nonlin.lean` around a function from a full local
coordinate to "included?":

- the source wrapper evaluates `BoolExpr` using `axisUids`, `coordMap`, and `evalBool`;
- the checked wrapper evaluates `PosBoolExpr` directly against the positional coordinate;
- the no-mask wrapper always includes the coordinate.

Keep row construction and all three normalization formulas in one implementation. This is the
smallest refactor that avoids semantic drift between source and checked masking.

### 4.8 Executable and JAX policy

`Eval/Plan/Executable.lean`'s affine-table and einsum candidates represent tensor reads only. During
the factor-type migration, their validators must treat an Iverson-bearing semantic assignment as
invalid rather than filter it out or stamp it with reference evidence. The experimental
`EvalPlanCodegen.lean` and its affine-corpus feature extractor must be adapted in the same task:
`FactorPlan` changes their input type even though they live outside the default build.

There is a measured prerequisite: `lake build JaxExperiment` is already red on the current tree.
`CheckedEvalPlan.checkedNodes` now contains the complete `CheckedPlanStepEvidence` sum, but the
experimental code still projects a nonexistent `.plan` field and treats the array as
`CheckedAssignPlan`; its error renderer is non-exhaustive, and its `idRaw` fixture still initializes
removed `RawEvalPlan.version`/`numericMode` fields and inserts a bare `AssignPlan` instead of a
`PlanStep`. Task 5.0 repairs that baseline before predicate work changes the factor type.

After that repair, the generator should inspect the complete checked-step sequence and add located
`JaxCodegenError` cases for:

- an Iverson factor, including node/term/factor index;
- a masked axiswise step;
- a checked step kind the generator does not support.

Both affine-reference and einsum modes reject these features. Implementing JAX predicate truth
tables or Boolean algebra is outside these slices.

## 5. Item 4 design: Boolean tensors

### 5.1 Match the reference carrier policy

The current source semantics are not a conventional runtime Boolean type system:

- every tensor is stored as Float;
- the destination declaration selects the contraction algebra;
- source declarations do not change gathering;
- source values are not checked to be `0.0` or `1.0`;
- predicate reads may feed real outputs;
- real reads may feed predicate outputs.

The checked backend should preserve this behavior:

- admit f64 and Bool source signatures into either f64 or Bool assignments;
- select the algebra from the destination signature;
- do not add a runtime 0/1 check;
- keep f32 rejected.

This makes `ScalarDType.bool` an algebra/signature tag over the existing Float carrier. A dedicated
non-binary differential fixture must pin this behavior; otherwise a future "type tightening" could
silently break parity.

### 5.2 Reuse `min` and `max` for Boolean contraction

Add one admitted Boolean algebra:

- factor operation: `ScalarBinOp.min`;
- factor identity: `ScalarConst.bool true`;
- reduction and term operation: `ScalarBinOp.max`;
- reduction and term identity: `ScalarConst.bool false`.

Extend Dense constant decoding so Boolean constants become `1.0` and `0.0`. `applyOp` and all three
folds remain unchanged.

Do not add `logicalAnd` or `logicalOr`: over the existing Float carrier, `min` and `max` are exactly
the operations the reference `Combine.bool` uses. The destination dtype and Boolean constants
already distinguish this algebra from tropical min/max.

Replace flat algebra admission with destination-specific admission:

- f64 destinations: real sum-product and tropical max/min;
- Bool destinations: Boolean min/max algebra only;
- f32 destinations: none.

Front-end-produced predicate assignments are already constrained to identity nonlinearity and sum
aggregation by `checkDtypes`. The reference evaluator mechanically prioritizes max/min for a
hand-built schedule that bypasses that phase, but such a value is not a valid DSL-pipeline output.
`prepareEvalPlan` must re-establish the source invariant and reject predicate max/min with a typed
`CapabilityError.predicateAggregation` carrying the destination name and aggregation operator.
Differential parity claims in these slices therefore cover `compileToScheduled`
outputs plus hand-built schedules that satisfy the same invariant, not arbitrary invalid
`ScheduledProgram` values.

### 5.3 Declaration-aware dtype resolution

Add one compiler helper that maps `(DeclEnv, name)` to:

- Bool for a declared predicate;
- f64 for tensor, linear, or undeclared names.

Externality remains determined by `ScheduledProgram.extNames`, not declaration kind:

- a read-only declared predicate is an external Bool input;
- a written declared predicate is produced;
- an unused declaration gets no slot;
- an undeclared read remains an external f64 input.

Use this helper for external signature validation and every produced signature.

First remove an existing ambiguity: `resolveDecls` currently inserts tensor-bearing declarations into
`DeclEnv` with last-declaration-wins semantics, while the reference `combineFor` searches the complete
declaration list with first-declaration-wins semantics. Reject duplicate tensor-bearing declaration
names before constructing the environment. Also make `combineFor` ignore axis/iteration declarations
when looking up an output's algebra, because axes and tensors are separate namespaces and an earlier
same-named axis must not hide a predicate declaration. This is directly required by Bool admission;
otherwise the same scheduled program can be simultaneously f64 and Bool depending on which existing
helper observes it. Add `CompileError.duplicateTensorDecl`, a conflicting tensor/predicate fixture,
and a same-named-axis/predicate fixture.

Keep `InputSignature.ofDenseInputs` unchanged. Add a separate declaration-aware companion, such as
`InputSignature.ofDenseInputsForDecls`, which labels supplied names from a `DeclEnv`. It constructs a
new signature; it never overwrites or "corrects" an explicitly supplied `InputSignature`.

### 5.4 Preserve complete signatures through scans

Replace `CompiledScan.stateShapes` with complete `stateSigs`. Reuse those signatures for:

- base destinations;
- recurrence destinations;
- state captures;
- scratch and state-result slots;
- complete-history publication.

External captures already copy complete outer signatures and `checkCaptures` already compares
complete signatures.

Add a scan write check requiring the block output signature's dtype to equal the destination
state's dtype. Geometry and shape checks alone currently allow a hand-built raw plan to write an f64
slice into Bool state. This is a newly-live sibling of the existing write validation and needs a
direct-plan negative fixture.

The scan worker remains Float-based:

- zero initialization is Boolean false;
- `commitWrite` copies Float values;
- no alternate state storage is needed.

`checkNonlinIO` remains f64-only. Predicate destinations cannot carry source nonlinearities, so Bool
support must not accidentally admit relu, softmax, or normalization over Bool slots.

### 5.5 Result signatures without changing `EvalReport`

`EvalReport` is shared with the reference evaluator and should not import plan-layer dtype.

Add a plan-local `PreparedPlan.materializedSignatures` accessor that pairs each
`materializedNames` binding with its `raw.tensorSigs` entry, preserving schedule order and repeated
names. Callers that need the meaning of Float-backed results can query the prepared plan; existing
`runPreparedDense` callers remain source-compatible.

### 5.6 JAX Bool rejection

The current JAX path claims ordered binary64 sum-product or an einsum optimization experiment. It
does not implement Boolean min/max algebra.

Extend its typed validation to reject Bool signatures/algebra before Python emission. Core
`Executable.lean` candidate validation must likewise refuse to label a Boolean semantic assignment
as `orderedReference64`.

## 6. Slice 5 tasks

Slice 5 lands first and closes Iverson factors and axiswise masks. The executable,
author-verified version of these tasks is
[`docs/superpowers/plans/2026-09-01-slice-5-predicate-mask-parity.md`](../docs/superpowers/plans/2026-09-01-slice-5-predicate-mask-parity.md)
(gitignored; verified paths, compiled snippets, named donors, locator fixtures).

### Task 5.0 - Restore the optional JAX target baseline

**Deliverable**

Repair the already-stale experimental code against the current checked-step API before changing
`TermPlan`:

- pattern-match every `CheckedPlanStepEvidence` case;
- route assignments through the existing affine/einsum paths;
- reject pointwise, axiswise, and scan steps with one located unsupported-step error;
- make compile-cause rendering exhaustive;
- remove obsolete raw-plan fields and wrap fixture assignments in `PlanStep.assign`.

This task restores existing intended behavior; it does not add predicate or Boolean support.

**Files**

- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`

**Fixtures: 4; mutation cycles: 2**

- existing identity assignment remains accepted;
- a pointwise checked step fails with the exact unsupported-step location;
- an axiswise checked step fails with the exact unsupported-step location;
- a scan step fails with the exact unsupported-step location.

**Gate**

`lake build JaxExperiment` must be green before Task 5.1 begins.

### Task 5.1 - Introduce ordered positional factor IR

**Deliverable**

Add positional expression types and `FactorPlan`; migrate every `TermPlan` consumer; implement direct
checked-plan validation and Dense execution. Keep source Iverson rejected until Task 5.2.

**Production files**

- `leanncd/LeanNCD/Eval/Plan/Kernel.lean`
- `leanncd/LeanNCD/Eval/Plan/Error.lean`
- `leanncd/LeanNCD/Eval/Plan/Check.lean`
- `leanncd/LeanNCD/Eval/Plan/Dense.lean`
- `leanncd/LeanNCD/Eval/Plan/RawStep.lean`
- `leanncd/LeanNCD/Eval/Plan/Block.lean`
- `leanncd/LeanNCD/Eval/Plan/EvalPlan.lean`
- `leanncd/LeanNCD/Eval/Plan/Scan.lean`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/LeanNCD/Eval/Plan/Executable.lean`
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`
- `leanncd/experiments/jax_bridge/EvalPlanAffineCorpus.lean`

`Compile.lean` changes in this task are mechanical adaptation of read and unary-read construction and
causality traversal, not source Iverson admission.

**Mechanical fixture migration**

Wrap existing direct `ReadPlan` factor literals in the affected files under `leanncd/test/Eval/Plan/`.
The current direct-plan set includes `BlockTest`, `CheckedPrivacyTest`, `CompileTest`,
`EvalPlanTest`, `ExecutableTest`, `GraphCheckTest`, `GraphDenseTest`, `KernelCheckTest`,
`KernelDenseTest`, `NonlinCompileTest`, `NonlinDenseTest`, `ScanCompileTest`, and `ScanTest`.
Re-run a repository-wide type-directed search after the migration rather than treating this list as
closed. `AdapterTest`, `ContractTest`, `DifferentialTest`, and `ScanContractTest` mention source
factors or import related modules but do not currently contain direct `ReadPlan` factor literals.

**New fixtures: 6; mutation cycles: 4**

| Fixture | Donor | What it distinguishes |
|---|---|---|
| Accepted positional Iverson | `KernelCheckTest.goodPlan`; insert a correctly sized predicate | Predicate checker path |
| Predicate-width locator | Same donor; insert a malformed predicate between the two reads | Original factor index 1, not a filtered index |
| True predicate execution | Accepted positional fixture; predicate true | `1.0` factor |
| False predicate execution | Same fixture; predicate false | Factor annihilation |
| No graph dependency | `GraphCheckTest.diamondPlan`; insert predicate | No fake source slot |
| Causality locator | A `ScanTest` block with a non-assignment before the bad read; insert predicate before that read | Block-step and original-factor locators both remain stable |

**Required review artifact**

Produce the factor-kind x consumer table from section 9 before review.

This task also establishes the closed, located experimental-JAX rejection for `FactorPlan.iverson`
and changes affine-corpus feature extraction to inspect read factors explicitly. It must leave
`lake build JaxExperiment` green; deferring this adaptation would leave the repository's optional
target uncompilable between Tasks 5.1 and 5.4.

### Task 5.2 - Admit and residualize existing source Iverson predicates

**Deliverable**

Remove the two `.iverson` rejection producers and recursively translate the existing UID-bearing
`BoolExpr` into `PosBoolExpr` through `lowerFactorPredicate`, using the assignment's existing
context, output basis, and pins. Keep the generic recursive basis-and-pins core private.

**Files**

- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean`
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`
- `leanncd/test/Eval/Plan/DifferentialTest.lean`
- `leanncd/test/Eval/Plan/AdapterTest.lean`

**Fixtures: 8; mutation cycles: 6**

| Fixture | Donor and minimal change |
|---|---|
| Pure Iverson | `Portfolio/RelationalTest.lean` RL1, unchanged |
| Retained/reduction order | `Portfolio/RecurrenceTest.lean` RC3, unchanged |
| Multiple reduction positions | `CompileTest.multiReductionSched`; append `[j < k]` and inspect `j -> 1`, `k -> 2` |
| UID, not name | `DifferentialTest.sameAxisNameSched`; add a predicate comparing the two `"l"` axes with distinct UIDs |
| Scan base Iverson | Convert the base-side `ScanCompileTest.badIverson` rejection |
| Scan recurrence Iverson | Convert the recurrence-side `badIverson` rejection |
| Pin and context residualization | Clone an accepted base/recur pair; use nested multiplication and absolute value over a base pin and a recurrence context axis |
| Source causality factor locator | Clone `ScanCompileTest`'s existing `stateReadNotCausal` term-1/factor-1 fixture; insert an Iverson immediately before the noncausal state read and require the original factor index |

Retain `CapabilityError.maskOrPredicate` with no producer.

### Task 5.3 - Add positional axiswise masks and share nonlinear math

**Deliverable**

Add `RawAxiswisePlan.mask`, its checker and Dense adapter, source lowering through
`lowerMaskPredicate` at all three compiler construction sites, the shared coordinate-inclusion
nonlinear core, and the complete-step JAX support check that routes the checked axiswise case to
the generic unsupported-step error. Do not introduce a schedule/plan coordinate-context field.
Extract a private compiler-local helper or structure only after completed wiring demonstrates
identical derivation at two or more sites; record the duplicated expressions it replaces.

**Files**

- `leanncd/LeanNCD/Eval/Nonlin.lean`
- `leanncd/LeanNCD/Eval/Plan/Nonlin.lean`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`
- `leanncd/test/Eval/Plan/NonlinCheckTest.lean`
- `leanncd/test/Eval/Plan/NonlinDenseTest.lean`
- `leanncd/test/Eval/Plan/NonlinCompileTest.lean`
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`

**Fixtures: 14; mutation cycles: 8**

| Fixture | Donor and minimal change |
|---|---|
| Top-level masked normalize | `Portfolio/NormTest.lean` NM4, unchanged |
| Non-last mask basis | NM5; add asymmetric `where s < q` so swapping the `s` and `q` positions changes the result |
| Masked softmax | NM4; change only the function |
| Masked L2 normalize | NM4; change only the function |
| Three all-masked rows | NM4; use `s < 0`, once per axiswise function |
| Masked extreme | NM4; change to softmax and place `1000` in the already-excluded `s = 0` entry |
| Masked scan base | Convert `ScanCompileTest.maskedAxiswiseBase` |
| Masked recurrence | Convert `ScanCompileTest.maskedAxiswiseRecur` |
| Seeded-axis-zero parity | Recurrence donor; use `where l = 0`, which is always true under the current missing-seeded-UID behavior but would vary if live context were substituted |
| Non-seeded plain-free scan coordinate | Derive from `ScanGen.template6`; retain the separate `.freeNorm i` and use the base mask `r != 0` over the eliminated non-seeded `.free r` coordinate |
| Eliminated freeNorm scan coordinate | Use the exact source `iter r = 2, c = 2; tensor Z(r); G[r.,0] := normalize(where r ≠ 0)(Z[r]); G[r+1,c+1] := G[r,c]` with `Z = [1,3]`; require source, the checked backend, and the hand-expected tensor of shape `[2,2]` with data `[0,0,1,0]` all to agree |
| Masked axiswise JAX rejection | Compile the masked top-level donor and require the generic located unsupported-step error before Python emission |

Retain `NonlinCompileError.maskedAxiswiseNotSupported` with no producer.
The eliminated-`.freeNorm` mutation must zero that coordinate during lowering and must fail this
fixture.

### Task 5.4 - Independent oracle, separate predicate corpus, and JAX rejection gates

**Deliverable**

Teach the independent scan unroller to rewrite predicate arithmetic and masks without importing the
implementations it checks; add compact curated parity cases; exercise the JAX rejections established
by Tasks 5.1 and 5.3.

**Files**

- `leanncd/test/Eval/PropertyOracle/Gen.lean`
- `leanncd/test/Eval/PropertyOracle/ScanGen.lean`
- `leanncd/test/Eval/PropertyOracle/ScanUnroll.lean`
- `leanncd/test/Eval/PropertyOracle/ScanOracle.lean`
- `leanncd/test/Eval/Plan/DifferentialTest.lean`
- `leanncd/test/Eval/Plan/ExecutableTest.lean`
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`
- `leanncd/experiments/jax_bridge/EvalPlanAffineCorpus.lean`

**Curated cases: 12; mutation cycles: 6**

- scan-free: RL1, RL6, RL7, RL8, NM4, and AT12;
- scan: recurrence Iverson, masked recurrence, seeded-axis-zero semantics, one base Iverson, and the
  `ScanGen.template6`-derived non-seeded `.free` scan-axis case;
- JAX: Iverson inserted at factor index 1 in the `idRaw` family.

`ScanUnroll` must recursively substitute `IdxExpr` inside both `PredArith`/`BoolExpr` occurrences,
including axiswise masks, while preserving factor order. The new oracle code may reuse source AST
traversal conventions but must not call checked predicate lowering/evaluation.

`ScanUnroll`'s Slice 5 fragment must explicitly reject an axiswise operation whose normalization
axis is an eliminated scan coordinate, with the named error
`ScanUnroll.fragment.eliminatedNormalizationAxis`. Do not add grouped `ScanUnroll` support in Slice
5. The eliminated-`.freeNorm` case is independently pinned in Task 5.3 by its hand-expected tensor,
source/checked comparison, and the mutation that zeroes the eliminated coordinate.

Do not append these cases to `PropertyOracle.enumPrograms`. The affine JAX corpus consumes that list
wholesale and treats every affine-reference rejection as fatal, while Iverson and masked programs
must now be rejected by JAX. Export a separate compact `predicatePrograms` list (or keep an
equivalent dedicated list in `DifferentialTest`) and run the reference/checked differential over it
separately. Keep the existing affine corpus's source list and positional indices stable. Scan cases
remain in their separate scan corpus and must be remeasured there.

## 7. Slice 4 tasks

Slice 4 starts only after Slice 5's full build and whole-branch review are clean.

### Task 4.1 - Admit the Boolean algebra in raw checked assignments

**Deliverable**

Add the Boolean algebra from existing `min/max` and Boolean constants; make assignment algebra
admission destination-specific; admit f64/Bool factor reads according to the Float-carrier policy.

**Files**

- `leanncd/LeanNCD/Eval/Plan/Check.lean`
- `leanncd/LeanNCD/Eval/Plan/Dense.lean`
- `leanncd/LeanNCD/Eval/Plan/Executable.lean`
- `leanncd/test/Eval/Plan/KernelCheckTest.lean`
- `leanncd/test/Eval/Plan/KernelDenseTest.lean`
- `leanncd/test/Eval/Plan/ExecutableTest.lean`

**Fixtures: 9; mutation cycles: 5**

| Fixture | Donor |
|---|---|
| OR versus numeric sum | Existing reference Bool-versus-real scalar contraction from `Eval/ScanTest.lean` |
| Empty Boolean product is true | `KernelDenseTest.efpPlan` |
| Zero-extent Boolean reduction is false | `KernelDenseTest.zerdPlan` |
| False factor annihilates | Accepted Boolean raw plan |
| Bool source into f64 | `KernelCheckTest.goodPlan`; change one source signature |
| f64 source into Bool | Same donor; change destination and algebra |
| Wrong algebra for Bool | Same Boolean donor; restore real algebra |
| f32 remains rejected | Existing dtype rejection fixture |
| Bool candidate cannot claim reference evidence | `ExecutableTest` identity candidate; change destination signature and algebra to Bool |

The f64-to-Bool fixture must include non-binary Float data and compare to the reference evaluator so
it fails if runtime 0/1 validation is introduced.

### Task 4.2 - Resolve declaration dtypes and preserve top-level signatures

**Deliverable**

Admit predicate declarations, add declaration-aware input-signature construction, preserve validated
input signatures, allocate top-level destinations with their declared dtype, and expose materialized
signatures from `PreparedPlan`.

**Files**

- `leanncd/LeanNCD/Eval/Plan/Signature.lean`
- `leanncd/LeanNCD/Eval/Plan/Prepared.lean`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/LeanNCD/Eval/Plan/Error.lean`
- `leanncd/LeanNCD/DSL/Pipeline/Structural.lean`
- `leanncd/LeanNCD/Exec/Uid.lean`
- `leanncd/LeanNCD/Eval/Contract.lean`
- `leanncd/test/DSL/Pipeline/StructuralTest.lean`
- `leanncd/test/Eval/ContractTest.lean`
- `leanncd/test/Eval/Plan/SignatureTest.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean`
- `leanncd/test/Eval/Plan/AdapterTest.lean`
- `leanncd/test/Eval/Plan/DifferentialTest.lean`

**Fixtures: 14; mutation cycles: 8**

| Fixture | Donor and minimal change |
|---|---|
| Declared external predicate into real output | `Portfolio/GnnScatterTest.lean` GN2 |
| Predicate contraction into real degree | GN3 |
| Produced predicate output | Existing reference Bool scalar contraction |
| Predicate output produced from Iverson | Slice 5 RL1 checked fixture; add a predicate declaration |
| Unused predicate declaration | Simple accepted `CompileTest` schedule; add one unused declaration |
| Compatibility helper remains f64 | Existing `SignatureTest` `ofDenseInputs` fixture |
| Materialized dtype/order/repeated names | `CompileTest.repeatSched` for binding order and `DifferentialTest.repeatProg` for executing last-write-wins behavior |
| Duplicate declarations fail loud | Clone a structural declaration fixture for tensor/tensor, predicate/predicate, tensor-then-predicate, and predicate-then-tensor duplicates |
| Axis name does not hide predicate dtype | Clone a predicate scalar fixture; add an earlier same-named axis declaration |
| Hand-built predicate max fails at preparation | Clone the produced-predicate fixture; change only `agg` to max and require `CapabilityError.predicateAggregation` with the exact name/operator payload |
| Hand-built predicate min fails at preparation | Same donor; change only `agg` to min and require the corresponding exact payload |

Retain `CapabilityError.booleanOutput` with no producer.

### Task 4.3 - Thread complete Boolean signatures through scans

**Deliverable**

Replace shape-only state metadata with complete signatures, remove every semantic hard-coded f64
allocation in scan compilation, and check write-source/state dtype equality.

**Files**

- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/LeanNCD/Eval/Plan/Scan.lean`
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`
- `leanncd/test/Eval/Plan/ScanTest.lean`
- `leanncd/test/Eval/PropertyOracle/ScanGen.lean`
- `leanncd/test/Eval/PropertyOracle/ScanOracle.lean`
- `leanncd/test/Eval/Plan/DifferentialTest.lean`

**Fixtures: 5; mutation cycles: 6**

| Fixture | Donor and minimal change |
|---|---|
| Predicate state with duplicate true witnesses | `ScanGen.template4`; declare state predicate and make recurrence have two true witnesses |
| Predicate base output | Accepted identity base assignment; declare its state predicate |
| Predicate recurrence and state capture | Same `template4` mutation |
| Coupled Bool/f64 states | Existing two-state accepted scan; declare one state predicate |
| Raw write dtype mismatch | Valid `ScanTest` raw plan; change only one block-output signature |

Independently restore each former f64 allocation site during mutation testing. The fixtures must fail
for state destination, base result, recurrence result, state capture, scratch/result, and published
history mistakes rather than merely proving one endpoint.

### Task 4.4 - Boundary parity, JAX Bool rejection, corpus, and docs

**Deliverable**

Complete top-level and scan differential coverage, named adapter coverage, plan-local result-signature
coverage, explicit JAX Bool rejection, count remeasurement, and documentation.

**Files**

- `leanncd/test/Eval/Plan/AdapterTest.lean`
- `leanncd/test/Eval/Plan/DifferentialTest.lean`
- `leanncd/test/Eval/Plan/ExecutableTest.lean`
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`
- `leanncd/experiments/jax_bridge/EvalPlanAffineCorpus.lean`
- documentation listed in section 11

**Fixtures: 6; mutation cycles: 4**

- Bool scalar adapter round-trip from the reference Bool scalar donor;
- predicate input into real output from GN2/GN3;
- Bool scan adapter from Task 4.3;
- materialized-signature order from `CompileTest.repeatSched` plus execution through
  `DifferentialTest.repeatProg`;
- typed JAX rejection by changing `idRaw`'s destination signature/algebra to Bool;
- typed JAX rejection for a Bool source feeding an f64 destination.

## 8. Dependency and parallelism plan

The landing order is:

`5.0 -> 5.1 -> 5.2 -> 5.3 -> 5.4 -> Slice 5 review -> 4.1 -> 4.2 -> 4.3 -> 4.4 -> Slice 4 review`.

The following preparation can run in parallel without overlapping compiler edits:

- Task 5.0 JAX baseline repair and Task 5.1 positional checker/Dense design;
- Task 5.1 positional checker/Dense work and Task 5.3's source nonlinear callback refactor;
- mechanical direct-plan fixture wrapping and `ScanUnroll` predicate-substitution design;
- JAX rejection fixtures and curated source fixture construction;
- Task 4.1 raw algebra/checker work and Task 4.2 signature-helper/accessor work;
- Task 4.3 raw scan-write mismatch fixture and Task 4.2 top-level adapter fixtures.

All edits to `Eval/Plan/Compile.lean` must be integrated serially. Avoid parallel branches that both
modify residualization, nonlinear construction, or scan slot allocation.

## 9. Required sibling audits

### 9.1 Factor-kind x consumer table

Task 5.1 must produce this table from the implemented code, classifying each cell as required,
forbidden, or intentionally ignored:

| Consumer | Plain read | Unary read | Iverson |
|---|---|---|---|
| Source slot discovery | | | |
| Runtime store validation | | | |
| Source dtype/shape checking | | | |
| Predicate width checking | | | |
| Outer forward-read checking | | | |
| Block forward-read checking | | | |
| Scan capture discovery | | | |
| Source compile causality | | | |
| Checked scan causality | | | |
| Affine-table candidate validation | | | |
| Einsum/JAX lowering | | | |
| Corpus feature extraction | | | |

Every blank must be filled from code. Every "ignored" cell is an audit target.

### 9.2 Unchanged source walkers

Explicitly re-read and record why each remains correct:

- `Factor.read?`;
- `Stmt.readFactors` and `Stmt.readNames`;
- predicate and nonlinear-mask axis traversals;
- UID relabeling/canonicalization;
- `termAxisUIDs`;
- `readAxisUIDs`;
- size inference constraints.

### 9.3 Locator preservation

Audit both checked forward-read loops, checked scan causality, and source-facing scan causality.
Fixtures must contain:

- a predicate between two reads, distinguishing original from filtered factor index;
- a non-assignment block step before the failing assignment, distinguishing block-step from filtered
  assignment index;
- both distinctions simultaneously in at least one fixture.

### 9.4 Scan write checks

Item 4 makes dtype a newly-live write invariant. Extend the existing write-predicate case table with
block-output dtype versus state dtype. Do not modify write geometry. If implementation touches
`classifyWriteRow`, `baseWriteRowsOk`, `stepWriteRowsOk`, free extents, pins, or causality rows, stop
and require the full write-geometry sibling audit rather than reviewing only the diff.

## 10. Mutation matrix

Every mutation must be applied, observed failing at the named fixture, restored, and rerun passing.

| Mutation | Fixture that must fail |
|---|---|
| Resolve predicate axes by name | Same-name/different-UID fixture |
| Reverse output and reduction positions | RC3 and multi-axis structural fixture |
| Omit `substitutePins` in predicate leaves | Base pin fixture |
| Drop Iverson factors | RL1 or RL3 |
| Reindex filtered reads/predicates | Combined block-step/factor locator fixture |
| Treat Iverson as a source slot | Graph/capture fixture |
| Invert mask inclusion polarity | NM4 or AT12 |
| Include masked extreme in softmax maximum | NM4-derived masked-softmax extreme fixture |
| Return a uniform row for all-masked softmax | All-masked exact-zero fixture |
| Substitute live scan context into axiswise mask | Seeded-axis-zero parity fixture |
| Reuse real `add` instead of Bool `max` | Duplicate-witness OR-versus-sum fixture |
| Enforce 0/1 or reject f64 into Bool | Non-binary Float-carrier differential fixture |
| Leave one scan signature hard-coded f64 | Corresponding Bool scan fixture |
| Omit predicate/mask substitution in `ScanUnroll` | Three-way scan oracle |
| Filter unsupported predicate before JAX lowering | Located JAX rejection fixture |
| Label Bool candidate `orderedReference64` | Bool executable rejection fixture |

## 11. Documentation and capability-count sweep

Review and update current-boundary claims in:

- `papers/backend_missing_functionality.md`;
- `papers/wave_c_capability_manifest.md`;
- `papers/wave_f_capability_manifest.md`;
- `papers/wave_f_scanplan_proposal.md`;
- `papers/eval_ir.md`;
- `papers/jax_evalplan_architecture.md`;
- `leanncd/LeanNCD/Eval/AGENTS.md`;
- `leanncd/AGENTS.md`;
- `leanncd/experiments/jax_bridge/README.md`.

Historical plans stay historical unless they explicitly claim to describe the current boundary.
Frozen capability classifiers may remain frozen, but must say so where a reader could mistake them
for production admission.

Remeasure rather than infer:

- the scan-free property corpus total and accepted/rejected split;
- affine corpus count;
- scan corpus total and acceptance split;
- three-way scan fixture total;
- remaining `CapabilityError`, `NonlinCompileError`, and plan-error producer counts;
- JAX feature masks, JIT checks, artifact sizes, literal counts, and timings;
- full build job count.

Before declaring either sweep complete, value-grep the whole repository for every old count and
accept/reject split, not merely the documents edited by the task.

## 12. Verification and completion gates

From `leanncd/`, use `"$HOME/.elan/bin/lake"` and build edited production modules before any direct
`lake env lean` check.

Before the first build in a fresh slice worktree, run the repository's
`.claude/skills/new-slice/prepare-worktree.sh` workflow. If a manual cache transfer is ever needed,
select the fullest donor by comparing
`.lake/packages/mathlib/.lake/build/lib/**/*.olean` with
`.lake/packages/mathlib/Mathlib/**/*.lean`, copy the donor's complete `.lake/` with plain
`rsync -a`, and verify the destination is at least 95% built before invoking Lake. Do not use
GNU-only rsync progress flags on macOS.

Targeted coverage must include:

- `Eval.Plan.KernelCheckTest` and `Eval.Plan.KernelDenseTest`;
- `Eval.Plan.CompileTest`, `Eval.Plan.NonlinCheckTest`, and
  `Eval.Plan.NonlinDenseTest`;
- `Eval.Plan.ScanCompileTest`, `Eval.Plan.ScanTest`, and
  `Eval.Plan.EvalPlanTest`;
- `Eval.Plan.AdapterTest`, `Eval.Plan.DifferentialTest`, and
  `Eval.Plan.ExecutableTest`;
- `Eval.PropertyOracle.ScanUnroll` and `Eval.PropertyOracle.ScanOracle`;
- relational, recurrence, norm, attention, and GNN portfolio targets used as donors;
- `JaxExperiment` and both affine JAX runners;
- after `JaxExperiment`, `lake env lean experiments/jax_bridge/EvalPlanAffineCorpus.lean` so its
  non-default feature extractor is not silently left incompatible;
- final full `lake build`.

Each slice completion record must contain:

- commit SHA;
- exact commands and exit statuses;
- observed fixture values;
- before/after corpus counts;
- every mutation's failing and restored-passing observation;
- completed factor-consumer and sibling-audit tables;
- stale-value grep results;
- two independent whole-branch reviews:
  1. source/positional semantic parity and oracle independence;
  2. checker, scan write/capture/causality, locator, and unchanged-consumer correctness.

## 13. Explicit non-goals

- No parameterization or replacement of the source predicate AST.
- No coordinate-context field on `ScheduledProgram` or persistent checked-plan values.
- No source `BoolExpr` retained in checked plan IR.
- No predicate truth tables stored in checked plans.
- No native Bool tensor storage.
- No runtime 0/1 validation.
- No f32 support.
- No logical-operation additions to `ScalarBinOp`.
- No JAX predicate, mask, or Boolean execution.
- No change to the current `ieq` approximation.
- No broadening of scan mask access to seeded/context axes.
- No dynamic shapes, scatter writes, callback morphisms, or nested scans.
- No plan dtype added to shared `EvalReport`.
- No write-geometry change.

## 14. Stop conditions

Stop rather than improvise if:

- a measured reference fixture contradicts the Float-carrier mixed-dtype policy;
- parity for scan masks requires exposing seeded coordinates rather than preserving the current
  missing-UID-to-zero behavior;
- the shared nonlinear callback changes existing unmasked values;
- adapting JAX would require a production-to-experiment dependency;
- a production factor consumer exists outside the inventoried set;
- a raw checked scan can still write a block result whose dtype differs from its state;
- an oracle or parity fixture cannot be mutation-proven non-tautological;
- either final reviewer finds a load-bearing parity or soundness defect.
