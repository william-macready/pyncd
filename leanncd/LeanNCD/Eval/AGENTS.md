# LeanNCD/Eval

## Purpose
Owns: the reference-semantics interpreter for the compiled DSL — takes a `ScheduledProgram` (from `../DSL/Pipeline/`) plus concrete input tensors and produces concrete output tensors over a single dense representation (`DenseTensor`). Exists to pin down ground-truth semantics (contraction scoping, scatter/gather, scan boundary rules, nonlinearity dispatch, axis-size inference) that the static compiler and any future fast backend must agree with — not a fast/vectorized executor.
Does not own: parsing/compilation/routing (`../DSL/`).

**House principle: fail loud.** Any axis whose size can't be inferred, unknown tensor, or domain violation (`log`≤0, `sqrt`<0, `1/0`) throws `EvalError` rather than silently defaulting.

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| Source entry (compile + evaluate, preserving warnings) | `Entry.lean` — `TLProgram.eval` |
| Scheduled worker (no source compiler dependency) | `Eval.lean` — `evalScheduled`; `EvalReport` is `Eval/Report.lean` |
| Dense tensor rep, coord math | `Tensor.lean` |
| Index/predicate/mask eval, zero-padded reads, unary math fns | `Gather.lean` |
| Scatter (`Out[2*i] := ...`) evaluation | `Scatter.lean` |
| Nonlinearities (relu/sigmoid/tanh/gelu/leakyrelu/softmax/normalize/l2normalize), both carriers — each formula written ONCE over a private `NonlinScalarOps α` record, instantiated as binary64 (`PointwiseFn.apply`/`AxiswiseFn.applyCore`, and the `reluT` … `l2normalizeT` entries) and native binary32 (`PointwiseFn.apply32`/`AxiswiseFn.applyCore32`) | `Nonlin.lean` |
| Recurrence / n-D scan evaluation | `Scan.lean` — dense slice computation followed by independent LHS placement for admitted scan scatters |
| Einstein-summation contraction, dtype semiring dispatch | `Contract.lean` |
| LHS-slot shape vocabulary (`normAxisUidOf`, `outputShape`) | `Slots.lean` |
| Pure affine constraint solver (RREF over `ℚ`) | `SizeSolve.lean` |
| Axis-size inference fixpoint (`inferAxisSizes`, `scatterOutputShapes`) | `SizeInfer.lean` |
| Compatibility umbrella re-exporting `Slots`/`SizeSolve`/`SizeInfer` (no new code) | `Shape.lean` |
| Every typed diagnostic (`EvalError`, `ShapeError`, `EvalWarning`, `SolveDiagnostic`, `EvalFailure`) + their sole renderers | `Error.lean` |
| Checked, positional tensor-plan IR + compiler + adapter (Wave C/F, nonlinearity thread 4) | `Plan/` (17 files: `Types`, `Kernel`, `Graph`, `Error`, `Check`, `Coordinates`, `Dense`, `Signature`, `Prepared`, `Compile`, `Adapter`, `Executable`, `Block`, `RawStep`, `Scan`, `EvalPlan`, `Nonlin`) |
| "Does this model class evaluate correctly" test suite | `test/Eval/Portfolio/*.lean` |

### The `Plan/` subtree
A second, checked evaluation path (Wave C, extended by Wave F's checked scan graph), independent of
the legacy `Gather`/`Contract`/`Scan` evaluator above and reachable from `import LeanNCD` via
`Eval.Plan.Adapter` (Wave C files) and, for the four Wave F additions below (`RawStep`/`Block`/
`Scan`/`EvalPlan`) plus a fifth added by this thread (`Plan.Nonlin`, nonlinearity thread 4 — not a
Wave F addition), direct imports in the top-level `LeanNCD.lean`. One line per file — see `papers/wave_c_capability_manifest.md` (Wave C
design), `papers/wave_f_scanplan_proposal.md` (Wave F checked-scan design), and
`papers/wave_f_capability_manifest.md` (Wave F's accepted/rejected scan constructs, corpus counts,
and audit findings) for the full designs, not duplicated here. Exception:
`Executable.lean` (Thread 5) is NOT reachable from `import LeanNCD`, so the blanket "reachable via
`Eval.Plan.Adapter`" claim above does not cover it. ⚠️ **But do not read that as "untested" or "not
built by default" — an earlier version of this passage said it is "consumed only by
`experiments/jax_bridge`", and that is wrong.** `test/Eval/Plan/ExecutableTest.lean` imports
`LeanNCD.Eval.Plan.Executable` directly and is listed in `lakefile.toml`'s `Tests` glob, and `Tests`
is a **default target** — so a bare `lake build` does compile and exercise this module. Its other
consumers are `experiments/jax_bridge/EvalPlanCodegen.lean` (the non-default `JaxExperiment`
library, which a bare `lake build` does NOT build) and `spikes/AxisABoundaryProbe.lean` (no target
at all). Three consumers, in three different build situations — check which one you mean before
concluding a change here is unexercised.

| File | Owns |
|---|---|
| `Types.lean` | static specialization vocabulary — `ScalarDType`, `TensorSignature`, `InputSignature` |
| `Kernel.lean` | one local operation's IR — `AffineMap`, factor/term records (`ReadPlan` carries an optional `unary : Option UnaryOp` inline transcendental, applied after the OOB pad), `AssignPlan`, and the scatter placement IR `ScatterPlan` (a destination placement map `outCoeffs`/`outBias`/`destShape` plus `fill` and collision `reduce`, wrapping an inner `compute : AssignPlan` that produces the values being placed — S-A Task 1) |
| `Graph.lean` | the unchecked plan graph — `RawEvalPlan` |
| `Error.lean` | closed diagnostics: `PlanError` (checker), `PositionalInputError` (runtime — its `unaryDomain`/`unaryDomain32` pair are the binary64/binary32 inline-unary domain-violation payloads, `UInt64`/`UInt32` value bits respectively; `unaryNotAdmittedForStorage` is retained producer-less since the f32 slice's Task 2 made `Float32` implement inline unary math too), `CapabilityError` (syntactically-visible capability rejection), `ScanCompileError` (F4 — source-scan pairing/geometry/causality rejection, which needs inferred sizes and lowered affine maps and so cannot be decided at preflight), `NonlinCompileError` (nonlinearity thread 4 — freeNorm-marker/`Nonlin`-kind agreement rejection, raised by `Compile.lean`'s `resolveNonlinAxis`, which likewise needs the statement's whole LHS slot list and so cannot be decided at preflight), `InputSignatureError`/`InputSignatureBuildError`/`InputBindingError`/`BindingsError`/`PreparedBindingsError` (boundary — `InputSignatureBuildError` is f32 Task 4's: what a DECLARATION-AWARE signature CONSTRUCTOR can reject, `.declaration` wrapping `buildDeclEnv`'s `CompileError` or a named `.storageKindMismatch`, as distinct from `InputSignatureError`'s verdict on an already-built signature), `PlanRunCause`/`PlanRunFailure` (run-time). `PlanCompileCause`/`PlanCompileFailure` are NOT here any more — F3 moved them to `EvalPlan.lean` |
| `Check.lean` | the LOCAL checker — `checkAssign`/`CheckedAssignPlan` (per-operation invariants, including context partition/projection) and `checkScatter`/`CheckedScatterPlan` (the scatter local checker — placement-map/`destShape`/`fill`/collision validity plus the nested compute half's own `checkAssign` obligations, S-A Task 3). The graph-level `checkPlan`/`CheckedEvalPlan` are NOT here any more — F3 moved them to `EvalPlan.lean` |
| `Coordinates.lean` | shared row-major coordinate primitives — `allCoords`, `applyAffine`, `flatIndex`, `inBoundsPerDim` (extracted from `Dense.lean`, no JAX/table/source-name concepts) |
| `Dense.lean` | Dense interpreter for one checked operation, over positional `DenseTensorOf α` storage. **Carrier-parametric since the f32 slice's Task 3**, through one PRIVATE `ScalarKernelOps α` record (constant decoding, exact zero/one, fallible `ScalarBinOp` selection, a carrier-specific unary callback) instantiated as `floatOps`/`float32Ops`, one private shared traversal `denseValueAtWith ops`, and one left-associated `foldScalars` applied at three named call sites — architecture doc §2.2's factor/reduction/term folds, which used to be three separate `factorFold`/`reductionFold`/`termFold` definitions. Public doors: `runDenseAssignAt`/`runDenseAssign` (binary64, guarded `.float64`) and `runDenseAssignAt32`/`runDenseAssign32` (native binary32, guarded `.float32`); all four take CHECKED evidence, and no raw-plan-plus-arbitrary-ops entry is exported. `gatherFactorWith` applies a `ReadPlan.unary` function after the OOB zero-pad — for `Float` via the shared `UnaryOp.applyChecked` (`Eval/Error.lean`), failing loud as `PositionalInputError.unaryDomain`; for `Float32` (f32 slice Task 2) via the sibling `UnaryOp.applyChecked32`, native binary32 throughout, failing loud as `PositionalInputError.unaryDomain32` — never the binary64 helper with a widen/narrow, which would be false f32. `unaryNotAdmittedForStorage` is retained producer-less, for a future carrier with no unary implementation at all. `runDenseScatter` (S-A Task 4) is the scatter worker, Float-only: it runs the compute half's source domain through the Float `denseValueAt`, then places each computed value into the `fill`-initialized destination through the `outCoeffs`/`outBias` placement map, resolving coincident writes under the `reduce` collision policy |
| `Dense32.lean` | ONE definition: the graph-level binary32 worker `runDensePlan32` (f32 slice, Task 3), downstream of `EvalPlan.lean` because it needs `CheckedEvalPlan`. Runs `.assign` through `runDenseAssign32` and, since F32-B Task 3, `.pointwise`/`.axiswise` through `runDensePointwise32`/`runDenseAxiswise32`; `.scatter`/`.scan` evidence is Float-backed by construction and refused as `storageKindMismatch .float32 .float64` (`checkPlan` never admits either in a `.float32` graph — F32-D/F32-C). Guarded `.float32` before arity and before any input is read. Its local half deliberately stays in `Dense.lean` beside the Float siblings so the two carriers cannot drift and no second unchecked execution door exists. Reachable from the root import via `Adapter32.lean`, which is what wires it into `LeanNCD.lean` |
| `Signature.lean` | C1's shape-specialization boundary — signature-driven axis-size inference in place of concrete tensors, plus the two DECLARATION-AWARE signature constructors `InputSignature.ofDenseInputsForDecls` (binary64) and `ofDenseInputs32ForDecls` (native binary32, f32 slice Task 4). Both share `declEnvOrThrow` (the duplicate-rejecting `buildDeclEnv`, reported first as `InputSignatureBuildError.declaration`), the per-name carrier rule `checkDeclCarriers` (over `storageConstraintOfName?` — a `.predicate` declaration is precision-NEUTRAL and rides either carrier; a real declaration disagreeing with the constructor's carrier is `storageKindMismatch` naming the input), and the carrier-agnostic shape/dtype traversal `signatureOfDenseInputs` — PRIVATE, because it carries no carrier guard and at `α := Float` would hand back an `.f32` signature for `Array Float` buffers (f32 slice final-review fix wave; `SignatureTest` fixture FW3 pins it with `#check_failure`). Deliberately NOT the schedule-wide `scheduleStorageKind`, whose `.float64` default would refuse a predicate-only binary32 input map. `ofDenseInputs` (declaration-blind, always `f64`) is unchanged and has no binary32 counterpart, because `f32` is never an undeclared name's answer |
| `Prepared.lean` | source-name-keyed bindings around a checked plan — `RequiredBindings`/`checkBindings` preserves name-unique `List.Perm` required-input semantics; private-constructor `CheckedPreparedBindings` validates those slots, materialized bounds, and the exact raw-derived publication sequence. Raw plans prove slots but cannot authenticate names. `materializedSignatures` resolves only through this checked view. |
| `Adapter.lean` | named ↔ positional runtime boundary — public `pack` and `unpack` validate once then delegate to checked workers; `runPreparedDense` shares its one checked view across both. Invalid bindings precede environment/store checks; valid bindings retain existing shape, store-arity, warnings, and last-name-wins behavior. Since the f32 slice's Task 4 it also owns the CARRIER-POLYMORPHIC cores both carriers' entries are built from — `NamedDenseEnvOf α`, `packBodyOf`, `unpackBodyOf`, `runPreparedDenseOf`. They are public, so each is GUARDED at its own element type: `StorageCarrier α` (defined here; `Float` ⇒ `.float64`, `Float32` ⇒ `.float32`) names the storage kind an `Array α` buffer is, and each core's FIRST statement rejects a plan of any other kind as `storageKindMismatch`. That is three guard lines, each shared by the binary64 and binary32 entry built on that core — not six per-entry lines: the cores used to be guardless behind private per-entry helpers, and `unpackBodyOf` at `α := Float` on a `.float32` plan returned `.ok` with `Array Float` buffers under the plan's output names (final-review fix wave; `AdapterTest` fixture FW1). `pack`/`unpack`/`pack32`/`unpack32` run `checkPreparedBindings` BEFORE their core's guard; the two runners' shared guard runs before it (fixtures pin guard ORDER, not mere existence) |
| `Adapter32.lean` | the NAMED binary32 boundary (f32 slice, Task 4): `pack32`/`unpack32`/`runPreparedDense32` over `NamedDenseEnv32 = HashMap String DenseTensor32` and `EvalReport32`, each reaching a `.float32` guard (the shared core's, keyed on `StorageCarrier Float32`) before that entry's storage/arity/publication work. Adds no traversal of its own — it is `Adapter.lean`'s three cores at `α := Float32` plus `runDensePlan32`. Native buffers all the way through: there is no widen-to-binary64-then-narrow leg on this path, and `Adapter32Test`'s reduction fixture (binary32 `+0` against binary64 `1` over `[2²⁴, 1, −2²⁴]`) is what discriminates one |
| `Executable.lean` | JAX executable phase (Thread 5, extended by Boolean-output Task 4.5): `ExecutionEvidence`, kernel/plan candidates, private-constructor `JaxKernel`/`JaxExecutable` gated by real validators (`validateAffineTable`/`validateEinsum`), plus the JAX SUPPORT gate (`JaxSupportError`, `checkJaxAssignSupport`) that rejects a Boolean destination, a Boolean source, tropical max/min algebra, a unary read, and (Task 4.5 closure) a CONTEXTFUL assignment — non-empty `AssignPlan.contextShape`, which both lowerings silently rendered context-free — before any candidate or evidence exists, in the declared order destination/algebra/context/factors that mirrors `checkAssign`'s own. Every standalone validator/entry takes one explicit complete `Array TensorSignature` and re-runs the assignment checker under it — the one matching the EVIDENCE'S OWN `CheckedAssignPlan.storageKind` (`checkAssign` for `.float64`, `checkAssignF32` for `.float32`, f32 slice Task 5), not a hardcoded binary64 one. That dispatch is not a widening: the support policy still admits only `f64` destinations and reads, so binary32 is still refused — it is refused as the LOCATED `destinationDType n slot .f32` rather than collapsing into `invalidSignatureContext (dtypeNotAdmitted …)`, which would blame the caller's table for the graph's own correct carrier. Separately and at PLAN level, `validateAndConstructExecutable` refuses a non-`.float64` `PreparedPlan` outright (`unsupportedStorageKind`) as its FIRST check — ahead of the aggregation equality, ahead of `checkPreparedBindings`, and ahead of the whole-candidate predicate — because a zero-step `.float32` candidate passes all three (`aggregateEvidenceList #[]` IS `orderedReference64`) and would otherwise be handed a reference64 executable. `JaxKernel` stores that validated table and `JaxExecutableWellFormed` ties it (and each candidate's assignment) to the corresponding prepared checked step. `validateEinsum` recomputes exact operand axes, requires exact `outputAxes = term.outputPos`, and (Task 4.5 re-review) mirrors the emitter's three TERM-level preconditions via `einsumTermRenderable` — non-empty factors, iteration rank within the shared `einsumLabelLimit` (pinned against `EvalPlanCodegen.labelTable` by a `#guard` there), and complete iteration-position coverage — so certification implies `lowerAssign` renders; a factor-free assignment used to be certified and then rejected `emptyTerm`. Renderability alone is NOT sufficient (Task 4.5 re-review, second finding): every factor's source extent must equal the iteration extent of the label it is emitted with, because a zero-padded read shorter than its own iteration basis renders happily as `a->a` and returns a DIFFERENT-shaped result than Dense. That rule is the PUBLIC, located `einsumTermLabelExtents` (whole-branch review): `validateEinsum` consumes its `Bool` view and `EvalPlanCodegen.lowerAssign` calls the same function and rejects with a located `labelExtentMismatch`, so it is no longer a validator/emitter disagreement — a public lowering entry must not return a semantically unsupported einsum program either. `affineReference` still renders it (its tables carry the zero-pad mask), so the rule stays einsum-scoped. Whole-branch review round 4: `JaxExecutableWellFormed` also ties the prepared source's own `PlanBindings` to its own `raw` (`checkPreparedBindings`/`preparedBindingsTied` — required bindings a name-unique permutation of `raw.inputSlots` via the shared `checkBindings`, materialized bindings in range via the shared `materializedSignatures` path and in `prepareEvalPlan`'s fresh-slot publication order), so a materialized slot 99 or a `requiredInputs` checked against another plan's slots can no longer receive evidence; `validateAndConstructExecutable` reports that as the typed `JaxExecutableValidationError.invalidBindings` (it no longer returns bare `String`s). Which NAME belongs to which slot is deliberately NOT re-derivable here and stays unchecked — `raw` carries no names. Consumed only by `experiments/jax_bridge`, not by the production `LeanNCD` import graph (see the exception noted above) |
| `Block.lean` | checked plan-block vertical slice (F2), generalized to `BlockStep` by the nonlinearity plan's Task 3 — `BlockError`, `CheckedBlockStepEvidence`, `CheckedPlanBlock`/`checkPlanBlock`, `runDenseBlock`; reuses `checkAssign`/`checkPointwise`/`checkAxiswise` and `runDenseAssignAt`/`runDensePointwise`/`runDenseAxiswise` per step, plus the shared `checkStepGraph` wiring loop, not a second local-graph implementation. One obligation is local to this file and has no outer-graph analogue: a `.pointwise`/`.axiswise` step's source must be a PRECEDING `.assign` step's destination (`nonlinearSourceNotLocalAssignment`) — that is what keeps `Scan.lean`'s assignment-only causality walk complete |
| `Nonlin.lean` | checked nonlinearity IR (nonlinearity thread 4) — `RawPointwisePlan`/`RawAxiswisePlan`, closed `NonlinPlanError`, shared geometry-check helper `checkNonlinIO` (case×class table rows 1-7), `checkPointwise`/`checkAxiswise` built on it (row 8 added by the latter), and dense workers `runDensePointwise`/`runDenseAxiswise`, which delegate all per-function math to `Eval/Nonlin.lean`'s `PointwiseFn.apply`/`AxiswiseFn.applyCore`. **Both carriers since F32-B Task 3**, on `CheckedAssignPlan`'s pattern: `CheckedPointwisePlan`/`CheckedAxiswisePlan` record the `storageKind` they were checked for (private constructors); one private core per checker (`checkNonlinIOCore kind`, admitting exactly `nonlinDtypeFor kind`) backs `checkPointwise`/`checkAxiswise` (`.float64`, unchanged behavior; public `checkNonlinIO` is the `.float64` core) and the siblings `checkPointwiseF32`/`checkAxiswiseF32` (`.float32`); the binary32 workers `runDensePointwise32`/`runDenseAxiswise32` apply `PointwiseFn.apply32`/`AxiswiseFn.applyCore32` natively. All four workers check the evidence's storage kind as their FIRST statement, before the store is looked at (`storageKindMismatch`, not `missingSlot`), and share one generic source validation and one mask helper — no second local-operation representation (unlike `Kernel.lean`'s `AssignPlan`, these steps carry no term/factor/reduction structure at all) |
| `RawStep.lean` | checked scan graph, Task 1 (F3); extended by nonlinearity thread 4's Task 2 and again by the nonlinearity plan's Task 3 — raw scan/local-block vocabulary: `BlockStep` (`.assign`/`.pointwise`/`.axiswise`, the element type of a local block, with `sourceSlots`/`destinationSlots`/`contextShape?`/`assign?` accessors), `RawPlanBlock` (its `steps` field holds those; relocated here from `Block.lean` so `Graph.lean` can reference a scan node without a circular import), `RawScanPlan`, `PlanStep` (`.assign`/`.scatter`/`.scan`/`.pointwise`/`.axiswise`, the OUTER graph's node type — deliberately a separate sum from `BlockStep`, which has neither a `.scan` nor a `.scatter` case; `.scatter` was added by the S-A plan's Task 1) |
| `Scan.lean` | checked scan graph, Tasks 2-3 (F3), extended by S-B — write-geometry classifier (`WriteRowKind`/`writeRowKinds`, including positive `.strided` rows), collision/coverage checks (`baseWriteRowsOk`/`stepWriteRowsOk`/`writesCollide`), shared row-extent agreement (`outputRowExtentsAgree`, using `scatterDestExtent` for `.strided` and identity placement for `.free`), pinned-literal range agreement (`pinnedLiteralsInRange`), the causality certificate (`stateReadCausal`), `checkScanPlan`/`CheckedScanPlan`, and the dense worker `runDenseScan` (mixed-radix coordinate enumeration + `commitWrite`). `.strided` is admitted only at non-advancing state dimensions; equal-scale distinct residues can prove base writes disjoint. Whole-branch review: `checkScanPlan` also requires an ADMITTED dtype for every state destination (`stateDtypeNotAdmitted`) and every capture's block-local input signature (`captureDtypeNotAdmitted`) — both are positions no `checkAssign` sees, and both cross-checks that compare them (`writeDtypeMismatch`, `captureSignatureMismatch`) are equality checks a matching pair of `f32`s satisfies; and `CheckedScanPlan` now STORES the signature table it was validated against, which `runDenseScan` runs from while requiring the caller's argument to equal it exactly (`PositionalInputError.signatureContextMismatch`) — checking under a `#[2]`-shaped state and running under a `#[1]`-shaped table used to return `.ok` with an `Array.set!` panic. The outer STORE's length is tied to that same stored table too (`PositionalInputError.storeArityMismatch`, exact equality, checked after the signature tie and before anything is allocated, read, or committed) — a store shorter than the table sent the destination loop's `Array.set!` out of range, which returns the store UNCHANGED, so the run reported `.ok` with the state simply absent |
| `EvalPlan.lean` | checked scan graph, Task 4 (F3) — outer-graph `checkPlan`/`CheckedEvalPlan`/`runDensePlan`, generalized from `AssignPlan`-only steps to `PlanStep`, dispatching `checkAssign`/`checkScatter`/`checkScanPlan`/`checkPointwise`/`checkAxiswise` per node without re-deriving any of their obligations (the `.assign`/`.pointwise`/`.axiswise` arms by the graph's storage kind — `checkAssignF32`/`checkPointwiseF32`/`checkAxiswiseF32` in a `.float32` graph, whose capability pass, over the original step indices, refuses only `.scatter`/`.scan` as `f32UnsupportedStep`), and `runDenseAssign`/`runDenseScatter`/`runDenseScan`/`runDensePointwise`/`runDenseAxiswise` likewise; `CheckedPlanStepEvidence` is the per-step evidence sum (`.assign`/`.scatter`/`.scan`/`.pointwise`/`.axiswise`), whose `.scatter` arm carries a `CheckedScatterPlan` and deliberately NOT the compute half's `CheckedAssignPlan` (S-A Task 2). A `checkScatter` failure surfaces as `PlanStepError.assign (.nodeError ni e)` — that constructor names the error's SHAPE (a plain `PlanError`), not the step's kind, unlike `.scan`/`.nonlin`. Also hosts `PlanCompileCause`/`PlanCompileFailure` (relocated from `Error.lean`, same acyclic-import constraint as `RawPlanBlock`'s move; F4 added the `scan` arm carrying `ScanCompileError`) |

### Key Relationships
`Entry.lean` imports `DSL.Compile`; `Eval.lean` does not. `Slots.lean`/`Gather.lean` import
`DSL.Ast`. The old
`Shape.lean` (axis-size inference + output-shape formulas, 475 lines) was split (Wave E, 4e) along
its real dependency boundaries: `Slots.lean` contains shared LHS-slot helpers and depends only on
`DSL.Ast`; independently, `SizeSolve.lean` imports `Tensor`/`Exec.Uid` and owns the pure affine
constraint solver with no notion of a `Stmt` or read position; `SizeInfer.lean` imports
`SizeSolve`/`Tensor`/`DSL.Ast`, builds constraints from concrete tensor shapes and statements, and
drives the solver to a fixpoint. `Shape.lean` is now a small compatibility umbrella importing all three
— nothing besides that umbrella's own doc comment lives there. Production modules use the narrow
module they actually need instead of the umbrella: `Nonlin.lean` imports `Slots.lean` (for
`normAxisUidOf`, since Wave B's `resolveNonlin`); `Scan.lean` imports `Contract`, `Nonlin`, and
`Slots.lean` (for `outputShape`, its state-allocation formula) plus `DSL.Pipeline.Types`;
`Contract.lean` imports `Gather` and `DSL.TraverseAxes` — it does not need any shape/size-solver
symbol at all; `Eval.lean` imports `Scan`, `Scatter`, and `SizeInfer.lean` directly (for
`inferAxisSizes`, called once from `evalScheduled`). `Entry.lean` then joins that worker with
`DSL.Compile` to define the source-program API. The import graph is
branched rather than linear: `DSL.Ast → Slots → Nonlin/Scan`; `Tensor → Gather → Contract`;
`Tensor + Exec.Uid → SizeSolve → SizeInfer`; and `Contract + Nonlin + Slots → Scan`, while
`Contract → Scatter`; `Eval` joins `Scan`, `Scatter`, and `SizeInfer`; and `Entry` joins `Eval`
with `DSL.Compile`. `LHSSlot.outExtent`
(defined in `../DSL/Ast.lean`, not here) is the single shared
scatter-extent formula both `Eval.scatterOutShape` and `SizeInfer.scatterOutputShapes` call.

`Error.lean` (Wave E, 4h) is a LEAF of this graph: it imports only `Exec.Uid`/`DSL.Ast`, never
anything under `Eval/`, so every other file here imports it (directly, per the "explicit import"
convention adopted in 4h — not just transitively through, say, `Contract`) rather than the reverse.
`SolveFailureKind`/`SolveDiagnostic`/`remediationOfDiagnostic`/`renderSolveDiagnostic` moved here
from `SizeSolve.lean` (now public — `SizeSolve.lean` still CONSTRUCTS a `SolveDiagnostic` at each
of its four failure points, but `Error.lean` is the only place one is ever rendered). `Tensor.lean`
no longer defines `EvalError` (it was `abbrev EvalError := String` pre-4h) — `Tensor.lean` stays
independent of error representation entirely, and `EvalError` now lives solely in `Error.lean`.

## Public API

### Key Exports

**Task 4.6 update:** `evalScheduled` and `prepareEvalPlan` both call the neutral
`Pipeline/ScheduledValidation.validateScheduled` boundary. It owns duplicate-safe declarations,
all source/destination rank checks, LHS axis-kind checks, predicate-output checks, producer order,
declaration-derived sizes, and ordered external names; neither boundary trusts the cached schedule
fields.

| Export | Used By | Change Impact |
|---|---|---|
| `TLProgram.eval` (`Entry.lean`) | diagnostic-aware callers | primary source entry; returns `Except EvalFailure EvalReport`, preserving warnings on success and failure |
| `evalScheduled` (`Eval.lean`) | `Entry.lean`, scheduled-program callers | compiler-independent worker; returns the same success/failure report pair as the source entry. Whole-branch review: it re-runs the shared `buildDeclEnv` over `sched.decls` FIRST, so a hand-built schedule declaring one tensor-bearing name twice is `EvalError.compile (.duplicateTensorDecl …)` rather than being evaluated under whichever kind `combineFor`'s first-match scan happens to pick — the same `CompileError` `prepareEvalPlan` reports as `sourceInvariant`. An `.axis` sharing a predicate's name is a different namespace and stays legal. Its size-inference seed is likewise re-derived (`declaredAxisSizes sched.decls`, not `sched.explicitSizes`) — the same rule `prepareEvalPlan` applies, so a stale cached map cannot make the two backends disagree. It also enforces the shared read/destination-rank and dtype invariants over every scheduled assignment (`checkScheduledReadRanks`/`checkScheduledDtypes`, both using the same `.plain`/scan-`base ++ recur` traversal). Thus malformed iteration/normalization axes report `iterAxisNotNat`/`normAxisNotReal` instead of executing, and invalid predicate output semantics remain compile errors. Order is the source pipeline's own: `buildDeclEnv`, all rank checks, then each statement's axis kinds before its predicate rules, followed by topology, size inference, and execution. |
| `DenseTensorOf α { shape; data }` (`Tensor.lean`) | every file here, through its aliases | invariant `data.size = ∏ shape` — no runtime check, breaking it silently breaks `get!`/`set!`/`ofFn`. `DenseTensor := DenseTensorOf Float` and `DenseTensor32 := DenseTensorOf Float32`. Only the carrier SHELL is generic; every helper beside it (`zeros`/`get!`/`set!`/`ofFn`/`approxEq`) stays binary64. Because turning a structure into an alias synthesizes none of its generated names, `DenseTensor.mk` is preserved as an abbreviation and `DenseTensor.shape`/`DenseTensor.data` as definitions with an explicitly-typed `DenseTensor` parameter (a bare abbreviation of a generic projection does NOT work through field notation) — `Eval.TensorTest`'s fixture 15 pins all three, and deleting one breaks `KernelDenseTest`/`GraphDenseTest`/`NonlinDenseTest`/`Portfolio.ScatterNonlinRejectTest` |
| `evalAssignDtypedSeeded`/`Combine` (`Contract.lean`) | `evalPlain` (via `evalAssignDtyped`, its empty-seed wrapper) AND `Scan.evalStmtSliceSeeded` | dtype→semiring dispatch (real/bool/tropical), now shared by plain and scan assignment — before Wave B (4c), the scan path matched `rhs.agg` manually and could never select `Combine.bool` for a predicate state; new dtype needs a new `Combine` + `combineFor` arm |
| `inferAxisSizes` (`SizeInfer.lean`, re-exported by `Shape.lean`) | `evalScheduled` | central sizing fixpoint; returns `Except EvalFailure (sizes × warnings)`, preserving warnings even if a later inference check fails |
| `evalScan` (`Scan.lean`) | `evalScheduled` | multi-axis scan driver — `axes` is a general `List AxisSpec`, not 1-D |
| `EvalError`/`ShapeError`/`EvalWarning` (`Error.lean`) | every worker's `Except EvalError _`; every typed test assertion | closed, layered diagnostic types (Wave E, 4h) — adding a genuinely new failure mode means adding a constructor here, not composing a new ad-hoc string; every existing `ToString` output is still byte-identical to the pre-4h flat messages |


### Core Types
`DenseTensorOf α { shape : List Nat; data : Array α }` — the only runtime value type, with
`DenseTensor := DenseTensorOf Float` (the reference evaluator's and every Float worker's carrier) and
`DenseTensor32 := DenseTensorOf Float32` (the binary32 worker's, f32 slice Task 3).
`EvalReportOf α { env : HashMap String (DenseTensorOf α); warnings : List EvalWarning }`
(`Eval/Report.lean`), with `EvalReport := EvalReportOf Float` — the successful result of either entry
path; `env` retains inputs plus computed tensors exactly as before 4i — and
`EvalReport32 := EvalReportOf Float32` (f32 slice Task 4, returned by `runPreparedDense32`). The
shell was parameterized the same way and for the same reason `DenseTensorOf` was; `EvalWarning` is
deliberately NOT parameterized (a sizing diagnostic is a statement about shapes, identical in both
precisions). `EvalReport.mk`/`.env`/`.warnings` survive as an explicit compatibility shim — an
`abbrev` alone does not synthesize a structure's generated names, and a bare `abbrev` of a generic
projection is not usable as a standalone function value (`AdapterTest`'s fixture 11 pins all three). `EvalFailure { error : EvalError; warnings : List EvalWarning }` (`Error.lean`) preserves
warnings inferred before a later inference or worker failure; only compile failures necessarily
carry `[]` because inference never ran. `EvalError` (`Error.lean`) — a closed, layered inductive (not
`abbrev EvalError := String` any more, as of Wave E 4h); `.compile`/`.shape` nest already-typed
causes (`CompileError`/`ShapeError`), the rest are closed constructors mapped 1:1 from every real
throw site found in an exhaustive 4h inventory. Tests match on constructors where it strengthens
the assertion (`AffineShapeSolverTest`'s solver-diagnostic blocks, `ContractTest`'s seed check,
`NonlinTest`, `ScanTest`, `ShapeTest`'s conflict test, `WaveBRegressionTest`,
`Portfolio/ScatterNonlinRejectTest`) or fall back to `toString e`/`toString w` for legacy renderer
checks and cases where "some error/warning fired" is the whole point.

## Contracts
- **Checked-plan `ScalarDType.bool` is a SEMANTIC ALGEBRA/SIGNATURE TAG over the graph's REAL
  carrier, never a native carrier of its own** (Task 4, `papers/boolean_predicate_output_evalplan.md`;
  generalized from "over Float storage" by the f32 slice's Task 3). Each carrier's own
  `ScalarKernelOps.decodeConst` (`Dense.lean`) decodes `.bool true`/`.bool false` to THAT carrier's
  exact one/zero — `1.0`/`0.0` for `Float`, `Float32.ofBits 0x3f800000`/`0x00000000` for `Float32` —
  and that carrier's own `min`/`max` run, in the same buffer as the graph's real tensors. Which real
  carrier a graph selects is `deriveStorageKind`'s answer over the whole signature table, in which
  `bool` contributes no constraint. Consequences that are easy to assume wrong:
  (a) **the DESTINATION selects the algebra** — `admittedAlgebrasFor` gives real sum-product plus the
  two tropical semirings to `f64`, Boolean min/max (`admittedAlgebraBool`) to `bool`, and nothing to
  `f32`; (b) **source/destination dtype equality is deliberately NOT an assignment obligation** — a
  `bool` source may feed an `f64` destination and vice versa, since gathering is dtype-blind, and
  `PlanError.dtypeMismatch` is retained producer-less as a result; (c) **runtime values are NOT
  restricted to `0.0`/`1.0`** — a non-binary Float keeps literal `min`/`max` behavior, matching the
  reference evaluator; adding a truth check would create a checked/reference divergence; (d)
  **declarations are authoritative** — `buildDeclEnv` rejects a repeated tensor-bearing name and an
  explicit input signature contradicting a declaration is rejected
  (`InputSignatureError.dtypeMismatch`), never rewritten; (e) `f32` stays rejected everywhere ON THE
  BINARY64 PATH — `admittedAlgebrasFor .f32` is empty, `dtypeAdmitted .f32` is false, and every Float
  worker/adapter door refuses `.float32` evidence — but it is no longer rejected everywhere full
  stop: the f32 slice gave it its own checker (`checkAssignF32`), its own algebra table
  (`admittedAlgebrasForF32`), and its own native workers (`runDenseAssignAt32`/`runDenseAssign32`/
  `runDensePlan32`). The two paths never meet; the storage kind recorded on checked evidence is what
  keeps them apart.
- **`scatterOutShape`/`scatterOutputShapes`/checked scan row extents MUST equal `LHSSlot.outExtent`** (`../DSL/Ast.lean`) — the sole stride-aligned formula. `Eval.scatterOutShape` and `SizeInfer.scatterOutputShapes` call it directly; checked scan geometry reaches it through `scatterDestExtent`. For one normalized positive coefficient `c`, nonnegative bias `b`, and source extent `n > 0`, the extent is `c*n + (b/c)*c`; all other forms retain the legacy linear fallback. History: an earlier duplicate upper-envelope formula disagreed with evaluator materialization and produced an unsound cropped read (fix `fc10d70`). **Do not add a second extent formula.**
- **The write-geometry surface MUST stay exhaustive over `WriteRowKind`** (`Plan/Scan.lean`, `Plan/Compile.lean`, and `test/Eval/Plan/ScanTest.lean`'s frozen oracle). S-B added `.strided outputPos scale offset` and deliberately discharged all **nine sites**: six in `Scan.lean`, one in `Compile.lean`, and two in the test oracle. No wildcard belongs at any site. The tripwire forces an explicit decision but cannot prove that decision sound, so each new kind still needs classifier witnesses, the complete phase×dimension case table, extent checks, collision evidence, and mutations. Current `.strided` rules: positive scale/nonnegative bias, ordered output cover like `.free`, shared `scatterDestExtent` equality, non-advancing dimensions only, and equal-scale/different-residue disjointness for base writes.
- **Fail-loud unsized axis**: `evalAssignSeeded` (the sole contraction implementation —
  `evalAssignWith` is its empty-seed wrapper) throws before building an output shape if any
  non-seeded free output axis, any per-term contracted axis, or any seeded axis has no inferable
  size, and rejects an out-of-range seed coordinate. Mirrored in `Eval.scatterOutShape`,
  `Scatter.evalScatter`, and `Scan.evalScan`. ⚠️ `Scan.evalScan` was **missing from this list, and
  that omission WAS the bug** (audit finding #5, fixed 2026-07-30): it used
  `(sizes[u]?).getD 0`, conflating "no extent" with "extent 0", which made `List.range (L-1)` run
  zero recurrence steps *and* drove an unchecked `Array.set!` — so a plain surface program with no
  `axis l` pin **panicked** with "index out of bounds" instead of returning an error. A second,
  narrower gap closed 2026-07-31 (Wave B, 4a): `evalAssignSeeded` had no check for a missing
  per-term contracted-axis size (silently contracted at extent one) or a missing seeded-axis size
  (silently produced a shape-`[0]` tensor). Keep all four call sites in this list: the gap was
  visible by reading it. Each of these five sites is now one `ShapeError.unsizedAxis uid site`
  constructor with a distinct `UnsizedAxisSite` tag (4h) — same five call sites, same five rendered
  messages, byte-for-byte.
- **Non-identity scatter is rejected, not silently dropped**: `Scatter.evalScatter` throws if `rhs.nonlin ≠ .identity` (defensive re-check; the primary gate is `checkScatterNonlin` in `../DSL/Pipeline/Structural.lean`, see that dir's AGENTS.md). Fixes the bug where `Out[2*i] := relu(X[i])` used to compile and silently drop the `relu`.
- **Per-term contraction scoping**: each `+`-joined RHS term is contracted over only the axes *that term* mentions (`termAxisUIDs`), not the union across the whole equation.
- **`readAxisUIDs` excludes nonlin-mask axes** — must stay `traverseAxesNoMask`, not the with-mask variant, or shape inference gets corrupted by mask-only UIDs.
- **RREF solver floor-then-verify convention** (`SizeSolve.lean`, driven by `SizeInfer.inferAxisSizes`): builds an upper-envelope affine constraint per unsized read position, reduces to RREF over `Rat`, floors any fractional solution (padded/stride semantics), then re-verifies the floored solution against every original constraint. Typed failure kinds (`inconsistent`/`underdetermined`/`nonIntegral`/`nonPositive`) with remediation hints — `SolveFailureKind`/`SolveDiagnostic` and the renderer/remediation helpers live in `Error.lean` as of 4h (`SizeSolve.lean` only constructs a `SolveDiagnostic` and wraps/throws it as `EvalError.shape (.solveFailure _)`; it never renders one).
- **`Combine`'s factor-product fold starts from `unit1`, never a literal `1.0`** — `unit1` is the
  multiplicative identity of one term's factor product, distinct from `unit0` (the identity of
  the outer term-aggregation fold). All four current `Combine` values (`real`/`bool`/`max`/`min`)
  happen to use ordinary multiplication, so `unit1 = 1.0` for each, but a future `Combine` whose
  `mul` is not ordinary multiplication (e.g. a min-plus/tropical semiring) depends on this field
  being threaded correctly rather than assumed.
- **`evalScatter`'s RHS value computation routes through the same `Combine` record `Contract.lean`
  uses, selected by `rhs.agg`** — not a separate hardcoded real sum-of-products. Before Wave C
  (4g), `rhs.agg` was never read inside `Scatter.lean` at all, so a `maxreduce`/`minreduce` scatter
  RHS silently computed a real sum instead of the declared tropical max/min.
- **`ScatterOpts.reduce` is a closed `CollisionReduce`, not a string** — `rejectCollisions`
  (default), `overwrite`, `sum`, `max`, `min`. Before Wave C (4g) it was `Option String` matched
  against only `"sum"`/`"max"`; an unrecognized string (or the never-implemented `"min"`) silently
  fell through to overwrite. The default changed from implicit-overwrite (`none`) to
  `rejectCollisions`, confirmed safe by running the full test suite — no surface-compiled scatter
  pattern in this codebase ever collides (`DSL/Pipeline/Structural.lean`'s `lowerArith` already
  rejects any surface-detectable collision independently, via `overlappingScatter`). Reaching
  `.overwrite`/`.sum`/`.max`/`.min` still requires the programmatic escape hatch (direct
  `Stmt.scatter` construction) — no surface DSL syntax sets this field to anything but the
  default.
- **`EvalError`/`ShapeError`/`EvalWarning` are closed, layered inductives with exactly one renderer
  each (`Error.lean`, Wave E 4h)** — every constructor traces to a real pre-4h throw site (an
  exhaustive inventory was taken before conversion; there is no generic `unsupported String`
  escape hatch and no speculative constructor added ahead of a second real caller). `.compile`/
  `.shape` nest an already-typed cause rather than flattening it. Every `ToString` instance
  reproduces its pre-4h flat message byte-for-byte — this is the behavior-preservation contract
  the whole conversion depends on, checked by running every test that used to grep the old string.
- **Warnings are outcome data, never trace output** (`Eval.lean`, Wave E 4i) —
  `inferAxisSizes`'s structured warning list is returned unchanged through `evalScheduled` and
  `TLProgram.eval`: successful execution carries it in `EvalReport`, while a later inference or
  worker failure carries it beside the fatal `EvalError` in `EvalFailure`. No output-only
  projection exists: callers that need tensors inspect `EvalReport.env` after handling the
  complete outcome. Do not reintroduce `dbg_trace` or make the source entry return only an
  environment/error.

## Patterns
The Portfolio suite (`test/Eval/Portfolio/`, shared `Harness.lean`) is a broad library of worked model fragments, one file per model family (LinAlg/Feedforward/Attention/ConvPool/Norm/Recurrence/GnnScatter/Relational/StatsLoss/Tropical/TensorNet/Generative/ClassicalML/EdgeCase). Three test styles (see `docs/test_portfolio.md`): **[N] numeric** (`assertEval`/`assertShape`, compare against a hand-computed tensor or property), **[R]/[F] runtime/compile failure** (`assertEvalError`/`assertCompileError`, checks the error string/constructor), and pure parse-errors (documented as comments only — `tlprog!` fails during elaboration, before any assertion machinery runs). `RejectTest.lean`/`ScatterNonlinRejectTest.lean` hold adversarial cases pinned to a specific error so a regression that turns a reject into a silent success is caught. `KnownGapTest.lean` is pure documentation — a triage taxonomy of DSL expressiveness gaps (rejecting/parse-level/missing-primitive/confirmed-non-gaps), not live assertions.

## Entry Points
| Task | Start Here |
|------|------------|
| Evaluate source while preserving warnings | `Entry.lean` — `TLProgram.eval` |
| Evaluate an existing schedule without importing the compiler | `Eval.lean` — `evalScheduled` |
| Run a checked plan (Wave C/F) | `Plan/Compile.lean` — `prepareEvalPlan`; `Plan/Adapter.lean` — `runPreparedDense` |
| Run a checked BINARY32 plan by name (f32 slice) | `Plan/Signature.lean` — `InputSignature.ofDenseInputs32ForDecls` over `DenseTensor32` inputs; `Plan/Compile.lean` — `prepareEvalPlan`; `Plan/Adapter32.lean` — `runPreparedDense32`. As of F32-B Tasks 2-4, this covers pointwise/axiswise nonlinearities and inline unary read factors, not merely the plain-identity fragment Task 1 shipped — `prepareEvalPlan`'s Step D emits the destination's own dtype/algebra for a nonlinear statement's two-step chain exactly as it does for `.identity`. Choosing the Float entry for a `.float32` plan (or vice versa) is a fail-loud `storageKindMismatch` at every door, never a conversion |
| Understand why a source scan was rejected | Match the `PlanCompileCause` constructor: `.capability` = syntactically visible (preflight, no sizes needed), `.scan` = `ScanCompileError` from `compileScan` (needs sizes/affine maps), `.invalidPlan` = `checkScanPlan` rejected COMPILER output, which is a compiler bug, not a source problem, `.nonlin` = `NonlinCompileError` from `resolveNonlinAxis` (freeNorm-marker/`Nonlin`-kind agreement, nonlinearity thread 4 — needs the statement's whole LHS slot list, so it cannot be decided at preflight either). Fixtures: `test/Eval/Plan/ScanCompileTest.lean` (`.capability`/`.scan`/`.invalidPlan`), `test/Eval/Plan/NonlinCompileTest.lean` (`.nonlin`) |
| Check that a compiled scan still MATCHES both references | `test/Eval/Plan/DifferentialTest.lean`'s `scanParityCheck` compares the checked plan, legacy evaluator, and independent scan-free oracle with pair-specific diagnostics, exact environment key/shape/value equality, warning-list equality for the reporting legs, unchanged inputs, and scratch privacy. The generated scan corpus stays 17; S-B adds a separate seven-program source corpus covering strided base/step writes, interleaving, contraction-before-placement, non-trailing advancement, two affine dimensions, and two scans with one S-B node. |
| Check a compiled scan against something that is NOT either evaluator | `test/Eval/PropertyOracle/ScanUnroll.lean`'s `independentRun` mechanically rewrites a scan into a scan-free leaf program, evaluates it through the ordinary assignment evaluator, and reconstructs histories independently. It calls no checked geometry, compiler residualization, or scan-worker placement helper. `ScanOracle.lean` retains the 17-case generated two-way sweep and separately compares its five hand-built S-B isolation cases against the legacy evaluator; `DifferentialTest.lean` supplies the seven source-generated three-way gate. |
| Understand why a source scatter was rejected | An affine or diagonal LHS is reclassified into a `Stmt.scatter` by `Compile.lean`'s `lowerArith`. Top-level restrictions remain: constant-affine and multi-axis placements, non-default collision policy, nonlinear placement, and predicate destinations fail at capability tier. Inside a scan, the admitted S-B subset is positive one-axis affine placement with nonnegative bias in non-advancing state dimensions, zero fill/reject collisions, identity nonlinearity, and consistent state extent. Context-affine, scratch-scatter, overlap, sign, and extent failures are typed `ScanCompileError`s. |
| Check that a compiled scatter still MATCHES the legacy evaluator | `test/Eval/Plan/DifferentialTest.lean` has two separate source-generated corpora: `scatterPrograms` (**9** top-level S-A cases) and `scanScatterPrograms` (**7** S-B cases, three-way with the independent oracle). The generated 3,832-case scan-free corpus and 17-case scan corpus remain unchanged. |
| Add a new nonlinearity | Legacy evaluator: `Nonlin.lean` — add a `PointwiseFn`/`Nonlin.axiswise` arm (`applyNonlin` needs no new case: it dispatches on the resolved `identity`/`pointwise`/`axiswise` SHAPE, not per function, so it already covers any new `PointwiseFn`/`AxiswiseFn` value), and (for an axiswise fn) confirm `resolveNonlin`'s existing marker check covers it — do not add a second marker-lookup site in `Eval.lean`/`Scan.lean`. <br> Plan layer (nonlinearity thread 4): its own new constructor in `DSL/Ast.lean`'s `PointwiseFn`/`AxiswiseFn`, one `pointwiseWith`/`axiswiseRowWith` arm in `Eval/Nonlin.lean` (the single formula both carriers share — not a `*T` body), any new constant added to **both** `floatNonlinOps` and `float32NonlinOps` (the binary32 one as an exact bit pattern), and a new fixture in each of `NonlinTest`/`Nonlin32Test` — nothing in `Plan/Nonlin.lean` changes, since its checker (`checkNonlinIO`) and dense workers are fully function-agnostic |
| Add a new dtype/semiring | `Contract.lean` — new `Combine.*` + `combineFor` arm. For a new CARRIER (not a semiring over an existing one) that is only the legacy-evaluator half: follow the f32 slice's shape instead — `DSL/Ast.lean`'s `TensorElementType`, `Plan/Check.lean`'s `checkAssignCore` `kind` parameter and algebra table, `Plan/Dense.lean`'s `ScalarKernelOps` instance, a graph worker beside `Dense32.lean`, a `StorageCarrier` instance (`Plan/Adapter.lean`) plus a named boundary beside `Adapter32.lean`, and a storage-kind guard at **every** door in the §3.5 table of `papers/f32_evalplan.md` |
| Understand why the LEGACY evaluator refused an `f32` program | It is **permanent, not a temporary stop.** Every worker under `Eval/` computes in binary64 `Float`, so a tensor an explicit `tensor f32` declaration commits to binary32 has no correct reading here — homogeneous or mixed alike. `evalScheduled` (`Eval.lean`) asks `scheduleFloat32Name?` for the FIRST used f32 name and reports `EvalError.unsupportedDtype nm` before size inference, the environment, or any statement runs; the four lower entries that do not route through it (`evalAssignDtypedSeeded` in `Contract.lean`, `evalPlain` in `Eval.lean`, `evalStmtSliceSeeded`/`evalScan` in `Scan.lean`) each carry their own `rejectUnsupportedStorage` guard at their own ENTRY — deliberately not left to the assignment arm's deeper one, because the `.scatter` and scan arms reach shape/nonlinearity failures first and would misreport the dtype refusal. Consequence for differential testing: **there is no legacy oracle for any f32 program**, which is why binary32 fixtures assert exact `Float32.toBits` values instead |
| Debug an axis-sizing failure | `SizeInfer.inferAxisSizes` — match the `ShapeError`/`SolveDiagnostic` constructor (`Error.lean`) directly, or `toString` it for the legacy flat message |
| Debug a scatter shape mismatch | Confirm `LHSSlot.outExtent` is the sole formula both call sites use |
| Add a portfolio test case | `test/Eval/Portfolio/<Family>Test.lean` + `Harness.lean` asserters |
| Run checked plans against JAX | `experiments/jax_bridge/run-evalplan-affine.sh` (20 curated boundary fixtures) and `run-evalplan-affine-corpus.sh` (all 3,832 `PropertyOracle.enumPrograms`, every output eager + first JIT representative per feature mask). The corpus currently has 45 masks; generated cases supply graph/combinatorial features while curated fixtures supply negative invalidity, zero coefficients/extents, and empty factors/terms. |

## Pitfalls
- **The checked backend executes Boolean/tropical/unary/CONTEXTFUL semantics; the experimental JAX
  backend REJECTS them** — `Plan/Executable.lean`'s `checkJaxAssignSupport` fails loud (located,
  typed) on a Boolean destination, a Boolean source, `admittedAlgebraMax`/`Min`, a `ReadPlan.unary`
  read, or a non-empty `AssignPlan.contextShape` before any Python, candidate, or
  `ExecutionEvidence` exists. Do not read "Boolean outputs are admitted" as "JAX runs Boolean plans"
  — there is no JAX Boolean execution. **JAX assignment kernels support only CONTEXT-FREE
  assignments**: a contextful assignment denotes a family of results indexed by a runtime context
  coordinate, and neither lowering has a parameter for it — `einsumOnly` used to contract the
  context position away as an ordinary label (`Y[] := X[l]` → `a->`) and `affineReference` emitted no
  `context_pos` key, both stamped with evidence. Reachable only through the standalone
  `CheckedAssignPlan` entries; `checkPlan` already refuses a contextful top-level step
  (`topLevelContextNotEmpty`). **A `.scatter` step is refused CATEGORICALLY, and there is
  deliberately no `checkJaxScatterSupport` to call** — `checkJaxAssignSupport` grades one
  assignment's semantics, but a scatter's placement map, `fill`, and collision policy have no
  representation in either lowering, so whether its compute half would pass is irrelevant. It joins
  `.scan`/`.pointwise`/`.axiswise` in `EvalPlanCodegen.lean`'s three `unsupportedStep` buckets; in
  the DEFAULT target the enforcing gate is `JaxExecutableWellFormed`'s per-step tie, which admits
  only an `.assign` step at a kernel's index — so validating a kernel from `s.compute` and
  presenting it as that step fails loud instead of collecting `orderedReference64`
  (`ExecutableTest.lean`'s scatter pair, with an `.assign` control over the same kernel).
  **The JAX backend is also BINARY64-ONLY, and its f32 gate is PLAN-level, not per-node** (f32 slice
  Tasks 2 and 5) — its fixtures and Python runtimes encode `UInt64` bits and assert
  `np.float64`/`jnp.float64`, and there is no binary32 evidence label at all (slice F32-JAX). All
  eight candidate/generator/renderer doors refuse a `.float32` `CheckedEvalPlan` FIRST:
  `lowerCheckPlanToCandidate`, `lowerPlan`, `generateForward`, `generateNamed`,
  `renderAffinePlanPositional`, `renderAffinePlanNamed`, and `renderInputConstants` (the seven in
  `EvalPlanCodegen.lean`, all through the one shared `requireFloat64Plan`), plus
  `validateAndConstructExecutable` here. The per-node support check CANNOT stand in for this: an
  all-input, ZERO-STEP f32 plan has no node to visit, every per-step obligation is vacuous, and
  `aggregateEvidenceList #[]` is `orderedReference64` — so without the plan-level gate such a
  candidate acquires a reference64 claim about a plan carrying no binary64 protection at all. Adding
  a ninth entry point means adding a ninth `requireFloat64Plan` call; the guard is expressed in
  STORAGE-KIND terms rather than as an f32 special case so a future complex plan meets the same
  fail-loud boundary.
- **scatterOutDim/scatterOutShape drift (historical, now structurally prevented)** — see Contracts. If a second scatter-extent formula is ever reintroduced, the drift bug returns silently.
- **Scan is genuinely n-D now** — `Scan.evalScan`'s `axes` drives a cartesian-product over every advancing axis; code assuming 1-D scan structure will misbehave on a 2-D recurrence.
- **An unsized scan iteration axis is an error naming its own fix** — `Scan.evalScan` reports "unsized iteration axis 'l' (uid N) — pin it with ``axis l : ℕ = N``, or ensure some read fixes its extent". One adjacent case is deliberately NOT covered: an axis pinned explicitly to `0` still yields `L = 0` (a stated intent, not a sizing gap). A second case, `axis l : ℕ[3]` pinning nothing at all, USED to be a live trap here (the kind-carried size was write-only) — audit finding H fixed it 2026-07-30 by deleting the payload from `AxisKind` itself, so `ℕ[3]` no longer parses as an axis kind at all (see `../DSL/AGENTS.md`).
- **Out-of-range reads are `.ok 0.0`, not `.error`** (`Gather.gatherRead`) — only genuine domain violations and unknown-tensor/unsized-axis conditions raise `EvalError`. Don't conflate "padded zero" with "failure."
- **`readAxisUIDs`/`termAxisUIDs`/`freeAxisUIDs` are NOT interchangeable** (`Contract.lean`) — `freeAxisUIDs` must return a subset (non-affine slots only); swapping these breaks shape inference or contraction scoping silently.
- **`stateShape` is confirmed gone** (deleted, "reuse outputShape") — `Scan.evalScan` allocates scan state via `Slots.outputShape` directly.
