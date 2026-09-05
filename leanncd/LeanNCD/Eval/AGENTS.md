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
| Nonlinearities (relu/sigmoid/tanh/gelu/softmax/normalize) | `Nonlin.lean` |
| Recurrence / n-D scan evaluation | `Scan.lean` |
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
`Executable.lean` (Thread 5) is NOT reachable from `import LeanNCD` — it is consumed only by
`experiments/jax_bridge` (the non-default `JaxExperiment` library), not by the production
`LeanNCD` import graph, so the blanket "reachable via `Eval.Plan.Adapter`" claim above does not
cover it.

| File | Owns |
|---|---|
| `Types.lean` | static specialization vocabulary — `ScalarDType`, `TensorSignature`, `InputSignature` |
| `Kernel.lean` | one local operation's IR — `AffineMap`, factor/term records (`ReadPlan` carries an optional `unary : Option UnaryOp` inline transcendental, applied after the OOB pad), `AssignPlan` |
| `Graph.lean` | the unchecked plan graph — `RawEvalPlan` |
| `Error.lean` | closed diagnostics: `PlanError` (checker), `PositionalInputError` (runtime), `CapabilityError` (syntactically-visible capability rejection), `ScanCompileError` (F4 — source-scan pairing/geometry/causality rejection, which needs inferred sizes and lowered affine maps and so cannot be decided at preflight), `NonlinCompileError` (nonlinearity thread 4 — freeNorm-marker/`Nonlin`-kind agreement rejection, raised by `Compile.lean`'s `resolveNonlinAxis`, which likewise needs the statement's whole LHS slot list and so cannot be decided at preflight), `InputSignatureError`/`InputBindingError`/`BindingsError` (boundary), `PlanRunCause`/`PlanRunFailure` (run-time). `PlanCompileCause`/`PlanCompileFailure` are NOT here any more — F3 moved them to `EvalPlan.lean` |
| `Check.lean` | the LOCAL checker — `checkAssign`/`CheckedAssignPlan` (per-operation invariants, including context partition/projection). The graph-level `checkPlan`/`CheckedEvalPlan` are NOT here any more — F3 moved them to `EvalPlan.lean` |
| `Coordinates.lean` | shared row-major coordinate primitives — `allCoords`, `applyAffine`, `flatIndex`, `inBoundsPerDim` (extracted from `Dense.lean`, no JAX/table/source-name concepts) |
| `Dense.lean` | Dense interpreter for one checked operation, over positional `DenseTensor` storage — `runDenseAssignAt` (context-indexed primitive, built from named folds `factorFold`/`reductionFold`/`termFold` matching architecture doc §2.2) and `runDenseAssign` (its empty-context wrapper). `gatherFactor` applies a `ReadPlan.unary` function after the OOB zero-pad via the shared `UnaryOp.applyChecked` (`Eval/Error.lean`), failing loud on a domain violation as `PositionalInputError.unaryDomain` — so `runDenseAssignAt` is `Except`-threaded |
| `Signature.lean` | C1's shape-specialization boundary — signature-driven axis-size inference in place of concrete tensors |
| `Prepared.lean` | source-name-keyed bindings around a checked plan — `PreparedPlan`; `RequiredBindings`/`checkBindings` (private-constructor, `List.Perm`-checked, name-unique `requiredInputs`); `PlanBindings.materializedWith`, the ONE materialized-binding resolution path (order and repeats preserved, an out-of-range slot is `PlanError.slotOutOfRange`, never a fabricated value), shared by the metadata accessor `PreparedPlan.materializedSignatures` and by execution (`Adapter.unpack`) so the two cannot drift |
| `Compile.lean` | the source compiler — capability preflight (C4 `capabilityPreflight`, F4 `checkScanLHSSlot`/`checkScanBlockStmt`, nonlinearity thread 4 `checkNonlinTopLevel`/`checkNonlinScanBlock`), the shared per-statement lowering core `residualizeAssignment` (used by plain, base, and step callers alike), the F4 scan specializer `compileScan` (state/scratch classification from `base`/`recur` DIRECTLY — never the scan's representative name, `ScanStmt.outputs`, or `.writes`), thread 4's axis resolver `resolveNonlinAxis` (freeNorm-marker/`Nonlin`-kind agreement), and `prepareEvalPlan` (its `.plain` branch now two-step-chains a `.pointwise`/`.axiswise` statement into an internal `.assign` that publishes no name, immediately followed by the real `.pointwise`/`.axiswise` step that publishes the statement's one materialized name). `prepareEvalPlan`'s Step 0 treats `sched.decls`/`sched.stmts` as the ONLY authority on a direct schedule: `sched.env` is re-derived by `buildDeclEnv`, `sched.extNames` by `orderedExternalNames`, and (whole-branch review) `sched.explicitSizes` by `declaredAxisSizes` — the same rule `schedule` used to build it, so `axis i : ℕ = 3` cached as `i ↦ 4` no longer seeds inference with an extent the source never declares |
| `Adapter.lean` | named ↔ positional runtime boundary — `pack`/`unpack`/`runPreparedDense`. `unpack` is `Except PlanError`-valued (whole-branch review): it resolves `materializedNames` through the shared `PlanBindings.materializedWith`, so a binding naming a slot outside the result store fails loud BEFORE any name is published (`PlanRunCause.materialization`), instead of publishing a fabricated empty tensor under a real output name |
| `Executable.lean` | JAX executable phase (Thread 5, extended by Boolean-output Task 4.5): `ExecutionEvidence`, kernel/plan candidates, private-constructor `JaxKernel`/`JaxExecutable` gated by real validators (`validateAffineTable`/`validateEinsum`), plus the JAX SUPPORT gate (`JaxSupportError`, `checkJaxAssignSupport`) that rejects a Boolean destination, a Boolean source, tropical max/min algebra, a unary read, and (Task 4.5 closure) a CONTEXTFUL assignment — non-empty `AssignPlan.contextShape`, which both lowerings silently rendered context-free — before any candidate or evidence exists, in the declared order destination/algebra/context/factors that mirrors `checkAssign`'s own. Every standalone validator/entry takes one explicit complete `Array TensorSignature` and re-runs `checkAssign` under it; `JaxKernel` stores that validated table and `JaxExecutableWellFormed` ties it (and each candidate's assignment) to the corresponding prepared checked step. `validateEinsum` recomputes exact operand axes, requires exact `outputAxes = term.outputPos`, and (Task 4.5 re-review) mirrors the emitter's three TERM-level preconditions via `einsumTermRenderable` — non-empty factors, iteration rank within the shared `einsumLabelLimit` (pinned against `EvalPlanCodegen.labelTable` by a `#guard` there), and complete iteration-position coverage — so certification implies `lowerAssign` renders; a factor-free assignment used to be certified and then rejected `emptyTerm`. Renderability alone is NOT sufficient (Task 4.5 re-review, second finding): every factor's source extent must equal the iteration extent of the label it is emitted with, because a zero-padded read shorter than its own iteration basis renders happily as `a->a` and returns a DIFFERENT-shaped result than Dense. That rule is the PUBLIC, located `einsumTermLabelExtents` (whole-branch review): `validateEinsum` consumes its `Bool` view and `EvalPlanCodegen.lowerAssign` calls the same function and rejects with a located `labelExtentMismatch`, so it is no longer a validator/emitter disagreement — a public lowering entry must not return a semantically unsupported einsum program either. `affineReference` still renders it (its tables carry the zero-pad mask), so the rule stays einsum-scoped. Consumed only by `experiments/jax_bridge`, not by the production `LeanNCD` import graph (see the exception noted above) |
| `Block.lean` | checked plan-block vertical slice (F2), generalized to `BlockStep` by the nonlinearity plan's Task 3 — `BlockError`, `CheckedBlockStepEvidence`, `CheckedPlanBlock`/`checkPlanBlock`, `runDenseBlock`; reuses `checkAssign`/`checkPointwise`/`checkAxiswise` and `runDenseAssignAt`/`runDensePointwise`/`runDenseAxiswise` per step, plus the shared `checkStepGraph` wiring loop, not a second local-graph implementation. One obligation is local to this file and has no outer-graph analogue: a `.pointwise`/`.axiswise` step's source must be a PRECEDING `.assign` step's destination (`nonlinearSourceNotLocalAssignment`) — that is what keeps `Scan.lean`'s assignment-only causality walk complete |
| `Nonlin.lean` | checked nonlinearity IR (nonlinearity thread 4) — `RawPointwisePlan`/`RawAxiswisePlan`, closed `NonlinPlanError`, shared geometry-check helper `checkNonlinIO` (case×class table rows 1-7), `checkPointwise`/`checkAxiswise` built on it (row 8 added by the latter), and dense workers `runDensePointwise`/`runDenseAxiswise`, which delegate all per-function math to `Eval/Nonlin.lean`'s `PointwiseFn.apply`/`AxiswiseFn.apply` — no second local-operation representation (unlike `Kernel.lean`'s `AssignPlan`, these steps carry no term/factor/reduction structure at all) |
| `RawStep.lean` | checked scan graph, Task 1 (F3); extended by nonlinearity thread 4's Task 2 and again by the nonlinearity plan's Task 3 — raw scan/local-block vocabulary: `BlockStep` (`.assign`/`.pointwise`/`.axiswise`, the element type of a local block, with `sourceSlots`/`destinationSlots`/`contextShape?`/`assign?` accessors), `RawPlanBlock` (its `steps` field holds those; relocated here from `Block.lean` so `Graph.lean` can reference a scan node without a circular import), `RawScanPlan`, `PlanStep` (`.assign`/`.scan`/`.pointwise`/`.axiswise`, the OUTER graph's node type — deliberately a separate sum from `BlockStep`, which has no `.scan` case) |
| `Scan.lean` | checked scan graph, Tasks 2-3 (F3) — write-geometry classifier (`WriteRowKind`/`writeRowKinds`), collision/coverage checks (`baseWriteRowsOk`/`stepWriteRowsOk`/`writesCollide`), free-row extent agreement (`freeExtentsAgree` — geometry admission covers rank/position only, so this is a SEPARATE check, not part of `baseWriteRowsOk`), pinned-literal range agreement (`pinnedLiteralsInRange` — its sibling: geometry admission never inspects a pinned literal's VALUE beyond `baseWriteRowsOk`'s single "some advancing dimension is `0`" rule), the causality certificate (`stateReadCausal`), `checkScanPlan`/`CheckedScanPlan`, and the dense worker `runDenseScan` (mixed-radix coordinate enumeration + `commitWrite`). Whole-branch review: `checkScanPlan` also requires an ADMITTED dtype for every state destination (`stateDtypeNotAdmitted`) and every capture's block-local input signature (`captureDtypeNotAdmitted`) — both are positions no `checkAssign` sees, and both cross-checks that compare them (`writeDtypeMismatch`, `captureSignatureMismatch`) are equality checks a matching pair of `f32`s satisfies; and `CheckedScanPlan` now STORES the signature table it was validated against, which `runDenseScan` runs from while requiring the caller's argument to equal it exactly (`PositionalInputError.signatureContextMismatch`) — checking under a `#[2]`-shaped state and running under a `#[1]`-shaped table used to return `.ok` with an `Array.set!` panic |
| `EvalPlan.lean` | checked scan graph, Task 4 (F3) — outer-graph `checkPlan`/`CheckedEvalPlan`/`runDensePlan`, generalized from `AssignPlan`-only steps to `PlanStep`, dispatching `checkAssign`/`checkScanPlan` per node without re-deriving either's obligations; also hosts `PlanCompileCause`/`PlanCompileFailure` (relocated from `Error.lean`, same acyclic-import constraint as `RawPlanBlock`'s move; F4 added the `scan` arm carrying `ScanCompileError`) |

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
| Export | Used By | Change Impact |
|---|---|---|
| `TLProgram.eval` (`Entry.lean`) | diagnostic-aware callers | primary source entry; returns `Except EvalFailure EvalReport`, preserving warnings on success and failure |
| `evalScheduled` (`Eval.lean`) | `Entry.lean`, scheduled-program callers | compiler-independent worker; returns the same success/failure report pair as the source entry. Whole-branch review: it re-runs the shared `buildDeclEnv` over `sched.decls` FIRST, so a hand-built schedule declaring one tensor-bearing name twice is `EvalError.compile (.duplicateTensorDecl …)` rather than being evaluated under whichever kind `combineFor`'s first-match scan happens to pick — the same `CompileError` `prepareEvalPlan` reports as `sourceInvariant`. An `.axis` sharing a predicate's name is a different namespace and stays legal. Its size-inference seed is likewise re-derived (`declaredAxisSizes sched.decls`, not `sched.explicitSizes`) — the same rule `prepareEvalPlan` applies, so a stale cached map cannot make the two backends disagree |
| `DenseTensor { shape; data }` | every file here | invariant `data.size = ∏ shape` — no runtime check, breaking it silently breaks `get!`/`set!`/`ofFn` |
| `evalAssignDtypedSeeded`/`Combine` (`Contract.lean`) | `evalPlain` (via `evalAssignDtyped`, its empty-seed wrapper) AND `Scan.evalStmtSliceSeeded` | dtype→semiring dispatch (real/bool/tropical), now shared by plain and scan assignment — before Wave B (4c), the scan path matched `rhs.agg` manually and could never select `Combine.bool` for a predicate state; new dtype needs a new `Combine` + `combineFor` arm |
| `inferAxisSizes` (`SizeInfer.lean`, re-exported by `Shape.lean`) | `evalScheduled` | central sizing fixpoint; returns `Except EvalFailure (sizes × warnings)`, preserving warnings even if a later inference check fails |
| `evalScan` (`Scan.lean`) | `evalScheduled` | multi-axis scan driver — `axes` is a general `List AxisSpec`, not 1-D |
| `EvalError`/`ShapeError`/`EvalWarning` (`Error.lean`) | every worker's `Except EvalError _`; every typed test assertion | closed, layered diagnostic types (Wave E, 4h) — adding a genuinely new failure mode means adding a constructor here, not composing a new ad-hoc string; every existing `ToString` output is still byte-identical to the pre-4h flat messages |


### Core Types
`DenseTensor { shape : List Nat; data : Array Float }` — the only runtime value type.
`EvalReport { env : HashMap String DenseTensor; warnings : List EvalWarning }` (`Eval/Report.lean`) —
the successful result of either entry path; `env` retains inputs plus computed tensors exactly as
before 4i. `EvalFailure { error : EvalError; warnings : List EvalWarning }` (`Error.lean`) preserves
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
- **Checked-plan `ScalarDType.bool` is a SEMANTIC ALGEBRA/SIGNATURE TAG over Float storage, never a
  native carrier** (Task 4, `papers/boolean_predicate_output_evalplan.md`). `DenseTensor` still holds
  `Array Float` everywhere; `Dense.constFloat` decodes `.bool true`/`.bool false` to `1.0`/`0.0`, and
  the ordinary Float `min`/`max` run. Consequences that are easy to assume wrong:
  (a) **the DESTINATION selects the algebra** — `admittedAlgebrasFor` gives real sum-product plus the
  two tropical semirings to `f64`, Boolean min/max (`admittedAlgebraBool`) to `bool`, and nothing to
  `f32`; (b) **source/destination dtype equality is deliberately NOT an assignment obligation** — a
  `bool` source may feed an `f64` destination and vice versa, since gathering is dtype-blind, and
  `PlanError.dtypeMismatch` is retained producer-less as a result; (c) **runtime values are NOT
  restricted to `0.0`/`1.0`** — a non-binary Float keeps literal `min`/`max` behavior, matching the
  reference evaluator; adding a truth check would create a checked/reference divergence; (d)
  **declarations are authoritative** — `buildDeclEnv` rejects a repeated tensor-bearing name and an
  explicit input signature contradicting a declaration is rejected
  (`InputSignatureError.dtypeMismatch`), never rewritten; (e) `f32` stays rejected everywhere.
- **`scatterOutShape`/`scatterOutputShapes` MUST equal `LHSSlot.outExtent`** (`../DSL/Ast.lean`) — the sole shared formula both `Eval.scatterOutShape` and `SizeInfer.scatterOutputShapes` call. History: an earlier duplicate formula (`scatterOutDim`, upper-envelope `max index + 1`) disagreed with the evaluator's stride-based materialization for strided scatters (`Out[2*i]`) — a downstream reader was sized to `3` while `evalScatter` materialized `4`, an unsound cropped read (fix `fc10d70`). The duplicate was deleted (`6a26825`) so both call sites share one function — **no import enforces this beyond both depending on the same function; a future second formula reintroduces the drift risk.**
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
| Understand why a source scan was rejected | Match the `PlanCompileCause` constructor: `.capability` = syntactically visible (preflight, no sizes needed), `.scan` = `ScanCompileError` from `compileScan` (needs sizes/affine maps), `.invalidPlan` = `checkScanPlan` rejected COMPILER output, which is a compiler bug, not a source problem, `.nonlin` = `NonlinCompileError` from `resolveNonlinAxis` (freeNorm-marker/`Nonlin`-kind agreement, nonlinearity thread 4 — needs the statement's whole LHS slot list, so it cannot be decided at preflight either). Fixtures: `test/Eval/Plan/ScanCompileTest.lean` (`.capability`/`.scan`/`.invalidPlan`), `test/Eval/Plan/NonlinCompileTest.lean` (`.nonlin`) |
| Check that a compiled scan still MATCHES the legacy evaluator | `test/Eval/Plan/DifferentialTest.lean`'s scan section — the eight-point execution matrix (`scanParityCheck`) over every `ScanCompileTest.lean` acceptance fixture plus the curated `enumScanCases` corpus gate (17 cases: 17 accepted, 0 `unsupportedNonlin`, 0 `unsupportedAgg` — was 9 / 4 / 4 at Wave F F4 authoring time; thread 4 Task 4 admitted pointwise/axiswise scan-block nonlinearities and the max/min-aggregation thread admitted `.max`/`.min`, moving all eight rejected cases into the accepted column). Parity holds only for the fragment where the checked Jacobi semantics and the legacy worker AGREE (proposal §10 Law 1) — see that section's scope note. Named-boundary FAILURES (missing/mis-shaped input at a scan capture, warning preservation) are in `test/Eval/Plan/AdapterTest.lean` Checks 11–16 |
| Check a compiled scan against something that is NOT either evaluator | The matrix's point 8 — `test/Eval/PropertyOracle/ScanUnroll.lean`'s `independentRun`, a mechanical rewrite of a scan into a scan-free leaf program (one leaf per state × history coordinate, one per scratch name × step iteration, plus a per-state zero leaf), evaluated by the ordinary assignment evaluator and reassembled with `DenseTensor.ofFn`. Deliberately calls no `runDenseScan`/`evalScan`/`writeRowKinds`/`applyAffine`/compiler-residualization/scan-worker-write helper (plan §4.8) — if you make it import one, the three-way gate stops being a differential. It implements the CHECKED (Jacobi) reading, so a disagreement with `evalScheduled` is a real Gauss-Seidel finding, not an oracle bug. Two-way sweep over all 17 generated cases: `test/Eval/PropertyOracle/ScanOracle.lean` |
| Add a new nonlinearity | Legacy evaluator: `Nonlin.lean` — add a `PointwiseFn`/`Nonlin.axiswise` arm, an `applyNonlin` case, and (for an axiswise fn) confirm `resolveNonlin`'s existing marker check covers it — do not add a second marker-lookup site in `Eval.lean`/`Scan.lean`. <br> Plan layer (nonlinearity thread 4): its own new constructor in `DSL/Ast.lean`'s `PointwiseFn`/`AxiswiseFn`, its `*T` implementation plus one match arm in `PointwiseFn.apply`/`AxiswiseFn.apply` (both `Eval/Nonlin.lean`), and a new fixture — nothing in `Plan/Nonlin.lean` changes, since its checker (`checkNonlinIO`) and dense workers are fully function-agnostic |
| Add a new dtype/semiring | `Contract.lean` — new `Combine.*` + `combineFor` arm |
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
  (`topLevelContextNotEmpty`).
- **scatterOutDim/scatterOutShape drift (historical, now structurally prevented)** — see Contracts. If a second scatter-extent formula is ever reintroduced, the drift bug returns silently.
- **Scan is genuinely n-D now** — `Scan.evalScan`'s `axes` drives a cartesian-product over every advancing axis; code assuming 1-D scan structure will misbehave on a 2-D recurrence.
- **An unsized scan iteration axis is an error naming its own fix** — `Scan.evalScan` reports "unsized iteration axis 'l' (uid N) — pin it with ``axis l : ℕ = N``, or ensure some read fixes its extent". One adjacent case is deliberately NOT covered: an axis pinned explicitly to `0` still yields `L = 0` (a stated intent, not a sizing gap). A second case, `axis l : ℕ[3]` pinning nothing at all, USED to be a live trap here (the kind-carried size was write-only) — audit finding H fixed it 2026-07-30 by deleting the payload from `AxisKind` itself, so `ℕ[3]` no longer parses as an axis kind at all (see `../DSL/AGENTS.md`).
- **Out-of-range reads are `.ok 0.0`, not `.error`** (`Gather.gatherRead`) — only genuine domain violations and unknown-tensor/unsized-axis conditions raise `EvalError`. Don't conflate "padded zero" with "failure."
- **`readAxisUIDs`/`termAxisUIDs`/`freeAxisUIDs` are NOT interchangeable** (`Contract.lean`) — `freeAxisUIDs` must return a subset (non-affine slots only); swapping these breaks shape inference or contraction scoping silently.
- **`stateShape` is confirmed gone** (deleted, "reuse outputShape") — `Scan.evalScan` allocates scan state via `Slots.outputShape` directly.
