# LeanNCD/Eval

## Purpose
Owns: the reference-semantics interpreter for the compiled DSL — takes a `ScheduledProgram` (from `../DSL/Pipeline/`) plus concrete input tensors and produces concrete output tensors over one dense representation (`DenseTensor`). It pins down ground-truth semantics (contraction scoping, scatter/gather, scan boundary rules, nonlinearity dispatch, axis-size inference) that the checked backend and any future fast backend must agree with. It is not a fast executor.
Does not own: parsing/compilation/routing (`../DSL/`). The checked, positional plan backend lives in `Plan/` and has its own node: **[`Plan/AGENTS.md`](Plan/AGENTS.md)**.

**House principle: fail loud.** An axis whose size can't be inferred, an unknown tensor, or a domain violation (`log`≤0, `sqrt`<0, `1/0`) throws `EvalError` rather than silently defaulting.

## Code Map

| Looking for... | Go to |
|---|---|
| Source entry (compile + evaluate, preserving warnings) | `Entry.lean` — `TLProgram.eval` |
| Scheduled worker (no source-compiler dependency) | `Eval.lean` — `evalScheduled`; `EvalReport` is in `Report.lean` |
| Dense tensor rep, coord math | `Tensor.lean` |
| Index/predicate/mask eval, zero-padded reads, unary math fns | `Gather.lean` |
| Scatter (`Out[2*i] := ...`) evaluation | `Scatter.lean` |
| Nonlinearities, both carriers — each formula written ONCE over a private `NonlinScalarOps α` record, instantiated as binary64 (`PointwiseFn.apply`/`AxiswiseFn.applyCore`, `reluT` … `l2normalizeT`) and native binary32 (`PointwiseFn.apply32`/`AxiswiseFn.applyCore32`) | `Nonlin.lean` |
| Recurrence / n-D scan evaluation | `Scan.lean` |
| Einstein-summation contraction, dtype→semiring dispatch | `Contract.lean` |
| LHS-slot shape vocabulary (`normAxisUidOf`, `outputShape`) | `Slots.lean` |
| Pure affine constraint solver (RREF over `ℚ`) | `SizeSolve.lean` |
| Axis-size inference fixpoint (`inferAxisSizes`, `scatterOutputShapes`) | `SizeInfer.lean` |
| Compatibility umbrella re-exporting `Slots`/`SizeSolve`/`SizeInfer` (no code) | `Shape.lean` |
| Every typed diagnostic (`EvalError`, `ShapeError`, `EvalWarning`, `SolveDiagnostic`, `EvalFailure`) and their sole renderers | `Error.lean` |
| Checked positional plan IR, compiler, workers, adapters, JAX executable phase | `Plan/` — see [`Plan/AGENTS.md`](Plan/AGENTS.md) |
| "Does this model class evaluate correctly" suite | `test/Eval/Portfolio/*.lean` |

### Import structure
Branched, not linear: `DSL.Ast → Slots → Nonlin/Scan`; `Tensor → Gather → Contract → Scatter`;
`Exec.Uid + Error → SizeSolve`, then `SizeSolve + Tensor + DSL.Ast → SizeInfer`;
`Contract + Nonlin + Slots + SizeSolve → Scan`; `Eval` joins `Scan`, `Scatter`, `SizeInfer`; `Entry`
joins `Eval` with `DSL.Compile` (`Eval.lean` itself never imports the compiler). Production modules
import the narrow module they need, not the `Shape.lean` umbrella. `Error.lean` is a leaf (imports
only `Exec.Uid`/`DSL.Ast`); files that throw or render diagnostics import it explicitly, while
`Tensor.lean`, `Slots.lean`, `Shape.lean`, and `Entry.lean` do not. `Tensor.lean` knows nothing about
error representation. `SizeSolve.lean` constructs `SolveDiagnostic`s but never renders one.

## Public API

| Export | Used By | Change Impact |
|---|---|---|
| `TLProgram.eval` (`Entry.lean`) | diagnostic-aware callers | primary source entry; `Except EvalFailure EvalReport`, preserving warnings on success and failure |
| `evalScheduled` (`Eval.lean`) | `Entry.lean`, scheduled-program callers | compiler-independent worker, same outcome pair. Calls the neutral `Pipeline/ScheduledValidation.validateScheduled` boundary (shared with `prepareEvalPlan`) and trusts no cached schedule field: it re-runs `buildDeclEnv` first (a duplicate tensor-bearing name is `EvalError.compile (.duplicateTensorDecl …)`), re-derives its size seed from `declaredAxisSizes sched.decls`, and checks read/destination ranks and dtypes over `.plain` and scan `base ++ recur`. Order: `buildDeclEnv`, rank checks, per-statement axis kinds then predicate rules, topology, size inference, execution |
| `DenseTensorOf α { shape; data }` (`Tensor.lean`) | every file, via aliases | invariant `data.size = ∏ shape`, unchecked — breaking it silently breaks `get!`/`set!`/`ofFn`. `DenseTensor := DenseTensorOf Float`, `DenseTensor32 := DenseTensorOf Float32`; only the shell is generic, helpers stay binary64. `DenseTensor.mk`/`.shape`/`.data` are explicit compatibility shims (an alias synthesizes no generated names) pinned by `Eval.TensorTest` fixture 15 |
| `EvalReportOf α { env; warnings }` (`Report.lean`) | both entry paths, `Plan/Adapter*.lean` | `EvalReport`/`EvalReport32` aliases; `EvalWarning` deliberately NOT parameterized. `EvalReport.mk`/`.env`/`.warnings` are shims pinned by `AdapterTest` fixture 11 |
| `evalAssignDtypedSeeded`/`Combine` (`Contract.lean`) | `evalPlain` (via `evalAssignDtyped`) and `Scan.evalStmtSliceSeeded` | the one dtype→semiring dispatch (real/bool/tropical) shared by plain and scan assignment; a new dtype needs a new `Combine` + `combineFor` arm |
| `inferAxisSizes` (`SizeInfer.lean`) | `evalScheduled` | sizing fixpoint; `Except EvalFailure (sizes × warnings)`, preserving warnings if a later check fails |
| `evalScan` (`Scan.lean`) | `evalScheduled` | multi-axis driver — `axes` is a general `List AxisSpec`, not 1-D |
| `EvalError`/`ShapeError`/`EvalWarning` (`Error.lean`) | every worker; typed test assertions | closed, layered inductives with exactly one renderer each; `.compile`/`.shape` nest typed causes. A new failure mode is a new constructor, never an ad-hoc string. Every `ToString` output is byte-identical to the historical flat message — tests that grep the rendered string depend on it |

`EvalFailure { error; warnings }` preserves warnings inferred before a later failure; only compile
failures necessarily carry `[]`. Tests match constructors where that strengthens the assertion and fall
back to `toString` for legacy renderer checks.

## Contracts
- **Every scatter extent MUST equal `LHSSlot.outExtent`** (`../DSL/Ast.lean`), the sole stride-aligned formula. `Eval.scatterOutShape` and `SizeInfer.scatterOutputShapes` call it directly; the checked scan geometry reaches it through `scatterDestExtent`. For one normalized positive coefficient `c`, nonnegative bias `b`, and source extent `n > 0` it is `c*n + (b/c)*c`; other forms keep the linear fallback. A duplicate formula once produced an unsound cropped read (fix `fc10d70`). **Do not add a second extent formula.**
- **Fail-loud unsized axis at every materialization site**: `evalAssignSeeded` (the sole contraction implementation) throws before building an output shape if any non-seeded free output axis, any per-term contracted axis, or any seeded axis has no inferable size, and rejects an out-of-range seed coordinate. Mirrored in `Eval.scatterOutShape`, `Scatter.evalScatter`, and `Scan.evalScan`. Each site is a distinct `UnsizedAxisSite` tag on `ShapeError.unsizedAxis`. Keep the list complete: `evalScan` once used `getD 0`, conflating "no extent" with "extent 0", and panicked on an unpinned scan axis.
- **Non-identity scatter is rejected, not dropped**: `Scatter.evalScatter` throws if `rhs.nonlin ≠ .identity` (defensive; the primary gate is `checkScatterNonlin` in `../DSL/Pipeline/Structural.lean`).
- **Scatter values use `Contract.lean`'s `Combine`, selected by `rhs.agg`** — never a hardcoded real sum-of-products (a `maxreduce` scatter once computed a real sum).
- **`ScatterOpts.reduce` is a closed `CollisionReduce`** (`rejectCollisions` default, `overwrite`, `sum`, `max`, `min`). Surface syntax only ever produces the default; the others need direct `Stmt.scatter` construction. `lowerArith` independently rejects surface-detectable collisions (`overlappingScatter`).
- **Per-term contraction scoping**: each `+`-joined RHS term contracts over only the axes it mentions (`termAxisUIDs`), not the union across the equation.
- **`readAxisUIDs` excludes nonlin-mask axes** — it must stay `traverseAxesNoMask`, or mask-only UIDs corrupt shape inference.
- **RREF floor-then-verify** (`SizeSolve.lean`, driven by `inferAxisSizes`): an upper-envelope affine constraint per unsized read position, RREF over `Rat`, floor any fractional solution (padding/stride semantics), then re-verify against every original constraint. Failure kinds `inconsistent`/`underdetermined`/`nonIntegral`/`nonPositive` carry remediation hints.
- **`Combine`'s factor-product fold starts from `unit1`, never a literal `1.0`.** `unit1` (identity of one term's factor product) is distinct from `unit0` (identity of the term-aggregation fold). All four current values have `unit1 = 1.0`, but not all use ordinary multiplication — `Combine.bool` is `⟨min, max, 0.0, 1.0⟩` — so thread the field; don't assume it.
- **Warnings are outcome data, never trace output**: returned unchanged through `evalScheduled`/`TLProgram.eval`, in `EvalReport` on success and beside the error in `EvalFailure`. Do not reintroduce `dbg_trace` or an environment-only entry.
- **The legacy evaluator refuses `f32` permanently.** Every worker here computes in binary64, so a `tensor f32` has no correct reading. `evalScheduled` reports `EvalError.unsupportedDtype nm` for the first used f32 name (`scheduleFloat32Name?`) before sizing runs; `evalAssignDtypedSeeded`, `evalPlain`, `evalStmtSliceSeeded`, and `evalScan` each guard at their own ENTRY (`rejectUnsupportedStorage`), because the scatter and scan arms would otherwise hit shape/nonlinearity failures first and misreport. Consequence: **there is no legacy oracle for any f32 program** — binary32 fixtures assert exact `Float32.toBits` values instead.

## Patterns
The Portfolio suite (`test/Eval/Portfolio/`, shared `Harness.lean`) has one file per model family. Test styles (see `docs/test_portfolio.md`): **[N] numeric** (`assertEval`/`assertShape`), **[R]/[F] runtime/compile failure** (`assertEvalError`/`assertCompileError`), and parse errors documented as comments only (`tlprog!` fails during elaboration, before any assertion runs). `RejectTest.lean`/`ScatterNonlinRejectTest.lean` pin adversarial cases to a specific error. `KnownGapTest.lean` is documentation — a triage taxonomy of DSL expressiveness gaps, not live assertions.

## Entry Points
| Task | Start Here |
|------|------------|
| Evaluate source, preserving warnings | `Entry.lean` — `TLProgram.eval` |
| Evaluate a schedule without the compiler | `Eval.lean` — `evalScheduled` |
| Anything on the checked plan backend (compile, run, f32, JAX, differential tests) | [`Plan/AGENTS.md`](Plan/AGENTS.md) |
| Add a new nonlinearity | Its constructor in `DSL/Ast.lean`'s `PointwiseFn`/`AxiswiseFn`; one `pointwiseWith`/`axiswiseRowWith` arm in `Nonlin.lean` (the single formula both carriers share); any new constant in **both** `floatNonlinOps` and `float32NonlinOps` (binary32 as an exact bit pattern); a fixture in each of `NonlinTest`/`Nonlin32Test`. `applyNonlin` needs no new case — it dispatches on the resolved shape, not per function — and `Plan/Nonlin.lean` is function-agnostic. For an axiswise fn, confirm `resolveNonlin`'s existing marker check covers it; don't add a second marker lookup |
| Add a new semiring over an existing carrier | `Contract.lean` — new `Combine.*` + `combineFor` arm. A new CARRIER is a checked-backend change: see [`Plan/AGENTS.md`](Plan/AGENTS.md) |
| Debug an axis-sizing failure | `SizeInfer.inferAxisSizes` — match the `ShapeError`/`SolveDiagnostic` constructor, or `toString` it |
| Debug a scatter shape mismatch | Confirm `LHSSlot.outExtent` is the only formula in use |
| Add a portfolio test case | `test/Eval/Portfolio/<Family>Test.lean` + `Harness.lean` asserters |

## Pitfalls
- **Scan is genuinely n-D** — `evalScan`'s `axes` drives a cartesian product over every advancing axis; code assuming 1-D scans misbehaves on a 2-D recurrence.
- **An unsized scan iteration axis is an error naming its own fix** ("pin it with ``axis l : ℕ = N``…"). An axis pinned explicitly to `0` still yields zero steps — a stated intent, not a sizing gap.
- **Out-of-range reads are `.ok 0.0`, not `.error`** (`Gather.gatherRead`). Don't conflate a padded zero with failure.
- **`readAxisUIDs`/`termAxisUIDs`/`freeAxisUIDs` are NOT interchangeable** (`Contract.lean`) — `freeAxisUIDs` returns a subset (non-affine slots only); swapping them silently breaks shape inference or contraction scoping.
- **Scan state is allocated with `Slots.outputShape`** — there is no `stateShape`; don't reintroduce one.
