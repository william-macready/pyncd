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
| Scheduled worker (no source compiler dependency) | `Eval.lean` — `evalScheduled`, `EvalReport` |
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
| "Does this model class evaluate correctly" test suite | `test/Eval/Portfolio/*.lean` |

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
| `evalScheduled` (`Eval.lean`) | `Entry.lean`, scheduled-program callers | compiler-independent worker; returns the same success/failure report pair as the source entry |
| `DenseTensor { shape; data }` | every file here | invariant `data.size = ∏ shape` — no runtime check, breaking it silently breaks `get!`/`set!`/`ofFn` |
| `evalAssignDtypedSeeded`/`Combine` (`Contract.lean`) | `evalPlain` (via `evalAssignDtyped`, its empty-seed wrapper) AND `Scan.evalStmtSliceSeeded` | dtype→semiring dispatch (real/bool/tropical), now shared by plain and scan assignment — before Wave B (4c), the scan path matched `rhs.agg` manually and could never select `Combine.bool` for a predicate state; new dtype needs a new `Combine` + `combineFor` arm |
| `inferAxisSizes` (`SizeInfer.lean`, re-exported by `Shape.lean`) | `evalScheduled` | central sizing fixpoint; returns `Except EvalFailure (sizes × warnings)`, preserving warnings even if a later inference check fails |
| `evalScan` (`Scan.lean`) | `evalScheduled` | multi-axis scan driver — `axes` is a general `List AxisSpec`, not 1-D |
| `EvalError`/`ShapeError`/`EvalWarning` (`Error.lean`) | every worker's `Except EvalError _`; every typed test assertion | closed, layered diagnostic types (Wave E, 4h) — adding a genuinely new failure mode means adding a constructor here, not composing a new ad-hoc string; every existing `ToString` output is still byte-identical to the pre-4h flat messages |


### Core Types
`DenseTensor { shape : List Nat; data : Array Float }` — the only runtime value type.
`EvalReport { env : HashMap String DenseTensor; warnings : List EvalWarning }` (`Eval.lean`) —
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
| Add a new nonlinearity | `Nonlin.lean` — add a `PointwiseFn`/`Nonlin.axiswise` arm, an `applyNonlin` case, and (for an axiswise fn) confirm `resolveNonlin`'s existing marker check covers it — do not add a second marker-lookup site in `Eval.lean`/`Scan.lean` |
| Add a new dtype/semiring | `Contract.lean` — new `Combine.*` + `combineFor` arm |
| Debug an axis-sizing failure | `SizeInfer.inferAxisSizes` — match the `ShapeError`/`SolveDiagnostic` constructor (`Error.lean`) directly, or `toString` it for the legacy flat message |
| Debug a scatter shape mismatch | Confirm `LHSSlot.outExtent` is the sole formula both call sites use |
| Add a portfolio test case | `test/Eval/Portfolio/<Family>Test.lean` + `Harness.lean` asserters |

## Pitfalls
- **scatterOutDim/scatterOutShape drift (historical, now structurally prevented)** — see Contracts. If a second scatter-extent formula is ever reintroduced, the drift bug returns silently.
- **Scan is genuinely n-D now** — `Scan.evalScan`'s `axes` drives a cartesian-product over every advancing axis; code assuming 1-D scan structure will misbehave on a 2-D recurrence.
- **An unsized scan iteration axis is an error naming its own fix** — `Scan.evalScan` reports "unsized iteration axis 'l' (uid N) — pin it with ``axis l : ℕ = N``, or ensure some read fixes its extent". One adjacent case is deliberately NOT covered: an axis pinned explicitly to `0` still yields `L = 0` (a stated intent, not a sizing gap). A second case, `axis l : ℕ[3]` pinning nothing at all, USED to be a live trap here (the kind-carried size was write-only) — audit finding H fixed it 2026-07-30 by deleting the payload from `AxisKind` itself, so `ℕ[3]` no longer parses as an axis kind at all (see `../DSL/AGENTS.md`).
- **Out-of-range reads are `.ok 0.0`, not `.error`** (`Gather.gatherRead`) — only genuine domain violations and unknown-tensor/unsized-axis conditions raise `EvalError`. Don't conflate "padded zero" with "failure."
- **`readAxisUIDs`/`termAxisUIDs`/`freeAxisUIDs` are NOT interchangeable** (`Contract.lean`) — `freeAxisUIDs` must return a subset (non-affine slots only); swapping these breaks shape inference or contraction scoping silently.
- **`stateShape` is confirmed gone** (deleted, "reuse outputShape") — `Scan.evalScan` allocates scan state via `Slots.outputShape` directly.
