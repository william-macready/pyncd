# LeanNCD/Eval

## Purpose
Owns: the reference-semantics interpreter for the compiled DSL — takes a `ScheduledProgram` (from `../DSL/Pipeline/`) plus concrete input tensors and produces concrete output tensors over a single dense representation (`DenseTensor`). Exists to pin down ground-truth semantics (contraction scoping, scatter/gather, scan boundary rules, nonlinearity dispatch, axis-size inference) that the static compiler and any future fast backend must agree with — not a fast/vectorized executor.
Does not own: parsing/compilation/routing (`../DSL/`).

**House principle: fail loud.** Any axis whose size can't be inferred, unknown tensor, or domain violation (`log`≤0, `sqrt`<0, `1/0`) throws `EvalError` rather than silently defaulting.

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| Entry point (compiled program → outputs) | `Eval.lean` — `TLProgram.eval`, `evalScheduled` |
| Dense tensor rep, coord math | `Tensor.lean` |
| Index/predicate/mask eval, zero-padded reads, unary math fns | `Gather.lean` |
| Scatter (`Out[2*i] := ...`) evaluation | `Scatter.lean` |
| Nonlinearities (relu/sigmoid/tanh/gelu/softmax/normalize) | `Nonlin.lean` |
| Recurrence / n-D scan evaluation | `Scan.lean` |
| Einstein-summation contraction, dtype semiring dispatch | `Contract.lean` |
| Axis-size inference (RREF solver), output-shape formulas | `Shape.lean` (largest, 475 lines) |
| "Does this model class evaluate correctly" test suite | `test/Eval/Portfolio/*.lean` |

### Key Relationships
`Eval.lean` imports `DSL.Compile`; `Shape.lean`/`Gather.lean` import `DSL.Ast`; `Scan.lean` imports `DSL.Pipeline.Types`; `Contract.lean` imports `DSL.TraverseAxes`. Internal chain: `Tensor` ← `Gather` ← `Nonlin`/`Shape` ← `Contract` ← `Scan`/`Scatter` ← `Eval`. `LHSSlot.outExtent` (defined in `../DSL/Ast.lean`, not here) is the single shared scatter-extent formula both `Eval.scatterOutShape` and `Shape.scatterOutputShapes` call.

## Public API

### Key Exports
| Export | Used By | Change Impact |
|---|---|---|
| `TLProgram.eval` | test harness (`assertEval*`) | the one blessed entry point; error-format changes break needle-matching across the whole Portfolio suite |
| `DenseTensor { shape; data }` | every file here | invariant `data.size = ∏ shape` — no runtime check, breaking it silently breaks `get!`/`set!`/`ofFn` |
| `evalAssignDtyped`/`Combine` (`Contract.lean`) | `evalPlain` | dtype→semiring dispatch (real/bool/tropical); new dtype needs a new `Combine` + `combineFor` arm |
| `inferAxisSizes` (`Shape.lean`) | `evalScheduled` | central sizing fixpoint, touches scatter-output propagation and both hard-conflict/warning paths |
| `evalScan` (`Scan.lean`) | `evalScheduled` | multi-axis scan driver — `axes` is a general `List AxisSpec`, not 1-D |

### Core Types
`DenseTensor { shape : List Nat; data : Array Float }` — the only runtime value type. `EvalError := String` — shared error type; tests pin down specific substrings.

## Contracts
- **`scatterOutShape`/`scatterOutputShapes` MUST equal `LHSSlot.outExtent`** (`../DSL/Ast.lean`) — the sole shared formula both `Eval.scatterOutShape` and `Shape.scatterOutputShapes` call. History: an earlier duplicate formula (`scatterOutDim`, upper-envelope `max index + 1`) disagreed with the evaluator's stride-based materialization for strided scatters (`Out[2*i]`) — a downstream reader was sized to `3` while `evalScatter` materialized `4`, an unsound cropped read (fix `fc10d70`). The duplicate was deleted (`6a26825`) so both call sites share one function — **no import enforces this beyond both depending on the same function; a future second formula reintroduces the drift risk.**
- **Fail-loud unsized axis**: `evalAssignWith` throws before building an output shape if any output axis has no inferable size; mirrored in `Eval.scatterOutShape` and `Scatter.evalScatter`.
- **Non-identity scatter is rejected, not silently dropped**: `Scatter.evalScatter` throws if `rhs.nonlin ≠ .identity` (defensive re-check; the primary gate is `checkScatterNonlin` in `../DSL/Pipeline/Structural.lean`, see that dir's AGENTS.md). Fixes the bug where `Out[2*i] := relu(X[i])` used to compile and silently drop the `relu`.
- **Per-term contraction scoping**: each `+`-joined RHS term is contracted over only the axes *that term* mentions (`termAxisUIDs`), not the union across the whole equation.
- **`readAxisUIDs` excludes nonlin-mask axes** — must stay `traverseAxesNoMask`, not the with-mask variant, or shape inference gets corrupted by mask-only UIDs.
- **RREF solver floor-then-verify convention** (`Shape.lean`): builds an upper-envelope affine constraint per unsized read position, reduces to RREF over `Rat`, floors any fractional solution (padded/stride semantics), then re-verifies the floored solution against every original constraint. Typed failure kinds (`inconsistent`/`underdetermined`/`nonIntegral`/`nonPositive`) with remediation hints.

## Patterns
The Portfolio suite (`test/Eval/Portfolio/`, shared `Harness.lean`) is a broad library of worked model fragments, one file per model family (LinAlg/Feedforward/Attention/ConvPool/Norm/Recurrence/GnnScatter/Relational/StatsLoss/Tropical/TensorNet/Generative/ClassicalML/EdgeCase). Three test styles (see `docs/test_portfolio.md`): **[N] numeric** (`assertEval`/`assertShape`, compare against a hand-computed tensor or property), **[R]/[F] runtime/compile failure** (`assertEvalError`/`assertCompileError`, checks the error string/constructor), and pure parse-errors (documented as comments only — `tlprog!` fails during elaboration, before any assertion machinery runs). `RejectTest.lean`/`ScatterNonlinRejectTest.lean` hold adversarial cases pinned to a specific error so a regression that turns a reject into a silent success is caught. `KnownGapTest.lean` is pure documentation — a triage taxonomy of DSL expressiveness gaps (rejecting/parse-level/missing-primitive/confirmed-non-gaps), not live assertions.

## Entry Points
| Task | Start Here |
|------|------------|
| Run a compiled program end-to-end | `Eval.TLProgram.eval` |
| Add a new nonlinearity | `Nonlin.lean` — add a `PointwiseFn`/`Nonlin.axiswise` arm + `applyNonlin` case |
| Add a new dtype/semiring | `Contract.lean` — new `Combine.*` + `combineFor` arm |
| Debug an axis-sizing failure | `Shape.inferAxisSizes` — check `SolveDiagnostic` message |
| Debug a scatter shape mismatch | Confirm `LHSSlot.outExtent` is the sole formula both call sites use |
| Add a portfolio test case | `test/Eval/Portfolio/<Family>Test.lean` + `Harness.lean` asserters |

## Pitfalls
- **scatterOutDim/scatterOutShape drift (historical, now structurally prevented)** — see Contracts. If a second scatter-extent formula is ever reintroduced, the drift bug returns silently.
- **Scan is genuinely n-D now** — `Scan.evalScan`'s `axes` drives a cartesian-product over every advancing axis; code assuming 1-D scan structure will misbehave on a 2-D recurrence.
- **Out-of-range reads are `.ok 0.0`, not `.error`** (`Gather.gatherRead`) — only genuine domain violations and unknown-tensor/unsized-axis conditions raise `EvalError`. Don't conflate "padded zero" with "failure."
- **`readAxisUIDs`/`termAxisUIDs`/`freeAxisUIDs` are NOT interchangeable** (`Contract.lean`) — `freeAxisUIDs` must return a subset (non-affine slots only); swapping these breaks shape inference or contraction scoping silently.
- **`stateShape` is confirmed gone** (deleted, "reuse outputShape") — `Scan.evalScan` allocates scan state via `Shape.outputShape` directly.
