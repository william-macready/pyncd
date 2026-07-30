# torch_compile

## Purpose
Owns: compiling a `data_structure.Category.Morphism` tree into a live `torch.nn.Module` tree — one `nn.Module` per categorical combinator (composition, product, threaded routing, repetition) and per leaf operator (einops contraction, registered torch function, or hand-written learned module like Linear, masked-softmax, or Scan).
Does not own: category theory (consumes `data_structure/`, never defines it) or ACSet serialization (`acset/`).

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| Entry point / dispatcher for any morphism → module | `torch_compile.py::ConstructedModule.construct` |
| Operator registry (stateful ops) vs. plain-function registry | `ConstructedModule.operation_registry` / `.functions_registry` |
| Einsum/einops string generation | `generate_einops_signature`, `generate_tensor_equation_signature` |
| Learned linear layer | `ConstructedLinear` → `torch_utilities.py::Multilinear` (tuple-shaped, since `nn.Linear` can't do multi-axis in/out) |
| `.normalize()` semantics | `ConstructedNorm.forward` |
| Masked softmax / masked normalize | `ConstructedMaskedSoftMax`, `ConstructedMaskedNormalize` |
| Iverson-bracket → tensor materialisation | `materialise.py::materialise_iverson` |
| Weave-to-torch-dim mapping (vmap vs `dim=` vs reshape) | `torch_compile.py::broadcast_func`, `bcast.py` |
| Constant-index reads / affine gather / affine scatter | `ConstructedSlice` / `ConstructedReindex` / `ConstructedScatter` |
| Recurrence/scan compilation (sequential + associative-scan fast path) | `ConstructedScan` |
| Dead file — do not look here for operators | `operators.py` (0 bytes since initial release) |

### Key Relationships
`torch_compile.py` is the hub; `bcast.py` and `materialise.py` are pure-function helpers it imports. `torch_utilities.py` is used only by `ConstructedLinear`. Everything categorical comes from `data_structure` (`Category`, `TensorDSL`, `Operators`) and `term_utilities` — this package never defines category theory, only consumes it.

## Public API

### Key Exports
| Export | Used By | Change Impact |
|---|---|---|
| `ConstructedModule.construct(target, dim=None)` | the only public compile entry point | changing match arms breaks compilation of whole morphism families |
| `ConstructedModule.add_function(func_type, func, dim, semantic)` | registers plain-torch-function operators at module load | new elementwise ops go through here, not a new class |
| `materialise_iverson(factor)` | `ConstructedTensorEquation`, masked softmax/normalize | raises `ValueError` on unsized axes — callers catch and fall back to caller-supplied tensors |

### Core Types
- `ConstructedModule[M]` (ABC) — base for all compiled modules; owns the two class-level dispatch registries.
- `Lambda(nn.Module)` — wraps a stateless registered function via `broadcast_func`.
- `Weights`/`Multilinear` — tuple-shaped learned linear layer.

## External Dependencies
| Library | Used For | Failure Mode |
|---|---|---|
| `torch`/`torch.nn` | all compiled modules, `vmap`, `index_put_`, `masked_fill` | version-sensitive: falls back to private `torch._higher_order_ops.associative_scan` if `torch.associative_scan` (≥2.5) is absent |
| `einops` | `einops.einsum` for `ConstructedEinops`/`ConstructedTensorEquation` | malformed contraction strings raise at first `forward()`, not at construct time |
| `torch._dynamo` | wraps `Scan`'s Python loop in `torch._dynamo.disable(...)` so `torch.compile` doesn't unroll it | private API — future dynamo changes could break scan compilation silently |

## Entry Points
| Task | Start Here |
|------|------------|
| Compile a morphism to a torch module | `torch_compile.py::ConstructedModule.construct` |
| Register a new plain-function operator (e.g. a new elementwise op) | `torch_compile.py`, near `ConstructedModule.add_function(...)` calls (~line 506-515) |
| Debug why a `Broadcasted` op picked the wrong torch call shape | `torch_compile.py::broadcast_func`, `bcast.py` |
| Add support for a masked nonlinearity | `ConstructedMaskedSoftMax`/`ConstructedMaskedNormalize` in `torch_compile.py` |

## Contracts
- `ConstructedModule.construct` requires an exact structural match; unhandled morphisms fall through to `raise NotImplementedError()` — new categorical constructors must be added to the `match` before they compile.
- `ConstructedTensorEquation` requires the equation's nonlinearity to be `None`/`Identity` — any other nonlinearity raises, and must be compiled as a separate `Broadcasted` step (not fused into the einsum).
- `ConstructedScan` requires `target.N` to be a concrete `nm.Integer` — symbolic iteration counts raise `ValueError` at construct time.
- `forward()` argument ordering is load-bearing: caller inputs first, then auto-materialised Iverson/mask buffers (`_caller_positions` tracks the split).

## Patterns
- **Compile pipeline**: `construct()` recurses structurally (`Composed`→`nn.Sequential`, `ProductOfMorphisms`→`nn.ModuleList`, `ThreadedComposed`→keeps a growing `live` list, routing later steps to reuse any earlier output by index). A `Broadcasted` leaf dispatches to `operation_registry` (dedicated class) or `functions_registry` (`Lambda` + `broadcast_func`).
- **`broadcast_func` branch order** (fastest→slowest): explicit `dim=` call → "implicit lower" fast path → semantic reshape (pure product shapes, no swaps) → `torch.vmap` composition (most general, slowest).
- **`ConstructedScan`** always builds a correctness-preserving sequential loop (`_run_loop`, wrapped in `torch._dynamo.disable`), and additionally an O(log N) `associative_scan` path when the step is provably affine in the state.
- **Iverson predicates are pre-evaluated once at construct time** into `{0,1}` buffers (`register_buffer`) — only works when every axis has a concrete size; otherwise the predicate must arrive as a caller-supplied runtime tensor.

## Pitfalls
- **`.normalize()` is NOT LayerNorm** (fix `9be5020`): `ConstructedNorm.forward` is `x / x.sum(dim, keepdim=True).clamp(min=1e-8)` — sum-normalization, no mean-subtraction, no learned affine. Porting a model description that expects `LayerNorm` semantics silently produces valid-but-wrong numbers.
- **ReLU dispatch must be registered explicitly, twice** (fix `d2efcef`) — `add_function(ops.Elementwise, torch.relu)` and `add_function(ops.ReLU, torch.relu)` both exist because a prior bug left `ops.ReLU` unregistered and a spurious identity Σ leaked into the `.linear()` path. A new nonlinearity operator type does **not** automatically inherit `Elementwise`'s registration — it needs its own `add_function` call.
- **Causal attention via a dedicated `causal_softmax` operator was tried and reverted** (`e29fdac`). Current supported path: true masked softmax (`ConstructedMaskedSoftMax`, masks with `-inf` before `torch.softmax`) or `normalize(scores * mask)` (`ConstructedMaskedNormalize`) — the latter has a real numerical failure mode (a masked-out key dominating the unmasked softmax can underflow causal positions to ~machine-epsilon, and `clamp(min=1e-8)` then means rows no longer sum to 1). Check this history before reintroducing dedicated causal-softmax support.
- **`operators.py` is dead** (0 bytes) — operator classes live in `data_structure.Operators`, not here.
- **Repeated-axis Iverson predicates allocate N^k-sized buffers, not N-sized** (documented "PERFORMANCE TRADEOFF" in `materialise.py`) — deliberate, since caller-supplied masks with repeated axes can't be pre-collapsed; the masked-softmax/normalize path is the exception (explicitly diagonal-collapsed before storing).
