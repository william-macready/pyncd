# data_structure

## Purpose
Owns: the category-theoretic core of pyncd — `Term`/`UID` identity machinery, the `BroadcastedCategory` (objects = `Array[Datatype, Axis]`, morphisms = `Broadcasted`), the affine `StrideCategory` (reindexing: identity/transpose/diagonal/convolution), concrete NN operators (`Linear`, `SoftMax`, `ReLU`, `Normalize`, ...), and the `TensorLogic`/`TensorDSL` einsum-like DSL that compiles into these same categorical objects.
Does not own: operator overloading (`@`/`*`/`>>`, see `construction_helpers/AGENTS.md`), PyTorch codegen (see `torch_compile/AGENTS.md`), rendering (see `display/AGENTS.md`), or ACSet/CSV serialization (see `acset/AGENTS.md`) — all of those import from here, never the reverse.

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| `Term`/`UTerm`/`UID`/`Context`/`EqualityClass` base machinery | `Term.py` |
| Numeric literals & symbolic sizes (`FreeNumeric`, `Integer`) | `Numeric.py` |
| `Axis`, `RawAxis`, `StrideMorphism` (affine reindexing) | `StrideCategory.py` |
| `NormAxis` (softmax axis), `NatAxis` (ℕ index) semantic tags | `AxisAnnotations.py` |
| `Datatype`, `Array`, `Weave`, `Broadcasted`, `Operator` | `BroadcastedCategory.py` |
| `Morphism`, `Composed`, `ThreadedComposed`, `ProductOfMorphisms`, `Rearrangement`, `Block` | `ProductCategory.py` |
| Umbrella re-export — **import this, not the leaves** | `Category.py` |
| Concrete NN operators: `Linear`, `Embedding`, `SoftMax`, `MaskedSoftMax`, `Normalize`, `MaskedNormalize`, `ReLU`, `Einops` | `Operators.py` |
| Iverson-bracket predicate trees, affine-index normalization | `TensorExpr.py` |
| `TensorEquation`, `TensorProgram`, topological sort | `TensorLogic.py` |
| `TL` DSL, `Scan`/`Slice`/`Reindex`/`Scatter` compiler entries | `TensorDSL.py` |

### Key Relationships
Import order (leaf → root): `Term.py` → `Numeric.py` → `StrideCategory.py`/`AxisAnnotations.py` → `ProductCategory.py` → `BroadcastedCategory.py` → `Category.py` (umbrella) → `Operators.py` → `TensorExpr.py` → `TensorLogic.py` → `TensorDSL.py`.
`Category.py` lazily re-exports `TensorEquation`/`TensorProgram` via `__getattr__` (PEP 562) instead of an eager import, to break the cycle `TensorLogic → Operators → Category → TensorLogic`.

## Public API

### Key Exports
| Export | Used By | Change Impact |
|---|---|---|
| `Category.py` (`Array`, `Broadcasted`, `Weave`, `StrideCategory`, `Morphism`, `Composed`, ...) | every other top-level package | Highest — renaming a re-exported name breaks the whole codebase |
| `TensorDSL.TL`, `axes`, `relu`, `softmax`, `normalize` | user-facing model-authoring (notebooks, `minimum_working_example_tl*.py`) | High — primary authoring surface |
| `TensorDSL.Scan`/`Slice`/`Reindex`/`Scatter` | `torch_compile/` (runtime lowering), `display/` (`Reindex` rendering) | High — compiler IR consumed directly downstream |
| `TensorExpr` private helpers (`_factor_axes`, `_serialize_iverson`) | `torch_compile/`, `acset/convert.py` | Medium — underscore-prefixed but imported across package boundaries |

### Core Types
- **`Term`/`UTerm`/`UID`** — every term is a frozen dataclass; `UTerm` adds identity via `UID`. Two axes are the *same axis* iff they share a UID — never compare by name.
- **`Axis`/`RawAxis`** — carries a symbolic `_size: Numeric`; `StrideMorphism` maps domain axes to `(axis, coefficient)` pairs (the affine engine).
- **`Array[B: Datatype, A: Axis]`** — object in `BroadcastedCategory`.
- **`Weave[B, A]`** — shape where each slot is a concrete `Axis` or `TILED` (filled at runtime from the shared "degree").
- **`Broadcasted`** — an `Operator` + `input_weaves`/`output_weaves`/`reindexings`.
- **`TensorEquation`** — one einsum-shaped RHS; `bc_signature()` derives the whole `Broadcasted` purely from axis UID identity.

## Contracts
- **UID identity is the only source of truth for "same axis"** — never rely on axis names for equality.
- **`lhs_indices` UIDs = retained axes; any UID only in `rhs` is summed over** — nothing statically prevents an axis appearing nowhere.
- **`Broadcasted.degree()` requires all `reindexings` to share the same domain** (`util.iallequals`); hand-built `Broadcasted`s must maintain this themselves.
- **`FreeNumeric` equality is by `uid._id`, not the `UID` object** (fix `d146fb6`: hashing the full `UID` broke round-trip equality after acset serialization — see `acset/AGENTS.md`). Any new `Numeric` subclass must hash a primitive, never a nested `Term`.
- **`Scan` base case must be at literal index `l=0`**; no `l+1` (next-step) reference is allowed on a recurrence RHS (`_check_no_lnext_on_rhs`).
- **`topological_sort`/`_topo_sort_entries` must raise `ValueError` on a short result** (cycle), not silently return a partial order (fix `c379cfe`) — a partial order fails later with a confusing `IndexError` instead.

## Entry Points
| Task | Start Here |
|------|------------|
| Author a model with the TL DSL | `TensorDSL.py` (`TL`, `axes`, `relu`, `softmax`, `normalize`) |
| Add a new NN operator (e.g. a new nonlinearity) | `Operators.py` — then register it in `torch_compile/AGENTS.md`'s `add_function`/`operation_registry` |
| Add a new `Axis`/`RawAxis` subclass | `AxisAnnotations.py` — then register it in `acset/AGENTS.md`'s UID type registry |
| Understand how `@`/`*`/`>>` are wired onto these types | `construction_helpers/AGENTS.md` (this dir defines the types, that dir defines the operators) |

## Patterns
- **Build a model with TL**: `TL()` → axes via `axes('i j k')`/`real_axis`/`norm_axis` → declare tensors (`tl.W.linear(...)`) → write equations `tl.Y[i,j] = tl.W[i,k]*tl.X[k,j]` → wrap nonlinearities `relu()`/`softmax(..., where=pred)` → `to_morphism()` (multi-equation) or `to_equation()` (single equation only).
- **Recurrences**: `tl.H[x,0] = base`, `tl.H[x,l+1] = recur` — DSL auto-detects base vs. recur shape; `_recognize_affine` tries an associative-scan decomposition. Multiple tensors sharing an iteration axis compile as one *coupled* Jacobi-style `Scan`.
- **Masked softmax/normalize**: `where=predicate` built from axis comparisons (monkey-patched onto `RawAxis` in `TensorExpr.py`); repeated-axis predicates are diagonal-collapsed (`_iverson_diagonal`) before alignment.

## Pitfalls
- **`Elementwise.template()` calls `cls()`, not `Elementwise()`** (fixes `d2efcef`, `3523d95`) so `ReLU`/`Dropout` subclasses keep their own operator name through composition — hardcoding `Elementwise()` at a new call site silently relabels every nonlinearity as generic sigma.
- **Scan step position tracking is easy to get backwards** (fixes `2853807`, `c9f09ac`): `Scan.step_x_l_positions` records where the iteration axis `l` appears in each per-step input because the runtime contract requires `l` last before slicing; wrong position silently transposes the wrong axis during unrolling.
- **Repeated-UID axes in one Iverson predicate need diagonal collapse** (fix `d4c28d6`) — skipping `_iverson_diagonal` before alignment silently produces a mask with the wrong rank.
- **`NormAxis`/`NatAxis` intentionally widen to `RawAxis` in `EqualityClass`** (fix `ffee350`) — this looks like it should require exact type match but doesn't; the annotation subclasses are purely semantic tags, treated identically to `RawAxis` by `bc_signature()`.
- **No dedicated `causal_softmax` operator exists** — one was tried and reverted (`e29fdac`). Causal masking is expressed via `softmax(expr, where=predicate)` (`MaskedSoftMax`). Check this history before re-adding one.
- **`ThreadedComposed` routing numbering is load-bearing**: indices `0..n_external-1` are caller inputs, `n_external+i` is step `i`'s output — any manual `ThreadedComposed` construction must match this exact convention or `torch_compile` feeds the wrong tensor into a step.
- **Coupled scans (`n_states > 1`) must be the terminal computation in a TL session** — `ThreadedComposed` feeds *all* of a step's outputs to the next module, so downstream equations consuming only a subset can't be chained correctly (documented limitation in `_finalize_iter_group`).
