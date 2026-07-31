# construction_helpers

## Purpose
Owns: the ergonomic operator layer over `data_structure`'s categorical primitives — `@` (composition), `*` (product), `>>` (batch lifting), and einops-/named-signature string parsing. It attaches these as dunder methods directly onto `data_structure.Category` classes (`Morphism.__matmul__`, `Datatype.__mul__`, `Morphism.__rrshift__`) — the base classes have no operators of their own until this package is imported.
Does not own: any new data types — this is purely a construction/orchestration layer over `data_structure/` (see that dir's `AGENTS.md`).

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| `@` composition semantics, axis alignment | `composition.py` — `composition()`, `align_axes()` |
| Cross-instance / reordered composition fix | `composition.py` — `_array_signature()`, `_find_composition_reordering()` |
| `*` product semantics | `product.py` — `object_product()`, `morphism_product()`, `general_product()` |
| `>>` batch lifting semantics | `lift.py` — `dynamic_object_lift()` |
| einops-style `"i j, j k -> i k"` parsing | `einops.py` — `signature_to_buckets()`, `bucketed_to_broadcast()` |
| named-signature parsing (broadcast/absorb/produce) | `signature.py` — `generic_signature()` |
| where operators get attached to base classes | bottom of each file: `cat.Morphism.__matmul__ = composition`, etc. |

### Key Relationships
Every file imports `data_structure.Category as cat`. `composition.py` imports `construction_helpers.product` and `.lift`; `lift.py` imports `construction_helpers.product`. `einops.py`/`signature.py` are standalone internally but consumed externally by `data_structure/Operators.py` to build operator templates. `Operators.py` also imports `construction_helpers.product` directly (`object_product`, `morphism_product`, `datatype_converter`, `axis_converter`, and the `ProductObjectTarget`/`ProductMorphismTarget` type aliases) for its own signature construction — so the reverse dependency covers `product.py` as well as the string-parsing helpers. Only `composition.py`/`lift.py` have no reverse dependency from `data_structure/`.

## Public API

### Key Exports
| Export | Used By | Change Impact |
|---|---|---|
| `composition()` / `cat.Morphism.__matmul__` | every `@` in every model file | Highest blast radius — bugs here silently mis-align axes everywhere |
| `object_product`/`morphism_product`/`general_product` / `cat.*.__mul__` | `*` throughout model files; used internally by `lift.py`; heavily used by `Operators.py` templates | Affects all parallel/product construction |
| `dynamic_object_lift()` / `cat.*.__rrshift__` | `>>` batch lifting | Governs how batch axes thread through morphisms |
| `signature_to_buckets`/`bucketed_to_broadcast`, `generic_signature` | `Operators.py` operator templates | Determines how string signatures become `Weave`/`Rearrangement` objects |

### Core Types
- `AxialObject` — the shape type used for axis alignment in `composition.py`.
- `ExcessProductSide` (Enum `TOP`/`BOTTOM`) — which side of a length-mismatched product is "excess."
- `SignatureMode` (Enum `SHORT`/`LONG`), `SignatureSegment` — signature-string parsing shapes.

## Entry Points
| Task | Start Here |
|------|------------|
| Understand why `@` composed two morphisms a certain way | `composition.py::composition()` (walk the 5-step pipeline in Patterns below) |
| Debug a `Datatype mismatch` / `Cannot align axes of different lengths` error | `composition.py::align_axes()` |
| Add a new einops-style or named-signature operator template | `einops.py::signature_to_buckets` or `signature.py::generic_signature`, consumed from `data_structure/Operators.py` |

## Contracts
- **Axis alignment**: composing `left @ right` zips `left.cod()`/`right.dom()` positionally and unifies axes via `ctx.append_iter`; mismatched datatypes raise `TypeError`, mismatched lengths raise `ValueError`.
- **Operator registration is an import side effect**: `@`/`*`/`>>` only work after the relevant submodule has been imported (monkey-patches `data_structure.Category` in place). Code using these operators implicitly depends on `construction_helpers` having been imported first — e.g. scripts import `construction_helpers as ch` purely for this side effect.
- **`excess_product`'s positional matching assumes the "extra" elements sit at a known contiguous end** (`TOP`/`BOTTOM`) — see Pitfalls, this broke under reordering.

## Patterns
- **`@` (composition)**: (1) wrap raw tuples as `Rearrangement`; (2) `add_excess_lift` right-lifts the smaller-rank side; (3) **reordering fix**: if `right.dom()` has more elements than `left.cod()`, `_find_composition_reordering` shape-matches (datatype + axis name/size) and inserts a corrective `Rearrangement` before falling through to positional matching; (4) `excess_product` splits genuine excess and lifts the other side; (5) `align_composed` flattens `Composed` chains and unifies axes.
- **`*` (product)**: funnels through `target_expand`, which recursively flattens tuples/`ProdObject`, drops empty `Rearrangement`s, and promotes bare `Datatype`→`Array` / `str`→`RawAxis` via a `conversion` callable.

## Pitfalls
- **Positional excess-matching breaks under reordered/cross-instance composition** (fix `c8267c9`): composing e.g. `attn_res() @ ffn_res()` where shared axes aren't at the expected end silently pairs the wrong axes, producing a runtime einsum subscript-size conflict rather than an error. Fixed by shape-based matching (`_array_signature`) that inserts a corrective `Rearrangement` — any future change to `excess_product` or `Array`/`RawAxis` internals must keep `_array_signature` in sync or the old positional bug resurfaces silently (falls back to `None`, no error raised).
- **`_array_signature` reaches into private fields** (`ax.uid._name.body`, `ax._size._value`) — a structural-equality workaround against `data_structure` internals, not a public API. Renaming those fields breaks composition reordering silently, without raising.
- **Greedy signature matching picks the first unused match** — if `right.dom()` has multiple elements with identical `(datatype, axes)` signatures, matching is ambiguous/order-dependent.
- **`excess_product`'s default side is `TOP`, but composition's main path calls it with `BOTTOM` explicitly**, while `add_excess_lift` uses the `TOP` default implicitly — two conventions coexist in the same function; read call sites carefully before changing either.
