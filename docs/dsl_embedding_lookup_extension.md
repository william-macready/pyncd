# DSL Extension: Embedding Lookups

**Status:** Deferred  
**Context:** Extension of `data_structure/TensorDSL.py` to express embedding/selection operations as first-class DSL equations, rather than falling back to `ops.Embedding.template()`.

---

## Motivation

The tensor logic DSL can already declare a tensor as a selection:

```python
tl.E.selection(nat_axis('v', 50257), real_axis('d', 512))
```

This annotation records that `E` is an embedding table indexed by a ℕ dimension into a ℝ dimension. However, the actual computation is still expressed as `ops.Embedding.template(vocab_size)` — an opaque operator outside the DSL. Ideally the same equation notation used for contractions would express the lookup:

```python
tl.Out[d] = tl.E[tl.token, d]
```

making the embedding a transparent, first-class equation with explicit type information, consistent with how contractions are written.

---

## How pyncd Represents Lookups

`ops.Embedding.template(vocab_size)` produces:

```python
Broadcasted(
    operator=Embedding(name='E'),
    input_weaves=(Weave(Natural(vocab_size), ()),),  # 0D Natural input — the token ID
    output_weaves=(Weave(Reals(), (d_axis,)),),       # 1D Reals output — embedding vector
    reindexings=(ProdObject().identity(),),           # empty identity
)
# degree = ()  ← no axes; this is a per-token, point-level operation
```

Key properties:
- The vocabulary dimension `v` is **not a shape axis** — it is the `Natural(vocab_size)` *datatype* of the input weave. It disappears into the type.
- The token ID is the **morphism domain itself** (a scalar Natural), not an indexed tensor.
- The embedding dimension `d` is a concrete axis in the output weave.
- The degree is **empty** — there is no sequence position `p`.

---

## The Sequence Dimension Problem

The first natural syntax attempt would be:

```python
tl.Out[p, d] = tl.E[tl.token[p], d]
```

This makes `p` (sequence position) explicit in the lookup, producing a `Broadcasted` with degree `(p, d)` and `cod = [Array(Reals, (p_axis, d_axis))]`.

**This breaks composition with the rest of the transformer.**

The `align_axes` function in `construction_helpers/composition.py` aligns axes strictly positionally and requires equal axis counts:

```python
if len(left_axes) != len(right_axes):
    raise ValueError("Cannot align axes of different lengths")
```

The downstream `transformer_core()` expects a 1-axis input `[Array(Reals, (m_axis,))]`. A 2-axis output `[Array(Reals, (p_axis, d_axis))]` cannot be aligned with it.

---

## Why `p` is Absent from the Embedding

The pyncd transformer has no single sequence-position axis `p` that threads through all layers. The sequence dimension is:

- **Absent** from the embedding, linear projections (Lq, Lk, Lv, Lo), and FFN — all of these are **point-level** (per-token) operations.
- **Explicit** only at the attention level, where `q` (query positions) and `x` (key positions) are introduced by `TensorEquation` axes.

Composition via `@` and auto-alignment in `construction_helpers` applies each point-level morphism independently across token positions. The attention core is the only layer that reasons about relationships *between* positions.

A DSL lookup equation must therefore also be point-level — no `p` in the degree — to compose correctly.

---

## Viable Syntax

The correct per-token syntax would be:

```python
tl.Out[d] = tl.E[tl.token, d]
```

where `tl.token` (unsubscripted — no `[...]`) represents the Natural-typed **morphism domain**, not a positionally indexed tensor. This would produce:

```python
Broadcasted(
    operator=Embedding(name='E'),
    input_weaves=(Weave(Natural(vocab_size), ()),),
    output_weaves=(Weave(Reals(), (WeaveMode.TILED,)),),
    reindexings=(Rearrangement(mapping=(0,), _dom=(d_axis,)),),
)
# degree = (d_axis,)
```

which aligns correctly with the downstream linear projections.

---

## Implementation Scope

No pyncd changes are required. All changes are confined to `TensorDSL.py` and `TensorLogic.py`.

**`TensorDSL.py`:**
- `LookupSlot` — wrapper produced when an unsubscripted `TensorProxy` appears as a subscript in another tensor's `__getitem__`.
- `LookupIndexedTensor` — returned by `TensorProxy.__getitem__` when a `LookupSlot` is detected among the indices.
- Updated `TensorProxy.__getitem__` — detect `TensorProxy` (unsubscripted) in the index tuple and wrap as `LookupSlot`.
- Updated `TensorProxy.__setitem__` — detect `LookupIndexedTensor` on RHS and create `TensorLookup` instead of `TensorEquation`.

**`TensorLogic.py`:**
- `TensorLookup` dataclass — stores `(lhs_name, lhs_indices, table_name, selected_axis, passthrough_axes)`.
- `TensorLookup.bc_signature()` — produces the per-token `Broadcasted` using `Natural(vocab_size)` as the input datatype. The `vocab_size` is read from the declaration: `tl.E.selection(nat_axis('v', 50257), ...)` stores the `NatAxis` with `Integer(50257)` as `_size`, which becomes `Natural(Integer(50257))`.

**`TL`:**
- `_register` must accept both `TensorEquation` and `TensorLookup`.
- `to_equation()` / `to_program()` must handle the mixed list.

---

## Open Questions

1. **`TensorProgram` with mixed equation types.** `to_morphism()` currently handles only `TensorEquation`. If a program mixes contractions and lookups (e.g., FFN equations plus an embedding lookup), `to_morphism()` needs to dispatch on type. The topological sort in `_topological_sort` already operates on names and would work unchanged; only `bc_signature()` dispatch changes.

2. **Undeclared lookup.** If `tl.E` has no `.selection()` declaration, there is no `Natural(vocab_size)` to put in the input weave. Options: require a declaration, infer from context, or raise at `bc_signature()` time.

3. **Multiple passthrough axes.** `tl.Out[d1, d2] = tl.E[tl.token, d1, d2]` — multiple passthrough axes — should work by extending the degree and output weave accordingly, but needs verification.

4. **Aggregator (inverse direction).** The aggregator `ops.Linear.template(1, (vocab_size,)) @ ops.SoftMax.template()` maps a real vector to a Natural-sized distribution. This is the reverse direction — a projection into vocabulary space. Whether this warrants a symmetric DSL form (e.g., `tl.Logits[v] = tl.W[v, d] * tl.h[d]` with `W` declared as a selection) is unresolved.
