# Boolean Semiring Extension

**Status:** Not yet implemented  
**Context:** Design notes for extending pyncd and tsncd to support the Boolean semiring `(𝔹, ∨, ∧)` alongside the existing arithmetic semiring `(ℝ, +, ×)`, enabling predicate tensors to be realised at the `Datatype` level rather than only at the axis-subtype level.

---

## Motivation

The tensor logic DSL currently encodes the Boolean vs arithmetic distinction at the axis level only: `.predicate()` declarations promote indices to `PredAxis`, and `T(x, y)` via `__call__` signals a predicate at the call site. However, `TensorEquation.bc_signature()` produces `Broadcasted[Reals, ...]` for all equations regardless of kind — the ∨/∧ semantics are not yet carried into the pyncd type system. A predicate einsum and an arithmetic einsum are indistinguishable in the resulting morphism.

Realising the full distinction requires:

1. A `Bool` datatype in pyncd
2. `bc_signature()` emitting `Broadcasted[Bool, ...]` for predicate equations
3. The `Einops` operator encoding which semiring it uses
4. Rendering support in both pyncd and tsncd

---

## Design

### 1. `Bool` datatype in pyncd

Add a `Bool` frozen dataclass alongside `Reals` and `Natural` in `data_structure/BroadcastedCategory.py`:

```python
@dataclass(frozen=True)
class Bool(Datatype):
    pass
```

No parameters are needed — unlike `Natural(max_value=n)`, Boolean tensors carry no size constraint beyond the shape axes.

### 2. `bc_signature()` dispatch

`TensorEquation.bc_signature()` already accepts a `datatype` argument (`datatype: B = Reals()`). The propagation path is:

- `TensorProgram.to_morphism()` detects PREDICATE declarations and passes `datatype=Bool()` to `bc_signature()` for the corresponding equation.
- Alternatively, `TL.to_morphism()` handles the dispatch directly by inspecting `TL._declarations` before calling `to_program().to_morphism()`.

This produces `Broadcasted[Bool, RawAxis, TensorEquation]` for predicate equations and leaves all arithmetic equations as `Broadcasted[Reals, ...]`.

### 3. Semiring on the `Einops` operator

The contraction *structure* (degree, weaves, reindexings) is identical for both semirings; only the reduction operation differs (`+`/`×` vs `∨`/`∧`). The preferred approach is a `semiring` field on `Einops` rather than a separate `BoolEinops` class:

```python
from enum import Enum

class Semiring(Enum):
    ARITHMETIC = 'arithmetic'
    BOOLEAN    = 'boolean'

@dataclass(frozen=True)
class Einops(Operator):
    signature: str    = ''
    semiring:  Semiring = Semiring.ARITHMETIC
```

`bc_signature()` sets `semiring=Semiring.BOOLEAN` when `datatype=Bool()`. This localises the ∨/∧ vs +/× distinction in one field without duplicating the structural machinery. Display and code generation branch on this field to render the operator differently.

### 4. Notation alignment

With the above, the DSL notation, Python mechanism, and pyncd type are in one-to-one correspondence:

| DSL syntax | Python hook | `Broadcasted` datatype | `Einops` semiring |
|---|---|---|---|
| `T[i, j]` | `__getitem__` | `Reals` | `ARITHMETIC` |
| `T(x, y)` | `__call__` | `Bool` | `BOOLEAN` |
| `T.lookup(d)` | method | `Natural(max_value=n)` | — (`Embedding` operator) |

---

## Rendering

Three aspects of the diagram can distinguish Boolean morphisms from arithmetic ones, in increasing implementation cost.

### 1. Equation string inside the operator box

The highest-signal change. Instead of `Σ`/`×` notation, Boolean equations render with `∃`/`∧`:

```text
Y[i,z] = Σ_k  W[i,k] × X[k,z]    ← arithmetic
Y(x,z) = ∃_y  R(x,y) ∧ S(y,z)    ← boolean
```

The `()` bracket notation already distinguishes kinds at the call site; carrying it through to the rendered string makes it visible inside the diagram box itself. This requires `TensorEquation` to produce its display string in a semiring-aware way — `Einops.semiring` (from the design above) provides the necessary field.

### 2. Wire styling for `Bool` arrays

Dashed lines are a standard convention for discrete/Boolean types in categorical diagrams, contrasting with solid lines for continuous `Reals`. However, tsncd already uses a `'5,5'` dash pattern on broadcaster separator curves (the lines dividing product elements in `Separated<T, S>`). Reusing the same pattern for Boolean wires would create a visual collision.

Two ways to avoid it:

- **Different dash pattern.** The `'5,5'` separator reads as "dashed"; Boolean wires could use `'2,6'` (short dot, long gap), which reads distinctly as "dotted" — a conventional signal for discrete types and perceptually different at a glance.
- **Color instead of dashing.** A solid wire in a distinct hue avoids the collision entirely. The `Natural` anchor already uses lime-green; a complementary color on the wire ties it visually to the `𝔹` anchor without ambiguity. Color communicates semantic type more naturally than stroke pattern, and the existing separator dashes are structural (they mark composition boundaries) — a type annotation should look different in kind, not just degree.

The most robust option is both: a `'2,6'` dotted stroke in a distinct color, redundantly encoding the distinction so it reads correctly in greyscale and for users who notice only one cue. Of the two alone, color is preferred.

### 3. `𝔹` datatype anchor

tsncd renders datatypes explicitly only for `Natural` — via a `DatatypeAnchor` (lime-green border, curved line with triangle arrow, LaTeX max-value annotation). `Reals` produces no visual element. A bare `Bool` would be equally invisible without an explicit rendering branch.

**`tsncd/src/data_structure/BroadcastedCategory.ts`**  
Add the TypeScript mirror class:

```typescript
export class Bool extends Datatype {}
```

**`tsncd/src/display/Framework/BroadcastedCategoryRenderer.ts`**  
Add an `instanceof cat.Bool` branch alongside the existing `Natural` check (currently around line 96):

```typescript
if (this.target.datatype instanceof cat.Bool) {
    this.datatype_anchor = new DatatypeAnchor(categoryRenderer, this.target.datatype);
}
```

The `DatatypeAnchor` displays a `𝔹` annotation rather than a numeric max-value, following the same curved-line-with-triangle-arrow visual convention used for `Natural`.

**pyncd text renderer (`display/node_category.py`)** requires no changes: the `datatype()` function renders the first two characters of the class name, so `Bool()` appears as `"Bo"` automatically.

---

The combination of dashed wires and `∃`/`∧` in the equation string gives an unambiguous visual language: a Boolean morphism is identifiable from either the wires entering and leaving it or the label inside the box.

---

## DSL simplification

The key simplification is that `PredAxis` becomes redundant and can be removed entirely.

Currently `PredAxis` exists as a workaround: because `bc_signature()` produces `Broadcasted[Reals, ...]` for all equations, the only way to preserve any trace of "this index belongs to a Boolean tensor" in the resulting morphism is to mark it at the axis level. `_pred_wrap()`, the PREDICATE branch in `TensorProxy._promote()`, and `PredAxis` itself all exist to carry a signal that `Bool` on the weave would carry directly and more correctly.

With `Bool` support the picture collapses to:

```python
# Before: declaration triggers axis promotion at __call__ time
tl.Mask.predicate(real_axis('q'), real_axis('x'))
tl.Comp[h, q, x] = tl.Mask(q, x) * tl.Query[q, h, k] * tl.Key[x, h, k]
# → PredAxis promotion; Broadcasted[Reals, ...] with PredAxis markers

# After: declaration is a pure kind annotation; __call__ triggers Bool datatype
tl.Mask.predicate(real_axis('q'), real_axis('x'))
tl.Comp[h, q, x] = tl.Mask(q, x) * tl.Query[q, h, k] * tl.Key[x, h, k]
# → plain RawAxis throughout; Broadcasted[Bool, ...] for the Mask factor
```

The call-site syntax is identical but the internal machinery simplifies:

- `PredAxis` dataclass — deleted
- `_pred_wrap()` — deleted
- PREDICATE branch in `TensorProxy._promote()` — reduces to the same no-op as TENSOR (arity check only, no promotion)
- `TensorProxy.__call__` — new method, mirrors `__getitem__` but passes `datatype=Bool()` to `bc_signature()`

The distinction migrates from the axis subtype (a structural marker baked into every index object) to the `Weave` datatype (where it semantically belongs and where pyncd already knows how to interpret it). The `.predicate()` declaration stays — it still drives the arity check and signals `__call__` as the expected access pattern — but it no longer needs to reshape the axis objects themselves.

---

## Summary of changes

| File | Change |
|---|---|
| `pyncd/data_structure/BroadcastedCategory.py` | Add `Bool` dataclass; add `Semiring` enum |
| `pyncd/data_structure/Operators.py` | Add `semiring` field to `Einops` |
| `pyncd/data_structure/TensorLogic.py` | `bc_signature()` passes `Bool()`/`Semiring.BOOLEAN` for predicate equations |
| `pyncd/data_structure/TensorDSL.py` | Remove `PredAxis`, `_pred_wrap()`, PREDICATE promotion branch; add `TensorProxy.__call__`; dispatch on PREDICATE kind in `TL.to_morphism()` |
| `pyncd/display/node_category.py` | No changes needed |
| `tsncd/src/data_structure/BroadcastedCategory.ts` | Add `Bool` class |
| `tsncd/src/display/Framework/BroadcastedCategoryRenderer.ts` | Add `instanceof cat.Bool` rendering branch |
