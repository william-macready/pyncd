# Weaves, Wires, and Morphisms: Overview

Abbott & Zardini (MIT LIDS), arXiv:2604.07242v2, April 2026.

---

## Motivation

PyTorch's broadcasting semantics, inherited from NumPy, are informal and difficult to reason about mathematically. This paper provides a categorical framework in which deep learning models are **algebraic terms** — formal expressions built from a small set of construction rules. The same term simultaneously supports:

- **Executable compilation** to PyTorch (via pyncd) or other targets
- **Diagrammatic rendering** as Neural Circuit Diagrams (via tsncd)
- **Algebraic manipulation** using category-theoretic rewriting

The key insight formalizes broadcasting — running an operation in parallel over additional axes — as a categorical construction expressible in terms of the axis-stride category **St** and the array-broadcasted category **Br**.

---

## The Term System

**Paper:** Section 2 — **Python:** [data_structure/Term.py](../data_structure/Term.py)

A term language provides a representational interface to the categorical ingredients (entities). Every object in this language is a **term**, and terms are constructed compositionally from simpler terms.

Mathematical entities are distinct from the concrete terms used to represent them so that the same underlying entity can be expressed as notation, a diagram, or code.

### Mathematical Encoding

**Γ** is a set of **mathematical entities**. These entities are objects, morphisms or products of either. Γ has a family of k-indexed **core properties** $π_k: Γ_{k,i} → Γ_{k,f}$, the basic structure maps that define what entities can do. These include k=dom, k=cod, k=composition, k=⊗ (monoidal product), etc.

A **constructed term system** is the representation layer: a set G of terms and an **interpretation function** V_G: G → Γ that says which mathematical entity each term denotes. For each core property π_k, the term system provides an internal counterpart p_k: G_{k,i} → G_{k,f} such that evaluating inside the term system agrees with evaluating in Γ after interpretation (soundness).

Terms fall into two kinds:

- **Construction rules** T_c: G_{c,i} → G_{c,f} — contravariant implementations of a chosen subset C ⊆ K of core properties. Each has a **recovery function** T̂_c: img(T_c) → G_{c,i} satisfying T̂_c ∘ T_c = Id, meaning the inputs that built the term can always be recovered from it. These are the data-wrapper terms.

- **Root terms** G_r — terms for non-constructed core properties. Rather than storing inputs, a root term carries **metadata** tags from which all relevant properties can be derived. Root terms correspond to "seed" or "primitive" morphisms in the category.

**Placeholder terms** are partially-instantiated terms with open slots represented by UIDs. A UID is a unique identifier that acts as a free variable in an expression: imposing the equation uid_a = uid_b unifies the two slots, propagating through the term. This is the mechanism behind autoalignment: two terms composed via `@` have their boundary axes unified by merging UIDs.

| Math concept | Python class | Notes |
|---|---|---|
| Construction rule / term | `Term` | Frozen `@dataclass`; reconstructable from fields |
| UTerm (term with identity) | `UTerm` | Adds `uid: UID[Self]` field |
| Unique identifier | `UID[T]` | Random int + optional `DynamicName` |
| Named variable | `DynamicName` | Body string + subscript chain + display settings |
| Immutable sequence Π_i T | `Prod[T]` | Type alias for `tuple[T, ...]` |
| Equality / axis alignment | `EqualityClass`, `Context` | Merges UIDs to declare axes equal |

`DynamicName` handles LaTeX rendering: `DynamicName('h', subscript=DynamicName('2'))` renders as h₂. `Context` accumulates equality classes and applies them to substitute canonical UTerms throughout an expression — this is how `@` alignment works.

---

## The Product Category Framework

**Paper:** Section 3 — **Python:** [data_structure/ProductCategory.py](../data_structure/ProductCategory.py)

The paper defines a **product category** as a categorical skeleton that can be instantiated with different choices of object type and root morphism type. The Python type alias captures the full grammar:

```python
type ProdCategory[L, M: Morphism] = (
    M
    | Rearrangement[L]
    | Composed[L, ProdCategory[L, M]]
    | ProductOfMorphisms[L, ProdCategory[L, M]]
    | Block[L, ProdCategory[L, M]]
)
```

Any morphism in a product category is one of five things: a root morphism, a rearrangement, a sequential composition, a parallel product, or a decorated block.

### Objects

**Objects** are products of atomic objects of type `L`:

- **Math:** Π_{i∈I} L_i — an ordered tuple of elements from the object type `L`
- **Python:** `ProdObject[L]` — wraps `content: Prod[L]` = `tuple[L, ...]`

The object `ProdObject(())` is the unit object **1**. The identity morphism on any object is a `Rearrangement` with mapping `(0, 1, 2, ...)`.

### Morphisms

There are five morphism forms. The first two are the core primitives; the remaining three are structural.

**1. Root morphisms** `M` — the category-specific primitive operations. Abstract in `ProductCategory`; concretely `StrideMorphism` in **St** and `Broadcasted` in **Br**.

**2. Rearrangements** `Rearrangement[L]` — morphisms that permute, copy, or delete components of a product object without invoking any root morphism. A rearrangement is identified by an integer tuple `mapping: Prod[int]` that indexes the domain: `apply(target) = (target[i] for i in mapping)`. Deletion is expressed by omitting an index; copying by repeating it.

**3. Sequential composition** `Composed[L, M]` — a tuple of morphisms f₁, f₂, ..., fₙ applied left-to-right (diagrammatic order). `dom()` is the domain of the first; `cod()` is the codomain of the last.

**4. Parallel product** `ProductOfMorphisms[L, M]` — morphisms f₁ × f₂ × ... × fₙ applied simultaneously on disjoint sub-products. `dom()` and `cod()` are the concatenations of the individual domains and codomains.

**5. Block** `Block[L, M]` — a morphism decorated with display metadata (`title`, `fill_color`) and a `repetition` count (e.g., "×6" for a stacked transformer layer). Blocks are transparent to the categorical semantics; they pass `dom()` and `cod()` through from their body.

---

## The Axis-Stride Category **St**

**Paper:** Definition 8 — **Python:** [data_structure/StrideCategory.py](../data_structure/StrideCategory.py)

**St** is an elemental Cartesian product category. Its role is to describe array *shapes* and the *coordinate transforms* between them, independently of any array data.

### Objects

**Objects** in **St** are **axes** and products of axes:

- A lone object is an **axis** `A` — a UTerm carrying a UID and a size `|A| ∈ ℕ`. The UID serves as the axis's identity across an expression; the size is itself a `FreeNumeric` (another UTerm) until configured.
- A product object `Π_{i∈I} A_i ∈ Ob**St**` is a **shape** — the set of all possible multi-index coordinates `(a_i)_{i∈I}` of an array.
- The unit object **1** is the empty product, corresponding to a scalar shape.

In Python, `Axis` is the abstract base (`UTerm`); `RawAxis` is the concrete subclass used for unspecialized axes. `Axis.named('h')` creates an axis whose UID carries the name `h` and whose size is a free numeric also named `|h|`.

### Morphisms

**Morphisms** in **St** are **finite affine transforms**: maps η: Π_{i∈I} A_i → Π_{j∈J} B_j that describe how input coordinates relate to output coordinates. Each output coordinate j is a linear combination of input coordinates plus a bias:

```
(∏_{i∈I} a_i) ∘ η = ∏_{j∈J} (v^η_j + Σ_{i∈I} Λ^η_{ij} · a_i)
```

where Λ^η is an ℕ^{I×J} matrix and v^η is an ℕ^J vector. The image must land within the codomain.

In Python, `StrideMorphism` stores `_dom: Prod[Axis]`, `_cod_stride: Prod[tuple[Axis, Prod[Numeric]]]` (each output axis paired with its coefficient row), and an optional name. `StrideMorphism.from_matrix((1, 1), dom_names=("x'", "w"), cod_names=("x",), name="+")` creates the convolution-shift transform x = x' + w.

The identity, permutation, diagonalization (η(p) = (p, p)), and deletion (η = ()) are all special cases of affine transforms and appear as `Rearrangement` morphisms in **St**.

---

## The Array-Broadcasted Category **Br**

**Paper:** Definitions 9–13 — **Python:** [data_structure/BroadcastedCategory.py](../data_structure/BroadcastedCategory.py), [data_structure/Operators.py](../data_structure/Operators.py)

**Br** is the category of deep learning models. It is a deletion product category, capturing both deterministic (**Set**) and probabilistic (**Stoch**) computation.

### Objects

**Objects** in **Br** are **arrays** `[a, A]`:

- `a ∈ Dt` is a **datatype** — the kind of value stored at each coordinate. Common datatypes are `Reals` (continuous, differentiable) and `Natural(max_value)` (discrete, used for token indices in embeddings).
- `A ∈ Ob**St**` is a **shape** — a product of axes that indexes the array's coordinates.
- An array `[a, A]` has an `El(A)`-family of values `x_{i_A} ∈ a` for each coordinate `i_A ∈ El(A)`.

A product object `Π_{i∈I} [a_i, A_i]` in **Br** is a tuple of arrays — the inputs or outputs of an operation.

In Python, `Array[B, A]` stores `datatype: B` and `_shape: Prod[A]`. `Reals()` and `Natural.template('v')` are the concrete datatypes. Objects are generally not constructed directly; they are computed from morphism `dom()` and `cod()` methods.

### Morphisms

**Morphisms** in **Br** are **broadcasted operations** `F: Π_{i∈I} [a_i, A_i] → Π_{j∈J} [b_j, B_j]`.

A broadcasted operation is built from four ingredients (Definition 13):

1. **A base operation** `f: Π_{i∈I} [a_i, A_i] → Π_{j∈J} [b_j, B_j]` in **Br** — the core computation. In code this is an `Operator` subclass (e.g., `Linear`, `Einops`, `SoftMax`).

2. **Reindexings** `(η_i)_{i∈I}` from **St** — affine transforms that relate the *degree* shape P (the batch/tiling shape) to each input's tiled shape Q_i. These describe which input coordinates are functions of the batch index. In Python, stored as `reindexings: Prod[StrideCategory[A]]` on `Broadcasted`.

3. **Input weaves** `(s_i)_{i∈I}` — for each input array, a **weave** partitions its axes into *target* axes (w=1, front) and *tiling* axes (w=0, back). Target axes carry the base operation's data; tiling axes are the broadcasted batch dimensions. In Python, `Weave[B, A]` stores a `_shape: Prod[A | WeaveMode]` where `WeaveMode.TILED` marks tiled positions and actual `Axis` objects mark target positions.

4. **Output weaves** `(t_j)_{j∈J}` — same structure for outputs, specifying which output axes are tiling (from the degree P) and which are target (from the base operation's output shape).

The full shape of the broadcasted operation is:

```
F: Π_{i∈I} [a_i, dom([Ω_{s_i}]_{A_i ⊗ Q_i})] → Π_{j∈J} [b_j, dom([Ω_{t_j}]_{B_j ⊗ P})]
```

In Python:

```python
@dataclass(frozen=True)
class Broadcasted[B: Datatype, A: Axis, O: Operator](Morphism[Array[B, A]]):
    operator:       O
    input_weaves:   Prod[Weave[B, A]]
    output_weaves:  Prod[Weave[B, A]]
    reindexings:    Prod[StrideCategory[A]]
```

`dom()` is computed from input weaves + reindexing codomains; `cod()` from output weaves + the shared degree P (= `reindexings[i].dom()`, which must be equal for all i).

### Key special cases

| Operation | How it appears in Br |
|---|---|
| Row-wise (batch) operation | Reindexing is identity; tiling axis = batch axis |
| Transposition | `Rearrangement` with swapped mapping |
| Diagonalization `y[p,:] = x[p,p,:]` | Reindexing η(p) = (p, p) |
| Repetition `y[p,:] = x[:]` | Reindexing η = () (deletion) |
| Einsum contraction | `Einops` operator with matching weaves |
| Linear layer | `Linear` operator; input and output weaves declare hidden/output axes |
| Convolution | `StrideMorphism` for the shift (x' + w) composed with `Linear` |

---

## Autoalignment via `@`

**Paper:** Section 5.1.1 — **Python:** [construction_helpers/composition.py](../construction_helpers/composition.py)

The `@` operator overloads `Morphism.__matmul__` to compose two morphisms with automatic axis alignment. When the codomain of the left morphism and the domain of the right morphism differ in the number of axes, identity morphisms (via `morphism_object_lift`) are inserted at the top or bottom to reconcile the mismatch. Once both sides have the same number of axes, a `Context` is built by pairing axes positionally and adding equality classes. Applying the context substitutes canonical UIDs throughout the composed expression, unifying named axes.

For example:

```python
qk_matmul @ softmax @ mask @ sv_matmul
```

At each `@`, the codomain axes of the left term are aligned with the domain axes of the right term. If `qk_matmul` outputs axes `[h, q, x]` and `softmax` generates a fresh unnamed axis that autoalignment then renames, the UID equality class merges the two and the composed expression has consistent axis identities.

---

## Concrete Operators

**Python:** [data_structure/Operators.py](../data_structure/Operators.py)

Operators are `Operator` subclasses (frozen dataclasses) that implement `bc_signature()` or `template()` to produce a fully-specified `Broadcasted` morphism:

| Operator | Description |
|---|---|
| `Einops.template('q h k, x h k -> h q x')` | General einsum; parses signature into weaves and reindexings |
| `Linear.template(input_size, output_size, name)` | Learned linear layer; tiling = all axes, target = input/output axes |
| `SoftMax.template()` | Normalization; input and output share one target axis |
| `Elementwise.template()` | Elementwise nonlinearity (sigmoid, ReLU, etc.) |
| `Normalize.template()` | RMSNorm; same shape in and out |
| `Embedding.template(vocab_size)` | Discrete → real map; input datatype is `Natural` |
| `AdditionOp.template()` | Elementwise addition of two arrays of the same shape |
| `WeightedTriangularLower.template()` | Causal mask; used in attention |

---

## End-to-End Example: Transformer

**Python:** [minimum_working_example.py](../minimum_working_example.py)

The transformer is built by composing the operators above:

```python
# Attention core: qk multiply → softmax → mask → sv multiply
qk_matmul = ops.Einops.template('q h k, x h k -> h q x')
softmax   = ops.SoftMax.template()
mask      = ops.WeightedTriangularLower().template()
sv_matmul = ops.Einops.template('h q x, x h k -> q h k')
_attention_core = Block.template(
    qk_matmul @ softmax @ mask @ sv_matmul,
    title='Attention Core', fill_color='#C5BEDF'
)

# Attention layer: project Q, K, V → attention core → project output
Lq = ops.Linear.template(('m',), 2, 'q')      # [x, m] → [x, h, k]  (2 output axes)
Lk = ops.Linear.template(('m',), 2, 'k')
Lv = ops.Linear.template(('m',), 2, 'v')
Lo = ops.Linear.template(2, ('m',), 'o')       # [h, k] → [m]
_attention_layer = (Lq * Lk * Lv) @ _attention_core @ Lo

# Transformer layer: attention + FFN, each with residual + norm, repeated 6 times
_transformer = Block.template(
    res(_attention_layer) @ res(ffn_layer()),
    title='Transformer Layer', repetition=6
)

# Full model: embedding → 6× transformer → aggregator
_transformer_model = embedding @ _transformer @ aggregator
```

Each `*` creates a `ProductOfMorphisms` (parallel); each `@` creates a `Composed` with autoalignment. The result is a single algebraic term that can be:

- Sent as JSON via WebSocket to the TypeScript renderer (`wst.send_term(...)`)
- Printed as a category diagram (`dpl.print_category(...)`)
- Compiled to a PyTorch module (via `torch_compile/`)

---

## Math-to-Python Reference

| Paper definition | Python class / function | File |
|---|---|---|
| Term (construction rule) | `Term` | `data_structure/Term.py` |
| UTerm (with UID) | `UTerm` | `data_structure/Term.py` |
| Unique identifier | `UID[T]` | `data_structure/Term.py` |
| Named variable | `DynamicName` | `data_structure/Term.py` |
| Immutable sequence Π_i T | `Prod[T]` | `data_structure/Term.py` |
| Equality class / alignment | `EqualityClass`, `Context` | `data_structure/Term.py` |
| Product category grammar | `ProdCategory[L, M]` | `data_structure/ProductCategory.py` |
| Product object Π_i L_i | `ProdObject[L]` | `data_structure/ProductCategory.py` |
| Root morphism | `Morphism[L]` (abstract) | `data_structure/ProductCategory.py` |
| Sequential composition | `Composed[L, M]` | `data_structure/ProductCategory.py` |
| Parallel product | `ProductOfMorphisms[L, M]` | `data_structure/ProductCategory.py` |
| Rearrangement [μ] | `Rearrangement[L]` | `data_structure/ProductCategory.py` |
| Block (grouped subterm) | `Block[L, M]` | `data_structure/ProductCategory.py` |
| Axis A with size \|A\| (Def 8) | `Axis` / `RawAxis` | `data_structure/StrideCategory.py` |
| Shape Π_{i∈I} A_i (Def 8) | `ProdObject[Axis]` | `data_structure/StrideCategory.py` |
| Finite affine transform (Def 8) | `StrideMorphism` | `data_structure/StrideCategory.py` |
| Datatype a ∈ Dt (Def 9) | `Datatype`, `Reals`, `Natural` | `data_structure/BroadcastedCategory.py` |
| Array [a, A] (Def 9) | `Array[B, A]` | `data_structure/BroadcastedCategory.py` |
| Weave w_i ∈ {0,1} (Def 12) | `Weave[B, A]`, `WeaveMode` | `data_structure/BroadcastedCategory.py` |
| Broadcasted operation F (Def 13) | `Broadcasted[B, A, O]` | `data_structure/BroadcastedCategory.py` |
| Base operator f | `Operator` subclass | `data_structure/Operators.py` |
| Autoalignment via composition | `composition`, `align_composed` | `construction_helpers/composition.py` |
| `@` operator | `Morphism.__matmul__` | `construction_helpers/composition.py` |
| Batch lift [f, P] (Def 11) | Product structure of `Broadcasted` | `data_structure/BroadcastedCategory.py` |
| Reindexing [a, η] (Def 10) | `reindexings` field of `Broadcasted` | `data_structure/BroadcastedCategory.py` |
