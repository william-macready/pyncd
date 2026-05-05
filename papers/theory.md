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

$\Gamma$ is a set of **mathematical entities**. These entities are objects, morphisms, or products of either. $\Gamma$ has a family of $k$-indexed **core properties** $\pi_k : \Gamma_{k,i} \to \Gamma_{k,f}$, the basic structure maps that define what entities can do. These include $k = \mathrm{dom}$, $k = \mathrm{cod}$, $k = \mathrm{composition}$, $k = {\otimes}$ (monoidal product), etc.

A **constructed term system** is the representation layer: a set $G$ of terms and an **interpretation function** $V_G : G \to \Gamma$ that says which mathematical entity each term denotes (we also have $V_G^{-1} :\Gamma \to G$). For each core property $\pi_k$, the term system provides an internal counterpart $p_k : G_{k,i} \to G_{k,f}$ such that evaluating inside the term system agrees with evaluating in $\Gamma$ after interpretation (soundness).

Terms are of two kinds:

- **Root terms** $G_r$ — the atoms of the term system. A root term is not assembled from smaller recoverable inputs; instead it carries **metadata** tags from which all relevant core properties can be computed directly. Root terms represent primitive, irreducible concepts — the specific choices of lone objects and root morphisms that distinguish one product category from another. In pyncd, `Axis` (carrying a UID and a size), `StrideMorphism` (carrying domain, coefficient matrix, and bias), and `Broadcasted` (carrying operator, weaves, and reindexings) are all root terms.

- **Construction rules** $T_c : G_{c,i} \to G_{c,f}$ build terms from smaller pieces. The output term is a **data wrapper around its inputs**: $G_{c,f}$ literally embeds $G_{c,i}$ inside itself, which is what the paper calls *contravariant* — the output contains the input rather than being derived from it. This guarantees a **recovery function** $\hat{T}_c : \mathrm{img}(T_c) \to G_{c,i}$ satisfying $\hat{T}_c \circ T_c = \mathrm{Id}$: the inputs can always be unwrapped from the output. In pyncd, `Composed`, `ProductOfMorphisms`, `Rearrangement`, and `Block` are construction rules common to  every product category.

A **UTerm** (uniquely-identified term) is a term that carries a **UID** — a randomly-generated integer identifier — as one of its fields. The UID is the term's identity: two UTerms with the same UID are treated as the same entity everywhere in an expression, regardless of other field values. Plain `Term`s have no UID because their identity is fully determined by their contents. UTerms include `Axis`, `BlockTag`, and `FreeNumeric` — things whose identity must be tracked independently of their current field values.

**Placeholder terms** are partially-instantiated terms with open slots represented by UIDs. A UID acts as a free variable in an expression: imposing $\mathrm{uid}_a = \mathrm{uid}_b$ unifies the two slots and propagates the substitution through the term. This is the mechanism behind autoalignment: two terms composed via `@` have their boundary axes unified by merging UIDs.

Terms are represent in pyncd as follows:

| Math concept | Python class | Notes |
| --- | --- | --- |
| Construction rule / term | `Term` | Frozen `@dataclass`; reconstructable from fields |
| UTerm (term with identity) | `UTerm` | Adds `uid: UID[Self]` field |
| Unique identifier | `UID[T]` | unique id + optional name (for readability); `T` is the `UTerm` subclass being identified (e.g. `UID[Axis]`), stored as `_type: Type[T]` |
| Immutable sequence $\Pi_i T$ | `Prod[T]` | Type alias for `tuple[T, ...]`; `T` is a static type annotation only, with no runtime representation |
| Equality / axis alignment | `EqualityClass`, `Context` | Merges UIDs to declare axes equal |

A `Context` is a collection of UID equality declarations. When two axes are identified as the same (e.g. during `@` composition), their UIDs are declared equal and grouped into an `EqualityClass` — a set of UIDs sharing one canonical representative. If a later declaration overlaps an existing class, the two classes are merged. Once all equalities are accumulated, `apply(expr)` walks the expression tree and rewrites every UID in each class to the canonical one, so every occurrence of "the same axis" carries an identical UID regardless of where it originated. In short, `Context` is a union-find structure over UIDs: feed it equality pairs, merge overlapping groups, then call `apply()` to make the equalities concrete throughout the tree.

---

## The Product Category Framework

**Paper:** Section 3 — **Python:** [data_structure/ProductCategory.py](../data_structure/ProductCategory.py)

A **product category** is a monoidal category whose monoidal product is the categorical product. Both $\mathbf{St}$ and $\mathbf{Br}$ are product categories: their objects are (possibly empty) tuples of lone objects, and the monoidal product is tuple concatenation. The construction rules — $\mathbf{Composed}$, $\mathbf{ProductOfMorphisms}$, $\mathbf{Rearrangement}$, $\mathbf{Block}$ — are generic across any product category so that a single parametric framework covers both.

$\mathbf{Prod}[L, M]$ denotes the product category (objects, morphisms, and categorical axioms). In Python this is split across two types: `ProdObject[L]` for objects and `ProdCategory[L, M]` for morphisms. Every morphism carries explicit `dom: ProdObject[L]` and `cod: ProdObject[L]` fields, so the same `L` parameter determines both what lone objects are and what the endpoints of morphisms look like. (Note that `Prod[T]` (from the term system) is unrelated, it is simply a type alias for `tuple[T, ...]` used as a generic sequence type inside `ProdObject` and elsewhere)

The type parameters $L$ and $M$ are filled in differently for each concrete category. $L$ is always a UTerm — it needs a UID for alignment — and is always the smallest irreducible unit of the domain:

| Category | $L$ (lone object) | $M$ (root morphism) |
| --- | --- | --- |
| $\mathbf{St}$ | `Axis` — a named axis with a UID and a size | `StrideMorphism` |
| $\mathbf{Br}$ | `Array` — a pair $[a, A]$ of a `Datatype` $a$ and a shape $A \in \mathrm{Ob}\,\mathbf{St}$ | `Broadcasted` |

An object in $\mathbf{St}$ is thus a tuple of axes, e.g. $(\mathtt{batch}, \mathtt{seq}, \mathtt{dim})$; an object in $\mathbf{Br}$ is a tuple of typed arrays, each indexed by one axis.

### Objects in ProdCategory

**Objects** $A \in \mathrm{Ob}\,\mathcal{C}$ are finite products of lone objects $A_i \in L$:

$$A = \Pi_{i \in I} A_i$$

The **unit object** is the empty product $\mathbf{1} = \Pi_{i \in \emptyset} A_i$. The identity morphism on any object is a `Rearrangement` with mapping $(0, 1, 2, \ldots)$.

A Python `ProdObject[L]` object is a thin wrapper whose sole field, `content: Prod[L]` = `tuple[L, ...]`, stores a tuple of lone objects. The sequence $A_1, A_2, \ldots, A_n \in L$ constitutes the product $A = A_1 \times A_2 \times \cdots \times A_n$. The wrapper exists so that an empty tuple is a valid object (the unit $\mathbf{1}$) and so that the type system can distinguish a product object from a bare tuple. For example, in $\mathbf{St}$ a `ProdObject[Axis]` representing $(\mathtt{batch}, \mathtt{seq}, \mathtt{dim})$ holds `content = (batch_axis, seq_axis, dim_axis)` where each entry is an `Axis` instance.

### Morphisms in ProdCategory

The Python type alias for morphisms captures the grammar
of morphism forms:

```python
type ProdCategory[L, M: Morphism] = (
    M
    | Rearrangement[L]
    | Composed[L, ProdCategory[L, M]]
    | ProductOfMorphisms[L, ProdCategory[L, M]]
    | Block[L, ProdCategory[L, M]]
)
```

The first two are the core primitives; the remaining three are structural.

**1. Root morphisms** $m \in M$ — the category-specific primitive operations. Abstract in `ProductCategory`; concretely `StrideMorphism` in **St** and `Broadcasted` in **Br**.

**2. Rearrangements** — given a domain $A = \Pi_{i \in I} A_i$ and a mapping $\mu : J \to I$, a rearrangement $[\mu]_{(A_i)_{i \in I}} : \Pi_{i \in I} A_i \to \Pi_{j \in J} A_{\mu(j)}$ takes the $\mu(j)$-th input as its $j$-th output. Deletion is expressed by omitting an index; copying by repeating it.

- **Python:** `Rearrangement[L]` with `mapping: Prod[int]` and `_dom: Prod[L]`.

**3. Sequential composition** — a tuple of morphisms $f_1, f_2, \ldots, f_n$ applied left-to-right (diagrammatic order). $\mathrm{dom}()$ is the domain of the first; $\mathrm{cod}()$ is the codomain of the last.

- **Python:** `Composed[L, M]` with `content: Prod[M]`.

**4. Parallel product** — morphisms $f_1 \otimes f_2 \otimes \cdots \otimes f_n$ applied simultaneously on disjoint sub-products. $\mathrm{dom}()$ and $\mathrm{cod}()$ are the concatenations of the individual domains and codomains. Satisfies **bifunctoriality**: $(f \mathbin{;} g) \otimes (h \mathbin{;} k) \equiv (f \otimes h) \mathbin{;} (g \otimes k)$.

- **Python:** `ProductOfMorphisms[L, M]` with `content: Prod[M]`.

**5. Block** — a morphism decorated with display metadata (`title`, `fill_color`) and a `repetition` count (e.g., $\times 6$ for a stacked transformer layer). Transparent to the categorical semantics; passes $\mathrm{dom}()$ and $\mathrm{cod}()$ through from the body.

- **Python:** `Block[L, M]` with `body: M` and `block_tag: BlockTag`.

With this infrastructure for **product categories** we turn to specific instantiations.

---

## The Axis-Stride Category **St**

**Paper:** Definition 8 — **Python:** [data_structure/StrideCategory.py](../data_structure/StrideCategory.py)

**St** is an elemental Cartesian product category (Cartesian means that the categorical product corresponds to the usual Cartesian product in **Set**). Its role is to describe array *shapes* and the *coordinate transforms* between them, independently of any array data.

### Objects in St

**Objects** in **St** are **axes** and products of axes:

- A lone object is an **axis** $A$ — a UTerm carrying a UID and a size $|A| \in \mathbb{N}$. The UID serves as the axis's identity across an expression; the size is itself a `FreeNumeric` (another UTerm) until configured.
- A product object $\Pi_{i \in I} A_i \in \mathrm{Ob}\,\mathbf{St}$ is a **shape** — the ordered set of multi-index coordinates $(a_i)_{i \in I}$ of an array.
- The unit object $\mathbf{1}$ is the empty product, corresponding to a scalar shape.

In Python, `Axis` is the abstract base (`UTerm`); `RawAxis` is the concrete subclass used for unspecialized axes. `Axis.named('h')` creates an axis whose UID carries the name $h$ and whose size is a free numeric also named $|h|$.

### Morphisms in St

**Morphisms** in **St** are **finite affine transforms**: maps $\eta : \Pi_{i \in I} A_i \to \Pi_{j \in J} B_j$ that describe how input coordinates relate to output coordinates. Each output coordinate $j$ is a linear combination of input coordinates plus a bias:

$$\left(\Pi_{i \in I}\, a_i\right) \mathbin{;} \eta \;=\; \Pi_{j \in J}\!\left(v^\eta_j + \sum_{i \in I} \Lambda^\eta_{ij} \cdot a_i\right)$$

where $\Lambda^\eta \in \mathbb{N}^{I \times J}$ is the coefficient matrix and $v^\eta \in \mathbb{N}^J$ is the bias vector. The image must land within the codomain.

In Python, `StrideMorphism` stores `_dom: Prod[Axis]` and `_cod_stride: Prod[tuple[Axis, Prod[Numeric]]]`. `_cod_stride` bundles the codomain axes and the coefficient matrix into a single field: each entry is a pair of one codomain axis and a tuple of coefficients — one per domain axis — forming one row of $\Lambda^\eta$. Keeping them paired ensures the two are always in lockstep. `cod()` recovers the codomain by stripping the coefficients: `ProdObject.from_iter(axis for axis, _ in self._cod_stride)`. An optional `name` field carries display metadata. For example, the convolution-shift $x = x' + w$ is

```python
StrideMorphism.from_matrix(
    (1, 1), 
    dom_names=("x'", "w"),
    cod_names=("x",),
    name="+"
).
```

Similarly, duplication $\eta(p) = (p, p)$ (mapping one input axis to two output axes both equal) uses two rows each with a single coefficient of 1:

```python
StrideMorphism.from_matrix(
    (1,),  # first output = 1·p
    (1,),  # second output = 1·p
    dom_names=("p",),
    cod_names=("p", "p")
)
```

The identity, permutation, duplication, and deletion ($\eta = ()$) are all special cases of affine transforms and appear as `Rearrangement` morphisms in **St**.

---

## The Array-Broadcasted Category **Br**

**Paper:** Definitions 9–13 — **Python:** [data_structure/BroadcastedCategory.py](../data_structure/BroadcastedCategory.py), [data_structure/Operators.py](../data_structure/Operators.py)

**Br** is the category of deep learning models. It is a deletion product category, capturing both deterministic (**Set**) and probabilistic (**Stoch**) computation.

### Objects in Br

**Objects** in **Br** are **arrays** $[a, A]$:

- $a \in \mathbf{Dt}$ is a **datatype** — the kind of value stored at each coordinate. Common datatypes are `Reals` ($\mathbb{R}$, continuous and differentiable) and `Natural(max_value)` ($\mathbb{N}_{<v}$, discrete, used for token indices in embeddings).
- $A \in \mathrm{Ob}\,\mathbf{St}$ is a **shape** — a product of axes that indexes the array's coordinates.
- An array $[a, A]$ has an $\mathrm{El}(A)$-family of values $x_{i_A} \in a$ for each coordinate $i_A \in \mathrm{El}(A)$. Here $\mathrm{El}(A)$ is the **set of elements** of the shape $A$ — the set of all valid index tuples. For $A = (a_1, \ldots, a_n)$ with axis sizes $s_1, \ldots, s_n$, this is the Cartesian product $\{0,\ldots,s_1{-}1\} \times \cdots \times \{0,\ldots,s_n{-}1\}$. Categorically, $\mathrm{El}(A)$ is the set of morphisms $\mathbf{1} \to A$ (global elements). An array is therefore a function from index tuples to values: $x : \mathrm{El}(A) \to a$.

A product object $\Pi_{i \in I} [a_i, A_i]$ in **Br** is a tuple of arrays — the inputs or outputs of an operation.

In Python, `Array[B, A]` stores `datatype: B` and `_shape: Prod[A]`. `Reals()` and `Natural.template('v')` are the concrete datatypes. Objects are generally not constructed directly; they are computed from morphism `dom()` and `cod()` methods.

### Morphisms in Br

**Morphisms** in **Br** are **broadcasted operations** $F : \Pi_{i \in I} [a_i, A_i] \to \Pi_{j \in J} [b_j, B_j]$.

A broadcasted operation is built from four ingredients (Definition 13):

1. **A base operation** — the core computation, provided as an `Operator` subclass (e.g., `Linear`, `Einops`, `SoftMax`, `Elementwise`, `Normalize`, `Embedding`, `AdditionOp`, `WeightedTriangularLower`).

2. **Reindexings** $(\eta_i)_{i \in I}$ from **St** — the base operation runs once per coordinate $p \in P$, where $P$ is the *degree* shape (the same loop index for every input). The reindexing $\eta_i : P \to Q_i$ is an affine transform that says, for each loop coordinate $p$, which coordinate $\eta_i(p) \in Q_i$ to read from input $i$'s tiling axes. All inputs share the same loop $P$; the reindexings let them access their data differently:

   | Case | Tensor equation | $P$ | $\eta$ |
   | --- | --- | --- | --- |
   | **Identity** — both inputs batched the same way | $C[b,i,j] = A[b,i,k]\, B[b,k,j]$ | $(b)$ | $\eta_A = \eta_B = \mathrm{id}$ |
   | **Deletion** — $B$ broadcast across batches | $C[b,i,j] = A[b,i,k]\, B[k,j]$ | $(b)$ | $\eta_A = \mathrm{id}$ <br> $\eta_B = ()$ |
   | **Duplication** — diagonal slice | $Y[p,j] = X[p,p,j]$ | $(p)$ | $\eta_X(p) = (p,p)$ |
   | **Projection** — outer product, each input indexed by one output axis | $C[i,j] = A[i]\, B[j]$ | $(i,j)$ | $\eta_A(i,j) = i$ <br> $\eta_B(i,j) = j$ |
   | **Affine scaling** — strided 1-D convolution; $s \in \mathbb{N}$ is a fixed stride constant baked into the `StrideMorphism` coefficient matrix, not an axis | $Y[b,p] = \textstyle\sum_w X[b,\, s{\cdot}p+w]\, W[w]$ | $(b,p)$ | $\eta_X(b,p) = (b,\, s{\cdot}p)$ <br> $\eta_W = ()$ |

   In Python, the tuple of reindexings is stored as the `reindexings: Prod[StrideCategory[A]]` field on the `Broadcasted` dataclass — the root morphism of **Br** that packages all four ingredients together. On a GPU, the loop $P$ is what gets tiled: each processor is assigned a small chunk of $P$'s coordinates, loads only the corresponding slice of each input, and works entirely in fast on-chip memory.

3. **Input weaves** $(s_i)_{i \in I}$ — for each input array, a **weave** partitions its axes into *target* axes ($w = 1$, front, operated on by the base function) and *tiling* axes ($w = 0$, back, the broadcasted batch dimensions). In Python, `Weave[B, A]` stores `_shape: Prod[A | WeaveMode]` where `WeaveMode.TILED` marks tiled positions and actual `Axis` objects mark target positions.

4. **Output weaves** $(t_j)_{j \in J}$ — same structure for outputs, specifying which output axes are tiling (from degree $P$) and which are target (from the base operation's output shape).

The full type of the broadcasted operation is:

$$F : \Pi_{i \in I}\!\left[a_i,\, \mathrm{dom}\!\left([\Omega_{s_i}]_{A_i \otimes Q_i}\right)\right] \;\longrightarrow\; \Pi_{j \in J}\!\left[b_j,\, \mathrm{dom}\!\left([\Omega_{t_j}]_{B_j \otimes P}\right)\right]$$

In Python:

```python
@dataclass(frozen=True)
class Broadcasted[B: Datatype, A: Axis, O: Operator](Morphism[Array[B, A]]):
    operator:       O
    input_weaves:   Prod[Weave[B, A]]
    output_weaves:  Prod[Weave[B, A]]
    reindexings:    Prod[StrideCategory[A]]
```

`dom()` is computed from input weaves and reindexing codomains; `cod()` from output weaves and the shared degree $P$ (= `reindexings[i].dom()`, equal for all $i$).

### Key special cases

| Operation | How it appears in **Br** |
| --- | --- |
| Row-wise (batch) operation | Reindexing is identity; tiling axis = batch axis |
| Transposition | `Rearrangement` with swapped mapping |
| Diagonalization $\mathbf{y}[p,:] = \mathbf{x}[p,p,:]$ | Reindexing $\eta(p) = (p, p)$ |
| Repetition $\mathbf{y}[p,:] = \mathbf{x}[:]$ | Reindexing $\eta = ()$ (deletion) |
| Einsum contraction | `Einops` operator with matching weaves |
| Linear layer | `Linear` operator; target axes = input/output axes |
| Convolution | `StrideMorphism` shift $(x' + w)$ composed with `Linear` |

---

## Autoalignment via `@`

**Paper:** Section 5.1.1 — **Python:** [construction_helpers/composition.py](../construction_helpers/composition.py)

The `@` operator overloads `Morphism.__matmul__` to compose two morphisms with automatic axis alignment. When $\mathrm{cod}(f)$ and $\mathrm{dom}(g)$ differ in the number of axes, identity morphisms are inserted via `morphism_object_lift` to reconcile the mismatch. Once both sides have the same number of axes, a `Context` is built by pairing axes positionally and adding equality classes. Applying the context substitutes canonical UIDs throughout the composed expression, unifying named axes.

For example:

```python
qk_matmul @ softmax @ mask @ sv_matmul
```

At each `@`, the codomain axes of the left term are aligned with the domain axes of the right. Fresh unnamed axes generated by `SoftMax.template()` are renamed by the alignment context to match named axes from adjacent operations.

---

## Concrete Operators

**Python:** [data_structure/Operators.py](../data_structure/Operators.py)

Operators are `Operator` subclasses (frozen dataclasses) that implement `template()` to produce a fully-specified `Broadcasted` morphism:

| Operator | Description |
| --- | --- |
| `Einops.template('q h k, x h k -> h q x')` | General einsum; parses signature into weaves and reindexings |
| `Linear.template(input_size, output_size, name)` | Learned linear layer |
| `SoftMax.template()` | Normalization along one target axis |
| `Elementwise.template()` | Elementwise nonlinearity ($\sigma$, ReLU, etc.) |
| `Normalize.template()` | RMSNorm; same shape in and out |
| `Embedding.template(vocab_size)` | Discrete $\to$ real; input datatype is `Natural` |
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

Each `*` creates a `ProductOfMorphisms` ($\otimes$, parallel); each `@` creates a `Composed` ($\mathbin{;}$, sequential) with autoalignment. The result is a single algebraic term that can be:

- Sent as JSON via WebSocket to the TypeScript renderer (`wst.send_term(...)`)
- Printed as a category diagram (`dpl.print_category(...)`)
- Compiled to a PyTorch module (via `torch_compile/`)

---

## Math-to-Python Reference

| Paper definition | Python class / function | File |
| --- | --- | --- |
| Term (construction rule) | `Term` | `data_structure/Term.py` |
| UTerm (with UID) | `UTerm` | `data_structure/Term.py` |
| Unique identifier | `UID[T]` | `data_structure/Term.py` |
| Named variable | `DynamicName` | `data_structure/Term.py` |
| Immutable sequence $\Pi_i T$ | `Prod[T]` | `data_structure/Term.py` |
| Equality class / alignment | `EqualityClass`, `Context` | `data_structure/Term.py` |
| Product category $\mathbf{Prod}[L,M]$ | `ProdCategory[L, M]` | `data_structure/ProductCategory.py` |
| Product object $\Pi_{i \in I} L_i$ | `ProdObject[L]` | `data_structure/ProductCategory.py` |
| Root morphism $m \in M$ | `Morphism[L]` (abstract) | `data_structure/ProductCategory.py` |
| Sequential composition $\mathbin{;}$ | `Composed[L, M]` | `data_structure/ProductCategory.py` |
| Parallel product $\otimes$ | `ProductOfMorphisms[L, M]` | `data_structure/ProductCategory.py` |
| Rearrangement $[\mu]$ | `Rearrangement[L]` | `data_structure/ProductCategory.py` |
| Block $B$ | `Block[L, M]` | `data_structure/ProductCategory.py` |
| Axis $A$ with size $\lvert A \rvert$ (Def 8) | `Axis` / `RawAxis` | `data_structure/StrideCategory.py` |
| Shape $\Pi_{i \in I} A_i$ (Def 8) | `ProdObject[Axis]` | `data_structure/StrideCategory.py` |
| Finite affine transform $\eta$ (Def 8) | `StrideMorphism` | `data_structure/StrideCategory.py` |
| Datatype $a \in \mathbf{Dt}$ (Def 9) | `Datatype`, `Reals`, `Natural` | `data_structure/BroadcastedCategory.py` |
| Array $[a, A]$ (Def 9) | `Array[B, A]` | `data_structure/BroadcastedCategory.py` |
| Weave $w_i \in \{0,1\}$ (Def 12) | `Weave[B, A]`, `WeaveMode` | `data_structure/BroadcastedCategory.py` |
| Broadcasted operation $F$ (Def 13) | `Broadcasted[B, A, O]` | `data_structure/BroadcastedCategory.py` |
| Base operator $f$ | `Operator` subclass | `data_structure/Operators.py` |
| Autoalignment $\mathbin{@}$ | `composition`, `align_composed` | `construction_helpers/composition.py` |
| Batch lift $[f, P]$ (Def 11) | Product structure of `Broadcasted` | `data_structure/BroadcastedCategory.py` |
| Reindexing $[a, \eta]$ (Def 10) | `reindexings` field of `Broadcasted` | `data_structure/BroadcastedCategory.py` |
