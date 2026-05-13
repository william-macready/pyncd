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

$\Gamma$ is a set of **mathematical entities**. These entities are objects, morphisms, or products of either. $\Gamma$ has a family of $k$-indexed **core properties** $\pi_k : \Gamma_{k,i} \to \Gamma_{k,f}$, the basic structure maps that define what entities can do. These include $k = \text{dom}$, $k = \text{cod}$, $k = \text{composition}$, $k = {\otimes}$ (monoidal product), etc.

A **constructed term system** is the representation layer: a set $G$ of terms and an **interpretation function** $V_G : G \to \Gamma$ that says which mathematical entity each term denotes (we also have $V_G^{-1} :\Gamma \to G$). For each core property $\pi_k$, the term system provides an internal counterpart $p_k : G_{k,i} \to G_{k,f}$ such that evaluating inside the term system agrees with evaluating in $\Gamma$ after interpretation (soundness).

Terms are of two kinds:

- **Root terms** $G_r$ — the atoms of the term system. A root term is not assembled from smaller recoverable inputs; instead it carries **metadata** tags from which all relevant core properties can be computed directly. Root terms represent primitive, irreducible concepts — the specific choices of lone objects and root morphisms that distinguish one product category from another. In pyncd, `Axis` (carrying a UID and a size), `StrideMorphism` (carrying domain and coefficient matrix), and `Broadcasted` (carrying operator, weaves, and reindexings) are all root terms.

- **Construction rules** $T_c : G_{c,i} \to G_{c,f}$ build terms from smaller pieces. The output term is a **data wrapper around its inputs**: $G_{c,f}$ literally embeds $G_{c,i}$ inside itself, which is what the paper calls *contravariant* — the output contains the input rather than being derived from it. This guarantees a **recovery function** $\hat{T}_c : \text{img}(T_c) \to G_{c,i}$ satisfying $\hat{T}_c \circ T_c = \text{Id}$: the inputs can always be unwrapped from the output. In pyncd, `Composed`, `ProductOfMorphisms`, `Rearrangement`, and `Block` are construction rules common to every product category.

A **UTerm** (uniquely-identified term) is a term that carries a **UID** — a randomly-generated integer identifier — as one of its fields. The UID is the term's identity: two UTerms with the same UID are treated as the same entity everywhere in an expression, regardless of other field values. Plain `Term`s have no UID because their identity is fully determined by their contents. UTerms include `Axis`, `BlockTag`, and `FreeNumeric` — things whose identity must be tracked independently of their current field values.

**Placeholder terms** are partially-instantiated terms with open slots represented by UIDs. A UID acts as a free variable in an expression: imposing $\text{uid}_a = \text{uid}_b$ unifies the two slots and propagates the substitution through the term. This is the mechanism behind autoalignment: two terms composed via `@` have their boundary axes unified by merging UIDs.

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
| $\mathbf{St}$ | `Axis` — a named axis with a UID and size $\in\mathbb{N}$ (axis $i$ is often denoted as $A_i$)| `StrideMorphism` |
| $\mathbf{Br}$ | `Array` — a pair $[a, A]$ of a `Datatype` $a$ ($\mathbb{N}$, $\mathbb{R}$, or $\mathbb{N}_n$, i.e. 1..$n$, in pyncd) and a shape $A \in \text{Ob}(\mathbf{St})$ | `Broadcasted` |

An object in $\mathbf{St}$ is thus a tuple of axes, e.g. $(\mathtt{batch}, \mathtt{seq}, \mathtt{dim})$; an object in $\mathbf{Br}$ is a tuple of typed arrays, each indexed by one axis.

### Objects in ProdCategory

**Objects** $A \in \text{Ob} \mathcal{C}$ are finite products of lone objects $A_i \in L$:

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

**2. Rearrangements** — given a domain $A = \Pi_{i \in I} A_i$ and a mapping $\mu : J \to I$, a rearrangement $[\mu]_{(A_i)_{i \in I}} : \Pi_{i \in I} A_i \to \Pi_{j \in J} A_{\mu(j)}$ selects the $\mu(j)$-th input as its $j$-th output. Defining $\text{count}[\mu](i) = \#\{j \in J |\mu(j) = i\}$
deletion of input $i$ is expressed by having $\text{count}[\mu](i)=0$ and copying by having $\text{count}[\mu](i)>1$.

- **Python:** `Rearrangement[L]` with `mapping: Prod[int]` and `_dom: Prod[L]`.

**3. Sequential composition** — a tuple of morphisms $f_1, f_2, \ldots, f_n$ applied left-to-right (diagrammatic order). $\text{dom}()$ is the domain of the first; $\text{cod}()$ is the codomain of the last.

- **Python:** `Composed[L, M]` with `content: Prod[M]`.

**4. Parallel product** — morphisms $f_1 \otimes f_2 \otimes \cdots \otimes f_n$ applied simultaneously on disjoint sub-products. $\text{dom}()$ and $\text{cod}()$ are the concatenations of the individual domains and codomains. Satisfies **bifunctoriality**: $(f ; g) \otimes (h ; k) \equiv (f \otimes h) ; (g \otimes k)$.

- **Python:** `ProductOfMorphisms[L, M]` with `content: Prod[M]`.

**5. Block** — a morphism decorated with display metadata (`title`, `fill_color`) and a `repetition` count (e.g., $\times 6$ for a stacked transformer layer). Transparent to the categorical semantics; passes $\text{dom}()$ and $\text{cod}()$ through from the body.

- **Python:** `Block[L, M]` with `body: M` and `block_tag: BlockTag`.

With this infrastructure for **product categories** we turn to specific instantiations.

### Elemental Categories

**Paper:** Definition 6

A product category is **elemental** if each object $X$ has a distinguished set of **elements** $\text{El}(X) \subseteq \mathcal{C}(\mathbf{1}, X)$ — morphisms from the unit object (which is the terminal object in a Cartesian category) — rich enough to uniquely determine morphisms: if $x \mathbin{;} f = x \mathbin{;} g$ for all $x \in \text{El}(X)$, then $f = g$. Elements of a product are tuples of elements of the factors:

$$\text{El}(\Pi_{i \in I} A_i) = \{ \Pi_{i \in I} a_i \mid a_i \in \text{El}(A_i) \}.$$

In particular, $|\text{El}(\Pi_{i \in I} A_i)| = \prod_{i \in I} |\text{El}(A_i)|$, and $|\text{El}(\mathbf{1})| = 1$.

Both **St** and **Br** are elemental categories. Elements are diagrammed as left-pointing pentagons and notated inline as $\langle x | : \mathbf{1} \to X$. The co-versions are right-pointing pentagons and notated inline as $| x \rangle :  X \to \mathbf{1}$.

---

## The Axis-Stride Category **St**

**Paper:** Definition 8 — **Python:** [data_structure/StrideCategory.py](../data_structure/StrideCategory.py)

**St** is an elemental Cartesian product category (Cartesian means that the categorical product corresponds to the usual Cartesian product in **Set**). Its role is to describe array *shapes* and the *coordinate transforms* between them, independently of any array data.

### Objects in St

**Objects** in **St** are **axes** and products of axes:

- A lone object is an **axis** $A$ — a UTerm carrying a UID and a size $|A| \in \mathbb{N}$. The UID serves as the axis's identity across an expression; the size is itself a `FreeNumeric` (another UTerm) until configured.
- A product object $\Pi_{i \in I} A_i \in \text{Ob}(\mathbf{St})$ is a **shape** — the ordered set of multi-index coordinates $(a_i)_{i \in I}$ of an array. (Convention used throughout: $I$ is the ordered index set of an array's axes, so $i \in I$ ranges over axis positions.)
- The unit object $\mathbf{1}$ is the empty product, corresponding to a scalar shape.

In Python, `Axis` is the abstract base (`UTerm`); `RawAxis` is the concrete subclass used for unspecialized axes. `Axis.named('h')` creates an axis whose UID carries the name $h$ and whose size is a free numeric also named $|h|$.

### Morphisms in St

**Morphisms** in **St** are **finite linear transforms**: maps $\eta : \Pi_{i \in I} A_i \to \Pi_{j \in J} B_j$ that describe how input coordinates relate to output coordinates. Each output coordinate $j$ is a linear combination of input coordinates:

$$(\Pi_{i \in I} a_i) ; \eta = \Pi_{j \in J}(\sum_{i \in I} \Lambda^\eta_{ij} \cdot a_i)$$

where $\Lambda^\eta \in \mathbb{N}^{I \times J}$ is the coefficient matrix. The image must land within the codomain.

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
 (1,), # first output = 1·p
 (1,), # second output = 1·p
 dom_names=("p",),
 cod_names=("p", "p")
)
```

The identity, permutation, duplication, and deletion ($\eta = ()$) are all special cases of linear transforms and appear as `Rearrangement` morphisms in **St**.

---

## The Array-Broadcasted Category **Br**

**Paper:** Definitions 9–13 — **Python:** [data_structure/BroadcastedCategory.py](../data_structure/BroadcastedCategory.py), [data_structure/Operators.py](../data_structure/Operators.py)

**Br** is the category of deep learning models. It is a deletion product category, capturing both deterministic (**Set**) and probabilistic (**Stoch**) computation.

In this section we introduce the diagrammatic conventions (following from string diagrams) for representing **Br**.

### Objects in Br

**Objects** in **Br** are **arrays** $[a, A]$:

- $a \in \mathbf{Dt}$ is a **datatype** — the kind of value stored at each coordinate. Common datatypes are `Reals` ($\mathbb{R}$, continuous and differentiable) and `Natural(max_value)` ($\mathbb{N}_{<v}$, discrete, used for token indices in embeddings).
- $A \in \text{Ob}(\mathbf{St})$ is a **shape** — a product of axes that indexes the array's coordinates.
- An array $[a, A]$ has an $\text{El}(A)$-family of values $x_{i_A} \in a$ for each coordinate $i_A \in \text{El}(A)$. Here $\text{El}(A)$ is the **set of elements** of the shape $A$ — the set of all valid index tuples. For $A = (a_1, \ldots, a_n)$ with axis sizes $s_1, \ldots, s_n$, this is the Cartesian product $\{0,\ldots,s_1{-}1\} \times \cdots \times \{0,\ldots,s_n{-}1\}$. Categorically, $\text{El}(A)$ is the set of morphisms $\mathbf{1} \to A$ (global elements). An array is therefore a function from index tuples to values: $x : \text{El}(A) \to a$.

A product object $\Pi_{i \in I} [a_i, A_i]$ in **Br** is a tuple of arrays — the inputs or outputs of an operation.

In Python, `Array[B, A]` stores `datatype: B` and `_shape: Prod[A]`. `Reals()` and `Natural.template('v')` are the concrete datatypes. Objects are generally not constructed directly; they are computed from morphism `dom()` and `cod()` methods.

### Morphisms in Br

**Morphisms** in **Br** are **broadcasted operations** $F : \Pi_{i \in I} [a_i, A_i] \to \Pi_{j \in J} [b_j, B_j]$. Diagrammatically, we illustrate a morphism $f$ taking array inputs $[a, A_0]$ and $[b, \mathbb{1}]$ (a scalar-shaped array with datatype $b$) to produce output $[c, C_0C_1]$ (an array with datatype $c$ and shape $C_0C_1$). <img src="images/morphism-diagram.png" alt="Morphism diagram: function f with inputs A₀, a, b and outputs C₁, C₀, c" width="100" style="float: right; margin-left: 1em;"/> The dashed line on the input side groups $[a, A_0]$ and $[b, \mathbb{1}]$ into an array product (a tuple of inputs), while the output wires $C_1$, $C_0$, and $c$ represent the shape axes and base datatype of the codomain. When the base datatype is $\mathbb{R}$, the datatype (line with arrow) may be omitted

Before jumping into the details we first consider broadcasting in general.

### Broadcasting

**Broadcasting** describes how a base operation is lifted to run in parallel over additional axes. The key property is compositionality: lifting an operation over an additional axis is a systematic transformation, and broadcasts over shared axes compose predictably. 

A broadcasted operation separates two concerns: the *base operation* (what computation is performed on a single tile) and the *broadcasting structure* (which axes are looped over and how each input is indexed at each step). The loop domain is called the **degree** $P \in \text{Ob}(\mathbf{St})$. A **tiling axis** is an axis of an input array that is looped over by $P$ rather than operated on directly by the base operation. For each input $i$, a reindexing morphism $\eta_i : P \to Q_i$ in **St** specifies, for each degree coordinate $p \in P$, which coordinate $\eta_i(p) \in Q_i$ to read from that input's tiling axes — selecting the slice the base operation sees at that step. Different inputs can have different tiling shapes $Q_i$: an input with $\eta_i = \text{id}$ is indexed normally across all of $P$, while an input with $\eta_i = ()$ (the constant map to the empty shape) is broadcast across all of $P$ — its single value is reused at every step.

Given a stride morphism $\eta : P \to Q$ in **St** and a base datatype $a$, the **identity reindexing** $[a, \eta] : [a, Q] \to [a, P]$ is a morphism in **Br** whose action on elements $(a_i)_{i \in \text{El}(Q)}$ is:

$$(a_i)_{i \in \text{El}(Q)} ; [a, \eta] = (a_{\eta(p)})_{p \in \text{El}(P)}$$

<img src="images/reindexing-diagram.png" alt="Reindexing diagram: hexagon passing over base operation" width="220" style="float: right; margin-left: 1em;"/> In other words, $[a, \eta]$ relabels coordinates without changing any data values — it reads from position $\eta(p)$ of the input for each output position $p$. Diagramatically, reindexing is represented with a hexagon. This is the categorical counterpart of array indexing: a stride morphism $\eta$ in **St** lifts to a pure reindexing in **Br**. <img src="images/slice-diagram.png" alt="Slice diagram: reindexings built from elements and identities" width="100" style="float: right; margin-left: 1em;"/> When $\eta$ is an element $\langle q | : \mathbf{1} \to Q$ (a single coordinate), $[a, q]$ recovers the **index** morphism $[a, q] : [a, Q] \to [a, \mathbf{1}]$, selecting a single slice. As an example the figure corresponds to a slice `X[i,:,j]`.

**Batch lifting** Given a morphism $f : X \to Y$ in **Br** and a shape $P \in \text{Ob}(\mathbf{St})$, the batch lift $[f, P] : [X, P] \to [Y, P]$ runs $f$ independently once for each coordinate in $P$ (where $[X, P]$ and $[Y, P]$ are the inputs and outputs of $f$ each extended by the extra batch shape $P$ — concretely, every array in $X$ (resp. $Y$) gains $P$ as an additional set of axes). The defining property is:

$$[f, P] ; [Y, p] = [X, p] ; f$$

<img src="images/batch-lift-diagram.png" alt="Batch lifting diagram: F = [f,P] on the left equals slicing at p then applying f on the right" width="195" style="float: right; margin-left: 1em;"/> That is: applying the batch-lifted operation and then slicing the output at index $|p\rangle$ gives the same result as slicing the input at $|p\rangle$ first and then applying $f$ directly. There is no interaction between different positions in $P$ — the batch lift is exactly $f$ run independently at each index, and this equation is the formal statement that slicing commutes with $f$ and diagrammed as shown for $X=[a,A]$, $Y=[b,B]$, and $F=[f,P]$.

**Definition 11** formalizes batch lifting using the copy remapping $\delta^P : P \to \mathbf{1}$ as
$$[f, P] ; [\delta^P]_{[Y,P]} ; \prod_{p \in \text{El}(P)} [Y, p] = [\delta^P]_{[X,P]} ; \left(\prod_{p \in \text{El}(P)} [X, p] ; f\right)$$
This is most easily understood with the following diagramatic example where
<img src="images/def11-equation.png" alt="Definition 11 equation: batch lift composed with copy remapping" width="320" style="float: right; margin-left: 1em;"/>
$P$ is a single axis of size 3. We see how $f$ is commuted through the copy operation creating 3 independent copies (executed on separate GPU cores).

To describe such operations generally we specify which axes from a set $I$ are to be copied. A set of Boolean values $(w_i)_{i\in I}$ is used for this and is called a **weave**.

A broadcasted operation is built from four ingredients (Definition 13):

1. **A base operation** — the core computation, provided as an `Operator` subclass (e.g., `Linear`, `Einops`, `SoftMax`, `Elementwise`, `Normalize`, `Embedding`, `AdditionOp`, `WeightedTriangularLower`).

2. **Reindexings** $(\eta_i)_{i \in I}$ from **St** — the base operation runs once per coordinate $p \in P$, where $P \in \text{Ob}(\mathbf{St})$ is the *degree* shape (the same loop domain for every input, equal to `reindexings[i].dom()` for all $i$). For `Einops`, $P$ equals the retained (output) index space of the signature — all output indices become degree axes, with contracted indices as the only target axes in the input weaves. For `Elementwise`, $P$ equals the full array shape with all positions TILED. For `Linear`, `SoftMax`, `Embedding`, `Normalize`, `AdditionOp`, and `WeightedTriangularLower`, $P$ is empty and all input/output axes are target positions in the weaves. (The examples below show $P$ as a batch dimension for illustrative clarity; calling `Einops.template()` with a full batched signature, e.g. `'b i k, b k j -> b i j'`, produces $P = (b,i,j)$.) The reindexing $\eta_i : P \to Q_i$ is a linear transform that says, for each loop coordinate $p$, which coordinate $\eta_i(p) \in Q_i$ to read from input $i$'s tiling axes. All inputs share the same loop $P$; the reindexings let them access their data differently:

   | Case | Tensor equation | $P$ | $\eta$ |
   | --- | --- | --- | --- |
   | **Identity** — both inputs batched the same way | $C[b,i,j] = A[b,i,k] B[b,k,j]$ | $(b)$ | $\eta_A = \eta_B = \text{id}$ |
   | **Deletion** — $B$ broadcast across batches | $C[b,i,j] = A[b,i,k] B[k,j]$ | $(b)$ | $\eta_A = \text{id}$ <br> $\eta_B = ()$ |
   | **Duplication** — diagonal slice | $Y[p,j] = X[p,p,j]$ | $(p)$ | $\eta_X(p) = (p,p)$ |
   | **Projection** — outer product, each input indexed by one output axis | $C[i,j] = A[i] B[j]$ | $(i,j)$ | $\eta_A(i,j) = i$ <br> $\eta_B(i,j) = j$ |
   | **Affine scaling** — strided 1-D convolution; $s \in \mathbb{N}$ is a fixed stride constant baked into the `StrideMorphism` coefficient matrix, not an axis | $Y[b,p] = \sum_w X[b, s{\cdot}p+w] W[w]$ | $(b,p)$ | $\eta_X(b,p) = (b, s{\cdot}p)$ <br> $\eta_W = ()$ |

   In Python, the tuple of reindexings is stored as the `reindexings: Prod[StrideCategory[A]]` field on the `Broadcasted` dataclass — the root morphism of **Br** that packages all four ingredients together. On a GPU, the loop $P$ is what gets tiled: each processor is assigned a small chunk of $P$'s coordinates, loads only the corresponding slice of each input, and works entirely in fast on-chip memory.

3. **Input weaves** $(s_i)_{i \in I}$ — for each input array, a **weave** partitions its axes into *target* axes (operated on by the base operation) and *tiling* axes (the broadcasted batch dimensions, looped over by $P$). For each $p \in P$ the reindexing $\eta_i(p)$ supplies the concrete tiling coordinates, selecting the slice of input $i$ that the base operation sees at that iteration. Different inputs can have different tiling shapes $Q_i$ — connected to the shared loop $P$ through possibly non-trivial reindexings — which is what allows one input to be broadcast across all of $P$ while another is indexed into normally. See [Weaves](#weaves) below.

4. **Output weaves** $(t_j)_{j \in J}$ — same structure for outputs. The degree loop $P$ also drives the outputs: for each $p \in P$ the base operation produces one output tile, which is written into the output array at tiling position $p$. Unlike inputs (which can each have a distinct tiling shape $Q_i$ via the reindexings), every output tiles over exactly $P$, so the canonical split is $B_j \otimes P$ rather than $B_j \otimes Q_i$. The output weave $t_j$ records where in the output array's memory layout the $P$ positions sit relative to the target axes $B_j$.

#### Weaves

**Motivation.** GPUs achieve efficiency by splitting an operation's work across many parallel cores, each with a small fast on-chip memory (SMEM) and access to slow global DRAM. The key strategy is *tiling*: partition a large axis into small tiles, assign one tile per core, and have each core load only its tile from DRAM and run the base operation entirely in SMEM. For this to work, every axis of every array must be classified as one of two kinds:

- A **tiling axis** is distributed across cores. Each core is responsible for one tile of coordinates along this axis and loads only that slice from DRAM. It is never seen by the base operation directly; the reindexing $\eta_i$ tells each core which slice to load.
- A **target axis** is loaded fully into a single core's SMEM and operated on directly by the base operation. Its total size must fit within the core's memory budget.

FlashAttention (Abbott & Zardini, 2025, §3.2) computes
$$O[b,h,q,d] = \sum_x \text{SoftMax}_x(\sum_k Q[b,h,q,k]  K[h,x,k]) V[h,x,d]$$
where $Q[b,h,q,k]$, $K[h,x,k]$, and $V[h,x,d]$ are the query, key, and value tensors: $b$ is the batch axis, $h$ indexes attention heads, $q$ and $x$ index query and key/value positions respectively, and $k$, $d$ are the head dimensions. The query axis $q$ is tiled across GPU cores — each core processes a $g_q$-sized block of query positions in SMEM — while the head dimensions $k$ and $d$ are target axes loaded fully per core. Streaming the key/value position axis $x$ through in tiles avoids materialising the full $q \times x$ attention score matrix in DRAM, achieving a ×6 throughput gain over standard PyTorch. A **weave** records this classification axis-by-axis for every array so the compiler can determine, for each tile of $P$, which slice of each array to load.

Formally (Definition 12), a **weave** is a boolean family $(w_i)_{i \in I}$ indexed by the axes of an array: $w_i = 1$ marks a **target** axis; $w_i = 0$ marks a **tiling** axis. From this family the paper derives a permutation $\Omega_w : I \to I$ with the **canonical** split form (all target axes first, then all tiling axes) as its **domain**, mapping to the actual **interleaved** axis order of the array. The inverse permutation $\Omega_w^{-1}$ maps from the interleaved order to canonical form (needed to recover the target/tiling partition from an array's memory layout).

In pyncd the boolean family is encoded directly in the weave's `_shape` field: a sequence — one entry per axis of array $i$ — where each entry is either:

- A concrete **`Axis` object** — a **target axis**. The base operation acts on this axis directly: it may contract over it (like the $k$ dimension in a dot product), pass it through as a free index, or produce it as output. The base operation sees exactly the sub-array formed by all target axes.
- **`WeaveMode.TILED`** — a **tiling axis**. This axis is not seen by the base operation at all. It is provided externally by the reindexing loop: at each degree coordinate $p \in P$, the reindexing $\eta_i(p)$ supplies the concrete index values for every `TILED` slot in the weave.

**Simple example — `Linear` applied row-wise:** $Y[b, s, j] = \sum_i X[b, s, i]  W[i, j]$, base op `'i -> j'`, $P = (b, s)$.

| Array | Shape | Weave `_shape` | Axis roles |
| --- | --- | --- | --- |
| $X[b,s,i]$ | $(b, s, i)$ | `(TILED, TILED, i)` | $b,s$ tiling — looped by $P$; $i$ target — contracted |
| $W[i,j]$ | $(i, j)$ | `(i, j)` | all target — no tiling axes, same $W$ for all $(b,s)$ |
| $Y[b,s,j]$ | $(b, s, j)$ | `(TILED, TILED, j)` | $b,s$ tiling — filled from $P$; $j$ target — produced by Linear |

$j$ is a target axis on the output side because it is produced by the base op, not by the broadcast loop.

**Complex example — multi-head attention with broadcast K and V:** The full attention computation (ignoring softmax and mask) runs in two broadcasted operations sharing degree $P = (b)$.

**Step 1 — QK score:** $S[b, h, q, x] = \sum_k Q[b, h, q, k]  K[h, x, k]$, base op `'h q k, h x k -> h q x'`.

| Array | Shape | Weave `_shape` | Axis roles |
| --- | --- | --- | --- |
| $Q[b,h,q,k]$ | $(b,h,q,k)$ | `(TILED, h, q, k)` | $b$ tiling — looped by $P$, reindexed by identity; $h,q$ target free; $k$ target contracted |
| $K[h,x,k]$ | $(h,x,k)$ | `(h, x, k)` | all target — no tiling axes, same $K$ reused for every $b$ |
| $S[b,h,q,x]$ | $(b,h,q,x)$ | `(TILED, h, q, x)` | $b$ tiling — filled from $P$; $h,q,x$ target — produced by Einops |

**Step 2 — value aggregation:** $O[b, h, q, d] = \sum_x S[b, h, q, x]  V[h, x, d]$, base op `'h q x, h x d -> h q d'`.

| Array | Shape | Weave `_shape` | Axis roles |
| --- | --- | --- | --- |
| $S[b,h,q,x]$ | $(b,h,q,x)$ | `(TILED, h, q, x)` | $b$ tiling — looped by $P$, reindexed by identity; $h,q$ target free; $x$ target contracted |
| $V[h,x,d]$ | $(h,x,d)$ | `(h, x, d)` | all target — no tiling axes, same $V$ reused for every $b$ |
| $O[b,h,q,d]$ | $(b,h,q,d)$ | `(TILED, h, q, d)` | $b$ tiling — filled from $P$; $h,q,d$ target — produced by Einops |

The single `TILED` entry at position 0 of $Q$'s (and $S$'s) weave means: "the first axis in memory is a batch axis — supply its index from the reindexing loop, not from the base op." $K$ and $V$ have no `TILED` entries: both are shared across all batch coordinates, loaded once per core into SMEM. The contraction axis $k$ (step 1) and $x$ (step 2) appear in input weaves but not in the output weave — they are consumed by the base op.

In Python, `Weave[B, A]` stores `datatype: B` and `_shape: Prod[A | WeaveMode]`. `WeaveMode` is a single-member enum (`WeaveMode.TILED`) used as a typed sentinel: the union `A | WeaveMode` means each position in `_shape` holds either a concrete `Axis` object (target) or the `TILED` placeholder (tiling).

The full type of the broadcasted operation is:

$$F : \Pi_{i \in I}[a_i,  \text{dom}([\Omega_{s_i}]_{A_i \otimes Q_i})]
\longrightarrow
\Pi_{j \in J}[b_j,  \text{dom}([\Omega_{t_j}]_{B_j \otimes P})]$$

Here $\Omega_{s_i}$ is the unweave rearrangement in **St** associated with input weave $s_i$. The subscript $A_i \otimes Q_i$ follows the standard rearrangement notation $[\mu]_{(A_i)_{i \in I}}$, where the subscript specifies the **domain** objects. The domain of $[\Omega_{s_i}]_{A_i \otimes Q_i}$ is therefore the **canonical** split form $A_i \otimes Q_i$ (all target axes $A_i$ first, then all tiling axes $Q_i$); the permutation $\Omega_{s_i}$ maps it to the actual **interleaved** axis order of the array. The $\text{dom}(\cdot)$ in the formula extracts $A_i \otimes Q_i$ as the canonical shape of input $i$. The output side is analogous: $\Omega_{t_j}$ maps from the canonical split form $B_j \otimes P$ to the interleaved output shape.

**Relation to covariant and contravariant indices.** The input/output weave structure is the pyncd analogue of the covariant/contravariant index distinction in classical tensor analysis. A target axis appearing in an **input weave** is being *consumed* by the operator — it plays the role of a contravariant (upper) index that is contracted against a matching lower index. A target axis appearing in an **output weave** is being *produced* — it plays the role of a covariant (lower) index. Composition enforces the matching rule: `Context.append_iter` unifies the output (covariant) axes of one morphism with the input (contravariant) axes of the next, exactly as classical contraction requires one upper and one lower index. The degree axes — `TILED` positions shared across both input and output weaves — correspond to the free indices that appear on both sides of a tensor equation and are neither contracted nor produced.

In Python:

```python
@dataclass(frozen=True)
class Broadcasted[B: Datatype, A: Axis, O: Operator](Morphism[Array[B, A]]):
 operator: O
 input_weaves: Prod[Weave[B, A]]
 output_weaves: Prod[Weave[B, A]]
 reindexings: Prod[StrideCategory[A]]
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

The `@` operator overloads `Morphism.__matmul__` to compose two morphisms $f; g$ (the left and right operands) with automatic axis alignment. When $\text{cod}(f)$ and $\text{dom}(g)$ differ in the number of axes, identity morphisms are inserted via `morphism_object_lift` to reconcile the mismatch. Once both sides have the same number of axes, a `Context` is built by pairing axes positionally and adding equality classes. Applying the context substitutes canonical UIDs throughout the composed expression, unifying named axes.

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
| `Embedding.template(embedding_size)` | Discrete $\to$ real; input datatype is `Natural` |
| `AdditionOp.template()` | Elementwise addition of two arrays of the same shape |
| `WeightedTriangularLower.template()` | Causal mask; used in attention |

---

## End-to-End Example: Transformer

**Python:** [minimum_working_example.py](../minimum_working_example.py)

The transformer is built by composing the operators above:

```python
# Attention core: qk multiply → softmax → mask → sv multiply
qk_matmul = ops.Einops.template('q h k, x h k -> h q x')
softmax = ops.SoftMax.template()
mask = ops.WeightedTriangularLower().template()
sv_matmul = ops.Einops.template('h q x, x h k -> q h k')
_attention_core = Block.template(
 qk_matmul @ softmax @ mask @ sv_matmul,
 title='Attention Core', fill_color='#C5BEDF'
)

# Attention layer: project Q, K, V → attention core → project output
Lq = ops.Linear.template(('m',), 2, 'q') # [x, m] → [x, h, k] (2 output axes)
Lk = ops.Linear.template(('m',), 2, 'k')
Lv = ops.Linear.template(('m',), 2, 'v')
Lo = ops.Linear.template(2, ('m',), 'o') # [h, k] → [m]
_attention_layer = (Lq * Lk * Lv) @ _attention_core @ Lo

# Transformer layer: attention + FFN (feed-forward network: Linear → ReLU → Linear), each with residual + norm, repeated 6 times
_transformer = Block.template(
 res(_attention_layer) @ res(ffn_layer()),
 title='Transformer Layer', repetition=6
)

# Full model: embedding → 6× transformer → aggregator
_transformer_model = embedding @ _transformer @ aggregator
```

Each `*` creates a `ProductOfMorphisms` ($\otimes$, parallel); each `@` creates a `Composed` ($;$, sequential) with autoalignment. The result is a single algebraic term that can be:

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
| Sequential composition $;$ | `Composed[L, M]` | `data_structure/ProductCategory.py` |
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
| Autoalignment $@$ | `composition`, `align_composed` | `construction_helpers/composition.py` |
| Batch lift $[f, P]$ (Def 11) | Product structure of `Broadcasted` | `data_structure/BroadcastedCategory.py` |
| Reindexing $[a, \eta]$ (Def 10) | `reindexings` field of `Broadcasted` | `data_structure/BroadcastedCategory.py` |
