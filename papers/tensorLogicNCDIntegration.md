# Tensor Logic as an Interface to pyncd

This document examines the relationship between Tensor Logic (Domingos 2025) and the pyncd categorical framework. The central proposal is that tensor logic equations can be embedded into pyncd's `Term` hierarchy as a first-class `Operator` subclass. Each tensor equation becomes a `TensorEquation(Operator)` term, stored as the `operator` field of a `Broadcasted` base morphism; a `TensorProgram(Term)` collects equations and converts them to a `Composed` morphism via `Context`-mediated axis unification. Index variables in the embedding are `Axis(UTerm)` objects whose UIDs carry identity — tensor logic's implicit name-sharing becomes explicit UID identity, tracked by the same `Context` machinery used throughout pyncd.

---

## 1. Background: Tensor Logic

For a detailed treatment of tensor logic and its foundations in einsum see [einsum_tensor_logic.md](einsum_tensor_logic.md). The subsections below summarise the concepts relevant to the pyncd integration.

### 1.1 Core idea

Pedro Domingos (2025) proposes **tensor logic** as a programming language whose sole primitive is the **tensor equation** — a named tensor defined as an einsum of other tensors with an optional nonlinearity applied to the result:

```text
Y[i, j] = relu(W[i, k] X[k, j])
```

Every statement is such an equation. A tensor logic *program* is a set of tensor equations. The language is intended to subsume both neural networks and logic programs: neural computation over the arithmetic semiring `(ℝ, +, ×)` and deductive reasoning over the Boolean semiring `(𝔹, ∨, ∧)` are the same structure under different semirings.

### 1.2 The two-way equivalence

The language rests on two formal equivalences.

**Relations are sparse Boolean tensors.** A relation `R(x, y)` is a Boolean matrix where `M_{xy} = 1` iff `(x, y) ∈ R`. The correspondence extends to n-ary relations and rank-n tensors; sparse storage is exactly tuple storage.

**A Datalog rule is an einsum over Boolean tensors.** The rule

```text
Aunt(x, z) ← Sister(x, y), Parent(y, z)
```

is equivalent to `A_{xz} = H(Σ_y S_{xy} P_{yz})` where `H` is the Heaviside step function converting a count of witnesses back to a Boolean. Without `H` this is a plain einsum over `(ℝ, +, ×)`. The join, projection, and existential quantification of relational algebra are all special cases of the einsum combine-then-aggregate structure.

### 1.3 Tensor operations as logical operations

| Logical / relational operation | Tensor logic operation |
| --- | --- |
| Natural join on shared variables | Elementwise product, summed over shared indices |
| Projection onto a subset of variables | Sum over non-output indices |
| Existential quantification | Projection + step function |
| Conjunction (AND) | Elementwise product |
| Disjunction (OR) | Elementwise sum |
| Negation (closed-world) | `1 − T` |

### 1.4 LHS index notation

Tensor equations use three kinds of LHS index. Two are relevant to this integration:

| Notation | Meaning |
| --- | --- |
| `i` | output index — stored in the result tensor |
| `t.` | normalization axis — function applied over the full slice along `t` |

The third notation, `*t` (virtual index — iterated in-place, enabling recurrence), is not addressed here. It would require a fixpoint combinator in `ProdCategory` that does not currently exist.

### 1.5 Neural networks in tensor logic

All standard architectures reduce to tensor equations. Selected examples from Domingos (2025):

```text
-- Perceptron
Y[i] = step(W[i,j] X[j])

-- Attention (softmax over normalization axis)
Comp[b, h, p, p'.] = softmax(Query[b,h,p,d] Key[b,h,p',d] / sqrt(D))

-- Output projection
Y[p, t.] = softmax(W_O[t,d] Stream[b,p,d])
```

A complete transformer fits in roughly a dozen tensor equations (Domingos 2025, Table 2).

### 1.6 Learning is free

The gradient of any tensor equation is itself a tensor equation. If `Y[...] = T[...] X₁[...] ... Xₙ[...]` then `∂Y[...]/∂T[...] = X₁[...] ... Xₙ[...]`. The full gradient of any loss is a sum of such equations and requires no special treatment beyond the equation language itself.

---

## 2. Background: Einsum

Tensor logic is built on einsum as its sole computational primitive. This section gives einsum a precise treatment since the mapping from tensor logic to pyncd runs through it.

### 2.1 Syntax

An einsum expression has the form:

```text
#(I₁, ..., Iₙ → I;  T₁, ..., Tₙ)
```

- `I₁, ..., Iₙ` — input index strings, one per tensor argument
- `I` — output index string
- `T₁, ..., Tₙ` — tensor arguments

Index symbols appearing only in inputs are **contracted** (summed over); symbols appearing on the output are **retained**.

| Operation | Linear algebra | Einsum |
| --- | --- | --- |
| Matrix product | `A · B` | `#(ij, jk → ik; A, B)` |
| Transposition | `Aᵀ` | `#(ij → ji; A)` |
| Inner product | `xᵀy` | `#(i, i → ; x, y)` |
| Outer product | `xyᵀ` | `#(i, j → ij; x, y)` |
| Trace | `tr(A)` | `#(ii → ; A)` |

### 2.2 Formal semantics

The result of an einsum over commutative semiring `(R, ⊕, ⊗)` is:

```text
T(x) = ⊕_{x̂: I → x}  ⊗ᵢ Tᵢ(x̂ ↾ Iᵢ)
```

For each output position `x`, aggregate over all global positions `x̂` projecting to `x` the combination of the corresponding input entries. This **combine-then-aggregate** structure unifies products, contractions, and reductions.

### 2.3 Algebraic properties

Wenig, Rump, Blacher, and Giesen (2025) formally prove commutativity, associativity, and distributivity of einsum. As a consequence:

- An n-tensor einsum decomposes into `n−1` binary einsums in any order (**contraction path**).
- Einsum distributes over elementwise aggregation, enabling algebraic simplification.
- Einsum rewriting rules are precisely query rewriting rules from relational algebra.

---

## 3. Background: pyncd

For a detailed treatment of the pyncd categorical framework see [theory.md](theory.md). The subsections below summarise the concepts relevant to the tensor logic integration.

### 3.1 The product category framework

pyncd represents neural network computations as morphisms in a **product category** `ProdCategory[L, M]`. Morphisms take one of five forms:

```text
ProdCategory[L, M] = M                         -- atomic base morphism
                   | Composed[L, M]            -- sequential composition
                   | ProductOfMorphisms[L, M]  -- parallel product
                   | Rearrangement[L]          -- permutation / copy / discard
                   | Block[L, M]               -- named sub-expression
```

The framework specialises to two concrete categories.

**St (StrideCategory):** objects are lists of `Axis` terms (each carrying a `Numeric` size); morphisms are `StrideMorphism` objects — linear coordinate transforms mapping one list of axes to another. Composition is matrix multiplication. This is the **semantic** layer — it tracks how index spaces are linearly related.

**Br (BroadcastedCategory):** objects are lists of `Array[Datatype, Axis]`; base morphisms are `Broadcasted[B, A, O]` values. The full morphism type is the same recursive `ProdCategory[Array, Broadcasted]` union — `Broadcasted`, `Composed`, `ProductOfMorphisms`, `Rearrangement`, and `Block`. This is the **computational** layer — each `Broadcasted` is one operator application with its index structure fully specified.

### 3.2 Broadcasted: the base morphism

In pyncd, `Array[B, A]` is the object type in `BroadcastedCategory` — it is pyncd's name for what tensor logic calls a tensor: a typed, multi-dimensional data structure with datatype `B` and a shape given by a list of `Axis` objects. A `Broadcasted[B, A, O]` encodes a single operator application over one or more such arrays:

```python
@dataclass(frozen=True)
class Broadcasted[B: Datatype, A: Axis, O: Operator]:
    operator: O                            # what computation to perform
    input_weaves: Prod[Weave[B, A]]        # how input arrays map to degree axes
    output_weaves: Prod[Weave[B, A]]       # how output arrays map to degree axes
    reindexings: Prod[StrideCategory[A]]   # index rewriting for each input
```

A `Weave` is a **shape template** for one array (i.e. an `Array[B, A]`). Each position is one of two kinds:

- **Degree position** (`WeaveMode.TILED`) — a placeholder filled with a degree axis at runtime. The **degree** $P$ is the shared loop domain of all reindexings (`reindexings[i].dom()`, equal for all inputs). For `Einops`, $P$ equals the retained (output) index space of the einsum signature; for all other operators $P$ is empty and the output axes are all target positions in the output weave.
- **Target position** (a concrete `Axis` object) — an axis private to that array, not shared with the degree.

The domain of each input array is reconstructed by filling its weave's TILED positions with `reindexing.cod()` and leaving target positions in place. The **reindexing** is a `StrideCategory` morphism with `dom() = degree` whose mapping selects which subset of degree axes that input contributes — for `Y[i,j] = W[i,k] X[k,j]`, W's reindexing selects `i` and X's selects `j`. For pure einsums a `Rearrangement` suffices; strided convolutions require a full `StrideMorphism`. The contracted index `k` appears as a concrete target axis in each input's weave and is summed over by the operator.

| Index role | Weave position | Example (`Y[i,j] = W[i,k] X[k,j]`) |
| --- | --- | --- |
| Degree / output index | `WeaveMode.TILED` | `i`, `j` — TILED in W's and X's weaves respectively |
| Contracted input index | Concrete `Axis` in input weave | `k` — concrete Axis in both W's and X's weaves |
| Produced output index | Concrete `Axis` in output weave | embedding dim in `Embedding` |

### 3.3 Operators

`Operator` is an abstract `Term` base class. Every `Broadcasted` carries an `operator: O` field that specifies what computation the morphism performs. The existing subclasses cover the standard neural network vocabulary:

| Operator | Description |
| --- | --- |
| `Einops` | General einsum; degree = retained (output) indices |
| `Elementwise` (e.g. ReLU, σ) / `SoftMax` | Pointwise and normalisation nonlinearities |
| `Linear` | Weight matrix application |
| `Embedding` | Lookup table: `Natural → Reals` |
| `AdditionOp` | Elementwise sum of matching arrays |
| `Normalize` | RMSNorm / LayerNorm |
| `WeightedTriangularLower` | Causal mask; used in attention |

The following terms are proposed as part of the tensor logic integration and are discussed in detail in §5:

| Class | Superclass | Produces | Scope |
| --- | --- | --- | --- |
| `TensorEquation` | `Operator` | `Broadcasted` via `bc_signature()` | one equation = one base morphism |
| `TensorProgram` | `Term` | `Composed` via `to_morphism()` | many equations = sequential composition |

`TensorProgram` is not an `Operator`: `Operator` is the type parameter stored in `Broadcasted.operator` and represents a single atomic computation, whereas `TensorProgram` wraps multiple equations and `to_morphism()` produces a `Composed` — a sequence of `Broadcasted` base morphisms spanning multiple steps with intermediate outputs.

Because `Operator` is a `Term`, any `Operator` subclass participates in `deep_reconstruct` and `Context.apply` traversal. This is the hook that makes the tensor logic integration possible: `TensorEquation` is an `Operator` subclass, so its internal structure — including its `Axis` index fields — is reachable by the standard `Term` machinery.

### 3.4 UID and Context: axis identity

Every `Axis` is a `UTerm` — it carries a `UID` that acts as its unique identity across expressions. Two axes are the same if and only if they share a `UID`. A `Context` is a union-find structure over `UID` equality classes:

```python
@dataclass
class Context:
    equality_classes: list[EqualityClass]
    def append_iter(self, target: Iterable[UTerm]) -> None: ...
    def apply[T: GeneralTerm](self, target: T) -> T: ...
```

When two morphisms are composed, `Context.append_iter` unifies the codomain axes of the first with the domain axes of the second. `Context.apply` then substitutes canonical representatives throughout the expression, aligning the axes.

---

## 4. Coverage Analysis

This section maps tensor logic concepts onto pyncd and identifies where the correspondence holds, where it is partial, and where pyncd provides structure that tensor logic does not express.

### 4.1 What tensor logic covers

**Einsum → `Einops`.** A tensor logic equation `Y[i,j] = W[i,k] X[k,j]` corresponds directly to an `Einops` operator with index annotation `i k, k j -> i j`. The retained indices `i, j` form the degree and occupy `WeaveMode.TILED` positions in both input weaves and the output weave. The contracted index `k` occupies target (non-TILED) positions in each input weave, and the `Einops` operator performs the summation over it. The reindexings are `Rearrangement` terms selecting which degree axes each input contributes: W contributes `i` and X contributes `j`.

**Elementwise nonlinearity → `Elementwise` / `ReLU` / `SoftMax`.** The optional nonlinearity in `Y[i] = relu(W[i,k] X[k])` selects the `Operator` subclass. The `.`-suffixed normalization axis maps to `SoftMax` or `Normalize`.

**Contraction structure and execution layout → degree, weaves, and reindexings.** Retained indices (those on the LHS) form the degree of the `Broadcasted` and occupy `WeaveMode.TILED` positions in every weave where they appear. Contracted indices (those on the RHS but not the LHS) become concrete target positions in input weaves, and the `Einops` operator sums over them. Per-input `Rearrangement` reindexings follow directly from which degree axes each input carries. The full weave structure is therefore derivable from the equation's index structure — tensor logic covers execution layout implicitly. pyncd makes it explicit by reifying it as typed `Weave` and `Rearrangement` objects that code generation can consume directly.

**Sequential composition → `Composed`.** A tensor logic program where one equation feeds the next maps to `Composed([m1, m2, ...])` in pyncd. With the term-based integration, `TensorProgram.to_morphism()` constructs this automatically.

### 4.2 Gaps closed by the integration (§5)

The following gaps in tensor logic are addressed by the term-based embedding described in §5.

**Axis identity.** In tensor logic, index variables are syntactic: two equations sharing a letter `k` share that index by convention, with no semantic identity machinery. This is a gap at the language level. The term-based embedding closes it by representing index variables as `Axis(UTerm)` objects: sharing is object sharing tracked by UID, not name matching. The choice of `Axis(UTerm)` as the representation for index variables in §5 is what makes this work — `Context` can then operate directly on `TensorEquation` values without any name-to-UID translation step.

**Degree as a first-class object.** The `degree()` method on `Broadcasted` returns the contraction index space as a `ProdObject[A]`. This enables checking, at construction time, that all input reindexings agree on which axes are contracted. Tensor logic has no type-level representation of contraction structure; `bc_signature()` in §5.3 derives and reifies the degree from the equation's UID graph.

### 4.3 What tensor logic does not cover

**Parallel product.** Tensor logic has no notion of running two computations independently in parallel and combining their outputs as a product. In pyncd, `ProductOfMorphisms([m1, m2])` applies two morphisms to disjoint inputs and concatenates the outputs as a `ProdObject`. This is the categorical product structure — essential for expressing multi-head attention, where each head operates independently — and has no counterpart in tensor logic. A tensor logic program must either write one equation per head or add a head index to the single equation, flattening the structure.

**Datatypes.** pyncd distinguishes `Reals` (continuous-valued arrays) from `Natural(max_value=n)` (discrete token indices). The canonical example is an embedding layer: a lookup table that maps a discrete token index (an integer in `[0, vocab_size)`) to a continuous real-valued vector. The input type is fundamentally different from a real-valued tensor — it cannot be added or multiplied, only used to index into the table. pyncd captures this at the type level: `Embedding.template('vocab', output_size=d_model)` produces a morphism with domain type `Natural(max_value=vocab)` and codomain type `Reals`, carrying the vocabulary size as a `Numeric` expression through the type system. Tensor logic treats all tensors uniformly as elements of a semiring — the equation `Y[i, d] = W[i, d]` looks identical whether `i` is a discrete token index or a real-valued sequence position. `TensorEquation` carries no datatype information; datatypes must be supplied as arguments to `bc_signature()` when constructing the `Weave` objects.

**Symbolic shape inference.** Axis sizes in pyncd are `Numeric` expressions — formal terms subject to symbolic manipulation. The size of a composed expression is derived algebraically from its components. `TensorProgram.to_morphism()` produces a morphism with symbolically-typed domain and codomain; tensor logic programs carry no shape information.

**Block structure.** `Block[L, M]` in pyncd names a sub-expression with a `BlockTag` and optional aesthetics. This supports structured display and selective substitution. `TensorProgram` is flat; hierarchical grouping is imposed by the surrounding pyncd expression.

### 4.4 Summary

| Concept | Tensor logic | pyncd |
| --- | --- | --- |
| Single einsum | `Y[i,j] = W[i,k] X[k,j]` | `TensorEquation` → `Broadcasted` via `bc_signature()` |
| Elementwise nonlinearity | `relu(...)` in equation | `operator` field on `TensorEquation` |
| Normalization axis | `t.` suffix | `SoftMax` / `Normalize` operator |
| Sequential composition | Feed-forward equation chain | `TensorProgram.to_morphism()` → `Composed` |
| Parallel composition | None | `ProductOfMorphisms([...])` |
| Axis identity | Syntactic name sharing | `Axis(UTerm)` with UID — object sharing |
| Datatypes | None (uniform semiring) | `Reals` / `Natural(max_value)` |
| Symbolic shapes | None | `Numeric` expressions on `Axis._size` |
| Sub-expression naming | None | `Block` + `BlockTag` |

---

## 5. The Term-Based Integration

### 5.1 The integration boundary

The coverage analysis locates a natural boundary: **one tensor equation corresponds to one `Broadcasted`**. A tensor equation specifies exactly what `Broadcasted` encodes:

1. Which tensors are combined (the inputs)
2. Which indices are contracted (the degree)
3. Which indices are retained (the targets)
4. What nonlinearity is applied (the operator)

The term-based integration achieves this by making `TensorEquation` an `Operator` subclass — a `Term` in the pyncd hierarchy. The equation is stored as the `Broadcasted.operator` field and is never discarded. Because `Operator` is a `Term`, `deep_reconstruct` and `Context.apply` traverse into `TensorEquation`'s internal fields, keeping the equation and the categorical structure in sync as axes are aligned.

### 5.2 `TensorEquation` as an `Operator` subclass

```python
@dataclass(frozen=True)
class TensorEquation(Operator):
    lhs_name:    DynamicName
    lhs_indices: Prod[Axis]                             # retained — identified by UID
    rhs:         Prod[tuple[DynamicName, Prod[Axis]]]   # (tensor_name, indices) per input
    operator:    Operator                               # nonlinearity, e.g. SoftMax(); Identity() if none
```

The index variables in `lhs_indices` and `rhs` are `Axis` objects — `UTerm` subclasses carrying UIDs. The same `Axis` object appearing in multiple positions encodes index sharing. An index is **contracted** if its UID appears in any `rhs` entry but not in `lhs_indices`; it is **retained** if its UID appears in `lhs_indices`. No string matching is involved: identity is UID identity.

The equation `Y[i, j] = W[i, k] X[k, j]` is constructed as:

```python
i = RawAxis.named('i')
j = RawAxis.named('j')
k = RawAxis.named('k')

eq = TensorEquation(
    lhs_name=DynamicName('Y'),
    lhs_indices=(i, j),
    rhs=(
        (DynamicName('W'), (i, k)),
        (DynamicName('X'), (k, j)),
    ),
    operator=Identity(),
)
```

The shared `k` object carries UID identity: its UID appears in both inputs but not in `lhs_indices`, making the contraction unambiguous.

For an equation with a nonlinearity,

```text
Y[b, p, t.] = softmax(W_O[t, d] Stream[b, p, d])
```

the `operator` field carries the `SoftMax` instance and the `.`-suffixed axis `t` requires a way to distinguish it from a plain retained index. This would be handled by a proposed new `Axis` subclass, `NormAxis`, not currently in the codebase, that marks the normalisation dimension:

```python
b      = RawAxis.named('b')   # batch
p      = RawAxis.named('p')   # sequence position
d      = RawAxis.named('d')   # model dimension (contracted)
t_norm = NormAxis.named('t')  # proposed new RawAxis subclass — marks the normalisation dimension

eq = TensorEquation(
    lhs_name=DynamicName('Y'),
    lhs_indices=(b, p, t_norm),   # t_norm: Axis with kind=NORM
    rhs=(
        (DynamicName('W_O'), (t_norm, d)),
        (DynamicName('Stream'), (b, p, d)),
    ),
    operator=SoftMax(),
)
```

### 5.3 `bc_signature()`: conversion to `Broadcasted`

`Operator` declares `bc_signature() → Broadcasted` as the standard construction pathway. `TensorEquation` implements it by reading the contraction structure from the UID graph:

1. **Retained axes** (`Axis` values whose UIDs appear in `lhs_indices`) — these form the degree; they occupy `WeaveMode.TILED` positions in every weave where they appear.
2. **Contracted axes** (`Axis` values whose UIDs appear in `rhs` but not in `lhs_indices`) — these become target (non-TILED) positions in their respective input weaves; the operator sums over them.
3. **Per-input reindexing**: build a `StrideCategory` morphism with `dom()=degree` selecting which degree axes this input participates in (a `Rearrangement` suffices for pure einsum).
4. **Return** `Broadcasted(operator=self, input_weaves=..., output_weaves=..., reindexings=...)`.

The result is `Broadcasted[B, A, TensorEquation]` — the operator field IS the equation.

### 5.4 Round-trip: equation and categorical structure stay in sync

Because `TensorEquation` is a `Term`, `Context.apply` reaches into its `lhs_indices` and `rhs` fields via `deep_reconstruct` and substitutes canonical axis UIDs alongside the `Broadcasted`'s weaves and reindexings. When two `Broadcasted[B, A, TensorEquation]` morphisms are composed and their shared axes are unified, both the categorical structure and the embedded equation are updated consistently.

This enables:

- **Display**: render `Broadcasted.operator` as a tensor logic equation string via `eq.to_string()`.
- **Round-trip editing**: modify `TensorEquation` fields and call `bc_signature()` to re-derive the `Broadcasted`.
- **Axis tracing**: the `Axis` objects in `TensorEquation.lhs_indices` are the same objects as those in `Broadcasted.output_weaves`, so any UID substitution is automatically reflected in both representations.

### 5.5 `TensorProgram(Term)` and `to_morphism()`

A tensor logic program is a set of equations linked by shared tensor names. `TensorProgram` represents this as a `Term` and converts it to a pyncd morphism:

```python
@dataclass(frozen=True)
class TensorProgram(Term):
    equations: Prod[TensorEquation]

    def to_morphism(self) -> ProdCategory[Array, Broadcasted]:
        ctx = Context()
        morphisms = []
        name_to_axes: dict[DynamicName, Prod[Axis]] = {}
        for eq in topological_sort(self.equations):
            # unify this equation's input axes with the output axes
            # of whichever prior equation defined each input tensor
            for tensor_name, input_axes in eq.rhs:
                if tensor_name in name_to_axes:
                    for prior_axis, eq_axis in zip(name_to_axes[tensor_name], input_axes):
                        ctx.append_iter((prior_axis, eq_axis))
            br = ctx.apply(eq).bc_signature()
            morphisms.append(br)
            name_to_axes[eq.lhs_name] = eq.lhs_indices
        return Composed(morphisms)
```

`topological_sort` orders equations so that each tensor is defined before it is used. The `name_to_axes` map translates tensor logic's implicit name-sharing into UID unification: when equation B refers to tensor `Hidden` that was defined by equation A, `ctx.append_iter` unifies A's `lhs_indices` with B's corresponding `rhs` entry. `ctx.apply(eq)` then substitutes canonical UIDs into both the equation and its resulting `Broadcasted`.

### 5.6 Beyond `TensorProgram` — Extending the Tensor Logic Interface

At and below `TensorProgram`, the tensor logic term representation covers sequential composition, einsum structure, nonlinearities, normalization axes, and axis identity. The remaining gaps — parallel product, datatypes, symbolic shapes, and block structure — are the caller's responsibility above `TensorProgram.to_morphism()` and are catalogued in §4.3.

This section describes what has been implemented in the Python DSL layer (`data_structure/TensorDSL.py`) and what remains as future work.

#### Python DSL: Implemented

`TensorDSL.py` provides a Python front-end for constructing `TensorEquation` and `TensorProgram` objects without manually populating dataclass fields. The core of the DSL is the `TL` registry:

```python
tl = TL()
i, j, k = axes('i j k')
tl.Y[i, j] = tl.W[i, k] * tl.X[k, j]
eq = tl.to_equation()        # TensorEquation
sig = tl.bc_signature()      # Broadcasted
```

`TL.__getattr__` returns a `TensorProxy` for any tensor name. Subscripting a proxy (`tl.W[i, k]`) returns an `IndexedTensor`. The `*` operator accumulates factors into an `RHSExpression`. Assignment (`tl.Y[i,j] = ...`) captures a `TensorEquation` in the registry. `relu()` and `softmax()` wrap an expression with the corresponding `Operator`. Multiple equations in one `TL` instance are collected and extracted as a `TensorProgram` via `tl.to_program()`. Calling `to_morphism()` on the result converts each `TensorEquation` to a `Broadcasted` via `bc_signature()` and assembles them into a `Composed` — the pyncd representation of sequential composition. Axis consistency across equations is established beforehand by a `Context` that unifies shared tensor UIDs as it walks the topological sort, playing the same role that `@`'s auto-alignment plays when morphisms are composed interactively.

**Tensor declarations** attach kind and shape metadata to a named tensor before it is used in equations:

```python
tl.W_in.tensor(real_axis('d_ff', 2048), real_axis('d', 512))
tl.Mask.predicate(real_axis('q'), real_axis('x'))
tl.E.selection(nat_axis('v', 50257), real_axis('d', 512))
```

Declarations are registered via `.tensor()`, `.predicate()`, and `.selection()` on a `TensorProxy` and stored in `TL._declarations`. They have two effects at indexing time: **arity checking** (the number of indices must match the declared shape) and **axis promotion** for non-contraction kinds. PREDICATE tensors promote all indices to `PredAxis`; SELECTION tensors promote indices at positions declared as `NatAxis` to `NatAxis`. TENSOR declarations perform no promotion — they carry shape and size metadata only.

**Typed axes** encode the ℕ vs ℝ distinction and optional concrete sizes directly on `Axis` objects:

```python
nat_axis('v', 50257)   # NatAxis with _size = Integer(50257)
nat_axis('v')          # NatAxis with _size = FreeNumeric  (type only, no size)
real_axis('d', 512)    # RawAxis with _size = Integer(512)
real_axis('d')         # RawAxis with _size = FreeNumeric  (type only, no size)
```

`NatAxis` and `PredAxis` are frozen zero-field dataclass subclasses of `RawAxis`, following the same pattern as the existing `NormAxis`. The type distinction is carried by the Python class; size is carried by the `_size` field inherited from `Axis`. Both are optional: a declaration without concrete sizes is valid and serves as a kind annotation without binding sizes.

Declarations are **entirely optional**. When absent, all existing behaviour — contraction detection, UID-based axis unification, `bc_signature()`, `to_morphism()` — is completely unchanged.

#### Parallel product from dependency analysis

Not yet implemented. A `TensorProgram`'s dependency DAG encodes parallelism implicitly: two equations with no directed path between them are independent and could be composed as `ProductOfMorphisms` rather than sequentially. The full program decomposes into alternating sequential steps and parallel blocks by finding **fork-join pairs** in the DAG — a fork where one tensor feeds multiple independent chains, a join where those chains reconverge. Between fork and join, the chains become the arguments of a `ProductOfMorphisms`; finding these pairs is a standard dominators/post-dominators analysis on the DAG.

The main complication is shared inputs: parallel branches often read from the same tensor (both attention heads read from the same embedded sequence). Since `ProductOfMorphisms` requires disjoint domain objects, shared inputs must be fanned out via a `Rearrangement` (copy mode) before the parallel block and outputs concatenated via another `Rearrangement` at the join. The UID-based `Axis` representation makes shared-input detection straightforward — the same `Axis` objects appearing in multiple branches are immediately identifiable.

This analysis is the inverse of tensor logic's conventional head-index trick, which encodes multi-head attention as a single batched equation with an explicit head dimension `h`. The two representations are semantically equivalent; the DAG analysis recovers the `ProductOfMorphisms` structure automatically from either form, exposing the parallelism explicitly to the pyncd type system.

#### Symbolic Shape Inference

Partially implemented. Tensor logic equations carry no size information. The DSL addresses this through **explicit axis annotation** rather than a full inference pass: `nat_axis('v', 50257)` and `real_axis('d', 512)` attach `Integer(n)` directly to the `_size` field of each axis at construction time, and tensor declarations carry this information positionally:

```python
tl.W_in.tensor(real_axis('d_ff', 2048), real_axis('d', 512))
```

This records that `W_in`'s first axis has size 2048 and its second has size 512, without requiring a separate annotation pass. Type-only declarations (no concrete size) are equally valid and record only the kind:

```python
tl.W_in.tensor(real_axis('d_ff'), real_axis('d'))
```

Declaration axes are separate objects from the equation-level axes (which are always created via `axes()`), so the size annotations are metadata on the declaration and do not affect the computation graph or `bc_signature()` output. A full shape propagation pass — which would unify declaration sizes with equation axes via `Context.append_iter` and propagate sizes forward through `TensorProgram.to_morphism()` — has not yet been implemented.

The longer-term design target is **tensor type signatures** that bind index names to sizes positionally:

```text
W_O    : (512, 64)
Stream : (32, 128, 64)

Y[b, p, t.] = softmax(W_O[t, d] Stream[b, p, d])
```

In the pyncd embedding this would become a shape propagation pass that runs alongside `TensorProgram.to_morphism()`. As the topological sort proceeds and `Context.append_iter` unifies UIDs, it would also unify sizes: when two axes merge their size variables resolve to the same `Numeric` expression, propagating shapes forward through the program exactly as UIDs are propagated now.

#### Embedding datatypes

Declaration annotation implemented; lookup equations deferred. The `.selection()` declaration is implemented and records that a tensor is a selection table indexed by a ℕ dimension. For example:

```python
tl.E.selection(nat_axis('v', 50257), real_axis('d', 512))
```

annotates `E` as an embedding matrix of vocabulary size 50,257 producing 512-dimensional real vectors. At indexing time, positional slots declared as `NatAxis` are promoted, distinguishing token-index dimensions from real-valued ones. This annotation is currently **decorative**: the actual lookup computation is still expressed via `ops.Embedding.template(vocab_size)`, not as a DSL equation.

Expressing the lookup as a first-class equation is deferred. The intended DSL syntax, working at the per-token level to match pyncd's point-level transformer architecture, would be:

```python
tl.Out[d] = tl.E[tl.token, d]
```

where `tl.token` (unsubscripted) represents the Natural-typed morphism domain — a single token ID — rather than a positionally-indexed tensor. The core issue is that tensor logic's contraction `Σ_i A[i,...] B[i,...]` requires *summing* over `i`, but an embedding lookup is *selection*: a token index is an opaque pointer into a table, not a position in a continuous space. In the pyncd embedding, pyncd already represents this correctly: `ops.Embedding.template(vocab_size)` produces a `Broadcasted` whose input weave has `Natural(vocab_size)` as its datatype and empty shape, encoding the vocabulary axis as a *type* rather than a *shape axis*. A `TensorLookup.bc_signature()` method could produce the same structure without any changes to pyncd; only `TensorDSL.py` and `TensorLogic.py` would need to be extended. The full scope of motivations and implementation issues is recorded in `docs/dsl_embedding_lookup_extension.md`.

The notation-level distinction proposed earlier — parentheses for selection vs square brackets for contraction — remains the right long-term design target:

```text
Y[b, p, d] = W[i, d] Token[b, p, i]   -- wrong: sums W over all vocab rows
Y[b, p, d] = W(Token[b, p], d)        -- correct: selects one row per position
```

but its realisation in the Python DSL awaits the `TensorLookup` implementation.

#### Predicate and numeric tensors

Axis-level distinction implemented; semiring-level distinction not yet implemented. The ℕ vs ℝ vs predicate distinction is implemented at the axis level. `NatAxis` marks a natural-number index dimension; `PredAxis` marks a predicate (Boolean-filter) dimension. Both are zero-field frozen dataclass subclasses of `RawAxis`, following the `NormAxis` pattern. The `.predicate()` declaration promotes all indices of the declared tensor to `PredAxis` at indexing time; `.selection()` promotes `NatAxis`-declared slots to `NatAxis`. The type distinction is therefore visible in the `TensorEquation.rhs` axis types and survives through `bc_signature()` and `Context`-mediated unification.

What is not yet implemented is the **semiring distinction** at the `Datatype` level. A `Bool` datatype subclass analogous to `Reals` and `Natural` does not exist; contracted indices over predicate tensors are not yet distinguished from summation. The longer-term design has curly braces for predicate (Boolean) tensors:

```text
Aunt{x, z} = Sister{x, y} Parent{y, z}    -- Boolean: AND + existential
Y[i, j]    = W[i, k] X[k, j]              -- numeric: multiply + sum
```

In the pyncd embedding, a `{}` tensor would map to a `Bool` datatype and contracted indices would become existential quantifications rather than sums. This requires both a new `Bool` datatype in pyncd and a corresponding treatment in `TensorEquation.bc_signature()`.

The three-way distinction across kinds is summarised as:

| Notation | Semantics | pyncd datatype | DSL status |
| --- | --- | --- | --- |
| `T[i, j]` | contraction — sum over shared indices | `Reals` | implemented |
| `T(i, d)` | selection — lookup row `i` | `Natural(max_value=n)` | deferred |
| `T{x, y}` | predicate — existential over shared indices | `Bool` | not yet implemented |

#### Unifying kind and shape in tensor declarations

Partially implemented via Python method API. The bracket type (kind) and the size annotation are both attributes of the same tensor dimension. In the Python DSL these are unified in tensor declarations, which record both together:

```python
tl.W.tensor(real_axis('d_ff', 2048), real_axis('d', 512))   # ℝ₂₀₄₈ × ℝ₅₁₂
tl.E.selection(nat_axis('v', 50257), real_axis('d', 512))   # ℕ₅₀₀₀₀ → ℝ₅₁₂
tl.Mask.predicate(real_axis('q'), real_axis('x'))            # 𝔹, sizes deferred
```

This is the Python realisation of the arrow-notation design target:

```text
W   : (ℝ_2048, ℝ_512)          -- contraction tensor
E   : ℕ_50000 -> ℝ_512          -- selection: token ID → embedding vector
```

The domain of the arrow maps to the positional shape tuple; the codomain maps to the kind (`tensor`, `predicate`, or `selection`). Size can be specified (`Integer(n)`) or left symbolic (`FreeNumeric`). As with the bracket notation, kind is fully derivable from the declaration — no per-index annotation in equations is needed. The remaining gap is that the Python declarations currently serve as metadata only; the shape inference pass that would propagate declared sizes into equation axes via `Context` unification is not yet implemented.

---

## 6. Summary

Tensor Logic (Domingos 2025) provides a compact notation for individual operator applications in which the index structure is made explicit. `TensorEquation(Operator)` embeds this notation into pyncd's `Term` hierarchy: each equation is a frozen dataclass whose `Axis` index fields carry UID identity, whose `bc_signature()` method produces the corresponding `Broadcasted[B, A, TensorEquation]`, and whose structure remains accessible and traversable throughout the expression's lifetime. `TensorProgram(Term)` collects equations, topologically sorts them, and produces a `Composed` morphism via `Context`-mediated axis unification — converting tensor logic's implicit name-sharing into pyncd's explicit UID identity.

The integration boundary is clean: `TensorProgram.to_morphism()` produces a morphism in `BroadcastedCategory`; above that level, `ProductOfMorphisms`, type-level datatypes, symbolic shape propagation, and `Block` structure are the caller's responsibility — categorical structures that tensor logic deliberately omits.

Beyond this core integration, §5.6 explores how the remaining gaps might themselves be closed by extending the tensor logic interface: extracting parallel product structure from the program's dependency DAG, adding symbolic shape inference via tensor type signatures, distinguishing embedding selection from contraction with a bracket convention, and separating predicate (Boolean) tensors from numeric ones — with all three distinctions unified into a single arrow-notation type signature that encodes index space, value type, and operation kind together.

---

## References

- Domingos, P. *Tensor Logic: The Language of AI*. 2025. arXiv:2510.12269.
- Wenig, M., Rump, P.G., Blacher, M., Giesen, J. *The Syntax and Semantics of einsum*. 2025. arXiv:2509.20020.
