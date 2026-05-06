# Tensor Logic as an Interface to pyncd

This document examines the relationship between Tensor Logic (Domingos 2025) and the pyncd categorical framework. The central proposal is that tensor logic equations can be embedded into pyncd's `Term` hierarchy as a first-class `Operator` subclass. Each tensor equation becomes a `TensorEquation(Operator)` term, stored as the `operator` field of a `Broadcasted` base morphism; a `TensorProgram(Term)` collects equations and converts them to a `Composed` morphism via `Context`-mediated axis unification. Index variables in the embedding are `Axis(UTerm)` objects whose UIDs carry identity — tensor logic's implicit name-sharing becomes explicit UID identity, tracked by the same `Context` machinery used throughout pyncd.

---

## 1. Background: Tensor Logic

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

**St (StrideCategory):** objects are lists of `Axis` terms (each carrying a `Numeric` size); morphisms are affine stride matrices mapping one list of axes to another. Composition is matrix multiplication. This is the **semantic** layer — it tracks how index spaces are linearly related.

**Br (BroadcastedCategory):** objects are lists of `Array[Datatype, Axis]`; base morphisms are `Broadcasted[B, A, O]` values. The full morphism type is a free list of base morphisms. Composition is list concatenation. This is the **computational** layer — each `Broadcasted` is one operator application with its index structure fully specified.

### 3.2 Broadcasted: the base morphism

A `Broadcasted[B, A, O]` encodes a single operator application:

```python
@dataclass(frozen=True)
class Broadcasted[B: Datatype, A: Axis, O: Operator]:
    operator: O                            # what computation to perform
    input_weaves: Prod[Weave[B, A]]        # how input arrays map to degree axes
    output_weaves: Prod[Weave[B, A]]       # how output arrays map to degree axes
    reindexings: Prod[StrideCategory[A]]   # index rewriting for each input
```

The **degree** is the shared index space across all inputs — the axes retained in the output (those not contracted). The `Weave` separates **degree axes** (shared, tiled across inputs) from **target axes** (private to each array). The `reindexings` are stride morphisms specifying how each input's axes map into the degree.

### 3.3 Operators

`Operator` is an abstract `Term` base class. Every `Broadcasted` carries an `operator: O` field that specifies what computation the morphism performs. The existing subclasses cover the standard neural network vocabulary:

| Operator | Description |
| --- | --- |
| `Einops` | General einsum; degree = contracted indices |
| `Elementwise` / `ReLU` / `SoftMax` | Pointwise and normalisation nonlinearities |
| `Linear` | Weight matrix application |
| `Embedding` | Lookup table: `Natural → Reals` |
| `AdditionOp` | Elementwise sum of matching arrays |
| `Normalize` | RMSNorm / LayerNorm |

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

**Einsum → `Einops`.** A tensor logic equation `Y[i,j] = W[i,k] X[k,j]` corresponds directly to an `Einops` operator with index annotation `i k, k j -> i j`. The contraction over `k` is encoded in the `reindexings`, and the retained indices `i, j` become target axes in `output_weaves`.

**Elementwise nonlinearity → `Elementwise` / `ReLU` / `SoftMax`.** The optional nonlinearity in `Y[i] = relu(W[i,k] X[k])` selects the `Operator` subclass. The `.`-suffixed normalization axis maps to `SoftMax` or `Normalize`.

**Contraction structure → degree and reindexings.** Contracted indices (those on the RHS but not the LHS) become the degree axes of the `Broadcasted`, shared across all `reindexings`. Retained indices become the target axes in the corresponding `Weave`.

**Sequential composition → `Composed`.** A tensor logic program where one equation feeds the next maps to `Composed([m1, m2, ...])` in pyncd. With the term-based integration, `TensorProgram.to_morphism()` constructs this automatically.

### 4.2 What tensor logic does not cover

**Parallel product.** Tensor logic has no notion of running two computations independently in parallel and combining their outputs as a product. In pyncd, `ProductOfMorphisms([m1, m2])` applies two morphisms to disjoint inputs and concatenates the outputs as a `ProdObject`. This is the categorical product structure — essential for expressing multi-head attention, where each head operates independently — and has no counterpart in tensor logic.

**Axis identity.** In tensor logic, index variables are syntactic: two equations sharing a letter `k` share that index by convention, with no semantic identity machinery. This is a gap at the language level. The term-based embedding closes it by representing index variables as `Axis(UTerm)` objects: sharing is object sharing tracked by UID, not name matching. The choice of `Axis(UTerm)` as the representation for index variables in §5 is what makes this work — `Context` can then operate directly on `TensorEquation` values without any name-to-UID translation step.

**Datatypes.** pyncd distinguishes `Reals` (continuous-valued arrays) from `Natural(max_value=n)` (discrete token indices). This distinction is load-bearing: `Embedding` maps `Natural → Reals` and the `max_value` field carries the vocabulary size as a `Numeric` expression. Tensor logic treats all tensors uniformly as elements of a semiring with no type-level separation between discrete and continuous domains.

**Symbolic shape inference.** Axis sizes in pyncd are `Numeric` expressions — formal terms subject to symbolic manipulation. The size of a composed expression is derived algebraically from its components. Tensor logic operates on concrete tensors with fixed shapes; symbolic shape propagation is outside its scope.

**Degree as a first-class object.** The `degree()` method on `Broadcasted` returns the shared index space as a `ProdObject[A]`. This enables checking, at construction time, that all input reindexings agree on which axes are contracted. Tensor logic has no type-level representation of contraction structure.

**Block structure.** `Block[L, M]` in pyncd names a sub-expression with a `BlockTag` and optional aesthetics. This supports structured display and selective substitution. Tensor logic programs are flat sets of equations with no hierarchical grouping.

### 4.3 Summary

| Concept | Tensor logic | pyncd |
| --- | --- | --- |
| Single einsum | `Y[i,k] = W[i,j] X[j,k]` | `TensorEquation` → `Broadcasted` via `bc_signature()` |
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

The coverage analysis locates a natural boundary: **one tensor equation corresponds to one `Broadcasted` (one `BrBase`)**. A tensor equation specifies exactly what `Broadcasted` encodes:

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

the `operator` field carries the `SoftMax` instance and the `.`-suffixed axis `t` is an `Axis` appearing in `lhs_indices` with a `NormAxis` annotation:

```python
b      = RawAxis.named('b')   # batch
p      = RawAxis.named('p')   # sequence position
d      = RawAxis.named('d')   # model dimension (contracted)
t_norm = NormAxis.named('t')  # vocabulary / output dimension, normalization axis

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

1. **Contracted axes**: collect `Axis` values whose UIDs appear in `rhs` but not in `lhs_indices` — these form the degree.
2. **Retained axes**: `Axis` values in `lhs_indices` — these become target axes in `output_weaves`.
3. **Per-input reindexing**: build a `StrideMorphism` mapping each input's index space into the degree.
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
                    ctx.append_iter(zip(name_to_axes[tensor_name], input_axes))
            br = ctx.apply(eq).bc_signature()
            morphisms.append(br)
            name_to_axes[eq.lhs_name] = eq.lhs_indices
        return Composed(morphisms)
```

`topological_sort` orders equations so that each tensor is defined before it is used. The `name_to_axes` map translates tensor logic's implicit name-sharing into UID unification: when equation B refers to tensor `Hidden` that was defined by equation A, `ctx.append_iter` unifies A's `lhs_indices` with B's corresponding `rhs` entry. `ctx.apply(eq)` then substitutes canonical UIDs into both the equation and its resulting `Broadcasted`.

### 5.6 What pyncd provides above `TensorProgram`

At and below `TensorProgram`, the tensor logic term representation covers sequential composition, einsum structure, nonlinearities, normalization axes, and axis identity. Above that level, pyncd provides structure that tensor logic does not express:

**Parallel product.** `ProductOfMorphisms([m1, m2])` applies two morphisms to disjoint inputs and concatenates the outputs as a `ProdObject`. Multi-head attention, where each head operates independently, requires this construct. A tensor logic program must either write one equation per head or add a head index to the single equation, flattening the structure.

**Datatypes.** `Embedding.template('vocab', output_size=d_model)` produces a morphism with domain type `Natural(max_value=vocab)` and codomain type `Reals`. The vocabulary size is a `Numeric` expression carried through the type system. `TensorEquation` carries datatypes on its `Axis` objects but tensor logic itself is semiring-uniform.

**Symbolic shapes.** Axis sizes are `Numeric` expressions in pyncd. Sequence length, head count, and key dimension are formal terms that propagate algebraically through composition. `TensorProgram.to_morphism()` produces a morphism with symbolically-typed domain and codomain; tensor logic programs carry no shape information.

**Block structure.** `Block[L, M]` with `BlockTag` names a sub-expression for display and selective substitution. `TensorProgram` is flat; hierarchical grouping is imposed by the surrounding pyncd expression.

---

## 6. Summary

Tensor Logic (Domingos 2025) provides a compact notation for individual operator applications in which the index structure is made explicit. `TensorEquation(Operator)` embeds this notation into pyncd's `Term` hierarchy: each equation is a frozen dataclass whose `Axis` index fields carry UID identity, whose `bc_signature()` method produces the corresponding `Broadcasted[B, A, TensorEquation]`, and whose structure remains accessible and traversable throughout the expression's lifetime. `TensorProgram(Term)` collects equations, topologically sorts them, and produces a `Composed` morphism via `Context`-mediated axis unification — converting tensor logic's implicit name-sharing into pyncd's explicit UID identity.

The integration boundary is clean: `TensorProgram.to_morphism()` produces a morphism in `BroadcastedCategory`; above that level, `ProductOfMorphisms`, type-level datatypes, symbolic shape propagation, and `Block` structure are the caller's responsibility — categorical structures that tensor logic deliberately omits.

---

## References

- Domingos, P. *Tensor Logic: The Language of AI*. 2025. arXiv:2510.12269.
- Wenig, M., Rump, P.G., Blacher, M., Giesen, J. *The Syntax and Semantics of einsum*. 2025. arXiv:2509.20020.
