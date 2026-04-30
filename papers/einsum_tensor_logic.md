# Tensor Logic and Einsum

## Tensor Logic

### Motivation

Pedro Domingos (2025) proposes tensor logic as a language to unify neural and symbolic AI. Neural networks and logic programs are both special cases of tensor computation, differing only in whether tensor entries are real numbers or Booleans and whether a threshold nonlinearity is applied.

### The Two Core Equivalences

**1. Relations are sparse Boolean tensors.**

A relation `R(x, y)` is a Boolean matrix M where M_{xy} = 1 iff (x,y) is in the relation. Storing only the nonzero entries is exactly storing the relation's tuples. The correspondence extends to n-ary relations and rank-n tensors.

**2. A Datalog rule is an einsum over Boolean tensors.**

The rule

```text
Aunt(x,z) ← Sister(x,y), Parent(y,z)
```

is equivalent to

```text
A_{xz} = H(Σ_y S_{xy} P_{yz})
```

where H is the Heaviside step function. The sum is an einsum: join on y, project y out. The step function is needed because the sum may exceed 1 when multiple witnesses y exist; without it, this is a plain einsum over the arithmetic semiring.

### Tensor Operations as Logical Operations

| Logical/relational operation | Tensor logic operation |
| --- | --- |
| Natural join on shared variables | Elementwise product, summed over shared indices |
| Projection onto a subset of variables | Sum over non-output indices |
| Existential quantification | Projection + step function |
| Conjunction (AND) | Elementwise product |
| Disjunction (OR) | Elementwise sum |
| Negation (closed-world) | 1 − T |

### The Language

A **tensor logic program** is a set of **tensor equations**. The LHS names the tensor being defined; the RHS is a series of tensor joins on shared indices followed by an optional nonlinearity. Any RHS index not on the LHS is summed out; equations with the same LHS are implicitly summed.

```text
Y[i] = step(W[i,j] X[j])        -- single-layer perceptron
```

Here j is contracted, i is retained, and `step` is applied elementwise.

### Neural Networks in Tensor Logic

All standard architectures reduce to tensor equations. A multilayer perceptron:

```text
X[i, j, *t+1] = sig(W[i,j,k] X[i,k,*t] + V[i,j] U[i,t])
```

The `*` prefix marks a **virtual index**: no storage is allocated for that dimension and values are updated in-place. Without `*`, `X[i,j,t]` stores all timesteps; with `*t`, `X[i,j]` is overwritten at each step. This enables genuinely recurrent computation — RNNs are Turing-complete (Siegelmann & Sontag, 1995), and are directly expressible via `*`-indexed equations.

A convolutional layer:

```text
Features[x,y] = relu(Filter[dx,dy,ch] Image[x+dx, y+dy, ch])
```

A graph neural network aggregation step:

```text
Agg[n, l, d]   = Neig(n, n') Z[n', l, d]
Emb[n, l+1, d] = relu(W_Agg[d] Agg[n,l,d] + W_Self[d] Emb[n,l,d])
```

Attention introduces a third notation, the **`.`-suffixed index**:

```text
Comp[b, h, p, p'.] = softmax(Query[b,h,p,d_k] Key[b,h,p',d_k] / sqrt(D_k))
```

A `.`-suffixed index is the **normalization axis**: the function is applied to the full slice along that index for each combination of the others. Softmax cannot be expressed as a plain einsum — each element depends on all elements along the same axis — so the `.` tells the runtime to group along it before applying the function. The output layer uses the same notation:

```text
Y[p, t.] = softmax(W_O[t,d] Stream[B,p,d])
```

The three LHS index notations:

| Notation | Meaning |
| --- | --- |
| `i` | output index |
| `*t` | virtual index — iterated in-place, no storage for t |
| `t.` | normalization axis — function applied over the full slice |

An entire transformer fits in roughly a dozen tensor equations (Domingos 2025, Table 2).

### Inference and Learning

**Inference** uses tensor generalizations of forward chaining (execute equations to fixpoint) and backward chaining (lazy evaluation from a query).

**Learning** is simple: the gradient of a tensor equation is itself a tensor equation. If

```text
Y[...] = T[...] X₁[...] ... Xₙ[...]
```

then

```text
∂Y[...]/∂T[...] = X₁[...] ... Xₙ[...]
```

The full gradient of any loss is a sum of such equations and is expressible in tensor logic.

### Reasoning in Embedding Space

When object embeddings are learned rather than one-hot, replacing Boolean tensors with real-valued embedding matrices turns deductive inference into **analogical reasoning**: similar objects borrow inferences from each other proportionally to their similarity. The degree is controlled by a temperature T in a sigmoid:

```text
σ(x, T) = 1 / (1 + e^{−x/T})
```

At T→0, reasoning is purely deductive. As T increases it becomes increasingly analogical, combining the scalability of neural networks with the soundness of symbolic reasoning.

### Implementation in PyRel

PyRel is an extension of Datalog that subsumes tensor logic. Tensor logic equations map directly to PyRel rules, with tensors as relations and contractions as aggregations over shared index variables. See [tensor_logic_in_pyrel.md](tensor_logic_in_pyrel.md) for a translation guide with worked examples.

### Einsum as the Foundation

Tensor logic's claim — that Datalog rules and neural network layers are based on the same operations — rests on a precise definition of what those operations are. The operations are einsums. Every tensor equation is an einsum or a composition of einsums with a nonlinearity, and the algebraic laws governing tensor logic programs — reordering, factoring, decomposing equations — are exactly the commutativity, distributivity, and associativity of einsum. The next section gives einsum a formal treatment, providing the mathematical substrate for the unification claim in The Connection section.

---

## Einsum

### What It Is

Einsum (Einstein summation) was introduced to NumPy in 2011 and is now standard in PyTorch, TensorFlow, and Julia (Tullio.jl). It unifies all linear and multilinear operations — matrix products, traces, contractions, outer products, transpositions — under a single parametric notation.

### Syntax

An einsum expression has the form:

```text
#(I₁, ..., Iₙ → I;  T₁, ..., Tₙ)
```

- `I₁,...,Iₙ` — **input index strings**, one per tensor argument
- `I` — **output index string**
- `T₁,...,Tₙ` — tensor **arguments**

Each letter names an axis. Symbols appearing only in inputs are **contracted** (summed over). Common examples:

| Operation | Linear algebra | Einsum |
| --- | --- | --- |
| Matrix product | A · B | `#(ij, jk → ik; A, B)` |
| Transposition | Aᵀ | `#(ij → ji; A)` |
| Inner product | xᵀy | `#(i, i → ; x, y)` |
| Outer product | xyᵀ | `#(i, j → ij; x, y)` |
| Trace / diagonal | diag(A) | `#(ii → i; A)` |
| Broadcast to diagonal | diag(v) | `#(i → ii; v)` |

### Formal Semantics

A tensor maps **positions** (multi-indices) to values in a **commutative semiring** (R, ⊕, ⊗). The arithmetic semiring (ℝ, +, ×) is standard; the Viterbi (max-product) and Tropical (min-plus) semirings enable max-product inference and shortest paths with identical notation.

The result of an einsum is computed via **global positions** — all assignments of values to every index symbol in the expression. Each global position x̂ projects onto output position x via I. The result is:

```text
T(x) = ⊕_{x̂: I→x}  ⊗ᵢ Tᵢ(x̂: Iᵢ)
```

For each output position, **aggregate** over all global positions projecting to it the **combination** of the corresponding input entries. This combine-then-aggregate structure is what makes einsum simultaneously a product and a sum.

### Algebraic Properties

Wenig, Rump, Blacher, and Giesen (2025) formally prove:

- **Commutativity**: reordering arguments is unchanged (⊗ is commutative)
- **Associativity**: a flat n-ary einsum decomposes into nested binary einsums in any order
- **Distributivity**: einsum distributes over elementwise aggregation (⊕), enabling factoring like AB + AC = A(B+C)

### Nesting, Denesting, and Contraction Paths

Associativity means an n-tensor einsum evaluates as n−1 binary einsums in any order — the choice of order is a **contraction path** with large impact on cost (finding the optimal path is NP-hard). Nested einsums always denest into a single flat expression; when inner and outer expressions share index symbols the denesting uses **delta tensors** (Kronecker deltas) to split and later merge indices.

Delta tensors satisfy two key simplification rules:

- Any delta tensor can be removed, leaving a scalar and one all-ones vector per affected index
- Delta tensors of any order decompose into products of unit matrices δ₁

---

## The Connection

### Einsum Is the Primitive Operation of Both

Einsum underlies both neural computation and logical inference. The two paradigms share identical formal structure:

| | Neural computation | Logical inference |
| --- | --- | --- |
| Data | Real-valued tensors | Boolean tensors (relations) |
| Combination | Multiplication | Conjunction (AND / product) |
| Aggregation | Summation | Existential quantification (OR / sum + step) |
| Operation | Einsum over (ℝ, +, ×) | Einsum over (𝔹, ∨, ∧) + step |

They differ in two ways:

1. The **semiring**: arithmetic vs. Boolean
2. The optional **Heaviside step** converting a count of witnesses back to a Boolean

All else — joins, projections, contractions, broadcasting — is structurally identical.

### The Semiring Perspective

Einsum is defined over any commutative semiring. The Boolean semiring (𝔹, ∨, ∧) is one, and einsum over it is exactly relational join-and-project (modulo the step function). The Viterbi semiring gives max-product inference; the Tropical semiring gives shortest paths. All are the same formal structure under different semirings.

### The Language Question

Tensor logic asks: what does a programming language look like if built around einsum as its sole primitive? The answer: every statement is a tensor equation; symbolic knowledge is sparse Boolean tensors; neural components are dense real-valued tensors; gradients are free (also tensor equations); and the neural-symbolic boundary is a single temperature parameter.

### Practical Implications

- **Database and tensor engines solve the same problem**: join-project optimization and contraction-path optimization are the same problem under different names.
- **Sparse tensors are relations**: sparse operations can run on relational database engines; dense subtensors on GPUs — a single program can mix both.
- **Tucker decomposition generalizes predicate invention**: learning A[i,j,k] = M[i,p] M'[j,q] M''[k,r] C[p,q,r] is equivalent to learning latent predicates from data.
- **Einsum rewriting = query rewriting**: the equivalence rules Wenig et al. prove are exactly the query rewriting rules used to optimize relational queries.

---

## References

- Domingos, P. [*Tensor Logic: The Language of AI*](https://arxiv.org/abs/2510.12269). 2025.
- Wenig, M., Rump, P.G., Blacher, M., Giesen, J. [*The Syntax and Semantics of einsum*](https://arxiv.org/abs/2509.20020). 2025.
