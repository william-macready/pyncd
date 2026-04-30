# Tensor Logic and Einsum

## Tensor Logic

### Motivation

Pedro Domingos (2025) proposes tensor logic as a programming language intended to unify neural and symbolic AI at a mathematical level. The claim is that neural networks and logic programs are not fundamentally different: they are both special cases of tensor computation, differing only in the data types of tensor entries (real numbers vs. Booleans) and the presence or absence of a threshold nonlinearity.

### The Two Core Equivalences

**1. Relations are sparse Boolean tensors.**

A logical relation `R(x, y)` over a domain of objects is exactly a Boolean matrix M where M_{xy} = 1 iff the tuple (x,y) is in the relation. For large domains, almost all entries are 0, so the matrix is sparse — but storing only the nonzero entries is precisely storing the relation's tuples. This correspondence extends to n-ary relations and rank-n Boolean tensors.

**2. A Datalog rule is an einsum over Boolean tensors.**

The rule

```text
Aunt(x,z) ← Sister(x,y), Parent(y,z)
```

is equivalent to the tensor equation

```text
A_{xz} = H(Σ_y S_{xy} P_{yz})
```

where H is the Heaviside step function. The sum Σ_y S_{xy} P_{yz} is an einsum: join on the shared index y, project out y to produce a matrix indexed by x and z. The step function is needed because the sum may exceed 1 when multiple witnesses y exist; without it, the computation is precisely an einsum over the arithmetic semiring.

### Tensor Operations as Logical Operations

| Logical/relational operation | Tensor logic operation |
| --- | --- |
| Natural join of R and S on shared variables | Elementwise product, summed over shared indices |
| Projection onto a subset of variables | Sum over non-output indices |
| Existential quantification | Projection + step function |
| Conjunction (AND) | Elementwise product |
| Disjunction (OR) | Elementwise sum |
| Negation (closed-world) | 1 − T |

### The Language

A **tensor logic program** is a set of **tensor equations**. Each equation has:

- A **left-hand side**: the tensor being defined, indexed by its output indices
- A **right-hand side**: a series of tensor joins (implicit, indicated by shared indices), followed by an optional elementwise nonlinearity

The projection (summation over non-output indices) is implicit: any index on the RHS that does not appear on the LHS is summed over. Equations with the same LHS are implicitly summed.

```text
Y[i] = step(W[i,j] X[j])        -- single-layer perceptron
```

Here j is contracted (summed), i is retained. The step function applies elementwise to the result.

### Neural Networks in Tensor Logic

All standard architectures reduce to tensor equations. A multilayer perceptron:

```text
X[i, j, *t+1] = sig(W[i,j,k] X[i,k,*t] + V[i,j] U[i,t])
```

The `*` prefix on an index marks it as a **virtual index**: no memory is allocated for that dimension, and successive values are written to the same location in-place. Without `*`, `X[i,j,t]` would be a 3D tensor storing activations at every timestep simultaneously. With `*t`, `X[i,j]` remains a 2D tensor that is overwritten at each step as `t` advances, expressing genuinely recurrent computation. This is what makes tensor logic Turing-complete: RNNs with in-place update semantics are Turing-complete (Siegelmann & Sontag, 1995), and they are directly expressible via `*`-indexed equations.

A convolutional layer:

```text
Features[x,y] = relu(Filter[dx,dy,ch] Image[x+dx, y+dy, ch])
```

A graph neural network aggregation step:

```text
Agg[n, l, d]   = Neig(n, n') Z[n', l, d]
Emb[n, l+1, d] = relu(W_Agg[d] Agg[n,l,d] + W_Self[d] Emb[n,l,d])
```

Attention uses a third index notation, the **`.`-suffixed index**, for normalization:

```text
Comp[b, h, p, p'.] = softmax(Query[b,h,p,d_k] Key[b,h,p',d_k] / sqrt(D_k))
```

A `.`-suffixed index marks the **normalization axis**: for every combination of the other indices, the named function (here softmax) is applied to the full slice along the dotted index and returns a normalized version of it. This is necessary because softmax is not elementwise and cannot be expressed as a plain einsum — it requires each element to be divided by a sum that depends on all elements along the same axis. The `.` tells the runtime to group along that axis before applying the function.

The same notation appears at the output layer to normalize over the vocabulary:

```text
Y[p, t.] = softmax(W_O[t,d] Stream[B,p,d])
```

Here softmax normalizes over `t` (tokens) for each position `p`, producing a probability distribution. Any vector normalization that cannot be decomposed elementwise — softmax, layer norm, log-sum-exp — requires this notation.

Together, the three index notations cover the three ways an index can appear on the LHS of a tensor equation:

| Notation | Meaning |
| --- | --- |
| `i` | plain output index — the result tensor is indexed by i |
| `*t` | virtual index — iterated in-place, no storage allocated for t |
| `t.` | normalization axis — the function is applied as a whole-vector operation over t |

An entire transformer can be written in roughly a dozen tensor equations (see Domingos 2025, Table 2).

### Inference and Learning

**Inference** uses tensor generalizations of forward chaining (execute equations in order until fixpoint) and backward chaining (lazy evaluation from a query).

**Learning** is structurally simple: because the gradient of a tensor equation is another tensor equation, backpropagation through a tensor logic program is itself a tensor logic program. If

```text
Y[...] = T[...] X₁[...] ... Xₙ[...]
```

then

```text
∂Y[...]/∂T[...] = X₁[...] ... Xₙ[...]
```

The full gradient of a loss L with respect to any tensor T is a sum over equations, and is automatically expressible in tensor logic.

### Reasoning in Embedding Space

The most novel contribution of tensor logic is the ability to do sound reasoning in embedding space. If object embeddings are learned (rather than one-hot), then replacing Boolean tensors with real-valued embedding matrices turns deductive inference into **analogical reasoning**: similar objects borrow inferences from each other, with weight proportional to similarity.

The transition from deductive to analogical is controlled by a temperature parameter in a sigmoid:

```text
σ(x, T) = 1 / (1 + e^{−x/T})
```

At T→0, the Gram matrix of embeddings approaches the identity matrix, and reasoning is purely deductive (no hallucination). As T increases, reasoning becomes increasingly analogical. This combines the scalability of neural networks with the soundness of symbolic reasoning.

### Implementation in PyRel

PyRel is an extension of Datalog that subsumes tensor logic. Tensor logic equations can be written directly as PyRel rules, with tensors represented as relations and contractions expressed as aggregations over shared index variables. See [tensor_logic_in_pyrel.md](tensor_logic_in_pyrel.md) for a systematic translation guide with worked examples.

### Einsum as the Foundation

Tensor logic's core claim — that Datalog rules and neural network layers are based on the same operations — rests on a precise notion of what those operations are. The operations are einsums. Every tensor equation in tensor logic is an einsum (or a composition of einsums with a nonlinearity), and the algebraic laws that make tensor logic programs well-behaved — the ability to reorder, factor, and decompose tensor equations — are exactly the commutativity, distributivity, and associativity of einsum. The next section gives einsum a formal treatment: its syntax, its semantics over commutative semirings, and the equivalence rules that govern how expressions can be reshaped. This provides the mathematical substrate on which the unification claim in The Connection section is built.

---

## Einsum

### What It Is

Einsum (Einstein summation) is a notation for expressing tensor computations introduced to NumPy in 2011, now standard across PyTorch, TensorFlow, and Julia (Tullio.jl). It generalizes all linear and multilinear operations — matrix products, traces, contractions, outer products, transpositions — under a single uniform syntax, replacing the proliferation of named operations in linear algebra with a single parametric one.

### Syntax

An einsum expression has the form:

```text
#(I₁, ..., Iₙ → I;  T₁, ..., Tₙ)
```

- `I₁,...,Iₙ` are **input index strings**, one per tensor argument
- `I` is the **output index string**
- `T₁,...,Tₙ` are the tensor **arguments**

Each letter in an index string names an axis. Every symbol appearing in the output must appear in at least one input string; symbols that appear only in inputs are **summed over** (contracted). Common operations expressed as einsums:

| Operation | Linear algebra | Einsum |
| --- | --- | --- |
| Matrix product | A · B | `#(ij, jk → ik; A, B)` |
| Transposition | Aᵀ | `#(ij → ji; A)` |
| Inner product | xᵀy | `#(i, i → ; x, y)` |
| Outer product | xyᵀ | `#(i, j → ij; x, y)` |
| Trace / diagonal | diag(A) | `#(ii → i; A)` |
| Broadcast to diagonal | diag(v) | `#(i → ii; v)` |

### Formal Semantics

A tensor is a mapping from **positions** (multi-indices) to values in a **commutative semiring** (R, ⊕, ⊗). The standard arithmetic semiring is (ℝ, +, ×); other notable examples are the Viterbi semiring (max-product) and the Tropical semiring (min-plus), enabling shortest-path and max-product inference with identical notation.

The semantics of an einsum expression is defined via **global positions**: the set X of all assignments of values to every index symbol appearing anywhere in the expression. Each global position x̂ projects onto an output position x via the output index string I. The result tensor is:

```text
T(x) = ⊕_{x̂: I→x}  ⊗ᵢ Tᵢ(x̂: Iᵢ)
```

In words: for each output position x, **aggregate** (sum) over all global positions that project to x, the **combination** (product) of the corresponding entries from each input tensor. This two-level structure — combine then aggregate — is what makes einsum simultaneously a product and a sum.

### Algebraic Properties

Wenig, Rump, Blacher, and Giesen (2025) provide the first formal proofs of the following:

- **Commutativity**: reordering tensor arguments leaves the result unchanged (because ⊗ is commutative)
- **Associativity**: a flat n-ary einsum can be decomposed into nested binary einsums in any order; equivalently, nested binary einsums can be flattened
- **Distributivity**: einsum distributes over elementwise aggregation (⊕), enabling factoring like AB + AC = A(B+C)

### Nesting, Denesting, and Contraction Paths

Associativity means a large einsum over n tensors can be evaluated as a sequence of n−1 binary einsums. The choice of evaluation order is called a **contraction path** and has enormous impact on computational cost (finding the optimal path is NP-hard). Nested einsums can always be **denested** (flattened) into a single expression, with care needed when inner and outer expressions share index symbols. The general denesting procedure uses **delta tensors** (Kronecker deltas) to split shared indices, applies restricted denesting, then merges indices back.

Delta tensors are themselves expressible as einsums and satisfy useful simplification rules:

- Any delta tensor can be removed from an expression, leaving only a scalar and one all-ones vector per affected index
- Delta tensors of any order decompose into products of unit matrices δ₁

---

## The Connection

### Einsum Is the Primitive Operation of Both

Einsum is the single computational primitive underlying both neural computation and logical inference. The two paradigms share identical formal structure:

| | Neural computation | Logical inference |
| --- | --- | --- |
| Data | Real-valued tensors | Boolean tensors (relations) |
| Combination | Multiplication | Conjunction (AND / product) |
| Aggregation | Summation | Existential quantification (OR / sum + step) |
| Operation | Einsum over (ℝ, +, ×) | Einsum over (𝔹, ∨, ∧) + step |

The difference is:

1. The **semiring**: arithmetic vs. Boolean
2. The optional **threshold nonlinearity** (Heaviside step) that converts a count of witnesses back to a Boolean

All else — joins, projections, contractions, broadcasting — is structurally identical.

### The Semiring Perspective

Wenig et al.'s formal treatment makes this precise: einsum is defined over any commutative semiring, not just the arithmetic one. The Boolean semiring (𝔹, ∨, ∧) is a commutative semiring, and einsum over it is exactly the relational join-and-project (modulo the step function). The Viterbi semiring gives max-product inference. The Tropical semiring gives shortest paths. These are all instances of the same formal structure, evaluated under different semirings.

### The Language Question

Tensor logic's contribution is to ask: if einsum is the fundamental operation of both neural and symbolic AI, what does a programming language look like if it is built around that operation? The answer is a language in which:

- Every statement is a tensor equation
- Symbolic knowledge is represented as Boolean (or sparse real-valued) tensors
- Neural components are dense real-valued tensors
- Computation is uniform: einsum + nonlinearity throughout
- Gradient computation is free: it is also a tensor logic program
- The neural-symbolic boundary is controlled by a single temperature parameter

### Practical Implications

The formal equivalence has several practical consequences:

- **Database engines and tensor engines are solving the same problem**: query evaluation is a sequence of join-project operations; tensor contraction is a sequence of einsum operations. The same optimization techniques (contraction paths, join-order optimization, sparsity exploitation) apply to both.
- **Sparse tensors are relations**: sparse tensor operations can be offloaded to relational database engines; dense subtensors can be handled on GPUs. A single program can mix both.
- **Tucker decomposition generalizes predicate invention**: learning a Tucker decomposition A[i,j,k] = M[i,p] M'[j,q] M''[k,r] C[p,q,r] is equivalent to learning latent predicates that explain the data — the tensor analog of inductive logic programming.
- **Einsum rewriting = query rewriting**: the algebraic equivalence rules (commutativity, associativity, distributivity, nesting/denesting) that Wenig et al. prove for einsum are exactly the query rewriting rules used to optimize relational queries.

---

## References

- Domingos, P. [*Tensor Logic: The Language of AI*](https://arxiv.org/abs/2510.12269). arXiv:2510.12269v3, 2025.
- Wenig, M., Rump, P.G., Blacher, M., Giesen, J. [*The Syntax and Semantics of einsum*](https://arxiv.org/abs/2509.20020). arXiv:2509.20020v3, 2025.
