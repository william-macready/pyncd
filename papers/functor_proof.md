# Functoriality of $[a, \cdot] : \mathbf{St}^{\mathrm{op}} \to \mathbf{Br}$

$[a, \cdot]$ is a contravariant functor from **St** to **Br**. Before validating the functor laws we motivate why the contravariance arises.

---

## Contents

1. [Why $[a, \cdot]$ is Contravariant](#why-a-cdot-is-contravariant)
2. [Setup](#setup)
3. [Proof: $[a, \cdot]$ Preserves Composition (Contravariantly)](#proof-a-cdot-preserves-composition-contravariantly)
4. [Corollary: $[a, \cdot]$ Preserves Identities](#corollary-a-cdot-preserves-identities)
5. [$\Lambda$ as a Broadcasted Operation](#lambda-as-a-broadcasted-operation)
6. [Lean 4 Proof: Functoriality of $[a, \cdot]$](#lean-4-proof-functoriality-of-a-cdot)
   - [Syntactic vs semantic equality](#syntactic-vs-semantic-equality)
   - [Element and array types](#element-and-array-types)
   - [Element action of a stride matrix](#element-action-of-a-stride-matrix)
   - [Composition and identity of applyStMat](#composition-and-identity-of-applystmat)
   - [Pullback: the morphism action of $[a, \cdot]$](#pullback-the-morphism-action-of-a-cdot)
   - [Functoriality theorems](#functoriality-theorems)
   - [Proof obligations](#proof-obligations)

---

## Why $[a, \cdot]$ is Contravariant

The morphism action of $[a,\cdot]$ reverses arrows: a stride morphism $\Lambda : P \to Q$ in **St** induces $[a,\Lambda] : [a,Q] \to [a,P]$ in **Br**. The examples below show why no other direction is possible. The remainder of this document then verifies that this reversal is functorial — preserving composition and identities.

**Simplest case.** Ignore $\text{El}$ entirely and think of objects as plain index sets and morphisms as plain functions $f : I \to J$. Then $[a, I]$ is just an array of length $|I|$, and $[a, f]$ is defined by:

$$([a, f](X))[i] = X[f(i)]$$

where $X \in [a, J]$. To evaluate $X[f(i)]$ you need $X$ indexed by $J$ (the codomain of $f$), and you get back something indexed by $I$ (the domain). Contravariance is the direction forced by precomposition.

The coordinate machinery introduced in Setup below replaces the scalar index $i \in I$ with a coordinate tuple $p \in \text{El}(P)$ and the function $f$ with matrix multiplication $p \mapsto p\Lambda$; every argument goes through unchanged.

---

**Example 1: $I = \{0,1,2,3\}$, $J = \{0,1\}$.** The rearrangement $\eta : P \to Q$ is defined by $\mu(0) = 1$, $\mu(1) = 3$, so the element action contracts 4D to 2D:

$$p\Lambda = (p_1,\, p_3) \qquad p \in \text{El}(P)$$

The induced morphism $[a, \eta] : [a, Q] \to [a, P]$ expands in the opposite direction:

$$Y[p_0, p_1, p_2, p_3] = X[p_1, p_3]$$

$Y$ broadcasts $X$ over the two unused axes; $p_0$ and $p_2$ are ignored. A covariant map $[a, P] \to [a, Q]$ would need to assign a value to each $q = (q_0, q_1)$ from $Y$, but all of $(p_0, q_0, p_2, q_1)$ for arbitrary $p_0, p_2$ share the same image — so infinitely many $Y$-values compete for each slot in $X$ with no canonical way to combine them. The element action is many-to-one; the covariant direction is undefined.

---

**Example 2: $I = \{0,1\}$, $J = \{0,1,2\}$.** The rearrangement $\eta : P \to Q$ is defined by $\mu(0) = 0$, $\mu(1) = 1$, $\mu(2) = 0$ — slot 2 of $Q$ duplicates slot 0 of $P$ — so the element action expands 2D to 3D:

$$p\Lambda = (p_0,\, p_1,\, p_0) \qquad p \in \text{El}(P)$$

The induced morphism $[a, \eta] : [a, Q] \to [a, P]$ contracts in the opposite direction:

$$Y[p_0, p_1] = X[p_0,\, p_1,\, p_0]$$

This is a *diagonal restriction*: $Y$ sees only the slice of $X$ where the third index equals the first. A covariant map $[a, P] \to [a, Q]$ would need to assign a value to each $q \in \text{El}(Q)$ from $Y$. But the image of the element action is only the diagonal $\{q : q_2 = q_0\}$; for $q$ off it — say $q = (0, 1, 1)$ — there is no $p$ with $p\Lambda = q$, so the assignment $X[q_0, q_1, q_2] \mathrel{:=} Y[\,?\,]$ is undefined. The element action is injective but not surjective; the covariant direction is again undefined.

**Why precomposition is the only well-typed direction.** The element action $p \mapsto p\Lambda$ is a total function $\text{El}(P) \to \text{El}(Q)$: for any $p$, the index $p\Lambda$ is a valid element of $\text{El}(Q)$, so $X[p\Lambda]$ is always defined. This makes the pullback $Y[p] \mathrel{:=} X[p\Lambda]$ well-typed for every $X \in [a, Q]$, producing output in $[a, P]$ — the arrow reverses. Any covariant assignment would require inverting $p\Lambda$, but a stride morphism need be neither injective (Example 1) nor surjective (Example 2). Contravariance is not a design choice; it is the only direction that is always well-defined.

---

## Setup

A stride morphism $\Lambda : P \to Q$ in **St** is a finite linear transform. Treating elements as row vectors, the induced coordinate map is

$$(p\Lambda)_j = \sum_{i \in I} p_i\, \Lambda_{ij} \qquad j \in J$$

where $I$ and $J$ are the axis index sets of $P$ and $Q$ respectively, $\Lambda \in \mathbb{N}^{I \times J}$ is the coefficient matrix, and $p = (p_i)_{i \in I} \in \text{El}(P)$. The matrix shape $I \times J$ matches the direction $P \to Q$: $p$ has $|I|$ entries and $p\Lambda$ has $|J|$ entries. **Rearrangements** are the special case where $\Lambda_{ij} = [\mu(j) = i]$ for some function $\mu : J \to I$ — each output coordinate $j$ selects exactly one input coordinate: $(p\Lambda)_j = p_{\mu(j)}$. Input $i$ may be selected by multiple outputs (duplication), exactly one (copy), or none (deletion); deletion is the reason column sums need not be 1.

Composition of stride morphisms acts on coordinates sequentially: $(\eta \mathbin{;} \mu)(p) = \mu(\eta(p))$ — apply $\eta$ first, then $\mu$. In matrix terms, if $\eta$ has matrix $\Lambda \in \mathbb{N}^{I \times J}$ and $\mu$ has matrix $M \in \mathbb{N}^{J \times K}$, the composite has matrix $\Lambda M \in \mathbb{N}^{I \times K}$ and acts as $p \mapsto (p\Lambda)M$.

For a fixed datatype $a$, the functor $[a, \cdot]$ acts on **objects** by sending each $P \in \mathbf{St}$ to the array object $[a, P] \in \mathbf{Br}$ — the collection of $a$-valued functions on $\text{El}(P)$:

$$[a, P] = \{ x : \text{El}(P) \to a \}$$

On **morphisms**, it assigns to each stride morphism $\Lambda : P \to Q$ a morphism $[a, \Lambda] : [a, Q] \to [a, P]$ in **Br** — the *identity reindexing* — whose element action is:

$$(x_q)_{q \in \text{El}(Q)} \mathbin{;} [a, \Lambda] = (x_{p\Lambda})_{p \in \text{El}(P)}$$

Output position $p$ reads from input position $p\Lambda \in \text{El}(Q)$. For a rearrangement this selects $x_{(p\Lambda)_j} = x_{p_{\mu(j)}}$ — pure axis permutation/selection. For general $\Lambda$ it computes a new coordinate by integer linear combination, e.g. $\Lambda = \bigl(\begin{smallmatrix}1 \\ 1\end{smallmatrix}\bigr) \in \mathbb{N}^{2 \times 1} : (x', w) \mapsto x' + w$ gives $Y[x', w] = X[x' + w]$ (translation).

## Proof: $[a, \cdot]$ Preserves Composition (Contravariantly)

**Claim:** For composable stride morphisms $\Lambda : P \to Q$ and $M : Q \to R$ in **St**,

$$[a, \Lambda \mathbin{;} M] = [a, M] \mathbin{;} [a, \Lambda]$$

Noting the contravariance, both sides are morphisms $[a, R] \to [a, P]$ in **Br**.

---

**Step 1: Reduce to the elemental criterion.**

**Br** is elemental: it suffices to show that $[a, \Lambda \mathbin{;} M]$ and $[a, M] \mathbin{;} [a, \Lambda]$ agree on every input element of $[a, R]$.

---

**Step 2: Fix an arbitrary element of $[a, R]$ and compute both sides.**

Let $x = (x_r)_{r \in \text{El}(R)} \in \text{El}([a, R])$ be arbitrary.

**Left side.** The composite $\Lambda \mathbin{;} M$ has matrix $\Lambda M$, so the element-action equation gives: for each $p \in \text{El}(P)$, the output at position $p$ is $x_r$ where $r = p(\Lambda M) \in \text{El}(R)$:
$$x \mathbin{;} [a, \Lambda \mathbin{;} M] = \bigl(x_{p(\Lambda M)}\bigr)_{p \in \text{El}(P)}$$

**Right side.** Compute $x \mathbin{;} \bigl([a, M] \mathbin{;} [a, \Lambda]\bigr)$ in two stages.

*Stage 1* — apply $[a, M] : [a, R] \to [a, Q]$ to $x$. The element-action equation (with $M : Q \to R$ playing the role of $\Lambda$) gives: for each $q \in \text{El}(Q)$, the output at position $q$ is $x_r$ where $r = qM \in \text{El}(R)$:
$$x \mathbin{;} [a, M] = \bigl(x_{qM}\bigr)_{q \in \text{El}(Q)}$$

Call this intermediate array $y = (y_q)_{q \in \text{El}(Q)}$, where $y_q = x_{qM}$.

*Stage 2* — apply $[a, \Lambda] : [a, Q] \to [a, P]$ to $y$. The element-action equation gives: for each $p \in \text{El}(P)$, the output at position $p$ is $y_q$ where $q = p\Lambda \in \text{El}(Q)$:
$$y \mathbin{;} [a, \Lambda] = \bigl(y_{p\Lambda}\bigr)_{p \in \text{El}(P)} = \bigl(x_{(p\Lambda)M}\bigr)_{p \in \text{El}(P)}$$

where the second equality substitutes $y_{p\Lambda} = x_{(p\Lambda)M}$.

**Both sides agree** because $p(\Lambda M) = (p\Lambda)M$ — matrix multiplication is associative.

---

**Step 3: Conclude.**

Since $x \in \text{El}([a, R])$ was arbitrary, the elemental criterion gives:

$$[a, \Lambda \mathbin{;} M] = [a, M] \mathbin{;} [a, \Lambda] \qquad \square$$

---

## Corollary: $[a, \cdot]$ Preserves Identities

**Claim:** For any object $A \in \mathbf{St}$ and datatype $a$, $[a, I_A] = \text{id}_{[a,A]}$, where $I_A$ is the identity stride morphism (identity coefficient matrix).

The element-action equation gives $x \mathbin{;} [a, I_A] = (x_{pI_A})_p = (x_p)_p = x = x \mathbin{;} \text{id}_{[a,A]}$, since $pI_A = p$. The elemental criterion gives $[a, I_A] = \text{id}_{[a,A]}$. $\square$

---

## $\Lambda$ as a Broadcasted Operation

See [theory.md §Broadcasting](papers/theory.md#broadcasting) for background on the `Broadcasted` structure (degree, weaves, reindexings, and operator).

Every stride morphism $\Lambda : P \to Q$ in **St** can be represented as a `Broadcasted` morphism $[a, \Lambda] : [a, Q] \to [a, P]$ in **Br** with the following structure:

| Field | Value |
| --- | --- |
| **Operator** | Identity (no computation on values) |
| **Degree** | $P$ — one iteration per output position |
| **Input weave** | $[a, Q]$ with all axes tiled — the full input is indexed by the degree |
| **Output weave** | $[a, P]$ with all axes tiled — each output position is written once |
| **Reindexing** | $\Lambda : P \to Q$ — at degree coordinate $p$, reads input at $p\Lambda \in \text{El}(Q)$ |

The element action is $Y[p] = X[p\Lambda]$ for all $p \in \text{El}(P)$, which is exactly the identity reindexing equation above.

**Rearrangements** ($\Lambda$ a 0-1 selection matrix) are the degenerate case: $p\Lambda$ selects a single input coordinate per output position, giving axis permutation, duplication ($\mu(j_1) = \mu(j_2)$), or deletion (some $i \notin \text{img}(\mu)$).

**General $\Lambda$** computes a new coordinate by integer linear combination. The two canonical examples from the theory:

- **Strided access** $\Lambda = (s) : (p) \mapsto (sp)$ — reads every $s$-th element: $Y[p] = X[sp]$.
- **Translation** $\Lambda = (1\ \ 1) : (x', w) \mapsto x' + w$ — unfolds a sliding window: $Y[x', w] = X[x' + w]$.

In practice, a stride morphism $\Lambda$ with coefficients $> 1$ rarely appears as a standalone `Broadcasted`; it more commonly appears as the reindexing $\eta_i$ *within* a `Broadcasted` that has a non-trivial operator (e.g. the affine scaling case $Y[b,p] = \sum_w X[b, s{\cdot}p + w]\, W[w]$ where $\Lambda$ is the reindexing $\eta_X(b,p) = (b,\, s{\cdot}p)$). In that role, $\Lambda$ specifies which slice of the input each iteration of the base operator sees, while the operator itself performs the value computation.

---

## Lean 4 Proof: Functoriality of $[a, \cdot]$

The definitions below use `StMat`, `Numeric`, and `BrMorph` from [leanncd.md](./leanncd.md). All types are Layer 1.

### Syntactic vs semantic equality

`BrMorph` is the **free category** on `BrBase` — morphisms are linked lists and composition is list concatenation. As a result, `[a, Λ ; M]` (a single-element list) and `[a, M] ; [a, Λ]` (a two-element list) are not definitionally equal as `BrMorph` values, even though they compute the same output on every input array.

Functoriality is therefore stated and proved at the **element-action level**: we exhibit the semantic function each side computes and prove the functions equal. This matches the mathematical proof, which uses the elemental criterion to reduce equality of morphisms to equality of their actions on elements.

### Element and array types

```lean
/-- A shape element: a symbolic coordinate tuple, one `Numeric` entry per axis. -/
def El (P : StObj) : Type := Fin P.length → Numeric

/-- An array of type `a` indexed by shape `P`. -/
def Arr (a : Type) (P : StObj) : Type := El P → a
```

`El P` uses `Numeric` coordinates rather than `ℕ` so that symbolic axis sizes need not be made concrete at proof time.

### Element action of a stride matrix

```lean
/-- `applyStMat Λ p` applies stride matrix `Λ : StMat P Q` to coordinate `p ∈ El P`,
    yielding coordinate `pΛ ∈ El Q`.
    Formula: `(pΛ)_i = Λ.bias i + Σ_j p j * Λ.coeffs i j`. -/
def applyStMat {P Q : StObj} (Λ : StMat P Q) (p : El P) : El Q :=
  fun i => Λ.bias i + ∑ j : Fin P.length, p j * Λ.coeffs i j
```

The sum matches the affine formula from [leanncd.md §4](papers/leanncd.md): `coeffs i j` is the $(i,j)$ entry of the coefficient matrix with $i$ indexing the codomain and $j$ the domain.

### Composition and identity of applyStMat

```lean
/-- Applying `Λ.comp M` equals applying `Λ` then `M`.
    Proof: unfold both sides; the goal is a polynomial identity over `Numeric`,
    closed by `ring` given `CommSemiring Numeric`. -/
theorem applyStMat_comp {P Q R : StObj}
    (Λ : StMat P Q) (M : StMat Q R) (p : El P) :
    applyStMat (StMat.comp Λ M) p = applyStMat M (applyStMat Λ p) := by
  funext i
  simp only [applyStMat, StMat.comp,
             Finset.sum_add_distrib, Finset.mul_sum,
             Finset.sum_mul, ← Finset.sum_comm]
  ring   -- requires CommSemiring Numeric (see leanncd.md §9.6)

/-- `StMat.id` acts as the identity coordinate map. -/
theorem applyStMat_id {P : StObj} (p : El P) :
    applyStMat (StMat.id P) p = p := by
  funext i
  simp only [applyStMat, StMat.id,
             Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
```

`applyStMat_comp` is the coordinate-level content of matrix multiplication associativity — the same fact that closes Step 2 of the mathematical proof via $p(\Lambda M) = (p\Lambda)M$.

### Pullback: the morphism action of $[a, \cdot]$

```lean
/-- `pullback Λ x` pulls array `x : Arr a Q` back along `Λ : StMat P Q`
    to produce an array on `P`. This is the element action of `[a, Λ] : [a, Q] → [a, P]`:
    for each output position `p ∈ El P`, read from input position `applyStMat Λ p ∈ El Q`. -/
def pullback {a : Type} {P Q : StObj}
    (Λ : StMat P Q) (x : Arr a Q) : Arr a P :=
  fun p => x (applyStMat Λ p)
```

### Functoriality theorems

```lean
/-- Identity law: pulling back along the identity stride morphism is the identity on arrays.
    Element-level content of `[a, id_P] = id_{[a, P]}`. -/
theorem pullback_id {a : Type} {P : StObj} (x : Arr a P) :
    pullback (StMat.id P) x = x := by
  funext p
  simp [pullback, applyStMat_id]

/-- Contravariant composition law: pulling back along `Λ.comp M` equals
    pulling back along `M` then along `Λ`.
    Element-level content of `[a, Λ ; M] = [a, M] ; [a, Λ]`. -/
theorem pullback_comp {a : Type} {P Q R : StObj}
    (Λ : StMat P Q) (M : StMat Q R) (x : Arr a R) :
    pullback (StMat.comp Λ M) x = pullback Λ (pullback M x) := by
  funext p
  simp only [pullback, applyStMat_comp]
```

`pullback_comp` is a one-liner once `applyStMat_comp` is established: unfolding both sides reduces the goal to `x (applyStMat (Λ.comp M) p) = x (applyStMat M (applyStMat Λ p))`, which is immediate from `applyStMat_comp` and congruence. This mirrors Step 3 of the mathematical proof (the elemental criterion step).

### Proof obligations

| Theorem | Status | Dependency |
| --- | --- | --- |
| `applyStMat_id` | **Closed** by `simp` + `ring` | `CommSemiring Numeric` |
| `applyStMat_comp` | **Closed** by `simp` + `ring` | `CommSemiring Numeric` |
| `pullback_id` | **Closed** by `simp` + `applyStMat_id` | — |
| `pullback_comp` | **Closed** by `simp` + `applyStMat_comp` | — |
| `CommSemiring Numeric` | **Open** (`sorry`) | See [leanncd.md §9.6](papers/leanncd.md) |

The only open obligation is `CommSemiring Numeric`, which is shared with `StMat.assoc` in the PROP instance for **St**. Every other step is either a definitional unfolding or a `ring` call.
