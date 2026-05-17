# Functoriality of $[a, \cdot] : \mathbf{St}^{\mathrm{op}} \to \mathbf{Br}$

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

See [theory.md §Broadcasting](papers/theory.md#L227) for background on the `Broadcasted` structure (degree, weaves, reindexings, and operator).

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

## Why $[a, \cdot]$ is Contravariant

**A stride morphism $\eta$ specifies where to *look*, not where to *write*.**

Consider the rearrangement $\eta : P \to Q$ in **St** where $P$ has 4 axis slots ($I = \{0,1,2,3\}$) and $Q$ has 2 axis slots ($J = \{0,1\}$), defined by $\mu : J \to I$ with

$$\mu(0) = 1, \qquad \mu(1) = 3$$

That is, output slot 0 draws from input slot 1, and output slot 1 draws from input slot 3. The coefficient matrix is $\Lambda \in \mathbb{N}^{4 \times 2}$ with $\Lambda_{ij} = [\mu(j)=i]$, so the element action contracts 4D to 2D:

$$p\Lambda = (p_{\mu(0)},\, p_{\mu(1)}) = (p_1,\, p_3) \qquad p \in \text{El}(P)$$

In **St**, the morphism flows $P \to Q$ — a contraction. The induced morphism in **Br** flows the *opposite* way, $[a, \eta] : [a, Q] \to [a, P]$: it takes a 2D array $X$ indexed over $\text{El}(Q)$ and produces a 4D array $Y$ indexed over $\text{El}(P)$:

$$Y[p_0, p_1, p_2, p_3] = X[p_1, p_3]$$

$Y$ is a broadcasting of $X$ over the two unused axes — it does not depend on $p_0$ or $p_2$ at all. So $\eta$ contracts (4D $\to$ 2D in **St**) while $[a,\eta]$ expands (2D $\to$ 4D in **Br**); the direction reverses.

**Why?** The morphism $\eta : P \to Q$ is a lookup recipe: given position $p \in \text{El}(P)$, it tells you which position $p\Lambda \in \text{El}(Q)$ to read from. To *execute* that recipe you must already have an array on $Q$ — and the result is an array on $P$. So $[a, \eta]$ consumes an input indexed by $Q$ and produces an output indexed by $P$, reversing the arrow.

**Two perspectives on the same rearrangement.** The function $\mu : J \to I$ maps output index positions to input index positions (output $\to$ input), while the element action $p\Lambda$ maps $\text{El}(P) \to \text{El}(Q)$ (input $\to$ output in **St**). These are the same data viewed from opposite ends: the identity $(p\Lambda)_j = p_{\mu(j)}$ says "the $j$-th output coordinate is the $\mu(j)$-th input coordinate." $\mu$ traces back which slot to pull from; $p\Lambda$ assembles the result. The reversal in **Br** is not a coincidence — it is exactly what it means for $\eta$ to be a lookup rather than a write.
