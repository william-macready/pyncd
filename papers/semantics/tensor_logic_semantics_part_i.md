# Tensor Logic semantics - Part I: Background notation

[Previous: Introduction](tensor_logic_semantics.md) | [Contents](README.md) | [Next: Part II: Core language and surface elaboration](tensor_logic_semantics_part_ii.md)

## In this part

- [Part I: Background notation](#part-i-background-notation)
- [1. Numbers, finite sets, and functions](#1-numbers-finite-sets-and-functions)
  - [1.1 Number systems and finite intervals](#11-number-systems-and-finite-intervals)
  - [1.2 Tuples, products, and rank-zero cases](#12-tuples-products-and-rank-zero-cases)
  - [1.3 Functions and inverse images](#13-functions-and-inverse-images)
- [2. Scalar algebras and finite combination](#2-scalar-algebras-and-finite-combination)
  - [2.1 The scalar carrier](#21-the-scalar-carrier)
  - [2.2 Finite sums and products](#22-finite-sums-and-products)
  - [2.3 Which algebraic laws each part uses](#23-which-algebraic-laws-each-part-uses)
  - [2.4 Scalar sorts](#24-scalar-sorts)
- [3. Axes, index variables, and valuations](#3-axes-index-variables-and-valuations)
  - [3.1 Axes and identities](#31-axes-and-identities)
  - [3.2 Index variables and contexts](#32-index-variables-and-contexts)
  - [3.3 Valuations](#33-valuations)
- [4. Tensor signatures, coordinates, and values](#4-tensor-signatures-coordinates-and-values)
  - [4.1 Signatures and coordinate domains](#41-signatures-and-coordinate-domains)
  - [4.2 Tensor values](#42-tensor-values)
- [5. Environments and stores](#5-environments-and-stores)
  - [5.1 Complete tensor environments](#51-complete-tensor-environments)
  - [5.2 Partial stores and available values](#52-partial-stores-and-available-values)
  - [5.3 Logical addresses, physical slots, and proof-only history](#53-logical-addresses-physical-slots-and-proof-only-history)
- [6. Index expressions and coordinate maps](#6-index-expressions-and-coordinate-maps)
  - [6.1 Evaluating index expressions](#61-evaluating-index-expressions)
  - [6.2 Read maps and write maps](#62-read-maps-and-write-maps)
- [7. Free indices, contraction, and broadcasting](#7-free-indices-contraction-and-broadcasting)
- [8. Operators, predicates, and definedness](#8-operators-predicates-and-definedness)
- [9. Programs and contribution occurrences](#9-programs-and-contribution-occurrences)
  - [9.1 Statement identities](#91-statement-identities)
  - [9.2 Tagged contribution occurrences](#92-tagged-contribution-occurrences)
- [10. Equality, source notation, and interpretation brackets](#10-equality-source-notation-and-interpretation-brackets)
- [11. Running examples fixing the notation](#11-running-examples-fixing-the-notation)
  - [11.1 Boundary contributions](#111-boundary-contributions)
  - [11.2 Colliding affine writes](#112-colliding-affine-writes)
  - [11.3 Activation before versus after collection](#113-activation-before-versus-after-collection)
  - [11.4 A finite history with persistent input](#114-a-finite-history-with-persistent-input)
- [12. Notation for operational and proof rules](#12-notation-for-operational-and-proof-rules)

## Part I: Background notation

This part fixes the mathematical objects shared by the core language,
both semantics, and the compilation contracts. Its source examples illustrate
contributions; their explicit syntax and interpretation are defined in
Parts [II](tensor_logic_semantics_part_ii.md#part-ii-core-language-and-surface-elaboration) and [III](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics).

## 1. Numbers, finite sets, and functions

### 1.1 Number systems and finite intervals

We use:

- $\mathbb{N}=\{0,1,2,\ldots\}$ for natural numbers, including zero.
- $\mathbb{Z}$ for integers.
- $\mathbb{R}$ for exact real numbers.
- $\mathbb{B}=\{\mathrm{false},\mathrm{true}\}$ for Booleans.

For $n\in\mathbb{N}$, define the finite ordinal

```math
[n]=\{k\in\mathbb{N}\mid k<n\}.
```

Thus $[0]=\varnothing$, $[1]=\{0\}$, and $[4]=\{0,1,2,3\}$.
The notation $[n]$ is a set, not a one-element list containing $n$.

A statement ranging over $l\in[N]$ visits $0,\ldots,N-1$. A history with a
base state and $N$ recurrence steps has time domain $[N+1]$, containing
$0,\ldots,N$.

For a finite set $A$, $|A|$ denotes its cardinality. For example,
$|[4]|=4$.

### 1.2 Tuples, products, and rank-zero cases

An ordered tuple is written $(a_1,\ldots,a_k)$. Its positions matter:
$(0,1)$ and $(1,0)$ need not denote the same coordinate.
In coordinate and shape notation, $(a)$ denotes a one-component tuple,
whereas $()$ denotes the empty tuple.

The Cartesian product

```math
A_1\times\cdots\times A_k
```

contains the tuples whose $j$th component belongs to $A_j$.

The product of no sets is the singleton $\{()\}$ containing the empty tuple.
This convention lets a scalar be treated as a rank-zero tensor with one
coordinate. By contrast, a product with any empty factor is empty.

**Examples.**

- $[2]\times[3]$ has six coordinates.
- A shape with one zero extent, such as $(2,0,3)$, has no coordinates.
- Shape $()$ has one coordinate, namely $()$.

### 1.3 Functions and inverse images

The notation $f:A\to B$ denotes a total function with domain $A$ and codomain
$B$. We write either $f(a)$ or, for tensors, $f[a]$ for application.
For a function on tuple arguments, $f(a,b)$ abbreviates $f((a,b))$.

Composition is $(g\circ f)(a)=g(f(a))$.

For $b\in B$, the inverse image or **fiber** of $b$ is

```math
f^{-1}(\{b\})=\{a\in A\mid f(a)=b\}.
```

This does not assume that $f$ is invertible.

A function is injective if

```math
f(a)=f(a')\Longrightarrow a=a'.
```

**Example: a write map with collisions.** Let

```math
\textcolor{#5688C7}{\phi}:[2]\times[2]\to[3],
\qquad
\textcolor{#5688C7}{\phi}(i,j)=i+j.
```

Then

```math
\textcolor{#5688C7}{\phi}^{-1}(\{1\})=\{(0,1),(1,0)\}.
```

Two different source coordinates address output coordinate $1$. Such a
collision is legitimate for additive contributions.

We use $\forall$ for universal quantification, $\exists$ for existential
quantification, $\land$ for conjunction, $\lor$ for disjunction, and
$\Longrightarrow$ for implication. The notation
$\{a\in A\mid \textcolor{#9D75C4}{Q}(a)\}$ selects the elements satisfying predicate $\textcolor{#9D75C4}{Q}$.

## 2. Scalar algebras and finite combination

### 2.1 The scalar carrier

$K$ denotes a set of scalar values. The numerical interpretation uses
$K=\mathbb{R}$. Exact reals are mathematical objects; this does not assert that
a Lean runtime stores exact real numbers.

Tensor contraction and contribution collection use a commutative semiring
([Section 2.3](#23-which-algebraic-laws-each-part-uses) records which results use which of its laws)

```math
\mathcal{K}=(K,\oplus,\otimes,0_K,1_K).
```

Specifically:

- $\oplus$ is associative and commutative, with identity $0_K$.
- $\otimes$ is associative and commutative, with identity $1_K$.
- Multiplication distributes over addition.
- $0_K$ is absorbing for multiplication.

The principal interpretations are:

| Interpretation | $K$ | $\oplus$ | $\otimes$ | $0_K$ | $1_K$ |
| --- | --- | --- | --- | --- | --- |
| Numerical | $\mathbb{R}$ | $+$ | $\cdot$ | $0$ | $1$ |
| Boolean | $\mathbb{B}$ | $\lor$ | $\land$ | false | true |
| Max-plus | $\mathbb{R}\cup\{-\infty\}$ | $\max$ | $+$ | $-\infty$ | $0$ |
| Min-plus | $\mathbb{R}\cup\{+\infty\}$ | $\min$ | $+$ | $+\infty$ | $0$ |

The word "additive" means combination by $\oplus$. For Boolean tensors this is
OR, not arithmetic addition of truth values, and for a max-plus tensor it is
$\max$. In the tropical rows $\otimes$ is ordinary addition, so $-\infty$
(respectively $+\infty$) is the absorbing element and the identity of $\oplus$.
Each row satisfies every law listed above on its exact carrier. Machine-number
behavior at infinities (for example the sum $(-\infty)+(+\infty)$ in floating
point) is outside the specified fragment, as for any machine-number carrier.

Subtraction, division, ordering, and nonlinear functions are **not** supplied
by the semiring structure alone. They need an appropriate carrier and their own
specified operations.

### 2.2 Finite sums and products

For a finite indexing set $A$ and a function $v:A\to K$, write

```math
\bigoplus_{a\in A}v(a)
\qquad\text{and}\qquad
\bigotimes_{a\in A}v(a)
```

for finite combination and multiplication. Their empty cases are

```math
\bigoplus_{a\in\varnothing}v(a)=0_K,
\qquad
\bigotimes_{a\in\varnothing}v(a)=1_K.
```

In the numerical interpretation, we also use $\sum$ and $\prod$.

These expressions are indexed by **occurrences**, not by the set of distinct
values. Equal-valued contributions are not deduplicated:

```math
\sum_{a\in[2]}3=6.
```

In the Boolean interpretation, combining two true contributions gives true
because OR is idempotent. Real addition is not idempotent.

Associativity and commutativity make finite combination independent of
enumeration order in this mathematical setting. Floating-point addition does
not satisfy those laws exactly; an implementation correspondence must address
that distinction explicitly.

### 2.3 Which algebraic laws each part uses

The standing assumption is a commutative semiring, but the results use
different fragments of it:

| Used by | Needs |
| --- | --- |
| Contribution collection ([Section 19](tensor_logic_semantics_part_iii.md#19-contribution-collection)), conservation, soundness, finite execution, and progress (Sections [24](tensor_logic_semantics_part_iv.md#24-machine-configurations-and-initialization)-[26](tensor_logic_semantics_part_iv.md#26-conservation-termination-and-correspondence)), and batched accumulation ([Section 32.1](tensor_logic_semantics_part_v.md#321-why-exact-batched-accumulation-refines-individual-steps)) | A commutative monoid $(K,\oplus,0_K)$ on the carrier of each defined tensor |
| Expression interpretation ([Section 18](tensor_logic_semantics_part_iii.md#18-expression-interpretation-and-definedness)), read footprints, read stability ([Section 23](tensor_logic_semantics_part_iv.md#23-read-footprints-and-executable-dependencies)) | No laws: $\oplus$, $\otimes$, $0_K$, $1_K$ are interpreted operations, and a reduction is the ascending fold of [Section 18.3](tensor_logic_semantics_part_iii.md#183-reduction-and-tabulation) |
| Enumeration independence of nested reductions ([Section 15.2](tensor_logic_semantics_part_ii.md#152-statement-variables-and-term-local-contraction)), the pure-einsum correspondence (Proposition 19.1), Sections [17.1](tensor_logic_semantics_part_ii.md#171-index-strings-and-global-valuations)-[17.3](tensor_logic_semantics_part_ii.md#173-connection-to-the-contribution-core) | The commutative-monoid laws of $\oplus$ (associativity, commutativity, identity), the coherence condition, and the bracketing convention below |
| Delta tensors, operand permutation, distribution, neutral operands (Sections [17.4](tensor_logic_semantics_part_ii.md#174-delta-tensors-and-diagonal-identities)-[17.6](tensor_logic_semantics_part_ii.md#176-neutral-operands-and-domain-preservation)) | The full semiring laws: $\otimes$ associative and commutative with identity $1_K$, distributivity, and $0_K$ absorbing |

No result of Parts [III](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics) and [IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics) uses a law of $\otimes$, distributivity, or
absorption; $1_K$ appears only as the value of a true Iverson predicate.

**Coherence.** An expression combines values with $\oplus$ and uses $0_K$ for an
empty reduction, while collection combines contribution values with $\oplus$
starting from $0_K$. Several results treat these as the same operation and the
same identity, for example the equality of a reduction with its finite
combination ([Section 15.2](tensor_logic_semantics_part_ii.md#152-statement-variables-and-term-local-contraction)), Proposition 19.1, and [Section 27.3](tensor_logic_semantics_part_iv.md#273-guards-empty-binders-and-failure), where an
empty reduction contributes the collection identity. This is an assumption on
the development: the expression-level $\oplus$ and $0_K$ agree with the
collection monoid. The Lean formalization keeps them as separate data and
links them by hypothesis; it evaluates a reduction as an ascending fold, which
equals the finite combination of [Section 2.2](#22-finite-sums-and-products) when the monoid laws and
coherence hold.

**Bracketing.** A finite product of an ordered list of factors is the
left-nested product. The $\bigotimes$ over operands in [Section 17.2](tensor_logic_semantics_part_ii.md#172-canonical-fiber-semantics) and the
product that [Section 15.2](tensor_logic_semantics_part_ii.md#152-statement-variables-and-term-local-contraction) builds from the same factors in the same order use
this nesting, so relating them uses no law of $\otimes$.

A formalization may give each defined tensor its own commutative monoid when it
proves only the results of the first row, which assume no coherence. Wherever
coherence is used, every defined tensor of a sort uses that sort's $\oplus$ and
$0$. No result compares the monoids of different tensors. This document does
not use that freedom.

### 2.4 Scalar sorts

The text is written for one carrier $K$, but nothing in Parts [III](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics)-[IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics) depends
on there being only one. A development may instead fix a family of **sorts**,
each with a carrier $K_s$ and operations $(\oplus_s,\otimes_s,0_s,1_s)$, and a
tensor signature ([Section 4.1](#41-signatures-and-coordinate-domains)) names the sort of its entries. Then:

- A scalar expression has a sort. Literals, tensor reads, Iverson values,
  $\oplus$, $\otimes$, reductions, tabulations, and selection stay within one
  sort, and a tensor read has the sort of the tensor.
- A contribution body has the sort of its destination tensor.
- A registered primitive ([Section 13.2](tensor_logic_semantics_part_ii.md#132-value-types-and-primitive-signatures)) may have input and output types in
  different sorts. This is the only way a value changes sort.
- Collection on a defined tensor uses the monoid of its sort. A sort that is
  the sort of no defined tensor needs no $\oplus$ laws for Sections [19](tensor_logic_semantics_part_iii.md#19-contribution-collection)-[26](tensor_logic_semantics_part_iv.md#26-conservation-termination-and-correspondence);
  enumeration independence of reductions in such a sort needs
  $(K_s,\oplus_s,0_s)$ to be a commutative monoid.
- Every carrier is nonempty, since it contains $0_s$.

The single-carrier text is the case of one sort. The concrete sort family used
for tensor logic is {real, Boolean, max-plus, min-plus}, the rows of the table in
[Section 2.1](#21-the-scalar-carrier). A defined tensor's sort selects the
$\oplus$ and $0_K$ used to collect every contribution addressed to it, whether
the contributions come from one statement or several, and the $\oplus$ and
$0_K$ of the contraction inside each statement's body (the coherence condition
of [Section 2.3](#23-which-algebraic-laws-each-part-uses)).

Implicit conversion between sorts is not part of the core, and neither are
machine-number carriers. A change of sort is a registered primitive with
declared input and output sorts. A surface language may *elaborate* an implicit
conversion into such a primitive. The elaborated conversions are:

- real $\leftrightarrow$ max-plus or min-plus: the identity on the values
  they share. (Real values lie in $\mathbb{R}$, a subset of both tropical
  carriers.)
- Boolean $\to$ any sort $K$: the unique semiring homomorphism, false
  $\mapsto 0_K$ and true $\mapsto 1_K$ of the target sort. This is the same
  rule that gives an Iverson value its meaning in
  [Section 8](#8-operators-predicates-and-definedness).

No conversion is specified from a tropical sort to the Boolean sort, or between
the two tropical sorts.

## 3. Axes, index variables, and valuations

### 3.1 Axes and identities

An axis $a$ has an identity and a finite extent $n_a\in\mathbb{N}$. Its
coordinate range is

```math
\textcolor{#5688C7}{I}_a=[n_a].
```

A printed name is only a label. Distinct axis identities can have the same
label or the same extent. Neither equal spelling nor equal cardinality
establishes identity.
Their coordinate ranges can nevertheless be equal as sets of integers.
Equality of those ranges does not, by itself, identify the axes.

The abstract distinction is relevant to the repository's UID-based axis
representation. The exact correspondence between these mathematical objects
and Lean structures will be specified separately.

### 3.2 Index variables and contexts

An index variable such as $i$ is a bound symbol ranging over a finite domain
$\textcolor{#5688C7}{I}_i$. An **index context** records a finite collection of distinct variable
identities and their domains:

```math
\textcolor{#5688C7}{\Gamma}=(i_1:\textcolor{#5688C7}{I}_{i_1},\ldots,i_k:\textcolor{#5688C7}{I}_{i_k}).
```

Write $\textcolor{#5688C7}{\mathop{\mathrm{vars}}\nolimits}(\textcolor{#5688C7}{\Gamma})=\{i_1,\ldots,i_k\}$ for the set of
variable identities declared in the context.
The affine core uses scalar integer indices. Tuple coordinates are formed
from several such indices; they are not single integer index variables.

Using the same variable twice imposes the same coordinate value twice. Using
different variables allows different values, even when their ranges coincide.

**Example.** In $\textcolor{#9D75C4}{M}[i,i]$, the two slots use one variable and select a
diagonal. In $\textcolor{#9D75C4}{M}[i,j]$, the two slots vary independently.

Variables are scoped by their binders. A consistently renamed bound variable
does not change meaning. Reusing the spelling `i` in separate statements does
not itself relate their valuations.

### 3.3 Valuations

A valuation $\textcolor{#5688C7}{\nu}$ for $\textcolor{#5688C7}{\Gamma}$ assigns each variable a coordinate in its
declared domain. The set of all such valuations is

```math
\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma})
=
\prod_{i\in\textcolor{#5688C7}{\mathop{\mathrm{vars}}\nolimits}(\textcolor{#5688C7}{\Gamma})}\textcolor{#5688C7}{I}_i.
```

Here the product is a dependent family of assignments keyed by variable
identity, not an assertion that variable order matters semantically.

We write $\textcolor{#5688C7}{\nu}(i)$ for the assigned coordinate. We write
$\textcolor{#5688C7}{\nu}[i\mapsto k]$ for extension with a fresh variable or replacement of an
existing variable's binding, with $k\in \textcolor{#5688C7}{I}_i$.

**Example.** For $\textcolor{#5688C7}{\Gamma}=(i:[2],j:[3])$, the valuation
$\textcolor{#5688C7}{\nu}=\{i\mapsto1,j\mapsto2\}$ evaluates $i+j$ to $3$.

An admissible iteration domain can be a subset

```math
\textcolor{#5688C7}{D}\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}),
```

such as the valuations satisfying an explicit guard. A guard restricts
which contributions exist; an Iverson factor changes the value of a
contribution. [Section 13.1](tensor_logic_semantics_part_ii.md#131-index-expressions-and-predicates) makes that distinction explicit in the syntax.

## 4. Tensor signatures, coordinates, and values

### 4.1 Signatures and coordinate domains

$T,\textcolor{#9D75C4}{U},W,\ldots$ denote tensor identifiers. A finite tensor signature $\textcolor{#5688C7}{\Sigma}$ records
the ordered coordinate domains and scalar carrier of each tensor.

For a rank-$k$ tensor $T$, write

```math
\textcolor{#5688C7}{\Sigma}(T)=(\textcolor{#5688C7}{I}_{T,1},\ldots,\textcolor{#5688C7}{I}_{T,k};K),
\qquad
\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)
=\textcolor{#5688C7}{I}_{T,1}\times\cdots\times \textcolor{#5688C7}{I}_{T,k}.
```

Its numerical shape is

```math
\textcolor{#5688C7}{\mathop{\mathrm{shape}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)
=(|\textcolor{#5688C7}{I}_{T,1}|,\ldots,|\textcolor{#5688C7}{I}_{T,k}|).
```

Coordinate-slot position is significant even when domains have equal sizes.
Shape equality alone does not establish a semantic correspondence between
axes.

**Example.** If $T$ has row domain $[5]$ and column domain $[4]$, then
$\textcolor{#5688C7}{\mathop{\mathrm{shape}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)=(5,4)$ and $(3,2)$ is a valid coordinate.
$(5,2)$ is not.

### 4.2 Tensor values

A tensor value for $T$ is a total function

```math
\textcolor{#398B83}{V}_T:\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)\to K.
```

Write $\textcolor{#398B83}{V}_T[p]$ for its value at coordinate tuple $p$.
The set of such functions can also be written
$K^{\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)}$.

The zero tensor is the function $\textcolor{#398B83}{\mathbf{0}}_T$ given by

```math
\textcolor{#398B83}{\mathbf{0}}_T[p]=0_K
```

at every coordinate. Zero defaults require a known coordinate domain; they
do not determine a tensor's shape.

A rank-zero tensor is a function $\{()\}\to K$ and is identified with its
single scalar value.

The notation $H_l$ abbreviates the slice $H[:,l]$ when time is the last
coordinate. For example, if $H:[d]\times[N+1]\to K$, then

```math
H_l[i]=H[i,l].
```

This shorthand refers to logical values, not to a storage layout.

## 5. Environments and stores

### 5.1 Complete tensor environments

A complete tensor environment $\textcolor{#398B83}{\rho}$ assigns each tensor identifier in scope
a value with the signature prescribed by $\textcolor{#5688C7}{\Sigma}$:

```math
\textcolor{#398B83}{\rho}(T):\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)\to K.
```

The notation $\textcolor{#398B83}{\rho}(T)[p]$ means "coordinate $p$ of the value assigned to $T$."

Write $\textcolor{#5688C7}{\mathrm{In}}$ for input identifiers and $\textcolor{#5688C7}{\mathrm{Def}}$ for defined
identifiers. These disjoint sets partition the signature's identifiers;
$\textcolor{#5688C7}{\mathrm{Out}}\subseteq\textcolor{#5688C7}{\mathrm{Def}}$ designates the outputs.
[Section 13.6](tensor_logic_semantics_part_ii.md#136-core-programs) includes these roles in a core program's declaration.

An input environment $\textcolor{#398B83}{\eta}$ assigns values only to identifiers in
$\textcolor{#5688C7}{\mathrm{In}}$. A supplied input value is not automatically a contribution
to a defined tensor.

Write $\textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{In}}}=\textcolor{#398B83}{\eta}$ when $\textcolor{#398B83}{\rho}$ agrees with $\textcolor{#398B83}{\eta}$ on all
designated inputs.

### 5.2 Partial stores and available values

For operational reasoning, a tensor address is a pair

```math
a=(T,p),\qquad p\in\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T).
```

Let $\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$ be the set of all such addresses, tagged
by tensor identifier. Coordinates of different tensors are different
addresses even if their tuples coincide.

A partial store is written

```math
\textcolor{#A87C28}{\sigma}:\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\rightharpoonup K.
```

The hooked arrow denotes a partial function.
$\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$ is the set of addresses at which a value is
available.

An absent value is **not** the same as an available zero. For example,
$(T,p)\notin\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$ does not imply
$\textcolor{#A87C28}{\sigma}(T,p)=0_K$.

Write $\textcolor{#A87C28}{\sigma}[(T,p)\mapsto v]$ for the store updated at that address.
This is a mathematical description of a machine-state update, not an
additive source-language statement.

[Part IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics) distinguishes finalized values from accumulators containing only some
contributions.

### 5.3 Logical addresses, physical slots, and proof-only history

An address $(T,p)$ identifies a **logical tensor coordinate**, not a memory
location. For example, $(H,(i,0))$ and $(H,(i,2))$ remain distinct addresses even if
an implementation stores them in the same buffer at different times.

For physical storage notation, let $\textcolor{#C16C86}{\mathcal{B}}$ be a finite set of buffer
identifiers, with capacity $m_{\textcolor{#C16C86}{\beta}}\in\mathbb{N}$ for each
$\textcolor{#C16C86}{\beta}\in\textcolor{#C16C86}{\mathcal{B}}$. Define

```math
\textcolor{#C16C86}{\mathop{\mathrm{Slot}}\nolimits}_{\textcolor{#C16C86}{\mathcal{B}}}
=\{(\textcolor{#C16C86}{\beta},k)\mid\textcolor{#C16C86}{\beta}\in\textcolor{#C16C86}{\mathcal{B}},\ k\in[m_{\textcolor{#C16C86}{\beta}}]\}.
```

A physical slot $\textcolor{#C16C86}{\xi}=(\textcolor{#C16C86}{\beta},k)$ is tagged by its buffer identifier, just
as a logical address is tagged by its tensor identifier.
An exact-value memory is a partial map
$\textcolor{#C16C86}{M}:\textcolor{#C16C86}{\mathop{\mathrm{Slot}}\nolimits}_{\textcolor{#C16C86}{\mathcal{B}}}\rightharpoonup K$.
An uninitialized slot is not a stored zero. A capacity-zero buffer has
no slots.

The logical store $\textcolor{#A87C28}{\sigma}$ records published values immutably. A physical
memory $\textcolor{#C16C86}{M}$ may change and reuse slots after their old contents are no
longer needed. A correctness proof may retain an old logical value as
**ghost history**: mathematical information carried by the proof but not
necessarily stored by the executing program.
Ghost history is not a runtime source of tensor values. Every actual read
and every returned output must still have a justified concrete representation.
[Part V](tensor_logic_semantics_part_v.md#part-v-compilation-and-refinement) makes this distinction precise.

Here "physical" distinguishes storage from tensor semantics; the contents
are still elements of the exact carrier $K$, not unspecified machine bits.

## 6. Index expressions and coordinate maps

### 6.1 Evaluating index expressions

An index expression $\textcolor{#9D75C4}{e}$ denotes an integer-valued expression under an
appropriate valuation. Write

```math
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}\mathclose{]\!]}_{\textcolor{#5688C7}{\nu}}\in\mathbb{Z}
```

for its evaluated value.

Examples include constants, variables, and affine expressions:

```math
\textcolor{#9D75C4}{e}=b+\sum_{j=1}^{k}c_j i_j,
\qquad b,c_j\in\mathbb{Z}.
```

Under $\textcolor{#5688C7}{\nu}(i)=2$, the expression $2i+1$ evaluates to $5$.
Evaluation into $\mathbb{Z}$ preserves negative values; it does not silently
convert them to valid natural-number coordinates.

For an access $T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k]$, write

```math
\textcolor{#5688C7}{\phi}(\textcolor{#5688C7}{\nu})=
(\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}_1\mathclose{]\!]}_{\textcolor{#5688C7}{\nu}},\ldots,
 \textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}_k\mathclose{]\!]}_{\textcolor{#5688C7}{\nu}}).
```

Calling this a map into $\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)$ asserts that the
tuple is in range throughout the stated domain. Otherwise, it is merely an
integer-tuple-valued expression requiring a boundary policy.

### 6.2 Read maps and write maps

A **read map** selects a source tensor coordinate.
A **write map** associates a contribution occurrence with its destination.
The arithmetic notation is the same, but their roles differ.

**Gather example.** With $i\in[3]$,

```math
Y[i]\textcolor{#9D75C4}{\mathrel{+}=}X[2i]
```

reads source coordinates $0,2,4$. The source must contain those coordinates
unless an extension policy is explicitly provided.

**Scatter example.** With $i\in[3]$ and $Y$ of shape $(6)$,

```math
Y[2i]\textcolor{#9D75C4}{\mathrel{+}=}X[i]
```

addresses output coordinates $0,2,4$. Coordinates $1,3,5$ receive no
contributions in this example.

## 7. Free indices, contraction, and broadcasting

A variable is **free** in an expression if it is not bound by a reduction
or another expression binder. A reduction binds its index locally.

In the normalized notation, free variables are the parameters of a
contribution, and contracted variables are explicitly bound:

```math
\textcolor{#9D75C4}{E}(i,j)=\bigoplus_{k\in \textcolor{#5688C7}{I}_k}W[i,k]\otimes X[k,j].
```

Here $i,j$ are free and $k$ is contracted.

Surface einsum notation may omit this binder:

```text
Y[i,j] = W[i,k] X[k,j]
```

The elaboration of surface notation is defined in [Part II](tensor_logic_semantics_part_ii.md#part-ii-core-language-and-surface-elaboration). We do not use
"all RHS-only variables are summed" as a substitute for specifying binder
scope.

**Term-local contraction example.**

```math
\textcolor{#9D75C4}{E}(i)=\left(\sum_{k\in \textcolor{#5688C7}{I}_k}W[i,k]X[k]\right)+B[i].
```

The bias is added once, not once per value of $k$.

**Broadcasting example.** A contribution parameterized by $i,l$ may have
value $X[i]$, independent of $l$. Varying $l$ generates separate contributions
with the same value at different history positions. Independence from a
variable is not contraction over that variable.

**Affine-write example.** In $Y[i+j]\textcolor{#9D75C4}{\mathrel{+}=}A[i]B[j]$, both $i$ and $j$
parameterize contributions because both occur in the output map. Their
colliding images are handled by contribution collection, not by contracting
either variable in the body.

## 8. Operators, predicates, and definedness

A primitive operator $f$ is specified by its input and output value spaces
and its domain of definition. Write

```math
f:\textcolor{#398B83}{\mathcal{D}}_f\to B,
\qquad
\textcolor{#398B83}{\mathcal{D}}_f\subseteq A,
```

when it accepts values in $\textcolor{#398B83}{\mathcal{D}}_f$ rather than all of $A$.

For exact real arithmetic:

- $\mathop{\mathrm{ReLU}}\nolimits(x)=\max(0,x)$ is defined for every real $x$.
- Real $\log(x)$ requires $x>0$.
- Real $\sqrt{x}$ requires $x\ge0$.
- Division by $z$ requires $z\ne0$.

An operator can consume a whole slice. For example, softmax over nonempty
$[m]$ is a function from $\mathbb{R}^{[m]}$ to
$\mathbb{R}^{[m]}$:

```math
\mathop{\mathrm{softmax}}\nolimits(x)[j]
=
\frac{\exp(x[j])}{\sum_{k\in[m]}\exp(x[k])}.
```

This is not an independent scalar operation at each coordinate. [Part IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics)
represents its slice dependencies through the full argument footprint.

An Iverson value embeds a predicate $\textcolor{#9D75C4}{Q}$ into the scalar algebra:

```math
\mathbf{1}_{\textcolor{#9D75C4}{Q}}
=
\begin{cases}
1_K,&\textcolor{#9D75C4}{Q}\text{ is true},\\
0_K,&\textcolor{#9D75C4}{Q}\text{ is false}.
\end{cases}
```

The values $0_K$ and $1_K$ are those of the sort of the surrounding expression:
in the max-plus sort a true predicate is $0$ and a false one is $-\infty$, in the
min-plus sort a false predicate is $+\infty$, and in the Boolean sort the values
are false and true. A false Iverson factor is therefore the absorbing element of
its sort, so in a max-plus reduction a masked term drops out of the maximum.

Multiplication by $\mathbf{1}_{\textcolor{#9D75C4}{Q}}$ is a value-level operation, not
short-circuit evaluation of the other factor. In the core, $\textcolor{#9D75C4}{Q}$ depends
only on index values, as specified in [Section 13.1](tensor_logic_semantics_part_ii.md#131-index-expressions-and-predicates).
For example, $\mathbf{1}_{i<1}\log(X[i])$ is still undefined at $i=1$
if $X[1]=-1$: the zero factor does not make the logarithm defined.

Likewise, a zero-valued contribution is different from removing an occurrence
using a guard, even when their final collected values coincide.

## 9. Programs and contribution occurrences

### 9.1 Statement identities

A program $\textcolor{#9D75C4}{P}$ has a finite sequence of source statements, each assigned a
distinct occurrence identifier $\textcolor{#9D75C4}{s}$.

The sequence records source occurrences; it does not prescribe an
execution order. Identical text appearing twice creates two statement
occurrences. They must not be deduplicated under numerical additive semantics.

In formulas, $\textcolor{#9D75C4}{s}\in \textcolor{#9D75C4}{P}$ means that $\textcolor{#9D75C4}{s}$ ranges over the program's distinct
statement identifiers, not over distinct statement texts.
For each core statement, use the data:

- $T_{\textcolor{#9D75C4}{s}}$: destination tensor identifier.
- $\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$: context of free contribution variables.
- $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}})$: admissible valuations.
- $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}:\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}\to\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T_{\textcolor{#9D75C4}{s}})$: write map.
- $\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}$: body expression, with free variables in $\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$.

[Part II](tensor_logic_semantics_part_ii.md#part-ii-core-language-and-surface-elaboration) gives the syntax that supplies these data. The write map is derived
from the statement's output index expressions.

### 9.2 Tagged contribution occurrences

A contribution occurrence is a pair $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$ with $\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$.
The collection of all occurrences is the tagged union

```math
\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}
=
\coprod_{\textcolor{#9D75C4}{s}\in \textcolor{#9D75C4}{P}}\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}
=
\{(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\mid \textcolor{#9D75C4}{s}\in \textcolor{#9D75C4}{P},\ \textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}\}.
```

The symbol $\coprod$ denotes a disjoint union: the statement identifier
distinguishes otherwise identical valuations.

Its destination is

```math
\textcolor{#9D75C4}{\mathop{\mathrm{dst}}\nolimits}(\textcolor{#9D75C4}{o})=(T_{\textcolor{#9D75C4}{s}},\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})).
```

**Example: different occurrences, different destinations.** Let $X$ have
shape $(2)$ and $Y$ shape $(3)$:

```text
s_1: Y[i+1] = X[i]    # i in [2]
```

| Contribution occurrence $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$ | Destination $\textcolor{#9D75C4}{\mathop{\mathrm{dst}}\nolimits}(\textcolor{#9D75C4}{o})$ |
| --- | --- |
| $(\textcolor{#9D75C4}{s}_1,\{i\mapsto0\})$ | $(Y,(1))$, the entry `Y[1]` |
| $(\textcolor{#9D75C4}{s}_1,\{i\mapsto1\})$ | $(Y,(2))$, the entry `Y[2]` |

An occurrence identifies a statement and its index assignment.
A destination identifies a tensor and its coordinate tuple.

For a tensor coordinate $(T,p)$, define its candidate contribution occurrences:

```math
\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,p)
=
\{(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}
  \mid T_{\textcolor{#9D75C4}{s}}=T,\ \textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})=p\}.
```

The word "candidate" does not indicate optional contributions. It emphasizes
that this definition locates occurrences without evaluating their bodies.

**Duplicate-statement example.** Independently, let $T$ and $X$ both
have shape $(2)$:

```text
s_1: T[i] = X[i]    # i in [2]
s_2: T[i] = X[i]    # i in [2]
```

At coordinate $(0)$, the two distinct occurrences are

```math
\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,(0))
=\{(\textcolor{#9D75C4}{s}_1,\{i\mapsto0\}),(\textcolor{#9D75C4}{s}_2,\{i\mapsto0\})\}.
```

Both have destination $(T,(0))$. With real-valued addition their
collected value is $2X[0]$, not $X[0]$.

**Example: one statement, a shared destination.** For
`s_1: Y[i+j] = A[i] B[j]`, with $A,B$ of shape $(2)$,
$i,j\in[2]$, and $Y$ of shape $(3)$,
the occurrences $(\textcolor{#9D75C4}{s}_1,\{i\mapsto0,j\mapsto1\})$ and
$(\textcolor{#9D75C4}{s}_1,\{i\mapsto1,j\mapsto0\})$ are different but both have destination
$(Y,(1))$. Their contributions are respectively $A[0]B[1]$ and
$A[1]B[0]$.

## 10. Equality, source notation, and interpretation brackets

We distinguish three kinds of notation:

| Notation | Role |
| --- | --- |
| Mathematical $a=b$ | Equality of mathematical objects |
| Surface `T[...] = E` | A source contribution statement |
| Core and expository $T[\textcolor{#5688C7}{\phi}(\textcolor{#5688C7}{\nu})]\textcolor{#9D75C4}{\mathrel{+}=}\textcolor{#9D75C4}{E}(\textcolor{#5688C7}{\nu})$ | Makes the contribution reading explicit |

The symbol $\textcolor{#9D75C4}{\mathrel{+}=}$ does not mean "read the current mutable value of
$T$ and update it immediately." It describes a contribution to be collected.
For a non-numerical scalar algebra, its combination operation is $\oplus$.

Use the following interpretation notation, made precise in [Part III](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics):

- $\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}\mathclose{]\!]}_{\textcolor{#5688C7}{\nu}}$: the value of an index expression.
- $\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\mathclose{]\!]}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$: the result of interpreting a tensor
  expression under a complete tensor environment and an index valuation;
  it may be undefined.
- $\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\mathclose{]\!]}}(\textcolor{#398B83}{\eta})$: the partial input-output denotation,
  defined when $\textcolor{#398B83}{\eta}$ has a unique complete model, as specified in [Section 20.3](tensor_logic_semantics_part_iii.md#203-functional-admissibility).
- $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$: environments satisfying a program's
  collected equations on the supplied inputs.

Expression interpretation and program-model satisfaction are different
notions: a complete environment can give every expression a value without
satisfying the equations defining its tensors. A cyclic program must not
be assumed to have a unique model merely because this notation is available.

## 11. Running examples fixing the notation

These examples illustrate the intended contribution reading. They do not
replace the formal semantic definitions in Parts [III](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics) and [IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics).

### 11.1 Boundary contributions

Let $C$ and $R$ be inputs of shapes $(4)$ and $(5)$, and let the defined
tensor $T$ have shape $(5,4)$:

```text
T[0,c] = C[c]    # c in [4]
T[r,0] = R[r]    # r in [5]
```

The first write map is $\textcolor{#5688C7}{\phi}_1(c)=(0,c)$ and the second is
$\textcolor{#5688C7}{\phi}_2(r)=(r,0)$. The corner has two contribution occurrences:
$(\textcolor{#9D75C4}{s}_1,c=0)$ and $(\textcolor{#9D75C4}{s}_2,r=0)$.

Under real-valued additive collection, the intended values are

```math
T[r,c]
=
\mathbf{1}_{r=0}C[c]
+
\mathbf{1}_{c=0}R[r].
```

In particular, $T[0,0]=C[0]+R[0]$. There is no requirement that the
two corner contributions agree. Interior coordinates receive an empty sum,
namely zero.

### 11.2 Colliding affine writes

Let $A,B$ be inputs of shape $(2)$ and $Y$ a defined tensor of shape $(3)$:

```text
Y[i+j] = A[i] B[j]    # i,j in [2]
```

The write fiber at $1$ has two occurrences, giving

```math
\begin{aligned}
Y[0]&=A[0]B[0],\\
Y[1]&=A[0]B[1]+A[1]B[0],\\
Y[2]&=A[1]B[1].
\end{aligned}
```

The body has no contracted variables. The addition arises from collecting
different free-variable valuations with the same write image.

### 11.3 Activation before versus after collection

Let $A,B$ be inputs on the same declared vector domain, with $T$ and,
where used, `Pre` defined on that domain. These two programs have different
collected values:

| Activation within contributions | Activation after collection |
| --- | --- |
| `T[i] = relu(A[i])` | `Pre[i] = A[i]` |
| `T[i] = relu(B[i])` | `Pre[i] = B[i]` |
| | `T[i] = relu(Pre[i])` |

They respectively give

```math
T[i]=\mathop{\mathrm{ReLU}}\nolimits(A[i])+\mathop{\mathrm{ReLU}}\nolimits(B[i])
```

and

```math
T[i]=\mathop{\mathrm{ReLU}}\nolimits(A[i]+B[i]).
```

For $A[i]=1$ and $B[i]=-1$, the first is $1$ and the second is $0$.
Expression structure, not statement enumeration order, determines the
activation boundary.

### 11.4 A finite history with persistent input

Let $X,Z$ be inputs of shape $(d)$ and $H$ a defined tensor of shape
$(d,N+1)$. Let
$F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$ be a total function:

```text
H[i,l]   = X[i]             # i in [d], l in [N+1]
H[i,0]   = Z[i]             # i in [d]
H[i,l+1] = F(H[:,l])[i]     # i in [d], l in [N]
```

The occurrences addressed to time zero come from the first two statements.
Occurrences addressed to later times come from the first and third.
The intended collected equations are

```math
H_0=X+Z,
\qquad
H_{l+1}=X+F(H_l)\quad(l\in[N]).
```

$H_l$ means the completed logical slice, not an accumulator containing only
some contributions. The domains $[N+1]$ and $[N]$ are deliberately different.
Reusing the printed variable `l` does not make their binders identical.

## 12. Notation for operational and proof rules

Use:

- $\textcolor{#A87C28}{\mathsf{Conf}}$ for a machine configuration.
- $\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\longrightarrow}\textcolor{#A87C28}{\mathsf{Conf}}'$ for one execution step.
- $\textcolor{#A87C28}{\longrightarrow}^{*}$ for zero or more execution steps.
- $\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\Downarrow}\textcolor{#398B83}{\rho}$ for termination with result environment $\textcolor{#398B83}{\rho}$.
- $\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)$ for the tensor addresses required to evaluate the
  contributions at address $a$, as defined in [Section 23](tensor_logic_semantics_part_iv.md#23-read-footprints-and-executable-dependencies).
- $r:\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\to\mathbb{N}$ for a dependency rank when
  a finite acyclic ordering exists.

The rank condition used in [Part IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics) is

```math
b\in\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)\Longrightarrow r(b)<r(a).
```

This is notation for a sufficient well-founded ordering, not a claim that all
tensor logic programs possess one. Dependencies at tensor-name level and
coordinate level are different: a recurrence can read its own tensor name
while still depending only on earlier coordinates.

For proof judgments, $\textcolor{#5688C7}{\Gamma}\vdash J$ reads "judgment $J$ holds in context
$\textcolor{#5688C7}{\Gamma}$." Here $\textcolor{#5688C7}{\Gamma}$ will be an index context unless explicitly qualified.
[Part II](tensor_logic_semantics_part_ii.md#part-ii-core-language-and-surface-elaboration) introduces structural typing judgments, and [Part III](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics) defines expression
interpretation and program models. [Part IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics) defines the execution judgments
and their rules.

---

[Previous: Introduction](tensor_logic_semantics.md) | [Contents](README.md) | [Next: Part II: Core language and surface elaboration](tensor_logic_semantics_part_ii.md)
