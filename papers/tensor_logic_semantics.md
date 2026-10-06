# Tensor Logic: Operational and Denotational Semantics

## Status and purpose

This specification defines tensor-logic syntax, denotational meaning,
reference execution, and compilation contracts. Its purpose is to provide
a coherent mathematical foundation for a Lean formalization and verified
implementation.

The intended language uses **additive contribution semantics**: separate source
statements can contribute to the same tensor coordinate. A source statement's
`=` is not, by itself, an assertion that the final tensor entry equals that
statement's contribution.

The specification separates three questions: what equations a program
defines, how those equations can be evaluated, and when a compiled execution
faithfully realizes that evaluation. A mutation order or storage convention
does not determine the source language's meaning.

### Roadmap and reading guide

The document has five parts, followed by a notation reference and bibliography:

| Part | Central question | Contents and result |
| --- | --- | --- |
| [I: Background notation](#part-i-background-notation), Sections 1-12 | What mathematical objects and notation are used? | Finite domains, scalar algebras, tensor signatures, environments, stores, indices, operators, and contribution occurrences, illustrated by running examples. |
| [II: Core language and surface elaboration](#part-ii-core-language-and-surface-elaboration), Sections 13-17 | What does a well-formed statement say explicitly? | Scoped core syntax, structural checks, surface-to-core translation, and the canonical pure-einsum meaning and rewrite conditions. |
| [III: Denotational semantics](#part-iii-denotational-semantics), Sections 18-22 | What equations and values does a program define? | Strict expression interpretation, additive collection, complete program models, and a partial input-output function on inputs with a unique model. |
| [IV: Operational semantics](#part-iv-operational-semantics), Sections 23-28 | How can the contributions be computed safely? | Read footprints, dependency ranks, accumulation and publication rules, explicit failures, and correspondence with unique models for the ranked fragment. |
| [V: Compilation and refinement](#part-v-compilation-and-refinement), Sections 29-34 | When does a compiled plan implement that meaning? | Plan contracts, buffer representations, simulation and progress obligations, batching, scan-buffer reuse, and a conditional compiler-correctness theorem. |

Read Parts I and II before the formal semantics: they establish the notation
and binding conventions used throughout. Part III applies even to cyclic
equation systems; the progress guarantees in Parts IV and V concern the
coordinate-ranked fragment, not every structurally valid program.
The distinction between having a unique model and having a supported
execution strategy is therefore essential.

The boundary, colliding-write, activation, and finite-history examples are
revisited across the parts to connect notation, elaboration, equations,
execution, and storage. Section 35 collects the notation; the references
identify the mathematical sources and related design documents.

### Semantic scope

The specification assumes:

- Finite, explicitly determined index domains, including finite scan histories.
- A fixed scalar algebra for a given development.
- Exact mathematical values, distinguished from machine floating-point values.
- Explicitly specified domains for primitive operators.
- Tensor names whose roles as inputs or defined tensors are distinguished.

Several distinctions apply throughout:

- A statement generates contributions; their collected totals define equations.
- A supplied input is not an implicit contribution, and an unwritten defined
  coordinate receives the empty sum on its declared domain.
- An unavailable value is not an available zero; a ready but undefined
  expression is a different case again.
- Primitive applications and constructed arrays use the strict interpretation
  in Part III. A zero multiplier is not a guard.
- Logical coordinates and published versions remain distinct even when
  physical storage is reused.

Cyclic dependencies remain permitted in the denotational language, but the
direct executor does not select solutions for cyclic equations. Padding,
out-of-range access, mixed scalar types, floating-point reduction order, and
machine-number representations are outside the specified fragment. Part V treats
physical storage reuse within an exact-value memory model; it does not
silently replace the scalar carrier by floating-point values.

The lemmas and theorems have mathematical arguments, not kernel-checked Lean
proofs. Compiler correctness is conditional on the stated certificates and
kernel contracts; it is not a claim that an existing compiler satisfies them.
Structural well-formedness alone establishes neither existence of a model
nor an executable dependency order.

The pure-einsum material draws on
[*The Syntax and Semantics of einsum*](https://arxiv.org/html/2509.20020).
Section 17 adapts it to zero-based finite domains, explicit signatures, and
tagged contributions. The paper uses one-based intervals with positive
extents; this specification permits zero extents. Correspondence arguments
must preserve that difference rather than exclude empty domains implicitly.

## Table of contents

- [Status and purpose](#status-and-purpose)
  - [Roadmap and reading guide](#roadmap-and-reading-guide)
  - [Semantic scope](#semantic-scope)
- [Part I: Background notation](#part-i-background-notation)
  - [1. Numbers, finite sets, and functions](#1-numbers-finite-sets-and-functions)
  - [2. Scalar algebras and finite combination](#2-scalar-algebras-and-finite-combination)
  - [3. Axes, index variables, and valuations](#3-axes-index-variables-and-valuations)
  - [4. Tensor signatures, coordinates, and values](#4-tensor-signatures-coordinates-and-values)
  - [5. Environments and stores](#5-environments-and-stores)
  - [6. Index expressions and coordinate maps](#6-index-expressions-and-coordinate-maps)
  - [7. Free indices, contraction, and broadcasting](#7-free-indices-contraction-and-broadcasting)
  - [8. Operators, predicates, and definedness](#8-operators-predicates-and-definedness)
  - [9. Programs and contribution occurrences](#9-programs-and-contribution-occurrences)
  - [10. Equality, source notation, and interpretation brackets](#10-equality-source-notation-and-interpretation-brackets)
  - [11. Running examples fixing the notation](#11-running-examples-fixing-the-notation)
  - [12. Notation for operational and proof rules](#12-notation-for-operational-and-proof-rules)
- [Part II: Core language and surface elaboration](#part-ii-core-language-and-surface-elaboration)
  - [13. Core syntax and binding](#13-core-syntax-and-binding)
  - [14. Structural well-formedness](#14-structural-well-formedness)
  - [15. Surface-to-core elaboration](#15-surface-to-core-elaboration)
  - [16. Worked core elaborations](#16-worked-core-elaborations)
  - [17. Pure einsum semantics and transformation foundations](#17-pure-einsum-semantics-and-transformation-foundations)
    - [17.1 Index strings and global valuations](#171-index-strings-and-global-valuations)
    - [17.2 Canonical fiber semantics](#172-canonical-fiber-semantics)
    - [17.3 Connection to the contribution core](#173-connection-to-the-contribution-core)
    - [17.4 Delta tensors and diagonal identities](#174-delta-tensors-and-diagonal-identities)
    - [17.5 Conditions for semantic transformations](#175-conditions-for-semantic-transformations)
    - [17.6 Neutral operands and domain preservation](#176-neutral-operands-and-domain-preservation)
- [Part III: Denotational semantics](#part-iii-denotational-semantics)
  - [18. Expression interpretation and definedness](#18-expression-interpretation-and-definedness)
  - [19. Contribution collection](#19-contribution-collection)
  - [20. Program models and functional denotation](#20-program-models-and-functional-denotation)
  - [21. Worked denotational examples](#21-worked-denotational-examples)
  - [22. Denotational scope and execution requirements](#22-denotational-scope-and-execution-requirements)
- [Part IV: Operational semantics](#part-iv-operational-semantics)
  - [23. Read footprints and executable dependencies](#23-read-footprints-and-executable-dependencies)
  - [24. Machine configurations and initialization](#24-machine-configurations-and-initialization)
  - [25. Execution rules and terminal outcomes](#25-execution-rules-and-terminal-outcomes)
  - [26. Conservation, termination, and correspondence](#26-conservation-termination-and-correspondence)
  - [27. Worked operational examples](#27-worked-operational-examples)
  - [28. Reference-machine boundaries and proof targets](#28-reference-machine-boundaries-and-proof-targets)
- [Part V: Compilation and refinement](#part-v-compilation-and-refinement)
  - [29. Execution plans and logical action contracts](#29-execution-plans-and-logical-action-contracts)
  - [30. Concrete states and logical representation](#30-concrete-states-and-logical-representation)
  - [31. Simulation and compiler correctness](#31-simulation-and-compiler-correctness)
  - [32. Batched collection and array kernels](#32-batched-collection-and-array-kernels)
  - [33. Scan compilation and buffer reuse](#33-scan-compilation-and-buffer-reuse)
  - [34. Refinement boundaries and formalization targets](#34-refinement-boundaries-and-formalization-targets)
- [35. Compact notation reference](#35-compact-notation-reference)
- [References and related documents](#references-and-related-documents)

## Part I: Background notation

This part fixes the mathematical objects shared by the core language,
both semantics, and the compilation contracts. Its source examples illustrate
contributions; their explicit syntax and interpretation are defined in
Parts II and III.

## 1. Numbers, finite sets, and functions

### 1.1 Number systems and finite intervals

We use:

- $\mathbb{N}=\{0,1,2,\ldots\}$ for natural numbers, including zero.
- $\mathbb{Z}$ for integers.
- $\mathbb{R}$ for exact real numbers.
- $\mathbb{B}=\{\mathrm{false},\mathrm{true}\}$ for Booleans.

For $n\in\mathbb{N}$, define the finite ordinal

$$
[n]=\{k\in\mathbb{N}\mid k<n\}.
$$

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

$$
A_1\times\cdots\times A_k
$$

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

$$
f^{-1}(\{b\})=\{a\in A\mid f(a)=b\}.
$$

This does not assume that $f$ is invertible.

A function is injective if

$$
f(a)=f(a')\Longrightarrow a=a'.
$$

**Example: a write map with collisions.** Let

$$
\phi:[2]\times[2]\to[3],
\qquad
\phi(i,j)=i+j.
$$

Then

$$
\phi^{-1}(\{1\})=\{(0,1),(1,0)\}.
$$

Two different source coordinates address output coordinate $1$. Such a
collision is legitimate for additive contributions.

We use $\forall$ for universal quantification, $\exists$ for existential
quantification, $\land$ for conjunction, $\lor$ for disjunction, and
$\Longrightarrow$ for implication. The notation
$\{a\in A\mid Q(a)\}$ selects the elements satisfying predicate $Q$.

## 2. Scalar algebras and finite combination

### 2.1 The scalar carrier

$K$ denotes a set of scalar values. The numerical interpretation uses
$K=\mathbb{R}$. Exact reals are mathematical objects; this does not assert that
a Lean runtime stores exact real numbers.

Tensor contraction and contribution collection use a commutative semiring

$$
\mathcal{K}=(K,\oplus,\otimes,0_K,1_K).
$$

Specifically:

- $\oplus$ is associative and commutative, with identity $0_K$.
- $\otimes$ is associative and commutative, with identity $1_K$.
- Multiplication distributes over addition.
- $0_K$ is absorbing for multiplication.

The two principal interpretations are:

| Interpretation | $K$ | $\oplus$ | $\otimes$ | $0_K$ | $1_K$ |
| --- | --- | --- | --- | --- | --- |
| Numerical | $\mathbb{R}$ | $+$ | $\cdot$ | $0$ | $1$ |
| Boolean | $\mathbb{B}$ | $\lor$ | $\land$ | false | true |

The word "additive" means combination by $\oplus$. For Boolean tensors this is
OR, not arithmetic addition of truth values.

Subtraction, division, ordering, and nonlinear functions are **not** supplied
by the semiring structure alone. They need an appropriate carrier and their own
specified operations.

### 2.2 Finite sums and products

For a finite indexing set $A$ and a function $v:A\to K$, write

$$
\bigoplus_{a\in A}v(a)
\qquad\text{and}\qquad
\bigotimes_{a\in A}v(a)
$$

for finite combination and multiplication. Their empty cases are

$$
\bigoplus_{a\in\varnothing}v(a)=0_K,
\qquad
\bigotimes_{a\in\varnothing}v(a)=1_K.
$$

In the numerical interpretation, we also use $\sum$ and $\prod$.

These expressions are indexed by **occurrences**, not by the set of distinct
values. Equal-valued contributions are not deduplicated:

$$
\sum_{a\in[2]}3=6.
$$

In the Boolean interpretation, combining two true contributions gives true
because OR is idempotent. Real addition is not idempotent.

Associativity and commutativity make finite combination independent of
enumeration order in this mathematical setting. Floating-point addition does
not satisfy those laws exactly; an implementation correspondence must address
that distinction explicitly.

## 3. Axes, index variables, and valuations

### 3.1 Axes and identities

An axis $a$ has an identity and a finite extent $n_a\in\mathbb{N}$. Its
coordinate range is

$$
I_a=[n_a].
$$

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
$I_i$. An **index context** records a finite collection of distinct variable
identities and their domains:

$$
\Gamma=(i_1:I_{i_1},\ldots,i_k:I_{i_k}).
$$

Write $\operatorname{vars}(\Gamma)=\{i_1,\ldots,i_k\}$ for the set of
variable identities declared in the context.
The affine core uses scalar integer indices. Tuple coordinates are formed
from several such indices; they are not single integer index variables.

Using the same variable twice imposes the same coordinate value twice. Using
different variables allows different values, even when their ranges coincide.

**Example.** In $M[i,i]$, the two slots use one variable and select a
diagonal. In $M[i,j]$, the two slots vary independently.

Variables are scoped by their binders. A consistently renamed bound variable
does not change meaning. Reusing the spelling `i` in separate statements does
not itself relate their valuations.

### 3.3 Valuations

A valuation $\nu$ for $\Gamma$ assigns each variable a coordinate in its
declared domain. The set of all such valuations is

$$
\operatorname{Val}(\Gamma)
=
\prod_{i\in\operatorname{vars}(\Gamma)}I_i.
$$

Here the product is a dependent family of assignments keyed by variable
identity, not an assertion that variable order matters semantically.

We write $\nu(i)$ for the assigned coordinate. We write
$\nu[i\mapsto k]$ for extension with a fresh variable or replacement of an
existing variable's binding, with $k\in I_i$.

**Example.** For $\Gamma=(i:[2],j:[3])$, the valuation
$\nu=\{i\mapsto1,j\mapsto2\}$ evaluates $i+j$ to $3$.

An admissible iteration domain can be a subset

$$
D\subseteq\operatorname{Val}(\Gamma),
$$

such as the valuations satisfying an explicit guard. A guard restricts
which contributions exist; an Iverson factor changes the value of a
contribution. Section 13.1 makes that distinction explicit in the syntax.

## 4. Tensor signatures, coordinates, and values

### 4.1 Signatures and coordinate domains

$T,U,W,\ldots$ denote tensor identifiers. A finite tensor signature $\Sigma$ records
the ordered coordinate domains and scalar carrier of each tensor.

For a rank-$k$ tensor $T$, write

$$
\Sigma(T)=(I_{T,1},\ldots,I_{T,k};K),
\qquad
\operatorname{Coord}_{\Sigma}(T)
=I_{T,1}\times\cdots\times I_{T,k}.
$$

Its numerical shape is

$$
\operatorname{shape}_{\Sigma}(T)
=(|I_{T,1}|,\ldots,|I_{T,k}|).
$$

Coordinate-slot position is significant even when domains have equal sizes.
Shape equality alone does not establish a semantic correspondence between
axes.

**Example.** If $T$ has row domain $[5]$ and column domain $[4]$, then
$\operatorname{shape}_{\Sigma}(T)=(5,4)$ and $(3,2)$ is a valid coordinate.
$(5,2)$ is not.

### 4.2 Tensor values

A tensor value for $T$ is a total function

$$
V_T:\operatorname{Coord}_{\Sigma}(T)\to K.
$$

Write $V_T[p]$ for its value at coordinate tuple $p$.
The set of such functions can also be written
$K^{\operatorname{Coord}_{\Sigma}(T)}$.

The zero tensor is the function $\mathbf{0}_T$ given by

$$
\mathbf{0}_T[p]=0_K
$$

at every coordinate. Zero defaults require a known coordinate domain; they
do not determine a tensor's shape.

A rank-zero tensor is a function $\{()\}\to K$ and is identified with its
single scalar value.

The notation $H_l$ abbreviates the slice $H[:,l]$ when time is the last
coordinate. For example, if $H:[d]\times[N+1]\to K$, then

$$
H_l[i]=H[i,l].
$$

This shorthand refers to logical values, not to a storage layout.

## 5. Environments and stores

### 5.1 Complete tensor environments

A complete tensor environment $\rho$ assigns each tensor identifier in scope
a value with the signature prescribed by $\Sigma$:

$$
\rho(T):\operatorname{Coord}_{\Sigma}(T)\to K.
$$

The notation $\rho(T)[p]$ means "coordinate $p$ of the value assigned to $T$."

Write $\mathrm{In}$ for input identifiers and $\mathrm{Def}$ for defined
identifiers. These disjoint sets partition the signature's identifiers;
$\mathrm{Out}\subseteq\mathrm{Def}$ designates the outputs.
Section 13.6 includes these roles in a core program's declaration.

An input environment $\eta$ assigns values only to identifiers in
$\mathrm{In}$. A supplied input value is not automatically a contribution
to a defined tensor.

Write $\rho|_{\mathrm{In}}=\eta$ when $\rho$ agrees with $\eta$ on all
designated inputs.

### 5.2 Partial stores and available values

For operational reasoning, a tensor address is a pair

$$
a=(T,p),\qquad p\in\operatorname{Coord}_{\Sigma}(T).
$$

Let $\operatorname{Addr}_{\Sigma}$ be the set of all such addresses, tagged
by tensor identifier. Coordinates of different tensors are different
addresses even if their tuples coincide.

A partial store is written

$$
\sigma:\operatorname{Addr}_{\Sigma}\rightharpoonup K.
$$

The hooked arrow denotes a partial function.
$\operatorname{dom}(\sigma)$ is the set of addresses at which a value is
available.

An absent value is **not** the same as an available zero. For example,
$(T,p)\notin\operatorname{dom}(\sigma)$ does not imply
$\sigma(T,p)=0_K$.

Write $\sigma[(T,p)\mapsto v]$ for the store updated at that address.
This is a mathematical description of a machine-state update, not an
additive source-language statement.

Part IV distinguishes finalized values from accumulators containing only some
contributions.

### 5.3 Logical addresses, physical slots, and proof-only history

An address $(T,p)$ identifies a **logical tensor coordinate**, not a memory
location. For example, $(H,(i,0))$ and $(H,(i,2))$ remain distinct addresses even if
an implementation stores them in the same buffer at different times.

For physical storage notation, let $\mathcal{B}$ be a finite set of buffer
identifiers, with capacity $m_\beta\in\mathbb{N}$ for each
$\beta\in\mathcal{B}$. Define

$$
\operatorname{Slot}_{\mathcal{B}}
=\{(\beta,k)\mid\beta\in\mathcal{B},\ k\in[m_\beta]\}.
$$

A physical slot $\xi=(\beta,k)$ is tagged by its buffer identifier, just
as a logical address is tagged by its tensor identifier.
An exact-value memory is a partial map
$M:\operatorname{Slot}_{\mathcal{B}}\rightharpoonup K$.
An uninitialized slot is not a stored zero. A capacity-zero buffer has
no slots.

The logical store $\sigma$ records published values immutably. A physical
memory $M$ may change and reuse slots after their old contents are no
longer needed. A correctness proof may retain an old logical value as
**ghost history**: mathematical information carried by the proof but not
necessarily stored by the executing program.
Ghost history is not a runtime source of tensor values. Every actual read
and every returned output must still have a justified concrete representation.
Part V makes this distinction precise.

Here "physical" distinguishes storage from tensor semantics; the contents
are still elements of the exact carrier $K$, not unspecified machine bits.

## 6. Index expressions and coordinate maps

### 6.1 Evaluating index expressions

An index expression $e$ denotes an integer-valued expression under an
appropriate valuation. Write

$$
\llbracket e\rrbracket_{\nu}\in\mathbb{Z}
$$

for its evaluated value.

Examples include constants, variables, and affine expressions:

$$
e=b+\sum_{j=1}^{k}c_j i_j,
\qquad b,c_j\in\mathbb{Z}.
$$

Under $\nu(i)=2$, the expression $2i+1$ evaluates to $5$.
Evaluation into $\mathbb{Z}$ preserves negative values; it does not silently
convert them to valid natural-number coordinates.

For an access $T[e_1,\ldots,e_k]$, write

$$
\phi(\nu)=
(\llbracket e_1\rrbracket_\nu,\ldots,
 \llbracket e_k\rrbracket_\nu).
$$

Calling this a map into $\operatorname{Coord}_{\Sigma}(T)$ asserts that the
tuple is in range throughout the stated domain. Otherwise, it is merely an
integer-tuple-valued expression requiring a boundary policy.

### 6.2 Read maps and write maps

A **read map** selects a source tensor coordinate.
A **write map** associates a contribution occurrence with its destination.
The arithmetic notation is the same, but their roles differ.

**Gather example.** With $i\in[3]$,

$$
Y[i]\mathrel{+}=X[2i]
$$

reads source coordinates $0,2,4$. The source must contain those coordinates
unless an extension policy is explicitly provided.

**Scatter example.** With $i\in[3]$ and $Y$ of shape $(6)$,

$$
Y[2i]\mathrel{+}=X[i]
$$

addresses output coordinates $0,2,4$. Coordinates $1,3,5$ receive no
contributions in this example.

## 7. Free indices, contraction, and broadcasting

A variable is **free** in an expression if it is not bound by a reduction
or another expression binder. A reduction binds its index locally.

In the normalized notation, free variables are the parameters of a
contribution, and contracted variables are explicitly bound:

$$
E(i,j)=\bigoplus_{k\in I_k}W[i,k]\otimes X[k,j].
$$

Here $i,j$ are free and $k$ is contracted.

Surface einsum notation may omit this binder:

```text
Y[i,j] = W[i,k] X[k,j]
```

The elaboration of surface notation is defined in Part II. We do not use
"all RHS-only variables are summed" as a substitute for specifying binder
scope.

**Term-local contraction example.**

$$
E(i)=\left(\sum_{k\in I_k}W[i,k]X[k]\right)+B[i].
$$

The bias is added once, not once per value of $k$.

**Broadcasting example.** A contribution parameterized by $i,l$ may have
value $X[i]$, independent of $l$. Varying $l$ generates separate contributions
with the same value at different history positions. Independence from a
variable is not contraction over that variable.

**Affine-write example.** In $Y[i+j]\mathrel{+}=A[i]B[j]$, both $i$ and $j$
parameterize contributions because both occur in the output map. Their
colliding images are handled by contribution collection, not by contracting
either variable in the body.

## 8. Operators, predicates, and definedness

A primitive operator $f$ is specified by its input and output value spaces
and its domain of definition. Write

$$
f:\mathcal{D}_f\to B,
\qquad
\mathcal{D}_f\subseteq A,
$$

when it accepts values in $\mathcal{D}_f$ rather than all of $A$.

For exact real arithmetic:

- $\operatorname{ReLU}(x)=\max(0,x)$ is defined for every real $x$.
- Real $\log(x)$ requires $x>0$.
- Real $\sqrt{x}$ requires $x\ge0$.
- Division by $z$ requires $z\ne0$.

An operator can consume a whole slice. For example, softmax over nonempty
$[m]$ is a function from $\mathbb{R}^{[m]}$ to
$\mathbb{R}^{[m]}$:

$$
\operatorname{softmax}(x)[j]
=
\frac{\exp(x[j])}{\sum_{k\in[m]}\exp(x[k])}.
$$

This is not an independent scalar operation at each coordinate. Part IV
represents its slice dependencies through the full argument footprint.

An Iverson value embeds a predicate $Q$ into the scalar algebra:

$$
\mathbf{1}_{Q}
=
\begin{cases}
1_K,&Q\text{ is true},\\
0_K,&Q\text{ is false}.
\end{cases}
$$

Multiplication by $\mathbf{1}_{Q}$ is a value-level operation, not
short-circuit evaluation of the other factor. In the core, $Q$ depends
only on index values, as specified in Section 13.1.
For example, $\mathbf{1}_{i<1}\log(X[i])$ is still undefined at $i=1$
if $X[1]=-1$: the zero factor does not make the logarithm defined.

Likewise, a zero-valued contribution is different from removing an occurrence
using a guard, even when their final collected values coincide.

## 9. Programs and contribution occurrences

### 9.1 Statement identities

A program $P$ has a finite sequence of source statements, each assigned a
distinct occurrence identifier $s$.

The sequence records source occurrences; it does not prescribe an
execution order. Identical text appearing twice creates two statement
occurrences. They must not be deduplicated under numerical additive semantics.

In formulas, $s\in P$ means that $s$ ranges over the program's distinct
statement identifiers, not over distinct statement texts.
For each core statement, use the data:

- $T_s$: destination tensor identifier.
- $\Gamma_s$: context of free contribution variables.
- $D_s\subseteq\operatorname{Val}(\Gamma_s)$: admissible valuations.
- $\phi_s:D_s\to\operatorname{Coord}_{\Sigma}(T_s)$: write map.
- $E_s$: body expression, with free variables in $\Gamma_s$.

Part II gives the syntax that supplies these data. The write map is derived
from the statement's output index expressions.

### 9.2 Tagged contribution occurrences

A contribution occurrence is a pair $o=(s,\nu)$ with $\nu\in D_s$.
The collection of all occurrences is the tagged union

$$
\mathcal{O}_P
=
\coprod_{s\in P}D_s
=
\{(s,\nu)\mid s\in P,\ \nu\in D_s\}.
$$

The symbol $\coprod$ denotes a disjoint union: the statement identifier
distinguishes otherwise identical valuations.

Its destination is

$$
\operatorname{dst}(o)=(T_s,\phi_s(\nu)).
$$

**Example: different occurrences, different destinations.** Let $X$ have
shape $(2)$ and $Y$ shape $(3)$:

```text
s_1: Y[i+1] = X[i]    # i in [2]
```

| Contribution occurrence $o=(s,\nu)$ | Destination $\operatorname{dst}(o)$ |
| --- | --- |
| $(s_1,\{i\mapsto0\})$ | $(Y,(1))$, the entry `Y[1]` |
| $(s_1,\{i\mapsto1\})$ | $(Y,(2))$, the entry `Y[2]` |

An occurrence identifies a statement and its index assignment.
A destination identifies a tensor and its coordinate tuple.

For a tensor coordinate $(T,p)$, define its candidate contribution occurrences:

$$
\mathcal{C}_P(T,p)
=
\{(s,\nu)\in\mathcal{O}_P
  \mid T_s=T,\ \phi_s(\nu)=p\}.
$$

The word "candidate" does not indicate optional contributions. It emphasizes
that this definition locates occurrences without evaluating their bodies.

**Duplicate-statement example.** Independently, let $T$ and $X$ both
have shape $(2)$:

```text
s_1: T[i] = X[i]    # i in [2]
s_2: T[i] = X[i]    # i in [2]
```

At coordinate $(0)$, the two distinct occurrences are

$$
\mathcal{C}_P(T,(0))
=\{(s_1,\{i\mapsto0\}),(s_2,\{i\mapsto0\})\}.
$$

Both have destination $(T,(0))$. With real-valued addition their
collected value is $2X[0]$, not $X[0]$.

**Example: one statement, a shared destination.** For
`s_1: Y[i+j] = A[i] B[j]`, with $A,B$ of shape $(2)$,
$i,j\in[2]$, and $Y$ of shape $(3)$,
the occurrences $(s_1,\{i\mapsto0,j\mapsto1\})$ and
$(s_1,\{i\mapsto1,j\mapsto0\})$ are different but both have destination
$(Y,(1))$. Their contributions are respectively $A[0]B[1]$ and
$A[1]B[0]$.

## 10. Equality, source notation, and interpretation brackets

We distinguish three kinds of notation:

| Notation | Role |
| --- | --- |
| Mathematical $a=b$ | Equality of mathematical objects |
| Surface `T[...] = E` | A source contribution statement |
| Core and expository $T[\phi(\nu)]\mathrel{+}=E(\nu)$ | Makes the contribution reading explicit |

The symbol $\mathrel{+}=$ does not mean "read the current mutable value of
$T$ and update it immediately." It describes a contribution to be collected.
For a non-numerical scalar algebra, its combination operation is $\oplus$.

Use the following interpretation notation, made precise in Part III:

- $\llbracket e\rrbracket_\nu$: the value of an index expression.
- $\llbracket E\rrbracket_{\rho,\nu}$: the result of interpreting a tensor
  expression under a complete tensor environment and an index valuation;
  it may be undefined.
- $\llbracket P\rrbracket(\eta)$: the partial input-output denotation,
  defined when $\eta$ has a unique complete model, as specified in Section 20.3.
- $\operatorname{Models}(P,\eta)$: environments satisfying a program's
  collected equations on the supplied inputs.

Expression interpretation and program-model satisfaction are different
notions: a complete environment can give every expression a value without
satisfying the equations defining its tensors. A cyclic program must not
be assumed to have a unique model merely because this notation is available.

## 11. Running examples fixing the notation

These examples illustrate the intended contribution reading. They do not
replace the formal semantic definitions in Parts III and IV.

### 11.1 Boundary contributions

Let $C$ and $R$ be inputs of shapes $(4)$ and $(5)$, and let the defined
tensor $T$ have shape $(5,4)$:

```text
T[0,c] = C[c]    # c in [4]
T[r,0] = R[r]    # r in [5]
```

The first write map is $\phi_1(c)=(0,c)$ and the second is
$\phi_2(r)=(r,0)$. The corner has two contribution occurrences:
$(s_1,c=0)$ and $(s_2,r=0)$.

Under real-valued additive collection, the intended values are

$$
T[r,c]
=
\mathbf{1}_{r=0}C[c]
+
\mathbf{1}_{c=0}R[r].
$$

In particular, $T[0,0]=C[0]+R[0]$. There is no requirement that the
two corner contributions agree. Interior coordinates receive an empty sum,
namely zero.

### 11.2 Colliding affine writes

Let $A,B$ be inputs of shape $(2)$ and $Y$ a defined tensor of shape $(3)$:

```text
Y[i+j] = A[i] B[j]    # i,j in [2]
```

The write fiber at $1$ has two occurrences, giving

$$
\begin{aligned}
Y[0]&=A[0]B[0],\\
Y[1]&=A[0]B[1]+A[1]B[0],\\
Y[2]&=A[1]B[1].
\end{aligned}
$$

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

$$
T[i]=\operatorname{ReLU}(A[i])+\operatorname{ReLU}(B[i])
$$

and

$$
T[i]=\operatorname{ReLU}(A[i]+B[i]).
$$

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

$$
H_0=X+Z,
\qquad
H_{l+1}=X+F(H_l)\quad(l\in[N]).
$$

$H_l$ means the completed logical slice, not an accumulator containing only
some contributions. The domains $[N+1]$ and $[N]$ are deliberately different.
Reusing the printed variable `l` does not make their binders identical.

## 12. Notation for operational and proof rules

Use:

- $\mathsf{Conf}$ for a machine configuration.
- $\mathsf{Conf}\longrightarrow\mathsf{Conf}'$ for one execution step.
- $\longrightarrow^{*}$ for zero or more execution steps.
- $\mathsf{Conf}\Downarrow\rho$ for termination with result environment $\rho$.
- $\operatorname{Dep}(a)$ for the tensor addresses required to evaluate the
  contributions at address $a$, as defined in Section 23.
- $r:\operatorname{Addr}_{\Sigma}\to\mathbb{N}$ for a dependency rank when
  a finite acyclic ordering exists.

The rank condition used in Part IV is

$$
b\in\operatorname{Dep}(a)\Longrightarrow r(b)<r(a).
$$

This is notation for a sufficient well-founded ordering, not a claim that all
tensor logic programs possess one. Dependencies at tensor-name level and
coordinate level are different: a recurrence can read its own tensor name
while still depending only on earlier coordinates.

For proof judgments, $\Gamma\vdash J$ reads "judgment $J$ holds in context
$\Gamma$." Here $\Gamma$ will be an index context unless explicitly qualified.
Part II introduces structural typing judgments, and Part III defines expression
interpretation and program models. Part IV defines the execution judgments
and their rules.

## Part II: Core language and surface elaboration

The core removes implicit contraction and implicit slice construction.
It retains additive statements: their contributions are not converted into
ordered mutation commands.

The core specifies the **in-bounds fragment**. A read or write must
address a valid coordinate throughout its applicable index domain. Boundary
extensions such as zero padding are not silently inserted; they require
separate syntax or an explicit extension of this fragment.

## 13. Core syntax and binding

### 13.1 Index expressions and predicates

The core index expressions are affine:

$$
e ::= b \mid i \mid e+e \mid c\,e,
\qquad b,c\in\mathbb{Z}.
$$

Here $i$ is an index variable from a context $\Gamma$, not a tensor value.
Subtraction is expressed using coefficient $-1$.
Scalar arithmetic in an expression is distinct from integer index arithmetic.

The index predicates used for guards and Iverson values are:

$$
Q ::= \mathrm{true}\mid\mathrm{false}
\mid e=e\mid e<e
\mid \neg Q\mid Q\land Q\mid Q\lor Q.
$$

The usual comparisons such as $e\le e'$ are abbreviations. Predicates depend
only on index valuations, not on tensor values. This makes a statement's
contribution domain determinable without executing its body.

Write $\llbracket Q\rrbracket_\nu\in\mathbb{B}$ for predicate evaluation
using integer comparisons and Boolean connectives.
This Boolean result is distinct from its scalar embedding
$\mathbf{1}_{Q}\in K$.

**Example.** The guard $i+1<4$ selects the valuations $i=0,1,2$ from
$i\in[4]$. It creates no occurrence for $i=3$.
Multiplication by $\mathbf{1}_{i+1<4}$ instead retains that occurrence
and changes its body value; it does not automatically suppress invalid reads.

### 13.2 Value types and primitive signatures

An expression has a value type $\tau$, which is either:

- The scalar type $K$.
- An array type $K^{I_1\times\cdots\times I_m}$, with $m\ge1$.

Each array slot has a specified finite coordinate domain, just as for a
tensor signature in Section 4. Rank-zero values use the scalar type $K$.
Arrays here are expression values, not necessarily named tensors.

A fixed primitive registry $\mathcal{F}$ supplies, for every operator $f$,
an arity $q$, input types $\tau_1,\ldots,\tau_q$, an output type $\tau$,
and a domain

$$
\mathcal{D}_f\subseteq\tau_1\times\cdots\times\tau_q.
$$

The types in this formula denote their value spaces. This specializes the
operator-domain notation from Section 8.
Primitive interpretations are deterministic mathematical functions of
their arguments on $\mathcal{D}_f$. They have no hidden store reads or side
effects. Computable implementations and domain tests are separate requirements.

For example, real ReLU has one scalar argument and result. Softmax for
$m>0$ has one argument and result of type $\mathbb{R}^{[m]}$.
A user-supplied $F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$ can be a registered
array operator, with its domain specified in the same way.

There is no implicit application of an array operator coordinate by
coordinate, and no implicit distribution of any operator over $\oplus$.

### 13.3 Expression constructors

The core expression constructors are:

| Constructor | Meaning and binding |
| --- | --- |
| $c_K$ | A scalar literal belonging to $K$ |
| $T[e_1,\ldots,e_k]$ | A scalar read from a named tensor |
| $\mathbf{1}_{Q}$ | Scalar embedding of an index predicate |
| $E_1\oplus E_2$ | Combination of two scalar expressions |
| $E_1\otimes E_2$ | Multiplication of two scalar expressions |
| $\bigoplus_{j\in I_j}E$ | Scalar reduction; binds $j$ in $E$ |
| $\operatorname{tab}_{j_1\in I_1,\ldots,j_m\in I_m}(E)$ | Array construction; binds all $j_1,\ldots,j_m$ in a scalar body |
| $\operatorname{at}(E,(e_1,\ldots,e_m))$ | Selects a scalar coordinate from an array expression |
| $f(E_1,\ldots,E_q)$ | Applies a primitive with its declared input and output types |

The number of indices in a named read must match its tensor rank. A scalar
tensor is read as $T[]$.
Tabulation uses $m\ge1$ distinct bound variables and constructs the full
Cartesian product of their domains, including an empty array if a domain
is empty.

The combining operations displayed here are scalar operations.
Pointwise array addition, if desired, is expressed by tabulating scalar
addition or by a registered primitive with an explicit array signature.

**Example: construct a vector, then select an entry.** Work over
$K=\mathbb{R}$ and let $X$ have shape $(3)$, with entries
$X[0]=2$, $X[1]=5$, and $X[2]=7$.
The array expression

$$
V=\operatorname{tab}_{j\in[3]}(X[j]+1)
$$

constructs all three entries: $V[0]=3$, $V[1]=6$, and $V[2]=8$.
The bound variable $j$ visits each coordinate; it is not summed out.
Selection then gives

$$
\operatorname{at}(V,(1))=6.
$$

Here $(1)$ is the one-coordinate tuple for a vector, and $V$ is an expository
name for the resulting value, not an additional core binding construct.
Thus `tab` constructs an array from a scalar body, whereas `at` reads
one scalar from that array.

**Example: a history slice.**

$$
\operatorname{tab}_{j\in[d]}(H[j,l])
$$

is an array expression of type $K^{[d]}$, with $l$ free and $j$ bound.
It makes the shorthand $H[:,l]$ from Part I explicit.

**Example: a scalar selected from an array computation.**

$$
\operatorname{at}\left(
F\left(\operatorname{tab}_{j\in[d]}(H[j,l])\right),(i)
\right)
$$

is the core form of $F(H[:,l])[i]$.

### 13.4 Scope, freshness, and substitution

All bound variables have identities distinct from the variables already
in scope. Printed names can be changed consistently to satisfy this
freshness convention.

For an expression $E$, $\operatorname{FV}(E)$ denotes its free variables.
For example,

$$
\operatorname{FV}\left(\bigoplus_{k\in I_k}W[i,k]\otimes X[k,j]\right)
=\{i,j\}.
$$

The corresponding notation applies to index expressions and predicates.
For multiple expressions, take the union of their free-variable sets.

$E[i:=e]$ denotes capture-avoiding substitution of index expression $e$
for the free occurrences of $i$. Bound variables are renamed when needed
to prevent capture. This syntactic substitution is distinct from the
valuation update $\nu[i\mapsto k]$.

**Example.** In

$$
E(i)=\bigoplus_{k\in[k_0]}W[i,k]\otimes X[k],
$$

the substitution $E[i:=k]$ first renames the bound reduction variable,
giving, for a fresh $h$,

$$
\bigoplus_{h\in[k_0]}W[k,h]\otimes X[h].
$$

The replacement's $k$ stays free.

### 13.5 Core contribution statements

A core statement with occurrence identifier $s$ has the form

$$
\text{for }\Gamma_s\text{ where }Q_s:
\qquad
T_s[e_{s,1},\ldots,e_{s,k_s}]\mathrel{+}=E_s.
$$

$\Gamma_s$ binds the statement's contribution variables in its guard,
output indices, and body. The body must have scalar type $K$.
The guard is optional, with omitted guard meaning $\mathrm{true}$.

The guard and output indices determine the data introduced in Section 9:

$$
D_s=\{\nu\in\operatorname{Val}(\Gamma_s)
       \mid\llbracket Q_s\rrbracket_\nu=\mathrm{true}\},
$$

$$
\phi_s(\nu)=
(\llbracket e_{s,1}\rrbracket_\nu,\ldots,
 \llbracket e_{s,k_s}\rrbracket_\nu).
$$

The binders are part of the statement's identity as a contribution
generator. They are not discarded when an output index simplifies.
For instance, with $i\in[3]$, the statement

$$
T[0i]\mathrel{+}=1_K
$$

has three occurrences addressed to coordinate $0$, not one.

### 13.6 Core programs

A core program consists of:

1. A finite signature $\Sigma$, over the fixed carrier $K$.
2. A partition of its tensor identifiers into designated inputs
   $\mathrm{In}$ and defined tensors $\mathrm{Def}$.
3. Designated output identifiers $\mathrm{Out}\subseteq\mathrm{Def}$.
4. A finite sequence of core statements with distinct occurrence identifiers.

These named identifier sets are finite; $\mathrm{In}$ and $\mathrm{Def}$
are disjoint and their union is exactly the identifier domain of $\Sigma$.
Every statement targets an identifier in $\mathrm{Def}$.
Reads may refer to either set.

A defined tensor need not have any statements targeting it. Its values
are governed by the empty-collection rule in Section 19.
Conversely, declaring a tensor to be an input does not
provide its values: an input environment $\eta$ must supply them.

Designated outputs specify whole tensor values with their declared coordinate
domains. If $H$ is a history tensor and $H\in\mathrm{Out}$, the output includes
every time slice, not just its last slice. Returning only the final state
requires a separately declared output, for example a tensor `Last` defined
by `Last[i] = H[i,N]`. This distinction also determines which values a
compiled execution must retain for output decoding.

## 14. Structural well-formedness

### 14.1 Judgments and admissible valuations

Use the judgments

$$
\Gamma\vdash e:\mathbb{Z},
\qquad
\Gamma\vdash Q:\mathrm{pred},
\qquad
\Sigma;\Gamma;D\vdash E:\tau,
$$

where $D\subseteq\operatorname{Val}(\Gamma)$.
The marker $\mathrm{pred}$ classifies index predicates; it is not a scalar
type. The primitive registry and scalar algebra are fixed parameters.

The expression judgment establishes binding, value types, and
in-bounds index use for valuations in $D$.
It does **not** assert that value-dependent primitive domains are met.
In particular, $\log(T[i])$ can have scalar type while still requiring
positive tensor values for its interpretation to be defined.

For a fresh $j:I_j$, define the lifted valuation domain

$$
D^{+j}
=
\{\nu[j\mapsto k]\mid\nu\in D,\ k\in I_j\}
\subseteq\operatorname{Val}(\Gamma,j:I_j).
$$

For several fresh variables, lift successively. This accounts for every
coordinate evaluated inside a reduction or tabulation.

**Example: a guarded row sum.** Work over $K=\mathbb{R}$, with
$\Sigma(X)=([4],[2];\mathbb{R})$ and $\Gamma=(i:[4])$.
Choose the index expression $e=i+1$ and predicate $Q=(i+1<4)$.
The first two judgments are

$$
\Gamma\vdash i+1:\mathbb{Z},
\qquad
\Gamma\vdash i+1<4:\mathrm{pred}.
$$

The admissible valuations are

$$
D=\{\{i\mapsto0\},\{i\mapsto1\},\{i\mapsto2\}\}.
$$

Introduce a fresh reduction variable $j\in[2]$. Lifting gives

$$
D^{+j}
=
\{\{i\mapsto a,j\mapsto b\}\mid a\in[3],\ b\in[2]\}.
$$

This domain contains six valuations. Every one makes the read
$X[i+1,j]$ valid: its row is $1$, $2$, or $3$, and its column is
$0$ or $1$. For instance, $\{i\mapsto2,j\mapsto1\}$ reads $X[3,1]$.
Consequently, the body and reduction judgments are

$$
\Sigma;(\Gamma,j:[2]);D^{+j}\vdash X[i+1,j]:\mathbb{R},
$$

$$
\Sigma;\Gamma;D\vdash
\bigoplus_{j\in[2]}X[i+1,j]:\mathbb{R}.
$$

The result is a scalar row sum for each admissible $i$, not an array.
If $D$ instead included $\{i\mapsto3\}$, the body would try to read
row $4$, so the in-bounds expression judgment would fail even though
$i+1$ remains a well-scoped integer expression.

### 14.2 Index and expression rules

Index literals are integers, variables must belong to $\Gamma$, and
affine constructors preserve the integer index type.
Predicates are built from well-scoped index expressions using the
constructors in Section 13.1.

The expression rules are:

| Constructor | Required premises and result |
| --- | --- |
| $c_K$ | $c_K\in K$; result $K$ |
| $T[e_1,\ldots,e_k]$ | $T$ is declared, rank is $k$, indices are well-scoped, and their tuple belongs to $\operatorname{Coord}_{\Sigma}(T)$ for every $\nu\in D$; result $K$ |
| $\mathbf{1}_{Q}$ | $\Gamma\vdash Q:\mathrm{pred}$; result $K$ |
| $E_1\oplus E_2$, $E_1\otimes E_2$ | Both operands have type $K$ under the same $\Sigma,\Gamma,D$; result $K$ |
| $\bigoplus_{j\in I_j}E$ | The body has type $K$ under $\Sigma;\Gamma,j:I_j;D^{+j}$; result $K$ |
| $\operatorname{tab}_{j_1\in I_1,\ldots,j_m\in I_m}(E)$ | The body has type $K$ under the extended context and lifted domain; result $K^{I_1\times\cdots\times I_m}$ |
| $\operatorname{at}(E,(e_1,\ldots,e_m))$ | $E$ has the matching array type, the indices are well-scoped, and the selected tuple is in its coordinate domain for every $\nu\in D$; result $K$ |
| $f(E_1,\ldots,E_q)$ | Each operand has the corresponding type from $\mathcal{F}$ under the same $\Sigma,\Gamma,D$; result is the declared output type |

Tabulation and reduction lift $D$ over the whole declared binder domain,
not just over coordinates occurring in some other statement.
Arrays are complete on their own declared domains, not sparse collections
of available entries. An explicitly restricted tabulation can still
construct a complete array on a prefix of a named tensor's domain.

These rules use compatible declared coordinate domains, not name-based
axis matching or an implicit transpose. An implementation mapping must
retain any axis identities and explicitly justified identifications.

The core permits an explicitly restricted index domain. For example,
with $A$ of shape $(3)$, $B$ of shape $(5)$, and $i\in[3]$, the reads
$A[i]$ and $B[i]$ are both in bounds. The pointwise product
$A[i]\otimes B[i]$ uses all three entries of $A$ but only the first
three entries of $B$; $B[3]$ and $B[4]$ are unused.
This is not a full-axis einsum, which requires matching domains for
the shared index.
The standard pure-einsum profile below imposes the additional full-domain
compatibility rule. It does not replace the more general core read rule.

### 14.3 Statement and program rules

A statement is structurally well-formed when:

1. Its destination belongs to $\mathrm{Def}$.
2. Its guard and output indices are well-scoped under $\Gamma_s$.
3. Its output arity matches the destination rank.
4. $\phi_s(\nu)\in\operatorname{Coord}_{\Sigma}(T_s)$ for every $\nu\in D_s$.
5. $\Sigma;\Gamma_s;D_s\vdash E_s:K$.

A program is structurally well-formed when its declarations, role
partition, output identifiers, occurrence identifiers, and every
statement satisfy their respective conditions.

Neither injectivity of $\phi_s$ nor disjointness of different statements'
write images is required. Additive overlap is allowed.
No condition here requires an acyclic dependency graph.

### 14.4 Mathematical conditions versus compiler decisions

The quantified in-bounds premises specify a mathematical property.
They do not require a particular compiler to decide every such property
automatically. A compiler may prove admitted affine cases, accept explicit
evidence, or reject a case it cannot establish.

Operator definedness is a different condition. The interpretation in
Section 18 accounts for $\mathcal{D}_f$ (where $f$ is the primitive
operator and $\mathcal{D}_f$ is its domain of definition), distinguishing
defined values from undefined results. Section 20 then specifies
admissible inputs for a functional program denotation.
A runtime check is not a proof that every input meets that condition.

**Guard example.** Let $X$ have shape $(4)$ and $i\in[4]$:

$$
\text{for }i\in[4]\text{ where }i+1<4:
\qquad Y[i]\mathrel{+}=X[i+1].
$$

The guard makes the read in bounds throughout $D_s$.
Replacing it by the body
$\mathbf{1}_{i+1<4}X[i+1]$ without a guard does not satisfy the read
rule at $i=3$.

## 15. Surface-to-core elaboration

**Surface notation** is the compact, user-facing syntax in which tensor
logic programs are written, such as `Y[i,j] = W[i,k] X[k,j]`.
It leaves some information implicit, including the contraction over $k$.
The **core notation** from Section 13 makes binders, reductions, and
operator applications explicit. **Elaboration** translates the surface
form into that core form; it is not execution of the program.

### 15.1 Explicit inputs to elaboration

The surface notation abbreviates the core; it is not a second semantics.
Elaboration takes:

- A tensor signature and the input/defined/output roles.
- Resolved index-variable identities and their finite domains.
- The statement's output indices, optional guard, and expression structure.
- The fixed primitive registry.

Domains may originate from declarations or an unambiguous inference
procedure. This section assumes each index variable's domain is already
known. It specifies translation into core syntax, not the preceding
domain-inference procedure. Equal printed names or equal extents alone do
not resolve semantic axis identities. Ambiguous or inconsistent domains are errors,
not silent choices.

**Standard pure-einsum profile.** When a statement is presented as an
ordinary full-axis einsum, its operand indices are bare variables,
its body is a product of at least one tensor read, and it has no guard or enclosing
primitive. Every occurrence of an index variable must range over the
entire coordinate domain of its corresponding slot. Thus all slots
sharing that variable must have equal resolved domains, not merely a
common in-bounds subset. Each output variable must occur in an operand.
The declared destination has one slot per output index, in that order,
with exactly that index's resolved domain. Repeated output variables are
permitted; they label separate destination slots.

Consequently, $A[i]B[i]$ with operand lengths $3$ and $5$ is rejected as
a standard full-axis einsum. An explicitly restricted core binder can
still specify the prefix computation described in Section 14.2.
Broadcasting an output-only variable from a declared domain is also a
core/general surface capability, not a standard pure-einsum inference.
Section 17 gives the reference semantics for the standard profile.

Surface syntax supported here consists of an additive body of products
of scalar factors, optionally enclosed by one unary scalar operator or
one marked slice operator. Factors are scalar literals, named scalar
reads, Iverson values, or registered scalar unary operators on a named
scalar read. Such a factor introduces no hidden reduction of its own.

More general nesting must use explicit core reductions, tabulations, and
primitive applications. This restriction prevents inventing a contraction
scope for arbitrary nested surface expressions.

Explicit core scalar expressions can also be written as a statement body,
with their binders and primitive signatures checked directly rather than
adding implicit contractions. The slice shorthand $T[:,l]$ expands to
$\operatorname{tab}_{j\in I_{T,1}}(T[j,l])$ for a fresh $j$;
the corresponding rule for several colon slots tabulates their declared
domains in slot order. Selection from an array expression, such as
$F(T[:,l])[i]$, expands to $\operatorname{at}$ as in Section 13.3.
The fixed indices must remain well-scoped and in bounds.

### 15.2 Statement variables and term-local contraction

The contribution-variable context $\Gamma_s$ contains the variables
occurring in the output index expressions. Domains are resolved as above.
They are collected before algebraically simplifying those expressions,
so cancellation of coefficients does not remove contribution binders.

For this surface fragment, guard variables must also belong to
$\Gamma_s$. A more general core statement can explicitly bind additional
contribution variables.

Write the surface additive body as a finite list of product terms
$t_1,\ldots,t_h$. For term $t_b$, define its contracted-variable set

$$
C_b=\operatorname{FV}(t_b)\setminus\operatorname{vars}(\Gamma_s),
$$

where $\operatorname{vars}(\Gamma_s)$ is the context's variable-identity set
from Section 3.2. Each contracted variable has its own resolved
domain.

Elaborate the factors to scalar core expressions, multiply them with
$\otimes$, and bind the variables in $C_b$ using nested $\bigoplus$
reductions. A repeated variable in several factors is bound once and
has the same value in each occurrence.

Use a fixed enumeration of $C_b$ to produce a concrete syntax tree.
The exact semiring interpretation will justify independence from that
enumeration; floating-point execution must separately specify its order.
Each reduction binder is scoped only over its own term.

Let $B_s$ denote the core body obtained by combining the elaborated terms
with $\oplus$. An empty product uses $1_K$, and an empty list of terms
uses $0_K$.

This rule gives

$$
W[i,k]X[k]+B[i]
\quad\mapsto\quad
\left(\bigoplus_{k\in I_k}W[i,k]\otimes X[k]\right)\oplus B[i].
$$

It does not give
$\bigoplus_{k\in I_k}(W[i,k]\otimes X[k]\oplus B[i])$.

### 15.3 Scalar operator placement

Without an enclosing operator, the contribution body is $E_s=B_s$.
With a registered unary scalar operator $f$, it is

$$
E_s=f(B_s).
$$

In particular, contractions inside each term and explicit combination
of those terms occur inside $f$'s argument.

Separate statements with enclosing operators still create separate
contributions. Elaboration does not move $f$ outside their collection
or assume $f(x\oplus y)=f(x)\oplus f(y)$.

### 15.4 Marked slice operators

In the marked slice abbreviation, a trailing dot on a surface output index
(for example, `A[q,s.]`) marks a slice axis; it is not part of the variable's
identity or an index arithmetic operation. The output marks distinct bare
variables $j_1,\ldots,j_m$ as the operator's slice axes. Each occurs in
exactly one output slot and nowhere else in the output indices.
Their resolved domains are $I_1,\ldots,I_m$.
The statement guard must be independent of these marked variables.
This defines a rectangular slice over the full product of the marked
variables' domains for each valuation of the other contribution variables.

The enclosing operator $f$ must have the array signature

$$
f:K^{I_1\times\cdots\times I_m}\to
  K^{I_1\times\cdots\times I_m}
$$

with its own specified domain $\mathcal{D}_f$.

Choose fresh variables $h_1,\ldots,h_m$ with those domains. The scalar
contribution body at the original output coordinates is

$$
E_s=
\operatorname{at}\left(
f\left(
\operatorname{tab}_{h_1\in I_1,\ldots,h_m\in I_m}
\left(B_s[j_1:=h_1,\ldots,j_m:=h_m]\right)
\right),
(j_1,\ldots,j_m)
\right).
$$

The simultaneous substitution affects free occurrences only.
Marked variables remain contribution variables, not contracted variables.
The fresh tabulation binders supply the entire slice to the operator.

This applies an operator to one statement's body slice.
It does not first collect slices from other statements defining the
same destination. To apply softmax or another operator to a collected
tensor, use a separate named intermediate, as in Section 11.3.

Nonrectangular slices, guards depending on marked slice variables, and other
operator shapes require explicit core expressions or an explicit surface-language
extension. They are not assigned an implicit meaning by this abbreviation.

### 15.5 Structural checks after elaboration

Derive $D_s$ and $\phi_s$ from the resulting statement and check the
rules in Section 14. Elaboration preserves every source statement
occurrence. It neither merges identical statements by textual equality
nor orders them as destructive assignments.

Recognition of bounded scans, scheduling, and kernel fusion belong to
compilation rather than surface elaboration; they do not change contribution
syntax.

## 16. Worked core elaborations

### 16.1 Matrix multiplication and a bias

Take inputs $W$ of shape $(i_0,k_0)$ and $X$ of shape $(k_0,j_0)$,
and a defined tensor $Y$ of shape $(i_0,j_0)$:

```text
Y[i,j] = W[i,k] X[k,j]
```

Its core statement is

$$
\text{for }i\in[i_0],j\in[j_0]:
\quad
Y[i,j]\mathrel{+}=
\bigoplus_{k\in[k_0]}W[i,k]\otimes X[k,j].
$$

For a separate vector-input bias example, retain $W$'s shape, take input
$X$ of shape $(k_0)$ and input $B$ of shape $(i_0)$, and define $Y$ on
shape $(i_0)$:

```text
Y[i] = W[i,k] X[k] + B[i]
```

the core is

$$
\text{for }i\in[i_0]:
\quad
Y[i]\mathrel{+}=
\left(\bigoplus_{k\in[k_0]}W[i,k]\otimes X[k]\right)\oplus B[i].
$$

If $k_0=0$, the reduction is $0_K$ and the contribution is $B[i]$.
That distinguishes the intended rule from incorrectly placing the bias
inside the empty reduction.

### 16.2 Diagonal reads and writes

For input $M$ of shape $(n,n)$ and a defined rank-zero `Trace`:

```text
Trace[] = M[i,i]
```

elaborates to the rank-zero contribution

$$
\text{for }():
\quad
\operatorname{Trace}[]\mathrel{+}=
\bigoplus_{i\in[n]}M[i,i].
$$

The empty statement context has one valuation, the empty assignment,
identified with $()$ under the rank-zero convention of Section 1.2.
The repeated RHS variable binds once and selects diagonal coordinates.

By contrast, with input $X$ of shape $(n)$ and a defined `Diagonal`
of shape $(n,n)$,

```text
Diagonal[i,i] = X[i]
```

has statement context $i\in[n]$ and write map
$\phi_s(i)=(i,i)$. It contributes only to diagonal coordinates of a
declared shape $(n,n)$ tensor. Off-diagonal coordinates have empty
contribution collections.

### 16.3 Colliding writes and lost-binder prevention

The affine-write example from Section 11.2 elaborates to

$$
\text{for }i\in[2],j\in[2]:
\quad
Y[i+j]\mathrel{+}=A[i]\otimes B[j].
$$

There is no body reduction. The two occurrences at output coordinate $1$
remain distinct members of $\mathcal{C}_P(Y,1)$, with scalar-coordinate
notation $1$ abbreviating tuple $(1)$.

In a separate numerical example, let $X$ be an input of shape $(3)$
and $Y$ a defined tensor of shape $(1)$. Then

```text
Y[i-i] = relu(X[i])    # i in [3]
```

retains three contribution occurrences at coordinate $0$.
Its intended collected value is

$$
Y[0]=\sum_{i\in[3]}\operatorname{ReLU}(X[i]),
$$

not $\operatorname{ReLU}(\sum_i X[i])$.
Simplifying $i-i$ must not change the statement's binding structure or
move its activation boundary.

### 16.4 A strided convolution and an in-bounds guard

Let inputs $X,W$ have shapes $(h,w)$ and $(a,b)$, and let $Y$ be a defined
tensor whose declared output domain contains $i,j$ values satisfying

$$
i+a\le h,\qquad 2j+b\le w.
$$

For nonempty filter extents $a,b$, these conditions ensure the largest
read coordinates are in bounds. All indices range over finite ordinals,
so their lower bounds are nonnegative.

The surface statement

```text
Y[i,j] = W[p,r] X[i+p,2*j+r]
```

elaborates to

$$
\text{for }i,j:
\quad
Y[i,j]\mathrel{+}=
\bigoplus_{p\in[a]}
\bigoplus_{r\in[b]}
W[p,r]\otimes X[i+p,2j+r],
$$

where the displayed $i,j$ binders abbreviate their declared domains.
Alternatively, those inequalities can be the statement guard, leaving
other output coordinates without contributions. That specifies a
guarded computation, not zero-padded convolution.

### 16.5 Softmax over an attention slice

Work over exact reals. Let inputs $Q,K_{\mathrm{key}}$ have shapes
$(q_0,d)$ and $(s_0,d)$, and let the defined tensor $A$ have shape
$(q_0,s_0)$, with $s_0>0$:

```text
A[q,s.] = softmax(Q[q,k] Key[s,k])
```

`Key` denotes $K_{\mathrm{key}}$. The marked variable $s$ selects the
slice domain $[s_0]$. The core body for $q\in[q_0],s\in[s_0]$ is

$$
\operatorname{at}\left(
\operatorname{softmax}\left(
\operatorname{tab}_{t\in[s_0]}
\left(\sum_{k\in[d]}Q[q,k]K_{\mathrm{key}}[t,k]\right)
\right),(s)
\right).
$$

The feature index $k$ is contracted; the key-position index is tabulated
for softmax and then selected at $s$. It is not contracted into a scalar.
The full statement contributes that body to $A[q,s]$.

### 16.6 A scan history with explicit slice input

Use the shapes and bounds of Section 11.4. The recurrence statement
elaborates to

$$
\text{for }i\in[d],l\in[N]:
\quad
H[i,l+1]\mathrel{+}=
\operatorname{at}\left(
F\left(\operatorname{tab}_{j\in[d]}(H[j,l])\right),(i)
\right).
$$

The read time $l$ and write time $l+1$ are both within $[N+1]$.
$l$ is a free contribution variable, not a contracted index.
The tabulated $j$ is fresh and represents all coordinates required by $F$.

For $N=0$, this statement has no occurrences, while the base statements
still apply at time zero. For $N>0$, its apparent self-reference by tensor
name does not prevent the coordinate-level dependency analysis in Section 23 from
recognizing a forward scan.

## 17. Pure einsum semantics and transformation foundations

This section fixes the mathematical reference meaning of the standard
pure-einsum profile from Section 15.1. It does not extend the core with
a new primitive and does not define whole-program semantics.

The reference operands are complete tensor values from an environment
$\rho$. There are no nonlinear operators, guards, or affine access
maps in this profile. The general core retains those capabilities.

### 17.1 Index strings and global valuations

An **index string** $L=(j_1,\ldots,j_k)$ is an ordered tuple of index
variable identities. Unlike a context, an index string can repeat an
identity. It specifies which variable supplies each coordinate slot.

For operands $T_1,\ldots,T_m$, with $m\ge1$, let $L_r$ be the string
for operand $T_r$ and let $L$ be the output string.
Empty strings represent scalar operands or a scalar result.
The standard profile requires:

1. $L_r$ has the same length as the rank of $T_r$.
2. Each index variable's domain equals the domain of every slot it labels.
3. Every variable in $L$ occurs in at least one operand string.
4. If the result is assigned to a declared destination $T_s$, its rank
   and ordered slot domains match $L$ exactly.

Let $\Gamma_{\mathrm{all}}$ contain every distinct variable in the
operand strings, once, with its resolved domain. This is a context
in the sense of Section 3, not a concatenation retaining duplicates.
Its valuations are the paper's global index assignments, expressed
using our existing $\operatorname{Val}$ notation.

For a string $L=(j_1,\ldots,j_k)$, define

$$
J_L=I_{j_1}\times\cdots\times I_{j_k},
\qquad
\pi_L(\nu)=(\nu(j_1),\ldots,\nu(j_k)).
$$

Thus $\pi_L:\operatorname{Val}(\Gamma_{\mathrm{all}})\to J_L$ is a
coordinate projection. Equal-domain compatibility ensures that
$J_{L_r}=\operatorname{Coord}_{\Sigma}(T_r)$ for each operand.
The destination condition similarly gives
$J_L=\operatorname{Coord}_{\Sigma}(T_s)$. A larger declared destination
would instead describe a core computation with additional empty fibers,
not this standard pure-einsum profile.

For the empty string, $J_{()}=\{()\}$ and $\pi_{()}(\nu)=()$.
For $L=(i,i)$, $J_L=I_i\times I_i$ but the projection reaches only
the diagonal. A coordinate projection need not be surjective.

**Example.** For matrix multiplication, the strings are
$L_1=(i,k)$, $L_2=(k,j)$, and $L=(i,j)$.
A global valuation of $i,k,j$ simultaneously identifies the entries
of both operands and the result coordinate.

### 17.2 Canonical fiber semantics

The result of this pure einsum is the tensor value $V_L:J_L\to K$
defined by

$$
V_L[p]
=
\bigoplus_{\substack{
 \nu\in\operatorname{Val}(\Gamma_{\mathrm{all}})\\
 \pi_L(\nu)=p
}}
\;\bigotimes_{r=1}^{m}
\rho(T_r)[\pi_{L_r}(\nu)].
$$

For each output coordinate, this combines all global assignments in
its projection fiber. Each assignment multiplies the corresponding
operand values. Equal-valued products remain distinct occurrences.

This definition directly handles:

- Contraction: assignments vary over variables not retained in $L$.
- Repeated input variables: the same value supplies several operand slots.
- Repeated output variables: off-diagonal projection fibers can be empty.
- Scalars: the empty string selects the sole rank-zero coordinate.
- Empty contracted domains: there are no global assignments, so a
  nonempty output domain receives $0_K$.

**Example: ordinary contraction.**

$$
V_{(i,j)}[i,j]
=\bigoplus_{k\in I_k}
\rho(W)[i,k]\otimes\rho(X)[k,j].
$$

**Example: diagonal construction.** For the single operand $v$ with
input string $(i)$ and output string $(i,i)$,

$$
V_{(i,i)}[p,q]
=
\begin{cases}
\rho(v)[p],&p=q,\\
0_K,&p\ne q.
\end{cases}
$$

The full output domain remains $I_i\times I_i$, not a diagonal-only
coordinate set.

**Example: scalar-only operands.** If every string is empty, then
$\Gamma_{\mathrm{all}}$ is empty and has one valuation.
The result is the product of the scalar operands, not an empty sum.

### 17.3 Connection to the contribution core

Partition the global variables into:

- The distinct output variables, forming the statement context
  $\Gamma_s$.
- The remaining variables, contracted in the body.

Use guard $\mathrm{true}$, an output map $\phi_s$ given by the same
tuple projection on $\operatorname{Val}(\Gamma_s)$, and body

$$
E_s=
\bigoplus_{\text{remaining variables}}
\;\bigotimes_{r=1}^{m}T_r[L_r].
$$

$T_r[L_r]$ abbreviates a read with the variables in $L_r$ in slot order.
The displayed reduction abbreviates nested core reductions, one binder
per remaining variable. When none remain, the body is just the product.

For this single statement, collecting body values over
$\mathcal{C}_P(T_s,p)$ is intended to reproduce the canonical formula.
The required correspondence proof separates each global valuation into
its output-variable valuation and its contracted-variable valuation,
then combines the finite sums. Empty domains and repeated output
indices must be included in the proof.

Section 19.3 states this correspondence using the core interpretation.
It remains a Lean proof obligation, not a completed formal theorem.

The formula cannot be extended to nonlinear bodies by moving an
operator inside the products or sums. For example,

$$
\operatorname{ReLU}\left(\sum_k W[i,k]X[k]\right)
$$

is not generally the sum of $\operatorname{ReLU}(W[i,k]X[k])$.
The operator boundary fixed in Sections 13 and 15 remains authoritative.

### 17.4 Delta tensors and diagonal identities

For a finite coordinate domain $J$, define the **delta tensor**

$$
\delta_J:J\times J\to K,
\qquad
\delta_J[p,q]=
\begin{cases}
1_K,&p=q,\\
0_K,&p\ne q.
\end{cases}
$$

If $J$ is a product of $k$ slot domains, this can be represented as
a rank-$2k$ named tensor with the two copies of those slots in order.
For the scalar coordinate domain $J=\{()\}$, it is the scalar $1_K$.

Delta is an equality indicator, already expressible by the core
Iverson constructor. For product coordinates, $p=q$ abbreviates conjunction
of the corresponding slot equalities. It needs no additional primitive operation.
For $p\in J$ and a complete value $V:J\to K$, finite combination gives

$$
\bigoplus_{q\in J}\delta_J[p,q]\otimes V[q]=V[p].
$$

Exactly one summand selects $p$ and the rest are $0_K$.
For empty $J$, this pointwise statement has no $p$ to quantify over.

For a vector $v:I\to K$, diagonal construction is

$$
D[p,q]=\delta_I[p,q]\otimes v[p].
$$

For matrices with compatible domains,

$$
\bigoplus_{k\in I}A[i,k]\otimes D[k,j]
=A[i,j]\otimes v[j].
$$

This explains how a nested contraction with a diagonal intermediate
can be replaced by a direct pointwise scaling. It uses an equality
constraint, not merely renaming a bound variable.

**Identity caveat.** With repeated input and output string $(i,i)$,
a single-operand einsum keeps diagonal entries and zeros the rest:

$$
V_{(i,i)}[p,q]
=
\begin{cases}
\rho(M)[p,p],&p=q,\\
0_K,&p\ne q.
\end{cases}
$$

It is not the identity on arbitrary matrices. The ordinary
single-operand identity law uses a string of distinct indices, so
every coordinate is reached exactly once.

### 17.5 Conditions for semantic transformations

The following transformations are useful foundations for
compiler proofs. Their validity is about the canonical pure-einsum
values, not about arbitrary primitive operators or floating-point
executions.

**Operand permutation.** Permuting operands preserves a contraction
only when their index strings are permuted with them.
This follows from commutativity of $\otimes$.
It does not assert that matrix multiplication satisfies $AB=BA$:
changing which tensor occupies a given index string changes its reads.

**Distribution over pointwise combination.** For complete tensor values
$U,V$ with the same coordinate domain, define

$$
(U\oplus V)[p]=U[p]\oplus V[p].
$$

A pure einsum distributes over replacement of one operand by this
pointwise combination, retaining that operand's index string.
The scalar distributive law and finite combination justify the result.
The core can express pointwise combination using tabulation, as
specified in Section 13.3.

**Nesting and denesting.** An intermediate contraction may aggregate
only indices that are no longer needed by the outer contraction.
Its output interface must retain the necessary shared and final-output
indices. Inner and outer index variables must be renamed apart except
where an interface explicitly identifies them.

For example,

$$
s=\sum_i a[i]b[i]c[i]
$$

can use $u[i]=a[i]b[i]$ followed by $s=\sum_i u[i]c[i]$.
Replacing $u$ by the scalar $\sum_i a[i]b[i]$ loses the correlation
with $c[i]$ and is generally incorrect.

Likewise,

$$
\left(\sum_i a[i]\right)\left(\sum_i b[i]\right)
=\sum_i\sum_j a[i]b[j],
$$

not $\sum_i a[i]b[i]$. Equal printed binder names in separate reductions
do not identify their variables.

For the restricted rule described in the reference paper, the inner
output string and its outer operand string agree, and inner and outer
variable sets intersect only in variables carried by that interface.
That condition permits matching valuations to be combined into one
global valuation.

**Renaming versus identification.** A capture-avoiding renaming changes
variable identifiers bijectively and preserves their declared domains.
Identifying two different variables constrains their values to agree;
it is not generally semantics-preserving without justification.
Delta factors and repeated interface indices can supply that justification.

The reference paper's general denesting construction uses an index-symbol
graph to derive the identifications forced by an interface. An
implementation may use such a graph or an equivalent representation,
but must preserve those constraints and compatible domains.
This specification does not prescribe that algorithm.

### 17.6 Neutral operands and domain preservation

Define an all-ones tensor $\mathbf{1}_J:J\to K$ by
$\mathbf{1}_J[p]=1_K$.
Multiplying a summand by an all-ones operand does not change its value.
Removing that operand is a different claim: it must not remove a
variable domain, introduce or remove reductions, or change output shape.

**Counterexample.** Over the reals,

$$
\sum_{j\in[m]}X[i]\cdot\mathbf{1}_{[m]}[j]=m\,X[i].
$$

Removing both the operand and the $j$ binder gives $X[i]$, which is
generally different, including when $m=0$.
If a domain-carrying operand is eliminated, its binder and domain must
remain explicit unless a separate valid rule removes them.

Similarly, all-ones values can be introduced to represent a constant
array or retain index information, but this does not create that domain
from nothing. Domains remain supplied by signatures and binders.

This is particularly important for differentiation. Over exact reals,
with $W$ of shape $(d,e)$ and $x$ of shape $(e)$,

$$
F[i]=\sum_{j\in[e]}W[i,j]x[j]
$$

has the coordinate derivative

$$
\frac{\partial F[i]}{\partial W[a,b]}
=\delta_{[d]}[i,a]x[b].
$$

The derivative has coordinate domain $[d]\times[d]\times[e]$ for
$(i,a,b)$, even though $W$ no longer appears as an operand in its value
expression. Those domains must survive any transformation.

Our explicit signatures and binders can preserve this information
without the reference paper's all-ones-operand workaround.
Rewrite and differentiation judgments must specify both their
result values and their result coordinate domains.
No differentiability claim is made here for arbitrary primitives such
as ReLU or for arbitrary semirings.

## Part III: Denotational semantics

Denotational semantics describes values and equations without prescribing
how a machine computes them. In this part, $\rho$ is always a complete,
signature-respecting environment as defined in Section 5. It supplies
candidate values even for tensors that the program defines.

Reading $\rho(T)$ does not recursively execute statements defining $T$.
Instead, expression interpretation uses those candidate values, and
the program equations determine whether the environment is a model.
This distinction allows the same definitions to describe both acyclic
programs and cyclic equation systems.

## 18. Expression interpretation and definedness

### 18.1 Successful and undefined results

For an expression value type $\tau$ from Section 13.2, define the result
space

$$
\operatorname{Result}(\tau)=\tau\sqcup\{\bot\}.
$$

This is a tagged disjoint union. A member of $\tau$ is a successful
value; $\bot$ denotes an undefined result. We write $v$ for the
successful tag carrying value $v$.

The symbol $\bot$ is not a scalar zero, a missing-store entry, a
floating-point NaN, or a selected solution of an equation. No order
or least-fixed-point interpretation is attached to it.

For a structurally well-formed expression
$\Sigma;\Gamma;D\vdash E:\tau$, a complete environment $\rho$, and
$\nu\in D$, define

$$
\llbracket E\rrbracket_{\rho,\nu}\in\operatorname{Result}(\tau).
$$

Index expressions and predicates have the total interpretations already
introduced: integer arithmetic for $\llbracket e\rrbracket_\nu$ and
Boolean operations for $\llbracket Q\rrbracket_\nu$.
The result space is needed for value-dependent primitive applications,
not to excuse malformed tensor accesses.

Use the notation

$$
\llbracket E\rrbracket_{\rho,\nu}\downarrow v
$$

to mean that the result is the successful value $v$, and

$$
\llbracket E\rrbracket_{\rho,\nu}=\bot
$$

to mean that it is undefined. The downward arrow on an expression
means definedness, not operational termination.
The separate $\mathsf{Conf}\Downarrow\rho$ notation denotes successful
machine execution in Part IV.

### 18.2 Scalar constructors

Scalar literals, named tensor reads, and Iverson values are interpreted by

$$
\llbracket c_K\rrbracket_{\rho,\nu}=c_K,
$$

$$
\llbracket T[e_1,\ldots,e_k]\rrbracket_{\rho,\nu}
=
\rho(T)[
 \llbracket e_1\rrbracket_\nu,\ldots,
 \llbracket e_k\rrbracket_\nu],
$$

$$
\llbracket\mathbf{1}_{Q}\rrbracket_{\rho,\nu}
=
\begin{cases}
1_K,&\llbracket Q\rrbracket_\nu=\mathrm{true},\\
0_K,&\llbracket Q\rrbracket_\nu=\mathrm{false}.
\end{cases}
$$

The read is valid by the structural premises and $\nu\in D$.
For a scalar tensor, its index tuple is empty.

For $\star\in\{\oplus,\otimes\}$, define the strict lifting

$$
\operatorname{lift}_2(\star,u,v)
=
\begin{cases}
u\star v,&u,v\text{ are successful scalar values},\\
\bot,&\text{otherwise}.
\end{cases}
$$

Then

$$
\llbracket E_1\star E_2\rrbracket_{\rho,\nu}
=
\operatorname{lift}_2\left(
 \star,\llbracket E_1\rrbracket_{\rho,\nu},
 \llbracket E_2\rrbracket_{\rho,\nu}
\right).
$$

Both operands must be defined, even when one is $0_K$.
This lifting is not an assertion that
$\operatorname{Result}(K)$ itself forms the scalar semiring.
For instance, multiplying a successful zero by $\bot$ gives $\bot$,
not a successful zero.

### 18.3 Reduction and tabulation

For a reduction, let
$v_k=\llbracket E\rrbracket_{\rho,\nu[j\mapsto k]}$ for each
$k\in I_j$. Define

$$
\llbracket\bigoplus_{j\in I_j}E\rrbracket_{\rho,\nu}
=
\begin{cases}
\displaystyle\bigoplus_{k\in I_j}v_k,
 &\text{every }v_k\text{ is successful},\\
\bot,&\text{otherwise}.
\end{cases}
$$

An empty reduction succeeds with $0_K$. Its body is not interpreted
at any valuation, so an unreachable primitive application does not
cause undefinedness.

For tabulation, let $J=I_1\times\cdots\times I_m$ and define the extended
valuation for $p=(p_1,\ldots,p_m)\in J$ by

$$
\nu_p=\nu[j_1\mapsto p_1,\ldots,j_m\mapsto p_m].
$$

The tabulation result is

$$
\llbracket
\operatorname{tab}_{j_1\in I_1,\ldots,j_m\in I_m}(E)
\rrbracket_{\rho,\nu}
=
\begin{cases}
V,&
\llbracket E\rrbracket_{\rho,\nu_p}\downarrow V[p]
\text{ for every }p\in J,\\
\bot,&\text{some body result is undefined}.
\end{cases}
$$

Here $V:J\to K$ is a complete array value.
An empty $J$ produces the unique empty array successfully.
These binders use exactly the lifted domains from Section 14.1.

### 18.4 Array selection and primitive application

For array selection, let
$p=(\llbracket e_1\rrbracket_\nu,\ldots,\llbracket e_m\rrbracket_\nu)$.
Then

$$
\llbracket\operatorname{at}(E,(e_1,\ldots,e_m))\rrbracket_{\rho,\nu}
=
\begin{cases}
V[p],&\llbracket E\rrbracket_{\rho,\nu}\downarrow V,\\
\bot,&\llbracket E\rrbracket_{\rho,\nu}=\bot.
\end{cases}
$$

The structural rule guarantees that $p$ belongs to the array domain.
Selection requires the array expression to denote a complete value.
It does not bypass an undefined element of a tabulation by selecting
a different coordinate.

For a primitive $f$ with arity $q$, interpret its operands and let
$u_r=\llbracket E_r\rrbracket_{\rho,\nu}$. Define

$$
\llbracket f(E_1,\ldots,E_q)\rrbracket_{\rho,\nu}
=
\begin{cases}
f(u_1,\ldots,u_q),
 &\text{all }u_r\text{ are successful and }
 (u_1,\ldots,u_q)\in\mathcal{D}_f,\\
\bot,&\text{otherwise}.
\end{cases}
$$

The primitive's signature guarantees the successful result has its
declared type. Its domain $\mathcal{D}_f$ determines definedness;
typing alone does not.
For a nullary primitive, its argument tuple is $()$ and the same
domain-membership rule applies.

### 18.5 Definedness examples and transformation limits

Work over exact reals. The following results illustrate strictness:

$$
\llbracket\log(-1)\rrbracket_{\rho,\nu}=\bot,
\qquad
\llbracket 0\cdot\log(-1)\rrbracket_{\rho,\nu}=\bot,
$$

$$
\llbracket\bigoplus_{j\in[0]}\log(-1)\rrbracket_{\rho,\nu}=0.
$$

The empty reduction has no body instances. Multiplication by zero,
by contrast, still has an undefined operand.

If $X$ has shape $(2)$ with $\rho(X)[0]=4$ and $\rho(X)[1]=-1$, then

$$
\llbracket
\operatorname{at}\left(
 \operatorname{tab}_{j\in[2]}(\log(X[j])),(0)
\right)
\rrbracket_{\rho,\nu}
=\bot.
$$

The selected coordinate would be positive before taking its logarithm,
but the array construction includes the invalid logarithm at coordinate
$1$. This is a deliberate complete-array interpretation, not lazy
coordinate selection.

Therefore, transformations involving partial primitives must preserve
both values and definedness. Replacing $0\cdot E$ by $0$ is unsound when
$E$ can be undefined. The pure semiring transformations of Section 17
do not have this problem: their structurally valid reads and semiring
operations are total on complete environments.

## 19. Contribution collection

### 19.1 Environments with defined contributions

For a structurally well-formed program $P$, define

$$
\operatorname{AdmEnv}(P)
=
\left\{
\rho\ \middle|\
\begin{array}{l}
\rho\text{ is a complete, signature-respecting environment, and}\\
\llbracket E_s\rrbracket_{\rho,\nu}\ne\bot
\text{ for every }(s,\nu)\in\mathcal{O}_P
\end{array}
\right\}.
$$

Membership says all actual contribution bodies are defined. It does
not yet say the environment satisfies the program's equations.

Guards affect $\mathcal{O}_P$ through $D_s$, before interpreting bodies.
A valuation excluded by a guard imposes no body-definedness obligation.
Likewise, a statement with an empty occurrence domain imposes none.
In contrast, a present zero-valued contribution must still be defined.

### 19.2 Statement contributions and collected tensors

For $\rho\in\operatorname{AdmEnv}(P)$, define the contribution tensor
of one statement:

$$
V_s^\rho[p]
=
\bigoplus_{\substack{\nu\in D_s\\\phi_s(\nu)=p}}
\llbracket E_s\rrbracket_{\rho,\nu},
\qquad p\in\operatorname{Coord}_{\Sigma}(T_s).
$$

Each term here is a successful scalar value; $\bot$ is never treated
as a summand.
An empty fiber gives $0_K$.

For every defined tensor $T$, define its collected value:

$$
\operatorname{Collect}_P(\rho)(T)[p]
=
\bigoplus_{(s,\nu)\in\mathcal{C}_P(T,p)}
\llbracket E_s\rrbracket_{\rho,\nu}.
$$

Equivalently, partitioning the occurrences by statement gives

$$
\operatorname{Collect}_P(\rho)(T)[p]
=
\bigoplus_{\substack{s\in P\\T_s=T}}V_s^\rho[p].
$$

The collection is indexed by statement occurrences, so duplicate
statements remain duplicate summands. In the Boolean interpretation,
the same definitions combine contributions by OR.

The prior candidate value $\rho(T)[p]$ is not an additional summand.
It influences a contribution only if that contribution explicitly
reads it. This is equation construction, not a cumulative update of
an existing mutable tensor.

A defined tensor with no targeting statements has the zero tensor as
its collected value. No analogous default supplies an omitted input:
the input environment must provide every designated input value.

### 19.3 Correspondence with pure einsum

For the normalized pure-einsum statement of Section 17.3,
the desired local correspondence is

$$
V_s^\rho[p]=V_L[p]
$$

for every output coordinate, with $V_L$ computed from the same operand
values in $\rho$ by Section 17.2.
This statement applies whenever the contribution tensor is defined;
the pure statement itself has no partial primitive applications.

The mathematical proof decomposes a global valuation into the values
of distinct output variables and the remaining contracted variables.
The core body combines over the latter, while the write fiber combines
over the former. The resulting finite combinations enumerate exactly
the assignments in $\pi_L^{-1}(\{p\})$.

Repeated output indices can leave an empty fiber, and an empty
contracted domain can leave an empty reduction. Both sides then use
the same $0_K$ convention. With no variables, the single empty
valuation yields the scalar operand product.

This supplies a precise target for a Lean elaboration-correctness
theorem. The proof description here is not a kernel-checked proof.

### 19.4 Source order and nonlinear boundaries

Permuting source statements while preserving their bodies, binders,
guards, and distinct occurrence identities leaves
$\operatorname{AdmEnv}(P)$ and collected values unchanged, up to the
corresponding relabeling of occurrences.
Finite commutative combination justifies this property.
Deleting a duplicate statement does not generally preserve it.

Collection does not move primitive operators across sums.
Two contributions $f(A[i])$ and $f(B[i])$ give

$$
f(\rho(A)[i])\oplus f(\rho(B)[i]),
$$

provided both applications are defined.
An intermediate defined by contributions $A[i]$ and $B[i]$, followed
by a read through $f$, is related by the program equations to

$$
f(\rho(A)[i]\oplus\rho(B)[i]).
$$

These are equal only under an appropriate property of $f$ on the
relevant values. The semantics assumes no such property.

## 20. Program models and functional denotation

### 20.1 Models on supplied inputs

An input environment $\eta$ is well-typed when it supplies a value
with the prescribed coordinate domain and carrier for every identifier
in $\mathrm{In}$, and its identifier domain is exactly $\mathrm{In}$.

For such an $\eta$, define

$$
\operatorname{Models}(P,\eta)
=
\left\{
\rho\in\operatorname{AdmEnv}(P)\ \middle|\
\begin{array}{l}
\rho|_{\mathrm{In}}=\eta,\ \text{and}\\
\rho(T)[p]=\operatorname{Collect}_P(\rho)(T)[p]\\
\text{for every }T\in\mathrm{Def}
\text{ and }p\in\operatorname{Coord}_{\Sigma}(T)
\end{array}
\right\}.
$$

All defined tensors participate in these equations, not just
designated outputs. Zero defaults follow from empty contribution
collections, rather than from an extra initialization equation.

Thus the unconditional denotational meaning of a structurally
well-formed program is its model relation: it associates each
well-typed input environment with its set of models.
That set can be empty, a singleton, or contain several environments.

### 20.2 A partial equation operator

The same definition can be expressed using the partial map

$$
\Phi_P:\operatorname{AdmEnv}(P)\to
\{\text{complete, signature-respecting environments}\},
$$

given by

$$
\Phi_P(\rho)(T)=
\begin{cases}
\rho(T),&T\in\mathrm{In},\\
\operatorname{Collect}_P(\rho)(T),&T\in\mathrm{Def}.
\end{cases}
$$

It is partial relative to the space of all complete environments,
because its domain is $\operatorname{AdmEnv}(P)$.
Its result need not itself belong to $\operatorname{AdmEnv}(P)$.
For example, for the scalar statement `T[] = log(T[])`, a candidate
value $T=1$ makes the contribution defined, but $\Phi_P$ produces
$T=0$, at which the same contribution is undefined.

A model is exactly an environment $\rho$ extending $\eta$ for which
$\Phi_P$ is defined and

$$
\Phi_P(\rho)=\rho.
$$

This is a fixed-point characterization of simultaneous equations,
not an instruction to iterate $\Phi_P$ from zero.
No least-fixed-point selection, convergence claim, or solver is
introduced by this characterization.

### 20.3 Functional admissibility

Let $\operatorname{Input}_{\Sigma}$ denote the well-typed input
environments for the program's designated inputs, and let
$\operatorname{Output}_{\Sigma}$ denote the corresponding value
environments on $\mathrm{Out}$.
The fixed program's role sets are implicit in this notation; $\Sigma$
alone does not determine which identifiers are inputs or outputs.

Define the set of **functionally admissible inputs** by

$$
\operatorname{AdmInput}(P)
=
\{\eta\in\operatorname{Input}_{\Sigma}
\mid\operatorname{Models}(P,\eta)
\text{ contains exactly one environment}\}.
$$

For $\eta\in\operatorname{AdmInput}(P)$ with unique model $\rho_\eta$,
define

$$
\llbracket P\rrbracket(\eta)=\rho_\eta|_{\mathrm{Out}}.
$$

This gives a partial function

$$
\llbracket P\rrbracket:
\operatorname{Input}_{\Sigma}
\rightharpoonup\operatorname{Output}_{\Sigma}.
$$

Here the function domain is precisely $\operatorname{AdmInput}(P)$.
If an application specifies an input class
$\mathcal{A}\subseteq\operatorname{Input}_{\Sigma}$, total functional
meaning on that class requires

$$
\mathcal{A}\subseteq\operatorname{AdmInput}(P).
$$

The unique-model criterion is deliberately stronger than uniqueness
of outputs alone. Several models might agree on all designated outputs
while differing in internal tensors. Such output-only determinacy
could be studied separately; it is not silently substituted for the
criterion above.

Functionally admissible inputs and admissible candidate environments
are different notions. An environment can make every contribution
defined without satisfying any defining equation.
Conversely, a program can have no model even if all expressions are
defined on every complete environment.

### 20.4 Denotation does not imply executability

The model relation does not require acyclic dependencies.
A cyclic equation system can have a unique model and hence a
functional denotation while being outside a compiler's supported
execution fragment.

Conversely, a structurally valid program with partial operators may
fail to have a model on some well-typed inputs.
An operational implementation must distinguish successful execution
from undefined operations or unsupported dependency forms; it must
not return a success-shaped default for these cases.

Least-model semantics for monotone Boolean recursion, algebraic
solvers, and fixed-point iterations would each impose additional
requirements or select a particular interpretation. They are not
part of the semantics defined here.

## 21. Worked denotational examples

### 21.1 Duplicate contributions and zero defaults

Let $X$ be a numerical input of shape $(2)$ with values $2,5$, and
$T$ a defined output of the same shape:

```text
s_1: T[i] = X[i]    # i in [2]
s_2: T[i] = X[i]    # i in [2]
```

Every body is defined. For every candidate environment extending
the inputs, the collected values are

$$
\operatorname{Collect}_P(\rho)(T)[0]=4,
\qquad
\operatorname{Collect}_P(\rho)(T)[1]=10.
$$

The model equations therefore force the unique output $T=(4,10)$.
There is no previous value of $T$ added to those entries.

For the boundary example in Section 11.1, the same definition gives
the sum at the corner and zero throughout the uncovered interior.
For an untargeted defined tensor it gives zero at every coordinate
of its declared domain.

### 21.2 An intermediate fixes the activation boundary

At a fixed coordinate with numerical inputs $A[i]=1$, $B[i]=-1$,
two statements targeting $T$ with bodies
$\operatorname{ReLU}(A[i])$ and $\operatorname{ReLU}(B[i])$
force $T[i]=1$.

If those inputs instead contribute to `Pre`, and the only contribution
to $T[i]$ is $\operatorname{ReLU}(\operatorname{Pre}[i])$, the model
equations force

$$
\operatorname{Pre}[i]=0,\qquad T[i]=0.
$$

The distinction follows from collected equations, not from the order
in which the statements are listed.

### 21.3 A guard differs from a zero multiplier

Let $X$ be a real input of shape $(2)$ with values $4,-1$, and let
$Y$ be a defined output of shape $(2)$.
The guarded core statement

$$
\text{for }i\in[2]\text{ where }i<1:
\quad Y[i]\mathrel{+}=\log(X[i])
$$

has only the occurrence $i=0$. Its unique model gives

$$
Y[0]=\log(4),\qquad Y[1]=0.
$$

Replacing the guard by an Iverson multiplier gives

$$
\text{for }i\in[2]:
\quad Y[i]\mathrel{+}=\mathbf{1}_{i<1}\log(X[i]).
$$

Now $i=1$ is an actual occurrence. Its body is undefined, so no
environment extending these inputs belongs to
$\operatorname{AdmEnv}(P)$ and the program has no model on this input.
The zero multiplier does not repair the logarithm's domain failure.

### 21.4 Three different cyclic equation systems

Work over $\mathbb{R}$ with scalar tensors. The following programs
are structurally well-formed:

| Source statements | Collected equation | Models |
| --- | --- | --- |
| `T[] = X[]`; `T[] = 2 T[]` | $T=X+2T$ | Unique: $T=-X$ for every supplied scalar $X$ |
| `T[] = T[]` | $T=T$ | Every real scalar value is a model |
| `T[] = T[] + 1` | $T=T+1$ | No model |

In the first row, $X$ is an input and $T$ is defined.
In the other rows, only $T$ is present and the input environment is
empty.
Every contribution expression in all three rows is defined on every
complete environment.

Thus the first program has a functional denotation despite its cycle.
The second and third do not satisfy the unique-model criterion.
A bounded-scan compiler may reject all three as unsupported cycles,
without contradicting their denotational descriptions.

### 21.5 Bounded histories have simultaneous equations too

For the finite-history program in Section 11.4, assume
$F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$ is total.
The collected equations are

$$
H_0=X+Z,
\qquad
H_{l+1}=X+F(H_l)\quad(l\in[N]).
$$

They determine a unique history for every well-typed $X,Z$:
construct $H_0$, then the successive slices. Induction on time shows
that any other model must agree at time zero and at each following
slice. Totality and the stated array signature of $F$ ensure that
each constructed slice is defined and has the required domain.

For $d=1$, $N=2$, $X[0]=2$, $Z[0]=3$, and $F(h)[0]=2h[0]$, the
history entries are

$$
H[0,0]=5,\qquad H[0,1]=12,\qquad H[0,2]=26.
$$

When $N=0$, only the base slice is present. The recurrence statement
has no occurrences and does not create an additional equation.
This establishes the mathematical history meaning. Part IV explains how
completion barriers and a time-based rank yield this same history.

## 22. Denotational scope and execution requirements

The denotational definitions apply to every structurally well-formed core
program, including cyclic equations. They determine a model relation and,
on inputs with a unique complete model, a partial input-output function.
They do not choose an execution order or guarantee that every input has
a model. In particular:

- Structural well-formedness does not discharge primitive definedness.
- Repeated destinations are contributions, not mutation versions.
- Array operators depend on complete slices, not partially collected
  coordinate values.
- A cyclic but structurally well-formed program can have zero, one,
  or many models. Executing such a program requires an execution
  restriction or a separately justified solver.

An execution strategy must respect these conditions rather than replace
them with mutation-order rules. Part IV supplies a direct executor for the
coordinate-ranked fragment.
It uses complete logical values, not guesses obtained by iterating $\Phi_P$.
Its correspondence is with the unique-model meaning of Section 20, not
with a newly selected least model or mutation-order interpretation.

## Part IV: Operational semantics

The reference machine evaluates and collects individual contribution
occurrences. It permits arbitrary interleaving where dependencies allow,
but publishes a defined coordinate only after all occurrences targeting it
have been consumed.

This is an abstract, exact-value machine using the primitive interpretations
fixed in Section 13.2. Expression evaluation
is atomic at this level. Computable implementations of the primitives and
their domain tests are separate requirements, especially over exact reals.

## 23. Read footprints and executable dependencies

### 23.1 Address partitions

Fix a structurally well-formed core program $P$. Its roles partition the
address set:

$$
\operatorname{Addr}_{\mathrm{In}}
=\{(T,p)\in\operatorname{Addr}_{\Sigma}\mid T\in\mathrm{In}\},
\qquad
\operatorname{Addr}_{\mathrm{Def}}
=\{(T,p)\in\operatorname{Addr}_{\Sigma}\mid T\in\mathrm{Def}\}.
$$

Recall the destination function from Section 9.2: for
$o=(s,\nu)\in\mathcal{O}_P$,

$$
\operatorname{dst}(o)=(T_s,\phi_s(\nu)).
$$

For $a=(T,p)\in\operatorname{Addr}_{\mathrm{Def}}$, abbreviate
$\mathcal{C}_P(a)=\mathcal{C}_P(T,p)$.
These are the existing tagged occurrences and fibers, not new contributions.

### 23.2 Read footprints of expressions

For a structurally valid expression at an admissible valuation $\nu$,
define its **read footprint**
$\operatorname{Read}(E,\nu)\subseteq\operatorname{Addr}_{\Sigma}$ recursively.
This set records which named coordinates must be available before the
expression is interpreted by the direct executor:

$$
\operatorname{Read}(c_K,\nu)
=\operatorname{Read}(\mathbf{1}_Q,\nu)=\varnothing,
$$

$$
\operatorname{Read}(T[e_1,\ldots,e_k],\nu)
=\{(T,(\llbracket e_1\rrbracket_\nu,\ldots,
        \llbracket e_k\rrbracket_\nu))\},
$$

$$
\operatorname{Read}(E_1\star E_2,\nu)
=\operatorname{Read}(E_1,\nu)\cup\operatorname{Read}(E_2,\nu),
\qquad\star\in\{\oplus,\otimes\},
$$

$$
\operatorname{Read}\left(\bigoplus_{j\in I_j}E,\nu\right)
=\bigcup_{k\in I_j}\operatorname{Read}(E,\nu[j\mapsto k]),
$$

$$
\operatorname{Read}\left(
 \operatorname{tab}_{j_1\in I_1,\ldots,j_m\in I_m}(E),\nu
\right)
=\bigcup_{p\in I_1\times\cdots\times I_m}
  \operatorname{Read}(E,\nu_p),
$$

$$
\operatorname{Read}(\operatorname{at}(E,(e_1,\ldots,e_m)),\nu)
=\operatorname{Read}(E,\nu),
$$

$$
\operatorname{Read}(f(E_1,\ldots,E_q),\nu)
=\bigcup_{r=1}^{q}\operatorname{Read}(E_r,\nu).
$$

Here $\nu_p$ is the simultaneous valuation extension from Section 18.3.
An empty union is empty, including for empty reductions, empty tabulations,
and nullary primitives.

The footprint of `at` includes the whole array expression, not just the
selected entry. Both operands of a scalar operation remain in the footprint,
even for multiplication by zero. These choices implement Part III's strict
interpretation. A statement guard instead removes excluded occurrences
before footprints are taken.

A footprint is a set: reading the same address twice does not create two
availability requirements. It does **not** erase the two reads from the
expression or erase contribution multiplicity.
The footprint is a sufficient readiness requirement, not a claim of minimal
mathematical dependence. Pruning a semantically irrelevant read requires
an additional value-and-definedness preservation argument.

### 23.3 Stable evaluation from a partial store

Write $\sigma\sqsubseteq\rho$ when the complete environment $\rho$ extends
the store's available values:

$$
\sigma(a)=\rho(T)[p]
\quad\text{for every }a=(T,p)\in\operatorname{dom}(\sigma).
$$

For typed stores, complete extensions exist: assign, for example, $0_K$ to
unspecified coordinates. This is a mathematical extension for defining an
interpretation, not operational permission to read missing values as zero.

**Read-stability lemma.** If two complete environments agree on
$\operatorname{Read}(E,\nu)$, their interpretations of $E$ at $\nu$ are
equal, including the possibility that both results are $\bot$.

The proof is structural induction on $E$. Reads use the stipulated
agreement; scalar operations use the induction hypotheses for both
operands. Reductions and tabulations use them at every actual body
valuation. Selection uses equality of the complete array result.
A primitive uses equal argument results and the same domain
$\mathcal{D}_f$, hence has equal definedness and value.

When
$\operatorname{Read}(E,\nu)\subseteq\operatorname{dom}(\sigma)$,
define the ready evaluation

$$
\operatorname{Eval}_{\sigma}(E,\nu)
=\llbracket E\rrbracket_{\rho,\nu}
\quad\text{for any complete }\rho\text{ with }\sigma\sqsubseteq\rho.
$$

Read stability makes the choice irrelevant. This result belongs to
$\operatorname{Result}(\tau)$ for an expression of type $\tau$.
Write $\operatorname{Eval}_{\sigma}(E,\nu)\downarrow v$ for a successful
result. If the footprint is not available, ready evaluation is not invoked:
the occurrence waits. Waiting is distinct from a ready result of $\bot$.

### 23.4 Coordinate dependencies and the ranked fragment

For $o=(s,\nu)$, abbreviate
$\operatorname{Read}(o)=\operatorname{Read}(E_s,\nu)$.
Define

$$
\operatorname{Dep}(a)
=\bigcup_{o\in\mathcal{C}_P(a)}\operatorname{Read}(o)
\quad(a\in\operatorname{Addr}_{\mathrm{Def}}),
$$

and set $\operatorname{Dep}(a)=\varnothing$ for input addresses.

The **coordinate-ranked fragment** consists of programs with a certificate
$r:\operatorname{Addr}_{\Sigma}\to\mathbb{N}$ satisfying

$$
b\in\operatorname{Dep}(a)\Longrightarrow r(b)<r(a).
$$

Equivalently, the finite directed graph with edges $b\to a$ for
$b\in\operatorname{Dep}(a)$ is acyclic.
This graph and its certificate are independent of input values: indices,
guards, and binder domains do not depend on tensor values.
The certificate ensures dependency progress, not primitive definedness.

A compiler for this fragment must justify such a certificate or explicitly
reject the dependency form. It may use symbolic ranks without enumerating
every coordinate. The abstract graph is a specification, not a prescribed
compilation data structure.

Dependencies must be taken at coordinate level. A finite history may read
the same tensor identifier that it defines while its time coordinates
still admit a strictly increasing rank.

## 24. Machine configurations and initialization

### 24.1 Published values, accumulators, and pending occurrences

A running configuration is a triple

$$
\mathsf{Conf}=(\sigma,\alpha,U),
$$

where:

- $\sigma:\operatorname{Addr}_{\Sigma}\rightharpoonup K$ is the store of
  **published, complete** coordinate values.
- $\alpha:\operatorname{Addr}_{\mathrm{Def}}\to K$ is the accumulator map.
  An accumulator may contain only some of a coordinate's contributions.
- $U\subseteq\mathcal{O}_P$ is the set of pending occurrences, not yet
  successfully consumed.

Accumulators are not expression-readable. Only $\sigma$ supplies named
reads. A published value is immutable; source contributions are never
applied as later mutations to that value.
The reference machine retains accumulators after publication to simplify
the conservation argument. Its immutable published history and completed
accumulators may become proof-only information in a compiled implementation,
as introduced in Section 5.3. This does not relax logical readiness.

It also has terminal failed configurations
$\mathsf{Failed}(o,\sigma,\alpha,U)$, recording an occurrence whose ready
body was undefined and the machine state at failure.
This outcome is an explicit error, not a scalar result or an empty sum.
More detailed primitive-path diagnostics can refine this record without
changing the rules below.

### 24.2 Initial configuration

For $\eta\in\operatorname{Input}_{\Sigma}$, initialize

$$
\operatorname{Init}(P,\eta)
=(\sigma_\eta,\alpha_0,\mathcal{O}_P),
$$

where

$$
\operatorname{dom}(\sigma_\eta)=\operatorname{Addr}_{\mathrm{In}},
\qquad
\sigma_\eta(T,p)=\eta(T)[p],
\qquad
\alpha_0(a)=0_K
\quad(a\in\operatorname{Addr}_{\mathrm{Def}}).
$$

No defined address is initially published.
Accumulator initialization is a machine operation, not an additional
source contribution. In particular, zero-filled accumulators do not make
a recurrence's future states readable.

The program's structural judgments and the complete input signature must
be validated before initialization. Missing inputs, malformed shapes, or
invalid structural accesses require explicit rejection; they are not
repaired with zeros. This applies even to an empty input tensor: its value
must be supplied although it contributes no coordinate entries to
$\sigma_\eta$.

## 25. Execution rules and terminal outcomes

The step relation fixes $P$ and its primitive registry. Rules select any
occurrence or address satisfying their premises; source-list order is not
an execution priority.

### 25.1 Consume a defined contribution

For $o=(s,\nu)$ and $a=\operatorname{dst}(o)$:

$$
\frac{
o\in U
\qquad
\operatorname{Read}(o)\subseteq\operatorname{dom}(\sigma)
\qquad
\operatorname{Eval}_{\sigma}(E_s,\nu)\downarrow v
}{
(\sigma,\alpha,U)
\longrightarrow
(\sigma,\alpha[a\mapsto\alpha(a)\oplus v],U\setminus\{o\})
}
\quad\mathrm{CONTRIBUTE}.
$$

This rule removes exactly one tagged occurrence and combines its value
exactly once. The destination remains unpublished until the completion
rule applies. A successful zero-valued body still consumes its occurrence.

### 25.2 Publish a completed coordinate

$$
\frac{
a\in\operatorname{Addr}_{\mathrm{Def}}\setminus
      \operatorname{dom}(\sigma)
\qquad
U\cap\mathcal{C}_P(a)=\varnothing
}{
(\sigma,\alpha,U)
\longrightarrow
(\sigma[a\mapsto\alpha(a)],\alpha,U)
}
\quad\mathrm{PUBLISH}.
$$

This is the **completion barrier**: no pending contribution to $a$ remains.
Publication may be delayed by scheduling but cannot occur early.

When $\mathcal{C}_P(a)=\varnothing$, publication is enabled immediately
and publishes $0_K$. An unwritten coordinate thus becomes an available
zero by an explicit completion step, not by treating absence as zero.
When a coordinate has contributions, even a currently zero accumulator
cannot be published until all those occurrences are consumed.

### 25.3 Surface undefined operations

For $o=(s,\nu)$:

$$
\frac{
o\in U
\qquad
\operatorname{Read}(o)\subseteq\operatorname{dom}(\sigma)
\qquad
\operatorname{Eval}_{\sigma}(E_s,\nu)=\bot
}{
(\sigma,\alpha,U)
\longrightarrow
\mathsf{Failed}(o,\sigma,\alpha,U)
}
\quad\mathrm{UNDEFINED}.
$$

The failed configuration has no outgoing steps. The invalid occurrence
is not consumed as zero, and partially published outputs are not returned
as a successful program result.
The occurrence identifier and valuation locate the failed contribution.

Undefinedness is checked only for actual, ready occurrences. A guard-excluded
valuation has no occurrence; an empty binder has no body instances.
No failure is raised for those absent body instances. A primitive applied
outside an empty binder still has its own domain requirement.

### 25.4 Completion and dependency blocking

A running configuration is **complete** when

$$
U=\varnothing,
\qquad
\operatorname{dom}(\sigma)=\operatorname{Addr}_{\Sigma}.
$$

It then determines a complete environment $\rho_\sigma$ by
$\rho_\sigma(T)[p]=\sigma(T,p)$.
Tensors with empty coordinate domains have their unique empty function
values in this environment.

Define successful execution by

$$
\mathsf{Conf}\Downarrow\rho
\quad\Longleftrightarrow\quad
\mathsf{Conf}\longrightarrow^{*}(\sigma,\alpha,\varnothing)
\text{ with }\operatorname{dom}(\sigma)=\operatorname{Addr}_{\Sigma}
\text{ and }\rho=\rho_\sigma.
$$

All defined tensors must complete, including internal tensors not in
$\mathrm{Out}$. This matches the complete-model criterion in Section 20.3.
The externally returned output is $\rho|_{\mathrm{Out}}$.

A running configuration is **blocked** when it is not complete and has
no enabled transition. It is neither a successful result nor an
undefined-operation failure. Blocking reports an unresolved dependency
structure; it does not prove that the equations lack a model.
Section 26 shows that a ranked program cannot reach such a state.

## 26. Conservation, termination, and correspondence

The claims below concern configurations reachable from
$\operatorname{Init}(P,\eta)$ for well-typed $\eta$.
They are mathematical claims with proof arguments, not already verified
Lean declarations.

### 26.1 Basic conservation invariants

Induction on transitions establishes:

1. $U\subseteq\mathcal{O}_P$ and every successful contribution step removes
   one previously pending occurrence. No occurrence is consumed twice.
2. Accumulators and published values belong to $K$.
3. Published addresses only increase, input values remain unchanged, and
   no published value is overwritten.
4. If a defined address is published, no occurrence targeting it remains
   pending, and its published value equals its accumulator.

More explicitly, if $v_o$ is the value returned at the step consuming $o$,
then at each running configuration

$$
\alpha(a)=
\bigoplus_{o\in\mathcal{C}_P(a)\setminus U}v_o.
$$

The values $v_o$ are associated with the execution history for this
argument; they need not be extra stored machine fields.
The formula follows from zero initialization and finite commutative
combination. Duplicate statements and colliding write valuations remain
distinct terms because they have distinct tagged occurrences.

### 26.2 Preservation of every candidate model

Fix any $\rho\in\operatorname{Models}(P,\eta)$.
At every reachable running configuration:

$$
\sigma\sqsubseteq\rho,
$$

$$
\alpha(a)=
\bigoplus_{(s,\nu)\in\mathcal{C}_P(a)\setminus U}
\llbracket E_s\rrbracket_{\rho,\nu}.
$$

Initially the store agrees on inputs and every sum is empty.
For a ready occurrence, read stability makes its ready evaluation equal
to its interpretation in $\rho$, which is defined since $\rho$ is a model.
A contribution step therefore preserves the accumulator formula.
At publication the sum contains all of $\mathcal{C}_P(a)$ and equals
$\rho(T)[p]$ by the model equation. Thus store agreement is preserved.
An undefined-operation step is impossible in the presence of such a model.

### 26.3 Successful execution gives the unique model

Suppose
$\operatorname{Init}(P,\eta)\Downarrow\rho_\sigma$.
Every occurrence was consumed successfully. Its footprint was available
when it was consumed, and published values never changed.
Read stability therefore identifies its recorded value with its
interpretation in the final $\rho_\sigma$.
All contribution bodies are defined there, and each published accumulator
is their complete fiber sum. Hence

$$
\rho_\sigma\in\operatorname{Models}(P,\eta).
$$

For any other model $\rho$, Section 26.2 gives
$\sigma\sqsubseteq\rho$ at the complete final store. Since the store has
every address, $\rho=\rho_\sigma$. Thus

$$
\operatorname{Models}(P,\eta)=\{\rho_\sigma\},
\qquad
\llbracket P\rrbracket(\eta)=\rho_\sigma|_{\mathrm{Out}}.
$$

No rank certificate is needed for this implication: any successful run
has this meaning.
Similarly, if a run reaches $\mathsf{Failed}(o,\sigma,\alpha,U)$,
then $\operatorname{Models}(P,\eta)=\varnothing$.
Otherwise Section 26.2 and read stability would force the failed ready
body to be defined in a model, a contradiction.
This failure claim does not apply to dependency blocking.

### 26.4 Finite execution and progress for ranked programs

For a running configuration define the natural-number measure

$$
\mu(\sigma,\alpha,U)
=|U|+
\left|\operatorname{Addr}_{\mathrm{Def}}\setminus
             \operatorname{dom}(\sigma)\right|.
$$

A contribution step decreases its first term by one. A publication step
decreases its second term by one. An undefined-operation step is terminal.
Thus every run has at most
$|\mathcal{O}_P|+|\operatorname{Addr}_{\mathrm{Def}}|$
non-failure steps and cannot have infinitely many transitions.
A **maximal run** continues until no transition is enabled; a finite
prefix stopped by a scheduler is not automatically maximal.
No fairness assumption is needed because the rules permit no stuttering steps.

Assume a rank certificate exists. In any reachable, noncomplete
running configuration there is an unpublished defined address:
if all were published, the invariants would also force $U=\varnothing$.
Choose one of minimum rank. All its dependencies are already published,
since inputs were supplied initially and defined dependencies have lower
rank. If its fiber has pending occurrences, each is ready and enables
either $\mathrm{CONTRIBUTE}$ or $\mathrm{UNDEFINED}$.
If it has none, $\mathrm{PUBLISH}$ is enabled.
This proves progress and excludes blocking.

Combining progress, finite execution, and Section 26.3 gives the
operational/denotational correspondence for the ranked fragment:

$$
\operatorname{Init}(P,\eta)\Downarrow\rho
\quad\Longleftrightarrow\quad
\operatorname{Models}(P,\eta)=\{\rho\}.
$$

In more detail, every maximal run either succeeds or explicitly fails.
If a model exists, model preservation excludes failure, so every maximal
run succeeds and returns that unique model. If no model exists,
successful completion is impossible, so every maximal run fails.
Ranked programs cannot have several models on the same input.

Therefore the direct executor realizes exactly the partial function of
Section 20.3 for ranked programs. Successful schedules produce the same
environment, even if they consume contributions and publish unrelated
addresses in different orders. On a failing input, schedules may report
different undefined occurrences; the first diagnostic is not claimed to
be schedule-independent.

## 27. Worked operational examples

### 27.1 An accumulator is not a readable intermediate

Use scalar numerical inputs $A[]=1$ and $B[]=-1$:

```text
Pre[] = A[]
Pre[] = B[]
T[]   = relu(Pre[])
```

After consuming only the first contribution,
$\alpha(\operatorname{Pre},())=1$, but
$(\operatorname{Pre},())\notin\operatorname{dom}(\sigma)$.
The contribution to $T$ is not ready. Consuming the second gives
$\alpha(\operatorname{Pre},())=0$; publication now makes the completed
zero readable. ReLU then contributes zero to $T$, which can be published.
Reversing the first two consumption steps gives the same result.

Applying ReLU to the partially accumulated value $1$ would violate the
readiness rule and change the program's meaning.
Separate contributions `relu(A[])` and `relu(B[])` instead produce $1$,
as in Section 21.2; that is a different program.

### 27.2 Boundary overlap and unwritten coordinates

For Section 11.1, the corner's fiber contains both its row and column
occurrences. If $C[0]=2$ and $R[0]=7$, its accumulator may first be $2$
or $7$, depending on scheduling. It becomes readable only after both
occurrences are consumed and $T[0,0]=9$ is published.
There is no overlap-agreement test.

An interior coordinate such as $(T,(1,1))$ has an empty fiber.
It can be published as zero immediately. A consumer may read that zero
after publication, but never merely because the address is absent.
Duplicate statements and affine write collisions use the same completion
rule, with all their occurrences retained.

### 27.3 Guards, empty binders, and failure

For the guarded logarithm of Section 21.3, only $i=0$ belongs to the
occurrence set. Its body is ready from the supplied $X$ and contributes
$\log(4)$; the empty fiber at $Y[1]$ publishes zero.

For the Iverson-multiplied version, both occurrences are present.
The body at $i=1$ is ready but undefined, so a maximal run reaches
$\mathsf{Failed}((s,i=1),\sigma,\alpha,U)$.
It cannot return the partially computed $Y$ as a successful output.

Empty binders also affect dependencies. The scalar statement

$$
T[]\mathrel{+}=\bigoplus_{j\in[0]}T[]
$$

has one contribution occurrence, but that body's read footprint is empty.
It contributes zero and $T$ then publishes zero.
The tensor name appears on both sides, yet there is no coordinate
dependency cycle: the bound body has no instances.

### 27.4 Bounded scans and complete logical slices

For Section 11.4, the recurrence body at $(i,l)$ has the core form

$$
\operatorname{at}\left(
F\left(\operatorname{tab}_{j\in[d]}(H[j,l])\right),(i)
\right).
$$

Its footprint is $\{(H,(j,l))\mid j\in[d]\}$.
Thus every coordinate of $H_l$ must be published before this recurrence
contribution is ready. No update reads a partially accumulated slice.

A certificate is

$$
r(X,i)=r(Z,i)=0,
\qquad
r(H,(i,l))=l+1,
$$

where $r(X,i)$ abbreviates $r((X,(i)))$, and similarly for $Z$.
The persistent-input and base contributions depend only on supplied
inputs. Every recurrence destination at time $l+1$ depends only on the
lower-ranked slice at time $l$.

For the scalar example $X[0]=2$, $Z[0]=3$, $F(h)[0]=2h[0]$, and $N=2$,
one legal schedule is:

| Step group | Accumulator change or publication |
| --- | --- |
| Consume the three persistent-input occurrences | Accumulators at times $0,1,2$ are each $2$ |
| Consume the base occurrence | Time-zero accumulator becomes $5$ |
| Publish time zero | $H[0,0]=5$ becomes readable |
| Consume the recurrence occurrence for $l=0$ | Time-one accumulator becomes $2+10=12$ |
| Publish time one | $H[0,1]=12$ becomes readable |
| Consume the recurrence occurrence for $l=1$ | Time-two accumulator becomes $2+24=26$ |
| Publish time two | $H[0,2]=26$ becomes readable |

The first row represents three separate machine steps.
There are six contribution steps and three publication steps in total.
Other legal schedules give the same history.
In particular, a future slice may accumulate its persistent input early,
but it cannot publish until its recurrence contributions also arrive.

When $N=0$ there are no recurrence occurrences. When $d=0$ there are no
history coordinates or contributions, and the history is the unique
empty tensor. No nonexistent recurrence body is evaluated.

### 27.5 A cycle can block with or without a model

For `T[] = X[]; T[] = 2 T[]`, the supplied-input occurrence can contribute
$X$ to the accumulator. The self-reading occurrence then waits for $T$,
while publication waits for that same occurrence. The machine is blocked,
although the unique model is $T=-X$.

For `T[] = T[]`, the initial machine is already blocked and the equations
have many models. For `T[] = T[] + 1`, it is also blocked and there is no
model. These three outcomes are denotationally different despite the
same kind of unresolved operational cycle.

None admits the rank certificate of Section 23.4.
A ranked-fragment compiler should report an unsupported dependency form,
not assert inconsistency or pick the zero accumulator as a solution.

## 28. Reference-machine boundaries and proof targets

Part IV specifies logical execution, not a storage layout or a claim about
the current compiler. A compiled implementation may collect whole tensors,
batch occurrences, fuse reductions, or run independent work in parallel,
provided it preserves:

- Every actual contribution occurrence, exactly once, including duplicate
  statements and colliding valuations.
- The exact-semiring fiber combination.
- Ready, complete values for every expression read and primitive argument.
- Immutable logical versions, particularly distinct scan time coordinates.
- Explicit undefined-operation failure and rejection of unsupported
  dependencies, rather than success-shaped defaults.

Fusing contribution and publication steps is valid only if the same
completion barrier is maintained. Pruning reads or occurrences requires
definedness preservation as well as value preservation.
Physical buffer reuse requires a separate liveness and representation
argument: a time-based logical rank does not itself justify overwriting a
value that a remaining operation still needs.
Exact commutative sums are not automatically bitwise floating-point
guarantees; a machine-arithmetic interpretation must specify its reduction
order or numerical correctness criterion.

The foundational proof targets are:

1. Typed expression interpretation and read footprints are well-defined;
   interpretation returns a declared value or $\bot$.
2. Interpretation and footprints respect bound-variable renaming and
   well-scoped, domain-respecting capture-avoiding substitution.
3. Read stability justifies ready evaluation independently of a chosen
   complete extension.
4. Core elaboration preserves pure-einsum values, domains, and multiplicity,
   including empty domains and repeated output indices.
5. Source-statement permutation preserves the model relation and successful
   execution results under corresponding occurrence relabeling.
6. The transition invariants and model-preservation claims hold.
7. The finite measure and rank certificate establish termination and
   progress; the resulting executor computes exactly the unique model
   or explicitly fails on a ranked program.

The arguments in Part IV establish the reference-machine properties.
Part V supplies the compilation/refinement layer: it defines plan contracts
and the relation between logical states and reusable storage.
General cyclic solvers remain a separately justified extension, not an
implicit fallback.

## Part V: Compilation and refinement

The reference machine specifies which values may be computed and when
they become readable. A compiled plan adds a schedule, kernels, and a
storage discipline. Correct compilation must preserve the reference
meaning while allowing many reference steps to be performed by one
kernel and allowing dead physical storage to be reused.

The plan contracts define an exact-value, sequential execution profile.
"Sequential" refers to command boundaries: a kernel may internally batch
or parallelize independent work if its contract is proved.
No particular existing plan representation or compiler is assumed to
satisfy these contracts. Lowering $K$ to machine arithmetic is a separate
refinement problem.

## 29. Execution plans and logical action contracts

### 29.1 Plans, commands, and annotations

Fix a structurally well-formed program $P$ in the coordinate-ranked fragment.
An execution plan $\Pi$ records the source signature and tensor roles
$(\mathrm{In},\mathrm{Def},\mathrm{Out})$,
a finite buffer collection $\mathcal{B}$ with capacities, and a finite
command sequence

$$
(\kappa_0,\ldots,\kappa_{m-1}).
$$

Each command has a kernel implementation and an annotation specifying
its logical action. The basic action contracts are:

- $\mathsf{Accumulate}(G)$, for a finite set
  $G\subseteq\mathcal{O}_P$ of tagged contribution occurrences.
- $\mathsf{Publish}(B)$, for a finite block
  $B\subseteq\operatorname{Addr}_{\mathrm{Def}}$ of coordinates.
- $\mathsf{Storage}(\theta)$, for a declared storage operation $\theta$
  such as initialization, copying, relocation, or retirement, with no
  change to the reference configuration.

Here $B$ is a set of logical addresses, not the buffer collection
$\mathcal{B}$. A block may describe a tensor, a slice, or a smaller region.
The set $G$ contains occurrence identities, not distinct numerical values;
equal-valued contributions are not deduplicated.

A fused command may have a finite sequence of these annotations.
Its contract is their sequential composition, even if intermediate
states exist only in its proof. Bounded loops may describe commands and
occurrence groups compactly; their mathematical expansion must be finite.
The specification does not require a compiler to enumerate every occurrence.

### 29.2 Accumulation and publication contracts

For $\mathsf{Accumulate}(G)$ at $(\sigma,\alpha,U)$, require

$$
G\subseteq U,
\qquad
\operatorname{Read}(o)\subseteq\operatorname{dom}(\sigma)
\quad\text{for every }o\in G.
$$

If every body succeeds with value $v_o$, the logical post-state is
$(\sigma,\alpha',U\setminus G)$, where

$$
\alpha'(a)
=\alpha(a)\oplus
 \bigoplus_{o\in G\cap\mathcal{C}_P(a)}v_o
\quad(a\in\operatorname{Addr}_{\mathrm{Def}}).
$$

The contract leaves $\sigma$ unchanged. If a body is undefined, the kernel
must explicitly fail in a way matching a reference execution ending in
$\mathsf{Failed}$, not produce a successful aggregate.
Section 32 specifies the correspondence for both cases.

For $\mathsf{Publish}(B)$, require

$$
B\cap\operatorname{dom}(\sigma)=\varnothing,
\qquad
U\cap\mathcal{C}_P(a)=\varnothing
\quad\text{for every }a\in B.
$$

Its logical post-state extends $\sigma$ by $a\mapsto\alpha(a)$ for all
$a\in B$, leaving $\alpha,U$ unchanged.
Publishing a block does not replace completion of its constituent fibers.
An empty $G$ or $B$ has no logical effect; it does not evaluate nonexistent
bodies or supply missing shapes.

### 29.3 Coverage and schedule certificates

Expand fused annotations in their stated order. A plan's logical schedule
must satisfy:

1. Its accumulation groups are pairwise disjoint and their union is
   $\mathcal{O}_P$.
2. Its publication blocks are pairwise disjoint and their union is
   $\operatorname{Addr}_{\mathrm{Def}}$.
3. Every defined address in $\operatorname{Read}(o)$ is published before
   the group containing $o$. Input addresses are supplied initially.
4. Every occurrence in $\mathcal{C}_P(a)$ is in an accumulation group
   before the block publishing $a$.

These conditions preserve all actual contributions and every declared
defined coordinate, including empty fibers. They also ensure the readiness
and completion premises of Section 29.2 at each successful prefix.
They do not establish body-definedness on every input.

Storage annotations have additional representation obligations in
Section 30. Schedule validity alone does not prove a correct kernel,
layout, or aliasing discipline.

For example, grouping both copies of `T[i] = X[i]` into one kernel is
permitted, but the group still contains both occurrence identities.
Publishing `T` after only one group is not permitted if another group
still contributes to it.

## 30. Concrete states and logical representation

### 30.1 Concrete command execution

A running concrete state has the form

$$
\mathsf{C}=(\mathsf{pc},M,\chi),
\qquad \mathsf{pc}\in[m+1],
$$

where $M$ is the memory from Section 5.3 and $\chi$ is the plan's specified
control and layout metadata. It is not a second source-language environment.
Metadata may be determined statically by the command position rather than
stored as runtime fields.

For $\mathsf{pc}<m$, executing $\kappa_{\mathsf{pc}}$ defines a transition

$$
\mathsf{C}\longrightarrow_\Pi\mathsf{C}'.
$$

A successful command advances $\mathsf{pc}$ by one.
An undefined source contribution produces a terminal
$\mathsf{PlanFailed}(o)$ with an identified source occurrence $o$.
Command execution must be defined by the chosen kernels; the action
annotations specify obligations on that execution, not a substitute for
implementing the kernels.

Write $\operatorname{Start}_\Pi(\eta)$ for concrete initialization from
the same well-typed input environment as the reference machine.
It validates input identifiers and shapes and installs the required
input values and initial metadata. An omitted empty input is still an error.

### 30.2 Resource views and live representations

Distinguish two kinds of logical resource:

- $\mathsf{pub}(a)$, for $a\in\operatorname{dom}(\sigma)$: the immutable
  published value $\sigma(a)$.
- $\mathsf{acc}(a)$, for
  $a\in\operatorname{Addr}_{\mathrm{Def}}\setminus\operatorname{dom}(\sigma)$:
  an unpublished accumulator value $\alpha(a)$.

For a related concrete and reference state, a layout view
$\lambda_{\mathsf{C}}$ partially maps these resources to
$\operatorname{Slot}_{\mathcal{B}}$.
The layout is justified by plan metadata and proof annotations; it may
be known from the command position.
Whenever a resource is mapped:

$$
M[\lambda_{\mathsf{C}}(\mathsf{pub}(a))]=\sigma(a),
\qquad
M[\lambda_{\mathsf{C}}(\mathsf{acc}(a))]=\alpha(a),
$$

with the respective side conditions
$a\in\operatorname{dom}(\sigma)$ and
$a\notin\operatorname{dom}(\sigma)$.
Every mapped slot is initialized. The simple profile here requires
$\lambda_{\mathsf{C}}$ to be injective on its domain: distinct simultaneously
represented resources occupy distinct slots.
More permissive aliasing needs a separate justification.

Define the output address set

$$
\operatorname{Addr}_{\mathrm{Out}}
=\{(T,p)\in\operatorname{Addr}_{\Sigma}\mid T\in\mathrm{Out}\}.
$$

At $(\sigma,\alpha,U)$, every published address in

$$
\operatorname{Need}_{\mathrm{pub}}(\sigma,U)
=\operatorname{dom}(\sigma)\cap
 \left(
 \operatorname{Addr}_{\mathrm{Out}}
 \cup\bigcup_{o\in U}\operatorname{Read}(o)
 \right)
$$

must have a mapped $\mathsf{pub}$ resource.
All outputs remain concretely represented once published, and every
remaining contribution's already-published sources remain represented.
A plan may retain extra resources for its own storage operations.
Any such operation's actual reads must also have valid representations.

For $a\in\operatorname{Addr}_{\mathrm{Def}}$, an unpublished address
that has already received a contribution must
retain a mapped accumulator:

$$
a\notin\operatorname{dom}(\sigma),
\quad
\mathcal{C}_P(a)\setminus U\ne\varnothing
\quad\Longrightarrow\quad
\mathsf{acc}(a)\in\operatorname{dom}(\lambda_{\mathsf{C}}).
$$

An untouched accumulator has the known value $0_K$ by Section 26.1 and
need not yet occupy a slot. Before a kernel updates or reads its physical
accumulator, it must materialize that zero or prove an equivalent
initial-write operation. Uninitialized memory is never used as a zero.

These requirements permit a compiled execution to forget dead published
values and completed accumulators physically. Their values remain in the
reference state as ghost history, not as available runtime storage.

### 30.3 Storage changes and retirement

A $\mathsf{Storage}(\theta)$ command must preserve its related reference
configuration. Typical valid effects include:

- Initialize an untouched accumulator's physical slot to $0_K$.
- Copy or relocate a represented resource, updating its layout view while
  preserving its value.
- Retire a published resource that is not needed by any remaining
  contribution, output decoding, or remaining concrete storage operation.
- Reuse a retired slot for a different logical resource.

A live unpublished accumulator cannot be discarded before its coordinate
is published. At publication its slot may change role from
$\mathsf{acc}(a)$ to $\mathsf{pub}(a)$ without changing its contents.
The reference accumulator remains in the proof state.

Retirement removes a physical representation, not the address from
$\operatorname{dom}(\sigma)$. Reuse does not identify the old and new logical
addresses. Buffer ownership and ordered coordinates must follow $\Sigma$;
matching printed axis names or equal extents is not a layout proof.

Liveness between commands is not sufficient for safety inside a kernel:
all required reads of old contents must occur before an overlapping write,
or an independent snapshot must preserve them. Temporary array storage
must also be initialized, typed, and protected from conflicting writes.

### 30.4 The refinement relation and output decoder

Write

$$
\mathcal{R}_\Pi(\mathsf{C},\mathsf{Conf})
$$

for the plan's representation relation. It includes:

1. The memory/layout equalities and live-resource requirements above.
2. Agreement between the command prefix and the reference bookkeeping:
   consumed occurrences, published coordinates, and remaining occurrences.
3. Correct types, capacities, coordinate layouts, and control metadata.

It relates memory to a reference configuration, not directly to an arbitrary
solution of the equations. Starting from the same input and simulating
steps will establish the related reference state's reachability.
Ghost information may witness this relation but may not supply kernel
reads or returned values.

At $\mathsf{pc}=m$, a successful output decoder
$\operatorname{Decode}_\Pi(\mathsf{C})$ must reconstruct the whole declared
output environment from concrete representations and signature metadata.
For every output coordinate:

$$
\operatorname{Decode}_\Pi(\mathsf{C})(T)[p]
=M[\lambda_{\mathsf{C}}(\mathsf{pub}((T,p)))].
$$

An output with empty coordinate domain is reconstructed as its unique
empty function with the declared signature; it requires no slots.
A scalar output requires its one rank-zero coordinate.
The decoder cannot recover overwritten output entries from ghost history
or silently supply zeros at missing nonempty output coordinates.

## 31. Simulation and compiler correctness

### 31.1 Acceptance and explicit rejection

Write $P\vdash\Pi\ \mathsf{valid}$ for a plan with the schedule,
representation, and kernel certificates specified here.
A proposed compiler may return an accepted plan with those certificates,
or explicitly reject an invalid source, unsupported dependency form,
unsupported primitive, or unjustified storage strategy.

Rejection does not assert that the program has no model.
Compiler completeness for every ranked program is not required by this
specification. Compiler **soundness** requires that every accepted plan
satisfy its certificates for all well-typed inputs, with semantic failures
handled as below.

### 31.2 Initial states and successful-step simulation

The initialization obligation is

$$
\mathcal{R}_\Pi(
 \operatorname{Start}_\Pi(\eta),\operatorname{Init}(P,\eta)).
$$

For each successful concrete step, require

$$
\mathcal{R}_\Pi(\mathsf{C},\mathsf{Conf})
\ \land\
\mathsf{C}\longrightarrow_\Pi\mathsf{C}'
\quad\Longrightarrow\quad
\exists\mathsf{Conf}'\;.\;
\mathsf{Conf}\longrightarrow^{*}\mathsf{Conf}'
\ \land\
\mathcal{R}_\Pi(\mathsf{C}',\mathsf{Conf}').
$$

The matching reference segment must implement the command's declared
annotations. A batch may match many contribution steps; a block publication
may match many publication steps; a pure storage change matches zero steps.
A fused command must justify the same intermediate logical barriers as
its annotation sequence.

This is a **forward simulation with stuttering**: a concrete step may
leave the reference state unchanged. It is not enough, by itself, to prove
concrete termination or prevent an incorrectly stuck compiled execution.

### 31.3 Failure matching, progress, and finishing

If a related concrete state steps to $\mathsf{PlanFailed}(o)$, require
a matching reference segment ending in

$$
\mathsf{Conf}\longrightarrow^{*}
\mathsf{Failed}(o,\sigma',\alpha',U').
$$

Thus the reported semantic failure is caused by an actual ready,
undefined source occurrence. A generic kernel exception is not automatically
such a proof. Resource exhaustion or hardware faults require separate
explicit implementation errors; they do not establish absence of a model.

Concrete progress requires that every reachable running state with
$\mathsf{pc}<m$ can execute its next command successfully or report a
matched semantic failure. It cannot merely wait forever for an unmet
completion premise that the schedule certificate should have supplied.
Kernel and domain-test implementations must terminate on their stated
preconditions. Since every successful command advances the bounded program
counter, maximal plan runs are then finite, including storage-only steps.

At $\mathsf{pc}=m$, terminal adequacy requires the related reference state
to be complete and

$$
\operatorname{Decode}_\Pi(\mathsf{C})=\rho_\sigma|_{\mathrm{Out}}.
$$

Write
$\operatorname{Start}_\Pi(\eta)\Downarrow_\Pi\zeta$
for a finite concrete run ending at such a successful final state with
decoded output environment $\zeta$.
No decoded success is permitted after a failed command.

### 31.4 The compiled-correctness theorem

For $P\vdash\Pi\ \mathsf{valid}$ in this ranked profile and well-typed $\eta$,
the preceding obligations yield

$$
\operatorname{Start}_\Pi(\eta)\Downarrow_\Pi\zeta
\quad\Longleftrightarrow\quad
\exists\rho\;.\;
\operatorname{Models}(P,\eta)=\{\rho\}
\ \land\ \zeta=\rho|_{\mathrm{Out}}.
$$

Equivalently, successful plan inputs are precisely
$\operatorname{AdmInput}(P)$, and on that domain the decoded output equals
$\llbracket P\rrbracket(\eta)$. The model-set formulation avoids applying
the partial denotation outside its domain.

For the forward direction, initialization and successful-step simulation
produce a reachable reference state; terminal adequacy makes it complete.
Section 26.3 then gives the unique model and the stated decoded output.
A matched concrete failure instead implies
$\operatorname{Models}(P,\eta)=\varnothing$.

For the reverse direction, a model excludes matched failure by
Section 26.2. Concrete progress, terminating kernels, and the finite command
counter force a successful final state, whose decoder returns that model's
outputs. If there is no model, successful finishing is impossible, so every
maximal valid-plan run reports a matched semantic failure.

The theorem is conditional on the stated certificates. It is a compiler
proof specification with a mathematical argument, not a claim that a
particular compiler or kernel has already been verified.

## 32. Batched collection and array kernels

### 32.1 Why exact batched accumulation refines individual steps

For a ready group $G$ with all successful values $v_o$, define

$$
\Delta_G(a)=\bigoplus_{o\in G\cap\mathcal{C}_P(a)}v_o.
$$

Enumerate $G$ in any order and apply $\mathrm{CONTRIBUTE}$ once per member.
Every member stays ready because these steps leave $\sigma$ unchanged.
The resulting accumulator is
$\alpha(a)\oplus\Delta_G(a)$, and the remaining set is $U\setminus G$.
Finite associativity and commutativity justify the aggregate update.
This proves the logical success contract without requiring identical
physical reduction order.

A grouped scatter kernel must compute these complete fibers, including
colliding valuations. An overwrite kernel does not satisfy the contract
when a fiber contains multiple contributions.
Likewise, counting only distinct numerical body values is not a substitute
for retaining all occurrence identities.

If a member is undefined, $\Delta_G$ is not defined by inserting zero or
NaN for it. A transactional kernel may report an undefined member before
committing any group contributions: the reference machine can choose that
member first. A kernel that commits a successful prefix before failing must
justify the corresponding reference prefix. In either case failure is
terminal and yields no successful output.

### 32.2 Complete arrays, empty groups, and shared computations

An array kernel must implement Section 18's interpretation, including
complete arguments, primitive domains, and complete-array selection.
In particular, computing only the selected coordinate of

$$
\operatorname{at}\left(
\operatorname{tab}_{j\in[2]}(\log(X[j])),(0)
\right)
$$

is not valid if the other tabulated coordinate has an invalid logarithm,
as in Section 18.5.

For a whole-slice primitive, the logical footprint contains every required
input coordinate. Those published values must have concrete representations
when the kernel reads them. Sharing one evaluation of a deterministic
array primitive among several occurrence bodies is permitted if it preserves
their individual values and definedness and their contribution accounting.

An empty occurrence group evaluates no bodies. A compiler must not invoke
a partial primitive merely because the syntax contains it in a statement
whose occurrence domain is empty.
An actually demanded primitive on an empty array is different: its
$\mathcal{D}_f$ condition still applies, as in Section 25.3.

### 32.3 Publication fusion and interference

An accumulation-and-publication kernel may fuse
$\mathsf{Accumulate}(G)$ and $\mathsf{Publish}(B)$ only when publication's
premises hold after removing $G$ from $U$. It must not expose partial
accumulators through an output view while another contribution remains.

For `Pre[] = A[]; Pre[] = B[]; T[] = relu(Pre[])`, collecting the two
`Pre` occurrences, publishing `Pre`, and then evaluating ReLU can be fused
if those logical barriers are respected internally. Applying ReLU after
just the first contribution changes the program.

Concurrent updates within a kernel need an implementation argument that
they realize the exact aggregate without lost or duplicated contributions.
If a destination aliases a source location, the old source values must
be preserved until every required read finishes. Exact semiring
commutativity alone does not prove either property.

## 33. Scan compilation and buffer reuse

### 33.1 A separate-buffer history plan

Use the finite history of Section 11.4 with total
$F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$.
For each $l\in[N+1]$, let
$B_l=\{(H,(i,l))\mid i\in[d]\}$.
Let $G_l^X$ be the persistent-input occurrences targeting $B_l$,
$G_0^Z$ the base occurrences, and $G_l^F$ for $1\le l\le N$ the
recurrence occurrences reading $H_{l-1}$ and targeting $B_l$.
These are subsets of the already defined $\mathcal{O}_P$.

A simple plan uses a distinct state buffer $\beta_l$ of capacity $d$ for
each time slice, alongside the supplied-input storage:

1. Initialize the physical accumulators for $B_0$ to zero.
2. Accumulate $G_0^X\cup G_0^Z$ and publish $B_0$.
3. For each $l=1,\ldots,N$, initialize $B_l$'s physical accumulators,
   accumulate $G_l^X\cup G_l^F$, and publish $B_l$.

The union in each group is a disjoint union of occurrence subsets.
Each recurrence group reads a complete, earlier published slice.
The certificate $r(H,(i,l))=l+1$ from Section 27.4 applies.
If an explicit `Last` output is included, finish by accumulating its reads
of $H_N$ and publishing `Last`.

Unlike the schedule in Section 27.4, this plan consumes a slice's persistent
input only when constructing that slice. It still accounts for every
occurrence exactly once. It never adds $X$ twice merely because a previous
slice remains stored.

### 33.2 Reusing two state buffers

If $H$ is internal and the designated output is defined by

$$
\operatorname{Last}[i]\mathrel{+}=H[i,N],
\qquad i\in[d],
$$

the plan can use two state buffers of capacity $d$:
one for the published current slice, the other for the next accumulator.
This counts state buffers only; supplied-input storage and any workspace
required by $F$ or its kernels are accounted for separately.

At each step, read the complete current slice, construct the next slice's
contributions in the other buffer, and publish the next slice.
After all recurrence occurrences reading the old slice have been consumed,
that slice has no remaining readers in this program.
It can be retired, and its buffer can be zero-initialized for a later
accumulator. Retirement occurs only after any other declared uses of that
slice have also finished.

The logical $\sigma$ still contains every earlier slice. Only its physical
representation is retired. Future untouched accumulators remain logical
zeros until materialized; this schedule does not pre-accumulate their
persistent-input contributions and then discard them.

For $d=1$, $N=2$, $X[0]=2$, $Z[0]=3$, and $F(h)[0]=2h[0]$, the storage
history can be:

| Completed action | State buffer $\beta_A$ | State buffer $\beta_B$ |
| --- | --- | --- |
| Construct and publish $H_0$ | $H_0=5$, live | Free |
| Construct and publish $H_1$ | Old $H_0$, now retireable | $H_1=12$, live |
| Retire $H_0$; construct and publish $H_2$ | $H_2=26$, live | Old $H_1$, now retireable |
| Retire $H_1$; construct and publish `Last` | $H_2$ can retire after the copy | $\operatorname{Last}=26$, retained output |

Each construction zero-initializes its destination accumulator before
adding the prescribed contributions. Input storage is separate from the
two state buffers in this table.
The final free buffer can hold `Last` while its source slice remains
readable during copying.

Although the slot formerly holding $H_0=5$ later holds $H_2=26$, the proof
history still has distinct logical addresses with values $5$ and $26$.
No remaining kernel is permitted to read the overwritten $H_0$ slot as
though it still represented $H_0$.

### 33.3 Full-history outputs change the retention obligation

If instead $H\in\mathrm{Out}$, every published slice belongs to
$\operatorname{Need}_{\mathrm{pub}}$. The two-buffer plan cannot simply
discard earlier slices and return only $H_N$.

It may still reuse working buffers if each completed slice is first copied
to retained output storage and its published layout view is relocated
there. The copy preserves the reference configuration; the working slot
becomes reusable while the output remains concretely represented.
Under this dense representation profile, retaining the full history uses
$d(N+1)$ scalar output slots, separate from any reusable working buffers.

Thus "two reusable state buffers" is not a claim that an entire requested
history can be returned using only $2d$ stored scalar values.
Output selection is a semantic contract, not an inference from the
compiler's preferred memory layout.

### 33.4 Scan edge cases and snapshots

For $N=0$, construct and publish only the base slice; the recurrence groups
are absent. A `Last` output reads that base slice.
For $d=0$, all slice and `Last` coordinate sets and contribution groups
are empty. Empty outputs keep their declared signatures but require no
slots, and no nonexistent recurrence body invokes $F$.

A partial $F$ uses the same schedule, but its demanded applications may
explicitly fail; totality was assumed above to guarantee success.
Reusing the current-slice buffer in place is not justified merely by a
time rank. A kernel must snapshot all required old values before overwriting
them or prove another read-before-write discipline for that particular $F$.
The two-buffer construction avoids that conflict between current-slice
reads and next-slice writes.

## 34. Refinement boundaries and formalization targets

Parts III-V separate three obligations:

1. **Meaning:** collected equations define models and functional denotation.
2. **Logical execution:** the reference machine collects occurrences and
   publishes completed coordinates.
3. **Compiled realization:** kernels, schedules, and storage represent and
   simulate that reference execution with explicit failure and progress.

This separation prevents a storage convention or an existing mutation
policy from silently defining the language.
Testing final outputs is useful evidence, but does not replace proofs of
occurrence coverage, barriers, domain behavior, and safe reuse.

The compilation-layer proof targets are:

- Typed plan annotations and sound validation of their coverage and order.
- Resource views, concrete states, and the representation relation,
  including empty shapes and untouched zero accumulators.
- Refinement lemmas for individual kernels, block publication, and storage
  operations; composite lemmas for fused commands.
- Preservation of explicit undefinedness when batching or sharing expressions.
- Concrete progress and termination, not just forward simulation.
- Terminal decoding and the compiled-correctness theorem.
- Separate-buffer and two-buffer scan proofs, with full-history and
  terminal-only output contracts tested separately.

These are proposed contracts and proof targets, not kernel-checked results
or claims about current compiler acceptance. Connecting them to Lean requires
choosing a concrete plan representation and kernel fragment and proving that
they satisfy the contracts, including additive contribution semantics.
Machine-number refinement, more permissive aliasing, asynchronous command
execution, and general cyclic solvers require their own explicit extensions.

## 35. Compact notation reference

| Symbol | Meaning |
| --- | --- |
| $[n]$ | Finite ordinal $\{0,\ldots,n-1\}$ |
| $()$ | Empty tuple; the sole rank-zero coordinate |
| $K$ | Scalar carrier |
| $\mathcal{K}$ | Scalar semiring structure |
| $\oplus,\otimes$ | Contribution/reduction combination and multiplication |
| $0_K,1_K$ | Additive and multiplicative identities |
| $a,I_a,n_a$ | Axis, its coordinate range, and extent |
| $\Gamma,\nu$ | Index context and valuation |
| $\operatorname{Val}(\Gamma)$ | All valuations for that context |
| $\Gamma_{\mathrm{all}}$ | All distinct variables of a pure einsum with resolved domains |
| $L,L_r$ | Output and operand index strings |
| $J_L,\pi_L$ | A string's coordinate domain and projection from a global valuation |
| $V_L$ | Canonical pure-einsum result tensor |
| $\operatorname{vars}(\Gamma)$ | Variable-identity set of an index context |
| $\operatorname{FV}(E)$ | Free variables of an expression |
| $E[i:=e]$ | Capture-avoiding index substitution |
| $D^{+j}$ | A valuation domain lifted over a fresh binder |
| $D_s$ | Admissible free-variable valuations for statement $s$ |
| $\Sigma$ | Tensor signature |
| $\mathrm{In},\mathrm{Def},\mathrm{Out}$ | Input, defined, and designated output identifiers |
| $\operatorname{Coord}_{\Sigma}(T)$ | Coordinate domain of tensor $T$ |
| $\rho,\eta$ | Complete tensor environment and input environment |
| $\operatorname{Result}(\tau),\bot$ | Successful typed values or an undefined result |
| $\llbracket E\rrbracket_{\rho,\nu}\downarrow v$ | Expression interpretation is defined with value $v$ |
| $\operatorname{lift}_2$ | Strict lifting of a scalar binary operation to results |
| $\sigma$ | Partial store of available coordinate values |
| $(T,p)$ | Tensor address |
| $\mathcal{B},m_\beta$ | Physical buffer identifiers and their capacities |
| $\operatorname{Slot}_{\mathcal{B}},\xi$ | Physical slot set and a slot $(\beta,k)$ |
| $M$ | Partial exact-value memory on physical slots |
| $\operatorname{Addr}_{\mathrm{In}},\operatorname{Addr}_{\mathrm{Def}}$ | Input and defined address partitions |
| $\operatorname{dst}(o)$ | Destination address of contribution occurrence $o$ |
| $\operatorname{Read}(E,\nu),\operatorname{Read}(o)$ | Read footprints of an expression instance and an occurrence |
| $\operatorname{Dep}(a),r$ | Coordinate dependency set and strictly increasing dependency rank |
| $\sigma\sqsubseteq\rho$ | The complete environment agrees with every published store value |
| $\operatorname{Eval}_{\sigma}(E,\nu)$ | Expression result from an available footprint, independent of complete extension |
| $\alpha,U$ | Defined-coordinate accumulators and pending occurrence set |
| $\operatorname{Init}(P,\eta)$ | Initial store, zero accumulators, and all pending occurrences |
| $\mathsf{Failed}(o,\sigma,\alpha,U)$ | Terminal undefined-contribution error with its occurrence and state |
| $\rho_\sigma$ | Complete environment reconstructed from a complete store |
| $\mu$ | Number of pending occurrences plus unpublished defined coordinates |
| $\Pi,\kappa_t$ | Execution plan and a kernel command with logical annotations |
| $\mathsf{Accumulate}(G),\mathsf{Publish}(B),\mathsf{Storage}(\theta)$ | Batched contribution, block publication, and representation-only action contracts |
| $\mathsf{C},\mathsf{pc},\chi$ | Concrete state, command position, and plan control/layout metadata |
| $\mathsf{pub}(a),\mathsf{acc}(a)$ | Published-value and unpublished-accumulator resource identities |
| $\lambda_{\mathsf{C}}$ | Partial resource-to-slot layout view |
| $\operatorname{Addr}_{\mathrm{Out}}$ | All declared output coordinates |
| $\operatorname{Need}_{\mathrm{pub}}(\sigma,U)$ | Published coordinates required by remaining contributions or outputs |
| $\mathcal{R}_\Pi$ | Concrete/reference representation relation |
| $\operatorname{Start}_\Pi,\operatorname{Decode}_\Pi$ | Concrete initialization and whole-output decoding |
| $P\vdash\Pi\ \mathsf{valid}$ | Certified schedule, representation, and kernel validity |
| $\longrightarrow_\Pi,\Downarrow_\Pi$ | Concrete plan-step and decoded successful-execution relations |
| $\mathsf{PlanFailed}(o)$ | Terminal concrete failure matched to an undefined source occurrence |
| $\zeta$ | Decoded output environment |
| $\Delta_G$ | Exact fiber aggregate for a successful ready occurrence group |
| $\phi_s$ | Statement's write map |
| $E_s$ | Statement's contribution expression |
| $(s,\nu)$ | Tagged contribution occurrence |
| $\mathcal{O}_P$ | All contribution occurrences of program $P$ |
| $\mathcal{C}_P(T,p)$ | Occurrences addressing coordinate $p$ of $T$ |
| $\operatorname{AdmEnv}(P)$ | Complete environments on which all actual contributions are defined |
| $V_s^\rho$ | Contribution tensor of statement $s$ in environment $\rho$ |
| $\operatorname{Collect}_P(\rho)$ | Values collected for all defined tensors |
| $\Phi_P$ | Partial equation operator preserving inputs and collecting defined tensors |
| $\operatorname{Input}_{\Sigma},\operatorname{Output}_{\Sigma}$ | Value environments on the program's designated input and output identifiers |
| $\operatorname{AdmInput}(P)$ | Well-typed inputs admitting exactly one complete model |
| $\mathbf{1}_{Q}$ | Iverson value of predicate $Q$ |
| $\delta_J$ | Equality-indicator tensor on $J\times J$ |
| $\mathbf{1}_J$ | All-ones tensor on coordinate domain $J$ |
| $\tau,\mathcal{F}$ | Expression value type and primitive registry |
| $\mathcal{D}_f$ | Domain of definition of primitive $f$ |
| $\operatorname{tab},\operatorname{at}$ | Array construction and scalar coordinate selection |
| $C_b,B_s$ | Contracted variables of a surface term and elaborated additive body |
| $\Sigma;\Gamma;D\vdash E:\tau$ | Structural expression judgment under a signature, index context, and admissible valuation domain |
| $H_l$ | Logical history slice $H[:,l]$ |
| $\llbracket\cdot\rrbracket$ | Interpretation brackets, with parameters as specified |
| $\operatorname{Models}(P,\eta)$ | Complete environments satisfying the collected equations on inputs $\eta$ |
| $\mathsf{Conf},\longrightarrow,\Downarrow$ | Machine configuration, execution-step relation, and successful termination |

## References and related documents

- Pedro Domingos, [*Tensor Logic: The Language of AI*](https://arxiv.org/html/2510.12269v3).
  Its additive convention motivates this specification; the definitions and
  implementation correspondence here must be stated independently.
- [*The Syntax and Semantics of einsum*](https://arxiv.org/html/2509.20020).
  Sections 3-4 provide the pure-einsum syntax and global-position semantics;
  Sections 5-7 supply algebraic, nesting, delta, and neutral-operand results.
  Section 17 adapts the relevant foundations to this document's conventions.
- [Tensor logic and einsum](einsum_tensor_logic.md).
- [Integer constants and affine index arithmetic](index_arithmetic.md).
- [Iteration in tensor logic](iteration.md).

Related repository documents describe existing designs or implementations.
They are context, not substitutes for the definitions in this specification.
