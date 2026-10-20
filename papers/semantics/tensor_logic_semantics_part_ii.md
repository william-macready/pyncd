# Tensor Logic semantics - Part II: Core language and surface elaboration

[Previous: Part I: Background notation](tensor_logic_semantics_part_i.md) | [Contents](README.md) | [Next: Part III: Denotational semantics](tensor_logic_semantics_part_iii.md)

## In this part

- [Part II: Core language and surface elaboration](#part-ii-core-language-and-surface-elaboration)
- [13. Core syntax and binding](#13-core-syntax-and-binding)
  - [13.1 Index expressions and predicates](#131-index-expressions-and-predicates)
  - [13.2 Value types and primitive signatures](#132-value-types-and-primitive-signatures)
  - [13.3 Expression constructors](#133-expression-constructors)
  - [13.4 Scope, freshness, and substitution](#134-scope-freshness-and-substitution)
  - [13.5 Core contribution statements](#135-core-contribution-statements)
  - [13.6 Core programs](#136-core-programs)
- [14. Structural well-formedness](#14-structural-well-formedness)
  - [14.1 Judgments and admissible valuations](#141-judgments-and-admissible-valuations)
  - [14.2 Index and expression rules](#142-index-and-expression-rules)
  - [14.3 Statement and program rules](#143-statement-and-program-rules)
  - [14.4 Mathematical conditions versus compiler decisions](#144-mathematical-conditions-versus-compiler-decisions)
- [15. Surface-to-core elaboration](#15-surface-to-core-elaboration)
  - [15.1 Explicit inputs to elaboration](#151-explicit-inputs-to-elaboration)
  - [15.2 Statement variables and term-local contraction](#152-statement-variables-and-term-local-contraction)
  - [15.3 Scalar operator placement](#153-scalar-operator-placement)
  - [15.4 Marked slice operators](#154-marked-slice-operators)
  - [15.5 Structural checks after elaboration](#155-structural-checks-after-elaboration)
- [16. Worked core elaborations](#16-worked-core-elaborations)
  - [16.1 Matrix multiplication and a bias](#161-matrix-multiplication-and-a-bias)
  - [16.2 Diagonal reads and writes](#162-diagonal-reads-and-writes)
  - [16.3 Colliding writes and lost-binder prevention](#163-colliding-writes-and-lost-binder-prevention)
  - [16.4 A strided convolution and an in-bounds guard](#164-a-strided-convolution-and-an-in-bounds-guard)
  - [16.5 Softmax over an attention slice](#165-softmax-over-an-attention-slice)
  - [16.6 A scan history with explicit slice input](#166-a-scan-history-with-explicit-slice-input)
  - [16.7 A causal mask is not a marked slice](#167-a-causal-mask-is-not-a-marked-slice)
- [17. Pure einsum semantics and transformation foundations](#17-pure-einsum-semantics-and-transformation-foundations)
  - [17.1 Index strings and global valuations](#171-index-strings-and-global-valuations)
  - [17.2 Canonical fiber semantics](#172-canonical-fiber-semantics)
  - [17.3 Connection to the contribution core](#173-connection-to-the-contribution-core)
  - [17.4 Delta tensors and diagonal identities](#174-delta-tensors-and-diagonal-identities)
  - [17.5 Conditions for semantic transformations](#175-conditions-for-semantic-transformations)
  - [17.6 Neutral operands and domain preservation](#176-neutral-operands-and-domain-preservation)

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

```math
\textcolor{#9D75C4}{e} ::= b \mid i \mid \textcolor{#9D75C4}{e}+\textcolor{#9D75C4}{e} \mid c\,\textcolor{#9D75C4}{e},
\qquad b,c\in\mathbb{Z}.
```

Here $i$ is an index variable from a context $\textcolor{#5688C7}{\Gamma}$, not a tensor value.
Subtraction is expressed using coefficient $-1$.
Scalar arithmetic in an expression is distinct from integer index arithmetic.

The index predicates used for guards and Iverson values are:

```math
\textcolor{#9D75C4}{Q} ::= \mathrm{true}\mid\mathrm{false}
\mid \textcolor{#9D75C4}{e}=\textcolor{#9D75C4}{e}\mid \textcolor{#9D75C4}{e}<\textcolor{#9D75C4}{e}
\mid \neg \textcolor{#9D75C4}{Q}\mid \textcolor{#9D75C4}{Q}\land \textcolor{#9D75C4}{Q}\mid \textcolor{#9D75C4}{Q}\lor \textcolor{#9D75C4}{Q}.
```

The usual comparisons such as $\textcolor{#9D75C4}{e}\le \textcolor{#9D75C4}{e}'$ are abbreviations. Predicates depend
only on index valuations, not on tensor values. This makes a statement's
contribution domain determinable without executing its body.

Write $\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{Q}\mathclose{]\!]}_{\textcolor{#5688C7}{\nu}}\in\mathbb{B}$ for predicate evaluation
using integer comparisons and Boolean connectives.
This Boolean result is distinct from its scalar embedding
$\mathbf{1}_{\textcolor{#9D75C4}{Q}}\in K$.

**Example.** The guard $i+1<4$ selects the valuations $i=0,1,2$ from
$i\in[4]$. It creates no occurrence for $i=3$.
Multiplication by $\mathbf{1}_{i+1<4}$ instead retains that occurrence
and changes its body value; it does not automatically suppress invalid reads.

### 13.2 Value types and primitive signatures

An expression has a value type $\textcolor{#5688C7}{\tau}$, which is either:

- The scalar type $K$.
- An array type $K^{\textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m}$, with $m\ge1$.

Each array slot has a specified finite coordinate domain, just as for a
tensor signature in [Section 4](tensor_logic_semantics_part_i.md#4-tensor-signatures-coordinates-and-values). Rank-zero values use the scalar type $K$.
Arrays here are expression values, not necessarily named tensors.

A fixed primitive registry $\textcolor{#9D75C4}{\mathcal{F}}$ supplies, for every operator $f$,
an arity $q$, input types $\textcolor{#5688C7}{\tau}_1,\ldots,\textcolor{#5688C7}{\tau}_q$, an output type $\textcolor{#5688C7}{\tau}$,
and a domain

```math
\textcolor{#398B83}{\mathcal{D}}_f\subseteq\textcolor{#5688C7}{\tau}_1\times\cdots\times\textcolor{#5688C7}{\tau}_q.
```

The types in this formula denote their value spaces. This specializes the
operator-domain notation from [Section 8](tensor_logic_semantics_part_i.md#8-operators-predicates-and-definedness).
Primitive interpretations are deterministic mathematical functions of
their arguments on $\textcolor{#398B83}{\mathcal{D}}_f$. They have no hidden store reads or side
effects. Computable implementations and domain tests are separate requirements.

For example, real ReLU has one scalar argument and result. Softmax is
registered for every $m\ge0$, with one argument and result of type
$\mathbb{R}^{[m]}$. Its domain of definition is all of $\mathbb{R}^{[m]}$
when $m>0$ and is empty when $m=0$, matching the nonempty requirement of
[Section 8](tensor_logic_semantics_part_i.md#8-operators-predicates-and-definedness). Because softmax is registered at $m=0$, a statement whose slice
domain is empty type checks; having no occurrences, it never demands the
application. A demanded application to an empty array is undefined.
A user-supplied $F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$ can be a registered
array operator, with its domain specified in the same way.

There is no implicit application of an array operator coordinate by
coordinate, and no implicit distribution of any operator over $\oplus$.

### 13.3 Expression constructors

The core expression constructors are:

| Constructor | Meaning and binding |
| --- | --- |
| $c_K$ | A scalar literal belonging to $K$ |
| $T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k]$ | A scalar read from a named tensor |
| $\mathbf{1}_{\textcolor{#9D75C4}{Q}}$ | Scalar embedding of an index predicate |
| $\textcolor{#9D75C4}{E}_1\oplus \textcolor{#9D75C4}{E}_2$ | Combination of two scalar expressions |
| $\textcolor{#9D75C4}{E}_1\otimes \textcolor{#9D75C4}{E}_2$ | Multiplication of two scalar expressions |
| $\bigoplus_{j\in \textcolor{#5688C7}{I}_j}\textcolor{#9D75C4}{E}$ | Scalar reduction; binds $j$ in $\textcolor{#9D75C4}{E}$ |
| $\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j_1\in \textcolor{#5688C7}{I}_1,\ldots,j_m\in \textcolor{#5688C7}{I}_m}(\textcolor{#9D75C4}{E})$ | Array construction; binds all $j_1,\ldots,j_m$ in a scalar body |
| $\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#9D75C4}{E},(\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_m))$ | Selects a scalar coordinate from an array expression |
| $f(\textcolor{#9D75C4}{E}_1,\ldots,\textcolor{#9D75C4}{E}_q)$ | Applies a primitive with its declared input and output types |

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

```math
\textcolor{#398B83}{V}=\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[3]}(X[j]+1)
```

constructs all three entries: $\textcolor{#398B83}{V}[0]=3$, $\textcolor{#398B83}{V}[1]=6$, and $\textcolor{#398B83}{V}[2]=8$.
The bound variable $j$ visits each coordinate; it is not summed out.
Selection then gives

```math
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#398B83}{V},(1))=6.
```

Here $(1)$ is the one-coordinate tuple for a vector, and $\textcolor{#398B83}{V}$ is an expository
name for the resulting value, not an additional core binding construct.
Thus `tab` constructs an array from a scalar body, whereas `at` reads
one scalar from that array.

**Example: a history slice.**

```math
\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[d]}(H[j,l])
```

is an array expression of type $K^{[d]}$, with $l$ free and $j$ bound.
It makes the shorthand $H[:,l]$ from [Part I](tensor_logic_semantics_part_i.md#part-i-background-notation) explicit.

**Example: a scalar selected from an array computation.**

```math
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
F\left(\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[d]}(H[j,l])\right),(i)
\right)
```

is the core form of $F(H[:,l])[i]$.

**Example: pointwise addition of two matrices.** There is no dedicated
constructor; pointwise array addition is tabulated scalar addition. Let $A$ and
$B$ be tensors of shape $(m,n)$. As an array value,

```math
\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{i\in[m],\,j\in[n]}\left(A[i,j]\oplus B[i,j]\right)
```

has type $K^{[m]\times[n]}$. The bound variables $i$ and $j$ visit every
coordinate; they are not summed out. Selection gives
$\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{i\in[m],\,j\in[n]}(A[i,j]\oplus B[i,j]),(0,1))=A[0,1]\oplus B[0,1]$,
and if $m=0$ or $n=0$ the result is the unique empty array. Every read is in
bounds because the binders range over the declared extents. A bare tabulation
cannot be a statement body, since a body must have scalar type
([Section 13.5](#135-core-contribution-statements)), but it can be the argument
of a registered array primitive.

To define a tensor $C$ of the same shape, use one core statement per
coordinate:

```math
\text{for }i\in[m],\,j\in[n]:
\quad
C[i,j]\textcolor{#9D75C4}{\mathrel{+}=}A[i,j]\oplus B[i,j].
```

In surface notation this is `C[i,j] = A[i,j] + B[i,j]`. It has two additive
terms and no contracted variable, so
[Section 15.2](#152-statement-variables-and-term-local-contraction) elaborates
it to exactly this statement, with one occurrence for each $(i,j)$.

### 13.4 Scope, freshness, and substitution

All bound variables have identities distinct from the variables already
in scope. Printed names can be changed consistently to satisfy this
freshness convention.

For an expression $\textcolor{#9D75C4}{E}$, $\textcolor{#9D75C4}{\mathop{\mathrm{FV}}\nolimits}(\textcolor{#9D75C4}{E})$ denotes its free variables.
For example,

```math
\textcolor{#9D75C4}{\mathop{\mathrm{FV}}\nolimits}\left(\bigoplus_{k\in \textcolor{#5688C7}{I}_k}W[i,k]\otimes X[k,j]\right)
=\{i,j\}.
```

The corresponding notation applies to index expressions and predicates.
For multiple expressions, take the union of their free-variable sets.

$\textcolor{#9D75C4}{E}[i:=\textcolor{#9D75C4}{e}]$ denotes capture-avoiding substitution of index expression $\textcolor{#9D75C4}{e}$
for the free occurrences of $i$. Bound variables are renamed when needed
to prevent capture. This syntactic substitution is distinct from the
valuation update $\textcolor{#5688C7}{\nu}[i\mapsto k]$.

**Example.** In

```math
\textcolor{#9D75C4}{E}(i)=\bigoplus_{k\in[k_0]}W[i,k]\otimes X[k],
```

the substitution $\textcolor{#9D75C4}{E}[i:=k]$ first renames the bound reduction variable,
giving, for a fresh $h$,

```math
\bigoplus_{h\in[k_0]}W[k,h]\otimes X[h].
```

The replacement's $k$ stays free.

### 13.5 Core contribution statements

A core statement with occurrence identifier $\textcolor{#9D75C4}{s}$ has the form

```math
\text{for }\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}\text{ where }\textcolor{#9D75C4}{Q}_{\textcolor{#9D75C4}{s}}:
\qquad
T_{\textcolor{#9D75C4}{s}}[\textcolor{#9D75C4}{e}_{\textcolor{#9D75C4}{s},1},\ldots,\textcolor{#9D75C4}{e}_{\textcolor{#9D75C4}{s},k_{\textcolor{#9D75C4}{s}}}]\textcolor{#9D75C4}{\mathrel{+}=}\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}.
```

$\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$ binds the statement's contribution variables in its guard,
output indices, and body. The body must have the scalar type of its
destination tensor ($K$ when there is one sort).
The guard is optional, with omitted guard meaning $\mathrm{true}$.

The guard and output indices determine the data introduced in [Section 9](tensor_logic_semantics_part_i.md#9-programs-and-contribution-occurrences):

```math
\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}=\{\textcolor{#5688C7}{\nu}\in\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}})
       \mid\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{Q}_{\textcolor{#9D75C4}{s}}\mathclose{]\!]}_{\textcolor{#5688C7}{\nu}}=\mathrm{true}\},
```

```math
\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})=
(\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}_{\textcolor{#9D75C4}{s},1}\mathclose{]\!]}_{\textcolor{#5688C7}{\nu}},\ldots,
 \textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}_{\textcolor{#9D75C4}{s},k_{\textcolor{#9D75C4}{s}}}\mathclose{]\!]}_{\textcolor{#5688C7}{\nu}}).
```

The binders are part of the statement's identity as a contribution
generator. They are not discarded when an output index simplifies.
For instance, with $i\in[3]$, the statement

```math
T[0i]\textcolor{#9D75C4}{\mathrel{+}=}1_K
```

has three occurrences addressed to coordinate $0$, not one.

### 13.6 Core programs

A core program consists of:

1. A finite signature $\textcolor{#5688C7}{\Sigma}$, over the scalar carrier $K$ (or the
   sort family of [Section 2.4](tensor_logic_semantics_part_i.md#24-scalar-sorts)).
2. A partition of its tensor identifiers into designated inputs
   $\textcolor{#5688C7}{\mathrm{In}}$ and defined tensors $\textcolor{#5688C7}{\mathrm{Def}}$.
3. Designated output identifiers $\textcolor{#5688C7}{\mathrm{Out}}\subseteq\textcolor{#5688C7}{\mathrm{Def}}$.
4. A finite sequence of core statements with distinct occurrence identifiers.

These named identifier sets are finite; $\textcolor{#5688C7}{\mathrm{In}}$ and $\textcolor{#5688C7}{\mathrm{Def}}$
are disjoint and their union is exactly the identifier domain of $\textcolor{#5688C7}{\Sigma}$.
Every statement targets an identifier in $\textcolor{#5688C7}{\mathrm{Def}}$.
Reads may refer to either set.

A defined tensor need not have any statements targeting it. Its values
are governed by the empty-collection rule in [Section 19](tensor_logic_semantics_part_iii.md#19-contribution-collection).
Conversely, declaring a tensor to be an input does not
provide its values: an input environment $\textcolor{#398B83}{\eta}$ must supply them.

**Remark (current production pipeline).** The production source language
does not declare $\mathrm{In}$ and $\mathrm{Def}$. It derives a name as a defined
tensor when some statement writes it and as an input when it is only read.
A defined tensor without statements, and a designated input that no statement
reads, are therefore not realized there (see the
[semantic gap audit](tensor_logic_semantic_gap_audit.md), F03 and W07). A supplied
input that names a defined tensor violates the disjointness of
$\mathrm{In}$ and $\mathrm{Def}$ and must be rejected; both backends reject such an
input at run time (`EvalError.inputIsDefined` on the reference evaluator,
`InputBindingError.inputIsDefined` on the plan path). See the
[decision note](additive_production_decision_note.md), Section B.

Designated outputs specify whole tensor values with their declared coordinate
domains. If $H$ is a history tensor and $H\in\textcolor{#5688C7}{\mathrm{Out}}$, the output includes
every time slice, not just its last slice. Returning only the final state
requires a separately declared output, for example a tensor `Last` defined
by `Last[i] = H[i,N]`. This distinction also determines which values a
compiled execution must retain for output decoding.

## 14. Structural well-formedness

### 14.1 Judgments and admissible valuations

Use the judgments

```math
\textcolor{#5688C7}{\Gamma}\vdash \textcolor{#9D75C4}{e}:\mathbb{Z},
\qquad
\textcolor{#5688C7}{\Gamma}\vdash \textcolor{#9D75C4}{Q}:\mathrm{pred},
\qquad
\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma};\textcolor{#5688C7}{D}\vdash \textcolor{#9D75C4}{E}:\textcolor{#5688C7}{\tau},
```

where $\textcolor{#5688C7}{D}\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma})$.
The marker $\mathrm{pred}$ classifies index predicates; it is not a scalar
type. The primitive registry and scalar algebra are fixed parameters.

The expression judgment establishes binding, value types, and
in-bounds index use for valuations in $\textcolor{#5688C7}{D}$.
It does **not** assert that value-dependent primitive domains are met.
In particular, $\log(T[i])$ can have scalar type while still requiring
positive tensor values for its interpretation to be defined.

For a fresh $j:\textcolor{#5688C7}{I}_j$, define the lifted valuation domain

```math
\textcolor{#5688C7}{D}^{+j}
=
\{\textcolor{#5688C7}{\nu}[j\mapsto k]\mid\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D},\ k\in \textcolor{#5688C7}{I}_j\}
\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma},j:\textcolor{#5688C7}{I}_j).
```

For several fresh variables, lift successively. This accounts for every
coordinate evaluated inside a reduction or tabulation.

**Example: a guarded row sum.** Work over $K=\mathbb{R}$, with
$\textcolor{#5688C7}{\Sigma}(X)=([4],[2];\mathbb{R})$ and $\textcolor{#5688C7}{\Gamma}=(i:[4])$.
Choose the index expression $\textcolor{#9D75C4}{e}=i+1$ and predicate $\textcolor{#9D75C4}{Q}=(i+1<4)$.
The first two judgments are

```math
\textcolor{#5688C7}{\Gamma}\vdash i+1:\mathbb{Z},
\qquad
\textcolor{#5688C7}{\Gamma}\vdash i+1<4:\mathrm{pred}.
```

The admissible valuations are

```math
\textcolor{#5688C7}{D}=\{\{i\mapsto0\},\{i\mapsto1\},\{i\mapsto2\}\}.
```

Introduce a fresh reduction variable $j\in[2]$. Lifting gives

```math
\textcolor{#5688C7}{D}^{+j}
=
\{\{i\mapsto a,j\mapsto b\}\mid a\in[3],\ b\in[2]\}.
```

This domain contains six valuations. Every one makes the read
$X[i+1,j]$ valid: its row is $1$, $2$, or $3$, and its column is
$0$ or $1$. For instance, $\{i\mapsto2,j\mapsto1\}$ reads $X[3,1]$.
Consequently, the body and reduction judgments are

```math
\textcolor{#5688C7}{\Sigma};(\textcolor{#5688C7}{\Gamma},j:[2]);\textcolor{#5688C7}{D}^{+j}\vdash X[i+1,j]:\mathbb{R},
```

```math
\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma};\textcolor{#5688C7}{D}\vdash
\bigoplus_{j\in[2]}X[i+1,j]:\mathbb{R}.
```

The result is a scalar row sum for each admissible $i$, not an array.
If $\textcolor{#5688C7}{D}$ instead included $\{i\mapsto3\}$, the body would try to read
row $4$, so the in-bounds expression judgment would fail even though
$i+1$ remains a well-scoped integer expression.

### 14.2 Index and expression rules

Index literals are integers, variables must belong to $\textcolor{#5688C7}{\Gamma}$, and
affine constructors preserve the integer index type.
Predicates are built from well-scoped index expressions using the
constructors in [Section 13.1](#131-index-expressions-and-predicates).

The expression rules are:

| Constructor | Required premises and result |
| --- | --- |
| $c_K$ | $c_K\in K$; result $K$ |
| $T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k]$ | $T$ is declared, rank is $k$, indices are well-scoped, and their tuple belongs to $\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)$ for every $\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}$; result $K$ |
| $\mathbf{1}_{\textcolor{#9D75C4}{Q}}$ | $\textcolor{#5688C7}{\Gamma}\vdash \textcolor{#9D75C4}{Q}:\mathrm{pred}$; result $K$ |
| $\textcolor{#9D75C4}{E}_1\oplus \textcolor{#9D75C4}{E}_2$, $\textcolor{#9D75C4}{E}_1\otimes \textcolor{#9D75C4}{E}_2$ | Both operands have type $K$ under the same $\textcolor{#5688C7}{\Sigma},\textcolor{#5688C7}{\Gamma},\textcolor{#5688C7}{D}$; result $K$ |
| $\bigoplus_{j\in \textcolor{#5688C7}{I}_j}\textcolor{#9D75C4}{E}$ | The body has type $K$ under $\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma},j:\textcolor{#5688C7}{I}_j;\textcolor{#5688C7}{D}^{+j}$; result $K$ |
| $\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j_1\in \textcolor{#5688C7}{I}_1,\ldots,j_m\in \textcolor{#5688C7}{I}_m}(\textcolor{#9D75C4}{E})$ | The body has type $K$ under the extended context and lifted domain; result $K^{\textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m}$ |
| $\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#9D75C4}{E},(\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_m))$ | $\textcolor{#9D75C4}{E}$ has the matching array type, the indices are well-scoped, and the selected tuple is in its coordinate domain for every $\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}$; result $K$ |
| $f(\textcolor{#9D75C4}{E}_1,\ldots,\textcolor{#9D75C4}{E}_q)$ | Each operand has the corresponding type from $\textcolor{#9D75C4}{\mathcal{F}}$ under the same $\textcolor{#5688C7}{\Sigma},\textcolor{#5688C7}{\Gamma},\textcolor{#5688C7}{D}$; result is the declared output type |

Tabulation and reduction lift $\textcolor{#5688C7}{D}$ over the whole declared binder domain,
not just over coordinates occurring in some other statement.
Arrays are complete on their own declared domains, not sparse collections
of available entries. An explicitly restricted tabulation can still
construct a complete array on a prefix of a named tensor's domain.

These rules use compatible declared coordinate domains, not name-based
axis matching or an implicit transpose. An implementation mapping must
retain any axis identities and explicitly justified identifications.
Because $\textcolor{#5688C7}{I}_a=[n_a]$ is a set of integers ([Section 3.1](tensor_logic_semantics_part_i.md#31-axes-and-identities)), these
judgments see only coordinate ranges: two axes of equal extent are
indistinguishable to them. Distinguishing such axes is the job of domain
resolution (assumed before elaboration in [Section 15.1](#151-explicit-inputs-to-elaboration)) and the
implementation mapping, not of the core rules.

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

1. Its destination belongs to $\textcolor{#5688C7}{\mathrm{Def}}$.
2. Its guard and output indices are well-scoped under $\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$.
3. Its output arity matches the destination rank.
4. $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})\in\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T_{\textcolor{#9D75C4}{s}})$ for every $\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$.
5. $\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}};\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}\vdash \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}:K$.

A program is structurally well-formed when its declarations, role
partition, output identifiers, occurrence identifiers, and every
statement satisfy their respective conditions.

Neither injectivity of $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}$ nor disjointness of different statements'
write images is required. Additive overlap is allowed.
No condition here requires an acyclic dependency graph.

Condition 4 applies to writes as well as reads. A write whose destination lies
outside the declared shape is not a dropped contribution but an ill-formed
statement, and a production profile must reject it rather than skip it. A
policy that drops such writes is a separate, explicit extension (see the
[boundary-policy note](tensor_logic_boundary_policies.md), Section 8.4.4); it
needs the occurrence demands of its drop timing and is not part of this core.

### 14.4 Mathematical conditions versus compiler decisions

The quantified in-bounds premises specify a mathematical property.
They do not require a particular compiler to decide every such property
automatically. A compiler may prove admitted affine cases, accept explicit
evidence, or reject a case it cannot establish.

Operator definedness is a different condition. The interpretation in
[Section 18](tensor_logic_semantics_part_iii.md#18-expression-interpretation-and-definedness) accounts for $\textcolor{#398B83}{\mathcal{D}}_f$ (where $f$ is the primitive
operator and $\textcolor{#398B83}{\mathcal{D}}_f$ is its domain of definition), distinguishing
defined values from undefined results. [Section 20](tensor_logic_semantics_part_iii.md#20-program-models-and-functional-denotation) then specifies
admissible inputs for a functional program denotation.
A runtime check is not a proof that every input meets that condition.

**Guard example.** Let $X$ have shape $(4)$ and $i\in[4]$:

```math
\text{for }i\in[4]\text{ where }i+1<4:
\qquad Y[i]\textcolor{#9D75C4}{\mathrel{+}=}X[i+1].
```

The guard makes the read in bounds throughout $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$.
Replacing it by the body
$\mathbf{1}_{i+1<4}X[i+1]$ without a guard does not satisfy the read
rule at $i=3$.

## 15. Surface-to-core elaboration

**Surface notation** is the compact, user-facing syntax in which tensor
logic programs are written, such as `Y[i,j] = W[i,k] X[k,j]`.
It leaves some information implicit, including the contraction over $k$.
The **core notation** from [Section 13](#13-core-syntax-and-binding) makes binders, reductions, and
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
still specify the prefix computation described in [Section 14.2](#142-index-and-expression-rules).
Broadcasting an output-only variable from a declared domain is also a
core/general surface capability, not a standard pure-einsum inference.
[Section 17](#17-pure-einsum-semantics-and-transformation-foundations) gives the reference semantics for the standard profile.

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
$\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in \textcolor{#5688C7}{I}_{T,1}}(T[j,l])$ for a fresh $j$;
the corresponding rule for several colon slots tabulates their declared
domains in slot order. Selection from an array expression, such as
$F(T[:,l])[i]$, expands to $\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}$ as in [Section 13.3](#133-expression-constructors).
The fixed indices must remain well-scoped and in bounds.

### 15.2 Statement variables and term-local contraction

The contribution-variable context $\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$ contains the variables
occurring in the output index expressions. Domains are resolved as above.
They are collected before algebraically simplifying those expressions,
so cancellation of coefficients does not remove contribution binders.

For this surface fragment, guard variables must also belong to
$\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$. A more general core statement can explicitly bind additional
contribution variables.

Write the surface additive body as a finite list of product terms
$t_1,\ldots,t_h$. For term $t_b$, define its contracted-variable set

```math
C_b=\textcolor{#9D75C4}{\mathop{\mathrm{FV}}\nolimits}(t_b)\setminus\textcolor{#5688C7}{\mathop{\mathrm{vars}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}),
```

where $\textcolor{#5688C7}{\mathop{\mathrm{vars}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}})$ is the context's variable-identity set
from [Section 3.2](tensor_logic_semantics_part_i.md#32-index-variables-and-contexts). Each contracted variable has its own resolved
domain.

Elaborate the factors to scalar core expressions, multiply them with
$\otimes$, and bind the variables in $C_b$ using nested $\bigoplus$
reductions. A repeated variable in several factors is bound once and
has the same value in each occurrence.

Use a fixed enumeration of $C_b$ to produce a concrete syntax tree.
The commutative-monoid laws of $\oplus$, with the coherence condition of
[Section 2.3](tensor_logic_semantics_part_i.md#23-which-algebraic-laws-each-part-uses), justify independence from that enumeration; floating-point
execution must separately specify its order.
Each reduction binder is scoped only over its own term.

Let $B_{\textcolor{#9D75C4}{s}}$ denote the core body obtained by combining the elaborated terms
with $\oplus$. An empty product uses $1_K$, and an empty list of terms
uses $0_K$.

This rule gives

```math
W[i,k]X[k]+B[i]
\quad\mapsto\quad
\left(\bigoplus_{k\in \textcolor{#5688C7}{I}_k}W[i,k]\otimes X[k]\right)\oplus B[i].
```

It does not give
$\bigoplus_{k\in \textcolor{#5688C7}{I}_k}(W[i,k]\otimes X[k]\oplus B[i])$.

**Example: two nested contractions.** Consider the surface statement

```text
Y[i] = A[i,j] B[j,k] X[k]
```

Its contribution context contains only the output variable $i$. Before
elaboration, the product term $t_1=A[i,j]B[j,k]X[k]$ has no reduction binders,
so all three index variables are syntactically free:

```math
\textcolor{#9D75C4}{\mathop{\mathrm{FV}}\nolimits}(t_1)=\{i,j,k\},
\qquad
\textcolor{#5688C7}{\mathop{\mathrm{vars}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}})=\{i\},
\qquad
C_1=\{i,j,k\}\setminus\{i\}=\{j,k\}.
```

Choosing $j$ as the outer binder and $k$ as the inner binder gives the
elaborated contribution body

```math
\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}(i)=
\bigoplus_{j\in \textcolor{#5688C7}{I}_j}
\left(
\bigoplus_{k\in \textcolor{#5688C7}{I}_k}
\left(A[i,j]\otimes B[j,k]\otimes X[k]\right)
\right).
```

The inner reduction holds $i,j$ fixed and combines the values over $k$;
the outer reduction then combines those results over $j$. Each repeated
variable is bound once. After elaboration, $j,k$ are bound and
$\textcolor{#9D75C4}{\mathop{\mathrm{FV}}\nolimits}(\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}})=\{i\}$:
the contractions occur inside one contribution body for each admissible $i$.

### 15.3 Scalar operator placement

Without an enclosing operator, the contribution body is $\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}=B_{\textcolor{#9D75C4}{s}}$.
With a registered unary scalar operator $f$, it is

```math
\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}=f(B_{\textcolor{#9D75C4}{s}}).
```

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
Their resolved domains are $\textcolor{#5688C7}{I}_1,\ldots,\textcolor{#5688C7}{I}_m$.
The statement guard must be independent of these marked variables.
This defines a rectangular slice over the full product of the marked
variables' domains for each valuation of the other contribution variables.

The enclosing operator $f$ must have the array signature

```math
f:K^{\textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m}\to
  K^{\textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m}
```

with its own specified domain $\textcolor{#398B83}{\mathcal{D}}_f$.

Choose fresh variables $h_1,\ldots,h_m$ with those domains. The scalar
contribution body at the original output coordinates is

```math
\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}=
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
f\left(
\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{h_1\in \textcolor{#5688C7}{I}_1,\ldots,h_m\in \textcolor{#5688C7}{I}_m}
\left(B_{\textcolor{#9D75C4}{s}}[j_1:=h_1,\ldots,j_m:=h_m]\right)
\right),
(j_1,\ldots,j_m)
\right).
```

The simultaneous substitution affects free occurrences only.
Marked variables remain contribution variables, not contracted variables.
The fresh tabulation binders supply the entire slice to the operator.

This applies an operator to one statement's body slice.
It does not first collect slices from other statements defining the
same destination. To apply softmax or another operator to a collected
tensor, use a separate named intermediate, as in [Section 11.3](tensor_logic_semantics_part_i.md#113-activation-before-versus-after-collection).

Nonrectangular slices, guards depending on marked slice variables, and other
operator shapes require explicit core expressions or an explicit surface-language
extension. They are not assigned an implicit meaning by this abbreviation.
A causal mask is such a guard; [Section 16.7](#167-a-causal-mask-is-not-a-marked-slice) gives its core forms.

### 15.5 Structural checks after elaboration

Derive $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$ and $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}$ from the resulting statement and check the
rules in [Section 14](#14-structural-well-formedness). Elaboration preserves every source statement
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

```math
\text{for }i\in[i_0],j\in[j_0]:
\quad
Y[i,j]\textcolor{#9D75C4}{\mathrel{+}=}
\bigoplus_{k\in[k_0]}W[i,k]\otimes X[k,j].
```

For a separate vector-input bias example, retain $W$'s shape, take input
$X$ of shape $(k_0)$ and input $B$ of shape $(i_0)$, and define $Y$ on
shape $(i_0)$:

```text
Y[i] = W[i,k] X[k] + B[i]
```

the core is

```math
\text{for }i\in[i_0]:
\quad
Y[i]\textcolor{#9D75C4}{\mathrel{+}=}
\left(\bigoplus_{k\in[k_0]}W[i,k]\otimes X[k]\right)\oplus B[i].
```

If $k_0=0$, the reduction is $0_K$ and the contribution is $B[i]$.
That distinguishes the intended rule from incorrectly placing the bias
inside the empty reduction.

### 16.2 Diagonal reads and writes

For input $\textcolor{#9D75C4}{M}$ of shape $(n,n)$ and a defined rank-zero `Trace`:

```text
Trace[] = M[i,i]
```

elaborates to the rank-zero contribution

```math
\text{for }():
\quad
\mathop{\mathrm{Trace}}\nolimits[]\textcolor{#9D75C4}{\mathrel{+}=}
\bigoplus_{i\in[n]}\textcolor{#9D75C4}{M}[i,i].
```

The empty statement context has one valuation, the empty assignment,
identified with $()$ under the rank-zero convention of [Section 1.2](tensor_logic_semantics_part_i.md#12-tuples-products-and-rank-zero-cases).
The repeated RHS variable binds once and selects diagonal coordinates.

By contrast, with input $X$ of shape $(n)$ and a defined `Diagonal`
of shape $(n,n)$,

```text
Diagonal[i,i] = X[i]
```

has statement context $i\in[n]$ and write map
$\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(i)=(i,i)$. It contributes only to diagonal coordinates of a
declared shape $(n,n)$ tensor. Off-diagonal coordinates have empty
contribution collections.

### 16.3 Colliding writes and lost-binder prevention

The affine-write example from [Section 11.2](tensor_logic_semantics_part_i.md#112-colliding-affine-writes) elaborates to

```math
\text{for }i\in[2],j\in[2]:
\quad
Y[i+j]\textcolor{#9D75C4}{\mathrel{+}=}A[i]\otimes B[j].
```

There is no body reduction. The two occurrences at output coordinate $1$
remain distinct members of $\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(Y,1)$, with scalar-coordinate
notation $1$ abbreviating tuple $(1)$.

In a separate numerical example, let $X$ be an input of shape $(3)$
and $Y$ a defined tensor of shape $(1)$. Then

```text
Y[i-i] = relu(X[i])    # i in [3]
```

retains three contribution occurrences at coordinate $0$.
Its intended collected value is

```math
Y[0]=\sum_{i\in[3]}\mathop{\mathrm{ReLU}}\nolimits(X[i]),
```

not $\mathop{\mathrm{ReLU}}\nolimits(\sum_i X[i])$.
Simplifying $i-i$ must not change the statement's binding structure or
move its activation boundary.

### 16.4 A strided convolution and an in-bounds guard

Let inputs $X,W$ have shapes $(h,w)$ and $(a,b)$, and let $Y$ be a defined
tensor whose declared output domain is such that every $(i,j)$ in it satisfies

```math
i+a\le h,\qquad 2j+b\le w.
```

For nonempty filter extents $a,b$, these conditions ensure the largest
read coordinates are in bounds. All indices range over finite ordinals,
so their lower bounds are nonnegative.

The surface statement

```text
Y[i,j] = W[p,r] X[i+p,2*j+r]
```

elaborates to

```math
\text{for }i,j:
\quad
Y[i,j]\textcolor{#9D75C4}{\mathrel{+}=}
\bigoplus_{p\in[a]}
\bigoplus_{r\in[b]}
W[p,r]\otimes X[i+p,2j+r],
```

where the displayed $i,j$ binders abbreviate their declared domains.
Alternatively, with a larger declared output domain, those inequalities can
be the statement guard, leaving other output coordinates without contributions. That specifies a
guarded computation, not zero-padded convolution.

### 16.5 Softmax over an attention slice

Work over exact reals. Let inputs $\textcolor{#9D75C4}{Q},\textcolor{#9D75C4}{\mathrm{Key}}$ have shapes
$(q_0,d)$ and $(\textcolor{#5688C7}{s}_0,d)$, and let the defined tensor $A$ have shape
$(q_0,\textcolor{#5688C7}{s}_0)$. If $\textcolor{#5688C7}{s}_0=0$, the statement below has no
occurrences and nothing is evaluated:

```text
A[q,s.] = softmax(Q[q,k] Key[s,k])
```

The marked variable $\textcolor{#5688C7}{s}$ selects the
slice domain $[\textcolor{#5688C7}{s}_0]$. The core body for $q\in[q_0],\textcolor{#5688C7}{s}\in[\textcolor{#5688C7}{s}_0]$ is

```math
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
\mathop{\mathrm{softmax}}\nolimits\left(
\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{t\in[\textcolor{#5688C7}{s}_0]}
\left(\sum_{k\in[d]}\textcolor{#9D75C4}{Q}[q,k]\textcolor{#9D75C4}{\mathrm{Key}}[t,k]\right)
\right),(\textcolor{#5688C7}{s})
\right).
```

The feature index $k$ is contracted; the key-position index is tabulated
for softmax and then selected at $\textcolor{#5688C7}{s}$. It is not contracted into a scalar.
The full statement contributes that body to $A[q,\textcolor{#5688C7}{s}]$.

### 16.6 A scan history with explicit slice input

Use the shapes and bounds of [Section 11.4](tensor_logic_semantics_part_i.md#114-a-finite-history-with-persistent-input). The recurrence statement
elaborates to

```math
\text{for }i\in[d],l\in[N]:
\quad
H[i,l+1]\textcolor{#9D75C4}{\mathrel{+}=}
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
F\left(\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[d]}(H[j,l])\right),(i)
\right).
```

The read time $l$ and write time $l+1$ are both within $[N+1]$.
$l$ is a free contribution variable, not a contracted index.
The tabulated $j$ is fresh and represents all coordinates required by $F$.

For $N=0$, this statement has no occurrences, while the base statements
still apply at time zero. For $N>0$, its apparent self-reference by tensor
name does not prevent the coordinate-level dependency analysis in [Section 23](tensor_logic_semantics_part_iv.md#23-read-footprints-and-executable-dependencies) from
recognizing a forward scan.

### 16.7 A causal mask is not a marked slice

Keep the inputs and shapes of [Section 16.5](#165-softmax-over-an-attention-slice), but normalize over only the keys
$t\le q$ for each query $q$. The marked-slice abbreviation of [Section 15.4](#154-marked-slice-operators) does
not apply: the mask $\textcolor{#5688C7}{s}\le q$ is a guard that depends on the marked variable
$\textcolor{#5688C7}{s}$. A mask inside the argument of $\mathop{\mathrm{softmax}}\nolimits$ does not work either.
That argument is a complete array on $[\textcolor{#5688C7}{s}_0]$, and multiplying an
entry by $\mathbf{1}_{t\le q}$ turns it into $0$. Then $\exp(0)=1$, so the key
is still normalized over, and exact reals have no $-\infty$ to use instead.

The core expresses the mask with scalar primitives. Register $\exp$, which is
total on $\mathbb{R}$, and division, defined where the divisor is nonzero
([Section 8](tensor_logic_semantics_part_i.md#8-operators-predicates-and-definedness)). Abbreviate the explicit reduction
$S(q,t)=\bigoplus_{k\in[d]}\textcolor{#9D75C4}{Q}[q,k]\otimes \textcolor{#9D75C4}{\mathrm{Key}}[t,k]$. For
$q\in[q_0]$ and $\textcolor{#5688C7}{s}\in[\textcolor{#5688C7}{s}_0]$, one statement suffices:

```math
A[q,\textcolor{#5688C7}{s}]\textcolor{#9D75C4}{\mathrel{+}=}
\mathop{\mathrm{div}}\nolimits\left(
\mathbf{1}_{\textcolor{#5688C7}{s}\le q}\otimes\exp(S(q,\textcolor{#5688C7}{s})),\;
\bigoplus_{t\in[\textcolor{#5688C7}{s}_0]}\mathbf{1}_{t\le q}\otimes\exp(S(q,t))
\right).
```

Every read is in bounds for every lifted valuation. Because $\exp$ is total,
multiplying by the Iverson value is safe here, unlike the logarithm of
[Section 21.3](tensor_logic_semantics_part_iii.md#213-a-guard-differs-from-a-zero-multiplier): the masked bodies are defined and contribute $0$. For
$\textcolor{#5688C7}{s}_0>0$ the denominator is at least $\exp(S(q,0))>0$, because $0\le q$ always holds,
so every division is defined and $A[q,\textcolor{#5688C7}{s}]=0$ for $\textcolor{#5688C7}{s}>q$. For
$\textcolor{#5688C7}{s}_0=0$ there are no occurrences.

An equivalent form uses guards, so masked bodies are never evaluated. Let $\mathit{Den}$ be
a defined tensor of shape $(q_0)$:

```math
\begin{aligned}
&\text{for }q\in[q_0],t\in[\textcolor{#5688C7}{s}_0]\text{ where }t\le q:
&&\mathit{Den}[q]\textcolor{#9D75C4}{\mathrel{+}=}\exp(S(q,t)),\\
&\text{for }q\in[q_0],\textcolor{#5688C7}{s}\in[\textcolor{#5688C7}{s}_0]\text{ where }\textcolor{#5688C7}{s}\le q:
&&A[q,\textcolor{#5688C7}{s}]\textcolor{#9D75C4}{\mathrel{+}=}\mathop{\mathrm{div}}\nolimits(\exp(S(q,\textcolor{#5688C7}{s})),\mathit{Den}[q]).
\end{aligned}
```

Entries with $\textcolor{#5688C7}{s}>q$ have empty fibers and are $0$. $\mathit{Den}[q]$ is read as a
named tensor, so its whole fiber is collected before any division is ready
([Section 25.2](tensor_logic_semantics_part_iv.md#252-publish-a-completed-coordinate)).

The two forms differ on fully masked rows. Replace $t\le q$ by the strict mask
$t<q$, and assume $q_0>0$ and $\textcolor{#5688C7}{s}_0>0$. Row $q=0$ then has no unmasked key.
In the first form the denominator at $q=0$ is a sum of $\textcolor{#5688C7}{s}_0$ masked zeros,
equal to $0_K$, so the division is undefined at an actual occurrence and the
program has no model (the machine ends in
$\textcolor{#A87C28}{\mathsf{Failed}}$). In the guarded form row $0$ has no
occurrence of $A$, so $A[0,\textcolor{#5688C7}{s}]=0$ is defined. This is the guard-versus-multiplier
distinction of [Section 21.3](tensor_logic_semantics_part_iii.md#213-a-guard-differs-from-a-zero-multiplier) again.

## 17. Pure einsum semantics and transformation foundations

This section fixes the mathematical reference meaning of the standard
pure-einsum profile from [Section 15.1](#151-explicit-inputs-to-elaboration). It does not extend the core with
a new primitive and does not define whole-program semantics.

The reference operands are complete tensor values from an environment
$\textcolor{#398B83}{\rho}$. There are no nonlinear operators, guards, or affine access
maps in this profile. The general core retains those capabilities.

Sections [17.1](#171-index-strings-and-global-valuations)-[17.3](#173-connection-to-the-contribution-core) need only the commutative-monoid laws of $\oplus$, the
coherence condition, and the bracketing convention of [Section 2.3](tensor_logic_semantics_part_i.md#23-which-algebraic-laws-each-part-uses). Sections [17.4](#174-delta-tensors-and-diagonal-identities)-[17.6](#176-neutral-operands-and-domain-preservation) use the full
semiring laws.

### 17.1 Index strings and global valuations

An **index string** $\textcolor{#5688C7}{L}=(j_1,\ldots,j_k)$ is an ordered tuple of index
variable identities. Unlike a context, an index string can repeat an
identity. It specifies which variable supplies each coordinate slot.

For operands $T_1,\ldots,T_m$, with $m\ge1$, let $\textcolor{#5688C7}{L}_r$ be the string
for operand $T_r$ and let $\textcolor{#5688C7}{L}$ be the output string.
Empty strings represent scalar operands or a scalar result.
The standard profile requires:

1. $\textcolor{#5688C7}{L}_r$ has the same length as the rank of $T_r$.
2. Each index variable's domain equals the domain of every slot it labels.
3. Every variable in $\textcolor{#5688C7}{L}$ occurs in at least one operand string.
4. If the result is assigned to a declared destination $T_{\textcolor{#9D75C4}{s}}$, its rank
   and ordered slot domains match $\textcolor{#5688C7}{L}$ exactly.

Let $\textcolor{#5688C7}{\Gamma}_{\mathrm{all}}$ contain every distinct variable in the
operand strings, once, with its resolved domain. This is a context
in the sense of [Section 3](tensor_logic_semantics_part_i.md#3-axes-index-variables-and-valuations), not a concatenation retaining duplicates.
Its valuations are the paper's global index assignments, expressed
using our existing $\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}$ notation.

For a string $\textcolor{#5688C7}{L}=(j_1,\ldots,j_k)$, define

```math
\textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}}=\textcolor{#5688C7}{I}_{j_1}\times\cdots\times \textcolor{#5688C7}{I}_{j_k},
\qquad
\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}}(\textcolor{#5688C7}{\nu})=(\textcolor{#5688C7}{\nu}(j_1),\ldots,\textcolor{#5688C7}{\nu}(j_k)).
```

Thus $\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}}:\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\mathrm{all}})\to \textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}}$ is a
coordinate projection. Equal-domain compatibility ensures that
$\textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}_r}=\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T_r)$ for each operand.
The destination condition similarly gives
$\textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}}=\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T_{\textcolor{#9D75C4}{s}})$. A larger declared destination
would instead describe a core computation with additional empty fibers,
not this standard pure-einsum profile.

For the empty string, $\textcolor{#5688C7}{J}_{()}=\{()\}$ and $\textcolor{#5688C7}{\pi}_{()}(\textcolor{#5688C7}{\nu})=()$.
For $\textcolor{#5688C7}{L}=(i,i)$, $\textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}}=\textcolor{#5688C7}{I}_i\times \textcolor{#5688C7}{I}_i$ but the projection reaches only
the diagonal. A coordinate projection need not be surjective.

**Example.** For matrix multiplication, the strings are
$\textcolor{#5688C7}{L}_1=(i,k)$, $\textcolor{#5688C7}{L}_2=(k,j)$, and $\textcolor{#5688C7}{L}=(i,j)$.
A global valuation of $i,k,j$ simultaneously identifies the entries
of both operands and the result coordinate.

### 17.2 Canonical fiber semantics

The result of this pure einsum is the tensor value $\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}:\textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}}\to K$
defined by

```math
\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}[p]
=
\bigoplus_{\substack{
 \textcolor{#5688C7}{\nu}\in\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\mathrm{all}})\\
 \textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}}(\textcolor{#5688C7}{\nu})=p
}}
\;\bigotimes_{r=1}^{m}
\textcolor{#398B83}{\rho}(T_r)[\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}_r}(\textcolor{#5688C7}{\nu})].
```

For each output coordinate, this combines all global assignments in
its projection fiber. Each assignment multiplies the corresponding
operand values. Equal-valued products remain distinct occurrences.

This definition directly handles:

- Contraction: assignments vary over variables not retained in $\textcolor{#5688C7}{L}$.
- Repeated input variables: the same value supplies several operand slots.
- Repeated output variables: off-diagonal projection fibers can be empty.
- Scalars: the empty string selects the sole rank-zero coordinate.
- Empty contracted domains: there are no global assignments, so a
  nonempty output domain receives $0_K$.

**Example: ordinary contraction.**

```math
\textcolor{#398B83}{V}_{(i,j)}[i,j]
=\bigoplus_{k\in \textcolor{#5688C7}{I}_k}
\textcolor{#398B83}{\rho}(W)[i,k]\otimes\textcolor{#398B83}{\rho}(X)[k,j].
```

**Example: diagonal construction.** For the single operand $v$ with
input string $(i)$ and output string $(i,i)$,

```math
\textcolor{#398B83}{V}_{(i,i)}[p,q]
=
\begin{cases}
\textcolor{#398B83}{\rho}(v)[p],&p=q,\\
0_K,&p\ne q.
\end{cases}
```

The full output domain remains $\textcolor{#5688C7}{I}_i\times \textcolor{#5688C7}{I}_i$, not a diagonal-only
coordinate set.

**Example: scalar-only operands.** If every string is empty, then
$\textcolor{#5688C7}{\Gamma}_{\mathrm{all}}$ is empty and has one valuation.
The result is the product of the scalar operands, not an empty sum.

### 17.3 Connection to the contribution core

Partition the global variables into:

- The distinct output variables, forming the statement context
  $\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$.
- The remaining variables, contracted in the body.

Use guard $\mathrm{true}$, an output map $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}$ given by the same
tuple projection on $\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}})$, and body

```math
\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}=
\bigoplus_{\text{remaining variables}}
\;\bigotimes_{r=1}^{m}T_r[\textcolor{#5688C7}{L}_r].
```

$T_r[\textcolor{#5688C7}{L}_r]$ abbreviates a read with the variables in $\textcolor{#5688C7}{L}_r$ in slot order.
The displayed reduction abbreviates nested core reductions, one binder
per remaining variable. When none remain, the body is just the product.

For this single statement, collecting body values over
$\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T_{\textcolor{#9D75C4}{s}},p)$ is intended to reproduce the canonical formula.
The required correspondence proof separates each global valuation into
its output-variable valuation and its contracted-variable valuation,
then combines the finite sums. Empty domains and repeated output
indices must be included in the proof.

[Section 19.3](tensor_logic_semantics_part_iii.md#193-correspondence-with-pure-einsum) states this correspondence using the core interpretation.
It is proved in Lean for the bounded source fragment (Proposition 19.1);
beyond that fragment it remains a proof obligation.

The formula cannot be extended to nonlinear bodies by moving an
operator inside the products or sums. For example,

```math
\mathop{\mathrm{ReLU}}\nolimits\left(\sum_k W[i,k]X[k]\right)
```

is not generally the sum of $\mathop{\mathrm{ReLU}}\nolimits(W[i,k]X[k])$.
The operator boundary fixed in Sections [13](#13-core-syntax-and-binding) and [15](#15-surface-to-core-elaboration) remains authoritative.

### 17.4 Delta tensors and diagonal identities

For a finite coordinate domain $\textcolor{#5688C7}{J}$, define the **delta tensor**

```math
\textcolor{#398B83}{\delta}_{\textcolor{#5688C7}{J}}:\textcolor{#5688C7}{J}\times \textcolor{#5688C7}{J}\to K,
\qquad
\textcolor{#398B83}{\delta}_{\textcolor{#5688C7}{J}}[p,q]=
\begin{cases}
1_K,&p=q,\\
0_K,&p\ne q.
\end{cases}
```

If $\textcolor{#5688C7}{J}$ is a product of $k$ slot domains, this can be represented as
a rank-$2k$ named tensor with the two copies of those slots in order.
For the scalar coordinate domain $\textcolor{#5688C7}{J}=\{()\}$, it is the scalar $1_K$.

Delta is an equality indicator, already expressible by the core
Iverson constructor. For product coordinates, $p=q$ abbreviates conjunction
of the corresponding slot equalities. It needs no additional primitive operation.
For $p\in \textcolor{#5688C7}{J}$ and a complete value $\textcolor{#398B83}{V}:\textcolor{#5688C7}{J}\to K$, finite combination gives

```math
\bigoplus_{q\in \textcolor{#5688C7}{J}}\textcolor{#398B83}{\delta}_{\textcolor{#5688C7}{J}}[p,q]\otimes \textcolor{#398B83}{V}[q]=\textcolor{#398B83}{V}[p].
```

Exactly one summand selects $p$ and the rest are $0_K$.
For empty $\textcolor{#5688C7}{J}$, this pointwise statement has no $p$ to quantify over.

For a vector $v:\textcolor{#5688C7}{I}\to K$, diagonal construction is

```math
\textcolor{#398B83}{D}[p,q]=\textcolor{#398B83}{\delta}_{\textcolor{#5688C7}{I}}[p,q]\otimes v[p].
```

For matrices with compatible domains,

```math
\bigoplus_{k\in \textcolor{#5688C7}{I}}A[i,k]\otimes \textcolor{#398B83}{D}[k,j]
=A[i,j]\otimes v[j].
```

This explains how a nested contraction with a diagonal intermediate
can be replaced by a direct pointwise scaling. It uses an equality
constraint, not merely renaming a bound variable.

**Identity caveat.** With repeated input and output string $(i,i)$,
a single-operand einsum keeps diagonal entries and zeros the rest:

```math
\textcolor{#398B83}{V}_{(i,i)}[p,q]
=
\begin{cases}
\textcolor{#398B83}{\rho}(\textcolor{#9D75C4}{M})[p,p],&p=q,\\
0_K,&p\ne q.
\end{cases}
```

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
$\textcolor{#398B83}{U},\textcolor{#398B83}{V}$ with the same coordinate domain, define

```math
(\textcolor{#398B83}{U}\oplus \textcolor{#398B83}{V})[p]=\textcolor{#398B83}{U}[p]\oplus \textcolor{#398B83}{V}[p].
```

A pure einsum distributes over replacement of one operand by this
pointwise combination, retaining that operand's index string.
The scalar distributive law and finite combination justify the result.
The core can express pointwise combination using tabulation, as
specified in [Section 13.3](#133-expression-constructors).

**Nesting and denesting.** An intermediate contraction may aggregate
only indices that are no longer needed by the outer contraction.
Its output interface must retain the necessary shared and final-output
indices. Inner and outer index variables must be renamed apart except
where an interface explicitly identifies them.

For example,

```math
\textcolor{#9D75C4}{s}=\sum_i a[i]b[i]c[i]
```

can use $u[i]=a[i]b[i]$ followed by $\textcolor{#9D75C4}{s}=\sum_i u[i]c[i]$.
Replacing $u$ by the scalar $\sum_i a[i]b[i]$ loses the correlation
with $c[i]$ and is generally incorrect.

Likewise,

```math
\left(\sum_i a[i]\right)\left(\sum_i b[i]\right)
=\sum_i\sum_j a[i]b[j],
```

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

Define an all-ones tensor $\mathbf{1}_{\textcolor{#5688C7}{J}}:\textcolor{#5688C7}{J}\to K$ by
$\mathbf{1}_{\textcolor{#5688C7}{J}}[p]=1_K$.
Multiplying a summand by an all-ones operand does not change its value.
Removing that operand is a different claim: it must not remove a
variable domain, introduce or remove reductions, or change output shape.

**Counterexample.** Over the reals,

```math
\sum_{j\in[m]}X[i]\cdot\mathbf{1}_{[m]}[j]=m\,X[i].
```

Removing both the operand and the $j$ binder gives $X[i]$, which is
generally different, including when $m=0$.
If a domain-carrying operand is eliminated, its binder and domain must
remain explicit unless a separate valid rule removes them.

Similarly, all-ones values can be introduced to represent a constant
array or retain index information, but this does not create that domain
from nothing. Domains remain supplied by signatures and binders.

This is particularly important for differentiation. Over exact reals,
with $W$ of shape $(d,e)$ and $x$ of shape $(e)$,

```math
F[i]=\sum_{j\in[e]}W[i,j]x[j]
```

has the coordinate derivative

```math
\frac{\partial F[i]}{\partial W[a,b]}
=\textcolor{#398B83}{\delta}_{[d]}[i,a]x[b].
```

The derivative has coordinate domain $[d]\times[d]\times[e]$ for
$(i,a,b)$, even though $W$ no longer appears as an operand in its value
expression. Those domains must survive any transformation.

Our explicit signatures and binders can preserve this information
without the reference paper's all-ones-operand workaround.
Rewrite and differentiation judgments must specify both their
result values and their result coordinate domains.
No differentiability claim is made here for arbitrary primitives such
as ReLU or for arbitrary semirings.

---

[Previous: Part I: Background notation](tensor_logic_semantics_part_i.md) | [Contents](README.md) | [Next: Part III: Denotational semantics](tensor_logic_semantics_part_iii.md)
