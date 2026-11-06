# Categorical Tensor Logic semantics: a prototype-grounded proposal

[Semantics contents](README.md) |
[Specification](tensor_logic_semantics.md) |
[Prototype and results](categorical_tensor_logic_lean_prototype.md)

## Summary

A **contribution** is one scalar value to be combined at a specified tensor
coordinate using that tensor's additive operation, such as ordinary addition
for numerical tensors. It is one term in the coordinate's collected value,
not an instruction to overwrite that coordinate. An undefined computation
does not supply a contribution and is not treated as a zero contribution.

A **statement** is an individually identified program clause specifying
finite ranges for its contribution variables, an optional condition
(its **guard**), a destination tensor coordinate, and an expression
(its **body**) producing a scalar contribution. Contribution variables
are indices whose assignments select individual instances of the clause.

An **occurrence** is the statement's identity paired with one assignment
to those variables that lies in their declared ranges and satisfies
the guard. A statement can generate many occurrences or none.
Identical clauses appearing separately have different statement identities
and therefore generate distinct occurrences.

The approach developed so far separates five layers:

1. **Index geometry:** finite coordinate domains and maps between them.
2. **Expression interpretation:** context-sensitive computations that can
   be undefined.
3. **Contribution collection:** additive combination of distinct tagged
   occurrences at their destinations.
4. **Logical execution:** availability of completed values and readiness
   of contribution and collector nodes.
5. **Implementation refinement:** schedules, kernels, and memory realise
   logical execution without changing its meaning.

The Lean prototype supports this separation. Its graph runner reproduces
the tested reference executions while storing produced contributions and
available values, rather than separately updating reference accumulators
and pending sets.

The strongest defensible conclusion is:

> A finite, typed dependency graph with partial expression interpretation
> and closed-writer collection is a credible foundation for logical
> execution. Its general correspondence and compositionality remain
> theorem targets, not consequences of the prototype alone.

The St/Br presentation can organise parts of the syntax and total
indexing. It is not assumed to be the best presentation of every layer.
Nor does this proposal require constructing a general categorical
framework before establishing the concrete correspondence.

This document distinguishes **mathematical constructions**, **observed
prototype evidence**, and **unproved proposal targets**. It does not
change the authoritative Tensor Logic specification.

The reading order follows the argument: Sections 1-5 establish meaning
and the proposed layers, Section 6 checks them against the prototype,
Sections 7-8 relate them to the categorical perspectives considered,
and Section 9 states the remaining proof targets.

## Table of contents

- [1. Begin with the meaning that execution must preserve](#1-begin-with-the-meaning-that-execution-must-preserve)
  - [1.1. What is an environment?](#11-what-is-an-environment)
  - [1.2. What makes an environment a model?](#12-what-makes-an-environment-a-model)
- [2. Index geometry acts on values](#2-index-geometry-acts-on-values)
  - [2.1. Finite domains and pullback](#21-finite-domains-and-pullback)
  - [2.2. Why the geometry should not dictate every computation](#22-why-the-geometry-should-not-dictate-every-computation)
- [3. Computations carry definedness obligations](#3-computations-carry-definedness-obligations)
  - [3.1. Interpretation is partial and context-sensitive](#31-interpretation-is-partial-and-context-sensitive)
  - [3.2. Partial functions provide a useful semantic category](#32-partial-functions-provide-a-useful-semantic-category)
  - [3.3. Value indexing and strict effect sequencing are separate](#33-value-indexing-and-strict-effect-sequencing-are-separate)
- [4. Additive collection is a different operation from reindexing](#4-additive-collection-is-a-different-operation-from-reindexing)
  - [4.1. Additive pushforward and its laws](#41-additive-pushforward-and-its-laws)
  - [4.2. Pure einsum fits the same organisation](#42-pure-einsum-fits-the-same-organisation)
  - [4.3. Keep the products distinct](#43-keep-the-products-distinct)
- [5. Closed-writer graphs provide the logical execution layer](#5-closed-writer-graphs-provide-the-logical-execution-layer)
  - [5.1. Readiness and completion](#51-readiness-and-completion)
  - [5.2. Open contributions and completed values are different interfaces](#52-open-contributions-and-completed-values-are-different-interfaces)
  - [5.3. Causal execution is not arbitrary equation solving](#53-causal-execution-is-not-arbitrary-equation-solving)
- [6. What the prototype actually supports](#6-what-the-prototype-actually-supports)
- [7. St/Br, indexed arrays, and open diagrams](#7-stbr-indexed-arrays-and-open-diagrams)
  - [7.1. St/Br remains a serious syntax candidate](#71-stbr-remains-a-serious-syntax-candidate)
  - [7.2. Naperian representation connects compact syntax to values](#72-naperian-representation-connects-compact-syntax-to-values)
  - [7.3. Open-diagram composition needs semantic interfaces](#73-open-diagram-composition-needs-semantic-interfaces)
  - [7.4. Temporal structure remains distinct](#74-temporal-structure-remains-distinct)
- [8. Where Turi-Plotkin and implementation refinement fit](#8-where-turi-plotkin-and-implementation-refinement-fit)
- [9. The most valuable theorem targets](#9-the-most-valuable-theorem-targets)
  - [9.1. Closed-graph/reference correspondence: unproved](#91-closed-graphreference-correspondence-unproved)
  - [9.2. Sealed sequential composition: unproved](#92-sealed-sequential-composition-unproved)
  - [9.3. Why unrestricted partial-function composition is unsafe](#93-why-unrestricted-partial-function-composition-is-unsafe)
- [Conclusion](#conclusion)
- [Notation reference](#notation-reference)

## 1. Begin with the meaning that execution must preserve

A core program, named $P$, declares:

- **Input tensors**, whose values are supplied from outside the program.
- **Defined tensors**, whose values must satisfy the program's contribution
  equations.
- **Designated outputs**, the defined tensors to return to the caller.
- **Contribution statements**, which specify values to combine at their
  destination coordinates.

Tensor and axis identities are part of the declaration; equal printed
names or equal extents do not establish identity. Every tensor also has
declared coordinate domains and a scalar value type.

### 1.1. What is an environment?

A **complete tensor environment**, named $\rho$, assigns a whole tensor
value to every declared tensor, both input and defined.
For a tensor identifier $T$, the notation $\rho(T)$ means the tensor
value assigned to $T$. For a valid coordinate tuple $p$, write
$\rho(T)[p]$ for that value's entry at $p$.

"Complete" means that every valid coordinate has a value of the declared
scalar type. There are no missing entries. A tensor with an empty
coordinate domain has its unique empty value.

An environment is a candidate assignment of mathematical values, not
necessarily the result of an execution. Assigning values to all tensors
does not yet establish that the equations hold, or that every expression
can be evaluated on those values. It is also different from a machine
store in which some coordinates are still unavailable.

An **input environment**, named $\eta$, assigns complete values only
to the input tensors. It supplies every declared input, including an
empty input tensor. The notation $\eta(T)[p]$ denotes an input entry
in the same way as $\rho(T)[p]$.

### 1.2. What makes an environment a model?

Write $\operatorname{Models}(P,\eta)$ for the set of complete
environments $\rho$ meeting all three conditions below.
These are requirements on the candidate values, not instructions
to mutate or repair an environment.

**1. Agree with the supplied inputs.** For every input tensor $T$
and every coordinate $p$ in its declared domain, require

$$
\rho(T)[p]=\eta(T)[p].
$$

Thus "extend $\eta$" means retaining exactly its input values while
also assigning values to the defined tensors. It does not mean adding
to the inputs, changing them during execution, or treating them as
implicit contributions. For example, if a supplied input entry is 3,
that same entry must be 3 in every model.

**2. Require every actual contribution body to be defined.**
Evaluate each occurrence's statement body using $\rho$ for all tensor
reads and the occurrence's assignment for its indices. Every such
evaluation must produce a scalar value, rather than an undefined result.
For example, reciprocal means division of 1 by its argument; a demanded
reciprocal of zero violates this condition.

This requirement includes contributions to internal nonoutput tensors
and contributions multiplied by zero. Guard-excluded occurrences and
nonexistent instances of empty binders are not evaluated. Providing a
complete environment does not itself guarantee expression definedness.

**3. Satisfy each collected coordinate equation.** For every coordinate
of every defined tensor, evaluate all actual contribution bodies targeting
that coordinate, combine their values using the declared additive
operation, and require the result to equal the value assigned there by
$\rho$.

"Defined coordinate" here means a coordinate of a tensor declared as
defined; it does not mean a coordinate that execution has already
published. Duplicate statements and different index assignments can
contribute separately to the same coordinate, even when their values
are equal. If no contribution targets the coordinate, its required value
is the additive identity: zero for ordinary numerical addition.

The candidate value already assigned to the destination is not an extra
summand. It affects a contribution only if that body's expression
explicitly reads it.

For example, let `X` be a scalar input with value 3 and `Y` a defined
scalar tensor. The empty brackets `[]` denote a scalar tensor's sole
coordinate. In this source notation, `=` introduces a contribution:

```text
Y[] = X[]
Y[] = X[]
```

Input agreement fixes `X[]` at 3. Both actual bodies return 3, so they
are defined. The collected equation requires `Y[]` to be 6 under
ordinary addition. Assigning 3 to `X[]` and 5 to `Y[]` gives a complete
environment, but not a model.

For equations that read defined tensors, the same candidate environment
is used throughout. The conditions are simultaneous consistency
requirements, not an instruction to process statements in source order.

This is the specified
[complete-model meaning](tensor_logic_semantics_part_iii.md#20-program-models-and-functional-denotation).
It includes internal tensors, not only outputs.

The set of models can be empty, have one member, or have several members.
The specified partial input-output function is defined only when this
complete model is unique.

That meaning must remain independent of an execution strategy. In
particular, a blocked cyclic computation can still have a unique model;
the direct reference machine does not solve arbitrary simultaneous
equations. Conversely, completion of a supported computation constructs
the model rather than selecting one by an unstated fixed-point rule.

## 2. Index geometry acts on values

### 2.1. Finite domains and pullback

Let $K$ be a set of scalar values, and $I$ and $J$ finite coordinate
sets. Write $K^I$ for functions from $I$ to $K$, representing a family
of scalar values; define $K^J$ similarly.

A coordinate map $r:I\longrightarrow J$ induces a function
$r^*:K^J\longrightarrow K^I$:

$$
r^*(v)=v\circ r.
$$

Here $v:J\longrightarrow K$ is a value family, $\circ$ denotes function
composition, and the superscript $*$ names **pullback** by precomposition.

Let $H$ be another finite coordinate set and
$s:J\longrightarrow H$ another map. Pullbacks satisfy

$$
(s\circ r)^*=r^*\circ s^*,
\qquad
(\operatorname{id}_I)^*=\operatorname{id}_{K^I}.
$$

The notation $\operatorname{id}$ denotes the identity function on the
subscripted set. The two identities above act on different kinds of input:

- $\operatorname{id}_I:I\longrightarrow I$ leaves each coordinate unchanged.
- $\operatorname{id}_{K^I}:K^I\longrightarrow K^I$ takes an entire value
  family and returns that same family unchanged. For every function
  $v:I\longrightarrow K$,

  $$
  \operatorname{id}_{K^I}(v)=v.
  $$

Thus $\operatorname{id}_{K^I}$ is a function acting on functions, not a
function selecting or changing an individual coordinate. Pulling a family
back along the identity coordinate map leaves the family unchanged,
which is what $(\operatorname{id}_I)^*=\operatorname{id}_{K^I}$ states.

These equations follow from ordinary function composition.
They organise value families as a contravariant functor
from finite sets to sets: coordinate maps go forward, reads go backward.

The identities and declared domains remain necessary typing information
around these underlying maps. The construction is not permission to
replace identity-aware alignment by cardinality matching.

### 2.2. Why the geometry should not dictate every computation

Affine index expressions present particular maps. Guards restrict
admissible assignments to finite subsets. A scalar has a singleton
coordinate domain; a zero extent produces an empty domain.

These distinctions can be described without requiring every admitted
domain to be a rectangular St object. The compiler can retain compact
affine and guarded descriptions rather than enumerate all coordinates.

The useful St-like principle is the separation of coordinate structure
from scalar values. Extending the source presentation or semantic domain
of coordinates need not change that principle.

## 3. Computations carry definedness obligations

### 3.1. Interpretation is partial and context-sensitive

A **primitive** is an operation treated as a basic building block of
expressions, such as reciprocal, square, or an operation on a whole array.
A **primitive registry** is a fixed catalogue specifying, for each
available primitive:

- Its number of arguments.
- The value type of each argument and of its result. A value type
  specifies a scalar carrier or an array's coordinate domains and
  scalar carrier.
- Its **domain of definition**: the argument values on which the
  operation is defined.
- The deterministic mathematical function giving its result on that
  domain.

Registered primitives have no hidden tensor reads or side effects:
their result depends only on their supplied argument values.
For example, real reciprocal takes one real scalar and returns a real
scalar, but its domain excludes zero. An array primitive can require an
entire array argument; it is not implicitly applied entry by entry.
This follows the
[primitive signatures](tensor_logic_semantics_part_ii.md#132-value-types-and-primitive-signatures)
in the specification.

A **typed expression** is an expression whose construction has been
checked against the tensor declarations, declared index variables,
admissible index assignments, and primitive signatures, yielding a
specified result type. Its checks ensure that:

- Every tensor and free index variable it uses is declared.
- Its operations receive arguments of the required types.
- Tensor and array accesses are within their declared coordinate
  domains at every index assignment demanded by its construction.
- Binding constructs, such as reductions and array tabulations,
  introduce and use their index variables consistently.

These are structural requirements. They do not guarantee that primitive
arguments satisfy their value-dependent domains. For example,
`reciprocal(0)` is a correctly typed real-scalar expression but is
undefined. An out-of-bounds tensor read, by contrast, is excluded by
the structural checks rather than accepted as a typed expression
that happens to be undefined.

Fix a registry and tensor declarations, and let $E$ be such a typed
expression. Write $\tau$ for its result type and $V_\tau$ for the set
of values of that type. Let $\mathsf{Env}$ denote the set of complete
environments and $\mathsf{Val}_E$ the set of admitted index valuations:
assignments of coordinates to the expression's free index variables.

Define $\operatorname{Result}(V_\tau)=V_\tau+\{\bot\}$, where $+$ is a
tagged disjoint union and $\bot$ denotes undefinedness. Interpretation
has the form

$$
\operatorname{eval}_E:
\mathsf{Env}\times\mathsf{Val}_E
\longrightarrow\operatorname{Result}(V_\tau).
$$

Here $\operatorname{eval}_E$ names the interpretation function and
$\times$ denotes Cartesian product of sets. Primitive domains,
binding, and actual array/reduction instances determine its result.
Undefinedness is not a scalar zero or an unavailable store entry.

The [strict expression semantics](tensor_logic_semantics_part_iii.md#18-expression-interpretation-and-definedness)
requires both operands of a scalar operation and every actual component
of an array construction to succeed. Empty binders evaluate no body
instances; guards remove excluded occurrences before evaluation.

### 3.2. Partial functions provide a useful semantic category

The category $\mathbf{Pfn}$ has sets as objects and partial functions
as morphisms. Composition succeeds only when both successive
applications are defined.

Using Cartesian product of underlying sets, **strict pairing** of
partial functions evaluates both components and succeeds only when
both succeed. This gives a symmetric monoidal structure: independent
computations can be placed alongside one another.

It does not make that product a categorical product in $\mathbf{Pfn}$.
Projecting one result after strict pairing still requires the other
computation to have succeeded. Erasing that computation can enlarge
the domain of definition.

This matches a central semantic requirement: unused numerical results
do not automatically mean their demanded computations can be discarded.
Some copying equations hold for deterministic partial functions, but
they do not identify execution traces or justify duplicating work
without considering diagnostics and cost.

This category is a useful target for interpretation. It is not claimed
to be an implemented categorical instance in the prototype.

### 3.3. Value indexing and strict effect sequencing are separate

Let $A$ and $B$ be sets and
$f:A\rightharpoonup B$ a partial function; the hooked arrow denotes
partiality. As with $K^I$, the notation $A^I$ and $B^I$ denotes
families indexed by $I$. For a finite index set $I$, define
$\operatorname{batch}_I(f):A^I\rightharpoonup B^I$ by applying $f$
at every coordinate and assembling a complete family only if every
application succeeds.

This factors into:

1. A family of individual partial results.
2. Strict sequencing of that family into one partial array result.

Empty batching succeeds with the unique empty family. An undefined
component in a nonempty demanded family prevents the whole result.

For $r:I\longrightarrow J$, write $r_A^*$ and $r_B^*$ for pullback
on $A$-valued and $B$-valued families, respectively. These subscripts
make the source and target of each composed function explicit.
Unrestricted naturality would require

$$
r_B^*\circ\operatorname{batch}_J(f)
=\operatorname{batch}_I(f)\circ r_A^*.
$$

That equation is false in general. The left side demands success at
every coordinate of $J$; the right side demands it only at coordinates
reached by $r$.

For example, reciprocal applied strictly to the rational array $(2,0)$
fails. Selecting its first coordinate before taking reciprocal succeeds.
This logical example illustrates the domain distinction; the prototype's
strict-array checks use the existing expression fixtures rather than a
new graph-level batching implementation.

A more accurate statement uses a **definedness order**. For partial
functions $h$ and $k$ with the same source and target, write
$h\preceq k$ when every input on which $h$ succeeds also makes $k$
succeed with the same value. Then

$$
r_B^*\circ\operatorname{batch}_J(f)
\preceq
\operatorname{batch}_I(f)\circ r_A^*.
$$

Equality holds when $f$ is total, when $r$ reaches every coordinate of
$J$, or under a separate guarantee that omitted applications succeed.
This is a mathematical statement about pointwise partial functions,
not a claimed general law for expressions with cross-coordinate reads.

Such directed compatibility is a better target than imposing an
unconditional strong reindexing action on every partial computation.

## 4. Additive collection is a different operation from reindexing

### 4.1. Additive pushforward and its laws

Assume now that $K$ has associative, commutative combination $\oplus$
with identity $0_K$, forming a **commutative monoid**.

Let $O$ be a finite set of tagged occurrences, $C$ a finite set of
defined addresses, and $d:O\longrightarrow C$ the destination map.
An **address** is a pair $(T,p)$ consisting of a tensor identifier
$T$ and one of its valid coordinate tuples $p$. A defined address
belongs to a tensor declared as defined, rather than as input.
For successful contribution values $v:O\longrightarrow K$, define
the **additive pushforward** $d_!:K^O\longrightarrow K^C$.
The subscript $!$, read "bang," distinguishes this induced map on
value families from the coordinate map $d$ itself. It means: send
contribution values forward along $d$, combining all values sent to
the same destination using $\oplus$. It is notation for this
construction, not a factorial or an inverse.

Explicitly:

$$
d_!(v)(a)=
\bigoplus_{\substack{o\in O\\d(o)=a}}v(o).
$$

Here $a\in C$ is a destination, $o\in O$ ranges over occurrences,
and $\bigoplus$ denotes finite combination. Empty fibers give $0_K$.

Unlike reindexing, this operation combines several inputs into one.
Equal values do not identify their occurrence tags.

With pointwise monoid operations on each value family, pushforward
preserves zero and addition. For another destination map
$e:C\longrightarrow H$, it satisfies

$$
(e\circ d)_!=e_!\circ d_!,
\qquad
(\operatorname{id}_O)_!=\operatorname{id}_{K^O}.
$$

These laws organise finite value families covariantly in the category
of commutative monoids and operation-preserving functions.
The existing
[collection layer](lean_executable_semantics_path_part_3.md#32-finite-additive-pushforward-covariance-and-multiplicity)
already records the corresponding identity, composition, grouping,
and relabeling results.

They do not establish a general pullback/pushforward adjunction or
Kan-extension construction. Undefined bodies are not summands:
pushforward begins after the included values have succeeded.
Strictly lifted scalar operations on results do not automatically
form another semiring; in particular, multiplying zero by an
undefined result remains undefined.

### 4.2. Pure einsum fits the same organisation

For pure einsum, additionally give $K$ a total multiplication
$\otimes$ and multiplicative identity $1_K$, with the commutative
semiring laws. This is an assumption on successful scalar values,
not on results containing $\bot$.

Let $m$ be the number of operands, with at least one operand.
For operand number $\ell\in\{1,\ldots,m\}$, let $J_\ell$ be its
coordinate domain and $v_\ell:J_\ell\longrightarrow K$ its complete value.
Let $M$ be the finite set of global index assignments, with maps
$\pi_\ell:M\longrightarrow J_\ell$ selecting each operand coordinate.
Define the summand family $w:M\longrightarrow K$ by

$$
w=\bigotimes_{\ell=1}^{m}\pi_\ell^*(v_\ell).
$$

The notation $\bigotimes$ means the finite pointwise product of
the pulled-back operand families. If
$\pi_{\mathrm{out}}:M\longrightarrow J_{\mathrm{out}}$ selects the
output coordinate in the output domain $J_{\mathrm{out}}$, then
the result value $V:J_{\mathrm{out}}\longrightarrow K$ is

$$
V=(\pi_{\mathrm{out}})_!(w).
$$

Thus operands are read on a common assignment domain, multiplied,
and collected into output fibers. Repeated indices and empty
fibers are expressed by the maps rather than informal name matching.
The [pure-einsum semantics](tensor_logic_semantics_part_ii.md#172-canonical-fiber-semantics)
already uses this organisation.

String diagrams can display this wiring and its algebraic equations.
They describe the computation's value unless an additional process
interpretation specifies readiness, steps, and observations.
Compact-closed or other tensor-diagram structures must be justified
for the chosen fragment; they are not implied merely by using a
symmetric monoidal operation theory.

### 4.3. Keep the products distinct

Juxtaposing array-valued wires uses product of value spaces.
Pointwise scalar multiplication and additive collection are specified
operations, not that product.

The representability identity
$(A\times B)^I\cong A^I\times B^I$ concerns Cartesian products;
$\cong$ here denotes a bijective correspondence.
It must not be silently transferred to ordinary vector-space tensor
products.

For a two-point index set and one-dimensional real vector spaces,
the analogous two sides with vector-space tensor product have
dimensions two and four, respectively. Thus a strong distributivity
claim requires the correct product or a separately defined fiberwise
tensor. Changing real vector spaces to semimodules does not by itself
resolve this mismatch or make nonlinear primitives linear.

## 5. Closed-writer graphs provide the logical execution layer

### 5.1. Readiness and completion

Fix a program and an actual occurrence $o$. Let $R_o$ be its full
**read footprint**: the set of named tensor addresses its body requires.
Once its statement, valuation, and registry are fixed,
read stability permits its body to be represented as a partial map
$g_o:K^{R_o}\rightharpoonup K$ in the one-carrier setting.
For multiple scalar sorts, the inputs instead use the corresponding
product of their value carriers.

The graph has two node kinds:

- A contribution node waits for all values in $R_o$, then evaluates
  the occurrence's whole body.
- A collector for an address waits for every actual occurrence
  targeting that address to produce a successful value.

The collector's output becomes readable only after that condition
holds. An empty writer family produces an available zero.

The operational state records available values and produced occurrence
values. Availability increases without changing previously available
values. The following reference information can be derived:

- Pending occurrences are the occurrences without produced values.
- An accumulator is the combination of values already produced for
  that destination.
- Published values are completed collector outputs and supplied inputs.

Atomic occurrence evaluation preserves the reference readiness boundary.
An invalid subexpression must not trigger a failure before another
required read makes the entire occurrence ready.

### 5.2. Open contributions and completed values are different interfaces

An **open writer interface** admits further contribution occurrences.
A **closed writer interface** fixes the complete occurrence family.
A **completed value interface** exposes the successful collected result.

These are three different states of the interface. Combining
contribution fragments is not the same operation as connecting a
completed value to a consumer.

The prototype implements validation of closed writer lists for one
fixed program, then runtime completion. Its `Fragment.append` merely
concatenates node lists; it does not yet implement general open
interfaces, writer ownership, or independent source-program gluing.

That limitation is the central remaining compositional issue.

### 5.3. Causal execution is not arbitrary equation solving

For the coordinate-ranked fragment, dependencies strictly increase
along an assigned natural-number rank. This gives progress for
direct execution.

Finite histories can have that property even when a tensor reads
earlier coordinates of itself. They require temporal causality,
not independent broadcasting along time or a blanket prohibition
on repeated tensor names.

The model relation still accommodates cyclic equations. A causal
executor and a solver for general cycles remain separate mechanisms.
Neither the graph picture nor the word "coalgebra" chooses a solution.

## 6. What the prototype actually supports

The implementation is
[`IndexedExecutionPrototype.lean`](../../leanncd/experiments/indexed_execution/IndexedExecutionPrototype.lean);
the checks are in
[`IndexedExecutionPrototypeTest.lean`](../../leanncd/experiments/indexed_execution/IndexedExecutionPrototypeTest.lean).
The [results note](categorical_tensor_logic_lean_prototype.md#5-observed-results)
records the executable observations and reproduction commands.

| Evidence | Supported conclusion | Boundary |
| --- | --- | --- |
| 36 passing checks, including 18 matched-priority comparison invocations | Tested graph executions match terminal outcomes, event data, intermediate snapshots, and blocked-read observations | Not 36 distinct programs, exhaustive schedules, or a general proof |
| Independent readiness and collector rules | Explicit ports can control tested executions without mutable pending and accumulator state | The program, footprints, and body interpreter are shared with the reference |
| Full-coordinate snapshots and input-presence checks | The comparison retains internal nonoutputs, unavailable values, zero values, occurrence identities, and empty-input validation | Reference snapshots are replayed from its witnessed events |
| Nonlinear, failure, chain, cycle, and malformed-port cases | Tests distinguish premature publication, nonlinear placement, waiting, undefinedness, and blocking | No general source admission or bounded-history adapter |
| Strict-array expression pins | Existing complete-array definedness is retained | Not graph-level evidence for a new strict-array node |
| Finite-family grouping/reindex checks | Concrete total-family laws have executable witnesses | No generic partial-lift or graph-batching theorem |
| Two implementation mutation controls | Tests detect an incorrect collector identity and removal of full-footprint readiness | Not evidence that every possible defect is covered |

The whole Lean build and branch review passed; the experiment adds no
new proofs, axioms, or `sorry`. This supports the implementation
hypothesis without establishing universal categorical laws.

An important restraint follows: **the prototype validates a different
state representation more strongly than it validates a new composition
theory**. Global writer information is still obtained from the known
whole program, and the strongest effect-sensitive examples remain
outside the new graph adapter.

## 7. St/Br, indexed arrays, and open diagrams

The categorical perspectives address different layers and different
notions of equivalence:

| Perspective | What it contributes | What it does not establish by itself |
| --- | --- | --- |
| St/Br and graded operation theories | Identity-aware shapes, typed composition, reindexing, broadcasting, and weave descriptions | A strict partial interpretation satisfying every total grading law |
| Naperian and applicative arrays | Values as coordinate-indexed families; coherent lookup, tabulation, and pointwise combination | Definedness-preserving elimination of demanded computations |
| Pullback and additive pushforward | Reads, contraction fibers, scatter, grouping, and occurrence multiplicity | A general operational model or a pullback/pushforward adjunction |
| Semiring tensor and string-diagram semantics | Algebraic contraction identities and compact pictures of index wiring | A schedule, storage policy, or strict partial semantics from the picture alone |
| Partial maps and effect sequencing | Primitive domains, strict assembly, and domain-sensitive transformation laws | A solver for cyclic equations or automatic trace equivalence |
| Closed-writer dataflow and coalgebras | Ready contribution steps, completion barriers, and next-step behaviour | General open-program composition or bialgebraic compatibility |
| Open graphs, ACSet interfaces, and network semantics | Explicit boundary matching and structural composition of presentations | Choosing the correct boundary or certifying a complete writer family |
| Complete-model relations and witness spans | General equation semantics, including multiple or absent models | An execution policy or unconditional composition of unique-model partial functions |
| Temporal iteration and scans | Finite causal dependencies and independent batching outside the time axis | Independent execution along time or unrestricted feedback solving |
| Turi-Plotkin and extensions | A route to constructor/behaviour compatibility and observation-sensitive compositionality | The required syntax, rule law, and hypotheses without further work |
| PROP interpretations, parameters, and refinement | Model interpretation, parameter handling, and implementation correctness targets | Concrete kernel progress, memory safety, or numerical guarantees from value equality alone |

This section relates indexed and diagrammatic presentations to the
layers established above. Section 8 addresses behavioural compatibility
and implementation; Section 9 states the remaining theorem targets.

### 7.1. St/Br remains a serious syntax candidate

In the [graded-PROP account](../graded_prop.md), $D$ names the index
category, instantiated by $\mathbf{St}$, and the operation category is
instantiated by $\mathbf{Br}$.

St describes axis identities, shapes, and coordinate transformations.
Br describes typed array operations and their sequential composition,
juxtaposition, and symmetry. A **colored PROP** is the corresponding
symmetric monoidal operation theory whose objects are lists of wire
types, called colors.

The graded lift extends an operation over an additional index domain.
A **weave** records which axes are local to the base operation and
which axes index independent copies of it. This is useful syntax for
retaining compact array-level descriptions rather than expanding
every contribution into a scalar node.

The candidate foundation is therefore not opposed to St/Br. It asks
whether that syntax should be interpreted by a more explicitly
effect-sensitive execution model, with collection and causal iteration
as distinct capabilities.

The full language must not be identified with a freely broadcastable
fragment without checking the laws. Reductions combine indexed values;
partial primitives impose domains; scans couple time positions.
Not all of these are independent lifting over the same kind of axis.
Nor does the existence of a shape map and action alone establish every
claimed fibration or a unique weave normal form.

### 7.2. Naperian representation connects compact syntax to values

Let $L$ be a shape object of $D$, and let $1_D$ be its unit scalar
shape. Define $\operatorname{El}(L)=D(1_D,L)$, the set of morphisms
from that unit to $L$; in the finite-coordinate interpretation these
are the shape's points.

Let $X$ be an array-valued wire interface and $[X,L]$ its lift over
$L$. Write $\mathsf{V}(X)$ for its interpreted value space.
The Naperian representation target is

$$
\mathsf{V}([X,L])
\cong
\mathsf{V}(X)^{\operatorname{El}(L)}.
$$

The right side is a family of $X$-values indexed by shape points.
Lookup and tabulation give the corresponding value-level correspondence.
The [Naperian discussion](../NaperianTyping.md)
appropriately treats this representation as additional structure,
not something supplied by shape monoidality alone.

This bridge is valuable for both semantics and implementation.
It can retain symbolic shape expressions while exposing the finite
coordinate families needed to define collection and test execution.
But representing successful values does not settle how a computation
produces them. Strict sequencing must still account for failures across
the demanded family, as in Section 3.

### 7.3. Open-diagram composition needs semantic interfaces

The [ACSet background](../acset.md) describes finite typed presentations
with explicit structural and attribute information. A diagram can
be composed through a specified boundary; a pushout is the categorical
gluing construction identifying that shared interface.

This perspective is compatible with the closed-writer graph proposal.
It could represent contribution ports, readable values, and writer
closure explicitly.

Two obligations remain separate from the gluing operation:

1. Identify the intended boundary, respecting identities, domains,
   sorts, and the roles of ports.
2. Establish that a published coordinate's complete writer family
   has been accounted for.

A structural pushout does not decide either obligation. Gluing an
additional writer to an already completed-value interface must not be
accepted merely because the underlying diagrams can be joined.

Open-network semantics, including
[open Petri nets](https://arxiv.org/abs/1808.05415), gives a useful
precedent for assigning execution processes compositionally to graphs.
It is not a ready-made Tensor Logic semantics: immutable shared reads,
additive writer multiplicity, and strict failures need their own account.
Likewise, identifying wires is not the same operation as adding their
scalar contributions.

### 7.4. Temporal structure remains distinct

The [temporal grading](../graded_prop.md#34-the-temporal-grading-and-making-scan-first-class)
offers an appropriate compact syntax for bounded scans. A scan is
finite causal iteration of a step computation, not independent
broadcasting along time.

For total step operations, prefix restriction and independent
batching are natural theorem targets. For partial steps, a complete
history can fail at a later position although an earlier prefix is
defined. Equality between restricting a completed history and
running only a prefix therefore needs definedness conditions or a
different observation policy.

Neither a fold interpretation nor a traced-diagram vocabulary should
silently introduce a solver for arbitrary cyclic equations. The
prototype's chain and blocked-cycle checks support this distinction,
but do not verify a full scan implementation.

## 8. Where Turi-Plotkin and implementation refinement fit

A coalgebra packages the graph's next-step behaviour. It does not
by itself prove that composition of graph syntax respects that
behaviour.

Concretely, choose an endofunctor describing terminal observations or
finite sets of labelled successor states. A coalgebra structure map
assigns each execution state that next-step information. This packages
the transition rules, including scheduling alternatives, without
changing their meaning. No generic coalgebra instance or
constructor-compatibility theorem is implemented by the prototype.

An **endofunctor algebra** is one structure arrow
$\alpha:FA\longrightarrow A$, for a chosen endofunctor $F$ and carrier
$A$. A **PROP algebra** is instead a structure-preserving interpretation
functor from a presented operation theory to a chosen target category.
The scalar commutative-monoid structure is a third use of "algebraic
structure." These notions should not be conflated.

A Turi-Plotkin-style treatment would require an explicit syntax
construction, behaviour functor, rule transformation, and compatibility
law. No such law is supplied automatically by having two node kinds.

It must also choose observations. Two expressions with the same
tensor value can have different execution steps, diagnostics, or costs.
A process interpretation cannot automatically descend through every
equation valid only for final values. Such transformations may instead
require a coarser observation policy or a refinement witness.

For physical implementations, the existing
[simulation with stuttering](tensor_logic_semantics_part_v.md#312-initial-states-and-successful-step-simulation)
is still the right direction. A batched command can match many logical
steps, and a storage-only command can match none. Concrete termination,
failure matching, and output representation remain separate obligations.
Neither a value-preserving functor nor a reparameterisation equation
alone proves safe memory reuse or concrete progress.

Thus Turi-Plotkin is a possible way to organise a subsequent
compositionality theorem. A finite-graph interpretation followed by
simulation may be the simpler route for the current static fragment.

Extensions for weak or trace observations can help compare executions
that hide different amounts of internal work. They must be applied to
a specified observation policy and constructor interface, not invoked
to assume that all value-preserving schedules or rewrites are equivalent.

Other extensions occupy different parts of the picture:

- Binding-aware syntax addresses scoped index variables and substitution;
  a shape-only operation signature does not account for these automatically.
- Probabilistic or weighted behaviour changes the behaviour model and its
  observations. The present prototype instead has exact deterministic
  body evaluation with scheduling choices.
- Higher-order extensions address languages accepting programs as function
  arguments. Registered scalar or array primitives do not make this core
  higher-order in that sense.

Likewise, a normalisation primitive is not automatically a Markov-category
construction. Softmax, sum normalisation, their domains, and their
algebraic identities need their own definitions. Their mere presence
does not supply a probabilistic process semantics.

The parameterised interpretation perspective also remains useful.
In the **Para construction**, a computation carries an explicit
parameter object, such as weights, and a map using those parameters.
It distinguishes architecture from a parameter choice and expresses
appropriate reparameterisations.

That is an interpretation layer, not a substitute for process
refinement. A schedule change, checkpointing scheme, or buffer
reallocation is not automatically just a weight reparameterisation.
Such transformations still need the appropriate execution and
representation arguments.

## 9. The most valuable theorem targets

### 9.1. Closed-graph/reference correspondence: unproved

Fix a well-formed finite program $P$ over the prototype's exact-rational
registry and a complete priority schedule $S$.
Let $\beta$ be a raw input binding, which may omit required inputs,
and $G$ a fragment accepted by `close` for $P$ and $S$.
Unlike the validated input environment $\eta$ of Section 1,
$\beta$ is input data awaiting validation.

Relate graph and reference states by agreement of:

- Tensor-level input presence.
- Available and published coordinate values.
- Pending identities and occurrences without produced values.
- Accumulators and sums of produced contributions.
- Terminal failure identities and the associated data snapshots.

The target is:

> With matched priority and the default sufficient budget, graph execution
> and reference execution reject the same invalid input or select the same
> next action, producing matching values, failure, or blocking. Neither
> graph budget exhaustion nor an internal mismatch occurs.

An inductive step correspondence would then give equal witnessed
events and snapshots across all coordinates, not only outputs.
Reference soundness would transfer successful graph execution to the
unique complete model, and reached undefinedness to absence of a model.
Blocking would still make no such claim.

No rank certificate is needed to compare the two fixed executions.
Rank hypotheses are needed for the separate no-blocking conclusion.
Failure identities are compared under matched priorities, not across
arbitrary different schedules.

This theorem is deliberately concrete. It should precede a general
categorical packaging of the operational rules.

### 9.2. Sealed sequential composition: unproved

A tractable composition target has two components, named $P$ and $Q$.
Let $X$ be $P$'s input interface and $Y$ its complete output interface,
which supplies every input of $Q$. An interface lists typed tensors
and their full coordinate domains.

Require:

- Distinct private tensor and occurrence identities.
- Explicit one-to-one matching of the typed boundary $Y$.
- Closed writers for $P$'s boundary values.
- No writes by $Q$ to $P$'s defined addresses.
- No reads by $P$ from values defined inside $Q$.
- Completion and definedness obligations for all internal work in both
  components, whether or not its value reaches the final output.

Write $Q\circ P$ for this proposed sequential composite and $\eta_X$
for validated inputs on $X$. Let $\rho_P$ and $\rho_Q$ denote complete
upstream and downstream models, respectively.
Write $\rho_P|_Y$ for restriction to the boundary tensors.

The safe semantic target is a bijection of complete-model witnesses:

$$
\operatorname{Models}(Q\circ P,\eta_X)
\cong
\left\{
(\rho_P,\rho_Q)\ \middle|\
\begin{array}{l}
\rho_P\in\operatorname{Models}(P,\eta_X),\\
\rho_Q\in\operatorname{Models}(Q,\rho_P|_Y)
\end{array}
\right\}.
$$

The pair retains both components' internal values rather than
hiding them before uniqueness is checked.

If the upstream model is unique and the downstream model on that
boundary is unique, the composite model is unique and its output
is obtained by the successive interpretations.

### 9.3. Why unrestricted partial-function composition is unsafe

The unique-model criterion is not automatically compositional for
arbitrary cyclic systems. A downstream component can exclude all but
one upstream model.

For a logical example over exact rationals, let an upstream scalar
$t$ satisfy $t=t^2$, where the superscript 2 denotes squaring.
Its two models have $t=0$ and $t=1$. Let the downstream scalar $u$
be the reciprocal of $t$, defined only when $t$ is nonzero.
Only the model with $t=1$ extends, giving $u=1$.

The composite has a unique complete model although the upstream
standalone partial function is undefined by the unique-model criterion.
This is a semantic example, not an executed prototype fixture or a
claim that the direct executor solves it.

Consequently, the general composition structure should retain
**compatible complete-model witnesses**. One categorical representation
is a span: a set of complete models equipped with maps to its input
and output environments. Composing such spans pairs models that
agree at the shared boundary and retains the witnesses.

This is a proposed semantic construction, not an implemented open-program
composition. Unlike an output-only relation, it need not identify
different internal models prematurely.

For components with at most one model on every input, such as the
ranked fragment under the specified assumptions, this particular
obstacle disappears. Extracting partial functions is then a more
reasonable compositional target, still subject to the explicit
interface conditions.

## Conclusion

The approach now has a plausible concrete centre:

> **Identity-aware index geometry, strict partial expression interpretation,
> multiplicity-preserving collection, and closed-writer dependency graphs.**

The prototype supports the graph/reference state relationship on its
tested instances and catches two meaningful implementation defects.
It does not yet decide the best categorical presentation of general
Tensor Logic.

The next decisive evidence should be a graph-level strict-array example
and genuine composition of independently authored writer fragments.
The next decisive theorem should be closed-graph/reference correspondence,
followed by composition that retains complete-model witnesses.

This ordering keeps elegance accountable to the actual semantics:
make the concrete structure sound and compositional, then choose the
categorical packaging that expresses those results most simply.

## Notation reference

Symbols are defined on introduction. This table collects the recurring
ones; it does not add assumptions beyond their definitions.

| Notation | Meaning |
| --- | --- |
| $P,Q$ | Core programs or components |
| $\rho$ | Complete candidate tensor environment |
| $\eta,\eta_X$ | Validated complete input environment, optionally restricted to interface $X$ |
| $\beta$ | Raw input binding awaiting validation |
| $\rho(T)[p]$ | Entry at coordinate $p$ of tensor $T$ in environment $\rho$ |
| $\operatorname{Models}(P,\eta)$ | Complete models of program $P$ on supplied inputs $\eta$ |
| $K$ | Scalar value carrier; collection additionally assumes its commutative-monoid structure |
| $I,J,H$ | Finite coordinate sets |
| $K^I,A^I,B^I$ | Value families indexed by $I$ |
| $r,s$ | Coordinate maps |
| $r^*,r_A^*,r_B^*$ | Pullback, with a value-carrier subscript when needed |
| $E,\tau,V_\tau$ | Expression, its value type, and its value space |
| $\mathsf{Env},\mathsf{Val}_E$ | Complete environments and admitted valuations for $E$ |
| $\operatorname{Result}(V_\tau),\bot$ | Successful values or undefinedness; the undefined result |
| $f:A\rightharpoonup B$ | Partial computation from $A$ to $B$ |
| $h\preceq k$ | Every successful application of $h$ is also a successful application of $k$ with the same value |
| $O,C,d$ | Tagged occurrences, defined addresses, and their destination map |
| $d_!$ | Additive pushforward along $d$ |
| $\oplus,0_K$ | Scalar combination and its identity |
| $\otimes,1_K$ | Scalar multiplication and its identity in the pure-einsum semiring fragment |
| $M,\pi_\ell,\pi_{\mathrm{out}}$ | Global assignments and their operand/output coordinate maps |
| $R_o,g_o$ | Full read footprint and partial body interpretation of occurrence $o$ |
| $D,L,1_D$ | Index category, shape object, and its unit scalar shape |
| $\operatorname{El}(L)$ | Points of shape $L$, represented by morphisms $1_D\to L$ |
| $[X,L],\mathsf{V}(X)$ | Lifted interface and interpreted value space |
| $S,G$ | Complete priority schedule and accepted graph fragment |
| $\rho_P,\rho_Q,\rho_P|_Y$ | Complete component models and upstream restriction to boundary $Y$ |
| $\circ,\operatorname{id},\cong$ | Composition, identity, and bijective correspondence, as typed in each use |
