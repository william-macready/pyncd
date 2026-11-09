# Categorical Tensor Logic semantics: a prototype-grounded proposal

[Semantics contents](README.md) |
[Specification](tensor_logic_semantics.md) |
[Prototype and results](categorical_tensor_logic_lean_prototype.md) |
[Witness-category proof and release evidence](categorical_witness_semantics_record.md)

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

The Lean development now provides executable evidence, proved typed
expression transport, conditional execution correspondence, and static
composition of source-contract matches, together with complete-model
restriction/gluing and a proved witness-span category. Given an explicit local
match between a source program and a closed writer contract, the
contract-based runner and reference executor have corresponding outcomes,
mapped event traces, and intermediate states. The graph still stores
produced contributions and available values rather than separately
updating reference accumulators and pending sets.

**Static composition** assembles a new component and its match certificate;
it is not a theorem that one component finishes before another starts.
The implemented constructor takes two independently matched, locally scoped
components and an explicit bijection between whole output and input tensors,
with certified coordinate-domain adapters. It constructs the composite
program, contract, fragment, schedule and match without asking the caller
to supply a whole-composite match or execution agreement.
See the [composition record](component_composition_record.md).

**Model composition** now proves that the composite's complete-model
witnesses correspond exactly to compatible complete witnesses of its two
components. It retains private values, internal definedness and empty tensor
metadata, and requires no rank, model-existence or uniqueness premise.
A separate theorem establishes successive partial-function denotation only
when both components have at most one complete model on every validated
input. Neither result asserts that the producer finishes before the consumer
starts. See the [model-gluing record](component_model_gluing_record.md).

**Categorical witness semantics** packages every validated input and every
complete model into a span between metadata-bearing whole-interface
environments. Arrows are spans up to an apex bijection commuting with both
environment maps; composition pairs compatible witnesses, and the identity
is the identity span. Quotient congruence, both unit laws and associativity
are proved. The component constructor preserves this composition through
explicit boundary and exterior interface transports, and both actual nested
component bracketings correspond to the same compatible model triple.
Injective-left spans have a quotient-invariant partial-map interpretation;
for components, this restriction is exactly `AtMostOneModels`.
The certified source presentation now adds a distinct whole-interface object
wrapper, matched leaves and explicit coordinate wires, a generated syntactic
congruence and an actual Mathlib functor into this witness category. Actual
component assembly and both nested constructor bracketings compare in the
source after their inherited transports. These are denotational results, not
event-sensitive process laws. See the
[witness semantics record](categorical_witness_semantics_record.md) and
[source-functor record](categorical_source_functor_record.md).

The independently authored validation fixture supplies actual
proof instances of the execution-correspondence theorem. Its six-event failure and
seven-event completion remain concrete executable observations;
the general correspondence is not inferred from those observations.
The same behaviours are now obtained from genuinely local producer and
consumer matches through the static constructor, retaining private `Audit`
work and introducing no forwarding-copy events.

The strongest defensible conclusion is:

> A finite, typed dependency graph with partial expression interpretation
> and closed-writer collection is a credible foundation for logical
> execution. Its correspondence with the reference semantics is proved
> under explicit local matching conditions, and compatible matched
> components construct both a correct composite match and a bijection of
> compatible complete-model witnesses. These witnesses give a proved
> denotational category, a composition-preserving component interpretation,
> and coherent nested composition after explicit interface transport.
> Partial-map composition is proved under explicit at-most-one-model
> hypotheses. Source-category laws, ranked phase execution and event-sensitive
> process laws remain separate obligations.

The St/Br presentation can organise parts of the syntax and total
indexing. It is not assumed to be the best presentation of every layer.
The correspondence proof did not require a general categorical framework
first. The witness category now packages complete-model meaning; connecting
St/Br syntax to that target still requires a separate interpretation.

This document distinguishes **mathematical constructions**, **observed
prototype evidence**, **proved conditional results**, and **unproved
proposal targets**. It does not change the authoritative Tensor Logic
specification.

The reading order follows the argument: Sections 1-5 establish meaning
and the proposed layers, Section 6 records experiments and the proofs,
Sections 7-8 relate them to the categorical perspectives considered,
and Section 9 separates established results from remaining targets.
Section 10 gives the categorization roadmap and a ledger of current progress.
Appendix A explains correspondence and how the static constructor supplies
its match, then the complete-model gluing and categorical witness arguments,
in mathematical rather than Lean notation.

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
  - [6.1. Verified evidence and its scope](#61-verified-evidence-and-its-scope)
  - [6.2. Composition results](#62-composition-results)
  - [6.3. Effect-sequencing results](#63-effect-sequencing-results)
  - [6.4. The combined test](#64-the-combined-test)
  - [6.5. Independent reference validation](#65-independent-reference-validation)
  - [6.6. What these results establish](#66-what-these-results-establish)
  - [6.7. Kernel-checked conditional correspondence](#67-kernel-checked-conditional-correspondence)
  - [6.8. Kernel-checked static component composition](#68-kernel-checked-static-component-composition)
  - [6.9. Kernel-checked model gluing and restricted denotation](#69-kernel-checked-model-gluing-and-restricted-denotation)
  - [6.10. Kernel-checked categorical witness semantics](#610-kernel-checked-categorical-witness-semantics)
- [7. St/Br, indexed arrays, and open diagrams](#7-stbr-indexed-arrays-and-open-diagrams)
  - [7.1. St/Br remains a serious syntax candidate](#71-stbr-remains-a-serious-syntax-candidate)
  - [7.2. Naperian representation connects compact syntax to values](#72-naperian-representation-connects-compact-syntax-to-values)
  - [7.3. Open-diagram composition needs semantic interfaces](#73-open-diagram-composition-needs-semantic-interfaces)
  - [7.4. Temporal structure remains distinct](#74-temporal-structure-remains-distinct)
- [8. Where Turi-Plotkin and implementation refinement fit](#8-where-turi-plotkin-and-implementation-refinement-fit)
- [9. Proof status and remaining targets](#9-proof-status-and-remaining-targets)
  - [9.1. Closed-graph/reference correspondence: conditional proof](#91-closed-graphreference-correspondence-conditional-proof)
  - [9.2. Sealed composition: model gluing proved, operational targets open](#92-sealed-composition-model-gluing-proved-operational-targets-open)
  - [9.3. Why unrestricted partial-function composition is unsafe](#93-why-unrestricted-partial-function-composition-is-unsafe)
- [10. Categorization roadmap and progress](#10-categorization-roadmap-and-progress)
  - [10.1. What each step buys us](#101-what-each-step-buys-us)
  - [10.2. Progress ledger](#102-progress-ledger)
  - [10.3. Remaining branches of the roadmap](#103-remaining-branches-of-the-roadmap)
- [Conclusion](#conclusion)
- [Appendix A. How the correspondence proof works](#appendix-a-how-the-correspondence-proof-works)
  - [A.1. Start with a local match, not matching executions](#a1-start-with-a-local-match-not-matching-executions)
  - [A.2. Relate the two representations of unfinished work](#a2-relate-the-two-representations-of-unfinished-work)
  - [A.3. Show that each action preserves the relation](#a3-show-that-each-action-preserves-the-relation)
  - [A.4. Lift local agreement to complete executions](#a4-lift-local-agreement-to-complete-executions)
  - [A.5. Transfer the meaning of successful and failed runs](#a5-transfer-the-meaning-of-successful-and-failed-runs)
  - [A.6. Establish genuine instances and audit the proof](#a6-establish-genuine-instances-and-audit-the-proof)
  - [A.7. Construct a match from component matches](#a7-construct-a-match-from-component-matches)
  - [A.8. Restrict and glue complete-model witnesses](#a8-restrict-and-glue-complete-model-witnesses)
  - [A.9. Turn model witnesses into categorical semantics](#a9-turn-model-witnesses-into-categorical-semantics)
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

This category is a useful target for interpretation. The prototype now
implements quotient-invariant partial maps for injective-left witness spans
and connects them to component denotation (Section 6.10). It does not install
a general $\mathbf{Pfn}$ category or prove a symmetric monoidal
interpretation of Tensor Logic in it.

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
This logical example illustrates the domain distinction. The effect
extension now tests strict tabulation and selection inside graph/reference
execution, and the composition extension retains that failure after
joining independent fragments. Both reuse expression interpretation;
neither introduces a generic batching implementation.

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

The original baseline prototype implements validation of closed writer lists for one
fixed program, then runtime completion. Its `Fragment.append` merely
concatenates node lists; it does not yet implement general open
interfaces, writer ownership, or independent source-program gluing.

The separate composition extension goes further: independently authored
fragments claim writer capability IDs against a declared contract.
Its `combine` checks identity collisions and `close` requires exact
capability coverage, correct destinations and footprints, readable
ports, and complete collectors. It uses no canonical whole-program graph
as its closure oracle.

The completeness assumption has moved to the declared contract, not
disappeared. Numeric capability IDs are checked identities rather than
unforgeable tokens. The later static constructor in Section 6.8 now proves
scoped source-program assembly from already matched components and explicit
whole-tensor boundaries. It does not infer leaf contracts or discover
unknown writers. Structural sealing fixes the writer family; it does not
guarantee runtime completion or definedness.

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

### 6.1. Verified evidence and its scope

The baseline implementation is
[`IndexedExecutionPrototype.lean`](../../leanncd/experiments/indexed_execution/IndexedExecutionPrototype.lean);
the checks are in
[`IndexedExecutionPrototypeTest.lean`](../../leanncd/experiments/indexed_execution/IndexedExecutionPrototypeTest.lean).
The separate extensions are
[`IndexedEffectSequencingTest.lean`](../../leanncd/experiments/indexed_execution/IndexedEffectSequencingTest.lean)
and
[`IndexedOpenComposition.lean`](../../leanncd/experiments/indexed_execution/IndexedOpenComposition.lean),
with composition checks in
[`IndexedOpenCompositionTest.lean`](../../leanncd/experiments/indexed_execution/IndexedOpenCompositionTest.lean).
The independent reference fixture is
[`IndexedCompositionParityTest.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionParityTest.lean).
The [results note](categorical_tensor_logic_lean_prototype.md#5-observed-results)
records the executable observations and reproduction commands.
The [proof record](categorical_tensor_logic_proof_record.md) and
[implemented theorem](../../leanncd/experiments/indexed_execution/IndexedCompositionValidated.lean)
record the separate semantic result.
The [transport record](component_transport_execution_record.md) and
[static-composition record](component_composition_record.md) record the
subsequent constructions and their own validation.
The [model-gluing record](component_model_gluing_record.md) records the
rank-independent witness theorem, restricted denotation and logical-model
counterexamples.
The [witness semantics record](categorical_witness_semantics_record.md)
records the subsequent target category, all-input composition comparison,
nested coherence, restricted partial maps and completed release gates.

| Evidence | Supported conclusion | Boundary |
| --- | --- | --- |
| Original 93 prototype checks: 36 baseline, 12 effect, 29 composition, 16 independent parity | Baseline/effect comparisons and two independently authored composed/reference cases match; other composition cases meet explicit expectations | These are the original suites, not a total count including later transport/composition fixtures; their 23 comparison invocations include repeated controls |
| Independent readiness and collector rules | Explicit ports can control tested executions without mutable pending and accumulator state | Expression interpretation is shared; the baseline also shares the reference program, while the composition runner uses a separate declared contract |
| Full-coordinate snapshots and input-presence checks | The comparison retains internal nonoutputs, unavailable values, zero values, occurrence identities, and empty-input validation | Reference snapshots are replayed from its witnessed events |
| Nonlinear, failure, chain, cycle, and malformed-port cases | Tests distinguish premature publication, nonlinear placement, waiting, undefinedness, and blocking | No general source admission or bounded-history adapter |
| Strict-array graph/reference cases and their composition | Undefined nonselected work still fails; the all-defined neighbour succeeds; a select-first shortcut is non-equivalent | The interpreter is shared, and there is no generic array-node lowering theorem |
| Declared-contract open fragments | Missing and extra writers, identity collisions, incorrect destinations, early closure and forged closed payloads are detected or safely regenerated | Closure is relative to the supplied contract, not discovery of unknown writers |
| Finite-family grouping/reindex checks | Concrete total-family laws have executable witnesses | No generic partial-lift or graph-batching theorem |
| Two baseline, four extension, and one reference-only mutation control | Tests detect incorrect collection, dropped readiness, bypassed strictness, incomplete closure, forged collectors, and one-sided reference disagreement | Not evidence that every possible defect is covered |
| Kernel-checked default execution correspondence | Every supplied local source-contract match yields corresponding validated executions, traces and state observations | Exact-rational profile and matched priorities; source alignment is a premise, not inferred |
| Proved match for the independently authored fixture | The general theorem has actual strict and total instances; the match is established for every rational fixture parameter | Shared expression helpers do not independently verify expression interpretation |
| Proved declaration/context transport | Certified adapters preserve ordered repeated footprints, readiness, strict partial evaluation and complete interpretation for every partial store | Supplied axis/domain adapters and the fixed rational registry, not automatic name/domain matching |
| Kernel-checked static match constructor | Two local matched components and an explicit whole-tensor boundary yield a composite match, including closure and canonical priority | The constructor alone produces no rank or phase theorem; the separate result in Section 6.9 supplies model gluing |
| Constructed composite correspondence instances | Strict/total, zero-writer, empty-port, collision and unequal-axis cases apply the existing general correspondence theorem to constructed matches | These instances do not establish categorical laws, general trace concatenation or an independent expression interpreter |
| Rank-independent complete-model gluing | Composite model witnesses are in bijection with dependent compatible component-model pairs, retaining all private work | Validated inputs, explicit typed boundary and fixed rational profile; no existence, uniqueness or execution premise |
| Restricted denotation composition | Both at-most-one-model hypotheses give the exact admissibility domain and transported successive output denotation | At most one model on every input does not imply existence; no unrestricted unique-model composition law |
| Kernel-checked cyclic and hidden-model cases | Downstream filtering and distinct internal witnesses with equal outputs are realized by matched model fixtures | Complete-store/model proofs, not claims that the executor solves cyclic equations |
| Metadata-bearing witness-span category | Span-isomorphism quotient, well-defined pullback composition, identity spans, both unit laws and associativity | Objects and homs in `Type 1`, environments and individual apexes in `Type 0`; no same-universe local-smallness claim |
| All-input categorical component comparison | Composite witnesses and wired component witnesses are bijective, with both exterior legs commuting | Explicit boundary/input/output equivalences; whole private stores survive, not only outputs or successful executions |
| Actual nested component coherence | Both source bracketings rebase to one compatible complete-model triple and hence the same quotient arrow | Fresh UIDs and nested programs need not be equal; no trace or process associativity follows |
| Injective-left partial-map connection | Quotient-invariant domains/values compose and agree with authoritative component admissibility and denotation | Component restriction is exactly `AtMostOneModels`; extraction is noncomputable and neither existence nor totality is asserted |
| Witness observation checks and ten release mutation controls | Checked private values, strict absence, empty metadata, nonconstant transport and unequal nested UIDs discriminate the specified faults | Copied-map controls are separate from donor substitutions; generic proofs and a shared interpreter are not independent arithmetic oracles |
| Certified source category and witness functor | Generated syntactic congruence, quotient category, genuine Mathlib functor, actual binary assembly and both nested-to-triple comparisons | Specified sealed matched-component/coordinate-wire presentation, not all Tensor Logic syntax, process laws or a faithfulness claim |
| Source observation checks and ten controls | Five donor families retain nonconstant wires, empty presence/metadata, complete hidden stores, strict/total neighbours and distinct nested private identities; four generic parities | Seven test-copy/donor observation controls and three theorem-level donor substitutions, not independent model semantics or mutations of generic soundness proofs |

The correspondence record reports successful full builds and branch review.
The executable modules
have a separate semantic proof layer, in addition to the fixture's
structural certificates. The recorded axiom audit verifies that the main
theorem and its strict/total instances depend only on `propext`,
`Classical.choice`, and `Quot.sound`, the allowed standard Lean axioms.
No new axiom, `sorry`, or unsafe proof shortcut was introduced.
This is not an axiom audit of every unrelated repository component.
The transport, static-composition, model-gluing and witness-category records report their full
builds, final reviews, namespace audits and particular mutation controls.
The original seven controls below are not the total across those later slices.

The seven mutation controls deliberately introduced faults in collection,
readiness, strict assembly, writer coverage, validated execution and
reference-only interpretation of `Audit`.
Each faulty version triggered its intended assertions; restoration was
byte-identical and the restored builds passed. This shows sensitivity to
these particular defects, not completeness of the test suite.

### 6.2. Composition results

Three independently built fragments contribute 1 and -1 to one
intermediate scalar and square its completed value. The collected
intermediate and squared result are both zero. After only the first
contribution, the intermediate is unavailable and the consumer is
disabled: it cannot square a subtotal of 1.

The tests also confirm that:

- Reversing or regrouping valid joins preserves the results.
- Distinct equal-valued contributions remain separate and both count.
- Missing writers, extra writers, overlapping capability claims, and
  duplicate tags are rejected.
- Structural closure cannot be followed by adding another fragment
  through the assembly interface.
- Publicly constructed closed payloads cannot bypass validation by
  omitting work or supplying premature collector ports.

**Conclusion:** an explicit writer contract provides a useful boundary
between assembling contributions and consuming completed values.
These tests do not establish arbitrary source-program composition.
The contract declares the complete permitted writer family; the
prototype does not discover unknown writers or automatically establish
source correspondence. The original proof supplies the fixture's match;
Section 6.8 adds a general static construction from component matches.
It still requires those leaf matches rather than inferring them from
arbitrary source programs.

### 6.3. Effect-sequencing results

The strict-effect case tabulates reciprocal over the two entries 2 and
0, then selects the first result. The whole computation fails because
the nonselected reciprocal of zero is demanded by array construction.
The neighbouring case with entries 2 and 4 succeeds and returns $1/2$.
Both outcomes match their reference executions, including the checked
events and intermediate snapshots.

A deliberately different select-first computation returns $1/2$
without evaluating the invalid second reciprocal. Its success is
recorded as evidence that the transformation is non-equivalent,
not as an accepted optimisation.

**Conclusion:** restricting successful values and restricting the work
performed by a partial computation are different operations. Strict
effect sequencing must preserve the required domain of definition;
the unrestricted reindexing equation in Section 3.3 is not valid
for this computation.

This is graph-level evidence for the distinction, but it still uses
the existing expression interpreter. It does not independently prove
that interpreter correct or establish a generic effect-sequencing law.

### 6.4. The combined test

The composition test adds an internal nonoutput contribution that reads
the completed intermediate and performs the strict array computation.
It waits while the intermediate is incomplete. Once ready, the
undefined nonselected reciprocal causes failure even though the
designated output has already been published as zero.

The all-defined neighbour completes, including its internal value
$1/2$. Replacing strict construction by the select-first shortcut
also succeeds, and is explicitly distinguished from the failing case.

**Conclusion:** correct composition must preserve both value
dependencies and completion/definedness obligations. Having the desired
output value available does not justify ignoring demanded internal work.

These composition-extension cases are checked against explicit
expectations; their two reference controls exercise the original runner.
The additional independent fixture below now compares the new composition
runner against an exact three-tensor reference program.

### 6.5. Independent reference validation

The new fixture independently declares a reference program and a fragment
contract for three scalar tensors: internal `Pre` and `Audit`, and output
`Out`. None is an input. Both computations collect contributions 1 and -1
into `Pre`, square the completed `Pre` into `Out`, and evaluate
`Pre` plus strict reciprocal-array selection into `Audit`.

| Case | Observed result in both executions |
| --- | --- |
| Array inputs 2 and 0 | Six events then failure at `Audit`; `Pre` and `Out` are published as zero, while `Audit` is unavailable and its occurrence remains pending |
| Array inputs 2 and 4 | Seven events then completion; `Pre = 0`, `Out = 0`, `Audit = 1/2`, with no pending occurrences |

The checks compare terminal outcomes, mapped ordered events, and every
recorded available/accumulator/pending snapshot. They also pin input and
output roles, the source-occurrence-to-writer mapping, and rejection of
unmapped or inconsistent observation identities. Observation errors
cannot count as matching results.

The reference does not supply the contract, and the contract does not
generate the reference program. Both deliberately share scalar operations,
typed expression helpers, and interpretation. The result therefore tests
independent composition and execution structure, not independent
implementation of arithmetic or partial-expression semantics.

The reference-only mutation replaced strict `Audit` evaluation with its
valid selected reciprocal, leaving the graph unchanged. It converted
the reference's failing case into success and broke the expected
parity checks. Restoration returned the source byte-identically and
the checks passed again.

These checks close the concrete independent-reference gap for the two
tested cases. They do not themselves prove general correspondence.
The separate proof now establishes a conditional general result and
supplies proved matches for these fixtures; neither claim establishes
complete coverage of contracts, source programs, or schedules.

### 6.6. What these results establish

Together, the results support the proposed separation of contribution
assembly, completed values, and computation effects. They strengthen
the case for interface-based logical execution without requiring
separately mutable accumulators and pending sets.

The independent validation has five consequences for the categorical
proposal:

1. **The writer interface has an external semantic check.** The contract
   is no longer tested only against its own expected result. A separately
   authored reference program agrees on contribution accounting,
   publication and failure. This supports the contract representation
   for the tested computation, not automatic contract correctness for
   arbitrary source programs.
2. **Completed-value boundaries preserve nonlinear placement.** Both
   executions collect the two `Pre` contributions before squaring its
   value. This supports distinguishing an open contribution interface
   from a readable completed value, rather than treating a subtotal
   as another interchangeable wire value.
3. **Definedness is part of the behaviour to preserve.** The strict case
   fails while its neighbour succeeds. Removing nonselected work on
   only the reference side changes failure to success and breaks parity.
   Thus an interpretation or rewrite must preserve demanded work's
   definedness, not merely numerical results on successful runs.
   This reinforces the domain-sensitive laws of Section 3.
4. **Whole-program completion is not an arbitrary graph convention.**
   `Audit` is genuinely internal in the independently declared reference,
   yet its failure prevents success after `Out` is published.
   The graph's obligation to finish internal work therefore agrees
   with the source's complete-model semantics in this test.
5. **A precise conditional operational correspondence is now proved.**
   The proof generalises the state relation to every finite source/contract
   pair satisfying its local match. It establishes related states,
   mapped traces, and matching outcomes without assuming those execution
   conclusions as premises. No global graded-action law is needed.

For leaf components, the retained caller obligation is consequently sharper: establish that
a source program and an independently supplied writer contract describe
the same typed occurrences, reads, destinations and completion
obligations and ordered priorities. The conditional theorem then proves
that their executions correspond; see the
[proof record](categorical_tensor_logic_proof_record.md).
Contract acceptance alone cannot establish this source-to-contract match.
For compatible composition, Section 6.8 derives the composite obligation
from the supplied local matches instead of requiring a new whole-match proof.

The important distinction is now **proved correspondence, static match
construction and categorical complete-model semantics versus open process
laws and broader source interpretations**. The proved results are general within their stated
premises, not limited to the tested examples. The witness bijection needs no
uniqueness; the denotation law explicitly needs at-most-one complete models
for both components. The target category laws and nested witness coherence
are proved separately in Section 6.10, together with source laws and an actual
functor for the specified sealed matched-component/wire presentation.
Automatic leaf-contract inference, broader source interpretations and ranked
phase/projection results remain unestablished.

Any priority pair satisfying the theorem's ordered matching condition is
covered. Equivalence across different priorities, arbitrary program
contexts, or all St/Br constructions is not established by this result.
Expression interpretation is still shared, and no memory-efficiency or
floating-point conclusion follows.

### 6.7. Kernel-checked conditional correspondence

The main declaration is
`IndexedOpenComposition.Correspondence.default_run_correspondence` in
[`IndexedCompositionValidated.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionValidated.lean).
It compares the actual default entry points `runChecked` and
`Program.Executor.runValidated`, including raw input validation.

Given a `SourceContractMatch`, the proved result supplies:

- The same first invalid-input rejection, or corresponding accepted runs.
- Matching complete, failed, or blocked outcomes.
- Equal ordered events after mapping source identities to graph identities.
- Related intermediate stores, pending occurrences, and accumulated values.
- Matching blocked-read diagnostics.

Separate proved corollaries exclude default-budget exhaustion and graph
readiness/collector mismatches. Successful completion yields the unique
complete reference model and its output denotation; reached undefinedness
excludes every model on those inputs. A supplied coordinate-rank
certificate additionally excludes blocking. Blocking alone still says
nothing about whether the equations have a model.

The theorem retains local source alignment as an assumption: roles,
occurrence identities, destinations, reads, body interpretation on every
partial store, and ordered priorities. Capability injectivity and exact
collector-fiber membership are derived from accepted closure and matching,
not extra assumptions about completed executions.

The proof is registered only with the non-default
`IndexedExecutionExperiment` target. It is not a production-backend
verification or a general categorical compositionality theorem.
Appendix A explains the argument and its observation conventions.

### 6.8. Kernel-checked static component composition

The public declarations `IndexedComponentComposition.compose_match` and
`compose` are in
[`IndexedComponentComposition.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentComposition.lean).
The former constructs a `SourceContractMatch`; the latter packages the
composite as another matched component.

Their inputs are two `MatchedComponent` values over finite decidable,
independently scoped `Declarations Unit` and a `Boundary`, using the fixed
rational registry and operations. A matched component
includes its existing source/contract match and exact whole-tensor ports.
The boundary supplies a bijection of every downstream input to every
upstream output, with a certified domain adapter for each pair; it does
not match by names or equal extents. These interfaces are defined in
[`IndexedComponentCompositionScope.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionScope.lean).

The composite retains all upstream tensors and a disjoint summand of
downstream defined tensors. Downstream inputs refer to the corresponding
upstream defined outputs, without additional external bindings, collectors
or copy computations. Checked even/odd identities separate private tensors,
tags and capabilities. All internal defined work, occurrence multiplicity,
zero-writer collectors and empty-port metadata survive.

The existing
[typed transport](../../leanncd/experiments/indexed_execution/IndexedComponentTransportEval.lean)
supplies body/read agreement on every partial store.
[Closure and assembly proofs](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionAssemble.lean)
derive canonical closure and full tensor coverage.
[Match construction](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionMatch.lean)
and [priority preservation](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionPriority.lean)
establish all nine fields. The caller supplies neither composite closure
nor a composite match, collector-fiber agreement, selected actions,
reached-store equality or execution agreement.

The
[constructed correspondence instances](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionCorrespondenceTest.lean)
then reuse `default_run_correspondence`, including an empty-interface
instance quantified over every raw binding. In the local producer/consumer
case, undefined nonselected reciprocal work still causes the six-event
private-`Audit` failure after publication of `Out`; its total neighbour
completes with seven events. Checked identity renaming changes numeric IDs,
not the required contribution/publication/failure sequence.
Expression helpers remain shared; this is not an independent numerical oracle.

No rank is required for static construction or correspondence. Appending
upstream priorities does not by itself prove that all upstream work finishes
before any downstream action. Rank stitching, that phase/projection theorem,
and process associativity/identities are still open. Complete-model gluing
and restricted denotation are the separate proved results in Section 6.9;
Section 10 records the proved witness-span category and denotational coherence.
The result belongs only to the non-default `IndexedExecutionExperiment`,
not a production backend or general category library.
See the [composition record](component_composition_record.md) for the exact
premises, fixture/control classifications, audits and completed gates.

### 6.9. Kernel-checked model gluing and restricted denotation

`IndexedComponentComposition.witnessesEquiv` in
[`IndexedComponentModelWitnesses.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentModelWitnesses.lean)
constructs an explicit bijection between complete composite models and
compatible component-model pairs. The downstream input depends on the
chosen upstream witness; this is not a product of two fixed model sets.
The witnesses are whole stores satisfying `Program.Models`, not output
assignments or distinct proof objects for the same store.

The scope remains finite decidable `Declarations Unit`, the fixed rational
registry and operations, and the existing `MatchedComponent`/`Boundary`
construction. The core theorem requires no rank, phase, execution success,
model existence or component uniqueness.

[`IndexedComponentModelInputs.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentModelInputs.lean)
defines inverse validated-input lifting/restriction, explicit `boundaryInput`,
whole-store restriction and `glueStore`. Every downstream input receives a
present whole value, including an empty one; noninput bindings remain absent.
The downstream store inverse needs boundary input agreement, supplied by a
compatible model, rather than holding for arbitrary unrelated store pairs.

[`IndexedComponentModelTransport.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentModelTransport.lean)
preserves and reflects every actual body's definedness and every collected
coordinate equation. Private tensors, repeated contributions, admitted
guards and zero-writer fibers remain in the model. Output-index/projection
transport separately retains empty-output identity.

The restricted corollaries `admInput_lift_iff`,
`admInput_restrictions_iff` and `denotation_successive` are in
[`IndexedComponentModelDenotation.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentModelDenotation.lean).
They require `AtMostOneModels` for both components on every validated input.
This compares whole model stores and asserts no existence. The domain
equivalence covers every validated composite input; the value theorem
transports successive denotation on exactly that admitted domain.
Neither theorem requires or constructs a composite rank certificate.

The
[local model tests](../../leanncd/experiments/indexed_execution/IndexedComponentModelLocalTest.lean)
exclude all strict-case composite models despite a satisfied visible
`Out = 0` equation, and retain total private `Audit = 1/2` in witness
round trips. The
[geometry tests](../../leanncd/experiments/indexed_execution/IndexedComponentModelGeometryTest.lean)
cover present empty inputs, empty output identity, nonconstant coordinate
transport and complete-store inverses.
The
[cycle tests](../../leanncd/experiments/indexed_execution/IndexedComponentModelCycleTest.lean)
prove the downstream-selection counterexample and preserve distinct internal
models with equal final outputs. These are logical model proofs, not
execution-completion assertions.

The [record](component_model_gluing_record.md) reports actual full builds,
namespace audits, all acceptance cases, unfiltered controls and adjudicated
whole-branch reviews. The result remains in the non-default
`IndexedExecutionExperiment`; it is not a general categorical library,
production-backend verification or an unrestricted partial-function law.

### 6.10. Kernel-checked categorical witness semantics

The public entry point is
[`IndexedWitnessSemantics.lean`](../../leanncd/experiments/indexed_execution/IndexedWitnessSemantics.lean),
with acceptance checks in
[`IndexedWitnessTest.lean`](../../leanncd/experiments/indexed_execution/IndexedWitnessTest.lean).
It belongs only to the non-default `IndexedExecutionExperiment`.
Component interpretation retains the finite decidable `Declarations Unit`,
fixed rational registry and explicit `MatchedComponent`/`Boundary` profile.

**Target category.**
[`IndexedWitnessInterface.lean`](../../leanncd/experiments/indexed_execution/IndexedWitnessInterface.lean)
defines `WholeInterface`: port tensor identities, injective UIDs, complete
sort/domain signatures and an exhaustive duplicate-free port roster.
`inputEquiv` reconstructs validated inputs, preserving tensor-level presence
even when a coordinate domain is empty; `outputEquiv` identifies whole output
families. Equal environment carriers do not identify interface metadata.

[`IndexedWitnessSpan.lean`](../../leanncd/experiments/indexed_execution/IndexedWitnessSpan.lean)
defines spans, `SpanIso` and quotient arrows. An isomorphism is a bijection
of apexes commuting with both environment legs, not an output-only relation.
Pullback congruence makes composition well-defined on the quotient;
`leftUnit`, `rightUnit` and `assoc` supply the ordinary Mathlib
`Category.{1} WholeInterface` instance. Objects and quotient homs live in
`Type 1`; each environment and apex lives in `Type 0`. Finite coordinates
do not imply a finite set of rational model stores or same-universe local
smallness.

**Composition-preserving interpretation.** `componentSpan` retains every
validated input paired with every complete `Program.Models` store. Its
left leg returns the input and its right leg projects the whole output.
No rank, execution success, existence or uniqueness hypothesis filters
this apex.
[`IndexedWitnessComposition.lean`](../../leanncd/experiments/indexed_execution/IndexedWitnessComposition.lean)
defines `boundaryEnvEquiv`, `compositeInputEquiv` and
`compositeOutputEquiv`. Graph spans express these administrative transports
without identifying distinct interface objects.
`allInputWiredEquiv` lifts model gluing over all validated inputs;
`compositeWiredIso` proves both exterior legs commute, and `composition_hom`
gives equality of the transported composite arrow and the wired component
arrows. Appendix A.9 spells out that equality.

**Actual nested coherence.**
[`IndexedWitnessCoherence.lean`](../../leanncd/experiments/indexed_execution/IndexedWitnessCoherence.lean)
constructs the boundaries needed by both nested source bracketings and proves
their environment-transport squares. `leftTripleIso` and `rightTripleIso`
take both rebased spans to the same `CompatibleTriple`, retaining all three
complete stores and both original boundary equations. `bracket_hom` follows.
This is stronger than target-span associativity alone: it compares the
actual component constructor's two bracketings. It does not equate their
fresh raw UIDs, nested declarations or source programs.

**Restricted partial maps.**
[`IndexedWitnessPartial.lean`](../../leanncd/experiments/indexed_execution/IndexedWitnessPartial.lean)
proves `component_injective_iff`: a component span's left leg is injective
exactly when it satisfies `AtMostOneModels`. Identity/graph spans and
pullback preserve injective left legs. Existence of a witness defines the
partial domain; its unique witness determines the output. Domain and value
are invariant under span isomorphism and obey successive-composition laws.
`component_composite_domain` and `component_composite_value` connect this
view to the existing admissibility and denotation theorems under both
component hypotheses. `RestrictedHom.partialOption` is noncomputable:
it uses classical witness choice, not an executable cyclic-model solver.
Absence of a witness yields `none`, never a fabricated zero value.

The checks retain hidden private-model multiplicity, strict `Audit` absence
versus its total neighbour, empty-port presence and UID metadata,
nonconstant boundary/exterior transport, and distinct nested UIDs with
preserved private values. The [release record](categorical_witness_semantics_record.md)
reports the full three-target build, namespace axiom audits, seven exact
copied-declaration parities, ten unfiltered expected mutation cycles with
byte-identical restoration, and adjudicated whole-branch reviews.
Copied-map observations and donor substitutions have different evidential
roles; neither replaces the generic proofs or independently verifies the
shared expression interpreter.

**Certified source presentation and functor.**
The public source entry is
[`IndexedSourceSemantics.lean`](../../leanncd/experiments/indexed_execution/IndexedSourceSemantics.lean).
[`IndexedSourceWire.lean`](../../leanncd/experiments/indexed_execution/IndexedSourceWire.lean)
defines a distinct `Object` wrapping the entire `WholeInterface`, avoiding a
competing category instance on target objects. A `Wire X Y` carries an explicit
bijection from Y's ports to X's ports and certified `Domain` coordinate/raw-axis
transport in that direction. Its environment equivalence reindexes coordinates
without changing rational values. Port pairing is explicit UID renaming, not
name or extent inference; an arbitrary value-changing environment bijection
is not administrative wire evidence. Identity, composition and inverse maps
are proved, including empty-coordinate ports. The actual input, boundary and
output wires induce precisely `compositeInputEquiv`, `boundaryEnvEquiv` and
`compositeOutputEquiv`.

[`IndexedSourceSyntax.lean`](../../leanncd/experiments/indexed_execution/IndexedSourceSyntax.lean)
defines typed `Term` identities, certified wires, actual `MatchedComponent`
leaves with supplied local matches, and sequential composition. The inductive
`Rel` is the generated equivalence/congruence for both units, associativity,
wire identity/composition/both inverses, actual binary assembly, both inherited
boundary squares and actual nested bracket comparison. It is not equality of
target denotations. The redundant bracket schema is sound independently;
both nested-to-triple source comparisons are derived without that schema.

[`IndexedSourceFunctor.lean`](../../leanncd/experiments/indexed_execution/IndexedSourceFunctor.lean)
proves every generator sound, descends composition to quotient `Hom`, installs
`Category.{1} Object`, and defines the actual Mathlib `semantics` functor.
Objects map to their underlying whole interfaces, leaves to the existing
complete-witness `componentSpan`, wires to `graphHom` of the certified induced
equivalence, and composition to target composition. No witness is filtered by
existence, uniqueness, rank or execution success.
`source_assembly` gives, in ordinary right-to-left notation,

$$
\operatorname{wire}(o)\circ L(\operatorname{compose}(A,B,b))
\circ\operatorname{wire}(i)
=L(B)\circ\operatorname{wire}(b)\circ L(A).
$$

Its interpretation invokes `composition_hom`, retaining both exterior legs.
`left_eq_triple` and `right_eq_triple` compare both actual constructor
bracketings to the same source composite using assembly, inherited boundary
squares, wire composition and source associativity. The separate bracket-schema
soundness invokes `bracket_hom` through explicit rebasing, not literal equality
of fresh UIDs, nested declarations or programs.

[`IndexedSourceTest.lean`](../../leanncd/experiments/indexed_execution/IndexedSourceTest.lean)
instantiates the category/functor laws and five donor families: nonconstant
wire/exterior transports, empty metadata/input presence, hidden complete-store
multiplicity, actual nested/private identities, and strict undefinedness versus
its total neighbour. Three exact copied coordinate maps and an inverse
observation have four separate universal parities. Ten observed controls
comprise seven test-copy/donor observations and three theorem-level donor
substitutions, not independent verification of shared model semantics or generic
proof mutations. Namespace audits use only standard axioms. The
[source record](categorical_source_functor_record.md) distinguishes prototype,
execution and release gates, findings and accounting.

The result is a denotational source category and functor for this finite
decidable, exact-rational, explicitly wired sealed matched-component
presentation. Source objects/homs remain `Type 1`, environments `Type 0`;
no finite rational-model-set, same-universe local-smallness or faithfulness
claim follows. Administrative source units are not event-free core programs.
Event-sensitive process composition, rank stitching, phase/trace projection,
broader source interpretations and backend refinement remain separate work.

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
| Complete-model relations and witness spans | Proved witness category and coherent component composition, including multiple or absent models | An execution policy or unconditional composition of unique-model partial functions |
| Certified matched-component source presentation | A quotient source category and genuine functor to complete-witness spans, including actual constructor assembly and nested transports | General St/Br or monoidal interpretation, event-sensitive process units, faithfulness or backend refinement |
| Temporal iteration and scans | Finite causal dependencies and independent batching outside the time axis | Independent execution along time or unrestricted feedback solving |
| Turi-Plotkin and extensions | A route to constructor/behaviour compatibility and observation-sensitive compositionality | The required syntax, rule law, and hypotheses without further work |
| PROP interpretations, parameters, and refinement | Model interpretation, parameter handling, and implementation correctness targets | Concrete kernel progress, memory safety, or numerical guarantees from value equality alone |

This section relates indexed and diagrammatic presentations to the
layers established above. Section 8 addresses behavioural compatibility
and implementation; Section 9 records proof status and remaining targets.

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

The scoped constructor in Section 6.8 now discharges the static closure
and matching obligations from local component matches and an explicit
boundary. It neither chooses that boundary nor allows downstream writers
to reopen the upstream family. This is a concrete semantic constraint on
gluing, not a general ACSet pushout or open-network interpretation theorem.

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

## 9. Proof status and remaining targets

### 9.1. Closed-graph/reference correspondence: conditional proof

Fix a finite well-formed reference program $P$ over the exact rational
numbers, denoted $\mathbb{Q}$, and the fixed `RationalReference` registry.
Let $S$ be its complete ordered priority schedule, $G$ a successfully closed
contract-based graph, and $\beta$ a raw input binding.

The implemented `SourceContractMatch` supplies these local conditions:

1. Common typed declarations, equal input roles and ordered tensor
   enumeration, and exact reference-output address coverage.
2. A bijection between actual source occurrences and writer-list positions.
3. Matching destinations and full ordered read lists.
4. Equal local `evalReady` results for every partial store, including
   readiness and undefinedness at the respective contexts.
5. Equality of the entire mapped reference priority list and canonical
   graph step list.

Successful closure is included in this match. The proof derives the
remaining capability-uniqueness and collector-fiber properties from it.
It does not assume equality of selected actions, traces, or final results.

**Proved statement:** with this match, the two default validated
executions correspond as described in Section 6.7. The result applies
generally to pairs satisfying those conditions, not just to the fixture.
No rank certificate is needed for correspondence or finite termination.
Ranking is used only for the additional no-blocking conclusion.

The independently authored fixture has `suppliedMatch other` for every
rational parameter `other`. Its strict and total execution instances are
applications of the general theorem, not Boolean parity results used
as assumptions.

The scope is the contract-based `IndexedOpenComposition.runChecked`
implementation. It does not assert a theorem about the older
`IndexedExecution.run`, arbitrary forged `Closed` records, source parsing,
or arbitrary unequal debugging budgets.

See the [proof record](categorical_tensor_logic_proof_record.md) for the
implementation inventory and audit. The
[design brief](categorical_tensor_logic_theorem_brief.md) explains the
original proof obligations; Appendix A gives the completed argument.

### 9.2. Sealed composition: model gluing proved, operational targets open

Let $P$ and $Q$ be upstream and downstream matched components, respectively,
in this finite exact-rational profile.
Let $X$ be $P$'s whole input interface and $Y$ its whole output interface.
Whole interfaces retain tensor identities, sorts and full coordinate domains,
including empty tensors; they are not merely lists of available addresses.

Write $I_Q$ for the downstream input tensors and $O_P$ for the upstream
output tensors. Supply a specified bijection $b:I_Q\cong O_P$.
For each input $i$, supply a certified adapter
$e_i:J_Q(i)\cong J_P(b(i))$, where $J_P(t)$ and $J_Q(t)$ denote the
respective declared coordinate domains of tensor $t$.
The adapters include extent-preserving axis correspondence and raw-policy
coherence, not merely equal cardinality.

**Static construction: proved.** Write $Q\circ_b P$ for the constructed
sealed composite along $b$. If $T_P$ is the upstream tensor type and $D_Q$
the downstream defined-tensor type, its declarations use $T_P\sqcup D_Q$,
where $\sqcup$ means disjoint union. The public constructor derives:

- Checked separation of private tensor, tag and capability identities.
- Upstream-only external inputs and downstream-only exterior outputs;
  every output remains a defined tensor rather than an input alias.
- All actual occurrences, full ordered reads and local body agreement.
- Complete collector coverage, including zero-writer fibers, without
  downstream writes to upstream results or upstream reads from downstream
  private values.
- All internal work and empty tensor metadata.
- Full ordered tensor validation and exact canonical priority matching.
- The composite `SourceContractMatch`, including successful closure.

No rank, composite match or execution-agreement premise is added.
The existing execution theorem now applies to this constructed match
rather than requiring a separate whole-composite reconstruction.
This does not infer leaf matches or provide residual inputs, fan-out,
open contribution ports or arbitrary domain adapters.

**Complete-model composition: proved.** Let $\eta_X$ be validated inputs on $X$,
and let $\rho_P,\rho_Q$ denote complete component-model witnesses.
Write $\eta_{\mathrm{comp}}$ for the corresponding validated composite input
constructed by `liftInput`: retain upstream bindings and leave downstream
defined tensors absent. `restrictInput` is its inverse, including
tensor-level presence for empty inputs.
Define $B_b(\rho_P)$ to be the downstream input environment transported
through the boundary by `boundaryInput`:

```math
B_b(\rho_P)(i)[p]=\rho_P(b(i))[e_i(p)],
\qquad p\in J_Q(i).
```

Every downstream input is present at tensor level, also for an empty domain;
noninput bindings are absent.
The implemented `witnessesEquiv` establishes the rank-independent bijection

```math
\operatorname{Models}(Q\circ_b P,\eta_{\mathrm{comp}})
\cong
\left\{
(\rho_P,\rho_Q)\ \middle|\
\begin{array}{l}
\rho_P\in\operatorname{Models}(P,\eta_X),\\
\rho_Q\in\operatorname{Models}(Q,B_b(\rho_P))
\end{array}
\right\}.
```

Both directions retain all private definedness and collected equations.
The pair retains both components' internal values rather than hiding them
before uniqueness is checked. No rank, existence or uniqueness premise is
needed, and the theorem is not restricted to reachable or successful stores.

**Partial-function composition: proved with extra hypotheses.**
`AtMostOneModels` means any two complete model stores are equal on every
validated input, without asserting that a model exists. With this property
for both $P$ and $Q$, `admInput_restrictions_iff` proves that the composite
has a unique model exactly when the upstream input is admissible and the
downstream input obtained from its output is admissible.

Let $f_P,f_Q,f_{Q\circ_b P}$ denote the respective unique-model partial
input-output meanings. `boundaryFromOutput` supplies downstream input from
an upstream output; `liftOutput` transports a downstream output into the
composite's output family. On exactly that admitted domain,
`denotation_successive` proves

```math
f_{Q\circ_b P}(\eta_{\mathrm{comp}})
=\operatorname{liftOutput}_b\!\left(
 f_Q\!\left(\operatorname{boundaryFromOutput}_b(f_P(\eta_X))\right)
\right).
```

The subscript $b$ fixes the same components and boundary as above.
This is a domain-and-value law under the two explicit component hypotheses,
not an unrestricted unique-model composition theorem or a totality result.

**Operational sequencing: still unproved.** A generic theorem that ranked
upstream execution completes before downstream execution, with projected
states and spliced traces, still needs rank stitching and a phase proof.
The first-enabled scheduler can skip blocked upstream work without those
additional hypotheses. Static sealing and model gluing are not runtime
completion.

Denotational associativity is now proved through compatible complete-model
triples and explicit interface reindexing. The semantic target has identity
spans; this does not supply source identities or process laws. Inserting a
core copy adds events, while input-as-output aliases violate the core's
defined-output rule.

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
This pattern is now realized by explicitly matched local components and
kernel-checked complete-model proofs in
[`IndexedComponentModelCycleTest.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentModelCycleTest.lean).
The composite uniqueness proof quantifies over every candidate store, not
just two listed witnesses. It is still not a claim that the direct executor
solves the cycle.

A companion hidden-model case preserves two distinct upstream stores
agreeing on their output boundary. Both extend to distinct complete
composite stores with equal whole final outputs. An output-only relation
would erase this distinction and cannot stand in for model uniqueness.

Consequently, the general composition structure should retain
**compatible complete-model witnesses**. One categorical representation
is a span: a set of complete models equipped with maps to its input
and output environments. Composing such spans pairs models that
agree at the shared boundary and retains the witnesses.

The witness-level composition is now packaged as a span-based categorical
interpretation for the specified scoped profile. Its target category laws
and nested denotational coherence are proved; relating it to process
observations remains separate work.
Unlike an output-only relation, it does not identify different internal
models prematurely.

For components with at most one model on every input, such as the
ranked fragment under the specified assumptions, this particular
obstacle disappears. The implemented domain and denotation corollaries now
make partial-function composition precise under explicit at-most-one-model
hypotheses for both components and the specified boundary conditions.

## 10. Categorization roadmap and progress

Categorization means specifying objects, morphisms, composition, identities
and an equivalence under which the category laws hold, then connecting that
structure to Tensor Logic's actual meaning. Calling a computation an arrow
or drawing a string diagram does not discharge those obligations.

The roadmap below is a logical dependency guide, not a claim that every
stage requires the previous stage's full implementation. The witness proof
completes the denotational target-category branch, including actual nested
component coherence and the restricted partial-map view. Source-category
packaging and ranked operational phase proofs remain different branches.

### 10.1. What each step buys us

| Step | Construction or obligation | What it buys us | Current boundary |
| --- | --- | --- | --- |
| 1. Fix interfaces and observations | Typed whole-tensor interfaces, explicit coordinate/identity transport, and a choice of value, witness or process equivalence | States exactly what may be connected and what information an equivalence may forget; empty tensors and private effects cannot disappear by accident | Whole interfaces and span-isomorphism equivalence implemented; event-sensitive equivalence remains open |
| 2. Give computations strict meaning | Partial expression interpretation, complete-model conditions and proved declaration/context transport | Separates undefinedness from unavailable data and numerical zero; preserves demanded internal work and nonselected array entries | Implemented substrate and proved transport |
| 3. Connect graphs to meaning | Local source-contract matches and graph/reference execution correspondence | Makes executable graphs accountable for occurrences, publication, failure and full intermediate data rather than only final outputs | Proved under supplied leaf matches and matched priorities |
| 4. Compose representations safely | Locally scoped components, typed boundaries, checked private identities, canonical closure and composite-match construction | Provides modular assembly without rebuilding a whole match, padding declaration universes or reopening an upstream writer family | Proved for the explicit sealed whole-tensor constructor |
| 5. Compose complete meanings | Model restriction/gluing and the restricted denotation law | Identifies composite models with compatible component witnesses, preserves internal multiplicity, and permits partial-function composition only with the stated uniqueness hypotheses | Proved; core gluing needs no uniqueness, restricted denotation needs both component hypotheses |
| 6. Package a semantic category | Witness spans over interface environments, span-isomorphism quotient, and composition interpreted as a pullback | Turns model gluing into a composition-preserving categorical interpretation with both exterior legs checked | Proved across all validated inputs with explicit boundary/exterior transports |
| 7. Prove category laws and units | Target identity spans and associativity; actual nested component comparison through compatible model triples | Makes repeated denotational composition coherent without treating extra computation events as no work | Target laws, graph-transport laws and nested coherence proved; source administrative syntax/units not supplied |
| 8. Connect process and implementation views | Ranked phase/projection and trace proofs, plus observation-sensitive frontend/backend interpretations or refinements | Explains when composition means sequential execution and which scheduling, representation or numerical transformations preserve the observations of interest | Open; the denotational proofs do not discharge these obligations |

The completed realization of Steps 6-7 is the **witness-span interpretation**.
For a whole-tensor interface $X$, write $\mathsf{Env}(X)$ for its space of
valid environments, retaining the declared tensor/domain information.
For a component $P:X\to Y$, let $W_P$ contain pairs $(\eta,\rho)$ of
validated input $\eta$ and complete model store $\rho$ on that input.
Its denotation is

$$
\mathsf{Env}(X)
\leftarrow
W_P
\rightarrow
\mathsf{Env}(Y).
$$

The left map returns the input environment; the right map projects the
whole model to the output interface. Composition forms the set of compatible
witness pairs over the explicitly transported boundary, a **pullback** in
sets. The all-input lift of the proved witness-gluing bijection supplies a span
isomorphism with the composite's model witnesses, commuting with both
exterior legs. Explicit graph spans carry boundary and exterior interface
transports. `IndexedWitnessSemantics` packages an ordinary category of
small-apex spans up to span isomorphism: objects and homs live in `Type 1`,
while each environment and complete-model witness apex lives in `Type 0`.
It does not claim same-universe local smallness.

Using spans up to **span isomorphism** means using a bijection of witness
sets that commutes with both boundary maps. This cannot collapse two distinct
compatible witnesses to one. It does not, however, imply equality of
execution events or coordinate-by-coordinate identity of different internal
representations. If those stronger observations matter, choose and justify
a stronger equivalence rather than silently assuming ordinary spans retain
them.

Both actual nested source bracketings are now compared, not just arbitrary
target spans: after rebasing their exterior interfaces, `leftTripleIso` and
`rightTripleIso` identify their complete witnesses with the same compatible
triple. The resulting `bracket_hom` is an equality of quotient arrows.
It retains model multiplicity and both original boundary equations without
equating fresh UIDs or claiming source-program equality.

In the at-most-one-model fragment, the left map is injective **if and only
if** `AtMostOneModels` holds. The proved restricted view makes witness
existence the partial domain and the unique witness's output the value;
both descend through span isomorphism and compose correctly. The component
domain/value theorems agree with authoritative admissibility and denotation
under both component hypotheses. This is noncomputable semantic extraction,
not model search or an unconditional unique-model law for cyclic programs.

The semantic identity is an identity span. If the source presentation itself
needs units, an administrative wire can represent the interface isomorphism
outside the core `Program` computation. A core copy may have identity
denotation but still adds writer/publication events; making its input a core
output violates `output_defined`. Denotational category laws therefore must
not be advertised as event-exact process laws.

### 10.2. Progress ledger

This ledger concerns the finite, exact-rational, explicitly wired experimental
profile developed here, not every Tensor Logic backend or every existing
categorical construction elsewhere in the repository.
**Proved** means the stated result has a checked implementation.
**Conditional** names retained hypotheses, not an unfinished proof.
**Proposed/open** means no result for this interpretation is claimed.

| Milestone | Current status | Evidence or remaining boundary |
| --- | --- | --- |
| Typed values, strict expressions and whole-model conditions | Implemented semantic substrate | [Core models](../../leanncd/LeanNCD/Semantics/Models.lean) and [strict interpretation](../../leanncd/LeanNCD/Semantics/Interpret.lean); internal occurrence definedness is required |
| Metadata-bearing whole-interface environments | Implemented with proved input/output equivalences | [Witness interfaces](../../leanncd/experiments/indexed_execution/IndexedWitnessInterface.lean); UID/sort/domain/port metadata and empty-input presence are retained, not quotiented by carrier equivalence |
| Declaration/context/coordinate transport | Proved | [Transport record](component_transport_execution_record.md); supplied certified adapters, not name-based or automatic domain matching |
| Graph/reference execution correspondence | Proved, conditional on a supplied local match | [Correspondence record](categorical_tensor_logic_proof_record.md); matched priorities and rational registry, no general backend claim |
| Static sealed composite and its match | Proved | [Composition record](component_composition_record.md); two local matched components plus an explicit whole-tensor boundary |
| Complete-model restriction/gluing | Proved, rank-independent | [Model-gluing record](component_model_gluing_record.md); full compatible witnesses, with no rank, existence or uniqueness premise |
| Successive partial-function domain and denotation | Proved, conditional on both components' `AtMostOneModels` hypotheses | [Denotation theorem](../../leanncd/experiments/indexed_execution/IndexedComponentModelDenotation.lean); uniqueness is not totality |
| Witness-span interpretation across all inputs | Proved, composition-preserving with explicit boundary and exterior transports | [Witness composition](../../leanncd/experiments/indexed_execution/IndexedWitnessComposition.lean); `allInputWiredEquiv`, `compositeWiredIso` and `composition_hom` retain whole private model stores and commute with both legs |
| Semantic target category laws and units | Proved | [Span category](../../leanncd/experiments/indexed_execution/IndexedWitnessSpan.lean); span-isomorphism quotient, pullback associativity and identity-span unit laws; graph spans supply administrative interface transports |
| Nested component denotational associativity | Proved after explicit interface reindexing | [Witness coherence](../../leanncd/experiments/indexed_execution/IndexedWitnessCoherence.lean); both actual bracketings correspond to the same compatible model triple, not equal raw IDs or programs |
| Injective-left partial-map interpretation | Proved; component restriction is exactly `AtMostOneModels` | [Restricted spans](../../leanncd/experiments/indexed_execution/IndexedWitnessPartial.lean); quotient invariance, closure under pullback and domain/value laws connect to authoritative admissibility and denotation; noncomputable extraction, not totality |
| Certified matched-component source category and functor | Proved for the specified generated presentation | [Source functor](../../leanncd/experiments/indexed_execution/IndexedSourceFunctor.lean); certified coordinate wires, source quotient laws, actual assembly/nesting and complete-witness interpretation with explicit transports |
| Core/process units | Open | Administrative source identities are not core computations; copies add events and aliases violate `output_defined` |
| Rank stitching and sequential phase/projection | Open | Individual ranked progress does not compose certificates or prove the whole upstream-before-downstream phase law |
| Event-sensitive process category | Open | For the proposed sealed-sequential interpretation, needs operational composition and a justified event/state observation equivalence, not merely span isomorphism |
| Categorical frontend/backend interpretation and refinement | Not established for this witness category | Existing syntax or plan/backend results are not automatically functors or refinements of this witness/process interpretation |

The current position is therefore **a proved denotational witness-span
category and a certified source-category functor**, not an event-sensitive
process category. See the [witness semantics record](categorical_witness_semantics_record.md)
and [source record](categorical_source_functor_record.md) for their separate
build, audit, control and review gates and limits. Rank/phase and trace-projection form the
independent operational task. General St/Br
packaging, numerical interpretation and implementation refinement must be
connected to the chosen semantics by their own arguments.

The ledger does not assign a percentage: a proof of model gluing and a proof
of process identity solve different problems, and their observations must
not be averaged into a single completion claim.

### 10.3. Remaining branches of the roadmap

There is no remaining target-span identity or associativity gap in this
profile. The next obligations depend on the intended claim:

- **Broader source interpretations:** the sealed matched-component source
  category and its witness functor are implemented in Section 6.10. Extending
  to broader interfaces, automatic leaf matches, St/Br, PROP or monoidal
  structure requires additional constructions and soundness arguments.
  The [source record](categorical_source_functor_record.md) gives the proved
  presentation and its limits; the handoff remains its historical goal brief.
- **Sequential process meaning:** stitch rank certificates, prove the
  upstream/downstream phase and state projections, then establish trace
  composition and process units under a specified observation equivalence.
  Compatible model triples alone cannot prove that upstream work finishes
  first, and semantic graph spans are not event-free core computations.
- **Frontend/backend connection and refinement:** relate St/Br or another
  source presentation to this witness target and prove the required
  implementation/observation laws. Value-level indexing, numerical
  approximation and physical storage correctness remain distinct claims;
  no general monoidal, graded or backend interpretation follows merely
  from the ordinary span-category laws.

These are open directions, not new implementation commitments. None requires
reproving the completed target-category laws or weakening strict definedness
and complete-witness retention to obtain a simpler output-only relation.

## Conclusion

The approach now has a plausible concrete centre:

> **Identity-aware index geometry, strict partial expression interpretation,
> multiplicity-preserving collection, and closed-writer dependency graphs.**

The original 93 executable checks and seven mutation controls provide
concrete validation. The subsequent Lean proofs establish conditional
execution correspondence and transfer the reference model, uniqueness,
denotation, and failure guarantees to matched graphs.

Typed transport and static sealed composition now construct composite
matches from locally matched components and explicit whole-tensor boundaries.
Complete-model restriction/gluing additionally proves the compatible-witness
bijection, and explicit at-most-one-model hypotheses give the exact
successive denotation domain and values.
The witness proof now packages those meanings into an ordinary span category,
proves composition preservation with both exterior legs, compares actual
nested component bracketings through compatible model triples, and derives
the quotient-invariant injective-left partial-map view. The certified source
presentation adds quotient source laws and an actual functor, connecting
actual binary assembly and both nested bracketings after explicit transports.
Their fixtures, audits, controls and reviews add evidence without
replacing the generic proofs or changing the language's strict partiality.

This is a sound operational bridge and a proved denotational source-to-witness
functor for the specified rational profile, not an event-sensitive
process category. Rank stitching/phase-projection followed by process
laws remains open with its own observation equivalence; Section 10 records
the different goals and current status.
Reproving execution correspondence or reconstructing an entire match for
each compatible composite is no longer necessary.

The choice of a broader categorical presentation remains open.
Automatic construction of leaf source-contract matches, broader interfaces,
broader source laws, process categorical laws and physical implementation refinement remain separate
obligations. The proved model-level composition law does not substitute for
an execution-phase or implementation-refinement theorem.

## Appendix A. How the correspondence proof works

### A.1. Start with a local match, not matching executions

The proof compares two representations of one computation. The reference
keeps published values, accumulators, and pending occurrences. The graph
keeps available values and individually produced contributions.

The supplied `SourceContractMatch` connects their static data:
roles, occurrence identities, destinations, footprints, body meanings,
and priority lists. In particular, it requires the matched bodies to
have the same `evalReady` result for every partial store.

That last condition is local expression agreement, not an assumption
that executions agree. Source and writer bodies may have different
index-context types. The proof does not need a generic syntactic
substitution compiler, but a future translator must justify the
body-agreement condition.

Accepted closure checks account for the complete capability family,
unique writer identities and destinations. Together with the source
occurrence bijection, these facts prove that each collector contains
exactly the writers for its source coordinate.
Thus no missing or duplicated contribution can be hidden behind a
separately assumed equality of aggregate results.

The relevant definitions are in
[`IndexedCompositionMatch.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionMatch.lean);
the derived capability and fiber facts are in
[`IndexedCompositionFibers.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionFibers.lean).

### A.2. Relate the two representations of unfinished work

Let $g$ denote a graph state and $c$ a reference running state.
Write $\mathcal{R}(g,c)$ for their state relation.
Using the occurrence set $O$, destination map $d$, and defined-address
set $C$ of Section 4, define:

- $\operatorname{Avail}_g$: the graph's partial available-value store.
- $\operatorname{Pub}_c$: the reference partial published-value store.
- $\mathsf{Done}_g\subseteq O$: source occurrences whose matched graph
  capability has produced a value.
- $\operatorname{Pending}_c\subseteq O$: pending reference occurrences.
- $v_o$: the recorded rational value of a produced occurrence
  $o\in\mathsf{Done}_g$.
- $\operatorname{Acc}_c(a)$: the reference accumulator at a defined
  address $a\in C$.

Use $\setminus$ for set difference and $\sum$ for finite rational
addition, with empty sum zero. The relation states:

$$
\operatorname{Avail}_g=\operatorname{Pub}_c,
$$

$$
\operatorname{Pending}_c=O\setminus\mathsf{Done}_g,
$$

$$
\operatorname{Acc}_c(a)=
\sum_{\substack{o\in\mathsf{Done}_g\\d(o)=a}}v_o.
$$

Equality of partial stores includes both availability and values.

These are not three copied runtime fields: the last two pieces of
reference bookkeeping are reconstructed from graph production.

The induction also carries a ledger invariant: produced capabilities
are valid and duplicate-free. Otherwise a lookup could hide extra
or repeated ledger entries. Available input coordinates are tracked
as present separately; the state relation alone should not be used
to justify a claim about arbitrary states missing their inputs.

Initially both stores contain the validated inputs, no writer has
produced anything, every source occurrence is pending, and accumulators
are zero. The relation and required invariants therefore hold initially.

### A.3. Show that each action preserves the relation

**A successful contribution.** Matching pending data and footprints make
the same writer/source occurrence ready. Local body agreement supplies
the same value. The graph records one fresh produced capability; the
reference removes its occurrence and adds that value to its accumulator.
The finite-sum equation is preserved.

**Publication.** A graph collector is enabled exactly when all its
capabilities are produced and the coordinate is unavailable. The derived
fiber correspondence makes this equivalent to the reference's completed
fiber and unpublished-coordinate conditions. The graph sum equals the
reference accumulator, so both publish the same value.
An empty fiber is the same argument with sum zero.

**Undefinedness.** If the ready body is undefined, both report the
corresponding occurrence as a terminal failure. Neither records a
successful contribution or returns a partial output as success.

Produced values remain recorded and published values remain unchanged
through subsequent successful steps. The proof concerns runs starting
from validated initial states, not invented states that merely resemble
some of the equations above.

The contribution and publication arguments are developed in
[`IndexedCompositionSteps.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionSteps.lean)
and
[`IndexedCompositionPublication.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionPublication.lean).

### A.4. Lift local agreement to complete executions

Equal eligibility is not enough to equate chosen events: two schedulers
could select different enabled actions. The match therefore relates the
entire ordered priority lists. Searching them for the first eligible
action selects corresponding steps. This is proved, not assumed.

Induction over the bounded runners then preserves the state relation,
ledger invariants, mapped events and terminal classification.
The complete key lists also yield equal default budgets. Successful
actions finish previously unfinished work, and failure is terminal,
so those default runs do not exhaust.

Full completion means all occurrences are consumed and all required
coordinates are published, not merely that outputs are available.
If unfinished work remains with no enabled action, both runners block,
with corresponding ordered missing-read diagnostics.

The raw state lists are not literally identical. The reference records
a final failed-state wrapper, whereas the graph returns a failed outcome
without appending a second snapshot of its unchanged data.
`referenceSnapshots` normalises this representation difference.
The undefined event and located failure are retained.

The trace/result relation is `ExecutionCorrespondence` in
[`IndexedCompositionCorrespondence.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionCorrespondence.lean).
The public default-entry-point theorem is then obtained in
[`IndexedCompositionValidated.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionValidated.lean).

### A.5. Transfer the meaning of successful and failed runs

Once executions correspond, the existing reference correctness theorems
can be reused rather than reproved.

- Graph completion supplies a corresponding reference completion and the
  same whole store. `completed_model` yields its model, uniqueness and
  output-denotation properties.
- Graph failure supplies the corresponding reference undefined occurrence.
  `failed_has_no_model` excludes every reference model on those inputs.
- `ranked_not_blocked` adds a rank certificate to exclude blocking.
  Without that extra premise, blocking carries no model-existence claim.

Output denotation uses the reference program's tensor roles and signatures.
This includes empty output tensors, whose identities cannot be recovered
from the graph contract's address-only output list.

These are semantic corollaries, not premises that the program already
has a model or that execution already succeeds.

### A.6. Establish genuine instances and audit the proof

[`IndexedCompositionFixtureProof.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionFixtureProof.lean)
constructs `suppliedMatch other` for every rational fixture parameter
`other`. It proves the actual source/writer bijection, body-context
agreement, closure, roles and priority match.
The strict and total execution instances apply the general theorem.
They are not proofs that a stored Boolean parity check equals true.

The six-event failure and seven-event completion are also retained as
executable regression observations. The tests and mutation controls
remain useful for protecting behaviour even though they are not the
proof's logical foundation.

[`IndexedCompositionProofAudit.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionProofAudit.lean)
audits the graph/proof and fixture-proof namespaces and reports the main
theorem's dependencies. The recorded result uses only the allowed standard
axioms named in Section 6.1.

The generality is conditional: finite typed declarations, exact rationals,
the fixed primitive registry, local body agreement and matched priorities.
The proof does not construct matches for arbitrary source programs or
establish a PROP interpretation, St/Br action, general component
composition law, numerical approximation theorem or physical-memory
refinement.

### A.7. Construct a match from component matches

The new static constructor supplies the correspondence proof's premise
compositionally, rather than proving another pair of runners equivalent.
It starts with two local `SourceContractMatch` values and an explicit
whole-tensor boundary.

1. **Keep ownership local.** Retain the upstream declaration universe and
   only downstream defined tensors in a disjoint summand. A downstream
   input maps to its specified upstream output. No ambient tensors create
   extra input or collector obligations.
2. **Transport identities and expressions.** Checked even/odd maps separate
   tensor UIDs, tags and capabilities. The occurrence bijections combine
   without dropping duplicate contributions or guard-admitted valuations.
   Typed expression transport preserves ordered full footprints and
   `evalReady` on every partial store, including ready undefinedness.
3. **Derive closure.** `ClosureFacts.of_close` extracts the component
   invariants. The concrete assembly proves the structural premises needed
   for `close_assembled`, including coverage of all noninput coordinates,
   valid reads and disjoint capability families. The public constructor's
   caller does not supply those premises as a disguised composite-closure
   assumption.
4. **Preserve the complete priority equation.** Collector lookup and step
   transport commute with the checked identity maps. Appended component
   keys map to the canonical composite steps in their original order.
   Equal eligibility or equal final values are not used as substitutes.
5. **Assemble the certificate and reuse execution correspondence.**
   `compose_match` constructs all nine match fields; `compose` retains
   exact whole ports, including empty outputs. Applying
   `default_run_correspondence` then supplies mapped events, related
   intermediate states and terminal outcomes for the composite.

The declarations are in
[`IndexedComponentComposition.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentComposition.lean).
The closure infrastructure is in
[`IndexedComponentClosureFacts.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentClosureFacts.lean)
and the assembly/priority derivations are in
[`IndexedComponentCompositionAssemble.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionAssemble.lean)
and
[`IndexedComponentCompositionPriority.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionPriority.lean).

The
[composed instances](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionCorrespondenceTest.lean)
include the six-event strict failure and seven-event total completion from
local producer/consumer matches, retaining private `Audit`. Empty interfaces,
zero-writer fibers, collisions and unequal-axis adapters provide further
discriminating cases. The interpreter remains shared.

This constructs a static matched component, not a runtime phase theorem,
or by itself a categorical identity/associativity law. Complete-model gluing
and categorical witness semantics are the separate proved results below;
source and operational obligations remain as stated in Sections 9.2 and 10.3.

### A.8. Restrict and glue complete-model witnesses

Model gluing works directly with complete stores and equations, rather than
assuming the runners reach those stores.

1. **Transport validated inputs separately from stores.** `liftInput` and
   `restrictInput` are inverse on validated inputs. `boundaryInput` uses the
   specified output/input coordinate adapters and supplies a present value
   for every downstream input, including an empty one.
2. **Split whole-store model obligations.** `outcome_upstream` and
   `outcome_downstream` reuse complete interpretation transport.
   `admEnv_components` preserves and reflects all actual bodies' definedness.
   `collect_upstream`, `collect_downstream` and `equations_components`
   preserve every finite contribution sum and coordinate equation,
   including private tensors and zero-writer fibers.
3. **Restrict and glue compatible stores.** Restriction uses the existing
   address embeddings. `glueStore` keeps upstream values and downstream
   defined values; downstream input agreement makes their boundary
   consistent. The inverse is not asserted for arbitrary incompatible pairs.
4. **Build the witness bijection.** `models_restrict_iff` and
   `models_glue_iff` establish both model directions.
   `witnessesEquiv` uses the store inverse laws to retain the full dependent
   pair of model subtypes. Proof irrelevance identifies proof terms for the
   same store, not different stores with the same output.
5. **Project outputs only after preserving complete witnesses.**
   `outputIndexEquiv` and output-projection transport retain whole output
   tensors, including empty ones. The two `AtMostOneModels` hypotheses
   separately give the exact admissibility-domain and successive-denotation
   corollaries; they do not add existence to the core gluing theorem.

The input/store operations are in
[`IndexedComponentModelInputs.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentModelInputs.lean),
the semantic transport in
[`IndexedComponentModelTransport.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentModelTransport.lean),
the witness inverses in
[`IndexedComponentModelWitnesses.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentModelWitnesses.lean),
and the restricted functional law in
[`IndexedComponentModelDenotation.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentModelDenotation.lean).

The strict `Audit` case has no complete composite model even when its visible
`Out` equation is satisfied. Its total neighbour retains the private audit
value in complete-store round trips. Empty and nonconstant-axis cases test
presence and coordinate transport; cyclic cases demonstrate both downstream
model filtering and hidden internal multiplicity. These are logical
complete-model conclusions, not execution-completion claims.

No rank, phase, model existence or uniqueness premise appears in the core
witness theorem. The categorical packaging and its laws are proved separately
below; runtime phase/projection, trace splicing and source/process laws
remain unproved.

### A.9. Turn model witnesses into categorical semantics

Write $X_P,Y_P$ for component $P$'s whole input/output interfaces, and
$W_P=\{(\eta,\rho)\mid\rho\in\operatorname{Models}(P,\eta)\}$ for its
all-input complete-model witnesses. Its span is
$F_P=(\mathsf{Env}(X_P)\xleftarrow{\ell_P}W_P
\xrightarrow{r_P}\mathsf{Env}(Y_P))$, with input reconstruction and output
projection as its legs.

1. **Choose the exact arrow equivalence.** A span isomorphism is an apex
   bijection $h:W\cong W'$ satisfying
   $\ell'\circ h=\ell$ and $r'\circ h=r$. Quotient by these isomorphisms,
   not by equality of visible outputs. Different complete private stores
   remain different witnesses; proof terms for the same store do not.
2. **Prove well-defined composition and units.** For spans
   $F:X\to Y$ and $G:Y\to Z$, composition has apex
   $\{(w,v)\mid r_F(w)=\ell_G(v)\}$ and exterior legs
   $\ell_F(w),r_G(v)$. Apex isomorphisms induce isomorphisms of these
   compatible pairs, so composition descends to the quotient.
   The identity span has apex $\mathsf{Env}(X)$ and both legs identity.
   Removing its determined witness proves both unit laws. Reassociating
   $((w,v),u)$ to $(w,(v,u))$ preserves both compatibility equalities and
   exterior legs, proving target associativity.
3. **Compare the actual component constructor.** Let
   $e_b:\mathsf{Env}(Y_P)\cong\mathsf{Env}(X_Q)$ be boundary transport,
   $i_b:\mathsf{Env}(X_P)\cong\mathsf{Env}(X_{Q\circ_b P})$ the exterior
   input transport, and
   $o_b:\mathsf{Env}(Y_{Q\circ_b P})\cong\mathsf{Env}(Y_Q)$ the exterior
   output transport. For an equivalence $e$, its graph span has apex its
   source environment, left leg identity and right leg $e$.
   If $[F]$ denotes a quotient arrow, `composition_hom` proves, with
   ordinary right-to-left composition,

   $$
   [\operatorname{graph}(o_b)]\circ[F_{Q\circ_b P}]
   \circ[\operatorname{graph}(i_b)]
   =
   [F_Q]\circ[\operatorname{graph}(e_b)]\circ[F_P].
   $$

   This is the all-input witness-gluing bijection together with **both**
   commuting exterior legs. The transports are essential: tagged composite
   interfaces are not literally the original interfaces.
4. **Compare actual source bracketings.** Construct the inherited boundaries
   for $(P,Q),R$ and $P,(Q,R)$, then prove their transport squares.
   After rebasing, both nested spans are isomorphic to the span of triples
   $(w_P,w_Q,w_R)$ satisfying the two original boundary equalities.
   Its legs are $\ell_P(w_P)$ and $r_R(w_R)$.
   `leftTripleIso`, `rightTripleIso` and `bracket_hom` establish the comparison
   without equating nested UIDs, declarations or source programs.
5. **Restrict to partial maps only with injective left legs.** The partial
   domain is $\{x\mid\exists w,\ell(w)=x\}$; injectivity makes the witness
   unique and its output $r(w)$ well-defined. Span isomorphisms preserve
   this domain and value, and pullback preserves injectivity and successive
   domain/value composition. For $F_P$, injectivity is equivalent to
   `AtMostOneModels P`. Under this restriction, witness existence agrees
   with authoritative unique-model admissibility; the output agrees with
   denotation. Both component hypotheses connect the composite view to
   successive denotation, without asserting existence or giving a solver.

These steps are implemented in the
[span](../../leanncd/experiments/indexed_execution/IndexedWitnessSpan.lean),
[composition](../../leanncd/experiments/indexed_execution/IndexedWitnessComposition.lean),
[coherence](../../leanncd/experiments/indexed_execution/IndexedWitnessCoherence.lean),
and [restricted partial-map](../../leanncd/experiments/indexed_execution/IndexedWitnessPartial.lean)
modules. They prove denotational category laws and constructor compatibility.
The identity graph/span is a semantic wire, not a core identity computation;
span isomorphism gives no schedule, event or phase equality.

6. **Present the source and descend a genuine functor.**
   [`IndexedSourceSyntax`](../../leanncd/experiments/indexed_execution/IndexedSourceSyntax.lean)
   generates typed identities, certified coordinate wires, matched leaves and
   sequential terms over distinct whole-interface source objects. Its inductive
   congruence states units, associativity, wire laws, actual assembly and
   inherited boundary/nesting schemas rather than denotation equality.
   [`IndexedSourceFunctor`](../../leanncd/experiments/indexed_execution/IndexedSourceFunctor.lean)
   proves each schema sound using the target results above, descends the quotient
   category and supplies `semantics`, an actual Mathlib functor from `Object`
   to `WholeInterface`. The leaf arrow retains the same all-input complete store;
   certified wire maps and both actual nested-to-triple derivations retain
   explicit interface transports. This denotational source completion does not
   supply rank, phase, trace, event-sensitive units or backend refinement.

## Notation reference

Symbols are defined on introduction. This table collects the recurring
ones; it does not add assumptions beyond their definitions.

| Notation | Meaning |
| --- | --- |
| $P,Q$ | Core programs or components |
| $\rho$ | Complete candidate tensor environment |
| $\eta,\eta_X$ | Validated complete input environment, optionally restricted to interface $X$ |
| $\eta_{\mathrm{comp}}$ | Validated composite input obtained by lifting the upstream input |
| $\beta$ | Raw input binding awaiting validation |
| $\rho(T)[p]$ | Entry at coordinate $p$ of tensor $T$ in environment $\rho$ |
| $\mathsf{Env}(X),W_P$ | Valid environments for a whole-tensor interface and complete-model witnesses of a component across its inputs |
| $X_P,Y_P,F_P,\ell_P,r_P$ | Component input/output interfaces, its complete-model span, and that span's input/output legs |
| $[F],\operatorname{graph}(e)$ | Span-isomorphism quotient arrow and graph span of an explicit environment equivalence |
| $e_b,i_b,o_b$ | Boundary environment transport and composite exterior input/output equivalences |
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
| $S,G$ | Complete priority schedule and canonical closed graph |
| $g,c,\mathcal{R}(g,c)$ | Graph state, reference running state, and their proved state relation |
| $\operatorname{Avail}_g,\operatorname{Pub}_c$ | Partial available and published stores |
| $\mathsf{Done}_g,\operatorname{Pending}_c$ | Produced mapped source occurrences and pending source occurrences |
| $\operatorname{Acc}_c(a),v_o$ | Reference accumulator at defined address $a$ and recorded value of produced occurrence $o$ |
| $T_P,D_Q,\sqcup$ | Upstream tensor identities, downstream defined tensor identities, and disjoint union |
| $I_Q,O_P,b,e_i$ | Downstream inputs, upstream outputs, explicit boundary bijection, and certified coordinate adapters |
| $J_P(t),J_Q(t)$ | Declared coordinate domains of tensor $t$ in the respective component |
| $\rho_P,\rho_Q$ | Complete component-model witnesses |
| $B_b(\rho_P)$ | Downstream input environment obtained by explicit boundary transport |
| $f_P,f_Q,f_{Q\circ_b P}$ | Unique-model partial input-output meanings for the respective programs |
| $\operatorname{boundaryFromOutput}_b,\operatorname{liftOutput}_b$ | Boundary input and composite output transport for the fixed components and boundary |
| $Q\circ_b P$ | Statically constructed sealed composite along boundary $b$ |
| $\circ,\operatorname{id},\cong$ | Composition, identity, and bijective correspondence, as typed in each use |
