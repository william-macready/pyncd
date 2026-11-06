# Tensor Logic through the categorical lens: a refined assessment

[Semantics contents](README.md) |
[Tensor Logic specification](tensor_logic_semantics.md) |
[Categorical background](categorical_operational_semantics.md)

## Summary

The Tensor Logic specification changes the assessment substantially.
It already supplies the operational model that an examination of the einsum
paper alone left us needing to choose. It also supplies mathematical
arguments connecting that model to program meaning and to compiled execution.

The most useful categorical approach is therefore **not to replace the
reference machine with a newly invented evaluator**. It is to explain and
organise the existing layers:

> Coordinate maps route values; partial functions interpret expressions;
> additive collection combines contributions; a transition system controls
> when complete results become readable; simulations justify implementations.

Much of this categorical organisation is already described in the
[companion guide's category-theoretic account](lean_executable_semantics_path_part_3.md).
The principal remaining question for a Turi-Plotkin treatment is more specific:

> Can we describe meaningful ways of constructing Tensor Logic programs or
> execution plans, and prove that those constructions are compatible with
> the reference machine's behaviour?

A coalgebraic description of the existing machine is straightforward.
A genuine bialgebraic account of source-program composition requires more
work, especially around shared writers and completion barriers.

This is an assessment, not a change to the specification or a new proof.
Statements about existing results below refer to the specification and its
[proof-status table](tensor_logic_semantics.md#proof-status-and-numbered-results).
That table distinguishes general contracts from results formalised for
particular profiles. This assessment does not independently recheck Lean
proofs or claim broader compiler coverage.

## 1. What the specification already settles

### 1.1. The language is more than a tree of contractions

The [core syntax](tensor_logic_semantics_part_ii.md#13-core-syntax-and-binding)
includes scalar expressions, finite reductions, array construction and
selection, and registered scalar or array primitives. Statements can have
affine read and write indices and index-dependent guards.

A primitive is a deterministic mathematical operation with a declared
domain of definition and no hidden reads or side effects. An array primitive
can require an entire input slice. These facilities cover nonlinear
operations as well as pure einsum.

The [scope and domain rules](tensor_logic_semantics_part_ii.md#14-structural-well-formedness)
also matter: variables have identities, domains can be empty, and a
well-typed primitive application need not be defined on every input value.
Numerical shape alone is not the whole type information.

### 1.2. Statements generate contributions, not successive assignments

A source statement generates one contribution occurrence for each
admissible assignment of its contribution variables. An occurrence retains
both its statement identity and that assignment. Two equal-valued
occurrences are still two contributions.

For example, two copies of a statement contributing an input value of 3 to
one coordinate produce 6 under ordinary addition, not 3. Affine writes
can also send several occurrences from one statement to the same coordinate.

The final coordinate value combines all its contributions. If no occurrence
targets a declared defined coordinate, its value is the additive identity.
A missing input, by contrast, is an error, not an implicit zero.

These are already explicit in
[tagged occurrences](tensor_logic_semantics_part_i.md#92-tagged-contribution-occurrences)
and [contribution collection](tensor_logic_semantics_part_iii.md#19-contribution-collection).
They must survive any categorical reformulation.

### 1.3. Meaning is defined before execution

The [denotational semantics](tensor_logic_semantics_part_iii.md#20-program-models-and-functional-denotation)
describes complete tensor environments satisfying the collected equations.
An environment supplies values for every declared tensor, not just outputs.
A **model** is such an environment that extends the supplied inputs, makes
every actual contribution defined, and satisfies those equations.

A program can have no model, one model, or several models. The specified
partial input-output function is defined only when the complete model is
unique. Agreement of outputs across several models is not substituted for
that condition.

Cyclic equations are allowed at this level. They are not silently
interpreted by iteration from zero or by choosing a least solution.

### 1.4. The reference machine already gives an execution policy

The [reference configuration](tensor_logic_semantics_part_iv.md#24-machine-configurations-and-initialization)
separates three things:

- Published coordinate values, which are complete and immutable.
- Accumulators, which may contain only some contributions.
- Pending contribution occurrences, which have not yet been consumed.

The [execution rules](tensor_logic_semantics_part_iv.md#25-execution-rules-and-terminal-outcomes)
allow any ready occurrence to contribute, publish a coordinate only after
all its occurrences are consumed, and explicitly fail when a ready
occurrence is undefined.

An accumulator cannot be read as though it were a completed tensor value.
This publication condition is a **completion barrier**: a boundary that
separates collecting a result from making it available to consumers.

The machine is nondeterministic only in its choice among enabled actions.
Each ready expression has a deterministic mathematical interpretation.
Its evaluation can include a whole reduction or array primitive; the
reference steps do not expose every arithmetic or memory operation.

### 1.5. Schedule independence is already justified at the right level

The specification distinguishes several results:

- Any successful reference run determines the unique complete model.
- Reaching an undefined-operation failure excludes every model.
- Every run is finite, because successful steps consume an occurrence or
  publish a previously unpublished coordinate.
- For the **coordinate-ranked fragment**, dependencies admit natural-number
  ranks that strictly increase from a read coordinate to its destination.
  This ensures progress: maximal runs cannot become dependency-blocked.

Consequently, for ranked programs, every maximal run either succeeds with
the same complete model or explicitly fails. Different failing schedules
may identify different undefined occurrences. Identical traces or failure
snapshots are not claimed.

These conclusions come from
[read stability](tensor_logic_semantics_part_iv.md#233-stable-evaluation-from-a-partial-store)
and [conservation, termination, and correspondence](tensor_logic_semantics_part_iv.md#26-conservation-termination-and-correspondence).
They do not require a fairness assumption: every reference step makes
bounded progress or ends in failure. Stopping a scheduler early is not a
maximal run.

This is much stronger than merely having a proposed evaluation order.

## 2. A small example that the categorical account must preserve

Consider scalar tensors, written with the empty coordinate list `[]`.
Let `A` and `B` be inputs with values 1 and -1, respectively. Let `Pre`
be an intermediate tensor and `Out` the designated output.

In the following source notation, `=` introduces a contribution rather
than an overwriting assignment:

```text
Pre[] = A[]
Pre[] = B[]
Out[] = relu(Pre[])
```

The primitive `relu` returns its argument when that argument is positive,
and zero otherwise.

After consuming the first contribution to `Pre`, its accumulator can hold
1. But `Pre` is not yet readable. Only after the second contribution has
been consumed can the completed value 0 be published. `Out` then becomes 0.
Reversing the first two contribution steps gives the same result.

There are two distinct ways to get the wrong answer:

1. Read the accumulator early and apply `relu` to 1.
2. Move `relu` inside collection, applying it separately to 1 and -1,
   then adding the results.

Either produces 1 instead of 0. The first violates publication readiness;
the second changes the location of a nonlinear operation.

This [existing operational example](tensor_logic_semantics_part_iv.md#271-an-accumulator-is-not-a-readable-intermediate)
shows why the execution cannot be explained solely as a network of linear
tensor maps. It also shows why the set of writers must be known before a
result is declared complete.

## 3. The algebraic organisation is already largely present

### 3.1. Reads and collection have different directions

For this explanation, fix one scalar carrier, named $K$. Write $\oplus$
for its contribution-combining operation and $0_K$ for that operation's
identity. Assume that combination is associative and commutative. These
data form a **commutative monoid**. Multiple scalar sorts use the same
construction separately on their respective carriers.

Let $I$ and $J$ be finite coordinate sets. Write $K^I$ for the set of
functions from $I$ to $K$, and similarly for $K^J$. These are coordinate
families of values.

A coordinate map $f:I\longrightarrow J$ induces a read operation
$f^*:K^J\longrightarrow K^I$, defined by

$$
f^*(v)=v\circ f,
$$

where $v:J\longrightarrow K$ is a value family and $\circ$ denotes
function composition. The superscript $*$ names this operation,
called **pullback**. It changes the coordinate domain by reading the
old family through $f$.

Collection goes in the other direction. Let $O$ be a finite set of tagged
occurrences, $A$ a finite set of destination addresses, and
$d:O\longrightarrow A$ their destination map. For a family of contribution
values $v:O\longrightarrow K$, define
$d_!:K^O\longrightarrow K^A$ by

$$
d_!(v)(a)=
\bigoplus_{\substack{o\in O\\d(o)=a}}v(o).
$$

Here $a\in A$ is a destination, $o\in O$ ranges over occurrences,
and $\bigoplus$ denotes finite combination using $\oplus$. An empty
combination is $0_K$. The subscript $!$ names this operation, called
**additive pushforward**.

Thus reads pull values back along coordinate maps, while writes collect
contributions forward along destination maps. Distinct occurrences with
equal values remain distinct terms in the combination.

### 3.2. This explains the connection to einsum without redefining it

Fix a complete environment $\rho$, meaning an assignment of values to all
declared tensors, on which every actual contribution body is defined.
Let $v_\rho:O\longrightarrow K$ assign each occurrence its body value
in that environment. The subscript records this dependence on $\rho$.

The collected family of values at defined addresses is then

$$
d_!(v_\rho).
$$

For pure einsum, the body values are products of operand values pulled
back to a common index-assignment domain. The final output is a
pushforward along the output-coordinate map. The specification already
develops this in
[canonical fiber semantics](tensor_logic_semantics_part_ii.md#172-canonical-fiber-semantics).

Moreover, the companion guide already presents this organisation and
records identity, composition, grouping, and occurrence-relabeling laws
for pushforward. These are existing foundations, not new proposals in
this assessment. See
[finite additive pushforward](lean_executable_semantics_path_part_3.md#32-finite-additive-pushforward-covariance-and-multiplicity).

The useful next step would be to package and reuse these laws as a common
interface for collection-preserving transformations, rather than invent
another definition of tensor contraction.

### 3.3. Nonlinear and partial primitives belong to another layer

The map $d_!$ preserves additive combination. Arbitrary registered
primitives need not do so.

Let $E$ be a well-typed expression with value type $\tau$, and let
$V_\tau$ be the set of values of that type. Let $\mathsf{Env}$ denote
the set of complete tensor environments and $D$ the set of admissible
index assignments for this expression.

Its interpretation has the form

$$
\operatorname{eval}_E:
\mathsf{Env}\times D\longrightarrow V_\tau+\{\bot\}.
$$

Here $\operatorname{eval}_E$ names the interpretation function,
$\times$ is Cartesian product, and $+$ is a tagged disjoint union.
The symbol $\bot$ denotes an undefined result, not a scalar zero.

This is a way to represent a **partial function** as a total function:
either return a value or explicitly return undefinedness. Composing such
interpretations propagates undefinedness. It does not turn the result
space into another semiring.

The [strict interpretation](tensor_logic_semantics_part_iii.md#18-expression-interpretation-and-definedness)
therefore matters categorically as well as operationally:

- Multiplication by zero does not suppress an undefined operand.
- Selecting an array entry still requires the whole constructed array.
- A guard can remove an occurrence before its body is interpreted.
- An empty reduction interprets no body instances.

The companion guide already explains this
[partial-map organisation](lean_executable_semantics_path_part_3.md#33-partial-maps-organize-expression-definedness).
It is a better home for general primitives than a category requiring
every morphism to preserve addition.

One relevant wording caveat is worth isolating. The
[scalar-sort discussion](tensor_logic_semantics_part_i.md#24-scalar-sorts)
calls the Boolean-to-any-sort conversion a semiring homomorphism.
The usual embedding of false as 0 and true as 1 is not an additive
homomorphism into the real numbers: Boolean OR combines true with true
to give true, whereas real addition combines 1 with 1 to give 2.
Such a conversion can still be a registered primitive; it should not
be assumed to preserve semiring structure. This assessment leaves the
specification unchanged.

## 4. The existing machine has a straightforward coalgebraic description

### 4.1. Fix the program before describing its states

Fix a structurally valid core program $P$ and a validated input environment
$\eta$. The symbols $P$ and $\eta$ name the program and supplied inputs.
Let $S$ be the set of reference configurations reachable from their
initial state, including terminal failed configurations.

A running state has the specification's form

$$
(\sigma,\alpha,U),
$$

where $\sigma$ is the partial store of published values, $\alpha$ is the
map of accumulators, and $U$ is the set of pending occurrences.
The letter $\alpha$ here denotes the specification's accumulator map,
not an algebra structure map.

The fixed program determines the occurrence identities, destinations,
read footprints, and primitive meanings. This avoids pretending that
states are untyped collections of arbitrary tensor entries.

### 4.2. Make alternative next steps explicit

Let $\mathcal{L}$ be a set of action labels recording contribution,
publication, and undefined-operation steps, including the relevant
occurrence or address identity. Let $\mathsf{R}$ be a set of tagged
terminal observations distinguishing:

- Success with the complete environment.
- Undefined-operation failure with its diagnostic information.
- Dependency blocking.

A failure observation can retain the specified occurrence and state
snapshot; forgetting that information would be a separate observation
choice.

For any set $X$, define a behaviour endofunctor $B$ by

$$
BX=\mathsf{R}+\mathcal{P}_f(\mathcal{L}\times X).
$$

The notation $\mathcal{P}_f(Y)$ means the set of finite subsets of a set
$Y$. The right branch therefore records a finite set of possible labelled
next states. For a function $h:X\longrightarrow Y$, the function $Bh$
leaves terminal observations and labels unchanged and applies $h$ to
each successor state.

The reference rules define a single morphism in the underlying category
of sets, namely the coalgebra structure map

$$
b:S\longrightarrow BS.
$$

Here $b$ returns either the state's terminal observation or its enabled
labelled transitions. It is not being asserted to be a structure-preserving
map between two coalgebras.

Branching is finite because a fixed program has finitely many occurrences
and defined addresses. The functor's finite subsets describe alternative
execution choices, not numerical summands: this use of sets does not
deduplicate contributions inside a run.

This is a direct categorical packaging of the existing rules, including
their deliberate scheduling freedom. A deterministic scheduler chooses
one of the legal next steps; it does not change the specification.

### 4.3. This packaging does not add new correctness theorems

The construction is mathematically straightforward. It does not establish
computability of arbitrary exact-real primitive operations or domain
tests, and it begins after structural and input validation.
In particular, an empty input tensor must still have been supplied even
though it contributes no coordinate entries to the initial store.

Nor does calling the transition system a coalgebra prove soundness,
termination, or schedule independence. Those properties follow from
the existing read-stability, conservation, and ranking arguments.
The coalgebra provides a common language in which to organise them.

The finite execution argument also means that a final-coalgebra
construction is not required merely to define the outcome of a chosen
maximal reference schedule.

## 5. Why this is not yet a full Turi-Plotkin account

### 5.1. A syntax algebra and a state coalgebra are not automatically a bialgebra

An expression syntax has constructors. The machine state space has
transitions. These are different carriers, and placing the two descriptions
side by side does not produce the compatibility law of a bialgebra.

For a candidate Turi-Plotkin formulation, let $\mathsf{Syn}$ name a
proposed syntax endofunctor and $\mathsf{Beh}$ a proposed behaviour
endofunctor on the same chosen category. Let $\mathsf{Term}$ denote
the functor forming finite syntax trees with possible variables.
These are structures to be constructed, not already-proved properties
of the reference machine.

Assuming the required products and free syntax are available, one
standard target is a natural transformation

$$
\lambda:
\mathsf{Syn}(\mathrm{Id}\times\mathsf{Beh})
\Longrightarrow
\mathsf{Beh}\,\mathsf{Term}.
$$

Here $\lambda$ names the proposed rule transformation, $\mathrm{Id}$ is
the identity functor, the product pairs a child state with its behaviour,
and $\Longrightarrow$ denotes a natural transformation.

The transformation would explain how constructor arguments and their
immediate behaviours determine the behaviour of the whole.
Its naturality and induced compatibility would need proofs.
The fixed-program coalgebra in Section 4 is not, by itself, this
uniform construction over a language.

Encoding every complete configuration as an unrelated syntax constant
would obscure the intended problem rather than solve it: it would say
little about meaningful program composition.

### 5.2. The difficult interface is shared contribution ownership

The publication rule asks whether **every occurrence targeting a
coordinate** has been consumed. That is information about the complete
program's writers, not merely the next step of one expression child.

Likewise, two otherwise independent source fragments may contribute to
the same tensor. Combining the fragments changes when that tensor is
complete. A fragment that publishes its local subtotal cannot simply
keep doing so after another writer is added.

Thus we must distinguish:

1. Combining contributions whose joint completion is still pending.
2. Composing blocks whose complete outputs are already available.

These are not interchangeable notions of composition.

A useful starting restriction would be **sealed blocks**: components
with declared inputs and outputs, distinct internal identities, and
an explicitly closed set of writers for each published result.
Additional writers would have to be combined before sealing, possibly
through a separate collector block.

This is a proposed interface discipline, not a restriction already
imposed on the whole source language. More general open-program
composition must describe writer ownership, identity renaming,
dependencies, and closing the contribution interface explicitly.
Only after specifying such a composition can we ask whether an
equivalence is preserved by it.

### 5.3. Scope information is richer than numerical shape

A uniform syntax category should retain the variable context,
admissible index domain, value type, tensor identities, and primitive
registry information used by the structural judgments.

Binders change the context in which their bodies are interpreted.
Treating them as ordinary untyped constructors would lose freshness,
substitution, and the difference between renaming a variable and
identifying two variables.

A context-indexed family of expression sets, with coherent renaming
and substitution operations, is a plausible setting. Its precise
construction remains work to do; saying "use a syntax functor" does
not discharge it.

This does not mean that higher-order operational semantics is
automatically required. The core passes scalar and finite array
values to primitives, not arbitrary program functions to other
programs. Index binding needs a careful account of scope, but it is
not by itself higher-order program execution.

### 5.4. The unrestricted denotation remains a model relation

For the full core, the model relation must remain distinct from the
partial function selected by uniqueness. A category whose morphisms
are only partial input-output functions would not, by itself, retain
all the specified model information.

In particular, the equation example with contributions `T[] = X[]`
and `T[] = 2 T[]` has the unique real solution `T = -X`, but the
reference machine can block waiting for the self-read. Other cyclic
examples have many models or none.
See [cyclic equations](tensor_logic_semantics_part_iii.md#214-three-different-cyclic-equation-systems)
and [dependency blocking](tensor_logic_semantics_part_iv.md#275-a-cycle-can-block-with-or-without-a-model).

The natural first operational target is therefore the ranked fragment,
while retaining the general model relation as the declarative meaning.
A more general solver would need its own existence, uniqueness, and
execution arguments. Neither a final coalgebra nor an iteration slogan
selects the intended solution automatically.

## 6. Choose the equivalence before claiming compositionality

The specification already supports agreement of successful results under
different legal schedules. That is not equality of step-by-step behaviour.

With the observations of Section 4, behaviours can reveal:

- Which occurrence is consumed first.
- When each coordinate is published.
- Which undefined occurrence is reported.
- The associated failure snapshot.

Different legal schedules can differ in these observations. Statement
permutation also requires transporting occurrence identities, not merely
comparing the same printed labels.

For result correctness, the existing theorems are the appropriate tools:
successful runs yield the unique complete model, and ranked programs
have the stated maximal-run correspondence. We should not replace
those conclusions with an unproved assertion of strong bisimilarity.

If internal scheduling steps are to be hidden, we need to specify
which terminal observations remain visible. In particular, collapsing
all semantic failures into one outcome is different from preserving
the first undefined occurrence and its snapshot.

Weak or trace-based extensions of mathematical operational semantics
may help once a precise composition and observation policy are chosen.
They have their own hypotheses; hiding labels does not automatically
make every desired equivalence a congruence.
See [abstract congruence criteria for weak bisimilarity](https://arxiv.org/abs/2010.07899).

For a future account of parallel execution, it may also be useful to
identify schedules that differ only by exchanging independent actions.
For example, two already-ready, successful contributions can be
consumed in either order: neither changes published reads, and their
accumulator updates commute. The existing
[batched-accumulation lemma](tensor_logic_semantics_part_v.md#321-why-exact-batched-accumulation-refines-individual-steps)
already captures the corresponding finite-group result. This should
not be generalised silently to identical failure histories.

## 7. Compiled execution calls for refinement, not literal step equality

The specification already provides the right direction here:
[a representation relation and a forward simulation with stuttering](tensor_logic_semantics_part_v.md#312-initial-states-and-successful-step-simulation).
A **representation relation** records how concrete memory represents a
logical reference configuration. **Stuttering** means that a physical
storage step may leave the logical configuration unchanged.

One compiled command can match:

- Several reference contribution steps.
- Several publication steps.
- A sequence of both.
- No reference steps, for a representation-only storage change.

Thus a simple requirement that one concrete step equal one reference
step would be wrong. The mathematical relation also retains proof
information that need not exist in physical memory; it should not be
replaced without justification by a total function extracting the
whole reference state from memory alone.

The [existing refinement contracts](tensor_logic_semantics_part_v.md#31-simulation-and-compiler-correctness)
also require failure matching, concrete progress, terminating kernels,
and output decoding. Forward simulation alone is not enough.

The [storage model](tensor_logic_semantics_part_v.md#30-concrete-states-and-logical-representation)
separates logical identity from physical location. Retirement and
buffer reuse do not erase logical history or permit kernels to read
ghost values. Whole-history outputs require retaining every requested
slice, even if a terminal-only computation could reuse two working
buffers.

Implementation errors such as resource or kernel faults are separately
distinguished from undefined source operations. They do not prove that
the source equations have no model. The compiled correspondence has an
explicit error-free profile.

A categorical reformulation should preserve these distinctions and
package the simulation structure, not demand a stronger equality that
valid implementations do not satisfy.

## 8. What would actually improve the approach?

### Preserve the existing semantic architecture

The current separation of equations, logical execution, and physical
refinement is a strength. It already prevents storage policy from
silently defining the source language. There is no categorical reason
to discard it.

The most useful refinements would be:

1. **Make the existing categorical interfaces explicit.** Reuse the
   pullback, additive-pushforward, and partial-expression layers,
   including their different preservation laws.
2. **Package the reference rules as a coalgebra.** Keep all legal
   schedules and distinguish success, undefinedness, and blocking.
   Treat a concrete scheduler as a separate legal-step selection.
3. **Choose a modest compositional target first.** A typed language
   of certified plan actions, or sealed ranked source blocks, is a
   clearer first target for an operational rule law than unrestricted
   shared-writer source composition. It would establish a result
   about that target, not automatically about the whole source language.
4. **Build the missing scope and interface structure before invoking
   a general theorem.** Specify the syntax category, behaviour
   functor, composition, rule transformation, and required invariants.
5. **Lift existing simulation contracts into reusable composition
   results.** Keep batching, fusion, storage-only steps, failure, and
   concrete progress visible in the statement.

Machine arithmetic remains a separate extension. The reference model
uses exact values, while floating-point combination can depend on
reduction order. The specification already identifies this boundary;
a categorical presentation must not turn exact schedule independence
into an unsupported bitwise guarantee.

### Revised difficulty assessment

| Objective | Assessment |
| --- | --- |
| Explain pure einsum as coordinate pullbacks followed by additive pushforward | Already present in the specification and companion guide |
| Explain general expression interpretation using partial functions | Already present |
| Describe the reference transition system as a coalgebra | Straightforward packaging of existing rules |
| Establish the recorded reference-machine correctness properties | Existing arguments and profile-specific formalised results; not consequences of the packaging alone |
| Give a binding-aware constructor semantics for expressions | Plausible, but requires an explicit indexed syntax and its laws |
| Obtain a Turi-Plotkin-style compositionality theorem for certified plans or sealed ranked blocks | A reasonable next target, not a completed result |
| Obtain that theorem for arbitrary open shared-writer source composition | The main unresolved interface-design challenge |
| Replace compiled refinement by exact equality of one-step behaviours | Inappropriate for batching, fusion, and storage steps |
| Execute general cyclic equations or obtain floating-point rewrite guarantees | Separate extensions with additional semantic choices |

## Conclusion

The refined perspective is not that Tensor Logic lacks operational semantics.
It already has a carefully separated operational and refinement model,
with substantial correctness results recorded for specific profiles.

The next categorical contribution should explain **which constructions
of programs and plans preserve that model**, rather than supply a
competing evaluator.

The central issue is not tensor contraction alone. It is the interaction
between **multiplicity-preserving contributions, complete publication,
partial or nonlinear operations, and shared dependencies**.

That is where a meaningful Turi-Plotkin account would earn its keep.

## Sources and reading order

1. [Tensor Logic specification and proof status](tensor_logic_semantics.md).
2. [Core syntax and pure-einsum foundations](tensor_logic_semantics_part_ii.md).
3. [Denotational semantics](tensor_logic_semantics_part_iii.md).
4. [Reference execution](tensor_logic_semantics_part_iv.md).
5. [Compilation and refinement](tensor_logic_semantics_part_v.md).
6. [Existing categorical organisation](lean_executable_semantics_path_part_3.md).
7. [Algebra and coalgebra background](categorical_operational_semantics.md#appendix-a-algebras-and-coalgebras).
8. Turi and Plotkin,
   [Towards a Mathematical Operational Semantics](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf),
   1997.
9. Klin,
   [Bialgebras for Structural Operational Semantics: An Introduction](https://www.cs.ox.ac.uk/people/bartek.klin/papers/tcs11.pdf),
   2011.
