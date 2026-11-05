# An effect-sensitive indexed model of Tensor Logic: Lean prototype design

[Semantics contents](README.md) |
[Tensor Logic specification](tensor_logic_semantics.md) |
[Earlier categorical assessment](categorical_tensor_logic_assessment.md)

## Status and purpose

This note describes an experiment, not a replacement semantics or a
generally proved implementation. It explains the proposed idea, the
design of a small executable Lean prototype, and the evidence that would
justify continuing with it.

The prototype will use ordinary Lean data and executable functions. It will
not require new correctness theorems, category instances with coherence
proofs, new axioms, or `sorry`. Reusing existing proved definitions and
validation infrastructure is compatible with that restriction.

Sections 1-10 describe the design and its intended requirements.
Section 11 records the first implemented prototype and observed checks;
these are finite experimental results, not a general correspondence proof.

## 1. The question we want to answer

The existing specification separates mathematical meaning, logical
execution, and physical implementation. The experiment retains that
separation. It asks whether a different presentation of logical computation
would make the middle layer easier to compose and implement:

> Can explicit contribution interfaces, completed-value interfaces, and
> strict effect sequencing make the reference machine's bookkeeping a
> derived execution strategy rather than the primary definition?

There are two failure modes for this investigation:

- The new presentation changes Tensor Logic's meaning to obtain simpler
  categorical laws.
- It preserves meaning but merely renames stores, accumulators, and pending
  sets without simplifying composition or correctness obligations.

The prototype must test against both possibilities.

The [St/Br framework](../graded_prop.md) is a source of useful constructions,
not a conclusion we presuppose. Its separation of coordinate geometry,
typed operations, lifting, and causal iteration should be reused where
helpful. A successful prototype need not realise every proposed graded-PROP
axiom, nor replace that framework wholesale.

## 2. What must not change

The [Tensor Logic specification](tensor_logic_semantics.md) remains the
behavioural contract. In particular:

1. A source statement generates tagged contribution occurrences. Duplicate
   statements and colliding destinations retain their multiplicity.
2. Guards and finite domains determine which occurrences exist before their
   bodies are evaluated. Nonexistent instances do not fail.
3. Collection combines contributions on their declared coordinate domains.
   Empty collections yield the additive identity; omitted inputs are not
   supplied by that rule.
4. An incomplete subtotal is not a readable tensor value.
5. Primitive operations retain their declared domains and placement.
   Nonlinear operations cannot be moved across collection without a
   separate justification.
6. Array construction and selection retain strict definedness: selecting
   one coordinate does not bypass failures elsewhere in the demanded array.
7. Every actual contribution and every defined coordinate participates in
   whole-program completion, including internal tensors not returned as
   outputs.
8. The unrestricted denotation remains a relation between inputs and
   complete models. The unique-complete-model criterion is not replaced
   by uniqueness of outputs.
9. Direct execution remains restricted to supported dependency forms.
   Rejecting an unsupported cycle does not establish that it has no model.
10. Logical identities are not physical locations. This first experiment
    does not introduce buffer reuse or floating-point arithmetic.

These are drawn from
[core statements](tensor_logic_semantics_part_ii.md#135-core-contribution-statements),
[strict interpretation](tensor_logic_semantics_part_iii.md#18-expression-interpretation-and-definedness),
[model semantics](tensor_logic_semantics_part_iii.md#20-program-models-and-functional-denotation),
and [reference execution](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics).

## 3. The proposed mathematical organisation

### 3.1. Value families are not computations producing value families

Let $I$ be a finite index set and $A$ a set of values. Write $A^I$ for
the set of functions from $I$ to $A$. Such a function is an indexed family
of values.

For another finite index set $J$, a coordinate map
$r:I\longrightarrow J$ induces a read operation
$r^*:A^J\longrightarrow A^I$ by

$$
r^*(v)=v\circ r.
$$

Here $v:J\longrightarrow A$ is a family, $\circ$ is function composition,
and the superscript $*$ names pullback by precomposition.

This is the familiar geometric content of reindexing. A checked affine
expression is one way of presenting such a map. Guarded index domains may
be subsets of rectangular domains; the prototype need not assume that
every such domain is already an ordinary St shape.

Now let $B$ be a set of result values. Define
$\operatorname{Result}(B)=B+\{\bot\}$, where $+$ is a tagged disjoint union
and $\bot$ denotes undefinedness. A partial computation can be represented
by a total function

$$
f:A\longrightarrow\operatorname{Result}(B).
$$

Applying this function independently at each coordinate gives a function
named $f^I$:

$$
f^I:A^I\longrightarrow\operatorname{Result}(B)^I.
$$

That result is a family of individual results. It is not yet a successfully
constructed complete array. A separate function,
$\operatorname{sequence}_I$, imposes the strict completion requirement:

$$
\operatorname{sequence}_I:
\operatorname{Result}(B)^I
\longrightarrow
\operatorname{Result}(B^I).
$$

It succeeds exactly when every member succeeds. An empty family succeeds
with the unique empty value family. Strict batch evaluation is therefore
the composite

$$
\operatorname{batch}_I(f)=\operatorname{sequence}_I\circ f^I.
$$

The prototype should make this distinction executable. Restricting the
index set before sequencing can remove a failure; restricting afterward
cannot. Thus the usual total-function reindexing equations must not be
assumed for every partial computation.

The proposed benefit is not a different result convention. It is making
the existing strictness visible in the compositional interface.

### 3.2. Contributions have identities and destinations

For a fixed finite core program, let $O$ denote its set of actual tagged
contribution occurrences, and let $C$ denote its set of defined coordinate
addresses. An address identifies a tensor together with its coordinate.
Let $d:O\longrightarrow C$ be the destination map.

For this first experiment, fix one exact scalar carrier $K$, with
associative, commutative contribution combination $\oplus$ and identity
$0_K$. These operations form a commutative monoid. The intended executable
carrier is Lean's exact rational arithmetic; multiplication and partial
primitives belong to expression interpretation rather than the collection
interface.

For each occurrence $o\in O$, let $R_o$ denote its read footprint. The
notation $K^{R_o}$ means assignments of scalar values to those addresses.
The occurrence's body determines a partial function

$$
g_o:K^{R_o}\rightharpoonup K.
$$

The hooked arrow $\rightharpoonup$ means a partial function.
[Read stability](tensor_logic_semantics_part_iv.md#233-stable-evaluation-from-a-partial-store)
justifies this factorisation: the full environment matters only through
the required coordinates, including its effect on definedness.

This is not permission to evaluate the body before its entire footprint
is available.

### 3.3. A collector has a closed family of input contributions

For a coordinate $a\in C$, define its writer family
$O_a=\{o\in O\mid d(o)=a\}$. The braces describe the occurrences whose
destination is $a$.

Its collector is the total function $\mu_a:K^{O_a}\longrightarrow K$
defined by

$$
\mu_a(v)=\bigoplus_{o\in O_a}v(o).
$$

Here $v:O_a\longrightarrow K$ supplies one value per occurrence, and
$\bigoplus$ denotes finite combination using $\oplus$. An empty
combination is $0_K$.

The writer family consists of identities, not distinct numerical values.
The collector cannot expose a readable result until every member has
succeeded. Its closed input interface expresses the publication barrier.

An open contribution interface can still accept writers. A completed-value
interface cannot. Combining open contributions and composing completed
values are different operations.

### 3.4. Causality is a separate capability

The first executable graphs are acyclic at coordinate level.
Independent coordinates can be evaluated in either order; a bounded
history has explicit dependencies on earlier coordinates.

This does not turn recurrence into independent broadcasting. It also
does not interpret arbitrary feedback as a solver. A cyclic source
program can retain its model relation while being rejected by this
prototype's execution admission.

The symbolic representation of finite histories can later use the
existing [temporal grading](../graded_prop.md#34-the-temporal-grading-and-making-scan-first-class).
The first experiment should establish behaviour on small concrete
histories before adding a symbolic scan representation.

## 4. Why the first prototype is deliberately not a category library

The categorical ideas determine the proposed interfaces and laws, but
the experiment should begin with executable representations:

- Finite, identity-labelled coordinate domains.
- Typed value and contribution ports.
- Explicit writer closure.
- Strict result assembly.
- Dependency-respecting graph execution.
- Comparisons with the existing reference semantics.

It should not begin by implementing a general PROP, fibration, actegory,
restriction category, or double category. Such packaging is justified
only after we know which operations and laws the prototype actually needs.

In particular, the prototype is not required to exhibit a global natural
transformation expressing every Tensor Logic constructor. It tests a
candidate foundation from which a sound compositional statement might
later be formulated.

## 5. The evidence we seek

There are three different levels of evidence:

1. **Semantic fidelity:** the graph and reference machine agree on
   successful complete environments and the specified terminal outcomes.
2. **Structural improvement:** interface construction prevents meaningful
   errors, such as reading an unsealed collector, rather than detecting
   exactly the same mistakes with renamed pending-set tests.
3. **Reusable reasoning:** at least one useful transformation has a
   compact, reusable preservation argument, while a tempting invalid
   transformation is explicitly rejected or shown to change behaviour.

Finite execution and executable checks can provide evidence for these
claims on the tested instances. They do not prove a general correspondence
theorem, a universal property, compiler correctness, or optimality of the
chosen categorical foundation.

## 6. The smallest executable Lean design

### 6.1. Start from an existing core program

The initial prototype should be parameterised by an already constructed
`LeanNCD.Semantics.Program` over the selected rational registry and an
already constructed complete reference `Schedule` for that program.
These supply the finite tensor, coordinate, occurrence, and enumeration
data. Donors over a different declaration or primitive registry cannot be
inserted into that schedule unchanged.

The graph's scalar values use the existing exact-rational registry.
Its initial nonlinear and partial witnesses should therefore use square
and reciprocal. ReLU is useful conceptually, but it is not an operation
we should claim is available in that particular reference registry.

Do not begin with a new parser, a replacement tensor declaration system,
or a generic St/Br interpreter. Keep the existing identity distinctions.
For generic core fixtures, use their actual tensor and occurrence
identities; use source UIDs when the donor actually carries them, not an
invented UID interpretation of every finite carrier.

### 6.2. Separate structural closure from runtime completion

Two different events must not share an ambiguous meaning of "seal":

- **Structural closure:** the builder fixes the complete writer family
  for a coordinate. No later writer may be added.
- **Runtime completion:** every writer in that closed family has produced
  a successful value, so the collector can expose its result.

The builder can accept open fragments of the program's known occurrence
family, combine them by disjoint identity-preserving union, and close
their destination interfaces. Closing checks that the declared writers
match the original program's complete fiber.

For the first prototype, this is composition of fragments of one fixed
program. It is not yet a semantics for arbitrary independently authored
open source programs. That larger interface problem remains a possible
follow-up.

The checks should reject duplicate occurrence identities, missing or
misrouted writers, incompatible ports, reads presented as completed values
before their collector interface is established, and attempts to extend
a structurally closed writer family.

### 6.3. Use two runtime node kinds

Each graph contains:

1. **EvaluateOccurrence:** a node with an occurrence identity, its entire
   read footprint, its destination, and its body interpretation.
2. **CollectCoordinate:** a node with a defined coordinate identity and
   the complete list of writer ports fixed by structural closure.

No separate operational "finish program" node is needed initially.
Whole-program completion can be a terminal predicate checked by the
runner.

The state records:

- Available input and completed-collector values.
- Successfully produced occurrence values.
- A terminal failure, if one has occurred.

A missing value and a produced zero are different states.
The prototype should not maintain a separately mutated pending set or
accumulator map: those are derived for comparison with the reference.
It may retain produced values after collection; this is a logical
prototype, not a memory-saving representation.

### 6.4. Keep occurrence evaluation atomic

An evaluation node becomes eligible only when it has not already
produced a value and every coordinate in its strict footprint is
available. It then evaluates its whole body:

- On success, record one produced value for that occurrence.
- On undefinedness, terminate with its occurrence identity and the
  preceding graph snapshot.
- Never convert an unavailable read to zero or to undefinedness.

This granularity is deliberate. Suppose one subexpression is undefined
but another required read can never become available. Evaluating the
undefined subexpression early could report a failure for an occurrence
that is never ready in the reference machine. That is not a harmless
change in evaluation order.

Decomposing bodies into primitive-level graph nodes is deferred until
there is an explicit account of the whole-footprint readiness barrier
and the resulting failure observations.

### 6.5. Collection creates availability

A collection node becomes eligible only when its coordinate is not
already available and every writer port has a produced value. It
combines exactly those values and makes the result available.

The graph performs no partial publication. A zero-writer collector can
complete without evaluating any body. An input coordinate cannot be
the destination of a collection node.

Eligibility should depend on the node's explicit ports, not a call to
the reference machine's `attempt` or `select` function.

### 6.6. Terminal observations are part of the design

Distinguish:

| Observation | Meaning |
| --- | --- |
| Complete | Every actual occurrence has succeeded and every defined coordinate is available |
| Failed | A ready occurrence's body is undefined |
| Blocked | Work remains, but no node is eligible |
| Invalid input | Required tensor-level input presence was not established |
| Unsupported | A requested feature has no justified prototype representation or adapter |
| Exhausted | A debugging/exploration budget was reached; the experiment is inconclusive |
| Invalid graph | A structural or adapter contract was violated |

These are conceptual observation categories, not promised Lean constructor
names. They must not collapse into one another.

The reference validates presence at tensor level, including zero-coordinate
inputs. The candidate must check the same requirement independently from
the raw binding. Typed core input values already carry coordinate-domain
information; testing arbitrary malformed external shapes would require
an additional, separately scoped untyped input interface.

The initial runner need not construct rank proofs. Normal progress tests
use ranked examples; deliberately unranked diagnostic examples may run
and report blocking without attempting to solve their equations.
Successful behaviour on the ranked examples is not a claim that the
prototype recognises the whole ranked fragment.

## 7. Reuse the reference implementation without hiding its proof boundary

GPT Sol's read-only API investigation identified the following reuse
surface. These are source-inspection findings, not compiled or executed
prototype observations.

### 7.1. The reference oracle

The relevant entry points are in
[`ReferenceExecutor.lean`](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean),
in the `LeanNCD.Semantics.Program.Executor` namespace:

- `runValidated` validates raw tensor-level input presence, then runs the
  executor and retains the admitted input and execution result.
- `run` executes with its existing finite initial budget and does not
  require a rank certificate.
- `runFuel` is a debugging facility, not evidence that arbitrary exhaustion
  means semantic failure.

An execution result exposes its terminal outcome and typed events.
The ordinary reference outcomes distinguish `complete`, `failed`,
`blocked`, and `exhausted`. The ranked no-blocking theorem is a
separate result requiring a rank certificate; we do not need to
manufacture that certificate merely to run a comparison.

The exact scalar interpretation is in
[`RationalReference.lean`](../../leanncd/LeanNCD/Semantics/RationalReference.lean):
`Carrier`, `ops`, `registry`, and the `Primitive.reciprocal` and
`Primitive.square` operations.

### 7.2. "No proofs" is a real construction constraint

The existing core is not entirely proof-free data:

- `Program` carries an `output_defined` obligation.
- Typed reads carry in-bounds/admission evidence.
- The reference `Schedule` carries duplicate-freedom and enumeration
  coverage evidence.

These structures appear in
[`Program.lean`](../../leanncd/LeanNCD/Semantics/Program.lean),
[`Types.lean`](../../leanncd/LeanNCD/Semantics/Types.lean),
and [`ExecutableState.lean`](../../leanncd/LeanNCD/Semantics/ExecutableState.lean).
Calling `runValidated` does not remove their construction requirements.

For the initial experiment, adopt the conservative rule:

> Reuse existing constructed programs, schedules, and admitted-read
> evidence. Do not introduce new theorem declarations or hand-written
> proof terms merely to populate the fixture suite.

Even a short `by decide` would be a new proof term; it should not be
quietly described as absent. If a desired case has no proof-free
construction route through existing infrastructure, record that
limitation and defer it rather than add `sorry`, invent a certificate,
or silently reduce the advertised coverage.

The admitted-source layer has existing proved schedule builders:
`sourceScheduleAt`, `sourceSchedule`, `sourceInputBinding`, and `runSource`
in [`Source/Schedule.lean`](../../leanncd/LeanNCD/Semantics/Source/Schedule.lean),
with `AdmittedSource.program` in
[`Source/Program.lean`](../../leanncd/LeanNCD/Semantics/Source/Program.lean).
Its source admission is restricted; it is not a generic adapter for
partial-primitive, guard, or cycle examples.

### 7.3. Share expression semantics, not the scheduler

For the first prototype, reuse the existing whole-body ready evaluator:
`evalReady` and `ReadyResult` in
[`Readiness.lean`](../../leanncd/LeanNCD/Semantics/Readiness.lean).
The expression operations `footprint`, `evalWith`, `interpret`, and
`sequence` live in
[`Interpret.lean`](../../leanncd/LeanNCD/Semantics/Interpret.lean).

The graph must compute eligibility from its own available-value ports.
If it declares an occurrence ready but the shared evaluator reports
waiting, that is a graph-contract discrepancy, not an excuse to fall
back to the reference scheduler.

This division intentionally shares expression interpretation. It tests
graph construction, availability, collection closure, scheduling, and
terminal observation independently. It does not independently verify
the shared interpreter's arithmetic or strictness.

The existing collection operations `Family`, `pullback`, and
`pushforward` in
[`Collection.lean`](../../leanncd/LeanNCD/Semantics/Collection.lean)
are useful total-family operations. They do not justify filling missing
produced values with zero before a collector is complete.

Do not use the reference `attempt` or `select` as the candidate's
eligibility predicate. Do not write another reference executor and
describe agreement between two new implementations as independent
verification.

## 8. Comparison observations and scheduling

### 8.1. Derive a reference-shaped view

From any nonfailed graph state, derive:

- The reference published store from inputs and completed collectors.
- The reference accumulator at each destination by combining its
  successfully produced occurrence values.
- The reference pending family from occurrences without produced values.

This is a computed comparison view, not additional state updated by
the graph runner.

Initially compare both complete outcomes and intermediate views under
a matched priority order. Restart selection at the beginning of that
order after every action, matching the reference selection discipline.
Event comparison should use explicit occurrence and address identities,
not numerical values or display names as substitutes.

### 8.2. Compare data, not dependent proof fields

Do not attempt direct equality on dependent execution objects containing
proof fields. Project both sides to ordinary runtime observations:

- Stable tensor identity and coordinate.
- Available versus missing value.
- Exact rational value when available.
- Stable statement and valuation identity.
- Terminal kind and located failure occurrence.
- Derived accumulator and pending rows for diagnostic snapshots.

Inspect every declared tensor, including internal nonoutputs. Empty
tensor metadata and input presence need their own observations because
there are no coordinate rows to reveal omission.

The existing `eventRow`, `vectorStore`, and `snapshot` definitions in
[`ExecutableReferenceTest.lean`](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)
are possible narrow donors.
[`Source/Observation.lean`](../../leanncd/LeanNCD/Semantics/Source/Observation.lean)
and [`Source/Diagnostics.lean`](../../leanncd/LeanNCD/Semantics/Source/Diagnostics.lean)
have richer observations for admitted sources, but not every helper is
an independent graph check: `observeSnapshot.eligible`, for example,
uses reference `attempt`.

A small generic data projection may be clearer than reusing a helper
whose eligibility logic would couple the two implementations.

### 8.3. Do not overstate schedule coverage

There are two different experiments:

1. Run the graph and reference using already available matched,
   complete priorities.
2. Explore every eligible graph successor on tiny finite instances.

The second does not automatically compare every reference schedule:
arbitrary new reference schedules require their coverage evidence.
Report exactly which reference priorities were exercised.

Different successful priorities should agree on the complete exact
environment. Different failing priorities need not choose the same
occurrence or snapshot. Under a matched priority, a failure-location
disagreement is an informative discrepancy and must not be hidden by
comparing only a generic failure flag.

State exploration needs explicit size and fuel limits. Reaching a limit
is inconclusive, not success, blocking, or proof of nontermination.

## 9. Fixture families and what each would teach us

Every row below is a proposed experiment. Donor names identify existing
material to assess for reuse; they do not assert that a fresh prototype
run has occurred or that every donor already has a usable schedule.

| Family | Distinguishing requirement | What agreement would tell us |
| --- | --- | --- |
| Duplicate and colliding contributions | Equal values with different occurrence identities must remain separate writers | The graph preserves occurrence identity, not merely a set of values |
| Nonlinear boundary | Compare operation-per-occurrence with operation-after-collection as intentionally different constructions | Collector closure preserves the placement of nonlinear operations |
| Strict partial expressions | A ready undefined operand remains undefined even with a zero multiplier; array selection cannot bypass demanded nonselected entries | The interface does not silently introduce short-circuit or lazy semantics |
| Unready partial occurrence | A missing footprint input prevents body evaluation even if another subexpression would be undefined | Atomic node readiness preserves legally reportable failures |
| Guards and empty domains | Excluded or nonexistent body instances are not evaluated; empty writer fibers complete as zero | Absence of work is distinguished from a failed or zero-valued result |
| Empty inputs | Omitted tensor-level input presence is rejected even when there are no coordinates | The graph has not confused declarations with coordinate enumeration |
| Internal work and completion | An undefined internal nonoutput cannot be ignored after outputs become available | Whole-program completion still matches the complete-model contract |
| Ranked chains and finite histories | Consumers wait for complete earlier values; relevant alternate priorities still progress | Availability is sufficient to express the intended causal execution |
| Unranked cycles | Blocking remains distinct from undefinedness and from the existence of equation models | The graph has not become an accidental cyclic solver |
| Interface composition | Combine disjoint occurrence fragments, close writers, then connect completed values; reject invalid alterations | The design supports more than a renamed closed-program loop |

### 9.1. Existing material to reuse

The source investigation confirmed that the named donors are public
definitions or abbreviations. The test modules are importable through
Lake's `test` library, whose source directory is `test` in
[`lakefile.toml`](../../leanncd/lakefile.toml). The import names include
`Semantics.ExecutableReferenceTest`, `Semantics.ExpressionTest`, and
`Semantics.CollectionModelTest`. They are not exported by the production
`LeanNCD.Semantics` module.

The most useful executable pairs are in
[`ExecutableReferenceTest.lean`](../../leanncd/test/Semantics/ExecutableReferenceTest.lean):

| Purpose | Existing program/body and schedule material |
| --- | --- |
| Duplicate writes | `program`, `duplicateBody`, and generic `schedule` |
| Colliding tagged valuations | `tagged`, `taggedSchedule` |
| Ready undefinedness and failure snapshots | `failureBody`, `failureAfterSchedule` |
| Guard exclusion | `excluded`, `excludedSchedule` |
| Zero-coordinate input presence | `emptyRole`, `emptySchedule` |
| Dependency chain and cycle | `routed`, `chainBody`, `cycleBody`, `routedSchedule` |
| Executable nonlinear and partial bodies | `squareBody`, `reciprocalBody`, and generic `schedule` |

These are source-checked reuse candidates with existing schedule
infrastructure, not reports of prototype executions. Reuse an existing
schedule or its already-supported `.reverse` operation rather than
construct a new schedule with manual coverage proofs.

Other useful donors have a narrower role:

- [`CollectionModelTest.lean`](../../leanncd/test/Semantics/CollectionModelTest.lean):
  `duplicate`, `collision`, `noStatements`, `partialProgram`, and
  `reciprocalProgram`. These include model-level donors; do not presume
  they all come with reusable executor schedules.
- [`ExpressionTest.lean`](../../leanncd/test/Semantics/ExpressionTest.lean):
  `zeroStrict`, `emptyReduction`, `emptyTab`, `selected`, and
  `nonselectedUndefined`. These pin expression semantics, not by
  themselves graph/reference end-to-end execution.
- [`RankedMachineTest.lean`](../../leanncd/test/Semantics/RankedMachineTest.lean):
  ranked dependencies, zero extents, and the distinction between cyclic
  model existence and blocked execution. Existing semantic witnesses
  are not automatically new executable graph adapters.

The expression and collection-model donors use different declarations,
carriers, or registries from the executable-reference fixtures. Their
existence does not supply an end-to-end adapter for strict tabulation,
selection, or every proposed history case.

No generic proof-free complete-schedule constructor or exhaustive
legal-reference-step enumerator was found in the inspected APIs.
The existing admitted-source schedule builder remains useful within
its own restricted fragment.

The first implementation checkpoint must confirm that these public
imports build in the chosen experimental location, exercise the selected
constructions, and record actual observations.
Keep three coverage labels in the result table: full graph/reference
comparison, expression/interface-only check, and deferred adapter.
Never report the union of those labels as end-to-end coverage.

### 9.2. Laws and deliberate non-laws

On the appropriate total, closed fragment, check:

- Pullback identity and composition.
- Additive pushforward identity, composition, grouping, and occurrence
  relabeling.
- Collection after exactly its closed writer family has succeeded.
- Immutability of available values.
- Agreement of successful complete environments across tested priorities.

Check counterexamples to the tempting but invalid generalisations:

- Arbitrary nonlinear operations do not distribute over collection.
- A zero multiplier does not suppress undefinedness.
- Strict array evaluation does not commute with every coordinate restriction.
- Having a model does not imply completion of unranked direct execution.
- Different priorities need not report the same first failing occurrence.

These counterexamples are part of the desired evidence: a useful
formalism must reject false equations, not merely validate convenient ones.

### 9.3. Controlled defects

After establishing an unmodified baseline, deliberately introduce one
candidate defect at a time:

- Deduplicate equal-valued writers.
- Replace collection by the last writer.
- Omit a writer port or allow premature collection.
- Treat a missing value as an available zero.
- Evaluate a partial occurrence before its entire footprint is ready.
- Omit nonselected strict-array demands.
- Finish when outputs alone are ready.
- Accept an omitted zero-coordinate input.

Each defect must violate a named, independently stated expectation.
Agreement between two legs sharing the same changed evaluator is not
a sufficient control. For shared expression semantics, the existing
expression pins or an independently stated definedness expectation
must expose the error.

These are proposed controls, not mutation results already observed.

## 10. What would count as simplification?

Correct final numbers are necessary but insufficient. Record whether:

1. The runtime has only available values, produced values, and terminal
   status, rather than a second mutable pending/accumulator machine.
2. Readiness follows from explicit value ports, and collection readiness
   follows from closed writer ports.
3. Open-fragment combination and writer closure reject meaningful bad
   compositions before execution.
4. The comparison view reconstructs reference bookkeeping without calling
   reference selection.
5. At least one useful grouping/batching operation has a small executable
   preservation check and a clear mathematical explanation.
6. Strictness counterexamples have an explicit place in the interface,
   rather than a growing list of scheduler exceptions.
7. Proof-free execution remains real: the prototype has not replaced
   ordinary construction with an indispensable new proof generator.

Do not use runtime speed or memory reduction as the initial success
criterion. Recording every produced contribution may use more storage
than an incremental accumulator. The proposed gain is a simpler semantic
and compositional interface, from which more efficient representations
could later be derived.

An honest no-go result includes:

- A graph completion or readiness rule that changes a supported outcome.
- A required global condition that cannot be represented by the proposed
  finite interfaces without reconstructing the original machine.
- Reuse so extensive that the candidate shares the reference scheduler,
  collection decisions, and observations, leaving little independent test.
- Important cases requiring new proof construction before they can be
  expressed, contrary to the initial constraint.
- A representation that cannot plausibly retain a compact symbolic form
  for larger finite domains.

## 11. First implementation and observed evidence

### 11.1. Files and invocation

The non-default `IndexedExecutionExperiment` Lake target builds:

- [`IndexedExecutionPrototype.lean`](../../leanncd/experiments/indexed_execution/IndexedExecutionPrototype.lean):
  explicit occurrence/read/writer ports, structural closure, graph state,
  independent priority selection, and data-only reference comparisons.
- [`IndexedExecutionPrototypeTest.lean`](../../leanncd/experiments/indexed_execution/IndexedExecutionPrototypeTest.lean):
  executable fixture assertions, malformed graph controls, expression pins,
  and finite-family checks.

Neither module is imported by production `LeanNCD`. No new theorems,
axioms, `sorry`, or hand-written proof terms were added.

From the checkout root, build dependencies and then execute the checks
afresh:

```bash
bash leanncd/scripts/lake-build.sh leanncd IndexedExecutionExperiment
bash leanncd/scripts/lean-file.sh leanncd experiments/indexed_execution/IndexedExecutionPrototypeTest.lean
```

The second command elaborates the test file again, so its executable
assertions run even when Lake has cached the module.

### 11.2. Observed coverage

The first implementation passes **36 executable check rows**, containing
**18 matched-priority graph/reference comparison invocations**. Those
numbers count assertions and invocations, not distinct programs or
exhaustive schedules.

| Evidence class | Observed coverage |
| --- | --- |
| Matched graph/reference runs | Duplicate writes; colliding tagged valuations; selected reversed priorities; ready undefinedness and failure snapshots; guards; empty fibers; empty input presence/absence; internal nonoutput work; coordinate chains and a blocked cycle; reciprocal and square |
| Intermediate-state pins | Open writer bundles remain unavailable; produced zero differs from missing; outputs alone do not complete internal work; full footprints wait for required coordinates |
| Construction controls | Fragment recomposition; missing node, duplicate tag, missing writer and dropped read rejection; malformed graph rejected by reference comparison |
| Expression-only evidence | Existing strict array selection/tabulation, zero-strictness, empty reduction and demanded empty-array cases |
| Total-family evidence | Concrete pushforward grouping/composition and reindex composition checks |

The comparison checks terminal kinds, located failures, every intermediate
available/accumulator/pending snapshot, event identities and values, and
blocked-read observations. It enumerates all declared coordinate rows,
including nonoutputs, and separately compares tensor-level input presence.

Two real source mutations were run through the
[mutation manifest](categorical_tensor_logic_prototype_mutations.json):
changing the collector's zero seed to one and removing the full-footprint
readiness gate. Both caused the intended fixture failures; both restored
byte-identically and rebuilt successfully. These are implementation
mutations, not changes to expected assertion values.

The full default Lean library and test build also completed successfully.
Existing repository proof warnings remain outside this prototype; the new
modules introduced no source warnings.

### 11.3. What remains untested or deliberately limited

- There is no exhaustive graph-state or reference-schedule explorer;
  only the selected complete priorities and reversals were exercised.
- Strict array selection has expression-level pins, not a graph adapter
  over the prototype's rational registry.
- The ranked chain is not a full bounded-history or symbolic scan adapter.
- Arbitrary source-program admission, general partial-primitive registries,
  and independently authored open-program composition are not implemented.
- The body interpreter and footprint construction are deliberately shared
  with the reference. Parity does not independently verify them.
- Structural closure validates a fixed program's canonical port lists.
  It is not yet a phase-typed open-interface calculus or a general account
  of port isomorphisms.

The observed structural gain is limited but real: the runner stores
available values and produced occurrences, while reference pending sets
and accumulators are derived only for comparison. Runtime eligibility
uses explicit graph ports rather than reference `attempt` or `select`.
Whether that scales to a simpler general categorical foundation remains
the next research question, not a conclusion of these checks.

## 12. What we will and will not learn

If the experiment succeeds, we will have evidence that explicit
contribution closure and availability can organise execution faithfully,
that effect-sensitive indexing captures important non-laws, and that
some reference bookkeeping can be derived from a more compositional
representation.

We will not yet have established:

- A general Turi-Plotkin compositionality theorem.
- That the candidate is the best categorical foundation.
- Full source-language admission or parser correspondence.
- A proof for all programs or all schedules.
- An implementation of every guarded, affine, nonlinear, or scan case.
- Correct floating-point reductions, memory reuse, or production kernels.
- A solver for general cyclic equations.

The most useful outcome may be a precise counterexample or a narrower
abstraction. The experiment is successful as research if it tells us
which part of the proposal deserves further work, even if the answer
is not to adopt the proposed organisation unchanged.
