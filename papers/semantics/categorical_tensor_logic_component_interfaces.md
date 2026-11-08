# Sealed component interfaces for categorical Tensor Logic

## Recommendation and status

Use **locally scoped matched components**, connected by explicit whole-tensor
wiring. Construct the composite source, contract, fragment and schedule by
transporting their static data, then construct its `SourceContractMatch`.
Reuse the landed execution-correspondence theorem only afterward.

The implemented static profile is finite computation over the existing
exact-rational registry. It preserves all internal work, uses upstream-first
priority, and introduces no copying computations. Coordinate-ranked phase
execution remains a later theorem. Neither St/Br nor a general category
library is a prerequisite.

Typed transport and static sealed composition are implemented and proved in
the nondefault experiment. `IndexedComponentComposition.compose` packages
the composite; `compose_match` derives its genuine `SourceContractMatch`.
See the [transport record](component_transport_execution_record.md) and
[composition record](component_composition_record.md) for validation and
recorded boundaries. Complete-model gluing, restricted denotation, the
witness-span target category and nested denotational coherence are also proved;
see the [witness semantics record](categorical_witness_semantics_record.md).
Ranked phase execution and source/process categorical laws remain design
obligations. The starting points
are the [categorical synthesis](categorical_tensor_logic_semantics.md),
especially Section 9 and its explanatory Appendix A, the
[proof record](categorical_tensor_logic_proof_record.md), and the
[theorem-design brief](categorical_tensor_logic_theorem_brief.md).
The authoritative existing match is
[`SourceContractMatch`](../../leanncd/experiments/indexed_execution/IndexedCompositionMatch.lean).
The static and denotational constructor names below are implemented; the
remaining ranked process theorems are proposals, not existing declarations.

## 1. A component owns a declaration universe

A **component** $C$ packages:

- Finite typed declarations $\Delta_C$, with injective tensor UIDs.
- A reference program $P_C$, a complete ordered schedule $S_C$, a contract
  $K_C$, a writer fragment $F_C$, and its canonically closed graph $G_C$.
- A supplied match $M_C$ between these five representations.
- A coordinate-rank certificate $r_C$ for the later ranked profile, not required
  by the implemented static component constructor.
- Ordered, duplicate-free whole-tensor input and output interfaces.

Here a **tensor UID** is its explicit identity, not its display name.
A **whole-tensor interface** records tensor identity, scalar sort and the
entire declared coordinate domain, including a domain with no coordinates.
The interface lists exactly the tensors selected by the program's respective
input/output predicates. Its order is presentation data; the schedule also
retains its own complete tensor-validation order.

Write $T_C$ for the tensor type of $\Delta_C$, $I_C$ for its input tensors,
$D_C$ for its defined tensors, and $O_C$ for its output tensors. A defined
tensor is a noninput, not a tensor whose runtime value is already available.
Outputs belong to $D_C$ by
[`Program.output_defined`](../../leanncd/LeanNCD/Semantics/Program.lean).
The **private tensors** are $D_C$ minus $O_C$; privacy hides their ports,
not their equations, occurrences, events or completion obligations.

There are no ambient tensors in $T_C$. A larger repository declaration table
must first be restricted, with evidence that every body read and destination
lies in this local universe. This is substantive:
[`close`](../../leanncd/experiments/indexed_execution/IndexedOpenComposition.lean)
requires enumeration of *all* tensors and collectors for *all* noninput
coordinates. Padding a producer's universe with a consumer's `Out` and
`Audit` creates spurious collectors if they are noninputs, or spurious
external bindings if they are inputs. An unused tensor is not automatically
outside the component.

The interface metadata supplements, rather than changes, `Contract.outputs`.
That address list cannot distinguish an empty output tensor from no output.
The program predicates and interface lists remain authoritative.

## 2. Boundary wiring and typed transport

Let $A$ be the upstream component and $B$ the downstream component. Require
an explicit bijection $b:I_B\cong O_A$, matching every downstream input to
one upstream output and using every upstream output. The symbol $\cong$
denotes a specified bijection, not inferred equality.
This first operation has no residual downstream inputs, fan-out between
distinct input ports, partial tensor ports or open additive ports.

For each tensor $t$, write $J_C(t)$ for its full coordinate type.
For each input $i$ of $B$, supply a typed domain adapter
$e_i:J_B(i)\cong J_A(b(i))$. The adapter states the intended coordinate
correspondence explicitly. Equal names, equal extents, equal cardinalities
and even equal numeric UIDs in independently authored components do not
establish a boundary connection.

### A deliberately restricted first adapter

Use explicit axis-position bijections preserving extents; pure UID renaming
with unchanged axis order is the simplest instance. These adapters induce
both the coordinate bijection and a raw-coordinate bijection commuting
with `Coord.raw`. Arbitrary finite-set bijections, reshapes and slices are
not admitted merely because their domains have the same size.

This restriction addresses an actual typing obligation.
[`AdmittedRead`](../../leanncd/LeanNCD/Semantics/Types.lean)
contains a raw coordinate, a read policy, a resolved coordinate or constant,
and an admission proof. Mapping only the resolved coordinate is insufficient.
For a declaration embedding $f$, let $e_t$ map a local tensor's coordinates
to its image coordinates, and let $u_t$ map its raw coordinates in the same
direction. Require

```math
u_t(\operatorname{raw}(p))=\operatorname{raw}(e_t(p)).
```

Here $\operatorname{raw}$ means `Coord.raw`. Transport a policy by applying
the old policy after $u_t^{-1}$ and mapping its result: map an addressed
coordinate by $e_t$, keep a constant unchanged, and keep rejection unchanged.
Transport the read's raw argument by $u_t$ and its resolved result by the
same result mapping. The displayed equation proves the new in-bounds law;
the old admission proof proves the transported admission equation.
Constants and boundary policies must not silently become ordinary reads.

Freshen retained tensor UIDs injectively into disjoint namespaces, except
for the explicitly wired boundary. Display-name collisions are harmless.
Any axis-identity transport is also explicit; do not blindly rename the
fixed registry's type indices. Existing
[`Source.UIDTransport`](../../leanncd/LeanNCD/Semantics/Source/Context.lean)
provides domain-aware valuation transport and useful prior art, not a
generic transporter for these expression trees.

### The required local transport lemmas

The experimental
[`transport`](../../leanncd/experiments/indexed_execution/IndexedComponentTransportExpr.lean)
and its
[evaluation laws](../../leanncd/experiments/indexed_execution/IndexedComponentTransportEval.lean)
implement the local obligations in this subsection. They use supplied
axis-certified adapters from
[`Domain`](../../leanncd/experiments/indexed_execution/IndexedComponentTransport.lean),
not automatic domain matching, and need no rank or reached-store premise.

Write $\widehat f(t,p)=(f(t),e_t(p))$ for the induced address embedding.
For a composite partial store $s$, define its local restriction $f^*s$ by
$(f^*s)(t,p)=s(\widehat f(t,p))$. A partial store records availability as
well as rational values; absence is not zero.

Define a structural expression transport $\operatorname{tr}_f$ across
declarations. In this profile it keeps expression result types, primitive
symbols, local array shapes and layouts unchanged, and transports tensor
reads as above. Statement valuation spaces and guards are copied.
If their dependent types require an explicit equivalence, precompose reads,
predicates and indices with that equivalence, extending it under `reduce`
and `tab`. This must include `iverson` predicates and `at` indices, not just
free scalar reads.

For every expression $E$, admitted valuation $\gamma$ and partial store $s$,
prove the following, with the corresponding valuation understood after any
context transport:

```math
\operatorname{footprint}(\operatorname{tr}_f E,\gamma)
=\operatorname{map}(\widehat f)(\operatorname{footprint}(E,\gamma)),
```

```math
\operatorname{evalReady}(s,\operatorname{tr}_f E,\gamma)
=\operatorname{evalReady}(f^*s,E,\gamma).
```

Here `map` maps a list elementwise, preserving order and repetitions;
`evalReady` uses the fixed rational operations. Its equality includes
not-ready, ready-but-undefined and ready-with-a-value.
Prove analogous complete-store interpretation transport.
[`Expr`](../../leanncd/LeanNCD/Semantics/Expr.lean),
[`footprint` and `evalWith`](../../leanncd/LeanNCD/Semantics/Interpret.lean),
and [`evalReady`](../../leanncd/LeanNCD/Semantics/Readiness.lean)
are the exact surfaces. In particular, selection retains the footprint
and strict evaluation of the *whole* array expression.

These are reusable structural lemmas, not an assumption of equality between
executions or of the desired composite match.

## 3. The sealed composition construction

Write $B\circ_b A$ for composition along the specified wiring $b$.
Choose the composite tensor type

```math
T_{BA}=T_A\sqcup D_B,
```

where $\sqcup$ means disjoint union. The upstream embedding includes all
of $T_A$. The downstream embedding sends a defined tensor to its new
disjoint summand and an input $i$ to the upstream tensor $b(i)$, using $e_i$
on coordinates. Both embeddings are injective; their images meet exactly
at the wired boundary.

Construct the composite as follows:

1. **Roles and source.** Inputs are exactly the embedded $I_A$; outputs are
   exactly the embedded $O_B$. Retain every defined tensor of both
   components, including upstream outputs now hidden from the exterior.
   Copy statement counts, valuation counts, guards and destinations through
   the embeddings; transport bodies structurally. No new occurrence is
   introduced and none is removed.
2. **Writer identities.** Injectively rename each component's tags and
   capability IDs into disjoint natural-number ranges. Rename every use,
   including collector lists and event identity maps. Append the transported
   writer lists, upstream first. Equal-valued writers remain distinct.
3. **Contract.** Enumerate the transported upstream tensor list followed by
   the downstream tensor list filtered to $D_B$. Append transported
   collector rows, upstream first, retaining each row's capability order.
   Take the duplicate-free union of transported readable lists. Use only
   downstream output addresses for the output list.
4. **Schedule and closure.** Use the same tensor enumeration in the
   composite schedule. Append the transported upstream and downstream key
   lists. Prove successful closure and its canonical step equation, rather
   than manufacturing public `Closed` data and trusting it.

There is no collector for a downstream input in its standalone component,
so no collector is removed or added at the join: the upstream collector
already owns that address. All other noninput collectors survive, including
zero-writer collectors. Empty tensors contribute metadata but no coordinate
collector. No global padding, output-to-input copy, or boundary input binding
is needed in the composite run.

### Three different meanings of closed or complete

- An **open contribution interface** offers a fragment whose writer family
  may still be extended before closure. It is not a value port.
- A **structurally closed writer family** has all its occurrences and
  capabilities fixed and checked. It can still block or fail when run.
- A **runtime-completed value** has every coordinate published. Successful
  completion of a *component* additionally requires all its internal work.

The operation composes structurally closed components. It never extends
upstream collector capability lists with downstream writers.
[`Assembly.sealed` and `extend`](../../leanncd/experiments/indexed_execution/IndexedOpenComposition.lean)
already distinguish sealing from extension, but do not implement this
cross-universe operation. Public numeric capabilities are collision-checked
IDs, not unforgeable authority.

Downstream destinations lie only in the $D_B$ summand. Upstream bodies
cannot refer to that summand. Thus downstream code cannot modify a sealed
upstream result, and upstream execution has no reverse dependency.
Do not prune private occurrences, short-circuit an additive cancellation,
or stop when exterior outputs become available.

## 4. Constructing the match, field by field

Let $M_A$ and $M_B$ be the supplied component matches. Let $P_{BA}$,
$S_{BA}$, $K_{BA}$, $F_{BA}$ and $G_{BA}$ denote the constructed composite
program, schedule, contract, fragment and canonical graph.
The following table covers every field of the existing match:

| Field | Construction and required proof |
| --- | --- |
| `close_ok` | A new closure-preservation lemma transports and appends the two accepted contracts/fragments. Disjoint defined images, fresh IDs, full domain adapters and footprint transport discharge coverage, uniqueness, destination and readable checks. Do not retain composite closure acceptance as a caller premise. |
| `input_roles` | By construction, only upstream inputs remain external. Wired downstream inputs now denote upstream defined tensors. |
| `tensor_order` | Set both lists to the specified upstream enumeration followed by the filtered downstream enumeration; prove complete, duplicate-free coverage, including empty tensors. |
| `outputs_exact` | Transport downstream exact output-address coverage and its defined-output proof. Whole output-tensor metadata is a separate interface invariant, especially for empty domains. |
| `sourceToWriter` | Identify composite occurrences with the disjoint union of component occurrences. Combine their supplied bijections with the equivalence between the two writer-position types and positions in the appended list. |
| `writer_destination` | Component destination equality followed by address transport; source guards and admitted valuation multiplicities are unchanged. |
| `writer_reads` | Component ordered-list equality followed by the footprint-transport lemma. No set conversion or deduplication. |
| `eval_agrees` | For an arbitrary composite partial store, restrict it to the relevant component. Transport the writer's unit-context evaluation, apply that component's `eval_agrees`, and transport its source-body evaluation back. |
| `priority` | Each supplied match already identifies its entire mapped key list with canonical closure steps. Prove that transport and collector-row append preserve that equation; therefore the appended composite keys map to the composite canonical steps. |

This uses schedules of *matched* components, not arbitrary independently
chosen priorities. Re-sorting composite collectors or capability lists would
invalidate the last row, even if all writers were still present.
The readable-list union may deduplicate addresses; the read lists themselves
must not be deduplicated.

Capability injectivity and exact collector fibers need not be additional
interface premises. Once this match exists, reuse their derivation in
[`IndexedCompositionFibers`](../../leanncd/experiments/indexed_execution/IndexedCompositionFibers.lean).
Likewise do not assume equal selected actions, traces, accumulated sums or
intermediate states; those are downstream results.

## 5. Static construction and later theorem dependencies

**Static match construction.** The implemented `compose_match` takes two
matched components and a `Boundary` supplying their exact bijective wiring
and certified domain adapters. The constructor chooses and proves disjoint
even/odd identity embeddings; callers do not allocate a namespace or supply
composite acceptance. `compose` packages the constructed data, ports and

```math
\operatorname{SourceContractMatch}
  (P_{BA},S_{BA},K_{BA},F_{BA},G_{BA}).
```

Rank certificates are not needed for this static theorem. Its transport and
closure lemmas are proved generically, not retained as new per-composite
hypotheses equivalent to reconstructing a whole match.

**Ranked sealed execution.** With both component rank certificates and valid
external inputs, the constructed execution runs all upstream work first.
If the upstream component fails, no downstream action occurs. If it completes,
the remaining execution is the transported downstream run on its whole
boundary output, retaining the completed upstream state.

Upstream-first list order alone is *not* a phase barrier: the runner skips
disabled actions. The ranked premise supplies the missing argument. Before
the first downstream action, projection to the upstream component is a
reachable standalone upstream state. If incomplete, ranked progress supplies
an enabled upstream action, which has higher priority than every downstream
action. Undefinedness terminates the run instead of allowing fall-through.
Thus no downstream action can precede upstream completion. Without ranking
or a separately proved upstream progress property, claim only ordered
priority, not strict sequential execution; do not add a new gate silently.

To construct a composite rank, choose a natural number $L$ strictly larger
than every upstream address rank, including input ranks; finiteness permits
this, also when the address set is empty. Keep upstream ranks and assign
$L+r_B(a)$ to each embedded downstream defined address $a$.
Internal downstream dependencies still decrease, boundary dependencies land
below $L$, and upstream dependencies are unchanged.
[`RankCertificate`](../../leanncd/LeanNCD/Semantics/Ranks.lean)
ranks full-footprint dependencies, not output dependencies alone.

The phase result must compare states by embeddings: downstream initial input
availability is the published upstream boundary, its produced ledger is
fresh, and the composite retains the upstream ledger and private values.
Splice the traces without an extra boundary event; join state observations
with one shared phase-boundary snapshot, not two. Use the existing failed-state
normalisation, not literal equality of raw reference machine-state lists.
This is a proposed additional proof, not already furnished by correspondence.

Dependency outline:

1. Declaration/address/store transport; admitted-read and context transport;
   ordered footprints and strict interpretation/readiness preservation.
2. Composite source occurrence and publication-key equivalences; role,
   interface-metadata and complete-enumeration facts.
3. Closure preservation, disjoint capability/tag renaming, and canonical
   priority append; assemble the nine match fields.
4. Apply
   [`default_run_correspondence`](../../leanncd/experiments/indexed_execution/IndexedCompositionValidated.lean)
   to obtain outcomes, mapped events and related intermediate states for
   the composite, on every raw composite binding.
5. Stitch ranks and prove the ranked phase/projection result; this remains
   separate from the rank-independent complete-model restriction/gluing
   theorem proved below.

The composite default graph budget is its total writer/publication step count
plus one, not the sum of the two standalone default budgets. Reuse the landed
budget and mismatch-exclusion results after constructing the match.
For invalid raw bindings, composite validation uses its own full tensor order;
do not equate it with two independent validations. In particular, the caller
must not supply the now-internal boundary as an external input.

## 6. Complete models before output functions

A **complete-model witness** is a whole tensor store satisfying input
agreement, definedness of every admitted occurrence body, and every collected
coordinate equation. It is not just an output assignment or a proof object's
identity. Write $\mathcal M_C(\eta)$ for the set of such stores for component
$C$ on validated input environment $\eta$.
These are the existing
[`Program.Models`](../../leanncd/LeanNCD/Semantics/Models.lean)
conditions.

For an upstream store $\rho_A$, define its downstream boundary environment
$B_b(\rho_A)$ by

```math
B_b(\rho_A)(i)(p)=\rho_A(b(i))(e_i(p)).
```

Here $i$ ranges over downstream input tensors and $p$ over their coordinates.
At tensor-binding level, each such input is present, even when its coordinate
domain is empty; noninput bindings are absent.
The proved restriction/gluing theorem is the bijection

```math
\mathcal M_{BA}(\eta)
\cong
\left\{(\rho_A,\rho_B)\ \middle|\
 \rho_A\in\mathcal M_A(\eta),\
 \rho_B\in\mathcal M_B(B_b(\rho_A))
\right\}.
```

Restriction uses the two address embeddings. Gluing uses $\rho_A$ on its
summand and $\rho_B$ on downstream defined tensors; input agreement gives
consistency on their intersection. Interpretation transport preserves every
body's definedness; occurrence bijections and finite-sum transport preserve
all collected equations, including zero-writer fibers.
Upstream internal witnesses are retained, not existentially hidden before
testing uniqueness. `IndexedComponentComposition.witnessesEquiv` in
[`IndexedComponentModelWitnesses`](../../leanncd/experiments/indexed_execution/IndexedComponentModelWitnesses.lean)
constructs this dependent whole-store bijection and its explicit inverses.
`models_restrictInput_iff` handles every validated composite input.
This model theorem needs no ranking, execution completion, model existence,
or component uniqueness.

Ranking gives **at most one model**, not guaranteed existence: ranked
complete-or-failed execution and existing whole-store uniqueness/failure
results establish the distinction. Let $f_C$ be the partial input-output
function defined exactly when $\mathcal M_C(\eta)$ has one member.
Under explicit at-most-one-complete-model assumptions for both components,
[`IndexedComponentModelDenotation`](../../leanncd/experiments/indexed_execution/IndexedComponentModelDenotation.lean)
proves the admissibility-domain correspondence (`admInput_restrictions_iff`)
and successive values (`denotation_successive`), giving
$f_{BA}=f_B\circ B_b\circ f_A$. Here $B_b$ on an output environment is the
same boundary reindexing. At-most-one does not assert existence.
There is no successful output when private work is undefined.

Without at-most-one-model upstream semantics, this partial-function equation
is unsafe. An upstream equation $t=t^2$ has rational models $0$ and $1$;
a downstream reciprocal excludes $0$. The composite can have one model
although the standalone upstream partial function is undefined.
Retaining compatible pairs of complete models avoids this loss of information.
The logical cyclic and hidden-multiplicity cases are now proved by
[`IndexedComponentModelCycleTest`](../../leanncd/experiments/indexed_execution/IndexedComponentModelCycleTest.lean);
they do not claim that execution solves a cycle or that ranks exist.
See the [model-gluing record](component_model_gluing_record.md) for all seven
acceptance cases, explicit private-work witnesses, and validation evidence.

## 7. Identity, associativity and observation levels

Distinguish four notions:

- **Value equality** means equality of partial input-output functions,
  including their domains, after explicit port reindexing.
- **Span isomorphism** is a bijection of complete witnesses commuting with
  both environment legs. It preserves fiber multiplicity, not execution
  events or the coordinate-level identity of private representations.
- **Process equivalence** means equal terminal classifications, mapped ordered
  events and related full intermediate snapshots after coherent bijective
  renaming of tensors, coordinates, occurrences, tags and capabilities.
  Preserve input-validation order and internal events; normalise only the
  already documented failed-state wrapper. This is the intended operational
  equivalence, not equality of raw numeric IDs or differently typed records.
- **Refinement** is a directed implementation-to-specification simulation
  with a stated observation map. Batching or extra implementation steps need
  such a separate argument, preserving required definedness and internal
  effects. Success-domain inclusion alone is too weak to justify an
  optimization that bypasses an undefined reciprocal.

For three components, preserve leaf order, each component's collector order
and each collector's capability order. Then the two bracketings retain the
same ordered work. The proposed associativity law is process equivalence
under disjoint-union reassociation and coherent boundary transport, plus the
corresponding bijection of complete-model witnesses. Flattened interface
wiring must agree. Nested numeric freshening may produce different IDs;
map them by original component provenance, not by numerical coincidence.
Generic transport must satisfy identity and composition laws so repeated
bracketing does not change policy resolution or ordered footprints.
The prerequisite policy-resolution, footprint and evaluation laws now satisfy
this local requirement; process associativity and process identities remain
separate proposed results.

For the denotational observation level, the witness-span implementation now
proves an ordinary target category, a composition-preserving interpretation
across all validated inputs, and nested component associativity through the
same compatible triple of complete models. Explicit boundary and exterior
environment equivalences commute with both legs; no raw UID coincidence is
used. See [witness coherence](../../leanncd/experiments/indexed_execution/IndexedWitnessCoherence.lean)
and [the witness semantics record](categorical_witness_semantics_record.md).
This closes the model-witness associativity obligation, not the proposed
process associativity or process identities.

There is **no event-exact core identity implemented by copying**.
A core copy must write and publish a fresh defined output; it adds observable
events and state. Making its input an output instead contradicts
`output_defined`. Empty tensors do not license a general aliasing rule.
A copy can represent the identity *value function*, but not this process unit.

The smallest honest first result is therefore an associative composition of
matched core components, without claiming units inside that class.
If units are needed for categorical packaging, represent an identity as an
**administrative wire**: an explicit interface isomorphism outside `Program`,
with no computation, writer, publication or runtime event. Composing with it
reduces to typed renaming of the existing component; it does not produce a
core program with an input alias as output. Its empty trace is structural
data, not a new successful instance of `SourceContractMatch`.
Identity laws then hold for this enlarged representation under process
equivalence. Extending the core theorem to arbitrary wire-only objects is
not claimed or required here.

## 8. Required validation example

Use separate local universes:

| Component | Inputs | Defined tensors | Outputs | Writer families |
| --- | --- | --- | --- | --- |
| Producer $A$ | None | `Pre` | `Pre` | Two distinct occurrences contributing $1$ and $-1$ |
| Consumer $B$ | `Pre` | `Out`, `Audit` | `Out` | One square occurrence; one strict audit occurrence |

Wire the consumer's independently identified scalar `Pre` to the producer's
scalar output by an explicit one-point domain adapter. Choose identity
renaming where existing IDs are already disjoint, or compare by their
explicit provenance map. The composite has exactly three scalar tensors,
four writer occurrences and three publications.
Use upstream collector `Pre`, then consumer collectors `Out`, `Audit`.

The audit is **not** reciprocal of `Pre`. As in
[`IndexedCompositionParityTest`](../../leanncd/experiments/indexed_execution/IndexedCompositionParityTest.lean),
let $a$ be a rational parameter and let $V_a$ be the strict array obtained
by taking reciprocals of the two arguments $[2,a]$. Its body is
`Pre + at(V_a, 0)`. Selecting coordinate zero still evaluates the entire
array, including the other reciprocal.

| Ordered event | $a=0$ | $a=4$ |
| --- | --- | --- |
| 1 | Produce $1$ for `Pre` | Same |
| 2 | Produce $-1$ for `Pre` | Same |
| 3 | Publish `Pre = 0` | Same |
| 4 | Produce `Out = square(Pre) = 0` | Same |
| 5 | Publish `Out = 0` | Same |
| 6 | Undefined `Audit`; fail | Produce `Audit = 1/2` |
| 7 | No event | Publish `Audit = 1/2`; complete |

In the first case, `Out` is published but there is no complete model and no
successful component result. In the second, the internal audit is retained
in the complete store. The existing
[`suppliedMatch`](../../leanncd/experiments/indexed_execution/IndexedCompositionFixtureProof.lean)
matches the whole fixture directly. The implemented
`IndexedComponentCompositionCorrespondenceTest` applies the general
correspondence theorem to the match constructed from two genuinely local
components, without another hand-authored four-occurrence match. Its executable
companion reobserves the six-event failure and seven-event completion,
without a boundary-copy event or duplicate collector.

## 9. Discriminating examples and counterexamples

| Case | Required judgment |
| --- | --- |
| Two private tensors share a display name or old UID | Freshen retained identities independently; never merge their equations or events. |
| Same-size ports with different intended coordinates | No implicit match. An explicit supported coordinate/raw-policy adapter is required. |
| Explicit axis permutation | Positive case: permute coordinates, raw arguments and policies together; retain ordered expression reads and their multiplicities. |
| Two equal contributions at one address | Keep two occurrences and capabilities. Deduplication changes collection, even if a cancellation example happens to mask it. |
| Nonempty defined tensor with an unwritten coordinate | Retain its empty-capability collector; publish additive zero. |
| Empty output wired to an empty input | Positive case: retain both port identities and the explicit empty-domain adapter; construct a present empty downstream binding at handoff. No address event can recover this metadata. |
| Missing empty external input | Reject at tensor validation; vacuous coordinate readiness is not input presence. |
| Upstream output available before private upstream failure | Upstream-first ranked composition still performs the private work and fails before starting the consumer. Output availability is not a handoff certificate. |
| Unranked upstream block plus an independent ready downstream writer | List priority alone may run the downstream writer. Outside the strict-phase theorem, not evidence that sealing supplies a barrier. |
| Downstream writer targets upstream `Pre` | Reject the interface/construction. Reopening its collector is open contribution assembly, not sealed value composition. |
| Select-first reciprocal shortcut | Reject as an equivalent implementation: it changes the strict failure case to completion. The existing fixture contains this negative control. |
| Copy inserted as a claimed process identity | Reject event-exact equality; it is only a possible value-level identity implementation. |
| Cyclic upstream model selected by downstream definedness | Outside the ranked partial-function fragment; retain whole-model pairs instead of silently choosing a model. |

## 10. Assumptions, obligations and remaining work

**Caller-supplied assumptions:** two genuine local component matches;
finite decidable typed universes; the fixed rational registry and operations;
exact whole-port coverage; explicit bijective boundary wiring and supported
domain adapters. Fresh identities are checked by the static constructor.
Rank certificates are additional future premises for ranked execution/function
corollaries, not static assumptions. No totality assumption.

**Proved static construction facts:** local transport correctness, complete
composite roles and metadata, closure acceptance, the occurrence bijection,
ordered priority equality and all nine match fields. Existing capability/fiber
results apply to the constructed match without additional assumptions.
Model restriction/gluing, restricted denotation, and denotational witness-span
coherence are also proved. Composite ranking, phase behavior and process
associativity remain unproved. None is replaced by assumed execution agreement.

**Recommendation over alternatives:**

- Local universes plus a disjoint sum avoid the unwanted obligations of a
  global declaration universe. A quotient of two full universes could encode
  the join, but adds dependent quotient bookkeeping without benefit here.
- Sealed whole-value ports avoid confusing additive writer assembly with
  sequential composition. Open ports are a separate future operation.
- Restricted domain adapters expose read-policy obligations; arbitrary
  coordinate bijections without policy transport are not sufficient.
- Static construction reuses the proved correspondence. A staged runner or
  copy adapter is unnecessary for the ranked, upstream-first case and would
  introduce another execution semantics or extra events.
- Indexed programs, explicit witnesses and ports are the smallest foundation
  matching the available theorem. The implemented witness-span interpretation
  packages their denotational meaning. St/Br and open-diagram interpretations
  remain future work; none substitutes for the explicit transport or
  match-construction obligations.

There is no known semantic blocker for this restricted target. The substantive
admitted-read/expression transport prerequisite and static component
match/closure/priority construction, complete-model gluing and denotational
category laws are now proved. Remaining unproved work is ranked phase execution
and source/process categorical laws.
Wider coordinate adapters, residual inputs, fan-out and open contribution
ports remain out of scope. Administrative graph spans provide semantic wires
and target units. Adjoining units to a source presentation remains a separate
packaging decision; requiring a
core `Program` identity under the unchanged event observation would instead
be a genuine obstruction, not a proof-engineering task.
