# From Tensor Logic semantics to a Lean executable reference

## 1. Purpose, authority, and current position

This document connects the mathematics of
[Tensor Logic: Operational and Denotational Semantics](tensor_logic_semantics.md)
to the landed Lean definitions and proofs, and describes the remaining path to
an executable reference that we can debug and validate. It is a roadmap and
code correspondence guide, not an implementation plan or a new semantic contract.
The specification remains authoritative.

**Snapshot: 2026-10-07, local main `071323a`.** The expression/readiness,
collection/model, and reference-machine soundness developments have landed.
The public entry is
[`LeanNCD.Semantics`](../../leanncd/LeanNCD/Semantics.lean), imported by
[`LeanNCD`](../../leanncd/LeanNCD.lean). They are a semantic validation layer,
separate from the production DSL evaluator and execution backends.

The central distinction is:

- **Expressions already have computational interpretation.** For concrete
  computable carriers, operations, and registries, Lean can evaluate
  `interpret`, `footprint`, and `evalReady`. Concrete finite collections also
  compute, as the existing guards demonstrate.
- **Models are a mathematical relation.** `Models` and `AdmInput` are
  propositions; `denotation` selects a unique model nonconstructively. It is
  not an executable equation solver.
- **The reference machine is currently a relation.** `Step` specifies legal
  transitions and `Reaches` specifies finite reachability. Its updates are
  currently noncomputable; fixtures construct runs by proofs, not by a scheduler.
- **Reached-run soundness is proved.** Any reached success yields the unique
  complete model; any reached ready-undefined failure excludes every model.
  Progress, termination, and executable scheduling remain to be supplied.

The intended path is therefore:

```text
typed expressions + strict interpretation + read stability       LANDED
                         |
tagged additive collection + complete model relation              LANDED
                         |
reference transitions + conservation + reached-run soundness      LANDED
                         |
coordinate ranks + finite measure + maximal-run correspondence    NEXT
                         |
computable state/step selection + validated reference executor    REMAINING
                         |
source correspondence + differential debugging                    REMAINING
                         |
compiled storage/backend refinement                              LATER
```

The executor can first operate on directly constructed admitted core programs.
A source elaborator is necessary for comparing source programs with production,
not for first running and debugging the core semantics.

## 2. One notation, two presentations

Use the specification's notation throughout:
$\Sigma$ for declarations, $\Gamma$ for a variable context, $\nu$ for a
valuation, $\rho$ for a complete environment, $\eta$ for supplied inputs,
and $\sigma$ for a partial published store. A machine configuration is
$(\sigma,\alpha,U)$. $s$ is a statement identifier and $o=(s,\nu)$ an occurrence.

The specification fixes a scalar carrier $K$. Lean generalizes this to a
family `K : S -> Type`, allowing typed scalar sorts and heterogeneous primitive
signatures. To recover the specification's single-carrier fragment, specialize
to one sort. In formulas below, $K$ means that specialization, or the carrier
of the particular defined tensor being collected.

Recovering the full exact-semiring interpretation also requires choosing the
specified semiring operations as `ScalarOps` and supplying their laws where
needed. The general Lean interface does not enforce this identification.
The collection and soundness results use weaker additive hypotheses.

Two naming collisions must not obscure the correspondence: Lean's declaration
parameter `σ` represents mathematical **$\Sigma$**, not the published store
$\sigma$; Lean's registry parameter `r` is not the dependency rank
$r:\operatorname{Addr}_{\Sigma}\to\mathbb N$.

| Mathematics | Lean representation | Specification |
| --- | --- | --- |
| Axis identity and extent | `Axis.uid`, `Axis.extent`; ordered `Shape := List Axis` | [3.1](tensor_logic_semantics.md#31-axes-and-identities), [4.1](tensor_logic_semantics.md#41-signatures-and-coordinate-domains) |
| $\operatorname{Coord}_{\Sigma}(T)$ | `Coord (σ.signature t).axes`, a product of bounded `Fin` coordinates; `Coord [] = Unit` | [4.1](tensor_logic_semantics.md#41-signatures-and-coordinate-domains) |
| Tensor value $I\to K$ | `Value K (.array s sh) = Coord sh.axes -> K s`; tensor signatures may also have rank zero | [4.2](tensor_logic_semantics.md#42-tensor-values), [13.2](tensor_logic_semantics.md#132-value-types-and-primitive-signatures) |
| Address $(T,p)$ | Dependent pair `Address σ := (t : σ.Tensor) × Coord (σ.signature t).axes` | [5.2](tensor_logic_semantics.md#52-partial-stores-and-available-values) |
| Complete $\rho$; partial $\sigma$ | `Store K σ`; `PartialStore K σ`, with `Option` at each typed cell | [5](tensor_logic_semantics.md#5-environments-and-stores) |
| $\Sigma;\Gamma;D\vdash E:\tau$ | `Expr K σ r Γ τ` on an already admitted valuation type | [13](tensor_logic_semantics.md#13-core-syntax-and-binding), [14](tensor_logic_semantics.md#14-structural-well-formedness) |
| $\operatorname{Result}(\tau)=\tau\sqcup\{\bot\}$ | `Option (Value K τ)`; `some v` is success, `none` is $\bot$ | [18.1](tensor_logic_semantics.md#181-successful-and-undefined-results) |
| $\llbracket E\rrbracket_{\rho,\nu}$ | `interpret ops ρ e γ` | [18](tensor_logic_semantics.md#18-expression-interpretation-and-definedness) |
| $\operatorname{Read}(E,\nu)$ | Membership in the list `footprint e γ`; repeated list entries do not change readiness | [23.2](tensor_logic_semantics.md#232-read-footprints-of-expressions) |
| $\operatorname{Eval}_{\sigma}(E,\nu)$ when ready | `evalReady ops p e γ = .evaluated ...`; `.notReady` means wait | [23.3](tensor_logic_semantics.md#233-stable-evaluation-from-a-partial-store) |

The representations and expression constructors are in
[`Types.lean`](../../leanncd/LeanNCD/Semantics/Types.lean) and
[`Expr.lean`](../../leanncd/LeanNCD/Semantics/Expr.lean).
`Declarations.uid` is injective: tensor identity is not string matching.
`Layout.enumerate : Fin count ≃ Coord sh` certifies a complete coordinate
enumeration, including zero-extent shapes.

### Admission is not yet elaboration

Lean's `Γ` is a **type of valuations**, rather than a list of named variables.
Reduction extends it to `Γ × Fin n`; tabulation extends it to
`Γ × Coord sh.axes`. This realizes the lifted body domains, but does not yet
formalize named binding, capture-avoiding substitution, or flattening a source
valuation domain to a finite enumeration.

Likewise, `AdmittedRead` supplies a resolved bounded coordinate or a constant,
with a proof that its read policy agrees with that resolution. The
specification's bounded-read fragment uses the coordinate case. Constant and
remapped boundary reads are explicit extensions explored by
[the boundary-policy note](tensor_logic_boundary_policies.md), not silently
adopted clauses of the core specification. A rejecting read cannot inhabit
the admitted interface at that valuation.

Destinations are already bounded coordinates. These types establish admission
of the constructed objects, not a runtime checker for malformed source text
or arbitrary raw write indices.

## 3. The category-theoretic organization

The design uses different mathematical structures for indexing, definedness,
collection, and execution. Keeping these layers distinct prevents a tempting
but incorrect conclusion: that every operation is a linear tensor morphism.

### 3.1 Finite coordinate families: representation and contravariance

For an index set $I$, write $K^I=\{v:I\to K\}$. This is the concrete Naperian
representation: the value functor $A\mapsto A^I=\operatorname{Set}(I,A)$ is
representable, with indexing and tabulation inverse by construction.
Finite tensor shapes supply products of finite index sets; the rank-zero
coordinate set is the singleton, not the empty set.

A coordinate map $f:I\to J$ induces a contravariant read map

$$
f^*:K^J\to K^I,\qquad f^*(v)=v\circ f.
$$

Thus $I\mapsto K^I$ has the contravariant finite-set organization
$\operatorname{FinSet}^{op}\to\operatorname{Set}$, or into additive commutative
monoids when $K$ has that structure. In
[`Collection.lean`](../../leanncd/LeanNCD/Semantics/Collection.lean),
`Family I K := I -> K` and `pullback f v := v ∘ f`.
Named expression reads implement the corresponding lookup directly through
`AdmittedRead`; they do not call `pullback` as a separate runtime operation.

Products organize binders and array values:
$K^{I\times J}\cong(K^J)^I$ is ordinary currying. Lean's product valuation
spaces and function-valued arrays realize this structure. A checked layout
chooses an enumeration; it does not change the coordinate domain.

These are concrete function representations. They are not derived from a
strong-monoidal action of an abstract category $D$, and this layer does not
instantiate the full $D$-graded colored PROP in
[Naperian Typing](../NaperianTyping.md).

### 3.2 Finite additive pushforward: covariance and multiplicity

Given finite occurrences $O$, a destination map $d:O\to I$, and an additive
commutative monoid $K$, define

$$
d_!:K^O\to K^I,\qquad
d_!(v)(p)=\bigoplus_{\substack{o\in O\\d(o)=p}}v(o).
$$

This is covariant collection, not overwrite. `pushforward d v` implements it
as a finite sum with a destination filter. The landed laws are:

| Law | Lean theorem in [Collection](../../leanncd/LeanNCD/Semantics/Collection.lean) |
| --- | --- |
| $d_!(0)=0$; $d_!(v\oplus w)=d_!(v)\oplus d_!(w)$ | `pushforward_zero`, `pushforward_add`; packaged as `pushforwardHom` |
| $(\operatorname{id})_!=\operatorname{id}$ | `pushforward_id` |
| $e_!\circ d_!=(e\circ d)_!$ | `pushforward_comp` |
| $(d\circ q)_!(v\circ q)=d_!(v)$ for an occurrence equivalence $q:O'\cong O$ | `pushforward_relabel` |
| Collection over $\coprod_s D_s$ equals combination of each statement's fiber collection | `pushforward_grouped` |

Identity and composition give the covariant finite-family organization into
additive commutative monoids; Lean proves these laws without constructing a
Mathlib `Functor`. Pullback is precomposition, but there are no additional
named pullback-law theorems in this module. No pullback/pushforward adjunction
or general Kan-extension construction has been formalized.

The coproduct is essential: equal values, duplicate bodies, and colliding
destinations do not identify the elements of $O$. Relabeling an occurrence
set is an isomorphism; deleting duplicates is not.

The routing/collection structure also explains the canonical pure-einsum
formula in [Section 17.2](tensor_logic_semantics.md#172-canonical-fiber-semantics).
Using that section's global valuation space, index strings, and projections,
write it as

$$
V_L=(\pi_L)_!
\left(\bigotimes_{r=1}^{m}
  \pi_{L_r}^{*}(\rho(T_r))\right).
$$

Here each pullback puts an operand on the common global valuation domain;
the product is pointwise semiring multiplication; output pushforward combines
the assignments in each output fiber. Repeated indices are encoded by the
maps, not by informal dimension-name matching. Empty fibers give $0_K$.
This is a mathematical decomposition of the specified formula. The generic
pushforward is landed, but the theorem connecting source pure-einsum
elaboration to this formula and the contribution core remains unproved.

### 3.3 Partial maps organize expression definedness

At fixed $\rho$ and admitted domain $D\subseteq\operatorname{Val}(\Gamma)$,
an expression has the mathematical form

$$
\llbracket E\rrbracket_\rho:
D\to\operatorname{Result}(\tau),\qquad
\operatorname{Result}(\tau)=\tau\sqcup\{\bot\}.
$$

This is a partial map of sets, represented by an arrow in the Kleisli category
of `Option`. Bind propagates undefinedness; pure embeds successful values.
For primitive $f$, the registry specifies its argument product, domain
$\mathcal D_f$, and total meaning on that domain. It therefore supplies a
partial map from the argument product to its result type.

Strict assembly uses

$$
\operatorname{sequence}:
\prod_i\operatorname{Option}(A_i)
\to\operatorname{Option}\left(\prod_i A_i\right).
$$

All actual components must succeed; the empty product succeeds.
[`Interpret.lean`](../../leanncd/LeanNCD/Semantics/Interpret.lean) implements
this with `sequence` and `Option` binds. This describes the categorical
organization of the definitions, not a landed categorical interpreter or a
claim that partial maps retain all cartesian-closed structure of sets.

Collection begins **after** every admitted body has a successful value.
It combines values in $K$, not in `Option K`. In particular, $\bot$ is not
a zero summand and the strict result type is not assumed to be a semiring.
Arbitrary primitives are partial set maps, not additive homomorphisms:
$f(x)\oplus f(y)$ cannot be replaced by $f(x\oplus y)$ without a separate
value-and-definedness theorem.

### 3.4 State extension organizes operational refinement

Published stores have the extension preorder $\sigma\sqsubseteq\sigma'$:
every available value in $\sigma$ remains available and unchanged in
$\sigma'$. This can be viewed as a thin category. Contribution steps leave
the published store unchanged; publication extends it. Ready interpretation
is stable along such extensions on its footprint.

The transition graph also generates finite execution paths.
`Step` and `Reaches` represent edges and finite reachability, respectively;
`Reaches` is propositional, not an executable trace container or a
formalized free-category interface. Soundness relates reachable complete
states to the model relation. A future executor must select these same edges;
a future backend must simulate their meaning, even if it batches several
edges or changes storage representation.

This is the organizing separation: **coordinate maps route; partial maps
interpret; additive pushforward collects; monotone publication makes completed
values readable.** The categorical explanation must not collapse these into
one unproved linear or monoidal interpretation.

## 4. What is implemented and proved

### 4.1 Strict expressions and stable ready evaluation

The constructors map directly to
[Sections 18.2-18.4](tensor_logic_semantics.md#182-scalar-constructors):

| Core expression | Lean constructor and interpretation |
| --- | --- |
| $c_K$, $T[e_1,\ldots,e_k]$, $\mathbf 1_Q$ | `Expr.lit`, `.read`, `.iverson` |
| $E_1\oplus E_2$, $E_1\otimes E_2$ | `.binary .add`, `.binary .mul`; both results must succeed |
| $\bigoplus_{j\in[n]}E$ | `.reduce n body`; ordered `foldValues` over `List.finRange n` |
| $\operatorname{tab}_J(E)$ | `.tab sh layout body`; `sequence` assembles a complete function array |
| $\operatorname{at}(E,p)$ | `.at e index`; first obtain the complete array value |
| $f(E_1,\ldots,E_q)$ | `.prim f args`; assemble all arguments, then `Registry.apply` checks the domain |

The correspondence is more than constructor naming.
[`Completeness.lean`](../../leanncd/LeanNCD/Semantics/Completeness.lean)
proves `sequence_some_iff`, `tab_complete`, `reduce_defined_iff`,
`reduce_empty`, `at_some_iff`, and `prim_some_iff`: these state the successful
result conditions of the mathematical clauses.

Algebraic hypotheses are deliberately local. `ScalarOps` contains operations
as data and imposes no semiring laws. `interpret_reduce_sum` identifies the
ordered reduction with $\bigoplus$ when the selected carrier has
`AddCommMonoid` and the supplied `zero` and `add` equal its identity and
addition. It does not assume those equalities for every carrier.

For [Section 23.3](tensor_logic_semantics.md#233-stable-evaluation-from-a-partial-store),
[`Readiness.lean`](../../leanncd/LeanNCD/Semantics/Readiness.lean) proves:

$$
\rho|_{\operatorname{Read}(E,\nu)}
=\rho'|_{\operatorname{Read}(E,\nu)}
\Longrightarrow
\llbracket E\rrbracket_{\rho,\nu}
=\llbracket E\rrbracket_{\rho',\nu}
\qquad\texttt{interpret\_stable}.
$$

`evalWith_stable` is the analogous partial-store theorem.
`checkReads_iff` validates the Boolean readiness check, and `ready_consistent`
equates ready evaluation with interpretation in an agreeing complete
environment. Its stronger whole-store use is `evaluated_consistent` in
[`Invariants.lean`](../../leanncd/LeanNCD/Semantics/Invariants.lean).

Use the three cases of `evalReady`:

```text
.notReady                 footprint unavailable: wait
.evaluated (some v)       ready, defined value v
.evaluated none           ready, undefined result bot
```

The low-level `evalWith` returns only `Option`; its `none` alone cannot
classify waiting versus undefinedness. A mathematical complete-extension
witness in `ready_complete_extension` is not a zero-fill runtime fallback.
Whole-array footprints and both strict operands remain required even when
one entry is selected or another operand is zero.

### 4.2 Occurrences, collection, and models

[`Program.lean`](../../leanncd/LeanNCD/Semantics/Program.lean) presents
[Sections 9 and 19](tensor_logic_semantics.md#9-programs-and-contribution-occurrences)
using local statement tags for each defined tensor. For a fixed target $T$
and $\rho\in\operatorname{AdmEnv}(P)$, define:

$$
O_T=\coprod_{\substack{s\in P\\T_s=T}}D_s,
\qquad
d_T(s,\nu)=\phi_s(\nu),
\qquad
v^\rho_T(s,\nu)=\llbracket E_s\rrbracket_{\rho,\nu}.
$$

`P.Occurrence t` is the dependent pair of a statement `Fin` tag and a
guard-admitted valuation subtype. The mathematical global $\mathcal O_P$
is correspondingly the disjoint union of these families over defined
tensors. Guards exclude valuations before body demand.

| Mathematics | Lean |
| --- | --- |
| $D_s$ | `{v : Fin (P.valuations t s) // P.guard t s v = true}` |
| $\phi_s$, $E_s$ | `P.destination t s`, `P.body t s` |
| $\llbracket E_s\rrbracket_{\rho,\nu}$ | `P.outcome ops ρ t o` |
| $\rho\in\operatorname{AdmEnv}(P)$ | `P.AdmEnv ops ρ` |
| Successful value $v^\rho_T(o)$ | `P.contribution ops ρ h t o`, extracted using admission proof `h` |
| $\operatorname{Collect}_P(\rho)(T)=d_{T!}(v^\rho_T)$ | `P.collect ops ρ h t`, directly defined using `pushforward` |

This last equality is the actual organizing implementation, not a categorical
analogy attached to an imperative collector. `collect_grouped` and
`collect_relabel` transfer the generic laws to program collection.

[`Models.lean`](../../leanncd/LeanNCD/Semantics/Models.lean) expresses
[Section 20](tensor_logic_semantics.md#20-program-models-and-functional-denotation):

$$
\rho\in\operatorname{Models}(P,\eta)
\iff
\rho\in\operatorname{AdmEnv}(P)
\ \land\ \rho|_{\mathrm{In}}=\eta
\ \land\
\forall T\in\mathrm{Def},p,\
\rho(T)[p]=\operatorname{Collect}_P(\rho)(T)[p].
$$

The Lean predicate is `P.Models ops η ρ`.
`ValidInput` requires tensor-level presence exactly for input tensors,
including empty inputs. `InputAgreement` supplies the middle conjunct;
the final conjunct quantifies over all defined tensors, including nonoutputs.
No prior candidate value is a collection seed.

`models_fixedpoint` identifies these equations with a fixed point of
`equationOperator` on its admitted domain. This operator neither specifies
iteration nor guarantees its result remains admitted.
`models_relabel` and `models_grouped` preserve the model relation.

`AdmInput` is $\exists!\rho,\operatorname{Models}(P,\eta)$.
`denotation` is the unique model's `outputProjection`, using
`Classical.choose`; `denotation_of_model` proves agreement with any supplied
model under the uniqueness premise. A unique output projection alone is
not enough.

### 4.3 Reference transitions and conservation

[`Machine.lean`](../../leanncd/LeanNCD/Semantics/Machine.lean) is the direct
presentation of
[Sections 24-25](tensor_logic_semantics.md#24-machine-configurations-and-initialization):

| Specification | Lean |
| --- | --- |
| $(\sigma,\alpha,U)$ | `Running.published`, `.accumulators`, `.pending` |
| $\operatorname{Init}(P,\eta)$ | `P.initial η`: supplied inputs, zero accumulators, all admitted tags pending |
| $U\cap\mathcal C_P(T,p)=\varnothing$ | `P.FiberEmpty c t p` |
| $\mathrm{CONTRIBUTE}$ | `Step.contribute`: selected tag pending, `.evaluated (some v)`; add at its destination and erase that tag |
| $\mathrm{PUBLISH}$ | `Step.publication`: unpublished defined coordinate, empty pending fiber; publish its retained accumulator |
| $\mathrm{UNDEFINED}$ | `Step.undefined`: selected tag pending, `.evaluated none`; enter `.failed t o c` with the unchanged snapshot |
| $\longrightarrow^*$ | `P.Reaches ops` |
| Complete / successful / blocked | `P.Complete`, `P.Successful ops η`, `P.Blocked ops` |
| Complete $\rho_\sigma$ | `P.finalStore c complete` |

`pending` is a family of finite sets, one per defined tensor, equivalent to
the global tagged pending set. Zero-valued contributions still erase their
tag. Empty fibers publish available zero explicitly. Accumulators are not
readable before publication; published coordinates cannot be overwritten.
Completion requires every declared address and every occurrence, not only
the designated outputs. `failed_terminal` proves failure has no outgoing step.

For [Section 26.1](tensor_logic_semantics.md#261-basic-conservation-invariants),
`Invariant` in
[`Invariants.lean`](../../leanncd/LeanNCD/Semantics/Invariants.lean) retains
proof-only consumed values $v_o$ and states

$$
\alpha(T,p)=
\bigoplus_{o\in\mathcal C_P(T,p)\setminus U}v_o.
$$

This is `conservation` via `spent`. `inputs` preserves supplied inputs;
`published` states that each published defined fiber is exhausted and its
value equals its accumulator. `consumed` says every consumed body still
interprets to its recorded value in every complete environment agreeing
with published cells.

`StateInvariant` existentially hides the history; it is not an extra runtime
field or an obligation for a caller to supply a model witness.
`reachable_invariant` proves it for every reached running or failed state.

### 4.4 What reached-run soundness establishes

[`Soundness.lean`](../../leanncd/LeanNCD/Semantics/Soundness.lean) proves the
central implications in
[Sections 26.2-26.3](tensor_logic_semantics.md#262-preservation-of-every-candidate-model):

| Theorem | Mathematical conclusion |
| --- | --- |
| `candidate_preserved` | Every candidate model agrees with every reached published store; a reached failed state is incompatible with that model |
| `successful_model` | Reached completion constructs $\rho_\sigma\in\operatorname{Models}(P,\eta)$ |
| `successful_unique` | Every model equals that complete $\rho_\sigma$ |
| `successful_admInput` | Reached success proves $\eta\in\operatorname{AdmInput}(P)$ |
| `successful_denotation` | $\llbracket P\rrbracket(\eta)=\rho_\sigma|_{\mathrm{Out}}$ |
| `failed_no_model` | Reached ready-undefined failure implies $\operatorname{Models}(P,\eta)=\varnothing$ |

No rank certificate, pre-existing model, or semiring multiplication law is
required for these results. Collection and conservation need
`AddCommMonoid` only on participating defined carriers; body operations
remain explicit data.

The crucial missing converse is that an appropriate execution reaches such
a terminal outcome. Blocking is not undefinedness and does not exclude a
model. In particular, unique-model existence for a cyclic program does not
establish executability by this machine.

### 4.5 Existing validation and its limits

The execution records distinguish observed computation, proof checking,
mutation controls, and unsupported claims:

| Landed layer | Tests | Validation record |
| --- | --- | --- |
| Strict expressions/readiness | [ExpressionTest](../../leanncd/test/Semantics/ExpressionTest.lean), [NativeTest](../../leanncd/test/Semantics/NativeTest.lean), [ContractTest](../../leanncd/test/Semantics/ContractTest.lean) | [Expression/readiness execution](expression_readiness_execution_record.md) |
| Collection/models | [CollectionModelTest](../../leanncd/test/Semantics/CollectionModelTest.lean) | [Collection/model execution](collection_model_execution_record.md) |
| Reference transitions/soundness | [ReferenceMachineTest](../../leanncd/test/Semantics/ReferenceMachineTest.lean) | [Reference-machine execution](reference_machine_execution_record.md) |

All are discovered by the default `Tests` target. Existing fixtures cover
strict zero multiplication, empty binders, whole-array selection obligations,
heterogeneous primitives, duplicate contributions, colliding destinations,
empty input presence, nonoutput equations, publication barriers, and failure
versus unavailable reads. The machine fixtures include a proved successful
run and failure exclusion, but are not runtime executions by a scheduler.
The cyclic blocked fixture is not separately proved reachable.

Native expression fixtures use checked binary32/binary64 primitive APIs and
observe rounding differences. They do not give machine floats exact additive
laws or connect a floating-point backend to the complete-model theorem.
Generic collection allows an appropriate Boolean OR additive structure, but
these collection/model fixtures do not establish a Boolean OR instance or
its execution profile.
The earlier [semantic-core spike](tensor_logic_semantic_core_spike_record.md)
and `ContractTest` supply a narrow signed-coordinate `StMat` seam, not a full
categorical interpretation or source correspondence.

## 5. Remaining work, in dependency order

### 5.1 Next: ranked progress, finite termination, and correspondence

The immediate proof target is
[Section 23.4](tensor_logic_semantics.md#234-coordinate-dependencies-and-the-ranked-fragment)
and [Section 26.4](tensor_logic_semantics.md#264-finite-execution-and-progress-for-ranked-programs).
These definitions and theorems are not yet supplied by the semantic modules.

Define dependencies from existing footprints:

$$
\operatorname{Dep}(a)=
\bigcup_{o\in\mathcal C_P(a)}\operatorname{Read}(o),
\qquad
b\in\operatorname{Dep}(a)\Longrightarrow r(b)<r(a).
$$

Dependencies are on **coordinates**, not tensor names. Finite history cells
of the same tensor can have strictly increasing ranks. All strict operand
and whole-array reads must be retained. Rank is independent of input values
and certifies readiness, not membership in primitive domains.

Define the measure

$$
\mu(\sigma,\alpha,U)
=|U|+
|\operatorname{Addr}_{\mathrm{Def}}\setminus\operatorname{dom}(\sigma)|.
$$

Prove that contribution and publication decrease it by one and failure is
terminal. This finite-transition bound does not require rank.
Initially $\mu=|\mathcal O_P|+|\operatorname{Addr}_{\mathrm{Def}}|$, so a run
has at most that many non-failure steps; an undefined step is terminal rather
than another running-state decrease.
Then use the reachable invariant and a minimum-rank unpublished defined
coordinate to prove progress: either its pending fiber has a ready occurrence,
enabling contribution or undefinedness, or its exhausted fiber enables
publication. Ranked reachable noncomplete states cannot block.

Together with existing soundness, the target is:

- Every **maximal** ranked run succeeds or explicitly fails; an arbitrary
  finite prefix stopped by a scheduler is not maximal.
- If a model exists, every maximal run succeeds with that unique model.
- If no model exists, every maximal run fails.
- Successful schedules give the same complete environment. Failing schedules
  may identify different first undefined occurrences.

This supplies the reverse direction missing from reached-run soundness:

$$
\operatorname{Init}(P,\eta)\Downarrow\rho
\quad\Longleftrightarrow\quad
\operatorname{Models}(P,\eta)=\{\rho\}
\qquad\text{for the coordinate-ranked fragment}.
$$

Acceptance cases should discriminate a ranked same-tensor history, empty-fiber
publication, a ready undefined primitive, and an unsupported unranked cycle.
A source rank checker need not enumerate all coordinates: an explicitly
supplied certificate is sufficient for this semantic proof stage.

### 5.2 Make the reference machine computational

The next executable capability must implement the relation, not redefine it.
For a concrete computable profile, supply:

1. Computable finite address and occurrence enumeration, equality, and state
   updates, replacing or refining the current noncomputable presentation.
   Function-valued arrays may remain extensional or acquire finite storage
   with a proved lookup/tabulation correspondence.
2. A step selector that checks pending tags, `evalReady`, and publication
   barriers. Prove each selected update is a `Step`, and that a reachable
   noncomplete ranked state cannot be incorrectly reported as having no step.
3. A driver with the proved finite bound and explicit terminal outcomes.
   Derive success/model and failure/no-model correctness from the existing
   soundness and new progress results. Budget exhaustion must not look like
   success or prove model nonexistence.
4. A trace recording selected statement/valuation tags, destinations, readiness,
   contributions, publications, and the exact failure snapshot. Formatting
   and finer primitive diagnostics can refine this information without changing
   definedness or rules.

A deterministic scheduling order makes debugging reproducible; alternative
legal schedules test independence of successful results. No fairness assumption
is needed for maximal runs under the finite, nonstuttering rules.
For unrestricted programs, blocking must remain distinct from undefinedness;
for the certified ranked profile, reachable blocking is excluded by proof.

The specification's exact-real carrier is not a promise of an exact-real
runtime. A first executable oracle can use exact rationals and an explicitly
supported primitive registry. Real transcendental operators, exact Complex
proof fixtures, and native floating-point execution have different computational
requirements. State the profile and reject unsupported cases explicitly.

### 5.3 Validate the executable core against the equations

Promote suitable existing logical fixtures into **actual executor runs**,
with assertions on outcomes and intermediate transitions, not only final
output values. Add the worked examples from
[Sections 21](tensor_logic_semantics.md#21-worked-denotational-examples)
and [27](tensor_logic_semantics.md#27-worked-operational-examples) within
the chosen computational profile.

For small exact cases, compare the returned complete store with independently
specified expected values and directly check all model equations. Compare
multiple legal schedules and require agreement on all defined coordinates.
Neither computation of collection in a supplied candidate environment nor
verification of one model is by itself an equation solver or uniqueness proof;
the ranked execution theorems provide that justification.

Controls must fail for the reasons the mathematics requires: occurrence
deduplication, early publication, missing-input zero-fill, unavailable-as-zero,
undefined-as-zero, skipped internal equations, and changed nonlinear boundaries.
This adds runtime discrimination to the existing proof/type mutation evidence.

### 5.4 Connect named source syntax and the production evaluator

For debugging source programs, establish the bridge in
[Sections 13-17](tensor_logic_semantics.md#part-ii-core-language-and-surface-elaboration)
and [19.3](tensor_logic_semantics.md#193-correspondence-with-pure-einsum).
The admitted core already interprets bodies; what remains is to justify how
source expressions become those bodies and domains:

- Named UID-based contexts, renaming, and capture-avoiding substitution,
  related to the existing typed valuation spaces.
- Structural checking and elaboration preserving guards, bounded reads/writes,
  lifted binder domains, and statement/valuation multiplicity.
- Pure-einsum correspondence, including term-local contraction, diagonal
  reads/writes, repeated output indices, and empty domains.
- Source permutation connected to existing occurrence-relabeling laws;
  corresponding successful-execution relabeling still needs a bridge.
- Explicit nonlinear boundaries: operator-before-collection and
  operator-after-collection are different programs.

Then use the executable core as an oracle for the production pipeline on the
**shared supported fragment**. Locate discrepancies by layer: source admission,
elaboration, body interpretation, occurrence collection, dependency/readiness,
publication, or backend arithmetic.

The [semantic gap audit](tensor_logic_semantic_gap_audit.md) records the known
production divergence for multiple statements defining one LHS: production
does not yet implement the specification's cross-statement additive collection.
The new semantic layer does. This must be tracked as an explicit contract
difference, not hidden by weakening the oracle or counted as a newly discovered
regression. First comparisons can use a clearly stated single-definition
fragment, without discarding collision or within-statement contraction checks.

### 5.5 Later: compiled and numerical refinement

[Part V](tensor_logic_semantics.md#part-v-compilation-and-refinement) supplies
the next contract beyond a debug-capable reference executor:
logical-to-physical representations, kernel contracts, simulation/progress,
batching, and buffer liveness for scans. Rank alone never justifies overwriting
a still-needed value. A checked production plan is not automatically a
certificate for these new semantics.

Floating-point correspondence needs its own ordered-reduction or numerical
correctness criterion. Exact commutative pushforward laws do not imply bitwise
schedule independence. Full $D$-graded categorical interpretation, general
cyclic solving, and configurable boundary-policy integration are also separate
extensions, not prerequisites silently added to the core executor.

## 6. The milestone we are working toward

A debug-capable Lean reference is complete for a stated profile when a
validated input and admitted ranked core program produce an inspectable,
finite execution, with proved legal transitions, and:

$$
\begin{aligned}
\mathsf{Success}(\rho)
&\Longrightarrow
\operatorname{Models}(P,\eta)=\{\rho\}
\ \land\
\llbracket P\rrbracket(\eta)=\rho|_{\mathrm{Out}},\\
\mathsf{Failed}(o,\sigma,\alpha,U)
&\Longrightarrow
\operatorname{Models}(P,\eta)=\varnothing.
\end{aligned}
$$

The driver must reach one of these outcomes on the certified ranked profile;
invalid input, unsupported capabilities, and unsupported dependency forms are
explicit admission errors, not successful values.
The landed soundness work already proves the implications **for reached
states**. The next proof and executable stages establish that a real Lean
driver reaches them and exposes enough evidence to debug the path.

The endpoint is an executable realization of the specified equations, not
zero-seeded fixed-point iteration, a floating-point solver presented as exact
mathematics, or a proof that the existing production compiler already refines
the semantics.
