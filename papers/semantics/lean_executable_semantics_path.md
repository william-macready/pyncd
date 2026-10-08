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
$\textcolor{#5688C7}{\Sigma}$ for declarations, $\textcolor{#5688C7}{\Gamma}$ for a variable context, $\textcolor{#5688C7}{\nu}$ for a
valuation, $\textcolor{#398B83}{\rho}$ for a complete environment, $\textcolor{#398B83}{\eta}$ for supplied inputs,
and $\textcolor{#A87C28}{\sigma}$ for a partial published store. A machine configuration is
$(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$. $\textcolor{#9D75C4}{s}$ is a statement identifier and $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$ an occurrence.

The mathematics uses the same
[notation color key](tensor_logic_semantics.md#notation-color-key) as the
specification, throughout the equations and correspondence tables:

| Color | Semantic role |
| --- | --- |
| $\textcolor{#5688C7}{\text{Blue}}$ | Domains, signatures, index binding, and coordinate maps |
| $\textcolor{#9D75C4}{\text{Purple}}$ | Program syntax and source identities, including tagged occurrences |
| $\textcolor{#398B83}{\text{Teal}}$ | Denotational values, expression results, and model equations |
| $\textcolor{#A87C28}{\text{Amber}}$ | Reference execution, published stores, accumulators, and readiness |
| $\textcolor{#C16C86}{\text{Rose}}$ | Compiled execution and physical representation, reserved for later refinement |

Color follows meaning, not spelling. Local coordinate maps are blue, while
an expression such as $\textcolor{#9D75C4}{e}$ is purple. Scalar algebra,
generic category notation, and ordinary mathematical punctuation remain
neutral. Lean identifiers and code examples retain their literal spelling
and are not recolored; in particular, the Lean declaration parameter `σ`
must not be confused with the mathematical published store
$\textcolor{#A87C28}{\sigma}$. The labels also make the guide usable in
monochrome. Math colors require no custom macros or CSS; named operators use
`\mathop{\mathrm{Name}}\nolimits` rather than GitHub's blocked `\operatorname`.
Use VS Code's
built-in Markdown math preview, or a browser Markdown preview with KaTeX
or MathJax support, as described in the linked color key.

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
parameter `σ` represents mathematical **$\textcolor{#5688C7}{\Sigma}$**, not the published store
$\textcolor{#A87C28}{\sigma}$; Lean's registry parameter `r` is not the dependency rank
$r:\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\to\mathbb N$.

| Mathematics | Lean representation | Specification |
| --- | --- | --- |
| Axis identity and extent | `Axis.uid`, `Axis.extent`; ordered `Shape := List Axis` | [3.1](tensor_logic_semantics.md#31-axes-and-identities), [4.1](tensor_logic_semantics.md#41-signatures-and-coordinate-domains) |
| $\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)$ | `Coord (σ.signature t).axes`, a product of bounded `Fin` coordinates; `Coord [] = Unit` | [4.1](tensor_logic_semantics.md#41-signatures-and-coordinate-domains) |
| Tensor value $\textcolor{#5688C7}{I}\to K$ | `Value K (.array s sh) = Coord sh.axes -> K s`; tensor signatures may also have rank zero | [4.2](tensor_logic_semantics.md#42-tensor-values), [13.2](tensor_logic_semantics.md#132-value-types-and-primitive-signatures) |
| Address $(T,p)$ | Dependent pair `Address σ := (t : σ.Tensor) × Coord (σ.signature t).axes` | [5.2](tensor_logic_semantics.md#52-partial-stores-and-available-values) |
| Complete $\textcolor{#398B83}{\rho}$; partial $\textcolor{#A87C28}{\sigma}$ | `Store K σ`; `PartialStore K σ`, with `Option` at each typed cell | [5](tensor_logic_semantics.md#5-environments-and-stores) |
| $\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma};\textcolor{#5688C7}{D}\vdash \textcolor{#9D75C4}{E}:\textcolor{#5688C7}{\tau}$ | `Expr K σ r Γ τ` on an already admitted valuation type | [13](tensor_logic_semantics.md#13-core-syntax-and-binding), [14](tensor_logic_semantics.md#14-structural-well-formedness) |
| $\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau})=\textcolor{#5688C7}{\tau}\sqcup\{\textcolor{#398B83}{\bot}\}$ | `Option (Value K τ)`; `some v` is success, `none` is $\textcolor{#398B83}{\bot}$ | [18.1](tensor_logic_semantics.md#181-successful-and-undefined-results) |
| $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\rrbracket}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$ | `interpret ops ρ e γ` | [18](tensor_logic_semantics.md#18-expression-interpretation-and-definedness) |
| $\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})$ | Membership in the list `footprint e γ`; repeated list entries do not change readiness | [23.2](tensor_logic_semantics.md#232-read-footprints-of-expressions) |
| $\textcolor{#A87C28}{\mathop{\mathrm{Eval}}\nolimits}_{\textcolor{#A87C28}{\sigma}}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})$ when ready | `evalReady ops p e γ = .evaluated ...`; `.notReady` means wait | [23.3](tensor_logic_semantics.md#233-stable-evaluation-from-a-partial-store) |

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

For an index set $\textcolor{#5688C7}{I}$, write $K^{\textcolor{#5688C7}{I}}=\{\textcolor{#398B83}{v}:\textcolor{#5688C7}{I}\to K\}$. This is the concrete Naperian
representation: the value functor $A\mapsto A^{\textcolor{#5688C7}{I}}=\mathop{\mathrm{Set}}\nolimits(\textcolor{#5688C7}{I},A)$ is
representable, with indexing and tabulation inverse by construction.
Finite tensor shapes supply products of finite index sets; the rank-zero
coordinate set is the singleton, not the empty set.

A coordinate map $\textcolor{#5688C7}{f}:\textcolor{#5688C7}{I}\to \textcolor{#5688C7}{J}$ induces a contravariant read map

$$
\textcolor{#5688C7}{f}^*:K^{\textcolor{#5688C7}{J}}\to K^{\textcolor{#5688C7}{I}},\qquad \textcolor{#5688C7}{f}^*(\textcolor{#398B83}{v})=\textcolor{#398B83}{v}\circ \textcolor{#5688C7}{f}.
$$

Thus $\textcolor{#5688C7}{I}\mapsto K^{\textcolor{#5688C7}{I}}$ has the contravariant finite-set organization
$\mathop{\mathrm{FinSet}}\nolimits^{op}\to\mathop{\mathrm{Set}}\nolimits$, or into additive commutative
monoids when $K$ has that structure. In
[`Collection.lean`](../../leanncd/LeanNCD/Semantics/Collection.lean),
`Family I K := I -> K` and `pullback f v := v ∘ f`.
Named expression reads implement the corresponding lookup directly through
`AdmittedRead`; they do not call `pullback` as a separate runtime operation.

Products organize binders and array values:
$K^{\textcolor{#5688C7}{I}\times \textcolor{#5688C7}{J}}\cong(K^{\textcolor{#5688C7}{J}})^{\textcolor{#5688C7}{I}}$ is ordinary currying. Lean's product valuation
spaces and function-valued arrays realize this structure. A checked layout
chooses an enumeration; it does not change the coordinate domain.

These are concrete function representations. They are not derived from a
strong-monoidal action of an abstract category $D$, and this layer does not
instantiate the full $D$-graded colored PROP in
[Naperian Typing](../NaperianTyping.md).

### 3.2 Finite additive pushforward: covariance and multiplicity

Given finite occurrences $\textcolor{#9D75C4}{O}$, a destination map $\textcolor{#5688C7}{d}:\textcolor{#9D75C4}{O}\to \textcolor{#5688C7}{I}$, and an additive
commutative monoid $K$, define

$$
\textcolor{#5688C7}{d}_!:K^{\textcolor{#9D75C4}{O}}\to K^{\textcolor{#5688C7}{I}},\qquad
\textcolor{#5688C7}{d}_!(\textcolor{#398B83}{v})(p)=\bigoplus_{\substack{\textcolor{#9D75C4}{o}\in \textcolor{#9D75C4}{O}\\d(\textcolor{#9D75C4}{o})=p}}\textcolor{#398B83}{v}(\textcolor{#9D75C4}{o}).
$$

This is covariant collection, not overwrite. `pushforward d v` implements it
as a finite sum with a destination filter. The landed laws are:

| Law | Lean theorem in [Collection](../../leanncd/LeanNCD/Semantics/Collection.lean) |
| --- | --- |
| $\textcolor{#5688C7}{d}_!(0)=0$; $\textcolor{#5688C7}{d}_!(\textcolor{#398B83}{v}\oplus \textcolor{#398B83}{w})=\textcolor{#5688C7}{d}_!(\textcolor{#398B83}{v})\oplus \textcolor{#5688C7}{d}_!(\textcolor{#398B83}{w})$ | `pushforward_zero`, `pushforward_add`; packaged as `pushforwardHom` |
| $(\mathop{\mathrm{id}}\nolimits)_!=\mathop{\mathrm{id}}\nolimits$ | `pushforward_id` |
| $\textcolor{#5688C7}{e}_!\circ \textcolor{#5688C7}{d}_!=(\textcolor{#5688C7}{e}\circ \textcolor{#5688C7}{d})_!$ | `pushforward_comp` |
| $(\textcolor{#5688C7}{d}\circ \textcolor{#5688C7}{q})_!(\textcolor{#398B83}{v}\circ \textcolor{#5688C7}{q})=\textcolor{#5688C7}{d}_!(\textcolor{#398B83}{v})$ for an occurrence equivalence $\textcolor{#5688C7}{q}:\textcolor{#9D75C4}{O}'\cong \textcolor{#9D75C4}{O}$ | `pushforward_relabel` |
| Collection over $\coprod_{\textcolor{#9D75C4}{s}} \textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$ equals combination of each statement's fiber collection | `pushforward_grouped` |

Identity and composition give the covariant finite-family organization into
additive commutative monoids; Lean proves these laws without constructing a
Mathlib `Functor`. Pullback is precomposition, but there are no additional
named pullback-law theorems in this module. No pullback/pushforward adjunction
or general Kan-extension construction has been formalized.

The coproduct is essential: equal values, duplicate bodies, and colliding
destinations do not identify the elements of $\textcolor{#9D75C4}{O}$. Relabeling an occurrence
set is an isomorphism; deleting duplicates is not.

The routing/collection structure also explains the canonical pure-einsum
formula in [Section 17.2](tensor_logic_semantics.md#172-canonical-fiber-semantics).
Using that section's global valuation space, index strings, and projections,
write it as

$$
\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}=(\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}})_!
\left(\bigotimes_{r=1}^{m}
  \textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}_r}^{*}(\textcolor{#398B83}{\rho}(T_r))\right).
$$

Here each pullback puts an operand on the common global valuation domain;
the product is pointwise semiring multiplication; output pushforward combines
the assignments in each output fiber. Repeated indices are encoded by the
maps, not by informal dimension-name matching. Empty fibers give $0_K$.
This is a mathematical decomposition of the specified formula. The generic
pushforward is landed, but the theorem connecting source pure-einsum
elaboration to this formula and the contribution core remains unproved.

### 3.3 Partial maps organize expression definedness

At fixed $\textcolor{#398B83}{\rho}$ and admitted domain $\textcolor{#5688C7}{D}\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma})$,
an expression has the mathematical form

$$
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\rrbracket}_{\textcolor{#398B83}{\rho}}:
\textcolor{#5688C7}{D}\to\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau}),\qquad
\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau})=\textcolor{#5688C7}{\tau}\sqcup\{\textcolor{#398B83}{\bot}\}.
$$

This is a partial map of sets, represented by an arrow in the Kleisli category
of `Option`. Bind propagates undefinedness; pure embeds successful values.
For primitive $f$, the registry specifies its argument product, domain
$\textcolor{#398B83}{\mathcal D}_f$, and total meaning on that domain. It therefore supplies a
partial map from the argument product to its result type.

Strict assembly uses

$$
\textcolor{#398B83}{\mathop{\mathrm{sequence}}\nolimits}:
\prod_i\textcolor{#398B83}{\mathop{\mathrm{Option}}\nolimits}(A_i)
\to\textcolor{#398B83}{\mathop{\mathrm{Option}}\nolimits}\left(\prod_i A_i\right).
$$

All actual components must succeed; the empty product succeeds.
[`Interpret.lean`](../../leanncd/LeanNCD/Semantics/Interpret.lean) implements
this with `sequence` and `Option` binds. This describes the categorical
organization of the definitions, not a landed categorical interpreter or a
claim that partial maps retain all cartesian-closed structure of sets.

Collection begins **after** every admitted body has a successful value.
It combines values in $K$, not in `Option K`. In particular, $\textcolor{#398B83}{\bot}$ is not
a zero summand and the strict result type is not assumed to be a semiring.
Arbitrary primitives are partial set maps, not additive homomorphisms:
$f(x)\oplus f(y)$ cannot be replaced by $f(x\oplus y)$ without a separate
value-and-definedness theorem.

### 3.4 State extension organizes operational refinement

Published stores have the extension preorder $\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#A87C28}{\sigma}'$:
every available value in $\textcolor{#A87C28}{\sigma}$ remains available and unchanged in
$\textcolor{#A87C28}{\sigma}'$. This can be viewed as a thin category. Contribution steps leave
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
| $c_K$, $T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k]$, $\mathbf 1_{\textcolor{#9D75C4}{Q}}$ | `Expr.lit`, `.read`, `.iverson` |
| $\textcolor{#9D75C4}{E}_1\oplus \textcolor{#9D75C4}{E}_2$, $\textcolor{#9D75C4}{E}_1\otimes \textcolor{#9D75C4}{E}_2$ | `.binary .add`, `.binary .mul`; both results must succeed |
| $\bigoplus_{j\in[n]}\textcolor{#9D75C4}{E}$ | `.reduce n body`; ordered `foldValues` over `List.finRange n` |
| $\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{\textcolor{#5688C7}{J}}(\textcolor{#9D75C4}{E})$ | `.tab sh layout body`; `sequence` assembles a complete function array |
| $\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#9D75C4}{E},p)$ | `.at e index`; first obtain the complete array value |
| $f(\textcolor{#9D75C4}{E}_1,\ldots,\textcolor{#9D75C4}{E}_q)$ | `.prim f args`; assemble all arguments, then `Registry.apply` checks the domain |

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
\textcolor{#398B83}{\rho}|_{\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})}
=\textcolor{#398B83}{\rho}'|_{\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})}
\Longrightarrow
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\rrbracket}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\rrbracket}_{\textcolor{#398B83}{\rho}',\textcolor{#5688C7}{\nu}}
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
and $\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$, define:

$$
\textcolor{#9D75C4}{O}_T=\coprod_{\substack{\textcolor{#9D75C4}{s}\in \textcolor{#9D75C4}{P}\\T_{\textcolor{#9D75C4}{s}}=T}}\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}},
\qquad
\textcolor{#5688C7}{d}_T(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})=\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu}),
\qquad
\textcolor{#398B83}{v}^{\textcolor{#398B83}{\rho}}_T(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})=\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\textcolor{#398B83}{\rrbracket}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}.
$$

`P.Occurrence t` is the dependent pair of a statement `Fin` tag and a
guard-admitted valuation subtype. The mathematical global $\textcolor{#9D75C4}{\mathcal O}_{\textcolor{#9D75C4}{P}}$
is correspondingly the disjoint union of these families over defined
tensors. Guards exclude valuations before body demand.

| Mathematics | Lean |
| --- | --- |
| $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$ | `{v : Fin (P.valuations t s) // P.guard t s v = true}` |
| $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}$, $\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}$ | `P.destination t s`, `P.body t s` |
| $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\textcolor{#398B83}{\rrbracket}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$ | `P.outcome ops ρ t o` |
| $\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$ | `P.AdmEnv ops ρ` |
| Successful value $\textcolor{#398B83}{v}^{\textcolor{#398B83}{\rho}}_T(\textcolor{#9D75C4}{o})$ | `P.contribution ops ρ h t o`, extracted using admission proof `h` |
| $\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)=\textcolor{#5688C7}{d}_{T!}(\textcolor{#398B83}{v}^{\textcolor{#398B83}{\rho}}_T)$ | `P.collect ops ρ h t`, directly defined using `pushforward` |

This last equality is the actual organizing implementation, not a categorical
analogy attached to an imperative collector. `collect_grouped` and
`collect_relabel` transfer the generic laws to program collection.

[`Models.lean`](../../leanncd/LeanNCD/Semantics/Models.lean) expresses
[Section 20](tensor_logic_semantics.md#20-program-models-and-functional-denotation):

$$
\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})
\iff
\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})
\ \land\ \textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{In}}}=\textcolor{#398B83}{\eta}
\ \land\
\forall T\in\textcolor{#5688C7}{\mathrm{Def}},p,\
\textcolor{#398B83}{\rho}(T)[p]=\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[p].
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

`AdmInput` is $\exists!\textcolor{#398B83}{\rho},\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$.
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
| $(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$ | `Running.published`, `.accumulators`, `.pending` |
| $\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ | `P.initial η`: supplied inputs, zero accumulators, all admitted tags pending |
| $\textcolor{#A87C28}{U}\cap\textcolor{#9D75C4}{\mathcal C}_{\textcolor{#9D75C4}{P}}(T,p)=\varnothing$ | `P.FiberEmpty c t p` |
| $\textcolor{#A87C28}{\mathrm{CONTRIBUTE}}$ | `Step.contribute`: selected tag pending, `.evaluated (some v)`; add at its destination and erase that tag |
| $\textcolor{#A87C28}{\mathrm{PUBLISH}}$ | `Step.publication`: unpublished defined coordinate, empty pending fiber; publish its retained accumulator |
| $\textcolor{#A87C28}{\mathrm{UNDEFINED}}$ | `Step.undefined`: selected tag pending, `.evaluated none`; enter `.failed t o c` with the unchanged snapshot |
| $\textcolor{#A87C28}{\longrightarrow}^*$ | `P.Reaches ops` |
| Complete / successful / blocked | `P.Complete`, `P.Successful ops η`, `P.Blocked ops` |
| Complete $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$ | `P.finalStore c complete` |

`pending` is a family of finite sets, one per defined tensor, equivalent to
the global tagged pending set. Zero-valued contributions still erase their
tag. Empty fibers publish available zero explicitly. Accumulators are not
readable before publication; published coordinates cannot be overwritten.
Completion requires every declared address and every occurrence, not only
the designated outputs. `failed_terminal` proves failure has no outgoing step.

For [Section 26.1](tensor_logic_semantics.md#261-basic-conservation-invariants),
`Invariant` in
[`Invariants.lean`](../../leanncd/LeanNCD/Semantics/Invariants.lean) retains
proof-only consumed values $\textcolor{#398B83}{v}_{\textcolor{#9D75C4}{o}}$ and states

$$
\textcolor{#A87C28}{\alpha}(T,p)=
\bigoplus_{\textcolor{#9D75C4}{o}\in\textcolor{#9D75C4}{\mathcal C}_{\textcolor{#9D75C4}{P}}(T,p)\setminus \textcolor{#A87C28}{U}}\textcolor{#398B83}{v}_{\textcolor{#9D75C4}{o}}.
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
| `successful_model` | Reached completion constructs $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}\in\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ |
| `successful_unique` | Every model equals that complete $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$ |
| `successful_admInput` | Reached success proves $\textcolor{#398B83}{\eta}\in\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})$ |
| `successful_denotation` | $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\rrbracket}(\textcolor{#398B83}{\eta})=\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}\vert_{\textcolor{#5688C7}{\mathrm{Out}}}$ |
| `failed_no_model` | Reached ready-undefined failure implies $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\varnothing$ |

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
\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)=
\bigcup_{\textcolor{#9D75C4}{o}\in\textcolor{#9D75C4}{\mathcal C}_{\textcolor{#9D75C4}{P}}(a)}\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o}),
\qquad
b\in\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)\Longrightarrow r(b)<r(a).
$$

Dependencies are on **coordinates**, not tensor names. Finite history cells
of the same tensor can have strictly increasing ranks. All strict operand
and whole-array reads must be retained. Rank is independent of input values
and certifies readiness, not membership in primitive domains.

Define the measure

$$
\textcolor{#A87C28}{\mu}(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})
=|\textcolor{#A87C28}{U}|+
|\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}\setminus\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})|.
$$

Prove that contribution and publication decrease it by one and failure is
terminal. This finite-transition bound does not require rank.
Initially $\textcolor{#A87C28}{\mu}=|\textcolor{#9D75C4}{\mathcal O}_{\textcolor{#9D75C4}{P}}|+|\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}|$, so a run
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
\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})\textcolor{#A87C28}{\Downarrow}\textcolor{#398B83}{\rho}
\quad\Longleftrightarrow\quad
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\{\textcolor{#398B83}{\rho}\}
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
\textcolor{#A87C28}{\mathsf{Success}}(\textcolor{#398B83}{\rho})
&\Longrightarrow
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\{\textcolor{#398B83}{\rho}\}
\ \land\
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\rrbracket}(\textcolor{#398B83}{\eta})=\textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{Out}}},\\
\textcolor{#A87C28}{\mathsf{Failed}}(\textcolor{#9D75C4}{o},\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})
&\Longrightarrow
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\varnothing.
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
