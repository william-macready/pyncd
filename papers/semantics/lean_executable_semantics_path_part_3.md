# Lean executable reference - 3. The category-theoretic organization

[Previous: 2. One notation, two presentations](lean_executable_semantics_path_part_2.md) | [Contents](README.md) | [Next: 4. What is implemented and proved](lean_executable_semantics_path_part_4.md)

## In this part

- [3. The category-theoretic organization](#3-the-category-theoretic-organization)
  - [3.1 Finite coordinate families: representation and contravariance](#31-finite-coordinate-families-representation-and-contravariance)
  - [3.2 Finite additive pushforward: covariance and multiplicity](#32-finite-additive-pushforward-covariance-and-multiplicity)
  - [3.3 Partial maps organize expression definedness](#33-partial-maps-organize-expression-definedness)
  - [3.4 State extension organizes operational refinement](#34-state-extension-organizes-operational-refinement)

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

```math
\textcolor{#5688C7}{f}^*:K^{\textcolor{#5688C7}{J}}\to K^{\textcolor{#5688C7}{I}},\qquad \textcolor{#5688C7}{f}^*(\textcolor{#398B83}{v})=\textcolor{#398B83}{v}\circ \textcolor{#5688C7}{f}.
```

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

```math
\textcolor{#5688C7}{d}_!:K^{\textcolor{#9D75C4}{O}}\to K^{\textcolor{#5688C7}{I}},\qquad
\textcolor{#5688C7}{d}_!(\textcolor{#398B83}{v})(p)=\bigoplus_{\substack{\textcolor{#9D75C4}{o}\in \textcolor{#9D75C4}{O}\\d(\textcolor{#9D75C4}{o})=p}}\textcolor{#398B83}{v}(\textcolor{#9D75C4}{o}).
```

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
formula in [Section 17.2](tensor_logic_semantics_part_ii.md#172-canonical-fiber-semantics).
Using that section's global valuation space, index strings, and projections,
write it as

```math
\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}=(\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}})_!
\left(\bigotimes_{r=1}^{m}
  \textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}_r}^{*}(\textcolor{#398B83}{\rho}(T_r))\right).
```

Here each pullback puts an operand on the common global valuation domain;
the product is pointwise semiring multiplication; output pushforward combines
the assignments in each output fiber. Repeated indices are encoded by the
maps, not by informal dimension-name matching. Empty fibers give $0_K$.
For the admitted bounded read-only fragment, `Term.collectedBody_correspondence`
and `AdmittedSource.collect_correspondence` now connect actual normalized
expressions and `Program.collect` to independently specified original-read
fibers. Each term's global domain is its read support union output support;
unused zero-extent declarations do not erase unrelated terms. The generic
theorems preserve factor order, repeated slots, empty fibers and multiplicity.

### 3.3 Partial maps organize expression definedness

At fixed $\textcolor{#398B83}{\rho}$ and admitted domain $\textcolor{#5688C7}{D}\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma})$,
an expression has the mathematical form

```math
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho}}:
\textcolor{#5688C7}{D}\to\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau}),\qquad
\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau})=\textcolor{#5688C7}{\tau}\sqcup\{\textcolor{#398B83}{\bot}\}.
```

This is a partial map of sets, represented by an arrow in the Kleisli category
of `Option`. Bind propagates undefinedness; pure embeds successful values.
For primitive $f$, the registry specifies its argument product, domain
$\textcolor{#398B83}{\mathcal D}_f$, and total meaning on that domain. It therefore supplies a
partial map from the argument product to its result type.

Strict assembly uses

```math
\textcolor{#398B83}{\mathop{\mathrm{sequence}}\nolimits}:
\prod_i\textcolor{#398B83}{\mathop{\mathrm{Option}}\nolimits}(A_i)
\to\textcolor{#398B83}{\mathop{\mathrm{Option}}\nolimits}\left(\prod_i A_i\right).
```

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
states to the model relation. `Event.Legal` and `Event.legal_step` certify the
executor's selected edges; `Execution.reaches` forgets its typed event path to
the existing reachability relation. These are not a new categorical interpreter;
a future backend must simulate their meaning, even if it batches several
edges or changes storage representation.

This is the organizing separation: **coordinate maps route; partial maps
interpret; additive pushforward collects; monotone publication makes completed
values readable.** The categorical explanation must not collapse these into
one unproved linear or monoidal interpretation.

---

[Previous: 2. One notation, two presentations](lean_executable_semantics_path_part_2.md) | [Contents](README.md) | [Next: 4. What is implemented and proved](lean_executable_semantics_path_part_4.md)
