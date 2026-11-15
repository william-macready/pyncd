# Chapter 3. Partial computations: bodies, strictness and footprints

**Summary.** A Tensor Logic body can fail, because a primitive such as
$\log$ is defined on only part of its argument space, and the semantics
records that failure as a separate result $\bot$ that is never a number.
This chapter organizes partiality in the category
$\mathbf{Pfn}=\mathrm{Kl}(\mathrm{Option})$, shows what strict pairing and
strict batching are as categorical structure and exactly where their
naturality fails, and then defines the read footprint, the set of addresses
that determines a body's result and that an executor must have before it
may evaluate.

## 1. Why bodies are partial

[Chapter 2](02-index-categories.md) worked with total maps (it previewed the
partial case only after Proposition 2.9). Restriction
$f^\ast$, pushforward $f_!$ and pointwise products are defined on every
family, because reads of a complete environment always succeed and
$\oplus,\otimes$ are total operations on $K$. Statement bodies, however, may
also apply *primitives*, and a primitive comes with a domain.

The primitive registry of the specification
([Part II, Section 13.2](../semantics/tensor_logic_semantics_part_ii.md#132-value-types-and-primitive-signatures))
gives each operator $f$ an arity $q$, input types $\tau_1,\dots,\tau_q$, an
output type $\tau$, and a domain
$\mathcal{D}_f\subseteq\tau_1\times\cdots\times\tau_q$. The meaning of $f$
is a deterministic function on $\mathcal{D}_f$, with no hidden reads and no
side effects. Over exact reals
([Part I, Section 8](../semantics/tensor_logic_semantics_part_i.md#8-operators-predicates-and-definedness)):

| Primitive | Type | Domain $\mathcal{D}_f$ |
| --- | --- | --- |
| $\mathrm{relu}$ | $\mathbb{R}\to\mathbb{R}$ | all of $\mathbb{R}$ |
| $\log$ | $\mathbb{R}\to\mathbb{R}$ | $x>0$ |
| $\sqrt{\cdot}$ | $\mathbb{R}\to\mathbb{R}$ | $x\ge 0$ |
| reciprocal | $\mathbb{R}\to\mathbb{R}$ | $x\neq 0$ |
| $\mathrm{softmax}_m$ | $\mathbb{R}^{[m]}\to\mathbb{R}^{[m]}$ | all of $\mathbb{R}^{[m]}$ if $m>0$; empty if $m=0$ |

The last row is worth a moment. Softmax is *registered* at every $m\ge 0$,
so a statement whose slice domain is empty type checks. Such a statement has
no occurrences and never demands the application. But a demanded application
to the empty array is undefined, since $\mathcal{D}_{\mathrm{softmax}_0}=\varnothing$.

Typing does not decide definedness. The expression `reciprocal(0)` is a
well-typed real scalar expression; it is undefined. An out-of-bounds tensor
read is different: it is rejected by the structural checks of Part II and
never becomes a typed expression that "happens to be undefined". Partiality
in this chapter is always value-dependent failure of a primitive, never a
malformed access.

**Definition 3.1 (result space).** For a value type $\tau$, the result space
is the tagged disjoint union

$$\mathrm{Result}(\tau)=V_\tau\sqcup\{\bot\},$$

where $V_\tau$ is the set of values of type $\tau$ ($K$ for a scalar,
$K^{\mathrm{Coord}}$ for an array; the specification writes $\tau$ for this
set). A member $v$ of
$V_\tau$ is a successful result; $\bot$ is the undefined result. We write
$[\![E]\!]_{\rho,\nu}\downarrow v$ when the result is the successful value
$v$, and $[\![E]\!]_{\rho,\nu}=\bot$ when it is undefined. The arrow
$\downarrow$ means definedness, not termination of a machine.

$\bot$ is a tag, and it is easy to mistake it for three things it is not
(CONVENTIONS fact 3):

1. **Not a scalar.** In particular it is not $0_K$. It cannot be a summand
   in collection, and $0_K\otimes\bot$ is not $0_K$.
2. **Not a missing store entry.** A missing entry means "not known yet"; the
   executor waits for it. $\bot$ means "known to fail". Section 6 keeps
   these apart.
3. **Not NaN.** A floating-point NaN is a value that flows through further
   arithmetic. $\bot$ is not a value of $K$ at all.

Moreover $\bot$ carries no order, and no least fixed point is ever taken:
the models of a program are *all* fixed points of its equation operator
([Chapter 4](04-denotational.md)). The order $\preceq$ defined in
Section 3 (and used in Sections 4 and 5) compares two computations; it is
never used to choose a solution.

**Example 3.2 (the running example).** In `Scorer`, the bodies of s1 and s2
are semiring expressions in reads, and s3 applies $\mathrm{relu}$, which is
total. Only s4, $L[]\mathrel{+}=\log(Y[1])$, can fail. Take the complete
environment built from the primary input $\eta_1$: $Z=(0,4)$, $Y=(0,4)$.
Then $[\![\log(Y[1])]\!]_{\rho,()}\downarrow\log 4$. Now take the failing
input $\eta_0$ ($X=(0,0)$, same $W,B$). The values that the collected
equations force are $Z=(1,0)$ and $Y=(1,0)$, and in any complete environment
with $\rho(Y)[1]=0$ we get $[\![\log(Y[1])]\!]_{\rho,()}=\bot$, because
$0\notin\mathcal{D}_{\log}$. One undefined body is enough:
$\mathrm{Models}(P,\eta_0)=\varnothing$ (Chapter 4), and the machine takes
UNDEFINED at occurrence $(s4,())$ ([Chapter 5](05-operational.md)).

*Why this matters for an agentic coder.* The type of a body's meaning is
not $K$ but $\mathrm{Result}(K)$. Code that returns `0.0` or `NaN` for a
failed primitive has silently changed the type, and every later law about
collection and models will be applied to the wrong objects. Represent
failure with an option-like type, and never coerce it to a scalar.

## 2. Pfn as the Kleisli category of Option

Partial maps compose, and they form a category. Its cleanest description
uses a monad (see [Chapter 0](00-prerequisites.md) for monads and Kleisli
categories). This section restates Chapter 0's Proposition 0.16 and the
sequence laws of its Proposition 0.18 in the notation used here, and adds
what Chapter 0 does not: the monoidal structure and the failure of its
naturality. Notation changes from Chapter 0: the Kleisli composite is written
$\diamond$, the batched map is $\mathrm{batch}_I(f)$ (Chapter 0's $p^I$), and
$f^I$ here is the unsequenced map $A^I\to(\mathrm{Option}\,B)^I$.

**Definition 3.3 (Pfn and Option).** The category $\mathbf{Pfn}$ has sets as
objects. A morphism $f:A\rightharpoonup B$ is a function from a subset
$\mathrm{dom}\,f\subseteq A$ to $B$. The identity is the total identity.
The composite $g\circ f$ has domain
$\{a\in\mathrm{dom}\,f\mid f(a)\in\mathrm{dom}\,g\}$ and sends $a$ to
$g(f(a))$. The *option monad* on $\mathbf{Set}$ is
$\mathrm{Option}\,A=A\sqcup\{\bot\}$ with unit
$\mathrm{some}_A:A\to\mathrm{Option}\,A$ (tag a value as successful) and
multiplication $\mathrm{join}_A:\mathrm{Option}\,\mathrm{Option}\,A\to\mathrm{Option}\,A$
(an inner or outer $\bot$ gives $\bot$; otherwise strip one tag). Its
Kleisli category $\mathrm{Kl}(\mathrm{Option})$ has a morphism $A\to B$ for
every function $A\to\mathrm{Option}\,B$, composed by
$g\diamond f=\mathrm{join}\circ\mathrm{Option}(g)\circ f$, with identities
$\mathrm{some}$. Note that $\mathrm{Result}(\tau)=\mathrm{Option}(V_\tau)$.

(We reserve $\eta$ for input environments, as in CONVENTIONS, so the unit of
the monad is written $\mathrm{some}$, which is also its Lean name.)

**Proposition 3.4** (Chapter 0, Proposition 0.16).
$\mathbf{Pfn}\cong\mathrm{Kl}(\mathrm{Option})$, by an
isomorphism that is the identity on objects.

*Proof.* Send $f:A\rightharpoonup B$ to $\hat f:A\to\mathrm{Option}\,B$,
$\hat f(a)=f(a)$ for $a\in\mathrm{dom}\,f$ and $\hat f(a)=\bot$ otherwise.
This is a bijection on hom-sets (recover $\mathrm{dom}\,f=\hat f^{-1}(B)$).
It sends identities to $\mathrm{some}$. For composition,
$(\hat g\diamond\hat f)(a)=\mathrm{join}(\mathrm{Option}(\hat g)(\hat f(a)))$
is $\bot$ if $\hat f(a)=\bot$ and is $\hat g(f(a))$ otherwise, which is
$\widehat{g\circ f}(a)$. $\square$

From now on we identify the two and drop the hats. The *Kleisli inclusion*
$\mathbf{Set}\to\mathbf{Pfn}$ sends a total map $h$ to $\mathrm{some}\circ h$;
we write it with the same letter. The *Kleisli lifting* of a total map
$h:A\to B$ to results is $\mathrm{Option}(h):\mathrm{Result}(A)\to\mathrm{Result}(B)$:
apply $h$ to a successful value, pass $\bot$ through. This is how every
total operation acts on results.

**Definition 3.5 (strict pairing and strict lifting).** Strict pairing is the
map
$$\mathrm{pair}_{A,B}:\mathrm{Option}\,A\times\mathrm{Option}\,B\to\mathrm{Option}(A\times B)$$
that returns $(a,b)$ when both components are successful and $\bot$
otherwise. For $f:C\rightharpoonup A$ and $g:C\rightharpoonup B$ the strict
pairing $\langle f,g\rangle:C\rightharpoonup A\times B$ is defined at $c$
exactly when both $f(c)$ and $g(c)$ are. For $f:A\rightharpoonup A'$ and
$g:B\rightharpoonup B'$, the product $f\times g:A\times B\rightharpoonup A'\times B'$
sends $(a,b)$ to $(f(a),g(b))$ when both are defined. Then
$\langle f,g\rangle=(f\times g)\circ\Delta_C$ with $\Delta_C$ the total
diagonal. For a binary scalar operation $\star\in\{\oplus,\otimes\}$, the
strict lifting is the composite of strict pairing and a total map:

$$\mathrm{lift}_2(\star)=\mathrm{Option}(\star)\circ\mathrm{pair}_{K,K}:\mathrm{Result}(K)\times\mathrm{Result}(K)\to\mathrm{Result}(K).$$

This is exactly the definition in
[Part III, Section 18.2](../semantics/tensor_logic_semantics_part_iii.md#182-scalar-constructors):
$u\star v$ when both are successful, $\bot$ otherwise. Anticipating Section 4, where $[\![E]\!]_\rho:D\rightharpoonup V_\tau$ is
the interpretation at fixed $\rho$, in $\mathbf{Pfn}$ we have
$[\![E_1\star E_2]\!]_\rho=\star\circ\langle[\![E_1]\!]_\rho,[\![E_2]\!]_\rho\rangle$.

**Proposition 3.6 (strict pairing is monoidal, not cartesian).**

1. $(\mathbf{Pfn},\times,1)$, with $\times$ on morphisms as in
   Definition 3.5 and the associator, unitors and symmetry of $\mathbf{Set}$,
   is a symmetric monoidal category.
2. It is not cartesian monoidal. The unit $1$ is not terminal in
   $\mathbf{Pfn}$ (the terminal object is $\varnothing$); the discard maps
   $!_A:A\to 1$ are not natural; and with the evident projections, the
   projection law $\pi_1\circ\langle f,g\rangle=f$ fails at every point
   where $f$ is defined and $g$ is not.

*Proof.* (1) $\mathrm{id}\times\mathrm{id}=\mathrm{id}$ is immediate. For
the interchange law, $(f'\circ f)\times(g'\circ g)$ and
$(f'\times g')\circ(f\times g)$ are both defined at $(a,b)$ exactly when
$f(a)$, $f'(f(a))$, $g(b)$ and $g'(g(b))$ are all defined, and then both
return $(f'(f(a)),g'(g(b)))$. The structure maps are total bijections. Their
naturality against partial maps is checked the same way: for the symmetry,
$\mathrm{swap}\circ(f\times g)$ and $(g\times f)\circ\mathrm{swap}$ are
both defined at $(a,b)$ exactly when $f(a)$ and $g(b)$ are; for the left
unitor, $\lambda\circ(\mathrm{id}_1\times f)$ and $f\circ\lambda$ are both
defined at $((),a)$ exactly when $f(a)$ is; the associator is similar with
three components. The pentagon, triangle and hexagon are equations between
total maps; they hold in $\mathbf{Set}$, and the Kleisli inclusion is a
functor.

(2) A partial map $A\rightharpoonup 1$ is determined by its domain, so
$\mathbf{Pfn}(A,1)$ is in bijection with the subsets of $A$ and has more
than one element when $A\neq\varnothing$. The only partial map into
$\varnothing$ is the nowhere-defined one, so $\varnothing$ is terminal (and
initial). Naturality of discard would require $!_B\circ f=!_A$ for every
$f:A\rightharpoonup B$; the left side has domain $\mathrm{dom}\,f$, the right
side has domain $A$. Finally, $\pi_1\circ\langle f,g\rangle$ is defined at
$c$ only when $g(c)$ is, while $f$ may be defined there. $\square$

**Example 3.7 (reciprocal).** Take $C=A=B=\mathbb{Q}$, $f=\mathrm{id}$,
$g=$ reciprocal with domain $\mathbb{Q}\setminus\{0\}$. Then
$\pi_1\circ\langle\mathrm{id},g\rangle$ is the identity restricted to
$\mathbb{Q}\setminus\{0\}$. At $c=0$ the left side is $\bot$ and
$\mathrm{id}(0)=0$. The value of the reciprocal was never used, yet its
failure is visible.

Two remarks. First, the interchange law holds because $\mathrm{Option}$ is a
*commutative* monad: running $f$ before $g$ or $g$ before $f$ gives the same
result. Lean's `do`-notation picks an order of binds; the result does not
depend on it. Second, $\mathbf{Pfn}$ does have categorical products, but they
are $A\sqcup B\sqcup(A\times B)$ (Exercise 1), which is not what Tensor Logic
computes. Copying *is* natural in $\mathbf{Pfn}$:
$\Delta_B\circ f=(f\times f)\circ\Delta_A$, since both sides are defined
where $f$ is. (Such structure is studied as *restriction categories*,
after Cockett and Lack; we do not need that theory.)

The consequence deserves a sentence of its own. Strict pairing is the
specification's choice: it defines $\mathrm{lift}_2$ that way
(Section 18.2), and a short-circuiting multiplication would still be a
morphism of $\mathbf{Pfn}$, just a different one. Given that $\star$ is
interpreted through strict pairing, dropping an operand whose value is
unused is an application of the naturality of discard, which Proposition 3.6
shows is false in $\mathbf{Pfn}$. A compiler pass that deletes such a
subcomputation is making exactly that mistake. The spec's rule that both
operands of $\otimes$ must be defined "even when one is $0_K$" is the
definition that makes this the case, applied to $0_K\otimes\log(-1)$; the
proposition explains why it cannot be relaxed without changing definedness.

*Why this matters for an agentic coder.* Dead-code elimination, common
subexpression elimination and short-circuit evaluation look like harmless
plumbing. In $\mathbf{Pfn}$ the first and the third are not equations. A
subterm may be dropped only when it is total on the inputs at hand, and that
is a fact to be proved, not assumed. (Duplicating or sharing a
deterministic subterm is fine for values, because copying is natural; it may
still change cost and diagnostics.)

## 3. sequence and batching

A reduction or a tabulation demands a whole family of body results, one per
coordinate. We need a single result for the family. That is the job of
`sequence`.

**Definition 3.8 (sequence).** For a finite set $I$ and a set $A$,
$$\mathrm{sequence}_I:(\mathrm{Option}\,A)^I\to\mathrm{Option}(A^I)$$
returns the family $(a_i)_{i\in I}$ when every component $x_i$ is the
successful value $a_i$, and $\bot$ when some component is $\bot$. More
generally, for a family of sets $(A_i)_{i\in I}$ it is the map
$\prod_i\mathrm{Option}(A_i)\to\mathrm{Option}(\prod_i A_i)$ with the same
rule.

The functor $(-)^I=\mathbf{Set}(I,-)$ is representable, and
$\mathrm{sequence}_I$ is its *traversal* with the Option effect: walk the
container, collect the effects, and succeed only if every position
succeeds. Functional programmers know it as `sequence` on fixed-length
vectors of options.

**Proposition 3.9 (laws of sequence).**

1. (empty) $\mathrm{sequence}_\varnothing$ sends the unique element of
   $(\mathrm{Option}\,A)^\varnothing=1$ to $\mathrm{some}$ of the empty family.
2. (naturality in $A$) For total $h:A\to B$,
   $\mathrm{Option}(h^I)\circ\mathrm{sequence}_I=\mathrm{sequence}_I\circ(\mathrm{Option}\,h)^I$.
3. (unit) $\mathrm{sequence}_I\circ(\mathrm{some}_A)^I=\mathrm{some}_{A^I}$.
4. (multiplication) $\mathrm{sequence}_I\circ(\mathrm{join}_A)^I=\mathrm{join}_{A^I}\circ\mathrm{Option}(\mathrm{sequence}_I)\circ\mathrm{sequence}_I$
   as maps $(\mathrm{Option}\,\mathrm{Option}\,A)^I\to\mathrm{Option}(A^I)$.
5. (sum) Under $A^{I\sqcup J}\cong A^I\times A^J$,
   $\mathrm{sequence}_{I\sqcup J}(x)=\mathrm{pair}\big(\mathrm{sequence}_I(x|_I),\mathrm{sequence}_J(x|_J)\big)$.
6. (singleton) Under $A^1\cong A$, $\mathrm{sequence}_1=\mathrm{id}$.

By (1), (5) and (6), $\mathrm{sequence}_{[n]}$ is iterated strict pairing.

*Proof.* Every statement has the same shape: both sides are $\bot$ exactly
when some innermost component is $\bot$, and otherwise both return the
evident family. For (2): both sides are $\bot$ iff some $x_i=\bot$; otherwise
both are $\mathrm{some}(h(a_i))_i$. For (3): every component is successful,
so the result is $\mathrm{some}(a)$. For (5): the left side succeeds iff
every component over $I\sqcup J$ succeeds, iff both restricted sequences
succeed, iff their strict pairing succeeds. (6) is immediate. (4) is the
multiplication law of the distributive law proved in Chapter 0,
Proposition 0.18; directly, both sides are defined iff every component is
$\mathrm{some}(\mathrm{some}\,a_i)$, and then both return $(a_i)_i$. $\square$

A natural transformation $\lambda:FT\Rightarrow TF$, from a functor $F$
composed with a monad $T$, that satisfies (3) and (4) is called a
*distributive law of the functor $F$ over the monad $T$* (also a Kleisli
law; Chapter 0, Definition 0.17). Proposition 3.9(2)-(4) says exactly that $\mathrm{sequence}_I$ is a
distributive law of $(-)^I$ over $\mathrm{Option}$ (this is Chapter 0,
Proposition 0.18). The standard payoff of a
distributive law is that $F$ lifts to the Kleisli category. Here is that
lifting.

**Definition 3.10 (batching).** For $f:A\rightharpoonup B$ and finite $I$,
$$\mathrm{batch}_I(f)=\mathrm{sequence}_I\circ f^I:A^I\rightharpoonup B^I,$$
where $f^I:A^I\to(\mathrm{Option}\,B)^I$ applies $f$ at each coordinate. So
$\mathrm{batch}_I(f)(a)$ is defined iff $f(a_i)$ is defined for every
$i\in I$, and then equals $(f(a_i))_i$.

**Proposition 3.11.** $\mathrm{batch}_I$ is a functor
$\mathbf{Pfn}\to\mathbf{Pfn}$ extending $(-)^I$: $\mathrm{batch}_I(h)=h^I$
for total $h$, $\mathrm{batch}_I(\mathrm{id})=\mathrm{id}$, and
$\mathrm{batch}_I(g\circ f)=\mathrm{batch}_I(g)\circ\mathrm{batch}_I(f)$.
For $I=\varnothing$, $\mathrm{batch}_\varnothing(f)=\mathrm{id}_1$ for every
$f$, including the nowhere-defined map.

*Proof.* The first two by Proposition 3.9(3). For composition, both sides
are defined at $a$ exactly when $f(a_i)$ and $g(f(a_i))$ are defined for
every $i$, with the same value. (The abstract proof uses 3.9(2) and (4).)
For $I=\varnothing$ there are no coordinates, so nothing is demanded.
$\square$

So batching is perfectly functorial in the *value* variable. The interesting
question is what happens in the *index* variable. A map $r:I\to J$ gives
restriction $r^\ast:A^J\to A^I$, $r^\ast a=a\circ r$ (Chapter 2,
Definition 2.6), on families of any set. To compare partial maps we need an
order on them.

**Definition 3.12 (definedness order).** For $h,k:A\rightharpoonup B$,
write $h\preceq k$ when every input on which $h$ succeeds also makes $k$
succeed with the same value: $h(a)\downarrow v\Rightarrow k(a)\downarrow v$.
Equivalently, the graph of $h$ is contained in the graph of $k$.

$\preceq$ is a partial order on each hom-set, and composition is monotone in
each argument, so $\mathbf{Pfn}$ is enriched in posets. A word on fact 3:
$\preceq$ is a relation between two partial maps with the same source and
target, namely inclusion of their graphs. It is not an order on
$\mathrm{Result}(\tau)$, and $\bot$ remains an unordered tag. We use it only
to compare *two computations*, typically a program and a proposed rewrite of
it. Nothing in the semantics is defined
as a least element or a limit of a chain in this order.

**Proposition 3.13 (lax naturality of batching).** For $r:I\to J$ in
$\mathbf{FinSet}$ and $f:A\rightharpoonup B$,
$$r_B^\ast\circ\mathrm{batch}_J(f)\ \preceq\ \mathrm{batch}_I(f)\circ r_A^\ast,$$
with equality when $f$ is total or $r$ is surjective.

The square, with the direction of the inequality marked:

```text
                 batch_J(f)
        A^J  -------------------->  B^J
         |                           |
  r_A^*  |                           |  r_B^*
         v            ⪯              v
        A^I  -------------------->  B^I
                 batch_I(f)

  (right then down)  ⪯  (down then right)
  restrict after batching is LESS defined than batching after restricting
```

*Proof.* First at the level of `sequence`. For $x\in(\mathrm{Option}\,A)^J$,
compare $\mathrm{Option}(r^\ast)(\mathrm{sequence}_J(x))$ with
$\mathrm{sequence}_I(r^\ast x)$. If the first succeeds, every $x_j$ is
successful, say $x_j=a_j$; in particular every $x_{r(i)}$ is, so the second
succeeds with $(a_{r(i)})_i=r^\ast a$, which is also the value of the first.
Hence $\mathrm{Option}(r^\ast)\circ\mathrm{sequence}_J\preceq\mathrm{sequence}_I\circ r^\ast$.
Now
$$r_B^\ast\circ\mathrm{batch}_J(f)=\mathrm{Option}(r^\ast)\circ\mathrm{sequence}_J\circ f^J\preceq\mathrm{sequence}_I\circ r^\ast\circ f^J=\mathrm{sequence}_I\circ f^I\circ r_A^\ast=\mathrm{batch}_I(f)\circ r_A^\ast,$$
using monotonicity of precomposition and $r^\ast\circ f^J=f^I\circ r^\ast$
(both send $a$ to $i\mapsto f(a_{r(i)})$).

Equality. If $r$ is surjective, every $j$ is some $r(i)$, so success of all
$x_{r(i)}$ implies success of all $x_j$, and the reverse inclusion of graphs
holds. If $f$ is total, $f^J$ lands in successful families, both sides are
total, and they agree by the inequality. $\square$

**Example 3.14 (the reciprocal of $(2,0)$).** Let $A=B=\mathbb{Q}$,
$f=$ reciprocal, $J=[2]$, $I=[1]$, and $r:[1]\to[2]$ the inclusion
$0\mapsto 0$. Take the family $a=(2,0)\in\mathbb{Q}^{[2]}$.

- Left side: $\mathrm{batch}_{[2]}(f)(2,0)$ demands $1/0$, so it is $\bot$,
  and $r^\ast(\bot)=\bot$.
- Right side: $r^\ast a=(2)$, and $\mathrm{batch}_{[1]}(f)(2)=(1/2)$.

The inequality is strict. Here $r$ is injective but not surjective, and $f$
is not total, so neither equality condition applies.

Two special cases are worth naming. For $I=\varnothing$, $r^\ast$ is the
discard $A^J\to A^\varnothing=1$ and $\mathrm{batch}_\varnothing(f)=\mathrm{id}_1$,
so the proposition reads $!\circ\mathrm{batch}_J(f)\preceq\,!$: the failure of
natural discard in Proposition 3.6 is lax naturality at the empty index
set. For $I=1$ and $r=p$ a point of $J$, $r^\ast$ is selection of the
coordinate $p$: this is the "select" in "select then compute".

This proposition is exactly CONVENTIONS fact 11. It kills the "select then
compute" optimisation in general. An optimiser that sees "build the whole
array of $f$-values, then read coordinate $p$" and replaces it by "read
coordinate $p$, then apply $f$" is replacing the left side of the square by
the right side. Proposition 3.13 says the right side is above the left in
$\preceq$: the rewrite can turn $\bot$ into a value, and it never does the
reverse. The categorical notes record this as an executed experiment
([categorical semantics, Section 6.3](../semantics/categorical_tensor_logic_semantics.md#63-effect-sequencing-results)):
tabulating reciprocal over $(2,0)$ and selecting the first entry fails, the
neighbouring case $(2,4)$ succeeds with $1/2$, and a deliberately different
select-first computation on $(2,0)$ returns $1/2$. That success is recorded
as evidence that the transformation is non-equivalent, not as an accepted
optimisation. The rewrite is valid only when $f$ is total, when $r$ is
surjective, or under a separate proof that the omitted applications
succeed.

A caveat from the source
([categorical semantics, Section 3.3](../semantics/categorical_tensor_logic_semantics.md#33-value-indexing-and-strict-effect-sequencing-are-separate)):
Proposition 3.13 is about applying one partial map pointwise. An array
primitive that consumes a whole tabulation, such as softmax, is not of this
form, and no general law is claimed for expressions with cross-coordinate
reads.

*Why this matters for an agentic coder.* Batching commutes with everything
in the value variable and only laxly in the index variable. Any rewrite that
narrows the set of coordinates on which a partial map is evaluated
(slicing before mapping, pushing a gather through an elementwise op, lazy
array construction) is a use of the false equation. Check the two equality
conditions, or do not perform the rewrite.

## 4. Interpretation of core expressions as a structural map into Pfn

Fix a complete environment $\rho$, an index context $\Gamma$, and an
admissible domain $D\subseteq\mathrm{Val}(\Gamma)$. For a well-formed
expression $E$ of type $\tau$, write $V_\tau$ for its value set:
$K$ for the scalar type, $K^{I_1\times\cdots\times I_m}$ for an array type
with $m\ge 1$
([Part II, Section 13.2](../semantics/tensor_logic_semantics_part_ii.md#132-value-types-and-primitive-signatures)).
The interpretation of Section 18 of the specification, read at fixed
$\rho$, is a partial map

$$[\![E]\!]_\rho:D\rightharpoonup V_\tau,\qquad \nu\mapsto[\![E]\!]_{\rho,\nu}.$$

A binder extends the
domain: the body of $\bigoplus_{j\in I_j}E$ or of $\mathrm{tab}_{j\in J}(E)$
is interpreted on $D\times I_j$ or $D\times J$, with $(\nu,k)$ standing for
the extended valuation $\nu[j\mapsto k]$.

Two maps from Chapter 2, Proposition 2.9 (the Naperian adjunction) do the
binding work. The unit, tabulation of the context,
$u_D:D\to(D\times J)^J$, $u_D(\nu)=(k\mapsto(\nu,k))$ (Chapter 2's
$\eta_\Gamma$, renamed because $\eta$ is reserved for inputs), and the counit,
evaluation, $\mathrm{ev}:K^J\times J\to K$, $\mathrm{ev}(V,p)=V[p]$.

**Definition 3.15 (Kleisli reading of the core constructors).** Each
constructor of [Part II, Section 13.3](../semantics/tensor_logic_semantics_part_ii.md#133-expression-constructors)
is read as a fixed operation of $\mathbf{Pfn}$ applied to the meanings of its
subterms:

| Constructor | Meaning in $\mathbf{Pfn}$ | Total? |
| --- | --- | --- |
| $c_K$ | constant map $\nu\mapsto c_K$ | yes |
| $\mathbf{1}_Q$ | $\nu\mapsto 1_K$ if $[\![Q]\!]_\nu$, else $0_K$ | yes |
| $T[e_1,\dots,e_k]$ | $\nu\mapsto\rho(T)[[\![e_1]\!]_\nu,\dots,[\![e_k]\!]_\nu]$ | yes, on complete $\rho$ |
| $E_1\star E_2$ | $\star\circ\langle[\![E_1]\!]_\rho,[\![E_2]\!]_\rho\rangle$, i.e. $\mathrm{lift}_2(\star)$ | iff both are |
| $\bigoplus_{j\in[n]}E$ | $\mathrm{fold}_n\circ\mathrm{batch}_{[n]}([\![E]\!]_\rho)\circ u_D$ | if the body is (always, if $n=0$) |
| $\mathrm{tab}_{j\in J}(E)$ | $\mathrm{batch}_J([\![E]\!]_\rho)\circ u_D$ | if the body is (always, if $J=\varnothing$) |
| $\mathrm{at}(E,(e_1,\dots,e_m))$ | $\mathrm{ev}\circ\langle[\![E]\!]_\rho,\iota_e\rangle$ | iff $[\![E]\!]_\rho$ is |
| $f(E_1,\dots,E_q)$ | $\mathrm{apply}_f\circ\langle[\![E_1]\!]_\rho,\dots,[\![E_q]\!]_\rho\rangle$ | not in general |

Here $\mathrm{fold}_n:K^{[n]}\to K$ is the total fold of $\oplus$ in ascending
order with $\mathrm{fold}_0=0_K$; $\iota_e:D\to J$ is the total index map
$\nu\mapsto([\![e_1]\!]_\nu,\dots,[\![e_m]\!]_\nu)$; and
$\mathrm{apply}_f:V_{\tau_1}\times\cdots\times V_{\tau_q}\rightharpoonup V_\tau$ is the
registry's partial map with domain $\mathcal{D}_f$. In the last row
$\langle\cdots\rangle$ is $q$-ary strict pairing, which by Proposition
3.9(5)-(6) is the dependent $\mathrm{sequence}_{[q]}$ (the arguments have
different types) after the total tupling into
$\prod_r\mathrm{Result}(\tau_r)$. A multi-binder tabulation uses $J=I_1\times\cdots\times I_m$.

Unfolding each row recovers Section 18 clause by clause:

- *Reads* are total because $\rho$ is complete and the structural premises
  put every index tuple in bounds
  ([Part III, Section 18.2](../semantics/tensor_logic_semantics_part_iii.md#182-scalar-constructors)).
- *Reduction.* $\mathrm{batch}_{[n]}([\![E]\!]_\rho)(u_D(\nu))$ is
  $\mathrm{sequence}_{[n]}$ of the family $k\mapsto[\![E]\!]_{\rho,\nu[j\mapsto k]}$.
  It succeeds iff every $v_k$ does, and then the fold gives
  $\bigoplus_k v_k$. For $n=0$, $\mathrm{batch}_\varnothing$ is
  $\mathrm{id}_1$ (Proposition 3.11), so the result is $0_K$. The composite
  contains no application of $[\![E]\!]_\rho$ at any point: "an empty
  reduction evaluates no body" is literally true of the formula. Its Lean form is `reduce_empty` in `Completeness.lean`: `evalWith ops p (.reduce 0 body) γ = some (ops s).zero`, whatever the body.
- *Tabulation* is the *Kleisli tabulation*: tabulate the context with the
  Naperian unit, then batch the body. In $\mathbf{Set}$, for a total body
  $g:D\times J\to K$, the composite $g^J\circ u_D$ is the curried map, the
  adjunct of Proposition 2.9. In $\mathbf{Pfn}$ the adjunct is replaced by
  the batched map: defined at $\nu$ only when every coordinate is. For
  $J=\varnothing$ it returns the unique empty array.
- *Selection* is postcomposition with the counit inside $\mathbf{Pfn}$. The
  index map is total, so $\langle[\![E]\!]_\rho,\iota_e\rangle$ is defined
  exactly where $[\![E]\!]_\rho$ is: selection needs the complete array, as
  [Section 18.4](../semantics/tensor_logic_semantics_part_iii.md#184-array-selection-and-primitive-application)
  requires.
- *Primitive application* sequences the arguments, then applies the
  registry's partial map.

Notice what happens to Chapter 2's equation
$\mathrm{at}(\mathrm{tab}_j(E),(p))=E[j:=p]$ in $\mathbf{Pfn}$. The left
side is $\mathrm{ev}_p\circ\mathrm{batch}_J([\![E]\!]_\rho)\circ u_D$, and
$\mathrm{ev}_p$ is $r^\ast$ for $r=p:1\to J$. Proposition 3.13 gives

$$[\![\mathrm{at}(\mathrm{tab}_{j\in J}(E),(p))]\!]_\rho\ \preceq\ [\![E[j:=p]]\!]_\rho,$$

with equality when the body is total. For an index map $\iota_e$ that
depends on $\nu$, apply Proposition 3.13 at each $\nu$ with
$r=\iota_e(\nu)$. So the $\beta$-equation that Chapter 2 derives from the
first triangle identity holds in $\mathbf{Pfn}$ only as an inequality (an
analogy with a lax adjunction; no adjunction in $\mathbf{Pfn}$ is claimed). Relatedly, the curry bijection of
Proposition 2.9 does not survive: two bodies undefined at different
coordinates of the same row tabulate to the same $\bot$, so
$g\mapsto\mathrm{batch}_J(g)\circ u_D$ is not injective on
$\mathbf{Pfn}(D\times J,K)$.

What "structural map" means here, honestly: the interpretation is defined
by recursion on syntax, and each clause is a fixed $\mathbf{Pfn}$ operation
on the meanings of the subterms. We do not claim a functor from a syntactic
category, or a symmetric monoidal interpretation of Tensor Logic in
$\mathbf{Pfn}$; the categorical notes say the prototype does not install a
general $\mathbf{Pfn}$ category or prove such an interpretation
([Section 3.2](../semantics/categorical_tensor_logic_semantics.md#32-partial-functions-provide-a-useful-semantic-category)),
and the Lean path document calls this "the categorical organization of the
definitions, not a landed categorical interpreter"
([Section 3.3](../semantics/lean_executable_semantics_path_part_3.md#33-partial-maps-organize-expression-definedness)).

**The Lean definitions.** The production development has exactly this
shape. In
[`Types.lean`](../../leanncd/LeanNCD/Semantics/Types.lean), a value type is
`Ty S` (constructors `scalar` and `array`), its values are
`Value K τ` (for an array, `Coord sh.axes → K s`), and the registry's
partial map is `Registry.apply`:

```lean
def Registry.apply (r : Registry K) (f : r.Op)
    (xs : (i : Fin (r.arity f)) → Value K (r.input f i)) : Option (Value K (r.output f)) :=
  if h : r.domain f xs = true then some (r.meaning f xs h) else none
```

The `domain` field is the Boolean test for $\mathcal{D}_f$, and `meaning`
needs a proof that the test passed: a total function on $\mathcal{D}_f$,
made partial by `apply`. (Lean is multi-sorted: `K : S → Type` assigns a
carrier to each sort; this chapter uses one carrier $K$.) The expression
type in
[`Expr.lean`](../../leanncd/LeanNCD/Semantics/Expr.lean) has the
constructors `Expr.lit`, `Expr.read`, `Expr.iverson`, `Expr.binary`,
`Expr.reduce`, `Expr.tab`, `Expr.at` and `Expr.prim`, indexed by a Lean type
`Γ` that is already the guard-admitted valuation space $D$ (binders extend
it to `Γ × Fin n` or `Γ × Coord sh.axes`). In
[`Interpret.lean`](../../leanncd/LeanNCD/Semantics/Interpret.lean), strict
assembly is `sequence`, defined over `Fin n` for a dependent family `A`:

```lean
def sequence : {n : Nat} → {A : Fin n → Type} →
    ((i : Fin n) → Option (A i)) → Option ((i : Fin n) → A i)
  | 0, _, _ => some (fun i => nomatch i)
  | _ + 1, _, f => do
      let x ← f 0
      let xs ← sequence (fun i => f i.succ)
      pure (Fin.cases x xs)
```

The two clauses are Proposition 3.9(1), and (5) with (6) for
$[n+1]=1\sqcup[n]$. Here `do`-notation is Kleisli composition: the block
`do let x ← m; k x` means $m$ followed by $k$ in $\mathrm{Kl}(\mathrm{Option})$,
and `pure` is $\mathrm{some}$. Reductions use `foldValues`:

```lean
def foldValues {V : Type} (ops : ScalarOps V) : List (Option V) → Option V
  | [] => some ops.zero
  | x :: xs => do
      let a ← x
      let b ← foldValues ops xs
      pure (ops.add a b)
```

This fuses `sequence` with the fold. Its definedness and value are
characterized by `foldValues_defined_iff` and `foldValues_some_map_sum`
(both in
[`Completeness.lean`](../../leanncd/LeanNCD/Semantics/Completeness.lean));
the fused statement itself is Exercise 7. It computes $v_0\oplus(v_1\oplus(\cdots\oplus(v_{n-1}\oplus 0_K)))$, which is
the spec's ascending fold under the monoid laws. The interpreter
`evalWith` takes a `PartialStore` (a function from addresses to `Option`)
and returns `Option (Value K τ)`, a Kleisli arrow out of `Γ`. Its binder,
selection and primitive clauses are the rows of Definition 3.15:

```lean
  | _, _, .reduce n body, γ =>
      foldValues (ops _) ((List.finRange n).map (fun i => evalWith ops store body (γ, i)))
  | _, _, .tab _ layout body, γ => do
      let xs ← sequence (fun i => evalWith ops store body (γ, layout.enumerate i))
      pure (fun p => xs (layout.enumerate.symm p))
  | _, _, .at e index, γ => do
      let xs ← evalWith ops store e γ
      pure (xs (index γ))
  | _, _, .prim f args, γ => do
      let xs ← sequence (fun i => evalWith ops store (args i) γ)
      r.apply f xs
```

The tabulation clause sequences over `Fin layout.count` and transports the
result along the bijection `layout.enumerate`. By the surjective case of
Proposition 3.13, sequencing commutes with reindexing along a bijection, so
the choice of layout does not affect the result. In Lean this follows from
`tab_complete` in `Completeness.lean`
(`evalWith ops p (.tab sh layout body) γ = some v ↔ ∀ c, evalWith ops p body (γ, c) = some (v c)`),
whose statement does not mention the layout. Finally, the complete-environment interpretation is
`evalWith` on the everywhere-successful store:

```lean
def interpret (ops : (s : S) → ScalarOps (K s)) (store : Store K σ)
    (e : Expr K σ r Γ τ) (γ : Γ) : Option (Value K τ) :=
  evalWith ops (fun a => some (store a)) e γ
```

`fun a => some (store a)` is the Kleisli inclusion of a complete
environment. Run on a genuinely partial store, `evalWith` is the ready
evaluation of Section 6, but only when the footprint is available; Section 6
explains the caveat.

One Lean detail goes beyond Section 18: `Expr.read` carries an
`AdmittedRead`, whose `resolved` field can be `.at p` (a coordinate, read at address `⟨t, p⟩`) or
`.const c` (a read that the admitted policy resolves to a constant). The
`.const` case evaluates to `some c` and contributes nothing to the
footprint. The in-bounds reads of Section 18.2 are the `.at` case.

*Why this matters for an agentic coder.* Each constructor's meaning is one
of a handful of $\mathbf{Pfn}$ combinators: constant, lifted total map,
strict pairing, batch after the Naperian unit, counit, registry partial
map. An implementation built from exactly these inherits strictness for
free; an evaluator that returns early from a product with a zero factor
has stopped using strict pairing, and computes a different (more defined)
morphism of $\mathbf{Pfn}$.

## 5. Definedness examples and transformation limits

Work over exact reals. The examples are those of
[Part III, Section 18.5](../semantics/tensor_logic_semantics_part_iii.md#185-definedness-examples-and-transformation-limits)
and [Section 21.3](../semantics/tensor_logic_semantics_part_iii.md#213-a-guard-differs-from-a-zero-multiplier),
read through Sections 2 to 4.

**Example 3.16 (strictness).**

1. $[\![\log(-1)]\!]_{\rho,\nu}=\bot$: $\mathrm{apply}_{\log}$ is undefined
   at $-1\notin\mathcal{D}_{\log}$.
2. $[\![0\otimes\log(-1)]\!]_{\rho,\nu}=\bot$: the strict pairing
   $\langle\mathrm{const}_0,[\![\log(-1)]\!]\rangle$ is undefined. In
   categorical terms, $\varnothing$ is a zero object of $\mathbf{Pfn}$, the
   nowhere-defined map is the zero morphism, and strict pairing with the zero
   morphism gives the zero morphism. The scalar $0_K$ is a successful value,
   not the zero morphism, so it cannot absorb $\bot$ (Exercise 6).
3. $[\![\bigoplus_{j\in[0]}\log(-1)]\!]_{\rho,\nu}=0$: by
   Proposition 3.11, $\mathrm{batch}_\varnothing=\mathrm{id}_1$; the body has
   no instances.

**Example 3.17 (complete-array interpretation).** Let $\rho(X)=(4,-1)$. Then
$$[\![\mathrm{at}(\mathrm{tab}_{j\in[2]}(\log(X[j])),(0))]\!]_{\rho,\nu}=\bot.$$
The tabulation is $\mathrm{batch}_{[2]}(\log)$ applied to $(4,-1)$, which
demands $\log(-1)$. Selecting coordinate $0$ afterwards cannot help. The
select-first computation $\log(X[0])$ would give $\log 4$. This is
Example 3.14 again with $f=\log$, the same $r:[1]\to[2]$, and the family
$(4,-1)$: the lax square is strict. (Chapter 2's running-example instance after
Proposition 2.9, $\mathrm{at}(\mathrm{tab}_j(\log(Y[j])),(1))$ on $\eta_1$,
is the strict case of Proposition 3.13 on `Scorer` itself.) The specification calls this "a
deliberate complete-array interpretation, not lazy coordinate selection".

**Example 3.18 (guard versus Iverson).** Let $X=(4,-1)$ be a real input and
$Y$ a defined tensor of shape $(2)$. The guarded core statement

$$\text{for }i\in[2]\text{ where }i<1:\quad Y[i]\mathrel{+}=\log(X[i])$$

has admissible domain $D=\{0\}\hookrightarrow[2]$, a subobject in
$\mathbf{FinSet}$. There is one occurrence, $i=0$, with body value
$\log 4$. The fibre of $(Y,1)$ is empty, so collection gives $0_K$ there,
and the unique model has $Y[0]=\log 4$, $Y[1]=0$. Replace the guard by an
Iverson factor:

$$\text{for }i\in[2]:\quad Y[i]\mathrel{+}=\mathbf{1}_{i<1}\otimes\log(X[i])$$

Now $D=[2]$ and $i=1$ is an actual occurrence, with body
$0\otimes\log(-1)=\bot$. No environment extending the input is admissible,
so there is no model. The machine finds the occurrence $(s,i{=}1)$ ready
(its footprint $\{(X,1)\}$ is an input) and takes UNDEFINED
([Part IV, Section 27.3](../semantics/tensor_logic_semantics_part_iv.md#273-guards-empty-binders-and-failure)).
Categorically, the guard acts *before* the body enters $\mathbf{Pfn}$: it
restricts the domain $D$ along a mono, so the body is never applied
outside $D$. The Iverson factor acts *inside* $\mathbf{Pfn}$, as a total
factor in a strict pairing, and a total factor cannot cancel $\bot$.

**Transformation limits.** A rewrite $L\rightsquigarrow R$ of expressions is
sound when $[\![L]\!]_\rho=[\![R]\!]_\rho$ as partial maps, for every
$\rho$: equal values *and* equal definedness. The recurring failure is
$[\![L]\!]_\rho\preceq[\![R]\!]_\rho$ with strict inequality: the rewrite
makes the program more defined.

- $0\otimes E\rightsquigarrow 0$. We have
  $[\![0\otimes E]\!]_\rho\preceq[\![0]\!]_\rho$, with equality iff
  $[\![E]\!]_\rho$ is total. When $E$ can be undefined the rewrite is
  unsound. It is the same failure as discard (Proposition 3.6) and as
  select-first (Proposition 3.13).
- $f(x)\oplus f(y)\rightsquigarrow f(x\oplus y)$. Primitives are partial set
  maps, not additive homomorphisms. For values: $\mathrm{relu}(1)+\mathrm{relu}(-1)=1$
  but $\mathrm{relu}(0)=0$. For definedness: $\log(2)+\log(-1)=\bot$, but
  $\log(2+(-1))=\log 1=0$. Each needs its own value-and-definedness theorem.
- Pure semiring rewrites from Chapter 2 (Propositions 2.7 and 2.12) are
  safe: their reads and operations are total on complete environments, so
  both sides are total and equality of values is all there is to check.

Why does "more defined" count as wrong? Because definedness is observable.
It decides whether $\mathrm{Models}(P,\eta)$ is empty (Chapter 4) and
whether the machine terminates in success or in $\mathsf{Failed}$
(Chapter 5). A rewrite that turns $\bot$ into a value changes the program's
denotation.

**Example 3.19 (running example, s4).** The body is $\log(Y[1])$, the
composite $\mathrm{apply}_{\log}\circ\mathrm{read}_{(Y,1)}$ of a total read
and a partial primitive. In the environment built from $\eta_1$,
$\rho(Y)[1]=4>0$ and the result is $\downarrow\log 4$; the unique model has
$L=\log 4$. In any environment with $\rho(Y)[1]=0$, as forced by $\eta_0$,
the result is $\bot$, and no sound rewrite of s4 can make it defined.

*Why this matters for an agentic coder.* Before applying an algebraic
simplification, ask which side is more defined. If the rewritten side is
more defined, the rewrite needs a proof that the original was defined on
the inputs that matter. The safe default for partial primitives is: no
rewrite without a value-and-definedness argument.

## 6. Read footprints and stability

The interpretation needs a complete environment. An executor has only a
*partial* store $\sigma:\mathrm{Addr}_\Sigma\rightharpoonup K$ of published
values. Which addresses must be in $\sigma$ before a body can be evaluated?
The read footprint answers this syntactically.

**Definition 3.20 (read footprint).** For a structurally valid expression
$E$ at an admissible valuation $\nu$, the read footprint
$\mathrm{Read}(E,\nu)\subseteq\mathrm{Addr}_\Sigma$ is defined by recursion
([Part IV, Section 23.2](../semantics/tensor_logic_semantics_part_iv.md#232-read-footprints-of-expressions)):

| Expression | $\mathrm{Read}(\,\cdot\,,\nu)$ |
| --- | --- |
| $c_K$, $\mathbf{1}_Q$ | $\varnothing$ |
| $T[e_1,\dots,e_k]$ | $\{(T,([\![e_1]\!]_\nu,\dots,[\![e_k]\!]_\nu))\}$ |
| $E_1\star E_2$ | $\mathrm{Read}(E_1,\nu)\cup\mathrm{Read}(E_2,\nu)$ |
| $\bigoplus_{j\in I_j}E$ | $\bigcup_{k\in I_j}\mathrm{Read}(E,\nu[j\mapsto k])$ |
| $\mathrm{tab}_{j_1\in I_1,\dots,j_m\in I_m}(E)$ | $\bigcup_{p\in I_1\times\cdots\times I_m}\mathrm{Read}(E,\nu_p)$ |
| $\mathrm{at}(E,(e_1,\dots,e_m))$ | $\mathrm{Read}(E,\nu)$ |
| $f(E_1,\dots,E_q)$ | $\bigcup_{r=1}^q\mathrm{Read}(E_r,\nu)$ |

An empty union is empty: empty reductions, empty tabulations and nullary
primitives read nothing, even when the body of an empty reduction mentions an
address. Three choices encode strictness. The footprint of
`at` is the footprint of the *whole* array expression, not of the selected
entry. Both operands of a product stay in the footprint, even when one is
the literal $0$. And a statement guard removes occurrences *before*
footprints are taken, so an excluded valuation contributes no reads at all.
The footprint is a set: reading an address twice is one availability
requirement (it does not erase either read from the expression).

**Example 3.21 (footprints).** For `Scorer` (CONVENTIONS section 3):
$\mathrm{Read}(s1,j)=\{(W,(j,0)),(W,(j,1)),(X,0),(X,1)\}$,
$\mathrm{Read}(s2,j)=\{(B,j)\}$, $\mathrm{Read}(s3,j)=\{(Z,j)\}$,
$\mathrm{Read}(s4,())=\{(Y,1)\}$. The reduction in s1 contributes the union
over $i\in[2]$ of the footprints of $W[j,i]\otimes X[i]$. For the examples of
Section 5: $\mathrm{Read}(\mathrm{at}(\mathrm{tab}_{j\in[2]}(\log X[j]),(0)),\nu)=\{(X,0),(X,1)\}$,
the whole array, matching the fact that $X[1]$ decides definedness;
$\mathrm{Read}(\mathbf{1}_{i<1}\otimes\log X[i],\ i{=}1)=\{(X,1)\}$; and, for the statement $T[]\mathrel{+}=\bigoplus_{j\in[0]}T[]$
(Part IV, Section 27.3), the body reads $(T,())$ but
$\mathrm{Read}(\bigoplus_{j\in[0]}T[],\nu)=\varnothing$, so there is no
self-dependency.

**Proposition 3.22 (read stability; Lemma 23.1 of the specification).** If
complete environments $\rho,\rho'$ agree on $\mathrm{Read}(E,\nu)$, then
$[\![E]\!]_{\rho,\nu}=[\![E]\!]_{\rho',\nu}$, including the case that both
are $\bot$.

*Proof.* Structural induction on $E$, simultaneously for all admissible
$\nu$.

- Literals and Iverson values do not mention $\rho$.
- A read $T[e]$ at $\nu$ returns $\rho(T)[p]$ with
  $p=[\![e]\!]_\nu$, and $(T,p)$ is in the footprint, so
  $\rho(T)[p]=\rho'(T)[p]$.
- For $E_1\star E_2$, the footprint contains both operand footprints, so
  by induction both operand results agree (as elements of
  $\mathrm{Result}(K)$, $\bot$ included), and $\mathrm{lift}_2(\star)$ is a
  function of them.
- For a reduction or tabulation, the footprint contains
  $\mathrm{Read}(E,\nu[j\mapsto k])$ for every actual $k$, so the induction
  hypothesis at each extended valuation makes the two families of body
  results equal; `sequence` and the fold are functions of the family.
- For $\mathrm{at}$, the footprints coincide, so the array results are equal
  and so is the selected entry (or both are $\bot$).
- For a primitive, the argument results are equal by induction, and
  $\mathrm{apply}_f$ is a function with a fixed domain $\mathcal{D}_f$, so
  definedness and value agree. $\square$

The selection case is why the footprint of `at` must include the whole
array: it uses the array result, which may be $\bot$ because of an
unselected coordinate.

**Proposition 3.23 (categorical restatement).** Identify
$\mathrm{Env}_\Sigma=\prod_T K^{\mathrm{Coord}_\Sigma(T)}$ with
$K^{\mathrm{Addr}_\Sigma}$, and let
$\mathrm{inc}:\mathrm{Read}(E,\nu)\hookrightarrow\mathrm{Addr}_\Sigma$ be the
inclusion. For fixed $\nu$, the map
$\rho\mapsto[\![E]\!]_{\rho,\nu}:\mathrm{Env}_\Sigma\to\mathrm{Result}(\tau)$
factors uniquely through the restriction
$\mathrm{inc}^\ast:\mathrm{Env}_\Sigma\to K^{\mathrm{Read}(E,\nu)}$:

$$[\![E]\!]_{-,\nu}=g_{E,\nu}\circ\mathrm{inc}^\ast\quad\text{for a unique } g_{E,\nu}:K^{\mathrm{Read}(E,\nu)}\to\mathrm{Result}(\tau).$$

*Proof.* $K$ is nonempty (it contains $0_K$), so $\mathrm{inc}^\ast$ is
surjective: any partial assignment extends, for instance by $0_K$. A
function factors through a surjection iff it is constant on its fibres,
and the fibres of $\mathrm{inc}^\ast$ are exactly the classes of
environments agreeing on the footprint. Proposition 3.22 gives constancy;
surjectivity gives uniqueness. $\square$

So the footprint is a finite set of addresses through which the whole
environment dependence of one occurrence factors. Note the factorization is
in $\mathbf{Set}$, into $\mathrm{Result}(\tau)$: equal undefinedness is
part of the statement.

**Definition 3.24 (ready evaluation;
[Part IV, Section 23.3](../semantics/tensor_logic_semantics_part_iv.md#233-stable-evaluation-from-a-partial-store)).**
Write $\sigma\sqsubseteq\rho$ when the complete environment $\rho$ extends
the store: $\sigma(a)=\rho(T)[p]$ for every $a=(T,p)\in\mathrm{dom}\,\sigma$.
When $\mathrm{Read}(E,\nu)\subseteq\mathrm{dom}\,\sigma$, define

$$\mathrm{Eval}_\sigma(E,\nu)=[\![E]\!]_{\rho,\nu}\quad\text{for any complete }\rho\text{ with }\sigma\sqsubseteq\rho.$$

This is well defined. An extension exists (fill the unspecified coordinates
with $0_K$; this is a mathematical device for stating the definition, not
permission to read missing values as zero). Any two extensions agree on
$\mathrm{dom}\,\sigma\supseteq\mathrm{Read}(E,\nu)$, so by stability they
give the same result. In the language of Proposition 3.23,
$\mathrm{Eval}_\sigma(E,\nu)=g_{E,\nu}(\sigma|_{\mathrm{Read}(E,\nu)})$.

An occurrence therefore has three possible states relative to a store:

| State | Condition | Machine behaviour (Chapter 5) |
| --- | --- | --- |
| waiting | $\mathrm{Read}(E,\nu)\not\subseteq\mathrm{dom}\,\sigma$ | $\mathrm{Eval}_\sigma$ not invoked |
| ready, defined | footprint available, $\mathrm{Eval}_\sigma(E,\nu)\downarrow v$ | CONTRIBUTE $v$ |
| ready, undefined | footprint available, $\mathrm{Eval}_\sigma(E,\nu)=\bot$ | UNDEFINED, terminal |

Waiting is not a ready $\bot$. This is fact 3 in operational form: a missing
store entry is not undefinedness.

**Example 3.25 (the running example on the machine).** On $\eta_0$, the
occurrence $(s4,())$ waits until $(Y,1)$ is published. The machine
publishes all of $Z$ and $Y$; once $(Y,1)$ is published with value $0$, the
occurrence is ready and $\mathrm{Eval}_\sigma(\log(Y[1]),())=\bot$, so the
machine takes UNDEFINED. On $\eta_1$, $(Y,1)$ is published with value $4$
and the occurrence contributes $\log 4$.

**The Lean development.** In `Interpret.lean`, `footprint` computes the
footprint as a `List (Address σ)`, clause by clause as in Definition 3.20
(the `at` clause is `footprint e γ`, the whole array expression; the binary
clause appends both operands). Duplicates are harmless because the list is
only used through membership. Running `evalWith` on a `PartialStore`
answers a read of a missing address with `none`. So `evalWith` on its own
*conflates* waiting with $\bot$: both come out as `none`. The development
separates them in
[`Readiness.lean`](../../leanncd/LeanNCD/Semantics/Readiness.lean) by
checking the footprint before evaluating:

```lean
inductive ReadyResult (V : Type)
  | notReady
  | evaluated : Option V → ReadyResult V

def evalReady (ops : (s : S) → ScalarOps (K s)) (p : PartialStore K σ)
    (e : Expr K σ r Γ τ) (γ : Γ) : ReadyResult (Value K τ) :=
  if checkReads p (footprint e γ) then .evaluated (evalWith ops p e γ) else .notReady
```

`ReadyResult.notReady` is waiting; `.evaluated none` is a ready $\bot$;
`.evaluated (some v)` is a ready value. The stability theorems, with names
copied from the file, are:

| Lean theorem | Content |
| --- | --- |
| `evalWith_stable` | partial stores agreeing on `footprint e γ` give equal `evalWith` results |
| `interpret_stable` | complete stores agreeing on the footprint give equal `interpret` results (Lemma 23.1) |
| `ready_consistent` | if `p a = some (ρ a)` on the footprint, then `evalReady ops p e γ = .evaluated (interpret ops ρ e γ)` |
| `notReady_iff` | `evalReady ops p e γ = .notReady ↔ ¬ Ready p e γ` |
| `checkReads_iff` | the Boolean check `checkReads` agrees with the predicate "every listed address is present" |

The statement of the first is

```lean
theorem evalWith_stable (ops : (s : S) → ScalarOps (K s))
    (e : Expr K σ r Γ τ) (γ : Γ) (p q : PartialStore K σ)
    (agree : ∀ a ∈ footprint e γ, p a = q a) :
    evalWith ops p e γ = evalWith ops q e γ
```

Its proof is the structural induction of Proposition 3.22, one case per
constructor. It is slightly stronger than the specification's lemma, since
it compares partial stores; `interpret_stable` derives Lemma 23.1 from it,
and the specification's status table cites these two names for Lemma 23.1.
`ready_consistent` is the well-definedness of Definition 3.24: whenever the
footprint is available, the ready result is the interpretation in *any*
complete extension. The existence of an extension is
`ready_complete_extension` in `Completeness.lean`: its witness fills missing
addresses with `ops.zero`, as a mathematical device and not as an evaluator
fallback. This is the precise sense of the remark at the end of Section 4:
`evalWith` over a `PartialStore` is the ready evaluation once `Ready` holds,
and `evalReady` is the function that respects the waiting/undefined
distinction.

*Why this matters for an agentic coder.* The footprint is what a scheduler
needs: an occurrence may run once its footprint is published, and not
before. It is *sufficient*, not minimal. In $X[0]\oplus(0\otimes X[1])$ the
address $(X,1)$ is in the footprint although neither the value nor the
definedness depends on it, because reads and $\otimes$ are total. Pruning it
would be sound, but only by that argument. In $0\otimes\log(X[1])$ the read
of $X[1]$ looks just as "irrelevant" to the value, yet it decides
definedness, and pruning it would require the unsound rewrite to $0$. A
scheduler that trims footprints needs a definedness-preservation argument
for every trim. And the executor must keep "not ready" and "undefined" as
different outcomes: collapsing them, as bare `evalWith` on a partial store
does, turns a wait into a failure.

## 7. What this chapter did not do

- No order on $\bot$ as a semantic value and no domain theory. The order
  $\preceq$ compares two partial maps, such as a program and its rewrite;
  no fixed point is chosen by it, and models remain *all* fixed points
  (Chapter 4).
- No laziness. Tabulation is complete-array and strict; selection does not
  bypass an undefined coordinate; inside an expression, an empty binder is
  the only way a subexpression is not evaluated, and at statement level a
  guard removes the occurrence before evaluation.
- No claim that $\mathrm{Result}(K)$ is a semiring. $\mathrm{lift}_2$ is a
  strict lifting, $0\otimes\bot=\bot$, and collection (Chapter 4) begins only
  after every admitted body has a successful value in $K$.
- No categorical interpreter. Definition 3.15 organizes Section 18 as
  $\mathbf{Pfn}$ combinators; the Lean theorems used are those quoted in
  Sections 4 and 6, from `Readiness.lean` and `Completeness.lean`.
- No general naturality law for array primitives with cross-coordinate
  reads; Proposition 3.13 is about pointwise batching of one partial map.

## Exercises

1. Show that the categorical product of $A$ and $B$ in $\mathbf{Pfn}$ is
   $A\sqcup B\sqcup(A\times B)$, with projections defined on the summands
   that contain the relevant component. Describe the pairing of
   $f:C\rightharpoonup A$ and $g:C\rightharpoonup B$ into it, and compare it
   with strict pairing on Example 3.7.
2. $^\ast$ Using the three laws of Proposition 3.9(2)-(4) (proved in
   Chapter 0, Proposition 0.18), derive from them alone, without unfolding
   the definition of $\mathrm{sequence}_I$, that $\mathrm{batch}_I$ preserves
   composition (Proposition 3.11).
3. $^\ast$ Prove Proposition 3.13 in full, including both equality cases.
   Then show that the condition "$r$ surjective" cannot be weakened to "$r$
   injective" (use Example 3.14), that for $I=\varnothing$ the proposition is
   exactly the failure of natural discard, and that for $r=p:1\to J$ it gives
   $[\![\mathrm{at}(\mathrm{tab}_{j\in J}(E),(p))]\!]_\rho\preceq[\![E[j:=p]]\!]_\rho$.
4. Compute the read footprints of every occurrence of the finite-history
   program of the specification's Sections 11.4 and 27.4 (persistent input
   `H[i,l] = X[i]` for $l\in[N+1]$, base `H[i,0] = Z[i]`, recurrence
   `H[i,l+1] = F(H[:,l])[i]` with core body
   $\mathrm{at}(F(\mathrm{tab}_{j\in[d]}(H[j,l])),(i))$) for $d=1$, $N=2$.
   Check that there are six occurrences. Then explain, for general $d$, why
   the recurrence footprint is the whole slice $\{(H,(j,l))\mid j\in[d]\}$
   and not just $(H,(i,l))$.
5. Let $X=(1,0)$. Compare the two core statements of Example 3.18 (the
   guard $i<1$, and the Iverson factor $\mathbf{1}_{i<1}$) on this input. Give the occurrences, their
   footprints, their body results, the models (if any), and the terminal
   outcome of the machine. Observe that the guarded model is $Y=(0,0)$, the
   very value a "treat $\bot$ as $0$" implementation would report for the
   Iverson program, and explain why that coincidence is a bug, not a
   reassurance.
6. Show that $\varnothing$ is a zero object of $\mathbf{Pfn}$ and that the
   zero morphism $0_{A,B}:A\rightharpoonup B$ is the nowhere-defined map.
   Prove $0\circ f=0$, $g\circ 0=0$ and $f\times 0=0$. Then explain, in
   these terms, why the constant map $\mathrm{const}_{0_K}$ is not a zero
   morphism and why $0_K\otimes\bot=\bot$.
7. Prove by induction on the list that `foldValues ops xs` equals "sequence
   the list, then fold the successful values with `ops.add` and `ops.zero`".
   Which algebraic laws of $(K,\oplus,0_K)$ are needed to identify this right
   fold ending in $0_K$ with the ascending fold
   $v_0\oplus v_1\oplus\cdots\oplus v_{n-1}$ for $n\ge 1$? Is commutativity
   among them?
8. The footprint is sufficient, not minimal. Give an expression $E$ and an
   address $a\in\mathrm{Read}(E,\nu)$ such that removing $a$ from the
   footprint still satisfies the conclusion of Proposition 3.22, and a second
   expression where removing a read that does not affect the *value* breaks
   Proposition 3.22 through *definedness*. State the argument a scheduler
   would need in the first case.
