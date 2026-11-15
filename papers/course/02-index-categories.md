# Chapter 2. Categories of indices and values

**Summary.** Tensor Logic separates *where* a value lives (a finite
coordinate set, an object of $\mathbf{FinSet}$) from *what* it is (a scalar
in $K$), and every tensor program combines three operations on scalar
families: restriction and sum over a fibre, the decategorified shadows of
$f^\ast$ and its left adjoint $\Sigma_f$ in the adjoint triple
$\Sigma_f\dashv f^\ast\dashv\Pi_f$ on set-valued families, and the pointwise
product, the shadow of the product of families over a common domain. The
chapter then shows that contraction patterns are spans whose composition
linearizes to matrix product, and that the occurrences of a program form a
coproduct, so that collection is a pushforward.

**Prerequisites and plan.** We use adjunctions, Kan extensions, spans and
pullbacks as defined in [Chapter 0](00-prerequisites.md), and the program
`Scorer` from [Chapter 1](01-tensor-logic.md). Sections 1 to 5 cover, in
order: coordinate sets and index maps; the adjoint triple on families of
sets; pullback and pushforward of scalars, the transpose identity, and
arrays as functions (the Naperian adjunction); contraction as span
composition; and occurrences as a coproduct. Partiality ($\bot$) is absent
on purpose; it arrives in [Chapter 3](03-partiality.md).

## 1. Shapes are objects of FinSet

Start with the running example. The input $W$ of `Scorer` is a $2\times 2$
table of reals. It has four entries, and each entry has an address: the
pair $(j,i)$ with $j,i\in[2]$. So $W$ is nothing more than a function

$$
W:[2]\times[2]\to\mathbb{R},\qquad W(0,0)=1,\ W(0,1)=1,\ W(1,0)=2,\ W(1,1)=-1.
$$

The same holds for every tensor in the program. $X$ and $B$ are functions
$[2]\to\mathbb{R}$. $Z$ and $Y$ are functions $[2]\to\mathbb{R}$. The scalar
$L$ is a function $1\to\mathbb{R}$ out of the one-point set $1=\{()\}$, which
we identify with its single value $\log 4$ on $\eta_1$.

Writing tensors this way splits a tensor into two pieces of data. The
*domain* (the coordinate set) says where values live; the *codomain* $K$
says what they are. Index manipulation (transposing, taking a diagonal,
broadcasting, scattering) acts only on domains. Arithmetic acts only on
values.

**Definition 2.1 (coordinate sets).** An axis $a$ has an identity and an
extent $n_a\in\mathbb{N}$; its coordinate range is $[n_a]$. A shape is a
finite list of axes; its coordinate set is the product
$[n_{a_1}]\times\cdots\times[n_{a_k}]$. The scalar shape has the empty list
and coordinate set $1=\{()\}$. A zero extent gives the empty coordinate set
$0=\varnothing$.

Two edge cases deserve a sentence each. The empty product is the one-point
set, so a scalar has exactly one coordinate, not zero coordinates. A product
with one zero factor is empty, so a shape such as $(2,0,3)$ has no
coordinates at all; a tensor of that shape is the unique function out of
$\varnothing$. These two conventions are the reason later chapters can treat
scalars and empty tensors without special cases.

Objects of $\mathbf{FinSet}$ are finite sets; morphisms are all functions.
Products exist (cartesian product), the terminal object is $1$, the initial
object is $0$, coproducts are disjoint unions.

Axes with equal extent have the same coordinate set: if $n_a=n_b$ then
$[n_a]$ and $[n_b]$ are one and the same object $[n]$ of $\mathbf{FinSet}$.
So $\mathbf{FinSet}$ does not see axis identity. The specification says the
same thing: coordinate ranges "can nevertheless be equal as sets of
integers. Equality of those ranges does not, by itself, identify the axes"
([Part I, Section 3.1](../semantics/tensor_logic_semantics_part_i.md#31-axes-and-identities)).
Identity lives elsewhere: in the signature $\Sigma$, which gives each tensor
its list of axes, and in the Lean `Shape`, a list of `Axis` records each
carrying a `uid` (below). Separately, the tensor identifier tags each
address, so $(Z,0)$ and $(Y,0)$ are different addresses (Section 5). The
repository's rule "axis identity is by UID, never by name" therefore forbids
inferring a map between two shapes from the coincidence of their extents.
Every map between coordinate sets is supplied explicitly by the program's
index expressions. A purely set-level instance of the same discipline:
$[2]\times[3]$ and $[3]\times[2]$ are isomorphic but different objects, and
a transpose must write down the swap.

The Lean module realizes Definition 2.1 directly.

`leanncd/LeanNCD/Semantics/Types.lean`:

```lean
structure Axis where
  uid : UID
  extent : Nat
  deriving DecidableEq, Repr

abbrev Shape := List Axis

@[reducible] def Coord : Shape → Type
  | [] => Unit
  | a :: sh => Fin a.extent × Coord sh
```

`Coord` builds the right-nested product
$[n_{a_1}]\times([n_{a_2}]\times(\cdots\times 1))$, which is canonically
isomorphic to the flat product of Definition 2.1. The empty shape gives
`Unit`, the set $1$. Notice that `Coord` reads only `a.extent`. The `uid`
lives in the `Shape`, not in the coordinate type. This is the precise sense
in which the coordinate set forgets identity.

**Definition 2.2 (index maps).** Fix an index context
$\Gamma=(i_1:[n_1],\dots,i_k:[n_k])$ with valuation set
$\mathrm{Val}(\Gamma)=\prod_m [n_m]$ and an admissible subset
$D\subseteq\mathrm{Val}(\Gamma)$ (the guard). An in-bounds tuple of affine
index expressions $(e_1,\dots,e_r)$ determines a function
$\phi : D\to [m_1]\times\cdots\times[m_r]$, $\nu\mapsto([\![e_1]\!]_\nu,\dots,[\![e_r]\!]_\nu)$.
A *read map* and a *write map* are index maps in the roles of
Section 6.2 of the specification (Part I).

The word "in-bounds" matters. An affine expression evaluates in
$\mathbb{Z}$, and only when every value lies in range throughout $D$ is the
tuple a function into the coordinate set. Otherwise it is an integer-valued
expression that needs a boundary policy
([Part I, Section 6.1](../semantics/tensor_logic_semantics_part_i.md#61-evaluating-index-expressions)).
In this chapter all index maps are in-bounds.

A *read map* says which source coordinate a contribution reads. A *write
map* says which destination coordinate a contribution addresses
([Part I, Section 6.2](../semantics/tensor_logic_semantics_part_i.md#62-read-maps-and-write-maps)).
Both are morphisms of $\mathbf{FinSet}$, and the two elementary properties of
a function, injectivity and surjectivity, have concrete meanings. In
$\mathbf{FinSet}$ the monomorphisms are exactly the injective functions and
the epimorphisms are exactly the surjective ones. For a *write* map, failure
to be epi means some destination coordinates receive no contribution, and
failure to be mono means several contributions collide at one destination.
For a *read* map, failure to be mono means one source value is reused
(broadcast), and failure to be epi means some source coordinates are never
read.

The following index maps appear in practice. Each is a morphism of
$\mathbf{FinSet}$.

| Source text | Map | Property |
| --- | --- | --- |
| `A[i,i]` read, $i\in[n]$ | diagonal $\Delta:[n]\to[n]\times[n]$ | mono (not epi when $n\ge2$) |
| `X[i]` read at $(i,l)$, $l\in[N]$ | projection $\pi:[n]\times[N]\to[n]$ | epi (broadcast) when $N\ge1$ |
| `Y[2i]` write, $i\in[3]$, $Y$ of extent 6 | $i\mapsto 2i$ | mono, not epi (scatter; unwritten coordinates get $0_K$) |
| `Y[i+j]` write, $i,j\in[2]$, $Y$ of extent 4 | $(i,j)\mapsto i+j$ | neither (collisions, collected additively) |
| guard `i+1<4` on $i\in[4]$ | subobject $D=\{0,1,2\}\hookrightarrow[4]$ | mono (removes occurrences) |
| scalar `T[]` | $1\to 1$ | iso (the identity) |
| `Y[1]` read in s4 | point $1\to[2]$, $()\mapsto 1$ | mono, not epi |

Two remarks on the table. The `Y[i+j]` row depends on the declared extent.
With $Y$ of extent 3, as in the specification's colliding-write example
([Part I, Section 11.2](../semantics/tensor_logic_semantics_part_i.md#112-colliding-affine-writes)),
the map is surjective: epi, but still not mono. With extent 4 the
coordinate $3$ is never written and the map is neither. In such a write,
both $i$ and $j$ parameterize occurrences and no index is contracted: the
sums at colliding coordinates come from collection (pushforward along the
write map, Section 5), whereas a contraction's sum is a reduction inside one
occurrence's body (Proposition 2.13). The values can coincide; the
occurrence counts and machine steps do not. And a guard does not
move coordinates: it is the inclusion of a subobject
$D\hookrightarrow\mathrm{Val}(\Gamma)$, and a guarded write map is a
function with domain $D$.

*Running example.* The statement context of s1 is $\Gamma_{s1}=(j:[2])$,
because $j$ is the only free variable of the core form
$Z[j]\mathrel{+}=\bigoplus_{i\in[2]}W[j,i]\otimes X[i]$. Elaboration binds
$i$ in a reduction, so the body is interpreted over the extended context
$(j:[2],i:[2])$, whose valuation set is $M=[2]\times[2]$. The write map is
$\phi_{s1}:[2]\to[2]$, $j\mapsto j$; the read maps inside the body are
$\pi_W=\mathrm{id}$ and $\pi_X:(j,i)\mapsto i$ on $M=[2]\times[2]$. The map
$\pi_X$ is epi and not mono: each $X[i]$ is read twice, once for each $j$.
The other statements are simpler. For s2 and s3 the write map and the single
read map are $\mathrm{id}_{[2]}$. For s4 the context is empty, so
$D_{s4}=1$, the write map is $1\to1$, and the read map is the point
$()\mapsto1$ of $[2]$ from the last row of the table.

*Why this matters for an agentic coder.* A shape is a type-level object,
not a list of integers. Two shapes with extents $(2,2)$ and different axis
identities are different shapes with the same coordinate set; a map between
their coordinates must be written, not assumed. The Lean type `Coord sh` is the coordinate set of
this object; the identities live in the list `sh` of `Axis` records, and
`Coord` is computed from the extents alone. For two concrete shapes with the
same extents, `Coord` reduces to the same type, so the type checker will not
catch a coordinate passed to the wrong shape. That discipline is yours:
every index map in generated code should come from an explicit index
expression that a reviewer can point to.

## 2. Set-valued families and the adjoint triple

This is the one place in the course where we meet Kan extensions in their
simplest nontrivial form. The plan is to do the categorical work with
families of *sets*, where every operation is forced by a universal property,
and then in Section 3 to count. Counting turns disjoint union into $+$ and
cartesian product into $\cdot$, and the einsum operations fall out.

Treat a finite set $I$ as a *discrete category*: its objects are the
elements of $I$ and its only morphisms are identities. A family of sets
over $I$ is a functor $A:I\to\mathbf{Set}$. Because $I$ has no
non-identity morphisms, such a functor is just an assignment of a set
$A(i)$ to each $i\in I$, and a natural transformation $\alpha:A\Rightarrow B$
is just a family of functions $\alpha_i:A(i)\to B(i)$ with no naturality
condition to check. Write $\mathbf{Set}^I$ for the category of such
families.

The same data can be packaged as one map: by Proposition 0.2 of
[Chapter 0](00-prerequisites.md), a family $A$ corresponds to its total set
$\coprod_{i\in I}A(i)\to I$, and $\mathbf{Set}^I$ is equivalent to the
slice $\mathbf{Set}/I$. The running example lives here: the destination map
$\mathrm{dst}:\mathcal{O}_P\to\mathrm{Addr}_{\mathrm{Def}}$ of
[Chapter 1](01-tensor-logic.md) is an object of the slice, and its family
sends each address $a$ to its writer family $\mathcal{C}_P(a)$, for example
$(Z,0)\mapsto\{(s1,j{=}0),(s2,j{=}0)\}$.

**Definition 2.3 (restriction).** For $f:I\to J$ in $\mathbf{FinSet}$,
restriction $f^\ast:\mathbf{Set}^J\to\mathbf{Set}^I$ is precomposition:
$(f^\ast B)(i)=B(f(i))$.

On morphisms, $(f^\ast\beta)_i=\beta_{f(i)}$. Restriction is strictly
functorial in $f$: $(\mathrm{id}_I)^\ast=\mathrm{id}$ and
$(g\circ f)^\ast=f^\ast\circ g^\ast$, because both sides are precomposition.
In the slice picture, $f^\ast$ sends $p:E\to J$ to the pullback
$I\times_J E=\{(i,e)\mid f(i)=p(e)\}\to I$. The fibre over $i$ is
$p^{-1}(f(i))$, which is $B(f(i))$. This is why restriction is also called
pullback.

**Theorem 2.4 (the adjoint triple).** Restriction has a left adjoint
$\Sigma_f$ and a right adjoint $\Pi_f$:

$$
\Sigma_f\dashv f^\ast\dashv \Pi_f,\qquad
(\Sigma_f A)(j)=\coprod_{i\in f^{-1}(j)}A(i),\qquad
(\Pi_f A)(j)=\prod_{i\in f^{-1}(j)}A(i).
$$

Moreover $\Sigma_f=\mathrm{Lan}_f$ and $\Pi_f=\mathrm{Ran}_f$, the left and
right Kan extensions along $f$ regarded as a functor between discrete
categories.

The equalities in the last sentence are, as always for universal
constructions, canonical isomorphisms. In the slice picture $\Sigma_f$ is
simply "compose with $f$": it sends $p:E\to I$ to $f\circ p:E\to J$, whose
fibre over $j$ is the disjoint union of the fibres of $p$ over $f^{-1}(j)$.

*Proof.* (i) *Kan extensions.* This is Proposition 0.11 of
[Chapter 0](00-prerequisites.md): the comma categories $f\downarrow j$ and
$j\downarrow f$ are the discrete category on the fibre $f^{-1}(j)$, so the
pointwise formula (Proposition 0.10) computes $\mathrm{Lan}_fA$ as the
coproduct over the fibre and $\mathrm{Ran}_fA$ as the product. Part (ii)
verifies the adjunctions by hand, so the proof does not depend on the
general theory.

(ii) *Hom-set bijection.* A morphism $\alpha:\Sigma_fA\to B$ in
$\mathbf{Set}^J$ is a family of functions

$$
\alpha_j:\coprod_{i\in f^{-1}(j)}A(i)\to B(j),\qquad j\in J.
$$

By the universal property of the coproduct, each $\alpha_j$ is the same as
a family of functions $\alpha_{j,i}:A(i)\to B(j)$, one for each $i$ with
$f(i)=j$. Every $i\in I$ lies in exactly one fibre, namely the fibre over
$f(i)$. So the whole collection is a family

$$
\beta_i:A(i)\to B(f(i))=(f^\ast B)(i),\qquad i\in I,
$$

which is precisely a morphism $\beta:A\to f^\ast B$ in $\mathbf{Set}^I$.
This gives the bijection

$$
\mathbf{Set}^J(\Sigma_f A,B)\cong\mathbf{Set}^I(A,f^\ast B),\qquad
\beta_i(a)=\alpha_{f(i)}(i,a).
$$

Naturality in $B$: postcomposing $\alpha$ with $\gamma:B\to B'$ postcomposes
each $\beta_i$ with $\gamma_{f(i)}=(f^\ast\gamma)_i$. Naturality in $A$:
precomposing $\alpha$ with $\Sigma_f\delta$ for $\delta:A'\to A$
precomposes each $\beta_i$ with $\delta_i$. Both are immediate from the
formula $\beta_i(a)=\alpha_{f(i)}(i,a)$.

For the right adjoint, a morphism $\beta:f^\ast B\to A$ is a family
$\beta_i:B(f(i))\to A(i)$. Group the $i$ by their image $j=f(i)$. For fixed
$j$ the functions $B(j)\to A(i)$, $i\in f^{-1}(j)$, are by the universal
property of the product the same as one function
$B(j)\to\prod_{i\in f^{-1}(j)}A(i)$. So

$$
\mathbf{Set}^I(f^\ast B,A)\cong\mathbf{Set}^J(B,\Pi_f A),
$$

naturally in $A$ and $B$ by the same bookkeeping.

(iii) *Units and counits.* By Proposition 0.4 the bijections determine the
units and counits; we record the formulas. For $\Sigma_f\dashv f^\ast$ the
unit is the coproduct injection and the counit is the fold map that forgets
which copy $b$ came from:

$$
\eta_i:A(i)\to(f^\ast\Sigma_f A)(i),\ a\mapsto(i,a);\qquad
\varepsilon_j:\coprod_{i\in f^{-1}(j)}B(j)\to B(j),\ (i,b)\mapsto b.
$$

For $f^\ast\dashv\Pi_f$ the unit is the diagonal
$B(j)\to\prod_{i\in f^{-1}(j)}B(j)$, $b\mapsto(b)_{i}$, and the counit is the
projection $\prod_{i'\in f^{-1}(f(i))}A(i')\to A(i)$ onto the factor $i$.
$\square$

Two consequences are used later.

*Functoriality.* $\Sigma_{\mathrm{id}}\cong\mathrm{id}$, since every fibre
of the identity is a singleton and a one-term coproduct is canonically its
term. And $\Sigma_{g\circ f}\cong\Sigma_g\circ\Sigma_f$: the fibre of
$g\circ f$ over $k$ is the disjoint union of the fibres $f^{-1}(j)$ over
$j\in g^{-1}(k)$, so

$$
\coprod_{i\in(g f)^{-1}(k)}A(i)\cong\coprod_{j\in g^{-1}(k)}\ \coprod_{i\in f^{-1}(j)}A(i).
$$

A second proof: $(g\circ f)^\ast=f^\ast g^\ast$, and left adjoints of
naturally isomorphic functors are naturally isomorphic, so
$\Sigma_{gf}\cong\Sigma_g\Sigma_f$. The same holds for $\Pi$.

*Beck–Chevalley.* Consider a pullback square of finite sets

$$
\begin{array}{ccc}
P & \xrightarrow{\;q\;} & J' \\
{\scriptstyle p}\downarrow & & \downarrow{\scriptstyle g} \\
I & \xrightarrow{\;f\;} & J
\end{array}
\qquad P=I\times_J J'=\{(i,j')\mid f(i)=g(j')\}.
$$

Because $f\circ p=g\circ q$, there is a canonical *comparison map*
$\Sigma_q\,p^\ast\Rightarrow g^\ast\,\Sigma_f$ of functors
$\mathbf{Set}^I\to\mathbf{Set}^{J'}$ (the *mate* of the square): apply the
unit of $\Sigma_f\dashv f^\ast$, rewrite $p^\ast f^\ast=q^\ast g^\ast$, then
apply the counit of $\Sigma_q\dashv q^\ast$,

$$
\Sigma_q\,p^\ast\xrightarrow{\ \Sigma_qp^\ast\eta\ }\Sigma_q\,p^\ast f^\ast\Sigma_f
\;=\;\Sigma_q\,q^\ast g^\ast\Sigma_f\xrightarrow{\ \varepsilon\,g^\ast\Sigma_f\ }g^\ast\,\Sigma_f.
$$

With the formulas of part (iii), it sends an element $((i,j'),a)$ of
$(\Sigma_qp^\ast A)(j')$, where $a\in A(i)$, to $(i,a)$. The
*Beck–Chevalley condition* says that this comparison map is an isomorphism,
$\Sigma_q\,p^\ast\cong g^\ast\,\Sigma_f$; dually one asks
$g^\ast\Pi_f\cong\Pi_q\,p^\ast$. In words: summing over fibres and then
restricting is the same as restricting to the pullback and then summing
over the fibres there.

It holds for every pullback square of finite sets. At $j'\in J'$,

$$
(g^\ast\Sigma_fA)(j')=\coprod_{i:\ f(i)=g(j')}A(i),\qquad
(\Sigma_qp^\ast A)(j')=\coprod_{(i,j'')\in P,\ j''=j'}A(i).
$$

The fibre $q^{-1}(j')=\{(i,j')\mid f(i)=g(j')\}$ is in bijection with
$f^{-1}(g(j'))$ by $(i,j')\mapsto i$, so the comparison map
$((i,j'),a)\mapsto(i,a)$ is a bijection at each $j'$. It commutes with any
morphism $A\to A'$, so it is a natural isomorphism.

The square that appears in s1 is the case $I=J'=[2]$, $J=1$, $f=g=\,!$ the
unique maps to the point. The pullback is $P=[2]\times_1[2]=[2]\times[2]$.
Identify $P$ with $M$ by $(i,j)\mapsto(j,i)$; then
$q=\pi_{\mathrm{out}}:(j,i)\mapsto j$ and $p=\pi_X:(j,i)\mapsto i$, and the
isomorphism reads $\coprod_{i\in[2]}A(i)\cong\coprod_{(j',i)\in M,\ j'=j}A(i)$
at each $j$. In tensor language: "sum $X$ over $i$, then broadcast the
result to every $j$" equals "broadcast $X$ to every $(j,i)$, then sum out
$i$ for each $j$".

**Example 2.5.** Take $f:[2]\times[2]\to[2]$, $(j,i)\mapsto j$, and the
one-point family $A(j,i)=\{\ast\}$, as in Example 0.12 of
[Chapter 0](00-prerequisites.md). Concretely,
$\Sigma_fA(0)=\{((0,0),\ast),((0,1),\ast)\}$: one element for each $i$ in
the fibre, tagged by where it came from. And
$\Pi_fA(0)=\{\ast\}\times\{\ast\}$ has the single element $(\ast,\ast)$. The
tags are the important part. Two elements that look the same ($\ast$ and
$\ast$) are kept apart in the coproduct because they sit over different
indices. That is the set-level version of the rule that equal-valued
contributions are not deduplicated.

Now vary the family to see the counting. Let
$A(j,i)=[n_{j,i}]$ with $n_{0,0}=1$, $n_{0,1}=1$, $n_{1,0}=2$, $n_{1,1}=0$.
Then

$$
|\Sigma_fA(0)|=1+1=2,\quad |\Sigma_fA(1)|=2+0=2,\quad
|\Pi_fA(0)|=1\cdot1=1,\quad |\Pi_fA(1)|=2\cdot0=0.
$$

An empty set in a fibre contributes nothing to the coproduct and kills the
product. These are the set-level origins of "$0_K$ is the identity of
$\oplus$" and "$0_K$ is absorbing for $\otimes$".

*Why this matters for an agentic coder.* The three operations in every
tensor program are restriction, sum over a fibre, and the pointwise product
of families on one index set. The first two are the shadows of $f^\ast$ and
$\Sigma_f$. The third is the shadow of the product of two families over a
common domain $M$, the fibre product in $\mathbf{Set}/M$ whose fibre over
$m$ is $A(m)\times B(m)$; it is not a member of the triple. The third member
of the triple, $\Pi_f$, has as shadow the product over a fibre, which has no
core constructor; its familiar instances occur only in other sorts
(Section 3). A coder who implements "sum over the contracted index" is
implementing $f_!$, the decategorified shadow of $\Sigma_f$. The $K$-valued
laws it obeys (functoriality, invariance under relabeling, grouping over
coproducts) have the same shape as the $\mathbf{Set}$-valued isomorphisms
and are proved directly (Proposition 2.7); nothing is inherited from
Theorem 2.4 as a theorem. For a loop that accumulates into `out[f(i)]`,
these laws license changing the loop order, chunking the source, and
renaming source indices. They do not license dropping tags: a loop that
skips "duplicate" sources has replaced a coproduct by a union.

## 3. Decategorification: K-valued families

Section 2 worked with sets. Tensors hold scalars. The bridge is counting.

Cardinality $|\cdot|:\mathbf{FinSet}\to\mathbb{N}$ (on objects) sends
disjoint union to $+$ and cartesian product to $\cdot$:
$|A\sqcup B|=|A|+|B|$, $|A\times B|=|A|\cdot|B|$, $|0|=0$, $|1|=1$, and
isomorphic sets have equal cardinality. For any commutative semiring $K$
there is a unique semiring homomorphism $\kappa:\mathbb{N}\to K$, namely
$\kappa(n)=1_K\oplus\cdots\oplus1_K$ ($n$ terms). Composing cardinality with
this semiring homomorphism sends finite sets to scalars, $\sqcup$ to
$\oplus$, and $\times$ to $\otimes$.

A *sort* is a scalar carrier with its own operations $(\oplus,\otimes,0,1)$
([Part I, Section 2.4](../semantics/tensor_logic_semantics_part_i.md#24-scalar-sorts)).
The specification uses four: the real sort $(\mathbb{R},+,\cdot,0,1)$, the
Boolean sort $(\vee,\wedge,\text{false},\text{true})$, the max-plus sort
$(\max,+,-\infty,0)$ and the min-plus sort $(\min,+,+\infty,0)$
([Part I, Section 2.1](../semantics/tensor_logic_semantics_part_i.md#21-the-scalar-carrier)).
In the real sort $\kappa$ is the inclusion $\mathbb{N}\subseteq\mathbb{R}$.
In the Boolean sort $\kappa(n)$ is "$n>0$", so a set is sent to the truth
value "it is inhabited".

A $K$-valued family is $v:I\to K$; the set of these is $K^I$. A family of
finite sets $A$ over $I$ gives the $\mathbb{N}$-valued family
$|A|:i\mapsto|A(i)|$, and then the $K$-valued family $\kappa\circ|A|$.

Apply this to the adjoint triple. For $f:I\to J$ and families $A$ over $I$,
$B$ over $J$:

$$
|\Sigma_fA|(j)=\sum_{i\in f^{-1}(j)}|A(i)|,\qquad
|f^\ast B|(i)=|B(f(i))|,\qquad
|\Pi_fA|(j)=\prod_{i\in f^{-1}(j)}|A(i)|.
$$

Each formula is the cardinality of the corresponding definition in
Theorem 2.4, using $|\coprod|=\sum$ and $|\prod|=\prod$. Read from right to
left, they *define* three operations on scalar families: sum over the fibre,
precomposition, and product over the fibre. The first two get names.

**Definition 2.6 (pullback and pushforward).** For $f:I\to J$:

$$
f^\ast:K^J\to K^I,\quad f^\ast v=v\circ f;\qquad
f_!:K^I\to K^J,\quad (f_!v)(j)=\bigoplus_{i\in f^{-1}(j)}v(i).
$$

$f^\ast$ needs no structure on $K$. $f_!$ needs the commutative monoid
$(K,\oplus,0_K)$; the empty fibre gives $0_K$.
Which structure is needed for which operation: the commutative monoid
$(K,\oplus,0_K)$ for $f_!$ (contraction as a sum); the commutative semiring
$(K,\oplus,\otimes,0_K,1_K)$ for the pointwise product, for the einsum formula
of Proposition 2.13 and for the transpose identity (Proposition 2.8).

The third operation of a tensor program, the pointwise product
$(u\otimes v)(m)=u(m)\otimes v(m)$ of two families on one index set $M$, does
not come from the triple. Its set-level origin is the product of two
families over $M$, $(A\times B)(m)=A(m)\times B(m)$, which is the product in
$\mathbf{Set}^M$ and, under $\mathbf{Set}^M\simeq\mathbf{Set}/M$, the fibre
product over the common domain $M$. Counting gives
$|A\times B|(m)=|A(m)|\cdot|B(m)|$.

The computation above is a small theorem: for families of finite sets,
$|\Sigma_fA|=f_!|A|$ and $|f^\ast B|=f^\ast|B|$ in $\mathbb{N}$-valued
families, and applying the homomorphism $\kappa$ transports both to $K$. That is
the precise content of "pushforward is the decategorification of
$\Sigma_f$". It is a statement about families that *are* cardinalities. A
general real family such as $X=(1,-2)$ is not the cardinality of anything,
so for general $K$ we do not derive the laws of $f_!$ from Theorem 2.4. We
prove them directly from the commutative monoid laws, and we use the set
level only as a guide to which laws to expect. This is the honest version of
the slogan, and it is the stance of CONVENTIONS fact 12.

*Running example.* The read and write maps of s1 act on the values of
$\eta_1$. Pull $X=(1,-2)$ back along $\pi_X:(j,i)\mapsto i$:

$$
\pi_X^\ast X:\ (0,0)\mapsto1,\ (0,1)\mapsto-2,\ (1,0)\mapsto1,\ (1,1)\mapsto-2.
$$

Each $X[i]$ appears twice, once for each $j$: this is broadcasting. Multiply
pointwise by $\pi_W^\ast W=W$ to get the summand family on $M$:

$$
\theta=\pi_W^\ast W\otimes\pi_X^\ast X:\ (0,0)\mapsto1,\ (0,1)\mapsto-2,\ (1,0)\mapsto2,\ (1,1)\mapsto2.
$$

Push forward along $\pi_{\mathrm{out}}:(j,i)\mapsto j$. The fibre over $0$ is
$\{(0,0),(0,1)\}$ and the fibre over $1$ is $\{(1,0),(1,1)\}$, so

$$
(\pi_{\mathrm{out}})_!\,\theta=(1+(-2),\ 2+2)=(-1,4).
$$

This is the contribution tensor $V_{s1}$, computed with one pullback, one
pointwise product and one pushforward.

In the next statement $K^I$ carries the pointwise monoid structure,
$(v\oplus w)(i)=v(i)\oplus w(i)$ and $0(i)=0_K$, and $\mathbf{CMon}$ is the
category of commutative monoids and monoid homomorphisms.

**Proposition 2.7 (laws of pushforward).** For a commutative monoid $K$:

1. $f_!$ is a monoid homomorphism: $f_!(0)=0$, $f_!(v\oplus w)=f_!v\oplus f_!w$.
2. $(\mathrm{id}_I)_!=\mathrm{id}_{K^I}$ and $(g\circ f)_!=g_!\circ f_!$.
3. (relabeling) For a bijection $e:I'\cong I$, $(f\circ e)_!(v\circ e)=f_!v$.
4. (grouping) For $I=\coprod_{s\in S}I_s$ with $f_s=f|_{I_s}$,
   $f_!v=\bigoplus_{s}(f_s)_!(v|_{I_s})$.

Dually $(\mathrm{id})^\ast=\mathrm{id}$, $(g\circ f)^\ast=f^\ast\circ g^\ast$.
So $I\mapsto K^I$ is a covariant functor $\mathbf{FinSet}\to\mathbf{CMon}$
via $f_!$ and a contravariant one via $f^\ast$.

In (4) the index set $S$ is finite, as in Lean's `pushforward_grouped`
(which assumes `Fintype A`), so $\bigoplus_s$ is a finite sum.

*Proof.* Everything rests on one fact: a finite sum in a commutative monoid
does not depend on how its terms are enumerated or bracketed, so it may be
reindexed along any bijection and split along any partition of its index
set.

(1) $(f_!0)(j)=\bigoplus_{i\in f^{-1}(j)}0_K=0_K$. And
$(f_!(v\oplus w))(j)=\bigoplus_{i\in f^{-1}(j)}\big(v(i)\oplus w(i)\big)$,
which by commutativity and associativity equals
$\bigoplus_{f(i)=j}v(i)\oplus\bigoplus_{f(i)=j}w(i)$.

(2) The fibre of $\mathrm{id}_I$ over $i$ is $\{i\}$, so
$((\mathrm{id}_I)_!v)(i)=v(i)$. For $f:I\to J$ and $g:J\to L$, the fibre of
$g\circ f$ over $k$ is partitioned by the value of $f$:
$(gf)^{-1}(k)=\coprod_{j\in g^{-1}(k)}f^{-1}(j)$. Splitting the sum along
this partition gives

$$
((g f)_!v)(k)=\bigoplus_{j\in g^{-1}(k)}\ \bigoplus_{i\in f^{-1}(j)}v(i)=(g_!(f_!v))(k).
$$

(3) The bijection $e$ restricts, for each $j$, to a bijection
$(f e)^{-1}(j)\to f^{-1}(j)$, $i'\mapsto e(i')$. Reindexing the sum along it
gives $\bigoplus_{f(e(i'))=j}v(e(i'))=\bigoplus_{f(i)=j}v(i)$.

(4) The fibre $f^{-1}(j)$ is partitioned as $\coprod_s f_s^{-1}(j)$.
Splitting the sum gives
$(f_!v)(j)=\bigoplus_s\bigoplus_{i\in f_s^{-1}(j)}v(i)=\bigoplus_s((f_s)_!(v|_{I_s}))(j)$.

The pullback laws are associativity of function composition:
$(\mathrm{id})^\ast v=v\circ\mathrm{id}=v$ and
$(gf)^\ast v=v\circ g\circ f=f^\ast(g^\ast v)$. Pullback is a monoid
homomorphism because the operations are pointwise. Together, (1) and (2)
say that $I\mapsto K^I$, $f\mapsto f_!$ is a functor into $\mathbf{CMon}$,
and the pullback laws say $I\mapsto K^I$, $f\mapsto f^\ast$ is a functor
$\mathbf{FinSet}^{\mathrm{op}}\to\mathbf{CMon}$. $\square$

Each law is the shadow of a set-level isomorphism. (2) is the shadow of
$\Sigma_{gf}\cong\Sigma_g\Sigma_f$. (4) is the decategorified statement that
$\mathrm{Lan}$ out of a coproduct is a coproduct of $\mathrm{Lan}$s: writing
$\iota_s:I_s\to I$ for the inclusions,
$\Sigma_fA\cong\coprod_s\Sigma_{f_s}\iota_s^\ast A$, because a fibre of $f$ is
the disjoint union of the fibres of the $f_s$. (3) is invariance of
$\mathrm{Lan}$ under an equivalence of the source: for a bijection $e$ the
counit $\Sigma_ee^\ast A\to A$ is an isomorphism (every fibre of $e$ is a
singleton; compare Exercise 1), so
$\Sigma_{fe}\,e^\ast A\cong\Sigma_f\Sigma_e e^\ast A\cong\Sigma_fA$. Taking
cardinalities of these isomorphisms gives (2), (3) and (4) for
$\mathbb{N}$-valued families. The direct proof above gives them for every
commutative monoid.

*Running example.* Law (2) is visible in s1. The output projection factors
as $\pi_{\mathrm{out}}=\phi_{s1}\circ\mathrm{pr}_j$, where
$\mathrm{pr}_j:M\to[2]$ forgets $i$ and $\phi_{s1}=\mathrm{id}$ is the write
map. So $(\pi_{\mathrm{out}})_!=(\phi_{s1})_!\circ(\mathrm{pr}_j)_!$: the
inner pushforward is the body's reduction $\bigoplus_i$, and the outer one
is collection along the write map. Law (4) is visible in collection: the
fibre of $(Z,0)$ splits by statement into one occurrence of s1 and one of
s2, and $Z[0]=V_{s1}[0]\oplus V_{s2}[0]=-1+1=0$.

**The Lean module.** The file
[`Collection.lean`](../../leanncd/LeanNCD/Semantics/Collection.lean) is a
line-by-line transcription of Definition 2.6 and Proposition 2.7.

`leanncd/LeanNCD/Semantics/Collection.lean`:

```lean
abbrev Family (I K : Type) := I → K

def pullback {I J K : Type} (f : I → J) (v : Family J K) : Family I K := v ∘ f

variable {O I J K : Type} [Fintype O] [AddCommMonoid K]

def pushforward [DecidableEq I] (d : O → I) (v : Family O K) : Family I K :=
  fun i => ∑ o, if d o = i then v o else 0
```

The definition sums over *all* of the finite source `O`, and the `if` is
the fibre: it keeps exactly the terms with $d(o)=i$ and replaces every
other term by `0`, the identity of the monoid, which changes nothing. So the
sum equals $\bigoplus_{o\in d^{-1}(i)}v(o)$, and an empty fibre gives `0`.
The hypotheses are what the mathematics needs: `Fintype O` makes the sum
finite, `AddCommMonoid K` is $(K,\oplus,0_K)$, and `DecidableEq I` lets the
`if` decide $d(o)=i$. Pullback needs no hypotheses.

| Statement | Lean name in `Collection.lean` |
| --- | --- |
| Definition 2.6, $f^\ast$ | `pullback` |
| Definition 2.6, $f_!$ | `pushforward` |
| 2.7(1), $f_!(0)=0$ | `pushforward_zero` |
| 2.7(1), $f_!(v\oplus w)=f_!v\oplus f_!w$ | `pushforward_add` |
| 2.7(1), packaged as a homomorphism `Family O K →+ Family I K` | `pushforwardHom` |
| 2.7(2), $(\mathrm{id})_!=\mathrm{id}$ | `pushforward_id` |
| 2.7(2), $e_!\circ d_!=(e\circ d)_!$ | `pushforward_comp` |
| 2.7(3), relabeling along `e : O' ≃ O` | `pushforward_relabel` |
| 2.7(4), grouping over a sigma type `(a : A) × B a` | `pushforward_grouped` |

`pushforward_comp` also asks for `Fintype I`, because the intermediate set
is summed over. `pushforward_grouped` states (4) pointwise, for a source
that is a sigma type, Lean's coproduct $\coprod_{a\in A}B(a)$. The pullback
laws have no named theorems; they hold by unfolding `v ∘ f`. The module
proves no adjunction between pullback and pushforward.

**Proposition 2.8 (transpose identity).** For a commutative semiring $K$,
$u\in K^I$, $w\in K^J$, and the pairing $\langle u,v\rangle_I=\bigoplus_i u(i)\otimes v(i)$:

$$
\langle f_!u,\,w\rangle_J=\langle u,\,f^\ast w\rangle_I.
$$

*Proof.* Expand the left side, distribute, and regroup:

$$
\begin{aligned}
\langle f_!u,w\rangle_J
&=\bigoplus_{j\in J}\Big(\bigoplus_{i\in f^{-1}(j)}u(i)\Big)\otimes w(j)\\
&=\bigoplus_{j\in J}\ \bigoplus_{i\in f^{-1}(j)}u(i)\otimes w(f(i))\\
&=\bigoplus_{i\in I}u(i)\otimes w(f(i)).
\end{aligned}
$$

The second step is right distributivity of $\otimes$ over $\oplus$, applied
to each fibre; for an empty fibre it is $0_K\otimes w(j)=0_K$, absorption.
In that step $w(j)$ was rewritten as $w(f(i))$, which is legitimate because
$f(i)=j$ inside the fibre. The third step merges the sums over the
partition $I=\coprod_jf^{-1}(j)$, which is Proposition 2.7(2) for the
composite $I\xrightarrow{f}J\to1$. The last expression is
$\langle u,f^\ast w\rangle_I$. $\square$

*Running example.* Take $f=\pi_{\mathrm{out}}$, $u=\theta$ the summand family
of s1, and test against $w=B=(1,0)\in K^{[2]}$. The left side is
$\langle(-1,4),(1,0)\rangle=-1$. On the right,
$\pi_{\mathrm{out}}^\ast B$ sends $(j,i)\mapsto B[j]$, so it is $1$ on
$(0,0),(0,1)$ and $0$ on $(1,0),(1,1)$, and
$\langle\theta,\pi_{\mathrm{out}}^\ast B\rangle=1\cdot1+(-2)\cdot1+2\cdot0+2\cdot0=-1$.

*What the identity means.* For vector spaces with a chosen basis, the
adjoint (transpose) of a linear map $T$ is the map $T^\top$ with
$\langle Tu,w\rangle=\langle u,T^\top w\rangle$. Proposition 2.8 says that
$f^\ast$ is the transpose of $f_!$. In matrix terms (Exercise 3), the matrix
of $f_!$ has a $1_K$ in position $(j,i)$ exactly when $f(i)=j$, and the
matrix of $f^\ast$ is its transpose. This is what "adjoint" means for linear
maps.

*Where the identity comes from.* Proposition 2.8, with the direct proof
above, is the theorem. The set level explains it: the transpose identity is
the decategorified shadow of the *projection formula* for $\Sigma_f$, also
called *Frobenius reciprocity*, together with functoriality of $\Sigma$
along $J\to1$. Write $A\times B$ for the pointwise product of two families
over one index set, $(A\times B)(x)=A(x)\times B(x)$, the set-level origin
of the pointwise product $u\otimes v$.

*Projection formula.* For $f:I\to J$, $A\in\mathbf{Set}^I$ and
$B\in\mathbf{Set}^J$ there is an isomorphism in $\mathbf{Set}^J$, natural in
$A$ and $B$,

$$
\Sigma_f\big(A\times f^\ast B\big)\;\cong\;\Sigma_fA\times B.
$$

Proof, fibre by fibre. Over $j$, the left side is
$\coprod_{i\in f^{-1}(j)}A(i)\times B(f(i))=\coprod_{i\in f^{-1}(j)}A(i)\times B(j)$,
because $f(i)=j$ in the fibre. The right side is
$\big(\coprod_{i\in f^{-1}(j)}A(i)\big)\times B(j)$, and distributivity of
$\times$ over $\sqcup$ in $\mathbf{Set}$ identifies it with the same set by
$((i,a),b)\mapsto(i,(a,b))$. Both sides over $j$ are therefore
$\coprod_{i\in f^{-1}(j)}A(i)\times B(j)$. The bijection commutes with
morphisms of $A$ and $B$, so it is natural. The projection formula is an
extra property of $\Sigma_f\dashv f^\ast$ that holds in $\mathbf{Set}$; it
does not follow from the adjunction alone.

*From the projection formula to the pairing.* Let $u=|A|$ and $w=|B|$. The
pairing $\langle f_!u,w\rangle_J=\sum_j|\Sigma_fA(j)|\cdot|B(j)|$ is the
cardinality of $\Sigma_{J\to1}(\Sigma_fA\times B)$, the disjoint union of
all fibres. By the projection formula this set is isomorphic to
$\Sigma_{J\to1}\Sigma_f(A\times f^\ast B)$, and by functoriality
($(J\to1)\circ f=(I\to1)$) to $\Sigma_{I\to1}(A\times f^\ast B)$. Its
cardinality is $\sum_i|A(i)|\cdot|B(f(i))|=\langle u,f^\ast w\rangle_I$. So
for families that are cardinalities, the transpose identity is the count of
a chain of set-level isomorphisms. For general $K$ the identity is proved
directly, as above. (The hom-set bijection of Theorem 2.4 counts to a
different, multiplicative identity,
$\prod_j|B(j)|^{|\Sigma_fA(j)|}=\prod_i|B(f(i))|^{|A(i)|}$.)

The transpose identity is *not* an adjunction of functors between $K^I$ and
$K^J$. For $K=\mathbb{R}$, $K^I$ carries no order or category structure in
which $f_!$ is adjoint to $f^\ast$, and the course claims no such
adjunction (CONVENTIONS fact 12). For the idempotent sorts (Boolean,
max-plus, min-plus, where $a\oplus a=a$) the families form posets and the
situation is different; the course does not treat it. The adjunction lives
one level up, on $\mathbf{Set}^I$ and $\mathbf{Set}^J$, and the transpose
identity is what survives when sets are replaced by numbers.

*What does not decategorify well.* The right adjoint $\Pi_f$ becomes the
fibrewise product

$$
(f_\otimes v)(j)=\bigotimes_{i\in f^{-1}(j)}v(i),\qquad\text{empty fibre}\mapsto1_K,
$$

which needs $\otimes$ and has no counterpart among the core constructors:
the Tensor Logic core reduces only with $\oplus$. The operation is
nevertheless familiar in particular sorts. In the Boolean sort $\otimes$ is
$\wedge$, so $f_\otimes$ is "for all $i$ in the fibre", while $f_!$ is "there
exists". In the max-plus sort $\otimes$ is ordinary $+$, so $f_\otimes$ is the
ordinary sum over the fibre; this is how a product of probabilities is
computed in log space. And $f_\otimes$ has no transpose identity of its own,
because the pairing is built from $\oplus$, which matches $\Sigma$, not $\Pi$.

### Arrays are functions: the Naperian adjunction

So far a family $v\in K^I$ has been a value. Tensor Logic also builds such
families inside expressions, by tabulating a scalar body over an index, and
takes them apart by selecting an entry. Both constructors come from one
adjunction.

**Proposition 2.9 (the Naperian adjunction).** For a finite set $I$,
$(-)\times I\dashv(-)^I$ on $\mathbf{Set}$, with unit tabulation
$\eta_A:A\to(A\times I)^I$ and counit lookup $\mathrm{ev}:A^I\times I\to A$.
Consequently $K^{I\times J}\cong(K^J)^I$ (currying). The core constructor
`tab` is the transpose of the body across this adjunction (currying, built
from the unit), and `at` is the counit applied to the pair (array, index).
The equation $\mathrm{at}(\mathrm{tab}_{j}(E),(p))=E[j:=p]$ holds for total
bodies (Chapter 3 treats the partial case).

The word *Naperian* refers to the right adjoint: $(-)^I=\mathbf{Set}(I,-)$
is a representable functor. Representable functors are called Naperian,
after Napier, because each has a "logarithm", its representing object $I$,
and the logarithm of a product of two of them is the disjoint union of
their logarithms: $A^I\times A^J\cong A^{I\sqcup J}$. The adjunction is
also a composite of the triple of Theorem 2.4 for $!:I\to1$: identifying
$\mathbf{Set}^1$ with $\mathbf{Set}$, $(-)\times I=\Sigma_!\,!^\ast$ and
$(-)^I=\Pi_!\,!^\ast$, and
$\mathbf{Set}(\Sigma_!\,!^\ast A,B)\cong\mathbf{Set}^I(!^\ast A,!^\ast B)\cong\mathbf{Set}(A,\Pi_!\,!^\ast B)$.

*Proof.* The adjunction, its unit and counit, and currying are
Proposition 0.6 of [Chapter 0](00-prerequisites.md) and the currying
consequence stated after it. Write $\hat g:A\to B^I$, $\hat g(a)=(i\mapsto g(a,i))$, for the
transpose of $g:A\times I\to B$. By Proposition 0.4,
$\hat g=g^I\circ\eta_A$, and $g=\mathrm{ev}\circ(\hat g\times\mathrm{id}_I)$.

For the constructors, fix a context $\Gamma$ with valuation set
$\mathrm{Val}(\Gamma)$. A scalar body $E$ in the context extended by
$j\in I$ is a total function $E:\mathrm{Val}(\Gamma)\times I\to K$.
Tabulation is its transpose,

$$
\mathrm{tab}_j(E)=\hat E=E^I\circ\eta_{\mathrm{Val}(\Gamma)}:\mathrm{Val}(\Gamma)\to K^I,
$$

the unit (here $\eta$ is the unit, not an input environment) followed by
applying $E$ under $(-)^I$. Selection of an array
$t:\mathrm{Val}(\Gamma)\to K^I$ at an index tuple $(p)$, read as a map
$p:\mathrm{Val}(\Gamma)\to I$, is the counit applied to the pair,

$$
\mathrm{at}(t,(p))=\mathrm{ev}\circ\langle t,p\rangle:\mathrm{Val}(\Gamma)\to K.
$$

Then
$\mathrm{at}(\mathrm{tab}_j(E),(p))(\nu)=\hat E(\nu)(p(\nu))=E(\nu,p(\nu))$,
which is $E[j:=p]$ evaluated at $\nu$. In arrows,
$\mathrm{ev}\circ\langle\hat E,p\rangle=\mathrm{ev}\circ(\hat E\times\mathrm{id}_I)\circ\langle\mathrm{id},p\rangle=E\circ\langle\mathrm{id},p\rangle$:
naturality of the counit followed by the first triangle identity, which is
the defining property of the transpose (Proposition 0.4). The argument
treats $E$ as a total function, which is why the equation is restricted to
total bodies. $\square$

*The partial case.* In Tensor Logic the body $E$ may be undefined at
some valuations, and tabulation is strict: it succeeds only if the body
succeeds at *every* coordinate
([Part III, Section 18.3](../semantics/tensor_logic_semantics_part_iii.md#183-reduction-and-tabulation)),
and selection does not bypass an undefined component (CONVENTIONS fact 4).
So for partial bodies the equation holds only as a definedness inequality:
if the left side is defined then it equals the right side, but the right
side can be defined when the left side is not. The specification's example
is $\mathrm{at}(\mathrm{tab}_{j\in[2]}(\log(X[j])),(0))$ with $X=(4,-1)$,
which is undefined although $\log(X[0])=\log4$ is defined
([Part III, Section 18.5](../semantics/tensor_logic_semantics_part_iii.md#185-definedness-examples-and-transformation-limits)).
The running example shows the same thing. At the model on
$\eta_1$, $Y=(0,4)$. The statement s4 reads $\log(Y[1])=\log4$, which is
defined. The "equivalent" expression $\mathrm{at}(\mathrm{tab}_j(\log(Y[j])),(1))$
is undefined, because the tabulation must also compute $\log(Y[0])=\log0$.
A rewrite from the second form to the first enlarges the domain of
definition; a rewrite from the first to the second shrinks it. Chapter 3
makes this "lax" behaviour precise.

*Lean.* The Lean types are literally the Naperian representation.

`leanncd/LeanNCD/Semantics/Types.lean`:

```lean
@[reducible] def Value (K : S → Type) : Ty S → Type
  | .scalar s => K s
  | .array s sh => Coord sh.axes → K s
```

An array value is a function out of its coordinate set. A scalar value is
an element of $K_s$, the rank-zero case identified with its single entry.

`leanncd/LeanNCD/Semantics/Expr.lean`:

```lean
  | tab {Γ s} (sh : ArrayShape) (layout : Layout sh.axes) :
      Expr K σ r (Γ × Coord sh.axes) (.scalar s) → Expr K σ r Γ (.array s sh)
  | at {Γ s sh} : Expr K σ r Γ (.array s sh) →
      (Γ → Coord sh.axes) → Expr K σ r Γ (.scalar s)
```

The signatures match the proof above exactly. `Expr.tab` takes a scalar body
in the context `Γ × Coord sh.axes` and returns an array in context `Γ`: the
transpose. `Expr.at` takes an array in context `Γ` and an index map
`Γ → Coord sh.axes`: the counit applied to the pair. The `layout` argument chooses
an enumeration of the coordinates for evaluation; it does not change the
coordinate set. In `leanncd/LeanNCD/Semantics/Interpret.lean`, `evalWith`
interprets `.tab` by running the body at every enumerated coordinate and
assembling the results with `sequence`, which fails if any component fails.
That is the strictness of the caution above, in code.

*A warning about products.* Because $(-)^I$ is a right adjoint, it preserves
products: $(A\times B)^I\cong A^I\times B^I$. A pair of families is a family
of pairs. This is the cartesian product, and it must not be confused with a
vector-space tensor product. Try the analogue with $\otimes$ for $I=[2]$ and
$A=B=\mathbb{R}$: the family $(A\otimes B)^I=(\mathbb{R}\otimes\mathbb{R})^{[2]}\cong\mathbb{R}^{[2]}$
has dimension $2$, while $A^I\otimes B^I=\mathbb{R}^{[2]}\otimes\mathbb{R}^{[2]}$
has dimension $4$. So the distributivity that holds for $\times$ fails for
$\otimes$ (compare the categorical proposal,
[Section 4.3](../semantics/categorical_tensor_logic_semantics.md#43-keep-the-products-distinct)).
The pointwise product $u\otimes v$ of two families in $K^{[2]}$, the
operation Tensor Logic actually uses, has 2 entries, not 4. An outer product
is obtained differently: pull both families back to the product index set
$[2]\times[2]$ and multiply pointwise there. The semantics never uses a
vector-space tensor product.

*Why this matters for an agentic coder.* This section is a checklist for
code that moves values between coordinate sets. A gather is $f^\ast$ and
needs nothing from $K$. A scatter-add or a reduction is $f_!$: it needs a
commutative monoid, and it is a homomorphism that composes, ignores
renumbering of sources, and can be computed chunk by chunk. Moving a weight
across a reduction is the transpose identity or the projection formula
(Lemma 2.12c in Section 4), and needs the full semiring. Tabulate-then-select differs from
direct evaluation once bodies can fail. Cite the Lean theorem for a law when
one exists; when none does (no adjunction on $K$-families), do not invent
one.

## 4. Contraction patterns are spans

An einsum statement has one finite set that controls everything: the set
$M$ of global valuations. Every operand coordinate and the output coordinate
are read off $M$ by maps. For two operands and one output this is a diagram
$J_1\leftarrow M\to J_2$ with a third leg to the output. The case of one
operand and one output is a span, and spans compose. This section
shows that composing contractions is composing spans.

**Definition 2.10 (span).** A span from $I$ to $J$ in $\mathbf{FinSet}$ is
$I\xleftarrow{l}M\xrightarrow{r}J$. Spans compose by pullback:
$(I\leftarrow M\to J)$ then $(J\leftarrow N\to L)$ gives
$I\leftarrow M\times_J N\to L$ with $M\times_J N=\{(m,n)\mid r(m)=l'(n)\}$.
Two spans are isomorphic when there is a bijection of apexes commuting with
both legs. $\mathbf{Span}(\mathbf{FinSet})$ has finite sets as objects and
isomorphism classes of spans as morphisms; the identity is
$I\xleftarrow{\mathrm{id}}I\xrightarrow{\mathrm{id}}I$.

In the composite, the second span is $J\xleftarrow{l'}N\xrightarrow{r'}L$,
and the legs of the composite are $l\circ\pi_M$ and $r'\circ\pi_N$, where
$\pi_M,\pi_N$ are the projections from $M\times_JN$. Read the apex as a set
of "paths": an element is a pair $(m,n)$ whose middle coordinates agree.
Definition 2.10 is Definition 0.29 of [Chapter 0](00-prerequisites.md)
restricted to finite sets; Chapter 0 defers the proof of the category laws
to here.

**Proposition 2.10a (spans form a category).** Composition in
Definition 2.10 is well defined on isomorphism classes, associative and
unital, so $\mathbf{Span}(\mathbf{FinSet})$ is a category.

*Proof.* We check the three things Definition 2.10 needs.

*Composition is well defined on isomorphism classes.* Let
$\alpha:M\to\bar M$ be an isomorphism of spans from $I$ to $J$ (so
$\bar l\alpha=l$ and $\bar r\alpha=r$) and $\beta:N\to\bar N$ one of spans
from $J$ to $L$. Then $(m,n)\mapsto(\alpha m,\beta n)$ sends
$M\times_JN$ into $\bar M\times_J\bar N$, because
$\bar r(\alpha m)=r(m)=l'(n)=\bar l'(\beta n)$. Its inverse is
$(\bar m,\bar n)\mapsto(\alpha^{-1}\bar m,\beta^{-1}\bar n)$ by the same
argument, and it commutes with the composite legs because $\alpha,\beta$
commute with $l$ and $r'$.

*Identities.* Compose the identity span on $I$ with
$I\xleftarrow{l}M\xrightarrow{r}J$. The apex is
$I\times_IM=\{(i,m)\mid i=l(m)\}$, and $m\mapsto(l(m),m)$ is a bijection
$M\to I\times_IM$ with inverse $(i,m)\mapsto m$. It commutes with the legs:
the left leg of the composite sends $(l(m),m)$ to $l(m)$ and the right leg
sends it to $r(m)$. The other identity law is symmetric.

*Associativity.* For a third span $L\xleftarrow{l''}Q\xrightarrow{r''}H$,

$$
(M\times_JN)\times_LQ=\{((m,n),q)\mid r(m)=l'(n),\ r'(n)=l''(q)\},
$$

$$
M\times_J(N\times_LQ)=\{(m,(n,q))\mid r'(n)=l''(q),\ r(m)=l'(n)\}.
$$

The map $((m,n),q)\mapsto(m,(n,q))$ is a bijection between them, and both
outer legs send the corresponding elements to $l(m)$ and $r''(q)$. So the
two composites are isomorphic spans. Since morphisms are isomorphism
classes, composition is strictly associative and unital in
$\mathbf{Span}(\mathbf{FinSet})$. $\square$

**Definition 2.11 (linearization).** A span $I\xleftarrow{l}M\xrightarrow{r}J$
with a weight $w\in K^M$ determines the matrix
$\mathrm{Lin}(l,w,r)=\langle l,r\rangle_!\,w\in K^{I\times J}$, the
pushforward of the weight along the paired map
$\langle l,r\rangle:M\to I\times J$, and the linear map $K^I\to K^J$,
$u\mapsto r_!(l^\ast u\otimes w)$. The matrix, applied to $u$, gives the
map.

Entrywise,

$$
\mathrm{Lin}(l,w,r)[i,j]=(\langle l,r\rangle_!\,w)(i,j)=\bigoplus_{m:\ l(m)=i,\ r(m)=j}w(m).
$$

Each row $i$ is the pushforward $r_!$ of the weight restricted to the fibre
$l^{-1}(i)$. With $w=1$ the map sends $u$ to
$j\mapsto\bigoplus_{m:r(m)=j}u(l(m))$. The map and the matrix agree and
determine each other. Given the matrix,

$$
\begin{aligned}
\bigoplus_{i\in I}u(i)\otimes\mathrm{Lin}[i,j]
&=\bigoplus_{i}\ \bigoplus_{m:\ l(m)=i,\ r(m)=j}u(l(m))\otimes w(m)\\
&=\bigoplus_{m:\ r(m)=j}u(l(m))\otimes w(m)=\big(r_!(l^\ast u\otimes w)\big)(j),
\end{aligned}
$$

by distributivity and then Proposition 2.7(4) for the partition of
$r^{-1}(j)$ by the value of $l$. Conversely, the map applied to the indicator
family $\delta_i$ ($1_K$ at $i$, $0_K$ elsewhere) returns row $i$ of the
matrix.

Let $\mathbf{Mat}(K)$ be the category whose objects are finite sets, whose
morphisms $I\to J$ are matrices in $K^{I\times J}$, with composition
$(A;B)[i,k]=\bigoplus_jA[i,j]\otimes B[j,k]$ and identities the delta
matrices $\delta_I[i,i']=\mathbf{1}_{i=i'}$. Associativity and unit laws are
the usual matrix computations, valid in any commutative semiring.

*Weighted spans.* Weighted spans also form a category. Two weighted spans
are isomorphic when a bijection of apexes commutes with the legs *and*
carries one weight to the other ($\bar w\circ\alpha=w$). The composite of
$(l,w,r)$ and $(l',w',r')$ has weight $\pi_M^\ast w\otimes\pi_N^\ast w'$ on
$M\times_JN$. The identity weighted span is the identity span with weight
$1$. The checks of Proposition 2.10a go through, with associativity of
$\otimes$ added for the associativity law and $1_K\otimes w=w$ added for the
unit laws. An unweighted span is a weighted span with
$w=1$, and composites of such spans keep weight $1\otimes1=1$, so
$\mathbf{Span}(\mathbf{FinSet})$ sits inside the weighted category.

**Proposition 2.12 (composition linearizes to matrix product).** For
composable weighted spans, the linearization of the pullback composite is
the composite of the linearizations:

$$
r'_!\big(l'^\ast\,r_!(l^\ast u\otimes w)\otimes w'\big) =
(r'\circ\pi_N)_!\big((l\circ\pi_M)^\ast u\otimes \pi_M^\ast w\otimes\pi_N^\ast w'\big).
$$

*Proof.* We need three lemmas, each a direct fibre computation.

**Lemma 2.12a (Beck–Chevalley, decategorified).** For the pullback square with
$P=M\times_JN$ and any $x\in K^M$,

$$
l'^\ast\,r_!\,x=(\pi_N)_!\,\pi_M^\ast\,x.
$$

At $n\in N$ the left side is $\bigoplus_{m:\ r(m)=l'(n)}x(m)$. The right side
is $\bigoplus_{(m,n')\in P,\ n'=n}x(m)$. The map $m\mapsto(m,n)$ is a bijection
from $\{m\mid r(m)=l'(n)\}$ onto the fibre $\pi_N^{-1}(n)$, by the definition
of $P$. Reindexing along it (Proposition 2.7(3)) shows the two sums are equal.
Note that this is the cardinality of the set-level isomorphism
$\Sigma_{\pi_N}\pi_M^\ast\cong l'^\ast\Sigma_r$ (Beck–Chevalley, Section 2).

**Lemma 2.12b (pullback preserves products).** For $h:P\to M$ and
$x,y\in K^M$, $h^\ast(x\otimes y)=h^\ast x\otimes h^\ast y$, because both are
$p\mapsto x(h(p))\otimes y(h(p))$.

**Lemma 2.12c (projection formula).** For $h:P\to N$, $x\in K^P$ and $y\in K^N$,

$$
(h_!x)\otimes y=h_!\big(x\otimes h^\ast y\big).
$$

At $n$, the left side is $\big(\bigoplus_{h(p)=n}x(p)\big)\otimes y(n)$. By
distributivity this is $\bigoplus_{h(p)=n}x(p)\otimes y(h(p))$, which is the
right side. For an empty fibre both sides are $0_K$, using absorption on the
left. This is the decategorified projection formula of Section 3.

Now compute, starting from the left side of the proposition:

$$
\begin{aligned}
l'^\ast\,r_!(l^\ast u\otimes w)
&=(\pi_N)_!\,\pi_M^\ast(l^\ast u\otimes w) &&\text{Lemma 2.12a}\\
&=(\pi_N)_!\big((l\circ\pi_M)^\ast u\otimes\pi_M^\ast w\big) &&\text{Lemma 2.12b and }(l\pi_M)^\ast=\pi_M^\ast l^\ast.
\end{aligned}
$$

Multiply by $w'$ and use Lemma 2.12c with $h=\pi_N$:

$$
(\pi_N)_!\big((l\pi_M)^\ast u\otimes\pi_M^\ast w\big)\otimes w' =
(\pi_N)_!\big((l\pi_M)^\ast u\otimes\pi_M^\ast w\otimes\pi_N^\ast w'\big).
$$

Finally apply $r'_!$ and use $r'_!\circ(\pi_N)_!=(r'\circ\pi_N)_!$ from
Proposition 2.7(2). The result is the right side of the proposition. $\square$

**Corollary 2.12d (Lin is a functor).** $\mathrm{Lin}$ is a functor
$\mathbf{Span}(\mathbf{FinSet})\to\mathbf{Mat}(K)$, and more generally a
functor from weighted spans.

*Proof.* Define $\mathrm{Lin}$ on a weighted span by its matrix
$\langle l,r\rangle_!w$. It is well defined on isomorphism classes by
Proposition 2.7(3): an isomorphism $\alpha$ satisfies
$\langle\bar l,\bar r\rangle\circ\alpha=\langle l,r\rangle$ and
$\bar w\circ\alpha=w$, so $\langle\bar l,\bar r\rangle_!\bar w=\langle l,r\rangle_!w$.
It preserves identities: the identity span with weight $1$ has matrix
$\langle\mathrm{id},\mathrm{id}\rangle_!1$, which is $1_K$ on the diagonal
and $0_K$ elsewhere, the delta matrix. (As maps, $u\mapsto\mathrm{id}_!(u\otimes1)=u$
by `pushforward_id`.) It preserves composition by Proposition 2.12, since the
map determines the matrix. $\square$

$\mathrm{Lin}$ is the decategorification of span composition: the apex of a composite
counts paths, and the matrix product sums their weights. It forgets
multiplicity: $1\leftarrow[2]\to1$ with weight $1$ and $1\leftarrow1\to1$
with weight $2$ are not isomorphic, yet both give the matrix $(2)$.

*Matrix multiplication.* $Y[i,k]=A[i,j]B[j,k]$ with $i\in[n_i]$, $j\in[n_j]$,
$k\in[n_k]$ is the composite of the spans
$[n_i]\leftarrow[n_i]\times[n_j]\to[n_j]$ and
$[n_j]\leftarrow[n_j]\times[n_k]\to[n_k]$ (legs the projections) with
weights $A$ and $B$. The pullback apex is
$\{((i,j),(j',k))\mid j=j'\}\cong[n_i]\times[n_j]\times[n_k]$ with weight
$A[i,j]\otimes B[j,k]$, so the matrix is $\bigoplus_jA[i,j]\otimes B[j,k]=Y[i,k]$.
The contracted index $j$ is the variable the pullback glues on.

The slogan "composition of two contractions is matrix multiplication" is a
statement about composition of morphisms in $\mathbf{Mat}(K)$. It is
transported from composition by pullback in $\mathbf{Span}(\mathbf{FinSet})$
by the functor $\mathrm{Lin}$ of Corollary 2.12d. A single statement with
several operands is the one-span presentation of the same composite: the
global valuation set $M$ of Proposition 2.13 plays the role of the pullback
apex, with one projection per operand and one for the output.

*Running example.* The statement s1 is such a composite. Encode $X$ as the
weighted span $1\xleftarrow{!}[2]\xrightarrow{\mathrm{id}}[2]$ with weight
$X$; it linearizes to the map $K^1\to K^{[2]}$, $\lambda\mapsto \lambda\otimes X$.
Encode $W$ as the weighted span $[2]\xleftarrow{\pi_X}M\xrightarrow{\pi_{\mathrm{out}}}[2]$
with weight $\pi_W^\ast W=W$, so that its left leg reads the index $i$ and
its right leg writes the index $j$. The pullback apex is
$\{(i',(j,i))\mid i'=i\}\cong M$, with legs to $1$ and to $j$, and weight
$X[i]\otimes W[j,i]$. Its linearization at $\lambda=1$ is

$$
j\mapsto\bigoplus_{i\in[2]}X[i]\otimes W[j,i]=(1\cdot1+(-2)\cdot1,\ 1\cdot2+(-2)(-1))=(-1,4),
$$

the value $V_{s1}$ computed in Section 3. The composite weight is
$\pi_X^\ast X\otimes\pi_W^\ast W$, which in a commutative semiring equals
the summand family $\theta=\pi_W^\ast W\otimes\pi_X^\ast X$ of Section 3.

Before the next statement, two conventions of the specification
([Part I, Section 2.3](../semantics/tensor_logic_semantics_part_i.md#23-which-algebraic-laws-each-part-uses)).
*Coherence* is the assumption that the $\oplus$ and $0_K$ an expression uses
for a reduction are the same monoid that collection uses. The *bracketing
convention* says that a finite product of an ordered list of factors is the
left-nested product, so two products of the same factors in the same order
are the same term and relating them uses no law of $\otimes$.

**Proposition 2.13 (pure einsum; Proposition 19.1 of the specification).**
Consider an einsum with $m\ge1$ operands $T_1,\dots,T_m$, global valuation
set $M=\mathrm{Val}(\Gamma_{\mathrm{all}})$, operand projections
$\pi_\ell:M\to\mathrm{Coord}(T_\ell)$ and output projection
$\pi_{\mathrm{out}}:M\to\mathrm{Coord}(Y)$, and let $s$ be its normalized
pure statement
([Part II, Section 17.3](../semantics/tensor_logic_semantics_part_ii.md#173-connection-to-the-contribution-core)).
Whenever the contribution tensor $V_s^\rho$ of $s$
([Part III, Section 19.2](../semantics/tensor_logic_semantics_part_iii.md#192-statement-contributions-and-collected-tensors))
is defined (a pure statement applies no partial primitive),

$$
V_s^\rho=(\pi_{\mathrm{out}})_!\Big(\bigotimes_{\ell=1}^m\pi_\ell^\ast\,\rho(T_\ell)\Big).
$$

Here $\Gamma_{\mathrm{all}}$ is the context of all distinct index variables
of the operand strings, and $\pi_\ell$, $\pi_{\mathrm{out}}$ are the tuple
projections $\pi_L(\nu)=(\nu(j_1),\dots,\nu(j_k))$ for the index strings $L$
of the operands and the output
([Part II, Section 17.1](../semantics/tensor_logic_semantics_part_ii.md#171-index-strings-and-global-valuations)).
At a coordinate $p$, the right side unfolds to

$$
\bigoplus_{\nu\in M,\ \pi_{\mathrm{out}}(\nu)=p}\ \bigotimes_{\ell=1}^m\rho(T_\ell)[\pi_\ell(\nu)],
$$

which is verbatim the canonical fibre semantics $V$ of
[Part II, Section 17.2](../semantics/tensor_logic_semantics_part_ii.md#172-canonical-fiber-semantics),
rewritten with the two functors. Repeated indices, diagonals, broadcasts,
and empty fibres are all encoded by the maps $\pi_\ell,\pi_{\mathrm{out}}$,
never by matching names. The content of the proposition is that the core
statement obtained by elaboration computes this same value.

*Idea of the proof.* Decompose each global valuation into its output part
and its contracted part. Elaboration splits the variables of $M$ into the
distinct output variables, which form the statement context $\Gamma_s$,
and the remaining variables, which form a context $\Gamma_c$ contracted in
the body. So $M\cong\mathrm{Val}(\Gamma_s)\times\mathrm{Val}(\Gamma_c)$, and
the output projection factors as

$$
\pi_{\mathrm{out}}=\phi_s\circ\mathrm{pr}_s,\qquad
\mathrm{pr}_s:M\to\mathrm{Val}(\Gamma_s),\quad\phi_s:\mathrm{Val}(\Gamma_s)\to\mathrm{Coord}(Y).
$$

By Proposition 2.7(2), $(\pi_{\mathrm{out}})_!=(\phi_s)_!\circ(\mathrm{pr}_s)_!$.
The inner pushforward $(\mathrm{pr}_s)_!$ is the body's nested reduction
over the contracted variables. The outer pushforward $(\phi_s)_!$ is the
sum over the write fibre that defines $V_s^\rho$. A repeated output index
makes $\phi_s$ a diagonal, whose off-diagonal fibres are empty and receive
$0_K$. An empty contracted domain makes every fibre of $\mathrm{pr}_s$
empty, so every body is an empty reduction with value $0_K$. The argument
uses only the commutative-monoid laws of $\oplus$, coherence and the
bracketing convention, not distributivity.

*Status.* The specification gives a paper argument
([Part III, Section 19.3](../semantics/tensor_logic_semantics_part_iii.md#193-correspondence-with-pure-einsum)).
Lean proves the proposition for the bounded source fragment only, as
`Term.collectedBody_correspondence`
(`leanncd/LeanNCD/Semantics/Source/Correspondence.lean`) and
`AdmittedSource.collect_correspondence`
(`leanncd/LeanNCD/Semantics/Source/ProgramCorrespondence.lean`); the
independence from the order of nested reductions is
`interpret_contract_reindex`
(`leanncd/LeanNCD/Semantics/Source/Lowering.lean`), which is relabeling,
Proposition 2.7(3), at the level of interpreted expressions. Beyond that
fragment the proposition remains a proof obligation
([Part II, Section 17.3](../semantics/tensor_logic_semantics_part_ii.md#173-connection-to-the-contribution-core)).
These three names live in the `Source/` subdirectory of
`leanncd/LeanNCD/Semantics/`; they are the names the specification's status
table and Part III, Section 19.3 cite.

Running example: s1 has $M=[2]\times[2]$, $\pi_W=\mathrm{id}$,
$\pi_X(j,i)=i$, $\pi_{\mathrm{out}}(j,i)=j$, and
$V_{s1}=(\pi_{\mathrm{out}})_!(\pi_W^\ast W\otimes\pi_X^\ast X)$, which on
$\eta_1$ is $(1\cdot1+1\cdot(-2),\ 2\cdot1+(-1)(-2))=(-1,4)$. The second
writer s2 contributes $B=(1,0)$, so collection (Chapter 4) gives $Z=(0,4)$.

In the factorization above, s1 has $\Gamma_c=(i:[2])$,
$\mathrm{pr}_s(j,i)=j$ and $\phi_{s1}=\mathrm{id}$. Its $\pi_X$ is a
broadcast (non-injective); a diagonal read `A[i,i]` would be a
non-surjective $\pi_\ell$; a diagonal write `D[i,i]` would be a
non-surjective $\pi_{\mathrm{out}}$ with empty off-diagonal fibres.

*Why this matters for an agentic coder.* An agent compiling einsum does not
need a name-matching heuristic. It needs the three maps and the two
functors. The optimizations of this section (fusing contractions,
reordering sums, contraction order) are instances of Proposition 2.12 or
Proposition 2.7 and can be checked against those laws. Contraction-order
optimization, for example, is associativity of span composition plus
functoriality of $\mathrm{Lin}$ (Corollary 2.12d). Other rewrites, such as
delta elimination and distribution over a pointwise $\oplus$, need the
conditions of
[Part II, Sections 17.4 and 17.5](../semantics/tensor_logic_semantics_part_ii.md#174-delta-tensors-and-diagonal-identities).
A transformation that is an instance of none of these is suspect:
replacing an intermediate by a scalar that drops a shared index changes the
apex, which is why $\sum_ia[i]b[i]c[i]\neq(\sum_ia[i]b[i])(\sum_ic[i])$ in
general ([Part II, Section 17.5](../semantics/tensor_logic_semantics_part_ii.md#175-conditions-for-semantic-transformations)).
And none of this applies across a nonlinear operator: $\mathrm{relu}$ in s3
is not a span.

## 5. Occurrences are a coproduct

**Definition 2.14 (occurrences and destinations).** For a program $P$ with
statements $s$, the occurrence set is the coproduct
$\mathcal{O}_P=\coprod_s D_s$ and the destination map
$\mathrm{dst}=[\,(T_s,\phi_s)\,]_s:\mathcal{O}_P\to\mathrm{Addr}_{\mathrm{Def}}$
is the copairing of the write maps. The fibre $\mathcal{C}_P(a)=\mathrm{dst}^{-1}(a)$
is the writer family of $a$.

The copairing is the map out of the coproduct given on the summand $D_s$ by
$\nu\mapsto(T_s,\phi_s(\nu))$, that is, $\mathrm{dst}(s,\nu)=(T_s,\phi_s(\nu))$.
Here $\mathrm{Addr}_{\mathrm{Def}}=\coprod_{T\in\mathrm{Def}}\mathrm{Coord}(T)$
is itself a coproduct: addresses are tagged by tensor, so $(Z,0)$ and
$(Y,0)$ are different even though their coordinate tuples agree
([Part I, Section 5.2](../semantics/tensor_logic_semantics_part_i.md#52-partial-stores-and-available-values)).

This is exactly the data a pushforward needs: a finite source, a finite
target, and a map. Each occurrence $o=(s,\nu)$ has a body value
$[\![E_s]\!]_{\rho,\nu}$, so for an environment in which every body is
defined, the body values form a family
$c_\rho\in\prod_{o\in\mathcal{O}_P}K$. Collection in Chapter 4 will be

$$
\mathrm{Collect}_P(\rho)=\mathrm{dst}_!\,c_\rho,\qquad
\mathrm{Collect}_P(\rho)(T)[p]=\bigoplus_{o\in\mathcal{C}_P(T,p)}c_\rho(o).
$$

(When defined tensors have different sorts, the pushforward is taken tensor
by tensor with the monoid of each tensor's sort; the regrouping is
Proposition 2.7(4).) Every property of collection that does not depend on
the bodies is therefore a property of $\mathrm{dst}_!$, already proved in
Section 3: an address with no writers gets $0_K$; collection can be
computed statement by statement and summed (grouping); and renaming
statements or valuations by a bijection changes nothing (relabeling).

*Why the coproduct, not the union.* Two statements with identical text
have occurrences tagged by different statement identifiers: in a coproduct
they are different elements and different summands, while in a union of
"texts with valuations" they would collapse to one. The first reading is
the correct one (CONVENTIONS fact 1). Relabeling the occurrence set by a
*bijection* is harmless (Proposition 2.7(3)); deleting a duplicate is not a
bijection. Try it: add to `Scorer` a statement s2' with the same text as
s2. Then $\mathcal{O}_P$ has nine elements and on $\eta_1$ the three writers
of $Z$ give $Z=(-1+1+1,\ 4+0+0)=(1,4)$. Deduplicating s2' gives back
$(0,4)$, a different tensor, and no law licenses it.

*Running example.* For `Scorer`, $D_{s1}=D_{s2}=D_{s3}=[2]$ and
$D_{s4}=\{()\}$, so $\mathcal{O}_P$ has seven elements:

| Occurrence $o$ | $\mathrm{dst}(o)$ |
| --- | --- |
| $(s1,j{=}0)$ | $(Z,0)$ |
| $(s1,j{=}1)$ | $(Z,1)$ |
| $(s2,j{=}0)$ | $(Z,0)$ |
| $(s2,j{=}1)$ | $(Z,1)$ |
| $(s3,j{=}0)$ | $(Y,0)$ |
| $(s3,j{=}1)$ | $(Y,1)$ |
| $(s4,())$ | $(L,())$ |

$\mathrm{Addr}_{\mathrm{Def}}$ has five elements. The fibres of $(Z,0)$ and
$(Z,1)$ have two elements each; those of $(Y,0)$, $(Y,1)$ and $(L,())$ have
one each. The map $\mathrm{dst}$ is surjective (every defined address has a
writer) and not injective (the two writers of each $Z[j]$ collide).

The number of writers is itself a pushforward. Push the constant family
$1\in K^{\mathcal{O}_P}$ forward along $\mathrm{dst}$:

$$
\mathrm{dst}_!\,1:\ (Z,0)\mapsto2,\ (Z,1)\mapsto2,\ (Y,0)\mapsto1,\ (Y,1)\mapsto1,\ (L,())\mapsto1.
$$

This is the cardinality of $\Sigma_{\mathrm{dst}}1$, whose value at $a$ is a
copy of the writer family $\mathcal{C}_P(a)$: a set and its
decategorification.

Now evaluate the bodies at the unique model on $\eta_1$, where $Z=(0,4)$
and $Y=(0,4)$. The body values are $(-1,4)$ for s1, $(1,0)$ for s2,
$(\mathrm{relu}\,0,\mathrm{relu}\,4)=(0,4)$ for s3, and $\log4$ for s4.
Pushing forward along $\mathrm{dst}$ gives $Z=(-1+1,4+0)=(0,4)$,
$Y=(0,4)$ and $L=\log4$, which is the model again. That the model is a
fixed point of collection is the subject of Chapter 4.

Collection is defined on every admissible environment, one in which all
seven bodies are defined. On the failing input $\eta_0$, take the
environment the machine builds, with $Z=(1,0)$ and $Y=(1,0)$. There the
body of s4 is $\log0$, undefined, so this environment is not admissible and
there is no family $c_\rho$ to push forward. Other environments extending
$\eta_0$ are admissible: the only partial body is $\log(Y[1])$, so any
$\rho$ with $\rho(Y)[1]>0$ will do, and collection is defined there. What
fails is the model equation. Collection forces $Z=(1,0)$ (since $X=0$), so
a fixed point must have $Z=(1,0)$ and then $Y=\mathrm{relu}(Z)=(1,0)$,
contradicting $Y[1]>0$. Hence $\mathrm{Models}(P,\eta_0)=\varnothing$
(Chapter 4).

*Lean.* The production module groups occurrences by defined tensor rather
than forming one global coproduct.

`leanncd/LeanNCD/Semantics/Program.lean`:

```lean
abbrev Occurrence (P : Program K σ r) (t : P.Defined) :=
  (s : Fin (P.statements t)) × {v : Fin (P.valuations t s) // P.guard t s v = true}
```

```lean
def collect (ρ : Store K σ) (h : P.AdmEnv ops ρ) (t : P.Defined) :
    Coord (σ.signature t.val).axes → K (σ.signature t.val).sort :=
  letI := coordDecidableEq (σ.signature t.val).axes
  pushforward (fun o : P.Occurrence t => P.destination t o.1 o.2)
    (P.contribution ops ρ h t)
```

`Program.Occurrence t` is a sigma type, Lean's coproduct, over the
statements `s` that target the defined tensor `t`; the summand for `s` is
the subtype of guard-passing valuations, which is $D_s$ (valuations are
numbered as `Fin (P.valuations t s)`, a choice of enumeration). Statement
identifiers are local to their target, so Lean's occurrence set for `t` is
$\coprod_{s:\,T_s=t}D_s$, and $\mathcal{O}_P$ is the coproduct of these over
`t`. Since $T_s$ is fixed per statement, $\mathrm{dst}$ is the coproduct of
the per-tensor maps `fun o => P.destination t o.1 o.2`. `Program.collect`
pushes the body values `P.contribution ops ρ h t` forward along that map:
it is $\mathrm{dst}_!\,c_\rho$ restricted to `t`. The argument
`h : P.AdmEnv ops ρ` means collection cannot be called without a proof that
every body is defined. The two collection laws are lifted to programs:
`Program.collect_grouped` is grouping by statement (it is proved by
`pushforward_grouped`), and `Program.collect_relabel` is relabeling of
occurrences along an equivalence (proved by `pushforward_relabel`).

*Why this matters for an agentic coder.* When you generate code that
accumulates into a tensor from several statements, you are implementing
$\mathrm{dst}_!$, and the occurrence set is your loop domain. Build it as a
tagged union: keep the statement identifier in the loop, and never merge
statements because their text, their body or their values agree. You are
free to process statements in any order, to fuse loops over valuations, or
to renumber valuations, because each of these is a bijection of the source
or a regrouping of it. Anything that changes the number of elements of the
source, such as common-subexpression elimination across two identical
writers, changes the answer.

## 6. What this chapter did not do

- **No $\otimes$ on $\bot$.** All values here are defined scalars. Strict
  products, the failure of $0\otimes\bot=0$, and lax naturality of batching
  are in [Chapter 3](03-partiality.md). The only glimpse was the caution
  after Proposition 2.9.
- **No additive pushforward of undefined values.** Collection begins after
  every admitted body is defined; $\bot$ is never a summand and is not
  $0_K$ ([Chapter 4](04-denotational.md)).
- **No adjunction on $K$-families.** Proposition 2.8 is the decategorified
  shadow of the projection formula for $\Sigma_f$, proved directly; the
  adjunction is a theorem only for $\mathbf{Set}$-valued families
  (Theorem 2.4).
- **No vector-space tensor products.** Products of value spaces are
  cartesian, and $\otimes$ is the pointwise product on one coordinate set.
- **No St/Br graded PROP.** The categorical proposal's identity-aware
  string-diagram syntax: an operation category $\mathbf{Br}$ (a colored
  PROP, that is, a symmetric monoidal category of string diagrams) graded
  by an index PROP $\mathbf{St}$ whose objects are shapes and whose
  morphisms are reindexings. It is discussed only in the
  [outlook](07-outlook.md).

## Exercises

1. Show that for $f:I\to J$ the unit $A\to f^\ast\Sigma_f A$ is an
   isomorphism for every $A$ (that is, it is a natural isomorphism) iff $f$
   is injective, and the counit $\Sigma_f f^\ast B\to B$ is an isomorphism
   for every $B$ iff $f$ is bijective. For the scatter write `Y[2i]`
   (injective, not surjective) and the colliding write `Y[i+j]` (surjective
   when $Y$ has extent 3, not when it has extent 4; never injective), say
   which of unit and counit fails and what that failure means for the
   written tensor.
2. Let $I=\coprod_{s\in S}I_s$ with $S$ finite, inclusions $\iota_s$, and
   $f_s=f\circ\iota_s$ for $f:I\to J$. Show that $A\mapsto(\iota_s^\ast A)_s$
   is an equivalence $\mathbf{Set}^I\simeq\prod_s\mathbf{Set}^{I_s}$, and
   that under it both $\Sigma_f$ and $(A_s)_s\mapsto\coprod_s\Sigma_{f_s}A_s$
   are left adjoint to $B\mapsto(f_s^\ast B)_s$. Deduce the grouping
   isomorphism $\Sigma_fA\cong\coprod_s\Sigma_{f_s}\iota_s^\ast A$ from the
   uniqueness of adjoints, without computing a fibre, and take cardinalities
   to recover Proposition 2.7(4) for $\mathbb{N}$-valued families.
3. Use the transpose identity (Proposition 2.8) to show that $f_!$ and
   $f^\ast$ are transposes of each other as matrices over $K$ when $I,J$ are
   enumerated. Write both matrices for $\pi_{\mathrm{out}}:M\to[2]$ of s1,
   with $M$ enumerated as $(0,0),(0,1),(1,0),(1,1)$, and redo the running
   example after Proposition 2.8 as a matrix computation.
4. Compute the span composite for `Y[i,k] = A[i,j] B[j,k]` followed by
   `Z[i] = Y[i,k] C[k]` and check that Proposition 2.12 gives the same
   matrix as evaluating the two statements in sequence.
5. Write the diagonal read `tr = A[i,i]` as a weighted span $1\leftarrow[n]\to 1$
   and compute its linearization.
6. $^\ast$ For a pullback square of finite sets as in Section 2, define the
   comparison map $g^\ast\Pi_f\Rightarrow\Pi_q\,p^\ast$ (the mate, built from
   the unit of $q^\ast\dashv\Pi_q$ and the counit of $f^\ast\dashv\Pi_f$),
   compute it on elements, and prove that it is an isomorphism. Then
   decategorify to the fibrewise product $f_\otimes$ of Section 3: show
   $g^\ast(f_\otimes v)=q_\otimes(p^\ast v)$ for $v\in K^I$ and any
   commutative monoid $(K,\otimes,1_K)$, and check it on the s1 square with
   $v=X=(1,-2)$.
7. $^\ast$ Let $\pi_1:I\times J\to I$ be the projection $(i,j)\mapsto i$. For
   a total body $E$ with free indices $i\in I$ and $j\in J$, show that
   $\mathrm{tab}_i\big(\bigoplus_{j\in J}E\big)=(\pi_1)_!\big(\mathrm{tab}_{(i,j)}(E)\big)$
   in $K^I$ ("sum then tabulate" equals "tabulate then sum"), using
   currying $K^{I\times J}\cong(K^J)^I$ (Proposition 2.9) and the fact that
   the fibre of $\pi_1$ over $i$ is $\{i\}\times J\cong J$ (relabeling,
   Proposition 2.7(3)). Then let $E$ be partial: show that both sides are
   defined exactly when $E$ is defined at every $(i,j)$ (strictness of
   tabulation and reduction, [Chapter 3](03-partiality.md)), so the equation
   still holds with equal definedness, unlike the equation of
   Proposition 2.9.
8. $^\ast$ Proposition 2.10a proves that $\mathbf{Span}(\mathbf{FinSet})$ is
   a category by computing with elements. (a) Reprove it for spans in any
   category with pullbacks, using only the universal property of the
   pullback (Definition 0.27): show that composition is well defined on
   isomorphism classes, and obtain associativity and the unit laws by
   pasting pullback squares (prove the pasting lemma you use). (b) Show that
   $\mathrm{Lin}$ (Corollary 2.12d) is faithful when $K=\mathbb{N}$: two
   spans $I\leftarrow M\to J$ with the same matrix are isomorphic. (c) Show
   that it is not faithful when $K$ is the Boolean sort.
