# Chapter 0. The categorical toolkit

**Summary.** This chapter collects the six constructions that the rest of the course uses beyond plain categories, functors and natural transformations: adjunctions, Kan extensions, monads with their Kleisli categories, algebras and coalgebras, spans with pullbacks, and equalizers. Each is introduced with the smallest examples later chapters need, and each section ends by naming the chapter that uses it. Examples marked `Scorer` use the program of [Chapter 1, Section 4](01-tensor-logic.md#4-the-running-example); read that section first or skip those examples on a first pass.

## 1. Conventions recap

We write $\mathbf{Set}$ for sets and functions, $\mathbf{FinSet}$ for finite sets and all functions, and $\mathbf{Pfn}$ for sets and partial functions. A partial function $f : A \rightharpoonup B$ is a function $f : \mathrm{dom}(f) \to B$ defined on a subset $\mathrm{dom}(f)\subseteq A$. Partial functions compose where both are defined: $(g\circ f)(a)$ is defined iff $a\in\mathrm{dom}(f)$ and $f(a)\in\mathrm{dom}(g)$, and then equals $g(f(a))$. The identity is the total identity. We write $[n]=\{0,\dots,n-1\}$, so $[0]=\varnothing$.

Functors and natural transformations are as usual. We write $\mathcal{D}^{\mathcal{C}}$ for the functor category, and an *endofunctor* is a functor $\mathcal{C}\to\mathcal{C}$. A contravariant functor is a functor out of $\mathcal{C}^{\mathrm{op}}$.

**Limits and colimits we need.** In $\mathbf{Set}$ and $\mathbf{FinSet}$: the terminal object $1=\{()\}$ (one map into it from every set), the initial object $0=\varnothing$ (one map out of it to every set), the product $A\times B$ of pairs with its projections, and the coproduct $A+B$ (disjoint union, tagged $\mathrm{inl}(a)$, $\mathrm{inr}(b)$) with its injections. A map out of a coproduct is a pair of maps (copairing); a map into a product is a pair of maps (pairing). For a family $(A_i)_{i\in I}$ the coproduct is $\coprod_{i\in I}A_i=\{(i,a)\mid a\in A_i\}$ and the product is $\prod_{i\in I}A_i$, the functions $v$ with $v(i)\in A_i$. An empty coproduct is $0$ and an empty product is $1$.

**Definition 0.1 (discrete category).** For a set $I$, the *discrete category* on $I$ has the elements of $I$ as objects and only identity morphisms. A functor $A : I\to\mathcal{C}$ from a discrete category is exactly an $I$-indexed family of objects $(A_i)_{i\in I}$. A natural transformation between two such functors is exactly a family of morphisms $(\alpha_i : A_i\to B_i)_{i\in I}$, with no naturality condition, as there are no non-identity morphisms. A function $f : I\to J$ is a functor between discrete categories.

We write $\mathbf{Set}^I$ for the category of functors $I\to\mathbf{Set}$ ("families of sets over $I$"). The *slice category* $\mathbf{Set}/I$ has as objects functions $p : A\to I$ and as morphisms $h : (A,p)\to(A',p')$ the functions $h : A\to A'$ with $p'\circ h=p$ ("maps over $I$").

**Proposition 0.2.** $\mathbf{Set}/I\simeq\mathbf{Set}^I$ (equivalence of categories).

*Proof.* Let $\Phi(A,p)_i=p^{-1}(i)$, the *fibre* over $i$; a map $h$ over $I$ restricts to fibres because $p'(h(a))=p(a)$. Let $\Psi(B)=(\coprod_i B_i,\ \text{first projection})$, sending $(\beta_i)$ to $(i,b)\mapsto(i,\beta_i(b))$. Then $\Phi\Psi(B)_i\cong B_i$ naturally, and $\Psi\Phi(A,p)=\coprod_i p^{-1}(i)\cong A$ over $I$ via $a\mapsto(p(a),a)$, naturally. $\square$

It is an equivalence, not an isomorphism, since sets of pairs are not the original sets. Given $f : I\to J$, composition with $f$, $(A,p)\mapsto(A,f\circ p)$, is a functor $\mathbf{Set}/I\to\mathbf{Set}/J$; Section 3 shows it is the left Kan extension along $f$.

*Why this matters for an agentic coder.* A tensor of shape $[2]\times[2]$ is a function from a coordinate set, and two coordinate sets of equal size are still different objects unless a bijection is supplied. Explicit maps prevent silent reindexing errors.

**Where this is used in the course.** Chapter 2 ([Categories of indices and values](02-index-categories.md#1-shapes-are-objects-of-finset)) takes $\mathbf{FinSet}$ as the category of coordinate sets and a family of values over $I$ as a functor out of the discrete category $I$. Every later chapter uses $\mathbf{Set}$ and $\mathbf{Pfn}$ as defined here.

## 2. Adjunctions

We give two equivalent definitions of adjunction.

**Definition 0.3 (adjunction).** Let $L:\mathcal{C}\to\mathcal{D}$ and $R:\mathcal{D}\to\mathcal{C}$ be functors. We say $L$ is *left adjoint* to $R$, written $L\dashv R$, when there is a bijection

$$\mathcal{D}(LA,B)\;\cong\;\mathcal{C}(A,RB)$$

natural in $A\in\mathcal{C}$ and $B\in\mathcal{D}$. Equivalently, there are natural transformations $\eta:\mathrm{id}_{\mathcal{C}}\Rightarrow RL$ (the *unit*) and $\varepsilon:LR\Rightarrow\mathrm{id}_{\mathcal{D}}$ (the *counit*) satisfying the *triangle identities*

$$\varepsilon_{LA}\circ L(\eta_A)=\mathrm{id}_{LA},\qquad R(\varepsilon_B)\circ\eta_{RB}=\mathrm{id}_{RB}.$$

**Proposition 0.4 (the two definitions agree).** Given the bijection, let $\eta_A$ be the image of $\mathrm{id}_{LA}$ and $\varepsilon_B$ the preimage of $\mathrm{id}_{RB}$. Conversely, given $\eta,\varepsilon$, send $\varphi : LA\to B$ to $R(\varphi)\circ\eta_A$ and $\psi : A\to RB$ to $\varepsilon_B\circ L(\psi)$. These are mutually inverse exactly when the triangle identities hold.

*Sketch.* Naturality in $A$ shows the image of $\varphi$ is $R(\varphi)\circ\eta_A$; taking $\varphi=\varepsilon_B$ gives the second triangle identity, and dually the first. For the converse, $\varepsilon_B\circ L(R(\varphi)\circ\eta_A)=\varepsilon_B\circ LR(\varphi)\circ L(\eta_A)=\varphi\circ\varepsilon_{LA}\circ L(\eta_A)=\varphi$, using naturality of $\varepsilon$ and the first triangle identity; the other composite uses naturality of $\eta$ and the second. $\square$

The unit maps every $A$ into the $R$ of its $L$; the counit evaluates an $L$ of an $R$ back down; the triangle identities say doing one then the other does nothing.

**Example 0.5 (free monoid).** Let $\mathbf{Mon}$ be monoids and monoid homomorphisms, and $U:\mathbf{Mon}\to\mathbf{Set}$ the forgetful functor. Let $\mathrm{List}(X)$ be the set of finite lists $[x_1,\dots,x_n]$ of elements of $X$, a monoid under concatenation with unit the empty list. On a function $g$, $\mathrm{List}(g)$ applies $g$ to each entry. Then $\mathrm{List}\dashv U$.

*Proof.* Unit: $\eta_X : X\to U\,\mathrm{List}(X)$, $x\mapsto[x]$. Counit: $\varepsilon_M:\mathrm{List}(UM)\to M$, $[m_1,\dots,m_n]\mapsto m_1\cdots m_n$ (multiply, with the empty list going to the unit). The counit is a monoid homomorphism because multiplying a concatenation of lists is the product of the two products. Triangle identities: the first sends $[x_1,\dots,x_n]$ to $[[x_1],\dots,[x_n]]$ and then concatenates, which gives back $[x_1,\dots,x_n]$. The second sends $m\in M$ to $[m]$ and then multiplies, giving $m$. So a monoid homomorphism out of $\mathrm{List}(X)$ is determined by its values on one-element lists, and any $h:X\to UM$ extends by $[x_1,\dots,x_n]\mapsto h(x_1)\cdots h(x_n)$. $\square$

**Proposition 0.6 (the Naperian adjunction).** For any set $I$, the functor $(-)\times I:\mathbf{Set}\to\mathbf{Set}$ is left adjoint to $(-)^I:\mathbf{Set}\to\mathbf{Set}$, where $B^I$ is the set of functions $I\to B$ and, for $k:B\to B'$, $k^I(v)=k\circ v$. The unit $\eta_A : A\to(A\times I)^I$ is *tabulation*, $\eta_A(a)=(i\mapsto(a,i))$. The counit $\varepsilon_B : B^I\times I\to B$ is *evaluation (lookup)*, $\varepsilon_B(v,i)=v(i)$. The same holds in $\mathbf{FinSet}$ for finite $I$.

*Proof.* Bijection: send $\varphi : A\times I\to B$ to its transpose $\hat\varphi:A\to B^I$, $\hat\varphi(a)(i)=\varphi(a,i)$. The inverse sends $\psi:A\to B^I$ to $(a,i)\mapsto\psi(a)(i)$. These are inverse. Naturality: for $h:A'\to A$ and $k:B\to B'$, the transpose of $k\circ\varphi\circ(h\times\mathrm{id}_I)$ sends $a'$ to $i\mapsto k(\varphi(h(a'),i))=k^I(\hat\varphi(h(a')))(i)$. Unit and counit: $\eta_A$ is the transpose of $\mathrm{id}_{A\times I}$ and $\varepsilon_B$ is the preimage of $\mathrm{id}_{B^I}$, matching the formulas. Triangle identities, checked directly on elements:

- $\varepsilon_{A\times I}\circ(\eta_A\times\mathrm{id}_I)$ sends $(a,i)$ to $(\eta_A(a),i)=((i'\mapsto(a,i')),i)$ and then evaluates at $i$, giving $(a,i)$.
- $(\varepsilon_B)^I\circ\eta_{B^I}$ sends $v\in B^I$ to the family $i\mapsto(v,i)$ and then applies $\varepsilon_B$ pointwise, giving $i\mapsto v(i)$, which is $v$. $\square$

**Consequence of Proposition 0.6 (currying).** $K^{I\times J}\cong(K^J)^I$: for every set $X$, $\mathbf{Set}(X,(K^J)^I)\cong\mathbf{Set}(X\times I,K^J)\cong\mathbf{Set}(X\times I\times J,K)\cong\mathbf{Set}(X,K^{I\times J})$ naturally in $X$, so Yoneda gives the isomorphism.

Functions out of a finite coordinate set behave like tensors, and tabulating and looking up are mutually inverse in the sense of the triangle identities. Note that $(A\times B)^I\cong A^I\times B^I$ is a *cartesian* product, not a vector-space tensor product: for $I=[3]$ and $A=B=\mathbb{R}$ it has dimension $6$, not $9$.

**Example 0.7 (an inclusion as a right adjoint).** View $\mathbb{R}$ and $\mathbb{Z}$ as posets, hence categories with one morphism $x\to y$ when $x\le y$. Let $\iota:\mathbb{Z}\hookrightarrow\mathbb{R}$ be the inclusion of the integers and $\lceil\cdot\rceil:\mathbb{R}\to\mathbb{Z}$ the ceiling. For $x\in\mathbb{R}$ and $n\in\mathbb{Z}$,

$$\lceil x\rceil\le n\iff x\le\iota(n).$$

Hom-sets have at most one element, so this natural bijection is a logical equivalence, and $\lceil\cdot\rceil\dashv\iota$. The unit is $x\le\lceil x\rceil$, the counit is $\lceil\iota(n)\rceil=n$, and the triangle identities are automatic in a poset. Dually $\iota\dashv\lfloor\cdot\rfloor$. So here the inclusion $\mathbb{Z}\subseteq\mathbb{R}$ is right adjoint to "round up to the nearest integer". The same works for any subset in which every $x$ has a least member above it.

**Theorem 0.8 (adjoints and limits).** Right adjoints preserve limits; left adjoints preserve colimits.

*Proof (colimits).* Let $L\dashv R$ and let $D$ be a diagram in $\mathcal{C}$ with colimit $\mathrm{colim}\,D$. For any $B$,
$$\mathcal{D}(L\,\mathrm{colim}\,D,B)\cong\mathcal{C}(\mathrm{colim}\,D,RB)\cong\lim_k\mathcal{C}(D_k,RB)\cong\lim_k\mathcal{D}(LD_k,B),$$
naturally in $B$. The right side says $L\,\mathrm{colim}\,D$ has the universal property of the colimit of $L\circ D$. Limits are dual. $\square$

Instances: $(-)\times I$ preserves coproducts, $(A+B)\times I\cong A\times I+B\times I$; $(-)^I$ preserves products, $(A\times B)^I\cong A^I\times B^I$, but not coproducts (Exercise 1); in Example 0.7, $\lceil\max(x,y)\rceil=\max(\lceil x\rceil,\lceil y\rceil)$ (joins are colimits in a poset).

*Why this matters for an agentic coder.* An adjunction is a specification with a built-in test suite: the unit, the counit and the triangle identities are laws that any implementation of "tabulate" and "lookup" must satisfy.

**Where this is used in the course.** Chapter 2 ([Arrays are functions: the Naperian adjunction](02-index-categories.md#arrays-are-functions-the-naperian-adjunction)) states Proposition 0.6 as "the Naperian adjunction": tabulation and lookup are the two constructors of the core language. The triple $\Sigma_f\dashv f^\ast\dashv\Pi_f$ of Chapter 2 is built from Section 3 below.

## 3. Kan extensions

Restricting a family along a map of index sets is easy. Kan extensions are the best ways to go back.

**Definition 0.9 (Kan extension).** Let $f:\mathcal{C}\to\mathcal{D}$ and $F:\mathcal{C}\to\mathcal{E}$ be functors. A *left Kan extension* of $F$ along $f$ is a functor $\mathrm{Lan}_fF:\mathcal{D}\to\mathcal{E}$ together with a natural transformation $\eta:F\Rightarrow(\mathrm{Lan}_fF)\circ f$, such that for every functor $G:\mathcal{D}\to\mathcal{E}$ and natural transformation $\alpha:F\Rightarrow G\circ f$ there is a unique natural transformation $\bar\alpha:\mathrm{Lan}_fF\Rightarrow G$ with $(\bar\alpha f)\circ\eta=\alpha$. Dually, a *right Kan extension* is $\mathrm{Ran}_fF:\mathcal{D}\to\mathcal{E}$ with $\varepsilon:(\mathrm{Ran}_fF)\circ f\Rightarrow F$, universal among $\beta:G\circ f\Rightarrow F$, which factor uniquely as $\varepsilon\circ(\bar\beta f)$.

With $f^\ast G=G\circ f$ (precomposition), when the Kan extensions exist for all $F$ the definition says
$$\mathrm{Lan}_f\dashv f^\ast\dashv\mathrm{Ran}_f,\qquad\text{i.e.}\quad \mathrm{Nat}(\mathrm{Lan}_fF,G)\cong\mathrm{Nat}(F,f^\ast G),\quad\mathrm{Nat}(f^\ast G,F)\cong\mathrm{Nat}(G,\mathrm{Ran}_fF).$$
So Kan extensions are adjoints to restriction.

**Proposition 0.10 (pointwise formula).** If $\mathcal{C}$ is small and $\mathcal{E}$ is cocomplete (resp. complete), as $\mathbf{Set}$ is, then
$$(\mathrm{Lan}_fF)(d)=\mathrm{colim}\Big((f\downarrow d)\xrightarrow{\ \pi\ }\mathcal{C}\xrightarrow{F}\mathcal{E}\Big),\qquad(\mathrm{Ran}_fF)(d)=\lim\Big((d\downarrow f)\xrightarrow{\ \pi\ }\mathcal{C}\xrightarrow{F}\mathcal{E}\Big).$$
The *comma category* $(f\downarrow d)$ has objects $(c,\ u:f(c)\to d)$ and morphisms $(c,u)\to(c',u')$ the maps $k:c\to c'$ with $u'\circ f(k)=u$; $(d\downarrow f)$ has objects $(c,\ u:d\to f(c))$, dually; $\pi$ forgets $u$. This is standard (Mac Lane, Chapter X).

**Proposition 0.11 (the discrete case).** Let $f:I\to J$ be a function between finite sets, regarded as a functor between discrete categories, and let $A\in\mathbf{Set}^I$. Then $\mathrm{Lan}_fA$ and $\mathrm{Ran}_fA$ exist and
$$(\mathrm{Lan}_fA)(j)=\coprod_{i\in f^{-1}(j)}A_i,\qquad(\mathrm{Ran}_fA)(j)=\prod_{i\in f^{-1}(j)}A_i.$$

*Proof via the pointwise formula.* An object of $(f\downarrow j)$ is a pair $(i,u)$ with $u:f(i)\to j$ in the discrete category $J$, so $u$ exists iff $f(i)=j$ and is then the identity: the objects are the fibre $f^{-1}(j)$. A morphism between them is a morphism of the discrete category $I$, hence an identity. So $(f\downarrow j)$ is the discrete category on $f^{-1}(j)$, and a colimit over it is the coproduct. The same holds for $(j\downarrow f)$ and a limit, which is the product.

*Direct proof of the universal property.* Define $\Sigma_fA$ by the coproduct formula and let $\eta_i:A_i\to(\Sigma_fA)_{f(i)}$ be the coproduct injection. Let $G\in\mathbf{Set}^J$ and let $\alpha:A\Rightarrow f^\ast G$, which by Definition 0.1 is just a family of functions $\alpha_i:A_i\to G_{f(i)}$. A natural transformation $\bar\alpha:\Sigma_fA\Rightarrow G$ is a family of functions $\bar\alpha_j:\coprod_{i\in f^{-1}(j)}A_i\to G_j$, and the condition $\bar\alpha_{f(i)}\circ\eta_i=\alpha_i$ says that the restriction of $\bar\alpha_j$ to the summand $A_i$ is $\alpha_i$. By the universal property of the coproduct there is exactly one such $\bar\alpha_j$ for each $j$, namely the copairing. For $\Pi_f$, define $\varepsilon_i:(\Pi_fA)_{f(i)}\to A_i$ as the projection. Given $\beta:f^\ast G\Rightarrow A$, i.e. functions $\beta_i:G_{f(i)}\to A_i$, the unique $\bar\beta_j:G_j\to\prod_{i\in f^{-1}(j)}A_i$ with $\varepsilon_i\circ\bar\beta_{f(i)}=\beta_i$ is the pairing. $\square$

**Notes.** (1) If the fibre is empty, $(\Sigma_fA)(j)=0=\varnothing$ and $(\Pi_fA)(j)=1$. This is the set-level origin of "an empty sum is zero". (2) Under Proposition 0.2, $\Sigma_f$ is composition with $f$ on $\mathbf{Set}/I$ and $f^\ast$ is pullback (Section 6). (3) Chapter 2 calls these functors $\Sigma_f=\mathrm{Lan}_f$ and $\Pi_f=\mathrm{Ran}_f$; the triple $\Sigma_f\dashv f^\ast\dashv\Pi_f$ is the displayed adjoint triple above for discrete categories.

**Example 0.12.** Take $f:[2]\times[2]\to[2]$, $(j,i)\mapsto j$, forgetting the contracted index $i$ of statement s1 of `Scorer` (defined in Chapter 1, Section 4), and $A(j,i)=\{\ast\}$. The fibre over each $j$ has two elements, so $(\Sigma_fA)(j)$ has two elements and $(\Pi_fA)(j)$ has one. For $J=1$ and $f$ the unique map $!:I\to1$, $\Sigma_!A$ is the disjoint union of the whole family and $\Pi_!A$ its cartesian product: sums and products of sets are Kan extensions to the point.

*Why this matters for an agentic coder.* Counting the elements of $\Sigma_fA$ gives the sum over a fibre. The adjoint triple is a theorem for $\mathbf{Set}$-valued families; the $K$-valued pushforward is its decategorified shadow, an analogy and not an adjunction between $K^I$ and $K^J$. Its laws (functoriality, relabeling, grouping) are proved directly from the commutative-monoid laws in [Chapter 2](02-index-categories.md#3-decategorification-k-valued-families), Propositions 2.7 and 2.8, and an implementation should test them as such.

**Where this is used in the course.** Chapter 2 ([Set-valued families and the adjoint triple](02-index-categories.md#2-set-valued-families-and-the-adjoint-triple)) names these functors $\Sigma_f$ and $\Pi_f$, builds the adjoint triple, and then replaces cardinalities by values in $K$ to obtain the pushforward $f_!$ ([Decategorification](02-index-categories.md#3-decategorification-k-valued-families)). In Chapter 4 collection is a pushforward along the destination map.

## 4. Monads and Kleisli categories

**Definition 0.13 (monad).** A *monad* on a category $\mathcal{C}$ is an endofunctor $T$ with natural transformations $\eta:\mathrm{id}\Rightarrow T$ (*unit*) and $\mu:T^2\Rightarrow T$ (*multiplication*, "flatten") satisfying
$$\mu\circ T\eta=\mathrm{id}_T=\mu\circ\eta T,\qquad\mu\circ T\mu=\mu\circ\mu T.$$
Wrapping then flattening does nothing, and flattening three layers is independent of order.

**Example 0.14 (the Option monad on $\mathbf{Set}$).** Let $\mathrm{Option}(A)=A\sqcup\{\bot\}$. Write $\downarrow a$ (*some*) for $a\in A$ and $\bot$ (*none*, read "undefined") for the added point. On functions, $\mathrm{Option}(g)(\downarrow a)=\downarrow g(a)$ and $\mathrm{Option}(g)(\bot)=\bot$.

- Unit: $\eta_A(a)=\downarrow a$.
- Multiplication (*join*): $\mu_A:\mathrm{Option}(\mathrm{Option}A)\to\mathrm{Option}A$ sends $\downarrow\downarrow a\mapsto\downarrow a$, $\ \downarrow\bot\mapsto\bot$, $\ \bot\mapsto\bot$.

*Laws.* Both $\mu\circ\mathrm{Option}(\eta)$ and $\mu\circ\eta_{\mathrm{Option}}$ send $\downarrow a\mapsto\downarrow a$ and $\bot\mapsto\bot$. The elements of $\mathrm{Option}^3A$ are $\bot$, $\downarrow\bot$, $\downarrow\downarrow\bot$ and $\downarrow\downarrow\downarrow a$; both ways of flattening give $\bot$ on the first three and $\downarrow a$ on the last. $\square$

Note that $\bot$ is one extra point with no order and no arithmetic: it is not zero.

**Definition 0.15 (Kleisli category).** For a monad $(T,\eta,\mu)$ on $\mathcal{C}$, the *Kleisli category* $\mathrm{Kl}(T)$ has the same objects as $\mathcal{C}$, and a morphism $A\to B$ in $\mathrm{Kl}(T)$ is a morphism $A\to TB$ in $\mathcal{C}$. The identity on $A$ is $\eta_A$. The composite of $f:A\to TB$ and $g:B\to TC$ is
$$g\star f=\mu_C\circ T(g)\circ f:A\to TC.$$
Associativity and the unit laws follow from the monad laws (the unit laws are the first two laws, associativity is the third together with naturality of $\mu$).

Define *bind*: for $x\in TB$ and $k:B\to TC$, $\;x\mathbin{\texttt{>>=}}k:=\mu_C(T(k)(x))$. Then $(g\star f)(a)=f(a)\mathbin{\texttt{>>=}}g$: "run $f$, feed its result, if any, to $g$". Lean's *do-notation* is syntax for this composition (we use the term only informally; Chapter 6 gives the dictionary).

**Proposition 0.16.** $\mathrm{Kl}(\mathrm{Option})\cong\mathbf{Pfn}$, an isomorphism of categories that is the identity on objects.

*Proof.* A morphism $A\to B$ in $\mathrm{Kl}(\mathrm{Option})$ is a function $f:A\to B\sqcup\{\bot\}$. Send it to the partial function with $\mathrm{dom}=\{a\mid f(a)\ne\bot\}$ and value $b$ when $f(a)=\downarrow b$. Conversely $p$ gives $f(a)=\downarrow p(a)$ on $\mathrm{dom}(p)$ and $\bot$ elsewhere; these are inverse bijections. Identities correspond ($\eta_A(a)=\downarrow a$). For composition, $\mu(\mathrm{Option}(g)(f(a)))$ is $\bot$ if $f(a)=\bot$, and $g(b)$ if $f(a)=\downarrow b$. So $(g\star f)(a)$ is defined iff $f(a)$ is defined and $g$ is defined at its value, with value $g(f(a))$: composition of partial functions. $\square$

Option is *strict*: $\bot\mathbin{\texttt{>>=}}k=\bot$ and $\downarrow a\mathbin{\texttt{>>=}}k=k(a)$, so undefined input always gives undefined output.

**Strength and distributive laws.** To combine undefinedness with products we need a *strength* $t_{A,B}:A\times TB\to T(A\times B)$, natural and compatible with $\eta,\mu$. For Option, $t(a,\downarrow b)=\downarrow(a,b)$ and $t(a,\bot)=\bot$. Composing the strength with its mirror (strengthening on the left, then on the right, or the other way round) gives the *strict pairing* $\mathrm{pair}:\mathrm{Option}A\times\mathrm{Option}B\to\mathrm{Option}(A\times B)$,
$$\mathrm{pair}(x,y)=\begin{cases}\downarrow(a,b)&\text{if }x=\downarrow a\text{ and }y=\downarrow b,\\\bot&\text{otherwise,}\end{cases}$$
defined exactly when both components are. That the two orders agree is the statement that Option is *commutative*.

**Definition 0.17 (distributive law of a functor over a monad).** Let $F$ be an endofunctor and $T$ a monad on $\mathcal{C}$. A *distributive law* of $F$ over $T$ is a natural transformation $\lambda:FT\Rightarrow TF$ with
$$\lambda\circ F\eta=\eta F,\qquad\lambda\circ F\mu=\mu F\circ T\lambda\circ\lambda T.$$
Such a $\lambda$ extends $F$ to a functor $\tilde F$ on $\mathrm{Kl}(T)$: $\tilde F$ is $F$ on objects, and sends a Kleisli morphism $f:A\to TB$ to $\lambda_B\circ F(f):FA\to TFB$.

**Proposition 0.18 (sequence).** For a set $I$, let $F=(-)^I$ and $T=\mathrm{Option}$. The map
$$\mathrm{sequence}_A:(\mathrm{Option}A)^I\to\mathrm{Option}(A^I),\qquad v\mapsto\begin{cases}\downarrow(i\mapsto a_i)&\text{if }v(i)=\downarrow a_i\text{ for all }i\in I,\\\bot&\text{if }v(i)=\bot\text{ for some }i,\end{cases}$$
is a distributive law of $(-)^I$ over Option.

*Proof.* Naturality is immediate. Unit law: $\mathrm{sequence}(i\mapsto\downarrow w(i))=\downarrow w$. Multiplication law: let $w\in(\mathrm{Option}^2A)^I$. The left side ($\mathrm{sequence}$ after pointwise $\mu$) is defined iff every $w(i)=\downarrow\downarrow a_i$. The right side applies $\mathrm{sequence}_{\mathrm{Option}A}$ (defined iff every $w(i)=\downarrow x_i$), then $\mathrm{sequence}_A$ to $(x_i)$ (defined iff every $x_i=\downarrow a_i$), then flattens; a $w(i)=\downarrow\bot$ gives $\bot$. They agree. $\square$

Via Proposition 0.16, $\tilde F$ lifts a partial function $p:A\rightharpoonup B$ to the *batched* map $p^I:A^I\rightharpoonup B^I$, defined at $v$ iff $p$ is defined at every $v(i)$. Note $\mathrm{sequence}$ is not invertible: it forgets which component was undefined.

**Example 0.19.** Let $\log:\mathbb{R}\rightharpoonup\mathbb{R}$ be the partial function defined on $(0,\infty)$. In `Scorer` on $\eta_1$ (the program and both inputs $\eta_1$, $\eta_0$ are defined in Chapter 1, Section 4) we have $Y=(0,4)$. Batching $\log$ over both components is undefined because $\log 0$ is, even though component $1$ is fine. Statement s4 reads only $Y[1]=4$, so $\log Y[1]=\log 4$ is defined. "Apply to the whole vector" versus "apply to the coordinate that is read" is strict sequencing versus a read footprint (Chapter 3).

*Why this matters for an agentic coder.* A function that returns `none` early is a Kleisli arrow. Chaining them with do-notation is Kleisli composition. Replacing strict `sequence` by "skip the bad entries" is a different semantics.

**Where this is used in the course.** Chapter 3 ([Partial computations](03-partiality.md)) takes $\mathbf{Pfn}=\mathrm{Kl}(\mathrm{Option})$ as the category of body interpretations, builds strict pairing from the strength above, uses $\mathrm{sequence}$ to batch a partial function over an index set, and shows batching is only lax natural in the index set.

## 5. Algebras and coalgebras

This section follows [Appendix A](../semantics/categorical_operational_semantics.md) of the operational-semantics note: an algebra combines structured inputs, a coalgebra unfolds a state. We avoid the letter $\Sigma$, reserved for tensor signatures.

**Definition 0.20 ($F$-algebra).** Let $F:\mathcal{C}\to\mathcal{C}$ be an endofunctor. An *$F$-algebra* is a pair $(A,\alpha)$, where $A$ is an object (the *carrier*) and $\alpha:FA\to A$ a morphism (the *structure map*). A *morphism* $h:(A,\alpha)\to(B,\beta)$ is a morphism $h:A\to B$ with $h\circ\alpha=\beta\circ F(h)$. An *initial algebra* is an initial object among algebras.

**Proposition 0.21.** For $F(X)=1+X$ on $\mathbf{Set}$ (with $F(g)$ the identity on the left summand and $g$ on the right), the algebra $(\mathbb{N},[0,\mathrm{succ}])$ is initial.

*Sketch.* An algebra $\beta:1+B\to B$ amounts to an element $b_0\in B$ (the image of the left summand) and a function $s:B\to B$. The morphism condition for $h:\mathbb{N}\to B$ reads $h(0)=b_0$ and $h(n+1)=s(h(n))$ on the two summands. These equations define $h$ by induction, and any morphism satisfies them. $\square$

The unique morphism out of an initial algebra is a definition by structural recursion; for $1+X$ it is recursion on $\mathbb{N}$.

**Definition 0.22 ($F$-coalgebra).** An *$F$-coalgebra* is a pair $(X,\gamma)$ with $\gamma:X\to FX$. A morphism $h:(X,\gamma)\to(Y,\delta)$ is a morphism $h:X\to Y$ with $\delta\circ h=F(h)\circ\gamma$.

**Example 0.23 (transition systems).** Let $\mathcal{P}_{\mathrm{fin}}(X)$ be the set of finite subsets of $X$, with $\mathcal{P}_{\mathrm{fin}}(g)(S)=g[S]$ the image. A coalgebra $\gamma:X\to\mathcal{P}_{\mathrm{fin}}(X)$ is a *finitely branching transition system*: write $x\to y$ when $y\in\gamma(x)$. Every state has finitely many successors, possibly none. A morphism $h$ satisfies $h[\gamma(x)]=\delta(h(x))$, which says two things: transitions are preserved ($x\to y$ implies $h(x)\to h(y)$), and every transition out of $h(x)$ lifts to one out of $x$.

In Chapter 5 the states are *configurations* $(\sigma,\alpha,U)$ of the reference machine and $\gamma$ sends one to its finitely many one-step successors; a terminal state has $\gamma(x)=\varnothing$.

**Definition 0.24 (subcoalgebra, invariant).** A subset $S\subseteq X$ is an *invariant* (or *subcoalgebra*) of $(X,\gamma)$ if it is closed under transition: $x\in S$ and $x\to y$ imply $y\in S$.

An invariant carries a unique coalgebra structure making $S\hookrightarrow X$ a coalgebra morphism: the restriction of $\gamma$, which lands in $S$ exactly by closure. Unions and intersections of invariants are invariants.

**Definition 0.25 (well-founded coalgebra).** A transition system is *well-founded* if it has no infinite path $x_0\to x_1\to x_2\to\cdots$.

**Proposition 0.26 (measures).** (a) If there is a function $\mu:X\to\mathbb{N}$ with $x\to y\Rightarrow\mu(y)<\mu(x)$, then the system is well-founded. (b) Conversely, a finitely branching well-founded system admits such a $\mu$.

*Proof.* (a) An infinite path would give an infinite strictly decreasing sequence $\mu(x_0)>\mu(x_1)>\cdots$ in $\mathbb{N}$, which cannot exist. (b) For a state $x$, the tree of paths starting at $x$ is finitely branching and has no infinite branch, so by König's lemma it is finite. Let $\mu(x)$ be the length of its longest path. A successor $y$ of $x$ starts a strictly shorter longest path. $\square$

A measure is a transition-preserving map into $(\mathbb{N},>)$ (where $n\to m$ iff $m<n$) that need not reflect transitions. Example: the reference machine's $\mu(\sigma,\alpha,U)=\lvert U\rvert+\lvert\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma\rvert$ drops by $1$ at each CONTRIBUTE step (one fewer pending occurrence) and each PUBLISH step (one more published address). Configurations and the rules CONTRIBUTE and PUBLISH are defined in [Chapter 5, Section 3](05-operational.md#3-the-three-rules-and-the-machine-as-a-coalgebra); here only the arithmetic of $\mu$ matters. For `Scorer` on $\eta_1$ it starts at $7+5=12$, and a maximal run has $7$ CONTRIBUTE and $5$ PUBLISH steps, ending at $0$. The terminal UNDEFINED step, which leads to a failure configuration with no $\mu$, is handled in Chapter 5.

**Final coalgebras (idea only).** A *final coalgebra* is a coalgebra $Z$ with exactly one morphism into it from every coalgebra. It is dual to the initial algebra. For a transition system it assigns each state its complete unfolded behaviour, so two states have the same image iff they are bisimilar (behaviourally indistinguishable); for $X\mapsto A\times X$ it is the set of infinite streams over $A$. We use it only by name.

*Why this matters for an agentic coder.* A step function from configurations to their enabled successors is a coalgebra; "never fails" is an invariant and "terminates" is a measure.

**Where this is used in the course.** Chapter 5 ([Operational semantics](05-operational.md)) presents the reference machine as a $\mathcal{P}_{\mathrm{fin}}$-coalgebra on configurations, proves safety properties as invariants, and uses the measure $\mu$ and the rank certificate for progress.

## 6. Spans and pullbacks

**Definition 0.27 (pullback).** Given $f:A\to C$ and $g:B\to C$, a *pullback* is an object $A\times_CB$ with maps $\pi_A,\pi_B$ satisfying $f\pi_A=g\pi_B$, universal among such: for every $p:P\to A$, $q:P\to B$ with $fp=gq$ there is a unique $u:P\to A\times_CB$ with $\pi_Au=p$ and $\pi_Bu=q$.

**Proposition 0.28.** In $\mathbf{Set}$, $A\times_CB=\{(a,b)\mid f(a)=g(b)\}$ with the two coordinate projections.

*Proof.* Given $p,q$ with $fp=gq$, the map $u(x)=(p(x),q(x))$ lands in the subset and is the only one compatible with the projections. $\square$

For $C=1$ the pullback is the product. For $g:1\to C$ picking an element $c$, the pullback $A\times_C1$ is the fibre $f^{-1}(c)$. In `Scorer` (with $\mathrm{dst}$, $\mathcal{O}_P$ and $\mathrm{Addr}_{\mathrm{Def}}$ as in Chapter 1, Section 3), for the destination map $\mathrm{dst}:\mathcal{O}_P\to\mathrm{Addr}_{\mathrm{Def}}$ and the address $(Z,0)$, the pullback along $(Z,0):1\to\mathrm{Addr}_{\mathrm{Def}}$ is the fibre $\{(s1,j{=}0),(s2,j{=}0)\}$, the two writers of $Z[0]$.

**Definition 0.29 (span).** A *span* from $A$ to $B$ is a diagram $A\xleftarrow{\ l\ }M\xrightarrow{\ r\ }B$; $M$ is the *apex*. Two spans with the same endpoints are *isomorphic* if there is a bijection of apexes commuting with both legs. Spans compose by pullback: $A\xleftarrow{\ l\ }M\xrightarrow{\ r\ }B$ followed by $B\xleftarrow{\ l'\ }N\xrightarrow{\ r'\ }C$ is
$$A\xleftarrow{\ l\circ\pi_M\ }M\times_BN\xrightarrow{\ r'\circ\pi_N\ }C,\qquad M\times_BN=\{(m,n)\mid r(m)=l'(n)\}.$$
The identity span on $A$ is $A\xleftarrow{\mathrm{id}}A\xrightarrow{\mathrm{id}}A$.

A pullback is unique only up to unique isomorphism, so composition is defined only up to span isomorphism. Sets with isomorphism classes of spans form a category, $\mathbf{Span}(\mathbf{Set})$ (locally large, which is harmless here), and $\mathbf{Span}(\mathbf{FinSet})$ for finite sets. The proof (identities and associativity up to isomorphism, by pasting pullbacks) is given in [Chapter 2, Section 4](02-index-categories.md#4-contraction-patterns-are-spans).

A span is a relation with multiplicities: the apex records *how* each $a$ is related to each $b$. A function $f$ is the span $A\xleftarrow{\mathrm{id}}A\xrightarrow{f}B$.

**Proposition 0.30 (partial functions as spans).** A partial function $p:A\rightharpoonup B$ corresponds to the span $A\xleftarrow{\ \subseteq\ }\mathrm{dom}(p)\xrightarrow{\ p\ }B$, whose left leg is injective (*monic*, i.e. injective in $\mathbf{Set}$). Isomorphism classes of spans with monic left leg correspond bijectively to partial functions, and span composition restricts to composition of partial functions.

*Proof.* Two such spans are isomorphic iff they have the same domain and agree on it, since an apex bijection must commute with the injective left leg. For composition, with $p:A\rightharpoonup B$ and $q:B\rightharpoonup C$, the pullback is $\{(a,b)\mid a\in\mathrm{dom}(p),\ p(a)=b,\ b\in\mathrm{dom}(q)\}\cong\{a\in\mathrm{dom}(p)\mid p(a)\in\mathrm{dom}(q)\}$, with left leg the inclusion into $A$ and right leg $q\circ p$. This is the span of $q\circ p$. $\square$

So partial functions are the spans whose apex has at most one point over each $a\in A$, which is exactly a monic left leg. A non-monic left leg means several (possibly equal-valued) ways to proceed from some $a$, a non-deterministic computation.

*Why this matters for an agentic coder.* A contraction pattern is a span of coordinate sets, and composing two contractions is a pullback. "Function, partial function, relation" is a statement about which leg is monic.

**Where this is used in the course.** Chapter 2 ([Contraction patterns are spans](02-index-categories.md#4-contraction-patterns-are-spans)) uses $\mathbf{Span}(\mathbf{FinSet})$ for pure einsum and proves that composition linearizes to matrix product. Chapter 4 ([Denotational semantics](04-denotational.md)) defines the denotation of a program as the witness span $\mathrm{Env}(\mathrm{In})\leftarrow W_P\to\mathrm{Env}(\mathrm{Out})$ and recovers partial functions as the monic-left-leg case.

## 7. Equalizers and fixed points

**Definition 0.31 (equalizer).** For parallel morphisms $f,g:A\rightrightarrows B$, an *equalizer* is a morphism $e:E\to A$ with $fe=ge$, universal among such: every $m:P\to A$ with $fm=gm$ factors uniquely as $m=e\circ\bar m$.

**Proposition 0.32.** In $\mathbf{Set}$ the equalizer is the inclusion of $E=\{a\in A\mid f(a)=g(a)\}$.

*Proof.* A map $m$ satisfies $fm=gm$ iff its image lies in $E$, and then factors uniquely through the injective inclusion. $\square$

**Fixed points.** For an endomap $\varphi:A\to A$, its set of *fixed points* is the equalizer of the parallel pair $(\varphi,\mathrm{id}_A)$:
$$\mathrm{Fix}(\varphi)=\{a\in A\mid\varphi(a)=a\}.$$

This construction takes *all* fixed points. There is no order on $A$, no notion of "least" or "first", and no iteration from a starting point. The set $\mathrm{Fix}(\varphi)$ may be empty, a point, or large. On $\mathbb{R}$: $x\mapsto x+1$ has none, $x\mapsto x^2$ has two ($0$ and $1$), and $\mathrm{id}$ has all of $\mathbb{R}$. Least-fixed-point theorems (Kleene, Tarski) need an order and monotonicity; contraction theorems need a metric. Neither is available here: $\bot$ carries no order and is not zero, so **there is no least fixed point**, and a program denotes a value only when its set of models has exactly one element. An equation operator that acts like $\mathrm{id}$ on some coordinate gives many models and no denotation; one like $x\mapsto x+1$ gives none.

The equation operator $\Phi_P$ of Chapter 4 is a map $\mathrm{AdmEnv}(P)\to\mathrm{Env}_\Sigma$, not an endomap, so its fixed points are the equalizer of $\Phi_P$ and the inclusion $\mathrm{AdmEnv}(P)\hookrightarrow\mathrm{Env}_\Sigma$, cut down to the environments extending a given input.

*Why this matters for an agentic coder.* Iterating "recompute until nothing changes" silently picks one fixed point from one start. An implementation must fail loudly when there is not exactly one.

**Where this is used in the course.** Chapter 4 ([Denotational semantics](04-denotational.md)) defines $\mathrm{Models}(P,\eta)$ as an equalizer of this kind and the denotation as defined only on inputs with exactly one model. Chapter 5 shows that a successful run produces the unique model.

## Exercises

1. Using Theorem 0.8, show that $(-)\times I$ preserves coproducts in $\mathbf{Set}$, i.e. $(A+B)\times I\cong A\times I+B\times I$. Show by counting, with $I=[2]$ and $A=B=1$, that $(-)^I$ does not preserve coproducts.

2. For $f:[2]\times[2]\to[2]$, $(j,i)\mapsto j$ and $A(j,i)=[\,j+i+1\,]$, compute the cardinalities of $(\Sigma_fA)(j)$ and $(\Pi_fA)(j)$ for $j=0,1$. 

3. Check the unit law of Definition 0.17 for $\mathrm{sequence}$, and compute $\mathrm{sequence}$ on the vectors $(\downarrow 1,\bot)$ and $(\downarrow 1,\downarrow 2)$. Explain, using Example 0.19 and the two inputs $\eta_1$ (where $Y=(0,4)$) and $\eta_0$ (where $Y=(1,0)$) of `Scorer` (Chapter 1, Section 4; its statement s4 is `L[] = log(Y[1])`), at which of the two inputs batching $\log$ over all of $Y$ and statement s4 are each undefined.

4. Let $X=\{0,1,2,3\}$ with $0\to1$, $0\to2$, $1\to3$, $2\to3$. (a) Find all invariants. (b) Find the smallest measure $\mu:X\to\mathbb{N}$ as in Proposition 0.26. (c) Add the transition $3\to0$: show well-foundedness fails and say which invariants survive.

5. $^\ast$ Prove Proposition 0.26(b) in detail, including the use of König's lemma. Give a well-founded coalgebra with no measure into $\mathbb{N}$ (necessarily not finitely branching).

6. $^\ast$ Prove Proposition 0.30 in full. Then show that, with $\mathbf{Pfn}=\mathrm{Kl}(\mathrm{Option})$ and the identification of Proposition 0.16, the assignment sending a partial function to its span defines a functor $\mathbf{Pfn}\to\mathbf{Span}(\mathbf{Set})$, and that it is faithful.
