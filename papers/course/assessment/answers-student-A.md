# Answers: student A

Sources used: `papers/course/README.md`, chapters 0 to 7, `lean/MiniTensorLogic.lean`, `assessment/questions.md`. Nothing else was read. Lean was not run; every Lean name below is copied from the notes or from the companion file. Chapter references are to the notes' own numbering ("Theorem 5.18" is the notes' name for specification Theorem 26.3, and so on).

## Q1

$f(0)=0,\ f(1)=1,\ f(2)=0$; $v=(5,7,11)$, $w=(2,3)$.

Pushforward sums over each fibre: $f^{-1}(0)=\{0,2\}$, $f^{-1}(1)=\{1\}$.

- $(f_!v)(0)=v_0+v_2=5+11=16$, $(f_!v)(1)=v_1=7$. So $f_!v=(16,7)$.
- Pullback is precomposition, $f^\ast w=w\circ f=(w_{f(0)},w_{f(1)},w_{f(2)})=(w_0,w_1,w_0)=(2,3,2)$.

Transpose identity (Proposition 2.8):

- $\langle f_!v,w\rangle_{[2]}=16\cdot2+7\cdot3=32+21=53$.
- $\langle v,f^\ast w\rangle_{[3]}=5\cdot2+7\cdot3+11\cdot2=10+21+22=53$.

Both are $53$, so the identity holds numerically.

## Q2

For $f:I\to J$ between finite sets (discrete categories) and $A:I\to\mathbf{Set}$ (Proposition 0.11, Theorem 2.4):

$$(\mathrm{Lan}_fA)(j)=\coprod_{i\in f^{-1}(j)}A_i=(\Sigma_fA)(j),\qquad(\mathrm{Ran}_fA)(j)=\prod_{i\in f^{-1}(j)}A_i=(\Pi_fA)(j).$$

Why they are the adjoints of restriction $f^\ast G=G\circ f$. Because the categories are discrete, a natural transformation is just a family of functions with no naturality condition. A map $\Sigma_fA\Rightarrow G$ is a family $\alpha_j:\coprod_{i\in f^{-1}(j)}A_i\to G_j$. By the universal property of the coproduct, each $\alpha_j$ is the same as a family $A_i\to G_j$ with $f(i)=j$. Every $i$ lies in exactly one fibre, so the whole collection is a family $A_i\to G_{f(i)}=(f^\ast G)_i$, i.e. a map $A\Rightarrow f^\ast G$. That is the bijection $\mathrm{Nat}(\mathrm{Lan}_fA,G)\cong\mathrm{Nat}(A,f^\ast G)$, so $\mathrm{Lan}_f\dashv f^\ast$. Dually, a map $f^\ast G\Rightarrow A$ is a family $G_{f(i)}\to A_i$. Grouping by fibre and using the universal property of the product, this is the same as a family $G_j\to\prod_{i\in f^{-1}(j)}A_i$, i.e. a map $G\Rightarrow\mathrm{Ran}_fA$, so $f^\ast\dashv\mathrm{Ran}_f$. (Equivalently via the pointwise formula: the comma categories $f\downarrow j$ and $j\downarrow f$ are discrete on the fibre.)

Which decategorifies to contraction: $\mathrm{Lan}_f=\Sigma_f$. Taking cardinalities sends $\coprod\mapsto\sum$ and, via $\kappa:\mathbb{N}\to K$, gives the pushforward $(f_!v)(j)=\bigoplus_{i\in f^{-1}(j)}v(i)$, which is summation over an index. Structure needed on $K$: a commutative monoid $(K,\oplus,0_K)$ (the empty fibre gives $0_K$). The transpose identity and contraction with $\otimes$-weights additionally need a commutative semiring (distributivity and absorption). $\Pi_f$ would decategorify to a fibrewise $\otimes$-product $f_\otimes$, which has no core constructor. The notes stress this is an analogy (a "shadow") and not an adjunction between $K^I$ and $K^J$.

## Q3

Statement `Y[i,k] = A[i,j] B[j,k]`, $i\in[2]$, $j\in[3]$, $k\in[2]$.

As two weighted spans composed by pullback (Chapter 2, "Matrix multiplication"):

- First span $[2]\xleftarrow{\pi_i}[2]\times[3]\xrightarrow{\pi_j}[3]$ with weight $A$.
- Second span $[3]\xleftarrow{\pi_j}[3]\times[2]\xrightarrow{\pi_k}[2]$ with weight $B$.
- Composite apex: $M\times_{[3]}N=\{((i,j),(j',k))\mid j=j'\}\cong[2]\times[3]\times[2]$, which has $12$ elements. Weight $A[i,j]\otimes B[j,k]$. The contracted index $j$ is the variable the pullback glues on.

Seen as one statement (Proposition 2.13), the global valuation set is $M=[2]\times[3]\times[2]$ with the three projections $\pi_A(i,j,k)=(i,j)$, $\pi_B(i,j,k)=(j,k)$ and output $\pi_{\mathrm{out}}(i,j,k)=(i,k)$. The apex is $M$ and the legs of the composite span are $(i,j,k)\mapsto i$ and $(i,j,k)\mapsto k$.

Formula:
$$Y=(\pi_{\mathrm{out}})_!\big(\pi_A^\ast A\otimes\pi_B^\ast B\big),\qquad Y[i,k]=\bigoplus_{j\in[3]}A[i,j]\otimes B[j,k].$$
That is pullback of each operand to $M$, pointwise product, then pushforward along the output projection.

Category: "composition of two contractions is matrix multiplication" is literally composition of morphisms in $\mathbf{Mat}(K)$ (objects finite sets, morphisms matrices, composite $(A;B)[i,k]=\bigoplus_jA[i,j]\otimes B[j,k]$). The linearization functor $\mathrm{Lin}:\mathbf{Span}(\mathbf{FinSet})\to\mathbf{Mat}(K)$ (Corollary 2.12d, from Proposition 2.12) carries span composition (pullback) to that composition. In $\mathbf{Span}(\mathbf{FinSet})$ (weighted) the same fact is the pullback composite. My answer is $\mathbf{Mat}(K)$, with $\mathrm{Lin}$ as the bridge; the Lean statement is `WSpan.lin_comp` in the companion.

## Q4

Statements: `T[0*i] = 1` with $i\in[3]$ (the binder is kept even though its coefficient is $0$), and `T[0] = 1` (empty context).

- First statement: $|D_s|=|[3]|=3$ occurrences, all addressed to $(T,0)$ (Section 2.5: binders are collected before output indices are simplified).
- Second statement: empty context, $\mathrm{Val}(())=\{()\}$ so exactly one occurrence, also addressed to $(T,0)$.
- Total: $3+1=4$ occurrences target $(T,0)$.
- Collected value over $\mathbb{R}$: $1+1+1+1=4$.

The construction that keeps them distinct is the coproduct $\mathcal{O}_P=\coprod_sD_s$ (occurrences tagged by the statement identifier $s$), with $\mathrm{dst}$ its copairing. A union of "texts with valuations" would collapse them. Relabelling by a bijection is harmless (Proposition 2.7(3)), deleting duplicates is not a bijection.

## Q5

Exact reals, $\mathrm{Result}(\mathbb{R})=\mathbb{R}\sqcup\{\bot\}$.

(a) $0\otimes\log(-1)=\bot$. Strict pairing is undefined when one component is, and $0_K$ is a successful value, not the zero morphism of $\mathbf{Pfn}$, so it cannot absorb $\bot$.

(b) $\bigoplus_{j\in[0]}\log(-1)=\downarrow 0$ (the value $0$). $\mathrm{batch}_\varnothing=\mathrm{id}_1$, so no body instance is evaluated and the empty reduction is $0_K$.

(c) $\mathrm{at}(\mathrm{tab}_{j\in[2]}\log X[j],(0))$ with $X=(4,-1)$ is $\bot$. Tabulation is strict batching and demands $\log(-1)$, and selection cannot bypass the undefined component.

(d) Guarded statement: the guard $i<1$ gives $D=\{0\}$, the only occurrence is $i=0$, whose body is $\log X[0]=\log4$, so the body is defined with value $\downarrow\log4$. The guard removes $i=1$ before any body is evaluated.

(e) Iverson version at $i=1$: the body is $\mathbf{1}_{1<1}\otimes\log(X[1])=0\otimes\log(-1)=\bot$ by strictness, and the occurrence exists, so the program has no model.

## Q6

Lax naturality (Proposition 3.13). For $r:I\to J$ in $\mathbf{FinSet}$ and partial $f:A\rightharpoonup B$,
$$r_B^\ast\circ\mathrm{batch}_J(f)\ \preceq\ \mathrm{batch}_I(f)\circ r_A^\ast .$$
The order $\preceq$ is the definedness order on partial maps with the same source and target (Definition 3.12): $h\preceq k$ iff $h(a)\downarrow v\Rightarrow k(a)\downarrow v$, i.e. inclusion of graphs. It is not an order on $\mathrm{Result}(\tau)$, and $\bot$ stays unordered. Restricting after batching is less defined than batching after restricting.

Equality holds when $f$ is total, or when $r$ is surjective (every $j$ is some $r(i)$, so success of the restricted batch forces success of the full batch).

Counterexample (Example 3.14): $f=$ reciprocal on $\mathbb{Q}$, $J=[2]$, $I=[1]$, $r:0\mapsto0$, $a=(2,0)$. Left: $\mathrm{batch}_{[2]}(f)(2,0)$ needs $1/0$, so it is $\bot$, and $r^\ast\bot=\bot$. Right: $r^\ast a=(2)$ and $\mathrm{batch}_{[1]}(f)(2)=(1/2)$. The inequality is strict; $r$ is injective but not surjective and $f$ is not total. In Lean: `batch_lax` and `batch_lax_strict`.

Forbidden optimisation: "select before compute". Replacing "build the whole array of $f$-values, then read coordinate $p$" by "read coordinate $p$, then apply $f$" (slicing before mapping, pushing a gather through an elementwise op, lazy array construction). The rewrite can turn $\bot$ into a value, which changes whether models exist. It is valid only if $f$ is total, $r$ is surjective, or the omitted applications are separately proved to succeed.

## Q7

Strict pairing makes $(\mathbf{Pfn},\times,1)$ symmetric monoidal but not cartesian (Proposition 3.6). Failing law: the projection law $\pi_1\circ\langle f,g\rangle=f$. $\pi_1\circ\langle f,g\rangle$ is defined at $c$ only when $g(c)$ is, while $f$ may be defined there. (A second failure: the unit $1$ is not terminal, the terminal object is $\varnothing$, and the discard maps $!_A:A\to1$ are not natural since $!_B\circ f$ has domain $\mathrm{dom}\,f$ while $!_A$ has domain $A$.)

Counterexample (Example 3.7): $f=\mathrm{id}$ on $\mathbb{Q}$, $g=$ reciprocal (domain $\mathbb{Q}\setminus\{0\}$). At $c=0$, $\pi_1\circ\langle\mathrm{id},g\rangle(0)=\bot$ but $\mathrm{id}(0)=0$. The value of the reciprocal was never used, yet its failure is visible.

Consequence: dropping an unused intermediate (dead-code elimination, short-circuiting $0\otimes E$) is the naturality of discard, which is false in $\mathbf{Pfn}$. A subcomputation may only be discarded when it is total on the inputs at hand, and that has to be proved. (Copying/sharing a deterministic subterm is fine, since $\Delta$ is natural.)

## Q8

Collection at $\rho_1$ (extends $\eta_1$ with $Z=(0,4)$, $Y=(0,4)$, $L=\log4$). Admissible since $\rho_1(Y)[1]=4>0$. Body values (Example 4.8): s1: $(-1,4)$; s2: $(1,0)$; s3: $(\mathrm{relu}\,0,\mathrm{relu}\,4)=(0,4)$; s4: $\log4$.

- $\mathrm{Collect}(\rho_1)(Z)=V_{s1}\oplus V_{s2}=(-1,4)+(1,0)=(0,4)$
- $\mathrm{Collect}(\rho_1)(Y)=V_{s3}=(0,4)$
- $\mathrm{Collect}(\rho_1)(L)=\log4$

These agree with $\rho_1$ on every defined tensor, and $\Phi_P$ copies the inputs, so $\Phi_P(\rho_1)=\rho_1$. It is a fixed point and $\rho_1\in\mathrm{Models}(\mathrm{Scorer},\eta_1)$. It is the only one, since the equations force $Z$, then $Y$, then $L$ level by level.

Fibre of $(Z,1)$: $\{(s1,j{=}1),(s2,j{=}1)\}$.

On $\eta_0$ ($X=(0,0)$): the equations for $Z$ read only inputs, so any model has $Z=(1,0)$, and the equations for $Y$ then force $Y=\mathrm{relu}(Z)=(1,0)$, so $\rho(Y)[1]=0$ and the body $\log0$ of s4 is $\bot$, i.e. $\rho\notin\mathrm{AdmEnv}$. Admissible environments exist (anything extending $\eta_0$ with $Y[1]>0$, e.g. $Z=(0,0),Y=(0,5),L=7$), because admissibility is only a condition on candidate values and mentions no equation, but none of them is a fixed point: a fixed point must have $Y[1]=0$, contradicting $Y[1]>0$. So $\mathrm{Models}(\mathrm{Scorer},\eta_0)=\varnothing$, and no choice of $L$ helps because the failure is in a body, not a value.

## Q9

Equalizer description (Proposition 4.12). With $\mathrm{AdmEnv}(P)$ the pullback of $\mathrm{def}^{\mathcal{O}_P}$ along $\mathrm{ev}_P$ (a subobject of $\mathrm{Env}_\Sigma$ with inclusion $i$), $\mathrm{Fix}(P)$ is the equalizer in $\mathbf{Set}$ of the parallel pair
$$\mathrm{AdmEnv}(P)\ \underset{i}{\overset{\Phi_P}{\rightrightarrows}}\ \mathrm{Env}_\Sigma,\qquad \Phi_P=\langle\mathrm{res}_{\mathrm{In}}\circ i,\ \mathrm{Collect}_P\rangle .$$
Equivalently it is the equalizer of $\mathrm{Collect}_P$ and $\mathrm{res}_{\mathrm{Def}}\circ i$ into $\mathrm{Env}(\mathrm{Def})$. The input $\eta$ enters through a pullback: $\mathrm{Models}(P,\eta)$ is the pullback of $\mathrm{res}_{\mathrm{In}}\circ i\circ e:\mathrm{Fix}(P)\to\mathrm{Env}(\mathrm{In})$ along $\eta:1\to\mathrm{Env}(\mathrm{In})$, the fibre of $\mathrm{Fix}(P)$ over $\eta$.

Why all fixed points and not a least one: the equalizer has no order, no starting point and no iteration. $\bot$ carries no order and is not zero, so there is no least fixed point. Kleene and Tarski need an order and monotonicity, contraction theorems need a metric, and neither is available. $\Phi_P$ is also not an endomap of $\mathrm{AdmEnv}(P)$ (Example 4.10), so iterating it is not even well typed. Iteration from zero diverges where the answer is unique and silently picks one fixed point where there are many. A program denotes a value only when its set of models has exactly one element.

Program `T[] = X[]; T[] = 2 T[]` with $X=3$: collected equation $T=X+2T=3+2T$, so $T=-3$. The model set is the singleton $\{T=-3\}$ (the unique model is the complete environment with $X=3$, $T=-3$). Iteration from $T_0=0$ gives $T_n=(2^n-1)\cdot3\to\infty$, so it diverges.

## Q10

Witness span (Definition 4.18). The witness set is $W_P=\{(\eta,\rho)\mid\eta\in\mathrm{Env}(\mathrm{In}),\ \rho\in\mathrm{Models}(P,\eta)\}\cong\coprod_\eta\mathrm{Models}(P,\eta)\cong\mathrm{Fix}(P)$. The span is
$$\mathrm{Env}(\mathrm{In})\xleftarrow{\ell}W_P\xrightarrow{r}\mathrm{Env}(\mathrm{Out}),\quad\ell(\eta,\rho)=\eta,\ r(\eta,\rho)=\rho|_{\mathrm{Out}}.$$

If $\mathrm{Out}_P=\mathrm{In}_Q$ (and $Q$'s defined identifiers are fresh), the composite span has apex the pullback
$$W_P\times_{\mathrm{Env}(\mathrm{Out}_P)}W_Q=\{(\rho_P,\rho_Q)\in\mathrm{Fix}(P)\times\mathrm{Fix}(Q)\mid\rho_P|_{\mathrm{Out}_P}=\rho_Q|_{\mathrm{In}_Q}\}.$$
By Theorem 4.22 this is in bijection with $\mathrm{Fix}(P;Q)$, the set of models of the glued program $P;Q$ (statements of both kept distinct, $\mathcal{O}_{P;Q}=\mathcal{O}_P\sqcup\mathcal{O}_Q$), via $\rho\mapsto(\pi_P\rho,\pi_Q\rho)$, commuting with both legs. So the span of $P;Q$ is isomorphic to the composite of the spans, with no existence, uniqueness or rank hypothesis.

Hypothesis for composing partial functions: $\mathrm{AtMostOneModels}(P)$ and $\mathrm{AtMostOneModels}(Q)$ (both left legs monic). Then $P;Q$ also has at most one model and $[\![P;Q]\!]=[\![Q]\!]\circ[\![P]\!]$ as a Kleisli composite in $\mathbf{Pfn}$ (Proposition 4.28), with domain $\{\eta\in\mathrm{AdmInput}(P)\mid[\![P]\!](\eta)\in\mathrm{AdmInput}(Q)\}$. (The notes say the domain and value formulas need only the hypothesis on $P$, but the full statement uses both; the experimental Lean assumes both.)

Why model existence does not compose (Example 4.30): $P$ is `t[] = t[] t[]` (models $t=0$ and $t=1$, so $[\![P]\!]$ is nowhere defined) and $Q$ is `u[] = log(t[])` (or reciprocal), with $\mathrm{AdmInput}(Q)=\{t>0\}$. By Corollary 4.23, $\mathrm{Models}(P;Q)\cong\mathrm{Models}(Q,0)\sqcup\mathrm{Models}(Q,1)=\varnothing\sqcup\{u=0\}$, so $P;Q$ has a unique model ($t=1,u=0$) although $[\![Q]\!]\circ[\![P]\!]$ is undefined. Replacing $P$ by $P'$: `t[] = t[]+1` (no models, also nowhere-defined denotation) gives a composite with no model. Equal partial functions, same $Q$, different results. Existence depends on the boundary values of $P$'s models, which the denotation forgets, not on whether $P$ and $Q$ each have models somewhere.

## Q11

The three rules (Definition 5.6), configuration $(\sigma,\alpha,U)$:

- CONTRIBUTE: requires a pending occurrence $o\in U$, its read footprint published ($\mathrm{Read}(o)\subseteq\mathrm{dom}\,\sigma$), and ready evaluation defined, $\mathrm{Eval}_\sigma(E_s,\nu)\downarrow v$. Effect: $\alpha(\mathrm{dst}\,o)\mathrel{\oplus}=v$, $o$ removed from $U$, $\sigma$ unchanged. (A zero-valued body still consumes its occurrence.)
- PUBLISH: requires a defined address $a\notin\mathrm{dom}\,\sigma$ with no pending occurrence targeting it ($U\cap\mathcal{C}_P(a)=\varnothing$), the completion barrier. Effect: $\sigma[a\mapsto\alpha(a)]$. An empty fibre can publish $0_K$ at once.
- UNDEFINED: requires a pending $o$ whose footprint is published and whose ready evaluation is $\bot$. Effect: move to the terminal $\mathsf{Failed}(o,\sigma,\alpha,U)$.

Program `Pre[]=A[]; Pre[]=B[]; T[]=relu(Pre[])`, $A=1$, $B=-1$. After consuming only `Pre = A`: $\alpha(\mathrm{Pre})=1$ (the table in Example 5.34), $\mathrm{dom}\,\sigma=\{(A,()),(B,())\}$ (the two inputs only; $\mathrm{Pre}$ and $T$ unpublished). The occurrence of $T$ is not ready: $\mathrm{Read}=\{(\mathrm{Pre},())\}\not\subseteq\mathrm{dom}\,\sigma$, so it waits, and PUBLISH at $\mathrm{Pre}$ is blocked by the pending `Pre = B`.

Independence of order: readiness depends only on $\mathrm{dom}\,\sigma$, never on an accumulator, and in either order the barrier leaves $\mathrm{Pre}$ unpublished until both contributions are consumed. If `Pre = B` is consumed first, the intermediate accumulator is $-1$ instead of $1$, but the accumulator is not readable, so the outcome ("not ready") is the same. Once both are consumed, $\mathrm{Pre}=0$ is published, then $T=\mathrm{relu}(0)=0$. Applying relu to the partial value $1$ would give $T=1$, the wrong answer, which is exactly the mistake the typing of `evalReady` (it receives only `c.published`) rules out.

## Q12

Theorem 26.3 (Theorem 5.18 in the notes): (i) if $\mathrm{Init}(P,\eta)\Downarrow\rho_\sigma$ (a run to a complete configuration), then $\mathrm{Models}(P,\eta)=\{\rho_\sigma\}$ and $[\![P]\!](\eta)=\rho_\sigma|_{\mathrm{Out}}$; (ii) if $\mathrm{Init}(P,\eta)\to^\ast\mathsf{Failed}(\dots)$, then $\mathrm{Models}(P,\eta)=\varnothing$.

Why no rank certificate: the proof is by invariants. Conservation (Lemma 5.14) shows the final store is a model, and Lemma 5.16(b) shows every reachable store $\sigma\sqsubseteq\rho$ for every model $\rho$. A complete store is maximal in the store category, so every model equals $\rho_\sigma$. For (ii), a model would put every reachable store below it, and then read stability would make the undefined body defined, a contradiction. Both statements only speak about runs that actually happened, so they do not need to know that a run exists or terminates in success or failure. In Lean: `successful_model`, `successful_unique`, `failed_no_model` take no `RankCertificate`.

Correspondence for the ranked fragment (Theorem 26.6, Theorem 5.28): let $P$ have a rank certificate. (1) Every maximal run succeeds or fails explicitly. (2) If a model exists, every maximal run succeeds and returns it. (3) If no model exists, every maximal run fails. (4) $\mathrm{Init}(P,\eta)\Downarrow\rho\iff\mathrm{Models}(P,\eta)=\{\rho\}$.

Why the hypothesis cannot be dropped: `T[] = T[]`. Its only occurrence reads $(T,())$, so $(T,())\in\mathrm{Dep}(T,())$ is a cycle, and by Proposition 5.26 no rank certificate exists. Every real number is a model (infinitely many). The machine is blocked at $\mathrm{Init}$: the occurrence waits for $(T,())$ and PUBLISH waits for the occurrence. So the maximal run neither succeeds nor fails, contradicting (1), and a ranked program would have at most one model (Corollary 5.29), which this one violates. Blocking says nothing about models. The notes' other cyclic program `T[]=X[]; T[]=2T[]` has exactly one model $T=-X$ but also blocks, showing the backward direction of (4) fails without a certificate.

## Q13

Rank certificate (Definition 5.25): a function $r:\mathrm{Addr}_\Sigma\to\mathbb{N}$ with $b\in\mathrm{Dep}(a)\Rightarrow r(b)<r(a)$ for all $a$, where $\mathrm{Dep}(a)=\bigcup_{o\in\mathcal{C}_P(a)}\mathrm{Read}(o)$. Lax morphism sense: $\mathrm{Dep}:\mathrm{Addr}_\Sigma\to\mathcal{P}_{\mathrm{fin}}(\mathrm{Addr}_\Sigma)$ is a $\mathcal{P}_{\mathrm{fin}}$-coalgebra (the dependency coalgebra); $r$ is a function $h$ with $h[\gamma(x)]\subseteq\delta(h(x))$, a lax morphism (simulation) into $(\mathbb{N},\mathrm{pred})$ with $\mathrm{pred}(n)=\{m\mid m<n\}$, i.e. $r[\mathrm{Dep}(a)]\subseteq\{m\mid m<r(a)\}$. It preserves transitions without reflecting them. A strict morphism (equality) would require every number below $r(a)$ to be the rank of a dependency, which `Scorer` cannot satisfy.

Running example: $r=0$ on every input address, $r(Z,j)=1$, $r(Y,j)=2$, $r(L,())=3$.

Finite history: $r(X,i)=r(Z,i)=0$ and $r(H,(i,l))=l+1$. For $N=2$ the time slices have ranks $1,2,3$ (for $d=1$: $r(H,(0,0))=1$, $r(H,(0,1))=2$, $r(H,(0,2))=3$). Check: $\mathrm{Dep}(H,(i,l{+}1))=\{(X,i)\}\cup\{(H,(j,l))\}$ has ranks $0$ and $l+1<l+2$.

Measure of the initial configuration of `Scorer` on $\eta_1$: $\mu=|U|+|\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma|=7+5=12$.

## Q14

A blocked configuration is a running configuration that is not complete and has no enabled transition (no CONTRIBUTE, PUBLISH or UNDEFINED applies). It reports an unresolved dependency structure and is neither success nor failure, and says nothing about whether a model exists. A failed configuration is reached by the rule UNDEFINED: a ready occurrence (footprint published) has body $\bot$. It is an explicit, terminal outcome and proves $\mathrm{Models}(P,\eta)=\varnothing$ (Theorem 5.18(ii)). A bare $\mathcal{P}_{\mathrm{fin}}$-coalgebra cannot tell them apart (both have empty successor set), hence the observation map.

Examples (Example 5.36):

- Blocks with no model: `T[] = T[] + 1`. Collected equation $T=T+1$, models none, blocked at $\mathrm{Init}$.
- Blocks with a unique model: `T[] = X[]; T[] = 2 T[]`. The machine consumes `T = X`, then the self-reading occurrence waits for $(T,())$ and publication waits for it, so it blocks. The model is $T=-X$.
- Blocks with many models: `T[] = T[]`, every real is a model, blocked at $\mathrm{Init}$.

## Q15

Dictionary, mini file (`Course.`) and production (`LeanNCD.Semantics.`), from the Chapter 6 tables and the Lean file.

| Notion | Mini (`lean/MiniTensorLogic.lean`) | Production |
| --- | --- | --- |
| pullback $f^\ast$ | `pullback` (with `pullback_id`, `pullback_comp`) | `pullback` |
| pushforward $f_!$ | `pushforward` (`pushforward_zero`, `_add`, `_id`, `_comp`, `_relabel`, `_grouped`) | `pushforward` (plus `pushforwardHom`) |
| occurrences as coproduct, $\mathcal{O}_P$ and $\mathrm{dst}$ | `Program.Occ` (sigma over statement positions), `Program.dst` | `Program.Occurrence` (sigma per defined tensor, `Program.Defined`), `Program.destination` |
| Kleisli interpretation | `evalWith`, `interpret` (built on `sequenceFin`; `Option` with `none` as $\bot$) | `evalWith`, `interpret` (built on dependent `sequence`; `Registry.apply` for primitives) |
| equation operator $\Phi_P$ | `Program.equationOperator` | `Program.equationOperator` |
| model relation | `Program.Models` (equivalence with collect equations: `Program.models_fixedpoint`) | `Program.Models`, `Program.models_fixedpoint` |
| step relation | `Program.Step` (constructors `contribute`, `publish`, `undefined`) | `Program.Step` (constructors `contribute`, `publication`, `undefined`) |
| termination measure | `Program.measure`, `Program.measure_decreases` | `Program.measure`, `Program.stateMeasure`, `Program.step_decreases`, `Program.step_wellFounded` |

Related: collection is `Program.collect` in both; admissibility `Program.AdmEnv` in both; production has `Program.Running`/`Program.MachineState` where mini has `Config`/`Outcome`.

## Q16

In the companion file the statement `s4` is `L[] += recip(Y[1])` (`.prim recip (.read .Y ...)`), not `log`. Reason: Lean has no computable logarithm on $\mathbb{Q}$, and `#eval` and `decide +kernel` need a computable scalar sort (everything is over $\mathbb{Q}$).

Why it is faithful to the notes' failing input $\eta_0$: in `Scorer`, $Y=\mathrm{relu}(Z)\ge0$ at every model. On values $\ge0$, $\log$ (domain $x>0$) is undefined exactly at $0$, and so is `recip` (domain $x\ne0$). So both bodies are undefined exactly when $Y[1]=0$. The two primitives have the same domain on the range of $\mathrm{relu}$ (non-negative values). Hence the program has a model on exactly the same inputs: on $\eta_1$ the model has $L=1/4$ instead of $\log4$, and on $\eta_0$, where $Y[1]=0$, there is no model in either version (`scorer_no_model₀`). The admissible environments do differ (one with $Y[1]<0$ is admissible for `recip` but not for $\log$), but a model forces $Y[1]\ge0$, so the difference never reaches `Models`.

## Where the notes were unclear

I list each place I had to interpret, guess or noticed tension.

1. Chapter 1, Section 2.5 and the question text for Q4. The notes write `T[0\cdot i]` (explicit coefficient) while Q4 writes `T[0i]`. I read it as coefficient $0$. A reader could read `0i` as something else. Chapter 1 Section 3 also says `T[0] = 1` "writes the first coordinate of a vector", while Q4 says the tensor has extent 1; both are consistent for my count but the shape of $T$ is not fixed by the notes.
2. Chapter 2, Section 4 and Proposition 2.13 (Q3). The notes give two presentations of a contraction: a composite of two spans glued over the contracted index (apex $\{((i,j),(j',k))\mid j=j'\}$), and one global valuation set $M$ with operand projections $\pi_\ell$ and $\pi_{\mathrm{out}}$. "The three projections" in Q3 could mean either. Also, "in which category is composition of contractions matrix multiplication a statement about composition of morphisms" could be answered as $\mathbf{Span}(\mathbf{FinSet})$ (composition is pullback) or $\mathbf{Mat}(K)$ (composition is matrix product), related by $\mathrm{Lin}$. The notes never say which one the slogan refers to.
3. Chapter 2, Section 3 and Chapter 0, Section 3 (Q2). "What structure on $K$ does the decategorification need" is answered with a commutative monoid for $f_!$ (Definition 2.6) but a commutative semiring for the transpose identity and for $\otimes$-weighted contractions. The notes do not say which one they regard as "the" requirement for "tensor contraction".
4. Chapter 3, Section 2 (Q7). Proposition 3.6 names several failures (unit not terminal, discard not natural, projection law fails); Q7 asks for "the failing law", so I had to choose the projection law and mention discard. The notes do not rank them.
5. Chapter 4, Section 5 and Example 4.16 (Q9). For `T[] = X[]; T[] = 2 T[]` the table gives $\mathrm{Fix}=\{-X\}$ as a set of values of $T$, but $\mathrm{Fix}(P)$ is defined as a set of complete environments. I answered both ways; the notes mix the two readings.
6. Chapter 4, Proposition 4.28 and the remark after it (Q10). The hypotheses are stated as both $\mathrm{AtMostOneModels}(P)$ and $(Q)$, then the notes say the domain and value formulas need only $P$, and that the one-sided form is "proved on paper only" while the experimental Lean assumes both. The precise hypothesis for "composite denotation becomes a composite of partial functions" is therefore ambiguous. Also Example 4.30 uses $\log$ while the proposal uses a reciprocal; the notes say either works.
7. Chapter 5, Example 5.34 and Q11. The question calls it "Section 27.1 of the notes' worked examples", but in the notes that is a specification section number; the notes' example is 5.34. The table gives $\alpha(\mathrm{Pre})=1$ only for the order `Pre = A` first, and the text says "swapping steps 1 and 2 gives the same result" without saying that the intermediate accumulator would be $-1$. The question's "why the answer does not depend on which contribution was consumed first" is ambiguous: the readiness answer is order independent, but $\alpha(\mathrm{Pre})$ is not.
8. Chapter 5, Remark 5.19 and Exercise 8 (Q12). The remark says Theorem 5.18 "holds for every well-formed program, cyclic ones included", then cautions that a successful run witnesses acyclicity, so part (i) is vacuous for cyclic programs. This reads as contradictory on a first pass about what "needs no rank certificate" means: the proof does not use one, but part (i) only has content for programs that have one. Q12's request to "say why it needs no rank certificate" therefore has two defensible answers.
9. Chapter 5, Definition 5.25 and Q13. "Give the rank certificate for the finite history $H$ with $N=2$": the notes only give the general symbolic $r(H,(i,l))=l+1$ and $r=0$ on $X,Z$; for concrete $d$ and the input addresses I had to instantiate it myself. Chapter 0 Section 5 also mentions $\mu$ "starts at $7+5=12$" before $\mu$ is defined (it points forward to Chapter 5).
10. Chapter 5, Sections 3.3 and 3.4 vs Chapter 0, Section 5 (Q14). Chapter 0 says a terminal UNDEFINED step leads to a failure configuration "with no $\mu$"; Chapter 5 gives it $\bar\mu=0$ (and Lean's `stateMeasure` uses $0$). Minor, but a reader could take them as inconsistent.
11. Chapter 6, Section 2 (Q15). The question asks "the corresponding definition in the production modules where the notes give it". For occurrences-as-coproduct the production notion is a per-tensor sigma (`Program.Occurrence`), not a single global coproduct, so "the" corresponding name is a matter of choice. For Kleisli interpretation the mini column also has `sequenceFin` and production `sequence`, and the registry map `Registry.apply` is the real partial map; I listed several names. The row for the termination measure lists `measure` in both but the well-foundedness theorems only in production.
12. Chapter 6, Section 3.6 (Q16). The justification "on values $\ge0$ the two undefined sets coincide" is clear, but the notes also concede the admissible environments differ ($Y[1]<0$). Whether "faithful" means equal admissible environments, equal models or equal model-existence is not stated; I took it to mean equal models/existence on the same inputs.
13. Chapter 2, Section 5 vs Chapter 1, Section 3 (Q4). Chapter 1 says "the number of occurrences is $|D_s|$, which depends on $\Gamma_s$ and $Q_s$, not on the rank of the destination", while Chapter 2 introduces the occurrence set via valuations $\nu\in D_s$ with a write map that may be non-injective. They agree, but the term "binder" versus "context variable" versus "valuation" is used interchangeably, which made the $T[0\cdot i]$ count harder to state precisely.
