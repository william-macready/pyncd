# Assessment answers, student B

Sources used: `papers/course/README.md`, chapters 00 to 07, and `papers/course/lean/MiniTensorLogic.lean`. Question text from `papers/course/assessment/questions.md`. No other material was consulted.

## Q1

$f^{-1}(0)=\{0,2\}$, $f^{-1}(1)=\{1\}$.

- $(f_!v)(j)=\bigoplus_{f(i)=j}v(i)$, so $f_!v=(5+11,\ 7)=(16,\ 7)$.
- $(f^\ast w)(i)=w(f(i))$, so $f^\ast w=(w_0,w_1,w_0)=(2,3,2)$.
- $\langle f_!v,w\rangle_{[2]}=16\cdot2+7\cdot3=53$.
- $\langle v,f^\ast w\rangle_{[3]}=5\cdot2+7\cdot3+11\cdot2=10+21+22=53$.

The two sides agree, as Proposition 2.8 requires.

## Q2

For $A:I\to\mathbf{Set}$ (a family of sets indexed by the discrete category $I$):

- $(\mathrm{Lan}_fA)(j)=\coprod_{i\in f^{-1}(j)}A(i)$ (Chapter 0, Proposition 0.11; Chapter 2, Theorem 2.4).
- $(\mathrm{Ran}_fA)(j)=\prod_{i\in f^{-1}(j)}A(i)$.

Why these are the adjoints of restriction: Definition 0.9 gives $\mathrm{Lan}_f\dashv f^\ast\dashv\mathrm{Ran}_f$ for Kan extensions along $f$, with $f^\ast G=G\circ f$. Chapter 2 checks the first adjunction by hand (Theorem 2.4(ii)). A family of maps $\alpha:\Sigma_fA\to B$ is, by the universal property of the coproduct, the same as a family of maps $A(i)\to B(f(i))$, one for each $i\in I$. That family is exactly a map $A\to f^\ast B$. The unit is the coproduct injection and the counit is the fold. For the right adjoint, a map $f^\ast B\to A$ is a family $B(f(i))\to A(i)$, and grouping the $i$ by $f(i)$ and applying the universal property of the product gives a map $B\to\Pi_fA$. The unit is the diagonal and the counit is the projection.

Decategorification: applying cardinality to the Set-level triple gives $|\Sigma_fA|(j)=\sum_{i\in f^{-1}(j)}|A(i)|$. Read as an operation on scalars, this is the pushforward $f_!$ of Definition 2.6, $(f_!v)(j)=\bigoplus_{f(i)=j}v(i)$. Summing over a contracted index is therefore $f_!$, the Lan/$\Sigma$ side. It needs only a commutative monoid $(K,\oplus,0_K)$, and an empty fibre gives $0_K$. The $\Pi$ side decategorifies to a fibrewise product $\bigotimes$, which needs $\otimes$ and has no core constructor (Chapter 2, Section 3). Chapter 2, Section 3 says the course claims no adjunction between $K$-valued families.

## Q3

Write the statement as two spans of finite sets (Chapter 2, Section 4):

- $[2]\xleftarrow{\ \pi_i\ }[2]\times[3]\xrightarrow{\ \pi_j\ }[3]$ with weight $A$.
- $[3]\xleftarrow{\ \pi_j\ }[3]\times[2]\xrightarrow{\ \pi_k\ }[2]$ with weight $B$.

Their composite is the pullback over $[3]$. The apex is $M=[2]\times[3]\times[2]$, the triples $(i,j,k)$ whose two middle coordinates agree. The three projections are $p_i:M\to[2]$, $p_j:M\to[3]$ and $p_k:M\to[2]$. The composite span has left leg $p_i$, right leg $p_k$, and weight $w(i,j,k)=A[i,j]\otimes B[j,k]$.

Pushforward formula: $Y=(p_i,p_k)_!\,w$, that is, $Y[i,k]=\bigoplus_{j\in[3]}A[i,j]\otimes B[j,k]$. In the form of Proposition 2.13 this is $Y=(\pi_{\mathrm{out}})_!(\pi_A^\ast A\otimes\pi_B^\ast B)$ with $\pi_{\mathrm{out}}=(p_i,p_k)$, $\pi_A=(p_i,p_j)$, $\pi_B=(p_j,p_k)$.

Category: "composition of contractions is matrix multiplication" is a statement in $\mathbf{Mat}(K)$, the category of finite sets with matrices as morphisms and $(A;B)[i,k]=\bigoplus_jA[i,j]\otimes B[j,k]$. The linearization $\mathrm{Lin}:\mathbf{Span}(\mathbf{FinSet})\to\mathbf{Mat}(K)$ is a functor (Corollary 2.12d), and Proposition 2.12 says it sends composite spans to composite matrices.

## Q4

The notes write this as $T[0\cdot i]$. I read the question's $T[0i]$ that way (see the unclear-section entry on index notation).

- $T[0\cdot i]\mathrel{+}=1$ for $i\in[3]$ has $|D_s|=3$ occurrences. Chapter 1, Section 2.5 says the binder is kept before the coefficient-0 index is simplified, so there are three occurrences, not one.
- $T[0]=1$ with no binders has exactly one occurrence (Chapter 1, Section 3).
- So four occurrences address $(T,0)$, and $|\mathcal C_P(T,0)|=4$.

Collected value over $\mathbb R$: each body is $1_K=1$, and $\oplus=+$. So $T[0]=1+1+1+1=4$. An empty fibre would give $0$, but this one is not empty.

The construction that keeps the occurrences distinct is the coproduct $\mathcal O_P=\coprod_sD_s$ (Definition 2.14). Each occurrence is tagged by its statement identifier and valuation, and the destination map is the copairing of the write maps. Chapter 2, Section 5 contrasts this with a union of texts, which would merge the two statements into one.

## Q5

- (a) $\bot$. Strictness: $\log(-1)$ is undefined, and $\otimes$ is strict, so both operands must be defined even when one is $0_K$ (Example 3.16(2)).
- (b) $0$. The reduction is over $[0]$. Batching over $\varnothing$ is the identity (Proposition 3.11), so no body is evaluated and the empty reduction is $0_K$ (Example 3.16(3)).
- (c) $\bot$. Tabulation is strict. It batches $\log$ over $X=(4,-1)$, which demands $\log(-1)$. Selecting coordinate $0$ afterwards cannot repair this (Example 3.17).
- (d) $\downarrow\log 4$. The guard $i<1$ leaves $D=\{0\}$, so there is one occurrence, with body $\log X[0]=\log 4$, which is defined (Example 3.18).
- (e) $\bot$. At $i=1$ the body is $\mathbf 1_{1<1}\otimes\log X[1]=0\otimes\log(-1)=0\otimes\bot=\bot$. The Iverson factor keeps the occurrence, and a total factor cannot cancel $\bot$ (Example 3.18).

## Q6

Proposition 3.13: for $r:I\to J$ in $\mathbf{FinSet}$ and $f:A\rightharpoonup B$,
$$r_B^\ast\circ\mathrm{batch}_J(f)\ \preceq\ \mathrm{batch}_I(f)\circ r_A^\ast .$$

- The order is the definedness order on partial maps $A^J\rightharpoonup B^I$: $h\preceq k$ when $h(a)\downarrow v$ implies $k(a)\downarrow v$ (Definition 3.12). It orders maps, not values, and $\bot$ has no place in it.
- Equality holds when $f$ is total, or when $r$ is surjective.
- Counterexample: $A=B=\mathbb Q$, $f=\mathrm{recip}$, $J=[2]$, $I=[1]$, $r(0)=0$ (injective, not surjective), and $a=(2,0)$. The left side demands $1/0$, so it is $\bot$. The right side gives $r^\ast a=(2)$ and then $(1/2)$. So the left side is less defined, strictly.
- Forbidden optimisation: "select, then compute". A compiler that replaces "build the whole array of $f$-values, then read coordinate $p$" by "read coordinate $p$, then apply $f$" changes the left side into the right side. That can turn $\bot$ into a value, so the rewrite is sound only if $f$ is total, $r$ is surjective, or the omitted applications are proved to succeed (Chapter 3, Section 3).

## Q7

Strict pairing fails the projection law. $\pi_1\circ\langle f,g\rangle=f$ fails at every point where $f$ is defined and $g$ is not. Equivalently, discard is not natural: $!_B\circ f=!_A$ fails for a partial $f$ (Proposition 3.6(2)).

Two-line counterexample: $f=\mathrm{id}$ and $g=\mathrm{recip}$ on $\mathbb Q$. At $c=0$, $\langle f,g\rangle(0)=\bot$ because $g(0)$ is undefined, so $\pi_1\langle f,g\rangle(0)=\bot$, while $f(0)=0$ (Example 3.7).

Consequence: an unused intermediate result cannot be discarded when its computation is partial, because dropping it changes definedness. For example $0\otimes\log(-1)=\bot\neq0$. Dead-code elimination is valid only for subterms that are total on the inputs at hand. Copying a deterministic subterm is fine, since $\Delta$ is natural (Chapter 3, Section 2).

## Q8

Collection at the claimed model $\rho_1$ on $\eta_1$ (Example 4.8):

- $Z[0]=V_{s1}[0]\oplus V_{s2}[0]=(1\cdot1+1\cdot(-2))+1=-1+1=0$.
- $Z[1]=V_{s1}[1]\oplus V_{s2}[1]=(2\cdot1+(-1)(-2))+0=4$.
- $Y[j]=\mathrm{relu}(Z[j])$, so $Y=(0,4)$.
- $L=\log Y[1]=\log4$. (The Lean file has $1/4$, a `recip` stand-in. See Q16.)

So $\mathrm{Collect}_P(\rho_1)$ equals $\rho_1$ on every defined coordinate, which means $\Phi_P(\rho_1)=\rho_1$. $\rho_1$ is admissible, since $Y[1]=4>0$.

Fibre of $(Z,1)$: $\mathcal C_P(Z,1)=\{(s1,j{=}1),(s2,j{=}1)\}$ (Chapter 1, Section 4.3).

Why $\mathrm{Models}(\mathrm{Scorer},\eta_0)$ is empty: the equations force $Z=(1,0)$, since $Z$ reads only inputs and $X=(0,0)$, $B[1]=0$. Then $Y[1]=\mathrm{relu}(Z[1])=0$. Admissibility needs $Y[1]>0$, so no fixed point is admissible. Admissibility alone does not constrain the inputs, so admissible environments exist over $\eta_0$; it is the combination with the equations that removes them.

## Q9

By Proposition 4.12, $\mathrm{Fix}(P)$ is the equalizer in $\mathbf{Set}$ of two parallel maps $\mathrm{AdmEnv}(P)\rightrightarrows\mathrm{Env}_\Sigma$: $\Phi_P$ and the inclusion $i$. Equivalently it is the equalizer of $\mathrm{Collect}_P$ and $\mathrm{res}_{\mathrm{Def}}\circ i$. $\mathrm{Models}(P,\eta)$ is the pullback of $\mathrm{res}_{\mathrm{In}}\circ i\circ e$ along $\eta:1\to\mathrm{Env}(\mathrm{In})$. So $\eta$ enters only as the constraint $\rho|_{\mathrm{In}}=\eta$. It picks out a fibre.

Why all fixed points: $\mathrm{Result}(K)$ and $\bot$ carry no order, and $\mathrm{Fix}(P)$ is defined without a starting point or iteration. The notes say no least-fixed-point selection is made (Chapter 4, Section 4), and iterating $\Phi_P$ is not even well typed, because $\Phi_P$ can leave $\mathrm{AdmEnv}$ (Example 4.10). Iterating from zero is wrong in every case (Examples 4.1 and 4.16).

Model set for $T[]=X[]$ and $T[]=2T[]$ with $X=3$: the collected equation is $T=X+2T$, so $T=-X=-3$. Check: $3+2(-3)=-3$. So $\mathrm{Models}=\{\rho\mid\rho(X)=3,\ \rho(T)=-3\}$, a singleton (Example 4.16, first row). All bodies are total, so $\mathrm{AdmEnv}=\mathrm{Env}_\Sigma$.

## Q10

Witness span: $W_P=\{(\eta,\rho)\mid\rho\in\mathrm{Models}(P,\eta)\}$ with legs $\ell(\eta,\rho)=\eta$ and $r(\eta,\rho)=\rho|_{\mathrm{Out}}$, giving $\mathrm{Env}(\mathrm{In})\xleftarrow{\ell}W_P\xrightarrow{r}\mathrm{Env}(\mathrm{Out})$ (Definition 4.18).

Composability: $\mathrm{In}_Q=\mathrm{Out}_P$ and the defined tensors of $Q$ are fresh (Definition 4.20). The composite span is the pullback $W_P\times_{\mathrm{Env}(\mathrm{Out}_P)}W_Q$, the pairs of models that agree on the boundary. By Theorem 4.22 the map $\rho\mapsto(\pi_P\rho,\pi_Q\rho)$ is a bijection from $\mathrm{Fix}(P;Q)$ onto this apex, and it commutes with both legs. So the apex is isomorphic to the set of models of the glued program $P;Q$, and the composite span is isomorphic to the span of $P;Q$.

Hypothesis for a composite of partial functions: $\mathrm{AtMostOneModels}(P)$, meaning every $\eta$ has at most one model of $P$ (Proposition 4.28). Then $[\![P;Q]\!]=[\![Q]\!]\circ[\![P]\!]$ as a Kleisli composite in $\mathbf{Pfn}$, with domain $\{\eta\in\mathrm{AdmInput}(P)\mid[\![P]\!](\eta)\in\mathrm{AdmInput}(Q)\}$. The notes say the domain and value formulas need only the hypothesis on $P$.

Why model existence still does not compose: a partial function forgets how many models stand behind each input-output pair. Whether $P;Q$ has a model depends on the boundary values of $P$'s models. Example 4.30 shows this. Take $P$: $t=t^2$, whose models are $t=0$ and $t=1$ and whose denotation is nowhere defined. Take $Q$: $u=\log t$, with $\mathrm{AdmInput}(Q)=\{t>0\}$. Then $\mathrm{Models}(P;Q)\cong\mathrm{Models}(Q,0)\sqcup\mathrm{Models}(Q,1)=\varnothing\sqcup\{u=0\}$. So $P;Q$ has a unique model, while $[\![Q]\!]\circ[\![P]\!]$ is undefined. Replacing $P$ by $t=t+1$ keeps the same denotation (nowhere defined), but then $P';Q$ has no model. Equal partial functions composed with the same $Q$ give different answers.

## Q11

The three rules (Definition 5.6):

- CONTRIBUTE. Requires an occurrence $o=(s,\nu)\in U$ whose footprint is published, $\mathrm{Read}(o)\subseteq\mathrm{dom}\,\sigma$, and whose body is defined, $\mathrm{Eval}_\sigma(E_s,\nu)\downarrow v$. Effect: $\alpha(\mathrm{dst}\,o)\mathrel{\oplus}=v$, and $o$ leaves $U$.
- PUBLISH. Requires an unpublished defined address $a\notin\mathrm{dom}\,\sigma$ with no pending writer, $U\cap\mathcal C_P(a)=\varnothing$. This is the completion barrier. Effect: $\sigma(a):=\alpha(a)$.
- UNDEFINED. Requires an occurrence in $U$ with published footprint and $\mathrm{Eval}_\sigma(E_s,\nu)=\bot$. Effect: move to the terminal state $\mathsf{Failed}(o,\sigma,\alpha,U)$.

Example (the program is `Pre[] = A[]; Pre[] = B[]; T[] = relu(Pre[])`, with $A=1$, $B=-1$; the notes call it Example 5.34, which the question calls Section 27.1 of the notes):

- After consuming only the first contribution, $\alpha(\mathrm{Pre})=1$.
- $\mathrm{dom}\,\sigma=\{A,B\}$, the inputs only. $\mathrm{Pre}$ is not published.
- $T$'s occurrence has footprint $\{(\mathrm{Pre},())\}$, which is not in $\mathrm{dom}\,\sigma$. So it is not ready and it waits.

Independence of the order: readiness reads only $\sigma$, and $\sigma$ gains $\mathrm{Pre}$ only at PUBLISH. PUBLISH needs both writers consumed, by the barrier. The accumulator value (1 or $-1$ in the middle) is never read, because `evalReady` receives only `c.published`. Swapping the two steps gives the same final result, consistent with Proposition 5.30.

## Q12

Theorem 26.3 (Theorem 5.18 in the notes):

- (i) If $\mathrm{Init}(P,\eta)\Downarrow\rho_\sigma$, then $\mathrm{Models}(P,\eta)=\{\rho_\sigma\}$ and $[\![P]\!](\eta)=\rho_\sigma|_{\mathrm{Out}}$.
- (ii) If $\mathrm{Init}(P,\eta)\to^\ast\mathsf{Failed}(o,\sigma,\alpha,U)$, then $\mathrm{Models}(P,\eta)=\varnothing$.

It needs no rank certificate because its proof uses only the conservation invariant (Lemma 5.14), candidate preservation (Lemma 5.16, which uses the barrier and admissibility of models), and the fact that a total store is maximal (Proposition 5.2(b)). None of these mentions ranks. Remark 5.19 says it holds for cyclic programs and every schedule. It does not say that a run succeeds or fails.

Ranked correspondence (Theorem 5.28), for programs with a rank certificate:

1. every maximal run succeeds or fails explicitly;
2. if a model exists, every maximal run succeeds and returns it;
3. if no model exists, every maximal run fails;
4. $\mathrm{Init}(P,\eta)\Downarrow\rho$ if and only if $\mathrm{Models}(P,\eta)=\{\rho\}$.

For $T[]=T[]$: the occurrence depends on $(T,())$, so $(T,())\in\mathrm{Dep}(T,())$ is a cycle and no certificate exists (Proposition 5.26). Every real is a model. The machine is blocked at $\mathrm{Init}$: the occurrence waits for $(T,())$, and PUBLISH is blocked by the pending writer. So the run is neither success nor failure. Statement (2) would require a successful run with a model, and here there is none, so the hypothesis cannot be dropped. Theorem 5.27 (ranked progress) is what rules out blocking, and its proof uses the rank.

## Q13

A rank certificate is a function $r:\mathrm{Addr}_\Sigma\to\mathbb N$ such that $r[\mathrm{Dep}(a)]\subseteq\{m\mid m<r(a)\}$ for every address $a$. Equivalently, $b\in\mathrm{Dep}(a)$ implies $r(b)<r(a)$ (Definition 5.25). Viewing $\mathrm{Dep}$ as a $\mathcal P_{\mathrm{fin}}$-coalgebra, $r$ is a lax morphism into $(\mathbb N,\mathrm{pred})$. It preserves transitions but need not reflect them. A strict morphism would require equality, and that fails for `Scorer`: $\mathrm{Dep}(L,())=\{(Y,1)\}$ would force $r(L)=1$ and $r(Y,1)=0$, so $\mathrm{Dep}(Y,1)=\{(Z,1)\}$ would have to equal $\{m<0\}=\varnothing$, which is impossible (Chapter 5, Section 8.2).

- Running example: $r=0$ on the inputs, $r(Z,j)=1$, $r(Y,j)=2$, $r(L,())=3$. Check: $\mathrm{Dep}(Z,j)$ consists of inputs (0 < 1), $\mathrm{Dep}(Y,j)=\{(Z,j)\}$ (1 < 2), $\mathrm{Dep}(L)=\{(Y,1)\}$ (2 < 3).
- Finite history with $N=2$ and $d=1$: $r(X,0)=r(Z,0)=0$ and $r(H,(0,l))=l+1$, so $r(H,(0,0))=1$, $r(H,(0,1))=2$, $r(H,(0,2))=3$. Check: $\mathrm{Dep}(H,(0,0))=\{(X,0),(Z,0)\}$ (0 < 1), and $\mathrm{Dep}(H,(0,l+1))=\{(X,0)\}\cup\{(H,(0,l))\}$ (0 < l+2 and l+1 < l+2).
- Measure of the initial configuration on $\eta_1$: $\mu=|U|+|\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma|=7+5=12$.

## Q14

A blocked configuration is a running configuration that is not complete and has no enabled rule (Definition 5.7). A failed configuration is $\mathsf{Failed}(o,\dots)$, reached by UNDEFINED at a ready occurrence. It is terminal, and it proves that there is no model (Theorem 5.18(ii)). A blocked run proves nothing about models.

- Blocks with no model: `T[] = T[] + 1`. $\mathrm{Init}$ is blocked, and $\mathrm{Models}=\varnothing$ (Example 5.36).
- Blocks with a unique model: `T[] = X[]; T[] = 2 T[]`. The run consumes the contribution $T=X$ and then blocks, because the self-reading occurrence waits and PUBLISH waits for the pending writer. The model is $T=-X$ (Example 5.36).
- Blocks with many models: `T[] = T[]`. It is blocked at $\mathrm{Init}$, and every real is a model.

## Q15

| Categorical notion | Mini (`Course.`) | Production (`LeanNCD.Semantics.`) |
| --- | --- | --- |
| Pullback $f^\ast$ | `pullback` (Part A) | `pullback` (`Collection.lean`) |
| Pushforward $f_!$ | `pushforward` (Part A) | `pushforward` (`Collection.lean`) |
| Occurrences as coproduct $\mathcal O_P$ | `Program.Occ`, a sigma over statement positions (Part C) | `Program.Occurrence t`, a sigma per defined tensor over a guard subtype (`Program.lean`) |
| Destination $\mathrm{dst}$ | `Program.dst` | `Program.destination` |
| Kleisli interpretation | `evalWith`, `interpret` (Part C) | `evalWith`, `interpret` (`Interpret.lean`) |
| Collection | `Program.collect` (Part C) | `Program.collect` (`Program.lean`) |
| Equation operator $\Phi_P$ | `Program.equationOperator` (Part C) | `Program.equationOperator` (`Models.lean`) |
| Model relation | `Program.Models`, with `models_fixedpoint` (Part C) | `Program.Models` (`Models.lean`) |
| Step relation | `Program.Step`, constructors `contribute`, `publish`, `undefined` (Part D) | `Program.Step`, constructors `contribute`, `publication`, `undefined` (`Machine.lean`) |
| Termination measure | `Program.measure`, with `measure_decreases` (Part D) | `Program.measure`, `Program.step_wellFounded` (`Measure.lean`) |

The production column is taken from the notes' Chapter 6 tables, and I could not check it against the production files.

## Q16

`recip` is used because Lean has no computable logarithm on $\mathbb Q$, and `#eval` and `decide +kernel` need computation (Chapter 6, Section 3.6). `recip q` is `none` at $q=0$ and `some (1/q)` otherwise.

The substitution is faithful for the question asked because of this property: on the nonnegative reals, both primitives are undefined exactly at $0$. A model forces $Y=\mathrm{relu}(Z)\ge0$, so at every model the body of `s4` is defined exactly when $Y[1]\neq0$, for both primitives.

- On $\eta_0$, the equations force $Y[1]=0$, so both bodies are undefined and there is no model.
- On $\eta_1$, $Y[1]=4$, so both bodies are defined. The values differ, $1/4$ against $\log 4$.

The domains do differ. `recip` is defined on $\mathbb Q\setminus\{0\}$ and $\log$ on $(0,\infty)$, so a negative $Y[1]$ is admissible for `recip` and not for $\log$. That changes $\mathrm{AdmEnv}$, but a model never has $Y[1]<0$, so the difference does not reach $\mathrm{Models}$ or $\mathrm{AdmInput}$. Chapter 6, Section 3.6 makes the same argument, and the Lean comment on `s4` gives the domain point only briefly.

## Where the notes were unclear

- **Chapter 5, Section 9.2 (Example 5.33, paragraph after the table).** The sentence listing other maximal runs is garbled. It reads "Other maximal runs fail earlier, at the same occurrence: $(s_1,1)$, $(s_2,1)$, PUBLISH $(Z,1)$, $(s_3,1)$, PUBLISH $(Y,1)$, UNDEFINED is a six-step maximal run that never publishes $Z[0]$ or $Y[0]$." The list is not a sequence of steps, "fail earlier at the same occurrence" is self-contradictory, and the six-step run is never written out. I could not reconstruct it.
- **Chapter 6, Section 3.8 (closing paragraph of the fuel discussion).** It repeats "fail earlier at that same occurrence". The same problem.
- **Chapter 5, Section 9.4 (Example 5.35, the schedule discussion).** "The first row is three machine steps: six CONTRIBUTE and three PUBLISH steps in all." It is unclear whether "first row" means the first table row (three contributions) or the whole schedule (nine steps, $\mu=9$). The arithmetic is consistent with the second reading.
- **Chapter 7, Section 4, item 5, against Chapter 5, Section 8 and Remark 5.23.** The rank target is written $(\mathbb N,<)$ in Chapter 7. Chapter 5 writes $(\mathbb N,\mathrm{pred})$ and identifies it with Chapter 0's $(\mathbb N,>)$. I read these as the same target, but the notation is inconsistent.
- **Index notation, Chapter 1, Sections 2.5 and 3, and Chapter 1, Section 2.1 grammar.** The notes write $T[0\cdot i]$ with a dot, and the grammar lists $c\,e$ for integer $c$. The question sheet writes $T[0i]$. Juxtaposition is not defined in the notes.
- **Chapter 7, Section 1, Theorem 31.3.** The three parts are cited as (a), (b) and (c), and Example 7.2 and Exercise 5 refer to parts (b) and (c). The notes never state the three parts. I inferred them from the prose: (a) a decoded success implies a singleton model set, (b) a matched failure implies an empty model set, and (c) the converse in the error-free profile. This is an inference, not a quotation.
- **Chapter 7, Example 7.2.** The rule that a block must not be published before all its writers are accumulated is given without a worked example. The sentence pointing to a specification example says that example "is about duplicate statements, not about the running example". I could not check it.
- **Chapter 7, Section 2 (status table preamble).** The notes say the table reflects a 2026-10-10 snapshot, but also say slice 4 was merged on 2026-10-12, and the table includes a slice 5 row. The notes say the date "is not a reliable cut-off". So I cannot tell which Lean results are current.
- **Chapter 6, Section 3.8, item 4.** "This matches Example 4.8" is stated for values that differ: the Lean body gives $1/4$ and the notes give $\log 4$. The difference is hedged only in parentheses.
- **Chapter 3, Section 3, and Chapter 4, Section 6.3.** Several claims rest on the categorical notes (Section 6.3 for the executed batching experiment, Section 9.3 for Example 4.30's original reciprocal version), and many cross-references point into `papers/semantics/`. Those sources were outside the permitted reading, so those claims are unverified here.
- **Chapter 3, Section 2, and Exercise 1.** The categorical product in $\mathbf{Pfn}$ is stated as $A\sqcup B\sqcup(A\times B)$ in the text and asked as an exercise, with no proof in the text. I did not need it for these answers.

## Self-assessment

Least confident: Q15 (the production column rests only on the notes' Chapter 6 tables, which I could not check against the production files), then Q4 (the index notation and whether $T[0i]$ is read as $T[0\cdot i]$) and Q10 (the exact form of the composite apex and which hypothesis each proof uses).
