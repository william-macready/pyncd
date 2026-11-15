# Answers to question set B (student C)

Conventions: $K=\mathbb{R}$ unless stated; "Prop/Def/Thm/Lemma n.m" refer to the course chapters. I read README, Chapters 0 to 5 and the Lean companion. I did not read Chapters 6 and 7 (see the last section).

## Q1

Statement: `Y[i+j] = A[i] B[j]`, $i\in[2]$, $j\in[3]$, $Y$ of extent 5, $A=(1,2)$, $B=(1,1,1)$.

**(a)** The context is $\Gamma=(i:[2],j:[3])$ and there is no guard, so $D=[2]\times[3]$ and the statement has $|D|=6$ occurrences (Def 1.8: occurrences are pairs $(s,\nu)$, one per admissible valuation). The write map is $\phi(i,j)=i+j$. Its fibres:

| address $(Y,k)$ | fibre |
| --- | --- |
| 0 | $\{(0,0)\}$ |
| 1 | $\{(0,1),(1,0)\}$ |
| 2 | $\{(0,2),(1,1)\}$ |
| 3 | $\{(1,2)\}$ |
| 4 | $\varnothing$ |

Sizes $1+2+2+1+0=6$ (Prop 1.9). $\phi$ is not injective (fibres of size 2, so not mono in $\mathbf{FinSet}$: collisions) and not surjective (coordinate 4 is never written, so not epi: it collects $0_K$). This is the "neither" row of the Chapter 2 table, Section 1, for extent 4 or more.

**(b)** The body at $(i,j)$ is $A[i]B[j]$, giving $\theta(0,0)=1,\theta(0,1)=1,\theta(0,2)=1,\theta(1,0)=2,\theta(1,1)=2,\theta(1,2)=2$. Then $Y=\phi_!\theta$ (Def 2.6, collection as dst-pushforward, Def 2.14 and Def 4.6):

$Y[0]=1$, $Y[1]=1+2=3$, $Y[2]=1+2=3$, $Y[3]=2$, $Y[4]=0$ (empty sum $=0_K$). So $Y=(1,3,3,2,0)$.

**(c)** No index is contracted. The contracted set of the term is $C=\mathrm{FV}(t)\setminus\mathrm{vars}(\Gamma_s)$ (Section 2.3 of Ch 1), and here $\Gamma_s$ is built from the variables of the output indices, which are $i$ and $j$ (both occur in `i+j`). So $C=\varnothing$ and the body $A[i]\otimes B[j]$ contains no reduction $\bigoplus$.

The difference is where the sum lives. In a contraction such as `Z[j] = W[j,i] X[i]` the sum over $i$ is inside the body of one occurrence per $j$ (a nested reduction, $(\mathrm{pr}_s)_!$, the inner factor of $\pi_{\rm out}=\phi_s\circ\mathrm{pr}_s$ in Prop 2.13); the write map $\phi_s$ is then injective (identity). Here $\mathrm{pr}_s=\mathrm{id}$ (no contracted context), every body is a single product, and the sum comes entirely from collection, i.e. from the outer pushforward $\phi_!=\mathrm{dst}_!$ over the non-injective write map (Prop 2.7(2) factorization, Def 2.14). Equivalently: contraction sums inside a body, a collision sums across occurrences. The numbers agree with the single-pushforward einsum formula, but the occurrence counts (6 here, versus 1 per output coordinate for a contraction) and the machine behaviour (CONTRIBUTE count) differ.

**(d)** Transpose identity (Prop 2.8) with $f=\phi$, $u=\theta\in K^{[2]\times[3]}$, $w=\mathbf 1\in K^{[5]}$:
$\langle\phi_!\theta,\mathbf 1\rangle_{[5]}=\langle\theta,\phi^\ast\mathbf 1\rangle_{[2]\times[3]}$.
Right side: $\phi^\ast\mathbf 1$ is all ones on the 6 pairs, so it is $\sum\theta=1+1+1+2+2+2=9$. Left side: $\sum_kY[k]$ must be 9. Indeed $1+3+3+2+0=9$. (Also $9=(\sum A)(\sum B)=3\cdot3$.) No coordinate of $Y$ was recomputed.

## Q2

**(a)** $G$: the guard $i<j$ on $[3]\times[3]$ keeps $(0,1),(0,2),(1,2)$, so $D_G$ has 3 occurrences. $I$: no guard, $D_I=[3]\times[3]$, 9 occurrences (Def 1.8; Section 2.2 of Ch 1: guard removes valuations, Iverson factor keeps them all).

**(b)** Let $v=M:[3]^2\to\mathbb{R}$ and $m:D\hookrightarrow[3]^2$ the subobject of the guard (Def 2.2 table: a guard is a mono). With $\log=\mathrm{id}$ all bodies are total.

* $G$: occurrence family is $m^\ast v$ on $D$, destination map $!\circ m:D\to1$. Collected value $S_G=(!\circ m)_!(m^\ast v)=!_!\big(m_!m^\ast v\big)$ by functoriality, Prop 2.7(2).
* $I$: occurrence family is $\chi_D\otimes v$ on $[3]^2$, destination $!:[3]^2\to1$. $S_I=!_!(\chi_D\otimes v)$.

So it suffices to show $m_!m^\ast v=\chi_D\otimes v$. Pointwise at $p$: the fibre of $m$ over $p$ is $\{p\}$ if $p\in D$ and empty otherwise, so $(m_!m^\ast v)(p)=v(p)$ for $p\in D$ and $0_K$ otherwise (empty fibre gives $0_K$, Def 2.6), which is $\chi_D(p)\otimes v(p)$ using $1\otimes v=v$ and $0\otimes v=0$ (absorption). Hence $S_G=S_I$.

The identity relating $m_!m^\ast v$ to $\chi_D$ and $v$ is the projection formula $m_!(x\otimes m^\ast y)=m_!x\otimes y$ (Lemma 2.12c) taken with $x=\mathbf 1_D$ and $y=v$, and $m_!\mathbf 1=\chi_D$ (fibre cardinalities $0$ or $1$, mapped by $\kappa$ to $0_K,1_K$). It is the decategorified shadow of the set-level projection formula $\Sigma_f(A\times f^\ast B)\cong\Sigma_fA\times B$ (Chapter 2, Section 3, after Prop 2.8; "Frobenius reciprocity"), which is also the ingredient behind the transpose identity.

**(c)** Take $M$ with $M[i,j]>0$ for $i<j$ and $M[1,0]=-1$, for instance $M=\begin{pmatrix}1&1&1\\-1&1&1\\1&1&1\end{pmatrix}$. $G$ evaluates $\log$ only at the three upper-triangle entries, all $>0$: unique model $S=3\log1=0$. In $I$ the occurrence $(i,j)=(1,0)$ has body $\mathbf 1_{1<0}\otimes\log(-1)=0\otimes\bot=\bot$ (strict pairing, Example 3.16(2), Example 3.18). That body reads only the input $M$, so no environment extending $M$ is admissible and $\mathrm{Models}(I,M)=\varnothing$ (as in Example 4.33).

General relation: as partial maps $\mathrm{Env}(\mathrm{In})\rightharpoonup\mathrm{Env}(\mathrm{Out})$, $[\![I]\!]\preceq[\![G]\!]$ (definedness order, Def 3.12), strictly. Whenever $I$ is defined, all nine entries are in the domain of $\log$, so $G$ is defined and, by the computation of (b) with $\log$ restored (the indicator kills the extra terms), has the same value. The converse fails (the $M$ above). So replacing a guard by an Iverson factor shrinks definedness; the guard is the more defined program.

## Q3

**(a)** $X=(2,0,4,0)$.
* P1: reads $X[0]=2$, $X[2]=4$, both nonzero. $Y=(1/2,1/4)$. $\mathrm{Models}(P1,X)=\{(X,Y=(1/2,1/4))\}$.
* P2: the $R$-statement has occurrences $k=0,1,2,3$. At $k=1$ and $k=3$ the body is $\mathrm{recip}(0)=\bot$ and reads only the input, so no extension of $X$ is admissible: $\mathrm{Models}(P2,X)=\varnothing$ (no output).

$X=(2,1,4,1)$.
* P1: $Y=(1/2,1/4)$, one model.
* P2: $R=(1/2,1,1/4,1)$ is forced and defined; $Y[i]=R[2i]$ gives $Y=(1/2,1/4)$. One model (as a complete environment it also contains $R$, so it is not literally the same set of environments as P1's; the outputs agree).

**(b)** Let $r:[2]\to[4]$, $r(i)=2i$, and $f=\mathrm{recip}$. Then P1 $=\mathrm{batch}_{[2]}(f)\circ r^\ast$ (select the read coordinates, then apply $f$) and P2 $=r^\ast\circ\mathrm{batch}_{[4]}(f)$ (build $R$, i.e. $f$ on all four coordinates, then gather). Lax naturality (Prop 3.13, with $J=[4]$, $I=[2]$):
$$[\![P2]\!]=r^\ast\circ\mathrm{batch}_{[4]}(f)\ \preceq\ \mathrm{batch}_{[2]}(f)\circ r^\ast=[\![P1]\!].$$
The equality case needs $f$ total or $r$ surjective. Both hypotheses fail: $\mathrm{recip}$ has domain $\ne0$ (not total) and $r$ is injective with image $\{0,2\}\ne[4]$ (not surjective, which is exactly the situation of Example 3.14: injective is not enough). The strictness is witnessed by $X=(2,0,4,0)$.

**(c)** Not meaning-preserving. The rewrite replaces the left side of the lax square by the right side, which can turn $\bot$ into a value and never the reverse. Observably: on $X=(2,0,4,0)$, P2 has no model and the reference machine ends in $\mathsf{Failed}$ (the occurrences $(R,k{=}1)$ and $(R,k{=}3)$ are ready from the start, since their footprints are inputs, and take UNDEFINED; Thm 5.18(ii): $\mathrm{Models}=\varnothing$, outputs not returned; which occurrence is reported depends on the schedule, Prop 5.30). P1 succeeds with $Y=(1/2,1/4)$. So the denotation's domain $\mathrm{AdmInput}$ changes (P2's contains the condition $X[1]\ne0\wedge X[3]\ne0$, P1's does not). On inputs where P2 does succeed, the successful run has $6+6=12$ steps ($\mu=|U|+|\mathrm{Addr}_{\rm Def}|=6+6$) while P1's has $2+2=4$, so the observation "number of steps" also differs.

"Nothing reads $R[1]$ or $R[3]$" is true but is not the relevant criterion: unread values still have occurrences, and every present occurrence must be defined (Def 4.4 and its remark; "undefined is not zero"). Dropping a computation whose result is unused is naturality of discard, which is false in $\mathbf{Pfn}$ (Prop 3.6; the "Why this matters" remark after Example 3.7: dead-code elimination is not an equation unless the dropped subterm is shown total on the inputs at hand). The rewrite would be valid only with a separate proof that $X[1],X[3]\ne0$.

## Q4

Merged statement `s12: Z[j] = W[j,i] X[i] + B[j]`.

**(a)** Core form, $\Gamma=(j:[2])$, term-local contraction (Section 2.3 of Ch 1):
$$\text{for }j\in[2]:\quad Z[j]\mathrel{+}=\Big(\bigoplus_{i\in[2]}W[j,i]\otimes X[i]\Big)\oplus B[j].$$
$i$ is contracted only in the first term; the bias is added once per $j$, not once per $i$.

**(b)** Let $v_1(j)=\bigoplus_iW[j,i]\otimes X[i]$ and $v_2(j)=B[j]$ (both total on every complete environment, since they apply no partial primitive).

* Original: occurrences $(s1,j)$ and $(s2,j)$ with the same destination $(Z,j)$. By grouping (Prop 2.7(4), Prop 4.7(1)) the collected value is $\mathrm{id}_!v_1\oplus\mathrm{id}_!v_2=v_1\oplus v_2$ (using $\mathrm{id}_!=\mathrm{id}$, Prop 2.7(2)).
* Merged: one occurrence $(s12,j)$ with value $v_1(j)\oplus v_2(j)$, collected value $\mathrm{id}_!(v_1\oplus v_2)=v_1\oplus v_2$.

So $\mathrm{Collect}$ agrees on $Z$ for every candidate $\rho$; the equations for $Y$ and $L$ are untouched. The law used is additivity of the pushforward ($f_!$ is a monoid homomorphism, Prop 2.7(1)) together with grouping over the coproduct of statements (2.7(4)). The relabeling law 2.7(3) is not enough because it needs a bijection of occurrence sets, and here the sets have 7 and 5 elements: merging is not a bijection (it is the sum of two contributions made into one summand, not a renaming).

Admissibility: strict lifting (Def 3.5, $\mathrm{lift}_2(\oplus)$) makes the merged body defined iff both operands are defined, i.e. iff both original occurrences $(s1,j)$, $(s2,j)$ are defined; and the other occurrences are unchanged. So $\mathrm{AdmEnv}$ is unchanged (here trivially, both bodies are total). Hence $\mathrm{Models}(P_{12},\eta)=\mathrm{Models}(P,\eta)$ as sets of complete environments for every $\eta$, the witness spans are equal (identity on the apex), and by Prop 4.24 the denotations agree.

**(c)** Occurrences: $2$ ($s12$) $+\,2$ ($s3$) $+\,1$ ($s4$) $=5$. Initial measure $\mu=|U|+|\mathrm{Addr}_{\rm Def}\setminus\mathrm{dom}\,\sigma|=5+5=10$. A successful maximal run has $5$ CONTRIBUTE $+\,5$ PUBLISH $=10$ steps (originally $7+5=12$).

**(d)** Differences visible even though the models agree: the occurrence set ($|\mathcal O|$ 5 versus 7), the initial measure and run length (10 versus 12), the per-statement contribution tensors ($V_{s12}=(0,4)$ versus $V_{s1}=(-1,4)$ and $V_{s2}=(1,0)$), the intermediate accumulators (e.g. $\alpha(Z,0)$ goes $-1\to0$ originally, but $0$ in one step now; no zero-valued separate consumption of $(s2,1)$), the read footprint of each occurrence (the merged one reads the union, so readiness could be later in general; here all inputs are published at Init), the set of possible schedules, and which occurrence is reported on a failure when bodies are partial. The dependency sets $\mathrm{Dep}(Z,j)$ and rank certificates are the same.

**(e)** `Z[j] = W[j,i] (X[i] + B[j])`: the term contains $i$ and $j$, $i$ is contracted in this one term, so the body is $\bigoplus_iW[j,i]\otimes(X[i]\oplus B[j])$. On $\eta_1$ ($W=\begin{pmatrix}1&1\\2&-1\end{pmatrix}$, $X=(1,-2)$, $B=(1,0)$):
* $j=0$: $1\cdot(1+1)+1\cdot(-2+1)=2-1=1$.
* $j=1$: $2\cdot(1+0)+(-1)(-2+0)=2+2=4$.

So $Z=(1,4)$, not $(0,4)$. The bias is inside the contraction and gets multiplied by the row sum: $Z[j]=(WX)[j]+B[j]\sum_iW[j,i]$ (row sums $2$ and $1$; this is the "bias added once per $i$" bug of Section 2.3 in weighted form). Consequently $Y=(1,4)$ and $Y[0]$ differs from the correct $0$; $L=\log4$ happens to agree. The elaboration rules never distribute $\otimes$ over $\oplus$ for you; the two programs are different.

## Q5

`T[] = X[]; T[] = -1 * recip(T[])`.

**(a)** Collected equation: $T=X\oplus(-1)\cdot\mathrm{recip}(T)=X-1/T$, with the second body defined iff $T\ne0$ (so $\mathrm{AdmEnv}=\{T\ne0\}$). Fixed points: $T^2-XT+1=0$, and $T=0$ is never a root (value 1), so admissibility is automatic. Hence
$$\mathrm{Models}(P,X)=\Big\{T=\tfrac{X\pm\sqrt{X^2-4}}2\Big\}$$
(each model is the complete environment $(X,T)$). Number of models: 2 if $|X|>2$; 1 (a double root, $T=X/2=\pm1$) if $|X|=2$; 0 if $|X|<2$. It is an equalizer in the sense of Prop 4.12; no least fixed point is chosen.

**(b)** $\mathrm{AdmInput}(P)=\{X:\text{exactly one model}\}=\{2,-2\}$ (Def 4.14), and $[\![P]\!](2)=(T=1)$, $[\![P]\!](-2)=(T=-1)$ (check $-2-1/(-1)=-1$). Undefined elsewhere.

**(c)** $W_P=\{(X,T):T^2-XT+1=0,\,T\ne0\}$. Since $X=T+1/T$ is determined by $T$, $W_P\cong\mathbb{R}\setminus\{0\}$ via $T$, with $\ell(T)=T+1/T$ and $r(T)=T$, i.e. $\mathbb{R}\xleftarrow{T+1/T}\mathbb{R}^\times\xrightarrow{\mathrm{id}}\mathbb{R}$. The left leg is not monic: $T$ and $1/T$ have the same image (e.g. $2$ and $1/2$ both give $X=5/2$); it is injective only on $\{\pm1\}$ pairs, i.e. fails to be monic everywhere else. Its image is $\{X:|X|\ge2\}=(-\infty,-2]\cup[2,\infty)$ (inputs with at least one model). By Prop 4.27 the span is therefore not the graph of a partial function; $[\![P]\!]$ keeps only the singleton fibres at $X=\pm2$.

**(d)** The reference machine. Init: $\mu=2+1=3$. $\mathrm{Dep}(T,())=\{(X,()),(T,())\}$ contains $(T,())$ itself, so a cycle and no rank certificate (Prop 5.26). For every $X$ the run is the same: CONTRIBUTE the occurrence of `T = X` (value $X$), then the occurrence `T = -1 recip(T)` has footprint $\{(T,())\}$, not published, so it waits, and PUBLISH of $(T,())$ needs no pending occurrence, so it waits too. The configuration is blocked (neither success nor failure; Def 5.7, Example 5.36 analogue). $X=1$ (no model), $X=2$ (one model), $X=3$ (two models) all block after one step.

$X=1$ does not end in $\mathsf{Failed}$ because UNDEFINED requires a *ready* occurrence whose evaluation is $\bot$ (Def 5.6); the second occurrence is never ready, as waiting is not $\bot$ (Def 3.24 table). "No model" implies failure only for ranked programs (Thm 5.28(3)); in general only the implication "failed run $\Rightarrow$ no model" holds (Thm 5.18(ii), Remark 5.19). The machine does not select a root of a cycle.

## Q6

`P: inputs x; defined h,y; outputs y; h[]=h[]; y[]=x[]` and `Q: z[]=recip(y[])`.

**(a)** Equations: $h=h$ (every $h$ works; admissible, bodies total), $y=x$. So $\mathrm{Models}(P,x)=\{(x,h=t,y=x):t\in\mathbb{R}\}$, a copy of $\mathbb{R}$ for every $x$. The span: $W_P\cong\mathbb{R}\times\mathbb{R}$ (coordinates $(x,h)$), $\ell(x,h)=x$, $r(x,h)=y=x$; $\mathrm{Env}(\mathrm{In})=\mathrm{Env}(\mathrm{Out})=\mathbb{R}$. The relation $\{(\ell(w),r(w))\}=\{(x,x)\}$ is the diagonal, the graph of the total identity function, so it is a function. But $[\![P]\!]$ is defined nowhere: every fibre $\ell^{-1}(x)\cong\mathbb{R}$ has more than one element, so $\mathrm{AdmInput}(P)=\varnothing$ (Def 4.14, Example 4.15).

**(b)** $W_Q=\{(y,z):y\ne0,\,z=1/y\}\cong\mathbb{R}^\times$. The composite span (Def 0.29/2.10, Thm 4.22) has apex the pullback $W_P\times_{\mathrm{Env}(y)}W_Q=\{((x,h),(y,z)):x=y,\,y\ne0,\,z=1/y\}\cong\mathbb{R}^\times\times\mathbb{R}$ (coordinates $(x,h)$ with $x\ne0$), $\ell(x,h)=x$, $r(x,h)=1/x$. (Equivalently the glued program $P;Q$ has $\mathrm{Fix}(P;Q)\cong\{(x,h,y{=}x,z{=}1/x):x\ne0\}$; fibrewise form Cor 4.23: $\coprod_{\rho_P\in\mathrm{Models}(P,x)}\mathrm{Models}(Q,x)$.) Every fibre over $x\neq 0$ is a copy of $\mathbb{R}$ and the fibre over $0$ is empty, so $\mathrm{AdmInput}(P;Q)=\varnothing$ and $[\![P;Q]\!]$ is the nowhere-defined partial function, even though the composite input-output relation is the graph of $x\mapsto1/x$ on $x\ne0$. (It agrees with the Kleisli composite $[\![Q]\!]\circ[\![P]\!]$, which is also nowhere defined, but only by coincidence: $\mathrm{AtMostOneModels}(P)$ fails, so Prop 4.28 does not apply.)

**(c)** The machine on $P$: $\mathrm{Dep}(h)=\{(h,())\}$, a self-cycle. Init $\mu=2+2=4$. The occurrence of `y = x` is ready, CONTRIBUTE; then PUBLISH $(y,())$; the occurrence of `h = h` waits for $(h,())$ and PUBLISH $h$ waits for that occurrence. After 2 steps the run is blocked ($\mu=2$), for every $x$: never success, never failure (like Example 5.36 row 2). The published $y$ is not returned: blocked is not success.

**(d)** $P'$: `x` input, `y[]=x[]`. $W_{P'}\cong\mathbb{R}$ with $\ell=r=\mathrm{id}$. Apexes $\mathbb{R}^2$ versus $\mathbb{R}$, and fibres over a point of size continuum versus 1, so no bijection commutes with $\ell$: the spans are not isomorphic. The output relations are both the diagonal. $[\![P']\!]$ is the total identity; $[\![P]\!]$ is nowhere defined. This is Example 4.25 (private multiplicity). It shows that "same input-output relation" is too coarse an equivalence: it does not determine the denotation, whereas span isomorphism does and is preserved by composition (Prop 4.24); this is why the notes choose span isomorphism (Section 6.2). The private tensor $h$ cannot be deleted for free.

## Q7

**(a)** Occurrences: $(b1,c{=}0)$ and $(b1,c{=}1)$ (write maps $c\mapsto(0,c)$), $(b2,r{=}0)$ and $(b2,r{=}1)$ (write maps $r\mapsto(r,0)$), and $(b3,())$: the context of $b3$ is empty (both variables contracted), so one occurrence. Total 5. Fibres:

| address | fibre |
| --- | --- |
| $(T,(0,0))$ | $\{(b1,0),(b2,0)\}$ |
| $(T,(0,1))$ | $\{(b1,1)\}$ |
| $(T,(1,0))$ | $\{(b2,1)\}$ |
| $(T,(1,1))$ | $\varnothing$ |
| $(S,())$ | $\{(b3,())\}$ |

Values: $T[0,0]=C[0]+R[0]=2+7=9$, $T[0,1]=C[1]=3$, $T[1,0]=R[1]=5$, $T[1,1]=0$ (empty fibre). $S=\sum_{r,c}T[r,c]^2=81+9+25+0=115$.

**(b)** $\mu(\mathrm{Init})=|U|+|\mathrm{Addr}_{\rm Def}|=5+5=10$. A successful maximal run has 5 CONTRIBUTE and 5 PUBLISH steps (including an explicit PUBLISH of $(T,(1,1))=0$). The earliest address that can be published is $(T,(1,1))$, at step 1: its fibre is empty so PUBLISH is enabled at $\mathrm{Init}$ (Section 3.2). (The first one with a nonempty fibre could be published at step 2, e.g. after CONTRIBUTE of $(b1,1)$, and $(T,(0,1))$ has no other writer.)

**(c)** After consuming only $(b1,c{=}0)$: $\alpha(T,(0,0))=0\oplus2=2$ (the barrier is not met, $(b2,0)$ pending). $b3$ is not ready: its footprint is all four addresses of $T$ (reduction reads everything under the binder, Def 3.20), and none is published.

**(d)** $r=0$ on $C,R$; $r(T,p)=1$ for all four $p$; $r(S,())=2$. Check: $\mathrm{Dep}(T,(0,0))=\{(C,0),(R,0)\}$, $\mathrm{Dep}(T,(0,1))=\{(C,1)\}$, $\mathrm{Dep}(T,(1,0))=\{(R,1)\}$, $\mathrm{Dep}(T,(1,1))=\varnothing$ (ranks $0<1$), $\mathrm{Dep}(S)=$ all four $T$ addresses ($1<2$). It is a lax morphism into $(\mathbb{N},\mathrm{pred})$ (Def 5.25).

**(e)** With storage zero-initialized and readable at any time, $b3$ may read a partially accumulated $T$. Possible outputs: the corner holds $0,2,7$ or $9$ (squares $0,4,49,81$), the cell $T[0,1]$ holds $0$ or $3$, $T[1,0]$ holds $0$ or $5$, and $T[1,1]=0$; so $S=\mathrm{corner}^2+\{0,9\}+\{0,25\}$, for example $0$ (read at start), $4+0+0=4$, $81+9+0=90$, and only $81+9+25=115$ is correct. This violates the readiness premise of CONTRIBUTE, $\mathrm{Read}(o)\subseteq\mathrm{dom}\,\sigma$ (published values only; accumulators are not readable and an absent coordinate is not zero), and that is only sound because PUBLISH's barrier $U\cap\mathcal C_P(a)=\varnothing$ guarantees that published means complete. The implementation has effectively published every $T$ coordinate early (and published $T[1,1]$ implicitly instead of by the explicit PUBLISH of an empty fibre).

## Q8

**(a)** Max-plus: $\oplus=\max$, $\otimes=+$. $(f_!v)(0)=\max(v_0,v_2)=\max(5,11)=11$, $(f_!v)(1)=v_1=7$, so $f_!v=(11,7)$. $f^\ast w=w\circ f=(w_0,w_1,w_0)=(2,3,2)$. Pairing $\langle u,v\rangle=\max_i(u_i+v_i)$.
LHS: $\langle f_!v,w\rangle=\max(11+2,7+3)=13$. RHS: $\langle v,f^\ast w\rangle=\max(5+2,7+3,11+2)=13$. Equal (Prop 2.8; max-plus is a commutative semiring).

**(b)** Max-plus: yes. In the fibre $\mathcal C(a)$ the two copies of the statement contribute the same value in every $\rho$ (same body, same destination, same definedness), and $x\oplus x=x$, so $\mathrm{Collect}$, $\mathrm{AdmEnv}$ and hence $\mathrm{Models}$ are unchanged. This is not a relabeling (the occurrence sets are not in bijection, Prop 2.7(3) does not apply); what is used is idempotence of $\oplus$ inside the pushforward, as for the Boolean sort (remark after Prop 4.7). Over $(\mathbb{R},+,\times)$: no. The duplicate adds a second summand; deleting it changes the collected value (Example 4.31: $T=(4,10)$ versus $(2,5)$, and Prop 4.7(4)). Definedness obligations are identical in both sorts; only the sum differs.

**(c)** Let $K$ be idempotent and $a\le b\iff a\oplus b=b$. This is a partial order: reflexive ($a\oplus a=a$), antisymmetric (commutativity), transitive (associativity); $x\le x\oplus y$ because $x\oplus(x\oplus y)=x\oplus y$; $0_K$ is bottom ($0\oplus w=w$); and if each $x_k\le w$ then $(\bigoplus_kx_k)\oplus w=w$ (induct; empty family: $0\oplus w=w$), so $\oplus$ is a join.

($\Rightarrow$) Suppose $f_!u\le w$. For each $i$, $u_i\le\bigoplus_{f(i')=f(i)}u_{i'}=(f_!u)(f(i))\le w(f(i))=(f^\ast w)(i)$. ($\Leftarrow$) Suppose $u_i\le w(f(i))$ for all $i$. For each $j$, every $u_i$ with $f(i)=j$ is $\le w_j$, so the join over the fibre is $\le w_j$ (empty fibre: $0_K\le w_j$). So $f_!u\le w$. $\square$

Categorically: viewing the posets $(K^I,\le)$ and $(K^J,\le)$ as categories, this is the hom-set bijection of an adjunction $f_!\dashv f^\ast$ (a Galois connection; the same shape as Example 0.7: left adjoint to a restriction functor). For the Boolean sort, $K^I=\mathcal P(I)$ with $\oplus=\vee$ and order inclusion; $f_!$ is direct image $U\mapsto f[U]$ and $f^\ast$ is preimage $W\mapsto f^{-1}[W]$, and the statement is $f[U]\subseteq W\iff U\subseteq f^{-1}[W]$.

Relation to Thm 2.4: Thm 2.4 gives $\Sigma_f\dashv f^\ast$ on set-valued families. Under decategorification into the Boolean sort ($\kappa(n)$ = "$n>0$", Section 3 of Ch 2) $\Sigma_f$ becomes $f_!$ and $f^\ast$ stays $f^\ast$, and the adjunction survives as this Galois connection. So for idempotent sorts the shadow of Thm 2.4 really is an adjunction, whereas for $\mathbb{R}$ only the transpose identity (Prop 2.8) survives, which the notes explicitly say is not an adjunction.

Over $(\mathbb{R},+,\times)$ it does not hold. With the relation $a\oplus b=b$ is $a+b=b$, i.e. $a=0$, which is not even reflexive (not a preorder). With the usual order on $\mathbb{R}$ it fails too: $f:[2]\to[1]$, $u=(-1,3)$, $w=2$: $f_!u=2\le2$ but $u\not\le(2,2)$.

## Q9

**(a)** Run of the modified machine on `Scorer` with $\eta_0$ ($X=(0,0)$): $(Z,j)$: all pending occurrences (s1,s2) are ready and defined, so LENIENT-PUBLISH adds their values and publishes $Z=(1,0)$. $(Y,j)$: $(s3,j)$ becomes ready, defined, publishes $Y=(1,0)$. $(L,())$: the unique occurrence $(s4,())$ is ready (it reads $(Y,1)$, now published as $0$); its body $\log0$ is undefined so its value is simply not added; it is removed from $U$ and $(L,())$ is published with $\alpha=0$. The configuration is complete with $Z=(1,0)$, $Y=(1,0)$, $L=0$. The modified machine returns $Y=(1,0)$, $L=0$: a success (Example 4.1, "undefined is zero").

**(b)** Theorem 5.18(i) (a successful run gives the unique model) fails: this run succeeds with $\rho_\sigma$, but $\mathrm{Models}(\mathrm{Scorer},\eta_0)=\varnothing$ (Example 4.13). The step of its proof that breaks is "Admissibility: every occurrence is consumed, so by item 5 (Lemma 5.14) every body is defined with value $v_o$": an occurrence removed from $U$ by the lenient rule has no recorded value, item 5 and the accumulator formula $\alpha(a)=\bigoplus_{o\in\mathcal C(a)\setminus U}v_o$ no longer hold (the invariant is not preserved), so $\rho_\sigma\in\mathrm{AdmEnv}$ fails (Lemma 5.14 item 5 and conservation). Consequently Theorem 5.28 also fails for ranked programs (`Scorer` is ranked, (3) says every maximal run fails when no model exists, here it succeeds), and the failed-run theorem 5.18(ii) becomes vacuous: no failed configuration exists, so there is no certificate of "no model".

On inputs that do have a model, the theorem still holds: let $\rho$ be a model. By induction $\sigma\sqsubseteq\rho$ along the run (Lemma 5.16(b)); a ready occurrence evaluates to $[\![E_s]\!]_{\rho,\nu}$ by read stability, which is defined because $\rho\in\mathrm{AdmEnv}$. So the lenient rule never actually skips anything, the run is a run of the original machine, and a successful run yields the unique model (Thm 5.18(i)). The failure is exactly on model-less inputs, which is where silent skipping matters.

**(c)** One sentence: $\bot$ is not a scalar and not $0_K$, so an undefined body can neither contribute nothing nor be skipped; a ready undefined body must stop the run in an explicit failure.

## Q10

**(a)** (Added to the inductive type: `| iverson {Γ : Type} (q : Γ → Bool) : Expr d K Γ`.)

```lean
-- in evalWith
  | _, .iverson q, γ => some (if q γ then 1 else 0)
-- in footprint
  | _, .iverson _, _ => []
```

The first uses the semiring `1` and `0` already available under `[Semiring K]`; it is total and mentions no store. The second says the Iverson factor reads nothing (Def 3.20: $\mathbf 1_Q$ has empty footprint, and the predicate depends on indices only).

**(b)** Claim: if `q γ = false` then `evalWith σ (.mul (.iverson q) e) γ = none ↔ evalWith σ e γ = none`.

Proof. Unfold `evalWith` at `.mul`: it is `do let x ← evalWith σ (.iverson q) γ; let y ← evalWith σ e γ; pure (x * y)`. By the new clause, with `q γ = false` the first bind is `some 0`, which binds to `0`. So the whole is `do let y ← evalWith σ e γ; pure (0 * y)`, i.e. `(evalWith σ e γ).map (fun y => 0 * y)`. Case split on `evalWith σ e γ`: if it is `none`, the result is `none`; if it is `some y`, the result is `some (0 * y)`, which is not `none`. Hence the result is `none` iff `evalWith σ e γ = none`. (No law about `0 * y` is used; only that the factor is `some` and the bind is strict.) $\square$

Semantic point: a zero Iverson factor does not remove the obligation that the other factor be defined; $0\otimes\bot=\bot$ because strict pairing is not cartesian and $0_K$ is a successful value, not the zero morphism (Example 3.16(2), Prop 3.6, Example 3.18). This is why an Iverson factor and a guard are different: the factor leaves the occurrence present and its body must be defined.

**(c)** The mini development expresses a guard by the choice of the statement's valuation space: `Stmt.n` is "the number of admissible valuations $|D_s|$", `dest : Fin n → ...`, and `body : Expr d K (Fin n)`, with the comment "guards are applied by choosing `n` and the enumeration" (production: the valuation type with a Boolean guard subtype). The guard is the subobject $D_s\hookrightarrow\mathrm{Val}(\Gamma_s)$ restricting the index set before any body exists; excluded valuations are not occurrences and their bodies are never evaluated. So no expression constructor is needed (and one could not recover the same behaviour from `iverson`, since that acts inside `Option` and cannot cancel an undefined body, as (b) shows).

## Where the notes were insufficient

* Chapter 2, Section 4 (Prop 2.13) and Chapter 1, Section 2.3: the proposition is stated for output tuples of variables; the Q1(c) discussion of a collision (affine output) uses the factorization $\pi_{\rm out}=\phi_s\circ\mathrm{pr}_s$ with $\mathrm{pr}_s=\mathrm{id}$, which I assembled from Prop 2.7(2), Def 2.14 and the Section 2.3 rule for $C_b$. The notes never state explicitly "a collision sum is collection, a contraction sum is the body reduction".
* Chapter 2, Section 3 (after Prop 2.8) says that for idempotent sorts "the situation is different; the course does not treat it". Q8(c) (and the Boolean/max-plus remarks of Q8(b)) asks precisely that. I derived the Galois connection from scratch; the notes give no result to cite besides Example 0.7 and Thm 2.4, and the claim that the Boolean $\kappa$ makes $\Sigma_f$ into direct image is only implicit (Section 3: "$\kappa(n)$ is $n>0$").
* Chapter 2, Section 2/3 and Lemma 2.12c: the identity $m_!m^\ast v=\chi_D\otimes v$ (Q2(b)) is not stated; I derived it from Lemma 2.12c with $x=\mathbf 1$. Likewise $m_!\mathbf 1=\chi_D$ is not stated.
* Chapter 3, Prop 3.13 and Section 5: batching is stated for values and an index map $r$. Using it for the program-level comparison of P1 and P2 in Q3 requires reading the intermediate defined tensor $R$ with single-writer fibres as plain $\mathrm{batch}$ followed by $r^\ast$; the notes do this only for the expression-level $\mathrm{at}(\mathrm{tab}(\cdot))$ and do not say how a defined-but-unread tensor in a program (with $\mathrm{Models}$ including $R$) relates. There is also no explicit statement about dead-code elimination of an unread *defined tensor* (only of subterms, Prop 3.6 remark); I applied that by analogy.
* Chapter 4: the notes treat deleting a duplicate (Prop 4.7(4), Example 4.31) but not merging two statements into one (Q4). The needed laws (2.7(1), 2.7(4)) are present, and the admissibility argument via strict $\mathrm{lift}_2$ (Def 3.5), but the combination is mine. The notes also do not say what happens to the witness span under a statement-level rewrite; I concluded identity on the apex from set equality of the models.
* Chapter 4, Section 5 and Chapter 5: "number of models" for a cyclic equation (Q5) is not covered beyond the three examples of Example 4.16; I computed the quadratic.
* Chapter 5, Def 5.6/Section 3.2 and Q7(b): "the earliest step at which some address can be published" is ambiguous about step numbering (Init is "step 0" in Example 5.32, so the first action is step 1); I answered step 1 by the empty-fibre PUBLISH. Also Q7(e) has two candidate violated premises (CONTRIBUTE readiness, and the PUBLISH barrier that makes "published" mean "complete"); the notes' phrase "an executor must not read an accumulator / treat an absent coordinate as zero" covers it but not in one named rule premise.
* Chapter 5, Thm 5.18/5.28 and Q9(b): the notes do not discuss modified rules, so which theorem "fails" depends on the reading. I named 5.18(i) (the proof breaks at admissibility via Lemma 5.14 item 5) and noted that 5.28(3) and 5.28(4) also fail; the statement that 5.18(i) still holds on inputs with a model is my own induction using Lemma 5.16(b), which is stated for the original machine.
* Chapter 5, Remark 5.19 vs Exercise 8 and Prop 5.37 table: the table's "exactly $\{\rho\}$: succeeds or blocks" row is formulated for programs "without a certificate" but Exercise 8 says such programs never succeed; slightly confusing. Not needed for the answers.
* Chapter 0 (Section 4, Example 0.19) and the Lean file: the Lean companion uses `recip` in place of `log` in `s4`, so $L=1/4$ rather than $\log 4$; this is stated in the file but contradicts the prose values of Chapters 1 and 4 if one reads the file alone.
* The Lean companion has no `iverson` constructor and no guard (the file says so), and Chapter 6, which would explain extending it, was not read by me. Q10 therefore relied on the file's `evalWith`/`footprint`, the Chapter 3 description of production `Expr.iverson`, and the `Stmt` doc-comment on guards.
* I did not read Chapters 6 (the Lean dictionary) or 7 (outlook); any facts that appear only there would not have been available to me.
