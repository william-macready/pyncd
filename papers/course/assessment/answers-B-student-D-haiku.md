# Answers to question set B (student D, Haiku 5.5)

Sources used: `questions-B.md`, `papers/course/README.md`, chapters 00 to 07, and `lean/MiniTensorLogic.lean`. I did not open any other assessment file, the specification, or `leanncd/`, and I did not run Lean. Chapter numbers below refer to the course files, for example "Ch 2 §3" is `02-index-categories.md`, section 3.

## Q1. Colliding writes

**(a)** The output index is $i+j$, which contains both variables, so $\Gamma_s=(i{:}[2],\,j{:}[3])$ and there is no guard. By Def 1.8 and Def 2.14, $\mathcal O_P=D_s=[2]\times[3]$, so there are $|\mathcal O_P|=6$ occurrences.

Write map $\varphi(i,j)=i+j\in[5]$. Fibres:

- $\varphi^{-1}(0)=\{(0,0)\}$
- $\varphi^{-1}(1)=\{(0,1),(1,0)\}$
- $\varphi^{-1}(2)=\{(0,2),(1,1)\}$
- $\varphi^{-1}(3)=\{(1,2)\}$
- $\varphi^{-1}(4)=\varnothing$

The sizes are $1+2+2+1+0=6$. $\varphi$ is not injective (two fibres have two points) and not surjective (4 is not hit). This is the "neither" row of the Ch 2 §1 table, for a colliding write.

**(b)** The summand family on the occurrence set is $\theta(i,j)=A[i]\otimes B[j]$, with values $1,1,1$ on $i=0$ and $2,2,2$ on $i=1$. Collection is $Y=\varphi_!\,\theta$ (Def 2.6, Def 2.14, Def 4.6):

$$Y[0]=1,\quad Y[1]=1+2=3,\quad Y[2]=1+2=3,\quad Y[3]=2,\quad Y[4]=0\ (\text{empty fibre}).$$

So $Y=(1,3,3,2,0)$.

**(c)** No index is contracted. The contracted set of a term is $C_b=\mathrm{FV}(t_b)\setminus\mathrm{vars}(\Gamma_s)$ (Ch 1 §2.3), and both $i$ and $j$ are output variables, so $C_b=\varnothing$. The body has no $\oplus$. The sum comes from collection: distinct occurrences $(s,(i,j))$ share the destination $(Y,k)$, and $\varphi_!$ adds their values (Ch 2 §1, the remark after the table; Ch 2 §5). In a true contraction such as $Z[j]=W[j,i]X[i]$, the sum over $i$ sits inside one occurrence body, so the occurrences are indexed by $j$ alone (Ch 1 §3, Prop 2.13). Here the machine needs 6 CONTRIBUTE steps, not 2.

**(d)** Prop 2.8 with $f=\varphi$, $u=\theta$, $w=\mathbf 1\in\mathbb R^{[5]}$:

- Left: $\langle\varphi_!\theta,\mathbf 1\rangle=\sum_k Y[k]=9$.
- Right: $\varphi^\ast\mathbf 1$ is the all-ones family on $[2]\times[3]$, so $\langle\theta,\varphi^\ast\mathbf 1\rangle=\sum_{i,j}A[i]B[j]=(\sum_i A[i])(\sum_j B[j])=3\cdot3=9$.

The two sides agree. The check is weak, though: it tests only the total. It would not notice that $Y[1]$ and $Y[2]$ were swapped. A coordinate-wise transpose check with an indicator $\delta_k$ reduces to the definition of $\varphi_!$, so it adds nothing. I rely on the hand computation in (b) for the coordinates.

## Q2. A guard over two variables

I read the `for` binders as part of $\Gamma_s$ (Ch 1 Def 1.7 and §2.5: the binders belong to the statement and survive cancellation). This reading is the main uncertainty in this answer; see the insufficiency list.

**(a)** G: $D=\{(i,j)\mid i<j\}=\{(0,1),(0,2),(1,2)\}$, so **3 occurrences**. I: $D=[3]^2$, so **9 occurrences**.

**(b)** Let $v=M\in\mathbb R^{[3]\times[3]}$. Let $m\colon D\hookrightarrow[3]^2$ be the inclusion, a mono (Ch 2 §1, the guard row). Let $\chi_D=m_!\mathbf 1_D$ be the Iverson indicator. Both programs write one address $(S,())$, with write map to the point $1$.

- G: $S_G=(!_D)_!(m^\ast v)=\sum_{x\in D}v(x)$.
- I: $S_I=(!)_!(\chi_D\otimes v)=\sum_{x\in[3]^2}\chi_D(x)\,v(x)$.

The identity needed is
$$m_!\,m^\ast v=\chi_D\otimes v.$$
Proof: Lemma 2.12c, the decategorified projection formula $h_!(x\otimes h^\ast y)=(h_!x)\otimes y$, with $h=m$, $x=\mathbf 1_D$, $y=v$. Because $m$ is injective, every fibre of $m$ has at most one point, so $m_!\mathbf 1_D=\chi_D$, and the right side is $\chi_D\otimes v$. Then $(!)_!(m_!m^\ast v)=(!\circ m)_!(m^\ast v)=(!_D)_!(m^\ast v)$ by Prop 2.7(2) (functoriality). Hence $S_I=S_G$ for every $M$.

The result this is the decategorified form of is the **projection formula** $\Sigma_f(A\times f^\ast B)\cong\Sigma_fA\times B$ (Ch 2 §3, the set-level statement). Its $K$-valued form is Lemma 2.12c. I applied it with $A=\mathbf 1$ over the subobject $D$.

**(c)** Take
$$M=\begin{pmatrix}0&1&1\\1&1&1\\1&1&1\end{pmatrix}.$$
- G has occurrences $(0,1),(0,2),(1,2)$, each with body $\log 1=0$, all defined. Its unique model has $S=0$.
- I has the occurrence $(0,0)$ with body $0\otimes\log 0=0\otimes\bot=\bot$ (Ex 3.16(2)). The body reads only the input, so no candidate extending $M$ is admissible (Def 4.4). $\mathrm{Models}(I,M)=\varnothing$.

General relation. The extra bodies of I, at $(i,j)\notin D$, are $0\otimes\log M[i,j]$. By strictness (Ch 3 Def 3.5) they are defined iff $\log M[i,j]$ is defined. So
$$\mathrm{dom}[\![I]\!]=\{M\mid \log M[i,j]\text{ defined for all }(i,j)\}\ \subseteq\ \mathrm{dom}[\![G]\!]=\{M\mid \log M[i,j]\text{ defined for }i<j\},$$
and the two values agree on $\mathrm{dom}[\![I]\!]$. In the definedness order of Ch 3 Def 3.12, $[\![I]\!]\preceq[\![G]\!]$: the Iverson program is the restriction of the guarded program to a smaller domain. Turning an Iverson factor into a guard is a rewrite that makes the program more defined. It is sound only if the removed bodies are total (Ch 3 §5, transformation limits; Ex 3.18).

## Q3. Gather through a partial map

Data: $X$ has extent 4. P1 is $Y[i]=\mathrm{recip}(X[2i])$ for $i\in[2]$. P2 is $R[k]=\mathrm{recip}(X[k])$ for $k\in[4]$, followed by $Y[i]=R[2i]$.

**(a)**

- $X=(2,0,4,0)$. P1 has occurrences at $i=0,1$ reading $X[0]=2$ and $X[2]=4$. Both are defined, so $Y=(1/2,\,1/4)$ with a unique model. P2 has occurrences $(R,1)$ and $(R,3)$, whose bodies $\mathrm{recip}(X[1])$ and $\mathrm{recip}(X[3])$ are $\mathrm{recip}(0)=\bot$ for every candidate. No candidate is admissible (Def 4.4), so $\mathrm{Models}=\varnothing$ and P2 has no output.
- $X=(2,1,4,1)$. P1 gives $Y=(1/2,1/4)$. P2 gives $R=(1/2,1,1/4,1)$ and $Y=(R[0],R[2])=(1/2,1/4)$. Both have a unique model with the same output.

**(b)** Let $r\colon[2]\to[4]$, $r(i)=2i$, and let $r^\ast a=a\circ r$ (Ch 2 Def 2.6, in the form used by Ch 3 Prop 3.13). Then
$$\text{P1}=\mathrm{batch}_{[2]}(\mathrm{recip})\circ r^\ast,\qquad \text{P2}=r^\ast\circ\mathrm{batch}_{[4]}(\mathrm{recip}).$$
Prop 3.13 with $I=[2]$, $J=[4]$, $f=\mathrm{recip}$ gives $r^\ast\circ\mathrm{batch}_J(f)\preceq\mathrm{batch}_I(f)\circ r^\ast$, that is, $[\![\text{P2}]\!]\preceq[\![\text{P1}]\!]$. P2 (restrict after batching) is less defined than P1 (batch after restricting).

The equality clause of Prop 3.13 needs "$f$ total or $r$ surjective". Both fail. $\mathrm{recip}$ is not total (undefined at 0). The map $r$ has image $\{0,2\}\neq[4]$, so it misses exactly the coordinates 1 and 3. On $X=(2,1,4,1)$ the two sides agree only because the omitted coordinates happen to be defined.

**(c)** The rewrite is not meaning-preserving. Def 4.4 requires every occurrence body to be defined, and "nothing reads $R[1]$" is a fact about reads, not about definedness. The occurrence $(R,1)$ has body $\mathrm{recip}(X[1])$. Dropping it changes the denotation from "no model" to "output defined" on inputs where the dropped body is undefined. This is the rewrite that Ch 3 §2 forbids: a subterm may be dropped only when it is total on the inputs at hand.

Observable change on the reference machine. On $X=(2,0,4,0)$, P2 reaches UNDEFINED at $(R,1)$ or $(R,3)$. Those occurrences are ready because their footprints $\{X[1]\}$ and $\{X[3]\}$ are published, so the run fails (Ch 5 Def 5.6, Thm 5.18(ii)). P1 runs to completion with $Y=(1/2,1/4)$. Which of the two failing occurrences is reported depends on the schedule (Ch 5 §10).

## Q4. Merging statements

**(a)** The merged statement has one term with a reduction and one term without, so the term-local rule of Ch 1 §2.3 applies. Its core form is
$$\text{for } j\in[2]:\qquad Z[j]\mathrel{+}=\Big(\bigoplus_{i\in[2]}W[j,i]\otimes X[i]\Big)\oplus B[j].$$
The bias is added once per $j$, not once per $i$.

**(b)** Let $O=O_{s1}\sqcup O_{s2}$ (4 occurrences), with body values $c_1(j)$ and $c_2(j)$ at the two statements. Let $p\colon O\to[2]$, $o\mapsto j$, forget the statement tag. The destination of every occurrence is $(Z,j)$, so $\mathrm{dst}=\mathrm{id}\circ p$ on the $Z$ addresses. The merged program has occurrence set $O'=[2]$, body $c'(j)=c_1(j)\oplus c_2(j)$, and destination the identity.

Collection of the original, by Prop 2.7(2) (functoriality), is $\mathrm{dst}_!c=p_!c$. The fibre of $p$ over $j$ has exactly two points, so by Def 2.6 and grouping (Prop 2.7(4)), $(p_!c)(j)=c_1(j)\oplus c_2(j)=c'(j)$. So the collected values are the same, and the merged program writes the same value to each $(Z,j)$.

The law used is therefore functoriality of pushforward through the statement-forgetting map, with the fibre split by statement. Relabeling (Prop 2.7(3)) does not apply: it needs a bijection $O\cong O'$, and $|O|=4\neq2=|O'|$. Merging is a many-to-one reindexing, which is a pushforward and not a relabeling.

Admissibility is unchanged. The merged body is defined iff both original bodies are, because a strict sum is defined only when both summands are (Ch 3 Def 3.5, $\mathrm{lift}_2$). $\mathrm{AdmEnv}$ is the set where every body is defined (Def 4.4), so it is the same set. $\Phi_P$ and $\mathrm{Models}$ depend only on $\mathrm{AdmEnv}$ and $\mathrm{Collect}$ (Defs 4.9, 4.11), so the model sets agree for every input, and the spans are isomorphic (Prop 4.24).

**(c)** The merged program has $|D_{s12}|+|D_{s3}|+|D_{s4}|=2+2+1=5$ occurrences and 5 defined addresses. Initially $\mu=|U|+|\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma|=5+5=10$ on $\eta_1$ (Lemma 5.21). Each CONTRIBUTE lowers $|U|$ by one and each PUBLISH lowers the unpublished count by one. A successful run ends with both at 0, so it has exactly $5+5=10$ steps: 5 CONTRIBUTE and 5 PUBLISH. The merged dependency graph is acyclic ($Z\leftarrow W,X,B$; $Y\leftarrow Z$; $L\leftarrow Y$), so Thm 5.28 applies and every maximal run succeeds.

**(d)** The models agree, but the machine traces do not:

- The run has 10 steps instead of 12, with 5 CONTRIBUTE steps instead of 7.
- The statement identity of each contribution changes, so any diagnostic that names a statement changes. A failing body in one summand would be reported at different occurrences in the two programs.
- The accumulator trajectory differs. In the original, $\alpha(Z,0)$ goes $-1$, then $0$. In the merged program it becomes $0$ at its single contribution. Ch 5 §10 lists accumulator values as schedule- and structure-dependent quantities, not invariants of the denotation.
- The store recorded in a failed configuration can differ (Ch 5 Def 5.7).

The denotation and span are the same (Prop 4.24). Operational traces are not invariant under this change, so "same models" is strictly weaker than "same run".

**(e)** The surface form $W[j,i](X[i]+B[j])$ is a product with a sum inside it, which is outside the surface fragment (Ch 1 §2.6). The notes say such a body must be written directly in core. The core form is $\bigoplus_i W[j,i]\otimes(X[i]\oplus B[j])$, because the notes give no implicit distribution (Ch 1 §2.4). The bias is therefore weighted by $W$ and summed over $i$:
$$Z[j]=\sum_i W[j,i]X[i]+B[j]\sum_i W[j,i].$$
On $\eta_1$:

- $Z[0]=1\cdot(1+1)+1\cdot(-2+1)=2-1=1$
- $Z[1]=2\cdot(1+0)+(-1)\cdot(-2+0)=2+2=4$

So $Z=(1,4)$, while the correct $Z=(0,4)$. $Y[0]=\mathrm{relu}(1)=1$ is also wrong, but $Y[1]=4$ is not, so $L=\log4$ happens to be correct. The error is that the bias is counted inside the contraction, weighted by each $W[j,i]$. Ch 1 §2.3 warns about counting the bias once per summed index; this variant weights it instead.

## Q5. A cyclic equation with a partial primitive

Collected equation: $T=X+(-1)\cdot\mathrm{recip}(T)$, that is, $T=X-1/T$. The two occurrences are s1 with value $X$ and s2 with value $-\mathrm{recip}(T)$ (Def 4.6). $\mathrm{AdmEnv}$ requires $T\ne0$.

**(a)** $\mathrm{Models}(P,X)=\{T\in\mathbb R\setminus\{0\}\mid T^2-XT+1=0\}$. The discriminant is $X^2-4$, so:

- $|X|>2$: two models, $T=(X\pm\sqrt{X^2-4})/2$. Their product is 1, so neither is 0.
- $|X|=2$: one model, $T=X/2$.
- $|X|<2$: no model.

**(b)** $\mathrm{AdmInput}(P)=\{-2,2\}$ (Def 4.14). $[\![P]\!](2)=1$ and $[\![P]\!](-2)=-1$. It is undefined elsewhere.

**(c)** $W_P=\{(X,T)\mid X=T+1/T,\ T\neq0\}$, which is bijective with $\mathbb R\setminus\{0\}$ via $T\mapsto(T+1/T,\,T)$. The legs are $\ell(T)=T+1/T$ and $r(T)=T$.

The left leg is **not monic**. For example $\ell(2)=\ell(1/2)=5/2$. Its fibres have size 2 over $|X|>2$, size 1 over $X=\pm2$, and size 0 for $|X|<2$. By Prop 4.27 the span is not the graph of a partial function. The image of $\ell$ is $\{|X|\ge2\}$, which is strictly larger than $\mathrm{AdmInput}=\{\pm2\}$. The right leg $r$ is injective.

**(d)** Initially the input $X$ is published and $U=\{s1,s2\}$.

- s1 is ready, because its footprint $\{X\}$ is published. CONTRIBUTE gives $\alpha(T)=X$.
- s2 reads $T$. Its footprint $\{T\}$ is never published, so s2 never becomes ready. Waiting is not $\bot$ (Ch 3 Def 3.24), so s2 is never evaluated.
- PUBLISH of $T$ is blocked by the pending writer s2 (Def 5.6).

No rule is enabled and $U\neq\varnothing$, so the configuration is **blocked** for $X=1$, $X=2$ and $X=3$.

For $X=1$ the run does not fail because UNDEFINED needs a ready occurrence whose body is $\bot$. s2 is never ready, so its body is never evaluated. The machine says nothing about whether a model exists; Ch 5 Remark 5.19 says a blocked run carries no information about models.

For $X=2$ and $X=3$ the run also blocks, even though a model exists for $X=2$. The dependency $T\in\mathrm{Dep}(T)$ is a cycle, so there is no rank certificate (Prop 5.26). Ch 5 §6 says a program with a dependency cycle never succeeds on any input, citing Exercise 8, so the blocked outcome is forced. This matches the first row of Ex 5.36.

## Q6. A private free tensor

**(a)** $\mathrm{Models}(P,x)$ consists of $\rho=(x,h,y)$ with $y=x$ and $h$ arbitrary. The equation $h=h$ has every real as a fixed point, and collection of $y$ gives $x$ (Prop 4.7). So $\mathrm{Models}(P,x)\cong\mathbb R$ and $W_P\cong\mathbb R_x\times\mathbb R_h$.

The relation $\{(\ell(w),r(w))\}$ is $\{(x,x)\}$, the identity relation. It is a function. But every fibre is infinite, so $\mathrm{AdmInput}(P)=\varnothing$ and $[\![P]\!]$ is defined nowhere (Def 4.14). A relation that is a function does not give a denotation.

**(b)** Composability holds: $\mathrm{In}_Q=\{y\}=\mathrm{Out}_P$ (Def 4.20). By Thm 4.22 the apex of the composite is
$$W_P\times_{\mathbb R}W_Q=\{((x,h),(y,z))\mid x=y\neq0,\ z=1/y\}\cong(\mathbb R\setminus\{0\})\times\mathbb R,$$
with legs $\ell(x,h,z)=x$ and $r(x,h,z)=z=1/x$. The relation is $x\mapsto1/x$ on $x\neq0$. But every fibre over $x\neq0$ still contains a copy of $\mathbb R$ (the free $h$), so $\mathrm{AdmInput}(P;Q)=\varnothing$ and $[\![P;Q]\!]$ is nowhere defined. The Kleisli composite $[\![Q]\!]\circ[\![P]\!]$ is also empty, because $[\![P]\!]$ is empty. This is the failure that Prop 4.28 and Ex 4.30 predict when $\mathrm{AtMostOneModels}(P)$ fails.

**(c)** On $P$, CONTRIBUTE of $s_y$ is enabled, since its footprint $\{x\}$ is published. It gives $\alpha(y)=x$, and then PUBLISH of $y$ is enabled, since no writer of $y$ is pending. The statement $s_h$ reads $h$, which is never published, so $s_h$ never becomes ready. PUBLISH of $h$ is blocked by the pending writer $s_h$. No rule applies, the run is not complete, and the outcome is **blocked**. The published $y$ is not a successful output (Ch 5 Def 5.7).

**(d)** $P'$ has $W_{P'}\cong\mathbb R$, with one point over each $x$. $W_P\cong\mathbb R^2$, with a copy of $\mathbb R$ over each $x$. Both input-output relations are the identity. The spans are not isomorphic, because an apex bijection commuting with the left legs would have to send each fibre $\mathbb R$ bijectively onto a point. The denotations differ: $[\![P']\!]$ is the identity and total, while $[\![P]\!]$ is nowhere defined.

So the relation-level equivalence would identify two programs with different meanings. This is why the notes use span isomorphism (Ch 4 §6.2, Prop 4.24, and Ex 4.25). The mechanism is the same as Ex 4.25, with $T=T^2$ replaced by $h=h$, which gives a continuum of witnesses instead of two points.

## Q7. A boundary program on the machine

Occurrences: b1 has $D=[2]$ (occurrences $(b1,0),(b1,1)$). b2 has $D=[2]$ (occurrences $(b2,0),(b2,1)$). b3 contracts both $r$ and $c$ and has no output index, so $\Gamma_s=()$ and it has one occurrence $(b3,())$. Total: 5 occurrences.

**(a)** Write maps: $\phi_{b1}(c)=(0,c)$, $\phi_{b2}(r)=(r,0)$, $\phi_{b3}=\mathrm{pt}$. Fibres of the defined addresses:

- $(T,(0,0))$: $\{(b1,0),(b2,0)\}$
- $(T,(0,1))$: $\{(b1,1)\}$
- $(T,(1,0))$: $\{(b2,1)\}$
- $(T,(1,1))$: $\varnothing$
- $(S,())$: $\{(b3,())\}$

Values: $T[0,0]=C[0]+R[0]=2+7=9$, $T[0,1]=C[1]=3$, $T[1,0]=R[1]=5$, and $T[1,1]=0$ (empty fibre). Then
$$S=\bigoplus_{r,c}T[r,c]\otimes T[r,c]=81+9+25+0=115.$$

**(b)** $\mu_0=|U|+|\mathrm{Addr}_{\mathrm{Def}}|=5+5=10$. A successful maximal run has 5 CONTRIBUTE and 5 PUBLISH steps, so 10 steps in total (Lemma 5.21, as in Q4(c)).

The earliest possible publication is step 1. The address $(T,(1,1))$ has an empty fibre, so PUBLISH is enabled from the start (Ch 5 §3.2). The first address with a writer can be published at step 2: contribute $(b1,1)$ or $(b2,1)$ at step 1, then publish its address at step 2.

$S$ is always published last, at step 10. Its only writer $(b3,())$ reads all four $T$ addresses, so $b3$ cannot contribute until those four addresses are published. The four $T$ publications and the four $T$ contributions take 8 steps, so $b3$ contributes at step 9 at the earliest, and $S$ is published at step 10.

**(c)** After only $(b1,c{=}0)$, $\alpha(T,(0,0))=C[0]=2$. This is the formula of Lemma 5.14, since the only consumed writer of $(T,(0,0))$ is $(b1,0)$. The occurrence $b3$ is **not ready**: its footprint is the four $T$ addresses, none of which is published.

**(d)** Rank certificate. The dependency sets (Def 5.24) are:

- $\mathrm{Dep}(T,(0,0))=\{(C,0),(R,0)\}$, $\mathrm{Dep}(T,(0,1))=\{(C,1)\}$, $\mathrm{Dep}(T,(1,0))=\{(R,1)\}$, $\mathrm{Dep}(T,(1,1))=\varnothing$
- $\mathrm{Dep}(S,())=\{(T,(r,c))\mid r,c\in[2]\}$

Take $r=0$ on inputs, $r=1$ on the four $T$ addresses, and $r=2$ on $(S,())$. Then $b\in\mathrm{Dep}(a)$ implies $r(b)<r(a)$ (Def 5.25, Prop 5.26). The program is ranked, so Thm 5.27 and 5.28 apply.

**(e)** The implementation reads $T$ at any time, so each $T[r,c]$ holds a partial accumulator. The possible values are $T[0,0]\in\{0,2,7,9\}$, $T[0,1]\in\{0,3\}$, $T[1,0]\in\{0,5\}$, and $T[1,1]=0$. So
$$S\in\{a^2+b^2+c^2\mid a\in\{0,2,7,9\},\ b\in\{0,3\},\ c\in\{0,5\}\}=\{0,4,9,13,25,29,34,38,49,58,74,81,83,90,106,115\}.$$
The correct value 115 appears only when all three fibres are complete ($a=9$, $b=3$, $c=5$).

The violated premise is the readiness premise $\mathrm{Read}(o)\subseteq\mathrm{dom}\,\sigma$ of CONTRIBUTE (Def 5.6). Reading an unpublished address is not the ready evaluation $\mathrm{Eval}_\sigma$ (Def 3.24). Zero-initialised storage that is read as a value also violates the rule that an absent coordinate is not zero (Ch 5 §1 table, and Def 5.4 where zero accumulators are not readable).

## Q8. Other sorts

**(a)** Max-plus: $\oplus=\max$, $\otimes=+$, $0_K=-\infty$.

- $f_!v(0)=\max(v(0),v(2))=\max(5,11)=11$, and $f_!v(1)=v(1)=7$, so $f_!v=(11,7)$.
- $f^\ast w=(w(f(0)),w(f(1)),w(f(2)))=(2,3,2)$.
- Left side: $\langle f_!v,w\rangle=\max(11+2,\ 7+3)=13$.
- Right side: $\langle v,f^\ast w\rangle=\max(5+2,\ 7+3,\ 11+2)=13$.

The identity holds (Prop 2.8, with $\langle u,v\rangle=\max_i(u(i)+v(i))$).

**(b)** Over max-plus, yes: deleting one of two identical statements preserves the model set. Collection is the $\oplus$-sum over each fibre (Def 4.6). Two copies of the same value $v$ give $\max(v,v)=v$, the same as one copy. The two copies also have identical definedness obligations, so $\mathrm{AdmEnv}$ is unchanged. This is the argument of Ch 4 §3 for the Boolean sort, which is also idempotent.

Over $(\mathbb R,+,\times)$, no. Two copies give $2v$. Ex 4.31 gives $(4,10)$ against $(2,5)$.

In both sorts the occurrence set and the CONTRIBUTE count still differ, so the machine traces differ (Ch 4 Exercise 6).

**(c)\*** Order $K$ by $a\le b\iff a\oplus b=b$, and order $K^I$ pointwise.

1. This is a partial order. It is reflexive by idempotence. It is antisymmetric: $a\oplus b=b$ and $b\oplus a=a$ give $a=b$. It is transitive: $a\oplus b=b$ and $b\oplus c=c$ give $a\oplus c=a\oplus b\oplus c=b\oplus c=c$.
2. $\oplus$ is the join: $a\le a\oplus b$, and if $a,b\le c$ then $(a\oplus b)\oplus c=a\oplus c=c$.
3. $0_K$ is least, since $0\oplus a=a$.

So for a finite sum, $\bigoplus_{i\in S}x_i\le c$ iff $x_i\le c$ for every $i\in S$. The empty sum $0_K$ is below everything.

Now $f_!u\le w$ iff, for every $j$, $\bigoplus_{f^{-1}(j)}u(i)\le w(j)$, iff for every $j$ and every $i\in f^{-1}(j)$, $u(i)\le w(j)$, iff for every $i$, $u(i)\le w(f(i))=(f^\ast w)(i)$, iff $u\le f^\ast w$. The third equivalence holds because each $i$ lies in exactly one fibre.

Categorically, $K^I$ and $K^J$ are thin categories (posets). The iff says $f_!\dashv f^\ast$, a Galois connection in which $f_!$ is the left adjoint. Left adjoints preserve joins, which matches $f_!(u\oplus u')=f_!u\oplus f_!u'$ (Prop 2.7(1)).

For the Boolean sort, $\oplus=\vee$, $\otimes=\wedge$, and $\mathrm{false}\le\mathrm{true}$. Then $f_!$ is the existential image $U\mapsto f(U)$ on subsets, and $f^\ast$ is the preimage $W\mapsto f^{-1}(W)$. The statement becomes $f(U)\subseteq W\iff U\subseteq f^{-1}(W)$.

This is the $\kappa$-shadow of Theorem 2.4. Ch 2 §3 says that $\kappa$ transports $|\Sigma_fA|=f_!|A|$ and $|f^\ast B|=f^\ast|B|$, and Theorem 2.4 gives $\Sigma_f\dashv f^\ast$ on set-valued families. The notes do not show that this transport preserves the adjunction, so I proved the order statement directly.

Over $(\mathbb R,+,\times)$ it fails. The relation $a\le b\iff a+b=b$ is not a partial order, since reflexivity fails unless $a=0$. With the usual order, take $I=[2]\to J=[1]$, $u=(1,1)$, $w=(1.5)$. Then $f_!u=2\not\le1.5$, but $u\le f^\ast w=(1.5,1.5)$. The reason is that $+$ is not the join for the usual order.

Check on (a): with $w'=(11,7)$, $f_!v=(11,7)\le w'$ and $v\le f^\ast w'=(11,7,11)$, which is consistent with the equivalence.

## Q9. A broken rule

**(a)** Start from $\eta_0$, with $X=(0,0)$, all 7 occurrences pending, and inputs published.

- $Z[0]$: both pending writers $(s1,0)$ and $(s2,0)$ are ready and defined, with values $0$ and $1$. The rule gives $\alpha(Z,0)=1$, removes both, and publishes $Z[0]=1$.
- $Z[1]$: the values are $0$ and $0$, so $Z[1]=0$.
- $Y[0]=\mathrm{relu}(1)=1$ and $Y[1]=\mathrm{relu}(0)=0$ are published.
- $L$: the pending writer $(s4,())$ is ready, since $Y[1]$ is published. Its body $\mathrm{recip}(0)$ is undefined, so it is not added. The rule still removes it, since it says to remove "all of them". Then $\alpha(L)=0$, and $L=0$ is published.

Now $U=\varnothing$ and every address is published, so the run is **complete**, returning $Z=(1,0)$, $Y=(1,0)$, $L=0$. This is a successful outcome on $\eta_0$, and it is not a model: $\mathrm{Models}(\mathrm{Scorer},\eta_0)=\varnothing$ (Ex 4.13). The run never reaches UNDEFINED. I read "remove all of them" as including the undefined occurrences; the question does not settle this.

**(b)** Thm 5.18(i) fails: a successful run should return the unique model, but $\eta_0$ has no model. The breaking step is the admissibility line of its proof, "every occurrence is consumed, so by item 5 every body is defined". Item 5 of Lemma 5.14 (consumed occurrences have a recorded defined value, valid for every $\rho\in\mathrm{Ext}(\sigma)$) is the first invariant to fail, because $(s4,())$ is consumed without any defined value. The equation for $L$ is then the empty sum $0$, which is the "undefined is zero" error of Ex 4.1.

On inputs that have a model, the theorem still holds. Suppose $\rho$ is a model. Then every body is defined at $\rho$ (Def 4.4). By the inductive argument of Lemma 5.16(b), $\sigma\sqsubseteq\rho$ throughout the run. So each ready occurrence has $\mathrm{Eval}_\sigma=[\![E_s]\!]_\rho$, which is defined (Prop 3.22 and Def 3.24). The undefined branch of the new rule is therefore unreachable. The rule degenerates into "contribute everything, then publish", with the completion barrier intact, and Lemma 5.14 item 5 and Thm 5.18(i) go through.

Thm 5.18(ii) is vacuous for the modified machine, because it never fails. Lemma 5.16(c) also holds, since there are no failed states at all.

**(c)** The rule counts an occurrence whose body is undefined as nothing (zero), instead of stopping the run with an explicit failure, which violates the fact that $\bot$ is not zero and not a scalar (CONVENTIONS fact 3, Ch 3 §1; Ch 5 §1 table; Ch 1 §4.5).

## Q10. Extending the Lean companion

This answer is written on paper. I have not compiled it, because I was told not to run Lean.

**(a)** Add the constructor to `Expr`:

```lean
  | iverson {Γ : Type} (q : Γ → Bool) : Expr d K Γ
```

Add a clause to `evalWith`:

```lean
  | _, .iverson q, γ => some (if q γ then 1 else 0)
```

Add a clause to `footprint`:

```lean
  | _, .iverson _, _ => []
```

The footprint is empty because $\mathbf 1_Q$ reads no tensor (Ch 3 Def 3.20).

**(b)** Let $q\gamma=\mathrm{false}$ and let $m=\mathrm{evalWith}\ \sigma\ e\ \gamma$. Unfolding the `mul` clause, and using $\mathrm{evalWith}\ \sigma\ (\mathrm{iverson}\ q)\ \gamma=\mathrm{some}\ 0$, the left side is the bind $\mathrm{some}\,0\gg\lambda x.\,(m\gg\lambda y.\,\mathrm{some}(x\cdot y))$. By the left identity of the Option monad, this equals
$$m\ \gg=\ \lambda y.\ \mathrm{some}(0\cdot y).$$
The continuation $\lambda y.\,\mathrm{some}(0\cdot y)$ never returns `none`. So the bind is `none` iff $m$ is `none`:

- if $m=\mathrm{none}$, the bind is `none`;
- if $m=\mathrm{some}\ y$, the bind is $\mathrm{some}(0\cdot y)$, which is not `none`.

Hence $\mathrm{evalWith}\ \sigma\ (\mathrm{mul}\ (\mathrm{iverson}\ q)\ e)\ \gamma=\mathrm{none}\iff\mathrm{evalWith}\ \sigma\ e\ \gamma=\mathrm{none}$.

Untested Lean sketch of the same argument:

```lean
theorem iverson_zero_mul_none_iff [Semiring K] (σ : Addr d → Option K) {Γ : Type}
    (q : Γ → Bool) (e : Expr d K Γ) (γ : Γ) (hq : q γ = false) :
    evalWith σ (.mul (.iverson q) e) γ = none ↔ evalWith σ e γ = none := by
  cases h : evalWith σ e γ <;> simp [evalWith, hq, h]
```

The semantic point is that an Iverson factor is a total factor inside a strict pairing, and a total factor cannot cancel $\bot$. The product $0\otimes\bot$ is $\bot$ (Ch 3 Ex 3.16(2) and Ex 3.18). The definedness of the body is decided by $e$ alone, and multiplying by zero does not change it. A guard, by contrast, removes the valuation before the body is evaluated.

**(c)** The mini development has no guard constructor. A statement's admissible valuations are exactly the elements of `Fin n`, where `n` is the number of valuations (the `Stmt` structure in the file). A guard is expressed by choosing `n` and the enumeration of the surviving valuations. For example, `for i in [2] where i < 1: Y[i] += log(X[i])` becomes `n := 1`, `dest := fun _ => 0`, and `body := prim log (read X (fun _ => 0))`.

No new constructor is needed, because the removed valuations never enter `Fin n`. They have no occurrence, no body evaluation, and no footprint, so they carry no obligation. This matches the guard semantics of Ch 1 §2.2 and the remark in Ch 3 Ex 3.18 that the guard acts before the body enters $\mathbf{Pfn}$. An Iverson factor keeps the valuation, so it needs a term that multiplies, which is the new constructor.

The price is that a guard is not data in the mini. `Stmt` cannot state which valuations are removed. The author chooses the enumeration, and nothing checks it against a predicate. Production uses a guard subtype (Ch 6 §4).

## Where the notes were insufficient

1. **Ch 1 §2.3 against §2.5 and Def 1.7.** §2.3 says $\Gamma_s$ is "built from the variables in its output indices". Def 1.7 and §2.5 say the `for` binders are part of the statement, and the $T[0\cdot i]$ example keeps a binder that does not occur in the output. Q2 depends on this: the reading gives 3 and 9 occurrences, while the §2.3 reading would give 1 for each. I took the §2.5 reading.

2. **Ch 1 §2.4 and §2.6.** There is no example of a product containing a sum, such as $W[j,i](X[i]+B[j])$, and no statement of the core form for it. Q4(e) depends on the core form, which I inferred from §2.3 and from the absence of implicit distribution in §2.4.

3. **Ch 2 §5 and Ch 4 §3 (Prop 4.7).** The notes give laws for relabeling, grouping and deleting duplicates (which is not licensed). They give no law for merging two distinct statements with a summed body. Q4(b) rests on my derivation from Prop 2.7(2).

4. **Ch 2 §1, §3 and §4.** The identity $m_!\,m^\ast v=\chi_D\otimes v$ for a subobject (a guard) is not stated. The nearest results are the set-level projection formula (Ch 2 §3), which the notes say is "an extra property", and Lemma 2.12c inside the proof of Prop 2.12. I specialised Lemma 2.12c with $x=\mathbf 1_D$, and the identity is not named anywhere in the notes.

5. **Ch 2 §3, final paragraphs.** The notes say the course does not treat idempotent sorts as posets. Q8(c) asks exactly for that, so I built it from first principles. The notes give the Boolean sort's operations but not its order, and they do not say whether $f_!\dashv f^\ast$ holds for idempotent sorts.

6. **Ch 3 §2 and Ch 4 Def 4.4.** The notes discuss dead subterms ("dead-code elimination", Ch 3 §2) but not dead statements, which are whole writes that nothing reads. Q3(c) concerns a dead statement. I concluded from Def 4.4, that every occurrence imposes definedness, but the notes never state this for statements.

7. **Ch 3 §5 (transformation limits).** There is no general statement comparing a guard with its Iverson counterpart as partial maps. Only one instance appears, in Ex 3.18 and Ex 4.33. I derived $[\![I]\!]\preceq[\![G]\!]$ in general (Q2(c)).

8. **Ch 4 §6.3 (Prop 4.28, Ex 4.30).** The notes do not say what $[\![P;Q]\!]$ is when $\mathrm{AtMostOneModels}(P)$ fails and the span relation is nonempty but $\mathrm{AdmInput}(P;Q)$ is empty. Ex 4.30 treats a different case, where the composite has a unique model. I computed Q6(b) directly from Def 4.14 and Thm 4.22.

9. **Ch 5 §7 (Lemma 5.21).** The lemma gives only an upper bound on steps. The exact count $|\mathcal O_P|+|\mathrm{Addr}_{\mathrm{Def}}|$ for successful runs is stated only for `Scorer` under Thm 5.28. I derived the general count from the decrement facts in the lemma's proof (Q4(c), Q7(b)).

10. **Ch 5 §3 (the rules) and Lemma 5.16(c).** The notes discuss no rule that removes pending occurrences without a value. The reading of Q9's rule is mine, and the claim that Lemma 5.16(c) still holds for a modified rule set is my argument, not the notes'.

11. **Ch 6 §2.3 (the `Expr` row) against the `Stmt` comment in `MiniTensorLogic.lean`.** The chapter says the mini "has no guards". The Lean file says guards are applied by choosing `n` and the enumeration. The chapter does not explain this encoding, and Q10(c) depends on it.

12. **Ch 5 §6 caution and Exercise 8.** The claim that a program with a dependency cycle never succeeds is stated in the text and rests on Exercise 8, which the notes do not answer. Q5(d) depends on it for $X=2$ and $X=3$.

## Self-assessment

Least confident: Q2 (it depends on the binder reading in item 1 above) and Q8(c) (the notes do not cover idempotent sorts, so it is built from first principles). Q4(b) is also uncertain, because the merge law is my derivation rather than a named result.
