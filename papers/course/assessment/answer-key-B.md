# Assessment: answer key for question set B

Instructor use. Scoring 0, 1 or 2 per question; 20 total. A 2 needs every ✓
item; a 1 needs the computational items right and the categorical
explanation partly right. ✗ marks errors that cap the question at 1 (or 0
if central).

## Q1

✓ Six occurrences, one per $(i,j)\in[2]\times[3]$; both variables appear
in the output index, so both parameterize occurrences.
✓ Fibres: $k{=}0:\{(0,0)\}$; $k{=}1:\{(0,1),(1,0)\}$; $k{=}2:\{(0,2),(1,1)\}$;
$k{=}3:\{(1,2)\}$; $k{=}4:\varnothing$. Not injective (collisions at 1 and 2),
not surjective (4 is missed).
✓ $Y=\phi_!(v)$ with $v(i,j)=A[i]B[j]$: $Y=(1,\,1+2,\,1+2,\,2,\,0)=(1,3,3,2,0)$;
$Y[4]=0_K$ from the empty fibre.
✓ No index is contracted: the body has no reduction. The sums come from
collection (pushforward along the write map), not from a reduction in the
body.
✓ $\langle\phi_!v,\mathbf 1\rangle_{[5]}=\sum_kY[k]=9$ and
$\langle v,\phi^\ast\mathbf 1\rangle=\sum_{i,j}A[i]B[j]=(1+2)(1+1+1)=9$.
✗ treating $j$ (or $i$) as contracted; ✗ omitting $Y[4]$ or giving it a
value other than 0.

## Q2

✓ $G$: three occurrences, $(0,1),(0,2),(1,2)$. $I$: nine.
✓ For total $v(i,j)=M[i,j]$: $S_G=(!\circ m)_!(m^\ast v)=!_!(m_!m^\ast v)$ by
functoriality, and $m_!m^\ast v=\chi_D\otimes v$ because $m$ is injective
(each fibre of $m$ has at most one point, $m_!$ of the constant family 1 is
$\chi_D$). Hence $S_G=!_!(\chi_D\otimes v)=S_I$.
✓ The identity is the projection formula $m_!(m^\ast v\otimes u)=v\otimes m_!u$
with $u=\mathbf 1$, the decategorified Frobenius reciprocity
$\Sigma_m(A\times m^\ast B)\cong\Sigma_mA\times B$ that the notes use to
explain the transpose identity (Chapter 2, Section 3).
✓ Any $M$ with $M[i,j]>0$ for $i<j$ and some $M[i,j]\le0$ with $i\ge j$, for
example all ones except $M[0,0]=0$: $G$ has the model $S=0$; $I$ demands
$1_{0<0}\otimes\log0=0\otimes\bot=\bot$, so no model.
✓ $I\preceq G$: wherever $I$ has a (unique) model, $G$ has the same one; the
converse fails. Equality when the body is total.
✗ claiming the Iverson zero cancels $\bot$; ✗ the inequality reversed.

## Q3

✓ $X=(2,0,4,0)$: P1 has the unique model $Y=(1/2,1/4)$; P2 has no model,
since the occurrences $(R,1)$ and $(R,3)$ demand $\mathrm{recip}(0)$.
$X=(2,1,4,1)$: both have $Y=(1/2,1/4)$ (P2 with $R=(1/2,1,1/4,1)$).
✓ With $r:[2]\to[4]$, $i\mapsto2i$: P2 is $r^\ast\circ\mathrm{batch}_{[4]}(\mathrm{recip})$
and P1 is $\mathrm{batch}_{[2]}(\mathrm{recip})\circ r^\ast$; lax naturality
gives P2 $\preceq$ P1. $r$ is not surjective, and recip is not total;
equality holds exactly on inputs with $X[1],X[3]\neq0$.
✓ Not meaning-preserving: occurrences of a non-output tensor are still
demanded (admissibility ranges over all occurrences), so deleting them is
the non-natural discard of Chapter 3. The rewrite turns no-model inputs
into model inputs. On the machine, P2 reaches UNDEFINED at $(R,1)$ or
$(R,3)$ (possibly as the very first step, since their footprints are
inputs), while P1 completes.
✗ accepting the rewrite because $R$ is not an output.

## Q4

✓ Core: for $j\in[2]$: $Z[j]\mathrel{+}=\big(\bigoplus_{i\in[2]}W[j,i]\otimes X[i]\big)\oplus B[j]$.
Term-local contraction: $i$ is bound only in the first term, so the bias is
added once.
✓ Old fibre of $(Z,j)$ is $\{(s1,j),(s2,j)\}$; by grouping (Proposition 2.7(4))
the collected value is $V_{s1}[j]\oplus V_{s2}[j]$, which equals the merged
body's value. Relabeling needs a bijection of occurrences, and the merge
maps four occurrences to two. Admissibility: strict $\oplus$ makes the
merged body defined iff both old bodies are (and here all are total).
Equal Collect and AdmEnv give equal $\Phi_P$, equal models, equal
denotation.
✓ Five occurrences ($2+2+1$); $\mu=5+5=10$; a successful maximal run has
5 CONTRIBUTE and 5 PUBLISH steps (10). Original: 12.
✓ Traces and event counts differ; the occurrence named in a failure
diagnostic can differ (if a body were partial); the rank certificate and
the models do not.
✓ Wrong merge: $Z[j]=\sum_iW[j,i](X[i]+B[j])=\sum_iW[j,i]X[i]+B[j]\sum_iW[j,i]$,
so on $\eta_1$: $Z[0]=-1+1\cdot2=1$, $Z[1]=4+0\cdot1=4$, $Z=(1,4)$ (bias
scaled by the row sum, i.e. added once per $i$).
✗ claiming relabeling suffices; ✗ $Z=(0,4)$ for the wrong merge.

## Q5

✓ $T=X-1/T$ with admissibility $T\ne0$, i.e. $T^2-XT+1=0$. Two models
when $|X|>2$, one ($T=X/2$) when $|X|=2$, none when $|X|<2$. Roots are
never 0 (their product is 1).
✓ $\mathrm{AdmInput}(P)=\{2,-2\}$; $[\![P]\!](2)=1$, $[\![P]\!](-2)=-1$.
✓ $W_P\cong\{(X,T)\mid T\ne0,\ X=T+1/T\}$, i.e. the graph of $T\mapsto T+1/T$
read backwards: $\ell(X,T)=X$, $r(X,T)=T$. $\ell$ is not monic (two
witnesses over $|X|>2$); its image is $(-\infty,-2]\cup[2,\infty)$.
✓ For every $X$ the machine consumes $T=X$ and then blocks: the
self-reading occurrence waits for $(T,())$, which waits for it. Same for
$X=1,2,3$, although they have zero, one and two models. No failure for
$X=1$: UNDEFINED needs a ready occurrence with an undefined body; the
recip occurrence is never ready. The absence of models comes from the
equations, not from an undefined demanded body. No rank certificate exists.
✗ saying the machine fails for $X=1$ or succeeds for $X=2$.

## Q6

✓ $\mathrm{Models}(P,x)=\{(h,y)\mid y=x,\ h\in\mathbb R\}\cong\mathbb R$;
$W_P\cong\mathbb R\times\mathbb R$ (pairs $(x,h)$), $\ell(x,h)=x$,
$r(x,h)=x$. The relation is the diagonal, the graph of the identity, a
function; but $\ell$ is not monic, so AtMostOneModels fails,
$\mathrm{AdmInput}(P)=\varnothing$ and $[\![P]\!]$ is nowhere defined.
✓ Composite apex $\{((x,h),(y,z))\mid x=y,\ y\ne0,\ z=1/y\}\cong(\mathbb R\setminus\{0\})\times\mathbb R$,
in bijection with the models of the glued program. $[\![P;Q]\!]$ is nowhere
defined (every input has 0 or infinitely many models), although the
output relation is the partial function $x\mapsto1/x$.
✓ Machine on $P$: contributes and publishes $y$, then blocks on $h$
(cycle, no rank certificate); neither success nor failure.
✓ $P'$ has $W_{P'}\cong\mathbb R$, monic left leg, $[\![P']\!]=\mathrm{id}$.
$P$ and $P'$ have the same output relation but non-isomorphic spans (no
apex bijection commutes with the legs: fibres have size $|\mathbb R|$
versus 1). Span isomorphism keeps private witnesses, which is why the
notes use it rather than the output relation: unique model is stronger
than unique output.
✗ $[\![P]\!]=\mathrm{id}$.

## Q7

✓ Occurrences: $(b1,0),(b1,1),(b2,0),(b2,1),(b3)$: five. Fibres:
$(T,(0,0))$: $\{(b1,0),(b2,0)\}$; $(T,(0,1))$: $\{(b1,1)\}$;
$(T,(1,0))$: $\{(b2,1)\}$; $(T,(1,1))$: $\varnothing$; $(S,())$: $\{b3\}$.
$T=\begin{pmatrix}9&3\\5&0\end{pmatrix}$, $S=81+9+25+0=115$.
✓ $\mu=5+5=10$; 5 CONTRIBUTE and 5 PUBLISH; $(T,(1,1))$ can be published
at the first step (empty fibre, value $0_K$).
✓ $\alpha(T,(0,0))=2$, unpublished; $b3$ reads all four $T$ addresses and
is not ready.
✓ Inputs $0$, $T$ $1$, $S$ $2$.
✓ Reading zero-initialized storage can give any value from $0$ (all zeros)
up to partial sums; for example $S=0$ if $b3$ runs first. It violates the
CONTRIBUTE premise $\mathrm{Read}(o)\subseteq\mathrm{dom}\,\sigma$:
accumulator initialization is not publication, and absence is not an
available zero.
✗ $S=4+9+\dots$ computed from $C,R$ alone without the corner sum; ✗ 6
occurrences.

## Q8

✓ (a) $f_!v=(\max(5,11),7)=(11,7)$, $f^\ast w=(2,3,2)$;
$\langle f_!v,w\rangle=\max(11+2,7+3)=13$,
$\langle v,f^\ast w\rangle=\max(5+2,7+3,11+2)=13$.
✓ (b) Max-plus: yes. Admissibility is unchanged (the duplicate's body has the
same definedness), and the collected value is unchanged because
$a\oplus a=a$. Over $(\mathbb R,+)$: no, the duplicate doubles its
contribution. The occurrences still differ in both cases. Only the value
is insensitive in the idempotent sort.
✓ (c) $f_!u\le w\iff\forall j:\bigoplus_{f(i)=j}u_i\le w_j\iff\forall i:u_i\le w_{f(i)}$
(a join is below $w_j$ iff each summand is; the empty join is the bottom
$0_K$). So $f_!\dashv f^\ast$ as monotone maps between posets, an adjunction
of thin categories (a Galois connection). Boolean sort: families are
subsets, $f_!$ is direct image, $f^\ast$ is preimage; the result is
image $\dashv$ preimage. This is Theorem 2.4's $\Sigma_f\dashv f^\ast$
restricted to subsingleton-valued families, with $\Sigma_f$ truncated to its
support. Over $(\mathbb R,+,\times)$ there is no such order-theoretic
adjunction ($\oplus$ is not a join), consistent with the notes' refusal to
claim an adjunction on $K$-families in general.
✗ claiming it holds over $\mathbb R$.

## Q9

✓ (a) On $\eta_0$: $Z=(1,0)$, $Y=(1,0)$ published normally; at $L$ the only
pending occurrence has undefined body $\log0$, is dropped, and $L$ is
published as the empty sum $0$. The run completes with $L=0$.
✓ (b) Theorem 5.18 (26.3) part (i) fails: a successful run returns a store
that is not a model ($\log Y[1]$ is undefined there, so it is not even
admissible), while $\mathrm{Models}(\eta_0)=\varnothing$. The broken proof
step is conservation (Lemma 26.1, items 1 and 5): dropped occurrences leave
$U$ without a recorded defined value, so the final accumulator is not the
fibre sum over all occurrences. Part (ii) becomes vacuous since nothing
fails. On inputs with a model the variant coincides with the original:
by Lemma 26.2(b) every reachable store lies below the model, so by read
stability every ready body is defined and nothing is dropped.
✓ (c) It treats $\bot$ as the empty contribution, i.e. as $0_K$; the semantics
forbids identifying undefinedness with zero (collection begins only after
every body is defined).
✗ saying 26.2(b) fails on inputs with a model.

## Q10

✓ (a) `| _, .iverson q, γ => some (if q γ then 1 else 0)` in `evalWith`
(needs `[Semiring K]`, already present); `| _, .iverson _, _ => []` in
`footprint`.
✓ (b) With `q γ = false`, `evalWith σ (.iverson q) γ = some 0`, so by the
`mul` clause the result is `evalWith σ e γ >>= fun y => pure (0 * y)`,
which is `none` iff `evalWith σ e γ = none` (bind on `some` passes through;
bind on `none` is `none`). It formalizes that an Iverson factor is a value,
not a guard: $0\otimes\bot=\bot$, and multiplication by a false indicator
does not remove the obligation.
✓ (c) A guard is expressed by the statement's admissible valuations: a
`Stmt` has `n` valuations and index functions `dest`/`body` on `Fin n`, so
excluded valuations are simply not among the `n`. The guard acts on the
occurrence set (the domain of the pushforward), not on body values, so no
expression constructor is involved.
✗ an `evalWith` clause returning `none` when `q γ = false`.
