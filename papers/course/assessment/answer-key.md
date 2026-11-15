# Assessment: answer key for question set A

Instructor use. Each answer lists the facts a correct response must contain
(marked ✓) and the common errors that lose credit (marked ✗). Scoring: 0,
1 (partially right), 2 (complete and correct) per question; 32 total.

## Q1

✓ $f_!v=(5+11,\,7)=(16,7)$. ✓ $f^\ast w=(w(f(0)),w(f(1)),w(f(2)))=(2,3,2)$.
✓ $\langle f_!v,w\rangle=16\cdot2+7\cdot3=53$;
$\langle v,f^\ast w\rangle=5\cdot2+7\cdot3+11\cdot2=10+21+22=53$.
✗ computing $f_!$ as an overwrite (taking $11$ or $5$ at $0$ instead of the sum).

## Q2

✓ $(\mathrm{Lan}_fA)(j)=\coprod_{i\in f^{-1}(j)}A(i)$ and
$(\mathrm{Ran}_fA)(j)=\prod_{i\in f^{-1}(j)}A(i)$ because the comma category
$f\downarrow j$ is the discrete fibre, so the pointwise colimit/limit is a
coproduct/product. ✓ Adjointness: a map out of a coproduct over the fibre
is a family of maps $A(i)\to B(f(i))$, i.e. a map $A\to f^\ast B$; dually for
products. ✓ $\mathrm{Lan}_f=\Sigma_f$ decategorifies to contraction (sum
over the fibre), needing a commutative monoid $(K,\oplus,0)$ (semiring only
when products are also used). ✗ saying restriction is the left adjoint;
✗ claiming an adjunction between $K^I$ and $K^J$ as sets.

## Q3

✓ Apex $M=[2]\times[3]\times[2]$ (valuations of $(i,j,k)$);
$\pi_A:(i,j,k)\mapsto(i,j)$, $\pi_B:(i,j,k)\mapsto(j,k)$,
$\pi_{\mathrm{out}}:(i,j,k)\mapsto(i,k)$;
$Y=(\pi_{\mathrm{out}})_!(\pi_A^\ast A\otimes\pi_B^\ast B)$. ✓ Equivalently
the composite of the spans $[2]\leftarrow[2]\times[3]\to[3]$ and
$[3]\leftarrow[3]\times[2]\to[2]$ by pullback, weighted by $A$ and $B$.
✓ The statement is composition in $\mathbf{Span}(\mathbf{FinSet})$,
linearized to $\mathbf{Mat}(K)$ (Proposition 2.12). ✗ identifying the
contraction by matching the letter $j$ rather than by the maps.

## Q4

✓ Four occurrences target $(T,0)$: three from the binder statement (one per
$i\in[3]$, the write map $i\mapsto0$ is constant) and one from the scalar
statement. ✓ Collected value $4$. ✓ The coproduct $\mathcal{O}_P=\coprod_sD_s$
(Definition 2.14 / Chapter 1): occurrences are tagged by statement identity
and valuation, so equal bodies and equal destinations do not identify them.
✗ answering 2 (deduplicating) or 1.

## Q5

✓ (a) $\bot$: strict product, $0\otimes\bot=\bot$.
✓ (b) $0$: an empty reduction evaluates no body.
✓ (c) $\bot$: tabulation is undefined if any component is; selection does not
bypass it.
✓ (d) $\log 4$: the guard leaves only $i=0$.
✓ (e) $\bot$: the Iverson factor keeps the occurrence; $0\otimes\log(-1)=\bot$.
✗ any "undefined is zero" answer; ✗ treating (c) lazily.

## Q6

✓ $r^\ast\circ\mathrm{batch}_J(f)\preceq\mathrm{batch}_I(f)\circ r^\ast$ in
the definedness order ($h\preceq k$: wherever $h$ is defined, $k$ is defined
with the same value); equality when $f$ is total or $r$ is surjective.
✓ Counterexample: $f=$ reciprocal, $J=[2]$, family $(2,0)$, $r$ picks
coordinate $0$: left side undefined (batching demands $1/0$), right side
$1/2$. ✓ Forbidden optimisation: "select the needed coordinate before
computing the whole array" (lazy selection); it enlarges the domain of
definition and changes which inputs fail. ✗ writing the inequality the
other way; ✗ claiming naturality holds.

## Q7

✓ Projection law $\pi_1\circ\langle f,g\rangle=f$ fails: with $f$ total and
$g$ undefined at $a$, the left side is undefined at $a$ and the right side is
$f(a)$. ✓ Hence $\mathbf{Pfn}$ with strict pairing is monoidal, not
cartesian. ✓ An unused result cannot be discarded without enlarging the
domain; "dead code elimination" of a demanded partial computation changes
meaning. ✗ claiming Pfn has products given by the cartesian product.

## Q8

✓ Fibres: $(Z,0)$ and $(Z,1)$ each have two occurrences $\{(s1,j),(s2,j)\}$;
$(Y,j)$ and $(L,())$ one each. ✓ $\mathrm{Collect}(Z)=(1-2+1,\ 2+2+0)=(0,4)$,
$\mathrm{Collect}(Y)=(\mathrm{relu}\,0,\mathrm{relu}\,4)=(0,4)$,
$\mathrm{Collect}(L)=\log4$; equal to $\rho$ on $Z,Y,L$ and inputs copied,
so $\Phi_P\rho=\rho$. ✓ On $\eta_0$: admissibility only needs $Y[1]>0$,
but the equations force $Z=(1,0)$ then $Y[1]=\mathrm{relu}(0)=0$, at which
$\log(Y[1])$ is undefined; so no admissible fixed point extends $\eta_0$.
✗ saying $\eta_0$ has no admissible environments; ✗ $L=0$ on $\eta_0$.

## Q9

✓ $\mathrm{Models}(P,\eta)$ is the equalizer of
$\Phi_P:\mathrm{AdmEnv}(P)\to\mathrm{Env}_\Sigma$ and the inclusion
$\mathrm{AdmEnv}(P)\hookrightarrow\mathrm{Env}_\Sigma$, intersected with
(pulled back to) the fibre over $\eta$ of the restriction
$\mathrm{Env}_\Sigma\to\mathrm{Env}(\mathrm{In})$. ✓ All fixed points: $\bot$
carries no order, no lfp is defined, the semantics is a relation and
uniqueness is a separate (operational) guarantee. ✓ $T=X+2T$ with $X=3$:
unique model $T=-3$ (the body is total, so the equalizer is the solution
set of $T=3+2T$). ✗ iterating $\Phi$ from $0$ and reporting divergence.

## Q10

✓ $W_P=\{(\eta,\rho)\mid\rho\in\mathrm{Models}(P,\eta)\}$ with
$\ell=$ restriction to inputs and $r=$ restriction to outputs. ✓ Composite
apex $\{(w_P,w_Q)\mid r_P(w_P)=\ell_Q(w_Q)\}$: pairs of models agreeing on
the boundary; in bijection with models of the glued program.
✓ If both have at most one model on every input (left legs monic), the
composite is the Kleisli composite in $\mathbf{Pfn}$, with domain
$\{\eta\in\mathrm{AdmInput}(P)\mid[\![P]\!]\eta\in\mathrm{AdmInput}(Q)\}$.
✓ Existence does not compose: $P$ may have a model whose output is outside
$\mathrm{AdmInput}(Q)$; uniqueness-everywhere is a hypothesis, not a
consequence. ✗ composing partial functions without the hypothesis.

## Q11

✓ CONTRIBUTE: pending occurrence, footprint published, body defined; adds
the value to the accumulator and removes the occurrence. PUBLISH: defined
address unpublished with no pending occurrence targeting it; copies the
accumulator to the store. UNDEFINED: pending, ready, body undefined; ends
the run. ✓ After one contribution $\alpha(\mathrm{Pre})\in\{1,-1\}$,
$\mathrm{dom}\,\sigma=\{A,B\}$ (inputs only), $T$'s contribution is not
ready because $(\mathrm{Pre},())\notin\mathrm{dom}\,\sigma$. ✓ Order does not
matter: readiness depends on publication, and publication needs both
occurrences consumed (completion barrier). ✗ reading the accumulator.

## Q12

✓ 26.3: if a run completes, its final store is a model and the only model;
if a run fails, there is no model; proof needs only the invariants (every
model extends every reachable store) and read stability; no rank.
✓ 26.6 (ranked): $\mathrm{Init}(P,\eta)\Downarrow\rho$ iff
$\mathrm{Models}(P,\eta)=\{\rho\}$; every maximal run succeeds iff a model
exists, fails iff none. ✓ `T[] = T[]` has many models yet the machine blocks
at once (the one occurrence waits for $T$, publication waits for the
occurrence); so without a rank "model exists" does not give "run succeeds".
✗ claiming blocking means no model.

## Q13

✓ $r:\mathrm{Addr}\to\mathbb{N}$ with $b\in\mathrm{Dep}(a)\Rightarrow r(b)<r(a)$;
as a lax coalgebra morphism: $r[\mathrm{Dep}(a)]\subseteq\{m\mid m<r(a)\}$
from the dependency coalgebra $\mathrm{Dep}:\mathrm{Addr}\to\mathcal{P}(\mathrm{Addr})$
to $n\mapsto\{m<n\}$ on $\mathbb{N}$ (inclusion, not equality, hence lax).
✓ Running example: inputs $0$, $Z$ $1$, $Y$ $2$, $L$ $3$. ✓ History:
$r(X,i)=r(Z,i)=0$, $r(H,(i,l))=l+1$. ✓ $\mu=|U|+|\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma|=7+5=12$.
✗ a rank that is not strictly increasing along dependencies.

## Q14

✓ Blocked: running, not complete, no enabled rule; failed: a ready body was
undefined; failure excludes models, blocking does not. ✓ `T[] = T[] + 1`
blocks, no model; `T[] = X[]; T[] = 2 T[]` blocks, unique model $T=-X$;
`T[] = T[]` blocks, every value is a model. ✗ treating blocked as failed or
as success with zero.

## Q15

Expected names (from the mini file; production names in parentheses):
pullback `Course.pullback` (`LeanNCD.Semantics.pullback`), pushforward
`Course.pushforward` (`pushforward`, laws `pushforward_id`,
`pushforward_comp`, `pushforward_add`, `pushforward_zero`,
`pushforward_relabel`, `pushforward_grouped`), occurrences `Course.Occ`
(`Program.Occurrence`, a sigma type), Kleisli interpretation
`Course.interpret` (`interpret`, `evalWith`, `sequence`, `foldValues`),
equation operator `Course.equationOperator` (`Program.equationOperator`),
model relation `Course.Models` with `models_fixedpoint`
(`Program.Models`, `models_fixedpoint`), step relation `Course.Step`
(`Program.Step`, constructors `contribute`, `publication`, `undefined`),
measure `Course.measure` with `measure_decreases` (`Measure.lean`:
`step_wellFounded`, `no_infinite_chain`). Grade against the final file;
accept any name the notes actually give. ✗ invented names.

## Q16

✓ Over $\mathbb{Q}$ the logarithm is not computable/representable, so the
mini file uses the reciprocal; ✓ since $Y=\mathrm{relu}(Z)\ge0$, both
primitives are undefined exactly when $Y[1]=0$ (log needs $Y[1]>0$,
reciprocal needs $Y[1]\neq0$) and $\eta_0$ forces $Y[1]=0$, so the failing input fails for both and the primary input
succeeds for both ($\log4$ versus $1/4$). ✗ claiming the two programs have
the same denotation on $\eta_1$.
