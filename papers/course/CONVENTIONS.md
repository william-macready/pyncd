# Conventions for authors of the course notes

Every chapter author reads this file first. It fixes notation, the running
example, the facts that no chapter may contradict, and the house style.
Chapters cite each other by file name and section title.

## 1. Files and cross-references

| File | Title | Introduces |
| --- | --- | --- |
| `README.md` | Syllabus | reading order |
| `00-prerequisites.md` | Categorical toolkit | adjunction, Kan extension, monad/Kleisli, (co)algebra, span, equalizer |
| `01-tensor-logic.md` | Tensor Logic and the running example | surface and core syntax, occurrences, the six semantic questions |
| `02-index-categories.md` | Categories of indices and values | FinSet, Σ ⊣ Δ ⊣ Π, pullback/pushforward, Naperian adjunction, Span(FinSet), einsum |
| `03-partiality.md` | Partial computations | Pfn = Kleisli(Option), strict pairing, `sequence`, lax naturality, read footprints |
| `04-denotational.md` | Denotational semantics | Env, Collect, Φ_P, Models as equalizer, denotation as span |
| `05-operational.md` | Operational semantics | configurations, store extension, machine coalgebra, invariants, ranks, correspondence |
| `06-lean.md` | From categories to Lean | dictionary, the mini development, agentic workflow |
| `07-outlook.md` | Refinement and open problems | Part V simulation, what is proved, adjustments to the proposal |
| `lean/MiniTensorLogic.lean` | Mini development | compiled companion |
| `assessment/` | Questions, keys, results | efficacy test |

Links: relative, e.g. `[Chapter 2](02-index-categories.md#3-decategorification-k-valued-families)`.
Section anchors are GitHub-style: lowercase, spaces to hyphens, punctuation
dropped.

## 2. Notation (use exactly these symbols)

| Symbol | Meaning |
| --- | --- |
| $[n]=\{0,\dots,n-1\}$ | finite interval, zero-based; $[0]=\varnothing$ |
| $\mathbf{FinSet}$ | category of finite sets and all functions |
| $\mathbf{Set}$ | sets and functions |
| $\mathbf{Pfn}$ | sets and partial functions; $f : A \rightharpoonup B$ |
| $\mathbf{Span}(\mathbf{FinSet})$ | finite sets, spans up to span isomorphism |
| $K$ | the scalar carrier; a commutative monoid $(K,\oplus,0_K)$, and a commutative semiring $(K,\oplus,\otimes,0_K,1_K)$ where multiplication is used |
| $K^I$ | the set of families $v : I \to K$; also written $\mathrm{Fam}(I)$ when $K$ is fixed |
| $f^\ast : K^J \to K^I$ | pullback (restriction) along $f : I \to J$: $f^\ast v = v \circ f$ |
| $f_! : K^I \to K^J$ | pushforward (sum over fibres): $(f_! v)(j)=\bigoplus_{f(i)=j} v(i)$ |
| $\Sigma_f \dashv f^\ast \dashv \Pi_f$ | the adjoint triple on $\mathbf{Set}$-valued families |
| $\mathrm{Lan}_f, \mathrm{Ran}_f$ | left/right Kan extension along $f$ |
| $\langle u, v\rangle_I = \bigoplus_{i\in I} u(i)\otimes v(i)$ | pairing on $K^I$ |
| $\Sigma$ | a tensor signature; $\mathrm{Coord}_\Sigma(T)$ the coordinate set of tensor $T$ |
| $\mathrm{In},\mathrm{Def},\mathrm{Out}$ | input, defined, output tensor identifiers; $\mathrm{Out}\subseteq\mathrm{Def}$ |
| $\mathrm{Addr}_\Sigma = \{(T,p)\}$ | addresses; $\mathrm{Addr}_{\mathrm{In}}$, $\mathrm{Addr}_{\mathrm{Def}}$ |
| $\mathrm{Env}_\Sigma = \prod_T K^{\mathrm{Coord}_\Sigma(T)}$ | complete environments $\rho$ |
| $\mathrm{Env}(\mathrm{In})$, $\mathrm{Env}(\mathrm{Out})$ | environments restricted to those tensors; input environments are $\eta$ |
| $s$ | a statement; $\Gamma_s$ its index context; $D_s\subseteq\mathrm{Val}(\Gamma_s)$ its admissible valuations (guard applied); $\phi_s : D_s \to \mathrm{Coord}(T_s)$ its write map; $E_s$ its body |
| $\mathcal{O}_P=\coprod_s D_s$ | occurrences of program $P$; an occurrence is $o=(s,\nu)$ |
| $\mathrm{dst} : \mathcal{O}_P \to \mathrm{Addr}_{\mathrm{Def}}$ | destination, $\mathrm{dst}(s,\nu)=(T_s,\phi_s(\nu))$ |
| $\mathcal{C}_P(a)=\mathrm{dst}^{-1}(a)$ | the fibre (writer family) of address $a$ |
| $V_\tau$ | the set of values of expression type $\tau$ ($K$ for scalars, $K^{\mathrm{Coord}}$ for arrays); never written $\mathrm{Val}(\tau)$, which is reserved for valuations |
| $\mathrm{Result}(\tau)=V_\tau\sqcup\{\bot\}$ | result space; $\bot$ is undefined, not zero |
| $[\![E]\!]_{\rho,\nu}\in\mathrm{Result}(\tau)$ | interpretation of body $E$ in $\rho$ at valuation $\nu$; $\downarrow v$ means defined with value $v$ |
| $\mathrm{AdmEnv}(P)$ | environments in which every occurrence body is defined |
| $\mathrm{Collect}_P(\rho)(T)[p]=\bigoplus_{o\in\mathcal{C}_P(T,p)}[\![E_s]\!]_{\rho,\nu}$ | collected value |
| $\Phi_P : \mathrm{AdmEnv}(P)\to\mathrm{Env}_\Sigma$ | equation operator (inputs copied, defined tensors collected) |
| $\mathrm{Models}(P,\eta)$ | $\{\rho\in\mathrm{AdmEnv}(P) \mid \rho\vert_{\mathrm{In}}=\eta,\ \Phi_P(\rho)=\rho\}$ |
| $\mathrm{AdmInput}(P)$ | inputs with exactly one model; $[\![P]\!] : \mathrm{Env}(\mathrm{In})\rightharpoonup\mathrm{Env}(\mathrm{Out})$ |
| $W_P$, $\mathrm{Env}(\mathrm{In})\xleftarrow{\ell}W_P\xrightarrow{r}\mathrm{Env}(\mathrm{Out})$ | witness span; $W_P=\{(\eta,\rho)\mid\rho\in\mathrm{Models}(P,\eta)\}$ |
| $\mathrm{Read}(E,\nu)\subseteq\mathrm{Addr}_\Sigma$ | read footprint |
| $\sigma : \mathrm{Addr}_\Sigma\rightharpoonup K$ | published store; $\sigma\sqsubseteq\sigma'$ store extension; $\sigma\sqsubseteq\rho$ when $\rho$ extends $\sigma$ |
| $(\sigma,\alpha,U)$ | running configuration: store, accumulators $\alpha:\mathrm{Addr}_{\mathrm{Def}}\to K$, pending occurrences $U\subseteq\mathcal{O}_P$ |
| $\mathsf{Failed}(o,\sigma,\alpha,U)$ | terminal failure |
| CONTRIBUTE, PUBLISH, UNDEFINED | the three rules |
| $\mathrm{Init}(P,\eta)$, $\mathsf{Conf}\Downarrow\rho$ | initial configuration; successful completion with final environment $\rho$ |
| $\mathrm{Dep}(a)$, $r:\mathrm{Addr}_\Sigma\to\mathbb{N}$ | dependency set; rank certificate ($b\in\mathrm{Dep}(a)\Rightarrow r(b)<r(a)$) |
| $\mu(\sigma,\alpha,U)=\lvert U\rvert+\lvert\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma\rvert$ | termination measure |

Math is written with `$...$` inline and `$$` display blocks on their own
lines. Never start a line with `=` or `-` inside math. No colour macros.

## 3. The running example (use these exact numbers everywhere)

Scalars are exact reals, $K=\mathbb{R}$. The program `Scorer`:

```text
inputs:   X[i]    i in [2]
          W[j,i]  j in [2], i in [2]
          B[j]    j in [2]
defined:  Z[j], Y[j]  j in [2];   L[]  (scalar)
outputs:  Y, L

s1:  Z[j] = W[j,i] X[i]      # surface einsum: i is contracted
s2:  Z[j] = B[j]             # a second writer to every Z[j]
s3:  Y[j] = relu(Z[j])
s4:  L[]  = log(Y[1])        # log is partial: needs Y[1] > 0
```

Core forms (after elaboration):

- s1: for $j\in[2]$: $Z[j] \mathrel{+}= \bigoplus_{i\in[2]} W[j,i]\otimes X[i]$
- s2: for $j\in[2]$: $Z[j] \mathrel{+}= B[j]$
- s3: for $j\in[2]$: $Y[j] \mathrel{+}= \mathrm{relu}(Z[j])$
- s4: (no binders) $L[] \mathrel{+}= \log(Y[1])$

Occurrences: $\mathcal{O}_P = D_{s1}\sqcup D_{s2}\sqcup D_{s3}\sqcup D_{s4}$ with
$D_{s1}=D_{s2}=D_{s3}=[2]$ (valuations of $j$) and $D_{s4}=\{()\}$; seven
occurrences in total. The fibre of $(Z,0)$ is $\{(s1,j{=}0),(s2,j{=}0)\}$.

Primary input $\eta_1$: $X=(1,-2)$, $W=\begin{pmatrix}1&1\\2&-1\end{pmatrix}$
(so $W[0,0]=1$, $W[0,1]=1$, $W[1,0]=2$, $W[1,1]=-1$), $B=(1,0)$.

Unique model on $\eta_1$:
$Z=(0,4)$, $Y=(0,4)$, $L=\log 4$. Check: $Z[0]=1\cdot1+1\cdot(-2)+1=0$,
$Z[1]=2\cdot1+(-1)(-2)+0=4$.

Failing input $\eta_0$: same $W,B$, $X=(0,0)$. Then $Z=(1,0)$, $Y=(1,0)$,
and $\log(Y[1])=\log 0$ is undefined: $\mathrm{Models}(P,\eta_0)=\varnothing$.
One maximal run publishes all of $Z$ and $Y$ and then takes UNDEFINED at
occurrence $(s4,())$; other maximal runs fail earlier, at the same occurrence.

Read footprints: $\mathrm{Read}(s1,j)=\{(W,(j,0)),(W,(j,1)),(X,0),(X,1)\}$;
$\mathrm{Read}(s2,j)=\{(B,j)\}$; $\mathrm{Read}(s3,j)=\{(Z,j)\}$;
$\mathrm{Read}(s4,())=\{(Y,1)\}$.

Rank certificate: $r=0$ on all input addresses, $r(Z,j)=1$, $r(Y,j)=2$,
$r(L,())=3$. A maximal run has 7 CONTRIBUTE steps and 5 PUBLISH steps on
$\eta_1$.

Pure-einsum reading of s1: global valuation set $M=[2]\times[2]$ (pairs
$(j,i)$), projections $\pi_W=\mathrm{id}:M\to[2]\times[2]$,
$\pi_X:(j,i)\mapsto i$, $\pi_{\mathrm{out}}:(j,i)\mapsto j$, and
$V_{s1}=(\pi_{\mathrm{out}})_!\big(\pi_W^\ast W\otimes\pi_X^\ast X\big)$.

The finite-history (scan) example for ranks is the specification's
Section 11.4 / 27.4: $d=1$, $N=2$, $X[0]=2$, $Z[0]=3$, $F(h)[0]=2h[0]$, history
$H[0,0]=5$, $H[0,1]=12$, $H[0,2]=26$, rank $r(H,(i,l))=l+1$.

## 4. Non-negotiable facts (from the specification)

1. A statement generates one occurrence per admissible valuation; duplicate
   statements generate distinct occurrences and are distinct summands.
2. Collection sums all occurrences addressed to a coordinate; an empty fibre
   gives $0_K$; the prior candidate value is not a summand.
3. $\bot$ is not a scalar, not zero, not a missing-store entry, not NaN, and
   carries no order; there is no least fixed point. Models are *all* fixed
   points of $\Phi_P$ extending $\eta$; the denotation exists only when the
   fixed point is unique.
4. Interpretation is strict: both operands of $\oplus,\otimes$ must be
   defined; $0\otimes\bot=\bot$; a tabulation is undefined if any component
   is; selection does not bypass an undefined component; a primitive is
   defined only on its domain $\mathcal{D}_f$; an empty reduction is $0_K$
   and evaluates no body.
5. A guard removes occurrences before evaluation; an Iverson factor keeps
   the occurrence and multiplies its value. $\mathbf{1}_{i<1}\log(X[i])$ is
   undefined at $i=1$ when $X[1]\le0$.
6. The machine: CONTRIBUTE needs the whole footprint published and a
   defined body; PUBLISH needs no pending occurrence targeting the address;
   UNDEFINED is terminal; blocked is neither success nor failure.
7. Accumulators are not readable; only published values are. Published
   values are immutable.
8. Theorem 26.3 (any successful run gives the unique model; a failed run
   shows there is none) needs no rank certificate. Theorems 26.5–26.6
   (progress, and the biconditional "success iff unique model") need the
   rank certificate. Blocking can occur with zero, one or many models
   (Section 27.5).
9. Read stability (Lemma 23.1): environments agreeing on
   $\mathrm{Read}(E,\nu)$ give equal results, including equal undefinedness.
10. The Lean module `LeanNCD.Semantics` realizes Parts III–IV; its theorem
    names are listed in the spec's status table and must be copied, never
    invented. Experimental categorical modules live under
    `leanncd/experiments/indexed_execution/` and are not production.
11. Batching a partial map over a finite index set is only lax-natural in
    the index set: $r^\ast\circ\mathrm{batch}_J(f)\preceq\mathrm{batch}_I(f)\circ r^\ast$,
    with equality when $f$ is total or $r$ is surjective.
12. No pullback/pushforward adjunction on $K$-families is claimed as a
    theorem; the adjoint triple is a theorem for $\mathbf{Set}$-valued
    families, and the transpose identity is its decategorified shadow.

## 5. House style

- Audience: a graduate student who knows basic category theory. Define
  every new term at first use; motivate before formalizing.
- Each chapter: a two-sentence summary at the top; numbered sections;
  definitions, propositions, and examples labelled `Definition 2.3`,
  `Proposition 2.4`, `Example 2.5` with the chapter number first; the
  running example appears in every chapter; a short "Why this matters for
  an agentic coder" paragraph at the end of each major section; exercises
  at the end (five to eight, with the two or three hardest marked `*`).
- Proofs: give the argument. Where the full proof is in the specification,
  give the idea and cite the section.
- Prose: short sentences, concrete before abstract. No em-dashes.
- Markdown: `$`/`$$` math; tables for dictionaries; fenced `text` blocks
  for TL source; fenced `lean` blocks for Lean.
- Never invent a Lean name. Cite names only from
  `leanncd/LeanNCD/Semantics/*.lean` or from `lean/MiniTensorLogic.lean`.
- Honesty: when a categorical structure is an analogy rather than a
  theorem, say "analogy" and state what is actually proved.
