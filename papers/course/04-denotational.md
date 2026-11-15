# Chapter 4. Denotational semantics: collection, models and spans

**Summary.** A Tensor Logic program means a relation between input environments and complete environments, its *models*, which are all the fixed points of a partial equation operator built from a pushforward and are presented as an equalizer in $\mathbf{Set}$. Packaging the models as a span $\mathrm{Env}(\mathrm{In})\xleftarrow{\ell}W_P\xrightarrow{r}\mathrm{Env}(\mathrm{Out})$ makes sequential composition a pullback, and recovers the partial input-output function exactly when the left leg is monic.

This chapter uses equalizers, spans and Kleisli categories from [Chapter 0](00-prerequisites.md#7-equalizers-and-fixed-points), pushforward and occurrences from [Chapter 2](02-index-categories.md), and strict interpretation from [Chapter 3](03-partiality.md). The semantic authority is Part III of the specification, Sections 18 to 22 ([`tensor_logic_semantics_part_iii.md`](../semantics/tensor_logic_semantics_part_iii.md)). Sections 1 to 5 and 7 follow the specification. Section 6 (gluing, the witness span, composition of partial functions) follows the categorical proposal's Appendix A.8 and A.9, which is a proposal and not the authority; its statements and proofs are given here for the plain-set version.

## 1. What a denotational semantics must say

An operational semantics says how a machine runs a program. A denotational semantics says what the program *means*, with no machine in sight. For Tensor Logic, fix the input values $\eta$. The meaning says which complete assignments $\rho$ to *every* tensor are consistent with the program: the *models* of $P$ on $\eta$. This is a *relation* between $\mathrm{Env}(\mathrm{In})$ and complete environments, with zero, one or many models per input, and internal tensors such as $Z$ in `Scorer` are part of a model. It is *independent of execution*: nothing in it says which statement runs first or what happens on a failure. Chapter 5 must prove that a machine agrees with it.

To see why the definition must be careful, try three naive answers on `Scorer` ([Chapter 1](01-tensor-logic.md#4-the-running-example)):

```text
s1:  Z[j] = W[j,i] X[i]
s2:  Z[j] = B[j]
s3:  Y[j] = relu(Z[j])
s4:  L[]  = log(Y[1])
```

with $\eta_1$: $X=(1,-2)$, $W=\begin{pmatrix}1&1\\2&-1\end{pmatrix}$, $B=(1,0)$, and $\eta_0$: the same $W,B$ with $X=(0,0)$.

**Example 4.1 (three wrong answers).**

*Last write wins.* Treat `=` as assignment and run the statements in order. Then $s2$ overwrites $s1$, so $Z=B=(1,0)$ on $\eta_1$, $Y=(1,0)$, and $\log(Y[1])=\log 0$ fails. The intended model on $\eta_1$ is $Z=(0,4)$, $Y=(0,4)$, $L=\log 4$. Last-write-wins turns a meaningful program into a failure.

*Undefined is zero.* Let an undefined body contribute $0$. On $\eta_0$ the body of $s4$ is $\log 0$, so $L$ would collect $0$ and the program would have the "model" $Z=(1,0)$, $Y=(1,0)$, $L=0$. The specification says there is no model on $\eta_0$, and a consumer could no longer tell "the score is $0$" from "the score does not exist".

*Iterate to a fixed point.* Start from the zero environment over $\eta_1$ (all defined coordinates $0$), recompute all defined tensors at once from the current values, and repeat until nothing changes. The very first step needs $\log(Y[1])=\log 0$, which is undefined, so the iteration cannot start although the program has a unique model. For cyclic programs it is worse (Example 4.16): it diverges on a program with a unique model and silently picks one of infinitely many.

The rest of the chapter builds the answer that survives all three tests. Its ingredients are: complete environments (Section 2), collection as a pushforward (Section 3), models as an equalizer (Section 4), the partial function on inputs with a unique model (Section 5), and the span that composes (Section 6).

*Why this matters for an agentic coder.* Each naive answer is a default of generated code (mutable arrays, `nan` or `0.0`, "loop until converged"), and the denotation is what those defaults must be tested against.

## 2. Environments

**Definition 4.2 (environments).** Let $\Sigma$ be a tensor signature whose identifiers are partitioned as $\mathrm{In}\sqcup\mathrm{Def}$, with $\mathrm{Out}\subseteq\mathrm{Def}$. The set of *complete environments* is the product in $\mathbf{Set}$

$$\mathrm{Env}_\Sigma=\prod_{T}K^{\mathrm{Coord}_\Sigma(T)}.$$

For a set $S$ of identifiers write $\mathrm{Env}(S)=\prod_{T\in S}K^{\mathrm{Coord}_\Sigma(T)}$ and $\mathrm{res}_S:\mathrm{Env}_\Sigma\to\mathrm{Env}(S)$, $\rho\mapsto\rho\vert_S$, for the product projection. Input environments are elements $\eta\in\mathrm{Env}(\mathrm{In})$.

An element $\rho$ assigns a whole tensor value $\rho(T):\mathrm{Coord}_\Sigma(T)\to K$ to every identifier. "Complete" means there are no missing entries: a tensor with an empty coordinate set has exactly one value, since $K^{\varnothing}=1$. Each tensor really has its own sort and $K$ should be read as $K_{\mathrm{sort}(T)}$; we keep one carrier.

**Proposition 4.3.** (1) $\mathrm{Env}_\Sigma\cong K^{\mathrm{Addr}_\Sigma}$. (2) $\mathrm{Env}_\Sigma\cong\mathrm{Env}(\mathrm{In})\times\mathrm{Env}(\mathrm{Def})$, with $\mathrm{res}_{\mathrm{In}}$ and $\mathrm{res}_{\mathrm{Def}}$ as the two projections. (3) The fibre $\mathrm{res}_{\mathrm{In}}^{-1}(\eta)$ is in bijection with $\mathrm{Env}(\mathrm{Def})$.

*Proof.* (1) $\mathrm{Addr}_\Sigma=\coprod_T\mathrm{Coord}_\Sigma(T)$, and $K^{(-)}$ sends coproducts to products because a function out of a disjoint union is a family of functions. (2) $\mathrm{In}$ and $\mathrm{Def}$ partition the identifiers, and a product over a disjoint union of index sets is the product of the two partial products. (3) follows from (2). $\square$

Form (1) is the one Lean uses. In `leanncd/LeanNCD/Semantics/Types.lean`:

```lean
abbrev Address (σ : Declarations S) := (t : σ.Tensor) × Coord (σ.signature t).axes
abbrev Store (K : S → Type) (σ : Declarations S) := (a : Address σ) → Cell K σ a
```

A `Store` is a dependent function on addresses, that is, an element of $K^{\mathrm{Addr}_\Sigma}$ with the carrier chosen by each tensor's sort.

For `Scorer`, $X$ has $2$ coordinates, $W$ has $4$, $B$ has $2$, $Z$ and $Y$ have $2$ each and $L$ has $1$. So $\mathrm{Env}_\Sigma\cong\mathbb{R}^{13}$, $\mathrm{Env}(\mathrm{In})\cong\mathbb{R}^{8}$, $\mathrm{Env}(\mathrm{Def})\cong\mathbb{R}^{5}$ and $\mathrm{Env}(\mathrm{Out})\cong\mathbb{R}^{3}$.

Next we cut out the environments in which every body can be evaluated. For each occurrence $o=(s,\nu)\in\mathcal{O}_P$ (Definition 2.14 in [Chapter 2](02-index-categories.md#5-occurrences-are-a-coproduct)) let

$$\mathrm{ev}_o:\mathrm{Env}_\Sigma\to\mathrm{Result}(K),\qquad \mathrm{ev}_o(\rho)=[\![E_s]\!]_{\rho,\nu},$$

the strict interpretation of [Chapter 3](03-partiality.md). Bodies are scalar, so their result space is $\mathrm{Result}(K)=K\sqcup\{\bot\}$. Tupling gives $\mathrm{ev}_P=\langle\mathrm{ev}_o\rangle_{o\in\mathcal{O}_P}:\mathrm{Env}_\Sigma\to\mathrm{Result}(K)^{\mathcal{O}_P}$. Let $\mathrm{def}:K\hookrightarrow\mathrm{Result}(K)$ be the inclusion of successful values. Its power $\mathrm{def}^{\mathcal{O}_P}$ is again injective.

**Definition 4.4 (admissible environments).** $\mathrm{AdmEnv}(P)$ is the pullback of $\mathrm{def}^{\mathcal{O}_P}$ along $\mathrm{ev}_P$:

```text
 AdmEnv(P) ----------- val -----------> K^{O_P}
     |                                     |
     i                                 def^{O_P}
     v                                     v
  Env_Σ  ------------- ev_P ----------> Result(K)^{O_P}
```

Concretely, by Proposition 0.28,

$$\mathrm{AdmEnv}(P)=\{\rho\in\mathrm{Env}_\Sigma\mid[\![E_s]\!]_{\rho,\nu}\neq\bot\ \text{for every }(s,\nu)\in\mathcal{O}_P\},$$

$i$ is the inclusion, and $\mathrm{val}(\rho)(o)$ is the unique $v\in K$ with $\mathrm{ev}_o(\rho)=\,\downarrow v$. Since the pullback of a mono is a mono, $i$ exhibits $\mathrm{AdmEnv}(P)$ as a subobject of $\mathrm{Env}_\Sigma$.

The pullback gives both the subset and the map $\mathrm{val}$, which turns definedness into scalars for Section 3. Three remarks (spec Section 19.1):

- A guard acts *before* this square. It shrinks $D_s$ and hence $\mathcal{O}_P$. A guard-excluded valuation is not an occurrence and imposes no definedness obligation.
- A present occurrence whose value would be zero must still be defined. Strictness gives $0\otimes\bot=\bot$, so a zero factor does not remove the obligation.
- $\mathrm{AdmEnv}(P)$ is a condition on a *candidate* $\rho$, including candidate values of defined tensors. It says nothing about whether $\rho$ satisfies any equation.

In Lean (`leanncd/LeanNCD/Semantics/Program.lean`) the three arrows of the square are visible by name:

```lean
def outcome (P : Program K σ r) (ops : (s : S) → ScalarOps (K s))
    (ρ : Store K σ) (t : P.Defined) (o : P.Occurrence t) :=
  interpret ops ρ (P.body t o.1) o.2

def AdmEnv (P : Program K σ r) (ops : (s : S) → ScalarOps (K s))
    (ρ : Store K σ) : Prop :=
  ∀ t o, (P.outcome ops ρ t o).isSome = true

def contribution (P : Program K σ r) (ops : (s : S) → ScalarOps (K s))
    (ρ : Store K σ) (h : P.AdmEnv ops ρ) (t : P.Defined) (o : P.Occurrence t) :
    K (σ.signature t.val).sort :=
  (P.outcome ops ρ t o).get (h t o)
```

`outcome` is $\mathrm{ev}_o$, with `Option` playing $\mathrm{Result}$. `AdmEnv` is the predicate defining the pullback. `contribution` is $\mathrm{val}$: it needs the proof `h` that $\rho$ lies in the pullback before it can extract a scalar.

**Example 4.5 (admissible environments of `Scorer`).** The bodies of $s1$ and $s2$ are polynomials and $\mathrm{relu}$ is total, so those six occurrences are defined on every $\rho$. The body of $s4$ is defined iff $\rho(Y)[1]>0$. Hence

$$\mathrm{AdmEnv}(\mathrm{Scorer})=\{\rho\in\mathbb{R}^{13}\mid\rho(Y)[1]>0\}.$$

This set does not mention the inputs, so it meets the fibre over $\eta_0$ in a large set. The environment $\rho^\sharp$ that extends $\eta_0$ by $Z=(0,0)$, $Y=(0,5)$, $L=7$ is admissible but not a model: the model equations force $Z=(1,0)$ and then $Y=(1,0)$, which lies outside $\mathrm{AdmEnv}$ (Section 4).

Keep two failure modes apart. On $\eta_0$, admissible extensions exist but the *equations* push every candidate out of $\mathrm{AdmEnv}$. In Example 4.33 below (the Iverson program of spec Section 21.3), a body reads only inputs and is undefined, so *no* extension of the input is admissible. Both inputs have no model, for different reasons.

*Why this matters for an agentic coder.* Admissibility is a cheap local check (evaluate every occurrence once), distinct from "is this a model". "No admissible extension" is stronger than "no model", and logging the wrong one misdiagnoses the failure.

## 3. Collection is a pushforward

On $\mathrm{AdmEnv}(P)$ every occurrence has a scalar value. Collection sums those values over each destination's fibre. This is exactly the pushforward of [Chapter 2](02-index-categories.md#3-decategorification-k-valued-families).

**Definition 4.6 (body values and collection).** For $\rho\in\mathrm{AdmEnv}(P)$ write $\mathrm{val}_\rho=\mathrm{val}(\rho):\mathcal{O}_P\to K$, so $\mathrm{val}_\rho(s,\nu)$ is the successful value of $[\![E_s]\!]_{\rho,\nu}$ (the family written $c_\rho$ in Chapter 2; the name $\mathrm{val}$ keeps $\mathrm{Val}$ for valuations). With $\mathrm{dst}:\mathcal{O}_P\to\mathrm{Addr}_{\mathrm{Def}}$ from Definition 2.14, define

$$\mathrm{Collect}_P(\rho)=\mathrm{dst}_!(\mathrm{val}_\rho)\in K^{\mathrm{Addr}_{\mathrm{Def}}}\cong\mathrm{Env}(\mathrm{Def}),$$

that is,

$$\mathrm{Collect}_P(\rho)(T)[p]=(\mathrm{dst}_!\,\mathrm{val}_\rho)(T,p)=\bigoplus_{o\in\mathcal{C}_P(T,p)}\mathrm{val}_\rho(o).$$

As a map, $\mathrm{Collect}_P=\mathrm{dst}_!\circ\mathrm{val}:\mathrm{AdmEnv}(P)\to\mathrm{Env}(\mathrm{Def})$. The *contribution tensor* of one statement is $V_s^\rho=(\phi_s)_!(\mathrm{val}_\rho\vert_{D_s})\in K^{\mathrm{Coord}(T_s)}$.

The types force the order: $\mathrm{dst}_!$ acts on a family of *scalars* in $K^{\mathcal{O}_P}$, never on $\mathrm{Result}(K)$-valued families ($\bot$ is never a summand, spec Section 19.2), so $\mathrm{Collect}_P$ is defined on $\mathrm{AdmEnv}(P)$, not on $\mathrm{Env}_\Sigma$.

**Proposition 4.7 (laws of collection).** Let $\rho\in\mathrm{AdmEnv}(P)$.

1. *(Grouping by statement.)* $\mathrm{Collect}_P(\rho)(T)[p]=\bigoplus_{s:\,T_s=T}V_s^\rho[p]$.
2. *(Relabeling.)* If $e:\mathcal{O}'\cong\mathcal{O}_P$ is a bijection, then $(\mathrm{dst}\circ e)_!(\mathrm{val}_\rho\circ e)=\mathrm{Collect}_P(\rho)$. In particular permuting the source statements changes nothing (spec Proposition 19.2).
3. *(Empty fibre.)* If $\mathcal{C}_P(T,p)=\varnothing$ then $\mathrm{Collect}_P(\rho)(T)[p]=0_K$. A defined tensor with no writers collects to the zero tensor.
4. *(Duplicates.)* Two statements with identical text are two summands.
5. *(No implicit summand.)* The candidate value $\rho(T)[p]$ is not a summand. It affects $\mathrm{Collect}_P(\rho)(T)[p]$ only if some body in the fibre reads $(T,p)$.

*Proof.* (1) $\mathcal{O}_P=\coprod_sD_s$ and $\mathrm{dst}$ restricted to $D_s$ is $\nu\mapsto(T_s,\phi_s(\nu))$. Proposition 2.7(4) splits $\mathrm{dst}_!$ into a sum over $s$ of the pushforwards along these restrictions. The restriction for $s$ has an empty fibre over $(T,p)$ unless $T_s=T$, and when $T_s=T$ its value at $(T,p)$ is $(\phi_s)_!(\mathrm{val}_\rho\vert_{D_s})(p)=V_s^\rho[p]$. (2) Proposition 2.7(3). A permutation of statements induces a bijection of $\mathcal{O}_P$ commuting with $\mathrm{dst}$ and $\mathrm{val}_\rho$. (3) The empty sum in a commutative monoid is $0_K$. (4) $\mathcal{O}_P$ is a coproduct (Definition 2.14), so the tags $s1\neq s2$ keep the two occurrences distinct, and both lie in the fibre. (5) The formula sums $\mathrm{val}_\rho$ over the fibre and contains no term $\rho(T)[p]$. $\square$

Part (4) has a converse worth stating. Deleting one of two duplicate statements is not a relabeling: the map from the smaller occurrence set to the larger one is injective but not surjective, so Proposition 2.7(3) does not apply, and the collected value can change (Example 4.31).

For the Boolean sort, take $K=\mathbb{B}$ with $\oplus=\mathrm{OR}$ and $0_K=\mathrm{false}$. The same formula collects by OR (spec Section 19.2). Because OR is idempotent, deleting a duplicate changes no Boolean value, and since the duplicate's definedness obligation is the original's, admissibility and models are unchanged too. The occurrence set still differs, so no relabeling law relates the two programs. Over a non-idempotent sort the values can differ.

*Lean.* `Program.collect` in `leanncd/LeanNCD/Semantics/Program.lean` is literally a pushforward of `contribution`:

```lean
def collect (ρ : Store K σ) (h : P.AdmEnv ops ρ) (t : P.Defined) :
    Coord (σ.signature t.val).axes → K (σ.signature t.val).sort :=
  letI := coordDecidableEq (σ.signature t.val).axes
  pushforward (fun o : P.Occurrence t => P.destination t o.1 o.2)
    (P.contribution ops ρ h t)
```

and `pushforward` in `leanncd/LeanNCD/Semantics/Collection.lean` is the fibre sum:

```lean
def pushforward [DecidableEq I] (d : O → I) (v : Family O K) : Family I K :=
  fun i => ∑ o, if d o = i then v o else 0
```

In Lean, `Occurrence t` is a sigma type over the statements writing `t`, so $\mathcal{O}_P=\coprod_t\mathtt{Occurrence}\ t$ and `collect ρ h t` is $\mathrm{Collect}_P(\rho)(t)$. Because `collect` takes the admissibility proof `h`, the type checker enforces that collection begins after definedness.

The laws are proved by the Chapter 2 lemmas: `Program.collect_grouped` is Proposition 4.7(1) within one target (proof `pushforward_grouped`), and `Program.collect_relabel` states `P.relabeledCollect ops e ρ h t = P.collect ops ρ h t` for bijections `e : ∀ t, O t ≃ P.Occurrence t` (proof `pushforward_relabel`). `Program.admEnv_relabel` says admissibility is invariant under relabeling too.

**Example 4.8 (collection on `Scorer`).** Let $\rho_1$ extend $\eta_1$ by $Z=(0,4)$, $Y=(0,4)$, $L=\log 4$. It is admissible since $\rho_1(Y)[1]=4>0$. The body values are:

| Occurrence $o$ | $\mathrm{dst}(o)$ | $\mathrm{val}_{\rho_1}(o)$ |
| --- | --- | --- |
| $(s1,j{=}0)$ | $(Z,0)$ | $1\cdot1+1\cdot(-2)=-1$ |
| $(s1,j{=}1)$ | $(Z,1)$ | $2\cdot1+(-1)(-2)=4$ |
| $(s2,j{=}0)$ | $(Z,0)$ | $B[0]=1$ |
| $(s2,j{=}1)$ | $(Z,1)$ | $B[1]=0$ |
| $(s3,j{=}0)$ | $(Y,0)$ | $\mathrm{relu}(\rho_1(Z)[0])=\mathrm{relu}(0)=0$ |
| $(s3,j{=}1)$ | $(Y,1)$ | $\mathrm{relu}(\rho_1(Z)[1])=\mathrm{relu}(4)=4$ |
| $(s4,())$ | $(L,())$ | $\log(\rho_1(Y)[1])=\log 4$ |

The fibres are $\mathcal{C}(Z,j)=\{(s1,j),(s2,j)\}$, $\mathcal{C}(Y,j)=\{(s3,j)\}$ and $\mathcal{C}(L,())=\{(s4,())\}$. Pushing forward, and grouping by statement as in Proposition 4.7(1):

$$\mathrm{Collect}(\rho_1)(Z)=V_{s1}\oplus V_{s2}=(-1,4)\oplus(1,0)=(0,4),$$

$$\mathrm{Collect}(\rho_1)(Y)=V_{s3}=(0,4),\qquad \mathrm{Collect}(\rho_1)(L)=\log 4.$$

These agree with $\rho_1$ on every defined tensor. Section 4 names this property.

Now take a candidate that is not a model: $\rho'$ extends $\eta_1$ by $Z=(0,0)$, $Y=(7,1)$, $L=0$. It is admissible because $1>0$. Collection gives $Z=(0,4)$ (the bodies of $s1,s2$ read only inputs), $Y=(\mathrm{relu}(0),\mathrm{relu}(0))=(0,0)$ (they read the *candidate* $Z$), and $L=\log 1=0$. The candidate $\rho'(Z)=(0,0)$ did not enter the collection of $Z$ as a summand. It entered the collection of $Y$, because $s3$ reads $Z$. This is Proposition 4.7(5) at work.

*Why this matters for an agentic coder.* Materialize $\mathcal{O}_P$ and $\mathrm{dst}$, evaluate each body once, stop on any undefined body, and only then sum. Deduplicating statements or adding the old value (reading `+=` as mutation) changes the program.

## 4. Models as an equalizer

Collection produces new values for the defined tensors from a candidate. A model is a candidate that reproduces itself.

**Definition 4.9 (equation operator).** The equation operator of $P$ is

$$\Phi_P=\langle\,\mathrm{res}_{\mathrm{In}}\circ i,\ \mathrm{Collect}_P\,\rangle:\mathrm{AdmEnv}(P)\to\mathrm{Env}(\mathrm{In})\times\mathrm{Env}(\mathrm{Def})\cong\mathrm{Env}_\Sigma.$$

Pointwise: $\Phi_P(\rho)(T)=\rho(T)$ for $T\in\mathrm{In}$ (inputs copied) and $\Phi_P(\rho)(T)=\mathrm{Collect}_P(\rho)(T)$ for $T\in\mathrm{Def}$ (defined tensors collected).

$\Phi_P$ is a total map on $\mathrm{AdmEnv}(P)$, and hence a partial map $\mathrm{Env}_\Sigma\rightharpoonup\mathrm{Env}_\Sigma$ with domain $\mathrm{AdmEnv}(P)$. It is *not* an endomap of $\mathrm{AdmEnv}(P)$: its result need not be admissible.

**Example 4.10 ($\Phi_P$ leaves $\mathrm{AdmEnv}$).** For the one-statement program `T[] = log(T[])` (spec Section 20.2) the candidate $T=1$ is admissible, since $\log 1$ is defined. But $\Phi_P$ sends it to $T=\log 1=0$, at which the same body is $\log 0=\bot$. In `Scorer`, $\Phi(\rho')$ for the candidate $\rho'$ of Example 4.8 has $Y=(0,0)$, so it is not in $\mathrm{AdmEnv}(\mathrm{Scorer})$. So $\Phi_P$ cannot in general be applied twice. A semantics that "iterates $\Phi_P$" is not even well typed.

**Definition 4.11 (models).** For $\eta\in\mathrm{Env}(\mathrm{In})$,

$$\mathrm{Models}(P,\eta)=\{\rho\in\mathrm{AdmEnv}(P)\mid\rho\vert_{\mathrm{In}}=\eta,\ \Phi_P(\rho)=\rho\}.$$

Equivalently (spec Section 20.1): $\rho$ extends $\eta$, every occurrence body is defined in $\rho$, and $\rho(T)[p]=\mathrm{Collect}_P(\rho)(T)[p]$ for every $T\in\mathrm{Def}$ and $p\in\mathrm{Coord}(T)$. *All* defined tensors take part, not only outputs. Zero defaults come from empty fibres, not from an initialization equation.

The definition is a conjunction of three conditions, each a limit.

**Proposition 4.12 (models as an equalizer).** Let $e:\mathrm{Fix}(P)\to\mathrm{AdmEnv}(P)$ be the equalizer in $\mathbf{Set}$ of $\Phi_P$ and $i$:

$$\mathrm{Fix}(P)\xrightarrow{\ e\ }\mathrm{AdmEnv}(P)\ \underset{i}{\overset{\Phi_P}{\rightrightarrows}}\ \mathrm{Env}_\Sigma.$$

1. $\mathrm{Fix}(P)=\{\rho\in\mathrm{AdmEnv}(P)\mid\Phi_P(\rho)=\rho\}$ with $e$ the inclusion.
2. $e$ is also the equalizer of $\mathrm{Collect}_P$ and $\mathrm{res}_{\mathrm{Def}}\circ i$.
3. $\mathrm{Models}(P,\eta)$ is the pullback of $\mathrm{res}_{\mathrm{In}}\circ i\circ e:\mathrm{Fix}(P)\to\mathrm{Env}(\mathrm{In})$ along $\eta:1\to\mathrm{Env}(\mathrm{In})$, that is, the fibre of $\mathrm{Fix}(P)$ over $\eta$.

In a picture, with the square a pullback and the top row an equalizer:

```text
 Models(P,η) ------> Fix(P) ---e---> AdmEnv(P) ==(Φ_P, i)==> Env_Σ
      |                 |
      v                 v  res_In ∘ i ∘ e
      1 ------η-----> Env(In)
```

| Condition in Definition 4.11 | Categorical construction | Object cut out |
| --- | --- | --- |
| every body defined | pullback of $\mathrm{def}^{\mathcal{O}_P}$ along $\mathrm{ev}_P$ | $\mathrm{AdmEnv}(P)$ |
| collected values reproduce $\rho$ | equalizer of $\Phi_P$ and $i$ | $\mathrm{Fix}(P)$ |
| $\rho\vert_{\mathrm{In}}=\eta$ | pullback along $\eta:1\to\mathrm{Env}(\mathrm{In})$ | $\mathrm{Models}(P,\eta)$ |

*Proof.* (1) is Proposition 0.32. (2) Under $\mathrm{Env}_\Sigma\cong\mathrm{Env}(\mathrm{In})\times\mathrm{Env}(\mathrm{Def})$ the two maps $\Phi_P$ and $i$ have the same first component $\mathrm{res}_{\mathrm{In}}\circ i$. Two maps into a product agree iff their components agree, so $\Phi_P\rho=i\rho$ iff $\mathrm{Collect}_P(\rho)=\rho\vert_{\mathrm{Def}}$. (3) By Proposition 0.28 the pullback is $\{(\ast,\rho)\mid\rho\in\mathrm{Fix}(P),\ \rho\vert_{\mathrm{In}}=\eta\}$, which is $\mathrm{Models}(P,\eta)$ up to the bijection $(\ast,\rho)\mapsto\rho$. $\square$

Part (2) says the equations live only on $\mathrm{Def}$. The inputs are pinned by part (3), the spec's "$\rho$ extends $\eta$".

Proposition 4.12 contains no order on $\mathrm{Env}_\Sigma$ or $\mathrm{Result}(K)$, no least fixed point, no starting point, no iteration. The equalizer takes *all* fixed points at once. The spec: the characterization is "not an instruction to iterate $\Phi_P$ from zero. No least-fixed-point selection, convergence claim, or solver is introduced" (Section 20.2). So $\mathrm{Models}(P,\eta)$ can be empty, a singleton, or large; Section 5 shows all three.

*Lean.* In `leanncd/LeanNCD/Semantics/Models.lean`:

```lean
def Models (η : P.Input) (ρ : Store K σ) : Prop :=
  ∃ h : P.AdmEnv ops ρ, P.InputAgreement η ρ ∧
    ∀ t p, ρ ⟨t.val, p⟩ = P.collect ops ρ h t p

/- This partial operator is defined only on AdmEnv. Its result is a complete
   store, not necessarily an admissible store; no iteration is specified. -/
def equationOperator (ρ : Store K σ) (h : P.AdmEnv ops ρ) : Store K σ :=
  fun a => if hi : P.input a.1 = true then ρ a
    else P.collect ops ρ h ⟨a.1, Bool.eq_false_iff.mpr hi⟩ a.2

theorem models_fixedpoint (η : P.Input) (ρ : Store K σ) :
    P.Models ops η ρ ↔ P.InputAgreement η ρ ∧
      ∃ h : P.AdmEnv ops ρ, P.equationOperator ops ρ h = ρ
```

`Program.Models` is the "equations on $\mathrm{Def}$" form, which is Proposition 4.12(2). `Program.equationOperator` is $\Phi_P$: the `if` copies inputs and collects defined tensors, and the argument `h` makes it a function on $\mathrm{AdmEnv}(P)$, not on all stores. `Program.models_fixedpoint` is Proposition 4.12(2), fibrewise: the equations-on-$\mathrm{Def}$ form is equivalent to the fixed-point form of Definition 4.11. `InputAgreement` is the fibre condition, `∃ h` is membership in $\mathrm{AdmEnv}(P)$, and the equation is the equalizer. `Models` is a predicate on pairs $(\eta,\rho)$, which is how Lean represents a subobject. The companion theorems `Program.models_relabel` and `Program.models_grouped` lift Proposition 4.7(2) and 4.7(1) from collection to models.

**Example 4.13 (the models of `Scorer`).** We compute $\mathrm{Fix}$ over each input by forcing, not by iterating. Fix $\eta$ and suppose $\rho\in\mathrm{Models}(\mathrm{Scorer},\eta)$. The equations for $Z$ read only inputs, so $\rho(Z)[j]=\bigoplus_iW[j,i]X[i]\oplus B[j]$ is forced. The equations for $Y$ read only $Z$, so $\rho(Y)=\mathrm{relu}(\rho(Z))$ is forced. The equation for $L$ forces $\rho(L)=\log\rho(Y)[1]$, provided $\rho$ is admissible.

On $\eta_1$ the forced values are $Z=(0,4)$, $Y=(0,4)$, and $\rho(Y)[1]=4>0$, so the forced candidate is admissible and $L=\log 4$. Conversely $\rho_1$ is a fixed point (Example 4.8). Hence $\mathrm{Models}(\mathrm{Scorer},\eta_1)=\{\rho_1\}$.

On $\eta_0$ the forced values are $Z=(1,0)$ and $Y=(1,0)$. Any $\rho$ satisfying the $Z$ and $Y$ equations has $\rho(Y)[1]=0$ and so is not in $\mathrm{AdmEnv}$. Hence $\mathrm{Models}(\mathrm{Scorer},\eta_0)=\varnothing$, although $\mathrm{AdmEnv}$ meets the fibre over $\eta_0$ (Example 4.5). No choice of $L$ helps: the failure is a body, not a value.

The forcing argument works because `Scorer` is layered: each equation reads only lower layers. Chapter 5 turns the layers into a rank certificate, which the denotation does not need.

*Why this matters for an agentic coder.* The model relation is a *check* on a given $\rho$, never a recipe for finding one. "Recompute until stable" is one search procedure with its own failure modes, not the semantics.

## 5. Denotation as a partial function

A relation is not yet a function. The specification extracts a function exactly where the relation is single-valued.

**Definition 4.14 (functional admissibility and denotation).** The *functionally admissible inputs* are

$$\mathrm{AdmInput}(P)=\{\eta\in\mathrm{Env}(\mathrm{In})\mid\mathrm{Models}(P,\eta)\text{ has exactly one element}\}.$$

For $\eta\in\mathrm{AdmInput}(P)$ with unique model $\rho_\eta$, put $[\![P]\!](\eta)=\rho_\eta\vert_{\mathrm{Out}}$. This defines a partial function

$$[\![P]\!]:\mathrm{Env}(\mathrm{In})\rightharpoonup\mathrm{Env}(\mathrm{Out})$$

with domain exactly $\mathrm{AdmInput}(P)$ (spec Section 20.3).

For `Scorer`, $\eta_1\in\mathrm{AdmInput}$ with $[\![\mathrm{Scorer}]\!](\eta_1)=(Y=(0,4),\ L=\log 4)$, and $\eta_0\notin\mathrm{AdmInput}$. Example 4.29 computes the whole domain.

Two remarks separate this definition from things it is easily confused with.

*Unique model is stronger than unique output.* The criterion counts complete models, internal tensors included. Several models might agree on all outputs.

**Example 4.15 (unique output, two models).** Let $X$ be a scalar input, $Y$ a scalar output and $T$ a scalar defined tensor that is not an output:

```text
s1:  Y[] = X[]
s2:  T[] = T[] T[]      # body T ⊗ T
```

The equations are $Y=X$ and $T=T^2$. Over $\mathbb{R}$, $T^2=T$ has the two solutions $0$ and $1$. So every $\eta$ has exactly two models, both with output $Y=X$. The output is determined, yet $\mathrm{AdmInput}=\varnothing$ and $[\![P]\!]$ is nowhere defined. The spec deliberately does not substitute output-only determinacy for the unique-model criterion (Section 20.3: it "could be studied separately; it is not silently substituted"). Section 6 shows that the span keeps exactly the information, private multiplicity, on which the two criteria disagree (Example 4.25).

*Denotation does not imply executability.* A cyclic program can have a unique model and so a denotation while lying outside any executor's fragment (spec Section 20.4). Conversely a well-formed program can have no model on some inputs, and an executor must then report failure, never a default value.

*Lean.* In `leanncd/LeanNCD/Semantics/Models.lean`:

```lean
def AdmInput (η : P.Input) : Prop := ∃! ρ, P.Models ops η ρ

noncomputable def denotation (η : P.Input) (h : P.AdmInput ops η) : P.Output :=
  P.outputProjection (Classical.choose h)

theorem denotation_of_model (η : P.Input) (h : P.AdmInput ops η)
    (ρ : Store K σ) (model : P.Models ops η ρ) :
    P.denotation ops η h = P.outputProjection ρ
```

`Program.AdmInput` is "there exists exactly one model". `Program.denotation` takes a proof of that and returns the output projection of the model, obtained by `Classical.choose`. It is honestly `noncomputable`: a computable version would need a solver for arbitrary cyclic programs, and choosing one would silently choose a semantics. What makes the definition usable is `Program.denotation_of_model`: whoever *has* a model, by any means, knows the denotation. Chapter 5's machine produces a model when it succeeds, and this theorem turns it into the denotation.

**Example 4.16 (three cyclic systems, spec Section 21.4).** Work over $\mathbb{R}$ with scalar tensors. In the first row $X$ is an input and $T$ is the defined output. In the other rows the input environment is empty and $T$ is the output. Every body is defined on every complete environment, so $\mathrm{AdmEnv}=\mathrm{Env}_\Sigma$ in all three.

| Source | $\Phi_P$ on $T$ | $\mathrm{Fix}$ over the input | Denotation | Iteration from $T_0=0$ |
| --- | --- | --- | --- | --- |
| `T[] = X[]`; `T[] = 2 T[]` | $T\mapsto X+2T$ | $\{-X\}$ | $X\mapsto-X$, total | $T_n=(2^n-1)X$, diverges if $X\neq0$ |
| `T[] = T[]` | $T\mapsto T$ | all of $\mathbb{R}$ | nowhere defined | stays at $0$, picks one model |
| `T[] = T[] + 1` | $T\mapsto T+1$ | $\varnothing$ | nowhere defined | $T_n=n$, runs forever |

Here $\mathrm{Fix}(P)$ is a set of complete environments $\rho$, each assigning a value to every tensor ($X$ and $T$ in the first row). With the input fixed to $X$ the only free coordinate is $T$, so the table abbreviates each environment by its $T$ value: $\{-X\}$ stands for the single environment $\{X\mapsto X,\ T\mapsto-X\}$, and "all of $\mathbb{R}$" for the environments $T\mapsto t$ with $t\in\mathbb{R}$.

For the first row, $T=X+2T$ iff $T=-X$, so $\mathrm{Fix}$ is a singleton for every $X$ and $\mathrm{AdmInput}=\mathrm{Env}(\mathrm{In})$. The program has a functional denotation *despite its cycle*. The second has a continuum of models, the third none. Iteration from zero is wrong in every row: it diverges where the answer is unique, returns an arbitrary answer where there are many, and fails to terminate where there are none. A bounded-scan compiler may reject all three as unsupported cycles without contradicting their denotations.

**Example 4.17 (a bounded history, spec Section 21.5).** For the finite-history program of spec Section 11.4, with inputs $X,Z$ of shape $(d)$, defined $H$ of shape $(d,N+1)$ and a total $F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$:

```text
H[i,l]   = X[i]             # i in [d], l in [N+1]
H[i,0]   = Z[i]             # i in [d]
H[i,l+1] = F(H[:,l])[i]     # i in [d], l in [N]
```

The fibre of $(H,(i,0))$ is $\{(\text{first},(i,0)),(\text{second},i)\}$ and the fibre of $(H,(i,l+1))$ is $\{(\text{first},(i,l+1)),(\text{third},(i,l))\}$. So the collected equations are

$$H_0=X+Z,\qquad H_{l+1}=X+F(H_l)\quad(l\in[N]).$$

These are simultaneous equations, just as in the cyclic examples. They have a unique solution, by induction on time: any model agrees with the constructed history at $l=0$, because $H_0$ reads only inputs, and if it agrees at $l$ it agrees at $l+1$, because $H_{l+1}$ reads only inputs and $H_l$. Totality of $F$ keeps every slice defined. So the constructed history is admissible and satisfies every equation by construction. It is a model, and by the induction it is the only one. For $d=1$, $N=2$, $X[0]=2$, $Z[0]=3$ and $F(h)[0]=2h[0]$:

$$H[0,0]=2+3=5,\qquad H[0,1]=2+2\cdot5=12,\qquad H[0,2]=2+2\cdot12=26.$$

The induction on time is the mathematical shadow of the rank $r(H,(i,l))=l+1$ that Chapter 5 uses to execute this program.

*Why this matters for an agentic coder.* Returning a value for every input claims $\mathrm{AdmInput}(P)=\mathrm{Env}(\mathrm{In})$, a theorem to prove per program. Where uniqueness is not established, the honest output is "no denotation".

## 6. The semantics as a span

The partial function $[\![P]\!]$ throws information away: on an input with two models it says nothing, and it never mentions internal tensors. To compose programs we need to keep the models themselves.

**Definition 4.18 (witness span).** The *witness set* of $P$ is

$$W_P=\{(\eta,\rho)\mid\eta\in\mathrm{Env}(\mathrm{In}),\ \rho\in\mathrm{Models}(P,\eta)\}\cong\coprod_{\eta\in\mathrm{Env}(\mathrm{In})}\mathrm{Models}(P,\eta),$$

with legs $\ell(\eta,\rho)=\eta$ and $r(\eta,\rho)=\rho\vert_{\mathrm{Out}}$. The *span of $P$* is

$$\mathrm{Env}(\mathrm{In})\xleftarrow{\ \ell\ }W_P\xrightarrow{\ r\ }\mathrm{Env}(\mathrm{Out}).$$

**Proposition 4.19.** $W_P\cong\mathrm{Fix}(P)$ via $(\eta,\rho)\mapsto\rho$. Under this bijection $\ell=\mathrm{res}_{\mathrm{In}}\circ i\circ e$ and $r=\mathrm{res}_{\mathrm{Out}}\circ i\circ e$. The fibre $\ell^{-1}(\eta)$ is $\mathrm{Models}(P,\eta)$.

*Proof.* Every $\rho\in\mathrm{Fix}(P)$ is a model of exactly one input, namely $\rho\vert_{\mathrm{In}}$. So $\rho\mapsto(\rho\vert_{\mathrm{In}},\rho)$ is inverse to the projection. The rest is Proposition 4.12(3). $\square$

So the apex of the span is the equalizer itself, and the left leg remembers which input each model extends. The span lives in $\mathbf{Span}(\mathbf{Set})$ (Definition 0.29), not $\mathbf{Span}(\mathbf{FinSet})$, because $\mathrm{Env}(\mathrm{In})$ is infinite when $K=\mathbb{R}$. The construction and its laws are exactly those of [Chapter 2, Definition 2.10](02-index-categories.md#4-contraction-patterns-are-spans): composition by pullback, equivalence by span isomorphism, identities $A\xleftarrow{\mathrm{id}}A\xrightarrow{\mathrm{id}}A$.

### 6.1 Sequential composition is a pullback

**Definition 4.20 (sequential gluing).** Programs $P$ and $Q$ are *composable* when $\mathrm{In}_Q=\mathrm{Out}_P$ (the same identifiers with the same signatures) and every defined identifier of $Q$ is fresh for $P$: $\mathrm{Def}_Q\cap(\mathrm{In}_P\cup\mathrm{Def}_P)=\varnothing$. The *glued program* $P;Q$ has

- identifiers $\mathrm{In}_P\sqcup\mathrm{Def}_P\sqcup\mathrm{Def}_Q$, with the signatures inherited from $P$ and $Q$;
- $\mathrm{In}_{P;Q}=\mathrm{In}_P$, $\mathrm{Def}_{P;Q}=\mathrm{Def}_P\sqcup\mathrm{Def}_Q$, $\mathrm{Out}_{P;Q}=\mathrm{Out}_Q$;
- the statements of $P$ and of $Q$, kept distinct, so $\mathcal{O}_{P;Q}=\mathcal{O}_P\sqcup\mathcal{O}_Q$ and $\mathrm{dst}_{P;Q}=\mathrm{dst}_P\sqcup\mathrm{dst}_Q$.

Two consequences of the hypotheses drive everything. The signatures $\Sigma_P$ and $\Sigma_Q$ share exactly the identifiers $\mathrm{Out}_P=\mathrm{In}_Q$. And a statement of $P$ names only tensors of $\Sigma_P$, a statement of $Q$ only tensors of $\Sigma_Q$. Write $\pi_P:\mathrm{Env}_{P;Q}\to\mathrm{Env}_{\Sigma_P}$ and $\pi_Q:\mathrm{Env}_{P;Q}\to\mathrm{Env}_{\Sigma_Q}$ for the restrictions. Because the identifier sets overlap exactly in $\mathrm{Out}_P$, the square

$$\mathrm{Env}_{P;Q}\cong\mathrm{Env}_{\Sigma_P}\times_{\mathrm{Env}(\mathrm{Out}_P)}\mathrm{Env}_{\Sigma_Q}$$

is a pullback in $\mathbf{Set}$: a complete environment of the glued program is the same as a pair of environments that agree on the boundary.

**Lemma 4.21 (signature weakening).** Let $\Sigma\subseteq\Sigma'$ and let $E$ be well formed over $\Sigma$. For $\rho\in\mathrm{Env}_{\Sigma'}$, $[\![E]\!]_{\rho,\nu}=[\![E]\!]_{\rho\vert_\Sigma,\nu}$, including equal undefinedness.

*Proof.* Induction on $E$ through the clauses of spec Section 18. The only clause that consults $\rho$ is the tensor read $T[e_1,\dots,e_k]$, which returns $\rho(T)[\dots]$ for a $T$ named in $E$, hence $T\in\Sigma$, where $\rho$ and $\rho\vert_\Sigma$ agree. Every other clause combines the results of subexpressions, strictly. The same one-clause observation drives read stability ([Proposition 3.22](03-partiality.md#6-read-footprints-and-stability)), which compares two environments over one signature. Guards and binders do not consult $\rho$ either, so a statement of $P$ has the same $D_s$ and $\phi_s$ in $P;Q$ as in $P$. $\square$

**Theorem 4.22 (composition of witness spans).** Let $P,Q$ be composable. The map

$$\rho\longmapsto(\pi_P\rho,\ \pi_Q\rho)$$

is a bijection from $\mathrm{Fix}(P;Q)$ onto

$$\{(\rho_P,\rho_Q)\in\mathrm{Fix}(P)\times\mathrm{Fix}(Q)\mid\rho_P\vert_{\mathrm{Out}_P}=\rho_Q\vert_{\mathrm{In}_Q}\},$$

which is the apex $W_P\times_{\mathrm{Env}(\mathrm{Out}_P)}W_Q$ of the composite span. It commutes with both legs. Hence the span of $P;Q$ is isomorphic to the composite in $\mathbf{Span}(\mathbf{Set})$ of the span of $P$ followed by the span of $Q$.

*Proof.* We go step by step through the three conditions of Proposition 4.12.

*(a) Definedness splits.* An occurrence of $P;Q$ lies in $\mathcal{O}_P$ or in $\mathcal{O}_Q$. For $o\in\mathcal{O}_P$, Lemma 4.21 gives $\mathrm{ev}^{P;Q}_o(\rho)=\mathrm{ev}^P_o(\pi_P\rho)$. For $o\in\mathcal{O}_Q$, likewise $\mathrm{ev}^{P;Q}_o(\rho)=\mathrm{ev}^Q_o(\pi_Q\rho)$. Hence $\rho\in\mathrm{AdmEnv}(P;Q)$ iff $\pi_P\rho\in\mathrm{AdmEnv}(P)$ and $\pi_Q\rho\in\mathrm{AdmEnv}(Q)$. On such $\rho$ the body values are the copairing $\mathrm{val}^{P;Q}_\rho=[\mathrm{val}^P_{\pi_P\rho},\mathrm{val}^Q_{\pi_Q\rho}]$.

*(b) Collection splits.* $\mathrm{Addr}_{\mathrm{Def}_{P;Q}}=\mathrm{Addr}_{\mathrm{Def}_P}\sqcup\mathrm{Addr}_{\mathrm{Def}_Q}$. By Proposition 2.7(4) applied to $\mathcal{O}_P\sqcup\mathcal{O}_Q$,

$$\mathrm{Collect}_{P;Q}(\rho)=(\mathrm{dst}_P)_!\,\mathrm{val}^P_{\pi_P\rho}\ \oplus\ (\mathrm{dst}_Q)_!\,\mathrm{val}^Q_{\pi_Q\rho},$$

with each pushforward extended by $0_K$ to the other summand. At an address of $\mathrm{Def}_P$ the second term has an empty fibre, because statements of $Q$ write only $\mathrm{Def}_Q$, so it contributes $0_K$. Hence $\mathrm{Collect}_{P;Q}(\rho)\vert_{\mathrm{Def}_P}=\mathrm{Collect}_P(\pi_P\rho)$, and symmetrically $\mathrm{Collect}_{P;Q}(\rho)\vert_{\mathrm{Def}_Q}=\mathrm{Collect}_Q(\pi_Q\rho)$.

*(c) Fixed points split.* By Proposition 4.12(2), $\rho\in\mathrm{Fix}(P;Q)$ iff $\rho$ is admissible and $\rho\vert_{\mathrm{Def}_{P;Q}}=\mathrm{Collect}_{P;Q}(\rho)$. By (a) and (b) this holds iff $\pi_P\rho\in\mathrm{Fix}(P)$ and $\pi_Q\rho\in\mathrm{Fix}(Q)$. Note that $Q$ has no equation on $\mathrm{In}_Q=\mathrm{Out}_P$. Those coordinates are governed by $P$'s equations, and the two halves of $\rho$ agree there by construction.

*(d) The bijection.* For $\rho\in\mathrm{Fix}(P;Q)$ both $\pi_P\rho$ and $\pi_Q\rho$ restrict to $\rho\vert_{\mathrm{Out}_P}$ on the boundary, so the pair is compatible. Conversely, given a compatible pair, let $\mathrm{glue}(\rho_P,\rho_Q)$ be $\rho_P$ on $\Sigma_P$ and $\rho_Q$ on $\mathrm{Def}_Q$. Then $\pi_P\,\mathrm{glue}=\rho_P$, and $\pi_Q\,\mathrm{glue}=\rho_Q$ because $\rho_P$ and $\rho_Q$ agree on $\mathrm{Out}_P=\mathrm{In}_Q$. By (c), $\mathrm{glue}$ lands in $\mathrm{Fix}(P;Q)$, and $\mathrm{glue}(\pi_P\rho,\pi_Q\rho)=\rho$. So the two maps are inverse.

*(e) The legs.* $\ell_{P;Q}(\rho)=\rho\vert_{\mathrm{In}_P}=\ell_P(\pi_P\rho)$ and $r_{P;Q}(\rho)=\rho\vert_{\mathrm{Out}_Q}=r_Q(\pi_Q\rho)$. These are the legs of the pullback composite (Definition 2.10). $\square$

No hypothesis on existence, uniqueness, acyclicity or ranks appears. The categorical proposal stresses the same point for its richer version (Appendix A.8: "No rank, phase, model existence or uniqueness premise appears in the core witness theorem").

**Corollary 4.23 (fibrewise form).** For every $\eta\in\mathrm{Env}(\mathrm{In}_P)$,

$$\mathrm{Models}(P;Q,\eta)\cong\coprod_{\rho_P\in\mathrm{Models}(P,\eta)}\mathrm{Models}\big(Q,\ \rho_P\vert_{\mathrm{Out}_P}\big).$$

*Proof.* Take the fibre over $\eta$ on both sides of Theorem 4.22, using $\ell_{P;Q}=\ell_P\circ\pi_P$. $\square$

Gluing is associative up to the canonical relabeling of occurrence tags, which changes nothing (Proposition 4.7(2)): $(P;Q);R$ and $P;(Q;R)$ have the same identifiers, statements and roles. This matches associativity of span composition up to isomorphism.

### 6.2 Why span isomorphism is the right equivalence

We want an equivalence of programs that respects the denotation and composition. Span isomorphism does.

**Proposition 4.24 (span invariants).** If the spans of $P$ and $P'$ are isomorphic, then $\mathrm{AdmInput}(P)=\mathrm{AdmInput}(P')$ and $[\![P]\!]=[\![P']\!]$. Moreover, if the spans of $P$ and $P'$ are isomorphic, the spans of $Q$ and $Q'$ are isomorphic, and $P',Q'$ are also composable, then the spans of $P;Q$ and $P';Q'$ are isomorphic.

*Proof.* An isomorphism $h:W_P\cong W_{P'}$ with $\ell'\circ h=\ell$ restricts to bijections $\ell^{-1}(\eta)\cong\ell'^{-1}(\eta)$, that is, $\mathrm{Models}(P,\eta)\cong\mathrm{Models}(P',\eta)$ by Proposition 4.19. So the fibres have the same cardinality and $\mathrm{AdmInput}$ agrees. On a singleton fibre $\{w\}$, $r'(h(w))=r(w)$, so the outputs agree. The last claim holds because span composition is well defined on isomorphism classes (Definition 2.10), together with Theorem 4.22. $\square$

A coarser equivalence would compare only the *relation* $\{(\ell(w),r(w))\}\subseteq\mathrm{Env}(\mathrm{In})\times\mathrm{Env}(\mathrm{Out})$, the input-output behaviour. It forgets how many models stand behind each pair.

**Example 4.25 (same behaviour, different spans).** Let $P_1$ be `Y[] = X[]` and let $P_2$ be the program of Example 4.15, which adds the private equation $T=T^2$. Both relate each $X$ to exactly the output $Y=X$, so their input-output relations are equal. But $W_{P_1}\cong\mathbb{R}$, one witness per input, while $W_{P_2}\cong\mathbb{R}\times\{0,1\}$, two witnesses per input. No bijection commutes with $\ell$, since fibres of size $1$ and $2$ cannot correspond. The spans are not isomorphic, and correctly so: $[\![P_1]\!]$ is total and $[\![P_2]\!]$ is empty. Relation-level equivalence identifies two programs with different denotations, so it cannot be the equivalence here.

Span isomorphism is coarse enough to forget how witnesses are named (any apex bijection commuting with both legs) and fine enough to keep private tensors that change the number of models.

### 6.3 Partial functions are the monic case

By Proposition 0.30, a span with injective left leg is the same as a partial function, and composition of such spans is composition in $\mathbf{Pfn}$.

**Definition 4.26 (at most one model).** Say $P$ has *at most one model everywhere*, written $\mathrm{AtMostOneModels}(P)$, if $\lvert\mathrm{Models}(P,\eta)\rvert\le1$ for every $\eta$. (Appendix A.9 of the proposal uses the same term for its richer components.)

**Proposition 4.27 (monic left leg).** $\ell:W_P\to\mathrm{Env}(\mathrm{In})$ is injective iff $\mathrm{AtMostOneModels}(P)$. In that case the span of $P$ is the graph of $[\![P]\!]$: its domain $\mathrm{im}\,\ell$ equals $\mathrm{AdmInput}(P)$, and its value at $\eta$ is $r$ of the unique witness, which is $[\![P]\!](\eta)$.

*Proof.* $\ell^{-1}(\eta)\cong\mathrm{Models}(P,\eta)$ (Proposition 4.19), and a map is injective iff all its fibres have at most one element. Under that hypothesis a fibre is nonempty iff it has exactly one element, so $\mathrm{im}\,\ell=\mathrm{AdmInput}(P)$, and the value is the output of the unique model. $\square$

Without $\mathrm{AtMostOneModels}(P)$ the span is not a partial function, and $[\![P]\!]$ is *not* its shadow under any functor: $[\![P]\!]$ keeps only the fibres of size exactly one. If a functor $F:\mathbf{Span}(\mathbf{Set})\to\mathbf{Pfn}$ sent each program's span to $[\![P]\!]$, Theorem 4.22 would give $[\![P;Q]\!]=[\![Q]\!]\circ[\![P]\!]$ for all composable pairs, which Example 4.30 refutes. The next two results show that this restriction composes well under the hypothesis and badly without it.

**Proposition 4.28 (composition in $\mathbf{Pfn}$).** Let $P,Q$ be composable.

(a) Under $\mathrm{AtMostOneModels}(P)$ alone, the domain of $[\![P;Q]\!]$ is

$$\mathrm{AdmInput}(P;Q)=\{\eta\in\mathrm{AdmInput}(P)\mid[\![P]\!](\eta)\in\mathrm{AdmInput}(Q)\},$$

and on that domain $[\![P;Q]\!]=[\![Q]\!]\circ[\![P]\!]$, as a Kleisli composite in $\mathbf{Pfn}=\mathrm{Kl}(\mathrm{Option})$ (Proposition 0.16).

(b) Under $\mathrm{AtMostOneModels}(P)$ and $\mathrm{AtMostOneModels}(Q)$, additionally $\mathrm{AtMostOneModels}(P;Q)$.

*Proof.* By Corollary 4.23, $\mathrm{Models}(P;Q,\eta)\cong\coprod_{\rho_P\in\mathrm{Models}(P,\eta)}\mathrm{Models}(Q,\rho_P\vert_{\mathrm{Out}_P})$. Since $\mathrm{AtMostOneModels}(P)$, the index set is empty or a singleton $\{\rho_P\}$. If it is empty, $\mathrm{Models}(P;Q,\eta)$ is empty. Otherwise $\eta\in\mathrm{AdmInput}(P)$ and $\mathrm{Models}(P;Q,\eta)\cong\mathrm{Models}(Q,\rho_P\vert_{\mathrm{Out}_P})$, which has exactly one element iff $[\![P]\!](\eta)=\rho_P\vert_{\mathrm{Out}_P}\in\mathrm{AdmInput}(Q)$. This is the domain formula. On this domain the unique model of $P;Q$ glues $\rho_P$ and the unique $\rho_Q$ (Theorem 4.22), and its output is $\rho_Q\vert_{\mathrm{Out}_Q}=[\![Q]\!]([\![P]\!](\eta))$. For (b), $\mathrm{AtMostOneModels}(Q)$ bounds every $\mathrm{Models}(Q,\cdot)$ by one element, so $\mathrm{Models}(P;Q,\eta)$ has at most one element for every $\eta$, which is $\mathrm{AtMostOneModels}(P;Q)$.

Alternatively, with both hypotheses: both spans have monic left legs (Proposition 4.27), so their composite is the graph of the composite partial function (Proposition 0.30). By Theorem 4.22 the span of $P;Q$ is isomorphic to this graph, so its left leg is monic, and by Proposition 4.27 and the bijection of Proposition 0.30 between isomorphism classes of monic spans and partial functions, $[\![P;Q]\!]=[\![Q]\!]\circ[\![P]\!]$. $\square$

The first proof uses $\mathrm{AtMostOneModels}(Q)$ only in its last step, for part (b): part (a) needs only $\mathrm{AtMostOneModels}(P)$ (Exercise 7). This one-sided form is proved here on paper only; the experimental Lean assumes both hypotheses. Example 4.30 shows that the hypothesis on $P$ cannot be dropped.

**Example 4.29 (`Scorer` is a composite).** Split `Scorer` at $Z$. Let $P$ have statements $s1,s2$, with $\mathrm{In}_P=\{X,W,B\}$ and $\mathrm{Def}_P=\mathrm{Out}_P=\{Z\}$. Let $Q$ have statements $s3,s4$, with $\mathrm{In}_Q=\{Z\}$ and $\mathrm{Def}_Q=\mathrm{Out}_Q=\{Y,L\}$. They are composable and $P;Q$ is `Scorer`: its outputs are $\{Y,L\}$, and $Z$ becomes internal.

$P$ has exactly one model on every input, $Z=WX+B$, so $\mathrm{AdmInput}(P)$ is everything and $[\![P]\!](\eta)=WX+B$. For $Q$, given $Z$, the equations force $Y=\mathrm{relu}(Z)$ and $L=\log Y[1]$, so $Q$ has at most one model, and one exactly when $\mathrm{relu}(Z[1])>0$, that is, $Z[1]>0$. By Proposition 4.28,

$$\mathrm{AdmInput}(\mathrm{Scorer})=\{\eta\mid W[1,0]X[0]+W[1,1]X[1]+B[1]>0\}.$$

On $\eta_1$ this is $2\cdot1+(-1)(-2)+0=4>0$, and $[\![\mathrm{Scorer}]\!](\eta_1)=[\![Q]\!](Z=(0,4))=(Y=(0,4),L=\log 4)$. On $\eta_0$ it is $0$, so $[\![P]\!](\eta_0)=(1,0)\notin\mathrm{AdmInput}(Q)$, and the composite is undefined, as Example 4.13 found directly.

**Example 4.30 (uniqueness is not compositional; categorical proposal, Section 9.3).** Without the hypotheses of Proposition 4.28 the partial function $[\![P;Q]\!]$ is not determined by $[\![P]\!]$ and $[\![Q]\!]$. Let $P$ have no inputs and one defined output $t$, with `t[] = t[] t[]`. Let $Q$ have input $t$ and output $u$, with `u[] = log(t[])`. (The proposal uses a reciprocal. Any primitive undefined at $0$ and defined at $1$ works.)

- $\mathrm{Models}(P,())=\{t=0,\ t=1\}$, so $\mathrm{AdmInput}(P)=\varnothing$ and $[\![P]\!]$ is nowhere defined.
- $Q$ has at most one model on every input, and $\mathrm{AdmInput}(Q)=\{t\mid t>0\}$.
- By Corollary 4.23, $\mathrm{Models}(P;Q,())\cong\mathrm{Models}(Q,0)\sqcup\mathrm{Models}(Q,1)=\varnothing\sqcup\{u=0\}$. The composite has a unique model, $t=1$, $u=0$.

So $[\![P;Q]\!]$ is defined, while the Kleisli composite $[\![Q]\!]\circ[\![P]\!]$ is not. Now replace $P$ by $P'$: `t[] = t[] + 1`. Then $[\![P']\!]=[\![P]\!]$, both nowhere defined, but $P';Q$ has no model. Equal partial functions, composed with the same $Q$, give different results. The span keeps both models of $P$, and the pullback against $Q$ discards $t=0$. The proposal records a kernel-checked instance of this pattern in `IndexedComponentModelCycleTest.lean`.

Two more lessons. *Model existence is not determined by the domains*: whether $P;Q$ has a model depends on the boundary values of $P$'s models (it is determined by the two input-output relations, composed as relations), not on whether $P$ and $Q$ each have models somewhere. And *Theorem 4.22 is not a solver*: finding the model of $P;Q$ above still requires solving $t=t^2$, where Chapter 5's machine blocks.

### 6.4 Identities, and what the experimental modules prove

The identity span on $\mathrm{Env}(\mathrm{In})$ has apex $\mathrm{Env}(\mathrm{In})$ and both legs the identity. No program with a nonempty input interface has this span literally, because inputs and defined tensors are disjoint and $\mathrm{Out}\subseteq\mathrm{Def}$. The closest program is a copy `X'[i] = X[i]`, which adds a tensor and occurrences. The identity is a semantic *wire*, not a program. The categorical proposal says the same (Appendix A.9: "The identity graph/span is a semantic wire, not a core identity computation").

Definition 4.20 requires $\mathrm{In}_Q=\mathrm{Out}_P$ literally. Real composition tags interfaces, which then "are not literally the original interfaces" (Appendix A.9), so comparisons need explicit transports. The experimental Lean development under `leanncd/experiments/indexed_execution/` proves analogues of Theorem 4.22, Propositions 4.24, 4.27 and 4.28 (under both at-most-one-model hypotheses) for that richer notion of component: witness spans ([`IndexedWitnessSpan.lean`](../../leanncd/experiments/indexed_execution/IndexedWitnessSpan.lean)), their composition ([`IndexedWitnessComposition.lean`](../../leanncd/experiments/indexed_execution/IndexedWitnessComposition.lean)), nested coherence ([`IndexedWitnessCoherence.lean`](../../leanncd/experiments/indexed_execution/IndexedWitnessCoherence.lean)), the restriction to partial maps ([`IndexedWitnessPartial.lean`](../../leanncd/experiments/indexed_execution/IndexedWitnessPartial.lean)), model gluing ([`IndexedComponentModelWitnesses.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentModelWitnesses.lean)) and the restricted functional law ([`IndexedComponentModelDenotation.lean`](../../leanncd/experiments/indexed_execution/IndexedComponentModelDenotation.lean)). These modules are experimental, not production. This chapter's plain-set version is a simplification whose proofs a student can check by hand.

*Why this matters for an agentic coder.* Gluing is always safe for models (Theorem 4.22), but stage-by-stage partial functions compose only with at-most-one-model certificates (Proposition 4.28). Without them, isolated input-output tests cannot predict the composite (Example 4.30), and a stage that "looks deterministic" may hide private models (Example 4.25).

## 7. Worked examples from the specification

The spec's Section 21 examples, read through the constructions above.

**Example 4.31 (duplicates and zero defaults, spec Section 21.1).** Let $X=(2,5)$ be an input of shape $(2)$ and $T$ a defined output of the same shape:

```text
d1: T[i] = X[i]    # i in [2]
d2: T[i] = X[i]    # i in [2]
```

$\mathcal{O}_P=D_{d1}\sqcup D_{d2}$ has four elements. The fibre of $(T,0)$ is $\{(d1,0),(d2,0)\}$, and that of $(T,1)$ is $\{(d1,1),(d2,1)\}$. Every body is defined and reads only $X$. So for every candidate $\rho$ extending the input,

$$\mathrm{Collect}(\rho)(T)[0]=2\oplus2=4,\qquad\mathrm{Collect}(\rho)(T)[1]=5\oplus5=10.$$

The fibre of $\mathrm{Fix}(P)$ over this input is a singleton and the unique output is $T=(4,10)$. No previous value of $T$ is added. Deleting $d2$ gives $T=(2,5)$, a different program (Proposition 4.7(4) and the remark after it). For a defined tensor with no writers, every fibre is empty and every model assigns it the zero tensor (Proposition 4.7(3)).

**Example 4.32 (the intermediate fixes the activation boundary, spec Section 21.2).** At a fixed coordinate take inputs $A[i]=1$, $B[i]=-1$. Two programs:

| Activation in contributions | Activation after collection |
| --- | --- |
| `T[i] = relu(A[i])` | `Pre[i] = A[i]` |
| `T[i] = relu(B[i])` | `Pre[i] = B[i]` |
| | `T[i] = relu(Pre[i])` |

In the first, the fibre of $(T,i)$ has two occurrences with values $\mathrm{relu}(1)=1$ and $\mathrm{relu}(-1)=0$, so $T[i]=1$. In the second, the fibre of $(\mathrm{Pre},i)$ collects $1\oplus(-1)=0$, and the single occurrence for $T$ reads the collected $\mathrm{Pre}[i]$, so the equations force $\mathrm{Pre}[i]=0$ and $T[i]=\mathrm{relu}(0)=0$. Collection never moves a primitive across a sum (spec Section 19.4). `Scorer` contains exactly this situation: $Z[0]$ collects $-1\oplus1=0$ and $s3$ applies $\mathrm{relu}$ afterwards, giving $Y[0]=0$. If $\mathrm{relu}$ were pushed into the two writers of $Z[0]$, the result would be $\mathrm{relu}(-1)+\mathrm{relu}(1)=1$.

**Example 4.33 (guard versus Iverson factor, spec Section 21.3).** Let $X=(4,-1)$ be a real input and $Y$ a defined output of shape $(2)$.

- *Guarded:* for $i\in[2]$ where $i<1$, $Y[i]\mathrel{+}=\log(X[i])$. The guard gives $D=\{0\}$, so $\mathcal{O}_P$ has one occurrence. Its body $\log 4$ is defined. The fibre of $(Y,1)$ is empty. The unique model is $Y[0]=\log 4$, $Y[1]=0$.
- *Iverson:* for $i\in[2]$, $Y[i]\mathrel{+}=\mathbf{1}_{i<1}\log(X[i])$. Now $\mathcal{O}_P$ has two occurrences. At $i=1$ the body is $0\otimes\log(-1)=0\otimes\bot=\bot$ by strictness. The body reads only the input, so it is undefined in *every* candidate extending this input. The fibre of $\mathrm{AdmEnv}(P)$ over the input is empty, hence so is $\mathrm{Models}$.

Contrast `Scorer` on $\eta_0$, where admissible extensions exist and the equations exclude them (Example 4.5). The guard removes an occurrence before the pullback of Definition 4.4; the Iverson factor keeps it inside.

## 8. Why this matters for an agentic coder

**Implement** four things, in this order. (1) The occurrence set $\mathcal{O}_P=\coprod_sD_s$, tagged by statement, with guards applied, and $\mathrm{dst}$. (2) Strict evaluation of every occurrence on a candidate $\rho$, stopping on $\bot$; only then do you hold $\mathrm{val}_\rho\in K^{\mathcal{O}_P}$. Mirror the Lean signature, in which `collect` cannot be called without the admissibility proof. (3) Collection as $\mathrm{dst}_!(\mathrm{val}_\rho)$, in any grouping (Proposition 4.7), with $0_K$ on empty fibres and OR for the Boolean sort. (4) The model relation as a *check*: input agreement, admissibility, $\mathrm{Collect}_P(\rho)=\rho\vert_{\mathrm{Def}}$. That check is the oracle for testing any executor. Return a denotation only when uniqueness is established, by a proof, a successful run of the reference machine (Theorem 26.3, which needs no rank certificate), a rank certificate (Chapter 5) or a separately justified solver.

**Never implement** "iterate from zero" as the *meaning* of a program (Examples 4.1, 4.16), deduplication of statements, a zero, `nan` or skipped term for $\bot$, or the old value as an extra summand.

**For pipelines**, composing the *functions* needs an at-most-one-model certificate for each component (Proposition 4.28). The categorical proposal (its Section 6.14, summarized in Section 9.3) records an experimental Lean result that matched ranked components have at most one model, one source of such certificates. Ask for the certificate, not for more test inputs.

## 9. What this chapter did not do

- **No execution.** Chapter 5 gives the reference machine and its correspondence with the unique-model meaning.
- **No solver.** A unique model gives a denotation, not a method (Section 20.4).
- **No floating point** and **no Part V.** $K$ is exact throughout; refinement is outlined in Chapter 7.
- **No metadata-bearing interfaces**, transports, or output-only determinacy (Example 4.15).

## Exercises

1. **Admissible but not a model.** (a) Verify $\mathrm{AdmEnv}(\mathrm{Scorer})=\{\rho\mid\rho(Y)[1]>0\}$. (b) Over $\eta_0$, let $\rho$ have $Z=(0,3)$, $Y=(0,5)$, $L=0$. Compute $\Phi(\rho)$ and $\Phi(\Phi(\rho))$, and show that $\Phi$ is undefined at $\Phi(\Phi(\rho))$. (c) Explain why (b) does not by itself prove $\mathrm{Models}(\mathrm{Scorer},\eta_0)=\varnothing$, and give the argument that does.

2. **The equalizer description.** Prove Proposition 4.12 in full from the universal properties, not just the set formulas: show that a map $m:A\to\mathrm{AdmEnv}(P)$ with $\Phi_P\circ m=i\circ m$ and $\mathrm{res}_{\mathrm{In}}\circ i\circ m$ constant at $\eta$ factors uniquely through $\mathrm{Models}(P,\eta)$.

3. **A cyclic singleton.** For `T[] = 2 T[] ; T[] = X[]` (scalar input $X$, scalar defined $T$, over $\mathbb{R}$), write $\mathrm{Env}_\Sigma$, $\mathrm{AdmEnv}$, $\Phi_P$ and the parallel pair whose equalizer is $\mathrm{Fix}(P)$. Show that the fibre over each $X$ is a singleton. Which result of this chapter tells you the answer must agree with row 1 of Example 4.16, where the statements are listed in the other order? Compute the first four iterates of $\Phi_P$ from $T=0$ with $X=1$.

4. **Unique outputs, two models.** Construct a program with one scalar input $X$, one scalar output $Y$ and one private scalar $T$, such that every input has exactly two models, both with output $Y=X+1$, and the two models differ only on $T$. Write $W_P$ and its fibres. What are $\mathrm{AdmInput}(P)$ and $[\![P]\!]$?

5. **A two-statement pipeline.** Let $P$: input $X$ of shape $(2)$, output $A$ of shape $(2)$, `A[i] = 2 X[i]`. Let $Q$: input $A$, output $S$ scalar, `S[] = log(A[0])`. (a) Describe $W_P$, $W_Q$ and their legs. (b) Compute the pullback $W_P\times_{\mathrm{Env}(A)}W_Q$. (c) Write the glued program $P;Q$ and verify the bijection of Theorem 4.22 directly. (d) Compute $\mathrm{AdmInput}(P;Q)$ and check it against Proposition 4.28.

6. **Relabeling and deletion.** (a) Show that swapping $s1$ and $s2$ in `Scorer` induces a bijection of $\mathcal{O}_P$ commuting with $\mathrm{dst}$, and conclude from `Program.collect_relabel` and `Program.models_relabel` that $\mathrm{Models}$ is unchanged. (First identify the swapped program's `Models` with `P.RelabeledModels ops e` for the induced `e`.) (b) In Example 4.31, write the inclusion of the occurrence set of the one-statement program into that of the two-statement program, and show it is not a bijection. (c) Over the Boolean sort with OR, deleting a duplicate does not change the collected value. Show that $\mathrm{AdmEnv}$ and $\mathrm{Models}$ are unchanged too (compare the definedness conditions of the two occurrences), and name one thing that still differs between the two programs. (Hint: $\mathcal{O}_P$, and Chapter 5's CONTRIBUTE count.)

7. $^\ast$ **Composition in Pfn.** Prove Proposition 4.28 twice: once from Corollary 4.23 (counting "exactly one" rather than "nonempty"), and once from Proposition 0.30 together with Theorem 4.22 and Proposition 4.27. Then show that the domain and value formulas already hold under $\mathrm{AtMostOneModels}(P)$ alone, and say exactly where the first proof uses $\mathrm{AtMostOneModels}(Q)$ and where the second needs it. Finally show, using Example 4.30, that $\mathrm{AtMostOneModels}(P)$ cannot be dropped.

8. $^\ast$ **Choosing the equivalence.** (a) Prove Proposition 4.24. (b) Show that the input-output relation $\{(\ell(w),r(w))\}$ is an invariant of span isomorphism, but that equality of relations does not imply span isomorphism (Example 4.25). (c) Using Example 4.30, show that equality of denotations $[\![P]\!]=[\![P']\!]$ is not preserved by gluing with a common $Q$. (d) Conclude that among the three equivalences "same relation", "same denotation", "isomorphic spans", only the last both determines the denotation and is preserved by composition.
