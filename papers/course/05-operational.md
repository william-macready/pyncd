# Chapter 5. Operational semantics: the reference machine as a coalgebra

**Summary.** The reference machine runs a Tensor Logic program one contribution occurrence at a time: it consumes ready occurrences into accumulators, publishes a coordinate only after its whole fibre has been consumed, and stops with an explicit failure when a ready body is undefined. We package it as a finitely branching coalgebra on configurations, with store extension as a thin category, invariants as subcoalgebras, a measure for termination and a rank certificate as lax morphisms into $(\mathbb{N},\mathrm{pred})$, and we prove that it agrees with the models of Chapter 4 (the fibres $\mathrm{Models}(P,\eta)$ of the equalizer $\mathrm{Fix}(P)$): a successful run always yields the unique model, a failed run always means there is no model, and on ranked programs every maximal run does one of the two.

The semantic authority is Part IV of the specification (`papers/semantics/tensor_logic_semantics_part_iv.md`, Sections 23 to 28); results carry its number in parentheses. The Lean counterparts are in `leanncd/LeanNCD/Semantics/`: `Machine.lean`, `Readiness.lean`, `Invariants.lean`, `Soundness.lean`, `Measure.lean`, `Ranks.lean` and `Progress.lean`. Every Lean name below is copied from those files.

A word on honesty (CONVENTIONS Section 5). The specification and Lean define the machine as a *transition relation*, `Step`. The coalgebra, the observation map, the thin category and the lax morphism are this course's organization of that relation (an organizing choice of this chapter's own framing; Chapter 7 lists where the notes adjust the categorical proposal). Each categorical statement repackages a theorem about the relation, and we say which. Lean defines no $\mathcal{P}_{\mathrm{fin}}$-coalgebra.

We use [Chapter 0](00-prerequisites.md#5-algebras-and-coalgebras) for coalgebras (Definition 0.22, Example 0.23, Definitions 0.24 and 0.25, Proposition 0.26); [Chapter 3](03-partiality.md#6-read-footprints-and-stability) for read footprints, read stability and ready evaluation (Definition 3.20, Proposition 3.22, Definition 3.24); and [Chapter 4](04-denotational.md#4-models-as-an-equalizer) for $\mathrm{AdmEnv}(P)$, $\mathrm{Collect}_P$, $\Phi_P$, the equalizer $\mathrm{Fix}(P)$ with its fibres $\mathrm{Models}(P,\eta)$ (Proposition 4.12), and the [witness span](04-denotational.md#6-the-semantics-as-a-span) $W_P\cong\mathrm{Fix}(P)$ (Proposition 4.19).

## 1. From equations to steps

Chapter 4 gave a program its meaning without running anything. $\mathrm{Models}(P,\eta)$ is the set of complete environments that extend $\eta$, make every occurrence body defined, and satisfy every collection equation. It is the set of *all* fixed points of $\Phi_P$ above $\eta$: possibly empty, a point, or large. No order and no iteration were involved.

This chapter asks how a machine computes that meaning, and when it can. The naive executor does `Z[j] += ...` into a buffer and lets a reader fire as soon as something has been added to it. `Scorer` shows why that is wrong. The coordinate $Z[0]$ has two writers, $(s_1,j{=}0)$ with value $-1$ and $(s_2,j{=}0)$ with value $1$. Statement order is not semantic, so running `Scorer` as $s_2,s_3,s_1,s_4$ is as legitimate as source order; a scheduler that runs $s_3$ once any contribution to $Z[0]$ has arrived does the same thing. If $s_3$ reads $Z[0]$ after only $(s_2,j{=}0)$ has run, it computes $\mathrm{relu}(1)=1$. The model has $Y[0]=\mathrm{relu}(0)=0$. Reading a half-collected coordinate changes the answer, and no fixed text order can be the rule, because other equivalent orders break it. The specification's own example of the same trap is Section 27.1 (Example 5.34 below).

Two terms first. A *maximal run* is a run that continues until no step is enabled; a prefix that a scheduler happens to stop is not maximal (Definition 5.7). A *lax morphism* between transition systems is a map that preserves transitions without necessarily reflecting them (Definition 5.25). The target of the two lax morphisms below is $(\mathbb{N},\mathrm{pred})$ with $\mathrm{pred}(n)=\{m\mid m<n\}$: the transition system "step to any smaller number". Chapter 0 writes it $(\mathbb{N},>)$ in the well-foundedness convention, where $n\to m$ iff $m<n$.

The specification's machine fixes four obligations and four prohibitions, the operational content of CONVENTIONS facts 6 to 8.

| An executor must | Because | Spec |
| --- | --- | --- |
| consume every occurrence exactly once | each occurrence is one summand, duplicates included | 25.1, 26.1 |
| combine contributions with $\oplus$ in $K$ | a coordinate's value is its fibre sum | 25.1 |
| publish a coordinate only when no occurrence targeting it is pending | readers must see complete values | 25.2 |
| stop with an explicit failure when a ready body is $\bot$ | $\bot$ is not a scalar and not zero | 25.3 |

| An executor must not | Because | Spec |
| --- | --- | --- |
| read an accumulator | a partial sum is not the coordinate's value | 24.1, 27.1 |
| treat an absent coordinate as zero | absence means "not yet"; an empty fibre publishes $0_K$ by an explicit step | 25.2 |
| return partial outputs after a failure | a failed run proves there is no model | 25.3, 26.3 |
| pick a solution of a cycle, such as the zero accumulator | blocked is neither success nor failure | 25.4, 27.5 |

The correctness theorems split in two. "A successful run gives the unique model, and a failed run shows there is none" needs no rank certificate. "Every maximal run succeeds exactly when a model exists" needs one. Blocking can happen with zero, one or many models.

| Operational notion | Categorical reading | Lean |
| --- | --- | --- |
| store extension $\sigma\sqsubseteq\sigma'$ | a thin category on partial stores | `Extends`, `Agrees` |
| one execution step | a $\mathcal{P}_{\mathrm{fin}}$-coalgebra on configurations | `Step` |
| a property of every reachable configuration | a subcoalgebra containing the initial configuration | `reachable_invariant` |
| termination | a measure, a lax morphism into $(\mathbb{N},\mathrm{pred})$ | `step_wellFounded` |
| progress | a rank certificate, a lax morphism from the dependency coalgebra into $(\mathbb{N},\mathrm{pred})$ | `RankCertificate`, `ranked_progress` |
| correctness | operational witnesses coincide with the models, the fibres of the equalizer $\mathrm{Fix}(P)$ | `initialization_iff_singleton` |

*Why this matters for an agentic coder.* The two rule tables are a review checklist. Find where an executor consumes each occurrence, decides a coordinate is complete, handles an undefined body, and reacts when nothing can move. A "default" in any of those places is a semantic decision, usually a wrong one.

## 2. Configurations and the store-extension category

### 2.1 Partial stores and their extensions

**Definition 5.1 (partial store, store extension).** A *partial store* is a partial function $\sigma:\mathrm{Addr}_\Sigma\rightharpoonup K$ with domain $\mathrm{dom}\,\sigma$. Write $\sigma\sqsubseteq\sigma'$ when $\mathrm{dom}\,\sigma\subseteq\mathrm{dom}\,\sigma'$ and $\sigma'(a)=\sigma(a)$ on $\mathrm{dom}\,\sigma$. A complete environment $\rho$ is the total store $(T,p)\mapsto\rho(T)[p]$, so $\sigma\sqsubseteq\rho$ means $\sigma(a)=\rho(T)[p]$ for every $a=(T,p)\in\mathrm{dom}\,\sigma$ (Section 23.3 of the specification). Write $\mathrm{Ext}(\sigma)=\{\rho\in\mathrm{Env}_\Sigma\mid\sigma\sqsubseteq\rho\}$.

**Proposition 5.2 (the store category).** (a) $\sqsubseteq$ is a partial order, so it defines a *thin* category $\mathbf{St}_\Sigma$: one morphism $\sigma\to\sigma'$ exactly when $\sigma\sqsubseteq\sigma'$. (b) The complete environments are exactly the maximal objects: if $\rho$ is total and $\rho\sqsubseteq\rho'$ then $\rho=\rho'$. (c) $\mathrm{Ext}(\sigma)\ne\varnothing$, and $\sigma\sqsubseteq\sigma'$ implies $\mathrm{Ext}(\sigma')\subseteq\mathrm{Ext}(\sigma)$; so $\mathrm{Ext}$ is a functor from $\mathbf{St}_\Sigma$ to subsets of $\mathrm{Env}_\Sigma$ under reverse inclusion.

*Proof.* (a) Reflexivity and transitivity are immediate; mutual extension forces equal domains and values. In a thin category, identities are reflexivity and composition is transitivity. (b) A total store has the largest domain. A store missing $a$ has a proper extension. (c) Fill unpublished coordinates with $0_K$: "a mathematical extension for defining an interpretation, not operational permission to read missing values as zero" (Section 23.3). Antitonicity is transitivity. $\square$

Part (c) is the hinge of the chapter. As the machine publishes, the set of complete environments it is compatible with shrinks. So a statement "for every $\rho\in\mathrm{Ext}(\sigma)$, something holds" survives publication. Lemma 5.14 item 5 has this form.

In the Lean files `σ` names the declarations, and a partial store is `PartialStore K σ := (a : Address σ) → Option (Cell K σ a)` (`Types.lean`). The two relations are in `Invariants.lean`:

```lean
def Extends (p q : PartialStore K σ) : Prop :=
  ∀ a v, p a = some v → q a = some v

def Agrees (p : PartialStore K σ) (ρ : Store K σ) : Prop :=
  ∀ a v, p a = some v → ρ a = v
```

`agrees_of_extends` is the transitivity in (c). The Lean path document (`lean_executable_semantics_path_part_3.md`, Section 3.4) views this preorder "as a thin category", and warns that `Reaches` is "not an executable trace container or a formalized free-category interface".

### 2.2 Configurations

**Definition 5.3 (configurations) (Section 24.1 of the specification).** A *running configuration* is a triple $(\sigma,\alpha,U)$: $\sigma:\mathrm{Addr}_\Sigma\rightharpoonup K$ is the store of **published, complete** values; $\alpha:\mathrm{Addr}_{\mathrm{Def}}\to K$ is the *accumulator* map, which may hold only some of a coordinate's contributions; $U\subseteq\mathcal{O}_P$ is the set of *pending* occurrences. A *failed configuration* $\mathsf{Failed}(o,\sigma,\alpha,U)$ records an occurrence whose ready body was undefined and the state at failure. $\mathsf{Conf}$ is the set of all running and failed configurations.

Two access rules belong to the definition. Only $\sigma$ supplies named reads; accumulators are not readable. Published values are immutable. The reference machine keeps accumulators after publication only to simplify the conservation argument; a compiled implementation may drop them, but "this does not relax logical readiness" (Section 24.1).

```lean
structure Running (P : Program K σ r) where
  published : PartialStore K σ
  accumulators : P.Accumulator
  pending : P.Pending

inductive MachineState (P : Program K σ r)
  | running : P.Running → MachineState P
  | failed : (t : P.Defined) → P.Occurrence t → P.Running → MachineState P
```

`MachineState` (`Machine.lean`) is $\mathsf{Conf}$. Lean indexes occurrences by destination tensor: `P.Occurrence t` pairs a statement of the defined tensor `t` with an admissible valuation (`Program.lean`). So `Accumulator` and `Pending` are families over defined tensors, and `failed` carries `t` beside the occurrence. The `Running` record is $(\sigma,\alpha,U)$ at failure.

### 2.3 The initial configuration

**Definition 5.4 (initialization) (Section 24.2 of the specification).** For a well-typed input $\eta$,
$$\mathrm{Init}(P,\eta)=(\sigma_\eta,\alpha_0,\mathcal{O}_P),\qquad \mathrm{dom}\,\sigma_\eta=\mathrm{Addr}_{\mathrm{In}},\quad \sigma_\eta(T,p)=\eta(T)[p],\quad \alpha_0(a)=0_K.$$

Inputs are published, accumulators are zero, every occurrence is pending, no defined address is published. Zero accumulators are a machine operation, not a contribution; they make nothing readable.

Validation comes *before* initialization. Structural judgments and the complete input signature are checked first. Missing inputs, malformed shapes or invalid accesses are rejected explicitly, not repaired with zeros. This holds even for an input with an empty coordinate set: it must be supplied, although it adds no entry to $\sigma_\eta$. In Lean (`Models.lean`) a well-typed input is an element of the subtype `Input` of `InputBinding` cut out by `ValidInput η`, which says `∀ t, (η t).isSome = P.input t`; the comment above it reads "Presence is a tensor-level fact even when its coordinate type is empty." Initialization is then total:

```lean
def initial (η : P.Input) : P.Running where
  published := fun a => (η.val a.1).map (fun f => f a.2)
  accumulators := fun _ _ => 0
  pending := fun _ => Finset.univ
```

**Example 5.5 (`Scorer` on $\eta_1$).** The initial store publishes the eight input addresses $X=(1,-2)$, $W[0,0]=1$, $W[0,1]=1$, $W[1,0]=2$, $W[1,1]=-1$, $B=(1,0)$. The five defined addresses $(Z,0),(Z,1),(Y,0),(Y,1),(L,())$ are unpublished with accumulator $0$. All seven occurrences are pending: $U=\{(s_1,0),(s_1,1),(s_2,0),(s_2,1),(s_3,0),(s_3,1),(s_4,())\}$, where $(s_1,0)$ abbreviates $(s_1,j{=}0)$.

*Why this matters for an agentic coder.* A configuration has three parts: what readers see, private partial sums, and work still owed. An implementation with one buffer per tensor, written by `+=` and read by consumers, has merged the first two and lost the third.

## 3. The three rules and the machine as a coalgebra

### 3.1 Ready evaluation

Chapter 3 defined the read footprint (Definition 3.20) and proved read stability (Proposition 3.22, Lemma 23.1 of the specification): complete environments agreeing on $\mathrm{Read}(E,\nu)$ give equal results, including equal undefinedness. Write $\mathrm{Read}(o)=\mathrm{Read}(E_s,\nu)$ for $o=(s,\nu)$. When $\mathrm{Read}(E,\nu)\subseteq\mathrm{dom}\,\sigma$, the *ready evaluation* (Definition 3.24) is
$$\mathrm{Eval}_\sigma(E,\nu)=[\![E]\!]_{\rho,\nu}\quad\text{for any }\rho\in\mathrm{Ext}(\sigma).$$
Read stability makes the choice irrelevant; Proposition 5.2(c) makes one exist. The result is $\downarrow v$ or $\bot$. If the footprint is not published, ready evaluation is not invoked: the occurrence *waits*. Waiting is not $\bot$. Lean makes the three outcomes a type, `ReadyResult` with the function `evalReady` (`Readiness.lean`; the code is shown in [Chapter 3](03-partiality.md#6-read-footprints-and-stability), Definition 3.24):
`notReady` is waiting, `evaluated none` is $\bot$, `evaluated (some v)` is $\downarrow v$. The stability theorems are `evalWith_stable`, `interpret_stable` and `ready_consistent`; the last is the defining equation of $\mathrm{Eval}_\sigma$.

### 3.2 The rules

**Definition 5.6 (the step relation) (Sections 25.1 to 25.3 of the specification).** For CONTRIBUTE and UNDEFINED, $o=(s,\nu)\in\mathcal{O}_P$ and $a=\mathrm{dst}(o)$. For PUBLISH there is no occurrence: $a$ is any defined address not yet published, whether or not any occurrence writes to it.

$$\frac{o\in U\qquad \mathrm{Read}(o)\subseteq\mathrm{dom}\,\sigma\qquad \mathrm{Eval}_\sigma(E_s,\nu)\downarrow v}{(\sigma,\alpha,U)\longrightarrow(\sigma,\ \alpha[a\mapsto\alpha(a)\oplus v],\ U\setminus\{o\})}\ \mathrm{CONTRIBUTE}$$

$$\frac{a\in\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma\qquad U\cap\mathcal{C}_P(a)=\varnothing}{(\sigma,\alpha,U)\longrightarrow(\sigma[a\mapsto\alpha(a)],\ \alpha,\ U)}\ \mathrm{PUBLISH}$$

$$\frac{o\in U\qquad \mathrm{Read}(o)\subseteq\mathrm{dom}\,\sigma\qquad \mathrm{Eval}_\sigma(E_s,\nu)=\bot}{(\sigma,\alpha,U)\longrightarrow\mathsf{Failed}(o,\sigma,\alpha,U)}\ \mathrm{UNDEFINED}$$

Failed configurations have no outgoing steps.

A rule may fire on *any* occurrence or address satisfying its premises; source order is not a priority. CONTRIBUTE removes exactly one occurrence and combines its value once; a zero-valued body still consumes its occurrence. PUBLISH is the **completion barrier**: publication may be delayed, never early. An empty fibre makes PUBLISH enabled from the start, and it publishes $0_K$ by an explicit step. A coordinate with writers cannot be published, even with a currently zero accumulator, until all are consumed. UNDEFINED does not consume the occurrence as zero, and partially published outputs are not returned. Undefinedness is checked only for actual, ready occurrences; guard-excluded valuations and empty binders have no bodies to fail.

The Lean relation has exactly three constructors (`Machine.lean`):

```lean
inductive Step : P.MachineState → P.MachineState → Prop
  | contribute (c : P.Running) (t : P.Defined) (o : P.Occurrence t)
      (v : K (σ.signature t.val).sort)
      (pending : o ∈ c.pending t)
      (evaluated : evalReady ops c.published (P.body t o.1) o.2 = .evaluated (some v)) :
      Step (.running c) (.running (P.consume c t o v))
  | publication (c : P.Running) (t : P.Defined)
      (p : Coord (σ.signature t.val).axes)
      (unpublished : c.published ⟨t.val, p⟩ = none)
      (finished : P.FiberEmpty c t p) :
      Step (.running c) (.running (P.publish c t p))
  | undefined (c : P.Running) (t : P.Defined) (o : P.Occurrence t)
      (pending : o ∈ c.pending t)
      (evaluated : evalReady ops c.published (P.body t o.1) o.2 = .evaluated none) :
      Step (.running c) (.failed t o c)
```

The premise `evaluated` packs "footprint published" with "body defined (or undefined)", since `evalReady` otherwise returns `notReady`. `FiberEmpty c t p` is `∀ o ∈ c.pending t, P.destination t o.1 o.2 ≠ p`, that is $U\cap\mathcal{C}_P(a)=\varnothing$. `consume` adds `v` at the destination and erases `o`; `publish` copies the accumulator into the store. Note that `evalReady` is applied to `c.published` and nothing else. **Accumulators are unreadable by typing.**

### 3.3 Outcomes

**Definition 5.7 (complete, blocked, successful) (Section 25.4 of the specification).** A running configuration is *complete* when $U=\varnothing$ and $\mathrm{dom}\,\sigma=\mathrm{Addr}_\Sigma$; it determines $\rho_\sigma(T)[p]=\sigma(T,p)$. *Successful execution* is
$$\mathsf{Conf}\Downarrow\rho\iff\mathsf{Conf}\longrightarrow^\ast(\sigma,\alpha,\varnothing)\ \text{with}\ \mathrm{dom}\,\sigma=\mathrm{Addr}_\Sigma\ \text{and}\ \rho=\rho_\sigma.$$
A running configuration is *blocked* when it is not complete and has no enabled transition. A *maximal run* is a run that continues until no transition is enabled, so it ends at a failed, complete or blocked configuration; a prefix that a scheduler happens to stop is not maximal.

All defined tensors must complete, internal ones such as $Z$ included, matching the complete-model criterion of Chapter 4. The caller receives $\rho_\sigma\vert_{\mathrm{Out}}$. Blocked is neither success nor failure: it reports an unresolved dependency structure, not the absence of a model. In Lean, `Reaches` is the reflexive-transitive closure of `Step` (constructors `refl`, `tail`), and:

```lean
def Complete (c : P.Running) : Prop :=
  (∀ t, c.pending t = ∅) ∧ ∀ a, (c.published a).isSome = true

def Blocked (c : P.Running) : Prop :=
  ¬ P.Complete c ∧ ¬ ∃ s, P.Step ops (.running c) s

def Successful (η : P.Input) (c : P.Running) : Prop :=
  P.Reaches ops (.running (P.initial η)) (.running c) ∧ P.Complete c
```

`finalStore c complete` is $\rho_\sigma$, and `finalStore_published` says it agrees with the store.

### 3.4 The machine as a coalgebra

**Proposition 5.8 (the machine is finitely branching).** For every configuration $c$ the successor set $\mathrm{step}(c)=\{c'\mid c\longrightarrow c'\}$ is finite: $\lvert\mathrm{step}(\sigma,\alpha,U)\rvert\le\lvert U\rvert+\lvert\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma\rvert$ and $\mathrm{step}(\mathsf{Failed}(\dots))=\varnothing$. Hence
$$\mathrm{step}:\mathsf{Conf}\longrightarrow\mathcal{P}_{\mathrm{fin}}(\mathsf{Conf})$$
is a coalgebra for the finite powerset functor (Chapter 0, Example 0.23).

*Proof.* CONTRIBUTE and UNDEFINED name a pending $o\in U$; for a given $o$ at most one fires, with at most one $v$, because $\mathrm{Eval}_\sigma(E_s,\nu)$ is a single element of $\mathrm{Result}(\tau)$. PUBLISH names an address in $\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma$ and is determined by it. Both sets are finite, so $\mathrm{step}(c)$ is the image of a partial map defined on $U\sqcup(\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma)$, which gives the bound. No rule leaves a failed configuration. $\square$

The bound is the measure $\mu$ of Section 7. Lean states the relation, not the bound; finiteness is available as instances (`definedFintype`, `definedAddressFintype` in `Ranks.lean`; `P.Occurrence t` is finite by its definition in `Program.lean`).

**Proposition 5.9 (terminal configurations).** A configuration with no successor is exactly one of: failed, complete, or blocked.

*Proof.* Failed configurations have no successor (`failed_terminal`, `Machine.lean`). A complete configuration has $U=\varnothing$ and every address published, so no rule applies (`complete_terminal`, `Progress.lean`). A non-complete running configuration with no successor is blocked by definition. $\square$

A bare $\mathcal{P}_{\mathrm{fin}}$-coalgebra cannot tell these apart: each has $\mathrm{step}(c)=\varnothing$. As the categorical operational semantics notes put it (`categorical_operational_semantics.md`, Appendix A.4, Example 3), "having no outgoing transitions need not distinguish successful termination from a stuck state." For TL this distinction is the correctness story, so we add an observation.

**Definition 5.10 (observation map).** Let $\mathrm{Obs}=\{\mathsf{running},\mathsf{blocked}\}\sqcup\{\mathsf{complete}(\rho)\mid\rho\in\mathrm{Env}_\Sigma\}\sqcup\{\mathsf{failed}(o)\mid o\in\mathcal{O}_P\}$. Define $\mathrm{obs}:\mathsf{Conf}\to\mathrm{Obs}$ by $\mathrm{obs}(\mathsf{Failed}(o,\dots))=\mathsf{failed}(o)$, $\mathrm{obs}(c)=\mathsf{complete}(\rho_\sigma)$ for complete $c$, $\mathsf{blocked}$ for blocked $c$, and $\mathsf{running}$ otherwise.

The label $\mathsf{running}$ means "can still move", narrower than "running configuration" (Lean's `Running` includes complete and blocked triples). By Proposition 5.9, $\mathrm{obs}(c)=\mathsf{running}$ iff $\mathrm{step}(c)\ne\varnothing$. The pair $\langle\mathrm{obs},\mathrm{step}\rangle$ is a coalgebra for $X\mapsto\mathrm{Obs}\times\mathcal{P}_{\mathrm{fin}}(X)$, whose morphisms preserve outcomes as well as transitions. Lean has no observation map; it has `Complete`, `Blocked` and the constructor `failed`.

**Proposition 5.11 (steps are morphisms of stores).** If $(\sigma,\alpha,U)\longrightarrow(\sigma',\alpha',U')$, then $\sigma\sqsubseteq\sigma'$: CONTRIBUTE gives $\sigma'=\sigma$ (an identity of $\mathbf{St}_\Sigma$), and PUBLISH gives $\sigma'=\sigma[a\mapsto\alpha(a)]$ with $a\notin\mathrm{dom}\,\sigma$ (a proper extension). So every run projects to a chain in $\mathbf{St}_\Sigma$, and $\mathrm{Ext}(\sigma)$ only shrinks along a run.

*Proof.* Read off the rules; the last clause is Proposition 5.2(c). $\square$

In Lean the one-step fact is `publish_extends` (`Invariants.lean`); `consume` leaves `published` unchanged by definition. This is the precise meaning of "published values are immutable". It also explains waiting. A missing address is not a value but a coordinate on which $\mathrm{Ext}(\sigma)$ still allows anything; evaluating there would make the result depend on an arbitrary choice of $\rho$.

**Example 5.12 (the initial step set of `Scorer` on $\eta_1$).**

| Occurrence | $\mathrm{Read}(o)$ | Published? | Ready evaluation |
| --- | --- | --- | --- |
| $(s_1,0)$ | $(W,(0,0)),(W,(0,1)),(X,0),(X,1)$ | yes | $\downarrow 1\cdot1+1\cdot(-2)=-1$ |
| $(s_1,1)$ | $(W,(1,0)),(W,(1,1)),(X,0),(X,1)$ | yes | $\downarrow 2\cdot1+(-1)(-2)=4$ |
| $(s_2,0)$ | $(B,0)$ | yes | $\downarrow 1$ |
| $(s_2,1)$ | $(B,1)$ | yes | $\downarrow 0$ |
| $(s_3,0)$ | $(Z,0)$ | no | waits |
| $(s_3,1)$ | $(Z,1)$ | no | waits |
| $(s_4,())$ | $(Y,1)$ | no | waits |

No PUBLISH is enabled: every fibre is nonempty and fully pending. This includes $(Z,0)$, whose accumulator $0$ already equals its final value; the barrier asks about pending occurrences, not about the current number. So $\mathrm{step}(\mathrm{Init}(P,\eta_1))$ has exactly four elements, one CONTRIBUTE per occurrence of $s_1$ and $s_2$, against the bound $7+5=12$. Its observation is $\mathsf{running}$.

*Why this matters for an agentic coder.* `Step` can be tested rule by rule. Readiness checks the published store only; the barrier checks the pending set only; neither looks at an accumulator. A scheduler is any choice of one element of $\mathrm{step}(c)$, and Section 8 shows the choice does not affect a successful result.

## 4. Invariants are subcoalgebras

**Definition 5.13 (initial invariant, reachable set).** Fix $P$ and $\eta$. A subset $I\subseteq\mathsf{Conf}$ is an *invariant of $(P,\eta)$* when $\mathrm{Init}(P,\eta)\in I$ and $c\in I$, $c\longrightarrow c'$ imply $c'\in I$. The *reachable set* is $\mathrm{Reach}(P,\eta)=\{c\mid\mathrm{Init}(P,\eta)\longrightarrow^\ast c\}$.

Chapter 0 (Definition 0.24) calls any transition-closed subset an *invariant* or subcoalgebra, with no condition on the initial configuration; an invariant of $(P,\eta)$ is such a subset that also contains $\mathrm{Init}(P,\eta)$. A transition-closed $I$ carries the restriction $\mathrm{step}\vert_I:I\to\mathcal{P}_{\mathrm{fin}}(I)$, and $I\hookrightarrow\mathsf{Conf}$ is a coalgebra morphism. $\mathrm{Reach}(P,\eta)$ is the *smallest* invariant of $(P,\eta)$: it is one, and induction on run length puts it inside every other. So to prove a property of every reachable configuration, exhibit an invariant of $(P,\eta)$ inside the set where the property holds. In Lean this is induction on `Reaches`, whose constructors are "the start" and "one more step".

**Lemma 5.14 (conservation) (Lemma 26.1 of the specification).** At every reachable running configuration $(\sigma,\alpha,U)$:

1. $U\subseteq\mathcal{O}_P$, and every CONTRIBUTE step removes one previously pending occurrence. No occurrence is consumed twice.
2. Accumulators and published values belong to $K$.
3. Published addresses only increase, input values remain unchanged, and no published value is overwritten.
4. If a defined address is published, no occurrence targeting it is pending, and its published value equals its accumulator.
5. Every consumed $o=(s,\nu)\in\mathcal{O}_P\setminus U$ has a recorded value $v_o$, the value returned when it was consumed, and for every complete $\rho$ with $\sigma\sqsubseteq\rho$, $[\![E_s]\!]_{\rho,\nu}$ is defined and equals $v_o$.

Moreover, for every defined address $a$,
$$\alpha(a)=\bigoplus_{o\in\mathcal{C}_P(a)\setminus U}v_o.$$

The values $v_o$ belong to the run's history; they need not be machine fields (Section 26.1).

*Proof.* Induction on reachability.

*Initial configuration.* $U=\mathcal{O}_P$, so items 1 and 5 are vacuous and the formula is the empty sum $0_K=\alpha_0(a)$. Only inputs are published, with the values of $\eta$.

*CONTRIBUTE at $o$, value $v$, $a=\mathrm{dst}(o)$.* Item 1 is the premise $o\in U$. The store is unchanged, giving item 3. For item 4: since $o\in U$ targets $a$, item 4 at the old configuration says $a$ is unpublished, so the only accumulator that changes is unpublished. The consumed part of $a$'s fibre gains $o$ and $\alpha(a)$ gains $v=v_o$, so the formula holds. For item 5, the new $o$ had $\mathrm{Read}(o)\subseteq\mathrm{dom}\,\sigma$ and $\mathrm{Eval}_\sigma(E_s,\nu)=\downarrow v$, so by the definition of ready evaluation, which rests on read stability, $[\![E_s]\!]_{\rho,\nu}=\downarrow v$ for *every* $\rho\in\mathrm{Ext}(\sigma)$.

*PUBLISH at $a$.* The premise $a\notin\mathrm{dom}\,\sigma$ gives item 3. The premise $U\cap\mathcal{C}_P(a)=\varnothing$ and $\sigma'(a)=\alpha(a)$ give item 4 at $a$. Item 5 survives because $\mathrm{Ext}(\sigma')\subseteq\mathrm{Ext}(\sigma)$ (Proposition 5.2(c)).

*UNDEFINED.* The failed configuration records the old state unchanged.

Every other item is preserved because the data it mentions is unchanged or $U$ only shrinks: item 5 for earlier consumed occurrences under CONTRIBUTE since $\sigma$ is unchanged, item 4 at a published $b\ne a$ since $\alpha(b)$ is unchanged, and the accumulator formula under PUBLISH since $\alpha$ and $U$ are unchanged. Item 2 is typing. $\square$

**The role of read stability.** Item 5 is where the operational and denotational worlds touch. The machine evaluated the body once, against a partial store; the model equations evaluate it against complete environments. Read stability makes these agree for every extension of the store at consumption time, and Proposition 5.11 says the store only grows afterwards. No model and no admissibility hypothesis is needed. This is also why footprints are strict (Chapter 3): `at` reads its whole array argument and $0\otimes E$ still reads $E$. Dropping the whole array of `at`, or the zero side of a product, would let the machine evaluate a body whose definedness is not yet determined. Footprints are sufficient, not minimal (Chapter 3, end of Section 6); only strict cases like these are at issue.

**Lean.** The invariant is a structure (`Invariants.lean`):

```lean
structure Invariant (η : P.Input) (c : P.Running) (values : P.History) : Prop where
  inputs : ∀ t f, η.val t = some f → ∀ p, c.published ⟨t, p⟩ = some (f p)
  published : ∀ t p v, c.published ⟨t.val, p⟩ = some v →
    P.FiberEmpty c t p ∧ v = c.accumulators t p
  conservation : ∀ t p, c.accumulators t p = P.spent c.pending values t p
  consumed : ∀ t o, o ∉ c.pending t → ∀ ρ, Agrees c.published ρ →
    P.outcome ops ρ t o = some (values t o)
```

| Lemma 5.14 | Lean |
| --- | --- |
| item 3, inputs unchanged | `Invariant.inputs` |
| item 3, published addresses only increase | `publish_extends` (one step) |
| item 4 | `Invariant.published` |
| accumulator formula | `Invariant.conservation`, with `spent` the sum over consumed occurrences |
| item 5 | `Invariant.consumed`; `Agrees c.published ρ` is $\sigma\sqsubseteq\rho$ |
| recorded values $v_o$ | `values : P.History`, updated by `record` |
| items 1 and 2 | step premises (`pending`, `Finset.erase`) and typing |

The cases are `initial_invariant`, `consume_invariant` and `publish_invariant`, assembled by `reachable_invariant` into `StateInvariant`. On `.failed t o c`, `StateInvariant` asserts the invariant for the recorded `c`, plus `o ∈ c.pending t` and `evalReady ... = .evaluated none`. The history is existentially quantified, matching the remark above. Item 5 for a new occurrence uses `evaluated_consistent`, which is read stability in the form "a ready result equals the interpretation in any agreeing complete store".

**Example 5.15.** Rows 1 to 3 of Example 5.32 below give $\alpha(Z,0)=-1\oplus1=0$ and $\alpha(Z,1)=4$ by the formula. Item 5 holds for $(s_1,0)$ because its body reads only inputs, so every $\rho$ extending them evaluates it to $-1$.

*Why this matters for an agentic coder.* An invariant is a checkable contract. Item 4 can be asserted at each publication; the accumulator formula can be checked by replaying recorded contributions. Any change to the rules must keep the reachable set inside the invariant, or every theorem downstream stops applying.

## 5. Every candidate model is preserved

**Lemma 5.16 (preservation of every candidate model) (Lemma 26.2 of the specification).** At every reachable running configuration $(\sigma,\alpha,U)$:

(a) For every defined $a=(T,p)$ and every complete $\rho$ with $\sigma\sqsubseteq\rho$,
$$\alpha(a)=\bigoplus_{(s,\nu)\in\mathcal{C}_P(a)\setminus U}[\![E_s]\!]_{\rho,\nu},$$
with every term defined. If moreover the fibre of $a$ has no pending occurrence and $\rho\in\mathrm{AdmEnv}(P)$, then $\alpha(a)=\mathrm{Collect}_P(\rho)(T)[p]$.

(b) For every $\rho\in\mathrm{Models}(P,\eta)$, $\sigma\sqsubseteq\rho$.

(c) If $\mathrm{Models}(P,\eta)\ne\varnothing$, no reachable configuration is $\mathsf{Failed}$.

*Proof.* (a) By Lemma 5.14 item 5 each term is defined and equals $v_{(s,\nu)}$, so the sum is the accumulator formula. A finished fibre is all of $\mathcal{C}_P(a)$, which gives $\mathrm{Collect}_P(\rho)(T)[p]$. No model is used.

(b) Induction on reachability, for a fixed model $\rho$. Initially $\sigma_\eta\sqsubseteq\rho$ since $\rho\vert_{\mathrm{In}}=\eta$. CONTRIBUTE leaves $\sigma$ unchanged. At PUBLISH on $a=(T,p)$: the induction hypothesis gives $\sigma\sqsubseteq\rho$, the fibre is finished, and $\rho$ is admissible. Part (a) gives $\alpha(a)=\mathrm{Collect}_P(\rho)(T)[p]$, and the model equation gives $\rho(T)[p]$. So the new value agrees with $\rho$.

(c) Suppose a reachable configuration takes UNDEFINED at $o=(s,\nu)$, and $\rho$ is a model. By (b) $\rho\in\mathrm{Ext}(\sigma)$, so read stability gives $[\![E_s]\!]_{\rho,\nu}=\mathrm{Eval}_\sigma(E_s,\nu)=\bot$, contradicting $\rho\in\mathrm{AdmEnv}(P)$. $\square$

In $\mathbf{St}_\Sigma$, part (b) says every reachable store is a *lower bound* of $\mathrm{Models}(P,\eta)$. With many models, the machine publishes only values on which all of them agree: the operational meaning of "the machine does not pick a fixed point". PUBLISH is the only rule that changes $\sigma$, and its premise supplies the finished-fibre hypothesis of the second clause of (a); the model supplies admissibility. The completion barrier is what makes (b) inductive.

**Lean.** Parts (b) and (c) are one theorem (`Soundness.lean`), propagating a predicate that is false on failed states:

```lean
def CandidateAgreement (ρ : Store K σ) : P.MachineState → Prop
  | .running c => Agrees c.published ρ
  | .failed _ _ _ => False

theorem candidate_preserved (η : P.Input) (ρ : Store K σ) (model : P.Models ops η ρ)
    {s : P.MachineState} (reached : P.Reaches ops (.running (P.initial η)) s) :
    P.CandidateAgreement ρ s := by
```

Its `publication` case uses `finished_accumulator`, the finished-fibre clause of (a); its `undefined` case uses `evaluated_consistent` against admissibility. The specification's status table marks Lemma 26.2 as partial in Lean: the partial-fibre sum in (a) "follows from `Invariant.conservation` and `Invariant.consumed` and is not stated separately in Lean".

**Example 5.17 (the barrier at $Z[0]$).** Let $\rho^\ast$ be the model on $\eta_1$: $Z=(0,4)$, $Y=(0,4)$, $L=\log4$. When $(Z,0)$ is published, both its occurrences are consumed, and (a) gives $\alpha(Z,0)=-1+1=0=\rho^\ast(Z)[0]$. Exercise 2 drops the barrier.

*Why this matters for an agentic coder.* Lemma 5.16(b) is the property to protect when optimizing. Any fusion, early release or speculative read must keep "everything published agrees with every model". The practical test: a value is safe to expose exactly when no contribution to it is outstanding.

## 6. Success gives the unique model; failure excludes all models

**Theorem 5.18 (successful and failed runs) (Theorem 26.3 of the specification).** (i) If $\mathrm{Init}(P,\eta)\Downarrow\rho_\sigma$, then $\mathrm{Models}(P,\eta)=\{\rho_\sigma\}$ and $[\![P]\!](\eta)=\rho_\sigma\vert_{\mathrm{Out}}$. (ii) If $\mathrm{Init}(P,\eta)\longrightarrow^\ast\mathsf{Failed}(o,\sigma,\alpha,U)$, then $\mathrm{Models}(P,\eta)=\varnothing$.

*Proof.* (i) Let $(\sigma,\alpha,\varnothing)$ be the complete final configuration and $\rho=\rho_\sigma$, so $\sigma\sqsubseteq\rho$. *Admissibility:* every occurrence is consumed, so by item 5 with this $\rho$ every body is defined, with value $v_o$. *Inputs:* unchanged by item 3. *Equations:* for defined $a=(T,p)$, item 4 gives $\rho(T)[p]=\sigma(a)=\alpha(a)$, and the accumulator formula with $U=\varnothing$ gives $\alpha(a)=\bigoplus_{o\in\mathcal{C}_P(a)}v_o=\mathrm{Collect}_P(\rho)(T)[p]$. So $\rho$ is a model. *Uniqueness:* for any model $\rho'$, Lemma 5.16(b) gives $\sigma\sqsubseteq\rho'$; $\sigma$ is total, hence maximal in $\mathbf{St}_\Sigma$ (Proposition 5.2(b)), so $\rho'=\rho_\sigma$. (ii) Lemma 5.16(c). $\square$

**Remark 5.19 (no rank certificate is needed).** Two separate points. First, the *proof* of Theorem 5.18 uses no rank certificate, and the theorem holds for every well-formed program, cyclic ones included, and under any schedule. Second, it does *not* say a run will succeed when a model exists, or fail when none does: a run can block, and blocking says nothing about models. Those converse directions are the job of the certificate (Section 8). This split is CONVENTIONS fact 8.

A caution about what the theorem's parts say about cyclic programs. A successful run itself witnesses acyclicity of the dependency graph. Order the addresses by the step at which each is published (inputs at step 0). If $b\in\mathrm{Dep}(a)$, some occurrence in the fibre of $a$ reads $b$; that occurrence was consumed before $a$ was published (the barrier), and it was consumed only once $b$ was published (readiness). So $b$ is published strictly before $a$, and publication time is a rank certificate. A program with a dependency cycle therefore never succeeds on any input (Exercise 8 asks for the details). Part (i), which concerns successful runs, therefore has content only for programs that could have been ranked; its point is that the scheduler need not know or check the certificate. Part (ii), which concerns failed runs, applies to every program, including cyclic ones.

**Lean.** The theorems in `Soundness.lean` take no certificate:

```lean
theorem successful_model (η : P.Input) (c : P.Running) (success : P.Successful ops η c) :
    P.Models ops η (P.finalStore c success.2) := by

theorem successful_unique (η : P.Input) (c : P.Running) (success : P.Successful ops η c) :
    ∀ ρ, P.Models ops η ρ → ρ = P.finalStore c success.2 := by

theorem failed_no_model (η : P.Input) (t : P.Defined) (o : P.Occurrence t) (c : P.Running)
    (reached : P.Reaches ops (.running (P.initial η)) (.failed t o c)) :
    ¬ ∃ ρ, P.Models ops η ρ := by
```

The same file packages (i) as `successful_admInput` and `successful_denotation`. The proof of `successful_unique` is `candidate_preserved` followed by function extensionality with `finalStore_published`: the "total stores are maximal" step.

**Example 5.20.** On $\eta_1$ the run of Example 5.32 ends with $Z=(0,4)$, $Y=(0,4)$, $L=\log4$, and Theorem 5.18(i) proves this is the only model, without the level-by-level argument of Chapter 1, Section 4.4. On $\eta_0$ a run reaches $\mathsf{Failed}((s_4,()),\dots)$ (Example 5.33), proving $\mathrm{Models}(P,\eta_0)=\varnothing$. Chapter 1, Section 4.5 needed an argument about all candidate environments; the machine needed one run.

*Why this matters for an agentic coder.* A successful run certifies the denotation and a failed run certifies its absence, whatever scheduler produced them, provided it took only legal steps. A blocked run must never be reported as either.

## 7. Termination

**Lemma 5.21 (finite execution) (Lemma 26.4 of the specification).** For a running configuration let
$$\mu(\sigma,\alpha,U)=\lvert U\rvert+\lvert\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma\rvert.$$
CONTRIBUTE decreases the first term by one, PUBLISH the second by one, and UNDEFINED leads to a terminal configuration. Hence every run from $\mathrm{Init}(P,\eta)$ has at most $\lvert\mathcal{O}_P\rvert+\lvert\mathrm{Addr}_{\mathrm{Def}}\rvert$ non-failure steps plus at most one failing step.

*Proof.* CONTRIBUTE removes one occurrence from $U$ and fixes $\sigma$; PUBLISH adds one defined address and fixes $U$. Initially $\mu=\lvert\mathcal{O}_P\rvert+\lvert\mathrm{Addr}_{\mathrm{Def}}\rvert$, and $\mu\ge0$. A failed configuration has no successor. $\square$

**Corollary 5.22 (the machine coalgebra is well-founded).** (a) $(\mathsf{Conf},\mathrm{step})$ is well-founded (Chapter 0, Definition 0.25). (b) From every configuration there is a maximal run; every maximal run is finite and ends at a failed, complete or blocked configuration (Proposition 5.9). (c) $\mathrm{Reach}(P,\eta)$ is finite.

*Proof.* (a) Send running configurations to $\mu+1$ and failed ones to $0$; call this function $\bar\mu$. Every step strictly decreases it, so Chapter 0, Proposition 0.26(a) applies. (b) Step while possible. (c) The tree of runs is finitely branching (Proposition 5.8) with no infinite branch, so it is finite by König's lemma. $\square$

No fairness assumption is needed: fairness matters only when an infinite run could starve an enabled action, and there are none.

A successful run is exact, not just bounded: a complete configuration has $U=\varnothing$ and every defined address published, so $\mu=0$, and every step decreased $\mu$ by exactly one. Hence every successful run has exactly $\lvert\mathcal{O}_P\rvert$ CONTRIBUTE steps and $\lvert\mathrm{Addr}_{\mathrm{Def}}\rvert$ PUBLISH steps, whatever the schedule.

The modified measure is Lean's `stateMeasure` (`Measure.lean`): `.running c` maps to `P.measure c + 1` and `.failed _ _ _` to `0`. The main results:

```lean
theorem step_wellFounded : WellFounded (fun b a => P.Step ops a b) :=

theorem no_infinite_chain (f : Nat → P.MachineState) :
    ¬ ∀ n, P.Step ops (f n) (f (n + 1)) := by
```

`step_wellFounded` says the *converse* of `Step` is well-founded, Lean's form of "no infinite forward run". Supporting lemmas: `initial_measure` (the measure of `initial η` is `P.occurrenceCount + Fintype.card P.DefinedAddress`), `consume_measure`, `publish_measure`, `step_decreases`. For counted traces `Trace n a b`, `running_trace_bound` gives `n ≤ P.measure c` and `failed_trace_bound` gives `n ≤ P.measure c + 1`. In `Progress.lean`, `terminal_extension` and `maximal_extension` produce a terminal reachable state by well-founded induction. Lean's `Maximal η s` is a property of a *state* (reachable and `Terminal`), not a run object.

**Remark 5.23 (the measure as a lax morphism).** Recall $\mathrm{pred}(n)=\{m\mid m<n\}=[n]$ from Section 1, so $(\mathbb{N},\mathrm{pred})$ is Chapter 0's $(\mathbb{N},>)$. The extended measure $\bar\mu$ of Corollary 5.22 satisfies $\bar\mu[\mathrm{step}(c)]\subseteq\mathrm{pred}(\bar\mu(c))$: it preserves transitions without reflecting them, as Chapter 0 observes after Proposition 0.26. Section 8 calls such maps lax morphisms and meets a second one.

For `Scorer` on $\eta_1$, $\mu$ starts at $7+5=12$ and every maximal run has exactly $12$ steps (every such run succeeds, by Theorem 5.28(2) below, so it consumes all 7 occurrences and publishes all 5 addresses). On $\eta_0$, the run of Example 5.33 takes $10$ non-failure steps, from $\mu=12$ to $\mu=2$, then one UNDEFINED step.

*Why this matters for an agentic coder.* Termination needs no analysis of the program, so a reference run on a small input is always a finite, checkable computation. What termination does not give is an answer: a run can terminate blocked.

## 8. Ranks and progress

### 8.1 Dependencies

**Definition 5.24 (dependencies) (Section 23.4 of the specification).** For a defined address $a$, $\mathrm{Dep}(a)=\bigcup_{o\in\mathcal{C}_P(a)}\mathrm{Read}(o)$; for input addresses $\mathrm{Dep}(a)=\varnothing$.

Each $b\in\mathrm{Dep}(a)$ must be published before the writer of $a$ that reads it can be consumed, hence before $a$ can be published. It depends on indices, guards and binder domains, never on tensor values: it is a property of the program, not of an input. In Lean (`Ranks.lean`):

```lean
def dependencies (P : Program K σ r) (a : Address σ) : Set (Address σ) :=
  {b | ∃ (t : P.Defined) (o : P.Occurrence t),
    a = ⟨t.val, P.destination t o.1 o.2⟩ ∧ b ∈ footprint (P.body t o.1) o.2}
```

Inputs have no writers, so this gives them no dependencies (`input_dependencies_empty`). For `Scorer`:

| Address $a$ | $\mathrm{Dep}(a)$ |
| --- | --- |
| input addresses | $\varnothing$ |
| $(Z,j)$ | $(W,(j,0)),(W,(j,1)),(X,0),(X,1),(B,j)$ |
| $(Y,j)$ | $(Z,j)$ |
| $(L,())$ | $(Y,1)$ |

### 8.2 Rank certificates as lax morphisms

Since $\mathrm{Addr}_\Sigma$ is finite, $\mathrm{Dep}:\mathrm{Addr}_\Sigma\to\mathcal{P}_{\mathrm{fin}}(\mathrm{Addr}_\Sigma)$ is a $\mathcal{P}_{\mathrm{fin}}$-coalgebra, the *dependency coalgebra*: a transition goes from an address to something it waits on.

**Definition 5.25 (lax morphism; rank certificate) (Section 23.4 of the specification).** For $\mathcal{P}_{\mathrm{fin}}$-coalgebras $(A,\gamma)$, $(B,\delta)$, a *lax morphism* (or *simulation*) is a function $h:A\to B$ with $h[\gamma(x)]\subseteq\delta(h(x))$ for every $x$. A *rank certificate* for $P$ is a lax morphism $r:(\mathrm{Addr}_\Sigma,\mathrm{Dep})\to(\mathbb{N},\mathrm{pred})$ (the target of Section 1), that is,
$$r[\mathrm{Dep}(a)]\subseteq\{m\mid m<r(a)\}\quad\text{for every }a,$$
equivalently $b\in\mathrm{Dep}(a)\Rightarrow r(b)<r(a)$. The *coordinate-ranked fragment* is the set of programs that have one.

The two forms are the same by unfolding. Lean uses the second (`Ranks.lean`):

```lean
structure RankCertificate (P : Program K σ r) where
  rank : Address σ → Nat
  decreases : ∀ a b, b ∈ P.dependencies a → rank b < rank a
```

**Why lax and not strict.** A strict coalgebra morphism requires *equality*, $r[\mathrm{Dep}(a)]=\{m\mid m<r(a)\}$. By Chapter 0, Example 0.23 that means preserving *and* reflecting transitions: every number below $r(a)$ would be the rank of a dependency of $a$. In `Scorer`, $\mathrm{Dep}(L,())=\{(Y,1)\}$ has one element, so a strict morphism forces $r(L,())=1$, then $r(Y,1)=0$, and then $\varnothing=\{m\mid m<0\}$ would have to equal $\{r(Z,1)\}$. So `Scorer` has no strict morphism into $(\mathbb{N},\mathrm{pred})$, although its dependencies are plainly well ordered. What we need is one-directional, "every dependency step goes down", and inclusion says exactly that. The certificate $r=0$ on inputs, $r(Z,j)=1$, $r(Y,j)=2$, $r(L,())=3$ is lax.

**Proposition 5.26 (rank certificates witness well-foundedness).** For a $\mathcal{P}_{\mathrm{fin}}$-coalgebra $(A,\mathrm{Dep})$ with $A$ finite, the following are equivalent: (1) a lax morphism $(A,\mathrm{Dep})\to(\mathbb{N},\mathrm{pred})$ exists; (2) $(A,\mathrm{Dep})$ is well-founded, with no infinite chain $a_{k+1}\in\mathrm{Dep}(a_k)$; (3) the graph with an edge $b\to a$ for each $b\in\mathrm{Dep}(a)$ is acyclic.

*Proof.* (1 ⇒ 2) A chain gives $r(a_0)>r(a_1)>\cdots$ in $\mathbb{N}$. (2 ⇒ 3) Going round a cycle forever is a chain. (3 ⇒ 2) An infinite chain in a finite set repeats, giving a cycle. (2 ⇒ 1) The *height* $h(a)=0$ if $\mathrm{Dep}(a)=\varnothing$, else $1+\max\{h(b)\mid b\in\mathrm{Dep}(a)\}$, is defined by well-founded recursion and satisfies $h(b)<h(a)$; Exercise 5 asks for details. $\square$

Item 3 is the specification's own reformulation (Section 23.4). The pattern is the measure's: the machine coalgebra has a lax morphism $\bar\mu$ into $(\mathbb{N},\mathrm{pred})$, witnessing that *runs* are finite (termination, for every program); the dependency coalgebra has $r$ into the same target, witnessing that *waiting* is finite (progress, for ranked programs only).

Three remarks from Section 23.4. The certificate guarantees dependency progress, not definedness: a ranked program can still fail. A compiler may justify it with symbolic ranks, such as $r(H,(i,l))=l+1$. And dependencies are taken at coordinate level, so a finite history may read the tensor it defines (Example 5.35).

### 8.3 Progress and correspondence

**Theorem 5.27 (ranked progress) (Theorem 26.5 of the specification).** If $P$ has a rank certificate, every reachable, non-complete running configuration has an enabled transition. No reachable configuration is blocked.

*Proof.* *Some defined address is unpublished.* Otherwise, with inputs published (item 3), $\mathrm{dom}\,\sigma=\mathrm{Addr}_\Sigma$; by item 4 no fibre has a pending occurrence, and every occurrence lies in its destination's fibre, so $U=\varnothing$ and the configuration is complete. *Pick one of minimal rank,* $a$. Every $b\in\mathrm{Dep}(a)$ is published: inputs were published initially, and a defined $b$ has $r(b)<r(a)$. *A rule fires at $a$.* A pending $o$ in its fibre has $\mathrm{Read}(o)\subseteq\mathrm{Dep}(a)\subseteq\mathrm{dom}\,\sigma$, so it is ready and enables CONTRIBUTE ($\downarrow v$) or UNDEFINED ($\bot$). With no pending occurrence, PUBLISH is enabled. $\square$

In `Progress.lean` the first step is `unpublished_of_noncomplete` (with `invariant_input_available`), and the minimum is taken with `Nat.find`:

```lean
theorem ranked_progress (certificate : P.RankCertificate) (η : P.Input) (c : P.Running)
    (reached : P.Reaches ops (.running (P.initial η)) (.running c))
    (incomplete : ¬ P.Complete c) : ∃ s, P.Step ops (.running c) s := by

theorem ranked_not_blocked (certificate : P.RankCertificate) (η : P.Input) (c : P.Running)
    (reached : P.Reaches ops (.running (P.initial η)) (.running c)) :
    ¬ P.Blocked ops c := by
```

**Theorem 5.28 (ranked correspondence) (Theorem 26.6 of the specification).** Let $P$ have a rank certificate. (1) Every maximal run from $\mathrm{Init}(P,\eta)$ succeeds or fails explicitly. (2) If a model exists, every maximal run succeeds and returns it. (3) If no model exists, every maximal run fails. (4) Consequently
$$\mathrm{Init}(P,\eta)\Downarrow\rho\iff\mathrm{Models}(P,\eta)=\{\rho\}.$$

*Proof.* (1) A maximal run ends terminal (Corollary 5.22), not blocked (Theorem 5.27), hence failed or complete (Proposition 5.9), and a reachable complete configuration is a success. (2) A model excludes failure (Lemma 5.16(c)), so the run succeeds, with the unique model (Theorem 5.18(i)). (3) Success would produce a model. (4) Forward is Theorem 5.18(i), with no certificate. Backward: a maximal run exists (Corollary 5.22(b)) and succeeds with $\rho$ by (2). $\square$

In `Progress.lean`:

```lean
theorem maximal_dichotomy (certificate : P.RankCertificate) (η : P.Input)
    (s : P.MachineState) (maximal : P.Maximal ops η s) :
    (∃ c, s = .running c ∧ P.Successful ops η c) ∨
      (∃ t o c, s = .failed t o c ∧ ¬ ∃ ρ, P.Models ops η ρ) := by
```

Items 2 and 3 are `model_maximal_success` and `no_model_maximal_failure`. Item 4 is `initialization_iff_singleton`, whose right side is literally `{ρ' | P.Models ops η ρ'} = {ρ}`. All take a `RankCertificate`.

**Corollary 5.29 (ranked uniqueness) (Corollary 26.7 of the specification).** A ranked program has at most one model on any well-typed input.

*Proof.* A model forces every maximal run to succeed (Theorem 5.28(2)); one exists (Corollary 5.22); a successful run has a unique model (Theorem 5.18(i)). $\square$

Lean has no separate theorem; the status table says it "follows from `model_maximal_success`, `maximal_extension` and `successful_unique`".

**Proposition 5.30 (schedule independence) (Section 26.4 of the specification, after Corollary 26.7).** Any two successful runs from $\mathrm{Init}(P,\eta)$ end with the same environment, whatever their order of events. No certificate is needed. On a failing input, different schedules may report different undefined occurrences.

*Proof.* Both final environments are the unique model (Theorem 5.18(i)). $\square$

Lean's `successful_schedules_agree` (`Progress.lean`) takes two `Successful` states and no certificate. For the second part, take `A[] = log(X[])` and `C[] = log(X[])` with $X=0$: both occurrences are ready and undefined at the start, so one maximal run fails at the writer of $A$, another at the writer of $C$. Both prove $\mathrm{Models}=\varnothing$; they differ only in the diagnostic.

**Remark 5.31 (production readiness is a strict subset).** The production profile (Section 23.4, Remark) orders whole tensors: a tensor is ready only when every statement defining it has run, and a tensor-level cycle is rejected, apart from a scan node's reads of its own state. Accepted programs have a coordinate certificate; the converse fails. `Scorer` is production-ready ($\{X,W,B\}\to Z\to Y\to L$). An illustration of the converse: $A$ of shape $(2)$, $B$ of shape $(1)$, scalar input $X$, statements

```text
A[0] = X[]
B[0] = A[0]
A[1] = B[0]
```

Coordinatewise $r(X,())=0$, $r(A,0)=1$, $r(B,0)=2$, $r(A,1)=3$ is a certificate. At tensor level, though, $A$ reads $B$ and $B$ reads $A$, a cycle $A\to B\to A$ that is not a scan node's read of its own state, so production rejects it.

*Why this matters for an agentic coder.* The certificate turns "the machine might answer" into "the machine always answers", and makes *any* legal scheduler correct, which licenses any out-of-order interleaving of single steps; parallel or batched execution additionally needs the refinement argument of Chapter 7. Without one, Theorem 5.18 still says how to read success and failure; a blocked run must be reported as unsupported, never as a value.

## 9. Worked runs

### 9.1 The running example on $\eta_1$

**Example 5.32 (a complete schedule on $\eta_1$).** One maximal run. "Value" is the ready evaluation consumed; accumulators and $\mu$ are shown after the step.

| # | Rule | Target | Value | $\alpha(Z,0)$ | $\alpha(Z,1)$ | $\alpha(Y,0)$ | $\alpha(Y,1)$ | $\alpha(L,())$ | Newly published | $\mu$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | Init | | | 0 | 0 | 0 | 0 | 0 | the 8 inputs | 12 |
| 1 | CONTRIBUTE | $(s_1,0)$ | $-1$ | $-1$ | 0 | 0 | 0 | 0 | | 11 |
| 2 | CONTRIBUTE | $(s_1,1)$ | $4$ | $-1$ | 4 | 0 | 0 | 0 | | 10 |
| 3 | CONTRIBUTE | $(s_2,0)$ | $1$ | 0 | 4 | 0 | 0 | 0 | | 9 |
| 4 | PUBLISH | $(Z,0)$ | | 0 | 4 | 0 | 0 | 0 | $Z[0]=0$ | 8 |
| 5 | CONTRIBUTE | $(s_2,1)$ | $0$ | 0 | 4 | 0 | 0 | 0 | | 7 |
| 6 | PUBLISH | $(Z,1)$ | | 0 | 4 | 0 | 0 | 0 | $Z[1]=4$ | 6 |
| 7 | CONTRIBUTE | $(s_3,0)$ | $\mathrm{relu}(0)=0$ | 0 | 4 | 0 | 0 | 0 | | 5 |
| 8 | CONTRIBUTE | $(s_3,1)$ | $\mathrm{relu}(4)=4$ | 0 | 4 | 0 | 4 | 0 | | 4 |
| 9 | PUBLISH | $(Y,0)$ | | 0 | 4 | 0 | 4 | 0 | $Y[0]=0$ | 3 |
| 10 | PUBLISH | $(Y,1)$ | | 0 | 4 | 0 | 4 | 0 | $Y[1]=4$ | 2 |
| 11 | CONTRIBUTE | $(s_4,())$ | $\log 4$ | 0 | 4 | 0 | 4 | $\log4$ | | 1 |
| 12 | PUBLISH | $(L,())$ | | 0 | 4 | 0 | 4 | $\log4$ | $L=\log4$ | 0 |

Seven CONTRIBUTE steps, one per occurrence; five PUBLISH steps, one per defined address. The final $\rho_\sigma$ is $Z=(0,4)$, $Y=(0,4)$, $L=\log4$, the model of Chapter 1, Section 4.4. Points to check:

- **$Z[0]$ is published only at step 4**, after both its occurrences are consumed. At step 0 its accumulator already holds the final $0$, at step 1 it holds $-1$; in neither is PUBLISH enabled, because the fibre has a pending occurrence.
- **$(s_3,0)$ waits until step 4**, since $(Z,0)\notin\mathrm{dom}\,\sigma$. The accumulator exists all along and is never read.
- **Step 5 consumes a zero.** $\alpha(Z,1)$ is unchanged, but the occurrence must still be consumed before $(Z,1)$ can be published.
- **Other schedules exist**, for instance $(s_3,0)$ right after step 4. By Proposition 5.30 every successful schedule ends with the same $\rho_\sigma$ (Exercise 1).

### 9.2 The failing input $\eta_0$

**Example 5.33 (a failing run on $\eta_0$).** Now $X=(0,0)$, so $Z=(1,0)$ and $Y=(1,0)$.

| # | Rule | Target | Value | Newly published | $\mu$ |
| --- | --- | --- | --- | --- | --- |
| 1 to 4 | CONTRIBUTE | $(s_1,0),(s_1,1),(s_2,0),(s_2,1)$ | $0,0,1,0$ | | 8 |
| 5, 6 | PUBLISH | $(Z,0),(Z,1)$ | | $Z=(1,0)$ | 6 |
| 7, 8 | CONTRIBUTE | $(s_3,0),(s_3,1)$ | $\mathrm{relu}(1)=1$, $\mathrm{relu}(0)=0$ | | 4 |
| 9, 10 | PUBLISH | $(Y,0),(Y,1)$ | | $Y=(1,0)$ | 2 |
| 11 | UNDEFINED | $(s_4,())$ | $\log0=\bot$ | | |

At step 11 the footprint $\{(Y,1)\}$ is published, so $(s_4,())$ is ready, and its evaluation is $\bot$. The machine moves to $\mathsf{Failed}\big((s_4,()),\sigma,\alpha,\{(s_4,())\}\big)$, with $\sigma$ holding the inputs, $Z$ and $Y$, and $\alpha(L,())=0$. The published $Y$ is *not* returned, and $L$ is not reported as $0$. By Theorem 5.18(ii), $\mathrm{Models}(P,\eta_0)=\varnothing$.

This is one maximal run: it publishes all of $Z$ and $Y$ and then fails, as Chapter 1, Section 4.5 describes. Other maximal runs reach UNDEFINED at the same occurrence after fewer steps. The shortest is the six-step run

1. CONTRIBUTE $(s_1,1)$, then
2. CONTRIBUTE $(s_2,1)$, then
3. PUBLISH $(Z,1)$ with value $0$, then
4. CONTRIBUTE $(s_3,1)$, then
5. PUBLISH $(Y,1)$ with value $0$, then
6. UNDEFINED at $(s_4,())$,

which never publishes $Z[0]$ or $Y[0]$ and leaves the four occurrences at $j=0$ pending. Every maximal run on $\eta_0$ fails at $(s_4,())$, since $\log$ is the only partial primitive in `Scorer`; the rest of the failure record (which addresses are published, which occurrences remain pending) depends on the schedule.

### 9.3 An accumulator is not a readable intermediate

**Example 5.34 (Section 27.1 of the specification).** Scalar inputs $A[]=1$, $B[]=-1$:

```text
Pre[] = A[]
Pre[] = B[]
T[]   = relu(Pre[])
```

| # | Rule | Target | $\alpha(\mathrm{Pre})$ | $\alpha(T)$ | Newly published | $T$ occurrence ready? |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | Init | | 0 | 0 | $A,B$ | no |
| 1 | CONTRIBUTE | `Pre = A` | 1 | 0 | | no: $\mathrm{Pre}$ unpublished |
| 2 | CONTRIBUTE | `Pre = B` | 0 | 0 | | no |
| 3 | PUBLISH | $(\mathrm{Pre},())$ | 0 | 0 | $\mathrm{Pre}=0$ | yes |
| 4 | CONTRIBUTE | `T = relu(Pre)` | 0 | 0 | | |
| 5 | PUBLISH | $(T,())$ | 0 | 0 | $T=0$ | |

After step 1 the accumulator holds $1$, but $(\mathrm{Pre},())\notin\mathrm{dom}\,\sigma$, so the $T$ occurrence is not ready, and PUBLISH at $\mathrm{Pre}$ waits for `Pre = B`. Applying ReLU to the partial value $1$ would give $T=1$ and change the meaning. Swapping steps 1 and 2 gives the same result: consuming `Pre = B` first makes the intermediate accumulator $-1$ instead of $1$, but the final value $0$ is the same. Readiness of the contribution to $T$ is the same in both orders, because it depends only on $\mathrm{dom}\,\sigma$, never on $\alpha$. Separate contributions `relu(A[])` and `relu(B[])` do give $1$, but that is a different program (Section 21.2 of the specification). In Lean the mistake cannot be written: `evalReady` receives `c.published` only.

### 9.4 A bounded scan and its rank

**Example 5.35 (Section 27.4 of the specification).** Inputs $X,Z$ of shape $(d)$, defined $H$ of shape $(d,N+1)$, total $F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$ (Section 11.4 of the specification):

```text
H[i,l]   = X[i]             # i in [d], l in [N+1]
H[i,0]   = Z[i]             # i in [d]
H[i,l+1] = F(H[:,l])[i]     # i in [d], l in [N]
```

The recurrence body at $(i,l)$ is $\mathrm{at}\big(F(\mathrm{tab}_{j\in[d]}(H[j,l])),(i)\big)$, whose footprint is the *whole* slice $\{(H,(j,l))\mid j\in[d]\}$, because `at` reads its whole array argument. No update reads a partially accumulated slice. So
$$\mathrm{Dep}(H,(i,0))=\{(X,i),(Z,i)\},\qquad \mathrm{Dep}(H,(i,l+1))=\{(X,i)\}\cup\{(H,(j,l))\mid j\in[d]\},$$
and although $H$ appears on both sides, a certificate exists: $r(X,i)=r(Z,i)=0$ and $r(H,(i,l))=l+1$, since $r(H,(j,l))=l+1<l+2$. For $d=1$, $N=2$ the certificate is concrete: $r(H,(0,0))=1$, $r(H,(0,1))=2$, $r(H,(0,2))=3$, and $r=0$ on the $X$ and $Z$ addresses.

With $d=1$, $N=2$, $X[0]=2$, $Z[0]=3$, $F(h)[0]=2h[0]$, there are $3+1+2=6$ occurrences and $3$ defined addresses, so $\mu$ starts at $9$. One legal schedule, copied from the specification:

| Step group | Accumulator change or publication |
| --- | --- |
| Consume the three persistent-input occurrences | Accumulators at times $0,1,2$ are each $2$ |
| Consume the base occurrence | Time-zero accumulator becomes $5$ |
| Publish time zero | $H[0,0]=5$ becomes readable |
| Consume the recurrence occurrence for $l=0$ | Time-one accumulator becomes $2+10=12$ |
| Publish time one | $H[0,1]=12$ becomes readable |
| Consume the recurrence occurrence for $l=1$ | Time-two accumulator becomes $2+24=26$ |
| Publish time two | $H[0,2]=26$ becomes readable |

The first row of the table stands for three machine steps, one per persistent-input occurrence, so the whole schedule has six CONTRIBUTE and three PUBLISH steps, and $\mu$ runs from $9$ to $0$. A future slice may accumulate its persistent input early but cannot publish before its recurrence contribution arrives. The rank adds no ordering beyond the barrier; it guarantees the barrier is always eventually met. With $N=0$ there are no recurrence occurrences; with $d=0$ there are no history coordinates and no recurrence body is evaluated.

### 9.5 Cycles block, with or without a model

**Example 5.36 (Section 27.5 of the specification).** Three scalar programs; $X$ is an input in the first.

| Program | Collected equation | Models | Machine |
| --- | --- | --- | --- |
| `T[] = X[]`; `T[] = 2 T[]` | $T=X+2T$ | exactly one, $T=-X$ | consumes `T = X`, then blocked |
| `T[] = T[]` | $T=T$ | every real number | blocked at $\mathrm{Init}$ |
| `T[] = T[] + 1` | $T=T+1$ | none | blocked at $\mathrm{Init}$ |

In the first, the input occurrence contributes $X$; the self-reading occurrence then waits for $(T,())$, while publication waits for that occurrence. In the others the only occurrence reads $(T,())$ from the start. All three have $(T,())\in\mathrm{Dep}(T,())$, a cycle, so none has a certificate (Proposition 5.26).

Blocked is neither success nor failure, and the machine does not say which denotational case holds. It does not assert inconsistency and does not pick the zero accumulator. Publishing $\alpha(T)$ would give $T=X$ in the first program (wrong unless $X=0$: the model is $-X$), $T=0$ in the second (one arbitrary model of infinitely many), and $T=0$ in the third (not a model). A ranked-fragment compiler should report an unsupported dependency form.

Contrast $T[]\mathrel{+}=\bigoplus_{j\in[0]}T[]$ (Section 27.3 of the specification). Its one occurrence reduces over the empty set, so its footprint is empty and $\mathrm{Dep}(T,())=\varnothing$. The name appears on both sides, but there is no coordinate cycle: the occurrence contributes $0_K$ at once and $T$ publishes $0$ (Exercise 6).

*Why this matters for an agentic coder.* These runs are test fixtures. A correct executor reproduces the $\eta_1$ environment under shuffled schedules, fails at $(s_4,())$ on $\eta_0$ without returning $Y$, gives $T=0$ in the `Pre` example, and reports the three cyclic programs as unsupported.

## 10. The two semantics agree

[Chapter 4](04-denotational.md#6-the-semantics-as-a-span) gave the witness span $\mathrm{Env}(\mathrm{In})\xleftarrow{\ell}W_P\to\mathrm{Env}(\mathrm{Out})$ with $W_P=\{(\eta,\rho)\mid\rho\in\mathrm{Models}(P,\eta)\}\cong\mathrm{Fix}(P)$ (Proposition 4.19). The machine gives its own witnesses,
$$W_P^{\mathrm{op}}=\{(\eta,\rho)\mid\mathrm{Init}(P,\eta)\Downarrow\rho\}.$$

**Proposition 5.37 (operational witnesses inside the model span).** (a) For every program, $W_P^{\mathrm{op}}\subseteq W_P$, and $\ell$ is injective on $W_P^{\mathrm{op}}$: successful outcomes form a partial function, defined only on $\mathrm{AdmInput}(P)$, where it agrees with $[\![P]\!]$. (b) If $P$ has a rank certificate, $W_P^{\mathrm{op}}=W_P$.

*Proof.* (a) Inclusion and agreement are Theorem 5.18(i); injectivity is Proposition 5.30, and "injective left leg" is "partial function" by Proposition 4.27. (b) If $(\eta,\rho)\in W_P$, then $\mathrm{Models}(P,\eta)=\{\rho\}$ (Corollary 5.29) and $\mathrm{Init}(P,\eta)\Downarrow\rho$ (Theorem 5.28(4)). $\square$

```text
                 W_P^op  ⊆  W_P
                /                \
          ℓ (mono on W_P^op)      ρ ↦ ρ|Out
              /                    \
         Env(In)                  Env(Out)
```

The table classifies outcomes by the model set. The middle column is this course's consequence of results that need no certificate (Lemma 5.16(c), Theorem 5.18, Corollary 5.22); recall every maximal run ends failed, complete or blocked.

| $\mathrm{Models}(P,\eta)$ | Any program (no certificate assumed): each maximal run | Program with a certificate: each maximal run |
| --- | --- | --- |
| empty | fails or blocks; never succeeds (Theorem 5.18(i)) | fails (Theorem 5.28(3)) |
| exactly $\{\rho\}$ | succeeds with $\rho$ or blocks; never fails (Lemma 5.16(c)) | succeeds with $\rho$ (Theorem 5.28(2)) |
| two or more | blocks: success would force uniqueness, failure would force emptiness | impossible (Corollary 5.29) |

The middle column does not assume a certificate is supplied, but by Exercise 8 a program for which no certificate exists (one whose dependency graph has a cycle) never succeeds. So the "succeeds" options in the middle column occur only for programs that admit a certificate, whether or not one was handed to the machine. The three cyclic programs of Example 5.36 fill the middle column's three rows with blocked runs.

For ranked programs, what depends on the schedule and what does not:

| Depends on the schedule | Does not |
| --- | --- |
| the order of CONTRIBUTE and PUBLISH events | whether the run succeeds or fails (Theorem 5.28) |
| intermediate accumulators ($\alpha(Z,0)$ is $-1$ or $1$ after one $Z[0]$ writer) | the final environment of a success (Proposition 5.30) |
| which failing occurrence is reported, and the store recorded with it | the length of a successful run, $\lvert\mathcal{O}_P\rvert+\lvert\mathrm{Addr}_{\mathrm{Def}}\rvert$ |

**Why this is the right shape for a correctness statement.** Theorem 5.28 quantifies over *every* maximal run, so it is a property of the coalgebra, not of a scheduler. That makes it portable. A backend need not reproduce one schedule; it must show that each of its executions corresponds to *some* run of this coalgebra, and then the correspondence transfers: success means the unique model, failure means none. Chapter 7 describes the Part V refinement layer that states this obligation.

*Why this matters for an agentic coder.* The handoff to a backend is a refinement obligation, not a test suite. "It matches the reference on $\eta_1$" checks one point of $W_P^{\mathrm{op}}$. "Every compiled execution is a run of the reference machine, up to stuttering" checks the whole span, failures included.

## 11. Why this matters for an agentic coder

- **Readiness and the barrier are the semantics.** A coordinate is readable when its last writer is consumed, not when its accumulator holds a plausible number: `Scorer`'s $Z[0]$ holds the right value $0$ before any work is done and is still not publishable. Any fusion or batching must keep the barrier.
- **Failure and blocking are outcomes, never values.** Never convert either into $0$, `nan`, a partial output or the zero accumulator; report an unsupported dependency form.
- **The rank certificate is an artifact.** A ranked-fragment compiler must produce one, possibly symbolically, or reject the program. "Statements run in text order" and "the last write wins" are scheduling choices that need a refinement argument.

## 12. What this chapter did not do

- **No storage.** Accumulators and the store are logical. Physical slots, buffer reuse and liveness belong to Part V and Chapter 7; a logical rank does not by itself justify overwriting a value a remaining operation still needs (Section 28).
- **No batching.** One step handles one occurrence or address. Batched execution is refinement with stuttering, and Chapter 3 explains why batching a partial map is only lax-natural.
- **No floating point.** $K$ is exact. Exact commutative sums are not bitwise floating-point guarantees; a machine-arithmetic interpretation must fix a reduction order or a numerical criterion.
- **No Turi-Plotkin bialgebra.** A bialgebraic treatment would add a syntax functor and a distributive law of syntax over behaviour. The categorical semantics document lists "a bounded scope-aware bialgebraic pilot" as a future direction (Summary roadmap; elaborated in Section 10.3) and states that "No generic coalgebra instance or Turi-Plotkin distributive law is supplied by the prototype" (Section 8). Chapter 7 covers the outlook.
- **No solver.** A cyclic program can have a unique model and still block. General cyclic solvers are "a separately justified extension, not an implicit fallback" (Section 28).

## Exercises

1. **Schedules.** Give a maximal run of `Scorer` on $\eta_1$ in which $(Y,0)$ is published before $(Z,1)$, and another in which $(s_2,0)$ is consumed before $(s_1,0)$. Tabulate the accumulators. Check both publish the same environment. Which Lean theorem guarantees this, and does it need a `RankCertificate`? (b) For `A[] = log(X[])`, `C[] = log(X[])` with $X=0$, list all maximal runs and their observations (Definition 5.10). Show they all prove $\mathrm{Models}=\varnothing$, and say which row of the schedule-dependence table in Section 10 the reported occurrence belongs to.

2. **Early publication breaks the invariant.** Let PUBLISH$'$ publish $a$ even while occurrences of $\mathcal{C}_P(a)$ are pending. (a) On `Scorer` with $\eta_1$, publish $(Z,0)$ after consuming only $(s_1,0)$, and show Lemma 5.16(b) fails for the model of Example 5.17. Does the output $Y$ change? (b) Publish $(Z,0)$ after consuming only $(s_2,0)$ and show the reported $Y$ is wrong. (c) Identify the step of the proof of Lemma 5.16(b) that breaks.

3. **A cyclic program as a coalgebra.** For `T[] = X[]; T[] = 2 T[]` with $X=3$: (a) list $\mathrm{Reach}(P,\eta)$ and write $\mathrm{step}$ on it and the observation map; (b) show the run blocks; (c) compute $\mathrm{Dep}(T,())$ and show directly that no rank certificate exists; (d) compute $\mathrm{Models}(P,\eta)$, and say which theorem would be violated if the machine published $\alpha(T)=3$.

4. $^\ast$ **The measure lemma.** (a) Prove Lemma 5.21 in full, with the bound $\lvert\mathrm{step}(c)\rvert\le\mu(c)$ of Proposition 5.8. (b) Prove $\mathrm{Reach}(P,\eta)$ finite using König's lemma. (c) Compute $\mu$ along Example 5.33 and along the six-step failing run of Section 9.2. (d) Explain why Lean's `stateMeasure` uses $\mu+1$ for running states and $0$ for failed ones.

5. $^\ast$ **Ranks as lax morphisms.** (a) Prove Proposition 5.26 in full, including the well-founded recursion defining the height $h$. (b) Show $h$ is the pointwise least certificate. (c) Compute $h$ for `Scorer` and for Example 5.35 and compare with the certificates in the text. (d) Show lax morphisms compose, and conclude that if a lax morphism $(A,\mathrm{Dep})\to(B,\mathrm{Dep}')$ exists and $(B,\mathrm{Dep}')$ has a certificate, so does $(A,\mathrm{Dep})$.

6. **An empty binder.** For $T[]\mathrel{+}=\bigoplus_{j\in[0]}T[]$, compute the footprint of its occurrence, $\mathrm{Dep}(T,())$ and a rank certificate, and write the maximal run. Do the same for `T[] = T[]`, and explain in one sentence why "the name $T$ appears on both sides" is the wrong test for a cycle.

7. **Guard versus Iverson, operationally.** With $X=(4,-1)$ (Section 21.3 of the specification), run the machine on `for i in [2] where i < 1: Y[i] += log(X[i])` and on `for i in [2]: Y[i] += 1_{i<1} log(X[i])`. List the occurrences, give a maximal run and its outcome for each, and explain why the Iverson version fails although its factor at $i=1$ is $0$.

8. $^\ast$ **Success witnesses acyclicity.** (a) Show that if some run from $\mathrm{Init}(P,\eta)$ succeeds, the dependency graph of $P$ is acyclic, so $P$ has a rank certificate. Hint: along a dependency cycle each address must be published before the next. (b) Conclude that a program with a dependency cycle never succeeds on any input. (c) Explain why Theorem 5.18(i) is vacuous outside the ranked fragment, yet still not empty: what does it give that Theorem 5.28 does not for a scheduler that never checks a certificate, and what does part (ii) give outside the ranked fragment?
