# Chapter 6. From categories to Lean

**Summary.** Chapters [2](02-index-categories.md) to [5](05-operational.md) built the semantics of Tensor Logic from five structures: families with pullback and pushforward, the Kleisli category of `Option`, collection and the model equalizer, and the reference machine. This chapter shows how each becomes a Lean definition or theorem, first in a compiled companion of about one thousand lines (`lean/MiniTensorLogic.lean`, namespace `Course`, importing only Mathlib), then in the production modules `LeanNCD.Semantics.*`, and it explains what that buys a coding agent that must edit the code.

We cite names from two bodies of Lean. The *mini development* is [`lean/MiniTensorLogic.lean`](lean/MiniTensorLogic.lean). The *production development* is [`leanncd/LeanNCD/Semantics/`](../../leanncd/LeanNCD/Semantics/). Every name below is copied from those files. Where this chapter writes a few lines of new Lean (Examples 6.1 and 6.2, and the exercises), it says so, and the lines were compiled in a scratch copy of the companion.

## 1. Why a proof assistant is the right target

In [Chapters 2](02-index-categories.md) to [5](05-operational.md) every structure came as a definition and a short list of laws. In prose, a law is a claim that a reader checks or trusts. In Lean, a definition is a term, a law is a theorem whose statement is a type, and a small kernel checks every proof. Nothing is left to the reader. Proposition 2.7(2) says $(g\circ f)_!=g_!\circ f_!$. In Lean it is a theorem called `pushforward_comp`. If the definition of `pushforward` changes so that the law fails, the file stops compiling at that theorem. The definitions of this course are the structures of those chapters, and the theorems are their laws.

For a coding agent this changes what an error looks like. In a test-driven loop, an edit that confuses $\bot$ with $0$, or that selects a coordinate before computing an array, produces a number, and a test on one input may not notice that it is wrong. In Lean, the same edit to the Lean model breaks a named theorem, and the compiler reports it as an error at that name. So an agent that violates a law of the Lean model gets a compile error, not a wrong number. The limits are real and Section 5(f) states them: the kernel checks laws about the Lean model, it does not say that the Lean model is the right semantics, and an edit to the Python or Rust compiler gets no such guard.

## 2. The dictionary

Each table below is one layer. Read a row as: the categorical notion and where this course defines it; the name in the mini development; the name in production; and what differs. Mini names live in namespace `Course` and production names in `LeanNCD.Semantics`; each column states its prefix once, and a name such as `Program.collect` means `Course.Program.collect` in the second column and `LeanNCD.Semantics.Program.collect` in the third. `none` means the development has no such declaration. This is the section to keep open while reading code.

### 2.1 Index geometry (Chapter 2)

| Categorical notion | Mini (`Course.`) | Production (`LeanNCD.Semantics.`) | What differs |
| --- | --- | --- | --- |
| Coordinate set $\mathrm{Coord}(T)$, Definition 2.1 | `Addr` over `Fin (d.size t)` | `Axis`, `Shape`, `Coord`, `Layout`, `canonicalLayout` | Mini flattens each tensor to one `Fin n`. Production keeps the axes, each with a `uid`, and a layout bijection. |
| Family $K^I$, Definition 2.6 | `Family` | `Family` | Identical: `abbrev Family (I K : Type) := I → K`. |
| Pullback $f^\ast$, Definition 2.6 | `pullback` | `pullback` | Identical. Mini names the contravariance laws `pullback_id` and `pullback_comp` (both `rfl`). Production names none. |
| Pushforward $f_!$, Definition 2.6 | `pushforward` | `pushforward` | Same body: a sum over all of the source with an `if` selecting the fibre. Mini calls the map `f : I → J`, production `d : O → I`. |
| Proposition 2.7(1) | `pushforward_zero`, `pushforward_add` | `pushforward_zero`, `pushforward_add`, `pushforwardHom` | Production also bundles an additive homomorphism. |
| Proposition 2.7(2) | `pushforward_id`, `pushforward_comp` | `pushforward_id`, `pushforward_comp` | Same statements. |
| Proposition 2.7(3), relabeling | `pushforward_relabel` | `pushforward_relabel` | Same. |
| Proposition 2.7(4), grouping | `pushforward_grouped` | `pushforward_grouped` | Same, over a sigma type `(a : A) × B a`. |
| Pairing $\langle u,v\rangle_I$ | `pairing` | none | Mini only. Needs `CommSemiring K`. |
| Proposition 2.8, transpose identity | `transpose` | none | Mini only. The decategorified shadow of $\Sigma_f\dashv f^\ast$. |
| Proposition 2.9, Naperian adjunction | `naperian` (an `Equiv`, currying) | none | Production is Naperian by representation: `Family`, `Store` and `PartialStore` are functions. It proves no currying equivalence. |
| Definitions 2.10 and 2.11, weighted span and linearization | `WSpan`, `WSpan.lin`, `WSpan.comp` | none in the core modules. Witness spans of [Chapter 4](04-denotational.md#6-the-semantics-as-a-span) are in `leanncd/experiments/indexed_execution/IndexedWitnessSpan.lean`: `IndexedWitness.Span`, `IndexedWitness.SpanIso` | Different spans. Mini has weighted contraction spans of finite sets. The experimental `Span` is a set of witnesses with two legs into environments. |
| Proposition 2.12, composition linearizes to matrix product | `WSpan.lin_comp` | none | The Beck-Chevalley and matrix-product law is proved only in mini. |
| Proposition 2.13, pure einsum, on `Scorer` | `W₁`, `X₁`, `Vs1` | none | Mini only. Production relates source einsums to `Program` in the `Source/` modules ([Chapter 2, Section 4](02-index-categories.md#4-contraction-patterns-are-spans)). |

### 2.2 Partiality (Chapter 3)

| Categorical notion | Mini (`Course.`) | Production (`LeanNCD.Semantics.`) | What differs |
| --- | --- | --- | --- |
| Result space $V\sqcup\{\bot\}$, Definition 3.1 | `Option`; `none` is $\bot$ | `Option` | Identical use of Lean's `Option`. |
| `sequence`, Definition 3.8 | `sequenceFin` | `sequence` | Mini: non-dependent, `(Fin n → Option α) → Option (Fin n → α)`. Production: dependent over `A : Fin n → Type`. |
| Laws of `sequence`, Proposition 3.9 | `sequenceFin_zero`, `sequenceFin_eq_some_iff`, `sequenceFin_some_iff` | `sequence_some_iff` (with `sequence_sound`, `sequence_complete`), in `Completeness.lean` | Same iff: `sequence f = some v ↔ ∀ i, f i = some (v i)`. Production states it for the dependent `sequence`. |
| Reduction (ordered sum) | `Expr.reduce`, evaluated by `sequenceFin` then `∑` | `foldValues`, `reduce_empty`, `reduce_defined_iff`, `reduce_sum` | Production fuses `sequence` with an ordered fold over `ScalarOps`. Mini sums with a `Finset` sum, which needs commutativity. Production proves the empty reduction is defined and the definedness iff (`Completeness.lean`). |
| Batching, Definition 3.10 | `batch` | none (`Expr.tab` sequences over a layout; its law is `tab_complete`) | Mini only as a named function. `tab_complete` says a tabulation is defined iff every component is, and mentions no layout. |
| Definedness order $\preceq$, Definition 3.12 | `DefLE` | none | Mini only. |
| Lax naturality, Proposition 3.13 and Example 3.14 | `batch_lax`, `recip`, `batch_lax_strict` | none | Mini only. Production states no Lean theorem for the law. |
| Strict pairing is not cartesian, Proposition 3.6 | `not_cartesian` | none | Mini only. |
| Registry partial map | `Expr.prim` with `f : K → Option K` | `Registry`, `Registry.apply` | Production: typed arity, a Boolean `domain`, and a `meaning` that needs a proof that the test passed. Mini: one unary function. |
| Kleisli interpreter, Definition 3.15 | `evalWith`, `interpret` | `evalWith`, `interpret` | Mini has six `Expr` constructors, production eight. |
| Read footprint, Definition 3.20 | `footprint` | `footprint` | Same recursion. Production adds `tab`, `at`, `iverson`, and resolves reads through `AdmittedRead`. |
| Read stability, Proposition 3.22 | none | `evalWith_stable`, `interpret_stable` | Production only. |
| Ready evaluation, Definition 3.24 | `Program.ready`, `Program.evalReady` | `Ready`, `checkReads`, `ReadyResult`, `evalReady`, `checkReads_iff`, `ready_consistent`, `notReady_iff`, `ready_complete_extension` | Mini: a Boolean `ready` plus `Option`. Production: a three-way `ReadyResult` that separates waiting from $\bot$. |

### 2.3 Programs and models (Chapters 1 and 4)

| Categorical notion | Mini (`Course.`) | Production (`LeanNCD.Semantics.`) | What differs |
| --- | --- | --- | --- |
| Signature $\Sigma$ | `Decl` | `Declarations`, `Signature`, `Ty`, `Value`, `ScalarOps` | Mini: tensors with a flattened size, one sort. Production: sorts `S`, carriers `K : S → Type`, and `unique : Function.Injective uid`. |
| Addresses $\mathrm{Addr}_\Sigma$ | `Addr` | `Address` | Both are sigma types: a tensor with one of its coordinates. |
| Environments, Definition 4.2 | `Env` | `Store`, `Cell`, and the partial `PartialStore` | Mini has no partial-store type: it uses `Addr d → Option K` directly. |
| Core expressions | `Expr` (`lit`, `read`, `add`, `mul`, `reduce`, `prim`) | `Expr` (`lit`, `read`, `iverson`, `binary`, `reduce`, `tab`, `at`, `prim`) and `Bin` | Mini has no guards, Iverson factors, tabulations or arrays. |
| Interpretation | `interpret` | `interpret` | Both are `evalWith` at the total store `some ∘ ρ`. |
| Statement and program | `Stmt`, `Program` | `Program` (fields `statements`, `valuations`, `guard`, `destination`, `body`) | Mini keeps one list of statements. Production groups statements per defined tensor and has an `output` flag. |
| Occurrences $\mathcal{O}_P$, Definition 2.14 | `Program.Occ` | `Program.Occurrence`, `Program.Defined` | Mini: one sigma over statement positions. Production: one sigma per defined tensor, over a guard subtype. |
| Destination $\mathrm{dst}$ | `Program.dst` | `Program.destination` | One global map versus one map per target. |
| Body value $[\![E_s]\!]_{\rho,\nu}$ | `Program.bodyVal` | `Program.outcome` | Same content. |
| $\mathrm{AdmEnv}(P)$, Definition 4.4 | `Program.AdmEnv` | `Program.AdmEnv` | Same shape: every occurrence body is `isSome`. |
| Contribution | `Program.contribution`, `Program.contribution_eq` | `Program.contribution` | Both take the admissibility proof. |
| Collection, Definition 4.6 | `Program.collect`, `Program.collect_fibre` | `Program.collect`, `Program.collect_grouped`, `Program.collect_relabel` | Mini is one `pushforward P.dst`. Production collects per tensor. |
| Equation operator $\Phi_P$, Definition 4.9 | `Program.equationOperator` | `Program.equationOperator` | Same: copy inputs, collect defined tensors. |
| $\mathrm{Models}(P,\eta)$, Definition 4.11 | `Program.Models` | `Program.Models` | Defined in opposite forms: see the next row. |
| Models as an equalizer, Proposition 4.12 | `Program.models_fixedpoint` | `Program.models_fixedpoint` | Mini defines `Models` as the fixed point and proves the collect equations. Production does the reverse. |
| $\mathrm{AdmInput}(P)$, Definition 4.14 | `Program.AdmInput` | `Program.AdmInput` | Both are `∃! ρ, ... Models ...`. |
| Denotation $[\![P]\!]$ | none | `Program.denotation`, `Program.denotation_of_model`, `Program.Output`, `Program.outputProjection` | Production only. `denotation` is noncomputable (`Classical.choose`). |
| Input environment $\eta$ | a dependent function on input addresses | `Program.InputBinding`, `Program.ValidInput`, `Program.Input`, `Program.InputAgreement` | Production records tensor-level presence as `Option`. |
| Relabeling and grouping of models, Propositions 4.7(1) and 4.7(2) | `pushforward_relabel` only | `Program.models_relabel`, `Program.models_grouped` | Production lifts the law to `Models`. |

### 2.4 The machine (Chapter 5)

| Categorical notion | Mini (`Course.`) | Production (`LeanNCD.Semantics.`) | What differs |
| --- | --- | --- | --- |
| Configuration $(\sigma,\alpha,U)$, Definition 5.3 | `Config` (`published`, `acc`, `pending`) | `Program.Running` (`published`, `accumulators`, `pending`) | Mini: pending is a `List`, accumulators on every address. Production: a `Finset` per defined tensor, accumulators on defined tensors only. |
| Outcomes, Definition 5.7 | `Outcome` (`running`, `failed`, `blocked`, `complete`) | `Program.MachineState` (`running`, `failed`); predicates `Program.Complete`, `Program.Blocked`, `Program.Successful` | Mini packages the scheduler's verdict as a datatype. Production keeps two machine states and states the verdicts as predicates. |
| $\mathrm{Init}(P,\eta)$, Definition 5.4 | `Program.initial` | `Program.initial` | Mini takes an `Env` and reads inputs only. Production takes a `P.Input`. |
| Effect of CONTRIBUTE | `Program.contribute` | `Program.consume` | Same effect: add to the accumulator, remove from pending. |
| Effect of PUBLISH | `Program.publish` | `Program.publish` | Same: freeze the accumulator into the store. |
| The three rules, Definition 5.6 | `Program.Step` with `contribute`, `publish`, `undefined` | `Program.Step` with `contribute`, `publication`, `undefined` | Mini: `Config → Outcome`, readiness as a Boolean premise. Production: `MachineState → MachineState`, readiness inside `evalReady ... = .evaluated (some v)`, and the premise `FiberEmpty`. |
| Reachability | `Program.Reaches` (`refl`, `step`) | `Program.Reaches` (`refl`, `tail`) | Mini prepends a step. Production appends one. |
| Failed states are terminal | no theorem | `Program.failed_terminal` | Production only. |
| Measure $\mu$, Lemma 5.21 | `Program.measure`, `Program.measure_decreases` | `Program.measure`, `Program.running_step_measure`, `Program.stateMeasure`, `Program.step_decreases` | Mini proves strict decrease for running steps. Production proves the equation `measure c = measure d + 1` and covers failed states. |
| Well-founded coalgebra, Corollary 5.22 | none | `Program.step_wellFounded`, `Program.no_infinite_chain` | Production only. |
| Running to the end | `Program.run`, `Program.runToEnd`, `Program.run_sound`, `Program.run_sound_failed` | `Program.Executor.run`, `Program.Executor.Schedule`, `Program.Executor.result_success`, `Program.Executor.result_failure`, `Program.Executor.run_not_exhausted` | Mini has one fixed scheduler and checks fuel sufficiency by `#eval`. Production takes any `Schedule`, proves results about any `Result`, and proves the fuel suffices. |
| Theorem 5.18, success and failure | none; instances `scorer_models₁`, `scorer_no_model₀` | `Program.successful_model`, `Program.successful_unique`, `Program.failed_no_model` | Mini checks the running example, not the general theorem. |
| Invariants, Lemmas 5.14 and 5.16 | none | `Program.Invariant`, `Program.reachable_invariant`, `Program.candidate_preserved` | Production only. |
| Rank certificate, Definition 5.25; Theorems 5.27 and 5.28 | none | `Program.RankCertificate`, `Program.dependencies`, `Program.ranked_progress`, `Program.maximal_dichotomy` | Production only. |
| Schedule independence, Proposition 5.30 | none | `Program.successful_schedules_agree` | Production only. |

*Why this matters for an agentic coder.* The dictionary tells an agent where to look and what it may trust. If a task touches a row whose mini column says `none`, the mini development is no evidence: only the production theorem is. If it touches a row that exists on both sides, the mini version is a small, fast place to test a change before touching the large one.

## 3. A guided walk through `MiniTensorLogic.lean`

Open the file beside this chapter. It has four parts, in the order of Chapters 2, 3, 4 and 5. Each part depends only on the earlier ones. The scalar sort is $K=\mathbb{Q}$, so everything computes.

*Reading the Lean.* `Fin n` is the interval $[n]$. `#eval` runs a definition and prints the result. `decide +kernel` asks the kernel itself to evaluate a decidable proposition, which is how the running-example facts are proved. A sigma type `(i : A) × B i` is a dependent pair, the coproduct $\coprod_{i\in A}B(i)$. `abbrev` is a transparent synonym for a type. `noncomputable` marks a definition that has no executable code (it uses classical choice or an infinite sum).

### 3.1 Pushforward and the transpose identity

```lean
def pushforward {I J K : Type} [Fintype I] [DecidableEq J] [AddCommMonoid K]
    (f : I → J) (v : Family I K) : Family J K :=
  fun j => ∑ i, if f i = j then v i else 0
```

This is Definition 2.6. The sum runs over all of $I$. The `if` keeps the terms of the fibre $f^{-1}(j)$ and replaces the others by $0$, so an empty fibre gives $0$. The hypotheses are exactly those of the mathematics: finiteness of the source, equality on the target to decide fibres, and a commutative monoid. Additive writes in Tensor Logic are pushforwards.

```lean
theorem transpose {I J K : Type} [Fintype I] [Fintype J] [DecidableEq J]
    [CommSemiring K] (f : I → J) (u : Family I K) (w : Family J K) :
    pairing (pushforward f u) w = pairing u (pullback f w) := by
```

This is Proposition 2.8, $\langle f_!u,w\rangle_J=\langle u,f^\ast w\rangle_I$. Its proof is six lines: swap the two finite sums. Look at what the type does *not* say. It is an identity between numbers for a commutative semiring. No statement of the form "pullback is adjoint to pushforward on $K$-families" appears anywhere in the file, which is CONVENTIONS fact 12. The docstring says the same.

### 3.2 Weighted spans and Proposition 2.12

```lean
def WSpan.comp {I J L K : Type} [Mul K] [DecidableEq J] (s : WSpan K I J)
    (t : WSpan K J L) : WSpan K I L where
  M := {p : s.M × t.M // s.r p.1 = t.l p.2}
  l p := s.l p.1.1
  r p := t.r p.1.2
  w p := s.w p.1.1 * t.w p.1.2
```

The apex of the composite is a subtype of the product: the pairs that agree over the middle set. That is the fibre product, the pullback in $\mathbf{FinSet}$, and the weight multiplies the two weights. Spans are not quotiented by span isomorphism here. The theorem compares only linearizations:

```lean
theorem WSpan.lin_comp {I J L K : Type} [CommSemiring K] [DecidableEq J]
    [DecidableEq L] (s : WSpan K I J) (t : WSpan K J L) (u : Family I K) :
    (s.comp t).lin u = t.lin (s.lin u) := by
```

This is Proposition 2.12: composing spans linearizes to composing matrices. The proof turns a sum over the fibre product into a filtered double sum (`Finset.sum_subtype`, `Finset.sum_filter`, `Fintype.sum_prod_type`), swaps the sums, and distributes the weight. It is the decategorified Beck-Chevalley square of Chapter 2.

The running example enters at the end of Part A: `Vs1` is $V_{s1}=(\pi_{\mathrm{out}})_!(\pi_W^\ast W\otimes\pi_X^\ast X)$ on the apex $[2]\times[2]$.

```lean
def Vs1 : Family (Fin 2) ℚ :=
  pushforward (fun p : Fin 2 × Fin 2 => p.1) (fun p => W₁ p * X₁ p.2)
```

The `#eval [Vs1 0, Vs1 1]` prints `[-1, 4]`, the two values of Proposition 2.13, and `example : Vs1 0 = -1 ∧ Vs1 1 = 4` checks them in the kernel with `decide +kernel`.

### 3.3 Sequencing, batching, and lax naturality

```lean
def sequenceFin : {n : Nat} → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => some Fin.elim0
  | _ + 1, f => do
      let x ← f 0
      let xs ← sequenceFin (fun i => f i.succ)
      pure (Fin.cons x xs)
```

This is Definition 3.8. The `do` block is Kleisli composition in $\mathrm{Kl}(\mathrm{Option})$: run `f 0`; if it is `none`, the whole result is `none`. The empty tabulation is `some`. The theorem `sequenceFin_some_iff` says a tabulation is defined iff every component is, which is strictness (CONVENTIONS fact 4).

```lean
def batch {n : Nat} (f : α → Option β) : (Fin n → α) → Option (Fin n → β) :=
  fun v => sequenceFin (f ∘ v)

def DefLE (g h : α → Option β) : Prop := ∀ a b, g a = some b → h a = some b

theorem batch_lax {m n : Nat} (f : α → Option β) (r : Fin m → Fin n) :
    DefLE (fun v : Fin n → α => (batch f v).map (fun w => w ∘ r))
      (fun v => batch f (v ∘ r)) := by
```

`batch` is Definition 3.10. `DefLE g h` says $g\preceq h$ (Definition 3.12): wherever `g` succeeds, `h` succeeds with the same value. It is an order on *maps*, and it puts no order on `β`. `batch_lax` is Proposition 3.13: batching over the large index set and then restricting along $r$ is less defined than restricting first. The proof is four tactic lines from `sequenceFin_eq_some_iff`: if every component of the big tabulation is defined, then so is every component the restriction kept.

The converse is false, and the file proves that it is false on Example 3.14:

```lean
theorem batch_lax_strict :
    batch recip ![(2 : ℚ), 0] = none ∧
      (batch recip (![(2 : ℚ), 0] ∘ (fun _ : Fin 1 => 0))).map (fun w => w 0) =
        some (1 / 2) := by
```

Here `recip` is the reciprocal on $\mathbb{Q}$, undefined exactly at $0$. Batching it over $(2,0)$ is `none`. Restricting to the first coordinate before batching gives `some (1 / 2)`. The two `#eval` lines print `none` and `some [1 / 2]`. The next theorem, `not_cartesian`, is Proposition 3.6 in one line of witnesses: `f = pure`, `g = recip`, `a = 0`.

### 3.4 `Expr` and `interpret`: the Kleisli map

```lean
inductive Expr (d : Decl) (K : Type) : Type → Type 1
  | lit {Γ : Type} (c : K) : Expr d K Γ
  | read {Γ : Type} (t : d.T) (ix : Γ → Fin (d.size t)) : Expr d K Γ
  | add {Γ : Type} (a b : Expr d K Γ) : Expr d K Γ
  | mul {Γ : Type} (a b : Expr d K Γ) : Expr d K Γ
  | reduce {Γ : Type} (n : Nat) (body : Expr d K (Γ × Fin n)) : Expr d K Γ
  | prim {Γ : Type} (f : K → Option K) (arg : Expr d K Γ) : Expr d K Γ
```

(Doc comments omitted.) The index `Γ` is a Lean type of valuations, the admitted domain $D$ of [Chapter 3](03-partiality.md#4-interpretation-of-core-expressions-as-a-structural-map-into-pfn). A binder extends it by a product, `Γ × Fin n`. An index expression is a Lean function `Γ → Fin (d.size t)`, so a read is in bounds by typing: an out-of-bounds read cannot be written. Now the interpreter:

```lean
  | _, .reduce _ body, γ => do
      let xs ← sequenceFin (fun i => evalWith σ body (γ, i))
      pure (∑ i, xs i)
  | _, .prim f a, γ => do
      let x ← evalWith σ a γ
      f x
```

These are two clauses of `evalWith`, a map into $\mathrm{Kl}(\mathrm{Option})$ (Definition 3.15). A reduction sequences its bodies and then sums. An empty reduction is `some 0` and evaluates no body, because `sequenceFin` on `Fin 0` is `some`. A primitive binds its argument first and then applies, so the primitive is never applied to $\bot$. The complete-environment interpretation is the Kleisli inclusion of $\rho$:

```lean
def interpret [Semiring K] (ρ : Env d K) {Γ : Type} (e : Expr d K Γ) (γ : Γ) :
    Option K :=
  evalWith (fun a => some (ρ a)) e γ
```

Reads in `interpret` are total, so $\bot$ arises only from primitives. `evalWith` against a partial store `σ` is the ready evaluation of [Chapter 3, Section 6](03-partiality.md#6-read-footprints-and-stability), and `evalReady` in Part D is `evalWith` on the published store.

### 3.5 Occurrences, collection, and models

```lean
abbrev Occ := (i : Fin P.stmts.length) × Fin (P.stmts.get i).n

def dst (o : P.Occ) : Addr d :=
  ⟨(P.stmts.get o.1).target, (P.stmts.get o.1).dest o.2⟩
```

`Occ` is the coproduct $\mathcal{O}_P=\coprod_sD_s$ of Definition 2.14, written as a sigma type over *positions in a list*. A duplicated statement is two list entries, so it is two occurrences (CONVENTIONS fact 1). `dst` is the copairing of the write maps. Collection is then one line:

```lean
def collect [Semiring K] (ρ : Env d K) (h : P.AdmEnv ρ) : Env d K :=
  pushforward P.dst (P.contribution ρ h)
```

This is literally `pushforward` of Section 3.1 applied to the contribution family: collection *is* the covariant functor of [Chapter 2](02-index-categories.md#3-decategorification-k-valued-families) (Definition 4.6). Two facts are visible in the type. The argument `h : P.AdmEnv ρ` means `collect` cannot be called until every body is defined, so collection happens after definedness and $\bot$ is never a summand. And the old value `ρ a` appears nowhere except through bodies that read it, so it is not a summand (CONVENTIONS fact 2). The models come next:

```lean
def Models [Semiring K] (η : (a : Addr d) → P.input a.1 = true → K)
    (ρ : Env d K) : Prop :=
  ∃ h : P.AdmEnv ρ, (∀ a (hi : P.input a.1 = true), ρ a = η a hi) ∧
    P.equationOperator ρ h = ρ
```

This is the equalizer of Proposition 4.12: admissible environments that extend $\eta$ and satisfy $\Phi_P(\rho)=\rho$. There is no least fixed point and no order on $\bot$: `Models` is a predicate on *all* fixed points. The theorem `models_fixedpoint` proves that this is equivalent to the collect equations `ρ a = P.collect ρ h a` at every defined address, and `AdmInput` is `∃! ρ, P.Models η ρ`.

### 3.6 `Scorer` in Lean

```lean
def wIdx (j i : Fin 2) : Fin 4 := ⟨2 * j.val + i.val, by omega⟩

def s1 : Stmt scorerDecl ℚ where
  target := .Z
  n := 2
  dest := fun j => j
  body := .reduce 2 (.mul (.read .W (fun p => wIdx p.1 p.2)) (.read .X (fun p => p.2)))
```

The signature `scorerDecl` is rank-flattened. `W` has size $4$, and $W[j,i]$ lives at flat coordinate $2j+i$: `wIdx 1 0` is $2$, and the input list `W = [1, 1, 2, -1]` of `ρ₁` has $W[1,0]=2$ at position $2$. The statement `s1` has $n=2$ valuations (the values of $j$), and its body is a reduction over a fresh binder: inside it the context is `Fin 2 × Fin 2`, so `p.1` is $j$ and `p.2` is $i$. Statement `s2` is a second writer to the same `Z` with `.read .B`, and `s3` is `.prim relu (.read .Z ...)`.

```lean
def s4 : Stmt scorerDecl ℚ where
  target := .L
  n := 1
  dest := fun _ => (0 : Fin 1)
  body := .prim recip (.read .Y (fun _ => (1 : Fin 2)))
```

Here the Lean departs from the notes: $s_4$ is `recip(Y[1])`, not `log(Y[1])`. Lean has no computable logarithm on $\mathbb{Q}$, and `#eval` and `decide +kernel` need computation. The substitution is harmless for the question the running example asks. In `Scorer`, $Y=\mathrm{relu}(Z)\ge0$ at every model. On a value that is $\ge0$, $\log$ is undefined exactly at $0$, and so is `recip`. Both bodies are undefined exactly when $Y[1]=0$. So both programs have a model on the same inputs. The notes' model has $L=\log4$ and the Lean model has $L=1/4$. The two programs do not have the same admissible environments: an environment with $Y[1]<0$ is admissible for `recip` and not for $\log$. But a *model* forces $Y[1]\ge0$, so the difference never reaches `Models`.

```lean
theorem scorer_models₁ : scorer.Models (inputOf ρ₁) ρ₁ :=
  ⟨scorer_adm₁, fun _ _ => rfl, by decide +kernel⟩
```

The third component is the statement $\Phi_P(\rho_1)=\rho_1$ on all $13$ addresses ($8$ inputs and $5$ defined). The kernel evaluates `collect` at each of them. This theorem says $\rho_1$ is *a* model of $\eta_1$. It does not say it is the only one: the mini development never proves `scorer.AdmInput (inputOf ρ₁)`. Uniqueness comes from Theorem 5.18, which only production proves (`successful_unique`).

```lean
theorem scorer_no_model₀ : ¬ ∃ ρ, scorer.Models (inputOf ρ₀) ρ := by
  rintro ⟨ρ, h, agree, fixed⟩
  have eqn := (scorer.models_fixedpoint (inputOf ρ₀) ρ).mp ⟨h, agree, fixed⟩
```

This is $\mathrm{Models}(\mathrm{Scorer},\eta_0)=\varnothing$, proved the way [Chapter 4](04-denotational.md#4-models-as-an-equalizer) does it, by forcing and not by running. The proof computes the two fibres with the kernel (the fibre of $(Z,1)$ is $\{(s_1,1),(s_2,1)\}$, the fibre of $(Y,1)$ is $\{(s_3,1)\}$). From $X=(0,0)$ and $B[1]=0$ it derives $Z[1]=0$, hence $Y[1]=\mathrm{relu}\,0=0$. The body of $(s_4,())$ is then `recip 0`, which is `none`, and that contradicts admissibility. The placeholder $L=0$ in `ρ₀` is irrelevant, since `inputOf ρ₀` reads only input coordinates.

### 3.7 The machine: `Step`, the measure, and `run`

```lean
inductive Step [Semiring K] : Config P → Outcome P → Prop
  | contribute (c : Config P) (o : P.Occ) (v : K) (pend : o ∈ c.pending)
      (rdy : P.ready c o = true) (ev : P.evalReady c o = some v) :
      Step c (.running (P.contribute c o v))
  | publish (c : Config P) (a : Addr d) (defined : P.input a.1 = false)
      (unpublished : c.published a = none) (finished : ∀ o ∈ c.pending, P.dst o ≠ a) :
      Step c (.running (P.publish c a))
  | undefined (c : Config P) (o : P.Occ) (pend : o ∈ c.pending)
      (rdy : P.ready c o = true) (ev : P.evalReady c o = none) :
      Step c (.failed o c)
```

(Doc comments omitted.) These are the three rules of Definition 5.6, and CONVENTIONS fact 6 can be read off the premises. CONTRIBUTE needs a pending occurrence that is ready (its whole footprint published) with a defined body. PUBLISH needs an unpublished defined address with *no pending writer*: the completion barrier. UNDEFINED needs a ready occurrence whose body is `none`, and it leads to `.failed`, which is terminal because `Step` only starts from a `Config`, and a failed outcome is not one. `Step` is a relation, so several rules may apply at once: the machine is nondeterministic, and `Step` is the specification.

```lean
def measure (c : Config P) : Nat :=
  c.pending.length +
    (Finset.univ.filter (fun a : Addr d => P.input a.1 = false ∧ c.published a = none)).card

theorem measure_decreases [Semiring K] {c c' : Config P}
    (h : P.Step c (.running c')) : P.measure c' < P.measure c := by
```

The function `measure` is $\mu=|U|+|\mathrm{Addr}_{\mathrm{Def}}\setminus\mathrm{dom}\,\sigma|$ of Lemma 5.21. `measure_decreases` says every running step lowers it by at least one: CONTRIBUTE removes a pending occurrence, PUBLISH removes an unpublished defined address. On `Scorer` the initial measure is $7+5=12$, which is the $7$ CONTRIBUTE and $5$ PUBLISH steps of a maximal run on $\eta_1$. The file proves the decrease. It does not prove the corollary that there is no infinite chain; production does (`no_infinite_chain`).

```lean
def run [Semiring K] : Nat → Config P → Outcome P
  | 0, c => .running c
  | fuel + 1, c =>
    match c.pending.find? (P.ready c) with
    | some o =>
      match P.evalReady c o with
      | some v => run fuel (P.contribute c o v)
      | none => .failed o c
    | none =>
      match (addrs (d := d)).find? (P.publishable c) with
      | some a => run fuel (P.publish c a)
      | none =>
        if c.pending.isEmpty && (addrs (d := d)).all (fun a => (c.published a).isSome)
        then .complete (fun a => (c.published a).getD 0)
        else .blocked c
```

`run` is one deterministic scheduler: take the first ready pending occurrence (and fail if its body is undefined); otherwise publish the first publishable address; otherwise stop, and say `complete` if nothing is pending and every address is published, `blocked` if not. The fuel argument makes it structurally recursive, and `runToEnd` gives it $\mu+1$ units. The theorem that ties it to the specification is soundness:

```lean
theorem run_sound [Semiring K] (ρ : Env d K) :
    ∀ (fuel : Nat) (c : Config P), P.run fuel c = .complete ρ →
      ∃ c', P.Reaches c c' ∧ c'.pending = [] ∧ ∀ a, c'.published a = some (ρ a)
```

Whatever `run` returns as `complete ρ`, there is a chain of `Step`s from `c` to a configuration with nothing pending whose published store is exactly `ρ`. Its companion `run_sound_failed` says the same for failure: a chain of steps to `c'`, and `UNDEFINED` applies at `c'`. Together with Theorem 5.18 of the notes, which the mini file does not formalize, this shows the failed run proves that there are no models. The scheduler is one strategy inside the relation `Step`, and nothing here proves that the fuel $\mu+1$ always reaches a verdict (complete, failed or blocked). The `#eval` checks below show that on the running example it does. Production proves the corresponding statement for its executor: `runFuel_not_exhausted` and `run_not_exhausted` (`ReferenceExecutor.lean`), with `initialBudget_agrees` (`ExecutableState.lean`).

### 3.8 The compiled output

Run the compile command of Section 6. These are its lines, copied from a run for this chapter (exit code 0):

```text
[-1, 4]
none
some [1 / 2]
[some (-1), some 4, some 1, some 0, some 0, some 4, some (1 / 4)]
[0, 4, 0, 4, 1 / 4]
none
"complete: Z[0]=0, Z[1]=4, Y[0]=0, Y[1]=4, L[0]=1/4"
"failed at (s4, 0); published: Z[0]=1, Z[1]=0, Y[0]=1, Y[1]=0, L[0]=_"
'Course.transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'Course.WSpan.lin_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Course.batch_lax' depends on axioms: [propext, Quot.sound]
'Course.batch_lax_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'Course.Program.models_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Course.scorer_models₁' depends on axioms: [propext, Classical.choice, Quot.sound]
'Course.scorer_no_model₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Course.Program.measure_decreases' depends on axioms: [propext, Classical.choice, Quot.sound]
'Course.Program.initial_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Course.Program.run_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Course.Program.run_sound_failed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Course.scorer_run₁' depends on axioms: [propext, Classical.choice, Quot.sound]
'Course.scorer_run₀' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Read the eight output lines against the notes, in order.

1. `[-1, 4]` is $V_{s1}$ of Proposition 2.13.
2. `none` is the strict batch of Example 3.14, which is undefined.
3. `some [1 / 2]` is the select-first side of Example 3.14, which is defined.
4. The seven body values on $\rho_1$, in the order of `scorerOccs`, are $s_1$ at $j=0,1$ (that is $-1,4$), $s_2$ ($1,0$), $s_3$ ($0,4$) and $s_4$ ($1/4$, the `recip` stand-in for $\log4$). This matches Example 4.8.
5. `[0, 4, 0, 4, 1 / 4]` is $\mathrm{Collect}_P(\rho_1)$ on $Z[0],Z[1],Y[0],Y[1],L[]$. It equals $\rho_1$ there, which is $\Phi_P(\rho_1)=\rho_1$.
6. `none` is the body of $(s_4,())$ on $\rho_0$: `recip 0`.
7. The machine on $\eta_1$ ends `complete`, with the model of `scorer_models₁`.
8. The machine on $\eta_0$ publishes all of $Z$ and $Y$ and then fails at $(s_4,())$, which the label prints as `(s4, 0)`. `L[0]=_` marks an unpublished address, and no value for $L$ is ever invented.

The thirteen listed theorems are the audit; the lemmas `scorer_adm₁`, `scorer_s4_undefined₀` and `Program.collect_fibre`, and the `Vs1` example, are not printed. Only `propext`, `Classical.choice` and `Quot.sound` appear. There is no `sorryAx`, and no `Lean.ofReduceBool` (the mark of `native_decide`), so the audited `decide +kernel` proofs add nothing to the trusted base. The theorems `scorer_run₁` and `scorer_run₀` are the two machine runs as kernel-checked statements.

Two further evaluations, not in the file, show the fuel arithmetic. On $\eta_1$, `run 12` returns `out of fuel` with $L$ already published, and `runToEnd` (fuel $\mu+1=13$) returns `complete`. The last unit of fuel is what lets the scheduler look around and report completion. On $\eta_0$, `run 10` is out of fuel with $Z=(1,0)$ and $Y=(1,0)$ published, and `run 11` fails at $(s_4,())$: ten steps and then the UNDEFINED step. These are the 11 steps of [Example 5.33](05-operational.md#9-worked-runs) in a different order: `run` takes the first ready pending occurrence, so it contributes $(s_3,0)$ right after $Z[0]$ is published and before $Z[1]$ is. Both are maximal runs that fail at the same occurrence $(s_4,())$, and Example 5.33 notes that other maximal runs, such as a six-step one that never publishes $Z[0]$, fail earlier at that same occurrence.

*Why this matters for an agentic coder.* The file is a template for a change that must be trusted. State the law as a theorem, state the running example as a kernel-checked theorem and as an `#eval`, and print the axioms. Each of those is something an agent can run and read without asking anyone.

## 4. What the production development adds and why

The mini development is a deliberately small retelling. The Lean path document states the organizing idea of the production development in one sentence (`papers/semantics/lean_executable_semantics_path_part_3.md`, Section 3.4): "coordinate maps route; partial maps interpret; additive pushforward collects; monotone publication makes completed values readable." Production keeps the four layers apart and adds, for each, what a real compiler front end needs.

**Sort-indexed carriers and a registry.** Scalars are not one type $K$. A `Declarations S` assigns each tensor a `Signature S` (a sort and axes), the carrier of a sort is `K : S → Type`, and `ScalarOps` supplies zero, one, add and mul per sort. Primitives are a `Registry K` with an operator type `Op`, an `arity`, typed `input` and `output`, a Boolean `domain` and a `meaning` that requires the proof `domain f xs = true`. `Registry.apply` makes a partial map out of the pair. The mini `prim` is a single unary `K → Option K` instead.

**Dependent coordinates make in-bounds reads a typing fact.** `Coord sh` is a product of `Fin a.extent`, and `Expr K σ r Γ τ` is indexed by the valuation type `Γ` and the value type `τ : Ty S`. A read carries an `AdmittedRead`: a `ReadPolicy`, a raw coordinate, a `resolved` outcome and the field `admission : ∀ γ, policy.resolve (raw γ) = (resolved γ).outcome`. The type `Resolved` has no `reject` constructor, so a read that the policy rejects at some valuation cannot be packaged into an `Expr`: rejection happens at admission, before an expression exists. Mini obtains in-bounds reads more crudely, with functions `Γ → Fin (d.size t)`.

**Guards as subtypes.** In `Program`, a body is an `Expr` over `{v : Fin (valuations t s) // guard t s v = true}`, and an occurrence is a statement together with such a `v`. A guard therefore removes occurrences before any body is evaluated. The Iverson factor is a different thing: the constructor `Expr.iverson`, which multiplies. CONVENTIONS fact 5 is a difference of *types* here. Mini has neither.

**Per-tensor occurrence grouping.** Statements are indexed by `{t // input t = false}`, so statement identifiers are local to their target, `Program.Occurrence t` is a sigma type per tensor, and collection is per tensor. The theorems `collect_grouped` and `collect_relabel` are [Proposition 4.7](04-denotational.md#3-collection-is-a-pushforward)(1) and (2), within one target.

**`PartialStore` and `ReadyResult`.** A published store is `PartialStore K σ`, a function into `Option`. `evalReady` returns a `ReadyResult`: `notReady` when part of the footprint is unpublished, and `evaluated (some v)` or `evaluated none` otherwise. Waiting and $\bot$ are different constructors of different types, so they cannot be confused. The step rules match on `.evaluated`. Mini collapses both into `Option` plus a Boolean `ready`, and its docstring has to warn that `none` means $\bot$ only on a ready occurrence. The categorical proposal's table of what each step buys (Section 10.1, step 2) lists the same separation as a benefit: it "separates undefinedness from unavailable data and numerical zero".

**`Fintype` and the computable scheduler.** `Program.tensors` is a `Fintype` field, and the finiteness of defined addresses is derived classically (`definedAddressFintype`, through `canonicalLayout`). So `measure` is noncomputable. `denotation` is noncomputable for a different reason, `Classical.choose`, and the invariants use `classical` reasoning. The computable side is separate: `ExecutableState`, `ExecutableSelection` and `ReferenceExecutor` define `Program.Executor.Schedule`, `Event` and `run`, and theorems such as `result_success`, `result_model`, `result_unique` and `result_failure` hold for any `Result`. The mini `run` is a toy of this executor, with `Decl.tensors` playing the role of the schedule.

**The ranked results.** `RankCertificate` is the structure `rank : Address σ → Nat` with `decreases : ∀ a b, b ∈ P.dependencies a → rank b < rank a`. On it production proves `ranked_progress` (a reachable, incomplete state has an enabled step), `maximal_dichotomy` (a maximal state is a success or a failure that proves there are no models), and `run_ranked_dichotomy` for the executor. Beside those sit `Invariant`, `reachable_invariant`, `candidate_preserved`, `successful_model`, `successful_unique`, `failed_no_model` and `successful_schedules_agree`. The "Current boundary" column of the proposal's Section 10.1 (step 9 for ranked phases) is the honest list of what is proved and what is a boundary.

**What the mini development leaves out.** The header of the file promised that its simplifications are collected here. Each is listed cell by cell in the "What differs" column of Section 2. The two omissions that matter most for trust are the general Theorem 5.18 (the mini file checks only its two instances) and the proof that `run` reaches a verdict (production proves it, see Section 3.7).

*Why this matters for an agentic coder.* Each addition is a place where an agent may be tempted to simplify and must not. Replacing `ReadyResult` by `Option` merges waiting and $\bot$. Replacing the guard subtype by an `if` inside the body turns a guard into an Iverson factor. Replacing the registry's proof-carrying `meaning` by a total function makes a primitive silently total. Production writes each of these distinctions into a type, so the edit breaks every proof and every program that depends on the distinction, and it cannot be done quietly.

## 5. How an agentic coder uses this structure

Six points.

**(a) Layers are modules, and dependencies run one way.** The core chain of production imports is:

```text
Types
Collection   <- Types
Expr         <- Types
Interpret    <- Expr
Readiness    <- Interpret
Program      <- Collection, Interpret
Models       <- Program
Machine      <- Models, Readiness
Ranks, Invariants <- Machine
Measure      <- Ranks
Soundness    <- Invariants
Progress     <- Measure, Soundness
```

Outside the chain: `Types` imports `LeanNCD.Exec.Uid`; `ExecutableState <- Progress`, `ExecutableSelection <- ExecutableState`, `ReferenceExecutor <- ExecutableSelection`; and `Completeness <- Readiness` (not on the chain, and nothing below it imports it).

These are five groups: indices (`Types`, `Collection`), partiality (`Expr`, `Interpret`, `Readiness`), programs (`Program`), models (`Models`), the machine (`Machine` and everything after it). `Collection` does not import `Interpret`, so `pushforward` cannot depend on $\bot$. Collect-after-definedness is enforced one level up, by the `AdmEnv` argument of `Program.collect`. An agent asked to change how reads work knows the change belongs in `Expr`, `Interpret` or `Readiness`, and that everything below it, including `evalWith_stable`, is affected. An agent asked to change publication works in `Machine` and knows `Invariants`, `Soundness`, `Measure` and `Progress` must follow. The mini file has the same one-way order: Part B uses nothing from Part A, Part C uses A and B, Part D uses A to C.

**(b) Each law is a theorem, so a refactor that breaks it does not build.** If the body of `pushforward` is rewritten so that `pushforward_comp` is false, the file stops compiling at that theorem. Example 6.1 shows a mutation on the running example.

**Example 6.1 (a mutation the build catches).** In a scratch copy of the companion, change `collect` so that it adds the candidate value, as in a naive "update in place":

```lean
def collect [Semiring K] (ρ : Env d K) (h : P.AdmEnv ρ) : Env d K :=
  fun a => pushforward P.dst (P.contribution ρ h) a + ρ a
```

Compiling gives two errors. `scorer_models₁` fails: `decide` cannot prove $\Phi_P(\rho_1)=\rho_1$. The theorem `Program.collect_fibre` fails: its goal no longer holds. The `#eval` of collection prints `[0, 8, 0, 8, 1 / 2]` instead of `[0, 4, 0, 4, 1 / 4]`: every defined value doubles, as the prior value is counted again (Proposition 4.7(5)). An agent that ran only the `#eval` would see wrong numbers. An agent that built the file sees two named theorems failing. $\square$

Two cautions. A mutation that changes only the *shape* of a definition can also break proofs for a syntactic reason. Removing the `finished` premise of `Step.publish` breaks `measure_decreases`, `run_sound` and `run_sound_failed` because the constructor changed arity, while the `#eval` outputs stay correct, since `run` has its own `publishable` check. That is a build failure, but it is not a semantic refutation. The semantic content of that premise lives in production: the publish case of `publish_invariant` takes `finished`. And theorems that pass say nothing about speed or memory.

**(c) The non-negotiable facts of CONVENTIONS Section 4 are definition shapes, theorems, or documented boundaries.**

| Fact | Form | Where |
| --- | --- | --- |
| 1. One occurrence per valuation; duplicates are distinct | definition shape | `Program.Occ` is a sigma over list positions; production `Program.Occurrence` |
| 2. Collection sums the fibre; empty is $0$; no prior value | definition shape and theorem | `pushforward`, `Program.collect`; `pushforward_zero`, `Program.collect_fibre`; Example 6.1 |
| 3. $\bot$ is not zero, has no order; no least fixed point | definition shape | `none` of `Option`; `DefLE` orders maps, not `β`; `Program.collect` needs `h : P.AdmEnv ρ`; `Program.Models` ranges over all fixed points |
| 4. Interpretation is strict | definition shape and theorem | `do`-blocks in `evalWith`; `sequenceFin_some_iff`; `not_cartesian` |
| 5. Guard removes occurrences; Iverson multiplies | definition shape (production) | guard subtype in `Program.body` against `Expr.iverson`; not modelled in mini |
| 6. Machine rules; blocked is neither | definition shape | the constructors of `Program.Step`; production `Program.Blocked` |
| 7. Accumulators are not readable; published values are immutable | definition shape | `Config.acc` and `Config.published` are separate fields; `evalReady` reads only `published`; the premise `unpublished` of `Step.publish` |
| 8. Theorem 5.18 needs no certificate; Theorems 5.27 and 5.28 do | theorem signature | `successful_model` takes no `RankCertificate`; `ranked_progress` and `maximal_dichotomy` take one |
| 9. Read stability | theorem | `evalWith_stable`, `interpret_stable` |
| 10. Names are copied, not invented | convention | this chapter's rule; enforced by grep, not by Lean |
| 11. Batching is lax-natural | theorem | `batch_lax`, `batch_lax_strict` |
| 12. No adjunction on $K$-families is claimed | documented boundary | `transpose` is proved; no adjunction statement exists in either development |

In fact 8, whether a theorem needs a hypothesis is visible in its signature, with no need to read the proof.

**(d) The AGENTS.md hierarchy is the same organizing principle for the Python codebase.** The repository's `CLAUDE.md` has an Intent Layer: a tree of `AGENTS.md` nodes, one per subsystem, each recording purpose, contracts, pitfalls and boundaries. Its Global Invariants and Pitfalls read like the Lean facts above:

> **`data_structure/` is a one-way dependency root, with one known exception.** [...]

> **Axis identity is by `UID`, never by name.** Two axes are "the same axis" iff they share a UID; string-based axis matching is a bug wherever it appears (see `data_structure/AGENTS.md` Contracts).

> **`.normalize()` is sum-normalization, not `LayerNorm`** — a documented, easy-to-assume-wrong trap in `torch_compile/`.

(These are verbatim from `CLAUDE.md`, bold markers included; `[...]` marks an omitted continuation, and the dash in the third is the source's own.) The first is the import graph of (a), stated in prose. The second has only a partial Lean counterpart, and it concerns tensors rather than axes: `Declarations.unique : Function.Injective uid` in `Types.lean` forces tensor identity to be by UID, and `Axis` carries a `uid` field, but no theorem says that an axis is identified by its UID alone. Coordinate sets forget axis identity (see [Chapter 2](02-index-categories.md#1-shapes-are-objects-of-finset)), so this is an analogy, not a proved invariant. The third is the kind of trap that the "never implement" list of [Chapter 4](04-denotational.md#8-why-this-matters-for-an-agentic-coder) names for semantics, and the node places it where the agent is working. The principle is the same: split the system into layers, make dependencies one-way, and name the facts that must not be violated. The enforcement differs. In Lean a violation is a compile error. In Python the Intent Layer is prose an agent must read, and the closest enforcement is the test suite (`tests/AGENTS.md` records the golden-file workflow). The hierarchy is weaker than the compiler, but it is the same idea.

**(e) A worked scenario: "optimize by selecting before computing the array".**

**Example 6.2 (select before compute).** An agent is asked to speed up a pipeline that builds a whole array of reciprocals $Q[j]=1/Y[j]$ and then reads $L=Q[1]$. Its plan: read $Y[1]$ first and compute only `recip (Y[1])`. In the notation of [Chapter 3](03-partiality.md#3-sequence-and-batching) it replaces "batch, then select" by "select, then batch". The agent first tries to *justify* the rewrite by stating it as a lemma for all index maps and all primitives:

```lean
theorem select_first_unsound :
    ¬ ∀ (m n : Nat) (f : ℚ → Option ℚ) (r : Fin m → Fin n) (v : Fin n → ℚ),
      (batch f v).map (fun w => w ∘ r) = batch f (v ∘ r) := by
  intro h
  obtain ⟨h1, h2⟩ := batch_lax_strict
  have := h 1 2 recip (fun _ => 0) ![(2:ℚ), 0]
  rw [h1, Option.map_none] at this
  rw [← this] at h2
  simp at h2
```

(New code for this chapter. It compiles in a scratch copy of the companion.) The equality is refuted by `batch_lax_strict`: the instance is $(2,0)$ with $r:[1]\to[2]$. The agent cannot prove the lemma, and the existing theorem `batch_lax` is the most it can have: the rewrite refines the original, turning `none` into `some` and never the reverse. On `Scorer` the difference is visible. At $\eta_1$ we have $Y=(0,4)$, so $Q[0]=1/Y[0]$ is undefined. The original program fails at the occurrence that computes $Q[0]$ and has no model. The rewritten program completes with $L=1/4$. The rewrite turns a failing program into a succeeding one. $\square$

What the agent does with this: it reports the theorem to the user, and it lists the three honest ways to proceed that [Chapter 3](03-partiality.md#3-sequence-and-batching) gives. Prove the primitive total on the relevant range; show that the index map is surjective (the file's `batch_lax` has an exercise on that case below); or prove that the omitted applications succeed. Otherwise it asks whether the user wants the changed meaning. This is the test that refuses the optimization: not a wrong number on a lucky input, but a statement the agent could not prove.

**(f) What the structure does not do.**

- It does not choose the semantics. Lean checks the theorems about the model written in Lean. Whether `Models` is the right notion of meaning is a design decision of the specification ([Chapter 4, Section 1](04-denotational.md#1-what-a-denotational-semantics-must-say)), and it was made before any Lean was written.
- It does not prove floating-point claims. The mini file runs over $\mathbb{Q}$ and production over exact sorts. A theorem about exact sums is not a statement about the order of floating-point reductions ([Chapter 5, Section 12](05-operational.md#12-what-this-chapter-did-not-do)).
- It does not replace mutation testing or fixtures. The specification distinguishes executed evidence (fixtures, mutations, oracles) from theorems. A theorem covers every input of the Lean model. A mutation test covers the code that implements the model. An agent that edits the compiler needs both, and [Chapter 7](07-outlook.md#2-what-is-proved-in-lean-today) returns to the gap between them.

## 6. How to run and extend

**Compile.** From the repository root:

```text
cd leanncd && PATH="$HOME/.elan/bin:$PATH" lake env lean ../papers/course/lean/MiniTensorLogic.lean
```

The README gives the same command without the `PATH` prefix. A clean run prints the output lines of Section 3.8 and exits with code $0$. `leanncd/AGENTS.md` and the Intent Layer table warn about the Mathlib cold build, so use an existing `.lake` and do not rebuild Mathlib.

**Add a statement to `scorer`.** Define `s5 : Stmt scorerDecl ℚ` in the style of `s2`: a `target`, a count `n` of valuations, a `dest : Fin n → Fin (scorerDecl.size target)` and a `body`. Put it in the list `stmts` of a new `Program`. The field `targets_defined` is proved by `rcases hs with rfl | ... <;> rfl`, with one `rfl` per statement, so add one alternative. Nothing else changes: `evalWith`, `footprint`, `Step`, `run` and `run_sound` are generic in the program. The label printed by `describe` is `s` followed by the position plus one. A theorem about the new program, such as a no-model claim, has to be re-proved, because proofs of `scorer_no_model₀` unfold `s1` to `s4` by name.

**Add a primitive.** A primitive is any `K → Option K`. Define it, for instance in the style of `recip`, and use it as `.prim f arg` in a body. Its domain is `{x | (f x).isSome}`. No definition changes. An agent must state the domain, because the domain *is* the semantics of the primitive: for `recip` it is $x\ne0$, and for `relu` all of $\mathbb{Q}$. For a binary primitive, add a constructor and the matching clauses of `evalWith` and `footprint`, in the style of `add`.

**Add `tab` and `at`.** This is a larger change, and production shows its shape. First, tensors need shapes: replace `Decl.size : T → Nat` by a `Shape` of axes with a `Coord` type and a `Layout` bijection to a flat `Fin`, as in `Types.lean`. Second, `Expr` needs a second index for the value type, `Ty`, so that `tab` has type `Expr K σ r (Γ × Coord sh.axes) (.scalar s) → Expr K σ r Γ (.array s sh)` and `at` consumes an array and returns a scalar. Third, `evalWith` needs a clause for each. `tab` sequences over `Fin layout.count` and transports the result along `layout.enumerate`; the non-dependent `sequenceFin` form suffices here, because every component has the same type, and the dependent `sequence` is needed only for `prim`, whose arguments have different types. `at` binds the array and applies it to the index. Fourth, `footprint` needs two clauses. Fifth, and most important, add a read-stability theorem like `evalWith_stable` and extend its induction to the two new cases, because the layout transport is exactly where a subtle bug would hide. [Chapter 3](03-partiality.md#4-interpretation-of-core-expressions-as-a-structural-map-into-pfn) derives layout independence from the Lean theorem `tab_complete` (`Completeness.lean`), whose statement does not mention the layout, so an agent changing `tab` must keep that theorem, and the `tab` case of `evalWith_stable`, compiling.

*Why this matters for an agentic coder.* The recipes are short because the structure is generic: one new constructor touches one interpreter, one footprint and one induction. A change that touches more places than that is a sign that a layer is being crossed.

## Exercises

1. **Duplicate a writer.** Define `scorerDup`, a program with statement list `[s1, s2, s2, s3, s4]`. Predict by hand the output of `describe` on `runToEnd (scorerDup.initial ρ₁)` and on `ρ₀`, including the occurrence label at which the run on $\eta_0$ fails. Check with `#eval`. Which statement of Section 4 of CONVENTIONS does the result illustrate?

2. **A constant family.** State and prove, for `pushforward f (fun _ => c)` at a coordinate `j`, a formula in terms of the cardinality of the fibre `Finset.univ.filter (fun i => f i = j)`. What does it say when the fibre is empty? Relate the result to Proposition 4.7(3).

3. **Two primitives.** Prove that `evalWith σ (.prim g (.prim f e)) γ = (evalWith σ e γ >>= f) >>= g`, the Kleisli composite. Then choose `f := recip`, `g := fun _ => some 0` and a store in which the read of `e` returns `0`. Predict and check the result with `#eval`. Why is it `none` although `g` is total and constant?

4. **A blocked program.** Encode `T[] = T[]` in the mini language: a `Decl` with one tensor of size $1$, a statement `T[0] += read T[0]`, and a `Program` whose `input` is `fun _ => false`. Prove, by `decide +kernel` or otherwise, that `runToEnd` from the initial configuration returns `.blocked`. Then explain, using [Chapter 4, Example 4.16](04-denotational.md#5-denotation-as-a-partial-function) and [Chapter 5, Example 5.36](05-operational.md#95-cycles-block-with-or-without-a-model), why this does not show that the program has no model.

5. $^\ast$ **Guard against Iverson.** Add a constructor `iverson (q : Γ → Bool)` to `Expr`, update `evalWith` (value `1` if `q γ`, else `0`) and `footprint` (the empty list). Which existing theorems need edits? (Check by compiling.) With $X=(4,0)$, encode the guarded statement (one valuation, `i = 0`) and the Iverson statement (two valuations, body `iverson (i < 1)` times `recip (X[i])`). Predict and check the outcomes. Relate the result to Example 3.18 and to CONVENTIONS fact 5.

6. $^\ast$ **The converse of `batch_lax`.** State and prove: if `r : Fin m → Fin n` is surjective, then `DefLE (fun v => batch f (v ∘ r)) (fun v => (batch f v).map (fun w => w ∘ r))`. Hint: choose a section `g` of `r` with `choose`, build the batched value on `Fin n` from `b ∘ g`, and use `sequenceFin_eq_some_iff` both ways. Explain why this is the case in which Proposition 3.13 holds with equality.

7. **Three mutants.** Predict, for each of the following edits to a copy of the companion, which declarations fail to compile and what `#eval` prints. Then check. (a) `collect` adds `ρ a`, as in Example 6.1. (b) `Step.publish` loses its `finished` premise. (c) `pushforward` tests `f i ≠ j` instead of `f i = j`. Which of the three is caught only by the build and not by the `#eval` outputs?

8. **Why production needs no `initial_nodup`.** The mini file proves `Program.initial_nodup` because `pending` is a `List`. Read `initial` and the type `Pending` in `Machine.lean`, and explain why production has no counterpart. What does `Finset.univ` do for the statement "each occurrence contributes exactly once"? Which of the simplifications in Section 4 does this exercise illustrate?
