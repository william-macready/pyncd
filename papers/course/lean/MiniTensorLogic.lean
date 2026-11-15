import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.DeriveFintype

/-!
# MiniTensorLogic: the compiled companion of the course

This file is the Lean companion of the course on the categorical semantics of
Tensor Logic (`papers/course/`). Chapter 6 walks through it. It is a deliberately
small re-telling of the production module `LeanNCD.Semantics` (under
`leanncd/LeanNCD/Semantics/`), which it does NOT import:

* Part A (Chapter 2): index geometry. Families, pullback, pushforward, the
  transpose identity, the Naperian adjunction, weighted spans.
* Part B (Chapter 3): partiality. `sequenceFin`, batching, lax naturality.
* Part C (Chapters 1, 3, 4): expressions, programs, collection, models, and the
  running example `Scorer`.
* Part D (Chapter 5): the machine, its termination measure, and an executable
  scheduler.

Simplifications versus production are stated where they occur and collected in
Chapter 6. The scalar sort of every example is `K = ℚ`, so everything computes.
-/

namespace Course

open Finset

/-! ## Part A. Index geometry (Chapter 2) -/

section PartA

/-- Chapter 2, Definition 2.6. A `K`-valued family over the coordinate set `I`,
an element of `K^I`. Naperian: a family is literally a function.
(Production: `LeanNCD.Semantics.Family` in `Collection.lean`.) -/
abbrev Family (I K : Type) := I → K

/-- Chapter 2, Definition 2.6. Pullback (restriction) `f^* v = v ∘ f` along an
index map `f : I → J`. This is the contravariant functor `FinSet^op → Set`;
reads are pullbacks. It needs no structure on `K`. -/
def pullback {I J K : Type} (f : I → J) (v : Family J K) : Family I K := v ∘ f

/-- Chapter 2, Definition 2.6. Pushforward (sum over fibres)
`(f_! v)(j) = ⊕_{f i = j} v i`. The `if` selects the fibre `f⁻¹(j)`; an empty
fibre gives `0`. This is the covariant functor `FinSet → CMon`, the
decategorified left Kan extension `Σ_f`; additive writes are pushforwards.
(Production: `LeanNCD.Semantics.pushforward`.) -/
def pushforward {I J K : Type} [Fintype I] [DecidableEq J] [AddCommMonoid K]
    (f : I → J) (v : Family I K) : Family J K :=
  fun j => ∑ i, if f i = j then v i else 0

/-- Chapter 2, Proposition 2.7 (dual part). Pullback along the identity is the
identity: functoriality of `K^(-)` on identities. -/
theorem pullback_id {I K : Type} (v : Family I K) : pullback id v = v := rfl

/-- Chapter 2, Proposition 2.7 (dual part). Pullback is contravariant:
`(g ∘ f)^* = f^* ∘ g^*`. -/
theorem pullback_comp {I J L K : Type} (f : I → J) (g : J → L) (v : Family L K) :
    pullback (g ∘ f) v = pullback f (pullback g v) := rfl

variable {I J L K : Type} [Fintype I] [AddCommMonoid K]

/-- Chapter 2, Proposition 2.7(1). Pushforward preserves zero.
(Adapted from `pushforward_zero` in `leanncd/LeanNCD/Semantics/Collection.lean`.) -/
theorem pushforward_zero [DecidableEq J] (f : I → J) :
    pushforward f (0 : Family I K) = 0 := by
  funext j
  simp [pushforward]

/-- Chapter 2, Proposition 2.7(1). Pushforward preserves addition, so `f_!` is a
monoid homomorphism `K^I → K^J`.
(Adapted from `pushforward_add` in `Collection.lean`.) -/
theorem pushforward_add [DecidableEq J] (f : I → J) (v w : Family I K) :
    pushforward f (v + w) = pushforward f v + pushforward f w := by
  funext j
  simp only [pushforward, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Chapter 2, Proposition 2.7(2). Pushforward along the identity is the
identity: every fibre of `id` is a singleton.
(Adapted from `pushforward_id` in `Collection.lean`.) -/
theorem pushforward_id [DecidableEq I] (v : Family I K) : pushforward id v = v := by
  funext i
  exact Finset.sum_ite_eq_of_mem' Finset.univ i v (Finset.mem_univ i)

/-- Chapter 2, Proposition 2.7(2). Pushforward is covariant:
`(g ∘ f)_! = g_! ∘ f_!` (summing over the fibre of `g ∘ f` is summing over the
fibres of `f` inside the fibre of `g`).
(Adapted from `pushforward_comp` in `Collection.lean`.) -/
theorem pushforward_comp [Fintype J] [DecidableEq J] [DecidableEq L]
    (f : I → J) (g : J → L) (v : Family I K) :
    pushforward g (pushforward f v) = pushforward (g ∘ f) v := by
  funext l
  simp only [pushforward, Function.comp_apply]
  have distribute (j : J) :
      (if g j = l then ∑ i, if f i = j then v i else 0 else 0) =
      ∑ i, if g j = l then (if f i = j then v i else 0) else 0 := by
    by_cases h : g j = l <;> simp [h]
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have swap (j : J) :
      (if g j = l then (if f i = j then v i else 0) else 0) =
      if f i = j then (if g j = l then v i else 0) else 0 := by
    split_ifs <;> rfl
  simp_rw [swap]
  exact Finset.sum_ite_eq_of_mem Finset.univ (f i) _ (Finset.mem_univ _)

/-- Chapter 2, Proposition 2.7(3) (relabeling). For a bijection `e : I' ≃ I`,
`(f ∘ e)_! (v ∘ e) = f_! v`: renaming the occurrences does not change the sum.
(Adapted from `pushforward_relabel` in `Collection.lean`.) -/
theorem pushforward_relabel {I' : Type} [Fintype I'] [DecidableEq J]
    (e : I' ≃ I) (f : I → J) (v : Family I K) :
    pushforward (f ∘ e) (v ∘ e) = pushforward f v := by
  funext j
  exact Equiv.sum_comp e (fun i => if f i = j then v i else 0)

/-- Chapter 2, Proposition 2.7(4) (grouping). Over a coproduct
`(a : A) × B a`, the pushforward is the sum of the pushforwards of the
summands: `Lan` out of a coproduct is the coproduct of the `Lan`s.
(Adapted from `pushforward_grouped` in `Collection.lean`.) -/
theorem pushforward_grouped {A : Type} [Fintype A] {B : A → Type}
    [∀ a, Fintype (B a)] [DecidableEq J]
    (f : ((a : A) × B a) → J) (v : Family ((a : A) × B a) K) (j : J) :
    pushforward f v j =
      ∑ a, pushforward (fun b => f ⟨a, b⟩) (fun b => v ⟨a, b⟩) j := by
  simp only [pushforward, Fintype.sum_sigma]

/-- Chapter 2, notation `⟨u, v⟩_I = ⊕_i u(i) ⊗ v(i)`: the pairing on `K^I`.
It needs a commutative semiring. -/
def pairing {I K : Type} [Fintype I] [CommSemiring K] (u v : Family I K) : K :=
  ∑ i, u i * v i

/-- Chapter 2, Proposition 2.8 (the transpose identity)
`⟨f_! u, w⟩_J = ⟨u, f^* w⟩_I`. This is what "adjoint" means for linear maps:
`f_!` and `f^*` are transpose matrices. It is the decategorified shadow of the
adjunction `Σ_f ⊣ f^*` on set-valued families; no adjunction of functors on
`K`-families is claimed (CONVENTIONS fact 12). -/
theorem transpose {I J K : Type} [Fintype I] [Fintype J] [DecidableEq J]
    [CommSemiring K] (f : I → J) (u : Family I K) (w : Family J K) :
    pairing (pushforward f u) w = pairing u (pullback f w) := by
  simp only [pairing, pushforward, pullback, Function.comp_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [ite_mul, zero_mul]
  simp

/-- Chapter 2, Proposition 2.9 (the Naperian adjunction `(-) × I ⊣ (-)^I`),
instantiated at `A`: maps `A × I → B` correspond to maps `A → (I → B)`. This is
currying. The unit `A → (A × I)^I`, `a ↦ (i ↦ (a, i))`, is tabulation; the
counit `B^I × I → B`, `(v, i) ↦ v i`, is lookup. Consequently
`K^(I × J) ≃ (K^J)^I`. -/
def naperian (A I B : Type) : (A × I → B) ≃ (A → (I → B)) where
  toFun f a i := f (a, i)
  invFun g p := g p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Chapter 2, Definitions 2.10 and 2.11. A weighted span
`I ←l– M –r→ J` in `FinSet` with weight `w ∈ K^M`. The apex `M` carries its own
`Fintype` instance. Spans are not quotiented by span isomorphism here; only
their linearizations are compared. -/
structure WSpan (K I J : Type) where
  /-- The apex of the span. -/
  M : Type
  /-- The apex is finite. -/
  [fm : Fintype M]
  /-- The left leg. -/
  l : M → I
  /-- The right leg. -/
  r : M → J
  /-- The weight on the apex. -/
  w : M → K

attribute [instance] WSpan.fm

/-- Chapter 2, Definition 2.11. Linearization of a weighted span: the map
`K^I → K^J`, `u ↦ r_!(l^* u ⊗ w)`. -/
def WSpan.lin {I J K : Type} [CommSemiring K] [DecidableEq J] (s : WSpan K I J)
    (u : Family I K) : Family J K :=
  pushforward s.r (fun m => u (s.l m) * s.w m)

/-- Chapter 2, Definition 2.10. Composition of weighted spans by pullback: the
apex is the fibre product `M ×_J N = {(m, n) | r m = l' n}`, the legs are
`l ∘ π_M` and `r' ∘ π_N`, and the weight is `π_M^* w ⊗ π_N^* w'`. -/
def WSpan.comp {I J L K : Type} [Mul K] [DecidableEq J] (s : WSpan K I J)
    (t : WSpan K J L) : WSpan K I L where
  M := {p : s.M × t.M // s.r p.1 = t.l p.2}
  l p := s.l p.1.1
  r p := t.r p.1.2
  w p := s.w p.1.1 * t.w p.1.2

/-- Chapter 2, Proposition 2.12. Composition of weighted spans linearizes to
the composite of linearizations (matrix product): `Lin` is a functor
`Span(FinSet) → Mat(K)` on composites. The proof is the decategorified
Beck–Chevalley square: a sum over the fibre product is a double sum with an
equality test, then distributivity. -/
theorem WSpan.lin_comp {I J L K : Type} [CommSemiring K] [DecidableEq J]
    [DecidableEq L] (s : WSpan K I J) (t : WSpan K J L) (u : Family I K) :
    (s.comp t).lin u = t.lin (s.lin u) := by
  funext l
  simp only [WSpan.lin, WSpan.comp, pushforward]
  -- Left side: a sum over the fibre product, rewritten as a filtered double sum.
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : s.M × t.M => s.r p.1 = t.l p.2)
      (by simp) (fun p : s.M × t.M =>
        if t.r p.2 = l then u (s.l p.1) * (s.w p.1 * t.w p.2) else 0)]
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  -- Right side: distribute the outer weight and test into the inner sum.
  split_ifs with hn
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> simp [mul_assoc]
  · simp

/-- Chapter 2, running example (Proposition 2.13). The weight matrix `W` of
`Scorer` on the primary input `η₁`, as a family over `[2] × [2]` with
`W[0,0] = 1`, `W[0,1] = 1`, `W[1,0] = 2`, `W[1,1] = -1`. -/
def W₁ : Family (Fin 2 × Fin 2) ℚ := fun p => ![![1, 1], ![2, -1]] p.1 p.2

/-- Chapter 2, running example. The input vector `X = (1, -2)` of `η₁`. -/
def X₁ : Family (Fin 2) ℚ := ![1, -2]

/-- Chapter 2, Proposition 2.13 on the running example: the pure-einsum value of
`s1`, `V_s1 = (π_out)_!(π_W^* W ⊗ π_X^* X)` with `M = [2] × [2]`,
`π_W = id`, `π_X (j, i) = i`, `π_out (j, i) = j`. -/
def Vs1 : Family (Fin 2) ℚ :=
  pushforward (fun p : Fin 2 × Fin 2 => p.1) (fun p => W₁ p * X₁ p.2)

-- Expected output: [-1, 4]
#eval [Vs1 0, Vs1 1]

/-- Chapter 2, running example checked in the kernel: `V_s1 = (-1, 4)`. -/
example : Vs1 0 = -1 ∧ Vs1 1 = 4 := by decide +kernel

end PartA

/-! ## Part B. Partiality (Chapter 3) -/

section PartB

variable {α β : Type}

/-- Chapter 3, `sequence`: the strength of `Option` over a finite product.
A tabulation `Fin n → Option α` is defined iff every component is, and then it
is the tuple of the components. For `n = 0` the empty tuple is defined.
(Non-dependent adaptation of `sequence` in
`leanncd/LeanNCD/Semantics/Interpret.lean`.) -/
def sequenceFin : {n : Nat} → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => some Fin.elim0
  | _ + 1, f => do
      let x ← f 0
      let xs ← sequenceFin (fun i => f i.succ)
      pure (Fin.cons x xs)

/-- Chapter 3. The empty tabulation is always defined. -/
theorem sequenceFin_zero (f : Fin 0 → Option α) : sequenceFin f = some Fin.elim0 := rfl

/-- Chapter 3. Characterization of `sequenceFin`: it returns `g` exactly when
every component returns the corresponding entry of `g`. -/
theorem sequenceFin_eq_some_iff :
    ∀ {n : Nat} (f : Fin n → Option α) (g : Fin n → α),
      sequenceFin f = some g ↔ ∀ i, f i = some (g i)
  | 0, f, g => by
    refine ⟨fun _ i => i.elim0, fun _ => ?_⟩
    rw [sequenceFin_zero]
    congr 1
    funext i
    exact i.elim0
  | n + 1, f, g => by
    have ih := sequenceFin_eq_some_iff (fun i : Fin n => f i.succ) (fun i => g i.succ)
    simp only [sequenceFin]
    constructor
    · intro h
      cases h0 : f 0 with
      | none => simp [h0] at h
      | some x =>
        cases ht : sequenceFin (fun i : Fin n => f i.succ) with
        | none => simp [h0, ht] at h
        | some xs =>
          simp only [h0, ht, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at h
          subst h
          have hxs := (sequenceFin_eq_some_iff _ xs).mp ht
          intro i
          refine Fin.cases ?_ (fun i => ?_) i
          · simpa using h0
          · simpa using hxs i
    · intro h
      have ht : sequenceFin (fun i : Fin n => f i.succ) = some (fun i => g i.succ) :=
        ih.mpr (fun i => h i.succ)
      rw [h 0, ht]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- Chapter 3. A tabulation is defined iff every component is defined
(strictness of `sequence`: one undefined component makes the whole undefined). -/
theorem sequenceFin_some_iff {n : Nat} (f : Fin n → Option α) :
    (sequenceFin f).isSome ↔ ∀ i, (f i).isSome := by
  constructor
  · intro h i
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp h
    simp [(sequenceFin_eq_some_iff f g).mp hg i]
  · intro h
    have hg := (sequenceFin_eq_some_iff f (fun i => (f i).get (h i))).mpr
      (fun i => by simp)
    simp [hg]

/-- Chapter 3. Batching a partial map `f : α ⇀ β` over the finite index set
`[n]`: apply it componentwise and `sequence`. This is the action of the
Kleisli map on `n`-tuples. -/
def batch {n : Nat} (f : α → Option β) : (Fin n → α) → Option (Fin n → β) :=
  fun v => sequenceFin (f ∘ v)

/-- Chapter 3. The definedness order on partial maps `α ⇀ β`: `g ⪯ h` when `h`
is defined (with the same value) wherever `g` is. Undefined is not a value and
not a least element of `β`; this is an order on maps, not on `β`. -/
def DefLE (g h : α → Option β) : Prop := ∀ a b, g a = some b → h a = some b

/-- Chapter 3, CONVENTIONS fact 11 (LAX NATURALITY). For `r : [m] → [n]`,
`r^* ∘ batch_n f ⪯ batch_m f ∘ r^*`: batching over the big index set and then
restricting is less defined than restricting first. The converse fails when `r`
forgets an undefined component (see `batch_lax_strict`). -/
theorem batch_lax {m n : Nat} (f : α → Option β) (r : Fin m → Fin n) :
    DefLE (fun v : Fin n → α => (batch f v).map (fun w => w ∘ r))
      (fun v => batch f (v ∘ r)) := by
  intro v b h
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
  have hall := (sequenceFin_eq_some_iff _ w).mp hw
  exact (sequenceFin_eq_some_iff _ (w ∘ r)).mpr (fun i => hall (r i))

/-- Chapter 3, counterexample partial primitive: the reciprocal on `ℚ`,
undefined exactly at `0`. -/
def recip : ℚ → Option ℚ := fun q => if q = 0 then none else some (1 / q)

/-- Chapter 3, lax naturality is strict: batching `recip` over `[2]` at
`(2, 0)` is undefined, while restricting along `r : [1] → [2]`, `0 ↦ 0` first
gives the defined `(1/2)`. -/
theorem batch_lax_strict :
    batch recip ![(2 : ℚ), 0] = none ∧
      (batch recip (![(2 : ℚ), 0] ∘ (fun _ : Fin 1 => 0))).map (fun w => w 0) =
        some (1 / 2) := by
  constructor <;> simp [batch, sequenceFin, recip]

-- Expected output: none
#eval (batch recip ![(2 : ℚ), 0]).map List.ofFn
-- Expected output: some [1 / 2]
#eval (batch recip (![(2 : ℚ), 0] ∘ (fun _ : Fin 1 => 0))).map List.ofFn

/-- Chapter 3. Strict pairing is not cartesian in `Pfn = Kl(Option)`: projecting
the strict pair `⟨f, g⟩` back to its first component does not recover `f`,
because the pair is undefined whenever `g` is. Witness: `f = pure`,
`g = recip`, at `a = 0`. -/
theorem not_cartesian : ∃ (f g : ℚ → Option ℚ) (a : ℚ),
    (do let x ← f a; let _ ← g a; pure x) ≠ f a :=
  ⟨pure, recip, 0, by simp [recip]⟩

end PartB

/-! ## Part C. Expressions, programs, models (Chapters 1, 3, 4) -/

section PartC

/-- Chapter 1, the tensor signature `Σ`. A finite, decidable set of tensor
identifiers, each with a flattened coordinate count: coordinates of `T` are
`[size T]` (rank-flattened; production keeps the shape `Coord sh`).
`tensors` is an explicit enumeration used only by the executable scheduler of
Part D (production enumerates through `Fintype` noncomputably). -/
structure Decl where
  /-- Tensor identifiers. -/
  T : Type
  /-- Finitely many tensors. -/
  [fT : Fintype T]
  /-- Tensor identity is decidable (identity by name of the identifier, never
  by shape). -/
  [dT : DecidableEq T]
  /-- Flattened coordinate count of each tensor. -/
  size : T → Nat
  /-- An executable enumeration of the tensors. -/
  tensors : List T
  /-- The enumeration is complete. -/
  tensors_complete : ∀ t, t ∈ tensors

attribute [instance] Decl.fT Decl.dT

/-- Chapter 1/4, `Addr_Σ = {(T, p)}`: an address is a tensor with one of its
coordinates. A sigma type, i.e. the coproduct `∐_T Coord(T)` in `FinSet`. -/
abbrev Addr (d : Decl) := (t : d.T) × Fin (d.size t)

/-- Chapter 4, `Env_Σ = ∏_T K^Coord(T)`: a complete environment, one scalar per
address. Uncurried (Naperian adjunction, Proposition 2.9). -/
abbrev Env (d : Decl) (K : Type) := Addr d → K

/-- Chapter 1, the core expression language over the index context `Γ` (a
type of valuations). Index expressions are Lean functions `Γ → Fin _`, so every
read is in bounds by typing (production: an `AdmittedRead` carrying a raw
coordinate and its resolved outcome; no guards, Iverson factors, tabulations or arrays here).
`reduce n body` sums `body` over a fresh binder `Fin n`. -/
inductive Expr (d : Decl) (K : Type) : Type → Type 1
  /-- A scalar literal. -/
  | lit {Γ : Type} (c : K) : Expr d K Γ
  /-- Read tensor `t` at the coordinate computed from the valuation. -/
  | read {Γ : Type} (t : d.T) (ix : Γ → Fin (d.size t)) : Expr d K Γ
  /-- Strict addition. -/
  | add {Γ : Type} (a b : Expr d K Γ) : Expr d K Γ
  /-- Strict multiplication. -/
  | mul {Γ : Type} (a b : Expr d K Γ) : Expr d K Γ
  /-- Reduction (sum) over a fresh binder ranging over `[n]`. -/
  | reduce {Γ : Type} (n : Nat) (body : Expr d K (Γ × Fin n)) : Expr d K Γ
  /-- A unary partial primitive with domain `{x | (f x).isSome}`. -/
  | prim {Γ : Type} (f : K → Option K) (arg : Expr d K Γ) : Expr d K Γ

variable {d : Decl} {K : Type}

/-- Chapter 3/5: evaluation against a partial store `σ : Addr ⇀ K`, a
structural map into `Kl(Option)`. Reads look up the store; `add`/`mul` are
strict (two binds); `reduce` tabulates with `sequenceFin` and then sums (an
empty reduction is `0` and evaluates no body); `prim` binds and then applies.
(Adapted from `evalWith` in `leanncd/LeanNCD/Semantics/Interpret.lean`, which
folds reductions with `foldValues` instead.) -/
def evalWith [Semiring K] (σ : Addr d → Option K) :
    {Γ : Type} → Expr d K Γ → Γ → Option K
  | _, .lit c, _ => some c
  | _, .read t ix, γ => σ ⟨t, ix γ⟩
  | _, .add a b, γ => do
      let x ← evalWith σ a γ
      let y ← evalWith σ b γ
      pure (x + y)
  | _, .mul a b, γ => do
      let x ← evalWith σ a γ
      let y ← evalWith σ b γ
      pure (x * y)
  | _, .reduce _ body, γ => do
      let xs ← sequenceFin (fun i => evalWith σ body (γ, i))
      pure (∑ i, xs i)
  | _, .prim f a, γ => do
      let x ← evalWith σ a γ
      f x

/-- Chapter 3: a structural map into `Kl(Option)`. The interpretation
`⟦E⟧_{ρ,ν} ∈ Result(K)` of a body in a complete environment `ρ`: reads are total
(`some (ρ a)`), so undefinedness comes only from primitives. This is
`evalWith` at the total store `some ∘ ρ`, exactly as production's `interpret`. -/
def interpret [Semiring K] (ρ : Env d K) {Γ : Type} (e : Expr d K Γ) (γ : Γ) :
    Option K :=
  evalWith (fun a => some (ρ a)) e γ

/-- Chapter 1, a core statement `T[φ(ν)] += E` for `ν ∈ D_s`. The admissible
valuation set `D_s` is `[n]` itself: guards are applied by choosing `n` and the
enumeration (production: valuations `Fin m` with a Boolean guard subtype). -/
structure Stmt (d : Decl) (K : Type) where
  /-- The written tensor `T_s`. -/
  target : d.T
  /-- The number of admissible valuations, `|D_s|`. -/
  n : Nat
  /-- The write map `φ_s : D_s → Coord(T_s)`. -/
  dest : Fin n → Fin (d.size target)
  /-- The body `E_s`, over the context `D_s`. -/
  body : Expr d K (Fin n)

/-- Chapter 1, a program: which tensors are inputs, and a list of statements,
each writing a defined (non-input) tensor. Duplicate statements are distinct
list entries, hence distinct occurrences (CONVENTIONS fact 1). (Production:
statements grouped per defined tensor, plus an output flag; outputs are
omitted here.) -/
structure Program (d : Decl) (K : Type) where
  /-- `T ∈ In`. -/
  input : d.T → Bool
  /-- The statements, in source order. -/
  stmts : List (Stmt d K)
  /-- Every target is a defined tensor. -/
  targets_defined : ∀ s ∈ stmts, input s.target = false

namespace Program

variable (P : Program d K)

/-- Chapter 2, Definition 2.14: occurrences `O_P = ∐_s D_s`, a sigma type over
statement positions. A coproduct, not a union: identical statements give
distinct occurrences. (Production: `Program.Occurrence`.) -/
abbrev Occ := (i : Fin P.stmts.length) × Fin (P.stmts.get i).n

/-- Chapter 2, Definition 2.14: the destination map `dst : O_P → Addr`, the
copairing of the write maps, `dst(s, ν) = (T_s, φ_s ν)`. -/
def dst (o : P.Occ) : Addr d :=
  ⟨(P.stmts.get o.1).target, (P.stmts.get o.1).dest o.2⟩

/-- Chapter 4: the value `⟦E_s⟧_{ρ,ν}` of an occurrence's body.
(Production: `Program.outcome`.) -/
def bodyVal [Semiring K] (ρ : Env d K) (o : P.Occ) : Option K :=
  interpret ρ (P.stmts.get o.1).body o.2

/-- Chapter 4, `AdmEnv(P)`: environments in which every occurrence body is
defined. -/
def AdmEnv [Semiring K] (ρ : Env d K) : Prop := ∀ o, (P.bodyVal ρ o).isSome

/-- Chapter 4: the scalar contributed by an occurrence of an admissible
environment. Collection begins only after definedness. -/
def contribution [Semiring K] (ρ : Env d K) (h : P.AdmEnv ρ) (o : P.Occ) : K :=
  (P.bodyVal ρ o).get (h o)

/-- Chapter 4, `Collect_P(ρ)(a) = ⊕_{o ∈ dst⁻¹(a)} ⟦E_s⟧_{ρ,ν}`: the
pushforward `dst_!` of the contribution family, literally Chapter 2's functor.
Empty fibres collect `0`; the prior value of `ρ a` is not a summand.
(Production: `Program.collect`.) -/
def collect [Semiring K] (ρ : Env d K) (h : P.AdmEnv ρ) : Env d K :=
  pushforward P.dst (P.contribution ρ h)

/-- Chapter 4, the equation operator `Φ_P : AdmEnv(P) → Env_Σ`: inputs are
copied, defined tensors are collected. A partial operator; no iteration is
specified. (Production: `Program.equationOperator`.) -/
def equationOperator [Semiring K] (ρ : Env d K) (h : P.AdmEnv ρ) : Env d K :=
  fun a => if P.input a.1 then ρ a else P.collect ρ h a

/-- Chapter 4, `Models(P, η)`: admissible environments extending the input `η`
that are fixed points of `Φ_P` (an equalizer of `Φ_P` and the inclusion). There
is no least fixed point and no order on `⊥`; all fixed points count.
(Production defines `Models` by the collect equations and proves this form.) -/
def Models [Semiring K] (η : (a : Addr d) → P.input a.1 = true → K)
    (ρ : Env d K) : Prop :=
  ∃ h : P.AdmEnv ρ, (∀ a (hi : P.input a.1 = true), ρ a = η a hi) ∧
    P.equationOperator ρ h = ρ

/-- Chapter 4: the fixed-point form of `Models` is equivalent to the collect
equations `ρ a = Collect_P(ρ)(a)` at every defined address.
(Adapted from `models_fixedpoint` in `leanncd/LeanNCD/Semantics/Models.lean`,
with the two sides swapped because `Models` is defined the other way here.) -/
theorem models_fixedpoint [Semiring K] (η : (a : Addr d) → P.input a.1 = true → K)
    (ρ : Env d K) :
    P.Models η ρ ↔ ∃ h : P.AdmEnv ρ, (∀ a (hi : P.input a.1 = true), ρ a = η a hi) ∧
      ∀ a, P.input a.1 = false → ρ a = P.collect ρ h a := by
  constructor
  · rintro ⟨h, agree, fixed⟩
    refine ⟨h, agree, fun a ha => ?_⟩
    have cell := congrFun fixed a
    simp only [equationOperator, ha] at cell
    exact cell.symm
  · rintro ⟨h, agree, equations⟩
    refine ⟨h, agree, ?_⟩
    funext a
    unfold equationOperator
    cases ha : P.input a.1
    · exact (equations a ha).symm
    · rfl

/-- Chapter 4, `AdmInput(P)`: inputs with exactly one model; on these the
denotation `⟦P⟧ η` is defined. -/
def AdmInput [Semiring K] (η : (a : Addr d) → P.input a.1 = true → K) : Prop :=
  ∃! ρ, P.Models η ρ

end Program

/-! ### The running example `Scorer` (CONVENTIONS section 3) -/

/-- Chapter 1, the tensor identifiers of `Scorer`. -/
inductive ScorerTensor
  | X | W | B | Z | Y | L
  deriving DecidableEq, Fintype, Repr

/-- Chapter 1, the signature of `Scorer`, rank-flattened: `W[j,i]` lives at
flat coordinate `2j + i`, and the scalar `L[]` has one coordinate. -/
def scorerDecl : Decl where
  T := ScorerTensor
  size
    | .X => 2 | .W => 4 | .B => 2
    | .Z => 2 | .Y => 2 | .L => 1
  tensors := [.X, .W, .B, .Z, .Y, .L]
  tensors_complete := by intro t; cases t <;> simp

/-- Chapter 1, the flat coordinate `2j + i` of `W[j, i]`. -/
def wIdx (j i : Fin 2) : Fin 4 := ⟨2 * j.val + i.val, by omega⟩

/-- Chapter 1, `relu`, a total primitive. -/
def relu : ℚ → Option ℚ := fun q => some (max q 0)

/-- Chapter 1, `s1: Z[j] += ⊕_i W[j,i] ⊗ X[i]` for `j ∈ [2]`. -/
def s1 : Stmt scorerDecl ℚ where
  target := .Z
  n := 2
  dest := fun j => j
  body := .reduce 2 (.mul (.read .W (fun p => wIdx p.1 p.2)) (.read .X (fun p => p.2)))

/-- Chapter 1, `s2: Z[j] += B[j]` for `j ∈ [2]`, a second writer to `Z[j]`. -/
def s2 : Stmt scorerDecl ℚ where
  target := .Z
  n := 2
  dest := fun j => j
  body := .read .B (fun j => j)

/-- Chapter 1, `s3: Y[j] += relu(Z[j])` for `j ∈ [2]`. -/
def s3 : Stmt scorerDecl ℚ where
  target := .Y
  n := 2
  dest := fun j => j
  body := .prim relu (.read .Z (fun j => j))

/-- Chapter 1, `s4: L[] += recip(Y[1])` (no binders: one valuation).
The course prose writes `log(Y[1])`; the Lean uses `recip` so that everything
computes over `ℚ`. Both are undefined exactly when `Y[1] = 0` (on the values
`relu` produces, `log` is undefined exactly at `0`), which is all the running
example uses. The model value `L = log 4` therefore becomes `L = 1/4`. -/
def s4 : Stmt scorerDecl ℚ where
  target := .L
  n := 1
  dest := fun _ => (0 : Fin 1)
  body := .prim recip (.read .Y (fun _ => (1 : Fin 2)))

/-- Chapter 1, the program `Scorer`: inputs `X, W, B`; statements `s1..s4`.
Its occurrences are `D_s1 ⊔ D_s2 ⊔ D_s3 ⊔ D_s4`, seven in total. -/
def scorer : Program scorerDecl ℚ where
  input
    | .X | .W | .B => true
    | _ => false
  stmts := [s1, s2, s3, s4]
  targets_defined := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> rfl

/-- Chapter 4, build an environment from per-tensor value lists (flat order). -/
def envOf (vals : ScorerTensor → List ℚ) : Env scorerDecl ℚ :=
  fun a => (vals a.1).getD a.2.val 0

/-- Chapter 4, `η₁` extended by the claimed model: inputs `X = (1,-2)`,
`W = [[1,1],[2,-1]]`, `B = (1,0)`, and `Z = (0,4)`, `Y = (0,4)`,
`L = 1/4` (the `recip` stand-in for `log 4`). -/
def ρ₁ : Env scorerDecl ℚ := envOf fun
  | .X => [1, -2] | .W => [1, 1, 2, -1] | .B => [1, 0]
  | .Z => [0, 4] | .Y => [0, 4] | .L => [1 / 4]

/-- Chapter 4, `η₀` (`X = (0, 0)`) extended by the values forced by `s1..s3`:
`Z = (1, 0)`, `Y = (1, 0)`; `L` is a placeholder `0`, since no value works. -/
def ρ₀ : Env scorerDecl ℚ := envOf fun
  | .X => [0, 0] | .W => [1, 1, 2, -1] | .B => [1, 0]
  | .Z => [1, 0] | .Y => [1, 0] | .L => [0]

/-- Chapter 4, the input `η` read off an environment (its input coordinates). -/
def inputOf (ρ : Env scorerDecl ℚ) :
    (a : Addr scorerDecl) → scorer.input a.1 = true → ℚ :=
  fun a _ => ρ a

/-- Chapter 4, the seven occurrences of `Scorer`, as (statement position,
valuation) pairs. -/
def scorerOccs : List scorer.Occ :=
  [⟨(0 : Fin 4), (0 : Fin 2)⟩, ⟨(0 : Fin 4), (1 : Fin 2)⟩,
   ⟨(1 : Fin 4), (0 : Fin 2)⟩, ⟨(1 : Fin 4), (1 : Fin 2)⟩,
   ⟨(2 : Fin 4), (0 : Fin 2)⟩, ⟨(2 : Fin 4), (1 : Fin 2)⟩,
   ⟨(3 : Fin 4), (0 : Fin 1)⟩]

-- Expected output: [some (-1), some 4, some 1, some 0, some 0, some 4, some (1 / 4)]
#eval scorerOccs.map (scorer.bodyVal ρ₁)

/-- Chapter 4, running example: every occurrence body is defined on `ρ₁`. -/
theorem scorer_adm₁ : scorer.AdmEnv ρ₁ := by
  unfold Program.AdmEnv
  decide +kernel

/-- Chapter 4, running example: on `ρ₁` collection reproduces `ρ₁` at every
defined address, `Z = (0,4)`, `Y = (0,4)`, `L = 1/4`; so `ρ₁` is a fixed point
of `Φ_P` and a model of `η₁`. Checked by kernel evaluation. -/
theorem scorer_models₁ : scorer.Models (inputOf ρ₁) ρ₁ :=
  ⟨scorer_adm₁, fun _ _ => rfl, by decide +kernel⟩

-- Expected output: [0, 4, 0, 4, 1 / 4]   (Z[0], Z[1], Y[0], Y[1], L[])
#eval [⟨.Z, (0 : Fin 2)⟩, ⟨.Z, (1 : Fin 2)⟩, ⟨.Y, (0 : Fin 2)⟩, ⟨.Y, (1 : Fin 2)⟩,
    ⟨.L, (0 : Fin 1)⟩].map
  (scorer.collect ρ₁ scorer_adm₁ : Addr scorerDecl → ℚ)

-- Expected output: none   (the body of s4 at `η₀`: recip (Y[1]) = recip 0)
#eval scorer.bodyVal ρ₀ ⟨(3 : Fin 4), (0 : Fin 1)⟩

/-- Chapter 4, running example: on `ρ₀` the occurrence `(s4, ())` is
undefined, so `ρ₀` is not admissible. -/
theorem scorer_s4_undefined₀ : scorer.bodyVal ρ₀ ⟨(3 : Fin 4), (0 : Fin 1)⟩ = none := by decide +kernel

/-- Chapter 4: a contribution is the value of a defined body. -/
theorem Program.contribution_eq [Semiring K] (P : Program d K) {ρ : Env d K}
    (h : P.AdmEnv ρ) {o : P.Occ} {v : K} (hv : P.bodyVal ρ o = some v) :
    P.contribution ρ h o = v :=
  Option.some_injective _ ((Option.some_get _).trans hv)

/-- Chapter 4: collection as a sum over the fibre `dst⁻¹(a)` as a finset. -/
theorem Program.collect_fibre [Semiring K] (P : Program d K) (ρ : Env d K)
    (h : P.AdmEnv ρ) (a : Addr d) :
    P.collect ρ h a = ∑ o ∈ Finset.univ.filter (fun o => P.dst o = a), P.contribution ρ h o := by
  simp only [Program.collect, pushforward, Finset.sum_filter]

/-- Chapter 4, running example: `Models(P, η₀) = ∅`. Any model of `η₀` has
`Z[1] = 2·0 + (-1)·0 + 0 = 0`, hence `Y[1] = relu 0 = 0`, hence the body of
`(s4, ())` is `recip 0`, undefined; so no environment extending `η₀` is even
admissible. -/
theorem scorer_no_model₀ : ¬ ∃ ρ, scorer.Models (inputOf ρ₀) ρ := by
  rintro ⟨ρ, h, agree, fixed⟩
  have eqn := (scorer.models_fixedpoint (inputOf ρ₀) ρ).mp ⟨h, agree, fixed⟩
  obtain ⟨h', -, eqs⟩ := eqn
  -- The two fibres used, computed by the kernel.
  have fibZ : Finset.univ.filter (fun o => scorer.dst o = ⟨.Z, (1 : Fin 2)⟩) =
      {⟨(0 : Fin 4), (1 : Fin 2)⟩, ⟨(1 : Fin 4), (1 : Fin 2)⟩} := by decide +kernel
  have fibY : Finset.univ.filter (fun o => scorer.dst o = ⟨.Y, (1 : Fin 2)⟩) =
      {⟨(2 : Fin 4), (1 : Fin 2)⟩} := by decide +kernel
  -- The body values involved, by unfolding the interpreter.
  have b01 : scorer.bodyVal ρ ⟨(0 : Fin 4), (1 : Fin 2)⟩ =
      some (∑ i : Fin 2, ρ ⟨.W, wIdx 1 i⟩ * ρ ⟨.X, i⟩) := by
    simp [Program.bodyVal, interpret, evalWith, sequenceFin, scorer, s1, Fin.sum_univ_two]
  have b11 : scorer.bodyVal ρ ⟨(1 : Fin 4), (1 : Fin 2)⟩ = some (ρ ⟨.B, (1 : Fin 2)⟩) := rfl
  have b21 : scorer.bodyVal ρ ⟨(2 : Fin 4), (1 : Fin 2)⟩ =
      some (max (ρ ⟨.Z, (1 : Fin 2)⟩) 0) := rfl
  have b30 : scorer.bodyVal ρ ⟨(3 : Fin 4), (0 : Fin 1)⟩ = recip (ρ ⟨.Y, (1 : Fin 2)⟩) := rfl
  -- Inputs agree with η₀: `X = (0, 0)` and `B[1] = 0`.
  have hX0 : ρ ⟨.X, (0 : Fin 2)⟩ = 0 := (agree _ rfl).trans (by decide +kernel)
  have hX1 : ρ ⟨.X, (1 : Fin 2)⟩ = 0 := (agree _ rfl).trans (by decide +kernel)
  have hB1 : ρ ⟨.B, (1 : Fin 2)⟩ = 0 := (agree _ rfl).trans (by decide +kernel)
  have z1 : ρ ⟨.Z, (1 : Fin 2)⟩ = 0 := by
    rw [eqs _ rfl, Program.collect_fibre, fibZ, Finset.sum_pair (by decide),
      Program.contribution_eq _ h' b01, Program.contribution_eq _ h' b11]
    simp only [Fin.sum_univ_two, hX0, hX1, hB1]
    simp
  have y1 : ρ ⟨.Y, (1 : Fin 2)⟩ = 0 := by
    rw [eqs _ rfl, Program.collect_fibre, fibY, Finset.sum_singleton,
      Program.contribution_eq _ h' b21, z1]
    simp
  have hs4 := h' ⟨(3 : Fin 4), (0 : Fin 1)⟩
  rw [b30, y1] at hs4
  simp [recip] at hs4

end PartC

/-! ## Part D. The machine (Chapter 5) -/

section PartD

variable {d : Decl} {K : Type}

/-- Chapter 5, `Read(E, ν)`: the read footprint of a body at a valuation, the
addresses it may read. A reduction reads the footprints of all its summands.
(Adapted from `footprint` in `leanncd/LeanNCD/Semantics/Interpret.lean`.) -/
def footprint : {Γ : Type} → Expr d K Γ → Γ → List (Addr d)
  | _, .lit _, _ => []
  | _, .read t ix, γ => [⟨t, ix γ⟩]
  | _, .add a b, γ => footprint a γ ++ footprint b γ
  | _, .mul a b, γ => footprint a γ ++ footprint b γ
  | _, .reduce n body, γ => (List.finRange n).flatMap (fun i => footprint body (γ, i))
  | _, .prim _ a, γ => footprint a γ

/-- Chapter 5, a running configuration `(σ, α, U)`: the published store
`σ : Addr ⇀ K`, the accumulators `α`, and the pending occurrences `U`, kept as
a list (it starts duplicate-free and only loses elements). Accumulators are not
readable; only published values are (CONVENTIONS fact 7). (Production:
`Program.Running`, with pending as a `Finset` per defined tensor and
accumulators only on defined tensors.) -/
structure Config (P : Program d K) where
  /-- The published store `σ`; published values are immutable. -/
  published : Addr d → Option K
  /-- The accumulators `α`. -/
  acc : Addr d → K
  /-- The pending occurrences `U`. -/
  pending : List P.Occ

/-- Chapter 5, the outcomes of the machine: still running, terminal failure
`Failed(o, σ, α, U)`, blocked (neither success nor failure), or complete with
the final environment. -/
inductive Outcome (P : Program d K)
  /-- A running configuration. -/
  | running (c : Config P)
  /-- Terminal failure at occurrence `o` (rule UNDEFINED). -/
  | failed (o : P.Occ) (c : Config P)
  /-- No rule applies and the run is not complete. -/
  | blocked (c : Config P)
  /-- Successful completion `Conf ⇓ ρ`. -/
  | complete (ρ : Env d K)

namespace Program

variable (P : Program d K)

/-- Chapter 5: an occurrence is ready when its whole footprint is published. -/
def ready (c : Config P) (o : P.Occ) : Bool :=
  (footprint (P.stmts.get o.1).body o.2).all (fun a => (c.published a).isSome)

/-- Chapter 5: evaluate an occurrence's body against the published store.
Reads of unpublished addresses yield `none`, but every rule checks `ready`
first, so on a ready occurrence `none` means a primitive was undefined.
(Production: `evalReady`, which folds the readiness check into a
`ReadyResult`.) -/
def evalReady [Semiring K] (c : Config P) (o : P.Occ) : Option K :=
  evalWith c.published (P.stmts.get o.1).body o.2

/-- Chapter 5, the effect of CONTRIBUTE: add `v` to the accumulator of
`dst o` and remove `o` from the pending list.
(Production: `Program.consume`.) -/
def contribute [Semiring K] (c : Config P) (o : P.Occ) (v : K) : Config P where
  published := c.published
  acc := fun a => c.acc a + if P.dst o = a then v else 0
  pending := c.pending.erase o

/-- Chapter 5, the effect of PUBLISH: freeze the accumulator of `a` into the
store. (Production: `Program.publish`.) -/
def publish (c : Config P) (a : Addr d) : Config P where
  published := fun b => if b = a then some (c.acc a) else c.published b
  acc := c.acc
  pending := c.pending

/-- Chapter 5, `Init(P, η)`: inputs published, accumulators `0`, every
occurrence pending. Only the input coordinates of `η` are read. -/
def initial [Zero K] (η : Env d K) : Config P where
  published := fun a => if P.input a.1 then some (η a) else none
  acc := fun _ => 0
  pending := (List.finRange P.stmts.length).flatMap
    (fun i => (List.finRange (P.stmts.get i).n).map (fun j => ⟨i, j⟩))

/-- Chapter 5: the initial pending list has no duplicates, so it represents
the set `U = O_P` (each occurrence contributes exactly once). -/
theorem initial_nodup [Zero K] (η : Env d K) : (P.initial η).pending.Nodup := by
  simp only [initial]
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => (List.nodup_finRange _).map (fun _ _ h => by simpa using h), ?_⟩
  refine (List.nodup_finRange _).pairwise_of_forall_ne (fun i _ j _ hij => ?_)
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro _ ⟨x, _, rfl⟩ ⟨y, _, hy⟩
  exact hij (congrArg Sigma.fst hy).symm

/-- Chapter 5, the three rules (CONVENTIONS fact 6), as a relation from a
running configuration to an outcome. CONTRIBUTE needs a pending, ready
occurrence with a defined body; PUBLISH needs an unpublished defined address
with no pending writer; UNDEFINED is terminal.
(Adapted from `Program.Step` in `leanncd/LeanNCD/Semantics/Machine.lean`.) -/
inductive Step [Semiring K] : Config P → Outcome P → Prop
  /-- CONTRIBUTE. -/
  | contribute (c : Config P) (o : P.Occ) (v : K) (pend : o ∈ c.pending)
      (rdy : P.ready c o = true) (ev : P.evalReady c o = some v) :
      Step c (.running (P.contribute c o v))
  /-- PUBLISH. -/
  | publish (c : Config P) (a : Addr d) (defined : P.input a.1 = false)
      (unpublished : c.published a = none) (finished : ∀ o ∈ c.pending, P.dst o ≠ a) :
      Step c (.running (P.publish c a))
  /-- UNDEFINED. -/
  | undefined (c : Config P) (o : P.Occ) (pend : o ∈ c.pending)
      (rdy : P.ready c o = true) (ev : P.evalReady c o = none) :
      Step c (.failed o c)

/-- Chapter 5, the termination measure
`μ(σ, α, U) = |U| + |Addr_Def \ dom σ|`.
(Production: `Program.measure` in `Measure.lean`.) -/
def measure (c : Config P) : Nat :=
  c.pending.length +
    (Finset.univ.filter (fun a : Addr d => P.input a.1 = false ∧ c.published a = none)).card

/-- Chapter 5: every running step strictly decreases the measure. CONTRIBUTE
removes a pending occurrence; PUBLISH removes an unpublished defined address.
This file proves only this one-step decrease; the chain-level consequence
(no infinite run) is left as an exercise, and production proves it as
`no_infinite_chain`.
(Production: `running_step_measure` and `step_decreases` in `Measure.lean`.) -/
theorem measure_decreases [Semiring K] {c c' : Config P}
    (h : P.Step c (.running c')) : P.measure c' < P.measure c := by
  cases h with
  | contribute o v pend _ _ =>
    have h1 := List.length_erase_of_mem pend
    have h2 := List.length_pos_of_mem pend
    simp only [measure, contribute]
    omega
  | publish a hdef hun _ =>
    simp only [measure, publish]
    apply Nat.add_lt_add_left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨a, by simp [hdef, hun], by simp⟩
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      by_cases hba : b = a
      · subst hba
        simp at hb
      · simpa [hba] using hb

/-! ### An executable scheduler -/

/-- Chapter 5: all addresses of the signature, in a fixed executable order. -/
def addrs : List (Addr d) :=
  d.tensors.flatMap (fun t => (List.finRange (d.size t)).map (fun p => ⟨t, p⟩))

/-- Chapter 5: the Boolean side conditions of PUBLISH. -/
def publishable (c : Config P) (a : Addr d) : Bool :=
  !P.input a.1 && (c.published a).isNone && c.pending.all (fun o => P.dst o != a)

/-- Chapter 5, a deterministic scheduler: take the first ready pending
occurrence (CONTRIBUTE, or UNDEFINED if its body is undefined); otherwise
publish the first publishable address; otherwise stop, complete if nothing is
pending and everything is published, blocked if not. Out of fuel returns
`.running`. This is one strategy inside the nondeterministic `Step` relation,
which is the specification. -/
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

/-- Chapter 5: run with fuel `μ + 1`. Every scheduler step is a `Step`, so by
`measure_decreases` this fuel suffices; that sufficiency is checked here only on
the two running-example runs (`scorer_run₁`, `scorer_run₀`), not proved in
general. -/
def runToEnd [Semiring K] (c : Config P) : Outcome P := P.run (P.measure c + 1) c

/-- Chapter 5: the reflexive-transitive closure of running steps
(`Conf →* Conf'`). (Production: `Program.Reaches`.) -/
inductive Reaches [Semiring K] : Config P → Config P → Prop
  /-- Zero steps. -/
  | refl (c : Config P) : Reaches c c
  /-- One running step, then more. -/
  | step {c c' c'' : Config P} : P.Step c (.running c') → Reaches c' c'' → Reaches c c''

/-- Chapter 5: `addrs` lists every address. -/
theorem mem_addrs (a : Addr d) : a ∈ addrs (d := d) := by
  simp only [addrs, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨a.1, d.tensors_complete _, a.2, rfl⟩

/-- Chapter 5, scheduler soundness for success: if `run` completes with `ρ`,
then `Step` chains from `c` to a configuration with nothing pending whose
published store is exactly `ρ` (`Conf ⇓ ρ`). The scheduler is one strategy of
the `Step` specification. -/
theorem run_sound [Semiring K] (ρ : Env d K) :
    ∀ (fuel : Nat) (c : Config P), P.run fuel c = .complete ρ →
      ∃ c', P.Reaches c c' ∧ c'.pending = [] ∧ ∀ a, c'.published a = some (ρ a)
  | 0, c, h => by simp [run] at h
  | fuel + 1, c, h => by
    unfold run at h
    split at h
    · rename_i o ho
      split at h
      · rename_i v hv
        obtain ⟨c', r, hp, hpub⟩ := run_sound ρ fuel _ h
        exact ⟨c', .step (.contribute c o v (List.mem_of_find?_eq_some ho)
          (List.find?_some ho) hv) r, hp, hpub⟩
      · cases h
    · split at h
      · rename_i a ha
        have hp := List.find?_some ha
        simp only [publishable, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none,
          List.all_eq_true, bne_iff_ne, ne_eq] at hp
        obtain ⟨c', r, hp', hpub⟩ := run_sound ρ fuel _ h
        exact ⟨c', .step (.publish c a hp.1.1 hp.1.2 hp.2) r, hp', hpub⟩
      · split at h
        · rename_i hc
          injection h with h
          subst h
          simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hc
          refine ⟨c, .refl c, hc.1, fun a => ?_⟩
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hc.2 a (mem_addrs a))
          simp [hv]
        · cases h

/-- Chapter 5, scheduler soundness for failure: if `run` fails at `o` in
configuration `c'`, then `Step` chains from `c` to `c'` and UNDEFINED applies
there. With Theorem 26.3 of the specification this shows there is no model. -/
theorem run_sound_failed [Semiring K] (o : P.Occ) (c' : Config P) :
    ∀ (fuel : Nat) (c : Config P), P.run fuel c = .failed o c' →
      P.Reaches c c' ∧ P.Step c' (.failed o c')
  | 0, c, h => by simp [run] at h
  | fuel + 1, c, h => by
    unfold run at h
    split at h
    · rename_i o' ho
      split at h
      · rename_i v hv
        obtain ⟨r, st⟩ := run_sound_failed o c' fuel _ h
        exact ⟨.step (.contribute c o' v (List.mem_of_find?_eq_some ho)
          (List.find?_some ho) hv) r, st⟩
      · rename_i hv
        injection h with h1 h2
        subst h1 h2
        exact ⟨.refl c, .undefined c o' (List.mem_of_find?_eq_some ho) (List.find?_some ho) hv⟩
    · split at h
      · rename_i a ha
        have hp := List.find?_some ha
        simp only [publishable, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none,
          List.all_eq_true, bne_iff_ne, ne_eq] at hp
        obtain ⟨r, st⟩ := run_sound_failed o c' fuel _ h
        exact ⟨.step (.publish c a hp.1.1 hp.1.2 hp.2) r, st⟩
      · split at h <;> cases h

/-- Chapter 5: the values of a complete outcome at the given addresses. -/
def completeValues (as : List (Addr d)) : Outcome P → Option (List K)
  | .complete ρ => some (as.map ρ)
  | _ => none

/-- Chapter 5: the occurrence at which an outcome failed, if it failed. -/
def failedAt : Outcome P → Option P.Occ
  | .failed o _ => some o
  | _ => none

/-- Chapter 5: a human-readable summary of an outcome, listing the defined
addresses (`_` marks an unpublished one). -/
def describe [ToString K] (name : d.T → String) : Outcome P → String :=
  let cells (f : Addr d → Option K) : String :=
    ", ".intercalate (((addrs (d := d)).filter (fun a => !P.input a.1)).map fun a =>
      s!"{name a.1}[{a.2.val}]=" ++ match f a with | some v => toString v | none => "_")
  fun
  | .running c => "out of fuel: " ++ cells c.published
  | .failed o c => s!"failed at (s{o.1.val + 1}, {o.2.val}); published: " ++ cells c.published
  | .blocked c => "blocked: " ++ cells c.published
  | .complete ρ => "complete: " ++ cells (fun a => some (ρ a))

end Program

/-- Chapter 5, display names of the `Scorer` tensors. -/
def ScorerTensor.name : ScorerTensor → String
  | .X => "X" | .W => "W" | .B => "B" | .Z => "Z" | .Y => "Y" | .L => "L"

-- Expected output: complete: Z[0]=0, Z[1]=4, Y[0]=0, Y[1]=4, L[0]=1/4
#eval scorer.describe ScorerTensor.name (scorer.runToEnd (scorer.initial ρ₁))

-- Expected output: failed at (s4, 0); published: Z[0]=1, Z[1]=0, Y[0]=1, Y[1]=0, L[0]=_
#eval scorer.describe ScorerTensor.name (scorer.runToEnd (scorer.initial ρ₀))

/-- Chapter 5, running example checked in the kernel: from `Init(P, η₁)` the
scheduler completes with `Z = (0,4)`, `Y = (0,4)`, `L = 1/4`, the model
`ρ₁` of `scorer_models₁`. -/
theorem scorer_run₁ :
    scorer.completeValues
      [⟨.Z, (0 : Fin 2)⟩, ⟨.Z, (1 : Fin 2)⟩, ⟨.Y, (0 : Fin 2)⟩, ⟨.Y, (1 : Fin 2)⟩,
        ⟨.L, (0 : Fin 1)⟩] (scorer.runToEnd (scorer.initial ρ₁)) =
      some [0, 4, 0, 4, 1 / 4] := by
  decide +kernel

/-- Chapter 5, running example checked in the kernel: from `Init(P, η₀)` the
scheduler takes UNDEFINED at the occurrence `(s4, ())`. -/
theorem scorer_run₀ :
    scorer.failedAt (scorer.runToEnd (scorer.initial ρ₀)) = some ⟨(3 : Fin 4), (0 : Fin 1)⟩ := by
  decide +kernel

end PartD

/-! ## Axiom audit

Only `propext`, `Classical.choice` and `Quot.sound` may appear. The kernel
checks (`decide +kernel`) add no axiom; nothing here uses `native_decide`. -/

#print axioms transpose
#print axioms WSpan.lin_comp
#print axioms batch_lax
#print axioms batch_lax_strict
#print axioms Program.models_fixedpoint
#print axioms scorer_models₁
#print axioms scorer_no_model₀
#print axioms Program.measure_decreases
#print axioms Program.initial_nodup
#print axioms Program.run_sound
#print axioms Program.run_sound_failed
#print axioms scorer_run₁
#print axioms scorer_run₀

end Course
