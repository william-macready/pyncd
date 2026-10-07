import LeanNCD.Semantics.Collection
import LeanNCD.Semantics.Interpret

namespace LeanNCD.Semantics

def coordDecidableEq : (sh : Shape) → DecidableEq (Coord sh)
  | [] => inferInstance
  | _ :: sh => @instDecidableEqProd _ _ inferInstance (coordDecidableEq sh)

/- Structural admission is encoded in the types, not a runtime/source checker.
   Statement identifiers are local to a defined target; duplicate bodies keep
   distinct identifiers. Valuations are admitted before body demand. -/
structure Program (K : S → Type) (σ : Declarations S) (r : Registry K) where
  tensors : Fintype σ.Tensor
  input : σ.Tensor → Bool
  output : σ.Tensor → Bool
  output_defined : ∀ t, output t = true → input t = false
  statements : {t : σ.Tensor // input t = false} → Nat
  valuations : (t : {t : σ.Tensor // input t = false}) → Fin (statements t) → Nat
  guard : (t : {t : σ.Tensor // input t = false}) →
    (s : Fin (statements t)) → Fin (valuations t s) → Bool
  destination : (t : {t : σ.Tensor // input t = false}) →
    (s : Fin (statements t)) → {v : Fin (valuations t s) // guard t s v = true} →
    Coord (σ.signature t.val).axes
  body : (t : {t : σ.Tensor // input t = false}) →
    (s : Fin (statements t)) →
    Expr K σ r {v : Fin (valuations t s) // guard t s v = true}
      (.scalar (σ.signature t.val).sort)

namespace Program

variable {K : S → Type} {σ : Declarations S} {r : Registry K}

abbrev Defined (P : Program K σ r) := {t : σ.Tensor // P.input t = false}
abbrev Occurrence (P : Program K σ r) (t : P.Defined) :=
  (s : Fin (P.statements t)) × {v : Fin (P.valuations t s) // P.guard t s v = true}

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

variable (P : Program K σ r) (ops : (s : S) → ScalarOps (K s))
variable [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]

def collect (ρ : Store K σ) (h : P.AdmEnv ops ρ) (t : P.Defined) :
    Coord (σ.signature t.val).axes → K (σ.signature t.val).sort :=
  letI := coordDecidableEq (σ.signature t.val).axes
  pushforward (fun o : P.Occurrence t => P.destination t o.1 o.2)
    (P.contribution ops ρ h t)

theorem collect_grouped (ρ : Store K σ) (h : P.AdmEnv ops ρ) (t : P.Defined)
    (p : Coord (σ.signature t.val).axes) :
    P.collect ops ρ h t p =
      ∑ s, letI := coordDecidableEq (σ.signature t.val).axes
        pushforward (P.destination t s)
          (fun v => P.contribution ops ρ h t ⟨s, v⟩) p := by
  letI := coordDecidableEq (σ.signature t.val).axes
  exact pushforward_grouped _ _ _

def relabeledCollect {O : P.Defined → Type} [∀ t, Fintype (O t)]
    (e : ∀ t, O t ≃ P.Occurrence t) (ρ : Store K σ) (h : P.AdmEnv ops ρ)
    (t : P.Defined) : Coord (σ.signature t.val).axes → K (σ.signature t.val).sort :=
  letI := coordDecidableEq (σ.signature t.val).axes
  pushforward (fun o => P.destination t (e t o).1 (e t o).2)
    (fun o => P.contribution ops ρ h t (e t o))

theorem collect_relabel {O : P.Defined → Type} [∀ t, Fintype (O t)]
    (e : ∀ t, O t ≃ P.Occurrence t) (ρ : Store K σ) (h : P.AdmEnv ops ρ)
    (t : P.Defined) :
    P.relabeledCollect ops e ρ h t = P.collect ops ρ h t := by
  letI := coordDecidableEq (σ.signature t.val).axes
  exact pushforward_relabel (e t)
    (fun o : P.Occurrence t => P.destination t o.1 o.2)
    (P.contribution ops ρ h t)

omit [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem admEnv_relabel {O : P.Defined → Type}
    (e : ∀ t, O t ≃ P.Occurrence t) (ρ : Store K σ) :
    (∀ t o, (P.outcome ops ρ t (e t o)).isSome = true) ↔ P.AdmEnv ops ρ := by
  constructor
  · intro h t o
    simpa using h t ((e t).symm o)
  · intro h t o
    exact h t (e t o)

end Program
end LeanNCD.Semantics
