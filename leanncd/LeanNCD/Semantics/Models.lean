import LeanNCD.Semantics.Program

namespace LeanNCD.Semantics.Program

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable (P : Program K σ r)

abbrev InputBinding := (t : σ.Tensor) →
  Option (Coord (σ.signature t).axes → K (σ.signature t).sort)

/- Presence is a tensor-level fact even when its coordinate type is empty. -/
def ValidInput (η : InputBinding (K := K) (σ := σ)) : Prop :=
  ∀ t, (η t).isSome = P.input t

abbrev Input := {η : InputBinding (K := K) (σ := σ) // P.ValidInput η}

def InputAgreement (η : P.Input) (ρ : Store K σ) : Prop :=
  ∀ t f, η.val t = some f → ∀ p, ρ ⟨t, p⟩ = f p

variable (ops : (s : S) → ScalarOps (K s))
variable [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]

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
      ∃ h : P.AdmEnv ops ρ, P.equationOperator ops ρ h = ρ := by
  constructor
  · rintro ⟨h, agree, equations⟩
    refine ⟨agree, h, ?_⟩
    funext a
    dsimp [equationOperator]
    split_ifs with hi
    · rfl
    · exact (equations ⟨a.1, Bool.eq_false_iff.mpr hi⟩ a.2).symm
  · rintro ⟨agree, h, fixed⟩
    refine ⟨h, agree, ?_⟩
    intro t p
    have cell := congrFun fixed ⟨t.val, p⟩
    simpa [equationOperator, t.property] using cell.symm

def RelabeledModels {O : P.Defined → Type} [∀ t, Fintype (O t)]
    (e : ∀ t, O t ≃ P.Occurrence t) (η : P.Input) (ρ : Store K σ) : Prop :=
  ∃ h : (∀ t o, (P.outcome ops ρ t (e t o)).isSome = true),
    P.InputAgreement η ρ ∧ ∀ t p, ρ ⟨t.val, p⟩ =
      P.relabeledCollect ops e ρ ((P.admEnv_relabel ops e ρ).mp h) t p

theorem models_relabel {O : P.Defined → Type} [∀ t, Fintype (O t)]
    (e : ∀ t, O t ≃ P.Occurrence t) (η : P.Input) (ρ : Store K σ) :
    P.RelabeledModels ops e η ρ ↔ P.Models ops η ρ := by
  constructor
  · rintro ⟨h, agree, equations⟩
    refine ⟨(P.admEnv_relabel ops e ρ).mp h, agree, ?_⟩
    intro t p
    simpa only [collect_relabel] using equations t p
  · rintro ⟨h, agree, equations⟩
    refine ⟨(P.admEnv_relabel ops e ρ).mpr h, agree, ?_⟩
    intro t p
    simpa only [collect_relabel] using equations t p

def GroupedModels (η : P.Input) (ρ : Store K σ) : Prop :=
  ∃ h : P.AdmEnv ops ρ, P.InputAgreement η ρ ∧ ∀ t p, ρ ⟨t.val, p⟩ =
    ∑ s, letI := coordDecidableEq (σ.signature t.val).axes
      pushforward (P.destination t s)
        (fun v => P.contribution ops ρ h t ⟨s, v⟩) p

theorem models_grouped (η : P.Input) (ρ : Store K σ) :
    P.GroupedModels ops η ρ ↔ P.Models ops η ρ := by
  simp only [GroupedModels, Models, collect_grouped]

def AdmInput (η : P.Input) : Prop := ∃! ρ, P.Models ops η ρ

abbrev Output := (t : {t : σ.Tensor // P.output t = true}) →
  Coord (σ.signature t.val).axes → K (σ.signature t.val).sort

def outputProjection (ρ : Store K σ) : P.Output := fun t p => ρ ⟨t.val, p⟩

noncomputable def denotation (η : P.Input) (h : P.AdmInput ops η) : P.Output :=
  P.outputProjection (Classical.choose h)

theorem denotation_of_model (η : P.Input) (h : P.AdmInput ops η)
    (ρ : Store K σ) (model : P.Models ops η ρ) :
    P.denotation ops η h = P.outputProjection ρ := by
  have unique := Classical.choose_spec h
  have eq := unique.2 ρ model
  exact congrArg P.outputProjection eq.symm

end LeanNCD.Semantics.Program
