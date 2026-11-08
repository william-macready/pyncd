import IndexedComponentCompositionScope
import LeanNCD.Semantics.Models

namespace IndexedWitness

open LeanNCD.Semantics
open LeanNCD
open IndexedComponentComposition

/-- A port-only, whole-tensor interface; even ports with no coordinates remain indexed. -/
structure WholeInterface where
  Tensor : Type
  uid : Tensor → UID
  unique : Function.Injective uid
  signature : Tensor → Signature Unit
  ports : List Tensor
  ports_nodup : ports.Nodup
  ports_complete : ∀ t, t ∈ ports

abbrev WholeInterface.Env (X : WholeInterface) :=
  (t : X.Tensor) → Coord (X.signature t).axes →
    RationalReference.Carrier (X.signature t).sort

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]

noncomputable def roleInterface (role : σ.Tensor → Bool) : WholeInterface where
  Tensor := {t : σ.Tensor // role t = true}
  uid := fun t => σ.uid t.val
  unique := by
    intro a b h
    exact Subtype.ext (σ.unique h)
  signature := fun t => σ.signature t.val
  ports := Finset.univ.toList
  ports_nodup := Finset.nodup_toList _
  ports_complete := by intro t; simp

noncomputable def inputInterface (A : MatchedComponent σ) : WholeInterface :=
  roleInterface A.program.input

noncomputable def outputInterface (A : MatchedComponent σ) : WholeInterface :=
  roleInterface A.program.output

def inputEnv (A : MatchedComponent σ) (η : A.program.Input) :
    (inputInterface A).Env := by
  intro t
  exact (η.val t.val).get (by simpa [t.property] using η.property t.val)

def envInput (A : MatchedComponent σ) (x : (inputInterface A).Env) :
    A.program.Input :=
  ⟨fun t => if h : A.program.input t = true then some (x ⟨t, h⟩) else none,
    by intro t; by_cases h : A.program.input t = true <;> simp [h]⟩

theorem inputEnv_envInput (A : MatchedComponent σ)
    (x : (inputInterface A).Env) : inputEnv A (envInput A x) = x := by
  funext t
  change (inputEnv A (envInput A x)) t = x t
  unfold inputEnv
  have he : (⟨t.val, t.property⟩ : {t : σ.Tensor // A.program.input t = true}) = t :=
    Subtype.ext rfl
  simp only [envInput, dif_pos t.property, Option.get_some]
  cases he
  rfl

theorem envInput_inputEnv (A : MatchedComponent σ)
    (η : A.program.Input) : envInput A (inputEnv A η) = η := by
  apply Subtype.ext
  funext t
  by_cases h : A.program.input t = true
  · have hs : ∃ f, η.val t = some f := by
      have hv := η.property t
      cases ht : η.val t with
      | none => simp [ht, h] at hv
      | some f => exact ⟨f, rfl⟩
    obtain ⟨f, hf⟩ := hs
    simp [envInput, h, inputEnv, hf]
  · have hn : η.val t = none := by
      have hv := η.property t
      cases hs : η.val t with
      | none => rfl
      | some f => simp [hs, h] at hv
    simp [envInput, h, hn]

def inputEquiv (A : MatchedComponent σ) :
    (inputInterface A).Env ≃ A.program.Input where
  toFun := envInput A
  invFun := inputEnv A
  left_inv := inputEnv_envInput A
  right_inv := envInput_inputEnv A

def outputEquiv (A : MatchedComponent σ) :
    (outputInterface A).Env ≃ A.program.Output :=
  Equiv.refl _

end IndexedWitness
