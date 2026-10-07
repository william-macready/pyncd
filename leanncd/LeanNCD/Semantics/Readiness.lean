import LeanNCD.Semantics.Interpret

namespace LeanNCD.Semantics

variable {S : Type} {K : S → Type} {σ : Declarations S} {r : Registry K}
  {Γ : Type} {τ : Ty S}

theorem evalWith_stable (ops : (s : S) → ScalarOps (K s))
    (e : Expr K σ r Γ τ) (γ : Γ) (p q : PartialStore K σ)
    (agree : ∀ a ∈ footprint e γ, p a = q a) :
    evalWith ops p e γ = evalWith ops q e γ := by
  induction e with
  | lit x => rfl
  | read t access =>
      cases h : access.resolved γ with
      | «at» c =>
          simpa only [evalWith, h] using agree ⟨t, c⟩ (by simp [footprint, h])
      | const c => simp only [evalWith, h]
  | iverson pred => rfl
  | binary b l e ihl ihe =>
      simp only [evalWith]
      rw [ihl γ (fun a ha => agree a (List.mem_append_left _ ha)),
        ihe γ (fun a ha => agree a (List.mem_append_right _ ha))]
  | reduce n body ih =>
      simp only [evalWith]
      congr 1
      apply List.map_congr_left
      intro i hi
      apply ih (γ, i)
      intro a ha
      exact agree a (List.mem_flatMap.mpr ⟨i, hi, ha⟩)
  | tab sh layout body ih =>
      have hb : (fun i => evalWith ops p body (γ, layout.enumerate i)) =
          (fun i => evalWith ops q body (γ, layout.enumerate i)) := by
        funext i
        apply ih (γ, layout.enumerate i)
        intro a ha
        exact agree a (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ha⟩)
      simp only [evalWith, hb]
  | «at» e index ih =>
      simp only [evalWith]
      rw [ih γ agree]
  | prim f args ih =>
      have hb : (fun i => evalWith ops p (args i) γ) =
          (fun i => evalWith ops q (args i) γ) := by
        funext i
        apply ih i γ
        intro a ha
        exact agree a (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ha⟩)
      simp only [evalWith, hb]

theorem interpret_stable (ops : (s : S) → ScalarOps (K s))
    (e : Expr K σ r Γ τ) (γ : Γ) (p q : Store K σ)
    (agree : ∀ a ∈ footprint e γ, p a = q a) :
    interpret ops p e γ = interpret ops q e γ :=
  evalWith_stable ops e γ _ _ (fun a ha => congrArg some (agree a ha))

def Ready (p : PartialStore K σ) (e : Expr K σ r Γ τ) (γ : Γ) : Prop :=
  ∀ a ∈ footprint e γ, (p a).isSome = true

def checkReads (p : PartialStore K σ) : List (Address σ) → Bool
  | [] => true
  | a :: as => (p a).isSome && checkReads p as

inductive ReadyResult (V : Type)
  | notReady
  | evaluated : Option V → ReadyResult V

def evalReady (ops : (s : S) → ScalarOps (K s)) (p : PartialStore K σ)
    (e : Expr K σ r Γ τ) (γ : Γ) : ReadyResult (Value K τ) :=
  if checkReads p (footprint e γ) then .evaluated (evalWith ops p e γ) else .notReady

theorem checkReads_iff (p : PartialStore K σ) (as : List (Address σ)) :
    checkReads p as = true ↔ ∀ a ∈ as, (p a).isSome = true := by
  induction as with
  | nil => simp [checkReads]
  | cons a as ih => simp [checkReads, ih]

theorem ready_consistent (ops : (s : S) → ScalarOps (K s))
    (e : Expr K σ r Γ τ) (γ : Γ) (p : PartialStore K σ) (ρ : Store K σ)
    (extension : ∀ a ∈ footprint e γ, p a = some (ρ a)) :
    evalReady ops p e γ = .evaluated (interpret ops ρ e γ) := by
  have ready : checkReads p (footprint e γ) = true :=
    (checkReads_iff p _).mpr (fun a ha => by simp [extension a ha])
  simp only [evalReady, ready, ↓reduceIte]
  exact congrArg ReadyResult.evaluated (evalWith_stable ops e γ p _ extension)

theorem notReady_iff (ops : (s : S) → ScalarOps (K s))
    (e : Expr K σ r Γ τ) (γ : Γ) (p : PartialStore K σ) :
    evalReady ops p e γ = .notReady ↔ ¬ Ready p e γ := by
  simp [evalReady, Ready, ← checkReads_iff]

#print axioms evalWith_stable
#print axioms interpret_stable
#print axioms ready_consistent

end LeanNCD.Semantics
