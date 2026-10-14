import LeanNCD.Semantics.Plan.ScanHistory.Core

namespace LeanNCD.Semantics.Program.Plan.ScanHistory

theorem footprint_cast {K : S → Type} {σ : Declarations S} {r : Registry K}
    {Γ : Type} {τ τ' : Ty S} (h : τ = τ') (e : Expr K σ r Γ τ) (γ : Γ) :
    footprint (cast (congrArg (Expr K σ r Γ) h) e) γ = footprint e γ := by
  cases h
  rfl

variable {V : Type} {d N : Nat} {r : Registry (Carrier V)}

theorem arrayExpr_footprint {Γ : Type} {σ : Declarations Unit}
    (f : RegisteredF r d) (arg : Expr (Carrier V) σ r Γ (stateTy d)) (γ : Γ) :
    footprint (f.arrayExpr arg) γ = footprint arg γ := by
  unfold RegisteredF.arrayExpr
  rw [footprint_cast f.output_eq]
  simp only [footprint]
  have argFootprint (j : Fin (r.arity f.op)) :
      footprint (cast (congrArg (Expr (Carrier V) σ r Γ) (f.input_eq j).symm) arg) γ =
        footprint arg γ :=
    footprint_cast (f.input_eq j).symm arg γ
  simp_rw [argFootprint]
  have len : (List.finRange (r.arity f.op)).length = 1 := by simpa using f.unary
  obtain ⟨j, hj⟩ := List.length_eq_one_iff.mp len
  rw [hj]
  simp

theorem recurrenceBody_footprint {Γ : Type} (f : RegisteredF r d)
    (i : Γ → Fin d) (l : Γ → Fin (N + 1)) (γ : Γ) :
    footprint (recurrenceBody f i l) γ =
      (List.finRange d).map fun j => historyAddress d N j (l γ) := by
  unfold recurrenceBody
  simp only [footprint]
  exact (arrayExpr_footprint f (priorSlice l) γ).trans (priorSlice_footprint l γ)

#print axioms footprint_cast
#print axioms arrayExpr_footprint
#print axioms recurrenceBody_footprint

end LeanNCD.Semantics.Program.Plan.ScanHistory
