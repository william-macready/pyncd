import LeanNCD.Semantics.Types

namespace LeanNCD.Semantics.Program.Plan.ScanHistory

abbrev State (V : Type) (d : Nat) := Fin d → V

variable {V : Type} {d : Nat}

/-- The independent full-history specification, before any plan or memory model. -/
def history [Add V] (F : State V d → State V d) (X Z : State V d) :
    Nat → State V d
  | 0 => fun i => X i + Z i
  | n + 1 => fun i => X i + F (history F X Z n) i

theorem history_zero [Add V] (F : State V d → State V d) (X Z : State V d) :
    history F X Z 0 = fun i => X i + Z i := rfl

theorem history_succ [Add V] (F : State V d → State V d) (X Z : State V d)
    (n : Nat) : history F X Z (n + 1) = fun i => X i + F (history F X Z n) i := rfl

/-- Any history satisfying the two recurrence equations agrees slice by slice. -/
theorem history_unique [Add V] (F : State V d → State V d) (X Z : State V d)
    (H : Nat → State V d) (base : H 0 = fun i => X i + Z i)
    (step : ∀ n, H (n + 1) = fun i => X i + F (H n) i) :
    H = history F X Z := by
  funext n
  induction n with
  | zero => exact base
  | succ n ih => rw [step n, history_succ, ih]

theorem state_zero_unique (a b : State V 0) : a = b := by
  funext i
  exact Fin.elim0 i

#print axioms history_zero
#print axioms history_succ
#print axioms history_unique
#print axioms state_zero_unique

end LeanNCD.Semantics.Program.Plan.ScanHistory
