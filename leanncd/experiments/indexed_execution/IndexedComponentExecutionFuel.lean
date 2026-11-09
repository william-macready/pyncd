import IndexedCompositionValidated

namespace IndexedComponentExecution

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedOpenComposition

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]

theorem stepFuel_add_of_not_exhausted (steps : List (Step σ)) (fuel extra : Nat)
    (state : State σ)
    (terminal : ∀ endpoint, (stepFuel steps fuel state).outcome ≠ .exhausted endpoint) :
    stepFuel steps (fuel + extra) state = stepFuel steps fuel state := by
  induction fuel generalizing state with
  | zero =>
      rw [stepFuel] at terminal
      conv_lhs => rw [stepFuel]
      conv_rhs => rw [stepFuel]
      by_cases hc : complete steps state = true
      · simp [hc]
      · simp only [hc, ↓reduceIte] at terminal ⊢
        cases hs : steps.find? (enabled state) with
        | none => simp [hs]
        | some step => simp [hs] at terminal
  | succ fuel ih =>
      rw [stepFuel] at terminal
      conv_lhs => rw [stepFuel]
      conv_rhs => rw [stepFuel]
      by_cases hc : complete steps state = true
      · simp [hc]
      · simp only [hc, ↓reduceIte, Nat.succ_add] at terminal ⊢
        cases hs : steps.find? (enabled state) with
        | none => simp [hs]
        | some step =>
            cases step with
            | write w =>
                simp only [hs]
                cases he : evalReady RationalReference.ops state.available w.body () with
                | notReady => rfl
                | evaluated result =>
                    cases result with
                    | none => rfl
                    | some value =>
                        simp only
                        rw [ih _ (by simpa [hs, he] using terminal)]
            | collect a caps =>
                simp only [hs]
                cases hv : caps.mapM (producedValue state) with
                | none => rfl
                | some values =>
                    simp only
                    rw [ih _ (by simpa [hs, hv] using terminal)]

theorem stepFuel_eq_of_enough (steps : List (Step σ)) (small large : Nat)
    (state : State σ) (enough : Correspondence.remaining steps state < small)
    (le : small ≤ large) :
    stepFuel steps large state = stepFuel steps small state := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  exact stepFuel_add_of_not_exhausted steps small extra state
    (Correspondence.stepFuel_not_exhausted steps small state enough)

theorem checked_eq_stepFuel
    {P : Program RationalReference.Carrier σ RationalReference.registry}
    {schedule : Executor.Schedule P} {contract : Contract σ} {fragment : Fragment σ}
    {graph : Closed σ} (M : SourceContractMatch P schedule contract fragment graph)
    (η : P.Input) :
    runChecked contract fragment η.val =
      stepFuel graph.steps (graph.steps.length + 1) (initial η.val) := by
  simp only [runChecked, M.close_ok]
  unfold execute
  have valid : graph.contract.tensors.find?
      (fun t => (η.val t).isSome != graph.contract.input t) = none := by
    apply List.find?_eq_none.mpr
    intro t _
    have hc := (close_success_canonical M.close_ok).1
    have ht := η.property t
    change (η.val t).isSome = P.input t at ht
    simp [hc, M.input_roles, ht]
  simp [valid]

end IndexedComponentExecution
