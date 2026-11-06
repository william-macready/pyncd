import IndexedOpenComposition

namespace IndexedOpenComposition.Correspondence

open LeanNCD.Semantics
open LeanNCD.Semantics.Program

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]

def unfinished (state : State σ) : Step σ → Bool
  | .write w => (producedValue state w.capability).isNone
  | .collect a _ => (state.available a).isNone

def remaining (steps : List (Step σ)) (state : State σ) : Nat :=
  steps.countP (unfinished state)

structure Extends (before after : State σ) : Prop where
  production : ∃ tail, after.produced = before.produced ++ tail
  available : ∀ a value, before.available a = some value →
    after.available a = some value

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem Extends.refl (state : State σ) : Extends state state :=
  ⟨⟨[], by simp⟩, fun _ _ h => h⟩

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem Extends.trans (first : Extends a b) (second : Extends b c) : Extends a c := by
  obtain ⟨left, hl⟩ := first.production
  obtain ⟨right, hr⟩ := second.production
  refine ⟨⟨left ++ right, ?_⟩, ?_⟩
  · simp [hr, hl, List.append_assoc]
  · intro address value h
    exact second.available address value (first.available address value h)

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem produce_extends (state : State σ) (cap : Nat) (value : ℚ) :
    Extends state { state with produced := state.produced ++ [(cap, value)] } := by
  exact ⟨⟨[(cap, value)], rfl⟩, fun _ _ h => h⟩

omit [Fintype σ.Tensor] in
theorem collect_extends (state : State σ) (a : Address σ) (value : ℚ)
    (fresh : state.available a = none) :
    letI := Program.Executor.addressEq (σ := σ)
    Extends state { state with
      available := Function.update state.available a (some value) } := by
  letI := Program.Executor.addressEq (σ := σ)
  constructor
  · exact ⟨[], by simp⟩
  · intro b old h
    have hne : b ≠ a := by
      intro heq
      subst b
      rw [fresh] at h
      contradiction
    simpa [Function.update_apply, hne] using h

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem produced_mapM_some (state : State σ) (caps : List Nat)
    (ready : caps.all (fun cap => (producedValue state cap).isSome) = true) :
    ∃ values, caps.mapM (producedValue state) = some values := by
  induction caps with
  | nil => exact ⟨[], rfl⟩
  | cons cap caps ih =>
      simp only [List.all_cons, Bool.and_eq_true_iff] at ready
      obtain ⟨values, hvalues⟩ := ih ready.2
      cases hcap : producedValue state cap with
      | none => simp [hcap] at ready
      | some value =>
          exact ⟨value :: values, by simp [List.mapM_cons, hcap, hvalues]⟩

theorem countP_strict {α : Type*} (steps : List α) (p q : α → Bool)
    (mono : ∀ s ∈ steps, p s = true → q s = true)
    (witness : ∃ s ∈ steps, p s = false ∧ q s = true) :
    steps.countP p < steps.countP q := by
  obtain ⟨s, hs, hp, hq⟩ := witness
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hs
  have hb : before.countP p ≤ before.countP q :=
    List.countP_mono_left (fun x hx hp => mono x (by simp [hx]) hp)
  have ha : after.countP p ≤ after.countP q :=
    List.countP_mono_left (fun x hx hp => mono x (by simp [hx]) hp)
  simp [List.countP_append, hp, hq] at *
  omega

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem producedValue_append (state : State σ) (cap : Nat) (value : ℚ)
    (fresh : producedValue state cap = none) (key : Nat) :
    producedValue { state with produced := state.produced ++ [(cap, value)] } key =
      if key = cap then some value else producedValue state key := by
  by_cases hk : key = cap
  · subst key
    have hn : state.produced.find? (fun row => row.1 == cap) = none := by
      cases h : state.produced.find? (fun row => row.1 == cap) <;>
        simp_all [producedValue]
    simp [producedValue, List.find?_append, hn]
  · simp [producedValue, List.find?_append, hk, Ne.symm hk, beq_iff_eq]

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem produce_decreases (steps : List (Step σ)) (state : State σ)
    (w : Writer σ) (member : Step.write w ∈ steps)
    (fresh : producedValue state w.capability = none) (value : ℚ) :
    remaining steps { state with produced := state.produced ++ [(w.capability, value)] } <
      remaining steps state := by
  apply countP_strict
  · intro step _ h
    cases step with
    | write v =>
        simp only [unfinished, producedValue_append state w.capability value fresh] at h
        split at h
        · simp at h
        · exact h
    | collect a caps => exact h
  · refine ⟨.write w, member, ?_, ?_⟩
    · simp [unfinished, producedValue_append state w.capability value fresh]
    · simp [unfinished, fresh]

omit [Fintype σ.Tensor] in
theorem collect_decreases (steps : List (Step σ)) (state : State σ)
    (a : Address σ) (caps : List Nat) (member : Step.collect a caps ∈ steps)
    (fresh : state.available a = none) (value : ℚ) :
    letI := Program.Executor.addressEq (σ := σ)
    remaining steps { state with
      available := Function.update state.available a (some value) } <
      remaining steps state := by
  letI := Program.Executor.addressEq (σ := σ)
  apply countP_strict
  · intro step _ h
    cases step with
    | write v => exact h
    | collect b ports =>
        simp only [unfinished, Function.update_apply] at h
        split at h
        · simp at h
        · exact h
  · refine ⟨.collect a caps, member, ?_, ?_⟩
    · simp [unfinished]
    · simp [unfinished, fresh]

omit [Fintype σ.Tensor] in
theorem stepFuel_not_exhausted (steps : List (Step σ)) (fuel : Nat)
    (state : State σ) (enough : remaining steps state < fuel) (endpoint : State σ) :
    (stepFuel steps fuel state).outcome ≠ .exhausted endpoint := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      rw [stepFuel]
      by_cases hc : complete steps state = true
      · simp [hc]
      · simp only [hc]
        cases hs : steps.find? (enabled state) with
        | none => simp
        | some step =>
            have member := List.mem_of_find?_eq_some hs
            have eligible := List.find?_some hs
            cases step with
            | write w =>
                have fresh : producedValue state w.capability = none := by
                  have h := Bool.and_eq_true_iff.mp eligible
                  simpa [enabled] using h.1
                simp only
                cases he : evalReady RationalReference.ops state.available w.body () with
                | notReady => simp
                | evaluated result =>
                    cases result with
                    | none => simp
                    | some value =>
                        simp only
                        apply ih
                        have hd := produce_decreases steps state w member fresh value
                        omega
            | collect a caps =>
                letI := Program.Executor.addressEq (σ := σ)
                have fresh : state.available a = none := by
                  have h := Bool.and_eq_true_iff.mp eligible
                  simpa [enabled] using h.1
                simp only
                cases hv : caps.mapM (producedValue state) with
                | none => simp
                | some values =>
                    simp only
                    apply ih
                    have hd := collect_decreases steps state a caps member fresh
                      (values.foldl (· + ·) (0 : ℚ))
                    exact hd.trans_le (Nat.le_of_lt_succ enough)

omit [Fintype σ.Tensor] in
theorem execute_not_exhausted (graph : Closed σ)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ))
    (endpoint : State σ) :
    (execute graph η).outcome ≠ .exhausted endpoint := by
  unfold execute
  split
  · simp
  · apply stepFuel_not_exhausted
    simp only [Option.getD_none]
    have h : remaining graph.steps (initial η) ≤ graph.steps.length :=
      List.countP_le_length
    omega

theorem runChecked_not_exhausted (contract : Contract σ) (fragment : Fragment σ)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ))
    (endpoint : State σ) :
    (runChecked contract fragment η).outcome ≠ .exhausted endpoint := by
  unfold runChecked
  split
  · simp
  · exact execute_not_exhausted _ _ _

omit [Fintype σ.Tensor] in
theorem stepFuel_not_collectorMismatch (steps : List (Step σ)) (fuel : Nat)
    (state : State σ) (address : Address σ) (endpoint : State σ) :
    (stepFuel steps fuel state).outcome ≠ .collectorMismatch address endpoint := by
  induction fuel generalizing state with
  | zero =>
      rw [stepFuel]
      split
      · simp
      · split <;> simp
  | succ fuel ih =>
      rw [stepFuel]
      split
      · simp
      · cases hs : steps.find? (enabled state) with
        | none => simp
        | some step =>
            have eligible := List.find?_some hs
            cases step with
            | write w =>
                simp only
                cases evalReady RationalReference.ops state.available w.body () with
                | notReady => simp
                | evaluated result =>
                    cases result with
                    | none => simp
                    | some value => exact ih _
            | collect a caps =>
                have ready : caps.all
                    (fun cap => (producedValue state cap).isSome) = true :=
                  (Bool.and_eq_true_iff.mp eligible).2
                obtain ⟨values, hv⟩ := produced_mapM_some state caps ready
                simp only [hv]
                exact ih _

omit [Fintype σ.Tensor] in
theorem stepFuel_states_extend (steps : List (Step σ)) (fuel : Nat)
    (state : State σ) :
    ∀ next ∈ (stepFuel steps fuel state).states, Extends state next := by
  have terminal (state : State σ) : ∀ next ∈ [state], Extends state next := by
    intro next member
    have same := List.mem_singleton.mp member
    subst next
    exact Extends.refl state
  induction fuel generalizing state with
  | zero =>
      rw [stepFuel]
      split
      · exact terminal state
      · split <;> exact terminal state
  | succ fuel ih =>
      rw [stepFuel]
      split
      · exact terminal state
      · cases hs : steps.find? (enabled state) with
        | none => exact terminal state
        | some step =>
            have eligible := List.find?_some hs
            cases step with
            | write w =>
                simp only
                cases evalReady RationalReference.ops state.available w.body () with
                | notReady => exact terminal state
                | evaluated result =>
                    cases result with
                    | none => exact terminal state
                    | some value =>
                        intro next member
                        simp only [List.mem_cons] at member
                        rcases member with rfl | member
                        · exact Extends.refl _
                        · exact (produce_extends state w.capability value).trans
                            (ih _ next member)
            | collect a caps =>
                have fresh : state.available a = none := by
                  have h := Bool.and_eq_true_iff.mp eligible
                  simpa [enabled] using h.1
                simp only
                cases hv : caps.mapM (producedValue state) with
                | none => exact terminal state
                | some values =>
                    intro next member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · exact Extends.refl _
                    · exact (collect_extends state a (values.foldl (· + ·) 0) fresh).trans
                        (ih _ next member)

end IndexedOpenComposition.Correspondence
