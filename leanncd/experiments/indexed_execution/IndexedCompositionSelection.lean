import IndexedCompositionMatch

namespace IndexedOpenComposition

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {schedule : Schedule P} {contract : Contract σ} {fragment : Fragment σ}
variable {graph : Closed σ}

def SourceContractMatch.event
    (M : SourceContractMatch P schedule contract fragment graph) :
    Executor.Event P → IndexedOpenComposition.Event σ
  | .contribution t o value =>
      .produced (M.tag ⟨t, o⟩) (M.capability ⟨t, o⟩) value
  | .publication t p value => .sealed ⟨t.val, p⟩ value
  | .undefined t o => .undefined (M.tag ⟨t, o⟩)

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem scan_first_attempt (c : P.Running) (keys : List (Key P)) :
    scan P RationalReference.ops c keys =
      (keys.find? fun k => (attempt P RationalReference.ops c k).isSome).bind
        (attempt P RationalReference.ops c) := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      cases h : attempt P RationalReference.ops c key <;> simp [scan, h, ih]

theorem first_eligible_agrees
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (c : P.Running)
    (eligibility : ∀ key,
      enabled g (M.step key) = (attempt P RationalReference.ops c key).isSome) :
    graph.steps.find? (enabled g) =
      (schedule.keys.find? fun k =>
        (attempt P RationalReference.ops c k).isSome).map M.step := by
  rw [← M.priority, List.find?_map]
  congr 2
  funext key
  exact eligibility key

def keyEquiv (P : Program RationalReference.Carrier σ RationalReference.registry) :
    Key P ≃ SourceOccurrence P ⊕
      ((t : P.Defined) × Coord (σ.signature t.val).axes) where
  toFun
    | .occurrence t o => .inl ⟨t, o⟩
    | .publication t p => .inr ⟨t, p⟩
  invFun
    | .inl ⟨t, o⟩ => .occurrence t o
    | .inr ⟨t, p⟩ => .publication t p
  left_inv := by intro key; cases key <;> rfl
  right_inv := by intro key; rcases key with ⟨t, o⟩ | ⟨t, p⟩ <;> rfl

omit [Fintype σ.Tensor] in
theorem schedule_default_budget (schedule : Schedule P) :
    initialBudget P = schedule.keys.length + 1 := by
  classical
  letI := finiteDefined P
  letI : ∀ t : P.Defined, Fintype (Coord (σ.signature t.val).axes) :=
    fun t => finiteCoords t.val
  letI : Fintype (Key P) := Fintype.ofEquiv _ (keyEquiv P).symm
  have full : schedule.keys.toFinset = Finset.univ := by
    ext key
    simp [schedule.keys_complete key]
  have length_card : schedule.keys.length = Fintype.card (Key P) := by
    rw [← List.toFinset_card_of_nodup schedule.keys_nodup, full]
    simp
  have coordinates (t : P.Defined) :
      Fintype.card (Coord (σ.signature t.val).axes) =
        (canonicalLayout (σ.signature t.val).axes).count := by
    simpa using
      (Fintype.card_congr (canonicalLayout (σ.signature t.val).axes).enumerate).symm
  rw [length_card, Fintype.card_congr (keyEquiv P)]
  simp [initialBudget, SourceOccurrence, Fintype.card_sum, Fintype.card_sigma,
    coordinates]

theorem default_budgets_agree
    (M : SourceContractMatch P schedule contract fragment graph) :
    initialBudget P = graph.steps.length + 1 := by
  have lengths := congrArg List.length M.priority
  rw [List.length_map] at lengths
  rw [schedule_default_budget schedule, lengths]

end IndexedOpenComposition
