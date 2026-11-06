import IndexedCompositionMatch
import IndexedCompositionRunner

namespace IndexedOpenComposition.Correspondence

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {schedule : Schedule P} {contract : Contract σ} {fragment : Fragment σ}
variable {graph : Closed σ}

def InputsAvailable
    (P : Program RationalReference.Carrier σ RationalReference.registry)
    (g : State σ) : Prop :=
  ∀ a, P.input a.1 = true → (g.available a).isSome = true

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem initial_inputs_available (η : P.Input) :
    InputsAvailable P (initial η.val) := by
  intro a input
  have present := η.property a.1
  rw [input] at present
  cases h : η.val a.1 with
  | none => simp [h] at present
  | some values => simp [initial, h]

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem InputsAvailable.extends (inputs : InputsAvailable P g)
    (extension : Extends g next) : InputsAvailable P next := by
  intro a input
  have present := inputs a input
  cases h : g.available a with
  | none => simp [h] at present
  | some value => simp [extension.available a value h]

theorem complete_agrees
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (inputs : InputsAvailable P g) :
    complete graph.steps g = true ↔ P.Complete c := by
  have member (key : Key P) : M.step key ∈ graph.steps := by
    rw [← M.priority]
    exact List.mem_map.mpr ⟨key, schedule.keys_complete key, rfl⟩
  constructor
  · intro finished
    have done := List.all_eq_true.mp finished
    constructor
    · intro t
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro o pending
      have produced := done (M.step (.occurrence t o)) (member _)
      have absent := (R.pending t o).mp pending
      change (producedValue g (M.capability ⟨t, o⟩)).isSome = true at produced
      simp [absent] at produced
    · intro a
      rw [← R.published]
      cases role : P.input a.1 with
      | true => exact inputs a role
      | false =>
          have published := done (M.step (.publication ⟨a.1, role⟩ a.2)) (member _)
          simpa [SourceContractMatch.step, keyStep] using published
  · intro finished
    apply List.all_eq_true.mpr
    intro step inSteps
    rw [← M.priority] at inSteps
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp inSteps
    cases key with
    | occurrence t o =>
        have notPending : o ∉ c.pending t := by simp [finished.1 t]
        have produced : producedValue g (M.capability ⟨t, o⟩) ≠ none :=
          fun absent => notPending ((R.pending t o).mpr absent)
        simpa [SourceContractMatch.step, keyStep, SourceContractMatch.capability,
          SourceContractMatch.writer, Option.isSome_iff_ne_none] using produced
    | publication t p =>
        simpa [SourceContractMatch.step, keyStep, R.published] using
          finished.2 ⟨t.val, p⟩

end IndexedOpenComposition.Correspondence
