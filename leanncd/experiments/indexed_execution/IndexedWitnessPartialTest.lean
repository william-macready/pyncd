import IndexedWitnessPartial
import IndexedComponentModelCycleTest
import IndexedComponentModelLocalTest
import Semantics.AxiomAudit

namespace IndexedWitnessPartialTest

open LeanNCD.Semantics
open IndexedWitness
open IndexedComponentComposition
open IndexedComponentModelCycleFixtures
open IndexedComponentModelCycleTest
open IndexedComponentCompositionPortFixtures
open IndexedComponentModelLocalFixtures
open IndexedComponentModelLocalTest

theorem strict_no_domain :
    ¬ (componentSpan (compose producerComponent (consumerComponent 0)
      (scalarBoundary 0))).Domain
        (inputEnv (compose producerComponent (consumerComponent 0)
          (scalarBoundary 0))
          (liftInput producerComponent (consumerComponent 0)
            (scalarBoundary 0) producerInput)) := by
  rintro ⟨⟨η, ρ⟩, he⟩
  have hi := (inputEquiv (compose producerComponent (consumerComponent 0)
    (scalarBoundary 0))).symm.injective he
  change η = _ at hi
  exact strict_no_composite ρ.val (hi ▸ ρ.property)

theorem total_domain :
    (componentSpan (compose producerComponent (consumerComponent 4)
      (scalarBoundary 4))).Domain
        (inputEnv (compose producerComponent (consumerComponent 4)
          (scalarBoundary 4))
          (liftInput producerComponent (consumerComponent 4)
            (scalarBoundary 4) producerInput)) :=
  ⟨⟨_, ⟨totalCompositeStore, total_composite_model⟩⟩, rfl⟩

theorem strict_consumer_atMostOne :
    AtMostOneModels (consumerComponent 0) := by
  intro η ρ ρ' hm _
  exact (strict_no_model η ρ hm).elim

theorem strict_consumer_undefined (x : (inputInterface (consumerComponent 0)).Env) :
    (componentSpan (consumerComponent 0)).partialOption
        ((component_injective_iff (consumerComponent 0)).2
          strict_consumer_atMostOne) x = none := by
  have hn : ¬ (componentSpan (consumerComponent 0)).Domain x := by
    rintro ⟨⟨η, ρ⟩, _⟩
    exact strict_no_model η ρ.val ρ.property
  simp [Span.partialOption, hn]

theorem cycle_upstream_not_injective :
    ¬ Function.Injective (componentSpan cycleUpstream).left := by
  intro h
  have hUnique := (component_injective_iff cycleUpstream).mp h
  apply IndexedComponentModelCycleTest.cycle_upstream_not_admissible
  exact ⟨scalarStore 0 0, cycle_upstream_zero_model,
    fun ρ hm => (hUnique (upstreamInput false) ρ
      (scalarStore 0 0) hm cycle_upstream_zero_model)⟩

theorem cycle_composite_domain :
    (componentSpan (compose cycleUpstream cycleDownstream cycleBoundary)).Domain
      (inputEnv (compose cycleUpstream cycleDownstream cycleBoundary)
        (liftInput cycleUpstream cycleDownstream cycleBoundary
          (upstreamInput false))) :=
  ⟨⟨_, ⟨cycleOneStore, cycle_one_model⟩⟩, rfl⟩

theorem cycle_composite_unique_at_input
    (w w' : (componentSpan (compose cycleUpstream cycleDownstream cycleBoundary)).W)
    (hw : (componentSpan (compose cycleUpstream cycleDownstream cycleBoundary)).left w =
      inputEnv (compose cycleUpstream cycleDownstream cycleBoundary)
        (liftInput cycleUpstream cycleDownstream cycleBoundary (upstreamInput false)))
    (hw' : (componentSpan (compose cycleUpstream cycleDownstream cycleBoundary)).left w' =
      inputEnv (compose cycleUpstream cycleDownstream cycleBoundary)
        (liftInput cycleUpstream cycleDownstream cycleBoundary (upstreamInput false))) :
    w = w' := by
  have hi := (inputEquiv (compose cycleUpstream cycleDownstream cycleBoundary)).symm.injective hw
  have hi' := (inputEquiv (compose cycleUpstream cycleDownstream cycleBoundary)).symm.injective hw'
  cases w with
  | mk η ρ =>
    cases w' with
    | mk η' ρ' =>
      dsimp at hi hi'
      subst η
      subst η'
      have hs : ρ.val = ρ'.val :=
        (cycle_composite_unique ρ.val ρ.property).trans
          (cycle_composite_unique ρ'.val ρ'.property).symm
      cases ρ with
      | mk store hm =>
        cases ρ' with
        | mk store' hm' =>
          dsimp at hs
          subst store'
          rfl

theorem downstream_selection_not_unrestricted :
    (∃ w : (componentSpan (compose cycleUpstream cycleDownstream cycleBoundary)).W,
      (componentSpan (compose cycleUpstream cycleDownstream cycleBoundary)).left w =
        inputEnv (compose cycleUpstream cycleDownstream cycleBoundary)
          (liftInput cycleUpstream cycleDownstream cycleBoundary
            (upstreamInput false)) ∧
      ∀ w' : (componentSpan (compose cycleUpstream cycleDownstream cycleBoundary)).W,
        (componentSpan (compose cycleUpstream cycleDownstream cycleBoundary)).left w' =
          inputEnv (compose cycleUpstream cycleDownstream cycleBoundary)
            (liftInput cycleUpstream cycleDownstream cycleBoundary
              (upstreamInput false)) → w' = w) ∧
    ¬ Function.Injective (componentSpan cycleUpstream).left := by
  constructor
  · obtain ⟨w, hw⟩ := cycle_composite_domain
    exact ⟨w, hw, fun w' hw' =>
      cycle_composite_unique_at_input w' w hw' hw⟩
  · exact cycle_upstream_not_injective

#print axioms IndexedWitness.Span.pullback_domain_iff
#print axioms IndexedWitness.Span.pullback_value
#print axioms IndexedWitness.RestrictedHom.partialOption
#print axioms IndexedWitness.component_injective_iff
#print axioms IndexedWitness.composite_rebased_value
#print axioms IndexedWitness.component_composite_domain
#print axioms IndexedWitness.component_composite_value
#print axioms downstream_selection_not_unrestricted
#audit_axioms IndexedWitness
#audit_axioms IndexedWitnessPartialTest

end IndexedWitnessPartialTest
