import IndexedComponentModelWitnesses
import IndexedComponentModelLocalFixtures

namespace IndexedComponentModelLocalTest

open LeanNCD.Semantics
open IndexedComponentComposition
open IndexedComponentCompositionPortFixtures
open IndexedComponentModelLocalFixtures

theorem boundary_zero_input (other : ℚ) :
    boundaryInput producerComponent (consumerComponent other) (scalarBoundary other)
      producerStore = consumerInput other := by
  apply Subtype.ext
  funext t
  fin_cases t <;> rfl

def totalCompositeStore :=
  glueStore producerComponent (consumerComponent 4) producerStore totalStore

theorem total_downstream_model :
    (consumerComponent 4).program.Models RationalReference.ops
      (boundaryInput producerComponent (consumerComponent 4) (scalarBoundary 4) producerStore)
      totalStore := by
  rw [boundary_zero_input]
  exact total_model

theorem total_composite_model :
    (program producerComponent (consumerComponent 4) (scalarBoundary 4)).Models
      RationalReference.ops
      (liftInput producerComponent (consumerComponent 4) (scalarBoundary 4) producerInput)
      totalCompositeStore := by
  exact (models_glue_iff producerComponent (consumerComponent 4) (scalarBoundary 4)
    producerInput producerStore totalStore total_downstream_model.choose_spec.1).mpr
      ⟨producer_model, total_downstream_model⟩

def totalPair : CompatibleWitnesses producerComponent (consumerComponent 4)
    (scalarBoundary 4) producerInput :=
  ⟨⟨producerStore, producer_model⟩, ⟨totalStore, total_downstream_model⟩⟩

def totalWitness : CompositeWitness producerComponent (consumerComponent 4)
    (scalarBoundary 4) producerInput :=
  ⟨totalCompositeStore, total_composite_model⟩

theorem total_pair_roundtrip :
    (witnessesEquiv producerComponent (consumerComponent 4) (scalarBoundary 4)
      producerInput)
        ((witnessesEquiv producerComponent (consumerComponent 4) (scalarBoundary 4)
          producerInput).symm totalPair) = totalPair :=
  Equiv.apply_symm_apply _ _

theorem total_witness_roundtrip :
    (witnessesEquiv producerComponent (consumerComponent 4) (scalarBoundary 4)
      producerInput).symm
        ((witnessesEquiv producerComponent (consumerComponent 4) (scalarBoundary 4)
          producerInput) totalWitness) = totalWitness :=
  Equiv.symm_apply_apply _ _

theorem total_store_values :
    totalCompositeStore ⟨.inl producerPre, ()⟩ = 0 ∧
    totalCompositeStore ⟨.inr ⟨consumerOut, rfl⟩, ()⟩ = 0 ∧
    totalCompositeStore ⟨.inr ⟨strictAudit, rfl⟩, ()⟩ = 1 / 2 := by
  decide +kernel

theorem strict_no_compatible :
    IsEmpty (CompatibleWitnesses producerComponent (consumerComponent 0)
      (scalarBoundary 0) producerInput) :=
  ⟨fun pair => strict_no_model _ pair.2.val pair.2.property⟩

theorem strict_no_composite (ρ : Store K
    (declarations producerComponent (consumerComponent 0))) :
    ¬ (program producerComponent (consumerComponent 0) (scalarBoundary 0)).Models
      RationalReference.ops
      (liftInput producerComponent (consumerComponent 0) (scalarBoundary 0) producerInput) ρ := by
  intro model
  have components := (models_restrict_iff producerComponent (consumerComponent 0)
    (scalarBoundary 0) producerInput ρ).mp model
  exact strict_no_model _ _ components.2

theorem zero_boundary_input :
    boundaryInput zeroProducerComponent (consumerComponent 4) zeroBoundary
      producerStore = consumerInput 4 := by
  apply Subtype.ext
  funext t
  fin_cases t <;> rfl

theorem zero_composite_model :
    (program zeroProducerComponent (consumerComponent 4) zeroBoundary).Models
      RationalReference.ops
      (liftInput zeroProducerComponent (consumerComponent 4) zeroBoundary producerInput)
      (glueStore zeroProducerComponent (consumerComponent 4) producerStore totalStore) := by
  have downstreamModel : (consumerComponent 4).program.Models RationalReference.ops
      (boundaryInput zeroProducerComponent (consumerComponent 4) zeroBoundary producerStore)
      totalStore := by
    rw [zero_boundary_input]
    exact total_model
  exact (models_glue_iff zeroProducerComponent (consumerComponent 4) zeroBoundary
    producerInput producerStore totalStore downstreamModel.choose_spec.1).mpr
      ⟨zero_producer_model, downstreamModel⟩

theorem zero_composite_forces_zero (ρ : Store K
    (declarations zeroProducerComponent (consumerComponent 4)))
    (model : (program zeroProducerComponent (consumerComponent 4) zeroBoundary).Models
      RationalReference.ops
      (liftInput zeroProducerComponent (consumerComponent 4) zeroBoundary producerInput) ρ) :
    ρ ⟨.inl producerPre, ()⟩ = 0 := by
  have upstreamModel := ((models_restrict_iff zeroProducerComponent (consumerComponent 4)
    zeroBoundary producerInput ρ).mp model).1
  exact zero_producer_forces_zero _ _ upstreamModel

#eval (totalCompositeStore ⟨.inl producerPre, ()⟩,
  totalCompositeStore ⟨.inr ⟨consumerOut, rfl⟩, ()⟩,
  totalCompositeStore ⟨.inr ⟨strictAudit, rfl⟩, ()⟩)

end IndexedComponentModelLocalTest
