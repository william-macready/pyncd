import IndexedComponentModelWitnesses
import IndexedComponentModelGeometryFixtures

namespace IndexedComponentModelGeometryTest

open LeanNCD.Semantics
open IndexedComponentComposition

namespace Empty

open IndexedComponentCompositionPortFixtures
open IndexedComponentModelGeometryFixtures.Empty

theorem lifted_input_present :
    (liftInput emptyProducerComponent emptyConsumerComponent emptyBoundary
      emptyValidatedInput).val (.inl emptyExternalInput) =
      some (fun p => Fin.elim0 p.1) := rfl

theorem boundary_input_present :
    (boundaryInput emptyProducerComponent emptyConsumerComponent emptyBoundary
      producerStore).val emptyConsumerPre = some transportedPre := rfl

theorem boundary_input_eq :
    boundaryInput emptyProducerComponent emptyConsumerComponent emptyBoundary
      producerStore = consumerInput := by
  apply Subtype.ext
  funext t
  fin_cases t <;> rfl

def compositeStore := glueStore emptyProducerComponent emptyConsumerComponent
  producerStore consumerStore

theorem downstream_model :
    emptyConsumerComponent.program.Models RationalReference.ops
      (boundaryInput emptyProducerComponent emptyConsumerComponent emptyBoundary producerStore)
      consumerStore := by
  rw [boundary_input_eq]
  exact consumer_model

theorem composite_model :
    (program emptyProducerComponent emptyConsumerComponent emptyBoundary).Models
      RationalReference.ops
      (liftInput emptyProducerComponent emptyConsumerComponent emptyBoundary emptyValidatedInput)
      compositeStore :=
  (models_glue_iff emptyProducerComponent emptyConsumerComponent emptyBoundary
    emptyValidatedInput producerStore consumerStore downstream_model.choose_spec.1).mpr
      ⟨producer_model, downstream_model⟩

theorem empty_output_identity :
    (program emptyProducerComponent emptyConsumerComponent emptyBoundary).output
      (.inr ⟨emptyConsumerOut, rfl⟩) = true ∧
    (outputIndexEquiv emptyProducerComponent emptyConsumerComponent emptyBoundary)
      ⟨.inr ⟨emptyConsumerOut, rfl⟩, rfl⟩ = ⟨emptyConsumerOut, rfl⟩ := by
  constructor
  · rfl
  · rfl

theorem input_roundtrip :
    restrictInput emptyProducerComponent emptyConsumerComponent emptyBoundary
      (liftInput emptyProducerComponent emptyConsumerComponent emptyBoundary
        emptyValidatedInput) = emptyValidatedInput :=
  restrictInput_liftInput _ _ _ _

theorem store_roundtrip :
    glueStore emptyProducerComponent emptyConsumerComponent
      (restrictUpstream emptyProducerComponent emptyConsumerComponent compositeStore)
      (restrictDownstream emptyProducerComponent emptyConsumerComponent emptyBoundary
        compositeStore) = compositeStore :=
  glueStore_restrictions _ _ _ _

end Empty

namespace Axis

open IndexedComponentCompositionAxisFixtures
open IndexedComponentModelGeometryFixtures.Axis
open IndexedComponentTransportTest (p q)

theorem boundary_input_eq :
    boundaryInput axisProducer axisConsumer axisBoundary producerStore = consumerInput := by
  apply Subtype.ext
  funext t
  fin_cases t <;> rfl

def compositeStore := glueStore axisProducer axisConsumer producerStore consumerStore

theorem downstream_model :
    axisConsumer.program.Models RationalReference.ops
      (boundaryInput axisProducer axisConsumer axisBoundary producerStore) consumerStore := by
  rw [boundary_input_eq]
  exact consumer_model

theorem composite_model :
    (program axisProducer axisConsumer axisBoundary).Models RationalReference.ops
      (liftInput axisProducer axisConsumer axisBoundary producerInput) compositeStore :=
  (models_glue_iff axisProducer axisConsumer axisBoundary
    producerInput producerStore consumerStore downstream_model.choose_spec.1).mpr
      ⟨producer_model, downstream_model⟩

theorem restricted_values :
    restrictDownstream axisProducer axisConsumer axisBoundary compositeStore ⟨0, p⟩ = 5 ∧
    restrictDownstream axisProducer axisConsumer axisBoundary compositeStore ⟨0, q⟩ = 2 ∧
    compositeStore ⟨.inr ⟨1, rfl⟩, ()⟩ = 14 := by
  unfold compositeStore
  rw [restrictDownstream_glueStore axisProducer axisConsumer axisBoundary
    producerStore consumerStore downstream_model.choose_spec.1]
  exact consumer_values

theorem restricted_not_flattened :
    (fun c => restrictDownstream axisProducer axisConsumer axisBoundary compositeStore ⟨0, c⟩)
      ≠ flattenedPre := by
  unfold compositeStore
  rw [restrictDownstream_glueStore axisProducer axisConsumer axisBoundary
    producerStore consumerStore downstream_model.choose_spec.1]
  exact Ne.symm coordinate_transport_distinct

theorem store_roundtrip :
    glueStore axisProducer axisConsumer
      (restrictUpstream axisProducer axisConsumer compositeStore)
      (restrictDownstream axisProducer axisConsumer axisBoundary compositeStore) =
      compositeStore :=
  glueStore_restrictions _ _ _ _

#eval (restrictDownstream axisProducer axisConsumer axisBoundary compositeStore ⟨0, p⟩,
  restrictDownstream axisProducer axisConsumer axisBoundary compositeStore ⟨0, q⟩,
  compositeStore ⟨.inr ⟨1, rfl⟩, ()⟩)

end Axis

end IndexedComponentModelGeometryTest
