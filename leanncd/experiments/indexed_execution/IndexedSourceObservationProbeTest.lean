import IndexedSourceObservationProbe
import IndexedWitnessCompositionTest
import IndexedWitnessTest
import IndexedWitnessPartialTest
import Semantics.AxiomAudit

namespace IndexedSourceObservationProbeTest
open LeanNCD.Semantics IndexedComponentComposition IndexedWitness IndexedSource
open IndexedSourceObservationProbe
open IndexedComponentTransportTest (p q swapDomain)
noncomputable section

namespace Axis
open IndexedComponentCompositionAxisFixtures
open IndexedWitnessCompositionTest.Axis (sourceEnv wrongReversed)
def wire := boundaryWire axisProducer axisConsumer axisBoundary
theorem boundary_cells :
    boundaryCopy wire sourceEnv ⟨0, rfl⟩ p = 5 ∧
      boundaryCopy wire sourceEnv ⟨0, rfl⟩ q = 2 ∧
      wrongReversed ⟨0, rfl⟩ q = 3 := by decide +kernel
theorem inverse_cells :
    inverseCopy wire (wire.env sourceEnv) ⟨1, rfl⟩ (swapDomain.coord p) = 5 ∧
      inverseCopy wire (wire.env sourceEnv) ⟨1, rfl⟩ (swapDomain.coord q) = 2 := by
  decide +kernel
end Axis

namespace Triple
open IndexedWitnessCompositionTest.Triple
theorem input_cells :
    inputCopy (inputWire A B ab) ((componentSpan A).left aWitness)
      ⟨.inl 0, rfl⟩ p = 5 ∧
    inputCopy (inputWire A B ab) ((componentSpan A).left aWitness)
      ⟨.inl 0, rfl⟩ q = 2 := by decide +kernel
theorem output_cells :
    outputCopy (outputWire (compose A B ab) C (leftNestedBoundary A B C ab bc))
      ((componentSpan (leftBracket A B C ab bc)).right leftWitness)
      ⟨1, rfl⟩ () = 134 := by decide +kernel
def privateId : Nat := (declarations (compose A B ab) C).uid (.inl (.inl 1))
theorem private_identity : privateId = 164 := by decide +kernel
end Triple

namespace Hidden
open IndexedComponentModelCycleFixtures
def second := IndexedWitnessTest.hiddenOne
theorem hidden_cell : second.2.val ⟨0, ()⟩ = 1 := by decide +kernel
end Hidden

namespace Empty
open IndexedComponentCompositionPortFixtures
def external : (inputInterface emptyProducerComponent).Tensor := ⟨emptyExternalInput, rfl⟩
theorem presence :
    ((inputEquiv emptyProducerComponent) IndexedWitnessTest.emptyInputEnv).val
      external.val ≠ none := by
  intro h
  have hp := ((inputEquiv emptyProducerComponent) IndexedWitnessTest.emptyInputEnv).property
    external.val
  rw [h] at hp
  exact Bool.noConfusion hp
def presenceCell : Bool :=
  (((inputEquiv emptyProducerComponent) IndexedWitnessTest.emptyInputEnv).val
    external.val).isSome
theorem presence_cell : presenceCell = true := by decide +kernel
end Empty

namespace Strict
open IndexedComponentModelLocalFixtures IndexedComponentCompositionPortFixtures
def profile : Nat := 0
theorem undefined :
    ¬ (componentSpan (compose producerComponent (consumerComponent profile)
      (scalarBoundary profile))).Domain
      (inputEnv (compose producerComponent (consumerComponent profile) (scalarBoundary profile))
        (liftInput producerComponent (consumerComponent profile) (scalarBoundary profile)
          producerInput)) := IndexedWitnessPartialTest.strict_no_domain
def totalProfile : Nat := 4
theorem defined :
    (componentSpan (compose producerComponent (consumerComponent totalProfile)
      (scalarBoundary totalProfile))).Domain
      (inputEnv (compose producerComponent (consumerComponent totalProfile)
        (scalarBoundary totalProfile)) (liftInput producerComponent (consumerComponent totalProfile)
          (scalarBoundary totalProfile) producerInput)) := IndexedWitnessPartialTest.total_domain
end Strict

namespace Metadata
open IndexedComponentCompositionPortFixtures
def original := output emptyProducerComponent
theorem distinct : original ≠ output IndexedWitnessCompositionTest.Empty.composite := by
  intro h
  exact IndexedWitnessCompositionTest.Empty.metadata_not_equal (congrArg Object.interface h)
end Metadata

#audit_axioms IndexedSourceObservationProbe
#audit_axioms IndexedSourceObservationProbeTest
end
end IndexedSourceObservationProbeTest
