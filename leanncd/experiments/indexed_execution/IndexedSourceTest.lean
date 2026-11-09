import IndexedSourceSemantics
import IndexedWitnessCompositionTest
import IndexedWitnessTest
import IndexedWitnessPartialTest
import Semantics.AxiomAudit

namespace IndexedSourceTest

open LeanNCD.Semantics IndexedComponentComposition IndexedWitness IndexedSource CategoryTheory

noncomputable section

example : Category.{1} Object := inferInstance
example : Object ⥤ WholeInterface := semantics
example (X Y : Object) (f : X ⟶ Y) : 𝟙 X ≫ f = f := Category.id_comp f
example (X Y : Object) (f : X ⟶ Y) : f ≫ 𝟙 Y = f := Category.comp_id f
example (W X Y Z : Object) (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := Category.assoc f g h
example (X : Object) : semantics.map (𝟙 X) = 𝟙 X.interface := semantics.map_id X
example (X Y Z : Object) (f : X ⟶ Y) (g : Y ⟶ Z) :
    semantics.map (f ≫ g) = semantics.map f ≫ semantics.map g := semantics.map_comp f g

namespace Axis
open IndexedComponentCompositionAxisFixtures
open IndexedComponentModelGeometryFixtures.Axis
open IndexedComponentTransportTest (swapDomain p q)
open IndexedWitnessCompositionTest.Axis (sourceEnv wrongReversed witness)

def wire := boundaryWire axisProducer axisConsumer axisBoundary

theorem coordinate_cells :
    wire.env sourceEnv ⟨0, rfl⟩ p = 5 ∧ wire.env sourceEnv ⟨0, rfl⟩ q = 2 := by
  decide +kernel

theorem inverse_cells :
    wire.inverse.env (wire.env sourceEnv) ⟨1, rfl⟩ (swapDomain.coord p) = 5 ∧
      wire.inverse.env (wire.env sourceEnv) ⟨1, rfl⟩ (swapDomain.coord q) = 2 := by
  rw [Wire.env_inverse, Equiv.symm_apply_apply]
  decide +kernel

theorem reversed_control :
    wrongReversed ⟨0, rfl⟩ q = 3 ∧ wire.env sourceEnv ⟨0, rfl⟩ q = 2 := by
  decide +kernel

example : arrow (.seq (.wire wire) (.wire wire.inverse)) = 𝟙 (output axisProducer) :=
  Quotient.sound (Rel.wire_left_inv wire)
example : arrow (.seq (.wire wire.inverse) (.wire wire)) = 𝟙 (input axisConsumer) :=
  Quotient.sound (Rel.wire_right_inv wire)
example : arrow (assembled axisProducer axisConsumer axisBoundary) =
    arrow (pair axisProducer axisConsumer axisBoundary) :=
  assembly_eq _ _ _
example : semantics.map (arrow (assembled axisProducer axisConsumer axisBoundary)) =
    semantics.map (arrow (pair axisProducer axisConsumer axisBoundary)) :=
  congrArg semantics.map (assembly_eq _ _ _)

theorem exterior_cells :
    (inputWire axisProducer axisConsumer axisBoundary).inverse.env
        ((componentSpan (compose axisProducer axisConsumer axisBoundary)).left witness) =
      (compositeRebasedSpan axisProducer axisConsumer axisBoundary).left witness ∧
    (outputWire axisProducer axisConsumer axisBoundary).env
        ((componentSpan (compose axisProducer axisConsumer axisBoundary)).right witness)
        ⟨1, rfl⟩ () = 14 := by
  refine ⟨?_, ?_⟩
  · rw [Wire.env_inverse, inputWire_env]; rfl
  · decide +kernel

end Axis

namespace Empty
open IndexedComponentCompositionPortFixtures
open IndexedWitnessCompositionTest.Empty (composite)

theorem metadata :
    output emptyProducerComponent ≠ output composite := by
  intro h
  exact IndexedWitnessCompositionTest.Empty.metadata_not_equal (congrArg Object.interface h)

theorem input_present :
    ((inputEquiv emptyProducerComponent) IndexedWitnessTest.emptyInputEnv).val
      emptyExternalInput ≠ none := by
  intro h
  have hp := ((inputEquiv emptyProducerComponent) IndexedWitnessTest.emptyInputEnv).property
    emptyExternalInput
  rw [h] at hp
  exact Bool.noConfusion hp

end Empty

namespace Triple
open IndexedWitnessCompositionTest.Triple
open IndexedComponentTransportTest (swapDomain p)

example : arrow (leftNested A B C ab bc) = arrow (IndexedSource.triple A B C ab bc) :=
  left_eq_triple _ _ _ _ _
example : arrow (rightNested A B C ab bc) = arrow (IndexedSource.triple A B C ab bc) :=
  right_eq_triple _ _ _ _ _
example : semantics.map (arrow (leftNested A B C ab bc)) =
    semantics.map (arrow (rightNested A B C ab bc)) :=
  sound (Rel.bracket A B C ab bc)
example : (bracketSpanIso A B C ab bc).witness leftWitness = rightWitness := bracket_applied
example : ((rightTripleEquiv A B C ab bc)
    ((bracketSpanIso A B C ab bc).witness leftWitness)) =
    IndexedWitnessCompositionTest.Triple.triple := returned_private_stores

theorem private_cells :
    leftWitness.2.val ⟨.inl (.inl 1), p⟩ = 15 ∧
      leftWitness.2.val ⟨.inl (.inr ⟨1, rfl⟩), swapDomain.coord p⟩ = 35 ∧
      rightWitness.2.val ⟨.inr ⟨.inr ⟨1, rfl⟩, rfl⟩, ()⟩ = 134 ∧
      (declarations (compose A B ab) C).uid (.inl (.inl 1)) = 164 ∧
      (declarations A (compose B C bc)).uid (.inl 1) = 82 := by
  decide +kernel

end Triple

namespace Hidden
open IndexedComponentModelCycleFixtures
open IndexedComponentModelLocalFixtures IndexedComponentCompositionPortFixtures
open IndexedWitnessTest (hiddenZero hiddenOne)

theorem complete_not_output_only :
    hiddenZero ≠ hiddenOne ∧
    (componentSpan hiddenUpstream).right hiddenZero =
      (componentSpan hiddenUpstream).right hiddenOne :=
  ⟨IndexedWitnessTest.hidden_witnesses_distinct, IndexedWitnessTest.hidden_outputs_equal⟩

example : semantics.map (arrow (.leaf hiddenUpstream)) =
    Quotient.mk _ (componentSpan hiddenUpstream) := rfl

example : ¬ (componentSpan (compose producerComponent (consumerComponent 0)
    (scalarBoundary 0))).Domain (inputEnv (compose producerComponent (consumerComponent 0)
      (scalarBoundary 0)) (liftInput producerComponent (consumerComponent 0)
        (scalarBoundary 0) producerInput)) := IndexedWitnessPartialTest.strict_no_domain
example : (componentSpan (compose producerComponent (consumerComponent 4)
    (scalarBoundary 4))).Domain (inputEnv (compose producerComponent (consumerComponent 4)
      (scalarBoundary 4)) (liftInput producerComponent (consumerComponent 4)
        (scalarBoundary 4) producerInput)) := IndexedWitnessPartialTest.total_domain

end Hidden

#audit_axioms IndexedSource
#audit_axioms IndexedSourceTest
#print axioms IndexedComponentTransport.Domain.inverse
#print axioms IndexedSource.sound
#print axioms IndexedSource.semantics
#print axioms IndexedSource.left_eq_triple
#print axioms IndexedSource.right_eq_triple

end

end IndexedSourceTest
