import IndexedComponentCompositionPortFixtures
import IndexedComponentCompositionAxisFixtures
import LeanNCD.Semantics.Models

namespace IndexedComponentModelGeometryFixtures

open LeanNCD.Semantics
open LeanNCD.Semantics.Program

namespace Empty

open IndexedComponentCompositionPortFixtures
open IndexedComponentComposition

def liftedInput : InputBinding (K := RationalReference.Carrier)
    (σ := declarations emptyProducerComponent emptyConsumerComponent) :=
  fun t => match t with
    | .inl s => emptyValidatedInput.val s
    | .inr _ => none

def producerStore : Store RationalReference.Carrier emptyProducerDeclarations :=
  fun a => Fin.elim0 a.2.1

def transportedPre : Coord [⟨51, 0⟩] → ℚ :=
  fun p => producerStore
    ⟨(emptyBoundary.matched ⟨emptyConsumerPre, rfl⟩).val,
      (emptyBoundary.domain ⟨emptyConsumerPre, rfl⟩).coord p⟩

def consumerInput : emptyConsumer.Input :=
  ⟨fun t => if t == emptyConsumerPre then some transportedPre else none,
    by intro t; fin_cases t <;> rfl⟩

def consumerStore : Store RationalReference.Carrier emptyConsumerDeclarations :=
  fun a => Fin.elim0 a.2.1

theorem producer_input_present :
    emptyValidatedInput.val emptyExternalInput =
      some (fun p => Fin.elim0 p.1) := rfl

theorem lifted_input_present :
    liftedInput (.inl emptyExternalInput) =
      some (fun p => Fin.elim0 p.1) := rfl

theorem transported_input_present :
    consumerInput.val emptyConsumerPre = some transportedPre := rfl

theorem missing_not_valid : ¬ emptyProducer.ValidInput emptyMissingInput := by
  intro valid
  have present := valid emptyExternalInput
  exact Bool.noConfusion present

theorem producer_model :
    emptyProducerComponent.program.Models RationalReference.ops
      emptyValidatedInput producerStore := by
  refine ⟨?_, ?_, ?_⟩
  · intro t o
    exact Fin.elim0 o.1
  · intro t f present p
    exact Fin.elim0 p.1
  · intro t p
    exact Fin.elim0 p.1

theorem consumer_model :
    emptyConsumerComponent.program.Models RationalReference.ops
      consumerInput consumerStore := by
  refine ⟨?_, ?_, ?_⟩
  · intro t o
    exact Fin.elim0 o.1
  · intro t f present p
    exact Fin.elim0 p.1
  · intro t p
    exact Fin.elim0 p.1

theorem output_roles_and_identity :
    emptyProducerComponent.program.output emptyProducerPre = true ∧
      emptyConsumerComponent.program.output emptyConsumerOut = true ∧
      emptyProducerDeclarations.uid emptyProducerPre = 0 ∧
      emptyConsumerDeclarations.uid emptyConsumerOut = 1 := by
  decide +kernel

end Empty

namespace Axis

open IndexedComponentCompositionAxisFixtures
open IndexedComponentTransportTest (srcShape dstShape p q)

def producerInput : producer.Input :=
  ⟨fun _ => none, by intro t; rfl⟩

def producerStore : Store RationalReference.Carrier producerDeclarations :=
  fun a => ((canonicalLayout dstShape).enumerate.symm a.2).val + 1

theorem producer_admitted : producer.AdmEnv RationalReference.ops producerStore := by
  rintro ⟨t, ht⟩ ⟨s, ⟨v, hv⟩⟩
  fin_cases t
  fin_cases s <;> fin_cases v <;> rfl

theorem producer_model :
    axisProducer.program.Models RationalReference.ops producerInput producerStore := by
  refine ⟨producer_admitted, ?_, ?_⟩
  · intro t f present
    contradiction
  · rintro ⟨t, ht⟩ ⟨i, j, ⟨⟩⟩
    fin_cases t
    fin_cases i <;> fin_cases j <;> decide +kernel +revert

def transportedPre : Coord srcShape → ℚ :=
  fun c => producerStore
    ⟨(axisBoundary.matched ⟨0, rfl⟩).val, (axisBoundary.domain ⟨0, rfl⟩).coord c⟩

def consumerInput : consumer.Input :=
  ⟨fun t => if h : t = 0 then by subst t; exact some transportedPre else none,
    by intro t; fin_cases t <;> rfl⟩

def consumerStore : Store RationalReference.Carrier consumerDeclarations :=
  fun ⟨t, c⟩ => if h : t = 0 then transportedPre (by subst t; exact c) else 14

theorem consumer_admitted : consumer.AdmEnv RationalReference.ops consumerStore := by
  rintro ⟨t, ht⟩ ⟨s, ⟨v, hv⟩⟩
  fin_cases t
  · contradiction
  · fin_cases s
    fin_cases v
    decide +kernel +revert

theorem consumer_model :
    axisConsumer.program.Models RationalReference.ops consumerInput consumerStore := by
  refine ⟨consumer_admitted, ?_, ?_⟩
  · intro t f present c
    fin_cases t
    · have hf : transportedPre = f := Option.some.inj present
      subst f
      rfl
    · contradiction
  · rintro ⟨t, ht⟩ c
    fin_cases t
    · contradiction
    · cases c
      decide +kernel +revert

theorem producer_statement_values :
    (List.finRange 6).map (fun i => producerStore ⟨0, producerCoord i⟩) =
      [1, 2, 3, 4, 5, 6] := by
  decide +kernel

theorem transported_input_present :
    consumerInput.val 0 = some transportedPre := rfl

theorem transported_distinguishing_values :
    transportedPre p = 5 ∧ transportedPre q = 2 ∧
      transportedPre (0, 0, ()) = 1 ∧ transportedPre (1, 2, ()) = 6 := by
  decide +kernel

theorem consumer_values :
    consumerStore ⟨0, p⟩ = 5 ∧ consumerStore ⟨0, q⟩ = 2 ∧
      consumerStore ⟨1, ()⟩ = 14 := by
  decide +kernel

def flattenedPre : Coord srcShape → ℚ :=
  fun c => producerStore
    ⟨0, (canonicalLayout dstShape).enumerate
      ((canonicalLayout srcShape).enumerate.symm c)⟩

theorem flattened_distinguishing_values :
    flattenedPre p = 3 ∧ flattenedPre q = 4 := by
  decide +kernel

theorem coordinate_transport_distinct : flattenedPre ≠ transportedPre := by
  intro equal
  have atP := congrFun equal p
  rw [flattened_distinguishing_values.1, transported_distinguishing_values.1] at atP
  norm_num at atP

theorem selected_sum_does_not_distinguish :
    transportedPre p + (transportedPre q + (transportedPre p + transportedPre q)) = 14 ∧
      flattenedPre p + (flattenedPre q + (flattenedPre p + flattenedPre q)) = 14 := by
  decide +kernel

end Axis

#eval ((Empty.liftedInput (.inl
    IndexedComponentCompositionPortFixtures.emptyExternalInput)).isSome,
  (Empty.consumerInput.val
    IndexedComponentCompositionPortFixtures.emptyConsumerPre).isSome)

#eval ((List.finRange 6).map
    (fun i => Axis.producerStore ⟨0, IndexedComponentCompositionAxisFixtures.producerCoord i⟩),
  (Axis.transportedPre IndexedComponentTransportTest.p,
    Axis.transportedPre IndexedComponentTransportTest.q),
  (Axis.flattenedPre IndexedComponentTransportTest.p,
    Axis.flattenedPre IndexedComponentTransportTest.q),
  Axis.consumerStore ⟨1, ()⟩)

#print axioms Empty.producer_model
#print axioms Empty.consumer_model
#print axioms Axis.producer_model
#print axioms Axis.consumer_model
#print axioms Axis.coordinate_transport_distinct

end IndexedComponentModelGeometryFixtures
