import IndexedComponentCompositionPortFixtures
import LeanNCD.Semantics.Models

namespace IndexedComponentModelLocalFixtures

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedComponentCompositionLocalFixtures
open IndexedComponentCompositionPortFixtures

def producerInput : producer.Input :=
  ⟨fun _ => none, by intro _; rfl⟩

def producerStore : Store RationalReference.Carrier producerDeclarations := fun _ => 0

theorem producer_model : producer.Models RationalReference.ops producerInput producerStore := by
  refine ⟨?_, ?_, ?_⟩
  · intro t o
    rcases o with ⟨s, v⟩
    fin_cases s <;> rfl
  · intro t f present
    contradiction
  · rintro ⟨t, ht⟩ p
    fin_cases t
    cases p
    decide +kernel +revert

def totalStore : Store RationalReference.Carrier consumerDeclarations :=
  fun a => if a.1 == strictAudit then 1 / 2 else 0

def consumerInput (other : ℚ) : (consumer other).Input :=
  ⟨fun t => if t == consumerPre then some (fun _ => 0) else none, by
    intro t
    fin_cases t <;> rfl⟩

theorem total_model :
    (consumer 4).Models RationalReference.ops (consumerInput 4) totalStore := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨t, ht⟩ ⟨s, v⟩
    fin_cases t
    · contradiction
    · norm_num [outcome, consumer, interpret, evalWith,
        IndexedCompositionParityTest.squareBody, IndexedCompositionParityTest.readScalar,
        LeanNCD.Semantics.sequence, Registry.apply, RationalReference.registry]
    · change ((consumer 4).outcome RationalReference.ops totalStore
        ⟨strictAudit, rfl⟩ ⟨s, v⟩).isSome = true
      decide +kernel +revert
  · intro t f present p
    fin_cases t
    · have hf : (fun _ : Coord [] => (0 : ℚ)) = f := Option.some.inj present
      subst f
      rfl
    · contradiction
    · contradiction
  · rintro ⟨t, ht⟩ p
    cases p
    fin_cases t
    · contradiction
    · decide +kernel +revert
    · decide +kernel +revert

theorem strict_audit_undefined (ρ : Store RationalReference.Carrier consumerDeclarations) :
    (consumer 0).outcome RationalReference.ops ρ
      ⟨strictAudit, rfl⟩ ⟨0, ⟨0, rfl⟩⟩ = none := by
  have tab : interpret RationalReference.ops ρ
      (IndexedCompositionParityTest.strictArray 0 Unit) () = none := by
    change interpret RationalReference.ops totalStore
      (IndexedCompositionParityTest.strictArray 0 Unit) () = none
    decide +kernel
  change ((some (ρ ⟨0, ()⟩)).bind fun x =>
    ((interpret RationalReference.ops ρ
      (IndexedCompositionParityTest.strictArray 0 Unit) ()).bind fun xs =>
        some (xs (Plan.ScanHistory.stateCoord (d := 2) 0))).bind fun y =>
          some (x + y)) = none
  rw [tab]
  rfl

theorem strict_no_model (ρ : Store RationalReference.Carrier consumerDeclarations) :
    ¬ (consumer 0).Models RationalReference.ops (consumerInput 0) ρ := by
  rintro ⟨adm, _, _⟩
  have audit := adm ⟨strictAudit, rfl⟩ ⟨0, ⟨0, rfl⟩⟩
  rw [strict_audit_undefined] at audit
  contradiction

theorem strict_out_equation :
    (consumer 0).outcome RationalReference.ops totalStore
      ⟨consumerOut, rfl⟩ ⟨0, ⟨0, rfl⟩⟩ = some 0 := by
  norm_num [outcome, consumer, consumerOut, interpret, evalWith,
    IndexedCompositionParityTest.squareBody, IndexedCompositionParityTest.readScalar,
    LeanNCD.Semantics.sequence, Registry.apply, RationalReference.registry, totalStore, strictAudit]
  decide

theorem zero_producer_model :
    zeroProducer.Models RationalReference.ops
      ⟨fun _ => none, by intro _; rfl⟩ producerStore := by
  refine ⟨?_, ?_, ?_⟩
  · intro t o
    exact Fin.elim0 o.1
  · intro t f present
    contradiction
  · rintro ⟨t, ht⟩ p
    fin_cases t
    cases p
    simp [collect, pushforward, zeroProducer, producerStore]

theorem zero_producer_forces_zero (η : zeroProducer.Input)
    (ρ : Store RationalReference.Carrier producerDeclarations)
    (model : zeroProducer.Models RationalReference.ops η ρ) :
    ρ ⟨producerPre, ()⟩ = 0 := by
  rcases model with ⟨adm, _, equations⟩
  have eq := equations ⟨producerPre, rfl⟩ ()
  simpa [collect, pushforward, zeroProducer] using eq

#eval (producerStore ⟨producerPre, ()⟩,
  totalStore ⟨consumerPre, ()⟩, totalStore ⟨consumerOut, ()⟩,
  totalStore ⟨strictAudit, ()⟩)

end IndexedComponentModelLocalFixtures
