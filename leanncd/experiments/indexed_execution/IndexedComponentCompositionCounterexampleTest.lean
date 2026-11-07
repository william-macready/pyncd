import IndexedComponentCompositionAssemble
import IndexedComponentCompositionPortFixtures
import IndexedComponentCompositionCollisionFixtures

namespace IndexedComponentCompositionCounterexampleTest

open LeanNCD.Semantics
open IndexedOpenComposition
open IndexedComponentTransport
open IndexedComponentComposition
open IndexedComponentCompositionPortFixtures

abbrev D := declarations producerComponent (consumerComponent 0)

def shortcut : Body D :=
  transport (downstream producerComponent (consumerComponent 0) (scalarBoundary 0)) id
    ((IndexedCompositionParityTest.graphShortcut.writers.get
      ⟨3, by simp [IndexedCompositionParityTest.graphShortcut]⟩).body)

def shortcutFragment : Fragment D :=
  ⟨(fragment producerComponent (consumerComponent 0) (scalarBoundary 0)).writers.map
    (fun w => if w.tag == 61 then { w with body := shortcut } else w)⟩

def observations : String × Nat × String × Nat × Option (List (Option ℚ)) :=
  let original := runChecked
    (contract producerComponent (consumerComponent 0) (scalarBoundary 0))
    (fragment producerComponent (consumerComponent 0) (scalarBoundary 0)) (fun _ => none)
  let altered := runChecked
    (contract producerComponent (consumerComponent 0) (scalarBoundary 0))
    shortcutFragment (fun _ => none)
  (original.outcome.kind, original.events.length, altered.outcome.kind, altered.events.length,
    altered.states.getLast?.map (fun s =>
      [s.available ⟨.inl 0, ()⟩,
        s.available ⟨.inr ⟨1, rfl⟩, ()⟩,
        s.available ⟨.inr ⟨2, rfl⟩, ()⟩]))

#eval IndexedCompositionParityTest.check "composite-private-shortcut-is-not-equivalent"
  observations ("failed", 6, "complete", 7, some [some 0, some 0, some (1 / 2)])

abbrev CollisionD := declarations
  IndexedComponentCompositionCollisionFixtures.collisionProducer
  IndexedComponentCompositionCollisionFixtures.collisionConsumer

def omittedCapability : Nat := 204

def omittedContract : Contract CollisionD :=
  { IndexedComponentCompositionCollisionFixtures.collisionContract with
    collectors :=
      IndexedComponentCompositionCollisionFixtures.collisionContract.collectors.map
        (fun row => (row.1, row.2.filter (fun cap => cap != omittedCapability))) }

def omittedFragment : Fragment CollisionD :=
  ⟨IndexedComponentCompositionCollisionFixtures.collisionFragment.writers.filter
    (fun w => w.capability != omittedCapability)⟩

def omissionObservations : String × Nat × Option (List (Option ℚ)) :=
  let altered := runChecked omittedContract omittedFragment (fun _ => none)
  (altered.outcome.kind, altered.events.length, altered.states.getLast?.map (fun s =>
    [s.available ⟨.inl 0, ()⟩, s.available ⟨.inl 1, ()⟩,
      s.available ⟨.inr ⟨1, rfl⟩, ()⟩, s.available ⟨.inr ⟨2, rfl⟩, ()⟩]))

#eval IndexedCompositionParityTest.check "composite-equal-contribution-omission-changes-result"
  omissionObservations ("complete", 8, some [some 1, some 7, some 1, some (3 / 2)])

#eval IndexedCompositionParityTest.check "composite-zero-collector-drop-is-rejected"
  (let original := contract zeroProducerComponent (consumerComponent 4) zeroBoundary
   let altered := { original with
     collectors := original.collectors.filter (fun row => !row.2.isEmpty) }
   match close altered (fragment zeroProducerComponent (consumerComponent 4) zeroBoundary) with
   | .error .missingCollector => true
   | _ => false)
  true

#eval IndexedCompositionParityTest.check "composite-duplicate-boundary-collector-is-rejected"
  (let original := contract producerComponent (consumerComponent 0) (scalarBoundary 0)
   let altered := { original with collectors := original.collectors ++ original.collectors.take 1 }
   match close altered (fragment producerComponent (consumerComponent 0) (scalarBoundary 0)) with
   | .error .duplicateCollector => true
   | _ => false)
  true

end IndexedComponentCompositionCounterexampleTest
