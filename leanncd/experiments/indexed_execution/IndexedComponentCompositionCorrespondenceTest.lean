import IndexedComponentComposition
import IndexedComponentCompositionTest
import IndexedComponentCompositionCollisionFixtures
import IndexedComponentCompositionAxisFixtures
import IndexedCompositionValidated

namespace IndexedComponentCompositionCorrespondenceTest

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedComponentComposition
open IndexedComponentCompositionPortFixtures
open IndexedOpenComposition.Correspondence

def scalarMatch (other : ℚ) :=
  compose_match producerComponent (consumerComponent other) (scalarBoundary other)

def zeroMatch := compose_match zeroProducerComponent (consumerComponent 4) zeroBoundary

def emptyMatch := compose_match emptyProducerComponent emptyConsumerComponent emptyBoundary

def collisionMatch :=
  compose_match IndexedComponentCompositionCollisionFixtures.collisionProducer
    IndexedComponentCompositionCollisionFixtures.collisionConsumer
    IndexedComponentCompositionCollisionFixtures.collisionBoundary

def axisMatch :=
  compose_match IndexedComponentCompositionAxisFixtures.axisProducer
    IndexedComponentCompositionAxisFixtures.axisConsumer
    IndexedComponentCompositionAxisFixtures.axisBoundary

theorem strict_correspondence : ValidatedCorrespondence (scalarMatch 0) (fun _ => none) :=
  default_run_correspondence (scalarMatch 0) (fun _ => none)

theorem total_correspondence : ValidatedCorrespondence (scalarMatch 4) (fun _ => none) :=
  default_run_correspondence (scalarMatch 4) (fun _ => none)

theorem zero_correspondence : ValidatedCorrespondence zeroMatch (fun _ => none) :=
  default_run_correspondence zeroMatch (fun _ => none)

theorem empty_correspondence
    (binding : InputBinding (K := RationalReference.Carrier)
      (σ := declarations emptyProducerComponent emptyConsumerComponent)) :
    ValidatedCorrespondence emptyMatch binding :=
  default_run_correspondence emptyMatch binding

theorem collision_correspondence : ValidatedCorrespondence collisionMatch (fun _ => none) :=
  default_run_correspondence collisionMatch (fun _ => none)

theorem axis_correspondence : ValidatedCorrespondence axisMatch (fun _ => none) :=
  default_run_correspondence axisMatch (fun _ => none)

end IndexedComponentCompositionCorrespondenceTest
