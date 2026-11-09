import IndexedRankedExecutionSemantics
import IndexedComponentRankedExecutionRankTest

namespace IndexedComponentRankedExecutionTest

open LeanNCD.Semantics
open IndexedOpenComposition
open IndexedComponentComposition
open IndexedComponentExecution
open IndexedComponentRankedExecutionFixtures
open IndexedComponentCompositionPortFixtures
open IndexedComponentCompositionLocalFixtures

def producerInput : producer.Input :=
  ⟨fun _ => none, by intro t; rfl⟩

def zeroProducerInput : zeroProducer.Input :=
  ⟨fun _ => none, by intro t; rfl⟩

def zeroProducerRank : zeroProducer.RankCertificate where
  rank := fun _ => 0
  decreases := by
    rintro a b ⟨t, o, _, _⟩
    exact Fin.elim0 o.1

def private_phases (upstreamOther downstreamOther : ℚ) :=
  compose_default_phases (consumerComponent upstreamOther) (consumerComponent downstreamOther)
    (privateBoundary upstreamOther downstreamOther) (privateInput upstreamOther)
    (consumerRank upstreamOther) (consumerRank downstreamOther)

def collection_phases (other : ℚ) :=
  compose_default_phases producerComponent (consumerComponent other) (scalarBoundary other)
    producerInput producerRank (consumerRank other)

def zero_phases :=
  compose_default_phases zeroProducerComponent (consumerComponent 4) zeroBoundary
    zeroProducerInput zeroProducerRank (consumerRank 4)

def empty_phases :=
  compose_default_phases emptyProducerComponent emptyConsumerComponent emptyBoundary
    emptyValidatedInput emptyProducerRank emptyConsumerRank

def axisInput : IndexedComponentCompositionAxisFixtures.axisProducer.program.Input :=
  ⟨fun _ => none, by intro t; rfl⟩

def axis_phases :=
  compose_default_phases IndexedComponentCompositionAxisFixtures.axisProducer
    IndexedComponentCompositionAxisFixtures.axisConsumer
    IndexedComponentCompositionAxisFixtures.axisBoundary axisInput
    IndexedComponentRankedExecutionRankTest.Axis.producerRank
    IndexedComponentRankedExecutionRankTest.Axis.consumerRank

def collisionInput :
    IndexedComponentCompositionCollisionFixtures.collisionProducer.program.Input :=
  ⟨fun _ => none, by intro t; rfl⟩

def collision_phases :=
  compose_default_phases IndexedComponentCompositionCollisionFixtures.collisionProducer
    IndexedComponentCompositionCollisionFixtures.collisionConsumer
    IndexedComponentCompositionCollisionFixtures.collisionBoundary collisionInput
    IndexedComponentRankedExecutionRankTest.Collision.producerRank
    IndexedComponentRankedExecutionRankTest.Collision.consumerRank

def private_reference_phases (upstreamOther downstreamOther : ℚ) :=
  reference_default_phases (consumerComponent upstreamOther) (consumerComponent downstreamOther)
    (privateBoundary upstreamOther downstreamOther) (privateInput upstreamOther)
    (consumerRank upstreamOther) (consumerRank downstreamOther)

def collection_reference_phases (other : ℚ) :=
  reference_default_phases producerComponent (consumerComponent other) (scalarBoundary other)
    producerInput producerRank (consumerRank other)

def zero_reference_phases :=
  reference_default_phases zeroProducerComponent (consumerComponent 4) zeroBoundary
    zeroProducerInput zeroProducerRank (consumerRank 4)

def empty_reference_phases :=
  reference_default_phases emptyProducerComponent emptyConsumerComponent emptyBoundary
    emptyValidatedInput emptyProducerRank emptyConsumerRank

def axis_reference_phases :=
  reference_default_phases IndexedComponentCompositionAxisFixtures.axisProducer
    IndexedComponentCompositionAxisFixtures.axisConsumer
    IndexedComponentCompositionAxisFixtures.axisBoundary axisInput
    IndexedComponentRankedExecutionRankTest.Axis.producerRank
    IndexedComponentRankedExecutionRankTest.Axis.consumerRank

def collision_reference_phases :=
  reference_default_phases IndexedComponentCompositionCollisionFixtures.collisionProducer
    IndexedComponentCompositionCollisionFixtures.collisionConsumer
    IndexedComponentCompositionCollisionFixtures.collisionBoundary collisionInput
    IndexedComponentRankedExecutionRankTest.Collision.producerRank
    IndexedComponentRankedExecutionRankTest.Collision.consumerRank

end IndexedComponentRankedExecutionTest
