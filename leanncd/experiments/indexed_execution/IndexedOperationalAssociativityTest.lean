import IndexedOperationalAssociativity
import IndexedOperationalAssociativityFixtures
import IndexedOperationalRunsPhases
import IndexedOperationalHistoryComposition

namespace IndexedOperationalAssociativityTest

open LeanNCD.Semantics
open IndexedComponentComposition IndexedComponentExecution IndexedWitness
open IndexedOperationalAssociativity IndexedOperationalAssociativityFixtures
open IndexedComponentCompositionPortFixtures IndexedComponentRankedExecutionFixtures

def private_observations (a b c : ℚ) :=
  nested_observations (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c) (privateInput a)
    (consumerRank a) (consumerRank b) (consumerRank c)

def collection_observations :=
  nested_observations producerComponent (consumerComponent 4) (consumerComponent 4)
    (scalarBoundary 4) (privateBoundary 4 4) IndexedComponentRankedExecutionTest.producerInput
    producerRank (consumerRank 4) (consumerRank 4)

def zero_observations :=
  nested_observations zeroProducerComponent (consumerComponent 4) (consumerComponent 4)
    zeroBoundary (privateBoundary 4 4) IndexedComponentRankedExecutionTest.zeroProducerInput
    IndexedComponentRankedExecutionTest.zeroProducerRank (consumerRank 4) (consumerRank 4)

def axis_observations :=
  nested_observations IndexedComponentCompositionAxisFixtures.axisProducer
    IndexedComponentCompositionAxisFixtures.axisConsumer (consumerComponent 4)
    IndexedComponentCompositionAxisFixtures.axisBoundary axisTailBoundary
    IndexedComponentRankedExecutionTest.axisInput
    IndexedComponentRankedExecutionRankTest.Axis.producerRank
    IndexedComponentRankedExecutionRankTest.Axis.consumerRank (consumerRank 4)

def collision_observations :=
  nested_observations IndexedComponentCompositionCollisionFixtures.collisionProducer
    IndexedComponentCompositionCollisionFixtures.collisionConsumer (consumerComponent 4)
    IndexedComponentCompositionCollisionFixtures.collisionBoundary (privateBoundary 4 4)
    IndexedComponentRankedExecutionTest.collisionInput
    IndexedComponentRankedExecutionRankTest.Collision.producerRank
    IndexedComponentRankedExecutionRankTest.Collision.consumerRank (consumerRank 4)

def empty_observations :=
  nested_observations emptyProducerComponent emptyConsumerComponent emptyConsumerComponent
    emptyBoundary emptyTailBoundary emptyValidatedInput
    emptyProducerRank emptyConsumerRank emptyConsumerRank

def private_reference (a b c : ℚ) :=
  IndexedOperationalRuns.nested_reference_runs
    (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c) (privateInput a)

def private_reference_outcomes (a b c : ℚ) :=
  IndexedOperationalRuns.ranked_nested_reference_outcomes
    (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c) (privateInput a)
    (consumerRank a) (consumerRank b) (consumerRank c)

def empty_reference :=
  IndexedOperationalRuns.nested_reference_runs
    emptyProducerComponent emptyConsumerComponent emptyConsumerComponent
    emptyBoundary emptyTailBoundary emptyValidatedInput

def private_phases (a b c : ℚ) :=
  IndexedOperationalRunsPhases.triple_phases
    (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c) (privateInput a)
    (consumerRank a) (consumerRank b) (consumerRank c)

def collection_phases :=
  IndexedOperationalRunsPhases.triple_phases producerComponent
    (consumerComponent 4) (consumerComponent 4)
    (scalarBoundary 4) (privateBoundary 4 4) IndexedComponentRankedExecutionTest.producerInput
    producerRank (consumerRank 4) (consumerRank 4)

def zero_phases :=
  IndexedOperationalRunsPhases.triple_phases zeroProducerComponent
    (consumerComponent 4) (consumerComponent 4)
    zeroBoundary (privateBoundary 4 4) IndexedComponentRankedExecutionTest.zeroProducerInput
    IndexedComponentRankedExecutionTest.zeroProducerRank (consumerRank 4) (consumerRank 4)

def axis_phases :=
  IndexedOperationalRunsPhases.triple_phases
    IndexedComponentCompositionAxisFixtures.axisProducer
    IndexedComponentCompositionAxisFixtures.axisConsumer (consumerComponent 4)
    IndexedComponentCompositionAxisFixtures.axisBoundary axisTailBoundary
    IndexedComponentRankedExecutionTest.axisInput
    IndexedComponentRankedExecutionRankTest.Axis.producerRank
    IndexedComponentRankedExecutionRankTest.Axis.consumerRank (consumerRank 4)

def collision_phases :=
  IndexedOperationalRunsPhases.triple_phases
    IndexedComponentCompositionCollisionFixtures.collisionProducer
    IndexedComponentCompositionCollisionFixtures.collisionConsumer (consumerComponent 4)
    IndexedComponentCompositionCollisionFixtures.collisionBoundary (privateBoundary 4 4)
    IndexedComponentRankedExecutionTest.collisionInput
    IndexedComponentRankedExecutionRankTest.Collision.producerRank
    IndexedComponentRankedExecutionRankTest.Collision.consumerRank (consumerRank 4)

def empty_phases :=
  IndexedOperationalRunsPhases.triple_phases
    emptyProducerComponent emptyConsumerComponent emptyConsumerComponent
    emptyBoundary emptyTailBoundary emptyValidatedInput
    emptyProducerRank emptyConsumerRank emptyConsumerRank

end IndexedOperationalAssociativityTest
