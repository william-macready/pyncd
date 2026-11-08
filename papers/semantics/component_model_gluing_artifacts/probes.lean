import IndexedComponentModelTest

open LeanNCD.Semantics
open IndexedComponentComposition
open IndexedComponentCompositionPortFixtures
open IndexedComponentModelCycleFixtures
open IndexedComponentModelCycleTest

#eval ((liftInput emptyProducerComponent emptyConsumerComponent emptyBoundary
  emptyValidatedInput).val (.inl emptyExternalInput)).isSome
#eval ((boundaryInput emptyProducerComponent emptyConsumerComponent emptyBoundary
  IndexedComponentModelGeometryFixtures.Empty.producerStore).val emptyConsumerPre).isSome
#eval (cycleOneStore ⟨.inl privateTensor, ()⟩,
  cycleOneStore ⟨.inr ⟨boundaryTensor, rfl⟩, ()⟩)
#eval (hiddenZeroStore ⟨.inl privateTensor, ()⟩,
  hiddenOneStore ⟨.inl privateTensor, ()⟩,
  hiddenZeroStore ⟨.inr ⟨boundaryTensor, rfl⟩, ()⟩,
  hiddenOneStore ⟨.inr ⟨boundaryTensor, rfl⟩, ()⟩)
