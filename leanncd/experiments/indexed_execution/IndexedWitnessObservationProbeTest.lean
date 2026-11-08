import IndexedWitnessObservationProbe
import IndexedWitnessCompositionTest
import IndexedWitnessPartialTest
import Semantics.AxiomAudit

namespace IndexedWitnessObservationProbeTest

open LeanNCD.Semantics IndexedComponentComposition IndexedWitness
open IndexedWitnessObservationProbe
open IndexedWitnessCompositionTest

namespace Hidden

open IndexedComponentModelCycleFixtures

-- The copied decomposition retains production proof-carrying compatibility.
def zeroWired := toWiredCopy hiddenUpstream totalDownstream hiddenBoundary
  IndexedWitnessCompositionTest.Hidden.zero
def oneWired := toWiredCopy hiddenUpstream totalDownstream hiddenBoundary
  IndexedWitnessCompositionTest.Hidden.one

theorem cells :
    zeroWired.val.1.val.1.2.val ⟨privateTensor, ()⟩ = 0 ∧
      oneWired.val.1.val.1.2.val ⟨privateTensor, ()⟩ = 1 ∧
      (componentSpanCopy totalDownstream).right zeroWired.val.2
        ⟨boundaryTensor, rfl⟩ () = 1 ∧
      (componentSpanCopy totalDownstream).right oneWired.val.2
        ⟨boundaryTensor, rfl⟩ () = 1 := by
  decide +kernel

theorem distinct : zeroWired ≠ oneWired := by
  intro h
  have he := congrArg
    (fun w : (wiredSpan hiddenUpstream totalDownstream hiddenBoundary).W =>
      w.val.1.val.1.2.val ⟨privateTensor, ()⟩) h
  change zeroWired.val.1.val.1.2.val ⟨privateTensor, ()⟩ =
    oneWired.val.1.val.1.2.val ⟨privateTensor, ()⟩ at he
  rw [cells.1, cells.2.1] at he
  norm_num at he

theorem equal_output :
    (componentSpanCopy totalDownstream).right zeroWired.val.2 =
      (componentSpanCopy totalDownstream).right oneWired.val.2 := by
  funext t c
  rcases t with ⟨t, ht⟩
  fin_cases t
  · contradiction
  · cases c; exact cells.2.2.1.trans cells.2.2.2.symm

-- A singleton restriction of a real total model, NOT whole-component injectivity.
def goodSpan : Span (inputInterface totalDownstream) (outputInterface totalDownstream) where
  W := Unit
  left := fun _ => (componentSpanCopy totalDownstream).left oneWired.val.2
  right := fun _ => (componentSpanCopy totalDownstream).right oneWired.val.2

theorem good_injective : Function.Injective goodSpan.left := by
  intro a b _
  change Unit at a b
  exact Subsingleton.elim a b

theorem good_option :
    goodSpan.partialOption good_injective (goodSpan.left ()) =
      some (goodSpan.right ()) := by
  classical
  have hx : goodSpan.Domain (goodSpan.left ()) := ⟨(), rfl⟩
  simp only [Span.partialOption, dif_pos hx]
  rw [Span.value_at]

theorem good_option_cell :
    Option.map (fun env => env ⟨boundaryTensor, rfl⟩ ())
      (goodSpan.partialOption good_injective (goodSpan.left ())) = some 1 := by
  rw [good_option]
  decide +kernel

end Hidden

namespace Audit

open IndexedComponentCompositionPortFixtures IndexedComponentModelLocalFixtures

-- This absence check is a donor/consumer theorem, not a copied numeric defect.
theorem strict_empty : IsEmpty (componentSpanCopy IndexedWitnessCompositionTest.Audit.strict).W :=
  IndexedWitnessCompositionTest.Audit.strict_span_empty

theorem total_cells :
    IndexedWitnessCompositionTest.Audit.totalWired.val.2.2.val ⟨strictAudit, ()⟩ = 1 / 2 ∧
      (componentSpanCopy (consumerComponent 4)).right
        IndexedWitnessCompositionTest.Audit.totalWired.val.2 ⟨consumerOut, rfl⟩ () = 0 := by
  decide +kernel

theorem strict_none (x : (inputInterface (consumerComponent 0)).Env) :
    (componentSpan (consumerComponent 0)).partialOption
      ((component_injective_iff (consumerComponent 0)).2
        IndexedWitnessPartialTest.strict_consumer_atMostOne) x = none :=
  IndexedWitnessPartialTest.strict_consumer_undefined x

end Audit

namespace Empty

open IndexedComponentCompositionPortFixtures

noncomputable def outputCopy := roleInterfaceCopy
  IndexedWitnessCompositionTest.Empty.composite.program.output

theorem metadata :
    outputCopy.uid IndexedWitnessCompositionTest.Empty.outputPort = 3 ∧
      (outputCopy.signature IndexedWitnessCompositionTest.Empty.outputPort).axes = [⟨51, 0⟩] := by
  decide +kernel

theorem present :
    IndexedWitnessCompositionTest.Empty.outputPort ∈ outputCopy.ports :=
  outputCopy.ports_complete _

theorem singleton : Subsingleton outputCopy.Env :=
  IndexedWitnessCompositionTest.Empty.env_singleton

theorem metadata_distinct :
    outputInterface emptyProducerComponent ≠ outputCopy :=
  IndexedWitnessCompositionTest.Empty.metadata_not_equal

theorem empty_input_present :
    ((envInputCopy emptyProducerComponent
      (inputEnv emptyProducerComponent emptyValidatedInput)).val emptyExternalInput).isSome = true := by
  decide +kernel

end Empty

namespace Axis

open IndexedComponentCompositionAxisFixtures
open IndexedComponentTransportTest (p q)

theorem boundary_cells :
    boundaryEnvEquivCopy axisProducer axisConsumer axisBoundary
      IndexedWitnessCompositionTest.Axis.sourceEnv ⟨0, rfl⟩ p = 5 ∧
      boundaryEnvEquivCopy axisProducer axisConsumer axisBoundary
        IndexedWitnessCompositionTest.Axis.sourceEnv ⟨0, rfl⟩ q = 2 ∧
      IndexedComponentModelGeometryFixtures.Axis.flattenedPre p = 3 ∧
      IndexedComponentModelGeometryFixtures.Axis.flattenedPre q = 4 ∧
      IndexedWitnessCompositionTest.Axis.wrongReversed ⟨0, rfl⟩ p = 4 ∧
      IndexedWitnessCompositionTest.Axis.wrongReversed ⟨0, rfl⟩ q = 3 := by
  decide +kernel

theorem external_copy_cells :
    compositeOutputEquivCopy axisProducer axisConsumer axisBoundary
        ((componentSpanCopy IndexedWitnessCompositionTest.Axis.composite).right
          IndexedWitnessCompositionTest.Axis.witness) ⟨1, rfl⟩ () = 14 := by
  decide +kernel

end Axis

namespace Triple

open IndexedWitnessCompositionTest.Triple
open IndexedComponentTransportTest (p q swapDomain)

theorem input_copy_cells :
    ((envInputCopy A (inputEnv A aInput)).val 0).get
        (by decide +kernel) p = 5 ∧
      ((envInputCopy A (inputEnv A aInput)).val 0).get
        (by decide +kernel) q = 2 ∧
      compositeInputEquivCopy A B ab (inputEnv A aInput) ⟨.inl 0, rfl⟩ p = 5 := by
  decide +kernel

theorem copied_boundaries :
    boundaryEnvEquivCopy A B ab ((componentSpanCopy A).right aWitness)
        ⟨0, rfl⟩ (swapDomain.coord p) = 15 ∧
      boundaryEnvEquivCopy A B ab ((componentSpanCopy A).right aWitness)
        ⟨0, rfl⟩ (swapDomain.coord q) = 12 ∧
      boundaryEnvEquivCopy B C bc ((componentSpanCopy B).right bWitness)
        ⟨0, rfl⟩ p = 35 ∧
      boundaryEnvEquivCopy B C bc ((componentSpanCopy B).right bWitness)
        ⟨0, rfl⟩ q = 32 := by
  decide +kernel

theorem original_final :
    (componentSpanCopy A).left aWitness ⟨0, rfl⟩ p = 5 ∧
      (componentSpanCopy A).left aWitness ⟨0, rfl⟩ q = 2 ∧
      (componentSpanCopy C).right cWitness ⟨1, rfl⟩ () = 134 := by
  decide +kernel

-- Both bracketing stores are donor/consumer checks, not copied coherence laws.
def leftStore := leftWitness.2.val
def rightStore := rightWitness.2.val

theorem private_stores :
    leftStore ⟨.inl (.inl 1), p⟩ = 15 ∧
      leftStore ⟨.inl (.inr ⟨1, rfl⟩), swapDomain.coord p⟩ = 35 ∧
      leftStore ⟨.inr ⟨1, rfl⟩, ()⟩ = 134 ∧
      rightStore ⟨.inl 1, p⟩ = 15 ∧
      rightStore ⟨.inr ⟨.inl 1, rfl⟩, swapDomain.coord p⟩ = 35 ∧
      rightStore ⟨.inr ⟨.inr ⟨1, rfl⟩, rfl⟩, ()⟩ = 134 := by
  decide +kernel

def leftUid := (declarations (compose A B ab) C).uid
def rightUid := (declarations A (compose B C bc)).uid

theorem unequal_raw_ids :
    leftUid (.inl (.inl 1)) = 164 ∧ rightUid (.inl 1) = 82 ∧
      leftUid (.inl (.inl 1)) ≠ rightUid (.inl 1) ∧
      leftUid (.inr ⟨1, rfl⟩) = 3 ∧ rightUid (.inr ⟨.inr ⟨1, rfl⟩, rfl⟩) = 7 := by
  decide +kernel

end Triple

#audit_axioms IndexedWitnessObservationProbe
#audit_axioms IndexedWitnessObservationProbeTest

end IndexedWitnessObservationProbeTest
