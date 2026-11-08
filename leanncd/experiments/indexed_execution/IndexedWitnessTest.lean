import IndexedWitnessSpan
import IndexedComponentCompositionPortFixtures
import IndexedComponentModelCycleFixtures
import Semantics.AxiomAudit

namespace IndexedWitnessTest

open LeanNCD.Semantics
open IndexedWitness
open IndexedComponentCompositionPortFixtures
open IndexedComponentModelCycleFixtures
open CategoryTheory

example : Category.{1} WholeInterface := inferInstance

example (X Y : WholeInterface) (f : X ⟶ Y) : (𝟙 X) ≫ f = f := Category.id_comp f
example (X Y : WholeInterface) (f : X ⟶ Y) : f ≫ (𝟙 Y) = f := Category.comp_id f
example (W X Y Z : WholeInterface) (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) : (f ≫ g) ≫ h = f ≫ (g ≫ h) := Category.assoc f g h

def emptyInputEnv : (inputInterface emptyProducerComponent).Env :=
  fun _ p => Fin.elim0 p.1

example : (((inputEquiv emptyProducerComponent) emptyInputEnv).val
    emptyExternalInput).isSome = true :=
  ((inputEquiv emptyProducerComponent) emptyInputEnv).property emptyExternalInput

example : (((inputEquiv emptyProducerComponent) emptyInputEnv).val
    emptyExternalInput) ≠ none := by
  intro h
  have hp := ((inputEquiv emptyProducerComponent) emptyInputEnv).property
    emptyExternalInput
  rw [h] at hp
  exact Bool.noConfusion hp

def hiddenZero : (componentSpan hiddenUpstream).W :=
  ⟨upstreamInput true, ⟨scalarStore 0 0, upstream_model true 0 (Or.inl rfl)⟩⟩

def hiddenOne : (componentSpan hiddenUpstream).W :=
  ⟨upstreamInput true, ⟨scalarStore 1 0, upstream_model true 1 (Or.inr rfl)⟩⟩

theorem hidden_witnesses_distinct : hiddenZero ≠ hiddenOne := by
  intro h
  exact hiddenStore_distinct
    (congrArg (fun w : (componentSpan hiddenUpstream).W => w.2.val) h)

theorem hidden_outputs_equal :
    (componentSpan hiddenUpstream).right hiddenZero =
      (componentSpan hiddenUpstream).right hiddenOne :=
  congrArg (outputEquiv hiddenUpstream).symm hidden_boundary_equal

#audit_axioms IndexedWitness
#audit_axioms IndexedWitnessTest

#print axioms IndexedWitness.inputEquiv
#print axioms IndexedWitness.SpanIso.pullback
#print axioms IndexedWitness.SpanIso.assoc
#print axioms IndexedWitness.homComp
#print axioms IndexedWitness.SpanIso.leftUnit
#print axioms IndexedWitness.componentSpan

end IndexedWitnessTest
