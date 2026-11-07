import IndexedComponentCompositionLocalFixtures
import IndexedComponentTransportTest

namespace IndexedComponentCompositionInterfaceTest

open LeanNCD.Semantics
open IndexedComponentTransport
open IndexedComponentCompositionLocalFixtures

example : (consumer 4).Defined := ⟨1, rfl⟩

theorem input_not_a_downstream_destination (t : (consumer 4).Defined) :
    t.val ≠ (0 : Fin 3) := by
  intro h
  have hp := t.property
  rw [h] at hp
  exact Bool.noConfusion hp

example : Nonempty (Domain IndexedComponentTransportTest.srcShape
    IndexedComponentTransportTest.dstShape) :=
  ⟨IndexedComponentTransportTest.swapDomain⟩

example : (canonicalLayout IndexedComponentTransportTest.srcShape).count = 6 ∧
    (canonicalLayout [⟨88, 6⟩]).count = 6 := ⟨rfl, rfl⟩

theorem equal_cardinality_is_not_an_axis_adapter :
    ¬ Nonempty (Domain IndexedComponentTransportTest.srcShape [⟨88, 6⟩]) := by
  rintro ⟨adapter⟩
  have h := Fintype.card_congr adapter.axes
  simp [IndexedComponentTransportTest.srcShape] at h

end IndexedComponentCompositionInterfaceTest
