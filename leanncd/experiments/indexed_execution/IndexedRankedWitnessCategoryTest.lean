import IndexedRankedWitnessOutcomeTest

namespace IndexedRankedWitnessCategoryTest

open LeanNCD.Semantics IndexedComponentComposition IndexedWitness CategoryTheory
open IndexedComponentCompositionLocalFixtures IndexedComponentCompositionPortFixtures
open IndexedComponentRankedExecutionFixtures IndexedRankedOperationalCore
open IndexedRankedOperationalCategory IndexedRankedWitnessComparison
open IndexedRankedOperationalTest
namespace RS
export IndexedRankedOperationalSource (arrow assembled pair)
end RS

noncomputable def route {X Y : IndexedRankedOperationalSource.Object}
    (t : IndexedRankedOperationalSource.Term X Y) :=
  (IndexedRankedOperationalSource.semantics ⋙ comparison).map (RS.arrow t)

theorem route_diagram {X Y : IndexedRankedOperationalSource.Object}
    (t : IndexedRankedOperationalSource.Term X Y) :
    route t =     (IndexedRankedWitnessSource.erase ⋙ IndexedSource.semantics).map (RS.arrow t) := by
  have h := Functor.congr_hom IndexedRankedWitnessSource.diagram (RS.arrow t)
  change route t = (𝟙 X.base.interface) ≫
    (IndexedRankedWitnessSource.erase ⋙ IndexedSource.semantics).map (RS.arrow t) ≫
      (𝟙 Y.base.interface) at h
  exact h.trans ((Category.id_comp _).trans (Category.comp_id _))

def cubeTarget : Target := ⟨IndexedRankedOperationalTest.object⟩

theorem identity_image :
    comparison.map (𝟙 cubeTarget) = 𝟙 cubeTarget.interface.interface :=
  comparison.map_id _

theorem rotate_image :
    comparison.map (show cubeTarget ⟶ cubeTarget from Quotient.mk _ (.admin rotate)) =
      graphHom rotate.env := comparison_admin rotate

theorem rotate_composed :
    comparison.map (show cubeTarget ⟶ cubeTarget from
      Quotient.mk _ (.admin (rotate.comp rotate))) =
      graphHom rotate.env ≫ graphHom rotate.env := comparison_wire_comp rotate rotate

theorem rotate_inverse :
    comparison.map (show cubeTarget ⟶ cubeTarget from Quotient.mk _ (.admin rotate.inverse)) =
      graphHom rotate.env.symm := comparison_wire_inverse rotate

def wireImageRow :=
  ((Span.graph rotate.env).left view.env 0 point,
    (Span.graph rotate.env).right view.env 0 point,
    (Span.graph rotate.inverse.env).right view.env 0 point,
    (Span.graph (rotate.comp rotate).env).right view.env 0 point)

#eval wireImageRow
example : wireImageRow = (11, 101, 110, 110) := by decide

noncomputable def binary :=
  RS.assembled (consumerComponent 4) (consumerComponent 4) (privateBoundary 4 4)
    (consumerRank 4) (consumerRank 4) (privateOrigin 4) (privateOrigin 4)

theorem binary_assembly :
    route binary = route (RS.pair (consumerComponent 4) (consumerComponent 4)
      (privateBoundary 4 4) (consumerRank 4) (consumerRank 4)
      (privateOrigin 4) (privateOrigin 4)) :=
  congrArg (IndexedRankedOperationalSource.semantics ⋙ comparison).map
    (IndexedRankedOperationalSource.assembly_eq _ _ _ _ _ _ _)

theorem binary_exterior :
    route binary =
      graphHom (IndexedSource.inputWire (consumerComponent 4) (consumerComponent 4)
        (privateBoundary 4 4)).env ≫
      Quotient.mk _ (componentSpan (privateComposite 4 4)) ≫
      graphHom (IndexedSource.outputWire (consumerComponent 4) (consumerComponent 4)
        (privateBoundary 4 4)).env := by
  rw [route_diagram]
  rfl

theorem binary_composition :
    route binary =
      Quotient.mk _ (componentSpan (consumerComponent 4)) ≫
      graphHom (IndexedSource.boundaryWire (consumerComponent 4) (consumerComponent 4)
        (privateBoundary 4 4)).env ≫ Quotient.mk _ (componentSpan (consumerComponent 4)) := by
  rw [binary_assembly, route_diagram]
  change (Quotient.mk _ (componentSpan (consumerComponent 4)) ≫
    graphHom (IndexedSource.boundaryWire (consumerComponent 4) (consumerComponent 4)
      (privateBoundary 4 4)).env) ≫ Quotient.mk _ (componentSpan (consumerComponent 4)) = _
  exact Category.assoc _ _ _

theorem interior_unit :
    route (privatePairWithUnit 4 4) = route (RS.pair
      (consumerComponent 4) (consumerComponent 4) (privateBoundary 4 4)
      (consumerRank 4) (consumerRank 4) (privateOrigin 4) (privateOrigin 4)) := by
  exact congrArg comparison.map (Quotient.sound (privateInteriorUnit 4 4))

theorem nested_images :
    route (privateLeft 4 4 4) = route (privateRight 4 4 4) :=
  congrArg comparison.map (Quotient.sound (privateReassociation 4 4 4))

theorem left_nested_diagram :
    route (privateLeft 4 4 4) =
      (IndexedRankedWitnessSource.erase ⋙ IndexedSource.semantics).map
        (RS.arrow (privateLeft 4 4 4)) := route_diagram _

theorem right_nested_diagram :
    route (privateRight 4 4 4) =
      (IndexedRankedWitnessSource.erase ⋙ IndexedSource.semantics).map
        (RS.arrow (privateRight 4 4 4)) := route_diagram _

theorem left_nested_exterior :
    route (privateLeft 4 4 4) =
      graphHom (IndexedSource.inputWire (consumerComponent 4) (consumerComponent 4)
        (privateBoundary 4 4)).env ≫
      graphHom (IndexedSource.inputWire (privateComposite 4 4) (consumerComponent 4)
        (leftNestedBoundary (consumerComponent 4) (consumerComponent 4) (consumerComponent 4)
          (privateBoundary 4 4) (privateBoundary 4 4))).env ≫
      Quotient.mk _ (componentSpan (leftBracket (consumerComponent 4) (consumerComponent 4)
        (consumerComponent 4) (privateBoundary 4 4) (privateBoundary 4 4))) ≫
      graphHom (IndexedSource.outputWire (privateComposite 4 4) (consumerComponent 4)
        (leftNestedBoundary (consumerComponent 4) (consumerComponent 4) (consumerComponent 4)
          (privateBoundary 4 4) (privateBoundary 4 4))).env := by
  rw [route_diagram]
  rfl

theorem right_nested_exterior :
    route (privateRight 4 4 4) =
      (graphHom (IndexedSource.inputWire (consumerComponent 4) (privateComposite 4 4)
        (rightNestedBoundary (consumerComponent 4) (consumerComponent 4) (consumerComponent 4)
          (privateBoundary 4 4) (privateBoundary 4 4))).env ≫
      Quotient.mk _ (componentSpan (rightBracket (consumerComponent 4) (consumerComponent 4)
        (consumerComponent 4) (privateBoundary 4 4) (privateBoundary 4 4))) ≫
      graphHom (IndexedSource.outputWire (consumerComponent 4) (privateComposite 4 4)
        (rightNestedBoundary (consumerComponent 4) (consumerComponent 4) (consumerComponent 4)
          (privateBoundary 4 4) (privateBoundary 4 4))).env) ≫
      graphHom (IndexedSource.outputWire (consumerComponent 4) (consumerComponent 4)
        (privateBoundary 4 4)).env := by
  rw [route_diagram]
  rfl

def shiftedRank : (consumerComponent 4).program.RankCertificate where
  rank a := (consumerRank 4).rank a + 1
  decreases a b h := Nat.add_lt_add_right ((consumerRank 4).decreases a b h) 1

example : (consumerRank 4).rank ⟨consumerPre, ()⟩ ≠ shiftedRank.rank ⟨consumerPre, ()⟩ := by
  decide

theorem rank_image :
    comparison.map (show (⟨IndexedSource.input (consumerComponent 4)⟩ : Target) ⟶
      ⟨IndexedSource.output (consumerComponent 4)⟩ from Quotient.mk _
        (.compute (consumerComponent 4) (consumerRank 4) (privateOrigin 4)
          (.identity _) (.identity _))) =
    comparison.map (show (⟨IndexedSource.input (consumerComponent 4)⟩ : Target) ⟶
      ⟨IndexedSource.output (consumerComponent 4)⟩ from Quotient.mk _
        (.compute (consumerComponent 4) shiftedRank (privateOrigin 4)
          (.identity _) (.identity _))) :=
  comparison_rank_origin_independent _ _ _ _ _ _ _

noncomputable def opaqueNormal : Normal
    (IndexedSource.input (consumerComponent 4)) (IndexedSource.output (consumerComponent 4)) :=
  .compute (privateComposite 4 4) (privateRank 4 4)
    (.opaque _ ⟨privateRank 4 4⟩)
    (IndexedSource.inputWire _ _ (privateBoundary 4 4))
    (IndexedSource.outputWire _ _ (privateBoundary 4 4))

noncomputable def joinedNormal : Normal
    (IndexedSource.input (consumerComponent 4)) (IndexedSource.output (consumerComponent 4)) :=
  .compute (privateComposite 4 4) (privateRank 4 4)
    (.joined _ _ (privateBoundary 4 4) (privateOrigin 4) (privateOrigin 4))
    (IndexedSource.inputWire _ _ (privateBoundary 4 4))
    (IndexedSource.outputWire _ _ (privateBoundary 4 4))

theorem operational_origins_distinct :
    (Quotient.mk _ opaqueNormal :
      Arrow (IndexedSource.input (consumerComponent 4)) (IndexedSource.output (consumerComponent 4))) ≠
        Quotient.mk _ joinedNormal := by
  intro equality
  obtain ⟨t, e, provenance, _⟩ := Quotient.exact equality
  exact opaque_not_joined _ _ (privateBoundary 4 4) ⟨privateRank 4 4⟩
    (privateOrigin 4) (privateOrigin 4) t e provenance

theorem origins_same_full_image :
    comparison.map (show (⟨IndexedSource.input (consumerComponent 4)⟩ : Target) ⟶
      ⟨IndexedSource.output (consumerComponent 4)⟩ from Quotient.mk _ opaqueNormal) =
    comparison.map (show (⟨IndexedSource.input (consumerComponent 4)⟩ : Target) ⟶
      ⟨IndexedSource.output (consumerComponent 4)⟩ from Quotient.mk _ joinedNormal) :=
  comparison_rank_origin_independent _ _ _ _ _ _ _

#print axioms binary_exterior
#print axioms binary_composition
#print axioms nested_images
#print axioms left_nested_exterior
#print axioms right_nested_exterior
#print axioms operational_origins_distinct
#print axioms origins_same_full_image

end IndexedRankedWitnessCategoryTest
