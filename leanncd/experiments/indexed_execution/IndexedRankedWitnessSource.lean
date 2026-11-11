import IndexedRankedWitnessComparison

namespace IndexedRankedWitnessSource

open LeanNCD.Semantics IndexedComponentComposition IndexedWitness
open IndexedRankedOperationalCore IndexedRankedOperationalCategory CategoryTheory
open IndexedRankedOperationalSource IndexedRankedWitnessComparison

def eraseTerm : {X Y : Object} → Term X Y → IndexedSource.Term X.base Y.base
  | _, _, .identity X => .identity X.base
  | _, _, .wire w => .wire w
  | _, _, @Term.leaf σ ft de A _ _ => @IndexedSource.Term.leaf σ ft de A
  | _, _, .seq f g => .seq (eraseTerm f) (eraseTerm g)

theorem erase_rel {X Y : Object} {f g : Term X Y} (h : Rel f g) :
    IndexedSource.Rel (eraseTerm f) (eraseTerm g) := by
  induction h with
  | refl f => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih ih' => exact .trans ih ih'
  | seq _ _ ih ih' => exact .seq ih ih'
  | id_left f => exact .id_left _
  | id_right f => exact .id_right _
  | assoc f g h => exact .assoc _ _ _
  | wire_id X => exact .wire_id _
  | wire_comp a b => exact .wire_comp _ _
  | wire_left_inv a => exact .wire_left_inv _
  | wire_right_inv a => exact .wire_right_inv _
  | assembly A B b rA rB oa ob => exact .assembly A B b
  | left_square A B C ab bc => exact .left_square A B C ab bc
  | right_square A B C ab bc => exact .right_square A B C ab bc

def erase : Object ⥤ IndexedSource.Object where
  obj := Object.base
  map f := Quotient.liftOn f (fun t => IndexedSource.arrow (eraseTerm t))
    (fun _ _ h => Quotient.sound (erase_rel h))
  map_id X := rfl
  map_comp := by
    intro X Y Z f g
    refine Quotient.inductionOn₂ f g ?_
    intro a b
    rfl

theorem normalize_denote {X Y : Object} (f : Term X Y) :
    f.normalize.source.denote = (eraseTerm f).denote := by
  induction f with
  | identity X =>
      exact (congrArg graphHom (IndexedSource.Wire.env_identity X.base)).trans
        (graphHom_identity _)
  | wire w => rfl
  | leaf A r o =>
      have hi : (graphHom (IndexedSource.Wire.identity (IndexedSource.input A)).env :
          inputInterface A ⟶ inputInterface A) = 𝟙 _ :=
        (congrArg (fun e => @graphHom (inputInterface A) (inputInterface A) e)
          (IndexedSource.Wire.env_identity (IndexedSource.input A))).trans
            (graphHom_identity _)
      have ho : (graphHom (IndexedSource.Wire.identity (IndexedSource.output A)).env :
          outputInterface A ⟶ outputInterface A) = 𝟙 _ :=
        (congrArg (fun e => @graphHom (outputInterface A) (outputInterface A) e)
          (IndexedSource.Wire.env_identity (IndexedSource.output A))).trans
            (graphHom_identity _)
      exact (congrArg₂ (fun (u : inputInterface A ⟶ inputInterface A)
          (v : outputInterface A ⟶ outputInterface A) =>
            u ≫ (Quotient.mk _ (componentSpan A) : inputInterface A ⟶ outputInterface A) ≫ v)
        hi ho).trans ((Category.id_comp _).trans (Category.comp_id _))
  | seq f g ih ih' =>
      exact (source_comp f.normalize g.normalize).trans
        (congrArg₂ (fun u v => u ≫ v) ih ih')

theorem diagram : semantics ⋙ comparison = erase ⋙ IndexedSource.semantics := by
  refine CategoryTheory.Functor.ext (h_obj := fun X => rfl) ?_
  intro X Y f
  refine Quotient.inductionOn f ?_
  intro t
  change IndexedRankedWitnessDescent.arrowHom (Quotient.mk _ t.normalize) =
    (𝟙 _) ≫ (eraseTerm t).denote ≫ (𝟙 _)
  rw [Category.id_comp, Category.comp_id]
  exact (IndexedRankedWitnessDescent.arrowHom_mk t.normalize).trans
    (normalize_denote t)

end IndexedRankedWitnessSource
