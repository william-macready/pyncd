import IndexedWitnessInterface
import Mathlib.CategoryTheory.Category.Basic

namespace IndexedWitness

open CategoryTheory
open LeanNCD.Semantics

structure Span (X Y : WholeInterface) where
  W : Type
  left : W → X.Env
  right : W → Y.Env

structure SpanIso {X Y : WholeInterface} (F G : Span X Y) where
  witness : F.W ≃ G.W
  left : ∀ w, G.left (witness w) = F.left w
  right : ∀ w, G.right (witness w) = F.right w

def SpanIso.refl {X Y : WholeInterface} (F : Span X Y) : SpanIso F F where
  witness := Equiv.refl _
  left := fun _ => rfl
  right := fun _ => rfl

def SpanIso.symm {X Y : WholeInterface} {F G : Span X Y}
    (e : SpanIso F G) : SpanIso G F where
  witness := e.witness.symm
  left := by intro w; simpa using (e.left (e.witness.symm w)).symm
  right := by intro w; simpa using (e.right (e.witness.symm w)).symm

def SpanIso.trans {X Y : WholeInterface} {F G H : Span X Y}
    (e : SpanIso F G) (f : SpanIso G H) : SpanIso F H where
  witness := e.witness.trans f.witness
  left := by intro w; exact (f.left (e.witness w)).trans (e.left w)
  right := by intro w; exact (f.right (e.witness w)).trans (e.right w)

instance spanSetoid (X Y : WholeInterface) : Setoid (Span X Y) where
  r F G := Nonempty (SpanIso F G)
  iseqv := ⟨fun F => ⟨SpanIso.refl F⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

abbrev WitnessHom (X Y : WholeInterface) := Quotient (spanSetoid X Y)

def Span.identity (X : WholeInterface) : Span X X where
  W := X.Env
  left := id
  right := id

def Span.pullback {X Y Z : WholeInterface} (F : Span X Y) (G : Span Y Z) :
    Span X Z where
  W := {p : F.W × G.W // F.right p.1 = G.left p.2}
  left := fun p => F.left p.val.1
  right := fun p => G.right p.val.2

def SpanIso.pullback {X Y Z : WholeInterface} {F F' : Span X Y}
    {G G' : Span Y Z} (e : SpanIso F F') (f : SpanIso G G') :
    SpanIso (F.pullback G) (F'.pullback G') where
  witness :=
    { toFun := fun p =>
        ⟨(e.witness p.val.1, f.witness p.val.2),
          by rw [e.right, f.left]; exact p.property⟩
      invFun := fun p =>
        ⟨(e.witness.symm p.val.1, f.witness.symm p.val.2),
          by
            have he := e.right (e.witness.symm p.val.1)
            have hf := f.left (f.witness.symm p.val.2)
            simp only [Equiv.apply_symm_apply] at he hf
            exact he.symm.trans (p.property.trans hf)⟩
      left_inv := by
        rintro ⟨⟨w, v⟩, h⟩
        apply Subtype.ext
        simp
      right_inv := by
        rintro ⟨⟨w, v⟩, h⟩
        apply Subtype.ext
        simp }
  left := by intro p; exact e.left _
  right := by intro p; exact f.right _

def SpanIso.leftUnit {X Y : WholeInterface} (F : Span X Y) :
    SpanIso ((Span.identity X).pullback F) F where
  witness :=
    { toFun := fun p => p.val.2
      invFun := fun w => ⟨(F.left w, w), rfl⟩
      left_inv := by
        rintro ⟨⟨x, w⟩, h⟩
        apply Subtype.ext
        exact Prod.ext h.symm rfl
      right_inv := fun _ => rfl }
  left := by
    rintro ⟨⟨x, w⟩, h⟩
    exact h.symm
  right := fun _ => rfl

def SpanIso.rightUnit {X Y : WholeInterface} (F : Span X Y) :
    SpanIso (F.pullback (Span.identity Y)) F where
  witness :=
    { toFun := fun p => p.val.1
      invFun := fun w => ⟨(w, F.right w), rfl⟩
      left_inv := by
        rintro ⟨⟨w, y⟩, h⟩
        apply Subtype.ext
        exact Prod.ext rfl h
      right_inv := fun _ => rfl }
  left := fun _ => rfl
  right := by
    rintro ⟨⟨w, y⟩, h⟩
    exact h

def SpanIso.assoc {W X Y Z : WholeInterface}
    (F : Span W X) (G : Span X Y) (H : Span Y Z) :
    SpanIso ((F.pullback G).pullback H) (F.pullback (G.pullback H)) where
  witness :=
    { toFun := fun p =>
        ⟨(p.val.1.val.1,
          ⟨(p.val.1.val.2, p.val.2), p.property⟩),
          p.val.1.property⟩
      invFun := fun p =>
        ⟨(⟨(p.val.1, p.val.2.val.1), p.property⟩,
          p.val.2.val.2), p.val.2.property⟩
      left_inv := by
        rintro ⟨⟨⟨⟨w, v⟩, hfg⟩, u⟩, hgh⟩
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext; rfl
        · rfl
      right_inv := by
        rintro ⟨⟨w, ⟨⟨v, u⟩, hgh⟩⟩, hfg⟩
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Subtype.ext; rfl }
  left := fun _ => rfl
  right := fun _ => rfl

def homId (X : WholeInterface) : WitnessHom X X :=
  Quotient.mk _ (Span.identity X)

def homComp {X Y Z : WholeInterface} (f : WitnessHom X Y)
    (g : WitnessHom Y Z) : WitnessHom X Z :=
  Quotient.liftOn₂ f g (fun F G => Quotient.mk _ (F.pullback G))
    (by
      intro F F' G G' ⟨e⟩ ⟨h⟩
      exact Quotient.sound ⟨e.pullback h⟩)

instance : Category.{1} WholeInterface where
  Hom := WitnessHom
  id := homId
  comp := homComp
  id_comp := by
    intro X Y f
    induction f using Quotient.inductionOn with
    | _ F => exact Quotient.sound ⟨SpanIso.leftUnit F⟩
  comp_id := by
    intro X Y f
    induction f using Quotient.inductionOn with
    | _ F => exact Quotient.sound ⟨SpanIso.rightUnit F⟩
  assoc := by
    intro W X Y Z f g h
    induction f using Quotient.inductionOn with
    | _ F =>
      induction g using Quotient.inductionOn with
      | _ G =>
        induction h using Quotient.inductionOn with
        | _ H => exact Quotient.sound ⟨SpanIso.assoc F G H⟩

/-- Every complete model on every validated input remains a separate witness. -/
def componentSpan {σ : LeanNCD.Semantics.Declarations Unit}
    [Fintype σ.Tensor] [DecidableEq σ.Tensor]
    (A : IndexedComponentComposition.MatchedComponent σ) :
    Span (inputInterface A) (outputInterface A) where
  W := Σ η : A.program.Input,
    {ρ : LeanNCD.Semantics.Store RationalReference.Carrier σ //
      A.program.Models RationalReference.ops η ρ}
  left := fun w => inputEnv A w.1
  right := fun w => (outputEquiv A).symm (A.program.outputProjection w.2.val)

end IndexedWitness
