import IndexedSourceSyntax
import Mathlib.CategoryTheory.Functor.Basic

namespace IndexedSource

open LeanNCD.Semantics IndexedComponentComposition IndexedWitness CategoryTheory

noncomputable def Term.denote : {X Y : Object} → Term X Y → (X.interface ⟶ Y.interface)
  | _, _, .identity _ => 𝟙 _
  | _, _, .wire w => graphHom w.env
  | _, _, @Term.leaf σ ft de A => @Quotient.mk _ _ (@componentSpan σ ft de A)
  | _, _, .seq f g => f.denote ≫ g.denote

theorem sound {X Y : Object} {f g : Term X Y} (h : Rel f g) :
    f.denote = g.denote := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | seq _ _ ih ih' => simp only [Term.denote, ih, ih']
  | id_left => exact Category.id_comp _
  | id_right => exact Category.comp_id _
  | assoc => exact Category.assoc _ _ _
  | wire_id X => exact (congrArg graphHom (Wire.env_identity X)).trans (graphHom_identity _)
  | wire_comp a b =>
      exact (graphHom_comp a.env b.env).trans (congrArg graphHom (Wire.env_comp a b).symm)
  | wire_left_inv a =>
      simp only [Term.denote, Wire.env_inverse, graphHom_comp,
        Equiv.self_trans_symm, graphHom_identity]
  | wire_right_inv a =>
      simp only [Term.denote, Wire.env_inverse, graphHom_comp,
        Equiv.symm_trans_self, graphHom_identity]
  | assembly A B b =>
      simpa only [assembled, pair, Term.denote, inputWire_env, outputWire_env,
        boundaryWire_env] using composition_hom A B b
  | left_square A B C ab bc =>
      simp only [Term.denote, boundaryWire_env, outputWire_env, graphHom_comp]
      apply congrArg graphHom
      apply Equiv.ext
      intro x
      exact left_boundary_square A B C ab bc x
  | right_square A B C ab bc =>
      simp only [Term.denote, boundaryWire_env, inputWire_env, graphHom_comp]
      apply congrArg graphHom
      apply Equiv.ext
      intro x
      exact right_boundary_square A B C ab bc x
  | bracket A B C ab bc =>
      have l := Quotient.sound (s := spanSetoid _ _)
        ⟨SpanIso.rebaseGraphs (componentSpan (leftBracket A B C ab bc))
          (leftBracketInputEquiv A B C ab bc) (leftBracketOutputEquiv A B C ab bc)⟩
      have r := Quotient.sound (s := spanSetoid _ _)
        ⟨SpanIso.rebaseGraphs (componentSpan (rightBracket A B C ab bc))
          (rightBracketInputEquiv A B C ab bc) (rightBracketOutputEquiv A B C ab bc)⟩
      simpa only [leftNested, rightNested, Term.denote, Wire.env_comp,
        inputWire_env, outputWire_env, leftBracketInputEquiv, leftBracketOutputEquiv,
        rightBracketInputEquiv, rightBracketOutputEquiv, ← Category.assoc] using
        l.trans ((bracket_hom A B C ab bc).trans r.symm)

abbrev Hom (X Y : Object) := Quotient (termSetoid X Y)

def homId (X : Object) : Hom X X := Quotient.mk _ (.identity X)

def homComp {X Y Z : Object} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Quotient.liftOn₂ f g (fun a b => Quotient.mk _ (.seq a b))
    (by intro a a' b b' h h'; exact Quotient.sound (Rel.seq h h'))

instance : Category.{1} Object where
  Hom := Hom
  id := homId
  comp := homComp
  id_comp := by
    intro X Y f
    induction f using Quotient.inductionOn with
    | _ f => exact Quotient.sound (Rel.id_left f)
  comp_id := by
    intro X Y f
    induction f using Quotient.inductionOn with
    | _ f => exact Quotient.sound (Rel.id_right f)
  assoc := by
    intro W X Y Z f g h
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        induction h using Quotient.inductionOn with
        | _ h => exact Quotient.sound (Rel.assoc f g h)

noncomputable def semantics : Object ⥤ WholeInterface where
  obj := Object.interface
  map := fun f => Quotient.liftOn f Term.denote (fun _ _ h => sound h)
  map_id := fun _ => rfl
  map_comp := by
    intro X Y Z f g
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g => rfl

def arrow {X Y : Object} (f : Term X Y) : X ⟶ Y := Quotient.mk _ f

theorem assembly_eq {σA σB : Declarations Unit}
    [Fintype σA.Tensor] [DecidableEq σA.Tensor]
    [Fintype σB.Tensor] [DecidableEq σB.Tensor]
    (A : MatchedComponent σA) (B : MatchedComponent σB) (b : Boundary A B) :
    arrow (assembled A B b) = arrow (pair A B b) :=
  Quotient.sound (Rel.assembly A B b)

theorem wire_comp_eq {X Y Z : Object} (a : Wire X Y) (b : Wire Y Z) :
    arrow (.wire a) ≫ arrow (.wire b) = arrow (.wire (a.comp b)) :=
  Quotient.sound (Rel.wire_comp a b)

theorem arrow_seq {X Y Z : Object} (f : Term X Y) (g : Term Y Z) :
    arrow (.seq f g) = arrow f ≫ arrow g := rfl

variable {σA σB σC : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable [Fintype σC.Tensor] [DecidableEq σC.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (C : MatchedComponent σC) (ab : Boundary A B) (bc : Boundary B C)

theorem source_assembly (b : Boundary A B) :
    arrow (.wire (inputWire A B b)) ≫ arrow (.leaf (compose A B b)) ≫
        arrow (.wire (outputWire A B b)) =
      arrow (.leaf A) ≫ arrow (.wire (boundaryWire A B b)) ≫ arrow (.leaf B) := by
  simpa only [assembled, pair, arrow_seq, Category.assoc] using assembly_eq A B b

theorem source_assembly_assoc (b : Boundary A B) {Z : Object} (f : output B ⟶ Z) :
    arrow (.wire (inputWire A B b)) ≫ arrow (.leaf (compose A B b)) ≫
        arrow (.wire (outputWire A B b)) ≫ f =
      arrow (.leaf A) ≫ arrow (.wire (boundaryWire A B b)) ≫ arrow (.leaf B) ≫ f := by
  simpa only [Category.assoc] using congrArg (fun g => g ≫ f) (source_assembly A B b)

theorem left_eq_triple :
    arrow (leftNested A B C ab bc) = arrow (triple A B C ab bc) := by
  have sq := Quotient.sound (s := termSetoid _ _) (Rel.left_square A B C ab bc)
  change arrow _ = arrow _ at sq
  simp only [arrow_seq] at sq
  simp only [leftNested, triple, pair, arrow_seq, ← wire_comp_eq, Category.assoc]
  rw [source_assembly (compose A B ab) C (leftNestedBoundary A B C ab bc), sq]
  simp only [Category.assoc]
  rw [source_assembly_assoc A B ab]

theorem right_eq_triple :
    arrow (rightNested A B C ab bc) = arrow (triple A B C ab bc) := by
  have sq := Quotient.sound (s := termSetoid _ _) (Rel.right_square A B C ab bc)
  change arrow _ = arrow _ at sq
  simp only [arrow_seq] at sq
  simp only [rightNested, triple, pair, arrow_seq, ← wire_comp_eq, Category.assoc]
  rw [source_assembly_assoc A (compose B C bc) (rightNestedBoundary A B C ab bc), sq]
  simp only [Category.assoc]
  rw [source_assembly B C bc]

end IndexedSource
