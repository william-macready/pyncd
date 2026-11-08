import IndexedWitnessCoherence
import IndexedWitnessTest
import Semantics.AxiomAudit

namespace IndexedWitnessCoherenceTest

open LeanNCD.Semantics
open IndexedWitness
open IndexedComponentComposition
open CategoryTheory

variable {σA σB σC : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable [Fintype σC.Tensor] [DecidableEq σC.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (C : MatchedComponent σC)
variable (ab : Boundary A B) (bc : Boundary B C)

example : Boundary (compose A B ab) C :=
  leftNestedBoundary A B C ab bc

example : Boundary A (compose B C bc) :=
  rightNestedBoundary A B C ab bc

example (w : (componentSpan (leftBracket A B C ab bc)).W) :
    (tripleSpan A B C ab bc).left
      ((leftTripleEquiv A B C ab bc) w) =
        (leftBracketSpan A B C ab bc).left w :=
  (leftTripleIso A B C ab bc).left w

example (w : (componentSpan (rightBracket A B C ab bc)).W) :
    (tripleSpan A B C ab bc).right
      ((rightTripleEquiv A B C ab bc) w) =
        (rightBracketSpan A B C ab bc).right w :=
  (rightTripleIso A B C ab bc).right w

noncomputable example : SpanIso (leftBracketSpan A B C ab bc)
    (rightBracketSpan A B C ab bc) :=
  bracketSpanIso A B C ab bc

example : (Quotient.mk _ (leftBracketSpan A B C ab bc) :
      inputInterface A ⟶ outputInterface C) =
    (Quotient.mk _ (rightBracketSpan A B C ab bc) :
      inputInterface A ⟶ outputInterface C) :=
  bracket_hom A B C ab bc

#audit_axioms IndexedWitness
#audit_axioms IndexedWitnessCoherenceTest

#print axioms IndexedWitness.leftNestedBoundary
#print axioms IndexedWitness.rightNestedBoundary
#print axioms IndexedWitness.left_boundary_square
#print axioms IndexedWitness.right_boundary_square
#print axioms IndexedWitness.leftTripleEquiv
#print axioms IndexedWitness.rightTripleEquiv
#print axioms IndexedWitness.bracketSpanIso
#print axioms IndexedWitness.bracket_hom

end IndexedWitnessCoherenceTest
