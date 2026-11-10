import IndexedRankedExecutionSemantics
import IndexedWitnessCoherence

namespace IndexedOperationalReassociation

open LeanNCD.Semantics
open IndexedComponentTransport
open IndexedComponentComposition
open IndexedComponentExecution
open IndexedOpenComposition
open IndexedWitness

variable {σA σB σC : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable [Fintype σC.Tensor] [DecidableEq σC.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (C : MatchedComponent σC)
variable (ab : Boundary A B) (bc : Boundary B C)

def tensorEquiv :
    (declarations (compose A B ab) C).Tensor ≃
      (declarations A (compose B C bc)).Tensor :=
  (Equiv.sumAssoc σA.Tensor B.program.Defined C.program.Defined).trans
    (Equiv.sumCongr (Equiv.refl _) (definedEquiv B C bc).symm)

def sourceOccurrenceEquiv :
    SourceOccurrence (leftBracket A B C ab bc).program ≃
      SourceOccurrence (rightBracket A B C ab bc).program :=
  (occurrenceEquiv (compose A B ab) C (leftNestedBoundary A B C ab bc)).trans
    ((Equiv.sumCongr (occurrenceEquiv A B ab) (Equiv.refl _)).trans
      ((Equiv.sumAssoc (SourceOccurrence A.program) (SourceOccurrence B.program)
        (SourceOccurrence C.program)).trans
        ((Equiv.sumCongr (Equiv.refl _) (occurrenceEquiv B C bc).symm).trans
          (occurrenceEquiv A (compose B C bc) (rightNestedBoundary A B C ab bc)).symm)))

def addressEquiv :
    Address (declarations (compose A B ab) C) ≃
      Address (declarations A (compose B C bc)) where
  toFun
    | ⟨.inl (.inl t), p⟩ => ⟨.inl t, p⟩
    | ⟨.inl (.inr t), p⟩ => ⟨.inr ⟨.inl t.val, t.property⟩, p⟩
    | ⟨.inr t, p⟩ => ⟨.inr ⟨.inr t, rfl⟩, p⟩
  invFun
    | ⟨.inl t, p⟩ => ⟨.inl (.inl t), p⟩
    | ⟨.inr ⟨.inl t, h⟩, p⟩ => ⟨.inl (.inr ⟨t, h⟩), p⟩
    | ⟨.inr ⟨.inr t, _⟩, p⟩ => ⟨.inr t, p⟩
  left_inv := by
    rintro ⟨t, p⟩
    rcases t with (t | t) | t <;> rfl
  right_inv := by
    rintro ⟨t, p⟩
    rcases t with t | ⟨t | t, h⟩ <;> rfl

def embedding :
    Embedding (declarations (compose A B ab) C)
      (declarations A (compose B C bc)) where
  tensor := tensorEquiv A B C ab bc
  injective := (tensorEquiv A B C ab bc).injective
  domain := by
    rintro ((t | t) | t) <;> exact Domain.id _

theorem embedding_address (a : Address (declarations (compose A B ab) C)) :
    (embedding A B C ab bc).address a = addressEquiv A B C ab bc a := by
  rcases a with ⟨(t | t) | t, p⟩ <;> rfl

theorem address_A (a : Address σA) :
    addressEquiv A B C ab bc
        ((upstream (compose A B ab) C).address ((upstream A B).address a)) =
      (upstream A (compose B C bc)).address a := rfl

theorem address_B (a : Address σB) :
    addressEquiv A B C ab bc
        ((upstream (compose A B ab) C).address ((downstream A B ab).address a)) =
      (downstream A (compose B C bc) (rightNestedBoundary A B C ab bc)).address
        ((upstream B C).address a) := by
  rcases a with ⟨t, p⟩
  change _ = (downstream A (compose B C bc) (rightNestedBoundary A B C ab bc)).address
    ⟨.inl t, p⟩
  by_cases h : B.program.input t = true
  · rw [downstream_input_address A B ab ⟨t, h⟩ p]
    rw [downstream_input_address A (compose B C bc)
      (rightNestedBoundary A B C ab bc) ⟨.inl t, h⟩ p]
    rfl
  · have hf : B.program.input t = false := Bool.eq_false_iff.mpr h
    rw [downstream_defined_address A B ab ⟨t, hf⟩ p]
    rw [downstream_defined_address A (compose B C bc)
      (rightNestedBoundary A B C ab bc) ⟨.inl t, hf⟩ p]
    rfl

theorem address_C (a : Address σC) :
    addressEquiv A B C ab bc
        ((downstream (compose A B ab) C (leftNestedBoundary A B C ab bc)).address a) =
      (downstream A (compose B C bc) (rightNestedBoundary A B C ab bc)).address
        ((downstream B C bc).address a) := by
  rcases a with ⟨t, p⟩
  by_cases h : C.program.input t = true
  · rw [downstream_input_address (compose A B ab) C
      (leftNestedBoundary A B C ab bc) ⟨t, h⟩ p]
    rw [downstream_input_address B C bc ⟨t, h⟩ p]
    change _ = (downstream A (compose B C bc) (rightNestedBoundary A B C ab bc)).address
      ⟨.inl (bc.matched ⟨t, h⟩).val, (bc.domain ⟨t, h⟩).coord p⟩
    rw [downstream_defined_address A (compose B C bc)
      (rightNestedBoundary A B C ab bc)
      ⟨.inl (bc.matched ⟨t, h⟩).val,
        B.program.output_defined _ (bc.matched ⟨t, h⟩).property⟩
      ((bc.domain ⟨t, h⟩).coord p)]
    rfl
  · have hf : C.program.input t = false := Bool.eq_false_iff.mpr h
    rw [downstream_defined_address (compose A B ab) C
      (leftNestedBoundary A B C ab bc) ⟨t, hf⟩ p]
    rw [downstream_defined_address B C bc ⟨t, hf⟩ p]
    change _ = (downstream A (compose B C bc) (rightNestedBoundary A B C ab bc)).address
      ⟨.inr ⟨t, hf⟩, p⟩
    rw [downstream_defined_address A (compose B C bc)
      (rightNestedBoundary A B C ab bc) ⟨.inr ⟨t, hf⟩, rfl⟩ p]
    rfl

theorem initial_available (η : A.program.Input)
    (a : Address (declarations (compose A B ab) C)) :
    (initial (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η).val).available
        (addressEquiv A B C ab bc a) =
      (initial (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
        (liftInput A B ab η)).val).available a := by
  rcases a with ⟨(t | t) | t, p⟩ <;> rfl

theorem input_roles (t : (declarations (compose A B ab) C).Tensor) :
    (rightBracket A B C ab bc).program.input (tensorEquiv A B C ab bc t) =
      (leftBracket A B C ab bc).program.input t := by
  rcases t with (t | t) | t <;> rfl

theorem output_roles (t : (declarations (compose A B ab) C).Tensor) :
    (rightBracket A B C ab bc).program.output (tensorEquiv A B C ab bc t) =
      (leftBracket A B C ab bc).program.output t := by
  rcases t with (t | t) | t <;> rfl

def rename (n : Nat) : Nat :=
  if n % 2 = 1 then 2 * n + 1
  else if n % 4 = 0 then n / 2 else n - 1

def unrename (n : Nat) : Nat :=
  if n % 2 = 0 then 2 * n
  else if n % 4 = 1 then n + 1 else n / 2

def identityEquiv : Nat ≃ Nat where
  toFun := rename
  invFun := unrename
  left_inv := by intro n; unfold rename unrename; split_ifs <;> omega
  right_inv := by intro n; unfold rename unrename; split_ifs <;> omega

theorem identity_A (n : Nat) :
    identityEquiv (upstreamId (upstreamId n)) = upstreamId n := by
  change rename (2 * (2 * n)) = 2 * n
  unfold rename
  split_ifs <;> omega

theorem identity_B (n : Nat) :
    identityEquiv (upstreamId (downstreamId n)) =
      downstreamId (upstreamId n) := by
  change rename (2 * (2 * n + 1)) = 2 * (2 * n) + 1
  unfold rename
  split_ifs <;> omega

theorem identity_C (n : Nat) :
    identityEquiv (downstreamId n) = downstreamId (downstreamId n) := by
  change rename (2 * n + 1) = 2 * (2 * n + 1) + 1
  unfold rename
  split_ifs <;> omega

theorem tensor_uid (t : (declarations (compose A B ab) C).Tensor) :
    (declarations A (compose B C bc)).uid (tensorEquiv A B C ab bc t) =
      identityEquiv ((declarations (compose A B ab) C).uid t) := by
  rcases t with (t | t) | t
  · exact (identity_A (σA.uid t)).symm
  · exact (identity_B (σB.uid t.val)).symm
  · exact (identity_C (σC.uid t.val)).symm

theorem default_budgets :
    (leftBracket A B C ab bc).graph.steps.length + 1 =
      A.graph.steps.length + B.graph.steps.length + C.graph.steps.length + 1 ∧
    (rightBracket A B C ab bc).graph.steps.length + 1 =
      A.graph.steps.length + B.graph.steps.length + C.graph.steps.length + 1 := by
  constructor <;>
    simp only [leftBracket, rightBracket, graph_steps_standalone,
      List.length_append, List.length_map]
  all_goals omega

noncomputable def leftRank (rankA : A.program.RankCertificate)
    (rankB : B.program.RankCertificate) (rankC : C.program.RankCertificate) :
    (leftBracket A B C ab bc).program.RankCertificate :=
  compositeRankCertificate (compose A B ab) C (leftNestedBoundary A B C ab bc)
    (compositeRankCertificate A B ab rankA rankB) rankC

noncomputable def rightRank (rankA : A.program.RankCertificate)
    (rankB : B.program.RankCertificate) (rankC : C.program.RankCertificate) :
    (rightBracket A B C ab bc).program.RankCertificate :=
  compositeRankCertificate A (compose B C bc) (rightNestedBoundary A B C ab bc)
    rankA (compositeRankCertificate B C bc rankB rankC)

end IndexedOperationalReassociation
