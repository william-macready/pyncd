import IndexedComponentComposition
import IndexedComponentModelInputs
import LeanNCD.Semantics.Ranks

namespace IndexedComponentComposition

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedComponentTransport

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (wire : Boundary A B)

/-- A strict bound on all upstream ranks, including inputs; the empty sum is zero. -/
noncomputable def rankOffset (rA : RankCertificate A.program) : Nat := by
  classical
  letI : ∀ t : σA.Tensor, Fintype (Coord (σA.signature t).axes) :=
    fun t => Program.Executor.finiteCoords (σ := σA) t
  exact (∑ a : Address σA, rA.rank a) + 1

theorem rank_lt_offset (rA : RankCertificate A.program) (a : Address σA) :
    rA.rank a < rankOffset A rA := by
  classical
  letI : ∀ t : σA.Tensor, Fintype (Coord (σA.signature t).axes) :=
    fun t => Program.Executor.finiteCoords (σ := σA) t
  change rA.rank a < (∑ b : Address σA, rA.rank b) + 1
  exact Nat.lt_succ_of_le
    (Finset.single_le_sum (fun b _ => Nat.zero_le (rA.rank b)) (Finset.mem_univ a))

theorem rankOffset_eq_one_of_isEmpty (rA : RankCertificate A.program)
    [IsEmpty (Address σA)] : rankOffset A rA = 1 := by
  classical
  simp [rankOffset]

noncomputable def compositeRank (rA : RankCertificate A.program)
    (rB : RankCertificate B.program) : Address (declarations A B) → Nat
  | ⟨.inl t, p⟩ => rA.rank ⟨t, p⟩
  | ⟨.inr t, p⟩ => rankOffset A rA + rB.rank ⟨t.val, p⟩

theorem compositeRank_upstream (rA : RankCertificate A.program)
    (rB : RankCertificate B.program) (a : Address σA) :
    compositeRank A B rA rB ((upstream A B).address a) = rA.rank a := by
  cases a
  rfl

theorem compositeRank_downstream_defined (rA : RankCertificate A.program)
    (rB : RankCertificate B.program) (t : B.program.Defined)
    (p : Coord (σB.signature t.val).axes) :
    compositeRank A B rA rB ((downstream A B wire).address ⟨t.val, p⟩) =
      rankOffset A rA + rB.rank ⟨t.val, p⟩ := by
  rw [downstream_defined_address A B wire t p]
  rfl

theorem compositeRank_downstream_input_lt (rA : RankCertificate A.program)
    (rB : RankCertificate B.program)
    (i : {t : σB.Tensor // B.program.input t = true})
    (p : Coord (σB.signature i.val).axes) :
    compositeRank A B rA rB ((downstream A B wire).address ⟨i.val, p⟩) <
      rankOffset A rA := by
  rw [downstream_input_address A B wire i p, compositeRank_upstream]
  exact rank_lt_offset A rA _

theorem compositeRank_decreases (rA : RankCertificate A.program)
    (rB : RankCertificate B.program) :
    ∀ a b, b ∈ (program A B wire).dependencies a →
      compositeRank A B rA rB b < compositeRank A B rA rB a := by
  rintro a b ⟨⟨t, ht⟩, ⟨s, v⟩, rfl, hb⟩
  cases t with
  | inl t =>
      change b ∈ footprint
        ((program A B wire).body (upstreamDefined A B wire ⟨t, ht⟩) s) v at hb
      rw [upstream_footprint] at hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      change compositeRank A B rA rB ((upstream A B).address c) <
        compositeRank A B rA rB
          ((upstream A B).address ⟨t, A.program.destination ⟨t, ht⟩ s v⟩)
      rw [compositeRank_upstream, compositeRank_upstream]
      exact rA.decreases _ _ ⟨⟨t, ht⟩, ⟨s, v⟩, rfl, hc⟩
  | inr t =>
      change b ∈ footprint
        ((program A B wire).body (downstreamDefined A B wire t) s) v at hb
      rw [downstream_footprint] at hb
      obtain ⟨⟨u, p⟩, hc, rfl⟩ := List.mem_map.mp hb
      change compositeRank A B rA rB ((downstream A B wire).address ⟨u, p⟩) <
        rankOffset A rA + rB.rank ⟨t.val, B.program.destination t s v⟩
      by_cases hu : B.program.input u = true
      · exact lt_of_lt_of_le
          (compositeRank_downstream_input_lt A B wire rA rB ⟨u, hu⟩ p)
          (Nat.le_add_right _ _)
      · have hf : B.program.input u = false := by
          cases h : B.program.input u <;> simp_all
        rw [compositeRank_downstream_defined A B wire rA rB ⟨u, hf⟩ p]
        exact Nat.add_lt_add_left
          (rB.decreases _ _ ⟨t, ⟨s, v⟩, rfl, hc⟩) _

/-- The certificate is for the actual `compose` program, not an assumed composite rank. -/
noncomputable def compositeRankCertificate (rA : RankCertificate A.program)
    (rB : RankCertificate B.program) :
    RankCertificate (compose A B wire).program where
  rank := compositeRank A B rA rB
  decreases := compositeRank_decreases A B wire rA rB

theorem compositeRankCertificate_upstream (rA : RankCertificate A.program)
    (rB : RankCertificate B.program) (a : Address σA) :
    (compositeRankCertificate A B wire rA rB).rank ((upstream A B).address a) =
      rA.rank a :=
  compositeRank_upstream A B rA rB a

theorem compositeRankCertificate_downstream_defined (rA : RankCertificate A.program)
    (rB : RankCertificate B.program) (t : B.program.Defined)
    (p : Coord (σB.signature t.val).axes) :
    (compositeRankCertificate A B wire rA rB).rank
        ((downstream A B wire).address ⟨t.val, p⟩) =
      rankOffset A rA + rB.rank ⟨t.val, p⟩ :=
  compositeRank_downstream_defined A B wire rA rB t p

end IndexedComponentComposition
