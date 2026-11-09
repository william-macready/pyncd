import IndexedComponentRankedExecutionFixtures
import IndexedComponentCompositionAxisFixtures
import IndexedComponentCompositionCollisionFixtures
import Semantics.AxiomAudit

noncomputable section

namespace IndexedComponentRankedExecutionRankTest

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedComponentComposition
open IndexedComponentTransport
open IndexedComponentTransportTest (p q)

namespace Axis

open IndexedComponentCompositionAxisFixtures

def producerRank : RankCertificate axisProducer.program where
  rank := fun a => a.2.1.val + 3 * a.2.2.1.val
  decreases := by
    rintro a b ⟨t, ⟨s, v⟩, ha, hb⟩
    simp [axisProducer, producer, footprint] at hb

def consumerRank : RankCertificate axisConsumer.program := by
  letI : DecidableEq (Address consumerDeclarations) := Program.Executor.addressEq
  exact {
    rank := fun a =>
      if a = ⟨0, p⟩ then 0 else if a = ⟨0, q⟩ then 1
      else if a.1 == 1 then 2 else 100
    decreases := by
      rintro a b ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩, rfl, hb⟩
      change b ∈ footprint (consumer.body ⟨t, ht⟩ s) ⟨v, hv⟩ at hb
      rw [← consumerMatch.writer_reads ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩] at hb
      change (t == 0) = false at ht
      fin_cases t <;> fin_cases s <;> fin_cases v
      all_goals first | exact False.elim (Bool.noConfusion ht) | skip
      all_goals
        change b ∈ [⟨0, p⟩, ⟨0, q⟩, ⟨0, p⟩, ⟨0, q⟩] at hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl
        all_goals first | change (0 : Nat) < 2 | change (1 : Nat) < 2
        all_goals decide }

def composite := compose axisProducer axisConsumer axisBoundary

def certificate : RankCertificate composite.program :=
  compositeRankCertificate axisProducer axisConsumer axisBoundary producerRank consumerRank

def boundaryP : Address (declarations axisProducer axisConsumer) :=
  (downstream axisProducer axisConsumer axisBoundary).address ⟨0, p⟩

def boundaryQ : Address (declarations axisProducer axisConsumer) :=
  (downstream axisProducer axisConsumer axisBoundary).address ⟨0, q⟩

theorem boundary_p_rank : certificate.rank boundaryP = 2 := by
  change compositeRank _ _ producerRank consumerRank
    ((downstream axisProducer axisConsumer axisBoundary).address ⟨0, p⟩) = 2
  rw [downstream_input_address axisProducer axisConsumer axisBoundary ⟨0, rfl⟩ p,
    compositeRank_upstream]
  rfl

theorem boundary_q_rank : certificate.rank boundaryQ = 3 := by
  change compositeRank _ _ producerRank consumerRank
    ((downstream axisProducer axisConsumer axisBoundary).address ⟨0, q⟩) = 3
  rw [downstream_input_address axisProducer axisConsumer axisBoundary ⟨0, rfl⟩ q,
    compositeRank_upstream]
  rfl

theorem boundary_ranks_nonconstant : certificate.rank boundaryP ≠ certificate.rank boundaryQ := by
  rw [boundary_p_rank, boundary_q_rank]
  decide

def resultTensor : composite.program.Defined :=
  downstreamDefined axisProducer axisConsumer axisBoundary ⟨1, rfl⟩

theorem full_footprint :
    footprint (composite.program.body resultTensor (0 : Fin 1)) ⟨(0 : Fin 1), rfl⟩ =
      [boundaryP, boundaryQ, boundaryP, boundaryQ] := by
  change footprint ((program axisProducer axisConsumer axisBoundary).body
    (downstreamDefined axisProducer axisConsumer axisBoundary ⟨1, rfl⟩)
    (0 : Fin 1)) ⟨(0 : Fin 1), rfl⟩ = _
  rw [downstream_footprint]
  rfl

theorem full_footprint_ranks :
    (footprint (composite.program.body resultTensor (0 : Fin 1))
      ⟨(0 : Fin 1), rfl⟩).map certificate.rank =
      [2, 3, 2, 3] := by
  rw [full_footprint]
  simp [boundary_p_rank, boundary_q_rank]

theorem full_footprint_decreases (b : Address (declarations axisProducer axisConsumer))
    (hb : b ∈ footprint (composite.program.body resultTensor (0 : Fin 1))
      ⟨(0 : Fin 1), rfl⟩) :
    certificate.rank b < certificate.rank
      ⟨resultTensor.val, composite.program.destination resultTensor (0 : Fin 1)
        ⟨(0 : Fin 1), rfl⟩⟩ :=
  certificate.decreases _ _ ⟨resultTensor, ⟨(0 : Fin 1), ⟨(0 : Fin 1), rfl⟩⟩, rfl, hb⟩

/-- Unread input coordinates may outrank the defined boundary output. -/
theorem unused_input_high_rank :
    axisConsumer.program.input 0 = true ∧
      consumerRank.rank ⟨0, (0, 0, ())⟩ = 100 ∧
      consumerRank.rank ⟨1, ()⟩ = 2 := by
  decide

theorem offset_includes_unused_input : 100 < rankOffset axisConsumer consumerRank := by
  have h := rank_lt_offset axisConsumer consumerRank ⟨0, (0, 0, ())⟩
  exact h

end Axis

namespace Collision

open IndexedComponentCompositionCollisionFixtures

def producerRank : RankCertificate collisionProducer.program where
  rank := fun a => a.1.val
  decreases := by
    rintro a b ⟨⟨t, ht⟩, ⟨s, v⟩, ha, hb⟩
    fin_cases t <;> simp [collisionProducer, producer, footprint] at hb

def consumerRank : RankCertificate collisionConsumer.program :=
  IndexedComponentRankedExecutionFixtures.consumerRank 4

def composite := compose collisionProducer collisionConsumer collisionBoundary

def certificate : RankCertificate composite.program :=
  compositeRankCertificate collisionProducer collisionConsumer collisionBoundary
    producerRank consumerRank

theorem guard_admission :
    collisionProducer.program.guard ⟨0, rfl⟩ (0 : Fin 1) (0 : Fin 3) = true ∧
      collisionProducer.program.guard ⟨0, rfl⟩ (0 : Fin 1) (1 : Fin 3) = false ∧
      collisionProducer.program.guard ⟨0, rfl⟩ (0 : Fin 1) (2 : Fin 3) = true := by
  decide

def guardedTensor : composite.program.Defined :=
  upstreamDefined collisionProducer collisionConsumer collisionBoundary ⟨0, rfl⟩

theorem guarded_full_footprint
    (v : {v : Fin 3 // collisionProducer.program.guard ⟨0, rfl⟩ (0 : Fin 1) v = true}) :
    footprint (composite.program.body guardedTensor (0 : Fin 1)) v = [] := by
  change footprint ((program collisionProducer collisionConsumer collisionBoundary).body
    (upstreamDefined collisionProducer collisionConsumer collisionBoundary ⟨0, rfl⟩)
    (0 : Fin 1)) v = []
  rw [upstream_footprint]
  rfl

theorem guarded_full_footprint_decreases
    (v : {v : Fin 3 // collisionProducer.program.guard ⟨0, rfl⟩ (0 : Fin 1) v = true})
    (b : Address (declarations collisionProducer collisionConsumer))
    (hb : b ∈ footprint (composite.program.body guardedTensor (0 : Fin 1)) v) :
    certificate.rank b < certificate.rank
      ⟨guardedTensor.val, composite.program.destination guardedTensor (0 : Fin 1) v⟩ :=
  certificate.decreases _ _ ⟨guardedTensor, ⟨(0 : Fin 1), v⟩, rfl, hb⟩

def boundaryRead : Address (declarations collisionProducer collisionConsumer) :=
  (downstream collisionProducer collisionConsumer collisionBoundary).address ⟨0, ()⟩

def outputTensor : composite.program.Defined :=
  downstreamDefined collisionProducer collisionConsumer collisionBoundary ⟨1, rfl⟩

def privateTensor : composite.program.Defined :=
  downstreamDefined collisionProducer collisionConsumer collisionBoundary ⟨2, rfl⟩

theorem downstream_full_footprints :
    footprint (composite.program.body outputTensor (0 : Fin 1))
        ⟨(0 : Fin 1), rfl⟩ = [boundaryRead] ∧
      footprint (composite.program.body privateTensor (0 : Fin 1))
        ⟨(0 : Fin 1), rfl⟩ = [boundaryRead] := by
  constructor
  · change footprint ((program collisionProducer collisionConsumer collisionBoundary).body
      (downstreamDefined collisionProducer collisionConsumer collisionBoundary ⟨1, rfl⟩)
      (0 : Fin 1)) ⟨(0 : Fin 1), rfl⟩ = _
    rw [downstream_footprint]
    rfl
  · change footprint ((program collisionProducer collisionConsumer collisionBoundary).body
      (downstreamDefined collisionProducer collisionConsumer collisionBoundary ⟨2, rfl⟩)
      (0 : Fin 1)) ⟨(0 : Fin 1), rfl⟩ = _
    rw [downstream_footprint]
    rfl

theorem private_not_output : composite.program.output privateTensor.val = false := rfl

theorem private_dependency :
    boundaryRead ∈ composite.program.dependencies ⟨privateTensor.val, ()⟩ := by
  refine ⟨privateTensor, ⟨(0 : Fin 1), ⟨(0 : Fin 1), rfl⟩⟩, rfl, ?_⟩
  rw [downstream_full_footprints.2]
  exact List.mem_singleton_self _

theorem private_full_footprint_decreases :
    certificate.rank boundaryRead < certificate.rank ⟨privateTensor.val, ()⟩ :=
  certificate.decreases _ _ private_dependency

theorem boundary_read_rank : certificate.rank boundaryRead = 0 := by
  change compositeRank _ _ producerRank consumerRank
    ((downstream collisionProducer collisionConsumer collisionBoundary).address ⟨0, ()⟩) = 0
  rw [downstream_input_address collisionProducer collisionConsumer collisionBoundary
    ⟨0, rfl⟩ (), compositeRank_upstream]
  rfl

end Collision

#audit_axioms IndexedComponentComposition
#audit_axioms IndexedComponentRankedExecutionFixtures
#audit_axioms IndexedComponentRankedExecutionRankTest

end IndexedComponentRankedExecutionRankTest
