import IndexedComponentComposition
import IndexedComponentCompositionTest
import IndexedComponentModelInputs
import IndexedComponentModelCycleFixtures
import IndexedCompositionValidated
import IndexedComponentCompositionRanks

namespace IndexedComponentRankedExecutionFixtures

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedOpenComposition
open IndexedComponentComposition
open IndexedComponentTransport
open IndexedComponentCompositionPortFixtures
open IndexedComponentCompositionLocalFixtures
open IndexedComponentCompositionTest (graphEventRow)

def producerRank : producer.RankCertificate where
  rank := fun _ => 0
  decreases := by
    rintro a b ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩, ha, hb⟩
    fin_cases t
    fin_cases s <;> simp [producer, footprint] at hb

def consumerRank (other : ℚ) : (consumer other).RankCertificate where
  rank := fun a => if a.1 == consumerPre then 0 else 1
  decreases := by
    rintro a b ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩, rfl, hb⟩
    rw [← (consumerMatch other).writer_reads ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩] at hb
    change (t == 0) = false at ht
    fin_cases t <;> fin_cases s <;> fin_cases v
    all_goals first | exact False.elim (Bool.noConfusion ht) | skip
    all_goals
      change b ∈ [⟨0, ()⟩] at hb
      have hb' := List.mem_singleton.mp hb
      subst b
      change (0 : Nat) < 1
      decide

def emptyProducerRank : emptyProducer.RankCertificate where
  rank := fun _ => 0
  decreases := by
    rintro ⟨t, p⟩
    exact Fin.elim0 p.1

def emptyConsumerRank : emptyConsumer.RankCertificate where
  rank := fun _ => 0
  decreases := by
    rintro ⟨t, p⟩
    exact Fin.elim0 p.1

def privateBoundary (upstreamOther downstreamOther : ℚ) :
    Boundary (consumerComponent upstreamOther) (consumerComponent downstreamOther) where
  matched :=
    { toFun := fun _ => ⟨consumerOut, rfl⟩
      invFun := fun _ => ⟨consumerPre, rfl⟩
      left_inv := by
        rintro ⟨t, ht⟩
        change (t == 0) = true at ht
        fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion ht)
      right_inv := by
        rintro ⟨t, ht⟩
        change (t == 1) = true at ht
        fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion ht) }
  domain := fun _ => Domain.id []

def privateInput (other : ℚ) : (consumerComponent other).program.Input :=
  ⟨fun t => if t == consumerPre then some (fun _ => 3) else none,
    by intro t; fin_cases t <;> rfl⟩

def privateComposite (upstreamOther downstreamOther : ℚ) :=
  compose (consumerComponent upstreamOther) (consumerComponent downstreamOther)
    (privateBoundary upstreamOther downstreamOther)

noncomputable def privateRank (upstreamOther downstreamOther : ℚ) :
    (privateComposite upstreamOther downstreamOther).program.RankCertificate :=
  compositeRankCertificate (consumerComponent upstreamOther) (consumerComponent downstreamOther)
    (privateBoundary upstreamOther downstreamOther)
    (consumerRank upstreamOther) (consumerRank downstreamOther)

def privateRun (upstreamOther downstreamOther : ℚ) :=
  let A := consumerComponent upstreamOther
  let B := consumerComponent downstreamOther
  let wire := privateBoundary upstreamOther downstreamOther
  let C := privateComposite upstreamOther downstreamOther
  runChecked C.contract C.fragment (liftInput A B wire (privateInput upstreamOther)).val

theorem private_not_blocked (upstreamOther downstreamOther : ℚ)
    (state : State (declarations (consumerComponent upstreamOther)
      (consumerComponent downstreamOther))) (missing : List (Nat ×
      List (Address (declarations (consumerComponent upstreamOther)
        (consumerComponent downstreamOther))))) :
    let C := privateComposite upstreamOther downstreamOther
    (runChecked C.contract C.fragment
      (liftInput (consumerComponent upstreamOther) (consumerComponent downstreamOther)
        (privateBoundary upstreamOther downstreamOther) (privateInput upstreamOther)).val).outcome ≠
      .blocked state missing :=
  Correspondence.ranked_not_blocked (privateComposite upstreamOther downstreamOther).matched
    (liftInput (consumerComponent upstreamOther) (consumerComponent downstreamOther)
      (privateBoundary upstreamOther downstreamOther) (privateInput upstreamOther))
    (privateRank upstreamOther downstreamOther) state missing

def privateSnapshots (upstreamOther downstreamOther : ℚ) :=
  (privateRun upstreamOther downstreamOther).states.map fun s =>
    ([s.available ⟨.inl consumerPre, ()⟩,
      s.available ⟨.inl consumerOut, ()⟩,
      s.available ⟨.inl strictAudit, ()⟩,
      s.available ⟨.inr ⟨consumerOut, rfl⟩, ()⟩,
      s.available ⟨.inr ⟨strictAudit, rfl⟩, ()⟩],
      s.produced)

def privateObservation (upstreamOther downstreamOther : ℚ) :=
  ((privateRun upstreamOther downstreamOther).outcome.kind,
    (privateRun upstreamOther downstreamOther).events.map graphEventRow,
    privateSnapshots upstreamOther downstreamOther)

open IndexedComponentModelCycleFixtures in
def unrankedRun :=
  let C := compose hiddenUpstream totalDownstream hiddenBoundary
  runChecked C.contract C.fragment
    (liftInput hiddenUpstream totalDownstream hiddenBoundary (upstreamInput true)).val

def unrankedObservation :=
  (unrankedRun.outcome.kind, unrankedRun.events.map graphEventRow,
    unrankedRun.states.map fun s =>
      ([s.available ⟨.inl IndexedComponentModelCycleFixtures.privateTensor, ()⟩,
        s.available ⟨.inl IndexedComponentModelCycleFixtures.boundaryTensor, ()⟩,
        s.available ⟨.inr ⟨IndexedComponentModelCycleFixtures.boundaryTensor, rfl⟩, ()⟩],
        s.produced))

open IndexedComponentModelCycleFixtures in
theorem hidden_no_rank : ¬ Nonempty hiddenUpstream.program.RankCertificate := by
  rintro ⟨certificate⟩
  let a : Address IndexedComponentModelCycleFixtures.declarations := ⟨privateTensor, ()⟩
  have selfDependency : a ∈ hiddenUpstream.program.dependencies a := by
    exact ⟨⟨privateTensor, rfl⟩,
      ⟨⟨0, by decide⟩, ⟨⟨0, by decide⟩, rfl⟩⟩, rfl, by decide⟩
  exact Nat.lt_irrefl (certificate.rank a) (certificate.decreases a a selfDependency)

def reorderedPrivateRun :=
  let C := privateComposite 0 4
  let rows := C.contract.collectors
  let reordered := { C.contract with
    collectors := rows.take 1 ++ rows.drop 2 ++ (rows.drop 1).take 1 }
  runChecked reordered C.fragment
    (liftInput (consumerComponent 0) (consumerComponent 4) (privateBoundary 0 4)
      (privateInput 0)).val

def reorderedPrivateObservation :=
  (reorderedPrivateRun.outcome.kind, reorderedPrivateRun.events.map graphEventRow,
    reorderedPrivateRun.states.getLast?.map fun s =>
      [s.available ⟨.inl consumerOut, ()⟩, s.available ⟨.inl strictAudit, ()⟩,
        s.available ⟨.inr ⟨consumerOut, rfl⟩, ()⟩,
        s.available ⟨.inr ⟨strictAudit, rfl⟩, ()⟩])

def privateReferenceCounts (upstreamOther downstreamOther : ℚ) :=
  let C := privateComposite upstreamOther downstreamOther
  let η := liftInput (consumerComponent upstreamOther) (consumerComponent downstreamOther)
    (privateBoundary upstreamOther downstreamOther) (privateInput upstreamOther)
  let result := Program.Executor.run C.program RationalReference.ops C.schedule η
  (result.events.length,
    (Correspondence.referenceSnapshots (C.program.initial η) result.events).length,
    C.graph.steps.length + 1,
    (consumerComponent upstreamOther).graph.steps.length + 1,
    (consumerComponent downstreamOther).graph.steps.length + 1)

def emptyBoundaryOutput : emptyProducer.Output :=
  fun _ p => Fin.elim0 p.1

theorem emptyBoundary_present :
    ((boundaryFromOutput emptyProducerComponent emptyConsumerComponent emptyBoundary
      emptyBoundaryOutput).val emptyConsumerPre).isSome = true := rfl

def emptyComposite := compose emptyProducerComponent emptyConsumerComponent emptyBoundary

def emptyCompositeInput :=
  liftInput emptyProducerComponent emptyConsumerComponent emptyBoundary emptyValidatedInput

noncomputable def emptyRank : emptyComposite.program.RankCertificate :=
  compositeRankCertificate emptyProducerComponent emptyConsumerComponent emptyBoundary
    emptyProducerRank emptyConsumerRank

theorem empty_rank_offset :
    rankOffset emptyProducerComponent emptyProducerRank = 1 := by
  letI : IsEmpty (Address emptyProducerDeclarations) := ⟨fun a => Fin.elim0 a.2.1⟩
  exact rankOffset_eq_one_of_isEmpty emptyProducerComponent emptyProducerRank

def emptyCompositeRun :=
  runChecked emptyComposite.contract emptyComposite.fragment emptyCompositeInput.val

def emptyDoubleInvalid : InputBinding (K := RationalReference.Carrier)
    (σ := declarations emptyProducerComponent emptyConsumerComponent)
  | .inl t => if t == emptyProducerPre then some (fun p => Fin.elim0 p.1) else none
  | .inr _ => none

def emptyObservation :=
  (emptyCompositeRun.outcome.kind, emptyCompositeRun.events.length,
    emptyCompositeRun.states.length, emptyComposite.graph.steps.length + 1,
    ((boundaryFromOutput emptyProducerComponent emptyConsumerComponent emptyBoundary
      emptyBoundaryOutput).val emptyConsumerPre).isSome,
    match (runChecked emptyComposite.contract emptyComposite.fragment emptyDoubleInvalid).outcome with
    | .invalidInput t => some ((declarations emptyProducerComponent emptyConsumerComponent).uid t)
    | _ => none)

def collectedRun (other : ℚ) :=
  let C := compose producerComponent (consumerComponent other) (scalarBoundary other)
  runChecked C.contract C.fragment (fun _ => none)

def collectionPrefix (other : ℚ) :=
  (collectedRun other).states.take 4 |>.map fun s =>
    (s.available ⟨.inl producerPre, ()⟩, s.produced)

def zeroCheckedRun :=
  let C := compose zeroProducerComponent (consumerComponent 4) zeroBoundary
  runChecked C.contract C.fragment (fun _ => none)

#eval IndexedCompositionParityTest.check "ranked-complete-contribution-boundary"
  (collectionPrefix 4, collectionPrefix 0,
    (collectedRun 4).events.length, (collectedRun 0).events.length)
  ([(none, []), (none, [(202, 1)]), (none, [(202, 1), (204, -1)]),
      (some 0, [(202, 1), (204, -1)])],
    [(none, []), (none, [(202, 1)]), (none, [(202, 1), (204, -1)]),
      (some 0, [(202, 1), (204, -1)])], 7, 6)

#eval IndexedCompositionParityTest.check "ranked-zero-writer-publication"
  (zeroCheckedRun.outcome.kind, zeroCheckedRun.events.map graphEventRow,
    zeroCheckedRun.states.length)
  ("complete",
    [("publish", 0, 0, some 0), ("write", 41, 403, some 0),
      ("publish", 3, 0, some 0), ("write", 61, 603, some (1 / 2)),
      ("publish", 5, 0, some (1 / 2))], 6)

#eval IndexedCompositionParityTest.check "ranked-reference-snapshots-and-budgets"
  (privateReferenceCounts 4 4, privateReferenceCounts 0 4, privateReferenceCounts 4 0)
  ((8, 9, 9, 5, 5), (3, 3, 9, 5, 5), (7, 7, 9, 5, 5))

#eval IndexedCompositionParityTest.check "ranked-empty-metadata-and-validation"
  emptyObservation ("complete", 0, 1, 1, true, some 20)

#eval IndexedCompositionParityTest.check "ranked-private-order-control"
  reorderedPrivateObservation
  ("failed",
    [("write", 40, 402, some 9), ("publish", 2, 0, some 9),
      ("write", 41, 403, some 81), ("publish", 3, 0, some 81),
      ("write", 61, 603, some (19 / 2)), ("publish", 5, 0, some (19 / 2)),
      ("undefined", 60, 0, none)],
    some [some 9, none, some 81, some (19 / 2)])

#eval IndexedCompositionParityTest.check "ranked-private-success"
  (privateObservation 4 4)
  ("complete",
    [("write", 40, 402, some 9), ("publish", 2, 0, some 9),
      ("write", 60, 602, some (7 / 2)), ("publish", 4, 0, some (7 / 2)),
      ("write", 41, 403, some 81), ("publish", 3, 0, some 81),
      ("write", 61, 603, some (19 / 2)), ("publish", 5, 0, some (19 / 2))],
    [([some 3, none, none, none, none], []),
      ([some 3, none, none, none, none], [(402, 9)]),
      ([some 3, some 9, none, none, none], [(402, 9)]),
      ([some 3, some 9, none, none, none], [(402, 9), (602, 7 / 2)]),
      ([some 3, some 9, some (7 / 2), none, none], [(402, 9), (602, 7 / 2)]),
      ([some 3, some 9, some (7 / 2), none, none], [(402, 9), (602, 7 / 2), (403, 81)]),
      ([some 3, some 9, some (7 / 2), some 81, none],
        [(402, 9), (602, 7 / 2), (403, 81)]),
      ([some 3, some 9, some (7 / 2), some 81, none],
        [(402, 9), (602, 7 / 2), (403, 81), (603, 19 / 2)]),
      ([some 3, some 9, some (7 / 2), some 81, some (19 / 2)],
        [(402, 9), (602, 7 / 2), (403, 81), (603, 19 / 2)])])

#eval IndexedCompositionParityTest.check "ranked-private-upstream-failure"
  (privateObservation 0 4)
  ("failed",
    [("write", 40, 402, some 9), ("publish", 2, 0, some 9), ("undefined", 60, 0, none)],
    [([some 3, none, none, none, none], []),
      ([some 3, none, none, none, none], [(402, 9)]),
      ([some 3, some 9, none, none, none], [(402, 9)])])

#eval IndexedCompositionParityTest.check "ranked-private-downstream-failure"
  (privateObservation 4 0)
  ("failed",
    [("write", 40, 402, some 9), ("publish", 2, 0, some 9),
      ("write", 60, 602, some (7 / 2)), ("publish", 4, 0, some (7 / 2)),
      ("write", 41, 403, some 81), ("publish", 3, 0, some 81), ("undefined", 61, 0, none)],
    [([some 3, none, none, none, none], []),
      ([some 3, none, none, none, none], [(402, 9)]),
      ([some 3, some 9, none, none, none], [(402, 9)]),
      ([some 3, some 9, none, none, none], [(402, 9), (602, 7 / 2)]),
      ([some 3, some 9, some (7 / 2), none, none], [(402, 9), (602, 7 / 2)]),
      ([some 3, some 9, some (7 / 2), none, none], [(402, 9), (602, 7 / 2), (403, 81)]),
      ([some 3, some 9, some (7 / 2), some 81, none],
        [(402, 9), (602, 7 / 2), (403, 81)])])

#eval IndexedCompositionParityTest.check "ranked-unranked-counterexample"
  unrankedObservation
  ("blocked",
    [("write", 40, 402, some 0), ("publish", 2, 0, some 0),
      ("write", 61, 603, some 1), ("publish", 3, 0, some 1)],
    [([none, none, none], []), ([none, none, none], [(402, 0)]),
      ([none, some 0, none], [(402, 0)]),
      ([none, some 0, none], [(402, 0), (603, 1)]),
      ([none, some 0, some 1], [(402, 0), (603, 1)])])

end IndexedComponentRankedExecutionFixtures
