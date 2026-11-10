import IndexedOperationalReassociation
import IndexedComponentRankedExecutionTest

namespace IndexedOperationalAssociativityFixtures

open LeanNCD.Semantics
open IndexedOpenComposition
open IndexedComponentTransport
open IndexedComponentComposition
open IndexedComponentExecution
open IndexedWitness
open IndexedComponentCompositionPortFixtures
open IndexedComponentRankedExecutionFixtures

def addresses (σ : Declarations Unit) (tensors : List σ.Tensor) : List (Address σ) :=
  tensors.flatMap fun t =>
    (List.finRange (canonicalLayout (σ.signature t).axes).count).map fun i =>
      ⟨t, (canonicalLayout (σ.signature t).axes).enumerate i⟩

abbrev EventRow := String × Nat × Nat × Option ℚ
abbrev StateRow := List (Option ℚ) × List (Nat × ℚ)

def eventRow {σ : Declarations Unit} : Event σ → EventRow
  | .produced tag cap value => ("produce", tag, cap, some value)
  | .sealed a value =>
      ("publish", σ.uid a.1,
        ((canonicalLayout (σ.signature a.1).axes).enumerate.symm a.2).val, some value)
  | .undefined tag => ("undefined", tag, 0, none)

def stateRow {σ : Declarations Unit} (roster : List (Address σ))
    (rename : Nat → Nat) (s : State σ) : StateRow :=
  (roster.map s.available, mapLedger rename s.produced)

def outcomeRow {σ : Declarations Unit} (roster : List (Address σ))
    (rename : Nat → Nat) (outcome : Outcome σ) :
    String × Option Nat × Option StateRow :=
  match outcome with
  | .complete s => ("complete", none, some (stateRow roster rename s))
  | .failed tag s => ("failed", some (rename tag), some (stateRow roster rename s))
  | other => (other.kind, none, none)

variable {σA σB σC : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable [Fintype σC.Tensor] [DecidableEq σC.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (C : MatchedComponent σC) (ab : Boundary A B) (bc : Boundary B C)

def leftInput (η : A.program.Input) :=
  liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
    (liftInput A B ab η)

def rightInput (η : A.program.Input) :=
  liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η

def leftRun (η : A.program.Input) :=
  runChecked (leftBracket A B C ab bc).contract (leftBracket A B C ab bc).fragment
    (leftInput A B C ab bc η).val

def rightRun (η : A.program.Input) :=
  runChecked (rightBracket A B C ab bc).contract (rightBracket A B C ab bc).fragment
    (rightInput A B C ab bc η).val

def comparison (η : A.program.Input) :=
  let l := leftRun A B C ab bc η
  let r := rightRun A B C ab bc η
  let roster := addresses _ (leftBracket A B C ab bc).contract.tensors
  let rightRoster := roster.map (IndexedOperationalReassociation.addressEquiv A B C ab bc)
  let events := l.events.map
    (mapEvent (IndexedOperationalReassociation.embedding A B C ab bc)
      IndexedOperationalReassociation.identityEquiv)
  (decide (outcomeRow roster IndexedOperationalReassociation.identityEquiv l.outcome =
      outcomeRow rightRoster id r.outcome),
    decide (events.map eventRow = r.events.map eventRow),
    decide (l.states.map (stateRow roster IndexedOperationalReassociation.identityEquiv) =
      r.states.map (stateRow rightRoster id)))

def privateComparison (a b c : ℚ) :=
  comparison (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c) (privateInput a)

def privateCounts (a b c : ℚ) :=
  let l := leftRun (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c) (privateInput a)
  let r := rightRun (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c) (privateInput a)
  (l.outcome.kind, l.events.length, l.states.length,
    r.outcome.kind, r.events.length, r.states.length)

def axisTailBoundary :
    Boundary IndexedComponentCompositionAxisFixtures.axisConsumer (consumerComponent 4) where
  matched :=
    { toFun := fun _ => ⟨1, rfl⟩
      invFun := fun _ => ⟨0, rfl⟩
      left_inv := by
        rintro ⟨t, h⟩
        change (t == 0) = true at h
        fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion h)
      right_inv := by
        rintro ⟨t, h⟩
        change (t == 1) = true at h
        fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion h) }
  domain := by
    rintro ⟨t, h⟩
    change (t == 0) = true at h
    have ht : t = 0 := by
      fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion h)
    subst t
    exact Domain.id []

def emptyTailBoundary : Boundary emptyConsumerComponent emptyConsumerComponent where
  matched :=
    { toFun := fun _ => ⟨emptyConsumerOut, rfl⟩
      invFun := fun _ => ⟨emptyConsumerPre, rfl⟩
      left_inv := by
        rintro ⟨t, h⟩
        change (t == 0) = true at h
        fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion h)
      right_inv := by
        rintro ⟨t, h⟩
        change (t == 1) = true at h
        fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion h) }
  domain := fun _ => Domain.id _

def collectionComparison :=
  comparison producerComponent (consumerComponent 4) (consumerComponent 4)
    (scalarBoundary 4) (privateBoundary 4 4) IndexedComponentRankedExecutionTest.producerInput

def zeroComparison :=
  comparison zeroProducerComponent (consumerComponent 4) (consumerComponent 4)
    zeroBoundary (privateBoundary 4 4) IndexedComponentRankedExecutionTest.zeroProducerInput

def axisComparison :=
  comparison IndexedComponentCompositionAxisFixtures.axisProducer
    IndexedComponentCompositionAxisFixtures.axisConsumer (consumerComponent 4)
    IndexedComponentCompositionAxisFixtures.axisBoundary axisTailBoundary
    IndexedComponentRankedExecutionTest.axisInput

def collisionComparison :=
  comparison IndexedComponentCompositionCollisionFixtures.collisionProducer
    IndexedComponentCompositionCollisionFixtures.collisionConsumer (consumerComponent 4)
    IndexedComponentCompositionCollisionFixtures.collisionBoundary (privateBoundary 4 4)
    IndexedComponentRankedExecutionTest.collisionInput

def emptyComparison :=
  comparison emptyProducerComponent emptyConsumerComponent emptyConsumerComponent
    emptyBoundary emptyTailBoundary emptyValidatedInput

def emptyObservation :=
  let l := leftBracket emptyProducerComponent emptyConsumerComponent emptyConsumerComponent
    emptyBoundary emptyTailBoundary
  let η := leftInput emptyProducerComponent emptyConsumerComponent emptyConsumerComponent
    emptyBoundary emptyTailBoundary emptyValidatedInput
  let result := leftRun emptyProducerComponent emptyConsumerComponent emptyConsumerComponent
    emptyBoundary emptyTailBoundary emptyValidatedInput
  (result.outcome.kind, result.events.length, result.states.length,
    l.graph.steps.length + 1,
    l.contract.tensors.map fun t => (l.program.input t, (η.val t).isSome))

def referenceStateRow {σ τ : Declarations Unit} [Fintype σ.Tensor]
    [DecidableEq σ.Tensor]
    {P : Program RationalReference.Carrier σ RationalReference.registry}
    {schedule : Program.Executor.Schedule P} {contract : Contract σ}
    {fragment : Fragment σ} {graph : Closed σ}
    (matched : SourceContractMatch P schedule contract fragment graph)
    (mapAddress : Address σ → Address τ) (rename : Nat → Nat)
    (roster : List (Address σ)) (s : P.Running) :
    List (Option ℚ) × List (Nat × Bool) × List (Nat × Nat × ℚ) :=
  (roster.map (fun a => (s.published a : Option ℚ)),
    schedule.keys.filterMap fun
      | .occurrence t o => some (rename (matched.capability ⟨t, o⟩),
          decide (o ∈ s.pending t))
      | .publication _ _ => none,
    schedule.keys.filterMap fun
      | .occurrence _ _ => none
      | .publication t p =>
          let a := mapAddress ⟨t.val, p⟩
          some (τ.uid a.1,
            ((canonicalLayout (τ.signature a.1).axes).enumerate.symm a.2).val,
            (s.accumulators t p : ℚ)))

def referenceComparison (η : A.program.Input) :=
  let l := leftBracket A B C ab bc
  let r := rightBracket A B C ab bc
  let li := leftInput A B C ab bc η
  let ri := rightInput A B C ab bc η
  let lr := Program.Executor.run l.program RationalReference.ops l.schedule li
  let rr := Program.Executor.run r.program RationalReference.ops r.schedule ri
  let roster := addresses _ l.contract.tensors
  let equiv := IndexedOperationalReassociation.addressEquiv A B C ab bc
  let le := (lr.events.map l.matched.event).map
    (mapEvent (IndexedOperationalReassociation.embedding A B C ab bc)
      IndexedOperationalReassociation.identityEquiv)
  let ls : List (List (Option ℚ) × List (Nat × Bool) × List (Nat × Nat × ℚ)) :=
    (Correspondence.referenceSnapshots (l.program.initial li) lr.events).map
    (referenceStateRow (τ := declarations A (compose B C bc)) l.matched equiv
      IndexedOperationalReassociation.identityEquiv roster)
  let rs : List (List (Option ℚ) × List (Nat × Bool) × List (Nat × Nat × ℚ)) :=
    (Correspondence.referenceSnapshots (r.program.initial ri) rr.events).map
    (referenceStateRow (τ := declarations A (compose B C bc)) r.matched id id (roster.map equiv))
  (decide (le.map eventRow = (rr.events.map r.matched.event).map eventRow),
    ls == rs, lr.events.length, ls.length, rr.events.length, rs.length)

def privateReference (a b c : ℚ) :=
  referenceComparison (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c) (privateInput a)

def donorReferences :=
  [referenceComparison producerComponent (consumerComponent 4) (consumerComponent 4)
      (scalarBoundary 4) (privateBoundary 4 4) IndexedComponentRankedExecutionTest.producerInput,
    referenceComparison zeroProducerComponent (consumerComponent 4) (consumerComponent 4)
      zeroBoundary (privateBoundary 4 4) IndexedComponentRankedExecutionTest.zeroProducerInput,
    referenceComparison IndexedComponentCompositionAxisFixtures.axisProducer
      IndexedComponentCompositionAxisFixtures.axisConsumer (consumerComponent 4)
      IndexedComponentCompositionAxisFixtures.axisBoundary axisTailBoundary
      IndexedComponentRankedExecutionTest.axisInput,
    referenceComparison IndexedComponentCompositionCollisionFixtures.collisionProducer
      IndexedComponentCompositionCollisionFixtures.collisionConsumer (consumerComponent 4)
      IndexedComponentCompositionCollisionFixtures.collisionBoundary (privateBoundary 4 4)
      IndexedComponentRankedExecutionTest.collisionInput,
    referenceComparison emptyProducerComponent emptyConsumerComponent emptyConsumerComponent
      emptyBoundary emptyTailBoundary emptyValidatedInput]

def privateRows (a b c : ℚ) :=
  let component := leftBracket (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c)
  let result := leftRun (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c) (privateInput a)
  result.states.map (stateRow (addresses _ component.contract.tensors) id)

def privateReferenceCuts :=
  let l := leftBracket (consumerComponent 4) (consumerComponent 4) (consumerComponent 4)
    (privateBoundary 4 4) (privateBoundary 4 4)
  let li := leftInput (consumerComponent 4) (consumerComponent 4) (consumerComponent 4)
    (privateBoundary 4 4) (privateBoundary 4 4) (privateInput 4)
  let lr := Program.Executor.run l.program RationalReference.ops l.schedule li
  let roster := addresses _ l.contract.tensors
  let rows := (Correspondence.referenceSnapshots (l.program.initial li) lr.events).map
    (referenceStateRow (τ := declarations (privateComposite 4 4) (consumerComponent 4))
      l.matched id id roster)
  (rows[4]?, rows[8]?)

def donorPrefixes :=
  let collected := leftRun producerComponent (consumerComponent 4) (consumerComponent 4)
    (scalarBoundary 4) (privateBoundary 4 4) IndexedComponentRankedExecutionTest.producerInput
  let zero := leftRun zeroProducerComponent (consumerComponent 4) (consumerComponent 4)
    zeroBoundary (privateBoundary 4 4) IndexedComponentRankedExecutionTest.zeroProducerInput
  let axisResult := leftRun IndexedComponentCompositionAxisFixtures.axisProducer
    IndexedComponentCompositionAxisFixtures.axisConsumer (consumerComponent 4)
    IndexedComponentCompositionAxisFixtures.axisBoundary axisTailBoundary
    IndexedComponentRankedExecutionTest.axisInput
  let collision := leftRun IndexedComponentCompositionCollisionFixtures.collisionProducer
    IndexedComponentCompositionCollisionFixtures.collisionConsumer (consumerComponent 4)
    IndexedComponentCompositionCollisionFixtures.collisionBoundary (privateBoundary 4 4)
    IndexedComponentRankedExecutionTest.collisionInput
  ((collected.events.take 3).map eventRow, (zero.events.take 2).map eventRow,
    axisResult.events.map eventRow, (collision.events.take 5).map eventRow)

def reorderedTripleRun :=
  let l := leftBracket (consumerComponent 4) (consumerComponent 4) (consumerComponent 4)
    (privateBoundary 4 4) (privateBoundary 4 4)
  let rows := l.contract.collectors
  let altered := { l.contract with
    collectors := rows.take 1 ++ rows.drop 2 ++ (rows.drop 1).take 1 }
  runChecked altered l.fragment
    (leftInput (consumerComponent 4) (consumerComponent 4) (consumerComponent 4)
      (privateBoundary 4 4) (privateBoundary 4 4) (privateInput 4)).val

def strongerThanFinalOutput :=
  let l := leftBracket (consumerComponent 4) (consumerComponent 4) (consumerComponent 4)
    (privateBoundary 4 4) (privateBoundary 4 4)
  let actual := leftRun (consumerComponent 4) (consumerComponent 4) (consumerComponent 4)
    (privateBoundary 4 4) (privateBoundary 4 4) (privateInput 4)
  let roster := addresses _ l.contract.tensors
  let original := actual.states.map (stateRow roster id)
  let changed := reorderedTripleRun.states.map (stateRow roster id)
  (actual.outcome.kind, reorderedTripleRun.outcome.kind,
    original.getLast?.map Prod.fst == changed.getLast?.map Prod.fst,
    original.getLast?.map Prod.snd == changed.getLast?.map Prod.snd,
    actual.events.map eventRow == reorderedTripleRun.events.map eventRow,
    original == changed)

#eval IndexedCompositionParityTest.check "operational-private-outcomes"
  [privateCounts 4 4 4, privateCounts 0 4 4, privateCounts 4 0 4, privateCounts 4 4 0]
  [("complete", 12, 13, "complete", 12, 13),
    ("failed", 3, 3, "failed", 3, 3),
    ("failed", 7, 7, "failed", 7, 7),
    ("failed", 11, 11, "failed", 11, 11)]

#eval IndexedCompositionParityTest.check "operational-private-full-observations"
  [privateComparison 4 4 4, privateComparison 0 4 4,
    privateComparison 4 0 4, privateComparison 4 4 0]
  [(true, true, true), (true, true, true), (true, true, true), (true, true, true)]

#eval IndexedCompositionParityTest.check "operational-donor-full-observations"
  [collectionComparison, zeroComparison, axisComparison, collisionComparison, emptyComparison]
  [(true, true, true), (true, true, true), (true, true, true),
    (true, true, true), (true, true, true)]

#eval IndexedCompositionParityTest.check "operational-empty-presence-coincident-cuts"
  emptyObservation
  ("complete", 0, 1, 1, [(true, true), (false, false), (false, false), (false, false)])

#eval IndexedCompositionParityTest.check "operational-private-reference"
  [privateReference 4 4 4, privateReference 0 4 4,
    privateReference 4 0 4, privateReference 4 4 0]
  [(true, true, 12, 13, 12, 13), (true, true, 3, 3, 3, 3),
    (true, true, 7, 7, 7, 7), (true, true, 11, 11, 11, 11)]

#eval IndexedCompositionParityTest.check "operational-donor-reference"
  donorReferences
  [(true, true, 11, 12, 11, 12), (true, true, 9, 10, 9, 10),
    (true, true, 18, 19, 18, 19), (true, true, 13, 14, 13, 14),
    (true, true, 0, 1, 0, 1)]

#eval IndexedCompositionParityTest.check "operational-private-snapshots"
  (privateRows 4 4 4)
  [([some 3, none, none, none, none, none, none], []),
    ([some 3, none, none, none, none, none, none], [(804, 9)]),
    ([some 3, some 9, none, none, none, none, none], [(804, 9)]),
    ([some 3, some 9, none, none, none, none, none], [(804, 9), (1204, 7 / 2)]),
    ([some 3, some 9, some (7 / 2), none, none, none, none], [(804, 9), (1204, 7 / 2)]),
    ([some 3, some 9, some (7 / 2), none, none, none, none],
      [(804, 9), (1204, 7 / 2), (806, 81)]),
    ([some 3, some 9, some (7 / 2), some 81, none, none, none],
      [(804, 9), (1204, 7 / 2), (806, 81)]),
    ([some 3, some 9, some (7 / 2), some 81, none, none, none],
      [(804, 9), (1204, 7 / 2), (806, 81), (1206, 19 / 2)]),
    ([some 3, some 9, some (7 / 2), some 81, some (19 / 2), none, none],
      [(804, 9), (1204, 7 / 2), (806, 81), (1206, 19 / 2)]),
    ([some 3, some 9, some (7 / 2), some 81, some (19 / 2), none, none],
      [(804, 9), (1204, 7 / 2), (806, 81), (1206, 19 / 2), (403, 6561)]),
    ([some 3, some 9, some (7 / 2), some 81, some (19 / 2), some 6561, none],
      [(804, 9), (1204, 7 / 2), (806, 81), (1206, 19 / 2), (403, 6561)]),
    ([some 3, some 9, some (7 / 2), some 81, some (19 / 2), some 6561, none],
      [(804, 9), (1204, 7 / 2), (806, 81), (1206, 19 / 2), (403, 6561), (603, 163 / 2)]),
    ([some 3, some 9, some (7 / 2), some 81, some (19 / 2), some 6561, some (163 / 2)],
      [(804, 9), (1204, 7 / 2), (806, 81), (1206, 19 / 2), (403, 6561), (603, 163 / 2)])]

#eval IndexedCompositionParityTest.check "operational-reference-shared-cuts"
  privateReferenceCuts
  (some
    ([some 3, some 9, some (7 / 2), none, none, none, none],
      [(804, false), (1204, false), (806, true), (1206, true), (403, true), (603, true)],
      [(4, 0, 9), (8, 0, 7 / 2), (6, 0, 0), (10, 0, 0), (3, 0, 0), (5, 0, 0)]),
   some
    ([some 3, some 9, some (7 / 2), some 81, some (19 / 2), none, none],
      [(804, false), (1204, false), (806, false), (1206, false), (403, true), (603, true)],
      [(4, 0, 9), (8, 0, 7 / 2), (6, 0, 81), (10, 0, 19 / 2), (3, 0, 0), (5, 0, 0)]))
#eval IndexedCompositionParityTest.check "operational-donor-event-order"
  donorPrefixes
  ([("produce", 40, 404, some 1), ("produce", 44, 408, some (-1)), ("publish", 0, 0, some 0)],
    [("publish", 0, 0, some 0), ("produce", 82, 806, some 0)],
    [("produce", 440, 2040, some 1), ("publish", 0, 0, some 1),
      ("produce", 444, 2044, some 2), ("publish", 0, 1, some 2),
      ("produce", 448, 2048, some 3), ("publish", 0, 2, some 3),
      ("produce", 452, 2052, some 4), ("publish", 0, 3, some 4),
      ("produce", 456, 2056, some 5), ("publish", 0, 4, some 5),
      ("produce", 460, 2060, some 6), ("publish", 0, 5, some 6),
      ("produce", 842, 2806, some 14), ("publish", 6, 0, some 14),
      ("produce", 41, 403, some 196), ("publish", 3, 0, some 196),
      ("produce", 61, 603, some (29 / 2)), ("publish", 5, 0, some (29 / 2))],
    [("produce", 120, 1204, some 7), ("publish", 8, 0, some 7),
      ("produce", 44, 408, some 1), ("produce", 40, 404, some 1), ("publish", 0, 0, some 2)])

#eval IndexedCompositionParityTest.check "operational-observation-stronger-than-final-values"
  strongerThanFinalOutput ("complete", "complete", true, false, false, false)

end IndexedOperationalAssociativityFixtures
