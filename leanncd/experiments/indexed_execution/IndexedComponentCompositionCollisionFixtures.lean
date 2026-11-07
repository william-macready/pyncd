import IndexedComponentCompositionAssemble
import IndexedComponentCompositionPortFixtures
import IndexedComponentTransportTest

namespace IndexedComponentCompositionCollisionFixtures

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor
open IndexedOpenComposition
open IndexedComponentComposition
open IndexedComponentTransport

@[reducible] def producerDeclarations : Declarations Unit :=
  ⟨Fin 2, fun t => 2 * t.val,
    by intro a b h; apply Fin.ext; change 2 * a.val = 2 * b.val at h; omega,
    fun _ => ⟨(), []⟩⟩

@[reducible] def producer : Program RationalReference.Carrier
    producerDeclarations RationalReference.registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun t => t == 0
  output_defined := by intro _ _; rfl
  statements := fun _ => 1
  valuations := fun t _ => if t.val.val == 0 then 3 else 1
  guard := fun t _ v => if t.val.val == 0 then v.val != 1 else true
  destination := fun _ _ _ => ()
  body := fun t _ => if t.val.val == 0 then .lit 1 else .lit 7

def producerSchedule : Schedule producer where
  tensors := [0, 1]
  tensors_nodup := by decide
  tensors_complete := by intro t; fin_cases t <;> simp
  keys := [
    .occurrence ⟨1, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
    .publication ⟨1, rfl⟩ (),
    .occurrence ⟨0, rfl⟩ ⟨0, ⟨2, rfl⟩⟩,
    .occurrence ⟨0, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
    .publication ⟨0, rfl⟩ ()]
  keys_nodup := by
    simp [List.nodup_cons, Key.occurrence.injEq, Key.publication.injEq, producer]
    intro h
    have he := congrArg (fun o : producer.Occurrence ⟨0, rfl⟩ => o.2.val.val) h
    exact Nat.noConfusion he
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨t, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      fin_cases t <;> fin_cases s <;> fin_cases v <;>
        first | exact False.elim (Bool.noConfusion hv) | simp [producer]
      all_goals first | exact Or.inl rfl | exact Or.inr rfl | rfl
    | publication t p =>
      rcases t with ⟨t, ht⟩
      cases p
      fin_cases t <;> simp

def producerContract : Contract producerDeclarations :=
  ⟨[0, 1], fun _ => false,
    [(⟨1, ()⟩, [301]), (⟨0, ()⟩, [102, 101])], [], [⟨0, ()⟩]⟩

def producerFragment : Fragment producerDeclarations :=
  ⟨[⟨10, 101, ⟨0, ()⟩, [], .lit 1⟩,
    ⟨11, 102, ⟨0, ()⟩, [], .lit 1⟩,
    ⟨30, 301, ⟨1, ()⟩, [], .lit 7⟩]⟩

def producerGraph : Closed producerDeclarations :=
  ⟨producerContract, canonicalSteps producerContract producerFragment⟩

def producerIndex (o : SourceOccurrence producer) : Fin 3 :=
  if o.1.val.val == 0 then
    if o.2.2.val.val == 0 then 0 else 1
  else 2

def producerOccurrence (i : Fin 3) : SourceOccurrence producer :=
  if i.val == 0 then ⟨⟨0, rfl⟩, ⟨0, ⟨0, rfl⟩⟩⟩
  else if i.val == 1 then ⟨⟨0, rfl⟩, ⟨0, ⟨2, rfl⟩⟩⟩
  else ⟨⟨1, rfl⟩, ⟨0, ⟨0, rfl⟩⟩⟩

def producerEquiv : SourceOccurrence producer ≃ Fin producerFragment.writers.length where
  toFun := producerIndex
  invFun := producerOccurrence
  left_inv := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    fin_cases t <;> fin_cases s <;> fin_cases v <;>
      first | exact False.elim (Bool.noConfusion hv) | rfl
  right_inv := by intro i; fin_cases i <;> rfl

def producerMatch : SourceContractMatch producer producerSchedule
    producerContract producerFragment producerGraph where
  close_ok := rfl
  input_roles := rfl
  tensor_order := rfl
  outputs_exact := by rintro ⟨t, p⟩; cases p; fin_cases t <;> simp [producerContract]
  sourceToWriter := producerEquiv
  writer_destination := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    fin_cases t <;> fin_cases s <;> fin_cases v <;>
      first | exact False.elim (Bool.noConfusion hv) | rfl
  writer_reads := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    fin_cases t <;> fin_cases s <;> fin_cases v <;>
      first | exact False.elim (Bool.noConfusion hv) | rfl
  eval_agrees := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩ store
    fin_cases t <;> fin_cases s <;> fin_cases v <;>
      first | exact False.elim (Bool.noConfusion hv) | rfl
  priority := rfl

def collisionProducer : MatchedComponent producerDeclarations where
  program := producer
  schedule := producerSchedule
  contract := producerContract
  fragment := producerFragment
  graph := producerGraph
  matched := producerMatch
  inputs := []
  outputs := [⟨0, (), [], rfl, rfl⟩]
  inputs_nodup := by simp
  outputs_nodup := by simp
  inputs_exact := by intro t; fin_cases t <;> simp
  outputs_exact := by intro t; fin_cases t <;> simp

def collisionConsumer := IndexedComponentCompositionPortFixtures.consumerComponent 4

def collisionBoundary : Boundary collisionProducer collisionConsumer where
  matched :=
    { toFun := fun _ => ⟨0, rfl⟩
      invFun := fun _ => ⟨0, rfl⟩
      left_inv := by
        rintro ⟨t, ht⟩
        change (t == 0) = true at ht
        fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion ht)
      right_inv := by
        rintro ⟨t, ht⟩
        change (t == 0) = true at ht
        fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion ht) }
  domain := fun _ => Domain.id []

def collisionContract := contract collisionProducer collisionConsumer collisionBoundary
def collisionFragment := fragment collisionProducer collisionConsumer collisionBoundary
def collisionGraph := graph collisionProducer collisionConsumer collisionBoundary

theorem collision_close_ok :
    close collisionContract collisionFragment = .ok collisionGraph :=
  close_ok collisionProducer collisionConsumer collisionBoundary

def collisionRun := runChecked collisionContract collisionFragment (fun _ => none)

def collisionWriterProvenance : List (Nat × Nat × Nat) :=
  collisionFragment.writers.map fun w =>
    (w.tag, w.capability, (declarations collisionProducer collisionConsumer).uid w.destination.1)

def collisionEvents : List (String × Nat × Nat × ℚ) :=
  collisionRun.events.map fun e => match e with
    | .produced tag cap value => ("write", tag, cap, value)
    | .sealed a value =>
      ("publish", (declarations collisionProducer collisionConsumer).uid a.1, 0, value)
    | .undefined tag => ("undefined", tag, 0, 0)

def collisionValues : Option (List (Option ℚ)) :=
  collisionRun.states.getLast?.map fun s =>
    [s.available ⟨.inl 0, ()⟩, s.available ⟨.inr ⟨1, rfl⟩, ()⟩,
      s.available ⟨.inl 1, ()⟩, s.available ⟨.inr ⟨2, rfl⟩, ()⟩]

def collisionPreMetadata : Nat × Nat × List Bool :=
  (producer.statements ⟨0, rfl⟩, producer.valuations ⟨0, rfl⟩ 0,
    (List.finRange 3).map (producer.guard ⟨0, rfl⟩ 0))

def collisionAssembledPreMetadata : Nat × Nat × List Bool :=
  let P := program collisionProducer collisionConsumer collisionBoundary
  let t := upstreamDefined collisionProducer collisionConsumer collisionBoundary ⟨0, rfl⟩
  let s : Fin (P.statements t) := ⟨0, by decide⟩
  (P.statements t, P.valuations t s, (List.finRange 3).map (P.guard t s))

def collisionAdmittedSourceOrder : List (Nat × Nat × Nat × Nat × Nat) :=
  producerSchedule.keys.filterMap fun k => match k with
    | .occurrence t o => some
      (t.val.val, o.1.val, o.2.val.val, (producerMatch.writer ⟨t, o⟩).tag,
        (producerMatch.writer ⟨t, o⟩).capability)
    | .publication _ _ => none

def collisionAssembledAdmittedSourceOrder : List (Nat × Nat × Nat) :=
  (schedule collisionProducer collisionConsumer collisionBoundary).keys.filterMap fun k =>
    match k with
    | .occurrence t o => match t.val with
      | .inl a => some (a.val, o.1.val, o.2.val.val)
      | .inr _ => none
    | .publication _ _ => none

#eval (collisionPreMetadata, collisionAssembledPreMetadata, collisionAdmittedSourceOrder,
  collisionAssembledAdmittedSourceOrder,
  collisionRun.outcome.kind, collisionWriterProvenance, collisionEvents, collisionValues)

#eval IndexedComponentTransportTest.check "collision.graph-only"
  (collisionRun.outcome.kind == "complete" &&
    collisionPreMetadata == (1, 3, [true, false, true]) &&
    collisionAssembledPreMetadata == collisionPreMetadata &&
    collisionAdmittedSourceOrder == [(1, 0, 0, 30, 301), (0, 0, 2, 11, 102),
      (0, 0, 0, 10, 101)] &&
    collisionAssembledAdmittedSourceOrder == [(1, 0, 0), (0, 0, 2), (0, 0, 0)] &&
    collisionWriterProvenance == [(20, 202, 0), (22, 204, 0), (60, 602, 4),
      (41, 403, 3), (61, 603, 5)] &&
    collisionEvents == [
      ("write", 60, 602, 7), ("publish", 4, 0, 7),
      ("write", 22, 204, 1), ("write", 20, 202, 1), ("publish", 0, 0, 2),
      ("write", 41, 403, 4), ("publish", 3, 0, 4),
      ("write", 61, 603, 5 / 2), ("publish", 5, 0, 5 / 2)] &&
    collisionValues == some [some 2, some 4, some 7, some (5 / 2)])

end IndexedComponentCompositionCollisionFixtures
