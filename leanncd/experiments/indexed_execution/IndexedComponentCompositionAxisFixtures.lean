import IndexedComponentCompositionAssemble
import IndexedComponentTransportTest

namespace IndexedComponentCompositionAxisFixtures

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor
open IndexedOpenComposition
open IndexedComponentComposition
open IndexedComponentTransport
open IndexedComponentTransportTest (srcShape dstShape swapDomain p q pointPolicy)

@[reducible] def producerDeclarations : Declarations Unit :=
  ⟨Fin 1, fun t => t.val, fun _ _ h => Fin.ext h, fun _ => ⟨(), dstShape⟩⟩

def producerCoord (i : Fin 6) : Coord dstShape :=
  (canonicalLayout dstShape).enumerate i

@[reducible] def producer : Program RationalReference.Carrier
    producerDeclarations RationalReference.registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun _ => true
  output_defined := by intro _ _; rfl
  statements := fun _ => 6
  valuations := fun _ _ => 1
  guard := fun _ _ _ => true
  destination := fun _ s _ => producerCoord s
  body := fun _ s => .lit (s.val + 1)

def producerSchedule : Schedule producer where
  tensors := [0]
  tensors_nodup := by simp
  tensors_complete := by intro t; fin_cases t; simp
  keys := [
    .occurrence ⟨0, rfl⟩ ⟨0, ⟨0, rfl⟩⟩, .publication ⟨0, rfl⟩ (producerCoord 0),
    .occurrence ⟨0, rfl⟩ ⟨1, ⟨0, rfl⟩⟩, .publication ⟨0, rfl⟩ (producerCoord 1),
    .occurrence ⟨0, rfl⟩ ⟨2, ⟨0, rfl⟩⟩, .publication ⟨0, rfl⟩ (producerCoord 2),
    .occurrence ⟨0, rfl⟩ ⟨3, ⟨0, rfl⟩⟩, .publication ⟨0, rfl⟩ (producerCoord 3),
    .occurrence ⟨0, rfl⟩ ⟨4, ⟨0, rfl⟩⟩, .publication ⟨0, rfl⟩ (producerCoord 4),
    .occurrence ⟨0, rfl⟩ ⟨5, ⟨0, rfl⟩⟩, .publication ⟨0, rfl⟩ (producerCoord 5)]
  keys_nodup := by
    simp [List.nodup_cons, Key.occurrence.injEq, Key.publication.injEq,
      producerCoord, canonicalLayout]
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨t, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      have hv' : v = 0 := Subsingleton.elim _ _
      subst v
      fin_cases t; fin_cases s <;> simp
    | publication t c =>
      rcases t with ⟨t, ht⟩
      fin_cases t
      rcases c with ⟨i, j, ⟨⟩⟩
      fin_cases i <;> fin_cases j <;> simp [producerCoord, canonicalLayout]
      all_goals decide

def producerContract : Contract producerDeclarations :=
  ⟨[0], fun _ => false,
    (List.finRange 6).map (fun i => (⟨0, producerCoord i⟩, [510 + i.val])), [],
    (List.finRange 6).map (fun i => ⟨0, producerCoord i⟩)⟩

def producerFragment : Fragment producerDeclarations :=
  ⟨(List.finRange 6).map fun i =>
    ⟨110 + i.val, 510 + i.val, ⟨0, producerCoord i⟩, [], .lit (i.val + 1)⟩⟩

def producerGraph : Closed producerDeclarations :=
  ⟨producerContract, canonicalSteps producerContract producerFragment⟩

def producerEquiv : SourceOccurrence producer ≃ Fin producerFragment.writers.length where
  toFun := fun o => ⟨o.2.1.val, by simp [producerFragment]⟩
  invFun := fun i => ⟨⟨0, rfl⟩, ⟨⟨i.val, by simpa [producerFragment] using i.isLt⟩,
    ⟨0, rfl⟩⟩⟩
  left_inv := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t
    rfl
  right_inv := fun _ => rfl

def producerMatch : SourceContractMatch producer producerSchedule
    producerContract producerFragment producerGraph where
  close_ok := rfl
  input_roles := rfl
  tensor_order := rfl
  outputs_exact := by
    rintro ⟨t, i, j, ⟨⟩⟩
    fin_cases t; fin_cases i <;> fin_cases j <;>
      simp [producerContract, List.finRange, producerCoord, canonicalLayout]
    all_goals decide
  sourceToWriter := producerEquiv
  writer_destination := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t; fin_cases s <;> rfl
  writer_reads := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t; fin_cases s <;> rfl
  eval_agrees := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩ store
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t; fin_cases s <;> rfl
  priority := rfl

@[reducible] def consumerDeclarations : Declarations Unit :=
  ⟨Fin 2, fun t => t.val, fun _ _ h => Fin.ext h,
    fun t => ⟨(), if t == 0 then srcShape else []⟩⟩

def readPre (c : Coord srcShape) : Expr RationalReference.Carrier
    consumerDeclarations RationalReference.registry Γ (.scalar ()) :=
  .read 0 ⟨pointPolicy, fun _ => Coord.raw c, fun _ => .at c,
    fun _ => pointPolicy.inBounds c⟩

def firstPoint : Coord srcShape := p

def consumerBody : Body consumerDeclarations :=
  .binary .add (readPre firstPoint)
    (.binary .add (readPre q) (.binary .add (readPre firstPoint) (readPre q)))

@[reducible] def consumer : Program RationalReference.Carrier
    consumerDeclarations RationalReference.registry where
  tensors := inferInstance
  input := fun t => t == 0
  output := fun t => t == 1
  output_defined := by intro t h; fin_cases t <;> simp_all
  statements := fun _ => 1
  valuations := fun _ _ => 1
  guard := fun _ _ _ => true
  destination := by
    rintro ⟨t, ht⟩ _ _
    have he : t = 1 := by
      fin_cases t
      · exact False.elim (Bool.noConfusion ht)
      · rfl
    subst t
    exact ()
  body := fun _ _ =>
    .binary .add (readPre firstPoint)
      (.binary .add (readPre q) (.binary .add (readPre firstPoint) (readPre q)))

def consumerSchedule : Schedule consumer where
  tensors := [0, 1]
  tensors_nodup := by decide
  tensors_complete := by intro t; fin_cases t <;> simp
  keys := [.occurrence ⟨1, rfl⟩ ⟨0, ⟨0, rfl⟩⟩, .publication ⟨1, rfl⟩ ()]
  keys_nodup := by simp
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨t, ht⟩
      change (t == 0) = false at ht
      rcases o with ⟨s, ⟨v, hv⟩⟩
      have hv' : v = 0 := Subsingleton.elim _ _
      subst v
      fin_cases t <;> fin_cases s <;>
        first | exact False.elim (Bool.noConfusion ht) | simp
    | publication t c =>
      rcases t with ⟨t, ht⟩
      change (t == 0) = false at ht
      fin_cases t
      · exact False.elim (Bool.noConfusion ht)
      · cases c; simp

def consumerContract : Contract consumerDeclarations :=
  ⟨[0, 1], fun t => t == 0, [(⟨1, ()⟩, [701])],
    (List.finRange 6).map (fun i => ⟨0, (canonicalLayout srcShape).enumerate i⟩),
    [⟨1, ()⟩]⟩

def consumerFragment : Fragment consumerDeclarations :=
  ⟨[⟨210, 701, ⟨1, ()⟩, [⟨0, firstPoint⟩, ⟨0, q⟩, ⟨0, firstPoint⟩, ⟨0, q⟩], consumerBody⟩]⟩

def consumerGraph : Closed consumerDeclarations :=
  ⟨consumerContract, canonicalSteps consumerContract consumerFragment⟩

def consumerEquiv : SourceOccurrence consumer ≃ Fin consumerFragment.writers.length where
  toFun := fun _ => ⟨0, by simp [consumerFragment]⟩
  invFun := fun _ => ⟨⟨1, rfl⟩, ⟨0, ⟨0, rfl⟩⟩⟩
  left_inv := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    change (t == 0) = false at ht
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t <;> fin_cases s <;>
      first | exact False.elim (Bool.noConfusion ht) | rfl
  right_inv := by intro i; fin_cases i; rfl

def consumerMatch : SourceContractMatch consumer consumerSchedule
    consumerContract consumerFragment consumerGraph where
  close_ok := rfl
  input_roles := rfl
  tensor_order := rfl
  outputs_exact := by
    rintro ⟨t, c⟩
    fin_cases t
    · simp [consumerContract]
    · cases c; simp [consumerContract]
  sourceToWriter := consumerEquiv
  writer_destination := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    change (t == 0) = false at ht
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t <;> fin_cases s <;>
      first | exact False.elim (Bool.noConfusion ht) | rfl
  writer_reads := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    change (t == 0) = false at ht
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t <;> fin_cases s <;>
      first | exact False.elim (Bool.noConfusion ht) | rfl
  eval_agrees := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩ store
    change (t == 0) = false at ht
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t <;> fin_cases s <;>
      first | exact False.elim (Bool.noConfusion ht) | rfl
  priority := rfl

def axisProducer : MatchedComponent producerDeclarations where
  program := producer
  schedule := producerSchedule
  contract := producerContract
  fragment := producerFragment
  graph := producerGraph
  matched := producerMatch
  inputs := []
  outputs := [⟨0, (), dstShape, rfl, rfl⟩]
  inputs_nodup := by simp
  outputs_nodup := by simp
  inputs_exact := by intro t; fin_cases t; simp
  outputs_exact := by intro t; fin_cases t; simp

def axisConsumer : MatchedComponent consumerDeclarations where
  program := consumer
  schedule := consumerSchedule
  contract := consumerContract
  fragment := consumerFragment
  graph := consumerGraph
  matched := consumerMatch
  inputs := [⟨0, (), srcShape, rfl, rfl⟩]
  outputs := [⟨1, (), [], rfl, rfl⟩]
  inputs_nodup := by simp
  outputs_nodup := by simp
  inputs_exact := by intro t; fin_cases t <;> simp
  outputs_exact := by intro t; fin_cases t <;> simp

def axisBoundary : Boundary axisProducer axisConsumer where
  matched :=
    { toFun := fun _ => ⟨0, rfl⟩
      invFun := fun _ => ⟨0, rfl⟩
      left_inv := by
        rintro ⟨t, ht⟩
        change (t == 0) = true at ht
        fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion ht)
      right_inv := by intro t; apply Subtype.ext; exact Subsingleton.elim _ _ }
  domain := by
    rintro ⟨t, ht⟩
    change (t == 0) = true at ht
    have he : t = 0 := by
      fin_cases t
      · rfl
      · exact False.elim (Bool.noConfusion ht)
    subst t
    exact swapDomain

def axisContract := contract axisProducer axisConsumer axisBoundary
def axisFragment := fragment axisProducer axisConsumer axisBoundary
def axisGraph := graph axisProducer axisConsumer axisBoundary

theorem axis_close_ok : close axisContract axisFragment = .ok axisGraph :=
  close_ok axisProducer axisConsumer axisBoundary

def axisRun := runChecked axisContract axisFragment (fun _ => none)

def axisAddressRows (as : List (Address (declarations axisProducer axisConsumer))) :
    List (Nat × Nat × Nat) :=
  as.map fun a => match a with
    | ⟨.inl _, c⟩ => (0, c.1.val, c.2.1.val)
    | ⟨.inr _, _⟩ => (1, 0, 0)

def axisMappedReads := axisAddressRows axisFragment.writers[6].reads
def axisMappedFootprint := axisAddressRows (footprint axisFragment.writers[6].body ())

def axisWriterProvenance : List (Nat × Nat × Nat × List Nat) :=
  axisFragment.writers.map fun w =>
    (w.tag, w.capability, (declarations axisProducer axisConsumer).uid w.destination.1,
      match w.destination with
      | ⟨.inl _, c⟩ => [c.1.val, c.2.1.val]
      | ⟨.inr _, _⟩ => [])

def axisEvents : List (String × Nat × Nat × ℚ) :=
  axisRun.events.map fun e => match e with
    | .produced tag cap value => ("write", tag, cap, value)
    | .sealed a value =>
      ("publish", (declarations axisProducer axisConsumer).uid a.1, 0, value)
    | .undefined tag => ("undefined", tag, 0, 0)

def axisValues := axisRun.states.getLast?.map fun s =>
  ((List.finRange 6).map (fun i => s.available ⟨.inl 0, producerCoord i⟩),
    s.available ⟨.inr ⟨1, rfl⟩, ()⟩)

#eval (axisRun.outcome.kind, axisMappedReads, axisMappedFootprint,
  axisWriterProvenance, axisEvents, axisValues)

#eval IndexedComponentTransportTest.check "axis.graph-only"
  (axisRun.outcome.kind == "complete" &&
    axisMappedReads == [(0, 2, 0), (0, 0, 1), (0, 2, 0), (0, 0, 1)] &&
    axisMappedFootprint == axisMappedReads &&
    axisWriterProvenance == [
      (220, 1020, 0, [0, 0]), (222, 1022, 0, [0, 1]),
      (224, 1024, 0, [1, 0]), (226, 1026, 0, [1, 1]),
      (228, 1028, 0, [2, 0]), (230, 1030, 0, [2, 1]), (421, 1403, 3, [])] &&
    axisEvents == [
      ("write", 220, 1020, 1), ("publish", 0, 0, 1),
      ("write", 222, 1022, 2), ("publish", 0, 0, 2),
      ("write", 224, 1024, 3), ("publish", 0, 0, 3),
      ("write", 226, 1026, 4), ("publish", 0, 0, 4),
      ("write", 228, 1028, 5), ("publish", 0, 0, 5),
      ("write", 230, 1030, 6), ("publish", 0, 0, 6),
      ("write", 421, 1403, 14), ("publish", 3, 0, 14)] &&
    axisValues == some ([some 1, some 2, some 3, some 4, some 5, some 6], some 14))

end IndexedComponentCompositionAxisFixtures
