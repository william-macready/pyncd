import IndexedCompositionFixtureProof

namespace IndexedComponentCompositionLocalFixtures

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor
open IndexedOpenComposition

@[reducible] def producerDeclarations : Declarations Unit :=
  ⟨Fin 1, fun t => t.val, fun _ _ h => Fin.ext h, fun _ => ⟨(), []⟩⟩

@[reducible] def producer : Program RationalReference.Carrier
    producerDeclarations RationalReference.registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun _ => true
  output_defined := by intro _ _; rfl
  statements := fun _ => 2
  valuations := fun _ _ => 1
  guard := fun _ _ _ => true
  destination := fun _ _ _ => ()
  body := fun _ s => if s.val == 0 then .lit 1 else .lit (-1)

def producerSchedule : Schedule producer where
  tensors := [0]
  tensors_nodup := by simp
  tensors_complete := by intro t; fin_cases t; simp
  keys := [
    .occurrence ⟨0, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
    .occurrence ⟨0, rfl⟩ ⟨1, ⟨0, rfl⟩⟩,
    .publication ⟨0, rfl⟩ ()]
  keys_nodup := by
    simp [List.nodup_cons, Key.occurrence.injEq]
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨t, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      have hv' : v = 0 := Subsingleton.elim _ _
      subst v
      fin_cases t; fin_cases s <;> simp
    | publication t p =>
      rcases t with ⟨t, ht⟩
      cases p
      fin_cases t
      simp

def producerContract : Contract producerDeclarations :=
  ⟨[0], fun _ => false, [(⟨0, ()⟩, [101, 102])], [], [⟨0, ()⟩]⟩

def producerFragment : Fragment producerDeclarations :=
  ⟨[⟨10, 101, ⟨0, ()⟩, [], .lit 1⟩,
    ⟨11, 102, ⟨0, ()⟩, [], .lit (-1)⟩]⟩

def producerGraph : Closed producerDeclarations :=
  ⟨producerContract, canonicalSteps producerContract producerFragment⟩

def producerOccurrence (i : Fin 2) : SourceOccurrence producer :=
  ⟨⟨0, rfl⟩, ⟨i, ⟨0, rfl⟩⟩⟩

def producerEquiv : SourceOccurrence producer ≃ Fin producerFragment.writers.length where
  toFun := fun o => o.2.1
  invFun := producerOccurrence
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
  outputs_exact := by rintro ⟨t, p⟩; fin_cases t; cases p; simp [producerContract]
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

abbrev consumerDeclarations := IndexedCompositionParityTest.D

@[reducible] def consumer (other : ℚ) : Program RationalReference.Carrier
    consumerDeclarations RationalReference.registry where
  tensors := inferInstance
  input := fun t => t == 0
  output := fun t => t == 1
  output_defined := by intro t h; fin_cases t <;> simp_all
  statements := fun _ => 1
  valuations := fun _ _ => 1
  guard := fun _ _ _ => true
  destination := fun _ _ _ => ()
  body := fun t _ => if t.val == 1 then IndexedCompositionParityTest.squareBody _
    else IndexedCompositionParityTest.auditBody other _

def consumerSchedule (other : ℚ) : Schedule (consumer other) where
  tensors := [0, 1, 2]
  tensors_nodup := by decide
  tensors_complete := by intro t; fin_cases t <;> simp
  keys := [
    .occurrence ⟨1, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
    .publication ⟨1, rfl⟩ (),
    .occurrence ⟨2, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
    .publication ⟨2, rfl⟩ ()]
  keys_nodup := by
    simp [List.nodup_cons, Key.occurrence.injEq, Key.publication.injEq, Fin.ext_iff]
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨t, ht⟩
      change (t == 0) = false at ht
      rcases o with ⟨s, ⟨v, hv⟩⟩
      have hv' : v = 0 := Subsingleton.elim _ _
      subst v
      fin_cases t <;> fin_cases s <;> simp_all [consumer]
      exact False.elim (Bool.noConfusion ht)
    | publication t p =>
      rcases t with ⟨t, ht⟩
      change (t == 0) = false at ht
      cases p
      fin_cases t <;> simp_all [consumer]
      exact False.elim (Bool.noConfusion ht)

def consumerContract : Contract consumerDeclarations :=
  ⟨[0, 1, 2], fun t => t == 0,
    [(IndexedCompositionParityTest.out, [201]), (IndexedCompositionParityTest.audit, [301])],
    [IndexedCompositionParityTest.pre], [IndexedCompositionParityTest.out]⟩

def consumerFragment (other : ℚ) : Fragment consumerDeclarations :=
  ⟨[⟨20, 201, IndexedCompositionParityTest.out, [IndexedCompositionParityTest.pre],
      IndexedCompositionParityTest.squareBody Unit⟩,
    ⟨30, 301, IndexedCompositionParityTest.audit, [IndexedCompositionParityTest.pre],
      IndexedCompositionParityTest.auditBody other Unit⟩]⟩

def consumerGraph (other : ℚ) : Closed consumerDeclarations :=
  ⟨consumerContract, canonicalSteps consumerContract (consumerFragment other)⟩

def consumerIndex (other : ℚ) (o : SourceOccurrence (consumer other)) : Fin 2 :=
  if o.1.val.val == 1 then 0 else 1

def consumerOccurrence (other : ℚ) (i : Fin 2) : SourceOccurrence (consumer other) :=
  if i.val == 0 then ⟨⟨1, rfl⟩, ⟨0, ⟨0, rfl⟩⟩⟩
  else ⟨⟨2, rfl⟩, ⟨0, ⟨0, rfl⟩⟩⟩

def consumerEquiv (other : ℚ) :
    SourceOccurrence (consumer other) ≃ Fin (consumerFragment other).writers.length where
  toFun := consumerIndex other
  invFun := consumerOccurrence other
  left_inv := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    change (t == 0) = false at ht
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t <;> fin_cases s <;>
      first | exact False.elim (Bool.noConfusion ht) | rfl
  right_inv := by intro i; fin_cases i <;> rfl

def consumerMatch (other : ℚ) : SourceContractMatch (consumer other) (consumerSchedule other)
    consumerContract (consumerFragment other) (consumerGraph other) where
  close_ok := rfl
  input_roles := rfl
  tensor_order := rfl
  outputs_exact := by
    rintro ⟨t, p⟩
    cases p
    fin_cases t <;> simp [consumerContract, IndexedCompositionParityTest.out]
  sourceToWriter := consumerEquiv other
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

def producerRun : Run producerDeclarations :=
  runChecked producerContract producerFragment (fun _ => none)

def consumerRun (other : ℚ) : Run consumerDeclarations :=
  runChecked consumerContract (consumerFragment other)
    (fun t => if t == 0 then some (fun _ => 0) else none)

#eval IndexedCompositionParityTest.check "local-producer"
  (producerRun.outcome.kind, producerRun.events.length,
    producerRun.states.getLast?.map (fun s => s.available ⟨0, ()⟩))
  ("complete", 3, some (some (0 : ℚ)))

#eval IndexedCompositionParityTest.check "local-consumer-strict"
  ((consumerRun 0).outcome.kind, (consumerRun 0).events.length,
    (consumerRun 0).states.getLast?.map (fun s =>
      [s.available ⟨0, ()⟩, s.available ⟨1, ()⟩, s.available ⟨2, ()⟩]))
  ("failed", 3, some [some (0 : ℚ), some 0, none])

#eval IndexedCompositionParityTest.check "local-consumer-total"
  ((consumerRun 4).outcome.kind, (consumerRun 4).events.length,
    (consumerRun 4).states.getLast?.map (fun s =>
      [s.available ⟨0, ()⟩, s.available ⟨1, ()⟩, s.available ⟨2, ()⟩]))
  ("complete", 4, some [some (0 : ℚ), some 0, some (1 / 2)])

end IndexedComponentCompositionLocalFixtures
