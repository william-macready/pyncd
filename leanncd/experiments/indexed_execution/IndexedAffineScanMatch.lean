import IndexedAffineScanConstruction
import IndexedComponentClosureFacts
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Sum

namespace IndexedExecutionExperiment.AffineScan

open LeanNCD.Semantics LeanNCD.Eval.Plan IndexedOpenComposition

variable (p : Profile d n)

instance : Fintype (declarations p).Tensor :=
  inferInstanceAs (Fintype (Fin (externalSlots p).length ⊕ Unit))

instance : DecidableEq (declarations p).Tensor :=
  inferInstanceAs (DecidableEq (Fin (externalSlots p).length ⊕ Unit))

theorem tensorOrder_nodup : (tensorOrder p).Nodup := by
  simp only [tensorOrder, declarations, List.nodup_append]
  refine ⟨(List.nodup_finRange _).map Sum.inl_injective, by simp, ?_⟩
  simp

theorem tensorOrder_complete (tx : (declarations p).Tensor) : tx ∈ tensorOrder p := by
  cases tx with
  | inl slot =>
      apply List.mem_append.mpr
      exact Or.inl (List.mem_map.mpr ⟨slot, by simp, rfl⟩)
  | inr u =>
      cases u
      apply List.mem_append.mpr
      exact Or.inr (List.Mem.head _)

def historyIndex : Address (declarations p) →
    Option (Fin (canonicalLayout (historyShape d n)).count)
  | ⟨.inl _, _⟩ => none
  | ⟨.inr _, q⟩ => some ((canonicalLayout (historyShape d n)).enumerate.symm q)

theorem writer_destination_injective :
    Function.Injective (fun s => (writer p s).destination) := by
  intro s t h
  have he := congrArg (historyIndex p) h
  simpa [historyIndex, writer] using he

theorem collectors_targets :
    (contract p).collectors.map Prod.fst =
      (List.finRange (canonicalLayout (historyShape d n)).count).map
        (fun s => (writer p s).destination) := by
  simp [contract, List.map_map]

theorem history_collected (q : Coord (historyShape d n)) :
    (⟨Sum.inr (), q⟩ : Address (declarations p)) ∈
      (contract p).collectors.map Prod.fst := by
  rw [collectors_targets]
  exact List.mem_map.mpr
    ⟨(canonicalLayout (historyShape d n)).enumerate.symm q, by simp, by simp [writer]⟩

theorem readable_complete (a : Address (declarations p)) :
    a ∈ (contract p).readable := by
  rcases a with ⟨tx, q⟩
  apply List.mem_flatMap.mpr
  refine ⟨tx, tensorOrder_complete p tx, ?_⟩
  exact List.mem_map.mpr
    ⟨(canonicalLayout ((declarations p).signature tx).axes).enumerate.symm q,
      by simp, by simp⟩

theorem readable_nodup : (contract p).readable.Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro tx _
    apply (List.nodup_finRange _).map
    intro i j he
    have hq : (canonicalLayout ((declarations p).signature tx).axes).enumerate i =
        (canonicalLayout ((declarations p).signature tx).axes).enumerate j := by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using he
    exact (canonicalLayout _).enumerate.injective hq
  · apply (tensorOrder_nodup p).imp
    intro tx ty hne a hx hy
    rcases List.mem_map.mp hx with ⟨i, _, hi⟩
    rcases List.mem_map.mp hy with ⟨j, _, hj⟩
    exact hne (by simpa using congrArg Sigma.fst (hi.trans hj.symm))

theorem find_unique {α : Type u} (xs : List α) (pred : α → Bool)
    (a : α) (ha : a ∈ xs) (hp : pred a = true)
    (unique : ∀ b ∈ xs, pred b = true → b = a) : xs.find? pred = some a := by
  cases hf : xs.find? pred with
  | none =>
      have hn := List.find?_eq_none.mp hf a ha
      simp [hp] at hn
  | some b =>
      have hb := unique b (List.mem_of_find?_eq_some hf) (List.find?_some hf)
      simp [hb]

theorem find_collector (s : Fin (canonicalLayout (historyShape d n)).count) :
    (contract p).collectors.find? (fun row => row.2.contains s.val) =
      some ((writer p s).destination, [s.val]) := by
  apply find_unique
  · exact List.mem_map.mpr ⟨s, by simp, rfl⟩
  · simp
  · intro row hr hp
    rcases List.mem_map.mp hr with ⟨t, _, rfl⟩
    have ht : t = s := Fin.ext (by simpa [eq_comm] using hp)
    subst t
    rfl

theorem find_writer (s : Fin (canonicalLayout (historyShape d n)).count) :
    (fragment p).writers.find? (fun w => w.capability == s.val) =
      some (writer p s) := by
  apply find_unique
  · exact List.mem_map.mpr ⟨s, by simp, rfl⟩
  · simp [writer]
  · intro w hw hp
    rcases List.mem_map.mp hw with ⟨t, _, rfl⟩
    have ht : t = s := Fin.ext (by simpa [writer] using hp)
    subst t
    rfl

theorem writer_valid (s : Fin (canonicalLayout (historyShape d n)).count) :
    validateWriter (contract p) (writer p s) = .ok () := by
  letI := Program.Executor.addressEq (σ := declarations p)
  have hr : ((writer p s).reads.all fun a =>
      (contract p).readable.any fun port => decide (port = a)) = true := by
    apply List.all_eq_true.mpr
    intro a _
    exact List.any_eq_true.mpr ⟨a, readable_complete p a, by simp⟩
  unfold validateWriter
  rw [show (writer p s).capability = s.val from rfl, find_collector]
  simp only [writer, decide_true, Bool.not_true]
  change (if !((writer p s).reads.all fun a =>
      (contract p).readable.any fun port => decide (port = a)) then
        Except.error Error.unreadableRead else Except.ok ()) = Except.ok ()
  simp [hr]

theorem writers_valid :
    validateWriters (contract p) (fragment p).writers = .ok () := by
  have all : ∀ ws : List (Fin (canonicalLayout (historyShape d n)).count),
      validateWriters (contract p) (ws.map (writer p)) = .ok () := by
    intro ws
    induction ws with
    | nil => rfl
    | cons s ss ih =>
        simp only [List.map_cons, validateWriters, writer_valid, ih]
        rfl
  exact all _

theorem closureFacts : ClosureFacts (contract p) (fragment p) where
  tensors_nodup := tensorOrder_nodup p
  tensors_count := by
    calc
      (tensorOrder p).length =
          ((List.finRange (externalSlots p).length).map
            (Sum.inl : Fin (externalSlots p).length → (declarations p).Tensor)).length +
              ([Sum.inr ()] : List (declarations p).Tensor).length :=
        @List.length_append (declarations p).Tensor _ _
      _ = (externalSlots p).length + 1 := by rw [List.length_map]; simp
      _ = Fintype.card (declarations p).Tensor := by
        change (externalSlots p).length + 1 = Fintype.card (Fin (externalSlots p).length ⊕ Unit)
        simp [Fintype.card_sum]
  collectors_nodup := by
    rw [collectors_targets]
    exact (List.nodup_finRange _).map (writer_destination_injective p)
  collectors_defined := by
    intro row hr
    rcases List.mem_map.mp hr with ⟨s, _, rfl⟩
    rfl
  collectors_cover := by
    intro a ha
    rcases List.mem_flatMap.mp ha with ⟨tx, ht, hp⟩
    have hin := (List.mem_filter.mp ht).2
    rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    cases tx with
    | inl slot => simp [contract, program] at hin
    | inr u => cases u; exact history_collected p _
  readable_nodup := readable_nodup p
  readable_valid := by
    rintro ⟨tx, q⟩ _
    cases tx with
    | inl slot => exact Or.inl rfl
    | inr u => cases u; exact Or.inr (history_collected p q)
  outputs_nodup := (List.nodup_finRange _).map (writer_destination_injective p)
  outputs_covered := by intro a ha; simpa [contract, List.map_map] using ha
  capabilities_nodup := by
    simpa [contract, List.flatMap_map, ← List.map_eq_flatMap] using
      (List.nodup_finRange _).map (Fin.val_injective :
        Function.Injective (fun s : Fin (canonicalLayout (historyShape d n)).count => s.val))
  tags_nodup := by
    simpa [fragment, List.map_map, Function.comp_def, writer] using
      (List.nodup_finRange _).map (Fin.val_injective :
        Function.Injective (fun s : Fin (canonicalLayout (historyShape d n)).count => s.val))
  writer_capabilities_nodup := by
    simpa [fragment, List.map_map, Function.comp_def, writer] using
      (List.nodup_finRange _).map (Fin.val_injective :
        Function.Injective (fun s : Fin (canonicalLayout (historyShape d n)).count => s.val))
  capabilities_covered := by
    intro cap hc
    simp only [contract, List.flatMap_map,
      ← List.map_eq_flatMap, List.mem_map] at hc
    rcases hc with ⟨s, hs, rfl⟩
    exact ⟨writer p s, List.mem_map.mpr ⟨s, hs, rfl⟩, rfl⟩
  writers_valid := writers_valid p

theorem close_ok :
    close (contract p) (fragment p) = .ok (graphCandidate p) :=
  (closureFacts p).close

open Program.Executor

def occurrenceKey (s : Fin (canonicalLayout (historyShape d n)).count) :
    Key (program p) :=
  .occurrence ((occurrenceEquiv p).symm s).1 ((occurrenceEquiv p).symm s).2

def publicationKey (s : Fin (canonicalLayout (historyShape d n)).count) :
    Key (program p) :=
  .publication ⟨.inr (), rfl⟩ ((canonicalLayout (historyShape d n)).enumerate s)

def keyIndex : Key (program p) → Fin (canonicalLayout (historyShape d n)).count
  | .occurrence tx o => occurrenceEquiv p ⟨tx, o⟩
  | .publication ⟨tx, ht⟩ q =>
      match tx, ht with
      | .inl _, ht => False.elim (Bool.noConfusion ht)
      | .inr _, _ => (canonicalLayout (historyShape d n)).enumerate.symm q

@[simp] theorem keyIndex_occurrence (s : Fin (canonicalLayout (historyShape d n)).count) :
    keyIndex p (occurrenceKey p s) = s := by
  simp [keyIndex, occurrenceKey]

@[simp] theorem keyIndex_publication (s : Fin (canonicalLayout (historyShape d n)).count) :
    keyIndex p (publicationKey p s) = s := by
  simp [keyIndex, publicationKey]

def keyOrder : List (Key (program p)) :=
  (List.finRange (canonicalLayout (historyShape d n)).count).flatMap
    (fun s => [occurrenceKey p s, publicationKey p s])

theorem keyOrder_nodup : (keyOrder p).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro s _
    simp [occurrenceKey, publicationKey]
  · apply (List.nodup_finRange _).imp
    intro s t hne k hs ht
    have hi : keyIndex p k = s := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> simp
    have hj : keyIndex p k = t := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp
    exact hne (hi.symm.trans hj)

theorem keyOrder_complete (k : Key (program p)) : k ∈ keyOrder p := by
  apply List.mem_flatMap.mpr
  refine ⟨keyIndex p k, by simp, ?_⟩
  cases k with
  | occurrence tx o =>
      have he : (occurrenceEquiv p).symm (occurrenceEquiv p ⟨tx, o⟩) = ⟨tx, o⟩ :=
        (occurrenceEquiv p).symm_apply_apply _
      have hk : occurrenceKey p (keyIndex p (.occurrence tx o)) = .occurrence tx o := by
        exact congrArg (fun z : SourceOccurrence (program p) => Key.occurrence z.1 z.2) he
      exact List.mem_cons.mpr (Or.inl hk.symm)
  | publication tx q =>
      rcases tx with ⟨tx, ht⟩
      cases tx with
      | inl slot => contradiction
      | inr u =>
          cases u
          have hk : publicationKey p (keyIndex p (.publication ⟨.inr (), ht⟩ q)) =
              .publication ⟨.inr (), ht⟩ q := by
            simp [publicationKey, keyIndex]
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hk.symm)))

def schedule : Schedule (program p) where
  tensors := tensorOrder p
  tensors_nodup := tensorOrder_nodup p
  tensors_complete := tensorOrder_complete p
  keys := keyOrder p
  keys_nodup := keyOrder_nodup p
  keys_complete := keyOrder_complete p

def sourceToWriter :
    SourceOccurrence (program p) ≃ Fin (fragment p).writers.length :=
  (occurrenceEquiv p).trans (finCongr (by simp [fragment]))

theorem writer_at (o : SourceOccurrence (program p)) :
    (fragment p).writers[sourceToWriter p o] = writer p (occurrenceEquiv p o) := by
  change (fragment p).writers.get (sourceToWriter p o) = _
  simp only [fragment, List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
  exact congrArg (writer p) (Fin.ext rfl)

theorem find_collector_destination (s : Fin (canonicalLayout (historyShape d n)).count) :
    (contract p).collectors.find? (fun row => decide (row.1 = (writer p s).destination)) =
      some ((writer p s).destination, [s.val]) := by
  letI := Program.Executor.addressEq (σ := declarations p)
  apply find_unique
  · exact List.mem_map.mpr ⟨s, by simp, rfl⟩
  · simp
  · intro row hr hp
    rcases List.mem_map.mp hr with ⟨t, _, rfl⟩
    have ht := writer_destination_injective p (of_decide_eq_true hp)
    subst t
    rfl

theorem collector_capabilities (s : Fin (canonicalLayout (historyShape d n)).count) :
    collectorCapabilities (contract p) (writer p s).destination = [s.val] := by
  exact congrArg (fun row : Option (Address (declarations p) × List Nat) =>
    (row.map Prod.snd).getD []) (find_collector_destination p s)

theorem graph_steps :
    (graphCandidate p).steps =
      (List.finRange (canonicalLayout (historyShape d n)).count).flatMap
        (fun s => [.write (writer p s), .collect (writer p s).destination [s.val]]) := by
  simp [graphCandidate, canonicalSteps, contract, List.flatMap_map, find_writer]

theorem schedule_priority :
    (schedule p).keys.map (keyStep (program p) (contract p) (fragment p)
      (sourceToWriter p)) = (graphCandidate p).steps := by
  rw [graph_steps]
  simp only [schedule, keyOrder, List.map_flatMap, List.map_cons, List.map_nil]
  apply List.flatMap_congr
  intro s _
  congr 1
  · simp only [occurrenceKey, keyStep, writer_at]
    change Step.write (writer p (occurrenceEquiv p ((occurrenceEquiv p).symm s))) =
      Step.write (writer p s)
    rw [Equiv.apply_symm_apply]
  · congr 1
    change Step.collect (writer p s).destination
      (collectorCapabilities (contract p) (writer p s).destination) =
        Step.collect (writer p s).destination [s.val]
    rw [collector_capabilities]

theorem factor_context (caps : Array BlockCapture) (basis : List Int)
    (f : FactorPlan) (γ : Γ)
    (store : PartialStore RationalReference.Carrier (declarations p)) :
    footprint (factorBody p caps (fun _ : Γ => basis) f) γ =
        footprint (factorBody p caps (fun _ : Unit => basis) f) () ∧
    evalWith RationalReference.ops store (factorBody p caps (fun _ : Γ => basis) f) γ =
        evalWith RationalReference.ops store (factorBody p caps (fun _ : Unit => basis) f) () := by
  cases f <;> exact ⟨rfl, rfl⟩

theorem product_context (caps : Array BlockCapture) (basis : List Int)
    (fs : List FactorPlan) (γ : Γ)
    (store : PartialStore RationalReference.Carrier (declarations p)) :
    footprint (orderedProduct p caps (fun _ : Γ => basis) fs) γ =
        footprint (orderedProduct p caps (fun _ : Unit => basis) fs) () ∧
    evalWith RationalReference.ops store (orderedProduct p caps (fun _ : Γ => basis) fs) γ =
        evalWith RationalReference.ops store (orderedProduct p caps (fun _ : Unit => basis) fs) () := by
  induction fs with
  | nil => exact ⟨rfl, rfl⟩
  | cons f fs ih =>
      have hf := factor_context p caps basis f γ store
      constructor
      · simp only [orderedProduct, footprint, hf.1, ih.1]
      · simp only [orderedProduct, evalWith, hf.2, ih.2]

theorem sum_context (caps : Array BlockCapture) (i clock : Int)
    (ts : List TermPlan) (γ : Γ)
    (store : PartialStore RationalReference.Carrier (declarations p)) :
    footprint (orderedSum p caps (fun _ : Γ => i) (fun _ => clock) ts) γ =
        footprint (orderedSum p caps (fun _ : Unit => i) (fun _ => clock) ts) () ∧
    evalWith RationalReference.ops store
        (orderedSum p caps (fun _ : Γ => i) (fun _ => clock) ts) γ =
      evalWith RationalReference.ops store
        (orderedSum p caps (fun _ : Unit => i) (fun _ => clock) ts) () := by
  induction ts with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih =>
      have hp := product_context p caps (termBasis t i clock) t.factors.toList γ store
      constructor
      · simp only [orderedSum, footprint, hp.1, ih.1]
      · simp only [orderedSum, evalWith, hp.2, ih.2]

theorem addressBody_context (q : Coord (historyShape d n)) (γ : Γ)
    (store : PartialStore RationalReference.Carrier (declarations p)) :
    footprint (addressBody p q) γ = footprint (addressBody p q) () ∧
    evalWith RationalReference.ops store (addressBody p q) γ =
      evalWith RationalReference.ops store (addressBody p q) () := by
  unfold addressBody
  split <;> apply sum_context

theorem source_outputs_exact (a : Address (declarations p)) :
    a ∈ (contract p).outputs ↔ (program p).output a.1 = true := by
  rcases a with ⟨tx, q⟩
  cases tx with
  | inl slot =>
      constructor
      · intro h
        rcases List.mem_map.mp h with ⟨s, _, hs⟩
        have ht := congrArg Sigma.fst hs
        cases ht
      · intro h
        contradiction
  | inr u =>
      cases u
      constructor
      · intro _; rfl
      · intro _
        have h := history_collected p q
        simpa only [contract, List.map_map, Function.comp_def] using h

def sourceMatch : SourceContractMatch (program p) (schedule p)
    (contract p) (fragment p) (graphCandidate p) where
  close_ok := close_ok p
  input_roles := rfl
  tensor_order := rfl
  outputs_exact := source_outputs_exact p
  sourceToWriter := sourceToWriter p
  writer_destination := by
    intro o
    rw [writer_at]
    rcases o with ⟨⟨tx, ht⟩, s, v, hv⟩
    cases tx with
    | inl slot => contradiction
    | inr u => cases u; rfl
  writer_reads := by
    intro o
    rw [writer_at]
    rcases o with ⟨⟨tx, ht⟩, s, v, hv⟩
    cases tx with
    | inl slot => contradiction
    | inr u =>
        cases u
        exact (addressBody_context p ((canonicalLayout (historyShape d n)).enumerate s)
          (⟨v, hv⟩ : {v : Fin 1 // true = true}) (fun _ => none)).1.symm
  eval_agrees := by
    intro o store
    rw [writer_at]
    rcases o with ⟨⟨tx, ht⟩, s, v, hv⟩
    cases tx with
    | inl slot => contradiction
    | inr u =>
        cases u
        have h := addressBody_context p ((canonicalLayout (historyShape d n)).enumerate s)
          (⟨v, hv⟩ : {v : Fin 1 // true = true}) store
        change evalReady RationalReference.ops store
          (addressBody p ((canonicalLayout (historyShape d n)).enumerate s)) () =
            evalReady RationalReference.ops store
              (addressBody p ((canonicalLayout (historyShape d n)).enumerate s))
                (⟨v, hv⟩ : {v : Fin 1 // true = true})
        simp only [evalReady, h.1, h.2]
  priority := schedule_priority p

end IndexedExecutionExperiment.AffineScan

#print axioms IndexedExecutionExperiment.AffineScan.close_ok
#print axioms IndexedExecutionExperiment.AffineScan.sourceMatch
#audit_axioms IndexedExecutionExperiment.AffineScan
