import IndexedOpenComposition

namespace IndexedOpenComposition

open LeanNCD.Semantics
open LeanNCD.Semantics.Program

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]

def canonicalSteps (contract : Contract σ) (fragment : Fragment σ) :
    List (Step σ) :=
  contract.collectors.flatMap fun row =>
    (row.2.filterMap fun cap =>
      fragment.writers.find? (fun w => w.capability == cap)).map Step.write ++
      [Step.collect row.1 row.2]

theorem close_success_tensors_nodup
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    contract.tensors.Nodup := by
  by_contra hn
  simp [close, hn] at h

theorem close_success_tensor_count
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    contract.tensors.length = Fintype.card σ.Tensor := by
  have hn := close_success_tensors_nodup h
  by_contra hc
  simp [close, hn, hc] at h

theorem close_success_collectors_nodup
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    (contract.collectors.map Prod.fst).Nodup := by
  letI : DecidableEq (Address σ) := Program.Executor.addressEq (σ := σ)
  have ht := close_success_tensors_nodup h
  have hc := close_success_tensor_count h
  by_contra hn
  simp [close, ht, hc, hn] at h

theorem close_success_no_input_collector
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    contract.collectors.any (fun row => contract.input row.1.1) = false := by
  letI : DecidableEq (Address σ) := Program.Executor.addressEq (σ := σ)
  have ht := close_success_tensors_nodup h
  have hc := close_success_tensor_count h
  have hn := close_success_collectors_nodup h
  by_cases hb : contract.collectors.any (fun row => contract.input row.1.1) = true
  · simp [close, ht, hc, hn, hb] at h
  · exact Bool.eq_false_iff.mpr hb

theorem close_success_tensors_complete
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    ∀ t : σ.Tensor, t ∈ contract.tensors := by
  have ht := close_success_tensors_nodup h
  have hc := close_success_tensor_count h
  have hall : contract.tensors.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [List.toFinset_card_of_nodup ht] using hc
  intro t
  apply List.mem_toFinset.mp
  rw [hall]
  exact Finset.mem_univ t

theorem close_success_canonical
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    g.contract = contract ∧ g.steps = canonicalSteps contract fragment := by
  have ht := close_success_tensors_nodup h
  have hc := close_success_tensor_count h
  have hn := close_success_collectors_nodup h
  have hi := close_success_no_input_collector h
  simp only [close, Id.run, pure_bind, ht, hc, hn, hi,
    decide_true, Bool.not_true, Bool.false_eq_true, bne_self_eq_false, if_false] at h
  repeat (split at h <;> try cases h)
  simp only [canonicalSteps, and_self]

theorem close_success_capabilities_nodup
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    (contract.collectors.flatMap Prod.snd).Nodup := by
  have ht := close_success_tensors_nodup h
  have hc := close_success_tensor_count h
  have hn := close_success_collectors_nodup h
  have hi := close_success_no_input_collector h
  simp only [close, Id.run, pure_bind, ht, hc, hn, hi,
    decide_true, Bool.not_true, Bool.false_eq_true, bne_self_eq_false, if_false] at h
  repeat (split at h <;> try cases h)
  simp_all

theorem close_success_defined_covered
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    ∀ a ∈ definedAddresses contract, a ∈ contract.collectors.map Prod.fst := by
  have ht := close_success_tensors_nodup h
  have hc := close_success_tensor_count h
  have hn := close_success_collectors_nodup h
  have hi := close_success_no_input_collector h
  simp only [close, Id.run, pure_bind, ht, hc, hn, hi,
    decide_true, Bool.not_true, Bool.false_eq_true, bne_self_eq_false, if_false] at h
  repeat (split at h <;> try cases h)
  simp_all [List.any_eq_true]

theorem close_success_validated_writers
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    validateWriters contract fragment.writers = .ok () := by
  have ht := close_success_tensors_nodup h
  have hc := close_success_tensor_count h
  have hn := close_success_collectors_nodup h
  have hi := close_success_no_input_collector h
  simp only [close, Id.run, pure_bind, ht, hc, hn, hi,
    decide_true, Bool.not_true, Bool.false_eq_true, bne_self_eq_false, if_false] at h
  repeat (split at h <;> try cases h)
  cases hv : validateWriters contract fragment.writers with
  | error e => simp_all
  | ok u => cases u; rfl

theorem validated_writers_forall (contract : Contract σ) :
    ∀ (writers : List (Writer σ)),
      validateWriters contract writers = .ok () →
        ∀ w ∈ writers, validateWriter contract w = .ok ()
  | [], _ => by simp
  | w :: ws, h => by
    have hw : validateWriter contract w = .ok () := by
      cases hv : validateWriter contract w with
      | error e =>
        simp only [validateWriters, hv] at h
        cases h
      | ok u => cases u; rfl
    have hws : validateWriters contract ws = .ok () := by
      simpa [validateWriters, hw] using h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hw
    · exact validated_writers_forall contract ws hws x hx

theorem validated_writer_destination_reads
    (contract : Contract σ) (w : Writer σ)
    (h : validateWriter contract w = .ok ()) :
    ∃ row, contract.collectors.find? (fun row => decide (w.capability ∈ row.2)) = some row ∧
      w.destination = row.1 ∧ w.reads = footprint w.body () := by
  letI : DecidableEq (Address σ) := Program.Executor.addressEq (σ := σ)
  cases hrow : contract.collectors.find? (fun row => decide (w.capability ∈ row.2)) with
  | none => simp [validateWriter, hrow] at h
  | some row =>
    refine ⟨row, rfl, ?_, ?_⟩
    · by_contra hb
      simp [validateWriter, hrow, hb] at h
      cases h
    · have hdst : w.destination = row.1 := by
        by_contra hb
        simp [validateWriter, hrow, hb] at h
        cases h
      by_contra hb
      simp [validateWriter, hrow, hdst, hb] at h
      cases h

theorem close_success_writer_collector
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    ∀ w ∈ fragment.writers,
      ∃ row ∈ contract.collectors, w.capability ∈ row.2 ∧
        w.destination = row.1 ∧ w.reads = footprint w.body () := by
  intro w hw
  obtain ⟨row, hfind, hdst, hreads⟩ :=
    validated_writer_destination_reads contract w
      (validated_writers_forall contract fragment.writers
        (close_success_validated_writers h) w hw)
  obtain ⟨hcap, i, hi, hget, _⟩ :=
    List.find?_eq_some_iff_getElem.mp hfind
  refine ⟨row, ?_, of_decide_eq_true hcap, hdst, hreads⟩
  rw [← hget]
  exact List.getElem_mem hi

theorem close_success_capability_covered
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    ∀ cap ∈ contract.collectors.flatMap Prod.snd,
      ∃ w ∈ fragment.writers, w.capability = cap := by
  have ht := close_success_tensors_nodup h
  have hc := close_success_tensor_count h
  have hn := close_success_collectors_nodup h
  have hi := close_success_no_input_collector h
  simp only [close, Id.run, pure_bind, ht, hc, hn, hi,
    decide_true, Bool.not_true, Bool.false_eq_true, bne_self_eq_false, if_false] at h
  repeat (split at h <;> try cases h)
  simp_all [List.any_eq_true, List.any_eq_false, List.mem_flatMap]
  intro cap t p caps hrow hcap
  solve_by_elim

theorem close_success_writer_capability
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    ∀ w ∈ fragment.writers, w.capability ∈ contract.collectors.flatMap Prod.snd := by
  have ht := close_success_tensors_nodup h
  have hc := close_success_tensor_count h
  have hn := close_success_collectors_nodup h
  have hi := close_success_no_input_collector h
  simp only [close, Id.run, pure_bind, ht, hc, hn, hi,
    decide_true, Bool.not_true, Bool.false_eq_true, bne_self_eq_false, if_false] at h
  repeat (split at h <;> try cases h)
  simp_all [List.any_eq_true, List.any_eq_false]

theorem close_success_capability_guard
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    (fragment.writers.any fun w =>
      (fragment.writers.filter fun v => v.capability == w.capability).length > 1) = false := by
  have ht := close_success_tensors_nodup h
  have hc := close_success_tensor_count h
  have hn := close_success_collectors_nodup h
  have hi := close_success_no_input_collector h
  simp only [close, Id.run, pure_bind, ht, hc, hn, hi,
    decide_true, Bool.not_true, Bool.false_eq_true, bne_self_eq_false, if_false] at h
  repeat (split at h <;> try cases h)
  rename_i hCovered hReadable hOutputs hCaps hTags hCapDup hMissing hExtra writerValue writerValidation
  have hbool := Bool.eq_false_iff.mpr hCapDup
  change (fragment.writers.any fun w =>
    (fragment.writers.filter fun v => v.capability == w.capability).length > 1) = false at hbool
  exact hbool

theorem close_success_tag_guard
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    (fragment.writers.any fun w =>
      (fragment.writers.filter fun v => v.tag == w.tag).length > 1) = false := by
  have ht := close_success_tensors_nodup h
  have hc := close_success_tensor_count h
  have hn := close_success_collectors_nodup h
  have hi := close_success_no_input_collector h
  simp only [close, Id.run, pure_bind, ht, hc, hn, hi,
    decide_true, Bool.not_true, Bool.false_eq_true, bne_self_eq_false, if_false] at h
  repeat (split at h <;> try cases h)
  rename_i hCovered hReadable hOutputs hCaps hTags hCapDup hMissing hExtra writerValue writerValidation
  have hbool := Bool.eq_false_iff.mpr hTags
  change (fragment.writers.any fun w =>
    (fragment.writers.filter fun v => v.tag == w.tag).length > 1) = false at hbool
  exact hbool

private theorem nodup_map_of_duplicate_guard (writers : List (Writer σ))
    (f : Writer σ → Nat)
    (h : (writers.any fun w => (writers.filter fun v => f v == f w).length > 1) = false) :
    (writers.map f).Nodup := by
  apply List.nodup_iff_count_eq_one.mpr
  intro cap
  intro hm
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
  have hrow := (List.any_eq_false.mp h) w hw
  have hlen : (writers.filter fun v => f v == f w).length ≤ 1 := by
    simpa using hrow
  have hcount : (writers.map f).count (f w) =
      (writers.filter fun v => f v == f w).length := by
    simp only [List.count, List.countP_map, List.countP_eq_length_filter]
    rw [List.filter_map, List.length_map]
    rfl
  have hpos : 1 ≤ (writers.map f).count (f w) :=
    List.one_le_count_iff.mpr (List.mem_map.mpr ⟨w, hw, rfl⟩)
  omega

theorem close_success_writer_capabilities_nodup
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    (fragment.writers.map Writer.capability).Nodup :=
  nodup_map_of_duplicate_guard fragment.writers Writer.capability
    (close_success_capability_guard h)

theorem close_success_writer_tags_nodup
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g) :
    (fragment.writers.map Writer.tag).Nodup :=
  nodup_map_of_duplicate_guard fragment.writers Writer.tag
    (close_success_tag_guard h)

private theorem collector_row_unique
    (rows : List (Address σ × List Nat))
    (hn : (rows.flatMap Prod.snd).Nodup)
    {cap : Nat} {row₁ row₂ : Address σ × List Nat}
    (h₁ : row₁ ∈ rows) (hc₁ : cap ∈ row₁.2)
    (h₂ : row₂ ∈ rows) (hc₂ : cap ∈ row₂.2) : row₁ = row₂ := by
  induction rows generalizing row₁ row₂ with
  | nil => cases h₁
  | cons row rest ih =>
    have hn' : (row.2 ++ rest.flatMap Prod.snd).Nodup := by
      simpa only [List.flatMap_cons] using hn
    have htail := hn'.of_append_right
    have hdisj := List.disjoint_of_nodup_append hn'
    rcases List.mem_cons.mp h₁ with rfl | hRest1
    · rcases List.mem_cons.mp h₂ with rfl | hRest2
      · rfl
      · have hcRest : cap ∈ rest.flatMap Prod.snd :=
          List.mem_flatMap.mpr ⟨row₂, hRest2, hc₂⟩
        exact False.elim ((List.disjoint_left.mp hdisj) hc₁ hcRest)
    · rcases List.mem_cons.mp h₂ with rfl | hRest2
      · have hcRest : cap ∈ rest.flatMap Prod.snd :=
          List.mem_flatMap.mpr ⟨row₁, hRest1, hc₁⟩
        exact False.elim ((List.disjoint_left.mp hdisj) hc₂ hcRest)
      · exact ih htail hRest1 hc₁ hRest2 hc₂

theorem close_success_writer_destination_iff
    {contract : Contract σ} {fragment : Fragment σ} {g : Closed σ}
    (h : close contract fragment = .ok g)
    {w : Writer σ} (hw : w ∈ fragment.writers)
    {row : Address σ × List Nat} (hrow : row ∈ contract.collectors) :
    w.capability ∈ row.2 ↔ w.destination = row.1 := by
  obtain ⟨row₀, hrow₀, hcap₀, hdst, _⟩ :=
    close_success_writer_collector h w hw
  constructor
  · intro hcap
    have heq : row₀ = row :=
      collector_row_unique contract.collectors
        (close_success_capabilities_nodup h) hrow₀ hcap₀ hrow hcap
    simpa [heq] using hdst
  · intro heq
    have hroweq : row₀ = row :=
      List.inj_on_of_nodup_map (close_success_collectors_nodup h)
        hrow₀ hrow (hdst.symm.trans heq)
    simpa [hroweq] using hcap₀

end IndexedOpenComposition
