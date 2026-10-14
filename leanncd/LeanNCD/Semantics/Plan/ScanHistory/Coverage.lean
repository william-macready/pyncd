import LeanNCD.Semantics.Plan.ScanHistory.Plan

namespace LeanNCD.Semantics.Program.Plan.ScanHistory

variable {V : Type} {d N : Nat} {r : Registry (Carrier V)}

theorem valuationIndex_pair (v : Fin (d * (N + 1))) :
    valuationIndex (valuationPair d N v).1 (valuationPair d N v).2 = v :=
  finProdFinEquiv.apply_symm_apply v

theorem persistent_guard (v : Fin (d * (N + 1))) :
    statementGuard d N persistentID v = true := by
  simp [statementGuard, persistentID, initialID, recurrenceID]

theorem initial_guard_iff (v : Fin (d * (N + 1))) :
    statementGuard d N initialID v = true ↔ (valuationPair d N v).2.val = 0 := by
  simp [statementGuard]

theorem recurrence_guard_iff (v : Fin (d * (N + 1))) :
    statementGuard d N recurrenceID v = true ↔ (valuationPair d N v).2.val < N := by
  simp [statementGuard, initialID, recurrenceID]

theorem source_ids_distinct :
    persistentID ≠ initialID ∧ persistentID ≠ recurrenceID ∧ initialID ≠ recurrenceID := by
  decide

theorem raw_valuation_count (f : RegisteredF r d) (s : Fin 3) :
    (program f N).valuations (historyDefined f N) s = d * (N + 1) := rfl

theorem defined_eq_history (f : RegisteredF r d) (t : (program f N).Defined) :
    t = historyDefined f N := by
  apply Subtype.ext
  exact defined_tensor t.val t.property

theorem historyDefAddr_inj (f : RegisteredF r d)
    (i j : Fin d) (l k : Fin (N + 1)) :
    historyDefAddr f N i l = historyDefAddr f N j k ↔ i = j ∧ l = k := by
  simp only [historyDefAddr, Sigma.mk.injEq, heq_eq_eq, true_and]
  change (i, l, ()) = (j, k, ()) ↔ i = j ∧ l = k
  simp only [Prod.mk.injEq, and_true]

theorem persistent_target (f : RegisteredF r d) (i : Fin d) (l : Fin (N + 1)) :
    OccRef.target (⟨historyDefined f N, persistentOccurrence f N i l⟩ :
      OccRef (program f N)) = historyDefAddr f N i l := by
  simp [OccRef.target, program, persistentOccurrence, destination, valuationPair_index,
    persistentID, recurrenceID, historyDefAddr, historyDefined]

theorem initial_target (f : RegisteredF r d) (i : Fin d) :
    OccRef.target (⟨historyDefined f N, initialOccurrence f N i⟩ :
      OccRef (program f N)) = historyDefAddr f N i 0 := by
  simp [OccRef.target, program, initialOccurrence, destination, valuationPair_index,
    initialID, recurrenceID, historyDefAddr, historyDefined]

theorem recurrence_target (f : RegisteredF r d) (i : Fin d) (k : Fin N) :
    OccRef.target (⟨historyDefined f N, recurrenceOccurrence f N i k⟩ :
      OccRef (program f N)) = historyDefAddr f N i k.succ := by
  simp [OccRef.target, program, recurrenceOccurrence, destination, valuationPair_index,
    recurrenceID, historyDefAddr, historyDefined, historyCoord, Fin.succ]

theorem occurrence_cases (f : RegisteredF r d) (x : OccRef (program f N)) :
    (∃ i l, x = ⟨historyDefined f N, persistentOccurrence f N i l⟩) ∨
    (∃ i, x = ⟨historyDefined f N, initialOccurrence f N i⟩) ∨
    (∃ i k, x = ⟨historyDefined f N, recurrenceOccurrence f N i k⟩) := by
  obtain ⟨t, s, v, hv⟩ := x
  obtain rfl := defined_eq_history f t
  fin_cases s
  · left
    refine ⟨(valuationPair d N v).1, (valuationPair d N v).2, ?_⟩
    simp [persistentOccurrence, persistentID, valuationIndex_pair]
  · right; left
    have hz : (valuationPair d N v).2 = 0 := by
      apply Fin.ext
      exact (initial_guard_iff v).mp hv
    refine ⟨(valuationPair d N v).1, ?_⟩
    have hi := valuationIndex_pair v
    rw [hz] at hi
    simp [initialOccurrence, initialID, hi]
  · right; right
    have hk : (valuationPair d N v).2.val < N := (recurrence_guard_iff v).mp hv
    let k : Fin N := ⟨(valuationPair d N v).2.val, hk⟩
    refine ⟨(valuationPair d N v).1, k, ?_⟩
    have he : (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ : Fin (N + 1)) =
        (valuationPair d N v).2 := rfl
    simp [recurrenceOccurrence, recurrenceID, he, valuationIndex_pair]

inductive OccurrenceIndex (d N : Nat)
  | persistent (i : Fin d) (l : Fin (N + 1))
  | initial (i : Fin d)
  | recurrence (i : Fin d) (k : Fin N)

def occurrenceRef (f : RegisteredF r d) (N : Nat) :
    OccurrenceIndex d N → OccRef (program f N)
  | .persistent i l => ⟨historyDefined f N, persistentOccurrence f N i l⟩
  | .initial i => ⟨historyDefined f N, initialOccurrence f N i⟩
  | .recurrence i k => ⟨historyDefined f N, recurrenceOccurrence f N i k⟩

theorem occurrenceRef_injective (f : RegisteredF r d) :
    Function.Injective (occurrenceRef f N) := by
  intro a b h
  cases a <;> cases b <;>
    simp only [occurrenceRef, Sigma.mk.injEq, heq_eq_eq] at h
  all_goals
    simp only [persistentOccurrence, initialOccurrence, recurrenceOccurrence,
      Sigma.mk.injEq, heq_eq_eq, Subtype.mk.injEq] at h
  all_goals
    try simp [persistentID, initialID, recurrenceID] at h
  all_goals
    have hp := congrArg (valuationPair d N) h
    simp only [valuationPair_index, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, hl⟩
    try obtain rfl := hl
    first
    | rfl
    | congr 1; exact Fin.ext (congrArg (fun l : Fin (N + 1) => l.val) hl)

theorem occurrenceRef_bijective (f : RegisteredF r d) :
    Function.Bijective (occurrenceRef f N) := by
  refine ⟨occurrenceRef_injective f, ?_⟩
  intro x
  rcases occurrence_cases f x with ⟨i, l, h⟩ | ⟨i, h⟩ | ⟨i, k, h⟩
  · exact ⟨.persistent i l, h.symm⟩
  · exact ⟨.initial i, h.symm⟩
  · exact ⟨.recurrence i k, h.symm⟩

theorem no_recurrence_zero (v : Fin (d * (0 + 1))) :
    statementGuard d 0 recurrenceID v = false := by
  simp [statementGuard, initialID, recurrenceID]

theorem no_occurrence_zero_dim (f : RegisteredF r 0) (N : Nat)
    (x : OccRef (program f N)) : False := by
  rcases occurrence_cases f x with ⟨i, _, _⟩ | ⟨i, _⟩ | ⟨i, _, _⟩ <;>
    exact Fin.elim0 i

#print axioms valuationIndex_pair
#print axioms persistent_guard
#print axioms initial_guard_iff
#print axioms recurrence_guard_iff
#print axioms source_ids_distinct
#print axioms raw_valuation_count
#print axioms defined_eq_history
#print axioms historyDefAddr_inj
#print axioms persistent_target
#print axioms initial_target
#print axioms recurrence_target
#print axioms occurrence_cases
#print axioms occurrenceRef_injective
#print axioms occurrenceRef_bijective
#print axioms no_recurrence_zero
#print axioms no_occurrence_zero_dim

end LeanNCD.Semantics.Program.Plan.ScanHistory
