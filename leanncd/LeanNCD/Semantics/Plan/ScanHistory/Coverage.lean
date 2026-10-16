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

theorem mem_block_iff (f : RegisteredF r d) (l : Fin (N + 1))
    (x : DefAddr (program f N)) :
    x ∈ block f N l ↔ ∃ i, historyDefAddr f N i l = x := by
  simp [block]

theorem block_nodup (f : RegisteredF r d) (l : Fin (N + 1)) :
    (block f N l).Nodup := by
  apply (List.nodup_finRange d).map
  intro i j h
  exact ((historyDefAddr_inj f i j l l).mp h).1

theorem blocks_disjoint (f : RegisteredF r d) (l m : Fin (N + 1)) (h : l ≠ m) :
    List.Disjoint (block f N l) (block f N m) := by
  intro x hx hy
  obtain ⟨i, rfl⟩ := (mem_block_iff f l x).mp hx
  obtain ⟨j, hj⟩ := (mem_block_iff f m _).mp hy
  exact h ((historyDefAddr_inj f i j l m).mp hj.symm).2

theorem persistentGroup_nodup (f : RegisteredF r d) (l : Fin (N + 1)) :
    (persistentGroup f N l).Nodup := by
  apply (List.nodup_finRange d).map
  intro i j h
  have hi : OccurrenceIndex.persistent i l = .persistent j l :=
    occurrenceRef_injective f h
  cases hi
  rfl

theorem initialGroup_nodup (f : RegisteredF r d) :
    (initialGroup f N).Nodup := by
  apply (List.nodup_finRange d).map
  intro i j h
  have hi : (OccurrenceIndex.initial i : OccurrenceIndex d N) = .initial j :=
    occurrenceRef_injective f h
  cases hi
  rfl

theorem recurrenceGroup_nodup (f : RegisteredF r d) (k : Fin N) :
    (recurrenceGroup f N k).Nodup := by
  apply (List.nodup_finRange d).map
  intro i j h
  have hi : OccurrenceIndex.recurrence i k = .recurrence j k :=
    occurrenceRef_injective f h
  cases hi
  rfl

theorem persistent_initial_disjoint (f : RegisteredF r d) (l : Fin (N + 1)) :
    List.Disjoint (persistentGroup f N l) (initialGroup f N) := by
  intro x hx hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hy
  have hi : (OccurrenceIndex.initial j : OccurrenceIndex d N) = .persistent i l :=
    occurrenceRef_injective f hj
  cases hi

theorem persistent_recurrence_disjoint (f : RegisteredF r d)
    (l : Fin (N + 1)) (k : Fin N) :
    List.Disjoint (persistentGroup f N l) (recurrenceGroup f N k) := by
  intro x hx hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hy
  have hi : OccurrenceIndex.recurrence j k = .persistent i l :=
    occurrenceRef_injective f hj
  cases hi

theorem group_nodup (f : RegisteredF r d) (l : Fin (N + 1)) :
    (group f N l).Nodup := by
  refine Fin.cases ?_ (fun k => ?_) l
  · exact (persistentGroup_nodup f 0).append (initialGroup_nodup f)
      (persistent_initial_disjoint f 0)
  · exact (persistentGroup_nodup f k.succ).append (recurrenceGroup_nodup f k)
      (persistent_recurrence_disjoint f k.succ k)

theorem group_target (f : RegisteredF r d) (l : Fin (N + 1))
    (x : OccRef (program f N)) (hx : x ∈ group f N l) :
    ∃ i, x.target = historyDefAddr f N i l := by
  revert hx
  refine Fin.cases ?_ (fun k => ?_) l
  · intro hx
    rcases List.mem_append.mp hx with hp | hi
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      exact ⟨i, persistent_target f i 0⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hi
      exact ⟨i, initial_target f i⟩
  · intro hx
    rcases List.mem_append.mp hx with hp | hr
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      exact ⟨i, persistent_target f i k.succ⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
      exact ⟨i, recurrence_target f i k⟩

theorem groups_disjoint (f : RegisteredF r d) (l m : Fin (N + 1)) (h : l ≠ m) :
    List.Disjoint (group f N l) (group f N m) := by
  intro x hx hy
  obtain ⟨i, hi⟩ := group_target f l x hx
  obtain ⟨j, hj⟩ := group_target f m x hy
  exact h ((historyDefAddr_inj f i j l m).mp (hi.symm.trans hj)).2

theorem persistent_mem_group (f : RegisteredF r d) (i : Fin d) (l : Fin (N + 1)) :
    occurrenceRef f N (.persistent i l) ∈ group f N l :=
  List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

theorem initial_mem_group (f : RegisteredF r d) (i : Fin d) :
    occurrenceRef f N (.initial i) ∈ group f N 0 := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

theorem recurrence_mem_group (f : RegisteredF r d) (i : Fin d) (k : Fin N) :
    occurrenceRef f N (.recurrence i k) ∈ group f N k.succ := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

theorem plan_accFlat (f : RegisteredF r d) (N : Nat) :
    (plan f N).accFlat = (List.finRange (N + 1)).flatMap (group f N) :=
  scheduleCommands_groups _ _ _

theorem plan_pubFlat (f : RegisteredF r d) (N : Nat) :
    (plan f N).pubFlat = (List.finRange (N + 1)).flatMap (block f N) :=
  scheduleCommands_pubs _ _ _

theorem plan_coverage1 (f : RegisteredF r d) (N : Nat) : (plan f N).Coverage1 := by
  constructor
  · rw [plan_accFlat, List.nodup_flatMap]
    exact ⟨fun l _ => group_nodup f l,
      (List.nodup_finRange (N + 1)).pairwise_of_forall_ne
        (fun l _ m _ h => groups_disjoint f l m h)⟩
  · intro x
    rw [plan_accFlat]
    rcases occurrence_cases f x with ⟨i, l, rfl⟩ | ⟨i, rfl⟩ | ⟨i, k, rfl⟩
    · exact List.mem_flatMap.mpr ⟨l, List.mem_finRange l, persistent_mem_group f i l⟩
    · exact List.mem_flatMap.mpr ⟨0, List.mem_finRange 0, initial_mem_group f i⟩
    · exact List.mem_flatMap.mpr
        ⟨k.succ, List.mem_finRange k.succ, recurrence_mem_group f i k⟩

theorem plan_coverage2 (f : RegisteredF r d) (N : Nat) : (plan f N).Coverage2 := by
  constructor
  · rw [plan_pubFlat, List.nodup_flatMap]
    exact ⟨fun l _ => block_nodup f l,
      (List.nodup_finRange (N + 1)).pairwise_of_forall_ne
        (fun l _ m _ h => blocks_disjoint f l m h)⟩
  · rintro ⟨t, c⟩
    obtain rfl := defined_eq_history f t
    obtain ⟨i, l, u⟩ := c
    cases u
    rw [plan_pubFlat]
    exact List.mem_flatMap.mpr
      ⟨l, List.mem_finRange l, (mem_block_iff f l _).mpr ⟨i, rfl⟩⟩

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
#print axioms mem_block_iff
#print axioms block_nodup
#print axioms blocks_disjoint
#print axioms persistentGroup_nodup
#print axioms initialGroup_nodup
#print axioms recurrenceGroup_nodup
#print axioms persistent_initial_disjoint
#print axioms persistent_recurrence_disjoint
#print axioms group_nodup
#print axioms group_target
#print axioms groups_disjoint
#print axioms persistent_mem_group
#print axioms initial_mem_group
#print axioms recurrence_mem_group
#print axioms plan_accFlat
#print axioms plan_pubFlat
#print axioms plan_coverage1
#print axioms plan_coverage2

end LeanNCD.Semantics.Program.Plan.ScanHistory
