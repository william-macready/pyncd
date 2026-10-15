import LeanNCD.Semantics.Plan.ScanHistory.Coverage

namespace LeanNCD.Semantics.Program.Plan.ScanHistory

variable {V : Type} {d : Nat} {r : Registry (Carrier V)}

def beforeB (f : RegisteredF r d) (N k : Nat) : List (DefAddr (program f N)) :=
  ((List.finRange (N + 1)).take k).flatMap (block f N)

def beforeG (f : RegisteredF r d) (N k : Nat) : List (OccRef (program f N)) :=
  ((List.finRange (N + 1)).take k).flatMap (group f N)

theorem command_init (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).commands[3 * k.val]? = some [.initZero (block f N k)] := by
  have hx : (List.finRange (N + 1))[k.val]? = some k := by
    rw [List.getElem?_eq_getElem (by simpa using k.isLt), List.getElem_finRange]
    simp
  simpa [plan, scheduleCommands, sliceCommands] using
    getElem?_flatMap_three (List.finRange (N + 1))
      (fun l => sliceCommands (block f N l) (group f N l)) (fun _ => rfl) hx 0 (by omega)

theorem command_acc (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).commands[3 * k.val + 1]? = some [.acc (group f N k)] := by
  have hx : (List.finRange (N + 1))[k.val]? = some k := by
    rw [List.getElem?_eq_getElem (by simpa using k.isLt), List.getElem_finRange]
    simp
  simpa [plan, scheduleCommands, sliceCommands] using
    getElem?_flatMap_three (List.finRange (N + 1))
      (fun l => sliceCommands (block f N l) (group f N l)) (fun _ => rfl) hx 1 (by omega)

theorem command_pub (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).commands[3 * k.val + 2]? = some [.pub (block f N k)] := by
  have hx : (List.finRange (N + 1))[k.val]? = some k := by
    rw [List.getElem?_eq_getElem (by simpa using k.isLt), List.getElem_finRange]
    simp
  simpa [plan, scheduleCommands, sliceCommands] using
    getElem?_flatMap_three (List.finRange (N + 1))
      (fun l => sliceCommands (block f N l) (group f N l)) (fun _ => rfl) hx 2 (by omega)

theorem command_end (f : RegisteredF r d) (N : Nat) :
    (plan f N).commands[3 * (N + 1)]? = none := by
  rw [← plan_length f N]
  simp

theorem consList_phase_zero (f : RegisteredF r d) (N k : Nat) :
    (plan f N).consList (3 * k) = beforeG f N k :=
  consList_at_slice_boundary _ _ _ _ rfl k

theorem matList_phase_zero (f : RegisteredF r d) (N k : Nat) :
    (plan f N).matList (3 * k) = beforeB f N k :=
  matList_at_slice_boundary _ _ _ _ rfl k

theorem pubList_phase_zero (f : RegisteredF r d) (N k : Nat) :
    (plan f N).pubList (3 * k) = beforeB f N k :=
  plan_pubList_boundary f N k

theorem consList_phase_one (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).consList (3 * k.val + 1) = beforeG f N k.val := by
  calc
    _ = (plan f N).consList (3 * k.val) := by
      simp [consList, (plan f N).prefixAnn_succ (command_init f N k), Ann.groups]
    _ = _ := consList_phase_zero f N k.val

theorem matList_phase_one (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).matList (3 * k.val + 1) = beforeB f N k.val ++ block f N k := by
  calc
    _ = (plan f N).matList (3 * k.val) ++ block f N k := by
      simp [matList, (plan f N).prefixAnn_succ (command_init f N k), Ann.inits]
    _ = _ := by rw [matList_phase_zero]

theorem pubList_phase_one (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).pubList (3 * k.val + 1) = beforeB f N k.val := by
  calc
    _ = (plan f N).pubList (3 * k.val) := by
      simp [pubList, (plan f N).prefixAnn_succ (command_init f N k), Ann.blocks]
    _ = _ := pubList_phase_zero f N k.val

theorem consList_phase_two (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).consList (3 * k.val + 2) = beforeG f N k.val ++ group f N k := by
  have index : 3 * k.val + 2 = (3 * k.val + 1) + 1 := by omega
  calc
    _ = (plan f N).consList (3 * k.val + 1) ++ group f N k := by
      rw [index]
      simp [consList, (plan f N).prefixAnn_succ (command_acc f N k), Ann.groups]
    _ = _ := by rw [consList_phase_one]

theorem matList_phase_two (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).matList (3 * k.val + 2) = beforeB f N k.val ++ block f N k := by
  have index : 3 * k.val + 2 = (3 * k.val + 1) + 1 := by omega
  calc
    _ = (plan f N).matList (3 * k.val + 1) := by
      rw [index]
      simp [matList, (plan f N).prefixAnn_succ (command_acc f N k), Ann.inits]
    _ = _ := matList_phase_one f N k

theorem pubList_phase_two (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).pubList (3 * k.val + 2) = beforeB f N k.val := by
  have index : 3 * k.val + 2 = (3 * k.val + 1) + 1 := by omega
  calc
    _ = (plan f N).pubList (3 * k.val + 1) := by
      rw [index]
      simp [pubList, (plan f N).prefixAnn_succ (command_acc f N k), Ann.blocks]
    _ = _ := pubList_phase_one f N k

theorem prefix_phase_lists (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    ((plan f N).consList (3 * k.val) = beforeG f N k.val ∧
      (plan f N).matList (3 * k.val) = beforeB f N k.val ∧
      (plan f N).pubList (3 * k.val) = beforeB f N k.val) ∧
    ((plan f N).consList (3 * k.val + 1) = beforeG f N k.val ∧
      (plan f N).matList (3 * k.val + 1) = beforeB f N k.val ++ block f N k ∧
      (plan f N).pubList (3 * k.val + 1) = beforeB f N k.val) ∧
    ((plan f N).consList (3 * k.val + 2) = beforeG f N k.val ++ group f N k ∧
      (plan f N).matList (3 * k.val + 2) = beforeB f N k.val ++ block f N k ∧
      (plan f N).pubList (3 * k.val + 2) = beforeB f N k.val) ∧
    ((plan f N).consList (3 * (k.val + 1)) = beforeG f N (k.val + 1) ∧
      (plan f N).matList (3 * (k.val + 1)) = beforeB f N (k.val + 1) ∧
      (plan f N).pubList (3 * (k.val + 1)) = beforeB f N (k.val + 1)) :=
  ⟨⟨consList_phase_zero f N _, matList_phase_zero f N _, pubList_phase_zero f N _⟩,
    ⟨consList_phase_one f N k, matList_phase_one f N k, pubList_phase_one f N k⟩,
    ⟨consList_phase_two f N k, matList_phase_two f N k, pubList_phase_two f N k⟩,
    ⟨consList_phase_zero f N _, matList_phase_zero f N _, pubList_phase_zero f N _⟩⟩

theorem prefix_retList (f : RegisteredF r d) (N pc : Nat) :
    (plan f N).retList pc = [] :=
  plan_retList f N pc

/-- A bounded boundary is either terminal or precedes one of the three slice commands. -/
theorem boundary_decomposition (N pc : Nat) (hpc : pc ≤ 3 * (N + 1)) :
    pc = 3 * (N + 1) ∨
      ∃ k : Fin (N + 1), ∃ phase : Fin 3, pc = 3 * k.val + phase.val := by
  by_cases final : pc = 3 * (N + 1)
  · exact Or.inl final
  · right
    refine ⟨⟨pc / 3, by omega⟩, ⟨pc % 3, by omega⟩, ?_⟩
    change pc = 3 * (pc / 3) + pc % 3
    omega

theorem command_index_decomposition (N pc : Nat) (hpc : pc < 3 * (N + 1)) :
    ∃ k : Fin (N + 1), ∃ phase : Fin 3, pc = 3 * k.val + phase.val := by
  rcases boundary_decomposition N pc (by omega) with final | indexed
  · omega
  · exact indexed

theorem group_targets_slice (f : RegisteredF r d) (N : Nat)
    (l : Fin (N + 1)) (x : OccRef (program f N)) :
    x ∈ group f N l ↔ ∃ i, x.target = historyDefAddr f N i l := by
  constructor
  · exact group_target f l x
  · rintro ⟨j, hj⟩
    rcases occurrence_cases f x with ⟨i, m, rfl⟩ | ⟨i, rfl⟩ | ⟨i, k, rfl⟩
    · rw [persistent_target] at hj
      obtain ⟨_, rfl⟩ := (historyDefAddr_inj f i j m l).mp hj
      exact persistent_mem_group f i m
    · rw [initial_target] at hj
      obtain ⟨_, rfl⟩ := (historyDefAddr_inj f i j 0 l).mp hj
      exact initial_mem_group f i
    · rw [recurrence_target] at hj
      obtain ⟨_, rfl⟩ := (historyDefAddr_inj f i j k.succ l).mp hj
      exact recurrence_mem_group f i k

theorem beforeB_mem (f : RegisteredF r d) (N k : Nat)
    (x : DefAddr (program f N)) :
    x ∈ beforeB f N k ↔ ∃ i l, l.val < k ∧ x = historyDefAddr f N i l := by
  simp only [beforeB, List.mem_flatMap]
  constructor
  · rintro ⟨l, hl, hx⟩
    obtain ⟨i, hi⟩ := (mem_block_iff f l x).mp hx
    exact ⟨i, l, by simpa only [List.mem_take_iff_idxOf_lt (List.mem_finRange l),
      List.idxOf_finRange] using hl, hi.symm⟩
  · rintro ⟨i, l, hl, rfl⟩
    refine ⟨l, ?_, (mem_block_iff f l _).mpr ⟨i, rfl⟩⟩
    simpa only [List.mem_take_iff_idxOf_lt (List.mem_finRange l),
      List.idxOf_finRange] using hl

theorem beforeG_mem (f : RegisteredF r d) (N k : Nat)
    (x : OccRef (program f N)) :
    x ∈ beforeG f N k ↔ ∃ l, l.val < k ∧ x ∈ group f N l := by
  simp only [beforeG, List.mem_flatMap]
  constructor
  · rintro ⟨l, hl, hx⟩
    exact ⟨l, by simpa only [List.mem_take_iff_idxOf_lt (List.mem_finRange l),
      List.idxOf_finRange] using hl, hx⟩
  · rintro ⟨l, hl, hx⟩
    exact ⟨l, by simpa only [List.mem_take_iff_idxOf_lt (List.mem_finRange l),
      List.idxOf_finRange] using hl, hx⟩

theorem beforeB_history_mem (f : RegisteredF r d) (N k : Nat)
    (i : Fin d) (l : Fin (N + 1)) :
    historyDefAddr f N i l ∈ beforeB f N k ↔ l.val < k := by
  rw [beforeB_mem]
  constructor
  · rintro ⟨j, m, hm, he⟩
    obtain ⟨_, rfl⟩ := (historyDefAddr_inj f i j l m).mp he
    exact hm
  · intro hl
    exact ⟨i, l, hl, rfl⟩

theorem beforeG_target_mem (f : RegisteredF r d) (N k : Nat)
    (x : OccRef (program f N)) :
    x ∈ beforeG f N k ↔ ∃ i l, l.val < k ∧ x.target = historyDefAddr f N i l := by
  rw [beforeG_mem]
  constructor
  · rintro ⟨l, hl, hx⟩
    obtain ⟨i, hi⟩ := (group_targets_slice f N l x).mp hx
    exact ⟨i, l, hl, hi⟩
  · rintro ⟨i, l, hl, hi⟩
    exact ⟨l, hl, (group_targets_slice f N l x).mpr ⟨i, hi⟩⟩

theorem beforeB_append_history_mem (f : RegisteredF r d) (N : Nat)
    (k : Fin (N + 1)) (i : Fin d) (l : Fin (N + 1)) :
    historyDefAddr f N i l ∈ beforeB f N k.val ++ block f N k ↔ l.val ≤ k.val := by
  rw [List.mem_append, beforeB_history_mem, mem_block_iff]
  simp only [historyDefAddr_inj]
  constructor
  · rintro (hl | ⟨_, _, he⟩)
    · omega
    · cases he
      omega
  · intro hl
    by_cases he : l = k
    · exact Or.inr ⟨i, rfl, he.symm⟩
    · left
      have hn : l.val ≠ k.val := fun h => he (Fin.ext h)
      omega

theorem beforeG_append_target_mem (f : RegisteredF r d) (N : Nat)
    (k : Fin (N + 1)) (x : OccRef (program f N)) :
    x ∈ beforeG f N k.val ++ group f N k ↔
      ∃ i l, l.val ≤ k.val ∧ x.target = historyDefAddr f N i l := by
  rw [List.mem_append, beforeG_target_mem, group_targets_slice]
  constructor
  · rintro (⟨i, l, hl, hi⟩ | ⟨i, hi⟩)
    · exact ⟨i, l, by omega, hi⟩
    · exact ⟨i, k, by omega, hi⟩
  · rintro ⟨i, l, hl, hi⟩
    by_cases he : l = k
    · exact Or.inr ⟨i, by simpa [he] using hi⟩
    · left
      have hn : l.val ≠ k.val := fun h => he (Fin.ext h)
      exact ⟨i, l, by omega, hi⟩

theorem cons_phase_iff (f : RegisteredF r d) (N : Nat)
    (k : Fin (N + 1)) (phase : Fin 3) (x : OccRef (program f N)) :
    (plan f N).Cons (3 * k.val + phase.val) x ↔
      ∃ i l, 3 * l.val + 2 ≤ 3 * k.val + phase.val ∧
        x.target = historyDefAddr f N i l := by
  fin_cases phase
  all_goals dsimp only
  all_goals unfold Cons
  · rw [Nat.add_zero, consList_phase_zero, beforeG_target_mem]
    constructor <;> rintro ⟨i, l, hl, hi⟩ <;> exact ⟨i, l, by omega, hi⟩
  · rw [consList_phase_one, beforeG_target_mem]
    constructor <;> rintro ⟨i, l, hl, hi⟩ <;> exact ⟨i, l, by omega, hi⟩
  · rw [consList_phase_two, beforeG_append_target_mem]
    constructor <;> rintro ⟨i, l, hl, hi⟩ <;> exact ⟨i, l, by omega, hi⟩

theorem mat_phase_iff (f : RegisteredF r d) (N : Nat)
    (k : Fin (N + 1)) (phase : Fin 3) (i : Fin d) (l : Fin (N + 1)) :
    (plan f N).Mat (3 * k.val + phase.val) (historyDefAddr f N i l) ↔
      3 * l.val + 1 ≤ 3 * k.val + phase.val := by
  fin_cases phase
  all_goals dsimp only
  all_goals unfold Mat
  · rw [Nat.add_zero, matList_phase_zero, beforeB_history_mem]
    omega
  · rw [matList_phase_one, beforeB_append_history_mem]
    omega
  · rw [matList_phase_two, beforeB_append_history_mem]
    omega

theorem history_pubList_mem (f : RegisteredF r d) (N pc : Nat)
    (i : Fin d) (l : Fin (N + 1)) :
    (plan f N).Pub pc (historyAddress d N i l) ↔
      historyDefAddr f N i l ∈ (plan f N).pubList pc := by
  unfold Pub
  change (false = true ∨ _) ↔ _
  simp only [Bool.false_eq_true, false_or, List.mem_map]
  constructor
  · rintro ⟨x, hx, he⟩
    rcases x with ⟨t, c⟩
    obtain rfl := defined_eq_history f t
    have hc : c = historyCoord i l := by
      simpa only [DefAddr.addr, historyAddress, historyDefined, Sigma.mk.injEq, heq_eq_eq,
        true_and] using he
    subst c
    exact hx
  · intro hx
    exact ⟨historyDefAddr f N i l, hx, rfl⟩

theorem pub_phase_iff (f : RegisteredF r d) (N : Nat)
    (k : Fin (N + 1)) (phase : Fin 3) (i : Fin d) (l : Fin (N + 1)) :
    (plan f N).Pub (3 * k.val + phase.val) (historyAddress d N i l) ↔
      3 * (l.val + 1) ≤ 3 * k.val + phase.val := by
  rw [history_pubList_mem]
  fin_cases phase
  all_goals dsimp only
  · rw [Nat.add_zero, pubList_phase_zero, beforeB_history_mem]
    omega
  · rw [pubList_phase_one, beforeB_history_mem]
    omega
  · rw [pubList_phase_two, beforeB_history_mem]
    omega

theorem prefix_membership (f : RegisteredF r d) (N pc : Nat)
    (hpc : pc ≤ 3 * (N + 1)) :
    (∀ x, (plan f N).Cons pc x ↔
      ∃ i l, 3 * l.val + 2 ≤ pc ∧ x.target = historyDefAddr f N i l) ∧
    (∀ i l, (plan f N).Mat pc (historyDefAddr f N i l) ↔ 3 * l.val + 1 ≤ pc) ∧
    (∀ i l, (plan f N).Pub pc (historyAddress d N i l) ↔ 3 * (l.val + 1) ≤ pc) := by
  rcases boundary_decomposition N pc hpc with rfl | ⟨k, phase, rfl⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [Cons, consList_phase_zero, beforeG_target_mem]
      constructor <;> rintro ⟨i, l, hl, hi⟩ <;>
        exact ⟨i, l, by have := l.isLt; omega, hi⟩
    · intro i l
      rw [Mat, matList_phase_zero, beforeB_history_mem]
      have := l.isLt
      omega
    · intro i l
      rw [history_pubList_mem, pubList_phase_zero, beforeB_history_mem]
      have := l.isLt
      omega
  · exact ⟨cons_phase_iff f N k phase, mat_phase_iff f N k phase,
      pub_phase_iff f N k phase⟩

theorem history_live_iff (f : RegisteredF r d) (N pc : Nat)
    (hpc : pc ≤ 3 * (N + 1)) (i : Fin d) (l : Fin (N + 1)) :
    (plan f N).Live pc (historyAddress d N i l) ↔ 3 * (l.val + 1) ≤ pc := by
  rw [Live, Ret, prefix_retList]
  simp only [List.map_nil, List.not_mem_nil, not_false_eq_true, and_true]
  exact (prefix_membership f N pc hpc).2.2 i l

theorem input_pub_live (f : RegisteredF r d) (N pc : Nat)
    (a : Address (declarations d N)) (ha : (program f N).input a.1 = true) :
    (plan f N).Pub pc a ∧ (plan f N).Live pc a := by
  have hp : (plan f N).Pub pc a := Or.inl ha
  refine ⟨hp, hp, ?_⟩
  simp only [Ret, prefix_retList, List.map_nil, List.not_mem_nil, not_false_eq_true]

#print axioms group_targets_slice
#print axioms beforeB_mem
#print axioms beforeG_mem
#print axioms beforeB_history_mem
#print axioms beforeG_target_mem
#print axioms beforeB_append_history_mem
#print axioms beforeG_append_target_mem
#print axioms cons_phase_iff
#print axioms mat_phase_iff
#print axioms history_pubList_mem
#print axioms pub_phase_iff
#print axioms prefix_membership
#print axioms history_live_iff
#print axioms input_pub_live
#print axioms command_init
#print axioms command_acc
#print axioms command_pub
#print axioms command_end
#print axioms consList_phase_zero
#print axioms matList_phase_zero
#print axioms pubList_phase_zero
#print axioms consList_phase_one
#print axioms matList_phase_one
#print axioms pubList_phase_one
#print axioms consList_phase_two
#print axioms matList_phase_two
#print axioms pubList_phase_two
#print axioms prefix_phase_lists
#print axioms prefix_retList
#print axioms boundary_decomposition
#print axioms command_index_decomposition

end LeanNCD.Semantics.Program.Plan.ScanHistory
