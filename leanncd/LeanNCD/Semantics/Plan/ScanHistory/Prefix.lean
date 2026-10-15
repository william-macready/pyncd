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
