import LeanNCD.Semantics.Plan.ScanHistory.Allocation
import LeanNCD.Semantics.Plan.ScanHistory.Operator
import LeanNCD.Semantics.Plan.ScanHistory.Schedule

namespace LeanNCD.Semantics.Program.Plan.ScanHistory

variable {V : Type} {d : Nat} {r : Registry (Carrier V)}

def block (f : RegisteredF r d) (N : Nat) (l : Fin (N + 1)) :
    List (DefAddr (program f N)) :=
  (List.finRange d).map fun i => historyDefAddr f N i l

def persistentGroup (f : RegisteredF r d) (N : Nat) (l : Fin (N + 1)) :
    List (OccRef (program f N)) :=
  (List.finRange d).map fun i => ⟨historyDefined f N, persistentOccurrence f N i l⟩

def initialGroup (f : RegisteredF r d) (N : Nat) : List (OccRef (program f N)) :=
  (List.finRange d).map fun i => ⟨historyDefined f N, initialOccurrence f N i⟩

def recurrenceGroup (f : RegisteredF r d) (N : Nat) (l : Fin N) :
    List (OccRef (program f N)) :=
  (List.finRange d).map fun i => ⟨historyDefined f N, recurrenceOccurrence f N i l⟩

def group (f : RegisteredF r d) (N : Nat) (l : Fin (N + 1)) :
    List (OccRef (program f N)) :=
  persistentGroup f N l ++ Fin.cases (initialGroup f N) (recurrenceGroup f N) l

def plan (f : RegisteredF r d) (N : Nat) : (program f N).Plan where
  tensors := [.X, .Z, .H]
  tensors_nodup := by simp
  tensors_complete := by intro t; cases t <;> simp
  commands := scheduleCommands (List.finRange (N + 1)) (block f N) (group f N)
  allocation := allocation f N

def input (f : RegisteredF r d) (N : Nat) (X Z : State V d) :
    (program f N).Input :=
  ⟨(fun t => match t with
    | .X => some (fun p => X p.1)
    | .Z => some (fun p => Z p.1)
    | .H => none), by intro t; cases t <;> rfl⟩

theorem block_length (f : RegisteredF r d) (N : Nat) (l : Fin (N + 1)) :
    (block f N l).length = d := by simp [block]

theorem group_length (f : RegisteredF r d) (N : Nat) (l : Fin (N + 1)) :
    (group f N l).length = 2 * d := by
  refine Fin.cases ?_ (fun j => ?_) l
  · simp [group, persistentGroup, initialGroup, two_mul]
  · simp [group, persistentGroup, recurrenceGroup, two_mul]

theorem zero_dim_group (f : RegisteredF r 0) (N : Nat) (l : Fin (N + 1)) :
    group f N l = [] :=
  List.length_eq_zero_iff.mp (by simpa using group_length f N l)

theorem plan_length (f : RegisteredF r d) (N : Nat) :
    (plan f N).commands.length = 3 * (N + 1) := by
  simp only [plan, scheduleCommands_length, List.length_finRange]

theorem plan_singleton (f : RegisteredF r d) (N : Nat) : (plan f N).Singleton :=
  singleton_of_scheduleCommands _ _ _ _ rfl

theorem plan_layout (f : RegisteredF r d) (N pc : Nat) : (plan f N).LayoutOK pc :=
  (plan f N).layoutOK_of_place_injective (place_injective f N) pc

theorem plan_retList (f : RegisteredF r d) (N pc : Nat) : (plan f N).retList pc = [] :=
  retList_at_any_boundary _ _ _ _ rfl pc

theorem plan_pubList_boundary (f : RegisteredF r d) (N k : Nat) :
    (plan f N).pubList (3 * k) =
      ((List.finRange (N + 1)).take k).flatMap (block f N) :=
  pubList_at_slice_boundary _ _ _ _ rfl k

theorem history_live_at_slice_boundary (f : RegisteredF r d) (N k : Nat)
    (i : Fin d) (l : Fin (N + 1)) (hl : l.val < k) :
    (plan f N).Live (3 * k) (historyAddress d N i l) := by
  refine ⟨Or.inr ?_, ?_⟩
  · apply List.mem_map.mpr
    refine ⟨historyDefAddr f N i l, ?_, rfl⟩
    rw [plan_pubList_boundary]
    apply List.mem_flatMap.mpr
    refine ⟨l, ?_, ?_⟩
    · rw [List.mem_take_iff_idxOf_lt (List.mem_finRange l), List.idxOf_finRange]
      exact hl
    · exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  · simp [Ret, plan_retList]

#print axioms block_length
#print axioms group_length
#print axioms zero_dim_group
#print axioms plan_length
#print axioms plan_singleton
#print axioms plan_layout
#print axioms plan_retList
#print axioms plan_pubList_boundary
#print axioms history_live_at_slice_boundary

end LeanNCD.Semantics.Program.Plan.ScanHistory
