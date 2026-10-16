import LeanNCD.Semantics.Plan.ScanHistory.Prefix
import LeanNCD.Semantics.Plan.Validity

namespace LeanNCD.Semantics.Program.Plan.ScanHistory

variable {V : Type} {d : Nat} {r : Registry (Carrier V)}

theorem plan_initOK_slice (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).InitOK (3 * k.val) (block f N k) := by
  have hk := k.isLt
  obtain ⟨hc, _, hp⟩ := prefix_membership f N (3 * k.val) (by omega)
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_block_iff f k x).mp hx
  refine ⟨?_, ?_⟩
  · change ¬ (plan f N).Pub (3 * k.val) (historyAddress d N i k)
    rw [hp i k]
    omega
  · intro o ho hd
    have ht : OccRef.target (⟨historyDefined f N, o⟩ : OccRef (program f N)) =
        historyDefAddr f N i k := by
      change (⟨historyDefined f N,
        (program f N).destination (historyDefined f N) o.1 o.2⟩ :
        DefAddr (program f N)) = _
      rw [hd]
      rfl
    obtain ⟨j, l, hl, hj⟩ := (hc _).mp ho
    have htime := ((historyDefAddr_inj f i j k l).mp (ht.symm.trans hj)).2
    subst l
    omega

theorem plan_accOK_slice (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).AccOK (3 * k.val + 1) (group f N k) := by
  have hk := k.isLt
  obtain ⟨hc, hm, _⟩ := prefix_membership f N (3 * k.val + 1) (by omega)
  refine ⟨group_nodup f k, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := (group_targets_slice f N k x).mp hx
  refine ⟨?_, ?_⟩
  · intro ho
    obtain ⟨j, l, hl, hj⟩ := (hc x).mp ho
    have htime := ((historyDefAddr_inj f i j k l).mp (hi.symm.trans hj)).2
    subst l
    omega
  · rw [hi, hm i k]

theorem plan_pubOK_slice (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).PubOK (3 * k.val + 2) (block f N k) := by
  have hk := k.isLt
  obtain ⟨hc, hm, hp⟩ := prefix_membership f N (3 * k.val + 2) (by omega)
  refine ⟨block_nodup f k, ?_⟩
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_block_iff f k x).mp hx
  refine ⟨?_, (hm i k).mpr (by omega), ?_⟩
  · change ¬ (plan f N).Pub (3 * k.val + 2) (historyAddress d N i k)
    rw [hp i k]
    omega
  · intro o hd
    apply (hc _).mpr
    refine ⟨i, k, by omega, ?_⟩
    change (⟨historyDefined f N,
      (program f N).destination (historyDefined f N) o.1 o.2⟩ :
      DefAddr (program f N)) = _
    rw [hd]
    rfl

theorem plan_initOK (f : RegisteredF r d) (N : Nat) :
    ∀ pc B, (plan f N).commands[pc]? = some [.initZero B] →
      (plan f N).InitOK pc B := by
  intro pc B hcmd
  obtain ⟨hpc, _⟩ := List.getElem?_eq_some_iff.mp hcmd
  rw [plan_length] at hpc
  obtain ⟨k, phase, rfl⟩ := command_index_decomposition N pc hpc
  fin_cases phase
  all_goals dsimp only at hcmd ⊢
  · simp only [Nat.add_zero, command_init, Option.some.injEq, List.cons.injEq,
      Ann.initZero.injEq, and_true] at hcmd
    subst B
    simpa only [Nat.add_zero] using plan_initOK_slice f N k
  · rw [command_acc] at hcmd
    cases hcmd
  · rw [command_pub] at hcmd
    cases hcmd

theorem plan_accOK (f : RegisteredF r d) (N : Nat) :
    ∀ pc G, (plan f N).commands[pc]? = some [.acc G] →
      (plan f N).AccOK pc G := by
  intro pc G hcmd
  obtain ⟨hpc, _⟩ := List.getElem?_eq_some_iff.mp hcmd
  rw [plan_length] at hpc
  obtain ⟨k, phase, rfl⟩ := command_index_decomposition N pc hpc
  fin_cases phase
  all_goals dsimp only at hcmd ⊢
  · simp only [Nat.add_zero, command_init] at hcmd
    cases hcmd
  · simp only [command_acc, Option.some.injEq, List.cons.injEq,
      Ann.acc.injEq, and_true] at hcmd
    subst G
    exact plan_accOK_slice f N k
  · rw [command_pub] at hcmd
    cases hcmd

theorem plan_pubOK (f : RegisteredF r d) (N : Nat) :
    ∀ pc B, (plan f N).commands[pc]? = some [.pub B] →
      (plan f N).PubOK pc B := by
  intro pc B hcmd
  obtain ⟨hpc, _⟩ := List.getElem?_eq_some_iff.mp hcmd
  rw [plan_length] at hpc
  obtain ⟨k, phase, rfl⟩ := command_index_decomposition N pc hpc
  fin_cases phase
  all_goals dsimp only at hcmd ⊢
  · simp only [Nat.add_zero, command_init] at hcmd
    cases hcmd
  · rw [command_acc] at hcmd
    cases hcmd
  · simp only [command_pub, Option.some.injEq, List.cons.injEq,
      Ann.pub.injEq, and_true] at hcmd
    subst B
    exact plan_pubOK_slice f N k

theorem persistentOccurrence_footprint (f : RegisteredF r d) (N : Nat)
    (i : Fin d) (k : Fin (N + 1)) :
    footprint ((program f N).body (historyDefined f N) persistentID)
      (persistentOccurrence f N i k).2 = [⟨.X, stateCoord i⟩] := by
  simp [program, historyDefined, statementBody, persistentOccurrence, persistentID,
    footprint, directRead, valuationPair_index]

theorem initialOccurrence_footprint (f : RegisteredF r d) (N : Nat) (i : Fin d) :
    footprint ((program f N).body (historyDefined f N) initialID)
      (initialOccurrence f N i).2 = [⟨.Z, stateCoord i⟩] := by
  simp [program, historyDefined, statementBody, initialOccurrence, persistentID, initialID,
    footprint, directRead, valuationPair_index]

theorem recurrenceOccurrence_footprint (f : RegisteredF r d) (N : Nat)
    (i : Fin d) (k : Fin N) :
    footprint ((program f N).body (historyDefined f N) recurrenceID)
      (recurrenceOccurrence f N i k).2 =
      (List.finRange d).map fun j =>
        historyAddress d N j ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ := by
  simp only [program, historyDefined, statementBody, recurrenceID, persistentID, initialID,
    Fin.reduceEq, ↓reduceIte]
  rw [recurrenceBody_footprint]
  simp only [recurrenceOccurrence, valuationPair_index]

theorem plan_readyOK_slice (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).ReadyOK (3 * k.val + 1) (group f N k) := by
  intro x hx a ha
  rcases occurrence_cases f x with ⟨i, l, rfl⟩ | ⟨i, rfl⟩ | ⟨i, l, rfl⟩
  · change a ∈ footprint ((program f N).body (historyDefined f N) persistentID)
      (persistentOccurrence f N i l).2 at ha
    rw [persistentOccurrence_footprint] at ha
    obtain rfl := List.mem_singleton.mp ha
    exact (input_pub_live f N _ _ rfl).2
  · change a ∈ footprint ((program f N).body (historyDefined f N) initialID)
      (initialOccurrence f N i).2 at ha
    rw [initialOccurrence_footprint] at ha
    obtain rfl := List.mem_singleton.mp ha
    exact (input_pub_live f N _ _ rfl).2
  · obtain ⟨j, hj⟩ := (group_targets_slice f N k _).mp hx
    rw [recurrence_target] at hj
    have htime := ((historyDefAddr_inj f i j l.succ k).mp hj).2
    subst k
    change a ∈ footprint ((program f N).body (historyDefined f N) recurrenceID)
      (recurrenceOccurrence f N i l).2 at ha
    rw [recurrenceOccurrence_footprint] at ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    apply (history_live_iff f N (3 * l.succ.val + 1)
      (by have := l.isLt; simp only [Fin.val_succ]; omega) j _).mpr
    simp only [Fin.val_succ]
    omega

theorem plan_readyOK (f : RegisteredF r d) (N : Nat) :
    ∀ pc G, (plan f N).commands[pc]? = some [.acc G] →
      (plan f N).ReadyOK pc G := by
  intro pc G hcmd
  obtain ⟨hpc, _⟩ := List.getElem?_eq_some_iff.mp hcmd
  rw [plan_length] at hpc
  obtain ⟨k, phase, rfl⟩ := command_index_decomposition N pc hpc
  fin_cases phase
  all_goals dsimp only at hcmd ⊢
  · simp only [Nat.add_zero, command_init] at hcmd
    cases hcmd
  · simp only [command_acc, Option.some.injEq, List.cons.injEq,
      Ann.acc.injEq, and_true] at hcmd
    subst G
    exact plan_readyOK_slice f N k
  · rw [command_pub] at hcmd
    cases hcmd

theorem plan_valid (f : RegisteredF r d) (N : Nat) : (plan f N).Valid := by
  refine ⟨plan_singleton f N, plan_coverage1 f N, plan_coverage2 f N,
    plan_initOK f N, plan_accOK f N, plan_pubOK f N, plan_readyOK f N, ?_,
    fun pc _ => plan_layout f N pc⟩
  intro pc B hcmd
  obtain ⟨hpc, _⟩ := List.getElem?_eq_some_iff.mp hcmd
  rw [plan_length] at hpc
  obtain ⟨k, phase, rfl⟩ := command_index_decomposition N pc hpc
  fin_cases phase
  all_goals dsimp only at hcmd
  · simp only [Nat.add_zero, command_init] at hcmd
    cases hcmd
  · rw [command_acc] at hcmd
    cases hcmd
  · rw [command_pub] at hcmd
    cases hcmd

theorem plan_checkPlan (f : RegisteredF r d) (N : Nat) :
    (plan f N).checkPlan = true :=
  (checkPlan_iff (plan f N)).mpr (plan_valid f N)

#print axioms plan_initOK_slice
#print axioms plan_accOK_slice
#print axioms plan_pubOK_slice
#print axioms plan_initOK
#print axioms plan_accOK
#print axioms plan_pubOK
#print axioms persistentOccurrence_footprint
#print axioms initialOccurrence_footprint
#print axioms recurrenceOccurrence_footprint
#print axioms plan_readyOK_slice
#print axioms plan_readyOK
#print axioms plan_valid
#print axioms plan_checkPlan

end LeanNCD.Semantics.Program.Plan.ScanHistory
