import LeanNCD.Semantics.Plan.ScanHistory.Prefix
import LeanNCD.Semantics.Plan.Simulation

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

#print axioms plan_initOK_slice
#print axioms plan_accOK_slice
#print axioms plan_pubOK_slice
#print axioms plan_initOK
#print axioms plan_accOK
#print axioms plan_pubOK

end LeanNCD.Semantics.Program.Plan.ScanHistory
