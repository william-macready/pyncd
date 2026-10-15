import LeanNCD.Semantics.Plan.ScanHistory.Model
import LeanNCD.Semantics.Plan.ScanHistory.Validity
import LeanNCD.Semantics.Plan.Run
import LeanNCD.Semantics.Plan.Correctness

namespace LeanNCD.Semantics.Program.Plan

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r} {π : P.Plan}
variable [DecidableEq σ.Tensor]
variable [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]

/-- A finite segment of the original valid plan succeeds in the presence of a model.
    The segment is not itself required to satisfy full-plan coverage. -/
private theorem prefix_model_R (ops : (s : S) → ScalarOps (K s))
    (hv : π.Valid) (η : P.Input) (ρ : Store K σ) (hρ : P.Models ops η ρ) :
    ∀ (cmds : List (Command P)) (pc : Nat) (M : Memory K π.allocation) (c : P.Running),
      (∀ j cmd, cmds[j]? = some cmd → π.commands[pc + j]? = some cmd) →
      π.R ops η pc M c → π.refState ops η pc = some c →
      ∃ M' c', π.runFrom ops pc M cmds = .done (pc + cmds.length) M' ∧
        π.refState ops η (pc + cmds.length) = some c' ∧
        π.R ops η (pc + cmds.length) M' c'
  | [], pc, M, c, _, hR, hc => by
    exact ⟨M, c, rfl, hc, hR⟩
  | cmd :: rest, pc, M, c, hcmds, hR, hc => by
    have hcmd : π.commands[pc]? = some cmd := by
      simpa using hcmds 0 cmd rfl
    have hlt : pc < π.commands.length := (List.getElem?_eq_some_iff.mp hcmd).1
    obtain ⟨a, rfl⟩ := hv.singleton _ (List.mem_of_getElem? hcmd)
    have hstep : π.stepCommand ops pc M [a] = π.stepPlan ops pc M := by
      simp [stepPlan, hcmd]
    cases hs : π.stepPlan ops pc M with
    | ok M₁ =>
      obtain ⟨layout, layout'⟩ := hv.layout_boundary hcmd
      obtain ⟨c₁, hc₁, hR₁, -⟩ :=
        step_R ops hR hc hcmd (hv.stepOK pc a hcmd) layout layout' hs
      obtain ⟨M', c', hr, hc', hR'⟩ :=
        prefix_model_R ops hv η ρ hρ rest (pc + 1) M₁ c₁
          (fun j cmd hj => by
            have := hcmds (j + 1) cmd (by simpa using hj)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
          hR₁ hc₁
      have he : pc + (rest.length + 1) = pc + 1 + rest.length := by omega
      refine ⟨M', c', ?_, ?_, ?_⟩
      · simpa only [runFrom, hstep, hs, List.length_cons, he] using hr
      · simpa only [List.length_cons, he] using hc'
      · simpa only [List.length_cons, he] using hR'
    | semFail o =>
      exact (step_failed_no_model ops hR hcmd
        (fun G hG x hx => by
          cases hG
          exact ((hv.accOK pc G hcmd).2 x hx).1) hs ⟨ρ, hρ⟩).elim
    | stuck => exact (step_not_stuck ops hv hR hlt hs).elim

namespace ScanHistory

variable {V : Type} [AddCommMonoid V] {d N : Nat} {r : Registry (Carrier V)}

/-- Every command boundary of an actual scan prefix succeeds and has the correct
    reference state and physical representation, including the zero bounds. -/
theorem prefix_done_R (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input)
    (pc : Nat) (hpc : pc ≤ 3 * (N + 1)) :
    ∃ M c,
      (plan f N).runFrom ops 0 ((plan f N).Start η)
        ((plan f N).commands.take pc) = .done pc M ∧
      (plan f N).refState ops η pc = some c ∧ (plan f N).R ops η pc M c := by
  have hlen : pc ≤ (plan f N).commands.length := by rwa [plan_length]
  have ht : ((plan f N).commands.take pc).length = pc :=
    List.length_take_of_le hlen
  have h := prefix_model_R ops (plan_valid f N) η (historyStore f N η)
    (historyStore_models f N ops η) ((plan f N).commands.take pc)
    0 ((plan f N).Start η) ((program f N).initial η)
    (fun j cmd hj => by
      rw [List.getElem?_take] at hj
      split_ifs at hj with hjpc
      simpa using hj)
    ((plan f N).R_start ops η) (by simp [refState, prefixAnn_zero])
  simpa only [ht, Nat.zero_add] using h

/-- Published history is the independent recurrence in both logical read views
    and the actual physical buffer, at every successful command prefix. -/
theorem history_retained (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input)
    (pc : Nat) (hpc : pc ≤ 3 * (N + 1))
    {M : Memory (Carrier V) (plan f N).allocation}
    (hrun : (plan f N).runFrom ops 0 ((plan f N).Start η)
      ((plan f N).commands.take pc) = .done pc M)
    (i : Fin d) (l : Fin (N + 1)) (hl : 3 * (l.val + 1) ≤ pc) :
    readSlot (allocation f N) M (historyAddress d N i l) =
        some (history f.transition (inputX η) (inputZ η) l.val i) ∧
    (plan f N).readPub pc M (historyAddress d N i l) =
        some (history f.transition (inputX η) (inputZ η) l.val i) ∧
    M (.inr ⟨l, i⟩) =
        some (history f.transition (inputX η) (inputZ η) l.val i) := by
  obtain ⟨M', c, hr, _, hR⟩ := prefix_done_R f N ops η pc hpc
  rw [hrun] at hr
  obtain rfl := (PlanOutcome.done.inj hr).2
  have live := (history_live_iff f N pc hpc i l).mpr hl
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((hR.published _).mpr live.1)
  have agree := (program f N).candidate_preserved ops η (historyStore f N η)
    (historyStore_models f N ops η) hR.reach
  have value : v = history f.transition (inputX η) (inputZ η) l.val i :=
    (agree (historyAddress d N i l) v hv).symm
  have published : c.published (historyAddress d N i l) =
      some (history f.transition (inputX η) (inputZ η) l.val i) := by
    rw [hv, value]
  have slot := (hR.pubSlot _ ((plan f N).slotView_pub.mpr live)).trans published
  refine ⟨slot, ((plan f N).readPub_eq ops hR live).trans published, ?_⟩
  simpa only [readSlot, program, isInput, Bool.false_eq_true, dite_false,
    allocation, historyAddress, historyCoord, cast_eq] using slot

/-- Later actual command prefixes retain every already published history value,
    including boundaries inside a later slice's init/acc/pub sequence. -/
theorem history_retained_later (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input)
    (pc pc' : Nat) (hpc' : pc' ≤ 3 * (N + 1)) (hle : pc ≤ pc')
    {M M' : Memory (Carrier V) (plan f N).allocation}
    (hrun : (plan f N).runFrom ops 0 ((plan f N).Start η)
      ((plan f N).commands.take pc) = .done pc M)
    (hrun' : (plan f N).runFrom ops 0 ((plan f N).Start η)
      ((plan f N).commands.take pc') = .done pc' M')
    (i : Fin d) (l : Fin (N + 1)) (hl : 3 * (l.val + 1) ≤ pc) :
    M' (.inr ⟨l, i⟩) =
        some (history f.transition (inputX η) (inputZ η) l.val i) ∧
    M' (.inr ⟨l, i⟩) = M (.inr ⟨l, i⟩) ∧
    readSlot (allocation f N) M' (historyAddress d N i l) =
      readSlot (allocation f N) M (historyAddress d N i l) ∧
    (plan f N).readPub pc' M' (historyAddress d N i l) =
      (plan f N).readPub pc M (historyAddress d N i l) := by
  obtain ⟨hs, hp, hm⟩ := history_retained f N ops η pc
    (Nat.le_trans hle hpc') hrun i l hl
  obtain ⟨hs', hp', hm'⟩ := history_retained f N ops η pc' hpc' hrun' i l
    (Nat.le_trans hl hle)
  exact ⟨hm', hm'.trans hm.symm, hs'.trans hs.symm, hp'.trans hp.symm⟩

/-- Every validated input completes, and the entire typed history is decoded.
    This includes successful decoding of an empty coordinate domain. -/
theorem scan_decode_history (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input) :
    ∃ M, (plan f N).runPlan ops ((plan f N).Start η) = .done (3 * (N + 1)) M ∧
      (plan f N).Decode (3 * (N + 1)) M = some (history_output f N η) := by
  simpa only [plan_length, history_output] using
    done_of_model ops (plan_valid f N) η (historyStore_models f N ops η)

/-- Completion needs neither a successful-run premise nor positive bounds. -/
theorem scan_done (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input) :
    ∃ M, (plan f N).runPlan ops ((plan f N).Start η) = .done (3 * (N + 1)) M := by
  obtain ⟨M, hr, -⟩ := scan_decode_history f N ops η
  exact ⟨M, hr⟩

/-- Admissibility is supplied by the independent history model, not assumed. -/
theorem scan_admInput (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input) :
    (program f N).AdmInput ops η :=
  ⟨historyStore f N η, historyStore_models f N ops η,
    fun ρ hρ => (models_iff_historyStore f N ops η ρ).mp hρ⟩

/-- The public denotation is the full independent history output. -/
theorem scan_denotation_history (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input) :
    (program f N).denotation ops η (scan_admInput f N ops η) =
      history_output f N η :=
  (program f N).denotation_of_model ops η (scan_admInput f N ops η)
    (historyStore f N η) (historyStore_models f N ops η)

#print axioms scan_done
#print axioms scan_decode_history
#print axioms scan_admInput
#print axioms scan_denotation_history
#print axioms prefix_done_R
#print axioms history_retained
#print axioms history_retained_later

end ScanHistory
end LeanNCD.Semantics.Program.Plan
