import LeanNCD.Semantics.Plan.Fusion
import LeanNCD.Semantics.Plan.Correctness

/- Slice 2 (T3): Lemma 31.2 and Theorem 31.3 for FUSED plans, stated about `π.runPlan` of the
   fused plan `π` under `FValid π := π.expand.Valid`. The run bridge (`runPlan_agree`, in
   Fusion.lean) says the fused run and the run of the expansion agree on final memory (done) and
   on the failing occurrence (failed), so the slice-1 run lemma lifts to any command boundary
   (`runFrom_R_F`; `runPlan_R_F` is its instance at pc = 0, with R at the end of the run, pc =
   number of commands) and the terminal theorems keep their proofs.
   `done m M'` reports `m = π.commands.length` (the number of COMMANDS, not annotations): the
   pc field is never compared across the fused plan and its expansion. Theorem 31.3 failure
   case compares fails / no-model only (D5; a failed fused command reports the PRE-command
   memory, D14). -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r} {π : P.Plan}

/-- Fusion validity: the expansion is valid (spec 29.3 "expand fused annotations in their
    stated order"). -/
abbrev FValid (π : P.Plan) : Prop := π.expand.Valid

section Check

variable [DecidableEq σ.Tensor]

/-- The slice-2 checker: the slice-1 checker on the expansion. -/
def checkPlanF (π : P.Plan) : Bool := π.expand.checkPlan

theorem checkPlanF_sound (h : π.checkPlanF = true) : π.FValid := checkPlan_sound π.expand h

theorem checkPlanF_complete (h : π.FValid) : π.checkPlanF = true := checkPlan_complete π.expand h

theorem checkPlanF_iff : π.checkPlanF = true ↔ π.FValid := checkPlan_iff π.expand

end Check

/-- At the end of the run the command prefix of the fused plan and the annotation prefix of the
    expansion are both the whole annotation list. -/
theorem prefixAnn_done {m n : Nat} (hm : m = π.commands.length) (hn : n = π.expand.commands.length) :
    π.prefixAnn m = π.expand.prefixAnn n := by
  subst hm hn
  rw [prefixAnn_length, prefixAnn_length, expand_ann]

variable [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))

omit [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
/-- `Decode` depends on the plan only through the annotation prefix at its position. -/
theorem decode_prefix_congr {π π' : P.Plan} {pc pc' : Nat}
    (h : π.prefixAnn pc = π'.prefixAnn pc') (M : Memory K σ) :
    π.Decode pc M = π'.Decode pc' M := by
  have hr : π.readPub pc = π'.readPub pc' := by
    funext M a
    have hp : π.Pub pc a ↔ π'.Pub pc' a := by simp [Pub, pubList, h]
    unfold readPub
    by_cases hπ : π.Pub pc a
    · rw [if_pos hπ, if_pos (hp.mp hπ)]
    · rw [if_neg hπ, if_neg (fun h' => hπ (hp.mpr h'))]
  unfold Decode
  rw [hr]

/-- **Mid-run run lemma for fused plans.** The slice-1 `run_R` from an arbitrary command boundary
    `pc` of a plan whose expansion is valid: from `R` and the reference state at `pc`, the run of
    the remaining commands ends `done` with `R` at the command count, or fails on a matched
    occurrence. -/
theorem runFrom_R_F (hv : π.FValid) (η : P.Input) (pc : Nat) (M : Memory K σ) (c : P.Running)
    (hle : pc ≤ π.commands.length) (hR : π.R ops η pc M c) (hc : π.refState ops η pc = some c) :
    (∃ M' c', π.runFrom ops pc M (π.commands.drop pc) = .done π.commands.length M' ∧
        π.refState ops η π.commands.length = some c' ∧ π.R ops η π.commands.length M' c' ∧
        ∃ events, Execution P ops events (.running c) (.running c')) ∨
    (∃ o pc' M' c' events, π.runFrom ops pc M (π.commands.drop pc) = .failed o pc' M' ∧
        Execution P ops events (.running c) (.failed o.1 o.2 c')) := by
  have hag := runFrom_agree π ops (π.commands.drop pc) pc M rfl
  have hoff : π.ann.drop (π.offset pc) = (π.commands.drop pc).flatten := by
    rw [ann_eq_append π pc]
    exact List.drop_left' rfl
  have hd : π.expand.commands.drop (π.offset pc) =
      (π.commands.drop pc).flatten.map (fun a => [a]) := by
    simp only [expand, ← List.map_drop, hoff]
  have hle' : π.offset pc ≤ π.expand.commands.length := by
    have := congrArg List.length (ann_eq_append π pc)
    simp only [List.length_append, offset] at this ⊢
    simp only [expand, List.length_map]
    omega
  have hp := prefixAnn_eq_expand (π := π) pc
  rcases run_R ops hv _ _ _ _ hd hle' (R_transport ops hp hR)
      ((refState_prefix_congr ops hp).symm.trans hc) with
    ⟨M', c', he, hc2, hR2, ev⟩ | ⟨o, pc', M', c', ev, he, hex⟩
  · rw [he] at hag
    cases h : π.runFrom ops pc M (π.commands.drop pc) with
    | done m M'' =>
      rw [h] at hag
      have hM : M'' = M' := hag
      have hm := runFrom_done_pc ops π _ pc M M'' m h
      have hmm : m = π.commands.length := by simp at hm; omega
      subst hM hmm
      have hq := prefixAnn_done (π := π) (m := π.commands.length) rfl
        (n := π.expand.commands.length) rfl
      exact Or.inl ⟨_, c', rfl, (refState_prefix_congr (η := η) ops hq).trans hc2,
        R_transport ops hq.symm hR2, ev⟩
    | failed o'' pc'' M'' => rw [h] at hag; exact False.elim hag
    | stuck pc'' M'' => rw [h] at hag; exact False.elim hag
  · rw [he] at hag
    cases h : π.runFrom ops pc M (π.commands.drop pc) with
    | done m M'' => rw [h] at hag; exact False.elim hag
    | failed o'' pc'' M'' =>
      rw [h] at hag
      have ho : o'' = o := hag
      subst ho
      exact Or.inr ⟨o'', pc'', M'', c', ev, rfl, hex⟩
    | stuck pc'' M'' => rw [h] at hag; exact False.elim hag

/-- **Run lemma for fused plans.** The slice-1 `runPlan_R` for a plan whose expansion is valid:
    when the run ends `done`, R holds at pc = number of commands (the end of the run). The
    intermediate command boundaries are covered by `runFrom_R_F`. -/
theorem runPlan_R_F (hv : π.FValid) (η : P.Input) :
    (∃ M' c', π.runPlan ops (Start η) = .done π.commands.length M' ∧
        π.refState ops η π.commands.length = some c' ∧ π.R ops η π.commands.length M' c' ∧
        ∃ events, Execution P ops events (.running (P.initial η)) (.running c')) ∨
    (∃ o pc' M' c' events, π.runPlan ops (Start η) = .failed o pc' M' ∧
        Execution P ops events (.running (P.initial η)) (.failed o.1 o.2 c')) := by
  simpa [runPlan] using runFrom_R_F ops hv η 0 (Start η) (P.initial η) (Nat.zero_le _)
    (π.R_start ops η) (by simp [refState, prefixAnn_zero])

/-- A fused plan with a valid expansion never gets stuck. -/
theorem runPlan_not_stuck_F (hv : π.FValid) (η : P.Input) (pc : Nat) (M : Memory K σ) :
    π.runPlan ops (Start η) ≠ .stuck pc M := by
  rcases runPlan_R_F ops hv η with ⟨_, _, h, -⟩ | ⟨_, _, _, _, _, h, -⟩ <;> rw [h] <;> simp

/-- **Lemma 31.2 (terminal adequacy), fused.** As `terminal_adequacy`, for the fused plan:
    `m` is the number of commands. -/
theorem terminal_adequacy_F (hv : π.FValid) (η : P.Input) {m : Nat} {M' : Memory K σ}
    (hrun : π.runPlan ops (Start η) = .done m M') :
    m = π.commands.length ∧ ∃ c, π.refState ops η m = some c ∧ π.R ops η m M' c ∧
      ∃ complete : P.Complete c,
        π.Decode m M' = some (P.outputProjection (P.finalStore c complete)) := by
  rcases runPlan_R_F ops hv η with ⟨M₁, c, h, hc, hR, -⟩ | ⟨_, _, _, _, _, h, -⟩
  · rw [hrun] at h
    obtain ⟨rfl, rfl⟩ := PlanOutcome.done.inj h
    have hp := prefixAnn_done (π := π) (m := π.commands.length) rfl
      (n := π.expand.commands.length) rfl
    have complete := complete_of_refState ops hv
      ((refState_prefix_congr (η := η) ops hp).symm.trans hc)
    have outs : ∀ t : {t : σ.Tensor // P.output t = true}, ∀ p, π.Pub π.commands.length ⟨t.val, p⟩ :=
      fun t p => (hR.published _).mp (complete.2 _)
    obtain ⟨out, hd, hout⟩ := π.decode_of_R ops hR outs
    refine ⟨rfl, c, hc, hR, complete, ?_⟩
    rw [hd]
    congr 1
    funext t p
    have h1 := hout t p
    rw [P.finalStore_published c complete] at h1
    exact (Option.some.inj h1).symm
  · rw [hrun] at h
    cases h

/-- **Theorem 31.3 (a), fused.** -/
theorem done_correct_F (hv : π.FValid) (η : P.Input) {m : Nat} {M' : Memory K σ}
    (hrun : π.runPlan ops (Start η) = .done m M') :
    ∃ c, ∃ success : P.Successful ops η c,
      (∀ ρ, P.Models ops η ρ ↔ ρ = P.finalStore c success.2) ∧
      π.Decode m M' = some (P.outputProjection (P.finalStore c success.2)) ∧
      P.denotation ops η (P.successful_admInput ops η c success) =
        P.outputProjection (P.finalStore c success.2) := by
  obtain ⟨-, c, -, hR, complete, hd⟩ := terminal_adequacy_F ops hv η hrun
  let success : P.Successful ops η c := ⟨hR.reach, complete⟩
  refine ⟨c, success, fun ρ => ⟨P.successful_unique ops η c success ρ, ?_⟩, hd,
    P.successful_denotation ops η c success⟩
  rintro rfl
  exact P.successful_model ops η c success

/-- **Theorem 31.3 (b), fused.** A `failed` fused run means no model exists (D5, D14: neither
    the failing occurrence nor the pre-command memory is compared). -/
theorem failed_correct_F (hv : π.FValid) (η : P.Input) {o : OccRef P} {pc : Nat}
    {M' : Memory K σ} (hrun : π.runPlan ops (Start η) = .failed o pc M') :
    ¬ ∃ ρ, P.Models ops η ρ := by
  rcases runPlan_R_F ops hv η with ⟨_, _, h, -⟩ | ⟨o', _, _, c', _, _, hex⟩
  · rw [hrun] at h
    cases h
  · exact P.failed_no_model ops η o'.1 o'.2 c' (hex.reaches P ops)

/-- **Theorem 31.3 (c), error-free profile, fused.** -/
theorem done_or_failed_F (hv : π.FValid) (η : P.Input) :
    (∃ M', π.runPlan ops (Start η) = .done π.commands.length M') ∨
      ∃ o pc M', π.runPlan ops (Start η) = .failed o pc M' := by
  rcases runPlan_R_F ops hv η with ⟨M', _, h, -⟩ | ⟨o, pc, M', _, _, h, -⟩
  · exact Or.inl ⟨M', h⟩
  · exact Or.inr ⟨o, pc, M', h⟩

/-- **Theorem 31.3 (c), converse, fused.** -/
theorem done_of_model_F (hv : π.FValid) (η : P.Input) {ρ : Store K σ}
    (hρ : P.Models ops η ρ) :
    ∃ M', π.runPlan ops (Start η) = .done π.commands.length M' ∧
      π.Decode π.commands.length M' = some (P.outputProjection ρ) := by
  rcases done_or_failed_F ops hv η with ⟨M', h⟩ | ⟨_, _, _, h⟩
  · obtain ⟨c, success, hmod, hd, -⟩ := done_correct_F ops hv η h
    rw [(hmod ρ).mp hρ]
    exact ⟨M', h, hd⟩
  · exact absurd ⟨ρ, hρ⟩ (failed_correct_F ops hv η h)

/-- (b) + (c), fused: the run is `done` iff a model exists. -/
theorem done_iff_model_F (hv : π.FValid) (η : P.Input) :
    (∃ m M', π.runPlan ops (Start η) = .done m M') ↔ ∃ ρ, P.Models ops η ρ := by
  constructor
  · rintro ⟨m, M', h⟩
    obtain ⟨c, success, hmod, -⟩ := done_correct_F ops hv η h
    exact ⟨_, (hmod _).mpr rfl⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨M', h, -⟩ := done_of_model_F ops hv η hρ
    exact ⟨_, M', h⟩

#print axioms checkPlanF_sound
#print axioms checkPlanF_complete
#print axioms checkPlanF_iff
#print axioms runPlan_agree
#print axioms runFrom_R_F
#print axioms runPlan_R_F
#print axioms runPlan_not_stuck_F
#print axioms terminal_adequacy_F
#print axioms done_correct_F
#print axioms failed_correct_F
#print axioms done_or_failed_F
#print axioms done_of_model_F
#print axioms done_iff_model_F

end LeanNCD.Semantics.Program.Plan
