import LeanNCD.Semantics.Plan.Run

/- Terminal adequacy (Lemma 31.2) and plan correctness (Theorem 31.3) for the
   slice-1 profile. Lemma 31.2 is the first consumer of `Valid.coverage1` and
   `Valid.coverage2`: at pc = m the related reference state is complete, so the
   reference final store exists, every output coordinate is published, and
   Decode returns its output projection. Theorem 31.3 compares outcomes only
   (done/model, failed/no model), never the failing occurrence or the failure
   snapshot (defect D5). -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r} {π : P.Plan}

/-- At pc = m the command prefix is the whole plan. -/
theorem prefixAnn_length (π : P.Plan) : π.prefixAnn π.commands.length = π.ann := by
  simp [prefixAnn, ann]

/-- Spec 29.3 condition 4 for every pub command, from `pubOK`. -/
theorem Valid.order4 (hv : π.Valid) : π.Order4 := by
  intro pc a ha y hy o hd
  cases a with
  | initZero S => cases hy
  | acc G => cases hy
  | pub B => exact ((hv.pubOK pc B ha).2 y hy).2.2 o hd

/-- N6 (D9): the covering half of condition 1 follows from the covering half of
    condition 2 and condition 4 (here: `pubOK`), in the singleton profile. -/
theorem cov1_of_cov2_pubOrder (hv : π.Valid) (x : OccRef P) : x ∈ π.accFlat :=
  π.accFlat_complete hv.singleton hv.coverage2.2 hv.order4 x

variable [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))

/-- The reference state related to pc = m is complete: pending is empty by
    coverage1 (every occurrence is in some group), and every address is
    published by coverage2 (every defined address is in some block) or is an
    input. -/
theorem complete_of_refState (hv : π.Valid) {η : P.Input} {c : P.Running}
    (hc : π.refState ops η π.commands.length = some c) : P.Complete c := by
  obtain ⟨hp, hb⟩ := π.refState_R2 ops hc
  refine ⟨fun t => Finset.ext fun o => ?_, fun a => ?_⟩
  · rw [hp]
    have hx : (⟨t, o⟩ : OccRef P) ∈ π.accFlat := hv.coverage1.2 ⟨t, o⟩
    simp only [Cons, consList, prefixAnn_length, Finset.notMem_empty, iff_false, not_not]
    exact hx
  · rw [hb]
    obtain ⟨t, p⟩ := a
    cases ht : P.input t
    · right
      simp only [pubList, prefixAnn_length, List.mem_map]
      exact ⟨⟨⟨t, ht⟩, p⟩, hv.coverage2.2 _, rfl⟩
    · exact Or.inl ht

/-- **Lemma 31.2 (terminal adequacy).** If a valid plan's run from `Start η`
    is `done m M'`, then `m = commands.length`, the related reference state
    `c = refState m` exists and is R-related to `M'`, `c` is complete (so the
    reference run is successful), and Decode returns the output projection of
    the reference final store. -/
theorem terminal_adequacy (hv : π.Valid) (η : P.Input) {m : Nat} {M' : Memory K σ}
    (hrun : π.runPlan ops (Start η) = .done m M') :
    m = π.commands.length ∧ ∃ c, π.refState ops η m = some c ∧ π.R ops η m M' c ∧
      ∃ complete : P.Complete c,
        π.Decode m M' = some (P.outputProjection (P.finalStore c complete)) := by
  rcases runPlan_R ops hv η with ⟨M₁, c, h, hc, hR, -⟩ | ⟨_, _, _, _, _, h, -⟩
  · rw [hrun] at h
    obtain ⟨rfl, rfl⟩ := PlanOutcome.done.inj h
    have complete := complete_of_refState ops hv hc
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

/-- **Theorem 31.3 (a).** A `done` run of a valid plan has exactly one model,
    the reference final store `ρ`; its decode is `ρ`'s output projection, which
    is also the denotation. -/
theorem done_correct (hv : π.Valid) (η : P.Input) {m : Nat} {M' : Memory K σ}
    (hrun : π.runPlan ops (Start η) = .done m M') :
    ∃ c, ∃ success : P.Successful ops η c,
      (∀ ρ, P.Models ops η ρ ↔ ρ = P.finalStore c success.2) ∧
      π.Decode m M' = some (P.outputProjection (P.finalStore c success.2)) ∧
      P.denotation ops η (P.successful_admInput ops η c success) =
        P.outputProjection (P.finalStore c success.2) := by
  obtain ⟨-, c, -, hR, complete, hd⟩ := terminal_adequacy ops hv η hrun
  let success : P.Successful ops η c := ⟨hR.reach, complete⟩
  refine ⟨c, success, fun ρ => ⟨P.successful_unique ops η c success ρ, ?_⟩, hd,
    P.successful_denotation ops η c success⟩
  rintro rfl
  exact P.successful_model ops η c success

/-- **Theorem 31.3 (b).** A `failed` run of a valid plan means no model exists.
    The failing occurrence and the memory are not compared (D5). -/
theorem failed_correct (hv : π.Valid) (η : P.Input) {o : OccRef P} {pc : Nat}
    {M' : Memory K σ} (hrun : π.runPlan ops (Start η) = .failed o pc M') :
    ¬ ∃ ρ, P.Models ops η ρ := by
  rcases runPlan_R ops hv η with ⟨_, _, h, -⟩ | ⟨o', _, _, c', _, _, hex⟩
  · rw [hrun] at h
    cases h
  · exact P.failed_no_model ops η o'.1 o'.2 c' (hex.reaches P ops)

/-- **Theorem 31.3 (c), error-free profile.** A valid plan's run is never
    `stuck`: it is `done` at `m = commands.length` or `failed`. -/
theorem done_or_failed (hv : π.Valid) (η : P.Input) :
    (∃ M', π.runPlan ops (Start η) = .done π.commands.length M') ∨
      ∃ o pc M', π.runPlan ops (Start η) = .failed o pc M' := by
  rcases runPlan_R ops hv η with ⟨M', _, h, -⟩ | ⟨o, pc, M', _, _, h, -⟩
  · exact Or.inl ⟨M', h⟩
  · exact Or.inr ⟨o, pc, M', h⟩

/-- **Theorem 31.3 (c), converse.** If a model exists, a valid plan's run is
    `done` and decodes to that model's output projection. -/
theorem done_of_model (hv : π.Valid) (η : P.Input) {ρ : Store K σ}
    (hρ : P.Models ops η ρ) :
    ∃ M', π.runPlan ops (Start η) = .done π.commands.length M' ∧
      π.Decode π.commands.length M' = some (P.outputProjection ρ) := by
  rcases done_or_failed ops hv η with ⟨M', h⟩ | ⟨_, _, _, h⟩
  · obtain ⟨c, success, hmod, hd, -⟩ := done_correct ops hv η h
    rw [(hmod ρ).mp hρ]
    exact ⟨M', h, hd⟩
  · exact absurd ⟨ρ, hρ⟩ (failed_correct ops hv η h)

/-- (b) + (c): a valid plan's run is `done` iff a model exists. -/
theorem done_iff_model (hv : π.Valid) (η : P.Input) :
    (∃ m M', π.runPlan ops (Start η) = .done m M') ↔ ∃ ρ, P.Models ops η ρ := by
  constructor
  · rintro ⟨m, M', h⟩
    obtain ⟨c, success, hmod, -⟩ := done_correct ops hv η h
    exact ⟨_, (hmod _).mpr rfl⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨M', h, -⟩ := done_of_model ops hv η hρ
    exact ⟨_, M', h⟩

#print axioms Valid.order4
#print axioms cov1_of_cov2_pubOrder
#print axioms complete_of_refState
#print axioms terminal_adequacy
#print axioms done_correct
#print axioms failed_correct
#print axioms done_or_failed
#print axioms done_of_model
#print axioms done_iff_model

end LeanNCD.Semantics.Program.Plan
