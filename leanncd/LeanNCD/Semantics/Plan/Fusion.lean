import LeanNCD.Semantics.Plan.Run

/- PROTOTYPE (slice 2, P1): fused commands by expansion.
   A fused command `[a₁, …, aₖ]` is the sequential composition of its annotations
   (spec 29.1). Its schedule is the plan's expansion `π.expand` (spec 29.3 "Expand
   fused annotations in their stated order"), whose every command is a singleton, so
   every slice-1 lemma applies to `π.expand` verbatim. A fused command executes by
   folding `execAnn` over its annotations at expanded positions `offset pc + j`
   on the RUNNING memory; a failure (or stuck) anywhere reports the PRE-command
   memory (`runFrom` already does), i.e. fusion is transactional per command.
   R is claimed only at command boundaries. -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r} (π : P.Plan)

theorem expand_singleton : π.expand.Singleton := by
  intro cmd hcmd
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hcmd
  exact ⟨a, rfl⟩

/-! ### Belongs in Simulation.lean -/

variable [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))
variable {η : P.Input}

/-- Fold of `step_R` over a list of annotations of a (singleton-command) plan `π'`. -/
theorem execAnns_R (π' : P.Plan) :
    ∀ (anns : List (Ann P)) (n : Nat) (M M' : Memory K σ) (c : P.Running),
      π'.R ops η n M c → π'.refState ops η n = some c →
      (∀ j a, anns[j]? = some a → π'.commands[n + j]? = some [a] ∧ π'.AnnOK (n + j) a) →
      π'.execAnns ops n M anns = .ok M' →
      ∃ c', π'.refState ops η (n + anns.length) = some c' ∧ π'.R ops η (n + anns.length) M' c' ∧
        ∃ events, Execution P ops events (.running c) (.running c')
  | [], n, M, M', c, hR, hc, _, h => by
    simp only [execAnns, StepResult.ok.injEq] at h
    subst h
    exact ⟨c, by simpa using hc, by simpa using hR, [], .nil _⟩
  | a :: as, n, M, M', c, hR, hc, hok, h => by
    obtain ⟨h0, hok0⟩ := hok 0 a rfl
    have hn : n + 0 = n := rfl
    rw [hn] at h0 hok0
    simp only [execAnns] at h
    cases hs : π'.execAnn ops n M a with
    | ok M₁ =>
      rw [hs] at h
      have hstep : π'.stepPlan ops n M = .ok M₁ := by
        simp [stepPlan, h0, stepCommand_single, hs]
      obtain ⟨c₁, hc₁, hR₁, ev, hex⟩ := step_R ops hR hc h0 hok0 hstep
      obtain ⟨c', hc', hR', ev', hex'⟩ := execAnns_R π' as n.succ M₁ M' c₁ hR₁ hc₁
        (fun j b hb => by
          have := hok (j + 1) b (by simpa using hb)
          rwa [show n + (j + 1) = n.succ + j by omega] at this) h
      have hl : n + (a :: as).length = n.succ + as.length := by simp; omega
      rw [hl]
      exact ⟨c', hc', hR', ev ++ ev', hex.append hex'⟩
    | semFail o => rw [hs] at h; cases h
    | stuck => rw [hs] at h; cases h

/-- Fold of `step_failed`: a semantic failure inside a fused command is matched by the
    reference execution of the EARLIER annotations of the command followed by the
    failing contribution. -/
theorem execAnns_failed (π' : P.Plan) :
    ∀ (anns : List (Ann P)) (n : Nat) (M : Memory K σ) (c : P.Running) (o : OccRef P),
      π'.R ops η n M c → π'.refState ops η n = some c →
      (∀ j a, anns[j]? = some a → π'.commands[n + j]? = some [a] ∧ π'.AnnOK (n + j) a) →
      π'.execAnns ops n M anns = .semFail o →
      ∃ c' events, Execution P ops events (.running c) (.failed o.1 o.2 c')
  | [], n, M, c, o, _, _, _, h => by simp [execAnns] at h
  | a :: as, n, M, c, o, hR, hc, hok, h => by
    obtain ⟨h0, hok0⟩ := hok 0 a rfl
    have hn : n + 0 = n := rfl
    rw [hn] at h0 hok0
    simp only [execAnns] at h
    cases hs : π'.execAnn ops n M a with
    | ok M₁ =>
      rw [hs] at h
      have hstep : π'.stepPlan ops n M = .ok M₁ := by
        simp [stepPlan, h0, stepCommand_single, hs]
      obtain ⟨c₁, hc₁, hR₁, ev, hex⟩ := step_R ops hR hc h0 hok0 hstep
      obtain ⟨c', ev', hex'⟩ := execAnns_failed π' as n.succ M₁ c₁ o hR₁ hc₁
        (fun j b hb => by
          have := hok (j + 1) b (by simpa using hb)
          rwa [show n + (j + 1) = n.succ + j by omega] at this) h
      exact ⟨c', ev ++ ev', hex.append hex'⟩
    | semFail o' =>
      rw [hs] at h
      cases h
      have hstep : π'.stepPlan ops n M = .semFail o := by
        simp [stepPlan, h0, stepCommand_single, hs]
      exact ⟨c, _, step_failed ops hR h0
        (fun G hG x hx => by
          cases hG
          exact ((show π'.AccOK n G from hok0).2 x hx).1) hstep⟩
    | stuck => rw [hs] at h; cases h

/-- Transport of R between plans along equal annotation prefixes. -/
theorem R_transport {π π' : P.Plan} {pc pc' : Nat} {M : Memory K σ} {c : P.Running}
    (h : π.prefixAnn pc = π'.prefixAnn pc') (hR : π.R ops η pc M c) : π'.R ops η pc' M c := by
  have hcons : ∀ x, π.Cons pc x ↔ π'.Cons pc' x := fun x => by simp [Cons, consList, h]
  have hpub : ∀ a, π.Pub pc a ↔ π'.Pub pc' a := fun a => by simp [Pub, pubList, h]
  have hmat : ∀ x, π.Mat pc x ↔ π'.Mat pc' x := fun x => by simp [Mat, matList, h]
  have hsv : ∀ r, π.SlotView pc r = π'.SlotView pc' r := by
    intro r; cases r <;> simp [SlotView, hpub, hmat]
  exact ⟨hR.reach, fun t o => by rw [← hcons]; exact hR.pending t o,
    fun a => by rw [← hpub]; exact hR.published a,
    fun a ha => hR.pubSlot a (by rw [hsv]; exact ha),
    fun x hx => hR.accSlot x (by rw [hsv]; exact hx),
    fun x hx ho => (hmat x).mp (hR.retain x (fun hp => hx ((hpub _).mp hp))
      (by obtain ⟨o, ho1, ho2⟩ := ho; exact ⟨o, (hcons _).mpr ho1, ho2⟩))⟩

theorem refState_prefix_congr {π π' : P.Plan} {pc pc' : Nat}
    (h : π.prefixAnn pc = π'.prefixAnn pc') : π.refState ops η pc = π'.refState ops η pc' := by
  simp only [refState, h]

/-- **Step simulation for a fused command** (iii): R at command boundaries only. -/
theorem step_R_command {pc : Nat} {cmd : Command P} {M M' : Memory K σ} {c : P.Running}
    (hR : π.R ops η pc M c) (hc : π.refState ops η pc = some c)
    (hcmd : π.commands[pc]? = some cmd)
    (ok : ∀ j a, cmd[j]? = some a → π.expand.AnnOK (π.offset pc + j) a)
    (h : π.stepCommand ops pc M cmd = .ok M') :
    ∃ c', π.refState ops η (pc + 1) = some c' ∧ π.R ops η (pc + 1) M' c' ∧
      ∃ events, Execution P ops events (.running c) (.running c') := by
  have hp := π.prefixAnn_eq_expand pc
  have hp' : π.prefixAnn (pc + 1) = π.expand.prefixAnn (π.offset pc + cmd.length) := by
    rw [π.prefixAnn_succ hcmd, expand_prefixAnn, ann_eq_append π pc, drop_flatten π hcmd,
      ← List.append_assoc, List.take_left' (by simp [offset])]
  obtain ⟨c', hc', hR', ev, hex⟩ := execAnns_R ops π.expand cmd (π.offset pc) M M' c
    (R_transport ops hp hR) ((refState_prefix_congr (η := η) ops hp).symm.trans hc)
    (fun j a hj => ⟨π.expand_commands_getElem? (π.ann_getElem?_offset hcmd hj),
      ok j a hj⟩) h
  exact ⟨c', (refState_prefix_congr (η := η) ops hp').trans hc',
    R_transport ops hp'.symm hR', ev, hex⟩

/-- Failure inside a fused command (d): the reference runs the earlier annotations of the
    command and then fails on `o`; the plan reports the pre-command memory. -/
theorem step_failed_command {pc : Nat} {cmd : Command P} {M : Memory K σ} {c : P.Running}
    {o : OccRef P}
    (hR : π.R ops η pc M c) (hc : π.refState ops η pc = some c)
    (hcmd : π.commands[pc]? = some cmd)
    (ok : ∀ j a, cmd[j]? = some a → π.expand.AnnOK (π.offset pc + j) a)
    (h : π.stepCommand ops pc M cmd = .semFail o) :
    ∃ c' events, Execution P ops events (.running c) (.failed o.1 o.2 c') := by
  have hp := π.prefixAnn_eq_expand pc
  exact execAnns_failed ops π.expand cmd (π.offset pc) M c o
    (R_transport ops hp hR) ((refState_prefix_congr (η := η) ops hp).symm.trans hc)
    (fun j a hj => ⟨π.expand_commands_getElem? (π.ann_getElem?_offset hcmd hj),
      ok j a hj⟩) h

/-- **Progress for a fused command**: on a plan whose expansion is valid, a related state at
    command `pc` never gets stuck on that command. -/
theorem stepCommand_not_stuck {pc : Nat} {cmd : Command P} {M : Memory K σ} {c : P.Running}
    (hv : π.expand.Valid) (hR : π.R ops η pc M c) (hc : π.refState ops η pc = some c)
    (hcmd : π.commands[pc]? = some cmd) : π.stepCommand ops pc M cmd ≠ .stuck := by
  have hp := π.prefixAnn_eq_expand pc
  exact execAnns_not_stuck ops hv cmd (π.offset pc) M c
    (R_transport ops hp hR) ((refState_prefix_congr (η := η) ops hp).symm.trans hc)
    (fun j a hj => π.expand_commands_getElem? (π.ann_getElem?_offset hcmd hj))

/-! ### Run bridge (T3): a fused run and the run of its expansion agree -/

/-- Two outcomes agree up to the stopping pc and the memory of a stopped run: `done` on the
    same final memory, `failed` on the same occurrence, or both `stuck`. -/
def PlanOutcome.Agree : PlanOutcome P → PlanOutcome P → Prop
  | .done _ M, .done _ M' => M = M'
  | .failed o _ _, .failed o' _ _ => o = o'
  | .stuck _ _, .stuck _ _ => True
  | _, _ => False

/-- A `done` run stops at the start position plus the number of commands consumed. -/
theorem runFrom_done_pc (π' : P.Plan) : ∀ (l : List (Command P)) (pc : Nat) (M M' : Memory K σ)
    (m : Nat), π'.runFrom ops pc M l = .done m M' → m = pc + l.length
  | [], pc, M, M', m, h => by
    have h' : PlanOutcome.done pc M = .done m M' := h
    have := (PlanOutcome.done.inj h').1
    simp; omega
  | cmd :: rest, pc, M, M', m, h => by
    simp only [runFrom] at h
    cases hs : π'.stepCommand ops pc M cmd with
    | ok M₁ =>
      rw [hs] at h
      have := runFrom_done_pc π' rest (pc + 1) M₁ M' m h
      simp; omega
    | semFail o => rw [hs] at h; cases h
    | stuck => rw [hs] at h; cases h

/-- Running singleton commands built from `anns` is `execAnns` of `anns`, then the rest. -/
theorem runFrom_append_anns (π' : P.Plan) : ∀ (anns : List (Ann P)) (n : Nat) (M : Memory K σ)
    (ys : List (Command P)),
    match π'.execAnns ops n M anns with
    | .ok M' => π'.runFrom ops n M (anns.map (fun a => [a]) ++ ys) =
        π'.runFrom ops (n + anns.length) M' ys
    | .semFail o => ∃ pc M', π'.runFrom ops n M (anns.map (fun a => [a]) ++ ys) = .failed o pc M'
    | .stuck => ∃ pc M', π'.runFrom ops n M (anns.map (fun a => [a]) ++ ys) = .stuck pc M'
  | [], n, M, ys => by simp [execAnns]
  | a :: as, n, M, ys => by
    have key := stepCommand_single π' ops n M a
    have e : n + (a :: as).length = n.succ + as.length := by simp; omega
    cases hs : π'.execAnn ops n M a with
    | ok M₁ =>
      have ih := runFrom_append_anns π' as n.succ M₁ ys
      simp only [execAnns, hs, List.map_cons, List.cons_append, runFrom, key, e]
      cases he : π'.execAnns ops n.succ M₁ as <;> rw [he] at ih <;> exact ih
    | semFail o => simp [execAnns, hs, runFrom, key]
    | stuck => simp [execAnns, hs, runFrom, key]

/-- **Run bridge.** From any command boundary `pc`, the fused run of the remaining commands and
    the run of their expansion (from the expanded position `offset pc`) agree: same final memory
    when done, same failing occurrence when failed. -/
theorem runFrom_agree : ∀ (l : List (Command P)) (pc : Nat) (M : Memory K σ),
    π.commands.drop pc = l →
    (π.runFrom ops pc M l).Agree
      (π.expand.runFrom ops (π.offset pc) M (l.flatten.map fun a => [a]))
  | [], pc, M, _ => by simp [runFrom, PlanOutcome.Agree]
  | cmd :: rest, pc, M, hl => by
    have hcmd : π.commands[pc]? = some cmd := by rw [← List.head?_drop, hl]; rfl
    have hrest : π.commands.drop (pc + 1) = rest := by rw [← List.tail_drop, hl]; rfl
    have hoff : π.offset (pc + 1) = π.offset pc + cmd.length := by
      simp [offset, prefixAnn_succ π hcmd]
    have ha := runFrom_append_anns ops π.expand cmd (π.offset pc) M
      (rest.flatten.map fun a => [a])
    have hfl : (cmd :: rest).flatten.map (fun a => [a]) =
        cmd.map (fun a => [a]) ++ rest.flatten.map (fun a => [a]) := by simp
    rw [hfl]
    simp only [runFrom]
    have hstep : π.stepCommand ops pc M cmd = π.expand.execAnns ops (π.offset pc) M cmd := rfl
    rw [hstep]
    cases he : π.expand.execAnns ops (π.offset pc) M cmd with
    | ok M' =>
      rw [he] at ha
      rw [ha, ← hoff]
      exact runFrom_agree rest (pc + 1) M' hrest
    | semFail o =>
      rw [he] at ha
      obtain ⟨pc', M'', h⟩ := ha
      rw [h]
      exact rfl
    | stuck =>
      rw [he] at ha
      obtain ⟨pc', M'', h⟩ := ha
      rw [h]
      exact True.intro

/-- `runFrom_agree` from the start: a fused plan's run and its expansion's agree. -/
theorem runPlan_agree (M : Memory K σ) :
    (π.runPlan ops M).Agree (π.expand.runPlan ops M) := by
  have h := runFrom_agree π ops π.commands 0 M List.drop_zero
  have e0 : π.offset 0 = 0 := by simp [offset, prefixAnn_zero]
  rw [e0] at h
  exact h

end LeanNCD.Semantics.Program.Plan
