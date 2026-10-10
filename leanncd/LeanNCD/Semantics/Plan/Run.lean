import LeanNCD.Semantics.Plan.Validity

/- Progress and the multi-step run lemma for valid plans (slice 1).
   `step_not_stuck`: a valid plan is never stuck at a related state.
   `run_R`: a run from a related state ends `done` at pc = m with R and a
   matching reference execution, or `failed` with a matching reference
   execution to a failed state; never `stuck`. -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r} {π : P.Plan}
variable [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))

/-! ### Progress -/

omit [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
/-- A group whose every footprint is readable never reports `stuck` in its scan. -/
theorem scanGroup_ne_stuck {p : PartialStore K σ} {G : List (OccRef P)}
    (ready : ∀ x ∈ G, checkReads p (footprint (P.body x.1 x.2.1) x.2.2) = true) :
    scanGroup ops p G ≠ some .stuck := by
  induction G with
  | nil => simp [scanGroup]
  | cons x G ih =>
    unfold scanGroup
    split
    · rename_i hn
      simp [evalReady, ready x List.mem_cons_self] at hn
    · simp
    · exact ih (fun y hy => ready y (List.mem_cons_of_mem _ hy))

/-- The commit phase succeeds when every destination slot is initialised. -/
theorem foldlM_addAt_some (v : Values P) : ∀ (G : List (OccRef P)) (M : Memory K σ),
    (∀ x ∈ G, (M (place x.dest)).isSome = true) → ∃ M', G.foldlM (addAt v) M = some M'
  | [], M, _ => ⟨M, rfl⟩
  | x :: G, M, h => by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    have step : addAt v M x = some (Function.update M (place x.dest) (some (addVal x a (v x)))) := by
      simp [addAt, ha]
    rw [List.foldlM_cons, step]
    refine foldlM_addAt_some v G _ (fun y hy => ?_)
    by_cases e : place y.dest = place x.dest
    · rw [e, Function.update_self]
      rfl
    · rw [Function.update_of_ne e]
      exact h y (List.mem_cons_of_mem _ hy)

variable {η : P.Input} {pc : Nat} {M : Memory K σ} {c : P.Running}

/-- Under R, a published address's slot is readable through the read view. -/
theorem readPub_isSome (hR : π.R ops η pc M c) {a : Address σ} (ha : π.Pub pc a) :
    (π.readPub pc M a).isSome = true := by
  simp only [readPub, if_pos ha]
  rw [hR.pubSlot a (slotView_pub π |>.mpr ha)]
  exact (hR.published a).mpr ha

/-- Under R, a materialised unpublished address has an initialised slot. -/
theorem acc_slot_isSome (hR : π.R ops η pc M c) {x : DefAddr P} (hm : π.Mat pc x)
    (hp : ¬ π.Pub pc x.addr) : (M (place x.addr)).isSome = true := by
  rw [hR.accSlot x (slotView_acc π |>.mpr ⟨hm, hp⟩)]
  rfl

/-- **Progress.** A valid plan at a related state, with a command left, is not
    stuck. Uses Singleton, AccOK (destinations in Mat, members unconsumed),
    ReadyOK (condition 3) and PubOK (unpublished, Mat). No `refState` hypothesis
    is needed: R alone suffices. -/
theorem step_not_stuck (hv : π.Valid) (hR : π.R ops η pc M c)
    (hpc : pc < π.commands.length) : π.stepPlan ops pc M ≠ .stuck := by
  obtain ⟨a, ha⟩ := hv.singleton _ (List.getElem_mem hpc)
  have hcmd : π.commands[pc]? = some [a] := by
    rw [List.getElem?_eq_getElem hpc, ha]
  unfold stepPlan
  rw [hcmd]
  cases a with
  | initZero S => simp [stepCommand, execAnn]
  | pub B =>
    obtain ⟨-, hB⟩ := hv.pubOK pc B hcmd
    simp only [stepCommand, execAnn, execPub]
    rw [if_pos]
    · simp
    · simp only [List.all_eq_true]
      intro x hx
      exact acc_slot_isSome ops hR (hB x hx).2.1 (hB x hx).1
  | acc G =>
    obtain ⟨-, hG⟩ := hv.accOK pc G hcmd
    have hready := hv.ready pc G hcmd
    simp only [stepCommand, execAnn, execAcc]
    split
    · rename_i res hres
      intro e
      subst e
      exact scanGroup_ne_stuck ops (fun x hx => (checkReads_iff _ _).mpr
        (fun a ha => readPub_isSome ops hR (hready x hx a ha))) hres
    · obtain ⟨M', hM'⟩ := foldlM_addAt_some (valuesOn ops (π.readPub pc M)) G M
        (fun x hx => acc_slot_isSome ops hR (hG x hx).2 (π.dest_not_pub ops hR (hG x hx).1))
      rw [hM']
      simp

/-! ### The multi-step run lemma -/

/-- **Run lemma.** From a related state at `pc` (with `c = refState pc`), the
    remaining run of a valid plan either finishes at `m = commands.length` with R
    and a reference execution `c →* c'` (`c' = refState m`), or fails on an
    occurrence `o` with a reference execution from `c` to `.failed o c''`.
    It is never stuck (no third disjunct). -/
theorem run_R (hv : π.Valid) :
    ∀ (l : List (Command P)) (pc : Nat) (M : Memory K σ) (c : P.Running),
      π.commands.drop pc = l → pc ≤ π.commands.length →
      π.R ops η pc M c → π.refState ops η pc = some c →
      (∃ M' c', π.runFrom ops pc M l = .done π.commands.length M' ∧
          π.refState ops η π.commands.length = some c' ∧ π.R ops η π.commands.length M' c' ∧
          ∃ events, Execution P ops events (.running c) (.running c')) ∨
      (∃ o pc' M' c' events, π.runFrom ops pc M l = .failed o pc' M' ∧
          Execution P ops events (.running c) (.failed o.1 o.2 c'))
  | [], pc, M, c, hl, hle, hR, hc => by
    have hpc : pc = π.commands.length :=
      le_antisymm hle (List.drop_eq_nil_iff.mp hl)
    subst hpc
    exact Or.inl ⟨M, c, rfl, hc, hR, [], .nil _⟩
  | cmd :: rest, pc, M, c, hl, _, hR, hc => by
    have hcmd : π.commands[pc]? = some cmd := by
      rw [← List.head?_drop, hl]
      rfl
    have hlt : pc < π.commands.length := (List.getElem?_eq_some_iff.mp hcmd).1
    obtain ⟨a, rfl⟩ := hv.singleton _ (List.mem_of_getElem? hcmd)
    have hrest : π.commands.drop (pc + 1) = rest := by
      rw [← List.tail_drop, hl]
      rfl
    have hstep : π.stepCommand ops pc M [a] = π.stepPlan ops pc M := by
      simp [stepPlan, hcmd]
    cases hs : π.stepPlan ops pc M with
    | ok M' =>
      obtain ⟨c', hc', hR', ev, hex⟩ := step_R ops hR hc hcmd (hv.stepOK pc a hcmd) hs
      have ih := run_R hv rest (pc + 1) M' c' hrest hlt hR' hc'
      simp only [runFrom, hstep, hs]
      rcases ih with ⟨M'', c'', hrun, hcm, hRm, ev', hex'⟩ | ⟨o, pc', M'', c'', ev', hrun, hex'⟩
      · exact Or.inl ⟨M'', c'', hrun, hcm, hRm, ev ++ ev', hex.append hex'⟩
      · exact Or.inr ⟨o, pc', M'', c'', ev ++ ev', hrun, hex.append hex'⟩
    | semFail o =>
      have hex := step_failed ops hR hcmd
        (fun G hG x hx => by
          cases hG
          exact ((hv.accOK pc G hcmd).2 x hx).1) hs
      simp only [runFrom, hstep, hs]
      exact Or.inr ⟨o, pc, M, c, _, rfl, hex⟩
    | stuck => exact absurd hs (step_not_stuck ops hv hR hlt)

/-- `run_R` from `Start`: a valid plan's `runPlan` either completes with R at
    `m` and a reference execution from the initial state, or fails with a
    matching reference failure. -/
theorem runPlan_R (hv : π.Valid) (η : P.Input) :
    (∃ M' c', π.runPlan ops (Start η) = .done π.commands.length M' ∧
        π.refState ops η π.commands.length = some c' ∧ π.R ops η π.commands.length M' c' ∧
        ∃ events, Execution P ops events (.running (P.initial η)) (.running c')) ∨
    (∃ o pc' M' c' events, π.runPlan ops (Start η) = .failed o pc' M' ∧
        Execution P ops events (.running (P.initial η)) (.failed o.1 o.2 c')) :=
  run_R ops hv π.commands 0 (Start η) (P.initial η) (List.drop_zero) (Nat.zero_le _)
    (π.R_start ops η) (by simp [refState, prefixAnn_zero])

/-- A valid plan's run from `Start` is never stuck. -/
theorem runPlan_not_stuck (hv : π.Valid) (η : P.Input) (pc : Nat) (M : Memory K σ) :
    π.runPlan ops (Start η) ≠ .stuck pc M := by
  rcases runPlan_R ops hv η with ⟨_, _, h, -⟩ | ⟨_, _, _, _, _, h, -⟩ <;> rw [h] <;> simp

#print axioms step_not_stuck
#print axioms run_R
#print axioms runPlan_R
#print axioms runPlan_not_stuck

end LeanNCD.Semantics.Program.Plan
