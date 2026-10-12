import LeanNCD.Semantics.Plan.Validity

/- Progress and the multi-step run lemma for valid singleton plans with typed allocations.
   `step_not_stuck`: a valid plan is never stuck at a related state.
   `run_R`: a run from a related state ends `done` at pc = m with R and a
   matching reference execution, or `failed` with a matching reference
   execution to a failed state; never `stuck`. Preservation uses the validity
   clause for layouts on both sides of each annotation. -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r} {π : P.Plan}
variable [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))

/-! ### Progress -/

omit [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
/-- A group whose every footprint is readable never reports `stuck` in its scan. -/
theorem scanGroup_ne_stuck (A : Allocation P) {p : PartialStore K σ} {G : List (OccRef P)}
    (ready : ∀ x ∈ G, checkReads p (footprint (P.body x.1 x.2.1) x.2.2) = true) :
    scanGroup ops A p G ≠ some .stuck := by
  induction G with
  | nil => simp [scanGroup]
  | cons x G ih =>
    unfold scanGroup
    split
    · rename_i hn
      simp [evalReady, ready x List.mem_cons_self] at hn
    · simp
    · exact ih (fun y hy => ready y (List.mem_cons_of_mem _ hy))

omit [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem cast_option_isSome {s t : S} (h : s = t) (v : Option (K s)) :
    (cast (congrArg (fun s => Option (K s)) h) v).isSome = v.isSome := by
  cases h
  rfl

omit [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem readSlot_isSome (A : Allocation P) (M : Memory K A) (a : Address σ) :
    (readSlot A M a).isSome = (M (place A a)).isSome := by
  rw [readSlot_eq_cast]
  exact cast_option_isSome (place_sort A a) _

/-- The commit phase succeeds when every destination slot is initialised. -/
theorem foldlM_addAt_some (v : Values P) :
    ∀ (G : List (OccRef P)) (M : Memory K π.allocation),
    (∀ x ∈ G, (readSlot π.allocation M x.dest).isSome = true) →
      ∃ M', G.foldlM (π.addAt v) M = some M'
  | [], M, _ => ⟨M, rfl⟩
  | x :: G, M, h => by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    have step : π.addAt v M x = some (π.writeDef M x.target (addVal x a (v x))) := by
      simp [addAt, ha]
    rw [List.foldlM_cons, step]
    refine foldlM_addAt_some v G _ (fun y hy => ?_)
    by_cases e : place π.allocation y.dest = place π.allocation x.dest
    · rw [readSlot_isSome, e]
      simp only [writeDef, OccRef.target_addr, Function.update_self]
      exact cast_option_isSome (place_sort π.allocation x.target.addr).symm _
    · rw [readSlot_isSome, π.writeDef_ne _ _ _ (Ne.symm e), ← readSlot_isSome]
      exact h y (List.mem_cons_of_mem _ hy)

variable {η : P.Input} {pc : Nat} {M : Memory K π.allocation} {c : P.Running}

/-- Under R, a live address's slot is readable through the read view. -/
theorem readPub_isSome (hR : π.R ops η pc M c) {a : Address σ} (ha : π.Live pc a) :
    (π.readPub pc M a).isSome = true := by
  simp only [readPub, if_pos ha]
  rw [hR.pubSlot a (slotView_pub π |>.mpr ha)]
  exact (hR.published a).mpr ha.pub

/-- Under R, a materialised unpublished address has an initialised slot. -/
theorem acc_slot_isSome (hR : π.R ops η pc M c) {x : DefAddr P} (hm : π.Mat pc x)
    (hp : ¬ π.Pub pc x.addr) :
    (readSlot π.allocation M x.addr).isSome = true := by
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
  | initZero S => simp [stepCommand_single, execAnn]
  | retire B => simp [stepCommand_single, execAnn]
  | pub B =>
    obtain ⟨-, hB⟩ := hv.pubOK pc B hcmd
    simp only [stepCommand_single, execAnn, execPub]
    rw [if_pos]
    · simp
    · simp only [List.all_eq_true]
      intro x hx
      exact acc_slot_isSome ops hR (hB x hx).2.1 (hB x hx).1
  | acc G =>
    obtain ⟨-, hG⟩ := hv.accOK pc G hcmd
    have hready := hv.ready pc G hcmd
    simp only [stepCommand_single, execAnn, execAcc]
    split
    · rename_i res hres
      intro e
      subst e
      exact scanGroup_ne_stuck ops π.allocation (fun x hx => (checkReads_iff _ _).mpr
        (fun a ha => readPub_isSome ops hR (hready x hx a ha))) hres
    · obtain ⟨M', hM'⟩ := foldlM_addAt_some (valuesOn ops (π.readPub pc M)) G M
        (fun x hx => acc_slot_isSome ops hR (hG x hx).2 (π.dest_not_pub ops hR (hG x hx).1))
      rw [hM']
      simp

/-- **Progress for a run of annotations.** On a valid (singleton) plan, folding `execAnn`
    over annotations scheduled at consecutive positions `n, n+1, …` from a related state is
    never stuck: each step is `step_not_stuck`, and a successful step re-establishes R
    (`step_R`). Used on `π.expand` for a fused command. -/
theorem execAnns_not_stuck (hv : π.Valid) :
    ∀ (anns : List (Ann P)) (n : Nat) (M : Memory K π.allocation) (c : P.Running),
      π.R ops η n M c → π.refState ops η n = some c →
      (∀ j a, anns[j]? = some a → π.commands[n + j]? = some [a]) →
      π.execAnns ops n M anns ≠ .stuck
  | [], n, M, c, _, _, _ => by simp [execAnns]
  | a :: as, n, M, c, hR, hc, hcmds => by
    have h0 : π.commands[n]? = some [a] := hcmds 0 a rfl
    have hlt : n < π.commands.length := (List.getElem?_eq_some_iff.mp h0).1
    have hstep : π.stepPlan ops n M = π.execAnn ops n M a := by
      simp [stepPlan, h0, stepCommand_single]
    have hns := step_not_stuck ops hv hR hlt
    rw [hstep] at hns
    simp only [execAnns]
    cases hs : π.execAnn ops n M a with
    | ok M₁ =>
      rw [hs] at hns
      have hs' : π.stepPlan ops n M = .ok M₁ := by rw [hstep, hs]
      obtain ⟨layout, layout'⟩ := hv.layout_boundary h0
      obtain ⟨c₁, hc₁, hR₁, -⟩ :=
        step_R ops hR hc h0 (hv.stepOK n a h0) layout layout' hs'
      exact execAnns_not_stuck hv as n.succ M₁ c₁ hR₁ hc₁ (fun j b hb => by
        have := hcmds (j + 1) b (by simpa using hb)
        rwa [show n + (j + 1) = n.succ + j by omega] at this)
    | semFail o => simp
    | stuck => rw [hs] at hns; exact absurd rfl hns

/-! ### The multi-step run lemma -/

/-- **Run lemma.** From a related state at `pc` (with `c = refState pc`), the
    remaining run of a valid plan either finishes at `m = commands.length` with R
    and a reference execution `c →* c'` (`c' = refState m`), or fails on an
    occurrence `o` with a reference execution from `c` to `.failed o c''`.
    It is never stuck (no third disjunct). -/
theorem run_R (hv : π.Valid) :
    ∀ (l : List (Command P)) (pc : Nat) (M : Memory K π.allocation) (c : P.Running),
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
      obtain ⟨layout, layout'⟩ := hv.layout_boundary hcmd
      obtain ⟨c', hc', hR', ev, hex⟩ :=
        step_R ops hR hc hcmd (hv.stepOK pc a hcmd) layout layout' hs
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
    (∃ M' c', π.runPlan ops (π.Start η) = .done π.commands.length M' ∧
        π.refState ops η π.commands.length = some c' ∧ π.R ops η π.commands.length M' c' ∧
        ∃ events, Execution P ops events (.running (P.initial η)) (.running c')) ∨
    (∃ o pc' M' c' events, π.runPlan ops (π.Start η) = .failed o pc' M' ∧
        Execution P ops events (.running (P.initial η)) (.failed o.1 o.2 c')) :=
  run_R ops hv π.commands 0 (π.Start η) (P.initial η) (List.drop_zero) (Nat.zero_le _)
    (π.R_start ops η) (by simp [refState, prefixAnn_zero])

/-- A valid plan's run from `Start` is never stuck. -/
theorem runPlan_not_stuck (hv : π.Valid) (η : P.Input) (pc : Nat)
    (M : Memory K π.allocation) : π.runPlan ops (π.Start η) ≠ .stuck pc M := by
  rcases runPlan_R ops hv η with ⟨_, _, h, -⟩ | ⟨_, _, _, _, _, h, -⟩ <;> rw [h] <;> simp

#print axioms step_not_stuck
#print axioms scanGroup_ne_stuck
#print axioms cast_option_isSome
#print axioms readSlot_isSome
#print axioms foldlM_addAt_some
#print axioms readPub_isSome
#print axioms acc_slot_isSome
#print axioms execAnns_not_stuck
#print axioms run_R
#print axioms runPlan_R
#print axioms runPlan_not_stuck

end LeanNCD.Semantics.Program.Plan
