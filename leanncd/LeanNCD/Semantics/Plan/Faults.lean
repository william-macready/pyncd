import LeanNCD.Semantics.Plan.FusionCorrectness

/- Implementation errors (spec Section 31.3, D7), as a wrapper over the unchanged run.
   A fault oracle `Faults` says, for each EXPANDED annotation position, whether the
   environment fails there (allocation failure, kernel fault). `runFromE` consults it
   for the positions a command occupies BEFORE the command runs, so a fault pre-empts a
   semantic failure at the same step and reports the PRE-command memory (transactional,
   as F4). With no fault it takes exactly the step `runFrom` takes. The kernels,
   `StepResult` and `PlanOutcome` are untouched, so every earlier theorem is the
   fault-free special case; `stuck` stays a plan defect, separate from `error`. -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r} (π : P.Plan)
variable [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))

/-- Kinds of implementation error: resource exhaustion and hardware or kernel faults.
    None of them says anything about whether a model exists. -/
inductive ImplErr
  | allocFail
  | kernelFault
  deriving DecidableEq, Repr

/-- A fault schedule: the fault, if any, striking at each expanded annotation position. -/
abbrev Faults := Nat → Option ImplErr

/-- The first fault among the `k` positions `n, n+1, …, n+k-1`. -/
def faultIn (faults : Faults) (n k : Nat) : Option ImplErr :=
  (List.range k).findSome? (fun j => faults (n + j))

theorem faultIn_eq_some {faults : Faults} {n k : Nat} {e : ImplErr}
    (h : faultIn faults n k = some e) : ∃ j, j < k ∧ faults (n + j) = some e := by
  obtain ⟨j, hj, hf⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨j, List.mem_range.mp hj, hf⟩

theorem faultIn_none {faults : Faults} (h : ∀ n, faults n = none) (n k : Nat) :
    faultIn faults n k = none := by
  simp [faultIn, h]

theorem faultIn_isSome {faults : Faults} {n k j : Nat} {e : ImplErr} (hj : j < k)
    (hf : faults (n + j) = some e) : ∃ e', faultIn faults n k = some e' := by
  cases h : faultIn faults n k with
  | some e' => exact ⟨e', rfl⟩
  | none =>
    have := List.findSome?_eq_none_iff.mp h j (List.mem_range.mpr hj)
    rw [hf] at this
    cases this

/-- Outcome of a run under a fault schedule: an ordinary `PlanOutcome`, or an
    implementation error at command `pc` with the pre-command memory. -/
inductive FOutcome (P : Program K σ r)
  | run (o : PlanOutcome P)
  | error (e : ImplErr) (pc : Nat) (M : Memory K σ)

/-- `runFrom` under a fault schedule. -/
def runFromE (faults : Faults) (pc : Nat) (M : Memory K σ) : List (Command P) → FOutcome P
  | [] => .run (.done pc M)
  | cmd :: rest =>
    match faultIn faults (π.offset pc) cmd.length with
    | some e => .error e pc M
    | none =>
      match π.stepCommand ops pc M cmd with
      | .ok M' => runFromE faults (pc + 1) M' rest
      | .semFail o => .run (.failed o pc M)
      | .stuck => .run (.stuck pc M)

def runPlanE (faults : Faults) (M : Memory K σ) : FOutcome P :=
  π.runFromE ops faults 0 M π.commands

/-- The error-free profile (spec 31.3): the run is one in which no implementation error occurs. -/
def ErrorFreeRun (faults : Faults) (M : Memory K σ) : Prop :=
  ∃ o, π.runPlanE ops faults M = .run o

/-- A schedule with no fault at any expanded position of the plan (it may hold faults beyond). -/
def NoFaultsInPlan (faults : Faults) : Prop := ∀ n, n < π.ann.length → faults n = none

/-! ### A run under faults is the fault-free run, truncated -/

/-- No fault, no difference. -/
theorem runFromE_noFault {faults : Faults} (h : ∀ n, faults n = none) :
    ∀ (l : List (Command P)) (pc : Nat) (M : Memory K σ),
      π.runFromE ops faults pc M l = .run (π.runFrom ops pc M l)
  | [], pc, M => by simp [runFromE, runFrom]
  | cmd :: rest, pc, M => by
    simp only [runFromE, runFrom, faultIn_none h]
    cases π.stepCommand ops pc M cmd <;> simp [runFromE_noFault h rest]

/-- A non-error outcome under faults is the fault-free outcome. -/
theorem runFromE_run {faults : Faults} :
    ∀ (l : List (Command P)) (pc : Nat) (M : Memory K σ) (o : PlanOutcome P),
      π.runFromE ops faults pc M l = .run o → π.runFrom ops pc M l = o
  | [], pc, M, o, h => by
    simp only [runFromE, FOutcome.run.injEq] at h
    simp [runFrom, h]
  | cmd :: rest, pc, M, o, h => by
    simp only [runFromE] at h
    split at h
    · cases h
    · rename_i hf
      simp only [runFrom]
      cases hs : π.stepCommand ops pc M cmd with
      | ok M' =>
        rw [hs] at h
        exact runFromE_run rest (pc + 1) M' o h
      | semFail o' =>
        rw [hs] at h
        simp only [FOutcome.run.injEq] at h
        simp [h]
      | stuck =>
        rw [hs] at h
        simp only [FOutcome.run.injEq] at h
        simp [h]

/-- An error stops the run at a command boundary `pc' = pc + k` with a fault at one of
    that command's expanded positions; the reported memory is exactly the fault-free
    memory there (the run of the first `k` commands is `done`). -/
theorem runFromE_error {faults : Faults} :
    ∀ (l : List (Command P)) (pc : Nat) (M : Memory K σ) (e : ImplErr) (pc' : Nat)
      (M' : Memory K σ),
      π.runFromE ops faults pc M l = .error e pc' M' →
      ∃ k cmd, l[k]? = some cmd ∧ pc' = pc + k ∧
        π.runFrom ops pc M (l.take k) = .done pc' M' ∧
        ∃ j, j < cmd.length ∧ faults (π.offset pc' + j) = some e
  | [], pc, M, e, pc', M', h => by simp [runFromE] at h
  | cmd :: rest, pc, M, e, pc', M', h => by
    simp only [runFromE] at h
    split at h
    · rename_i e' hf
      simp only [FOutcome.error.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨0, cmd, rfl, rfl, by simp [runFrom], faultIn_eq_some hf⟩
    · cases hs : π.stepCommand ops pc M cmd with
      | ok M₁ =>
        rw [hs] at h
        obtain ⟨k, c, hc, hpc, hrun, hj⟩ := runFromE_error rest (pc + 1) M₁ e pc' M' h
        refine ⟨k + 1, c, by simpa using hc, by omega, ?_, hj⟩
        simp [runFrom, hs, hrun]
      | semFail o => rw [hs] at h; cases h
      | stuck => rw [hs] at h; cases h

/-! ### Theorem 31.3 (a), (b) under any fault schedule -/

variable {π}

/-- **31.3 (a) under faults.** A `done` run, whatever faults the schedule holds elsewhere,
    has exactly one model, the reference final store. -/
theorem done_correct_E (hv : π.Valid) (faults : Faults) (η : P.Input) {m : Nat}
    {M' : Memory K σ}
    (hrun : π.runPlanE ops faults (Start η) = .run (.done m M')) :
    ∃ c, ∃ success : P.Successful ops η c,
      (∀ ρ, P.Models ops η ρ ↔ ρ = P.finalStore c success.2) ∧
      π.Decode m M' = some (P.outputProjection (P.finalStore c success.2)) ∧
      P.denotation ops η (P.successful_admInput ops η c success) =
        P.outputProjection (P.finalStore c success.2) :=
  done_correct ops hv η (runFromE_run π ops _ _ _ _ hrun)

/-- **31.3 (b) under faults.** A `failed` run means no model exists. -/
theorem failed_correct_E (hv : π.Valid) (faults : Faults) (η : P.Input) {o : OccRef P}
    {pc : Nat} {M' : Memory K σ}
    (hrun : π.runPlanE ops faults (Start η) = .run (.failed o pc M')) :
    ¬ ∃ ρ, P.Models ops η ρ :=
  failed_correct ops hv η (runFromE_run π ops _ _ _ _ hrun)

/-- A valid plan's run under faults is never `stuck` either: `stuck` stays a plan defect. -/
theorem runPlanE_not_stuck (hv : π.Valid) (faults : Faults) (η : P.Input) (pc : Nat)
    (M : Memory K σ) : π.runPlanE ops faults (Start η) ≠ .run (.stuck pc M) := fun h =>
  runPlan_not_stuck ops hv η pc M (runFromE_run π ops _ _ _ _ h)

/-- With no faults the wrapped run is the plain run (the error-free special case). -/
theorem runPlanE_noFault {faults : Faults} (h : ∀ n, faults n = none) (M : Memory K σ) :
    π.runPlanE ops faults M = .run (π.runPlan ops M) :=
  runFromE_noFault π ops h _ _ _

/-! ### The error-free profile -/

/-- A schedule with no fault at any plan position gives an error-free run. -/
theorem errorFreeRun_of_noFaultsInPlan {faults : Faults} (h : π.NoFaultsInPlan faults)
    (M : Memory K σ) : π.ErrorFreeRun ops faults M := by
  cases hrun : π.runPlanE ops faults M with
  | run o => exact ⟨o, hrun⟩
  | error e pc' M' =>
    exfalso
    obtain ⟨k, cmd, hc, hpc, -, j, hj, hf⟩ := runFromE_error π ops _ _ _ _ _ _ hrun
    subst hpc
    rw [Nat.zero_add] at hf
    have hja := π.ann_getElem?_offset hc (List.getElem?_eq_getElem hj)
    rw [h _ (List.getElem?_eq_some_iff.mp hja).1] at hf
    cases hf

/-! ### Fused plans (`FValid`) under faults -/

/-- **31.3 (a), fused, under faults.** -/
theorem done_correct_FE (hv : π.FValid) (faults : Faults) (η : P.Input) {m : Nat}
    {M' : Memory K σ}
    (hrun : π.runPlanE ops faults (Start η) = .run (.done m M')) :
    ∃ c, ∃ success : P.Successful ops η c,
      (∀ ρ, P.Models ops η ρ ↔ ρ = P.finalStore c success.2) ∧
      π.Decode m M' = some (P.outputProjection (P.finalStore c success.2)) ∧
      P.denotation ops η (P.successful_admInput ops η c success) =
        P.outputProjection (P.finalStore c success.2) :=
  done_correct_F ops hv η (runFromE_run π ops _ _ _ _ hrun)

/-- **31.3 (b), fused, under faults.** -/
theorem failed_correct_FE (hv : π.FValid) (faults : Faults) (η : P.Input) {o : OccRef P}
    {pc : Nat} {M' : Memory K σ}
    (hrun : π.runPlanE ops faults (Start η) = .run (.failed o pc M')) :
    ¬ ∃ ρ, P.Models ops η ρ :=
  failed_correct_F ops hv η (runFromE_run π ops _ _ _ _ hrun)

/-- A fused plan with a valid expansion never gets `stuck`, with or without faults. -/
theorem runPlanE_not_stuck_FE (hv : π.FValid) (faults : Faults) (η : P.Input) (pc : Nat)
    (M : Memory K σ) : π.runPlanE ops faults (Start η) ≠ .run (.stuck pc M) := fun h =>
  runPlan_not_stuck_F ops hv η pc M (runFromE_run π ops _ _ _ _ h)

/-- **31.3 (c), error-free profile, under a schedule.** An error-free run of a fused plan with
    a valid expansion ends `done` or `failed`. -/
theorem done_or_failed_FE (hv : π.FValid) (faults : Faults) (η : P.Input)
    (hef : π.ErrorFreeRun ops faults (Start η)) :
    (∃ M', π.runPlanE ops faults (Start η) = .run (.done π.commands.length M')) ∨
      ∃ o pc M', π.runPlanE ops faults (Start η) = .run (.failed o pc M') := by
  obtain ⟨o, ho⟩ := hef
  have h : π.runPlan ops (Start η) = o := runFromE_run π ops _ _ _ _ ho
  rcases done_or_failed_F ops hv η with ⟨M', h'⟩ | ⟨o', pc, M', h'⟩
  · rw [h'] at h
    subst h
    exact Or.inl ⟨M', ho⟩
  · rw [h'] at h
    subst h
    exact Or.inr ⟨o', pc, M', ho⟩

/-- **31.3 (c), converse, error-free.** A model forces an error-free run to be `done`, with the
    decoded output the model's. -/
theorem done_of_model_FE (hv : π.FValid) (faults : Faults) (η : P.Input) {ρ : Store K σ}
    (hρ : P.Models ops η ρ) (hef : π.ErrorFreeRun ops faults (Start η)) :
    ∃ M', π.runPlanE ops faults (Start η) = .run (.done π.commands.length M') ∧
      π.Decode π.commands.length M' = some (P.outputProjection ρ) := by
  obtain ⟨M', h, hd⟩ := done_of_model_F ops hv η hρ
  obtain ⟨o, ho⟩ := hef
  have h' : π.runPlan ops (Start η) = o := runFromE_run π ops _ _ _ _ ho
  rw [h] at h'
  subst h'
  exact ⟨M', ho, hd⟩

/-- **31.3 (c), iff, error-free.** -/
theorem done_iff_model_FE (hv : π.FValid) (faults : Faults) (η : P.Input)
    (hef : π.ErrorFreeRun ops faults (Start η)) :
    (∃ m M', π.runPlanE ops faults (Start η) = .run (.done m M')) ↔ ∃ ρ, P.Models ops η ρ := by
  constructor
  · rintro ⟨m, M', h⟩
    obtain ⟨c, success, hmod, -⟩ := done_correct_FE ops hv faults η h
    exact ⟨_, (hmod _).mpr rfl⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨M', h, -⟩ := done_of_model_FE ops hv faults η hρ hef
    exact ⟨_, M', h⟩

/-- Outside the error-free profile a valid plan can end in an implementation error even when a
    model exists (spec 31.3, last sentence): with a fault at an executed position of the first
    command, the fault-free run is `done` while the faulty run is an `error` at pc 0. -/
theorem error_despite_model (hv : π.FValid) (η : P.Input) {ρ : Store K σ}
    (hρ : P.Models ops η ρ) {faults : Faults} {cmd : Command P}
    (hcmd : π.commands[0]? = some cmd) {j : Nat} (hj : j < cmd.length) {e : ImplErr}
    (hf : faults j = some e) :
    (∃ M', π.runPlanE ops (fun _ => none) (Start η) = .run (.done π.commands.length M')) ∧
      ∃ e', π.runPlanE ops faults (Start η) = .error e' 0 (Start η) := by
  obtain ⟨M', h, -⟩ := done_of_model_F ops hv η hρ
  refine ⟨⟨M', by rw [runPlanE_noFault ops (fun _ => rfl), h]⟩, ?_⟩
  cases hl : π.commands with
  | nil => simp [hl] at hcmd
  | cons c rest =>
    rw [hl] at hcmd
    obtain rfl : c = cmd := Option.some.inj hcmd
    have h0 : π.offset 0 = 0 := by simp [offset, prefixAnn_zero]
    obtain ⟨e', hfi⟩ := faultIn_isSome (n := π.offset 0) (k := c.length) hj
      (by rw [h0]; simpa using hf)
    exact ⟨e', by simp only [runPlanE, hl, runFromE, hfi]⟩

/-! ### `R` at the error state -/

/-- **`R` at the error state.** An error at command `pc'` leaves a memory related to the
    reference state there: the error state is a fault-free reachable state. -/
theorem runFromE_error_R (hv : π.FValid) {faults : Faults} {η : P.Input} :
    ∀ (l : List (Command P)) (pc : Nat) (M : Memory K σ) (c : P.Running) (e : ImplErr)
      (pc' : Nat) (M' : Memory K σ),
      π.commands.drop pc = l → π.R ops η pc M c → π.refState ops η pc = some c →
      π.runFromE ops faults pc M l = .error e pc' M' →
      ∃ c', π.refState ops η pc' = some c' ∧ π.R ops η pc' M' c'
  | [], pc, M, c, e, pc', M', _, _, _, h => by simp [runFromE] at h
  | cmd :: rest, pc, M, c, e, pc', M', hl, hR, hc, h => by
    have hcmd : π.commands[pc]? = some cmd := by
      rw [← List.head?_drop, hl]
      rfl
    have hrest : π.commands.drop (pc + 1) = rest := by
      rw [← List.tail_drop, hl]
      rfl
    have ok : ∀ j a, cmd[j]? = some a → π.expand.AnnOK (π.offset pc + j) a := fun j a hj =>
      hv.stepOK (π.offset pc + j) a (π.expand_commands_getElem? (π.ann_getElem?_offset hcmd hj))
    simp only [runFromE] at h
    split at h
    · simp only [FOutcome.error.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact ⟨c, hc, hR⟩
    · cases hs : π.stepCommand ops pc M cmd with
      | ok M₁ =>
        rw [hs] at h
        obtain ⟨c₁, hc₁, hR₁, -⟩ := step_R_command π ops hR hc hcmd ok hs
        exact runFromE_error_R hv rest (pc + 1) M₁ c₁ e pc' M' hrest hR₁ hc₁ h
      | semFail o => rw [hs] at h; cases h
      | stuck => rw [hs] at h; cases h

/-- `runFromE_error_R` from `Start`. -/
theorem runPlanE_error_R (hv : π.FValid) (faults : Faults) (η : P.Input) {e : ImplErr}
    {pc' : Nat} {M' : Memory K σ}
    (h : π.runPlanE ops faults (Start η) = .error e pc' M') :
    ∃ c', π.refState ops η pc' = some c' ∧ π.R ops η pc' M' c' :=
  runFromE_error_R ops hv π.commands 0 (Start η) (P.initial η) e pc' M' List.drop_zero
    (π.R_start ops η) (by simp [refState, prefixAnn_zero]) h

#print axioms runFromE_noFault
#print axioms runFromE_run
#print axioms runFromE_error
#print axioms done_correct_E
#print axioms failed_correct_E
#print axioms runPlanE_not_stuck
#print axioms errorFreeRun_of_noFaultsInPlan
#print axioms done_correct_FE
#print axioms failed_correct_FE
#print axioms runPlanE_not_stuck_FE
#print axioms done_or_failed_FE
#print axioms done_of_model_FE
#print axioms done_iff_model_FE
#print axioms error_despite_model
#print axioms runFromE_error_R
#print axioms runPlanE_error_R

end LeanNCD.Semantics.Program.Plan
