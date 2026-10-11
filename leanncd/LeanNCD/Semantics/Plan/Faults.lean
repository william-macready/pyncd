import LeanNCD.Semantics.Plan.Correctness

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

#print axioms runFromE_noFault
#print axioms runFromE_run
#print axioms runFromE_error
#print axioms done_correct_E
#print axioms failed_correct_E
#print axioms runPlanE_not_stuck

end LeanNCD.Semantics.Program.Plan
