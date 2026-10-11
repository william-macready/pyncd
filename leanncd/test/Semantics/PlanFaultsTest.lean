import Semantics.PlanFusionCorrectnessTest

/- D7 fixtures: implementation errors as a fault oracle (`Plan/Faults.lean`). Every asserted
   value was observed from a real run. Plans: `fused` = [[initZero; acc], [pub]] (expanded
   positions 0, 1 | 2) and the scalar fused plan `sPlanFused` = [[initZero], [acc, pub, acc, pub]]
   (positions 0 | 1, 2, 3, 4; with `bad` the second accumulate, position 3, fails semantically). -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

/-- A schedule with exactly one fault, at expanded position `n`. -/
def faultAt (n : Nat) (e : ImplErr) : Faults := fun k => if k = n then some e else none

/-- Two faults: `e₁` at position `n₁`, `e₂` at position `n₂`. -/
def faultsAt (n₁ : Nat) (e₁ : ImplErr) (n₂ : Nat) (e₂ : ImplErr) : Faults :=
  fun k => if k = n₁ then some e₁ else if k = n₂ then some e₂ else none

/-- Outcome kind, pc, error, memory row of a faulty run (taggedOut). -/
def eRow {P : Program Carrier declarations registry} : FOutcome P →
    String × Nat × Option ImplErr × List (Option ℚ)
  | .run o => let r := outcomeRow o; ("run:" ++ r.1, r.2.1, none, r.2.2.2)
  | .error e pc M => ("error", pc, some e, rowOf (PlanOutcome.done (P := P) 0 M))

def eFused (faults : Faults) := fused.runPlanE ops faults (Start η0)

/-! ### (1) `fused`: no fault, then a single fault at each position -/

#eval check "faults-none" (eRow (eFused fun _ => none))
  ("run:done", 2, none, [some 0, some 14, some 0])
-- position 0: first annotation of command 0 -> error at pc 0, the Start memory.
#eval check "faults-first-position" (eRow (eFused (faultAt 0 .allocFail)))
  ("error", 0, some .allocFail, [none, none, none])
-- position 1: MIDDLE of the fused command. initZero would have run, but the command is
-- all-or-nothing: the reported memory is still the pre-command (Start) memory.
#eval check "faults-mid-fused-command" (eRow (eFused (faultAt 1 .kernelFault)))
  ("error", 0, some .kernelFault, [none, none, none])
-- position 2: the last command -> pc 1, memory after command 0.
#eval check "faults-last-position" (eRow (eFused (faultAt 2 .allocFail)))
  ("error", 1, some .allocFail, [some 0, some 14, some 0])
-- position 3 is past the plan (3 annotations): never reached, the run is the plain run.
#eval check "faults-beyond-plan" (eRow (eFused (faultAt 3 .allocFail)))
  ("run:done", 2, none, [some 0, some 14, some 0])

/-! ### (2) which fault is reported -/

-- two faults inside one command: the FIRST position's fault is reported.
#eval check "faults-first-wins-in-command"
  (eRow (eFused (faultsAt 0 .kernelFault 1 .allocFail)))
  ("error", 0, some .kernelFault, [none, none, none])
-- faults in two commands: the EARLIER command stops the run.
#eval check "faults-first-wins-across-commands"
  (eRow (eFused (faultsAt 2 .allocFail 1 .kernelFault)))
  ("error", 0, some .kernelFault, [none, none, none])

/-! ### (3) a fault pre-empts a semantic failure in the same command -/

def sRowEP (bad : Bool) (π : (scalarRole bad).Plan) (faults : Faults) :
    String × Nat × Option ImplErr × List (Option ℚ) :=
  let row (M : Memory Carrier scalarDeclarations) :=
    [M (place ⟨0, ()⟩), M (place ⟨1, ()⟩), M (place ⟨2, ()⟩)]
  match π.runPlanE ops faults (Start (scalarInput bad)) with
  | .run (.done pc M) => ("run:done", pc, none, row M)
  | .run (.failed _ pc M) => ("run:failed", pc, none, row M)
  | .run (.stuck pc M) => ("run:stuck", pc, none, row M)
  | .error e pc M => ("error", pc, some e, row M)

def sRowE (bad : Bool) := sRowEP bad (sPlanFused bad)

-- control: with no faults the bad plan fails semantically in command 1 (pre-command memory).
#eval check "faults-semfail-control" (sRowE true fun _ => none)
  ("run:failed", 1, none, [some 7, some 0, some 0])
-- a fault at position 4, AFTER the failing annotation (position 3) of the same command, still
-- wins: the fault is consulted before the command runs.
#eval check "faults-preempt-semfail" (sRowE true (faultAt 4 .kernelFault))
  ("error", 1, some .kernelFault, [some 7, some 0, some 0])
-- the good plan under the same position-4 fault: error, not done.
#eval check "faults-good-plan-error" (sRowE false (faultAt 4 .allocFail))
  ("error", 1, some .allocFail, [some 7, some 0, some 0])

-- singleton `sPlan` = [initZero | acc1 | pub1 | acc2 | pub2] (positions 0-4): the bad plan fails
-- semantically at command 3 (acc2) with pre-command memory [7,2,0]; a fault at a LATER command
-- (position 4) is never reached, a fault at the failing command (position 3) pre-empts it.
#eval check "faults-later-command-not-reached" (sRowEP true (sPlan true) (faultAt 4 .kernelFault))
  ("run:failed", 3, none, [some 7, some 2, some 0])
#eval check "faults-at-failing-command" (sRowEP true (sPlan true) (faultAt 3 .kernelFault))
  ("error", 3, some .kernelFault, [some 7, some 2, some 0])

/-! ### (4) theorem instances -/

example : fused.ann.length = 3 := rfl

-- the error-free profile by schedule: a fault beyond the plan is no fault in the plan ...
example : fused.NoFaultsInPlan (faultAt 3 .allocFail) := by
  intro n hn
  have : n < 3 := hn
  simp [faultAt]
  omega

-- ... and a fault inside the plan is not (negative control: the predicate has teeth).
example : ¬ fused.NoFaultsInPlan (faultAt 2 .allocFail) := by
  intro h
  have := h 2 (by decide)
  simp [faultAt] at this

theorem fused_beyond_errorFree : fused.ErrorFreeRun ops (faultAt 3 .allocFail) (Start η0) :=
  fused.errorFreeRun_of_noFaultsInPlan ops (by
    intro n hn
    have : n < 3 := hn
    simp [faultAt]
    omega) _

/-- (c) under an error-free run: done iff a model exists. -/
theorem fused_done_iff_model_beyond :
    (∃ m M', fused.runPlanE ops (faultAt 3 .allocFail) (Start η0) = .run (.done m M')) ↔
      ∃ ρ, taggedOut.Models ops η0 ρ :=
  done_iff_model_FE ops fused_fvalid _ η0 fused_beyond_errorFree

/-- Outside the error-free profile: the model exists, the fault-free run is `done`, and the
    faulty run is an error at pc 0. -/
theorem fused_error_despite_model :
    (∃ M', fused.runPlanE ops (fun _ => none) (Start η0) = .run (.done fused.commands.length M')) ∧
      ∃ e', fused.runPlanE ops (faultAt 1 .kernelFault) (Start η0) = .error e' 0 (Start η0) := by
  obtain ⟨ρ, hρ⟩ := fused_has_model
  exact error_despite_model ops fused_fvalid η0 hρ (cmd := [.initZero block, .acc group])
    rfl (j := 1) (by decide) (e := .kernelFault) (by simp [faultAt])

/-- `R` at the error state of the position-2 fault (pc 1): the memory is related to the
    reference state there. -/
theorem fused_error_R : ∃ c', fused.refState ops η0 1 = some c' ∧
    fused.R ops η0 1 (finalMemory fusedRun) c' :=
  runPlanE_error_R ops fused_fvalid (faultAt 2 .allocFail) η0
    (e := .allocFail) (pc' := 1) (M' := finalMemory fusedRun) (by
      -- the pre-command memory at pc 1 is the memory after command 0, i.e. fusedRun's final
      -- memory (command 1 is `pub`, which writes nothing)
      rfl)

#print axioms fused_beyond_errorFree
#print axioms fused_done_iff_model_beyond
#print axioms fused_error_despite_model
#print axioms fused_error_R

end LeanNCD.Semantics.PlanFixtures
