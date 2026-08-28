import DSL.Pipeline.RouteWeaveTest
import Eval.Plan.NonlinCompileTest
import Eval.Plan.NonlinDenseTest
import Eval.Plan.ScanCompileTest

/-!
# Task 4 nonlinear scan admission seed — Phase 1 and Phase 2 stop report

This seed follows the ordered rehearsal requested for Task 4 of
`papers/nonlinearity_split_pair_direct_lowering.md`.

* Phase 1 rehearses `retainedAxisPos`.
* Phase 2 inventories the required donors, executes only public donor schedules with their exact
  donor inputs through legacy `evalScheduled`, and records the missing source provenance.
* The stop condition is reached in Phase 2: the six spike source-program/input pairs cannot be
  recovered from retained repository history, refs, worktrees, or session evidence.

There is deliberately no independent-unroller clone, `.freeNorm` oracle implementation, mutation
hook, Plan lowering, or Phase 3–7 claim in this file.
-/

namespace LeanNCD.NonlinearScanAdmissionSeed

open LeanNCD LeanNCD.Eval Std

/-! ## Phase 1 — retained local-axis positions -/

def retainedAxisPos (slots : List LHSSlot) (p : Nat) : Nat :=
  (slots.take p).countP (fun sl => match sl with
    | .free _ | .freeNorm _ => true
    | _ => false)

private def posL : AxisSpec := ⟨"posL", 4291, .nat⟩
private def posM : AxisSpec := ⟨"posM", 4292, .nat⟩
private def posI : AxisSpec := ⟨"posI", 4293, .real⟩
private def posJ : AxisSpec := ⟨"posJ", 4294, .real⟩
private def posK : AxisSpec := ⟨"posK", 4295, .real⟩

#guard retainedAxisPos [.iterNext posL, .freeNorm posJ] 1 == 0
#guard retainedAxisPos
  [.iterNext posL, .free posI, .freeNorm posJ, .iterNext posM, .free posK] 2 == 1
#guard retainedAxisPos
  [.free posI, .iterNext posL, .free posJ, .freeNorm posK] 3 == 2

/-! ## Phase 2 — exact donor recovery and legacy executions

### Private ReLU source donor

The source below is a faithful local clone of private
`test/DSL/Pipeline/ScanAffineTest.lean::reluScan`. Its source construction is recovered, but that
donor contains no input tensors and the spike did not retain its six fixture input sets. Consequently
it is compiled here but is not assigned invented inputs or claimed to reproduce a recorded value.
-/

def reluScanSource : TLProgram := tlprog!{
  iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := relu(S[j, l] · A[j, k])
}

def reluScanScheduled : Option ScheduledProgram :=
  match reluScanSource.compileToScheduled.run 0 with
  | .ok sched _ => some sched
  | .error _ _ => none

#guard reluScanScheduled.isSome

/-!
### Public scheduled-program donors

These are referenced directly, not reconstructed:

* `ScanCompileTest.coupledSched` with `coupledInputs`;
* `ScanCompileTest.scratchSched` with `scratchInputs`;
* `ScanCompileTest.multiBaseSched` with `multiBaseInputs`.

Their observed values are defensible executions of the named donors. They are not the missing spike
programs and are not asserted equal to any of §3.6's six recorded targets.
-/

def legacyState (sched : ScheduledProgram) (inputs : HashMap String DenseTensor)
    (name : String) : Option DenseTensor :=
  (evalScheduled sched inputs).toOption.bind (·.env[name]?)

def donorLine (label : String) (sched : ScheduledProgram)
    (inputs : HashMap String DenseTensor) (name : String) : String :=
  match legacyState sched inputs name with
  | some t => label ++ ": " ++ name ++ " shape " ++ toString (repr t.shape) ++
      " = " ++ toString (repr t.data)
  | none => label ++ ": legacy evalScheduled produced no `" ++ name ++ "`"

#guard (evalScheduled
  Eval.Plan.ScanCompileTest.coupledSched
  Eval.Plan.ScanCompileTest.coupledInputs).isOk
#guard (evalScheduled
  Eval.Plan.ScanCompileTest.scratchSched
  Eval.Plan.ScanCompileTest.scratchInputs).isOk
#guard (evalScheduled
  Eval.Plan.ScanCompileTest.multiBaseSched
  Eval.Plan.ScanCompileTest.multiBaseInputs).isOk

/-!
### Fragment and Plan-only donors

`NonlinCompileTest.sampleMask` is only a mask expression.
`NonlinDenseTest.axiswisePlan` is a Plan-level worker fixture, not a `TLProgram` or
`ScheduledProgram`. They are recovered and checked below, but neither can supply a missing source
program to legacy `evalScheduled`.

Task 1's public `RouteWeaveTest.freeNormAxiswiseProg` is an exact top-level axiswise source donor; it
is not a scan and contains no inputs. It is compiled to confirm availability, not presented as the
interleaved-axiswise spike source.
-/

#guard Eval.Plan.NonlinCompileTest.sampleMask ==
  BoolExpr.rel .eq (.embed (.const 0)) (.embed (.const 0))

#guard match Eval.Plan.NonlinDenseTest.axiswisePlan.steps[1]? with
  | some (LeanNCD.Eval.Plan.PlanStep.axiswise p) => p.axisPos == 1 && p.fn == .normalize
  | _ => false

#guard match LeanNCD.freeNormAxiswiseProg.compileToScheduled.run 0 with
  | .ok sched _ => sched.stmts.length == 1
  | .error _ _ => false

run_cmd do
  Lean.logInfo "PHASE 1 COMPLETE: retainedAxisPos guards passed"
  Lean.logInfo (donorLine "PHASE 2 exact public donor coupledSched"
    Eval.Plan.ScanCompileTest.coupledSched Eval.Plan.ScanCompileTest.coupledInputs "G")
  Lean.logInfo (donorLine "PHASE 2 exact public donor coupledSched"
    Eval.Plan.ScanCompileTest.coupledSched Eval.Plan.ScanCompileTest.coupledInputs "H")
  Lean.logInfo (donorLine "PHASE 2 exact public donor scratchSched"
    Eval.Plan.ScanCompileTest.scratchSched Eval.Plan.ScanCompileTest.scratchInputs "S")
  Lean.logInfo (donorLine "PHASE 2 exact public donor multiBaseSched"
    Eval.Plan.ScanCompileTest.multiBaseSched Eval.Plan.ScanCompileTest.multiBaseInputs "dp")
  Lean.logInfo "PHASE 2 STOP: exact source-program/input pairs for multiple §3.6 groups were not recovered"
  Lean.logInfo "PHASES 3–7 NOT EXECUTED"

end LeanNCD.NonlinearScanAdmissionSeed
