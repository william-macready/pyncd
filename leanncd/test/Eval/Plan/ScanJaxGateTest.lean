import LeanNCD.Eval.Plan.Executable
import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter32
import Eval.Plan.ScanCompileTest

/-!
# `checkJaxScanSupport` on a compiled two-axis scan

`ExecutableTest` pins the scan gate on `ScanTest`'s hand-built scans, where no checked two-axis plan
exists. `ScanCompileTest.coupledSched` is one: it COMPILES (two advancing axes, two coupled states),
so the gate's multi-axis refusal is reachable from a real checked scan and is pinned here. Separate
file because importing `ScanCompileTest` into `ExecutableTest` brings the DSL's `bias` keyword into
scope and breaks that file's structure-instance fields.
-/

namespace LeanNCD.Eval.Plan.ScanJaxGateTest
open LeanNCD.Eval.Plan

/-- The compiled checked scan of `coupledSched` (the first scan node of its plan). -/
def coupledChecked? : Option CheckedScanPlan :=
  match ScanCompileTest.prepared ScanCompileTest.coupledSched ScanCompileTest.coupledInputs with
  | none => none
  | some p => p.plan.checkedNodes.findSome? fun | .scan c => some c | _ => none

#guard coupledChecked?.isSome
-- Two history axes, and the gate refuses it with the located `scanMultiAxis`. The accept neighbour
-- (a one-axis scan passes the same gate) is `ExecutableTest`'s `linearScan` guards.
#guard (match coupledChecked? with
  | some c => c.raw.historyExtents.size == 2 && (match checkJaxScanSupport 5 c with
      | .error e => e == .scanMultiAxis 5
      | .ok _ => false)
  | none => false)

/-! ### The `.booleanReach` profile on the compiled Boolean-reachability scan

Donor: `reachProg`, copied verbatim from `experiments/jax_bridge/EvalPlanLogicSmoke.lean`, prepared by
the same path (`compileToScheduled`, `InputSignature.ofDenseInputs[32]ForDecls`, `prepareEvalPlan`).
Its scan node writes a Boolean state (`Reach`), and a later real node (`Closed`, f64) reads it. -/

open LeanNCD LeanNCD.Eval Std

def reachProg : TLProgram := tlprog!{
  axis i : ℕ = 6, j : ℕ = 6, k : ℕ = 6
  iter h = 7
  predicate Edge(i, j), Reach(i, j, h)
  tensor f64 Closed(i, j)
  Reach[i, j, 0] := [i = j]
  Reach[i, j, h +1] := Reach[i, j, h] + Reach[i, k, h] · Edge[k, j]
  Closed[i, j] := Reach[i, j, 6]
}

def retag32 (p : TLProgram) : TLProgram :=
  { p with decls := p.decls.map fun d => match d with
      | .typedTensor .f64 n ax => .typedTensor .f32 n ax
      | d => d }

def edgeEnv : NamedDenseEnv := HashMap.ofList [("Edge", ⟨[6, 6], Array.replicate 36 0⟩)]

def reachPrepared? (f32 : Bool) : Option PreparedPlan :=
  match ((if f32 then retag32 reachProg else reachProg).compileToScheduled).run 0 with
  | .error _ _ => none
  | .ok sched _ =>
    if f32 then
      match InputSignature.ofDenseInputs32ForDecls sched.decls
          (edgeEnv.map fun _ t => ⟨t.shape, t.data.map Float.toFloat32⟩) with
      | .ok sig => (prepareEvalPlan sched sig).toOption
      | .error _ => none
    else
      match InputSignature.ofDenseInputsForDecls sched.decls edgeEnv with
      | .ok sig => (prepareEvalPlan sched sig).toOption
      | .error _ => none

def reachScan? (f32 : Bool) : Option CheckedScanPlan :=
  match reachPrepared? f32 with
  | none => none
  | some p => p.plan.checkedNodes.findSome? fun | .scan c => some c | _ => none

def reachVerdict (f32 : Bool) (profile : JaxRenderProfile) : Option JaxSupportError :=
  match reachScan? f32 with
  | none => some (.scanMultiAxis 999)  -- sentinel: the donor itself must compile (guarded below)
  | some c => match checkJaxScanSupport 5 c profile with
    | .ok _ => none
    | .error e => some e

-- The donor compiles in both precisions, to a scan whose state is Boolean.
#guard (reachScan? false).isSome
#guard (reachScan? true).isSome
-- Accept under the new profile (the base block's Boolean destination is slot 0 of its own table);
-- refused, located at that destination, by `.realOnly` and `.maxPlus` (observed).
#guard reachVerdict false .booleanReach == none
#guard reachVerdict false .realOnly == some (.destinationDType 5 0 .bool)
#guard reachVerdict false .maxPlus == some (.destinationDType 5 0 .bool)
-- Pin 7: the binary32 retag of the same program (Boolean algebra constants are unchanged; `Closed`
-- becomes f32 under `admittedAlgebraF32`).
#guard reachVerdict true .booleanReach == none
#guard reachVerdict true .realOnly == some (.destinationDType 5 0 .bool)
#guard reachVerdict true .maxPlus == some (.destinationDType 5 0 .bool)

end LeanNCD.Eval.Plan.ScanJaxGateTest
