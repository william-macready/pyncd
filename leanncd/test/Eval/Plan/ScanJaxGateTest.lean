import LeanNCD.Eval.Plan.Executable
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

end LeanNCD.Eval.Plan.ScanJaxGateTest
