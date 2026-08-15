-- leanncd/test/Eval/Plan/EvalPlanTest.lean
import LeanNCD.Eval.Plan.EvalPlan
import Eval.Plan.ScanTest

/-!
# Wave F F3 Task 4: outer-graph `checkPlan`/`runDensePlan` scan integration tests

The first test to exercise `checkPlan`/`runDensePlan`'s real multi-output scan dispatch (Tasks 1-3
built and unit-tested `checkScanPlan`/`runDenseScan` in isolation; nothing before this file wired a
`.scan` step into an outer `RawEvalPlan` graph and ran it end-to-end).

Reuses `ScanTest`'s `linearScan` fixture (Task 3: `S[iterAt l 0] := S0`, `S[iterNext l] := S[l] +
X[l]`, outer slots `0 = S0`, `1 = X`, `2 = S`) verbatim as one `PlanStep.scan` node, composed with a
plain `PlanStep.assign` node reading the scan's own output (`Y[i] := S[i]`, a new outer slot `3 =
Y`) — proving multi-output outer-graph wiring: the scan's single state destination (slot 2) is
marked produced ATOMICALLY by `checkPlan`, then the plain node reads it.

Four cases: the accept case (checked + run end-to-end, against Task 3's own verified numbers), a
plain step reading the scan's state destination BEFORE the scan step runs (`invalidForwardRead`),
two steps (a `.scan` and an `.assign`) targeting the same outer slot (`duplicateDestination`), and a
scan step whose own `checkScanPlan` fails, confirming it surfaces as `PlanStepError.scan` (not
double-wrapped through `.assign`/`nodeError`).
-/

namespace LeanNCD.Eval.Plan.EvalPlanTest
open LeanNCD.Eval.Plan
open LeanNCD.Eval.Plan.ScanTest

def isOk : Except PlanStepError CheckedEvalPlan → Bool
  | .ok _ => true | .error _ => false

def errOf : Except PlanStepError CheckedEvalPlan → Option PlanStepError
  | .ok _ => none | .error e => some e

/-! ## Outer graph: `linearScan` (Task 3) as one `.scan` node, plus a plain `.assign` node reading
its output. -/

-- `Y[i] := S[i]`: an identity read of the scan's own state destination (slot 2).
def readS : ReadPlan :=
  { sourceSlot := 2, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

def yAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[readS] }]
  , algebra := admittedAlgebra }

-- Outer slots: `0 = S0`, `1 = X`, `2 = S` (`ScanTest.outerSigs`, reused verbatim), plus a new
-- slot `3 = Y` (the plain step's output).
def outerTensorSigs : Array TensorSignature := outerSigs ++ #[{ shape := #[3], dtype := .f64 }]

def outerPlan : RawEvalPlan :=
  { tensorSigs := outerTensorSigs, inputSlots := #[0, 1]
  , steps := #[.scan linearScan, .assign yAssign]
  , numericMode := .reference64SumProduct }

def outerInputs : Array DenseTensor :=
  #[ { shape := [], data := #[1.0] }, { shape := [3], data := #[10.0, 20.0, 30.0] } ]

-- Accept: `checkPlan` dispatches the scan node to `checkScanPlan`, marks its one state destination
-- (slot 2) available, then checks the plain node's read of it — no `invalidForwardRead`, no
-- `duplicateDestination`. `runDensePlan` then dispatches to `runDenseScan` for the scan node and
-- `runDenseAssign` for the plain node. Reuses Task 3's own verified numbers (`ScanTest` Fixture 1):
-- S0=1, X=[10,20,30] ⇒ S=[1,11,31]; Y is an identity copy of S, so Y=[1,11,31] too.
#guard isOk (checkPlan outerPlan)

run_cmd do
  match checkPlan outerPlan with
  | .error e => throwError s!"accept: checkPlan rejected a well-formed scan-containing graph: {repr e}"
  | .ok checked =>
      match runDensePlan checked outerInputs with
      | .error e => throwError s!"accept: runDensePlan error: {repr e}"
      | .ok result =>
          let S := result.getD 2 { shape := [], data := #[] }
          let Y := result.getD 3 { shape := [], data := #[] }
          unless DenseTensor.approxEq S { shape := [3], data := #[1.0, 11.0, 31.0] } do
            throwError s!"accept: wrong S {repr S.data}"
          unless DenseTensor.approxEq Y { shape := [3], data := #[1.0, 11.0, 31.0] } do
            throwError s!"accept: wrong Y {repr Y.data}"

/-! ## Mutation: forward read of a scan's state destination before the scan step runs -/

-- The plain step moved BEFORE the scan step: `yAssign` (now node 0) reads slot 2 (S), which the
-- scan step (now node 1) has not yet produced.
def forwardReadPlan : RawEvalPlan :=
  { outerPlan with steps := #[.assign yAssign, .scan linearScan] }

#guard errOf (checkPlan forwardReadPlan) == some (.assign (.invalidForwardRead 0 0 0 2))

/-! ## Mutation: two steps (a `.scan` and an `.assign`) both targeting the same outer slot -/

-- `zAssign` targets slot 2 — the same slot `linearScan`'s own state (`stateS`) already targets.
-- Reuses `yAssign`'s read of slot 2 (by node 1, slot 2 is already available, so the SOURCE check
-- passes and only the DESTINATION check can fire).
def zAssign : AssignPlan := { yAssign with destinationSlot := 2 }

def duplicateDestPlan : RawEvalPlan :=
  { outerPlan with steps := #[.scan linearScan, .assign zAssign] }

#guard errOf (checkPlan duplicateDestPlan) == some (.assign (.duplicateDestination 2 0 1))

/-! ## Mutation: a scan step whose `checkScanPlan` fails, surfacing as `PlanStepError.scan` -/

-- Reuses `ScanTest`'s own plan-verified `zeroExtent` mutation (`historyExtents := #[0]`) —
-- `checkScanPlan` fails immediately (before any sigs-dependent check), so the surrounding
-- `outerTensorSigs`/`inputSlots` don't matter here. Confirms `checkScanPlan`'s failure surfaces as
-- `PlanStepError.scan stepIndex cause` directly, not wrapped through `.assign`/`nodeError`.
def scanFailPlan : RawEvalPlan :=
  { outerPlan with steps := #[.scan { linearScan with historyExtents := #[0] }] }

#guard errOf (checkPlan scanFailPlan) == some (.scan 0 (.zeroExtent 0))

end LeanNCD.Eval.Plan.EvalPlanTest
