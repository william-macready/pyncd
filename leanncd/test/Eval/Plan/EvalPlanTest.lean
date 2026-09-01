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
               , factors := #[.read readS] }]
  , algebra := admittedAlgebra }

-- Outer slots: `0 = S0`, `1 = X`, `2 = S` (`ScanTest.outerSigs`, reused verbatim), plus a new
-- slot `3 = Y` (the plain step's output).
def outerTensorSigs : Array TensorSignature := outerSigs ++ #[{ shape := #[3], dtype := .f64 }]

def outerPlan : RawEvalPlan :=
  { tensorSigs := outerTensorSigs, inputSlots := #[0, 1]
  , steps := #[.scan linearScan, .assign yAssign]
  }

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

/-! ## Fix-wave addition: a `.assign` step's bad forward read at term index ≥ 1

Review finding (Important #1): routing the forward-read availability check through the generic
`PlanStep.sourceSlots` accessor loses the original per-term/per-factor locators — every fixture
above happens to have its bad read at term 0/factor 0, which masked the loss (`checkPlan` now uses
a direct per-term/per-factor loop for `.assign` steps instead, restoring the original locators).
This fixture's bad read sits at term INDEX 1 (the second term), pinning the `ti` locator down for
real: term 0 reads slot 0 (`A`, a graph input, available), term 1 reads slot 1 (`Z`, neither an
input nor produced by anything), so the graph is rejected with `ti = 1`, not `ti = 0`. -/

def termLocatorSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }   -- 0 = A (input)
   , { shape := #[2], dtype := .f64 }   -- 1 = Z (never an input, never produced)
   , { shape := #[2], dtype := .f64 } ] -- 2 = C (dest)

def termLocatorReadA : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[2], oobPolicy := .zeroPad }

def termLocatorReadZ : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[2], oobPolicy := .zeroPad }

def termLocatorTerm0 : TermPlan :=
  { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
  , factors := #[.read termLocatorReadA] }

def termLocatorTerm1 : TermPlan :=
  { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
  , factors := #[.read termLocatorReadZ] }

-- `C[i] := A[i] + Z[i]`: term 0 (index 0) is fine; term 1 (index 1) is the bad read.
def termLocatorAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[2]
  , terms := #[termLocatorTerm0, termLocatorTerm1], algebra := admittedAlgebra }

def termLocatorPlan : RawEvalPlan :=
  { tensorSigs := termLocatorSigs, inputSlots := #[0]
  , steps := #[.assign termLocatorAssign]
  }

-- `ti = 1`, `fi = 0`, slot = 1 — the exact locator of the bad read, not `0 0` by coincidence.
#guard errOf (checkPlan termLocatorPlan) == some (.assign (.invalidForwardRead 0 1 0 1))

-- Task 5.1: outer forward-read locator with an Iverson factor BEFORE the failing read. The bad term
-- becomes `[iverson, read(Z)]` (iteration basis `#[2]`, size 1, so leaf width 1). The forward-read
-- check skips the predicate but keeps the all-factor index, so it reports `fi = 1`, NOT filtered-read
-- 0 — the two would coincide in the read-only `termLocatorPlan` above.
def termLocatorPredZ : PosBoolExpr :=
  .rel .lt (.affine { coeffs := #[0], bias := 0 }) (.affine { coeffs := #[0], bias := 1 })

def termLocatorTerm1Iverson : TermPlan :=
  { termLocatorTerm1 with factors := #[.iverson termLocatorPredZ, .read termLocatorReadZ] }

def termLocatorAssignIverson : AssignPlan :=
  { termLocatorAssign with terms := #[termLocatorTerm0, termLocatorTerm1Iverson] }

def termLocatorPlanIverson : RawEvalPlan :=
  { tensorSigs := termLocatorSigs, inputSlots := #[0]
  , steps := #[.assign termLocatorAssignIverson] }

#guard errOf (checkPlan termLocatorPlanIverson) == some (.assign (.invalidForwardRead 0 1 1 1))

-- Task 5.1: `PlanStep.sourceSlots` excludes Iverson factors (filterMap reads). An assign whose term
-- is `[read(slot 0), iverson, read(slot 1)]` yields only the two read slots, in order — the Iverson
-- factor is omitted (unchanged accessor code a diff cannot show; this assertion is the guard).
def sourceSlotIversonAssign : AssignPlan :=
  { termLocatorAssign with terms := #[{ termLocatorTerm0 with
      factors := #[.read termLocatorReadA, .iverson termLocatorPredZ, .read termLocatorReadZ] }] }

#guard (PlanStep.assign sourceSlotIversonAssign).sourceSlots == #[0, 1]

/-! ## Fix-wave addition: a genuine two-state scan, exercised through the multi-destination path

Review finding (Important #3): every scan fixture above reuses `linearScan`, which has exactly one
state (one destination slot) — nothing distinguished a correct "check/mark every destination" loop
from a bug that only checks/commits `dests[0]!`. Reuses `ScanTest.coupledScan` (Task 3's
Fibonacci-shaped `G`/`H` scan: `G[0] := C; H[0] := C; G[l+1] := G[l]+H[l]; H[l+1] := G[l]`, two
`StateSlot`s — `stateGCoupled` destSlot 1, `stateHCoupled` destSlot 2) as a standalone outer
`.scan` node. -/

def twoStateOuterPlan : RawEvalPlan :=
  { tensorSigs := outerSigsCoupled, inputSlots := #[0]
  , steps := #[.scan coupledScan]
  }

def coupledOuterInputs : Array DenseTensor := #[ { shape := [], data := #[1.0] } ]

-- Accept: BOTH destination slots (1 = G, 2 = H) end up marked produced — if `checkPlan` only
-- checked/committed `dests[0]!`, slot 2 would still show as unproduced and `missingProduction 2`
-- would fire, so `isOk` alone already distinguishes that bug; `runDensePlan` below additionally
-- confirms the checked node is the real, correctly-constructed scan (not just "some node got
-- pushed"), reusing Task 3's own verified Fixture-4 numbers: C=1 ⇒ G=[1,2,3,5], H=[1,1,2,3].
#guard isOk (checkPlan twoStateOuterPlan)

run_cmd do
  match checkPlan twoStateOuterPlan with
  | .error e => throwError s!"two-state accept: checkPlan rejected a well-formed 2-state scan: {repr e}"
  | .ok checked =>
      match runDensePlan checked coupledOuterInputs with
      | .error e => throwError s!"two-state accept: runDensePlan error: {repr e}"
      | .ok result =>
          let G := result.getD 1 { shape := [], data := #[] }
          let H := result.getD 2 { shape := [], data := #[] }
          unless DenseTensor.approxEq G { shape := [4], data := #[1.0, 2.0, 3.0, 5.0] } do
            throwError s!"two-state accept: wrong G {repr G.data}"
          unless DenseTensor.approxEq H { shape := [4], data := #[1.0, 1.0, 2.0, 3.0] } do
            throwError s!"two-state accept: wrong H {repr H.data}"

-- `H[i] := C` (a valid broadcast of the scalar input into H's own shape `[4]`), placed BEFORE the
-- scan so it already produces slot 2 (H's own future destination) by the time the scan step runs.
-- G's destination (slot 1, checked FIRST in `coupledScan.states` order) is fine and unproduced —
-- only H's (checked SECOND) collides, so this pins down that the destination loop genuinely
-- iterates every destination rather than stopping at (or only ever inspecting) the first.
def preemptRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[], bias := #[] }, sourceShape := #[], oobPolicy := .zeroPad }

def preemptTerm : TermPlan :=
  { iterationShape := #[4], contextPos := #[], outputPos := #[0], reductionPos := #[]
  , factors := #[.read preemptRead] }

def preemptAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[4]
  , terms := #[preemptTerm], algebra := admittedAlgebra }

def collideOuterPlan : RawEvalPlan :=
  { tensorSigs := outerSigsCoupled, inputSlots := #[0]
  , steps := #[.assign preemptAssign, .scan coupledScan]
  }

-- Reported collision is slot 2 (H), first produced by node 0 (`preemptAssign`), re-targeted by
-- node 1 (the scan) — NOT slot 1 (G), which never collides here.
#guard errOf (checkPlan collideOuterPlan) == some (.assign (.duplicateDestination 2 0 1))

end LeanNCD.Eval.Plan.EvalPlanTest
