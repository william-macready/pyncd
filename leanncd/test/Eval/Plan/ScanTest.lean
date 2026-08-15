-- leanncd/test/Eval/Plan/ScanTest.lean
import LeanNCD.Eval.Plan.Scan

/-!
# Wave F F3 Task 1: write-geometry recognizer + `checkScanPlan` structural-half tests

Two families:

1. The write-geometry recognizer worked examples (face/point-override/collision/two-free-faces),
   reproducing the plan's own hand-verified numbers against a 2-D `dp` state (row axis `r`, column
   axis `c`), independent of any full `RawScanPlan`.
2. `checkScanPlan` over a hand-built linear self-recurrence (`linearScan`: `S[iterAt l 0] := S0`,
   `S[iterNext l] := S[l] + X[l]`, one 1-D state, one advancing axis) — the accept case plus one
   mutation per reachable `ScanPlanError` branch not already exercised by the accept/zeroExtent/
   writeGeometryNotAdmitted trio the plan itself worked out. The four closed-policy `*NotAdmitted`
   branches (`iterationOrderNotAdmitted`, `boundaryPolicyNotAdmitted`, `snapshotPolicyNotAdmitted`,
   `materializationPolicyNotAdmitted`) are unreachable in this Wave: each enum has exactly one
   constructor, so no other value can ever be constructed to trigger them.
3. (Task 2) `stateReadCausal`'s causality certificate: a deep-history accept, the Jacobi/Gauss-Seidel
   discriminator's unsafe constant read now rejected at check time, a look-ahead-bias rejection, and
   a non-advancing-dimension exemption — see Part 4 below.
-/

namespace LeanNCD.Eval.Plan.ScanTest
open LeanNCD.Eval.Plan

/-! ## Part 1: write-geometry recognizer worked examples

A 2-D `dp` state (rank 2: row axis `r` = dim0, column axis `c` = dim1), matching the plan's own
verification against F0's face-plus-point-override fixture. -/

-- Base write: dp[0, j] = ROWFACE[j] — row pinned to 0, column free.
def faceWrite : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[0], #[1]], bias := #[0, 0] } }

def faceRows : Array (Option WriteRowKind) := writeRowKinds 2 0 faceWrite

#guard baseWriteRowsOk #[0] 1 faceRows

-- Base write: dp[1, 0] = ONE — a fully-pinned point override, disjoint from the face (r=1 vs r=0).
def pointWrite : StateWriteMap :=
  { outputSlot := 1, stateIndex := 0, map := { coeffs := #[#[], #[]], bias := #[1, 0] } }

def pointRows : Array (Option WriteRowKind) := writeRowKinds 2 0 pointWrite

#guard baseWriteRowsOk #[0, 1] 0 pointRows

#guard writesCollide faceRows pointRows == false

-- A shrunk point override now sharing (0,0) with the face — must be rejected as colliding.
def shrunkPointWrite : StateWriteMap :=
  { outputSlot := 1, stateIndex := 0, map := { coeffs := #[#[], #[]], bias := #[0, 0] } }

def shrunkPointRows : Array (Option WriteRowKind) := writeRowKinds 2 0 shrunkPointWrite

#guard writesCollide faceRows shrunkPointRows == true

-- A second free-axis face (column pinned to 0, row free) — individually well-formed, but never
-- disjoint from the first face (both let one axis range freely, so no dimension can force them
-- apart).
def colFaceWrite : StateWriteMap :=
  { outputSlot := 2, stateIndex := 0, map := { coeffs := #[#[1], #[0]], bias := #[0, 0] } }

def colFaceRows : Array (Option WriteRowKind) := writeRowKinds 2 0 colFaceWrite

#guard baseWriteRowsOk #[1] 1 colFaceRows

#guard writesCollide faceRows colFaceRows == true

-- Step write: dp[r+1, c+1] := dp[r,c] + T[r,c] — both axes advancing.
def dpStepWrite : StateWriteMap :=
  { outputSlot := 3, stateIndex := 0, map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[1, 1] } }

def dpStepRows : Array (Option WriteRowKind) := writeRowKinds 2 2 dpStepWrite

#guard stepWriteRowsOk #[0, 1] 0 dpStepRows

/-! ## Part 2: `checkScanPlan` over a linear self-recurrence

Outer slots: `0 = S0` (scalar), `1 = X` (shape `[3]`), `2 = S` (shape `[3]`). Base: `S[iterAt l 0] :=
S0`. Step: `S[iterNext l] := S[l] + X[l]`. `historyExtents := #[3]` (one advancing axis, size 3),
so `stepExtents = #[2]` (two transitions: l=0 -> S[1], l=1 -> S[2]). -/

def outerSigs : Array TensorSignature :=
  #[{ shape := #[], dtype := .f64 }, { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 }]

def stateS : StateSlot := { destSlot := 2, advancingDims := #[0], materialization := .completeHistory }

-- Base block: a single scalar input that is also its own sole output (no assignment needed — an
-- input slot is already "available", so it counts as produced without a copy step).
def baseBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[], dtype := .f64 }]
  , inputs := #[0], assignments := #[], outputs := #[0] }

def baseCaptureS0 : BlockCapture := { inputSlot := 0, source := .external 0 }

def baseWriteS : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[]], bias := #[0] } }

-- Step block: reads X[l] and (a snapshot of) S[l], sums them into a scalar output.
def stepReadX : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[3], oobPolicy := .zeroPad }

def stepReadS : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[3], oobPolicy := .zeroPad }

def termX : TermPlan :=
  { iterationShape := #[2], contextPos := #[0], outputPos := #[], reductionPos := #[], factors := #[stepReadX] }

def termS : TermPlan :=
  { iterationShape := #[2], contextPos := #[0], outputPos := #[], reductionPos := #[], factors := #[stepReadS] }

def stepAssign : AssignPlan :=
  { contextShape := #[2], destinationSlot := 2, outputShape := #[], terms := #[termX, termS]
  , algebra := admittedAlgebra }

def stepBlock : RawPlanBlock :=
  { contextShape := #[2]
  , tensorSigs := #[{ shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0, 1], assignments := #[stepAssign], outputs := #[2] }

def stepCaptureX : BlockCapture := { inputSlot := 0, source := .external 1 }
def stepCaptureS : BlockCapture := { inputSlot := 1, source := .state 0 }

def stepWriteS : StateWriteMap :=
  { outputSlot := 2, stateIndex := 0, map := { coeffs := #[#[1]], bias := #[1] } }

def linearScan : RawScanPlan :=
  { states := #[stateS]
  , baseBlock := baseBlock, baseCaptures := #[baseCaptureS0], baseWrites := #[baseWriteS]
  , stepBlock := stepBlock, stepCaptures := #[stepCaptureX, stepCaptureS], stepWrites := #[stepWriteS]
  , historyExtents := #[3]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

-- Accept: every obligation holds.
run_cmd do
  match checkScanPlan outerSigs linearScan with
  | .error e => throwError s!"checkScanPlan rejected a well-formed scan: {repr e}"
  | .ok _checked => pure ()

-- Mutation (plan-verified): historyExtents := #[0] -> zeroExtent.
run_cmd do
  match checkScanPlan outerSigs { linearScan with historyExtents := #[0] } with
  | .ok _ => throwError "zero-extent history should have been rejected"
  | .error e => unless e == .zeroExtent 0 do throwError s!"zeroExtent: wrong error {repr e}"

-- Mutation (plan-verified): step write bias 1 -> 2 (look-ahead-shaped) -> writeGeometryNotAdmitted.
def lookAheadStepWrite : StateWriteMap := { stepWriteS with map := { stepWriteS.map with bias := #[2] } }

run_cmd do
  match checkScanPlan outerSigs { linearScan with stepWrites := #[lookAheadStepWrite] } with
  | .ok _ => throwError "look-ahead-shaped step write should have been rejected"
  | .error e =>
      unless e == .writeGeometryNotAdmitted false 0 do
        throwError s!"writeGeometryNotAdmitted: wrong error {repr e}"

/-! ## Part 3: exhaustive mutation matrix — one fixture per remaining reachable `ScanPlanError`

`emptyBlock` is a placeholder `RawPlanBlock` for mutations whose throw happens before `checkScanPlan`
ever inspects a block's own content (the whole states-validation pass and the two block-context-shape
checks all precede `checkPlanBlock`). -/

def emptyBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[], inputs := #[], assignments := #[], outputs := #[] }

-- noStates
run_cmd do
  match checkScanPlan outerSigs { linearScan with states := #[] } with
  | .ok _ => throwError "empty states should have been rejected"
  | .error e => unless e == .noStates do throwError s!"noStates: wrong error {repr e}"

-- noAdvancingAxes (reachable but not in the brief's enumerated list; added for completeness per
-- the slice's own "every reachable branch" gate).
run_cmd do
  match checkScanPlan outerSigs { linearScan with historyExtents := #[] } with
  | .ok _ => throwError "empty historyExtents should have been rejected"
  | .error e => unless e == .noAdvancingAxes do throwError s!"noAdvancingAxes: wrong error {repr e}"

-- stateDestSlotOutOfRange
def badDestState : StateSlot := { destSlot := 99, advancingDims := #[0], materialization := .completeHistory }

run_cmd do
  match checkScanPlan outerSigs
      { linearScan with states := #[badDestState], baseBlock := emptyBlock, stepBlock := emptyBlock } with
  | .ok _ => throwError "out-of-range state destSlot should have been rejected"
  | .error e =>
      unless e == .stateDestSlotOutOfRange 0 99 3 do
        throwError s!"stateDestSlotOutOfRange: wrong error {repr e}"

-- duplicateStateDestSlot
run_cmd do
  match checkScanPlan outerSigs
      { linearScan with states := #[stateS, stateS], baseBlock := emptyBlock, stepBlock := emptyBlock } with
  | .ok _ => throwError "duplicate state destSlot should have been rejected"
  | .error e =>
      unless e == .duplicateStateDestSlot 1 0 2 do
        throwError s!"duplicateStateDestSlot: wrong error {repr e}"

-- advancingDimOutOfRange
def outOfRangeDimState : StateSlot := { stateS with advancingDims := #[5] }

run_cmd do
  match checkScanPlan outerSigs
      { linearScan with states := #[outOfRangeDimState], baseBlock := emptyBlock, stepBlock := emptyBlock } with
  | .ok _ => throwError "out-of-range advancing dim should have been rejected"
  | .error e =>
      unless e == .advancingDimOutOfRange 0 5 1 do
        throwError s!"advancingDimOutOfRange: wrong error {repr e}"

-- duplicateAdvancingDim (needs a 2-axis scan so a 2-entry advancingDims array can repeat a dim)
def dupDimState : StateSlot := { stateS with advancingDims := #[0, 0] }

run_cmd do
  let dupDimScan := { linearScan with
    states := #[dupDimState], historyExtents := #[3, 3],
    baseBlock := emptyBlock, stepBlock := emptyBlock }
  match checkScanPlan outerSigs dupDimScan with
  | .ok _ => throwError "duplicate advancing dim should have been rejected"
  | .error e =>
      unless e == .duplicateAdvancingDim 0 0 do
        throwError s!"duplicateAdvancingDim: wrong error {repr e}"

-- advancingDimCountMismatch
def wrongCountState : StateSlot := { stateS with advancingDims := #[0, 1] }

run_cmd do
  match checkScanPlan outerSigs
      { linearScan with states := #[wrongCountState], baseBlock := emptyBlock, stepBlock := emptyBlock } with
  | .ok _ => throwError "advancing-dim count mismatch should have been rejected"
  | .error e =>
      unless e == .advancingDimCountMismatch 0 1 2 do
        throwError s!"advancingDimCountMismatch: wrong error {repr e}"

-- advancingSizeMismatch
run_cmd do
  match checkScanPlan outerSigs
      { linearScan with historyExtents := #[5], baseBlock := emptyBlock, stepBlock := emptyBlock } with
  | .ok _ => throwError "advancing-size mismatch should have been rejected"
  | .error e =>
      unless e == .advancingSizeMismatch 0 0 5 3 do
        throwError s!"advancingSizeMismatch: wrong error {repr e}"

-- baseBlockContextNotEmpty
run_cmd do
  match checkScanPlan outerSigs
      { linearScan with baseBlock := { emptyBlock with contextShape := #[1] }, stepBlock := emptyBlock } with
  | .ok _ => throwError "nonempty base-block context should have been rejected"
  | .error e =>
      unless e == .baseBlockContextNotEmpty #[1] do
        throwError s!"baseBlockContextNotEmpty: wrong error {repr e}"

-- stepBlockContextMismatch
run_cmd do
  match checkScanPlan outerSigs
      { linearScan with baseBlock := emptyBlock, stepBlock := { emptyBlock with contextShape := #[9] } } with
  | .ok _ => throwError "mismatched step-block context should have been rejected"
  | .error e =>
      unless e == .stepBlockContextMismatch #[2] #[9] do
        throwError s!"stepBlockContextMismatch: wrong error {repr e}"

-- baseBlockError (propagated BlockError from checkPlanBlock, e.g. a duplicate output slot)
def brokenBaseBlock : RawPlanBlock := { baseBlock with outputs := #[0, 0] }

run_cmd do
  match checkScanPlan outerSigs { linearScan with baseBlock := brokenBaseBlock } with
  | .ok _ => throwError "a checkPlanBlock-invalid base block should have been rejected"
  | .error e =>
      unless e == .baseBlockError (.duplicateOutputSlot 0) do
        throwError s!"baseBlockError: wrong error {repr e}"

-- stepBlockError (propagated BlockError from checkPlanBlock, e.g. a duplicate output slot)
def brokenStepBlock : RawPlanBlock := { stepBlock with outputs := #[2, 2] }

run_cmd do
  match checkScanPlan outerSigs { linearScan with stepBlock := brokenStepBlock } with
  | .ok _ => throwError "a checkPlanBlock-invalid step block should have been rejected"
  | .error e =>
      unless e == .stepBlockError (.duplicateOutputSlot 2) do
        throwError s!"stepBlockError: wrong error {repr e}"

-- captureInputSlotOutOfRange
run_cmd do
  match checkScanPlan outerSigs
      { linearScan with baseCaptures := #[{ baseCaptureS0 with inputSlot := 99 }] } with
  | .ok _ => throwError "out-of-range capture input slot should have been rejected"
  | .error e =>
      unless e == .captureInputSlotOutOfRange true 0 99 do
        throwError s!"captureInputSlotOutOfRange: wrong error {repr e}"

-- duplicateCaptureInput
run_cmd do
  match checkScanPlan outerSigs { linearScan with baseCaptures := #[baseCaptureS0, baseCaptureS0] } with
  | .ok _ => throwError "duplicate capture input should have been rejected"
  | .error e =>
      unless e == .duplicateCaptureInput true 0 do
        throwError s!"duplicateCaptureInput: wrong error {repr e}"

-- blockInputNotCaptured
run_cmd do
  match checkScanPlan outerSigs { linearScan with baseCaptures := #[] } with
  | .ok _ => throwError "an uncaptured block input should have been rejected"
  | .error e =>
      unless e == .blockInputNotCaptured true 0 do
        throwError s!"blockInputNotCaptured: wrong error {repr e}"

-- stateCaptureInBaseBlock
run_cmd do
  match checkScanPlan outerSigs
      { linearScan with baseCaptures := #[{ baseCaptureS0 with source := .state 0 }] } with
  | .ok _ => throwError "a state capture in the base block should have been rejected"
  | .error e =>
      unless e == .stateCaptureInBaseBlock 0 do
        throwError s!"stateCaptureInBaseBlock: wrong error {repr e}"

-- captureStateIndexOutOfRange
run_cmd do
  match checkScanPlan outerSigs
      { linearScan with stepCaptures := #[stepCaptureX, { stepCaptureS with source := .state 99 }] } with
  | .ok _ => throwError "out-of-range capture state index should have been rejected"
  | .error e =>
      unless e == .captureStateIndexOutOfRange false 1 99 1 do
        throwError s!"captureStateIndexOutOfRange: wrong error {repr e}"

-- captureExternalSlotOutOfRange
run_cmd do
  match checkScanPlan outerSigs
      { linearScan with baseCaptures := #[{ baseCaptureS0 with source := .external 99 }] } with
  | .ok _ => throwError "out-of-range capture external slot should have been rejected"
  | .error e =>
      unless e == .captureExternalSlotOutOfRange true 0 99 3 do
        throwError s!"captureExternalSlotOutOfRange: wrong error {repr e}"

-- captureSignatureMismatch
run_cmd do
  match checkScanPlan outerSigs
      { linearScan with baseCaptures := #[{ baseCaptureS0 with source := .external 1 }] } with
  | .ok _ => throwError "a mismatched capture signature should have been rejected"
  | .error e =>
      unless e == .captureSignatureMismatch true 0
          { shape := #[3], dtype := .f64 } { shape := #[], dtype := .f64 } do
        throwError s!"captureSignatureMismatch: wrong error {repr e}"

-- writeStateIndexOutOfRange
run_cmd do
  match checkScanPlan outerSigs { linearScan with baseWrites := #[{ baseWriteS with stateIndex := 99 }] } with
  | .ok _ => throwError "out-of-range write state index should have been rejected"
  | .error e =>
      unless e == .writeStateIndexOutOfRange true 0 99 1 do
        throwError s!"writeStateIndexOutOfRange: wrong error {repr e}"

-- writeSourceNotBlockOutput
run_cmd do
  match checkScanPlan outerSigs { linearScan with baseWrites := #[{ baseWriteS with outputSlot := 5 }] } with
  | .ok _ => throwError "a write from a non-output slot should have been rejected"
  | .error e =>
      unless e == .writeSourceNotBlockOutput true 0 5 do
        throwError s!"writeSourceNotBlockOutput: wrong error {repr e}"

-- blockOutputNotWritten
run_cmd do
  match checkScanPlan outerSigs { linearScan with baseWrites := #[] } with
  | .ok _ => throwError "an unwritten block output should have been rejected"
  | .error e =>
      unless e == .blockOutputNotWritten true 0 do
        throwError s!"blockOutputNotWritten: wrong error {repr e}"

-- duplicateWriteForOutput
run_cmd do
  match checkScanPlan outerSigs { linearScan with baseWrites := #[baseWriteS, baseWriteS] } with
  | .ok _ => throwError "two writes to the same output should have been rejected"
  | .error e =>
      unless e == .duplicateWriteForOutput true 0 0 1 do
        throwError s!"duplicateWriteForOutput: wrong error {repr e}"

/-! ### A second base output, for `baseWritesOverlap`

`baseBlockExtra` gives the base block a second scalar output (`slot 1`) that is a trivial identity
copy of its sole input, purely so two DISTINCT base writes can both target the same state. -/

def baseSigsExtra : Array TensorSignature :=
  #[{ shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 }]

def baseIdRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[], bias := #[] }, sourceShape := #[], oobPolicy := .zeroPad }

def baseIdTerm : TermPlan :=
  { iterationShape := #[], contextPos := #[], outputPos := #[], reductionPos := #[], factors := #[baseIdRead] }

def baseIdAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[], terms := #[baseIdTerm]
  , algebra := admittedAlgebra }

def baseBlockExtra : RawPlanBlock :=
  { contextShape := #[], tensorSigs := baseSigsExtra, inputs := #[0], assignments := #[baseIdAssign]
  , outputs := #[0, 1] }

def overlapWrite1 : StateWriteMap :=
  { outputSlot := 1, stateIndex := 0, map := { coeffs := #[#[]], bias := #[0] } }

-- baseWritesOverlap
run_cmd do
  match checkScanPlan outerSigs
      { linearScan with baseBlock := baseBlockExtra, baseWrites := #[baseWriteS, overlapWrite1] } with
  | .ok _ => throwError "two overlapping base writes to the same state should have been rejected"
  | .error e =>
      unless e == .baseWritesOverlap 0 0 1 do
        throwError s!"baseWritesOverlap: wrong error {repr e}"

-- captureTargetsNonInput (a valid, non-input slot of `baseBlockExtra` wrongly captured)
run_cmd do
  let nonInputCaptureScan := { linearScan with
    baseBlock := baseBlockExtra,
    baseCaptures := #[{ baseCaptureS0 with inputSlot := 1 }],
    baseWrites := #[baseWriteS, overlapWrite1] }
  match checkScanPlan outerSigs nonInputCaptureScan with
  | .ok _ => throwError "a capture targeting a non-input slot should have been rejected"
  | .error e =>
      unless e == .captureTargetsNonInput true 1 do
        throwError s!"captureTargetsNonInput: wrong error {repr e}"

/-! ### A second persistent state, for `noBaseWriteForState`/`noStepWriteForState`

`outerSigsTwoStates` adds a fourth outer slot `U` (shape `[3]`) for a second, independent 1-D
state sharing the same scan axis. -/

def outerSigsTwoStates : Array TensorSignature := outerSigs ++ #[{ shape := #[3], dtype := .f64 }]

def stateU : StateSlot := { destSlot := 3, advancingDims := #[0], materialization := .completeHistory }

-- noBaseWriteForState: state U has neither a base nor a step write; the base check fires first.
run_cmd do
  match checkScanPlan outerSigsTwoStates { linearScan with states := #[stateS, stateU] } with
  | .ok _ => throwError "a state with no base write should have been rejected"
  | .error e =>
      unless e == .noBaseWriteForState 1 do
        throwError s!"noBaseWriteForState: wrong error {repr e}"

def stateUBaseWrite : StateWriteMap :=
  { outputSlot := 1, stateIndex := 1, map := { coeffs := #[#[]], bias := #[0] } }

-- noStepWriteForState: state U now has a base write but still no step write.
run_cmd do
  let noStepWriteScan := { linearScan with
    states := #[stateS, stateU], baseBlock := baseBlockExtra,
    baseWrites := #[baseWriteS, stateUBaseWrite] }
  match checkScanPlan outerSigsTwoStates noStepWriteScan with
  | .ok _ => throwError "a state with no step write should have been rejected"
  | .error e =>
      unless e == .noStepWriteForState 1 do
        throwError s!"noStepWriteForState: wrong error {repr e}"

/-! ### A second step output, for `multipleStepWritesForState`

`stepBlockExtra` gives the step block a second scalar output (`slot 3`) reusing `termX`'s read of
`X[l]`, so a second, independently-valid step write can also target state 0. -/

def stepExtraAssign : AssignPlan :=
  { contextShape := #[2], destinationSlot := 3, outputShape := #[], terms := #[termX]
  , algebra := admittedAlgebra }

def stepBlockExtra : RawPlanBlock :=
  { stepBlock with
    tensorSigs := stepBlock.tensorSigs ++ #[{ shape := #[], dtype := .f64 }],
    assignments := stepBlock.assignments ++ #[stepExtraAssign],
    outputs := #[2, 3] }

def stepWriteExtra : StateWriteMap :=
  { outputSlot := 3, stateIndex := 0, map := { coeffs := #[#[1]], bias := #[1] } }

-- multipleStepWritesForState
run_cmd do
  match checkScanPlan outerSigs
      { linearScan with stepBlock := stepBlockExtra, stepWrites := #[stepWriteS, stepWriteExtra] } with
  | .ok _ => throwError "two step writes to the same state should have been rejected"
  | .error e =>
      unless e == .multipleStepWritesForState 0 0 1 do
        throwError s!"multipleStepWritesForState: wrong error {repr e}"

/-! ## Part 4: Task 2 — causality certificate

Four fixtures reproducing the brief's worked causality table: a deep-history accept (mirrors F0's
own `G[l+1] := G[l-2]` fixture in `test/Eval/ScanTest.lean`, same axis size 5), the Jacobi/
Gauss-Seidel snapshot-safety discriminator's unsafe constant read (F0's `A[.const 1]`) now rejected
at CHECK time instead of silently misevaluated, a look-ahead-bias rejection, and a non-advancing-
dimension exemption (confirming the certificate does not over-reach into ordinary elementwise
reads). -/

-- Deep-history scan: one state G (shape [5]), advancing dim 0. Base: G[0] := G0 (= 5). Step:
-- G[l+1] := G[l-2] (coeffs=#[1], bias=#[-2] at G's own dimension 0).
def outerSigsDeepHistory : Array TensorSignature :=
  #[{ shape := #[], dtype := .f64 }, { shape := #[5], dtype := .f64 }]

def stateG : StateSlot := { destSlot := 1, advancingDims := #[0], materialization := .completeHistory }

def baseBlockG : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[], dtype := .f64 }]
  , inputs := #[0], assignments := #[], outputs := #[0] }

def baseCaptureG0 : BlockCapture := { inputSlot := 0, source := .external 0 }

def baseWriteG : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[]], bias := #[0] } }

-- Step block: reads a snapshot of G at l-2 (deep history), one scalar output.
def stepReadG : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[-2] }, sourceShape := #[5], oobPolicy := .zeroPad }

def termG : TermPlan :=
  { iterationShape := #[4], contextPos := #[0], outputPos := #[], reductionPos := #[], factors := #[stepReadG] }

def stepAssignG : AssignPlan :=
  { contextShape := #[4], destinationSlot := 1, outputShape := #[], terms := #[termG]
  , algebra := admittedAlgebra }

def stepBlockG : RawPlanBlock :=
  { contextShape := #[4]
  , tensorSigs := #[{ shape := #[5], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0], assignments := #[stepAssignG], outputs := #[1] }

def stepCaptureG : BlockCapture := { inputSlot := 0, source := .state 0 }

def stepWriteG : StateWriteMap :=
  { outputSlot := 1, stateIndex := 0, map := { coeffs := #[#[1]], bias := #[1] } }

def deepHistoryScan : RawScanPlan :=
  { states := #[stateG]
  , baseBlock := baseBlockG, baseCaptures := #[baseCaptureG0], baseWrites := #[baseWriteG]
  , stepBlock := stepBlockG, stepCaptures := #[stepCaptureG], stepWrites := #[stepWriteG]
  , historyExtents := #[5]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

-- Accept: the deep-history read (coeffs=#[1], bias=#[-2]) is causal — a single unit coefficient at
-- the read's own scan-context position, with non-positive bias.
run_cmd do
  match checkScanPlan outerSigsDeepHistory deepHistoryScan with
  | .error e => throwError s!"checkScanPlan rejected the deep-history scan: {repr e}"
  | .ok _checked => pure ()

-- Reject: the Jacobi/Gauss-Seidel discriminator's unsafe read (F0 Task 3's `B[l+1] := A[.const 1]`)
-- reproduced here as a constant read of G's own history, ignoring the loop axis entirely —
-- coeffs=#[0], bias=#[1]. The legacy evaluator's `readsIterAhead`-style syntactic check only
-- matches a positive `.shift`, so it does NOT catch this; `stateReadCausal` does, because the
-- read's sole row then has zero nonzero coefficients.
def constReadG : ReadPlan := { stepReadG with map := { coeffs := #[#[0]], bias := #[1] } }
def termConstG : TermPlan := { termG with factors := #[constReadG] }
def stepAssignConstG : AssignPlan := { stepAssignG with terms := #[termConstG] }
def stepBlockConstG : RawPlanBlock := { stepBlockG with assignments := #[stepAssignConstG] }

run_cmd do
  match checkScanPlan outerSigsDeepHistory { deepHistoryScan with stepBlock := stepBlockConstG } with
  | .ok _ => throwError "a constant (Jacobi-style unsafe) state read should have been rejected"
  | .error e => unless e == .causalityFailure 0 0 0 do
      throwError s!"causalityFailure (constant read): wrong error {repr e}"

-- Reject: a look-ahead-shaped read, coeffs=#[1] bias=#[1] (reads G[l+1] instead of G[l-2] or
-- G[l]) — the same single-unit-coefficient row shape as a causal advancing read, but with a
-- positive bias.
def lookAheadReadG : ReadPlan := { stepReadG with map := { coeffs := #[#[1]], bias := #[1] } }
def termLookAheadG : TermPlan := { termG with factors := #[lookAheadReadG] }
def stepAssignLookAheadG : AssignPlan := { stepAssignG with terms := #[termLookAheadG] }
def stepBlockLookAheadG : RawPlanBlock := { stepBlockG with assignments := #[stepAssignLookAheadG] }

run_cmd do
  match checkScanPlan outerSigsDeepHistory { deepHistoryScan with stepBlock := stepBlockLookAheadG } with
  | .ok _ => throwError "a look-ahead-shaped state read should have been rejected"
  | .error e => unless e == .causalityFailure 0 0 0 do
      throwError s!"causalityFailure (look-ahead read): wrong error {repr e}"

/-! ### Non-advancing dimension exemption

A second, independent 2-D state `Gj` (dim0 = `j`, a plain non-advancing elementwise axis, size 2;
dim1 = `l`, the advancing axis, size 3) confirms `stateReadCausal` genuinely ignores non-advancing
rows: the `j` row's affine map is mutated to something arbitrary and non-canonical (`coeffs=#[7,
-3], bias=42` — not a recognized `.free`/`.pinned`/`.advancing` write-row shape at all, and not
even a plausible read of `j`) while the `l` row stays an ordinary causal predecessor read, and
`checkScanPlan` still accepts the scan — proving the certificate checks only `advancingDims`, not
every state dimension. -/

def outerSigsGj : Array TensorSignature :=
  #[{ shape := #[2], dtype := .f64 }, { shape := #[2, 3], dtype := .f64 }]

def stateGj : StateSlot := { destSlot := 1, advancingDims := #[1], materialization := .completeHistory }

def baseBlockGj : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[2], dtype := .f64 }]
  , inputs := #[0], assignments := #[], outputs := #[0] }

def baseCaptureG0j : BlockCapture := { inputSlot := 0, source := .external 0 }

-- Gj[j, 0] := G0j[j] — j free, l pinned to 0 (touches the lower boundary).
def baseWriteGj : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[1], #[]], bias := #[0, 0] } }

def stepCaptureGj : BlockCapture := { inputSlot := 0, source := .state 0 }

-- Canonical read: Gj[j, l] (elementwise-j, ordinary predecessor-l) — row0 (j, non-advancing) is a
-- plain free projection; row1 (l, advancing) is causal.
def readGjCanonical : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[0, 1], #[1, 0]], bias := #[0, 0] }
  , sourceShape := #[2, 3], oobPolicy := .zeroPad }

def termGj : TermPlan :=
  { iterationShape := #[2, 2], contextPos := #[0], outputPos := #[1], reductionPos := #[]
  , factors := #[readGjCanonical] }

def stepAssignGj : AssignPlan :=
  { contextShape := #[2], destinationSlot := 1, outputShape := #[2], terms := #[termGj]
  , algebra := admittedAlgebra }

def stepBlockGj : RawPlanBlock :=
  { contextShape := #[2]
  , tensorSigs := #[{ shape := #[2, 3], dtype := .f64 }, { shape := #[2], dtype := .f64 }]
  , inputs := #[0], assignments := #[stepAssignGj], outputs := #[1] }

-- Gj[j, l+1] := <expr> — j free (output position 0), l advancing (context position 0).
def stepWriteGj : StateWriteMap :=
  { outputSlot := 1, stateIndex := 0, map := { coeffs := #[#[0, 1], #[1, 0]], bias := #[0, 1] } }

def nonAdvancingScan : RawScanPlan :=
  { states := #[stateGj]
  , baseBlock := baseBlockGj, baseCaptures := #[baseCaptureG0j], baseWrites := #[baseWriteGj]
  , stepBlock := stepBlockGj, stepCaptures := #[stepCaptureGj], stepWrites := #[stepWriteGj]
  , historyExtents := #[3]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

-- Accept (canonical): both rows well-behaved.
run_cmd do
  match checkScanPlan outerSigsGj nonAdvancingScan with
  | .error e => throwError s!"checkScanPlan rejected the canonical non-advancing-read scan: {repr e}"
  | .ok _checked => pure ()

-- Mutation: replace ONLY the non-advancing (j) row with an arbitrary, non-canonical affine map.
-- `checkScanPlan` must still accept the scan, since `j` is not an advancing dimension of `Gj` and
-- so carries no causality obligation at all.
def readGjWild : ReadPlan :=
  { readGjCanonical with
    map := { coeffs := readGjCanonical.map.coeffs.set! 0 #[7, -3]
           , bias := readGjCanonical.map.bias.set! 0 42 } }

def termGjWild : TermPlan := { termGj with factors := #[readGjWild] }
def stepAssignGjWild : AssignPlan := { stepAssignGj with terms := #[termGjWild] }
def stepBlockGjWild : RawPlanBlock := { stepBlockGj with assignments := #[stepAssignGjWild] }

run_cmd do
  match checkScanPlan outerSigsGj { nonAdvancingScan with stepBlock := stepBlockGjWild } with
  | .error e =>
      throwError s!"checkScanPlan rejected a scan whose only irregularity is a non-advancing \
dimension's read — the causality certificate must not check non-advancing rows: {repr e}"
  | .ok _checked => pure ()

end LeanNCD.Eval.Plan.ScanTest
