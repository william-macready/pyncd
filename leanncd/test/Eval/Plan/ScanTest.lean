-- leanncd/test/Eval/Plan/ScanTest.lean
import LeanNCD.Eval.Plan.Scan

/-!
# Wave F F3 Task 1: write-geometry recognizer + `checkScanPlan` structural-half tests

Four families:

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
4. (Task 3) `runDenseScan` execution: six hand-computed fixtures (linear self-recurrence, deep
   history, extent-one, coupled `G`/`H`, face-plus-point-override multi-base-write, asymmetric `2×3`
   rectangular) each asserted against a real numeric target, plus three §11.4 mutations against
   hand-modified worker copies (reversed rank order, decremented step-write bias, stale state
   capture) — see Parts 5-6 below.
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

/-! ## Part 5: Task 3 — `runDenseScan` fixtures and mutation coverage

Six hand-computed fixtures, each asserted directly against `runDenseScan`'s output (not just
`checkScanPlan`'s acceptance). Fixture 1 reuses `linearScan`/`outerSigs`/`stateS` verbatim (Part 2);
Fixture 2 reuses `deepHistoryScan`/`outerSigsDeepHistory`/`stateG` verbatim (Part 4). Fixtures 3-6 are
new `RawScanPlan`s built by the same construction pattern.

**A genuine gap found and fixed while building Fixtures 5/6, not a construction bug**: the first draft
of `commitWrite` (verified only against Fixture 1's fully-pinned/fully-advancing writes) applied
`applyAffine w.map iter` with `iter := []` for every base write and read only `blockStore.getD
w.outputSlot {...}.data.getD 0 0.0` (element 0) — so a base write with a genuine FREE output position
(e.g. a row-face write `dp[0, c] := ROWFACE[c]`) always resolved to one coordinate (its bias
components alone) from one source element, silently dropping every other free-axis value. Confirmed
empirically before any fix: a direct construction of F0's face-write fixture through the ORIGINAL
`runDenseScan` produced `#[0,0,1,1]`, not `#[0,1,1,1]` — `dp[0,1]` (which should be `ROWFACE[1] = 1`)
was never written. `checkScanPlan`'s `baseWriteRowsOk` structurally ACCEPTS free-position base writes
(Part 1's own `faceWrite` fixture) — the gap was in the worker, not the checker. `commitWrite` now
iterates `allCoords out.shape` and commits every element (see `Scan.lean`'s doc comment on
`commitWrite`), reducing to the original single-coordinate behavior exactly when the output is
scalar (`allCoords [] = [[]]`, one iteration). Fixtures 5 and 6 below use GENUINE free-position base
writes (`faceWrite` from Part 1, and an analogous free-over-`r` write for the asymmetric case) —
matching F0's original fixture intent — now that the worker executes them correctly. -/

def outerStoreLinear : Array DenseTensor :=
  #[ { shape := [], data := #[1.0] }
   , { shape := [3], data := #[10.0, 20.0, 30.0] }
   , { shape := [3], data := Array.replicate 3 0.0 } ]

-- Fixture 1: linear self-recurrence. Verified: S = [1, 11, 31].
run_cmd do
  match checkScanPlan outerSigs linearScan with
  | .error e => throwError s!"F1 (linear scan) checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScan outerSigs checked outerStoreLinear with
      | .error e => throwError s!"F1 (linear scan) runDenseScan error: {repr e}"
      | .ok result =>
          let S := result.getD 2 { shape := [], data := #[] }
          unless DenseTensor.approxEq S { shape := [3], data := #[1.0, 11.0, 31.0] } do
            throwError s!"F1 (linear scan): wrong result {repr S.data}"

def outerStoreDeepHistory : Array DenseTensor :=
  #[ { shape := [], data := #[5.0] }
   , { shape := [5], data := Array.replicate 5 0.0 } ]

-- Fixture 2: deep history (k=2 look-back). Verified: G = [5, 0, 0, 5, 0].
run_cmd do
  match checkScanPlan outerSigsDeepHistory deepHistoryScan with
  | .error e => throwError s!"F2 (deep history) checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScan outerSigsDeepHistory checked outerStoreDeepHistory with
      | .error e => throwError s!"F2 (deep history) runDenseScan error: {repr e}"
      | .ok result =>
          let G := result.getD 1 { shape := [], data := #[] }
          unless DenseTensor.approxEq G { shape := [5], data := #[5.0, 0.0, 0.0, 5.0, 0.0] } do
            throwError s!"F2 (deep history): wrong result {repr G.data}"

/-! ### Fixture 3: extent one (base-only)

Axis size 1 ⇒ `stepExtents = #[0]` ⇒ `mixedRadixDomainSize = 0`: the step loop runs zero times, so
the state must equal exactly its base value. Reuses `baseBlock`'s generic scalar-passthrough shape
(Part 2) — no assignments needed, the captured input is already its own output. -/

def outerSigsExtentOne : Array TensorSignature :=
  #[{ shape := #[], dtype := .f64 }, { shape := #[1], dtype := .f64 }]

def stateSExtentOne : StateSlot :=
  { destSlot := 1, advancingDims := #[0], materialization := .completeHistory }

def baseCaptureS0ExtentOne : BlockCapture := { inputSlot := 0, source := .external 0 }
def baseWriteSExtentOne : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[]], bias := #[0] } }

def stepReadSExtentOne : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[1], oobPolicy := .zeroPad }
def termSExtentOne : TermPlan :=
  { iterationShape := #[0], contextPos := #[0], outputPos := #[], reductionPos := #[]
  , factors := #[stepReadSExtentOne] }
def stepAssignSExtentOne : AssignPlan :=
  { contextShape := #[0], destinationSlot := 1, outputShape := #[], terms := #[termSExtentOne]
  , algebra := admittedAlgebra }
def stepBlockExtentOne : RawPlanBlock :=
  { contextShape := #[0]
  , tensorSigs := #[{ shape := #[1], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0], assignments := #[stepAssignSExtentOne], outputs := #[1] }
def stepCaptureSExtentOne : BlockCapture := { inputSlot := 0, source := .state 0 }
def stepWriteSExtentOne : StateWriteMap :=
  { outputSlot := 1, stateIndex := 0, map := { coeffs := #[#[1]], bias := #[1] } }

def extentOneScan : RawScanPlan :=
  { states := #[stateSExtentOne]
  , baseBlock := baseBlock, baseCaptures := #[baseCaptureS0ExtentOne], baseWrites := #[baseWriteSExtentOne]
  , stepBlock := stepBlockExtentOne, stepCaptures := #[stepCaptureSExtentOne]
  , stepWrites := #[stepWriteSExtentOne]
  , historyExtents := #[1]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

def outerStoreExtentOne : Array DenseTensor :=
  #[ { shape := [], data := #[7.0] }, { shape := [1], data := #[0.0] } ]

-- Fixture 3: extent one. Verified: S = [7].
run_cmd do
  match checkScanPlan outerSigsExtentOne extentOneScan with
  | .error e => throwError s!"F3 (extent one) checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScan outerSigsExtentOne checked outerStoreExtentOne with
      | .error e => throwError s!"F3 (extent one) runDenseScan error: {repr e}"
      | .ok result =>
          let S := result.getD 1 { shape := [], data := #[] }
          unless DenseTensor.approxEq S { shape := [1], data := #[7.0] } do
            throwError s!"F3 (extent one): wrong result {repr S.data}"

/-! ### Fixture 4: coupled `G`/`H` (Fibonacci-shaped)

The first real exercise of the multi-state path: TWO `StateSlot`s, a step block with TWO state
captures and TWO state-result outputs, and TWO `StateWriteMap`s in `stepWrites` (`stateIndex := 0`
for `G`, `stateIndex := 1` for `H`). `G[0] := C; H[0] := C; G[l+1] := G[l] + H[l]; H[l+1] := G[l]`. -/

def outerSigsCoupled : Array TensorSignature :=
  #[{ shape := #[], dtype := .f64 }, { shape := #[4], dtype := .f64 }, { shape := #[4], dtype := .f64 }]

def stateGCoupled : StateSlot := { destSlot := 1, advancingDims := #[0], materialization := .completeHistory }
def stateHCoupled : StateSlot := { destSlot := 2, advancingDims := #[0], materialization := .completeHistory }

-- Base block: one captured input C, one assignment producing a second (identical) output, so G's
-- and H's base writes can each target a DISTINCT block output slot (every write's outputSlot must be
-- distinct — `duplicateWriteForOutput`).
def baseIdReadCoupled : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[], bias := #[] }, sourceShape := #[], oobPolicy := .zeroPad }
def baseIdTermCoupled : TermPlan :=
  { iterationShape := #[], contextPos := #[], outputPos := #[], reductionPos := #[]
  , factors := #[baseIdReadCoupled] }
def baseIdAssignCoupled : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[], terms := #[baseIdTermCoupled]
  , algebra := admittedAlgebra }
def baseBlockCoupled : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0], assignments := #[baseIdAssignCoupled], outputs := #[0, 1] }

def baseCaptureCCoupled : BlockCapture := { inputSlot := 0, source := .external 0 }
def baseWriteGCoupled : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[]], bias := #[0] } }
def baseWriteHCoupled : StateWriteMap :=
  { outputSlot := 1, stateIndex := 1, map := { coeffs := #[#[]], bias := #[0] } }

def readGForGCoupled : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[4], oobPolicy := .zeroPad }
def readHForGCoupled : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[4], oobPolicy := .zeroPad }
def readGForHCoupled : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[4], oobPolicy := .zeroPad }

def termGGCoupled : TermPlan :=
  { iterationShape := #[3], contextPos := #[0], outputPos := #[], reductionPos := #[]
  , factors := #[readGForGCoupled] }
def termHGCoupled : TermPlan :=
  { iterationShape := #[3], contextPos := #[0], outputPos := #[], reductionPos := #[]
  , factors := #[readHForGCoupled] }
def termGHCoupled : TermPlan :=
  { iterationShape := #[3], contextPos := #[0], outputPos := #[], reductionPos := #[]
  , factors := #[readGForHCoupled] }

def stepAssignGCoupled : AssignPlan :=
  { contextShape := #[3], destinationSlot := 2, outputShape := #[], terms := #[termGGCoupled, termHGCoupled]
  , algebra := admittedAlgebra }
def stepAssignHCoupled : AssignPlan :=
  { contextShape := #[3], destinationSlot := 3, outputShape := #[], terms := #[termGHCoupled]
  , algebra := admittedAlgebra }

def stepBlockCoupled : RawPlanBlock :=
  { contextShape := #[3]
  , tensorSigs := #[{ shape := #[4], dtype := .f64 }, { shape := #[4], dtype := .f64 }
                  , { shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0, 1], assignments := #[stepAssignGCoupled, stepAssignHCoupled], outputs := #[2, 3] }

def stepCaptureGCoupled : BlockCapture := { inputSlot := 0, source := .state 0 }
def stepCaptureHCoupled : BlockCapture := { inputSlot := 1, source := .state 1 }

def stepWriteGCoupled : StateWriteMap :=
  { outputSlot := 2, stateIndex := 0, map := { coeffs := #[#[1]], bias := #[1] } }
def stepWriteHCoupled : StateWriteMap :=
  { outputSlot := 3, stateIndex := 1, map := { coeffs := #[#[1]], bias := #[1] } }

def coupledScan : RawScanPlan :=
  { states := #[stateGCoupled, stateHCoupled]
  , baseBlock := baseBlockCoupled, baseCaptures := #[baseCaptureCCoupled]
  , baseWrites := #[baseWriteGCoupled, baseWriteHCoupled]
  , stepBlock := stepBlockCoupled, stepCaptures := #[stepCaptureGCoupled, stepCaptureHCoupled]
  , stepWrites := #[stepWriteGCoupled, stepWriteHCoupled]
  , historyExtents := #[4]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

def outerStoreCoupled : Array DenseTensor :=
  #[ { shape := [], data := #[1.0] }
   , { shape := [4], data := Array.replicate 4 0.0 }
   , { shape := [4], data := Array.replicate 4 0.0 } ]

-- Fixture 4: coupled G/H. Verified: G = [1,2,3,5], H = [1,1,2,3].
run_cmd do
  match checkScanPlan outerSigsCoupled coupledScan with
  | .error e => throwError s!"F4 (coupled) checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScan outerSigsCoupled checked outerStoreCoupled with
      | .error e => throwError s!"F4 (coupled) runDenseScan error: {repr e}"
      | .ok result =>
          let G := result.getD 1 { shape := [], data := #[] }
          let H := result.getD 2 { shape := [], data := #[] }
          unless DenseTensor.approxEq G { shape := [4], data := #[1.0, 2.0, 3.0, 5.0] } do
            throwError s!"F4 (coupled): wrong G {repr G.data}"
          unless DenseTensor.approxEq H { shape := [4], data := #[1.0, 1.0, 2.0, 3.0] } do
            throwError s!"F4 (coupled): wrong H {repr H.data}"

/-! ### Fixture 5: face-plus-point-override multi-base-write

F0's `dp` fixture, unmodified: a row-0 face write `dp[0, c] := ROWFACE[c]` (free over `c`) plus a
point override `dp[1,0] := ONE`. Reuses Part 1's `faceWrite`/`pointWrite` directly (same
`outputSlot`s, same geometry, already independently verified structurally-accepted by
`baseWriteRowsOk`/`writesCollide` in Part 1) — the base block's own outputs are slot 0 (ROWFACE,
passed through whole) and slot 1 (ONE, passed through whole), matching `faceWrite.outputSlot = 0` /
`pointWrite.outputSlot = 1` exactly, so no assignments are needed (both inputs are already their own
outputs, the same "input doubles as output" shape `baseBlock`/`baseBlockCoupled` use elsewhere).
`stepWriteDpMulti` reuses Part 1's `dpStepWrite`'s map (only the outputSlot differs, since this
scan's own step block numbers its output differently). -/

def outerSigsMultiBase : Array TensorSignature :=
  #[{ shape := #[2], dtype := .f64 }, { shape := #[], dtype := .f64 }
  , { shape := #[2,2], dtype := .f64 }, { shape := #[2,2], dtype := .f64 }]

def stateDpMulti : StateSlot :=
  { destSlot := 3, advancingDims := #[0,1], materialization := .completeHistory }

def baseBlockMultiBase : RawPlanBlock :=
  { contextShape := #[]
  , tensorSigs := #[{ shape := #[2], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0, 1], assignments := #[], outputs := #[0, 1] }

def baseCaptureRowfaceMulti : BlockCapture := { inputSlot := 0, source := .external 0 }
def baseCaptureOneMulti : BlockCapture := { inputSlot := 1, source := .external 1 }

def stepReadDpMulti : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1,0], #[0,1]], bias := #[0,0] }, sourceShape := #[2,2]
  , oobPolicy := .zeroPad }
def stepReadTMulti : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1,0], #[0,1]], bias := #[0,0] }, sourceShape := #[2,2]
  , oobPolicy := .zeroPad }
def termDpReadMulti : TermPlan :=
  { iterationShape := #[1,1], contextPos := #[0,1], outputPos := #[], reductionPos := #[]
  , factors := #[stepReadDpMulti] }
def termTReadMulti : TermPlan :=
  { iterationShape := #[1,1], contextPos := #[0,1], outputPos := #[], reductionPos := #[]
  , factors := #[stepReadTMulti] }
def stepAssignDpMulti : AssignPlan :=
  { contextShape := #[1,1], destinationSlot := 2, outputShape := #[], terms := #[termDpReadMulti, termTReadMulti]
  , algebra := admittedAlgebra }
def stepBlockMultiBase : RawPlanBlock :=
  { contextShape := #[1,1]
  , tensorSigs := #[{ shape := #[2,2], dtype := .f64 }, { shape := #[2,2], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0, 1], assignments := #[stepAssignDpMulti], outputs := #[2] }
def stepCaptureDpMulti : BlockCapture := { inputSlot := 0, source := .state 0 }
def stepCaptureTMulti : BlockCapture := { inputSlot := 1, source := .external 2 }
def stepWriteDpMulti : StateWriteMap := { dpStepWrite with outputSlot := 2 }

def multiBaseScan : RawScanPlan :=
  { states := #[stateDpMulti]
  , baseBlock := baseBlockMultiBase, baseCaptures := #[baseCaptureRowfaceMulti, baseCaptureOneMulti]
  , baseWrites := #[faceWrite, pointWrite]
  , stepBlock := stepBlockMultiBase, stepCaptures := #[stepCaptureDpMulti, stepCaptureTMulti]
  , stepWrites := #[stepWriteDpMulti]
  , historyExtents := #[2,2]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

def outerStoreMultiBase : Array DenseTensor :=
  #[ { shape := [2], data := #[0.0, 1.0] }
   , { shape := [], data := #[1.0] }
   , { shape := [2,2], data := #[1.0,1.0,1.0,1.0] }
   , { shape := [2,2], data := Array.replicate 4 0.0 } ]

/-! #### `writeFreeExtentMismatch`: a free face WIDER than the state's own dimension

The final whole-branch review's Critical finding, reproduced on this fixture. Before
`freeExtentsAgree` existed, `checkWrites` compared only the free positions' RANK/ORDER against the
block output (`baseWriteRowsOk`'s `outputShapeSize` is `shape.size`, a COUNT), never their SIZE — so
declaring `ROWFACE` as shape `[5]` while `dp`'s own free dimension is size `2` was accepted, and
`runDenseScan` then committed `ROWFACE[2..4]` through `flatIndex` into cells belonging to other rows
(or past the end of `dp.data` entirely).

Only two fields differ from `multiBaseScan`: outer slot 0 and the base block's input-0 signature
both become `[5]` (they must move together, or `captureSignatureMismatch` fires first and the
extent check is never reached). `dp` itself is untouched at `[2,2]`, so `faceWrite`'s free row —
state dim 1, size `2` — now disagrees with the block output's size `5` at free position `0`. -/

def outerSigsFreeExtentMismatch : Array TensorSignature :=
  outerSigsMultiBase.set! 0 { shape := #[5], dtype := .f64 }

def baseBlockFreeExtentMismatch : RawPlanBlock :=
  { baseBlockMultiBase with
    tensorSigs := baseBlockMultiBase.tensorSigs.set! 0 { shape := #[5], dtype := .f64 } }

def freeExtentMismatchScan : RawScanPlan :=
  { multiBaseScan with baseBlock := baseBlockFreeExtentMismatch }

-- The predicate itself, on the exact rows involved: `faceRows`'s free row is state dim 1.
#guard freeExtentsAgree #[2,2] #[2] faceRows == true
#guard freeExtentsAgree #[2,2] #[5] faceRows == false

-- writeFreeExtentMismatch: accepted before the fix (`checkScanPlan` returned `.ok`, and
-- `runDenseScan` then wrote out of region), rejected now.
run_cmd do
  match checkScanPlan outerSigsFreeExtentMismatch freeExtentMismatchScan with
  | .ok _ =>
      throwError "a base write whose free face is WIDER than the state's own dimension should have \
been rejected — this is the final-review Critical finding"
  | .error e =>
      unless e == .writeFreeExtentMismatch true 0 0 #[2,2] #[5] do
        throwError s!"writeFreeExtentMismatch: wrong error {repr e}"

/-! #### `writePinnedLiteralOutOfRange`: a base write PINNED outside the state's own dimension

The sibling of the finding above, same failure class, found while documenting that fix and
independently reproduced by a second reviewer. Geometry admission recognizes a row as `.pinned lit`
without ever inspecting `lit`'s VALUE: `baseWriteRowsOk` requires only that SOME advancing dimension
be pinned to literal `0`, so with `dp`'s `advancingDims = #[0,1]`, `pointWrite`'s dim-1 `0` alone
satisfied that rule and left the dim-0 literal completely unconstrained. `dp[5, 0] := ONE` on a
`[2,2]` state passed `checkScanPlan`, and `commitWrite` then reached `Array.set!` out of range
(`lean_array_set_panic`, or a silent commit to the wrong cell).

One field differs from `multiBaseScan`: `pointWrite`'s dim-0 bias `1 -> 5`. Nothing else moves — the
write is still fully pinned (scalar output, no free rows), still admitted by `baseWriteRowsOk`, and
still non-colliding with `faceWrite` (row `5` vs row `0` are different literals), so the plan
reaches the new check with every earlier check passed. -/

def outOfRangePointWrite : StateWriteMap :=
  { pointWrite with map := { coeffs := #[#[], #[]], bias := #[5, 0] } }

def outOfRangePointRows : Array (Option WriteRowKind) := writeRowKinds 2 0 outOfRangePointWrite

-- Still admitted by the geometry rule — that is exactly why a separate value check is needed.
#guard baseWriteRowsOk #[0, 1] 0 outOfRangePointRows
#guard writesCollide faceRows outOfRangePointRows == false

-- The predicate itself, on the exact rows involved (`pointRows` is the real, in-range fixture).
#guard pinnedLiteralsInRange #[2,2] pointRows == true
#guard pinnedLiteralsInRange #[2,2] outOfRangePointRows == false
-- A NEGATIVE literal is out of range too (`Int.toNat` would silently clamp it to `0`).
#guard pinnedLiteralsInRange #[2,2] (writeRowKinds 2 0
  { pointWrite with map := { coeffs := #[#[], #[]], bias := #[-1, 0] } }) == false

def pinnedOutOfRangeScan : RawScanPlan :=
  { multiBaseScan with baseWrites := #[faceWrite, outOfRangePointWrite] }

-- writePinnedLiteralOutOfRange: accepted before the fix (`checkScanPlan` returned `.ok`, and
-- `runDenseScan` then panicked in `Array.set!`), rejected now. Locator is base write index 1
-- (`faceWrite` at index 0 passes first), state 0, whose shape is `#[2,2]`.
run_cmd do
  match checkScanPlan outerSigsMultiBase pinnedOutOfRangeScan with
  | .ok _ =>
      throwError "a base write PINNED outside the state's own dimension should have been rejected \
— this is the sibling of the final-review Critical free-extent finding"
  | .error e =>
      unless e == .writePinnedLiteralOutOfRange true 1 0 #[2,2] do
        throwError s!"writePinnedLiteralOutOfRange: wrong error {repr e}"

-- Fixture 5: face-plus-point-override multi-base-write. Verified: dp = [0,1,1,1] (row-major [2,2]).
run_cmd do
  match checkScanPlan outerSigsMultiBase multiBaseScan with
  | .error e => throwError s!"F5 (multi-base-write) checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScan outerSigsMultiBase checked outerStoreMultiBase with
      | .error e => throwError s!"F5 (multi-base-write) runDenseScan error: {repr e}"
      | .ok result =>
          let dp := result.getD 3 { shape := [], data := #[] }
          unless DenseTensor.approxEq dp { shape := [2,2], data := #[0.0, 1.0, 1.0, 1.0] } do
            throwError s!"F5 (multi-base-write): wrong result {repr dp.data}"

/-! ### Fixture 6: asymmetric rectangular `2×3`, all-axis `+1`

`historyExtents := #[2,3]` — two DIFFERENT per-axis extents (`r` size 2, `c` size 3) — so
`stepExtents = #[1,2]`. `G[r,0] := Z[r]` — a genuine free-over-`r` base write (row1/`c` pinned to
`0`) — matching F0's original fixture intent, now that `commitWrite` executes free positions
correctly. The base block passes `Z` straight through as its own output (no assignment needed, same
"input doubles as output" shape used throughout this file). -/

def outerSigsAsym : Array TensorSignature :=
  #[{ shape := #[2], dtype := .f64 }, { shape := #[2,3], dtype := .f64 }, { shape := #[2,3], dtype := .f64 }]

def stateGAsym : StateSlot := { destSlot := 2, advancingDims := #[0,1], materialization := .completeHistory }

def baseBlockAsym : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[2], dtype := .f64 }]
  , inputs := #[0], assignments := #[], outputs := #[0] }

def baseCaptureZAsym : BlockCapture := { inputSlot := 0, source := .external 0 }

-- G[r, 0] := Z[r] — r free (output position 0), c pinned to 0 (touches the lower boundary).
def baseWriteGFaceAsym : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[1], #[0]], bias := #[0, 0] } }

def stepReadGAsym : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1,0], #[0,1]], bias := #[0,0] }, sourceShape := #[2,3]
  , oobPolicy := .zeroPad }
def stepReadAAsym : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1,0], #[0,1]], bias := #[0,0] }, sourceShape := #[2,3]
  , oobPolicy := .zeroPad }
def termGAsym : TermPlan :=
  { iterationShape := #[1,2], contextPos := #[0,1], outputPos := #[], reductionPos := #[]
  , factors := #[stepReadGAsym] }
def termAAsym : TermPlan :=
  { iterationShape := #[1,2], contextPos := #[0,1], outputPos := #[], reductionPos := #[]
  , factors := #[stepReadAAsym] }
def stepAssignAsym : AssignPlan :=
  { contextShape := #[1,2], destinationSlot := 2, outputShape := #[], terms := #[termGAsym, termAAsym]
  , algebra := admittedAlgebra }
def stepBlockAsym : RawPlanBlock :=
  { contextShape := #[1,2]
  , tensorSigs := #[{ shape := #[2,3], dtype := .f64 }, { shape := #[2,3], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0, 1], assignments := #[stepAssignAsym], outputs := #[2] }
def stepCaptureGAsym : BlockCapture := { inputSlot := 0, source := .state 0 }
def stepCaptureAAsym : BlockCapture := { inputSlot := 1, source := .external 1 }
def stepWriteGAsym : StateWriteMap :=
  { outputSlot := 2, stateIndex := 0, map := { coeffs := #[#[1,0], #[0,1]], bias := #[1,1] } }

def asymScan : RawScanPlan :=
  { states := #[stateGAsym]
  , baseBlock := baseBlockAsym, baseCaptures := #[baseCaptureZAsym]
  , baseWrites := #[baseWriteGFaceAsym]
  , stepBlock := stepBlockAsym, stepCaptures := #[stepCaptureGAsym, stepCaptureAAsym]
  , stepWrites := #[stepWriteGAsym]
  , historyExtents := #[2,3]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

def outerStoreAsym : Array DenseTensor :=
  #[ { shape := [2], data := #[2.0, 5.0] }
   , { shape := [2,3], data := Array.replicate 6 1.0 }
   , { shape := [2,3], data := Array.replicate 6 0.0 } ]

-- Fixture 6: asymmetric 2x3. Verified: G = [2,0,0, 5,3,1] (row-major [2,3]).
run_cmd do
  match checkScanPlan outerSigsAsym asymScan with
  | .error e => throwError s!"F6 (asymmetric) checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScan outerSigsAsym checked outerStoreAsym with
      | .error e => throwError s!"F6 (asymmetric) runDenseScan error: {repr e}"
      | .ok result =>
          let G := result.getD 2 { shape := [], data := #[] }
          unless DenseTensor.approxEq G { shape := [2,3], data := #[2.0,0.0,0.0, 5.0,3.0,1.0] } do
            throwError s!"F6 (asymmetric): wrong result {repr G.data}"

/-! ## Part 6: Task 3 — §11.4 mutation coverage

Three mutations, each a hand-modified COPY of `runDenseScan` (never the shipped function itself),
each demonstrating that a specific piece of the worker's behavior is load-bearing rather than
incidental. `commitWrite` (Scan.lean) is `private`, so each copy commits writes through a local
`commitWriteLocal` rather than reaching across the module boundary.

⚠️ `commitWriteLocal` is NOT a faithful copy of `commitWrite`: it is the SCALAR-OUTPUT-ONLY
specialization, reading element `0` at the single coordinate `applyAffine w.map iter` — which is
exactly the pre-fix `commitWrite` bug Fixtures 5/6 found (a genuine free-position write must place
EVERY element of its output, iterating `allCoords out.shape`). It stays valid only because every
mutation fixture below (`coupledScan`, `deepHistoryScan`, `linearScan`) has scalar step outputs and
no free-position write, where the two agree by `allCoords [] = [[]]`. Any future mutation fixture
with a free-position write must copy the real `commitWrite` equation instead of reusing this. -/

def commitWriteLocal (target : DenseTensor) (w : StateWriteMap) (blockStore : Array DenseTensor)
    (iter : List Int) : DenseTensor :=
  let coord := (applyAffine w.map iter).map Int.toNat
  let v := (blockStore.getD w.outputSlot { shape := [], data := #[] }).data.getD 0 0.0
  { target with data := target.data.set! (flatIndex target.shape coord) v }

/-! ### Mutation A: reverse the mixed-radix rank order

Decode each rank `r` from `domainSize - 1 - r` instead of `r` directly, on the coupled fixture (the
richest ordering: state-to-state coupling makes traversal order visibly observable). If order were
NOT actually load-bearing (e.g. if some other invariant made the result order-independent), this
mutation would still reproduce `[1,2,3,5]`/`[1,1,2,3]` — it does not. -/

def reversedDomainRank (D : Array Nat) (r : Nat) : Nat := mixedRadixDomainSize D - 1 - r

def runDenseScanReversedOrder (sigs : Array TensorSignature) (c : CheckedScanPlan)
    (outerStore : Array DenseTensor) : Except PositionalInputError (Array DenseTensor) := do
  let raw := c.raw
  let mut states : Array DenseTensor := raw.states.map (fun st =>
    let sig := sigs.getD st.destSlot { shape := #[], dtype := .f64 }
    { shape := sig.shape.toList, data := Array.replicate (sig.shape.toList.foldl (· * ·) 1) 0.0 })
  let baseExternalInputs ← raw.baseCaptures.mapM (fun cap => match cap.source with
    | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
    | .state _ => throw (PositionalInputError.arityMismatch 0 0))
  let baseStore ← runDenseBlock c.checkedBase [] baseExternalInputs
  for w in raw.baseWrites do
    let target := states.getD w.stateIndex { shape := [], data := #[] }
    states := states.set! w.stateIndex (commitWriteLocal target w baseStore [])
  let domainSize := mixedRadixDomainSize c.stepExtents
  for r in [0 : domainSize] do
    -- MUTATION: decode from the reversed rank instead of `r` directly (was: `mixedRadixUnrank
    -- c.stepExtents r`).
    let q := mixedRadixUnrank c.stepExtents (reversedDomainRank c.stepExtents r)
    let oldStates := states
    let stepInputs ← raw.stepCaptures.mapM (fun cap => match cap.source with
      | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
      | .state si => pure (oldStates.getD si { shape := [], data := #[] }))
    let ctx : List Int := q.toList.map Int.ofNat
    let stepStore ← runDenseBlock c.checkedStep ctx stepInputs
    let mut nextStates := states
    for w in raw.stepWrites do
      let target := nextStates.getD w.stateIndex { shape := [], data := #[] }
      nextStates := nextStates.set! w.stateIndex (commitWriteLocal target w stepStore ctx)
    states := nextStates
  let mut result := outerStore
  for h : si in [0 : raw.states.size] do
    result := result.set! raw.states[si].destSlot (states.getD si { shape := [], data := #[] })
  return result

-- Mutated: reversed rank order on the coupled fixture gives G = [1,2,0,0], not the real [1,2,3,5] —
-- ranks 2,3 get processed as if they were ranks 0,1 (mapped through `reversedDomainRank`, domainSize
-- 3 ⇒ r=0↦2, r=1↦1, r=2↦0), so the writes destined for positions 2,3 never actually run in the
-- correct order and the last two Fibonacci steps are lost. Restored (Fixture 4 above, real
-- `runDenseScan`, real rank order): G = [1,2,3,5], H = [1,1,2,3] — correct.
run_cmd do
  match checkScanPlan outerSigsCoupled coupledScan with
  | .error e => throwError s!"MutA checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScanReversedOrder outerSigsCoupled checked outerStoreCoupled with
      | .error e => throwError s!"MutA runDenseScan error: {repr e}"
      | .ok result =>
          let G := result.getD 1 { shape := [], data := #[] }
          if DenseTensor.approxEq G { shape := [4], data := #[1.0,2.0,3.0,5.0] } then
            throwError s!"MutA: reversed rank order should NOT reproduce the correct G, got {repr G.data}"
          unless DenseTensor.approxEq G { shape := [4], data := #[1.0,2.0,0.0,0.0] } do
            throwError s!"MutA: expected the specific wrong value [1,2,0,0], got {repr G.data}"

/-! ### Mutation B: change one step-write's `+1` bias

`classifyWriteRow` (Scan.lean) only recognizes `bias == 1` for an advancing row, so mutating a
fixture's OWN write map to any other bias is rejected by `checkScanPlan` itself before ever reaching
`runDenseScan` (structurally unreachable, same reason Part 2's `lookAheadStepWrite` mutation is a
CHECK-time rejection, not a value mismatch). So this mutation targets the WORKER's commit arithmetic
instead: every step write's bias is decremented by 1 before committing (i.e. "commit to `q` instead
of `q+1`"), on the real, unmutated `deepHistoryScan` fixture — simulating a worker that got the
canonical `+1` advancing convention wrong, independent of what the checked plan declares. -/

def runDenseScanBadStepBias (sigs : Array TensorSignature) (c : CheckedScanPlan)
    (outerStore : Array DenseTensor) : Except PositionalInputError (Array DenseTensor) := do
  let raw := c.raw
  let mut states : Array DenseTensor := raw.states.map (fun st =>
    let sig := sigs.getD st.destSlot { shape := #[], dtype := .f64 }
    { shape := sig.shape.toList, data := Array.replicate (sig.shape.toList.foldl (· * ·) 1) 0.0 })
  let baseExternalInputs ← raw.baseCaptures.mapM (fun cap => match cap.source with
    | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
    | .state _ => throw (PositionalInputError.arityMismatch 0 0))
  let baseStore ← runDenseBlock c.checkedBase [] baseExternalInputs
  for w in raw.baseWrites do
    let target := states.getD w.stateIndex { shape := [], data := #[] }
    states := states.set! w.stateIndex (commitWriteLocal target w baseStore [])
  let domainSize := mixedRadixDomainSize c.stepExtents
  for r in [0 : domainSize] do
    let q := mixedRadixUnrank c.stepExtents r
    let oldStates := states
    let stepInputs ← raw.stepCaptures.mapM (fun cap => match cap.source with
      | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
      | .state si => pure (oldStates.getD si { shape := [], data := #[] }))
    let ctx : List Int := q.toList.map Int.ofNat
    let stepStore ← runDenseBlock c.checkedStep ctx stepInputs
    let mut nextStates := states
    for w in raw.stepWrites do
      let target := nextStates.getD w.stateIndex { shape := [], data := #[] }
      -- MUTATION: decrement every bias by 1 before applying the write map (was: `w.map` unchanged).
      let mutatedMap : AffineMap := { w.map with bias := w.map.bias.map (· - 1) }
      let coord := (applyAffine mutatedMap ctx).map Int.toNat
      let v := (stepStore.getD w.outputSlot { shape := [], data := #[] }).data.getD 0 0.0
      nextStates := nextStates.set! w.stateIndex
        { target with data := target.data.set! (flatIndex target.shape coord) v }
    states := nextStates
  let mut result := outerStore
  for h : si in [0 : raw.states.size] do
    result := result.set! raw.states[si].destSlot (states.getD si { shape := [], data := #[] })
  return result

-- Mutated: every step write now lands one position early (`q` instead of `q+1`), so `q=0`
-- overwrites the freshly-written base value at position 0 with the pre-step (zero) read, and every
-- later position inherits zeros the same way. Deep-history G collapses to all zeros: [0,0,0,0,0].
-- Restored (Fixture 2 above, real `runDenseScan`, real `+1` bias): G = [5,0,0,5,0] — correct.
run_cmd do
  match checkScanPlan outerSigsDeepHistory deepHistoryScan with
  | .error e => throwError s!"MutB checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScanBadStepBias outerSigsDeepHistory checked outerStoreDeepHistory with
      | .error e => throwError s!"MutB runDenseScan error: {repr e}"
      | .ok result =>
          let G := result.getD 1 { shape := [], data := #[] }
          if DenseTensor.approxEq G { shape := [5], data := #[5.0,0.0,0.0,5.0,0.0] } then
            throwError s!"MutB: bias-decremented worker should NOT reproduce the correct G, got {repr G.data}"
          unless DenseTensor.approxEq G { shape := [5], data := #[0.0,0.0,0.0,0.0,0.0] } do
            throwError s!"MutB: expected the specific wrong value [0,0,0,0,0], got {repr G.data}"

/-! ### Mutation C: bind a state capture from a stale array

`runDenseScan`'s real step-input construction reads `oldStates`, refreshed at the START of every `r`
iteration from the then-current `states` (which already reflects every PRIOR iteration's committed
writes — the "immutable pre-step snapshot" is per-iteration, not per-scan). This copy instead
snapshots ONCE, before the domain loop begins, and every iteration's state capture reads that same
stale snapshot forever — on the real linear-scan fixture. -/

def runDenseScanStaleCapture (sigs : Array TensorSignature) (c : CheckedScanPlan)
    (outerStore : Array DenseTensor) : Except PositionalInputError (Array DenseTensor) := do
  let raw := c.raw
  let mut states : Array DenseTensor := raw.states.map (fun st =>
    let sig := sigs.getD st.destSlot { shape := #[], dtype := .f64 }
    { shape := sig.shape.toList, data := Array.replicate (sig.shape.toList.foldl (· * ·) 1) 0.0 })
  let baseExternalInputs ← raw.baseCaptures.mapM (fun cap => match cap.source with
    | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
    | .state _ => throw (PositionalInputError.arityMismatch 0 0))
  let baseStore ← runDenseBlock c.checkedBase [] baseExternalInputs
  for w in raw.baseWrites do
    let target := states.getD w.stateIndex { shape := [], data := #[] }
    states := states.set! w.stateIndex (commitWriteLocal target w baseStore [])
  let domainSize := mixedRadixDomainSize c.stepExtents
  -- MUTATION: snapshot ONCE, before the loop, instead of once per iteration (was: `let oldStates :=
  -- states` INSIDE the loop body, refreshed every `r`).
  let staleStates := states
  for r in [0 : domainSize] do
    let q := mixedRadixUnrank c.stepExtents r
    let stepInputs ← raw.stepCaptures.mapM (fun cap => match cap.source with
      | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
      | .state si => pure (staleStates.getD si { shape := [], data := #[] }))  -- MUTATION: never refreshed
    let ctx : List Int := q.toList.map Int.ofNat
    let stepStore ← runDenseBlock c.checkedStep ctx stepInputs
    let mut nextStates := states
    for w in raw.stepWrites do
      let target := nextStates.getD w.stateIndex { shape := [], data := #[] }
      nextStates := nextStates.set! w.stateIndex (commitWriteLocal target w stepStore ctx)
    states := nextStates
  let mut result := outerStore
  for h : si in [0 : raw.states.size] do
    result := result.set! raw.states[si].destSlot (states.getD si { shape := [], data := #[] })
  return result

-- Mutated: the linear scan's `l=1` step now reads S's STALE (base-only) snapshot at position 1
-- (still 0) instead of the freshly-written 11 from `l=0`'s step, giving S = [1,11,20] (20 = X[1] +
-- 0, not X[1] + S[1] = 20 + 11 = 31). Restored (Fixture 1 above, real `runDenseScan`, refreshed
-- snapshot every iteration): S = [1,11,31] — correct.
run_cmd do
  match checkScanPlan outerSigs linearScan with
  | .error e => throwError s!"MutC checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScanStaleCapture outerSigs checked outerStoreLinear with
      | .error e => throwError s!"MutC runDenseScan error: {repr e}"
      | .ok result =>
          let S := result.getD 2 { shape := [], data := #[] }
          if DenseTensor.approxEq S { shape := [3], data := #[1.0,11.0,31.0] } then
            throwError s!"MutC: stale-capture worker should NOT reproduce the correct S, got {repr S.data}"
          unless DenseTensor.approxEq S { shape := [3], data := #[1.0,11.0,20.0] } do
            throwError s!"MutC: expected the specific wrong value [1,11,20], got {repr S.data}"

/-! ## Part 7: Task 1 (F4) — write-map rank checks and capture-order resolution

Two soundness gaps in F3's shipped checker/worker, closed here before F4's Task 3 source compiler
builds on top of them.

**Gap 1**: `checkWrites` never validated that a `StateWriteMap`'s `AffineMap` actually has one
coefficient row and one bias entry per the state's own rank before `writeRowKinds` read it —
`writeRowKinds`/`classifyWriteRow` read row `d` via `Array.getD d ...`, silently substituting a
zero default for a SHORT array rather than rejecting it (and silently ignoring excess rows of an
OVER-length array). `coeffs` and `bias` are checked independently below, since they are separate
arrays that can disagree with the state's rank independently of each other.

**Gap 2**: `runDenseScan` built each block's input-value array by mapping over its OWN capture
array (`raw.baseCaptures`/`raw.stepCaptures`) in whatever order that array happened to be stored,
then passed the result POSITIONALLY into `runDenseBlock`, which binds `inputs[i]` to `raw.inputs[i]`
— `block.inputs`, sorted/deduplicated by `checkPlanBlock`, a SEPARATE order from the capture array's
own storage order. `checkCaptures` only guarantees the capture array is valid as a SET (every input
captured exactly once); nothing ties its storage order to `block.inputs`' order, so a capture array
not already sorted by `inputSlot` silently bound the wrong tensor to the wrong block input. -/

/-! ### Gap 1: coefficient/bias rank mismatch

Reuses Part 5's `multiBaseScan`/`outerSigsMultiBase` (`dp`, a rank-2 state) and Part 1's `faceWrite`
(base write index `0` of `multiBaseScan.baseWrites`) as the write under mutation, so every fixture
below reaches `checkWrites`' new rank checks with every earlier obligation (state index, output
slot, duplicate-output) already satisfied. -/

def shortCoeffsFaceWrite : StateWriteMap :=
  { faceWrite with map := { faceWrite.map with coeffs := #[#[0]] } }
def longCoeffsFaceWrite : StateWriteMap :=
  { faceWrite with map := { faceWrite.map with coeffs := #[#[0], #[1], #[0]] } }
def shortBiasFaceWrite : StateWriteMap :=
  { faceWrite with map := { faceWrite.map with bias := #[0] } }
def longBiasFaceWrite : StateWriteMap :=
  { faceWrite with map := { faceWrite.map with bias := #[0, 0, 0] } }

-- writeCoeffRankMismatch: fewer coefficient rows than `dp`'s rank (2).
run_cmd do
  match checkScanPlan outerSigsMultiBase
      { multiBaseScan with baseWrites := #[shortCoeffsFaceWrite, pointWrite] } with
  | .ok _ =>
      throwError "a write with fewer coefficient rows than the state's rank should have been rejected"
  | .error e =>
      unless e == .writeCoeffRankMismatch true 0 0 2 1 do
        throwError s!"writeCoeffRankMismatch (short): wrong error {repr e}"

-- writeCoeffRankMismatch: more coefficient rows than `dp`'s rank.
run_cmd do
  match checkScanPlan outerSigsMultiBase
      { multiBaseScan with baseWrites := #[longCoeffsFaceWrite, pointWrite] } with
  | .ok _ =>
      throwError "a write with more coefficient rows than the state's rank should have been rejected"
  | .error e =>
      unless e == .writeCoeffRankMismatch true 0 0 2 3 do
        throwError s!"writeCoeffRankMismatch (long): wrong error {repr e}"

-- writeBiasRankMismatch: fewer bias entries than `dp`'s rank.
run_cmd do
  match checkScanPlan outerSigsMultiBase
      { multiBaseScan with baseWrites := #[shortBiasFaceWrite, pointWrite] } with
  | .ok _ =>
      throwError "a write with fewer bias entries than the state's rank should have been rejected"
  | .error e =>
      unless e == .writeBiasRankMismatch true 0 0 2 1 do
        throwError s!"writeBiasRankMismatch (short): wrong error {repr e}"

-- writeBiasRankMismatch: more bias entries than `dp`'s rank.
run_cmd do
  match checkScanPlan outerSigsMultiBase
      { multiBaseScan with baseWrites := #[longBiasFaceWrite, pointWrite] } with
  | .ok _ =>
      throwError "a write with more bias entries than the state's rank should have been rejected"
  | .error e =>
      unless e == .writeBiasRankMismatch true 0 0 2 3 do
        throwError s!"writeBiasRankMismatch (long): wrong error {repr e}"

-- The same check applies to a STEP write (`isBase = false`), confirming the rank obligation is not
-- accidentally base-only: `stepWriteDpMulti` (Part 5) with one coefficient row dropped.
def shortCoeffsStepWrite : StateWriteMap :=
  { stepWriteDpMulti with map := { stepWriteDpMulti.map with coeffs := #[#[1, 0]] } }

run_cmd do
  match checkScanPlan outerSigsMultiBase { multiBaseScan with stepWrites := #[shortCoeffsStepWrite] } with
  | .ok _ =>
      throwError
        "a step write with fewer coefficient rows than the state's rank should have been rejected"
  | .error e =>
      unless e == .writeCoeffRankMismatch false 0 0 2 1 do
        throwError s!"writeCoeffRankMismatch (step): wrong error {repr e}"

/-! ### Gap 2: capture-array-order resolution

Each fixture below stores its capture array deliberately NOT in sorted-`inputSlot` order (the exact
condition `checkCaptures` never rules out), then compares the REAL `runDenseScan` against
`runDenseScanOldCaptureOrder` — a hand-modified copy reproducing the pre-fix behavior (mapping over
the capture array in its own stored order, `commitWriteLocal`-based per Part 6's convention since
`commitWrite` is `private`). If the fix were not load-bearing, both would agree; they do not. -/

def runDenseScanOldCaptureOrder (sigs : Array TensorSignature) (c : CheckedScanPlan)
    (outerStore : Array DenseTensor) : Except PositionalInputError (Array DenseTensor) := do
  let raw := c.raw
  let mut states : Array DenseTensor := raw.states.map (fun st =>
    let sig := sigs.getD st.destSlot { shape := #[], dtype := .f64 }
    { shape := sig.shape.toList, data := Array.replicate (sig.shape.toList.foldl (· * ·) 1) 0.0 })
  -- MUTATION (the pre-Task-1 bug): map over the capture array in ITS OWN stored order instead of
  -- resolving each of `block.inputs`' slots by lookup — passed positionally into `runDenseBlock`
  -- regardless of whether that order matches `raw.baseBlock.inputs`'/`raw.stepBlock.inputs`' sorted
  -- order.
  let baseExternalInputs ← raw.baseCaptures.mapM (fun cap => match cap.source with
    | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
    | .state _ => throw (PositionalInputError.arityMismatch 0 0))  -- unreachable: checked
  let baseStore ← runDenseBlock c.checkedBase [] baseExternalInputs
  for w in raw.baseWrites do
    let target := states.getD w.stateIndex { shape := [], data := #[] }
    states := states.set! w.stateIndex (commitWriteLocal target w baseStore [])
  let domainSize := mixedRadixDomainSize c.stepExtents
  for r in [0 : domainSize] do
    let q := mixedRadixUnrank c.stepExtents r
    let oldStates := states
    -- MUTATION: same as above, for the step block's captures.
    let stepInputs ← raw.stepCaptures.mapM (fun cap => match cap.source with
      | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
      | .state si => pure (oldStates.getD si { shape := [], data := #[] }))
    let ctx : List Int := q.toList.map Int.ofNat
    let stepStore ← runDenseBlock c.checkedStep ctx stepInputs
    let mut nextStates := states
    for w in raw.stepWrites do
      let target := nextStates.getD w.stateIndex { shape := [], data := #[] }
      nextStates := nextStates.set! w.stateIndex (commitWriteLocal target w stepStore ctx)
    states := nextStates
  let mut result := outerStore
  for h : si in [0 : raw.states.size] do
    result := result.set! raw.states[si].destSlot (states.getD si { shape := [], data := #[] })
  return result

/-! #### Base-capture reordering (external-only, same-shaped inputs)

Two independent extent-one states `G3`/`H3` (Fixture 3's shape, so the step loop runs zero times and
only the base path is exercised) fed by a two-input base block whose captures are stored in REVERSED
`inputSlot` order — the capture for input `1` listed before the capture for input `0`. Both inputs
share the same scalar shape, so `checkCaptures`'s own signature check cannot distinguish a correct
binding from a swapped one; only positional-vs-lookup resolution can. -/

def outerSigsBaseReorder : Array TensorSignature :=
  #[{ shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 }
  , { shape := #[1], dtype := .f64 }, { shape := #[1], dtype := .f64 }]

def stateG3 : StateSlot := { destSlot := 2, advancingDims := #[0], materialization := .completeHistory }
def stateH3 : StateSlot := { destSlot := 3, advancingDims := #[0], materialization := .completeHistory }

def baseBlockReorder : RawPlanBlock :=
  { contextShape := #[]
  , tensorSigs := #[{ shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0, 1], assignments := #[], outputs := #[0, 1] }

-- Deliberately reversed: the capture for input slot `1` is stored BEFORE the capture for input
-- slot `0`.
def baseCaptureBReorder : BlockCapture := { inputSlot := 1, source := .external 1 }
def baseCaptureAReorder : BlockCapture := { inputSlot := 0, source := .external 0 }

def baseWriteG3 : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[]], bias := #[0] } }
def baseWriteH3 : StateWriteMap :=
  { outputSlot := 1, stateIndex := 1, map := { coeffs := #[#[]], bias := #[0] } }

def stepReadG3 : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[1], oobPolicy := .zeroPad }
def stepReadH3 : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[1], oobPolicy := .zeroPad }
def termG3 : TermPlan :=
  { iterationShape := #[0], contextPos := #[0], outputPos := #[], reductionPos := #[], factors := #[stepReadG3] }
def termH3 : TermPlan :=
  { iterationShape := #[0], contextPos := #[0], outputPos := #[], reductionPos := #[], factors := #[stepReadH3] }
def stepAssignG3 : AssignPlan :=
  { contextShape := #[0], destinationSlot := 2, outputShape := #[], terms := #[termG3], algebra := admittedAlgebra }
def stepAssignH3 : AssignPlan :=
  { contextShape := #[0], destinationSlot := 3, outputShape := #[], terms := #[termH3], algebra := admittedAlgebra }
def stepBlockReorder : RawPlanBlock :=
  { contextShape := #[0]
  , tensorSigs := #[{ shape := #[1], dtype := .f64 }, { shape := #[1], dtype := .f64 }
                  , { shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0, 1], assignments := #[stepAssignG3, stepAssignH3], outputs := #[2, 3] }
def stepCaptureG3 : BlockCapture := { inputSlot := 0, source := .state 0 }
def stepCaptureH3 : BlockCapture := { inputSlot := 1, source := .state 1 }
def stepWriteG3 : StateWriteMap :=
  { outputSlot := 2, stateIndex := 0, map := { coeffs := #[#[1]], bias := #[1] } }
def stepWriteH3 : StateWriteMap :=
  { outputSlot := 3, stateIndex := 1, map := { coeffs := #[#[1]], bias := #[1] } }

def baseReorderScan : RawScanPlan :=
  { states := #[stateG3, stateH3]
  , baseBlock := baseBlockReorder, baseCaptures := #[baseCaptureBReorder, baseCaptureAReorder]
  , baseWrites := #[baseWriteG3, baseWriteH3]
  , stepBlock := stepBlockReorder, stepCaptures := #[stepCaptureG3, stepCaptureH3]
  , stepWrites := #[stepWriteG3, stepWriteH3]
  , historyExtents := #[1]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

def outerStoreBaseReorder : Array DenseTensor :=
  #[ { shape := [], data := #[7.0] }, { shape := [], data := #[3.0] }
   , { shape := [1], data := #[0.0] }, { shape := [1], data := #[0.0] } ]

-- The fix: the real `runDenseScan` resolves each block input by `inputSlot` lookup, so the reversed
-- storage order in `baseCaptures` has no effect. G3 = external slot 0 = 7, H3 = external slot 1 = 3.
run_cmd do
  match checkScanPlan outerSigsBaseReorder baseReorderScan with
  | .error e => throwError s!"baseReorder (real) checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScan outerSigsBaseReorder checked outerStoreBaseReorder with
      | .error e => throwError s!"baseReorder (real) runDenseScan error: {repr e}"
      | .ok result =>
          let G3 := result.getD 2 { shape := [], data := #[] }
          let H3 := result.getD 3 { shape := [], data := #[] }
          unless DenseTensor.approxEq G3 { shape := [1], data := #[7.0] } do
            throwError s!"baseReorder (real): wrong G3 {repr G3.data}"
          unless DenseTensor.approxEq H3 { shape := [1], data := #[3.0] } do
            throwError s!"baseReorder (real): wrong H3 {repr H3.data}"

-- The bug reproduced: the old, positional-order worker maps over `baseCaptures` in its OWN stored
-- order (`[input-1's capture, input-0's capture]`), so `runDenseBlock` binds slot 0 ↦ external 1
-- (= 3) and slot 1 ↦ external 0 (= 7) — G3 and H3 come out SWAPPED: G3 = 3, H3 = 7.
run_cmd do
  match checkScanPlan outerSigsBaseReorder baseReorderScan with
  | .error e => throwError s!"baseReorder (old) checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScanOldCaptureOrder outerSigsBaseReorder checked outerStoreBaseReorder with
      | .error e => throwError s!"baseReorder (old) runDenseScan error: {repr e}"
      | .ok result =>
          let G3 := result.getD 2 { shape := [], data := #[] }
          let H3 := result.getD 3 { shape := [], data := #[] }
          if DenseTensor.approxEq G3 { shape := [1], data := #[7.0] } then
            throwError s!"baseReorder (old): should NOT reproduce the correct G3, got {repr G3.data}"
          unless DenseTensor.approxEq G3 { shape := [1], data := #[3.0] } do
            throwError s!"baseReorder (old): expected the specific wrong value G3 = 3, got {repr G3.data}"
          if DenseTensor.approxEq H3 { shape := [1], data := #[3.0] } then
            throwError s!"baseReorder (old): should NOT reproduce the correct H3, got {repr H3.data}"
          unless DenseTensor.approxEq H3 { shape := [1], data := #[7.0] } do
            throwError s!"baseReorder (old): expected the specific wrong value H3 = 7, got {repr H3.data}"

/-! #### Coupled-state step-capture reordering

Reuses Part 5's `coupledScan` (Fibonacci-shaped `G`/`H`) verbatim except for one field:
`stepCaptures` stores `H`'s capture before `G`'s, though `G`'s `inputSlot` (`0`) is lower. Under the
fix this has no effect (Fixture 4's `G = [1,2,3,5]`, `H = [1,1,2,3]` reproduced exactly). Under the
old positional-order worker, `stepBlockCoupled`'s input slot 0 (meant for `G`) instead receives `H`,
and slot 1 (meant for `H`) receives `G`, EVERY iteration: `H`'s recurrence (`stepAssignHCoupled`
reads ONLY slot 0) becomes `H[l+1] := H[l]` instead of `G[l]`, so `H` freezes at its base value
forever (`[1,1,1,1]`). `G`'s recurrence (`stepAssignGCoupled` sums BOTH slots) is, per iteration,
unaffected by which slot holds which real value — but it still consumes `H`'s value from the
PRECEDING iteration, which is itself already corrupted from iteration 2 onward, so `G` silently
diverges too, one step later than `H` does (`[1,2,3,4]` instead of `[1,2,3,5]`). This is exactly why
the fixture asserts EXACT histories for BOTH states rather than just checking "something changed" —
a capture-order bug can leave one output looking right for a while and still be wrong. -/

def coupledStepReorderScan : RawScanPlan :=
  { coupledScan with stepCaptures := #[stepCaptureHCoupled, stepCaptureGCoupled] }

-- The fix: real `runDenseScan` reproduces Fixture 4 exactly, regardless of `stepCaptures`' order.
run_cmd do
  match checkScanPlan outerSigsCoupled coupledStepReorderScan with
  | .error e => throwError s!"coupledStepReorder (real) checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScan outerSigsCoupled checked outerStoreCoupled with
      | .error e => throwError s!"coupledStepReorder (real) runDenseScan error: {repr e}"
      | .ok result =>
          let G := result.getD 1 { shape := [], data := #[] }
          let H := result.getD 2 { shape := [], data := #[] }
          unless DenseTensor.approxEq G { shape := [4], data := #[1.0, 2.0, 3.0, 5.0] } do
            throwError s!"coupledStepReorder (real): wrong G {repr G.data}"
          unless DenseTensor.approxEq H { shape := [4], data := #[1.0, 1.0, 2.0, 3.0] } do
            throwError s!"coupledStepReorder (real): wrong H {repr H.data}"

-- The bug reproduced: H freezes at its base value; G then diverges too, one step later.
run_cmd do
  match checkScanPlan outerSigsCoupled coupledStepReorderScan with
  | .error e => throwError s!"coupledStepReorder (old) checkScanPlan rejected: {repr e}"
  | .ok checked =>
      match runDenseScanOldCaptureOrder outerSigsCoupled checked outerStoreCoupled with
      | .error e => throwError s!"coupledStepReorder (old) runDenseScan error: {repr e}"
      | .ok result =>
          let G := result.getD 1 { shape := [], data := #[] }
          let H := result.getD 2 { shape := [], data := #[] }
          if DenseTensor.approxEq G { shape := [4], data := #[1.0, 2.0, 3.0, 5.0] } then
            throwError s!"coupledStepReorder (old): G should NOT reproduce the correct sequence, got {repr G.data}"
          unless DenseTensor.approxEq G { shape := [4], data := #[1.0, 2.0, 3.0, 4.0] } do
            throwError s!"coupledStepReorder (old): expected the specific wrong value G = [1,2,3,4], got {repr G.data}"
          if DenseTensor.approxEq H { shape := [4], data := #[1.0, 1.0, 2.0, 3.0] } then
            throwError s!"coupledStepReorder (old): H should NOT reproduce the correct sequence, got {repr H.data}"
          unless DenseTensor.approxEq H { shape := [4], data := #[1.0, 1.0, 1.0, 1.0] } do
            throwError s!"coupledStepReorder (old): expected the specific wrong value H = [1,1,1,1], got {repr H.data}"

/-!
## `CheckedScanPlan` construction boundary (compile-time privacy check)

Pins that `checkScanPlan` is the only way to obtain a `CheckedScanPlan`, matching
`CheckedPrivacyTest.lean`'s check for `CheckedAssignPlan` and `BlockTest.lean`'s for
`CheckedPlanBlock`: the structure's constructor is `private mk ::`, so anonymous-constructor
notation (`⟨...⟩`) cannot be used to smuggle an unchecked `RawScanPlan` past `checkScanPlan` from
outside `LeanNCD.Eval.Plan`. This matters more here than for either predecessor, because
`runDenseScan` performs NO bounds recovery of its own (see `commitWrite`'s doc comment): a
`CheckedScanPlan` wrapped around a plan whose write geometry was never checked would write through
`flatIndex` at unvalidated coordinates.

As in both precedents, the negative half of this check is NOT an automated `#guard` — it is a
documented manual verification. The line below is deliberately commented out; it must never be
uncommented in committed code, because it must NOT compile:

```
-- def smuggledScan : CheckedScanPlan := ⟨freeExtentMismatchScan⟩
```

Note the payload it names: `freeExtentMismatchScan` is the very plan the Critical-finding fixture
above proves `checkScanPlan` REJECTS, so this is exactly the bypass that would matter.

Manually verified (2026-08-15) by uncommenting that exact line (with `freeExtentMismatchScan :
RawScanPlan` already in scope above) and running, from `leanncd/`:

```
lake env lean test/Eval/Plan/ScanTest.lean
```

Observed failure, exit code 1, literal captured stdout/stderr:

```
test/Eval/Plan/ScanTest.lean:1288:38: error: Invalid `⟨...⟩` notation: Constructor for `LeanNCD.Eval.Plan.CheckedScanPlan` is marked as private
```

The line was re-commented immediately after confirming the failure; this file compiles clean with
it commented out, exercising only the positive half (normal construction via `checkScanPlan` works,
already exercised by every fixture above).
-/

end LeanNCD.Eval.Plan.ScanTest
