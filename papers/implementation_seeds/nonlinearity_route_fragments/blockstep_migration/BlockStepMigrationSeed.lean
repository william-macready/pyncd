import LeanNCD.Eval.Plan.EvalPlan

/-!
# Task 3 `BlockStep` migration rehearsal

This executable seed rehearses assignment, pointwise, and axiswise block steps without replacing or
modifying the production Plan modules. The six disabled mutation toggles are changed one at a time
during the rehearsal, then restored.
-/

namespace LeanNCD.Eval.Plan.BlockStepMigrationSeed

open Lean
open LeanNCD.Eval

inductive BlockStep
  | assign (a : AssignPlan)
  | pointwise (p : RawPointwisePlan)
  | axiswise (a : RawAxiswisePlan)
  deriving DecidableEq, BEq, Repr, Inhabited

def BlockStep.sourceSlots : BlockStep → Array TensorSlot
  | .assign a => a.terms.flatMap (·.factors.map (·.sourceSlot))
  | .pointwise p => #[p.sourceSlot]
  | .axiswise a => #[a.sourceSlot]

def BlockStep.destinationSlots : BlockStep → Array TensorSlot
  | .assign a => #[a.destinationSlot]
  | .pointwise p => #[p.destinationSlot]
  | .axiswise a => #[a.destinationSlot]

def BlockStep.contextShape? : BlockStep → Option (Array Nat)
  | .assign a => some a.contextShape
  | .pointwise _ | .axiswise _ => none

structure RawPlanBlock where
  contextShape : Array Nat
  tensorSigs   : Array TensorSignature
  inputs       : Array TensorSlot
  steps        : Array BlockStep
  outputs      : Array TensorSlot
  deriving DecidableEq, BEq, Repr, Inhabited

inductive CheckedBlockStepEvidence
  | assign (c : CheckedAssignPlan)
  | pointwise (c : CheckedPointwisePlan)
  | axiswise (c : CheckedAxiswisePlan)
  deriving Repr

inductive BlockError
  | wiring (cause : PlanError)
  | duplicateOutputSlot (slot : TensorSlot)
  | blockContextMismatch (nodeIndex : Nat) (expected actual : Array Nat)
  | nonlin (nodeIndex : Nat) (cause : NonlinPlanError)
  | nonlinearSourceNotLocalAssignment (nodeIndex : Nat) (sourceSlot : TensorSlot)
  deriving DecidableEq, BEq, Repr, Inhabited

private def firstDuplicateSlot : List TensorSlot → Option TensorSlot
  | [] => none
  | s :: rest => if rest.contains s then some s else firstDuplicateSlot rest

structure CheckedPlanBlock where private mk ::
  raw          : RawPlanBlock
  checkedNodes : Array CheckedBlockStepEvidence
  deriving Repr

def enableDropPointwiseDispatchMutation : Bool := false
def enableDropAxiswiseDispatchMutation : Bool := false
def enableAssignmentCheckerForNonlinMutation : Bool := false
def enableDropNonlinearProvenanceMutation : Bool := false
def enableSkipLookAheadCausalityMutation : Bool := false
def enableRejectDeepHistoryMutation : Bool := false

def checkPlanBlock (block : RawPlanBlock) : Except BlockError CheckedPlanBlock := do
  let n := block.tensorSigs.size
  for h : i in [0 : block.outputs.size] do
    let s := block.outputs[i]
    unless s < n do throw (.wiring (.slotOutOfRange s n))
  unless block.outputs.toList.Nodup do
    throw (.duplicateOutputSlot ((firstDuplicateSlot block.outputs.toList).getD 0))
  let mut nodes : Array (WiringNode BlockError CheckedBlockStepEvidence) := #[]
  let mut precedingAssignmentDestinations : Array TensorSlot := #[]
  for h : ni in [0 : block.steps.size] do
    let step := block.steps[ni]
    let precedingAssignments := precedingAssignmentDestinations
    nodes := nodes.push
      { contextCheck := match step.contextShape? with
          | some actual =>
              unless actual == block.contextShape do
                throw (.blockContextMismatch ni block.contextShape actual)
          | none => pure ()
      , destinationSlots := step.destinationSlots
      , sourceCheck := fun available => match step with
          | .assign a => do
              for h2 : ti in [0 : a.terms.size] do
                let t := a.terms[ti]
                for h3 : fi in [0 : t.factors.size] do
                  let f := t.factors[fi]
                  match available[f.sourceSlot]? with
                  | none => throw (.wiring (.nodeError ni (.slotOutOfRange f.sourceSlot n)))
                  | some true => pure ()
                  | some false => throw (.wiring (.invalidForwardRead ni ti fi f.sourceSlot))
          | .pointwise p => do
              match available[p.sourceSlot]? with
              | none => throw (.wiring (.nodeError ni (.slotOutOfRange p.sourceSlot n)))
              | some false => throw (.wiring (.invalidForwardRead ni 0 0 p.sourceSlot))
              | some true => pure ()
              unless enableDropNonlinearProvenanceMutation ||
                  precedingAssignments.contains p.sourceSlot do
                throw (.nonlinearSourceNotLocalAssignment ni p.sourceSlot)
          | .axiswise a => do
              match available[a.sourceSlot]? with
              | none => throw (.wiring (.nodeError ni (.slotOutOfRange a.sourceSlot n)))
              | some false => throw (.wiring (.invalidForwardRead ni 0 0 a.sourceSlot))
              | some true => pure ()
              unless enableDropNonlinearProvenanceMutation ||
                  precedingAssignments.contains a.sourceSlot do
                throw (.nonlinearSourceNotLocalAssignment ni a.sourceSlot)
      , localCheck := match step with
          | .assign a => match checkAssign block.tensorSigs a with
              | .error e => throw (.wiring (.nodeError ni e))
              | .ok c => pure (.assign c)
          | .pointwise p =>
              if enableAssignmentCheckerForNonlinMutation then
                match checkAssign block.tensorSigs default with
                | .error e => throw (.wiring (.nodeError ni e))
                | .ok c => pure (.assign c)
              else
                match checkPointwise block.tensorSigs p with
                | .error e => throw (.nonlin ni e)
                | .ok c => pure (.pointwise c)
          | .axiswise a =>
              if enableAssignmentCheckerForNonlinMutation then
                match checkAssign block.tensorSigs default with
                | .error e => throw (.wiring (.nodeError ni e))
                | .ok c => pure (.assign c)
              else
                match checkAxiswise block.tensorSigs a with
                | .error e => throw (.nonlin ni e)
                | .ok c => pure (.axiswise c) }
    match step with
    | .assign a => precedingAssignmentDestinations :=
        precedingAssignmentDestinations.push a.destinationSlot
    | .pointwise _ | .axiswise _ => pure ()
  let checkedNodes ← checkStepGraph n block.inputs BlockError.wiring nodes
  return CheckedPlanBlock.mk block checkedNodes

def runDenseBlock (c : CheckedPlanBlock) (ctx : List Int) (inputs : Array DenseTensor) :
    Except PositionalInputError (Array DenseTensor) := do
  let raw := c.raw
  unless inputs.size == raw.inputs.size do
    throw (.arityMismatch raw.inputs.size inputs.size)
  let placeholder : DenseTensor := { shape := [], data := #[] }
  let mut store : Array DenseTensor := Array.replicate raw.tensorSigs.size placeholder
  for h : i in [0 : raw.inputs.size] do
    let slot := raw.inputs[i]
    let t := inputs[i]!
    let sig := raw.tensorSigs.getD slot { shape := #[], dtype := .f64 }
    unless t.shape == sig.shape.toList do throw (.shapeMismatch slot sig.shape t.shape)
    unless t.data.size == sig.shape.toList.foldl (· * ·) 1 do
      throw (.storageMismatch slot t.shape t.data.size)
    store := store.set! slot t
  for node in c.checkedNodes do
    match node with
    | .assign a =>
        store := store.set! a.plan.destinationSlot (← runDenseAssignAt a ctx store)
    | .pointwise p =>
        unless enableDropPointwiseDispatchMutation do
          store := store.set! p.raw.destinationSlot
            (runDensePointwise p (store.getD p.raw.sourceSlot placeholder))
    | .axiswise a =>
        unless enableDropAxiswiseDispatchMutation do
          store := store.set! a.raw.destinationSlot
            (runDenseAxiswise a (store.getD a.raw.sourceSlot placeholder))
  return store

def wrapCompilerBlock (block : LeanNCD.Eval.Plan.RawPlanBlock) : RawPlanBlock :=
  { contextShape := block.contextShape
  , tensorSigs := block.tensorSigs
  , inputs := block.inputs
  , steps := block.assignments.map .assign
  , outputs := block.outputs }

private def identityAssign (contextShape shape : Array Nat) (source destination : TensorSlot) :
    AssignPlan :=
  let contextWidth := contextShape.size
  let iterationShape := contextShape ++ shape
  let coeffs := (Array.range shape.size).map (fun row =>
    (Array.range iterationShape.size).map (fun col => if col == contextWidth + row then 1 else 0))
  let read : ReadPlan :=
    { sourceSlot := source, map := { coeffs, bias := Array.replicate shape.size 0 }
    , sourceShape := shape, oobPolicy := .zeroPad }
  let term : TermPlan :=
    { iterationShape := iterationShape, contextPos := Array.range contextWidth
    , outputPos := (Array.range shape.size).map (contextWidth + ·), reductionPos := #[]
    , factors := #[read] }
  { contextShape, destinationSlot := destination, outputShape := shape
  , terms := #[term]
  , algebra := admittedAlgebra }

private def BlockStep.toAssignment (contextShape : Array Nat) : BlockStep → AssignPlan
  | .assign a => a
  | .pointwise p => identityAssign contextShape p.shape p.sourceSlot p.destinationSlot
  | .axiswise a => identityAssign contextShape a.shape a.sourceSlot a.destinationSlot

private def RawPlanBlock.toProduction (block : RawPlanBlock) : LeanNCD.Eval.Plan.RawPlanBlock :=
  { contextShape := block.contextShape, tensorSigs := block.tensorSigs, inputs := block.inputs
  , assignments := block.steps.map (·.toAssignment block.contextShape), outputs := block.outputs }

structure RawScanPlan where
  states         : Array StateSlot
  baseBlock      : RawPlanBlock
  baseCaptures   : Array BlockCapture
  baseWrites     : Array StateWriteMap
  stepBlock      : RawPlanBlock
  stepCaptures   : Array BlockCapture
  stepWrites     : Array StateWriteMap
  historyExtents : Array Nat
  iterationOrder : ScanIterationOrder
  boundaryPolicy : ScanBoundaryPolicy
  snapshotPolicy : ScanSnapshotPolicy
  deriving DecidableEq, BEq, Repr, Inhabited

inductive ScanError
  | baseBlockError (cause : BlockError)
  | stepBlockError (cause : BlockError)
  | structural (cause : ScanPlanError)
  | causalityFailure (stateIndex blockStepIndex termIndex factorIndex : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

structure CheckedScanPlan where private mk ::
  raw         : RawScanPlan
  checkedBase : CheckedPlanBlock
  checkedStep : CheckedPlanBlock
  deriving Repr

private def RawScanPlan.toProduction (raw : RawScanPlan) : LeanNCD.Eval.Plan.RawScanPlan :=
  let stepCaptures := raw.stepCaptures.map (fun capture =>
    match capture.source with
    | .external _ => capture
    | .state si =>
        { capture with source := .external (raw.states.getD si default).destSlot })
  { states := raw.states
  , baseBlock := raw.baseBlock.toProduction
  , baseCaptures := raw.baseCaptures
  , baseWrites := raw.baseWrites
  , stepBlock := raw.stepBlock.toProduction
  , stepCaptures
  , stepWrites := raw.stepWrites
  , historyExtents := raw.historyExtents
  , iterationOrder := raw.iterationOrder
  , boundaryPolicy := raw.boundaryPolicy
  , snapshotPolicy := raw.snapshotPolicy }

def checkScanPlan (sigs : Array TensorSignature) (raw : RawScanPlan) :
    Except ScanError CheckedScanPlan := do
  let checkedBase ← (checkPlanBlock raw.baseBlock).mapError .baseBlockError
  let checkedStep ← (checkPlanBlock raw.stepBlock).mapError .stepBlockError
  for h : ci in [0 : raw.stepCaptures.size] do
    match raw.stepCaptures[ci].source with
    | .external _ => pure ()
    | .state si =>
        unless si < raw.states.size do
          throw (.structural (.captureStateIndexOutOfRange false ci si raw.states.size))
  match LeanNCD.Eval.Plan.checkScanPlan sigs raw.toProduction with
  | .error e => throw (.structural e)
  | .ok _ => pure ()
  let stateCaptureFor : TensorSlot → Option Nat := fun inputSlot =>
    (raw.stepCaptures.find? (fun c => c.inputSlot == inputSlot)).bind (fun c => match c.source with
      | .state si => some si | .external _ => none)
  for h : bi in [0 : raw.stepBlock.steps.size] do
    match raw.stepBlock.steps[bi] with
    | .pointwise _ | .axiswise _ => pure ()
    | .assign a =>
        for h2 : ti in [0 : a.terms.size] do
          let t := a.terms[ti]
          for h3 : fi in [0 : t.factors.size] do
            let f := t.factors[fi]
            match stateCaptureFor f.sourceSlot with
            | none => pure ()
            | some si =>
                let st := raw.states.getD si default
                if enableRejectDeepHistoryMutation && f.map.bias.any (· < 0) then
                  throw (.causalityFailure si bi ti fi)
                unless enableSkipLookAheadCausalityMutation ||
                    stateReadCausal st.advancingDims t.contextPos f do
                  throw (.causalityFailure si bi ti fi)
  return CheckedScanPlan.mk raw checkedBase checkedStep

def wrapCompilerScan (raw : LeanNCD.Eval.Plan.RawScanPlan) : RawScanPlan :=
  { states := raw.states, baseBlock := wrapCompilerBlock raw.baseBlock
  , baseCaptures := raw.baseCaptures, baseWrites := raw.baseWrites
  , stepBlock := wrapCompilerBlock raw.stepBlock
  , stepCaptures := raw.stepCaptures, stepWrites := raw.stepWrites
  , historyExtents := raw.historyExtents, iterationOrder := raw.iterationOrder
  , boundaryPolicy := raw.boundaryPolicy, snapshotPolicy := raw.snapshotPolicy }

/-! ## Block fixtures 1-4 and 7 -/

def blockSigs : Array TensorSignature :=
  #[{ shape := #[2, 3], dtype := .f64 }, { shape := #[3], dtype := .f64 }]

def blockReadX : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[0, 0] }
  , sourceShape := #[2, 3], oobPolicy := .zeroPad }

def blockAssign : AssignPlan :=
  let term : TermPlan :=
    { iterationShape := #[2, 3], contextPos := #[0], outputPos := #[1]
    , reductionPos := #[], factors := #[blockReadX] }
  { contextShape := #[2], destinationSlot := 1, outputShape := #[3]
  , terms := #[term]
  , algebra := admittedAlgebra }

def pointwiseBlock : RawPlanBlock :=
  { contextShape := #[2]
  , tensorSigs := blockSigs ++ #[{ shape := #[3], dtype := .f64 }]
  , inputs := #[0]
  , steps := #[.assign blockAssign,
      .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[3], fn := .relu }]
  , outputs := #[2] }

def axiswiseBlock : RawPlanBlock :=
  { contextShape := #[2]
  , tensorSigs := blockSigs ++ #[{ shape := #[3], dtype := .f64 }]
  , inputs := #[0]
  , steps := #[.assign blockAssign,
      .axiswise { sourceSlot := 1, destinationSlot := 2, shape := #[3]
                , axisPos := 0, fn := .normalize }]
  , outputs := #[2] }

def fwdSigs : Array TensorSignature :=
  #[{ shape := #[4], dtype := .f64 }, { shape := #[4], dtype := .f64 },
    { shape := #[4], dtype := .f64 }]

def fwdReadSlot0 : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[4], oobPolicy := .zeroPad }

def fwdReadSlot1 : ReadPlan := { fwdReadSlot0 with sourceSlot := 1 }

def fwdAssignA : AssignPlan :=
  let term : TermPlan :=
    { iterationShape := #[4], contextPos := #[], outputPos := #[0]
    , reductionPos := #[], factors := #[fwdReadSlot1] }
  { contextShape := #[], destinationSlot := 2, outputShape := #[4]
  , terms := #[term]
  , algebra := admittedAlgebra }

def fwdAssignB : AssignPlan :=
  let term : TermPlan :=
    { iterationShape := #[4], contextPos := #[], outputPos := #[0]
    , reductionPos := #[], factors := #[fwdReadSlot0] }
  { contextShape := #[], destinationSlot := 1, outputShape := #[4]
  , terms := #[term]
  , algebra := admittedAlgebra }

def unproducedPointwiseBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := fwdSigs, inputs := #[0]
  , steps := #[
      .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[4], fn := .relu },
      .assign fwdAssignB]
  , outputs := #[2] }

def collidingPointwiseDestinationBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := fwdSigs, inputs := #[0]
  , steps := #[.assign fwdAssignB,
      .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[4], fn := .relu },
      .assign fwdAssignA]
  , outputs := #[2] }

def nonlinearChainBlock : RawPlanBlock :=
  { pointwiseBlock with
    tensorSigs := pointwiseBlock.tensorSigs ++ #[{ shape := #[3], dtype := .f64 }]
    steps := pointwiseBlock.steps ++ #[
      .axiswise { sourceSlot := 2, destinationSlot := 3, shape := #[3]
                , axisPos := 0, fn := .normalize }]
    outputs := #[3] }

run_cmd do
  let input : DenseTensor := { shape := [2, 3], data := #[1, -2, 3, 4, -5, 6] }
  match checkPlanBlock pointwiseBlock with
  | .error e => throwError s!"fixture 1 rejected: {repr e}"
  | .ok checked => match runDenseBlock checked [0] #[input] with
      | .error e => throwError s!"fixture 1 execution failed: {repr e}"
      | .ok store =>
          unless store[2]!.data == #[1, 0, 3] do
            throwError s!"fixture 1 wrong result: {repr store[2]!.data}"
          logInfo s!"fixture 1 pointwise result {repr store[2]!.data}"

run_cmd do
  let input : DenseTensor := { shape := [2, 3], data := #[1, 2, 3, 4, 5, 6] }
  match checkPlanBlock axiswiseBlock with
  | .error e => throwError s!"fixture 2 rejected: {repr e}"
  | .ok checked => match runDenseBlock checked [0] #[input] with
      | .error e => throwError s!"fixture 2 execution failed: {repr e}"
      | .ok store =>
          unless store[2]!.data.size == 3 &&
              store[2]!.data[0]! < store[2]!.data[1]! &&
              store[2]!.data[1]! < store[2]!.data[2]! do
            throwError s!"fixture 2 wrong result: {repr store[2]!.data}"
          logInfo s!"fixture 2 axiswise result {repr store[2]!.data}"

#guard match checkPlanBlock unproducedPointwiseBlock with
  | .error (.wiring (.invalidForwardRead 0 0 0 1)) => true
  | _ => false

#guard match checkPlanBlock collidingPointwiseDestinationBlock with
  | .error (.wiring (.duplicateDestination 2 1 2)) => true
  | _ => false

#guard match checkPlanBlock nonlinearChainBlock with
  | .error (.nonlinearSourceNotLocalAssignment 2 2) => true
  | _ => false

/-! ## Scan donors and fixtures 5-6, 8-9 -/

def outerSigsDeepHistory : Array TensorSignature :=
  #[{ shape := #[], dtype := .f64 }, { shape := #[5], dtype := .f64 }]

def stateG : StateSlot :=
  { destSlot := 1, advancingDims := #[0], materialization := .completeHistory }

def baseBlockG : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[], dtype := .f64 }]
  , inputs := #[0], steps := #[], outputs := #[0] }

def baseCaptureG0 : BlockCapture := { inputSlot := 0, source := .external 0 }

def baseWriteG : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[]], bias := #[0] } }

def stepReadG : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[-2] }
  , sourceShape := #[5], oobPolicy := .zeroPad }

def termG : TermPlan :=
  { iterationShape := #[4], contextPos := #[0], outputPos := #[], reductionPos := #[]
  , factors := #[stepReadG] }

def stepAssignG : AssignPlan :=
  { contextShape := #[4], destinationSlot := 1, outputShape := #[], terms := #[termG]
  , algebra := admittedAlgebra }

def stepBlockG : RawPlanBlock :=
  { contextShape := #[4]
  , tensorSigs := #[{ shape := #[5], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0], steps := #[.assign stepAssignG], outputs := #[1] }

def stepCaptureG : BlockCapture := { inputSlot := 0, source := .state 0 }

def stepWriteG : StateWriteMap :=
  { outputSlot := 1, stateIndex := 0, map := { coeffs := #[#[1]], bias := #[1] } }

def deepHistoryScan : RawScanPlan :=
  { states := #[stateG]
  , baseBlock := baseBlockG, baseCaptures := #[baseCaptureG0], baseWrites := #[baseWriteG]
  , stepBlock := stepBlockG, stepCaptures := #[stepCaptureG], stepWrites := #[stepWriteG]
  , historyExtents := #[5], iterationOrder := .axisZeroFastest
  , boundaryPolicy := .zeroThenBaseOverlay, snapshotPolicy := .immutablePreStep }

def lookAheadReadG : ReadPlan :=
  { stepReadG with map := { coeffs := #[#[1]], bias := #[1] } }

def termLookAheadG : TermPlan := { termG with factors := #[lookAheadReadG] }
def stepAssignLookAheadG : AssignPlan := { stepAssignG with terms := #[termLookAheadG] }
def stepBlockLookAheadG : RawPlanBlock :=
  { stepBlockG with steps := #[.assign stepAssignLookAheadG] }

def capturedPointwiseBlock : RawPlanBlock :=
  { stepBlockLookAheadG with
    tensorSigs := #[{ shape := #[5], dtype := .f64 }, { shape := #[5], dtype := .f64 }]
    steps := #[.pointwise
      { sourceSlot := 0, destinationSlot := 1, shape := #[5], fn := .relu }] }

def launderedLookAheadRead : ReadPlan := { lookAheadReadG with sourceSlot := 2 }
def launderedLookAheadTerm : TermPlan := { termLookAheadG with factors := #[launderedLookAheadRead] }
def launderedLookAheadAssign : AssignPlan :=
  { stepAssignLookAheadG with terms := #[launderedLookAheadTerm] }

def launderingBlock : RawPlanBlock :=
  { stepBlockLookAheadG with
    tensorSigs := stepBlockLookAheadG.tensorSigs ++ #[{ shape := #[5], dtype := .f64 }]
    steps := #[
      .pointwise { sourceSlot := 0, destinationSlot := 2, shape := #[5], fn := .relu },
      .assign launderedLookAheadAssign] }

def deepHistoryThenPointwiseBlock : RawPlanBlock :=
  { stepBlockG with
    tensorSigs := stepBlockG.tensorSigs ++ #[{ shape := #[], dtype := .f64 }]
    steps := stepBlockG.steps ++ #[
      .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[], fn := .relu }] }

def deepHistoryThenPointwiseScan : RawScanPlan :=
  { deepHistoryScan with stepBlock := deepHistoryThenPointwiseBlock }

def lookAheadThenPointwiseBlock : RawPlanBlock :=
  { stepBlockLookAheadG with
    tensorSigs := stepBlockLookAheadG.tensorSigs ++ #[{ shape := #[], dtype := .f64 }]
    steps := stepBlockLookAheadG.steps ++ #[
      .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[], fn := .relu }] }

def lookAheadThenPointwiseScan : RawScanPlan :=
  { deepHistoryScan with stepBlock := lookAheadThenPointwiseBlock }

#guard match checkPlanBlock capturedPointwiseBlock with
  | .error (.nonlinearSourceNotLocalAssignment 0 0) => true
  | _ => false

#guard match checkPlanBlock launderingBlock with
  | .error (.nonlinearSourceNotLocalAssignment 0 0) => true
  | _ => false

#guard match checkScanPlan outerSigsDeepHistory deepHistoryThenPointwiseScan with
  | .ok _ => true
  | _ => false

#guard match checkScanPlan outerSigsDeepHistory lookAheadThenPointwiseScan with
  | .error (.causalityFailure 0 0 0 0) => true
  | _ => false

def compilerAssignmentBlock : LeanNCD.Eval.Plan.RawPlanBlock :=
  { contextShape := #[4], tensorSigs := stepBlockG.tensorSigs, inputs := #[0]
  , assignments := #[stepAssignG], outputs := #[1] }

#guard (wrapCompilerBlock compilerAssignmentBlock).steps.all (fun step => match step with
  | .assign _ => true
  | .pointwise _ | .axiswise _ => false)

end LeanNCD.Eval.Plan.BlockStepMigrationSeed
