-- leanncd/LeanNCD/Eval/Plan/Scan.lean (part 1 of several in this plan)
import LeanNCD.Eval.Plan.Block

namespace LeanNCD.Eval.Plan

/-- One recognized shape for a write-map row: pinned to a literal, an order-preserving projection
    of the block's own output slice, or bound to `context[p] + 1` (step writes only). Anything else
    is an unrecognized affine geometry and must be rejected. -/
inductive WriteRowKind
  | pinned    (lit : Int)
  | free      (outputPos : Nat)
  | advancing (contextPos : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Classify one complete-state dimension's write row. `contextWidth` is `0` for a base write and
    `advancingDims.size` for a step write — the same `AffineMap` shape serves both, distinguished
    only by how many leading domain positions are scan-context rather than output-slice. -/
def classifyWriteRow (contextWidth : Nat) (coeffRow : Array Int) (bias : Int) : Option WriteRowKind :=
  let nz := coeffRow.toList.zipIdx.filter (fun (c, _) => c != 0)
  match nz with
  | [] => some (.pinned bias)
  | [(c, p)] =>
      if c == 1 && p < contextWidth && bias == 1 then some (.advancing p)
      else if c == 1 && p ≥ contextWidth && bias == 0 then some (.free (p - contextWidth))
      else none
  | _ => none

/-- Row classifications for one write against one state, given the complete state's rank and the
    write's declared context width (`0` for base, `advancingDims.size` for step). -/
def writeRowKinds (stateRank contextWidth : Nat) (w : StateWriteMap) : Array (Option WriteRowKind) :=
  (Array.range stateRank).map (fun d =>
    classifyWriteRow contextWidth (w.map.coeffs.getD d #[]) (w.map.bias.getD d 0))

/-- A base write's rows must all be recognized, its free positions must cover `0 .. outputShape)`
    in increasing order (order-preserving onto the block's own output axes), and at least one
    advancing dimension must be pinned to literal `0` (touches the lower boundary). -/
def baseWriteRowsOk (advancingDims : Array Nat) (outputShapeSize : Nat)
    (rows : Array (Option WriteRowKind)) : Bool :=
  rows.all Option.isSome &&
  ((rows.toList.filterMap (fun r => match r with | some (.free p) => some p | _ => none))
    == List.range outputShapeSize) &&
  advancingDims.any (fun d => rows.getD d none == some (.pinned 0))

/-- A step write's rows: every advancing dimension must be `.advancing` at its own context position
    (dimension `advancingDims[i]` at context position `i`), every other dimension must be `.free`
    in increasing order onto the block's own output axes, and no row may be unrecognized. -/
def stepWriteRowsOk (advancingDims : Array Nat) (outputShapeSize : Nat)
    (rows : Array (Option WriteRowKind)) : Bool :=
  rows.all Option.isSome &&
  (advancingDims.toList.zipIdx.all (fun (d, i) => rows.getD d none == some (.advancing i))) &&
  ((rows.toList.zipIdx.filterMap (fun (r, d) =>
      if advancingDims.contains d then none else match r with
        | some (.free p) => some p | _ => none))
    == List.range outputShapeSize)

/-- Two writes' declared regions collide iff no dimension forces them apart. Since every row is
    `.pinned`/`.free`/`.advancing`, a dimension forces the regions apart only when BOTH writes pin
    it to DIFFERENT literals; `.free`/`.advancing` always range over their full domain and can never
    exclude the other write. This single rule is what makes "two full free-axis faces never
    disjoint" (proposal §5.1) a structural consequence rather than an asserted claim — verified
    below against F0's own worked fixture. -/
def writesCollide (rowsA rowsB : Array (Option WriteRowKind)) : Bool :=
  ¬ (List.range rowsA.size).any (fun d =>
      match rowsA.getD d none, rowsB.getD d none with
      | some (.pinned a), some (.pinned b) => a != b
      | _, _ => false)

/-- A raw `RawScanPlan` violates a scan-level invariant. Indices identify the offending
    state/write/capture so a failure is locatable without re-deriving it (proposal §7.5). -/
inductive ScanPlanError
  | noStates
  | noAdvancingAxes
  | zeroExtent                    (axisIndex : Nat)
  | stateDestSlotOutOfRange       (stateIndex : Nat) (slot : TensorSlot) (tableSize : Nat)
  | duplicateStateDestSlot        (stateIndex firstStateIndex : Nat) (slot : TensorSlot)
  | advancingDimOutOfRange        (stateIndex dim rank : Nat)
  | duplicateAdvancingDim         (stateIndex dim : Nat)
  | advancingDimCountMismatch     (stateIndex expected actual : Nat)
  | advancingSizeMismatch         (stateIndex axisIndex expected actual : Nat)
  | baseBlockContextNotEmpty      (actual : Array Nat)
  | stepBlockContextMismatch      (expected actual : Array Nat)
  | baseBlockError                (cause : BlockError)
  | stepBlockError                (cause : BlockError)
  | captureInputSlotOutOfRange    (isBase : Bool) (captureIndex : Nat) (slot : TensorSlot)
  | duplicateCaptureInput         (isBase : Bool) (slot : TensorSlot)
  | captureTargetsNonInput        (isBase : Bool) (slot : TensorSlot)
  | blockInputNotCaptured         (isBase : Bool) (slot : TensorSlot)
  | stateCaptureInBaseBlock       (captureIndex : Nat)
  | captureStateIndexOutOfRange   (isBase : Bool) (captureIndex stateIndex numStates : Nat)
  | captureExternalSlotOutOfRange (isBase : Bool) (captureIndex : Nat) (slot tableSize : Nat)
  | captureSignatureMismatch      (isBase : Bool) (captureIndex : Nat)
                                  (expected actual : TensorSignature)
  | noBaseWriteForState           (stateIndex : Nat)
  | noStepWriteForState           (stateIndex : Nat)
  | multipleStepWritesForState    (stateIndex firstWriteIndex secondWriteIndex : Nat)
  | writeStateIndexOutOfRange     (isBase : Bool) (writeIndex stateIndex numStates : Nat)
  | writeSourceNotBlockOutput     (isBase : Bool) (writeIndex : Nat) (slot : TensorSlot)
  | blockOutputNotWritten         (isBase : Bool) (outputSlot : TensorSlot)
  | duplicateWriteForOutput       (isBase : Bool) (outputSlot : TensorSlot)
                                  (firstWriteIndex secondWriteIndex : Nat)
  | writeGeometryNotAdmitted      (isBase : Bool) (writeIndex : Nat)
  | baseWritesOverlap             (stateIndex firstWriteIndex secondWriteIndex : Nat)
  | iterationOrderNotAdmitted     (order : ScanIterationOrder)
  | boundaryPolicyNotAdmitted     (policy : ScanBoundaryPolicy)
  | snapshotPolicyNotAdmitted     (policy : ScanSnapshotPolicy)
  | materializationPolicyNotAdmitted (stateIndex : Nat) (policy : MaterializationPolicy)
  | causalityFailure              (stateIndex termIndex factorIndex : Nat)  -- Task 2
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Evidence that one `RawScanPlan` is a sound checked scan: both blocks are checked, every
    capture/write obligation in proposal §7.3 holds, and (Task 2) causality holds for every state
    read. `stepExtents` is retained rather than recomputed by every consumer. -/
structure CheckedScanPlan where private mk ::
  raw         : RawScanPlan
  checkedBase : CheckedPlanBlock
  checkedStep : CheckedPlanBlock
  stepExtents : Array Nat
  deriving Repr

/-- Validate a block's captures against its own declared `inputs`: every capture's `inputSlot` is
    one of the block's inputs, every input has exactly one capture, and (for the base block) no
    capture may be a state capture. `numStates`/`states`/`isBase` parameterize the two call sites
    identically rather than duplicating this function. -/
private def checkCaptures (sigs : Array TensorSignature) (block : RawPlanBlock)
    (captures : Array BlockCapture) (numStates : Nat) (states : Array StateSlot) (isBase : Bool) :
    Except ScanPlanError Unit := do
  let mut boundInputs : Array Bool := Array.replicate block.tensorSigs.size false
  for h : i in [0 : captures.size] do
    let c := captures[i]
    unless c.inputSlot < block.tensorSigs.size do
      throw (.captureInputSlotOutOfRange isBase i c.inputSlot)
    unless block.inputs.contains c.inputSlot do
      throw (.captureTargetsNonInput isBase c.inputSlot)
    if boundInputs.getD c.inputSlot false then throw (.duplicateCaptureInput isBase c.inputSlot)
    boundInputs := boundInputs.set! c.inputSlot true
    match c.source with
    | .external outerSlot =>
        unless outerSlot < sigs.size do
          throw (.captureExternalSlotOutOfRange isBase i outerSlot sigs.size)
        let expected := sigs.getD outerSlot { shape := #[], dtype := .f64 }
        let actual := block.tensorSigs.getD c.inputSlot { shape := #[], dtype := .f64 }
        unless expected == actual do throw (.captureSignatureMismatch isBase i expected actual)
    | .state stateIndex =>
        if isBase then throw (.stateCaptureInBaseBlock i)
        unless stateIndex < numStates do
          throw (.captureStateIndexOutOfRange isBase i stateIndex numStates)
        let st := states.getD stateIndex default
        let expected := sigs.getD st.destSlot { shape := #[], dtype := .f64 }
        let actual := block.tensorSigs.getD c.inputSlot { shape := #[], dtype := .f64 }
        unless expected == actual do throw (.captureSignatureMismatch isBase i expected actual)
  for inputSlot in block.inputs do
    unless boundInputs.getD inputSlot false do throw (.blockInputNotCaptured isBase inputSlot)

/-- Validate one block's writes against its own declared `outputs` and against `states`: every
    write's `stateIndex` is in range, every write's `outputSlot` is a declared block output, every
    declared output is written by exactly one write, base-write geometry is admitted and pairwise
    disjoint across each state's FULL write list, and step-write geometry is admitted. Returns, per
    state, the accepted row classifications so the caller can additionally require exactly one step
    write and at least one base write. -/
private def checkWrites (sigs : Array TensorSignature) (block : RawPlanBlock)
    (writes : Array StateWriteMap) (states : Array StateSlot) (isBase : Bool) :
    Except ScanPlanError (Array (Array (Array (Option WriteRowKind)))) := do
  let mut writtenOutputs : Array (Option Nat) := Array.replicate block.tensorSigs.size none
  let mut rowsByState : Array (Array (Array (Option WriteRowKind))) :=
    Array.replicate states.size #[]
  for h : wi in [0 : writes.size] do
    let w := writes[wi]
    unless w.stateIndex < states.size do
      throw (.writeStateIndexOutOfRange isBase wi w.stateIndex states.size)
    unless block.outputs.contains w.outputSlot do
      throw (.writeSourceNotBlockOutput isBase wi w.outputSlot)
    match writtenOutputs.getD w.outputSlot none with
    | some firstWi => throw (.duplicateWriteForOutput isBase w.outputSlot firstWi wi)
    | none => writtenOutputs := writtenOutputs.set! w.outputSlot (some wi)
    let st := states.getD w.stateIndex default
    let stateRank := (sigs.getD st.destSlot { shape := #[], dtype := .f64 }).shape.size
    let contextWidth := if isBase then 0 else st.advancingDims.size
    let rows := writeRowKinds stateRank contextWidth w
    let outputShapeSize := (block.tensorSigs.getD w.outputSlot { shape := #[], dtype := .f64 }).shape.size
    let admitted := if isBase then baseWriteRowsOk st.advancingDims outputShapeSize rows
                    else stepWriteRowsOk st.advancingDims outputShapeSize rows
    unless admitted do throw (.writeGeometryNotAdmitted isBase wi)
    rowsByState := rowsByState.set! w.stateIndex (rowsByState.getD w.stateIndex #[] |>.push rows)
  for outputSlot in block.outputs do
    unless writtenOutputs.getD outputSlot none |>.isSome do
      throw (.blockOutputNotWritten isBase outputSlot)
  -- pairwise disjointness across each state's FULL base-write list (proposal §7.3: not just
  -- checked between an arbitrarily chosen pair; index into each state's own accumulated write
  -- list, not the raw `writes` array — the implementer may thread through global write indices
  -- instead if a reviewer prefers that error shape, a call-site detail with no semantic effect).
  if isBase then
    for h : si in [0 : rowsByState.size] do
      let stateRows := rowsByState[si]
      for h2 : a in [0 : stateRows.size] do
        for h3 : b in [0 : stateRows.size] do
          if a < b then
            if writesCollide stateRows[a] stateRows[b] then throw (.baseWritesOverlap si a b)
  return rowsByState

/-- Validate an unchecked scan node (proposal §7.3). This version omits causality — Task 2 adds the
    `stateReadCausal` pass before the final `return`. -/
def checkScanPlan (sigs : Array TensorSignature) (raw : RawScanPlan) :
    Except ScanPlanError CheckedScanPlan := do
  if raw.states.isEmpty then throw .noStates else pure ()
  if raw.historyExtents.isEmpty then throw .noAdvancingAxes else pure ()
  for h : i in [0 : raw.historyExtents.size] do
    if raw.historyExtents[i] == 0 then throw (.zeroExtent i) else pure ()
  let stepExtents : Array Nat := raw.historyExtents.map (· - 1)
  let numAxes := raw.historyExtents.size
  let mut destSeen : Array (Option Nat) := Array.replicate sigs.size none
  for h : si in [0 : raw.states.size] do
    let st := raw.states[si]
    unless st.destSlot < sigs.size do
      throw (.stateDestSlotOutOfRange si st.destSlot sigs.size)
    match destSeen.getD st.destSlot none with
    | some firstSi => throw (.duplicateStateDestSlot si firstSi st.destSlot)
    | none => destSeen := destSeen.set! st.destSlot (some si)
    unless st.advancingDims.size == numAxes do
      throw (.advancingDimCountMismatch si numAxes st.advancingDims.size)
    let stateSig := sigs.getD st.destSlot { shape := #[], dtype := .f64 }
    let mut dimSeen : Array Bool := Array.replicate stateSig.shape.size false
    for h2 : i in [0 : st.advancingDims.size] do
      let d := st.advancingDims[i]
      unless d < stateSig.shape.size do throw (.advancingDimOutOfRange si d stateSig.shape.size)
      if dimSeen.getD d false then throw (.duplicateAdvancingDim si d)
      dimSeen := dimSeen.set! d true
      unless stateSig.shape.getD d 0 == raw.historyExtents.getD i 0 do
        throw (.advancingSizeMismatch si i (raw.historyExtents.getD i 0) (stateSig.shape.getD d 0))
    unless st.materialization == .completeHistory do
      throw (.materializationPolicyNotAdmitted si st.materialization)
  unless raw.iterationOrder == .axisZeroFastest do
    throw (.iterationOrderNotAdmitted raw.iterationOrder)
  unless raw.boundaryPolicy == .zeroThenBaseOverlay do
    throw (.boundaryPolicyNotAdmitted raw.boundaryPolicy)
  unless raw.snapshotPolicy == .immutablePreStep do
    throw (.snapshotPolicyNotAdmitted raw.snapshotPolicy)
  unless raw.baseBlock.contextShape == #[] do throw (.baseBlockContextNotEmpty raw.baseBlock.contextShape)
  unless raw.stepBlock.contextShape == stepExtents do
    throw (.stepBlockContextMismatch stepExtents raw.stepBlock.contextShape)
  let checkedBase ← (checkPlanBlock raw.baseBlock).mapError .baseBlockError
  let checkedStep ← (checkPlanBlock raw.stepBlock).mapError .stepBlockError
  checkCaptures sigs raw.baseBlock raw.baseCaptures raw.states.size raw.states true
  checkCaptures sigs raw.stepBlock raw.stepCaptures raw.states.size raw.states false
  let baseRowsByState ← checkWrites sigs raw.baseBlock raw.baseWrites raw.states true
  let stepRowsByState ← checkWrites sigs raw.stepBlock raw.stepWrites raw.states false
  for h : si in [0 : raw.states.size] do
    if (baseRowsByState.getD si #[]).size == 0 then throw (.noBaseWriteForState si) else pure ()
    match (stepRowsByState.getD si #[]).size with
    | 0 => throw (.noStepWriteForState si)
    | 1 => pure ()
    | _ => throw (.multipleStepWritesForState si 0 1)
  -- Task 2 inserts the causality pass here, before the return below.
  return CheckedScanPlan.mk raw checkedBase checkedStep stepExtents

end LeanNCD.Eval.Plan
