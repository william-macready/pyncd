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
    in increasing order onto the block's own output axes, and no row may be unrecognized.

    The third clause states the "must BE `.free`" half explicitly rather than leaving it implied by
    the fourth clause's positional cover. Without it the fourth clause's `filterMap` maps a
    non-`.free` row at a non-advancing dimension to `none` and DROPS it from the
    `List.range outputShapeSize` comparison entirely — so an `.advancing i` row sitting at a
    dimension that is not `advancingDims[i]` (indeed at no advancing dimension at all) was admitted,
    and was then invisible to both value checks downstream: `freeExtentsAgree` matches only `.free`
    and `pinnedLiteralsInRange` only `.pinned`. Such a row reached `commitWrite` completely
    unbounded — its coordinate is `ctx[i] + 1`, bounded only by the extent of a DIFFERENT dimension
    (`advancingSizeMismatch` relates `stateShape[advancingDims[i]]` to `historyExtents[i]` and says
    nothing about a dimension outside `advancingDims`). The final F4 review's repro, state `#[4,2]`
    with `advancingDims := #[0]` and dim 1 also `.advancing 0`, produced all three failure modes in
    one run: an in-range write by luck, a silent aliasing write into an unrelated cell, and an
    out-of-range `Array.set!` that panicked and dropped the write with no diagnostic. The same hole
    admitted a `.pinned` row at a non-advancing dimension too — memory-safe, since
    `pinnedLiteralsInRange` range-checks it, but still not the canonical rectangular all-axis `+1`
    geometry §5.1/§7.3 fix, and it leaves slices of the state silently unwritten. This is the fourth
    instance of one gap shape across F3/F4 (free extents, pinned literals, write-map rank, this):
    a geometry predicate that says which rows MUST be a given kind without saying which rows MAY
    NOT be. -/
def stepWriteRowsOk (advancingDims : Array Nat) (outputShapeSize : Nat)
    (rows : Array (Option WriteRowKind)) : Bool :=
  rows.all Option.isSome &&
  (advancingDims.toList.zipIdx.all (fun (d, i) => rows.getD d none == some (.advancing i))) &&
  (rows.toList.zipIdx.all (fun (r, d) => advancingDims.contains d ||
    (match r with | some (.free _) => true | _ => false))) &&
  ((rows.toList.zipIdx.filterMap (fun (r, d) =>
      if advancingDims.contains d then none else match r with
        | some (.free p) => some p | _ => none))
    == List.range outputShapeSize)

/-- For every `.free` row, the state's own dimension size must equal the block output's size at the
    corresponding free position — proposal §7.3's "write-result signature agreement with the
    unpinned state dimensions", previously checked only for rank/position, never for size. Without
    it, a write whose free face is WIDER than the state's own dimension writes out of its declared
    region (silently into another row's cells, or past the end of the tensor entirely); a NARROWER
    one leaves part of the region it claims to cover unwritten. At its only call site it runs AFTER
    `baseWriteRowsOk`/`stepWriteRowsOk` have admitted the geometry, which forces `rows.size` to be
    the state's rank and every free position to be in range — so neither `getD` default is
    reachable there. -/
def freeExtentsAgree (stateShape : Array Nat) (outputShape : Array Nat)
    (rows : Array (Option WriteRowKind)) : Bool :=
  rows.toList.zipIdx.all (fun (r, d) => match r with
    | some (.free p) => stateShape.getD d 0 == outputShape.getD p 0
    | _ => true)

/-- Every `.pinned` row's literal must be a valid in-range coordinate for its own state dimension —
    proposal §7.3's write-result signature agreement extended to pinned (not just free) positions.
    `.free`/`.advancing` rows are vacuously fine (their range is already bounded by the checked
    output/context shapes elsewhere). Sibling of `freeExtentsAgree`, same failure class: geometry
    admission recognizes a row as `.pinned lit` without ever looking at `lit`'s VALUE, so
    `baseWriteRowsOk`'s "some advancing dimension is pinned to `0`" rule leaves every OTHER pinned
    literal — and any pinned literal on a non-advancing dimension — completely unconstrained. A base
    write like `dp[5, 0] := ONE` on a `[2,2]` state was accepted, and `runDenseScan` then either
    panicked in `Array.set!` or committed to the wrong cell. -/
def pinnedLiteralsInRange (stateShape : Array Nat) (rows : Array (Option WriteRowKind)) : Bool :=
  rows.toList.zipIdx.all (fun (r, d) => match r with
    | some (.pinned lit) => 0 ≤ lit && lit.toNat < stateShape.getD d 0
    | _ => true)

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

/-- Whether one read row (for state dimension `d`, whose scan-context position is `ctxPos`) is
    causal: exactly one nonzero coefficient, equal to `1`, at `ctxPos`, and non-positive bias. This
    single row-shape rule captures all three cases of proposal §7.4's causality obligation
    uniformly — out-of-bounds zero-padding, initialized-boundary reads, and a strictly-earlier
    recurrence producer are not case-split here: a canonical `q + 1` successor write makes every row
    satisfying this shape resolve to one of those three automatically, regardless of the concrete
    bias value or declared extents (the checker "tests this implication directly over the canonical
    geometry," per §7.4, rather than leaving it as worker folklore). -/
def causalAdvancingRow (row : Array Int) (bias : Int) (ctxPos : Nat) : Bool :=
  let nz := row.toList.zipIdx.filter (fun (c, _) => c != 0)
  match nz with
  | [(c, p)] => c == 1 && p == ctxPos && bias ≤ 0
  | _ => false

/-- Every advancing dimension of a captured state's read must be causal at its own scan-context
    position; non-advancing dimensions are ordinary reads and carry no causality obligation. -/
def stateReadCausal (advancingDims : Array Nat) (contextPos : Array Nat) (f : ReadPlan) : Bool :=
  advancingDims.size == contextPos.size &&
  (Array.range advancingDims.size).all (fun i =>
    causalAdvancingRow (f.map.coeffs.getD (advancingDims.getD i 0) #[])
      (f.map.bias.getD (advancingDims.getD i 0) 0) (contextPos.getD i 0))

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
  | writeCoeffRankMismatch        (isBase : Bool) (writeIndex stateIndex expected actual : Nat)
  | writeBiasRankMismatch         (isBase : Bool) (writeIndex stateIndex expected actual : Nat)
  | writeGeometryNotAdmitted      (isBase : Bool) (writeIndex : Nat)
  | writeFreeExtentMismatch       (isBase : Bool) (writeIndex stateIndex : Nat)
                                  (stateShape outputShape : Array Nat)
  | writePinnedLiteralOutOfRange  (isBase : Bool) (writeIndex stateIndex : Nat)
                                  (stateShape : Array Nat)
  | baseWritesOverlap             (stateIndex firstWriteIndex secondWriteIndex : Nat)
  | iterationOrderNotAdmitted     (order : ScanIterationOrder)
  | boundaryPolicyNotAdmitted     (policy : ScanBoundaryPolicy)
  | snapshotPolicyNotAdmitted     (policy : ScanSnapshotPolicy)
  | materializationPolicyNotAdmitted (stateIndex : Nat) (policy : MaterializationPolicy)
  | causalityFailure              (stateIndex blockStepIndex termIndex factorIndex : Nat)  -- F3 Task 2
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Evidence that one `RawScanPlan` is a sound checked scan: both blocks are checked, every
    capture/write obligation in proposal §7.3 holds, and causality holds for every state read.
    `stepExtents` is retained rather than recomputed by every consumer.

    There is deliberately no separate `CausalityCertificate` type or field: the certificate IS
    `checkScanPlan`'s own causality loop over `stateReadCausal`, and a `CheckedScanPlan` value's
    existence — obtainable only through `checkScanPlan`, since `mk` is `private` — is itself the
    evidence a worker relies on. Storing a redundant marker field would add a second thing to keep
    in sync with the check that already ran. -/
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
    declared output is written by exactly one write, every write's `AffineMap` has exactly one
    coefficient ROW and one bias ENTRY per the state's own rank (checked here, BEFORE
    `writeRowKinds` ever reads either array: `writeRowKinds`/`classifyWriteRow` read row `d` via
    `Array.getD d ...`, which silently substitutes a zero-row/zero-bias default for a SHORT array
    rather than rejecting it, so an under-length `coeffs`/`bias` would otherwise be admitted as if
    its missing rows were all-zero; an OVER-length array would instead have its excess rows silently
    ignored — both checked here independently, since `coeffs` and `bias` are separate arrays that
    can disagree with the state's rank independently of each other), base-write geometry is admitted
    and pairwise disjoint across each state's FULL write list, step-write geometry is admitted, and
    every
    admitted write's free rows agree in SIZE with the state's own dimensions (`freeExtentsAgree` —
    geometry admission covers only rank/position) and every pinned row's LITERAL is an in-range
    coordinate of that dimension (`pinnedLiteralsInRange` — geometry admission never inspects a
    pinned literal's value beyond the single "some advancing dimension is `0`" rule). Returns, per
    state, the accepted row
    classifications PAIRED with each write's original global index `wi` (so a caller needing a real
    locator — e.g. `multipleStepWritesForState`'s first/second write index — doesn't have to
    re-derive it), so the caller can additionally require exactly one step write and at least one
    base write. -/
private def checkWrites (sigs : Array TensorSignature) (block : RawPlanBlock)
    (writes : Array StateWriteMap) (states : Array StateSlot) (isBase : Bool) :
    Except ScanPlanError (Array (Array (Nat × Array (Option WriteRowKind)))) := do
  let mut writtenOutputs : Array (Option Nat) := Array.replicate block.tensorSigs.size none
  let mut rowsByState : Array (Array (Nat × Array (Option WriteRowKind))) :=
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
    let stateShape := (sigs.getD st.destSlot { shape := #[], dtype := .f64 }).shape
    let contextWidth := if isBase then 0 else st.advancingDims.size
    unless w.map.coeffs.size == stateShape.size do
      throw (.writeCoeffRankMismatch isBase wi w.stateIndex stateShape.size w.map.coeffs.size)
    unless w.map.bias.size == stateShape.size do
      throw (.writeBiasRankMismatch isBase wi w.stateIndex stateShape.size w.map.bias.size)
    let rows := writeRowKinds stateShape.size contextWidth w
    let outputShape := (block.tensorSigs.getD w.outputSlot { shape := #[], dtype := .f64 }).shape
    let admitted := if isBase then baseWriteRowsOk st.advancingDims outputShape.size rows
                    else stepWriteRowsOk st.advancingDims outputShape.size rows
    unless admitted do throw (.writeGeometryNotAdmitted isBase wi)
    unless freeExtentsAgree stateShape outputShape rows do
      throw (.writeFreeExtentMismatch isBase wi w.stateIndex stateShape outputShape)
    unless pinnedLiteralsInRange stateShape rows do
      throw (.writePinnedLiteralOutOfRange isBase wi w.stateIndex stateShape)
    rowsByState := rowsByState.set! w.stateIndex (rowsByState.getD w.stateIndex #[] |>.push (wi, rows))
  for outputSlot in block.outputs do
    unless writtenOutputs.getD outputSlot none |>.isSome do
      throw (.blockOutputNotWritten isBase outputSlot)
  -- pairwise disjointness across each state's FULL base-write list (proposal §7.3: not just
  -- checked between an arbitrarily chosen pair; index into each state's own accumulated write
  -- list, not the raw `writes` array — deliberately per-state-local indices `a`/`b`, not the
  -- global `wi`s now carried alongside each entry's rows, confirmed correct and intentional by
  -- review: `baseWritesOverlap`'s locator is "which of this state's own writes collided", not
  -- "which raw write index", so `.2` (the rows) is all this loop needs).
  if isBase then
    for h : si in [0 : rowsByState.size] do
      let stateRows := rowsByState[si]
      for h2 : a in [0 : stateRows.size] do
        for h3 : b in [0 : stateRows.size] do
          if a < b then
            if writesCollide stateRows[a].2 stateRows[b].2 then throw (.baseWritesOverlap si a b)
  return rowsByState

/-- Validate an unchecked scan node (proposal §7.3), INCLUDING causality: the final loop before
    `return` walks every `.assign` step-block factor that reads a captured state and requires
    `stateReadCausal` of it, so a look-ahead or loop-axis-ignoring state read is rejected here
    rather than left as a worker-side assumption (proposal §7.4).

    **Why walking only `.assign` steps is complete.** A block's nonlinear steps
    (`.pointwise`/`.axiswise`) have no term/factor structure and so no state read to classify, but
    that alone would not justify skipping them — a nonlinear step reading a captured state
    directly, or an assignment reading a nonlinear step that read one, would launder a non-causal
    read past this loop.

    Neither is reachable, but **the argument needs four guards, not one**, and three of them live
    outside this function. `checkPlanBlock` (`Block.lean`) runs first, above; then:

    1. its `nonlinearSourceNotLocalAssignment` admits a nonlinear step only when its source is a
       PRECEDING `.assign` step's destination;
    2. `checkStepGraph`'s `inputSlotOverwritten` stops an assignment ever writing a declared block
       input, so `.assign` destinations are disjoint from `block.inputs`;
    3. `checkCaptures`' `captureTargetsNonInput` (this file, above) forces every state capture's
       `inputSlot` to BE a declared block input;
    4. `checkStepGraph`'s `duplicateDestination` stops a nonlinear step aliasing a preceding
       assignment's destination.

    (1)∧(2)∧(3) is what actually yields "a nonlinear step's source is never a capture" — (1) alone
    does not. (4) yields "never another nonlinear step's result." Given those, every path from a
    captured state into a nonlinearity passes through an assignment this loop inspects, and an
    assignment reading a nonlinear result reads a non-capture slot, so no obligation is dropped.
    **Weakening any one of the four reopens the hole**, including in files this one does not
    mention — see `checkPlanBlock`'s own docstring for the worked failure scenario. The block-level
    fixtures pinning legs (1) and (2), and the scan-level fixture pinning that block checking runs
    before this loop at all, are in `test/Eval/Plan/ScanTest.lean` and `BlockTest.lean`.

    The loop enumerates the UNFILTERED `steps` array, so `causalityFailure`'s `blockStepIndex` is a
    position in `stepBlock.steps` — NOT a position in a filtered assignment sublist. The two
    coincide in any block whose steps are all assignments, which is why every pre-existing fixture
    passes either way; `ScanTest.lean`'s `stepBlockNonlinBetweenAssignsG` is the one that pins the
    difference, by putting a nonlinear step between two assignments so the offending assignment sits
    at block-step index 2 and filtered index 1. -/
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
    let stateStepWrites := stepRowsByState.getD si #[]
    match stateStepWrites.size with
    | 0 => throw (.noStepWriteForState si)
    | 1 => pure ()
    | _ =>
        throw (.multipleStepWritesForState si (stateStepWrites.getD 0 (0, #[])).1
          (stateStepWrites.getD 1 (0, #[])).1)
  let stateCaptureFor : TensorSlot → Option Nat := fun inputSlot =>
    (raw.stepCaptures.find? (fun c => c.inputSlot == inputSlot)).bind (fun c => match c.source with
      | .state si => some si | .external _ => none)
  for h : ai in [0 : raw.stepBlock.steps.size] do
    match raw.stepBlock.steps[ai] with
    | .pointwise _ | .axiswise _ => pure ()
    | .assign a =>
        for h2 : ti in [0 : a.terms.size] do
          let t := a.terms[ti]
          for h3 : fi in [0 : t.factors.size] do
            match t.factors[fi] with
            | .iverson _ => pure ()  -- predicate factor captures no state; keep `fi` at all-factor index
            | .read f =>
              match stateCaptureFor f.sourceSlot with
              | none => pure ()
              | some si =>
                  let st := raw.states.getD si default
                  unless stateReadCausal st.advancingDims t.contextPos f do
                    throw (.causalityFailure si ai ti fi)
  return CheckedScanPlan.mk raw checkedBase checkedStep stepExtents

/-- `rank_D(q) = sum_i q[i] * product_{j<i} D[j]` (proposal §6.6): axis `0` varies fastest. -/
def mixedRadixRank (D : Array Nat) (q : Array Nat) : Nat :=
  (Array.range D.size).foldl (fun acc i =>
    acc + q.getD i 0 * (Array.range i).foldl (fun p j => p * D.getD j 1) 1) 0

/-- Inverse of `mixedRadixRank`: axis `0` decoded first (fastest-varying), matching
    `ScanIterationOrder.axisZeroFastest`. Deliberately independent from `Coordinates.lean`'s
    `allCoords` (last-index-fastest, the local-kernel's own row-major convention) — proposal §9.3:
    "Rank/unrank belongs to the scan worker and is intentionally independent from the local
    assignment kernel's coordinate enumerator." -/
def mixedRadixUnrank (D : Array Nat) (r : Nat) : Array Nat := Id.run do
  let mut rem := r
  let mut q : Array Nat := #[]
  for d in D do
    q := q.push (rem % d)
    rem := rem / d
  return q

def mixedRadixDomainSize (D : Array Nat) : Nat := D.foldl (· * ·) 1

/-- Place one write's value(s) into a complete-state tensor. `ctx` is the write's context portion
    (empty for base, the current recurrence coordinate for step); the write's full domain is
    `ctx ++ outputCoord` for every coordinate `outputCoord` of the block's own output tensor at
    `w.outputSlot` (proposal §6.5) — a write with a genuinely FREE position (e.g. a face write like
    `dp[0, j] := ROWFACE[j]`) has a non-scalar output and must place every one of its elements, not
    just element `0`. Reduces to the scalar case cleanly: `allCoords [] = [[]]` (one iteration),
    `flatIndex [] [] = 0`, so a fully-pinned/advancing write (no free positions, scalar output)
    behaves exactly as a single-coordinate commit.

    **Bounds obligation this relies on.** Unlike `gatherFactor` (`Dense.lean`) and
    `Executable.lean`, this function does NOT call `inBoundsPerDim` before `flatIndex`: it performs
    no bounds recovery, trusting `checkScanPlan` the same way the base/step phases of
    `runDenseScan` below trust it.

    **First, a premise the row analysis below silently assumes: `out.shape` is a RUNTIME value, and
    every checker that bounds it reasons over the DECLARED `block.tensorSigs[w.outputSlot].shape`.**
    The two must agree. Before block steps generalized, that was one short step — `runDenseAssignAt`
    returns exactly `a.outputShape` and `checkAssign` forces `destSig.shape == a.outputShape`. A
    block output may now be produced by a `.pointwise`/`.axiswise` step instead, and the agreement
    then rests on a longer chain that lives in another file: `checkNonlinIO` (`Nonlin.lean`) forcing
    `srcSig.shape == declared shape == destSig.shape`, AND every arm of `PointwiseFn.apply`/
    `AxiswiseFn.apply` (`Eval/Nonlin.lean`) being shape-preserving — the axiswise arms via
    `perRowCore`, which only writes into an existing `acc` and never rebuilds a shape. All arms
    were audited and the invariant holds today.

    **If a future `AxiswiseFn` constructor ever reduces along its axis** (a `sum`/`argmax` that drops
    a dimension), that change looks entirely local to `Nonlin.lean` and `checkNonlinIO`'s
    shape-equality clause — and it would silently break this function: a step write whose output slot
    is that step's destination would enumerate a runtime shape smaller than the declared region the
    row checks approved, writing into another row's cells or panicking in `Array.set!`. That is
    verbatim the F3 free-extent / F4 advancing-row bug class. `checkNonlinIO`'s shape equality is
    therefore load-bearing for scan writes, not merely local geometry.

    Given that premise, row by row, per `writeRowKinds`/`baseWriteRowsOk`/`stepWriteRowsOk`:
    - a `.free p` row ranges over exactly `out.shape[p]`, which `freeExtentsAgree` forces to equal
      the state's own extent at that dimension (this was the gap the final F3 review found: before
      it, only the free positions' RANK/ORDER was checked, so a wider output face wrote into other
      rows' cells or past the end of the tensor);
    - an `.advancing i` row is `ctx[i] + 1`, with `ctx` from `mixedRadixUnrank c.stepExtents` and
      `stepExtents = historyExtents - 1`. `advancingSizeMismatch` ties `historyExtents[i]` to
      `stateShape[advancingDims[i]]` — and ONLY to that dimension — so this argument holds exactly
      because `stepWriteRowsOk` now forbids an `.advancing` row anywhere outside `advancingDims`
      (its third clause) while requiring the row at `advancingDims[i]` to be `.advancing i` (its
      second). Given both, the row's dimension IS `advancingDims[i]` and it stays within
      `[1, extent)`. This was the gap the final F4 review found: the third clause did not exist, an
      `.advancing` row at a non-advancing dimension was dropped from the positional cover instead of
      rejected, and the resulting coordinate was bounded by the wrong dimension's extent — aliasing
      into an unrelated in-bounds cell, or panicking in `Array.set!`;
    - a `.pinned lit` row is `lit` verbatim, and `pinnedLiteralsInRange` forces `0 ≤ lit` and
      `lit < stateShape[d]`. This was the SIBLING gap of the free-extent one, found while
      documenting that fix: `baseWriteRowsOk` requires only that SOME advancing dimension be pinned
      to `0`, leaving every other pinned literal unconstrained, so a hand-built base write
      `dp[5, 0] := ONE` on a `[2,2]` state was accepted here and reached `Array.set!` out of range
      (`lean_array_set_panic`, or a silent commit to the wrong cell). A guard HERE could not have
      fixed it (this function returns a `DenseTensor`, not an `Except`, so it could only silently
      drop the write) — it belongs in `checkWrites` beside `freeExtentsAgree`, which is where it
      now lives. -/
private def commitWrite (target : DenseTensor) (w : StateWriteMap) (blockStore : Array DenseTensor)
    (ctx : List Int) : DenseTensor := Id.run do
  let out := blockStore.getD w.outputSlot { shape := [], data := #[] }
  let mut target := target
  for oc in allCoords out.shape do
    let iter := ctx ++ oc
    let coord := (applyAffine w.map iter).map Int.toNat
    let v := out.data.getD (flatIndex out.shape (oc.map Int.toNat)) 0.0
    target := { target with data := target.data.set! (flatIndex target.shape coord) v }
  return target

/-- The general Dense scan worker (proposal §9): allocate, apply every checked base write, then for
    each recurrence coordinate in increasing mixed-radix rank, bind an immutable pre-step snapshot,
    run the checked step block, and commit every designated next-state slice simultaneously.
    Independent of `Eval.evalScan`/`evalScheduled` by construction — imports neither, builds no
    `HashMap UID Int`, knows no source names (proposal §9.1). `sigs` supplies each state's declared
    complete shape for allocation.

    **Capture-order obligation.** `runDenseBlock` treats its `inputs : Array DenseTensor` argument as
    POSITIONAL against `block.inputs` — `inputs[i]` binds to `raw.inputs[i]` — and `block.inputs` is
    sorted/deduplicated by `checkPlanBlock`. Each block's input-value array below is therefore built
    by resolving, for every slot in `raw.baseBlock.inputs`/`raw.stepBlock.inputs` (in THAT order), the
    unique capture whose `inputSlot` matches it — a lookup, not a positional pass-through — rather
    than by mapping over `raw.baseCaptures`/`raw.stepCaptures` in their own stored order. A capture
    array is only guaranteed order-INSENSITIVE-valid by `checkCaptures` (every input captured exactly
    once, as a set); nothing ties its storage order to `block.inputs`' sorted order, so a caller
    supplying captures in any other order would otherwise have this function silently bind the wrong
    tensor to the wrong `runDenseBlock` input position. -/
def runDenseScan (sigs : Array TensorSignature) (c : CheckedScanPlan) (outerStore : Array DenseTensor) :
    Except PositionalInputError (Array DenseTensor) := do
  let raw := c.raw
  let mut states : Array DenseTensor := raw.states.map (fun st =>
    let sig := sigs.getD st.destSlot { shape := #[], dtype := .f64 }
    { shape := sig.shape.toList, data := Array.replicate (sig.shape.toList.foldl (· * ·) 1) 0.0 })
  let baseExternalInputs ← raw.baseBlock.inputs.mapM (fun inputSlot =>
    match raw.baseCaptures.find? (fun cap => cap.inputSlot == inputSlot) with
    | none => throw (PositionalInputError.arityMismatch 0 0)  -- unreachable: checked (checkCaptures)
    | some cap => match cap.source with
      | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
      | .state _ => throw (PositionalInputError.arityMismatch 0 0))  -- unreachable: checked
  let baseStore ← runDenseBlock c.checkedBase [] baseExternalInputs
  for w in raw.baseWrites do
    let target := states.getD w.stateIndex { shape := [], data := #[] }
    states := states.set! w.stateIndex (commitWrite target w baseStore [])
  let domainSize := mixedRadixDomainSize c.stepExtents
  for r in [0 : domainSize] do
    let q := mixedRadixUnrank c.stepExtents r
    let oldStates := states
    let stepInputs ← raw.stepBlock.inputs.mapM (fun inputSlot =>
      match raw.stepCaptures.find? (fun cap => cap.inputSlot == inputSlot) with
      | none => throw (PositionalInputError.arityMismatch 0 0)  -- unreachable: checked (checkCaptures)
      | some cap => match cap.source with
        | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
        | .state si => pure (oldStates.getD si { shape := [], data := #[] }))
    let ctx : List Int := q.toList.map Int.ofNat
    let stepStore ← runDenseBlock c.checkedStep ctx stepInputs
    let mut nextStates := states
    for w in raw.stepWrites do
      let target := nextStates.getD w.stateIndex { shape := [], data := #[] }
      nextStates := nextStates.set! w.stateIndex (commitWrite target w stepStore ctx)
    states := nextStates
  let mut result := outerStore
  for h : si in [0 : raw.states.size] do
    result := result.set! raw.states[si].destSlot (states.getD si { shape := [], data := #[] })
  return result

end LeanNCD.Eval.Plan
