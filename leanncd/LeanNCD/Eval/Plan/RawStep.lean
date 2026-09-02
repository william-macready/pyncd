-- leanncd/LeanNCD/Eval/Plan/RawStep.lean
import LeanNCD.Eval.Plan.Kernel
import LeanNCD.Eval.Plan.Nonlin

namespace LeanNCD.Eval.Plan

/-- Which values a scan actually returns. Wave F admits exactly one policy. -/
inductive MaterializationPolicy
  | completeHistory
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Coordinate enumeration order over a scan's recurrence domain. Wave F admits exactly one. -/
inductive ScanIterationOrder
  | axisZeroFastest
  deriving DecidableEq, BEq, Repr, Inhabited

/-- How complete state histories are initialized before base writes apply. Wave F admits exactly
    one. -/
inductive ScanBoundaryPolicy
  | zeroThenBaseOverlay
  deriving DecidableEq, BEq, Repr, Inhabited

/-- What a step block's state captures observe. Wave F admits exactly one. -/
inductive ScanSnapshotPolicy
  | immutablePreStep
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One persistent scan state: the outer graph slot that receives its complete history, which of
    its own tensor dimensions are advancing (in scan-context order, so `advancingDims[i]` is the
    state dimension driven by context position `i`), and how it materializes. -/
structure StateSlot where
  destSlot        : TensorSlot
  advancingDims   : Array Nat
  materialization : MaterializationPolicy
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Where a block input's value comes from: an already-available outer graph slot, or a snapshot
    of one persistent state (by index into `RawScanPlan.states`). -/
inductive CaptureSource
  | external (outerSlot : TensorSlot)
  | state    (stateIndex : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One block-input binding. -/
structure BlockCapture where
  inputSlot : TensorSlot
  source    : CaptureSource
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One state write: a block output slot's value, placed into complete state `stateIndex` through
    `map`. `map`'s domain is `context ++ outputSlice` (empty context for a base write); its
    codomain is the complete state's own rank, one row per state dimension. Reuses `AffineMap`
    unchanged rather than inventing a second placement-map type. -/
structure StateWriteMap where
  outputSlot : TensorSlot
  stateIndex : Nat
  map        : AffineMap
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One step of a local plan block: an ordinary context-parameterized assignment, or one of the two
    nonlinearity operations (Thread 4's `RawPointwisePlan`/`RawAxiswisePlan`). Generalizes
    `RawPlanBlock`'s former assignment-only element type so a block can express the
    `assign → pointwise/axiswise` chain a nonlinear statement lowers to
    (`papers/nonlinearity_split_pair_direct_lowering.md` §3.5). Deliberately a separate sum from
    `PlanStep` below rather than a reuse of it: a block step has no `.scan` case (scans do not
    nest), and its nonlinear cases carry no `contextShape` of their own. -/
inductive BlockStep
  | assign (a : AssignPlan)
  | pointwise (p : RawPointwisePlan)
  | axiswise (a : RawAxiswisePlan)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Every slot this step reads: `.assign` flattens its per-term factor reads, the two nonlinear
    kinds read exactly one. Symmetric with `PlanStep.sourceSlots` (`EvalPlan.lean`) and provided
    for the same reason — but note `checkPlanBlock` does NOT route through it, for the same reason
    `checkPlan` does not for `.assign`: the forward-read check needs the original per-term/
    per-factor indices to fill `invalidForwardRead`'s payload, and the nonlinear arms read their
    single `sourceSlot` field directly. Retained as the symmetric half of the accessor pair; it has
    no call site today. -/
def BlockStep.sourceSlots : BlockStep → Array TensorSlot
  | .assign a => a.terms.flatMap TermPlan.readSourceSlots
  | .pointwise p => #[p.sourceSlot]
  | .axiswise a => #[a.sourceSlot]

/-- Every slot this step writes. All three kinds write exactly one, but the array shape is what
    `WiringNode.destinationSlots` takes, so `checkStepGraph` consumes every step kind uniformly. -/
def BlockStep.destinationSlots : BlockStep → Array TensorSlot
  | .assign a => #[a.destinationSlot]
  | .pointwise p => #[p.destinationSlot]
  | .axiswise a => #[a.destinationSlot]

/-- This step's own declared context shape, if it has one. Only `.assign` carries a
    `contextShape`; the two nonlinearity operations are context-free, so `checkPlanBlock`'s
    block-context obligation is vacuous for them rather than silently comparing against a
    default. -/
def BlockStep.contextShape? : BlockStep → Option (Array Nat)
  | .assign a => some a.contextShape
  | .pointwise _ | .axiswise _ => none

/-- Project the underlying `AssignPlan` of an `.assign` step, for a caller that cares only about
    assignments and has nothing to do for the other kinds. Used by the structural assertions over
    compiler-produced blocks in `test/Eval/Plan/ScanCompileTest.lean`, which would otherwise need a
    full `match` inside every field projection. Note `Scan.lean`'s assignment-only causality walk
    does NOT use it: that loop must bind the payload and fall through on the nonlinear kinds, which
    a direct `match` expresses without an intermediate `Option`. -/
def BlockStep.assign? : BlockStep → Option AssignPlan
  | .assign a => some a
  | .pointwise _ | .axiswise _ => none

/-- A local, acyclic, context-parameterized dataflow graph — the base block or the step block of a
    scan (proposal §6.2). Relocated from `Block.lean` (F2): this type only ever needed the raw
    node types (`Kernel.lean`'s `AssignPlan`/`TensorSlot`/`TensorSignature`, and since Task 3
    `Nonlin.lean`'s `RawPointwisePlan`/`RawAxiswisePlan` via `BlockStep`) — the CHECKERS and
    WORKERS (`checkPlanBlock`/`runDenseBlock`, and through them `checkAssign`/`runDenseAssignAt`
    and their nonlinear counterparts) are what live downstream, not this definition. Moving it here
    (instead of leaving it in `Block.lean`) is what lets `RawEvalPlan` (`Graph.lean`) reference
    `RawScanPlan` without a circular import — see this plan's Architecture section for the full
    argument. -/
structure RawPlanBlock where
  contextShape : Array Nat
  tensorSigs   : Array TensorSignature
  inputs       : Array TensorSlot
  steps        : Array BlockStep
  outputs      : Array TensorSlot
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One unchecked scan node: explicit states, base/step blocks, their captures and write maps, and
    the closed policies every checked scan admits in this version. -/
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

/-- One outer graph node: an ordinary local assignment, a scan, or one of the two nonlinearity
    operations (Thread 4). `RawEvalPlan.steps` becomes `Array PlanStep` in F3 (was `Array
    AssignPlan`). -/
inductive PlanStep
  | assign   (a : AssignPlan)
  | scan     (s : RawScanPlan)
  | pointwise (p : RawPointwisePlan)
  | axiswise  (a : RawAxiswisePlan)
  deriving DecidableEq, BEq, Repr, Inhabited

end LeanNCD.Eval.Plan
