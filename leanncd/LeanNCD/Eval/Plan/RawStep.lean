-- leanncd/LeanNCD/Eval/Plan/RawStep.lean
import LeanNCD.Eval.Plan.Kernel

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

/-- A local, acyclic, context-parameterized dataflow graph — the base block or the step block of a
    scan (proposal §6.2). Relocated from `Block.lean` (F2): this type only ever needed
    `Kernel.lean` (`AssignPlan`, `TensorSlot`, `TensorSignature`) — `checkPlanBlock`/`runDenseBlock`
    are what need `checkAssign`/`runDenseAssignAt`, not this definition. Moving it here (instead of
    leaving it in `Block.lean`) is what lets `RawEvalPlan` (`Graph.lean`) reference `RawScanPlan`
    without a circular import — see this plan's Architecture section for the full argument. -/
structure RawPlanBlock where
  contextShape : Array Nat
  tensorSigs   : Array TensorSignature
  inputs       : Array TensorSlot
  assignments  : Array AssignPlan
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

/-- One outer graph node: an ordinary local assignment, or a scan. `RawEvalPlan.steps` becomes
    `Array PlanStep` in F3 (was `Array AssignPlan`). -/
inductive PlanStep
  | assign (a : AssignPlan)
  | scan   (s : RawScanPlan)
  deriving DecidableEq, BEq, Repr, Inhabited

end LeanNCD.Eval.Plan
