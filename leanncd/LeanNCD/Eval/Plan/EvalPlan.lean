-- leanncd/LeanNCD/Eval/Plan/EvalPlan.lean
import LeanNCD.Eval.Plan.Scan

/-!
# Wave F outer-graph integration (F3, Task 4)

Relocates `checkPlan`/`CheckedEvalPlan` (previously `Check.lean`) and `runDensePlan` (previously
`Dense.lean`) here, generalized to `PlanStep`, and adds real multi-output dispatch to
`checkScanPlan`/`runDenseScan` (`Scan.lean`). This is the only module that can see both the
local-kernel checker/worker (`Check.lean`/`Dense.lean`) and the scan checker/worker (`Scan.lean`)
without a cycle: `Scan.lean` imports `Block.lean` imports `Dense.lean` imports `Check.lean`, so a
module downstream of `Scan.lean` is the first point where both halves are simultaneously visible.

Also relocates `PlanCompileCause`/`PlanCompileFailure` from `Error.lean`: `invalidPlan`'s payload is
now `PlanStepError`, which depends on `ScanPlanError` (`Scan.lean`) — the same acyclic-import
constraint one layer up, so both types move here too.
-/

namespace LeanNCD.Eval.Plan

/-- One outer step's checked meaning: either a local assignment or a scan. Replaces
    `CheckedEvalPlan.checkedNodes`'s previous element type, `CheckedAssignPlan`, now that outer
    nodes are no longer uniformly assignments. -/
inductive CheckedPlanStepEvidence
  | assign (c : CheckedAssignPlan)
  | scan   (c : CheckedScanPlan)
  deriving Repr

/-- A `PlanStep`'s outer-graph-visible source/destination slots — derived, not stored (proposal
    §6.6: "These are derived functions, not stored fields"). An assignment has one destination; a
    scan has one per state, plus every base/step external capture as a source alongside its own
    factor sources are already covered by the block's own checking. -/
def PlanStep.sourceSlots : PlanStep → Array TensorSlot
  | .assign a => a.terms.flatMap (·.factors.map (·.sourceSlot))
  | .scan s => (s.baseCaptures ++ s.stepCaptures).filterMap (fun c => match c.source with
      | .external slot => some slot | .state _ => none)

def PlanStep.destinationSlots : PlanStep → Array TensorSlot
  | .assign a => #[a.destinationSlot]
  | .scan s => s.states.map (·.destSlot)

/-- Evidence that a `RawEvalPlan`'s wiring is sound, generalized to `PlanStep`: every step is
    locally checked (via `checkAssign` or `checkScanPlan`), input slots are in-range/unique/ordered,
    no step's destination overwrites an existing slot, every read is from an input or an earlier
    destination, and every non-input slot is produced exactly once. A scan step's MULTIPLE
    destination slots are all marked produced together, atomically with respect to this outer-graph
    tracking — matching the scan's own atomic commit semantics one level up. -/
structure CheckedEvalPlan where private mk ::
  raw          : RawEvalPlan
  checkedNodes : Array CheckedPlanStepEvidence
  deriving Repr

/-- `checkPlan`'s error type, generalized from bare `PlanError` now that an outer step can fail
    either as a malformed assignment (unchanged `PlanError`, including its existing `nodeError`
    wrapper) or a malformed scan (`ScanPlanError`, not representable inside `PlanError` itself — see
    this plan's Architecture section for why). Derives the same four classes `PlanError`/
    `ScanPlanError` both already carry (`DecidableEq, BEq, Repr, Inhabited`), not just `Repr`, so
    downstream types built on top of it (`PlanCompileCause` below) can keep their own existing
    `DecidableEq`/`BEq`/`Inhabited` derivations. -/
inductive PlanStepError
  | assign (cause : PlanError)
  | scan   (stepIndex : Nat) (cause : ScanPlanError)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Validate an open evaluation graph. Generalizes Wave C's `checkPlan` (previously in `Check.lean`)
    to `PlanStep`: an ordinary node still uses `checkAssign` verbatim and requires empty context
    exactly as before; a scan node uses `checkScanPlan` and requires ALL of its declared destination
    slots to be currently unavailable (so none can already be produced) before checking, then marks
    all of them available together afterward. Every `PlanError`-shaped failure from the loop below is
    wrapped as `.assign (...)`; a `checkScanPlan` failure becomes `.scan ni e` directly (no
    double-wrapping through `nodeError`, since `ScanPlanError` already carries its own internal
    locators). -/
def checkPlan (raw : RawEvalPlan) : Except PlanStepError CheckedEvalPlan := do
  unless raw.numericMode == .reference64SumProduct do
    throw (.assign (.numericModeNotAdmitted raw.numericMode))
  let n := raw.tensorSigs.size
  for h : i in [0 : raw.inputSlots.size] do
    let s := raw.inputSlots[i]
    unless s < n do throw (.assign (.slotOutOfRange s n))
    if h2 : i + 1 < raw.inputSlots.size then
      let s2 := raw.inputSlots[i + 1]
      if s == s2 then throw (.assign (.duplicateInputSlot s))
      else if s2 < s then throw (.assign (.inputSlotsNotOrdered i))
  let mut available : Array Bool := Array.replicate n false
  let mut producedBy : Array (Option Nat) := Array.replicate n none
  for s in raw.inputSlots do
    available := available.set! s true
  let mut checkedNodes : Array CheckedPlanStepEvidence := #[]
  for h : ni in [0 : raw.steps.size] do
    let step := raw.steps[ni]
    for src in step.sourceSlots do
      match available[src]? with
      | none => throw (.assign (.nodeError ni (.slotOutOfRange src n)))
      | some true => pure ()
      | some false => throw (.assign (.invalidForwardRead ni 0 0 src))
    let dests := step.destinationSlots
    for dest in dests do
      match available[dest]? with
      | none => throw (.assign (.nodeError ni (.slotOutOfRange dest n)))
      | some isAvail =>
          if isAvail then
            match producedBy[dest]?.join with
            | none => throw (.assign (.inputSlotOverwritten dest ni))
            | some firstNode => throw (.assign (.duplicateDestination dest firstNode ni))
    match step with
    | .assign a =>
        unless a.contextShape == #[] do throw (.assign (.topLevelContextNotEmpty ni))
        match checkAssign raw.tensorSigs a with
        | .error e => throw (.assign (.nodeError ni e))
        | .ok c => checkedNodes := checkedNodes.push (.assign c)
    | .scan s =>
        match checkScanPlan raw.tensorSigs s with
        | .error e => throw (.scan ni e)
        | .ok c => checkedNodes := checkedNodes.push (.scan c)
    for dest in dests do
      available := available.set! dest true
      producedBy := producedBy.set! dest (some ni)
  for h : i in [0 : n] do
    unless available[i]! do throw (.assign (.missingProduction i))
  return CheckedEvalPlan.mk raw checkedNodes

/-- Execute a checked graph over positional Dense inputs. Generalizes `runDensePlan` (previously in
    `Dense.lean`): a `.assign` node uses `runDenseAssign` exactly as before; a `.scan` node uses
    `runDenseScan` and writes every one of its state destinations into the store. -/
def runDensePlan (c : CheckedEvalPlan) (inputs : Array DenseTensor) :
    Except PositionalInputError (Array DenseTensor) := do
  let raw := c.raw
  unless inputs.size == raw.inputSlots.size do
    throw (.arityMismatch raw.inputSlots.size inputs.size)
  let n := raw.tensorSigs.size
  let placeholder : DenseTensor := { shape := [], data := #[] }
  let mut store : Array DenseTensor := Array.replicate n placeholder
  for h : i in [0 : raw.inputSlots.size] do
    let slot := raw.inputSlots[i]
    let t := inputs[i]!
    let sig := raw.tensorSigs.getD slot { shape := #[], dtype := .f64 }
    unless t.shape == sig.shape.toList do throw (.shapeMismatch slot sig.shape t.shape)
    unless t.data.size == sig.shape.toList.foldl (· * ·) 1 do
      throw (.storageMismatch slot t.shape t.data.size)
    store := store.set! slot t
  for node in c.checkedNodes do
    match node with
    | .assign c => store := store.set! c.plan.destinationSlot (← runDenseAssign c store)
    | .scan c => store ← runDenseScan raw.tensorSigs c store
  return store

/-- §5.5's sketch, verified as-is. Relocated from `Error.lean` (see that file's note): `invalidPlan`'s
    payload is `PlanStepError`, defined just above, which needs `ScanPlanError` (`Scan.lean`) — one
    layer downstream of where `Error.lean` sits in the import graph. Does NOT derive `Repr`:
    `ShapeError` (an existing sibling type) has no `Repr` instance, and `Repr` derivation requires
    every constructor's payload to support it, unlike `DecidableEq`/`Inhabited`. -/
inductive PlanCompileCause
  | inputSignature (cause : InputSignatureError)
  | capability     (cause : CapabilityError)
  | shape          (cause : ShapeError)
  | invalidPlan    (cause : PlanStepError)
  | bindings       (cause : BindingsError)
  deriving DecidableEq, BEq, Inhabited

/-- Same finding applies here: `EvalWarning` also has no `Repr`, so this likewise derives
    `DecidableEq, BEq, Inhabited` but not `Repr`. `#guard`-based equality testing is unaffected —
    `DecidableEq`/`BEq` are exactly what `==` needs, and both derive cleanly. -/
structure PlanCompileFailure where
  cause    : PlanCompileCause
  warnings : List EvalWarning
  deriving DecidableEq, BEq, Inhabited

end LeanNCD.Eval.Plan
