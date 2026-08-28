-- leanncd/LeanNCD/Eval/Plan/Block.lean
import LeanNCD.Eval.Plan.Dense

/-!
# Wave F checked plan-block vertical slice (F2)

A local, acyclic, context-parameterized dataflow graph — the base block or the step block of a
future scan (`papers/wave_f_scanplan_proposal.md` §6.2). Local assignments are plain `AssignPlan`s
sharing this block's `contextShape` — the same node type the outer graph uses (`Graph.lean`'s
`RawEvalPlan.steps`), so F2 introduces no second local-operation representation.
`checkPlanBlock` is the local-graph analogue of `checkPlan` (proposal §7.2), not a special
evaluator convention: it reuses `checkAssign` per node and the identical availability/production-
order wiring loop `checkPlan` already applies to the outer graph. `runDenseBlock` is the
corresponding analogue of `runDensePlan`, reusing `runDenseAssignAt` per node. No scan constructor
exists yet — `RawEvalPlan` is untouched by this file.
-/

namespace LeanNCD.Eval.Plan

inductive CheckedBlockStepEvidence
  | assign (c : CheckedAssignPlan)
  | pointwise (c : CheckedPointwisePlan)
  | axiswise (c : CheckedAxiswisePlan)
  deriving Repr

/-- A raw `RawPlanBlock` violates a local-graph invariant. `wiring` reuses `PlanError` verbatim for
    every failure mode `checkPlanBlock`'s wiring loop shares with `checkPlan`'s outer-graph loop
    (slot range, input uniqueness/order, overwrite, duplicate destination, missing production,
    invalid forward read, and per-node `checkAssign` failure) — no second copy of those
    constructors. Only the two obligations a block has and the outer plan does not get their own
    constructors. -/
inductive BlockError
  | wiring                (cause : PlanError)
  | duplicateOutputSlot   (slot : TensorSlot)
  | blockContextMismatch  (nodeIndex : Nat) (expected actual : Array Nat)
  | nonlin (nodeIndex : Nat) (cause : NonlinPlanError)
  | nonlinearSourceNotLocalAssignment (nodeIndex : Nat) (sourceSlot : TensorSlot)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- First slot in `slots` that recurs later in the list, if any. Mirrors `Prepared.lean`'s
    `firstDuplicateName`, generalized to `TensorSlot` so `duplicateOutputSlot` can carry a
    witness. -/
private def firstDuplicateSlot : List TensorSlot → Option TensorSlot
  | [] => none
  | s :: rest => if rest.contains s then some s else firstDuplicateSlot rest

/-- Evidence that one `RawPlanBlock` is a sound local graph: every local assignment is checked
    against `block.contextShape`, inputs are in-range/unique/ordered, outputs are in-range/unique,
    no assignment overwrites an input, and every non-input local slot — outputs included — is
    produced exactly once. -/
structure CheckedPlanBlock where private mk ::
  raw          : RawPlanBlock
  checkedNodes : Array CheckedBlockStepEvidence
  deriving Repr

/-- One node of a shared availability/production-order wiring loop, generalized from `checkPlan`'s
    and `checkPlanBlock`'s near-identical loops (see this module's own `checkPlanBlock` and
    `EvalPlan.lean`'s `checkPlan`, both built on this). Every genuinely shared `PlanError`-shaped
    failure (slot range, input ordering, overwrite, duplicate destination, missing production) is
    embedded through exactly one caller-supplied function, `liftWiring : PlanError → E`
    (`checkStepGraph`'s own parameter, not a `WiringNode` field); what varies per call site and per
    node is the context obligation (`contextCheck`), which slots this node writes
    (`destinationSlots`), how its reads are validated against the current availability snapshot
    (`sourceCheck`), and its own local checker's result (`localCheck`). -/
structure WiringNode (E C : Type) where
  contextCheck     : Except E Unit
  destinationSlots : Array TensorSlot
  sourceCheck      : Array Bool → Except E Unit
  localCheck       : Except E C

/-- Shared availability/production-order wiring loop: validate `inputs` (in-range, unique, ordered),
    then for each node in sequence — context check, destination-availability check (every declared
    destination, none already produced), source check against the availability snapshot as it
    stands BEFORE this node's own destinations are marked produced (so a self-aliasing
    source-equals-destination read is rejected via `sourceCheck`, never silently satisfied), the
    node's own local check, then mark every declared destination produced together — and finally
    confirm every non-input slot ended up produced. Preserves `checkPlan`/`checkPlanBlock`'s existing
    per-node order (context → destination → source → local-check) and their `Except`-short-circuit
    behavior by construction: a node past the first failure is never reached by the `for` loop. -/
def checkStepGraph {E C : Type} (n : Nat) (inputs : Array TensorSlot) (liftWiring : PlanError → E)
    (nodes : Array (WiringNode E C)) : Except E (Array C) := do
  for h : i in [0 : inputs.size] do
    let s := inputs[i]
    unless s < n do throw (liftWiring (.slotOutOfRange s n))
    if h2 : i + 1 < inputs.size then
      let s2 := inputs[i + 1]
      if s == s2 then throw (liftWiring (.duplicateInputSlot s))
      else if s2 < s then throw (liftWiring (.inputSlotsNotOrdered i))
  let mut available : Array Bool := Array.replicate n false
  let mut producedBy : Array (Option Nat) := Array.replicate n none
  for s in inputs do available := available.set! s true
  let mut checkedNodes : Array C := #[]
  for h : ni in [0 : nodes.size] do
    let node := nodes[ni]
    node.contextCheck
    for dest in node.destinationSlots do
      match available[dest]? with
      | none => throw (liftWiring (.nodeError ni (.slotOutOfRange dest n)))
      | some isAvail =>
          if isAvail then
            match producedBy[dest]?.join with
            | none => throw (liftWiring (.inputSlotOverwritten dest ni))
            | some firstNode => throw (liftWiring (.duplicateDestination dest firstNode ni))
    node.sourceCheck available
    let c ← node.localCheck
    checkedNodes := checkedNodes.push c
    for dest in node.destinationSlots do
      available := available.set! dest true
      producedBy := producedBy.set! dest (some ni)
  for h : i in [0 : n] do
    unless available[i]! do throw (liftWiring (.missingProduction i))
  return checkedNodes

/-- Validate one local block graph. Reuses `checkAssign` per assignment and the identical
    availability/production-order discipline `checkPlan` (`EvalPlan.lean`) already applies to the
    outer graph — both now delegate their wiring loop to the shared `checkStepGraph` above,
    parameterized by this block's own `tensorSigs`/`inputs` instead of `RawEvalPlan`'s
    `tensorSigs`/`inputSlots`, plus the one block-specific obligation `checkPlan` has no analogue
    for: every assignment's `contextShape` must equal the block's declared `contextShape`
    (`checkPlan` instead requires empty context, via `topLevelContextNotEmpty`). The
    `outputs`-range/uniqueness check has no analogue in `checkStepGraph` either — there is no
    "declared outputs" concept at the outer-graph level — so it stays a separate step here, run
    before the shared loop. -/
def checkPlanBlock (block : RawPlanBlock) : Except BlockError CheckedPlanBlock := do
  let n := block.tensorSigs.size
  for h : i in [0 : block.outputs.size] do
    let s := block.outputs[i]
    unless s < n do throw (.wiring (.slotOutOfRange s n))
  unless (block.outputs.toList).Nodup do
    throw (.duplicateOutputSlot
      ((firstDuplicateSlot block.outputs.toList).getD 0))
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
              unless precedingAssignments.contains p.sourceSlot do
                throw (.nonlinearSourceNotLocalAssignment ni p.sourceSlot)
          | .axiswise a => do
              match available[a.sourceSlot]? with
              | none => throw (.wiring (.nodeError ni (.slotOutOfRange a.sourceSlot n)))
              | some false => throw (.wiring (.invalidForwardRead ni 0 0 a.sourceSlot))
              | some true => pure ()
              unless precedingAssignments.contains a.sourceSlot do
                throw (.nonlinearSourceNotLocalAssignment ni a.sourceSlot)
      , localCheck := match step with
          | .assign a => match checkAssign block.tensorSigs a with
              | .error e => throw (.wiring (.nodeError ni e))
              | .ok c => pure (.assign c)
          | .pointwise p =>
              match checkPointwise block.tensorSigs p with
              | .error e => throw (.nonlin ni e)
              | .ok c => pure (.pointwise c)
          | .axiswise a =>
              match checkAxiswise block.tensorSigs a with
              | .error e => throw (.nonlin ni e)
              | .ok c => pure (.axiswise c) }
    match step with
    | .assign a => precedingAssignmentDestinations :=
        precedingAssignmentDestinations.push a.destinationSlot
    | .pointwise _ | .axiswise _ => pure ()
  let checkedNodes ← checkStepGraph n block.inputs BlockError.wiring nodes
  return CheckedPlanBlock.mk block checkedNodes

/-- Execute one checked block at a fixed enclosing-scan context coordinate. Positional store is
    local to this invocation — sized to the block's own `tensorSigs`, not the outer plan's. Reuses
    `runDenseAssignAt` per node exactly as `runDensePlan` does for the outer graph; this is the only
    place F2 evaluates a local assignment. -/
def runDenseBlock (c : CheckedPlanBlock) (ctx : List Int) (inputs : Array DenseTensor) :
    Except PositionalInputError (Array DenseTensor) := do
  let raw := c.raw
  unless inputs.size == raw.inputs.size do
    throw (.arityMismatch raw.inputs.size inputs.size)
  let n := raw.tensorSigs.size
  let placeholder : DenseTensor := { shape := [], data := #[] }
  let mut store : Array DenseTensor := Array.replicate n placeholder
  for h : i in [0 : raw.inputs.size] do
    let slot := raw.inputs[i]
    let t := inputs[i]!
    let sig := raw.tensorSigs.getD slot { shape := #[], dtype := .f64 }
    unless t.shape == sig.shape.toList do
      throw (.shapeMismatch slot sig.shape t.shape)
    unless t.data.size == sig.shape.toList.foldl (· * ·) 1 do
      throw (.storageMismatch slot t.shape t.data.size)
    store := store.set! slot t
  for node in c.checkedNodes do
    match node with
    | .assign a =>
        store := store.set! a.plan.destinationSlot (← runDenseAssignAt a ctx store)
    | .pointwise p =>
        store := store.set! p.raw.destinationSlot
          (runDensePointwise p (store.getD p.raw.sourceSlot placeholder))
    | .axiswise a =>
        store := store.set! a.raw.destinationSlot
          (runDenseAxiswise a (store.getD a.raw.sourceSlot placeholder))
  return store

end LeanNCD.Eval.Plan
