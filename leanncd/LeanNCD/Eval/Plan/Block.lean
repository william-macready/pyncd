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

/-- A local, acyclic, context-parameterized dataflow graph — the base block or the step block of a
    future scan (`papers/wave_f_scanplan_proposal.md` §6.2). Local assignments are plain
    `AssignPlan`s sharing this block's `contextShape` — the same node type the outer graph uses, so
    F2 introduces no second local-operation representation. -/
structure RawPlanBlock where
  contextShape : Array Nat
  tensorSigs   : Array TensorSignature
  inputs       : Array TensorSlot
  assignments  : Array AssignPlan
  outputs      : Array TensorSlot
  deriving DecidableEq, BEq, Repr, Inhabited

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
  checkedNodes : Array CheckedAssignPlan
  deriving Repr

/-- Validate one local block graph. Reuses `checkAssign` per assignment and the identical
    availability/production-order discipline `checkPlan` (`Check.lean`) already applies to the
    outer graph — the same loop shape, parameterized by this block's own `tensorSigs`/`inputs`
    instead of `RawEvalPlan`'s `tensorSigs`/`inputSlots`, plus the one block-specific obligation
    `checkPlan` has no analogue for: every assignment's `contextShape` must equal the block's
    declared `contextShape` (`checkPlan` instead requires empty context, via
    `topLevelContextNotEmpty`). -/
def checkPlanBlock (block : RawPlanBlock) : Except BlockError CheckedPlanBlock := do
  let n := block.tensorSigs.size
  for h : i in [0 : block.inputs.size] do
    let s := block.inputs[i]
    unless s < n do throw (.wiring (.slotOutOfRange s n))
    if h2 : i + 1 < block.inputs.size then
      let s2 := block.inputs[i + 1]
      if s == s2 then throw (.wiring (.duplicateInputSlot s))
      else if s2 < s then throw (.wiring (.inputSlotsNotOrdered i))
  for h : i in [0 : block.outputs.size] do
    let s := block.outputs[i]
    unless s < n do throw (.wiring (.slotOutOfRange s n))
  unless (block.outputs.toList).Nodup do
    throw (.duplicateOutputSlot
      ((firstDuplicateSlot block.outputs.toList).getD 0))
  let mut available : Array Bool := Array.replicate n false
  let mut producedBy : Array (Option Nat) := Array.replicate n none
  for s in block.inputs do
    available := available.set! s true
  let mut checkedNodes : Array CheckedAssignPlan := #[]
  for h : ni in [0 : block.assignments.size] do
    let step := block.assignments[ni]
    unless step.contextShape == block.contextShape do
      throw (.blockContextMismatch ni block.contextShape step.contextShape)
    let destSlot := step.destinationSlot
    match available[destSlot]? with
    | none => throw (.wiring (.nodeError ni (.slotOutOfRange destSlot n)))
    | some isAvail =>
        if isAvail then
          match producedBy[destSlot]?.join with
          | none => throw (.wiring (.inputSlotOverwritten destSlot ni))
          | some firstNode => throw (.wiring (.duplicateDestination destSlot firstNode ni))
    for h2 : ti in [0 : step.terms.size] do
      let t := step.terms[ti]
      for h3 : fi in [0 : t.factors.size] do
        let f := t.factors[fi]
        match available[f.sourceSlot]? with
        | none => throw (.wiring (.nodeError ni (.slotOutOfRange f.sourceSlot n)))
        | some true => pure ()
        | some false => throw (.wiring (.invalidForwardRead ni ti fi f.sourceSlot))
    match checkAssign block.tensorSigs step with
    | .error e => throw (.wiring (.nodeError ni e))
    | .ok c =>
        checkedNodes := checkedNodes.push c
        available := available.set! destSlot true
        producedBy := producedBy.set! destSlot (some ni)
  for h : i in [0 : n] do
    unless available[i]! do throw (.wiring (.missingProduction i))
  return CheckedPlanBlock.mk block checkedNodes

end LeanNCD.Eval.Plan
