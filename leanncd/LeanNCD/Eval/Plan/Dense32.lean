import LeanNCD.Eval.Plan.EvalPlan

/-!
# Native binary32 graph execution (f32 slice, Task 3)

This module owns exactly ONE definition: the graph-level binary32 worker `runDensePlan32`. Its local
half — `runDenseAssignAt32`/`runDenseAssign32`, the scalar kernel seam, and the shared assignment
traversal — lives in `Dense.lean` beside its binary64 siblings, so the two carriers cannot drift in
fold order, zero-pad behavior, or predicate handling, and so no second unchecked public execution
door exists.

It sits HERE, downstream of `EvalPlan.lean`, for the same import-order reason `runDensePlan` does:
`CheckedEvalPlan` is defined there. `Adapter32.lean` (Task 4) imports this module, which is what
makes it reachable from the top-level `LeanNCD` import without a cycle.
-/

namespace LeanNCD.Eval.Plan

/-- Execute a checked BINARY32 graph over positional native `Float32` inputs. The binary32 sibling of
    `runDensePlan`, retaining its graph step order, input-slot placement, destination replacement,
    shape/storage checks, and exact store arity verbatim — only the carrier and the per-step worker
    differ.

    **The storage-kind guard is first, before the arity check and before any input is read**, the
    mirror of `runDensePlan`'s own. A binary64 checked graph executed here would silently answer a
    binary64 question in binary32; a guard placed after the arity check would instead report
    `arityMismatch` for a plan whose buffers this worker must never touch.

    **Every step kind runs natively, since F32-C.** `.assign` runs `runDenseAssign32`, `.pointwise`/
    `.axiswise` run `runDensePointwise32`/`runDenseAxiswise32` (F32-B), `.scatter` runs
    `runDenseScatter32` (F32-D), and `.scan` runs `runDenseScan32` (F32-C), each of which re-checks
    its own evidence's storage kind as its first statement. Matched arm by arm rather than through a
    catch-all, so a future admission remains a deliberate edit at its own arm.

    Signature dtypes are not re-examined here, exactly as `runDensePlan` does not re-examine its own:
    `checkPlan` already committed the WHOLE table to `.float32` (through `deriveStorageKind`, or —
    for a bool-only table — through its scan blocks' first real slot), which admits `f32` and
    `bool` signatures and nothing else, and that commitment is what `c.storageKind` records. Only
    the shape and the native buffer length are runtime facts, and both are checked. -/
def runDensePlan32 (c : CheckedEvalPlan) (inputs : Array DenseTensor32) :
    Except PositionalInputError (Array DenseTensor32) := do
  unless c.storageKind == .float32 do
    throw (.storageKindMismatch .float32 c.storageKind)
  let raw := c.raw
  unless inputs.size == raw.inputSlots.size do
    throw (.arityMismatch raw.inputSlots.size inputs.size)
  let n := raw.tensorSigs.size
  let placeholder : DenseTensor32 := { shape := [], data := #[] }
  let mut store : Array DenseTensor32 := Array.replicate n placeholder
  for h : i in [0 : raw.inputSlots.size] do
    let slot := raw.inputSlots[i]
    let t := inputs[i]!
    let sig := raw.tensorSigs.getD slot { shape := #[], dtype := .f32 }
    unless t.shape == sig.shape.toList do throw (.shapeMismatch slot sig.shape t.shape)
    unless t.data.size == sig.shape.toList.foldl (· * ·) 1 do
      throw (.storageMismatch slot t.shape t.data.size)
    store := store.set! slot t
  for node in c.checkedNodes do
    match node with
    | .assign a => store := store.set! a.plan.destinationSlot (← runDenseAssign32 a store)
    | .scatter s =>
        store := store.set! s.plan.compute.destinationSlot (← runDenseScatter32 s store)
    | .scan c => store ← runDenseScan32 raw.tensorSigs c store
    | .pointwise p =>
        store := store.set! p.raw.destinationSlot (← runDensePointwise32 p store)
    | .axiswise a =>
        store := store.set! a.raw.destinationSlot (← runDenseAxiswise32 a store)
  return store

end LeanNCD.Eval.Plan
