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

    **Assignment-only, and every other evidence kind is refused as binary64 evidence.** That is not a
    placeholder: `checkPlan` rejects a `.scatter`/`.scan`/`.pointwise`/`.axiswise` step in a
    `.float32` graph outright (`PlanStepError.f32UnsupportedStep`), so those arms are unreachable for
    any `CheckedEvalPlan` whose `storageKind` is `.float32` — and, independently, every one of those
    four checkers (`checkScatter`, `checkScanPlan`, `checkPointwise`, `checkAxiswise`) is Float-backed
    by design, so such evidence genuinely IS binary64 evidence. `storageKindMismatch .float32
    .float64` therefore states the literal truth about what arrived rather than inventing a new
    diagnostic for a state the checker already prevents. Matched arm by arm rather than through a
    catch-all so admitting one of these kinds in a later slice (F32-B/C/D) is a deliberate edit at
    its own arm.

    Signature dtypes are not re-examined here, exactly as `runDensePlan` does not re-examine its own:
    `checkPlan`'s `deriveStorageKind` already committed the WHOLE table to `.float32`, which admits
    `f32` and `bool` signatures and nothing else, and that commitment is what `c.storageKind`
    records. Only the shape and the native buffer length are runtime facts, and both are checked. -/
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
    | .scatter _ => throw (.storageKindMismatch .float32 .float64)
    | .scan _ => throw (.storageKindMismatch .float32 .float64)
    | .pointwise _ => throw (.storageKindMismatch .float32 .float64)
    | .axiswise _ => throw (.storageKindMismatch .float32 .float64)
  return store

end LeanNCD.Eval.Plan
