import LeanNCD.Eval.Tensor
import LeanNCD.Eval.Plan.Check
import LeanNCD.Eval.Plan.Coordinates

/-!
# Wave C Dense interpretation of one checked operation (C2)

The pullback-product-pushforward semantics of proposal §8, over positional `DenseTensor` storage.
Independent of the legacy evaluator by construction — this module imports neither `Gather` nor
`Contract`, builds no `HashMap UID Int`, and knows no source names — so the two implementations can
serve as each other's oracle in C4's differential matrix. Row-major coordinate enumeration, affine
application, flattening, and the per-dimension bounds predicate live in `Coordinates.lean`.
-/

namespace LeanNCD.Eval.Plan
open LeanNCD.Eval

/-- Gather one factor. Every source dimension is range-tested BEFORE flattening (`inBoundsPerDim`,
    `Coordinates.lean`): testing the flat offset instead can alias distinct invalid coordinates onto
    a valid address (proposal §8.3). -/
private def gatherFactor (store : Array DenseTensor) (f : ReadPlan) (iter : List Int) : Float :=
  match store[f.sourceSlot]? with
  | none => 0.0
  | some t =>
      let src := applyAffine f.map iter
      let shape := f.sourceShape.toList
      if inBoundsPerDim shape src then (t.data[flatIndex shape (src.map Int.toNat)]?).getD 0.0
      else 0.0

private def applyOp : ScalarBinOp → Float → Float → Float
  | .add => (· + ·)
  | .mul => (· * ·)

/-- Decode a checked plan's scalar constant to its `Float` value. The catch-all `_ => 0.0` arm is
    dead code in practice, not a real default: `checkAssign`'s `algebraNotAdmitted` guard
    (`Check.lean`) forces `a.algebra == admittedAlgebra` exactly, and `admittedAlgebra`'s
    `factorId`/`reduceId` are both `.f64 _` — the only `ScalarConst` values a `CheckedAssignPlan`
    can ever carry here. Kept as a total match (rather than an exhaustive `.f64`-only one) so this
    function does not need to change shape if `ScalarConst` grows a new constructor; see
    `ScalarConst`'s own doc comment (`Types.lean`) for why `.f32`/`.bool` can never actually reach
    here. -/
private def constFloat : ScalarConst → Float
  | .f64 bits => Float.ofBits bits
  | _ => 0.0

/-- Validate the positional store against the shapes `checkAssign` already validated. Runtime
    values are a separate trust boundary from plan structure, so this is a value check, not a
    re-validation of the plan. -/
private def validateStore (c : CheckedAssignPlan) (store : Array DenseTensor) :
    Except PositionalInputError Unit := do
  for t in c.plan.terms do
    for f in t.factors do
      match store[f.sourceSlot]? with
      | none => throw (.missingSlot f.sourceSlot store.size)
      | some d =>
          unless d.shape == f.sourceShape.toList do
            throw (.shapeMismatch f.sourceSlot f.sourceShape d.shape)
          unless d.data.size == f.sourceShape.toList.foldl (· * ·) 1 do
            throw (.storageMismatch f.sourceSlot d.shape d.data.size)

/-- Execute one checked operation. Fold order is source-declared and preserved exactly: factors
    from `factorId`, then that term's reduction coordinates from `reduceId`, then completed terms
    from `reduceId` in term-array order. The inner reduction fold and the outer term fold are NOT
    flattened — `Y[i] := A[i] + P[i,j]` must add `A[i]` once, not once per `j` (proposal §8.2). -/
def runDenseAssign (c : CheckedAssignPlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  validateStore c store
  let a := c.plan
  let alg := a.algebra
  let factorId := constFloat alg.factorId
  let reduceId := constFloat alg.reduceId
  let mut out : Array Float := #[]
  for oc in allCoords a.outputShape.toList do
    let mut acc := reduceId
    for t in a.terms do
      let redShape := t.reductionPos.toList.filterMap (fun p => t.iterationShape[p]?)
      let mut termAcc := reduceId
      for rc in allCoords redShape do
        let mut iter : Array Int := Array.replicate t.iterationShape.size 0
        for (p, v) in t.outputPos.toList.zip oc do iter := iter.set! p v
        for (p, v) in t.reductionPos.toList.zip rc do iter := iter.set! p v
        let mut prod := factorId
        for f in t.factors do
          prod := applyOp alg.factorOp prod (gatherFactor store f iter.toList)
        termAcc := applyOp alg.reduceOp termAcc prod
      acc := applyOp alg.reduceOp acc termAcc
    out := out.push acc
  return { shape := a.outputShape.toList, data := out }

/-- Execute a checked graph over positional Dense inputs, ordered by `c.raw.inputSlots`. Checks
    input arity, validates each input tensor's shape and storage against its declared signature,
    places inputs into their declared slots, then runs each checked node in order via
    `runDenseAssign`, inserting its result at that node's destination slot. Every non-input slot is
    populated by construction — `checkPlan` already established that every non-input slot has
    exactly one producer and that every read only touches an already-available slot at the point it
    is read — so the placeholder value used to pre-fill not-yet-produced slots is never actually
    read; this is the total "unwrap" that guarantee supports, not a silent default. Arity mismatch
    is reported via the dedicated `PositionalInputError.arityMismatch` constructor. Per-input shape
    and storage mismatches use the same `shapeMismatch`/`storageMismatch` constructors
    `runDenseAssign`'s `validateStore` uses for read factors — an input slot no node reads (e.g. an
    unused graph input) still gets its declared signature enforced here, not skipped. -/
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
    -- `slot < raw.tensorSigs.size` was already range-checked by `checkPlan`; the default here is
    -- never actually used, `getD` just avoids requiring an `Inhabited TensorSignature` instance.
    let sig := raw.tensorSigs.getD slot { shape := #[], dtype := .f64 }
    unless t.shape == sig.shape.toList do
      throw (.shapeMismatch slot sig.shape t.shape)
    unless t.data.size == sig.shape.toList.foldl (· * ·) 1 do
      throw (.storageMismatch slot t.shape t.data.size)
    store := store.set! slot t
  for node in c.checkedNodes do
    let result ← runDenseAssign node store
    store := store.set! node.plan.destinationSlot result
  return store

end LeanNCD.Eval.Plan
