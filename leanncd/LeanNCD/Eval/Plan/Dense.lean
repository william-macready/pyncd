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

/-- Fold one term's factor product, left to right in stored factor order (architecture doc §2.2:
    `factorFold([]) = float64(1)`, `factorFold(xs ++ [x]) = float64(factorFold(xs) * x)`). Named
    separately from `reductionFold`/`termFold` even though all three are left folds over `applyOp`
    because §2.2 gives each its own operation/identity — factors use `factorOp`/`factorId`, never
    `reduceOp`/`reduceId`. -/
private def factorFold (alg : ContractionAlgebra) (xs : List Float) : Float :=
  xs.foldl (applyOp alg.factorOp) (constFloat alg.factorId)

example (alg : ContractionAlgebra) : factorFold alg [] = constFloat alg.factorId := rfl

example (alg : ContractionAlgebra) (xs : List Float) (x : Float) :
    factorFold alg (xs ++ [x]) = applyOp alg.factorOp (factorFold alg xs) x := by
  simp [factorFold, List.foldl_append]

/-- Fold one term's reduction coordinates, left to right in row-major order (architecture doc §2.2:
    `reductionFold([]) = float64(0)`, `reductionFold(xs ++ [x]) = float64(reductionFold(xs) + x)`).
    Each `x` here is that reduction coordinate's factor product (`factorFold`'s result), not a raw
    factor value. -/
private def reductionFold (alg : ContractionAlgebra) (xs : List Float) : Float :=
  xs.foldl (applyOp alg.reduceOp) (constFloat alg.reduceId)

example (alg : ContractionAlgebra) : reductionFold alg [] = constFloat alg.reduceId := rfl

example (alg : ContractionAlgebra) (xs : List Float) (x : Float) :
    reductionFold alg (xs ++ [x]) = applyOp alg.reduceOp (reductionFold alg xs) x := by
  simp [reductionFold, List.foldl_append]

/-- Fold completed terms into one output coordinate's value, left to right in term-array order
    (architecture doc §2.2: `termFold([]) = float64(0)`, `termFold(xs ++ [x]) =
    float64(termFold(xs) + x)`). Defined with the same `reduceOp`/`reduceId` as `reductionFold` —
    not a coincidence: `ContractionAlgebra`'s own doc comment (`Types.lean`) states that term
    combination and reduction intentionally share one op/identity pair, mirroring the reference
    evaluator's `Combine.combine`/`unit0`. Kept as its own named function (rather than reusing
    `reductionFold` under a second name) so each of §2.2's three fold equations has exactly one
    Lean definition to pin it to. -/
private def termFold (alg : ContractionAlgebra) (xs : List Float) : Float :=
  xs.foldl (applyOp alg.reduceOp) (constFloat alg.reduceId)

example (alg : ContractionAlgebra) : termFold alg [] = constFloat alg.reduceId := rfl

example (alg : ContractionAlgebra) (xs : List Float) (x : Float) :
    termFold alg (xs ++ [x]) = applyOp alg.reduceOp (termFold alg xs) x := by
  simp [termFold, List.foldl_append]

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

/-- Validate a runtime context coordinate against the checked context shape: same rank, and every
    component in range. A separate check from `checkAssign`'s structural work — `ctx` is a runtime
    value supplied per call, not plan data (proposal §7.1). -/
private def validateContext (a : AssignPlan) (ctx : List Int) : Except PositionalInputError Unit :=
  let inRange := (ctx.zip a.contextShape.toList).all (fun (v, d) => 0 ≤ v && v < (d : Int))
  if ctx.length == a.contextShape.size && inRange then pure ()
  else throw (.contextShapeMismatch a.contextShape ctx)

/-- Execute one checked operation at a fixed context coordinate. Fold order is source-declared and
    preserved exactly: factors via `factorFold`, then that term's reduction coordinates via
    `reductionFold`, then completed terms via `termFold`, in term-array order — matching architecture
    doc §2.2's three fold equations one-for-one. The inner reduction fold and the outer term fold
    are NOT flattened — `Y[i] := A[i] + P[i,j]` must add `A[i]` once, not once per `j` (proposal
    §8.2). `ctx` is bound once per call, at every term's `contextPos` positions, and held fixed
    across the whole output/reduction double-loop — it does not get enumerated like
    `outputPos`/`reductionPos` do. -/
def runDenseAssignAt (c : CheckedAssignPlan) (ctx : List Int) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  validateContext c.plan ctx
  validateStore c store
  let a := c.plan
  let alg := a.algebra
  let out : List Float := (allCoords a.outputShape.toList).map (fun oc =>
    let termAccs : List Float := a.terms.toList.map (fun t =>
      let redShape := t.reductionPos.toList.filterMap (fun p => t.iterationShape[p]?)
      let prods : List Float := (allCoords redShape).map (fun rc =>
        let iter : Array Int := Id.run do
          let mut iter : Array Int := Array.replicate t.iterationShape.size 0
          for (p, v) in t.contextPos.toList.zip ctx do iter := iter.set! p v
          for (p, v) in t.outputPos.toList.zip oc do iter := iter.set! p v
          for (p, v) in t.reductionPos.toList.zip rc do iter := iter.set! p v
          return iter
        let factorVals : List Float := t.factors.toList.map (fun f => gatherFactor store f iter.toList)
        factorFold alg factorVals)
      reductionFold alg prods)
    termFold alg termAccs)
  return { shape := a.outputShape.toList, data := out.toArray }

/-- The empty-context wrapper every existing (scan-free) call site uses. -/
def runDenseAssign (c : CheckedAssignPlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor :=
  runDenseAssignAt c [] store

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
