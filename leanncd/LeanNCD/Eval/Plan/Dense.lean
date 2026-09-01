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

/-- The Dense positional predicate evaluator's only failure: an Iverson leaf whose coefficient width
    disagrees with the iteration coordinate it is evaluated against. The checker (`checkAssign`)
    forbids this at plan-check time, so it is unreachable for any checked plan; kept so the evaluator
    is total and fails loud. Distinct from `PositionalInputError` (this is the predicate arithmetic's
    own error, mapped into `PositionalInputError.predicateWidthMismatch` at the one Dense call site
    that runs it). -/
inductive PosPredicateError
  | affineWidthMismatch (expected : Nat) (actual : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Evaluate one positional affine leaf `coeffs · iter + bias` at an iteration coordinate. Rejects a
    width mismatch rather than silently truncating the shorter of the two — a UID-free leaf must span
    exactly the positional basis. -/
def evalPosAffine (a : PosAffine) (iter : List Int) : Except PosPredicateError Int :=
  if a.coeffs.size == iter.length then
    .ok ((a.coeffs.toList.zip iter).foldl (fun acc (c, v) => acc + c * v) a.bias)
  else
    .error (.affineWidthMismatch a.coeffs.size iter.length)

/-- Evaluate positional predicate arithmetic at an iteration coordinate → `Int`. Mirrors the source
    `evalPred` (`Eval/Gather.lean`) exactly — `mul` multiplies, `iabs` takes `Int.natAbs` cast back
    to `Int` — but over the UID-free positional leaf instead of a `HashMap UID Int` coordinate. -/
def evalPosPredArith (iter : List Int) : PosPredArith → Except PosPredicateError Int
  | .affine a => evalPosAffine a iter
  | .mul a b => do return (← evalPosPredArith iter a) * (← evalPosPredArith iter b)
  | .iabs a => do return ((← evalPosPredArith iter a).natAbs : Int)

/-- Evaluate a positional Boolean predicate at an iteration coordinate → `Bool`. Mirrors the source
    `evalBool` (`Eval/Gather.lean`): `.ieq` is the same structural-`Int`-equality approximation of the
    DSL's modular equality. Imports neither `Eval.Gather` nor the source `evalPred`/`evalBool`. -/
def evalPosBool (iter : List Int) : PosBoolExpr → Except PosPredicateError Bool
  | .rel op a b => do
      let x ← evalPosPredArith iter a
      let y ← evalPosPredArith iter b
      return (match op with
        | .lt => decide (x < y)
        | .le => decide (x ≤ y)
        | .eq => decide (x = y)
        | .ne => decide (x ≠ y)
        | .ge => decide (x ≥ y)
        | .gt => decide (x > y))
  | .and a b => do return (← evalPosBool iter a) && (← evalPosBool iter b)
  | .or a b => do return (← evalPosBool iter a) || (← evalPosBool iter b)
  | .not a => do return !(← evalPosBool iter a)
  | .ieq a b => do return (← evalPosPredArith iter a) == (← evalPosPredArith iter b)

/-- Gather one factor. Every source dimension is range-tested BEFORE flattening (`inBoundsPerDim`,
    `Coordinates.lean`): testing the flat offset instead can alias distinct invalid coordinates onto
    a valid address (proposal §8.3). A `unary` function is applied to the gathered value AFTER the
    out-of-bounds zero-pad (so an out-of-bounds read contributes `f(0)`, matching the reference
    `gather`), and can fail loud on a domain violation (`log`/`sqrt`/`recip`) via the shared
    `UnaryOp.applyChecked` — the same oracle the reference `applyUnaryFn` wraps. -/
private def gatherFactor (store : Array DenseTensor) (f : ReadPlan) (iter : List Int) :
    Except PositionalInputError Float :=
  let base : Float :=
    match store[f.sourceSlot]? with
    | none => 0.0
    | some t =>
        let src := applyAffine f.map iter
        let shape := f.sourceShape.toList
        if inBoundsPerDim shape src then (t.data[flatIndex shape (src.map Int.toNat)]?).getD 0.0
        else 0.0
  match f.unary with
  | none => .ok base
  | some op => (op.applyChecked base).mapError (fun dop => .unaryDomain dop (Float.toBits base) f.sourceSlot)

private def applyOp : ScalarBinOp → Float → Float → Float
  | .add => (· + ·)
  | .mul => (· * ·)
  | .min => fun a b => Min.min a b
  | .max => fun a b => Max.max a b

/-- Decode a checked plan's scalar constant to its `Float` value. The catch-all `_ => 0.0` arm is
    dead code in practice, not a real default: `checkAssign`'s `algebraNotAdmitted` guard
    (`Check.lean`) forces `a.algebra ∈ admittedAlgebras`, and every `factorId`/`reduceId` of those
    three algebras (real sum-product plus the two tropical semirings) is `.f64 _` — the only
    `ScalarConst` values a `CheckedAssignPlan` can ever carry here. Kept as a total match (rather than
    an exhaustive `.f64`-only one) so this function does not need to change shape if `ScalarConst`
    grows a new constructor; see `ScalarConst`'s own doc comment (`Types.lean`) for why `.f32`/`.bool`
    can never actually reach here. -/
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
      match f with
      | .iverson _ => pure ()  -- a predicate factor reads no store slot
      | .read f =>
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
  let out ← (allCoords a.outputShape.toList).mapM (fun oc => do
    let termAccs ← a.terms.toList.mapM (fun t => do
      let redShape := t.reductionPos.toList.filterMap (fun p => t.iterationShape[p]?)
      let prods ← (allCoords redShape).mapM (fun rc => do
        let iter : Array Int := Id.run do
          let mut iter : Array Int := Array.replicate t.iterationShape.size 0
          for (p, v) in t.contextPos.toList.zip ctx do iter := iter.set! p v
          for (p, v) in t.outputPos.toList.zip oc do iter := iter.set! p v
          for (p, v) in t.reductionPos.toList.zip rc do iter := iter.set! p v
          return iter
        let factorVals ← t.factors.toList.mapM (fun f => match f with
          | .read r => gatherFactor store r iter.toList
          | .iverson b =>
              (evalPosBool iter.toList b
                |>.mapError (fun e => match e with
                  | .affineWidthMismatch exp act => PositionalInputError.predicateWidthMismatch exp act)).map
                (fun v => if v then 1.0 else 0.0))
        return factorFold alg factorVals)
      return reductionFold alg prods)
    return termFold alg termAccs)
  return { shape := a.outputShape.toList, data := out.toArray }


/-- The empty-context wrapper every existing (scan-free) call site uses. -/
def runDenseAssign (c : CheckedAssignPlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor :=
  runDenseAssignAt c [] store

-- `runDensePlan` used to live here (C3), but now that a checked outer graph can contain a `.scan`
-- node (whose worker is `runDenseScan`, `Scan.lean`), it relocated to `EvalPlan.lean` — the only
-- module that can see both this file's `runDenseAssign` and `Scan.lean`'s `runDenseScan` without a
-- circular import. See `EvalPlan.lean`.

end LeanNCD.Eval.Plan
