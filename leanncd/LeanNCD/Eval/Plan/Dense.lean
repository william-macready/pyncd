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

/-- Decode a checked plan's scalar constant to its `Float` value. `.bool` is a semantic tag over the
    same Float storage, so `true`/`false` decode to the reference evaluator's Boolean identities
    `1.0`/`0.0` (`Combine.bool`'s `unit0`/`unit1`) — no separate Boolean carrier, no coercion of
    gathered values. The catch-all `_ => 0.0` arm now covers `.f32` only, and is dead code in
    practice rather than a real default: `checkAssign`'s `algebraNotAdmitted` guard (`Check.lean`)
    forces `a.algebra ∈ admittedAlgebrasFor destDtype`, whose `.f32` row is empty and whose other
    rows carry only `.f64`/`.bool` constants — the only `ScalarConst` values a `CheckedAssignPlan`
    can ever carry here. Kept as a total match so this function does not need to change shape if
    `ScalarConst` grows a new constructor. -/
private def constFloat : ScalarConst → Float
  | .f64 bits => Float.ofBits bits
  | .bool true => 1.0
  | .bool false => 0.0
  | _ => 0.0

/-- Fold one term's factors left to right in stored order. For the original real specialization this
    is architecture doc §2.2's `factorFold([]) = float64(1)` and multiplication step; generally the
    checked destination algebra supplies that identity and operation. Named separately from
    `reductionFold`/`termFold` because factors use `factorOp`/`factorId`, never
    `reduceOp`/`reduceId`. -/
private def factorFold (alg : ContractionAlgebra) (xs : List Float) : Float :=
  xs.foldl (applyOp alg.factorOp) (constFloat alg.factorId)

example (alg : ContractionAlgebra) : factorFold alg [] = constFloat alg.factorId := rfl

example (alg : ContractionAlgebra) (xs : List Float) (x : Float) :
    factorFold alg (xs ++ [x]) = applyOp alg.factorOp (factorFold alg xs) x := by
  simp [factorFold, List.foldl_append]

/-- Fold one term's reduction coordinates left to right in row-major order. For the original real
    specialization this is architecture doc §2.2's zero-initialized addition; generally the checked
    destination algebra supplies the identity and operation. Each value is that reduction
    coordinate's factor product (`factorFold`'s result), not a raw factor value. -/
private def reductionFold (alg : ContractionAlgebra) (xs : List Float) : Float :=
  xs.foldl (applyOp alg.reduceOp) (constFloat alg.reduceId)

example (alg : ContractionAlgebra) : reductionFold alg [] = constFloat alg.reduceId := rfl

example (alg : ContractionAlgebra) (xs : List Float) (x : Float) :
    reductionFold alg (xs ++ [x]) = applyOp alg.reduceOp (reductionFold alg xs) x := by
  simp [reductionFold, List.foldl_append]

/-- Fold completed terms into one output coordinate's value, left to right in term-array order.
    Defined with the same `reduceOp`/`reduceId` as `reductionFold` — not a coincidence:
    `ContractionAlgebra`'s own doc comment (`Types.lean`) states that term combination and reduction
    intentionally share one op/identity pair, mirroring the reference evaluator's
    `Combine.combine`/`unit0`. Kept as its own named function rather than reusing `reductionFold`
    under a second name so each semantic fold remains explicit. -/
private def termFold (alg : ContractionAlgebra) (xs : List Float) : Float :=
  xs.foldl (applyOp alg.reduceOp) (constFloat alg.reduceId)

example (alg : ContractionAlgebra) : termFold alg [] = constFloat alg.reduceId := rfl

example (alg : ContractionAlgebra) (xs : List Float) (x : Float) :
    termFold alg (xs ++ [x]) = applyOp alg.reduceOp (termFold alg xs) x := by
  simp [termFold, List.foldl_append]

/-- Validate the positional store against the shapes `checkAssign` already validated. Runtime
    values are a separate trust boundary from plan structure, so this is a value check, not a
    re-validation of the plan.

    Takes a raw `AssignPlan`, matching `validateContext` beside it: both read plan FIELDS only and
    neither consults the checked wrapper, so the `Checked` guarantee belongs at the public API
    boundary, not on a private helper. `runDenseScatter` validates a scatter's compute half — a raw
    `AssignPlan` reached through `CheckedScatterPlan`, which deliberately stores no
    `CheckedAssignPlan` for it — through this same function rather than a second copy. -/
private def validateStore (a : AssignPlan) (store : Array DenseTensor) :
    Except PositionalInputError Unit := do
  for t in a.terms do
    for (_, f) in t.readFactorsIndexed do
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

/-- ONE output coordinate's value under a raw `AssignPlan`, at a fixed context coordinate. Fold order
    is source-declared and preserved exactly: factors via `factorFold`, then that term's reduction
    coordinates via `reductionFold`, then completed terms via `termFold`, in term-array order —
    matching architecture doc §2.2's three fold equations one-for-one. The inner reduction fold and
    the outer term fold are NOT flattened — `Y[i] := A[i] + P[i,j]` must add `A[i]` once, not once per
    `j` (proposal §8.2). `ctx` is bound at every term's `contextPos` positions and held fixed here —
    it does not get enumerated like `outputPos`/`reductionPos` do.

    Takes a raw `AssignPlan` and not a `CheckedAssignPlan` for the reason `validateStore` above does:
    the body reads plan fields only, so the checked wrapper's guarantee lives at the public API
    boundary rather than on this helper, and both callers are already past that boundary.
    `runDenseAssignAt` enumerates `outputShape` and maps this over it (the output-driven case);
    `runDenseScatter` enumerates the same array as its SOURCE domain and places each value through a
    separate map, reaching the compute half through `CheckedScatterPlan`, which deliberately stores no
    `CheckedAssignPlan` for it. Shared rather than duplicated so the two workers cannot drift in fold
    order, zero-pad behavior, or predicate handling. -/
private def denseValueAt (a : AssignPlan) (ctx : List Int) (store : Array DenseTensor)
    (oc : List Int) : Except PositionalInputError Float := do
  let alg := a.algebra
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
  return termFold alg termAccs

/-- Execute one checked operation at a fixed context coordinate: `denseValueAt` at every output
    coordinate, in row-major order, into a tensor of the plan's own `outputShape`. -/
def runDenseAssignAt (c : CheckedAssignPlan) (ctx : List Int) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  validateContext c.plan ctx
  validateStore c.plan store
  let a := c.plan
  let out ← (allCoords a.outputShape.toList).mapM (denseValueAt a ctx store)
  return { shape := a.outputShape.toList, data := out.toArray }


/-- The empty-context wrapper every existing (scan-free) call site uses. -/
def runDenseAssign (c : CheckedAssignPlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor :=
  runDenseAssignAt c [] store

/-! ## The dense scatter worker (S-A Task 4)

`runDenseScatter` is free-standing: `checkPlan` still rejects every scatter step with
`.scatterNotChecked` (`EvalPlan.lean`) and `runDensePlan` has no `.scatter` arm, because
`CheckedPlanStepEvidence` has no `.scatter` constructor yet. Wiring is a later task; this is the
worker it will call, exactly as `checkScatter` (`Check.lean`) is the checker it will call.
-/

/-- Execute one checked scatter over a positional store. SOURCE-driven, which is the whole structural
    difference from `runDenseAssignAt`: that worker enumerates its DESTINATION and pulls one value per
    destination cell, while this one enumerates `compute.outputShape` — the source iteration domain —
    evaluates the compute half there through the shared `denseValueAt`, and PUSHES the value to
    `outCoeffs · sourceCoordinate + outBias`. Unwritten destination cells keep `fill`.

    Reproduces `Eval/Scatter.lean`'s `evalScatter` equation for equation **for the real sum-product
    algebra**, because differential parity against that evaluator is this feature's correctness gate
    (plan §2.1) — including the two places where matching it means NOT improving it:

    * **An out-of-range destination coordinate is skipped silently.** The reference tests its placed
      coordinate against the output shape and simply does not write when it fails, with no
      diagnostic. `checkScatter`'s docstring names this as the one case-audit cell it leaves to this
      worker, and rejecting it here — statically or at runtime — would refuse programs the reference
      accepts. The test is `inBoundsPerDim` (`Coordinates.lean`), the same per-dimension predicate
      `gatherFactor` uses on the read side, and it runs BEFORE `flatIndex`: a flat-offset test can
      alias distinct invalid coordinates onto a valid address (proposal §8.3). So `Int.toNat` on the
      destination coordinate is never lossy here — every component is already known non-negative.
    * **The `.toNat` extent degeneracies reach this worker as an empty destination, not as an
      error.** A zero or negative placement coefficient makes `LHSSlot.outExtent` clamp that
      dimension's extent to `0` (`ScatterCheckTest` pins both), and `checkScatter` admits the plan
      because `destShape` does equal `outExtent`'s answer. Here that means `inBoundsPerDim` is false
      at every source coordinate, so every write is skipped by the rule above and the result is the
      empty tensor the reference produces. Nothing special-cases it.

    **A TROPICAL-algebra scatter's unwritten cells diverge from the reference BY DESIGN, and that
    divergence is permanent.** The scoping of the parity claim above is load-bearing, not hedging:
    the reference's `ScatterOpts.fill` is an `Int` (`DSL/Ast.lean`) which `evalScatter` widens with
    `Float.ofInt`, so the reference layer cannot express `±∞` at all and fills every unwritten cell
    with an integer-valued Float — `0.0` in practice, its default. `checkScatter` meanwhile forces
    `fill == compute.algebra.reduceId`, which for `admittedAlgebraMax`/`Min` IS `∓∞`, and the checked
    plan's `fill : ScalarConst` can carry it. So on a max/min scatter the two implementations
    provably disagree on every unwritten cell, and this worker is the correct one: filling with `0.0`
    under max-product would let a spurious zero win the reduction over an all-negative cell, the
    exact incoherence `PlanError.scatterFillNotIdentity` exists to reject. `ScatterDenseTest`'s
    tropical-`fill` fixture pins the checked-layer value and records the divergence; a differential
    corpus must therefore not treat a tropical scatter as a parity-checked entry without special
    casing the unwritten cells.

    `writtenBy` maps a destination flat index to the FIRST source coordinate that wrote there, and
    exists only to name both halves of a conflict in `scatterCollision` — the reference's own reason
    for carrying it. `.rejectCollisions` is the only policy `checkScatter` admits, so the four arms
    beside it are unreachable for any `CheckedScatterPlan`; they are written to the reference's own
    equations (not to each other) so that admitting one later is a checker change alone. -/
def runDenseScatter (c : CheckedScatterPlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  let s := c.plan
  let a := s.compute
  -- A scatter is admitted only as a top-level step, so its compute half runs at the empty context —
  -- the same coordinate `runDenseAssign` supplies. Validated rather than assumed: `checkScatter`
  -- deliberately does not check `compute.contextShape` (`checkPlan`'s `contextCheck` owns that), so
  -- a non-empty one must fail loud here instead of silently binding no context position.
  validateContext a []
  validateStore a store
  let destShape := s.destShape.toList
  -- The placement map's fields already ARE `AffineMap`'s, row per destination dimension and width per
  -- source position, so `applyAffine` applies as-is — no second affine evaluator.
  let placement : AffineMap := { coeffs := s.outCoeffs, bias := s.outBias }
  let fill := constFloat s.fill
  let mut data : Array Float := Array.replicate (destShape.foldl (· * ·) 1) fill
  let mut writtenBy : Std.HashMap Nat (List Nat) := {}
  for sc in allCoords a.outputShape.toList do
    let val ← denseValueAt a [] store sc
    let dc := applyAffine placement sc
    if inBoundsPerDim destShape dc then
      let oc := dc.map Int.toNat
      let fi := flatIndex destShape oc
      let prev := data.getD fi fill
      match s.reduce with
      | .rejectCollisions =>
          match writtenBy[fi]? with
          | some firstSrc => throw (.scatterCollision oc firstSrc (sc.map Int.toNat))
          | none =>
              writtenBy := writtenBy.insert fi (sc.map Int.toNat)
              data := data.set! fi val
      | .overwrite => data := data.set! fi val
      | .sum => data := data.set! fi (prev + val)
      | .max => data := data.set! fi (Max.max prev val)
      | .min => data := data.set! fi (Min.min prev val)
  return { shape := destShape, data := data }

-- `runDensePlan` used to live here (C3), but now that a checked outer graph can contain a `.scan`
-- node (whose worker is `runDenseScan`, `Scan.lean`), it relocated to `EvalPlan.lean` — the only
-- module that can see both this file's `runDenseAssign` and `Scan.lean`'s `runDenseScan` without a
-- circular import. See `EvalPlan.lean`.

end LeanNCD.Eval.Plan
