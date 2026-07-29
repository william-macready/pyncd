import LeanNCD.Eval.Contract
namespace LeanNCD.Eval
open Std

/-- Source axes of a scatter: the axis-UIDs appearing in the affine LHS slots, unioned with the
    RHS read/mask axes; de-duplicated, in first-seen order. -/
def scatterSourceAxes (slots : List LHSSlot) (rhs : RHSExpr) : List UID :=
  (slots.flatMap (fun sl => idxAxisUIDs sl.outIdx) ++ readAxisUIDs rhs).eraseDups

/-- Evaluate a scatter stmt. `outShape` is the output dims (caller supplies, from the decl/inference).
    Each source coord → rhs value (∏ over factors, Σ over terms; no contraction axes beyond source)
    → written to the affine output coord. Output is initialised to `opts.fill`; with
    `opts.reduce = some "sum"` collisions accumulate, otherwise the last write wins (overwrite).
    Out-of-range output coordinates are skipped. -/
def evalScatter (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (nm : String) (slots : List LHSSlot) (rhs : RHSExpr) (opts : ScatterOpts) (outShape : List Nat) :
    Except EvalError (String × DenseTensor) := do
  -- Defensive check (belt-and-suspenders — Spike-3 Stage-0 policy, SHORT-TERM not permanent):
  -- the surface compiler's `checkScatterNonlin` (DSL/Pipeline/Structural.lean) is the primary gate
  -- rejecting a non-identity scatter nonlinearity, but a programmatic caller can build this AST
  -- directly (bypassing validation), and below never applied `rhs.nonlin` to the body — silently
  -- dropping it (the bug this Stage fixes). Fail loud instead of silently erasing it.
  if rhs.nonlin ≠ Nonlin.identity then
    throw s!"evalScatter: non-identity nonlinearity on scatter {nm} is unsupported (Spike-3 Stage-0 policy)"
  -- up-front validation: every read name must be a known tensor
  for rn in (readNames rhs).eraseDups do
    if !(env.contains rn) then
      throw s!"evalScatter: unknown tensor {rn}"
  let srcAxes := scatterSourceAxes slots rhs
  -- Every source axis must have an inferred size; an unsized one is an upstream sizing gap, so
  -- fail loud rather than silently iterating it once (`.getD 1`), which drops source coordinates.
  let srcSizes ← srcAxes.mapM (fun u => match sizes[u]? with
    | some n => pure n
    | none   => throw s!"evalScatter: unsized source axis uid {u}")
  let mut out := DenseTensor.ofFn outShape (fun _ => Float.ofInt opts.fill)
  for sc in cartesian srcSizes do
    let coord : HashMap UID Int := (srcAxes.zip sc).foldl (fun m (u, v) => m.insert u (Int.ofNat v)) {}
    -- rhs value at this source coord: ∏ over a term's factors, Σ over terms (no extra contraction).
    let mut val := 0.0
    for t in rhs.body.terms do
      let mut prod := 1.0
      for f in t.factors do
        match gather env coord f with
        | .ok v   => prod := prod * v
        | .error e => throw e   -- e.g. a .unaryFn domain violation; out-of-range reads are `.ok 0.0`, not `.error`
      val := val + prod
    -- output coordinate = each slot's affine image at this source coord
    let outCoordZ : List Int := slots.map (fun sl => evalIdx coord sl.outIdx)
    if (outCoordZ.zip outShape).all (fun (z, d) => 0 ≤ z && z < (d : Int)) then
      let oc := outCoordZ.map Int.toNat
      let prev := out.get! oc
      let new := match opts.reduce with
        | some "sum" => prev + val
        | some "max" => Max.max prev val
        | _          => val
      out := out.set! oc new
  return (nm, out)

end LeanNCD.Eval
