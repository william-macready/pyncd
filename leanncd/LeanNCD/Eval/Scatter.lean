import LeanNCD.Eval.Contract
import LeanNCD.Eval.Error
namespace LeanNCD.Eval
open Std

/-- Source axes of a scatter: the axis-UIDs appearing in the affine LHS slots, unioned with the
    RHS read/mask axes; de-duplicated, in first-seen order. -/
def scatterSourceAxes (slots : List LHSSlot) (rhs : RHSExpr) : List UID :=
  (slots.flatMap (fun sl => idxAxisUIDs sl.outIdx) ++ readAxisUIDs rhs).eraseDups

/-- Evaluate a scatter stmt. `decls` selects the algebra for a `predicate` destination (Boolean
    `(∧, ∃)`, via `combineFor`); a real destination is unchanged. `outShape` is the output dims (caller supplies, from the decl/inference).
    Each source coord → rhs value (per the 4b `Combine` selected by `rhs.agg` — `.sum`/`.max`/
    `.min` combine terms, not a hardcoded real sum) → written to the affine output coord. Output
    is initialised to `opts.fill`; see `opts.reduce`'s own doc comment for the collision policy.
    Colliding writes (two or more source coords landing on the same output coord) are merged per
    `opts.reduce`: `.rejectCollisions` (default) errors naming both conflicting source coords;
    `.overwrite` keeps the last write; `.sum`/`.max`/`.min` fold every write (including the first)
    starting from `opts.fill`. Non-colliding coordinates behave identically under every policy.
    Out-of-range output coordinates are skipped. -/
def evalScatter (decls : List Decl) (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (nm : String) (slots : List LHSSlot) (rhs : RHSExpr) (opts : ScatterOpts) (outShape : List Nat) :
    Except EvalError (String × DenseTensor) := do
  -- Defensive check (belt-and-suspenders — Spike-3 Stage-0 policy, SHORT-TERM not permanent):
  -- the surface compiler's `checkScatterNonlin` (DSL/Pipeline/Structural.lean) is the primary gate
  -- rejecting a non-identity scatter nonlinearity, but a programmatic caller can build this AST
  -- directly (bypassing validation), and below never applied `rhs.nonlin` to the body — silently
  -- dropping it (the bug this Stage fixes). Fail loud instead of silently erasing it.
  if rhs.nonlin ≠ Nonlin.identity then
    throw (.unsupportedScatterNonlin nm)
  -- up-front validation: every read name must be a known tensor
  for rn in (readNames rhs).eraseDups do
    if !(env.contains rn) then
      throw (.unknownTensor .scatter rn)
  let srcAxes := scatterSourceAxes slots rhs
  -- Every source axis must have an inferred size; an unsized one is an upstream sizing gap, so
  -- fail loud rather than silently iterating it once (`.getD 1`), which drops source coordinates.
  let srcSizes ← srcAxes.mapM (fun u => match sizes[u]? with
    | some n => pure n
    | none   => throw (.shape (.unsizedAxis u .scatterSource)))
  -- RHS aggregation: select the Combine record from rhs.agg (4b), not a hardcoded real
  -- sum-of-products — a maxreduce/minreduce scatter RHS must use tropical max/min, not silently
  -- compute a real sum instead (Wave-C corroborating example, fixed here).
  -- Dtype-aware, like every other worker: `combineFor` selects the Boolean `(∧, ∃)` algebra for a
  -- `predicate`-declared destination, so a Boolean scatter's values stay {0,1}.
  let c : Combine := combineFor decls nm rhs.agg
  -- The `.sum` COLLISION policy folds writes with `+`; into a predicate that would leave {0,1}, so
  -- there it folds with the Boolean `∃` (max) instead.
  let boolDest := isPredicateDest decls nm
  let mut out := DenseTensor.ofFn outShape (fun _ => Float.ofInt opts.fill)
  -- Tracks, per output flat-index, the FIRST source coordinate that wrote there — used only to
  -- name the conflicting pair when `.rejectCollisions` fires; every other policy ignores it.
  let mut writtenBy : HashMap Nat (List Nat) := {}
  for sc in cartesian srcSizes do
    let coord : HashMap UID Int := (srcAxes.zip sc).foldl (fun m (u, v) => m.insert u (Int.ofNat v)) {}
    -- rhs value at this source coord: ∏ over a term's factors (from c.unit1), combined over
    -- terms (from c.unit0) per the Combine selected above.
    let mut val := c.unit0
    for t in rhs.body.terms do
      let mut prod := c.unit1
      for f in t.factors do
        match gather env coord f with
        | .ok v   => prod := c.mul prod v
        | .error e => throw e   -- e.g. a .unaryFn domain violation; out-of-range reads are `.ok 0.0`, not `.error`
      val := c.combine val prod
    -- output coordinate = each slot's affine image at this source coord
    let outCoordZ : List Int := slots.map (fun sl => evalIdx coord sl.outIdx)
    if (outCoordZ.zip outShape).all (fun (z, d) => 0 ≤ z && z < (d : Int)) then
      let oc := outCoordZ.map Int.toNat
      let fi := DenseTensor.flatIdx outShape oc
      let prev := out.get! oc
      match opts.reduce with
      | .rejectCollisions =>
          match writtenBy[fi]? with
          | some firstSrc =>
              throw (.scatterCollision nm oc firstSrc sc)
          | none =>
              writtenBy := writtenBy.insert fi sc
              out := out.set! oc val
      | .overwrite => out := out.set! oc val
      | .sum        => out := out.set! oc (if boolDest then Max.max prev val else prev + val)
      | .max        => out := out.set! oc (Max.max prev val)
      | .min        => out := out.set! oc (Min.min prev val)
  return (nm, out)

end LeanNCD.Eval
