import LeanNCD.Eval.Shape
import LeanNCD.Eval.Gather
import LeanNCD.DSL.TraverseAxes
namespace LeanNCD.Eval
open Std

-- E1 migration sub-project 2: the five `*AxisUIDs` collectors below are `ConstL (List UID)`
-- instantiations of the production `NodeName.traverseAxes` machinery
-- (`LeanNCD/DSL/TraverseAxes.lean`), the UID-direction analogue of sub-project 1's `specs*`
-- migration. `freeAxisUIDs` is deliberately NOT migrated (see its comment).

/-- All axis-UIDs referenced by an index expression.
    The `ConstL (List UID)` instantiation of `IdxExpr.traverseAxes`. -/
def idxAxisUIDs (e : IdxExpr) : List UID :=
  (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run

/-- All axis-UIDs referenced by predicate arithmetic.
    The `ConstL (List UID)` instantiation of `PredArith.traverseAxes`. -/
def predAxisUIDs (e : PredArith) : List UID :=
  (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run

/-- All axis-UIDs referenced by a Boolean/mask predicate.
    The `ConstL (List UID)` instantiation of `BoolExpr.traverseAxes`. -/
def boolAxisUIDs (e : BoolExpr) : List UID :=
  (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run

/-- The free axes (LHS) of an assign, as UID list (affine slots contribute none). -/
-- Deliberately NOT migrated to `traverseAxes` (unlike the other collectors in this block):
-- `LHSSlot.axisUID?` returns `none` for `.affine` slots, so `freeAxisUIDs` collects a *subset* — the
-- free (non-affine) axes only — not every axis. `LHSSlot.traverseAxes` visits every axis
-- (including the affine slot's `IdxExpr`), so this is not a `traverseAxes` instantiation and the
-- spike proves no equivalence for it. Migrating it would silently change its meaning.
def freeAxisUIDs (slots : List LHSSlot) : List UID := slots.filterMap (·.axisUID?)

/-- Every axis-UID appearing in one product term's reads/masks. This is the per-term
    contraction scope: a `+`-joined RHS sums each term over only the axes *that term*
    mentions, not the union of axes across the whole equation (see `evalAssignWith`).
    The `ConstL (List UID)` instantiation of `ProdTerm.traverseAxes`. -/
def termAxisUIDs (t : ProdTerm) : List UID :=
  (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) t).run

/-- Every axis-UID appearing anywhere in the RHS reads/masks (union across all terms).
    Used for size inference / shape solving, where the full axis set is wanted — NOT for
    contraction scoping, which must stay per-term (`termAxisUIDs`). -/
-- The `ConstL (List UID)` instantiation of `RHSExpr.traverseAxesNoMask`.
-- IMPORTANT — `traverseAxesNoMask`, NOT `traverseAxesWithMask`: `readAxisUIDs` deliberately
-- EXCLUDES the nonlin-mask axes (the documented `specsRHS`-includes-vs-`readAxisUIDs`-excludes
-- asymmetry). `traverseAxesNoMask` never visits `r.nonlin`. A future edit to `WithMask` here
-- would silently pull nonlin-mask UIDs into shape inference and corrupt it — do not change it.
def readAxisUIDs (rhs : RHSExpr) : List UID :=
  (RHSExpr.traverseAxesNoMask (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) rhs).run

/-- Every `.read` tensor name appearing in the RHS. -/
def readNames (rhs : RHSExpr) : List String :=
  rhs.body.terms.flatMap (fun t => t.factors.filterMap (fun
    | .read nm _ => some nm
    | .iverson _ => none
    | .unaryFn _ nm _ => some nm))

/-- The cartesian product of `[0..d-1]` ranges (one per dimension). Reuses `allCoords`. -/
def cartesian (dims : List Nat) : List (List Nat) := DenseTensor.allCoords dims

/-- Evaluate a `.plain` assign (identity nonlin) to its output tensor.
    `mul` combines factors within a product term; `combine` folds contributions onto the
    accumulator starting from `unit0`. Default is the ℝ contraction `(*, +, 0)`.

    Each product term is contracted **independently**, over only the axes that term itself
    mentions (`termAxisUIDs`), then its result is folded into the output accumulator via
    `combine`. This is standard per-term (Einstein) summation scoping: a `k`-less term like
    `a[i]` in `Y[i] := a[i] + W[i,k]·v[k]` must never be summed over `k` at all, since it has
    no `k`-dependence. Scoping contraction at the whole-equation level instead (one shared
    axis set for every term) would force `a[i]` through a `k`-indexed loop it doesn't need,
    adding it in `|k|` times instead of once.

    All `.read`/`.unaryFn` tensor names are validated against `env` up front. A `gather` error
    during accumulation is now genuinely reachable — a `.unaryFn` domain violation (e.g.
    `log` of a non-positive value) — and propagates as a hard `.error`, per this evaluator's
    fail-loud convention; it is never treated as an out-of-range pad (out-of-range reads return
    `.ok 0.0` directly from `gather`, they never reach the `.error` branch at all). -/
def evalAssignWith (mul : Float → Float → Float) (combine : Float → Float → Float) (unit0 : Float)
    (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (nm : String) (slots : List LHSSlot) (rhs : RHSExpr) : Except EvalError (String × DenseTensor) := do
  -- up-front validation: every read name must be a known tensor
  for rn in (readNames rhs).eraseDups do
    if !(env.contains rn) then
      throw s!"evalAssign: unknown tensor {rn}"
  let frees := freeAxisUIDs slots
  -- fail loud: a free output axis with no inferred size would silently yield a 0-extent tensor.
  for u in frees do
    if (sizes[u]?).isNone then
      throw s!"evalAssign {nm}: output axis (uid {u}) has no inferable size (it appears in no read position)"
  let outShape := outputShape sizes slots
  let data ← (DenseTensor.allCoords outShape).mapM (fun fcoord => do
      let baseCoord : HashMap UID Int := (frees.zip fcoord).foldl (fun m (u, v) => m.insert u (Int.ofNat v)) {}
      let mut acc := unit0
      for t in rhs.body.terms do
        let termContr := (termAxisUIDs t).eraseDups.filter (fun u => ! frees.contains u)
        let termSizes := termContr.map (fun u => (sizes[u]?).getD 1)
        let mut termAcc := unit0
        for cc in cartesian termSizes do
          let coord := (termContr.zip cc).foldl (fun m (u, v) => m.insert u (Int.ofNat v)) baseCoord
          let mut prod := 1.0
          for f in t.factors do
            match gather env coord f with
            | .ok v   => prod := mul prod v
            | .error e => throw e
          termAcc := combine termAcc prod
        acc := combine acc termAcc
      pure acc)
  return (nm, ⟨outShape, data.toArray⟩)

/-- The default tensor (ℝ) contraction: multiply factors, then sum contributions. -/
def evalAssign := evalAssignWith (· * ·) (· + ·) 0.0

/-- The contraction "semiring" to use for an output, selected by its declared dtype. -/
structure Combine where
  mul     : Float → Float → Float
  combine : Float → Float → Float
  unit0   : Float

/-- The ℝ contraction `(×, Σ)`: multiply factors, then sum. -/
def Combine.real : Combine := ⟨(· * ·), (· + ·), 0.0⟩

/-- The Boolean contraction `(∧, ∃)` on 0/1 Floats: `min` factors (∧), `max` terms (∃). -/
def Combine.bool : Combine := ⟨min, max, 0.0⟩

/-- The tropical max contraction `(×, max, −∞)`: multiply factors within a term, then take max
    across terms and contracted axes. Identity is `−∞` so all-negative inputs reduce correctly. -/
def Combine.max : Combine := ⟨(· * ·), fun (a b : Float) => Max.max a b, -1.0 / 0.0⟩

/-- The tropical min contraction `(×, min, +∞)`: multiply factors within a term, then take min
    across terms and contracted axes. Identity is `+∞` so all-positive inputs reduce correctly. -/
def Combine.min : Combine := ⟨(· * ·), fun (a b : Float) => Min.min a b, 1.0 / 0.0⟩

/-- Pick the `Combine` for an output given its decl and the RHS aggregation op.
    Priority: `agg = .max` ⇒ tropical max; `agg = .min` ⇒ tropical min; `predicate` ⇒ bool; else real. -/
def combineFor (decls : List Decl) (nm : String) (agg : AggOp) : Combine :=
  match agg with
  | .max => Combine.max
  | .min => Combine.min
  | .sum => match decls.find? (fun d => d.name == nm) with
      | some (.predicate _ _) => Combine.bool
      | _                     => Combine.real

/-- dtype-aware assign: choose the `Combine` from the decls and `rhs.agg`, then evaluate.
    `agg = .max` ⇒ tropical `(×, max, −∞)`;
    `predicate` ⇒ Boolean `(∧, ∃)`;
    else ℝ `(×, Σ, 0)`. -/
def evalAssignDtyped (decls : List Decl)
    (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (nm : String) (slots : List LHSSlot) (rhs : RHSExpr) :
    Except EvalError (String × DenseTensor) :=
  let c := combineFor decls nm rhs.agg
  evalAssignWith c.mul c.combine c.unit0 env sizes nm slots rhs

/-- Like `evalAssign`, but with a `seed : HashMap UID Int` of axis-UIDs pinned to fixed values
    (e.g. the iteration axis of a scan, pinned to the current slice `l`). The seeded UIDs are
    excluded from BOTH the free (output) axes and the contracted axes; every per-output coord is
    seeded with these fixed values. Output shape/order follows the NON-seeded free slots.
    Uses the caller-supplied contraction `(mul, combine, unit0)`, so a `maxreduce` scan step
    reduces with tropical max — not the ℝ sum (KG-scanagg). -/
def evalAssignSeeded (mul : Float → Float → Float) (combine : Float → Float → Float) (unit0 : Float)
    (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (seed : HashMap UID Int) (nm : String) (slots : List LHSSlot) (rhs : RHSExpr) :
    Except EvalError (String × DenseTensor) := do
  for rn in (readNames rhs).eraseDups do
    if !(env.contains rn) then
      throw s!"evalAssign: unknown tensor {rn}"
  -- free axes = LHS slot axes minus the seeded UIDs (and minus affine slots, which contribute none)
  let freesAll := freeAxisUIDs slots
  let frees := freesAll.filter (fun u => ! seed.contains u)
  -- output shape: each non-seeded free slot's size, in slot order
  let outShape := slots.filterMap (fun sl => match sl.axisUID? with
    | some u => if seed.contains u then none else some ((sizes[u]?).getD 0)
    | none   => none)
  let data ← (DenseTensor.allCoords outShape).mapM (fun fcoord => do
      let baseCoord : HashMap UID Int :=
        (frees.zip fcoord).foldl (fun m (u, v) => m.insert u (Int.ofNat v)) seed
      let mut acc := unit0
      for t in rhs.body.terms do
        -- per-term contraction scoping, same rationale as `evalAssignWith`.
        let termContr := (termAxisUIDs t).eraseDups.filter (fun u => ! frees.contains u && ! seed.contains u)
        let termSizes := termContr.map (fun u => (sizes[u]?).getD 1)
        let mut termAcc := unit0
        for cc in cartesian termSizes do
          let coord := (termContr.zip cc).foldl (fun m (u, v) => m.insert u (Int.ofNat v)) baseCoord
          let mut prod := 1.0
          for f in t.factors do
            match gather env coord f with
            | .ok v   => prod := mul prod v
            | .error e => throw e
          termAcc := combine termAcc prod
        acc := combine acc termAcc
      pure acc)
  return (nm, ⟨outShape, data.toArray⟩)

end LeanNCD.Eval
