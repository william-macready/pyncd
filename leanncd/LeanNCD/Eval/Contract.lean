import LeanNCD.Eval.Shape
import LeanNCD.Eval.Gather
import LeanNCD.DSL.TraverseAxes
namespace LeanNCD.Eval
open Std

-- E1 migration sub-project 2: the five `*AxisUIDs` collectors below are re-expressed as
-- `ConstL (List UID)` instantiations of the production `NodeName.traverseAxes` machinery
-- (`LeanNCD/DSL/TraverseAxes.lean`), the UID-direction analogue of sub-project 1's `specs*`
-- migration. Each keeps a frozen `_old` body and a kernel-checked `_eq_old` certifying the new
-- definition equals the prior hand-written one; the `_old`/`_eq_old` scaffolding is deleted in
-- Task B2. `freeAxisUIDs` is deliberately NOT migrated (see its comment).

/-- All axis-UIDs referenced by an index expression. -/
-- Now the `ConstL (List UID)` instantiation of `IdxExpr.traverseAxes`; `idxAxisUIDs_eq_old`
-- certifies it equals the prior hand-written body.
def idxAxisUIDs (e : IdxExpr) : List UID :=
  (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run

-- Frozen pre-migration body: the behaviour-preservation anchor `idxAxisUIDs_eq_old` certifies
-- against; slated for deletion in Task B2 (see the SCAFFOLDING note in `Structural.lean`).
def idxAxisUIDs_old : IdxExpr → List UID
  | .axis a      => [a.uid]
  | .const _     => []
  | .scale _ a   => [a.uid]
  | .shift a _   => [a.uid]
  | .affine _ xs => xs.map (·.2.uid)

/-- Ports the spike theorem `traverseAxes_const_eq_idxAxisUIDs`
    (`test/DSL/TraverseAxesSpike.lean`): the bare-axis arms are `[a.uid]` and `.const` is `[]`
    (all `rfl`); `.affine` folds the coordinate list, pushing the `(·.uid)`-map through each
    `Prod.mk`-repaired const action (`hmap` collapses the `Prod.mk` wrapping). -/
theorem idxAxisUIDs_eq_old (e : IdxExpr) : idxAxisUIDs e = idxAxisUIDs_old e := by
  cases e with
  | axis a => rfl
  | const n => rfl
  | scale c a => rfl
  | shift a n => rfl
  | affine n xs =>
      have hmap : (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> (⟨[ca.2.uid]⟩ : ConstL (List UID) AxisSpec))
          = (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) := rfl
      have core : ∀ ys : List (Int × AxisSpec),
          (Traversable.traverse (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) ys).run
            = ys.map (·.2.uid) := by
        intro ys
        induction ys with
        | nil => rfl
        | cons hd tl ih =>
            show [hd.2.uid] ++
                (Traversable.traverse (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) tl).run
              = hd.2.uid :: List.map (·.2.uid) tl
            rw [ih]
            rfl
      -- restate the goal with the new `idxAxisUIDs` unfolded to its `.run`; RHS is `idxAxisUIDs_old`'s
      -- `.affine` arm `xs.map (·.2.uid)`.
      show (IdxExpr.affine n <$>
          Traversable.traverse (fun ca => Prod.mk ca.1 <$> (⟨[ca.2.uid]⟩ : ConstL (List UID) AxisSpec)) xs :
          ConstL (List UID) IdxExpr).run = xs.map (·.2.uid)
      rw [hmap]
      exact core xs

/-- All axis-UIDs referenced by predicate arithmetic. -/
-- `ConstL (List UID)` instantiation of `PredArith.traverseAxes`; `predAxisUIDs_eq_old` certifies it.
def predAxisUIDs (e : PredArith) : List UID :=
  (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run

-- Frozen pre-migration body; calls the frozen `_old` collectors so it is the faithful original.
-- Slated for Task B2 deletion.
def predAxisUIDs_old : PredArith → List UID
  | .embed e => idxAxisUIDs_old e
  | .mul a b => predAxisUIDs_old a ++ predAxisUIDs_old b
  | .iabs a  => predAxisUIDs_old a

/-- Ports the spike theorem `traverseAxes_const_eq_predAxisUIDs`: `.embed` delegates to
    `idxAxisUIDs_eq_old`; `.mul` pushes the map through the `++` of the two child runs via the
    IHs; `.iabs` is the single-child run. Each `show` restates the goal with the (definitionally
    equal) new collectors so the IH `rw`s find a syntactic match. -/
theorem predAxisUIDs_eq_old (e : PredArith) : predAxisUIDs e = predAxisUIDs_old e := by
  induction e with
  | embed e => exact idxAxisUIDs_eq_old e
  | mul a b iha ihb =>
      show predAxisUIDs a ++ predAxisUIDs b = predAxisUIDs_old a ++ predAxisUIDs_old b
      rw [iha, ihb]
  | iabs a iha =>
      show predAxisUIDs a = predAxisUIDs_old a
      exact iha

/-- All axis-UIDs referenced by a Boolean/mask predicate. -/
-- `ConstL (List UID)` instantiation of `BoolExpr.traverseAxes`; `boolAxisUIDs_eq_old` certifies it.
def boolAxisUIDs (e : BoolExpr) : List UID :=
  (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run

-- Frozen pre-migration body (calls the frozen `_old` collectors); slated for Task B2 deletion.
def boolAxisUIDs_old : BoolExpr → List UID
  | .rel _ a b => predAxisUIDs_old a ++ predAxisUIDs_old b
  | .and a b   => boolAxisUIDs_old a ++ boolAxisUIDs_old b
  | .or  a b   => boolAxisUIDs_old a ++ boolAxisUIDs_old b
  | .not a     => boolAxisUIDs_old a
  | .ieq a b   => predAxisUIDs_old a ++ predAxisUIDs_old b

/-- Ports the spike theorem `traverseAxes_const_eq_boolAxisUIDs`: `.rel`/`.ieq` cross-node
    delegate to `predAxisUIDs_eq_old` over the `++` of the two child runs; `.and`/`.or`/`.not`
    recurse via the IHs. -/
theorem boolAxisUIDs_eq_old (e : BoolExpr) : boolAxisUIDs e = boolAxisUIDs_old e := by
  induction e with
  | rel op a b =>
      show predAxisUIDs a ++ predAxisUIDs b = predAxisUIDs_old a ++ predAxisUIDs_old b
      rw [predAxisUIDs_eq_old a, predAxisUIDs_eq_old b]
  | and a b iha ihb =>
      show boolAxisUIDs a ++ boolAxisUIDs b = boolAxisUIDs_old a ++ boolAxisUIDs_old b
      rw [iha, ihb]
  | or a b iha ihb =>
      show boolAxisUIDs a ++ boolAxisUIDs b = boolAxisUIDs_old a ++ boolAxisUIDs_old b
      rw [iha, ihb]
  | not a iha =>
      show boolAxisUIDs a = boolAxisUIDs_old a
      exact iha
  | ieq a b =>
      show predAxisUIDs a ++ predAxisUIDs b = predAxisUIDs_old a ++ predAxisUIDs_old b
      rw [predAxisUIDs_eq_old a, predAxisUIDs_eq_old b]

/-- The free axes (LHS) of an assign, as UID list (affine slots contribute none). -/
-- Deliberately NOT migrated to `traverseAxes` (unlike the other collectors in this block):
-- `lhsAxisUID?` returns `none` for `.affine` slots, so `freeAxisUIDs` collects a *subset* — the
-- free (non-affine) axes only — not every axis. `LHSSlot.traverseAxes` visits every axis
-- (including the affine slot's `IdxExpr`), so this is not a `traverseAxes` instantiation and the
-- spike proves no equivalence for it. Migrating it would silently change its meaning.
def freeAxisUIDs (slots : List LHSSlot) : List UID := slots.filterMap lhsAxisUID?

/-- Every axis-UID appearing in one product term's reads/masks. This is the per-term
    contraction scope: a `+`-joined RHS sums each term over only the axes *that term*
    mentions, not the union of axes across the whole equation (see `evalAssignWith`). -/
-- `ConstL (List UID)` instantiation of `ProdTerm.traverseAxes`; `termAxisUIDs_eq_old` certifies it.
def termAxisUIDs (t : ProdTerm) : List UID :=
  (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) t).run

-- Frozen pre-migration body (inline per-`Factor` match, calling the frozen `_old` collectors);
-- slated for Task B2 deletion.
def termAxisUIDs_old (t : ProdTerm) : List UID :=
  t.factors.flatMap (fun
    | .read _ es => es.flatMap idxAxisUIDs_old
    | .iverson b => boolAxisUIDs_old b
    | .unaryFn _ _ es => es.flatMap idxAxisUIDs_old)

/-- Ports the spike theorem `traverseAxes_const_eq_termAxisUIDs`, with the inline per-`Factor`
    match handled arm-by-arm as in the spike's `traverseAxes_const_eq_factorAxisUIDs`. `hfac`
    proves each `Factor`'s run equals the matching `_old` arm (`.read`/`.unaryFn` fold
    `idxAxisUIDs_eq_old` over the index list; `.iverson` delegates to `boolAxisUIDs_eq_old`);
    `core` then folds `hfac` over the factor list. -/
theorem termAxisUIDs_eq_old (t : ProdTerm) : termAxisUIDs t = termAxisUIDs_old t := by
  have hfac : ∀ x : Factor,
      (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) x).run
        = (match x with
           | .read _ es => es.flatMap idxAxisUIDs_old
           | .iverson b => boolAxisUIDs_old b
           | .unaryFn _ _ es => es.flatMap idxAxisUIDs_old) := by
    intro x
    cases x with
    | read nm es =>
        show (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) es).run
          = es.flatMap idxAxisUIDs_old
        induction es with
        | nil => rfl
        | cons hd tl ih =>
            show idxAxisUIDs hd ++
                (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
              = idxAxisUIDs_old hd ++ tl.flatMap idxAxisUIDs_old
            rw [idxAxisUIDs_eq_old hd, ih]
    | iverson b => exact boolAxisUIDs_eq_old b
    | unaryFn op nm es =>
        show (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) es).run
          = es.flatMap idxAxisUIDs_old
        induction es with
        | nil => rfl
        | cons hd tl ih =>
            show idxAxisUIDs hd ++
                (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
              = idxAxisUIDs_old hd ++ tl.flatMap idxAxisUIDs_old
            rw [idxAxisUIDs_eq_old hd, ih]
  -- fold `hfac` over the factor list (`termAxisUIDs_old t` is `t.factors.flatMap` of that match).
  show (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) t.factors).run
    = termAxisUIDs_old t
  have core : ∀ ys : List Factor,
      (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run
        = ys.flatMap (fun x =>
            match x with
            | .read _ es => es.flatMap idxAxisUIDs_old
            | .iverson b => boolAxisUIDs_old b
            | .unaryFn _ _ es => es.flatMap idxAxisUIDs_old) := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) hd).run ++
            (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
          = (match hd with
             | .read _ es => es.flatMap idxAxisUIDs_old
             | .iverson b => boolAxisUIDs_old b
             | .unaryFn _ _ es => es.flatMap idxAxisUIDs_old)
            ++ tl.flatMap (fun x =>
                match x with
                | .read _ es => es.flatMap idxAxisUIDs_old
                | .iverson b => boolAxisUIDs_old b
                | .unaryFn _ _ es => es.flatMap idxAxisUIDs_old)
        rw [hfac hd, ih]
  exact core t.factors

/-- Every axis-UID appearing anywhere in the RHS reads/masks (union across all terms).
    Used for size inference / shape solving, where the full axis set is wanted — NOT for
    contraction scoping, which must stay per-term (`termAxisUIDs`). -/
-- Migrated as the `ConstL (List UID)` instantiation of `RHSExpr.traverseAxesNoMask`.
-- IMPORTANT — `traverseAxesNoMask`, NOT `traverseAxesWithMask`: `readAxisUIDs` deliberately
-- EXCLUDES the nonlin-mask axes (the documented `specsRHS`-includes-vs-`readAxisUIDs`-excludes
-- asymmetry). `traverseAxesNoMask` never visits `r.nonlin`. A future edit to `WithMask` here
-- would silently pull nonlin-mask UIDs into shape inference and corrupt it; `readAxisUIDs_eq_old`
-- is the tripwire — it would fail to close. `readAxisUIDs_eq_old` also certifies this equals the
-- prior hand-written body.
def readAxisUIDs (rhs : RHSExpr) : List UID :=
  (RHSExpr.traverseAxesNoMask (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) rhs).run

-- Frozen pre-migration body (calls the frozen `termAxisUIDs_old`); slated for Task B2 deletion.
def readAxisUIDs_old (rhs : RHSExpr) : List UID :=
  rhs.body.terms.flatMap termAxisUIDs_old

/-- Ports the spike theorem `traverseAxes_const_eq_readAxisUIDs` (via `NoMask`): the `NoMask` run
    reduces to `SumExpr`'s traversal over `r.body` (nonlin never touched), then `core` folds
    `termAxisUIDs_eq_old` over `r.body.terms`. -/
theorem readAxisUIDs_eq_old (r : RHSExpr) : readAxisUIDs r = readAxisUIDs_old r := by
  show (SumExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r.body).run
    = r.body.terms.flatMap termAxisUIDs_old
  have core : ∀ ys : List ProdTerm,
      (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run
        = ys.flatMap termAxisUIDs_old := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show termAxisUIDs hd ++
            (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
          = termAxisUIDs_old hd ++ tl.flatMap termAxisUIDs_old
        rw [termAxisUIDs_eq_old hd, ih]
  exact core r.body.terms

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

/-- The declared name of a `Decl`. -/
def declName : Decl → String
  | .tensor n _      => n
  | .predicate n _   => n
  | .linear n _ _    => n
  | .axis ax _       => ax.name

/-- Pick the `Combine` for an output given its decl and the RHS aggregation op.
    Priority: `agg = .max` ⇒ tropical max; `agg = .min` ⇒ tropical min; `predicate` ⇒ bool; else real. -/
def combineFor (decls : List Decl) (nm : String) (agg : AggOp) : Combine :=
  match agg with
  | .max => Combine.max
  | .min => Combine.min
  | .sum => match decls.find? (fun d => declName d == nm) with
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
  let outShape := slots.filterMap (fun sl => match lhsAxisUID? sl with
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
