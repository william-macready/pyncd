import LeanNCD.Eval.Plan.Types
import LeanNCD.DSL.Ast


/-!
# Wave C local operation IR (C2)

One complete local tensor operation, with iteration space, affine pullback maps, factor product,
and ordered pushforward all explicit — the decomposition MLIR Linalg motivates (proposal §11.3).
No graph scheduling, no source names, no axis UIDs: those belong to `Compile.lean` (C4) and are
compiled away before an `AssignPlan` exists.
-/

namespace LeanNCD.Eval.Plan

/-- `UnaryOp` (`DSL/Ast.lean`) derives `DecidableEq` but not `BEq`; `ReadPlan` derives `BEq`, so it
    needs one for its `Option UnaryOp` field. Mirrors the manual instances `Plan/Nonlin.lean` adds
    for `PointwiseFn`/`AxiswiseFn`. -/
instance : BEq LeanNCD.UnaryOp := ⟨fun a b => decide (a = b)⟩

/-- An integer-affine map `sourceCoordinate = coeffs * iterationCoordinate + bias`, with one
    `coeffs` row and one `bias` component per SOURCE dimension, each row of term-basis width.
    Kept as one row per source dimension rather than a flattened offset because zero-padding
    validity is defined per source dimension: flattening first can alias distinct invalid
    coordinates onto a valid flat address (proposal §8.3). -/
structure AffineMap where
  coeffs : Array (Array Int)
  bias   : Array Int
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One factor: a gather from `sourceSlot` through `map`, against a shape the checker has already
    verified equals that slot's signature. `unary`, when present, is a transcendental function
    (`log`/`exp`/…) applied to the gathered value AFTER the out-of-bounds zero-pad — so an
    out-of-bounds read contributes `f(0)`, matching the reference `gather` exactly. -/
structure ReadPlan where
  sourceSlot  : TensorSlot
  map         : AffineMap
  sourceShape : Array Nat
  oobPolicy   : OutOfBoundsPolicy
  unary       : Option UnaryOp := none
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One affine predicate leaf over a positional iteration coordinate. -/
structure PosAffine where
  coeffs : Array Int
  bias : Int
  deriving DecidableEq, BEq, Repr, Inhabited

/-- UID-free predicate arithmetic. -/
inductive PosPredArith
  | affine : PosAffine → PosPredArith
  | mul : PosPredArith → PosPredArith → PosPredArith
  | iabs : PosPredArith → PosPredArith
  deriving DecidableEq, BEq, Repr, Inhabited

/-- UID-free Boolean predicate. -/
inductive PosBoolExpr
  | rel : RelOp → PosPredArith → PosPredArith → PosBoolExpr
  | and : PosBoolExpr → PosBoolExpr → PosBoolExpr
  | or : PosBoolExpr → PosBoolExpr → PosBoolExpr
  | not : PosBoolExpr → PosBoolExpr
  | ieq : PosPredArith → PosPredArith → PosBoolExpr
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Ordered factor: a tensor read or a positional Iverson predicate, in source order. -/
inductive FactorPlan
  | read : ReadPlan → FactorPlan
  | iverson : PosBoolExpr → FactorPlan
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The underlying read of a factor, or a default `ReadPlan` for a predicate factor. TEST-ONLY: a
    convenience for fixtures that operate over read factors only (every factor a source program
    compiles to is a `.read` today, so this never actually hits the predicate arm there) and index
    straight into `.factors` without the `.iverson`-skip discipline production code uses. Production
    code must go through `TermPlan.forEachReadFactor`/`readSourceSlots`/`hasIverson` instead — those
    skip `.iverson` factors rather than silently substituting a garbage default `ReadPlan` for one. -/
def FactorPlan.readOrDefault : FactorPlan → ReadPlan
  | .read r => r
  | .iverson _ => default

/-- Every affine leaf's coefficient-row width in a positional predicate arithmetic tree, in
    left-to-right leaf order. The checker compares each against the term's `iterationShape.size`;
    a UID-free predicate leaf must span exactly the term's positional iteration basis. -/
def PosPredArith.affineWidths : PosPredArith → List Nat
  | .affine a => [a.coeffs.size]
  | .mul x y => x.affineWidths ++ y.affineWidths
  | .iabs x => x.affineWidths

/-- Every affine leaf's coefficient-row width in a positional Boolean predicate, in left-to-right
    leaf order (delegating to `PosPredArith.affineWidths` at each arithmetic operand). -/
def PosBoolExpr.affineWidths : PosBoolExpr → List Nat
  | .rel _ a b => a.affineWidths ++ b.affineWidths
  | .and a b => a.affineWidths ++ b.affineWidths
  | .or a b => a.affineWidths ++ b.affineWidths
  | .not a => a.affineWidths
  | .ieq a b => a.affineWidths ++ b.affineWidths

/-- One product term. `iterationShape` is the term's coordinate basis (retained output axes
    followed by that term's contracted axes); `contextPos`/`outputPos`/`reductionPos` classify
    every position of that basis. The classification is explicit rather than rediscovered from
    affine coefficients: a syntactically-mentioned axis can densify to a zero coefficient yet still
    belong to the reduction domain, and so still affect multiplicity (proposal §7.4).

    `factors` is ONE ordered array of `FactorPlan` (`read | iverson`) in source order — never two
    parallel arrays. Every filtered traversal (source-slot discovery, forward-read/causality checks)
    keeps the ORIGINAL all-factor index, never a reindexed filtered-read index. -/
structure TermPlan where
  iterationShape : Array Nat
  contextPos     : Array Nat
  outputPos      : Array Nat
  reductionPos   : Array Nat
  factors        : Array FactorPlan
  deriving DecidableEq, BEq, Repr, Inhabited

/-- This term's `.read` factors only, paired with each one's original all-factor index (`fi`) —
    never a reindexed read-only index — dropping `.iverson` factors (they read no store slot,
    capture no scan state, and have no source slot to check). This is the ONE shared derivation
    behind every "skip predicate factors, check the rest" site: `Block.lean`/`EvalPlan.lean`'s
    forward-read checks, `Scan.lean`/`Compile.lean`'s causality checks, and `Dense.lean`'s runtime
    store validation — each still iterates the result with its own ordinary `for`, so it keeps
    throwing its own error type with no monad-genericity indirection. -/
def TermPlan.readFactorsIndexed (t : TermPlan) : List (Nat × ReadPlan) :=
  t.factors.toList.zipIdx.filterMap (fun (f, fi) => match f with
    | .read r => some (fi, r) | .iverson _ => none)

/-- Every `.read` factor's source slot, in source order, dropping `.iverson` factors. Shared by
    `PlanStep.sourceSlots`/`BlockStep.sourceSlots`'s `.assign` arm — both flatten the same shape
    over the same `TermPlan`, so it lives once here. -/
def TermPlan.readSourceSlots (t : TermPlan) : Array TensorSlot :=
  t.factors.filterMap (fun f => match f with
    | .read r => some r.sourceSlot | .iverson _ => none)

/-- Whether this term carries at least one Iverson predicate factor. -/
def TermPlan.hasIverson (t : TermPlan) : Bool :=
  t.factors.any (fun f => match f with | .iverson _ => true | .read _ => false)

/-- One complete local operation: terms combined into one destination tensor under one algebra,
    evaluated at one runtime context coordinate (empty for a top-level, scan-free assignment). -/
structure AssignPlan where
  contextShape    : Array Nat
  destinationSlot : TensorSlot
  outputShape     : Array Nat
  terms           : Array TermPlan
  algebra         : ContractionAlgebra
  deriving DecidableEq, BEq, Repr, Inhabited

end LeanNCD.Eval.Plan
