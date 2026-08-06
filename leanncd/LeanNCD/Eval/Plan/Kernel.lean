import LeanNCD.Eval.Plan.Types

/-!
# Wave C local operation IR (C2)

One complete local tensor operation, with iteration space, affine pullback maps, factor product,
and ordered pushforward all explicit — the decomposition MLIR Linalg motivates (proposal §11.3).
No graph scheduling, no source names, no axis UIDs: those belong to `Compile.lean` (C4) and are
compiled away before an `AssignPlan` exists.
-/

namespace LeanNCD.Eval.Plan

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
    verified equals that slot's signature. -/
structure ReadPlan where
  sourceSlot  : TensorSlot
  map         : AffineMap
  sourceShape : Array Nat
  oobPolicy   : OutOfBoundsPolicy
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One product term. `iterationShape` is the term's coordinate basis (retained output axes
    followed by that term's contracted axes); `outputPos`/`reductionPos` classify every position
    of that basis. The classification is explicit rather than rediscovered from affine
    coefficients: a syntactically-mentioned axis can densify to a zero coefficient yet still
    belong to the reduction domain, and so still affect multiplicity (proposal §7.4). -/
structure TermPlan where
  iterationShape : Array Nat
  outputPos      : Array Nat
  reductionPos   : Array Nat
  factors        : Array ReadPlan
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One complete local operation: terms combined into one destination tensor under one algebra. -/
structure AssignPlan where
  destinationSlot : TensorSlot
  outputShape     : Array Nat
  terms           : Array TermPlan
  algebra         : ContractionAlgebra
  deriving DecidableEq, BEq, Repr, Inhabited

end LeanNCD.Eval.Plan
