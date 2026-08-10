import LeanNCD.Eval.Plan.Coordinates

/-!
# Wave C shared coordinate primitives tests

Covers `allCoords`, `applyAffine`, `flatIndex`, and `inBoundsPerDim` (`Coordinates.lean`)
independently of `Dense.lean`'s `gatherFactor`, which merely calls them.
-/

namespace LeanNCD.Eval.Plan.CoordinatesTest
open LeanNCD.Eval.Plan

/-!
## `allCoords` — row-major enumeration order
-/

-- scalar: one empty coordinate.
#guard allCoords [] == [[]]

-- rank-1.
#guard allCoords [3] == [[0], [1], [2]]

-- rank-2: the LAST index varies fastest (row-major).
#guard allCoords [2, 3] ==
  [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2]]

-- zero extents produce no coordinates, whether the zero dimension is the only one, the outer one,
-- or the inner one.
#guard allCoords [0] == []
#guard allCoords [0, 3] == []
#guard allCoords [2, 0] == []

/-!
## `applyAffine` — positive, negative, scaled, zero-coefficient, multi-axis rows
-/

-- positive coefficient, zero bias.
#guard applyAffine { coeffs := #[#[1]], bias := #[0] } [5] == [5]

-- negative bias (a shift read, e.g. `X[i-2]`).
#guard applyAffine { coeffs := #[#[1]], bias := #[-2] } [0] == [-2]

-- scaled coefficient (a stride read, e.g. `X[2*i]`).
#guard applyAffine { coeffs := #[#[2]], bias := #[0] } [3] == [6]

-- zero-coefficient row: the source coordinate is the bias alone, independent of the iteration
-- coordinate.
#guard applyAffine { coeffs := #[#[0, 0]], bias := #[5] } [2, 3] == [5]

-- multi-axis affine row, e.g. `X[2*i + j]`.
#guard applyAffine { coeffs := #[#[2, 1]], bias := #[0] } [1, 2] == [4]

/-!
## `flatIndex` — valid row-major flat indices
-/

#guard flatIndex [4] [3] == 3
#guard flatIndex [2, 3] [1, 2] == 5
#guard flatIndex [2, 3] [0, 0] == 0

/-!
## `inBoundsPerDim` — per-dimension validity, tested BEFORE flattening
-/

-- in range on every dimension.
#guard inBoundsPerDim [2, 3] [1, 2] == true

-- negative on one dimension.
#guard inBoundsPerDim [2, 3] [-1, 0] == false

-- at (not past) the extent on one dimension — the upper bound is exclusive.
#guard inBoundsPerDim [2, 3] [2, 0] == false
#guard inBoundsPerDim [2, 3] [0, 3] == false

/-- Same folding formula as `flatIndex`, but over `Int` — used only in this test to demonstrate why
    `inBoundsPerDim` must be checked BEFORE flattening, not after (proposal §8.3). -/
def intFlatten (shape : List Nat) (coord : List Int) : Int :=
  (shape.zip coord).foldl (fun acc (d, c) => acc * (d : Int) + c) 0

-- The alias fixture: against `shape = [2, 3]`, the per-dimension-invalid coordinate `[-1, 3]`
-- (dimension 0 is negative; dimension 1 is at its extent) has the SAME naive flattened offset
-- (`-1*3 + 3 = 0`) as the genuinely valid coordinate `[0, 0]`. `inBoundsPerDim` must reject
-- `[-1, 3]` outright — flattening it first and only then bounds-checking the *offset* would let
-- it alias onto valid address `0` and silently read `[0, 0]`'s value instead of zero-padding.
#guard inBoundsPerDim [2, 3] [-1, 3] == false
#guard intFlatten [2, 3] [-1, 3] == (flatIndex [2, 3] [0, 0] : Int)

end LeanNCD.Eval.Plan.CoordinatesTest
