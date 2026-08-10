import LeanNCD.Eval.Plan.Kernel

/-!
# Wave C shared row-major coordinate primitives (C2)

Row-major coordinate enumeration, affine application, flattening, and the per-dimension bounds
predicate `Dense.lean`'s `gatherFactor` uses to gather one factor. Extracted from `Dense.lean`
unchanged so a future experimental backend can reuse these exact equations without introducing any
JAX/lookup-table/source-name/codegen concept into this production module.
-/

namespace LeanNCD.Eval.Plan

/-- Row-major coordinate enumeration: the last index varies fastest (C0's declared order). -/
def allCoords : List Nat → List (List Int)
  | [] => [[]]
  | d :: rest => (List.range d).flatMap (fun i => (allCoords rest).map (fun c => Int.ofNat i :: c))

/-- Flatten a row-major coordinate against `shape` into a single storage offset. -/
def flatIndex (shape : List Nat) (coord : List Nat) : Nat :=
  (shape.zip coord).foldl (fun acc (d, c) => acc * d + c) 0

/-- `coeffs * iteration + bias`, one component per source dimension. -/
def applyAffine (m : AffineMap) (iter : List Int) : List Int :=
  (m.coeffs.toList.zip m.bias.toList).map (fun (row, b) =>
    (row.toList.zip iter).foldl (fun acc (c, x) => acc + c * x) b)

/-- Per-dimension bounds predicate: `true` iff every coordinate component lies within its own
    dimension's extent `[0, d)`. Callers MUST test this before calling `flatIndex` — testing the
    flattened offset instead can alias distinct invalid coordinates onto a valid flat address
    (proposal §8.3). -/
def inBoundsPerDim (shape : List Nat) (coord : List Int) : Bool :=
  (shape.zip coord).all (fun (d, z) => 0 ≤ z && z < (d : Int))

end LeanNCD.Eval.Plan
