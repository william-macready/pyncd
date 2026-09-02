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

/-- The Dense positional predicate evaluator's only failure: an Iverson leaf whose coefficient width
    disagrees with the iteration coordinate it is evaluated against. The checker (`checkAssign`)
    forbids this at plan-check time, so it is unreachable for any checked plan; kept so the evaluator
    is total and fails loud. Distinct from `PositionalInputError` (this is the predicate arithmetic's
    own error, mapped into `PositionalInputError.predicateWidthMismatch` at the one Dense call site
    that runs it). Lives here beside the coordinate primitives so both `Dense.lean` (Iverson factors)
    and the checked axiswise mask adapter (`Plan/Nonlin.lean`) reach the single evaluator without an
    import cycle — a UID-free positional predicate is a coordinate primitive, same category as
    `inBoundsPerDim`. -/
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

end LeanNCD.Eval.Plan
