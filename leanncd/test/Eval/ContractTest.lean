import LeanNCD.Eval.Contract
import LeanNCD.Eval.SizeInfer   -- `inferAxisSizes`, used directly below (was transitive via `Eval.Shape`)
namespace LeanNCD.Eval
open Std
private def ax (nm : String) (u : Nat) : AxisSpec := { name := nm, uid := u, kind := .real }
private def tensorOf (shape : List Nat) (xs : List Float) : DenseTensor := ⟨shape, xs.toArray⟩

-- W (2×3) · X (3×2) = known 2×2 product.
-- W = [[1,2,3],[4,5,6]], X = [[1,0],[0,1],[1,1]]  ⇒  W·X = [[4,5],[10,11]]
run_cmd do
  let i := ax "i" 1; let k := ax "k" 2; let j := ax "j" 3
  let W := tensorOf [2,3] [1,2,3, 4,5,6]
  let X := tensorOf [3,2] [1,0, 0,1, 1,1]
  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "W" W).insert "X" X
  let mm : Stmt := .assign "Y" [.free i, .free j]
    { body := { terms := [{ factors := [.read "W" [.axis i, .axis k], .read "X" [.axis k, .axis j]] }] }, nonlin := .identity }
  match inferAxisSizes {} env [mm] with
  | .error e => throwError (toString e)
  | .ok (sizes, _) =>
    match evalAssign env sizes "Y" [.free i, .free j] { body := { terms := [{ factors := [.read "W" [.axis i, .axis k], .read "X" [.axis k, .axis j]] }] }, nonlin := .identity } with
    | .error e => throwError (toString e)
    | .ok (_, Y) =>
        let expected := tensorOf [2,2] [4,5, 10,11]
        unless DenseTensor.approxEq Y expected do throwError s!"matmul wrong: {repr Y.data}"

-- elementwise sum of two terms: Z[i] := A[i] + B[i]  (A=[1,2,3], B=[10,20,30]) ⇒ [11,22,33]
run_cmd do
  let i := ax "i" 1
  let A := tensorOf [3] [1,2,3]; let B := tensorOf [3] [10,20,30]
  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "A" A).insert "B" B
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "A" [.axis i]] }, { factors := [.read "B" [.axis i]] }] }, nonlin := .identity }
  match inferAxisSizes {} env [.assign "Z" [.free i] rhs] with
  | .error e => throwError (toString e)
  | .ok (sizes, _) => match evalAssign env sizes "Z" [.free i] rhs with
    | .error e => throwError (toString e)
    | .ok (_, Z) => unless DenseTensor.approxEq Z (tensorOf [3] [11,22,33]) do throwError "sum wrong"

-- missing input tensor ⇒ .error (not silent 0)
run_cmd do
  let i := ax "i" 1
  let A := tensorOf [3] [1,2,3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "A" A
  let sizes : HashMap UID Nat := ({} : HashMap UID Nat).insert 1 3
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "MISSING" [.axis i]] }] }, nonlin := .identity }
  match evalAssign env sizes "Q" [.free i] rhs with
  | .error _ => pure ()
  | .ok _ => throwError "expected error for missing input tensor"

-- Masked aggregation: Result[] := F[t,i]·F[t,j]·edge[i,j], all axes contracted ⇒ scalar.
-- F : [1,2] (t=1, i/j=2): F = [[1, 1]] (so F[0,0]=1, F[0,1]=1). edge : [2,2] = [[1,0],[0,1]] (identity).
-- ℝ reading: Σ_{t,i,j} F[t,i]·F[t,j]·edge[i,j] = (i=j terms) F[0,0]²·1 + F[0,1]²·1 = 1 + 1 = 2.
run_cmd do
  let t := ax "t" 1; let i := ax "i" 2; let j := ax "j" 3
  let F := tensorOf [1,2] [1, 1]
  let edge := tensorOf [2,2] [1,0, 0,1]
  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "F" F).insert "edge" edge
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "F" [.axis t, .axis i], .read "F" [.axis t, .axis j], .read "edge" [.axis i, .axis j]] }] }, nonlin := .identity }
  match inferAxisSizes {} env [.assign "Result" [] rhs] with
  | .error e => throwError (toString e)
  | .ok (sizes, _) =>
    -- ℝ (tensor) reading ⇒ scalar 2.0
    match evalAssignDtyped [.tensor "Result" []] env sizes "Result" [] rhs with
    | .error e => throwError (toString e)
    | .ok (_, R) => unless DenseTensor.approxEq R (tensorOf [] [2.0]) do throwError s!"ℝ agg wrong: {repr R.data}"
    -- Boolean (predicate) reading ⇒ ∃ t,i,j with all-1 ⇒ 1.0 (there is such a term)
    match evalAssignDtyped [.predicate "Result" []] env sizes "Result" [] rhs with
    | .error e => throwError (toString e)
    | .ok (_, R) => unless DenseTensor.approxEq R (tensorOf [] [1.0]) do throwError s!"Bool agg wrong: {repr R.data}"

-- 4b: a term with an EMPTY factor list must fold to the Combine's `unit1`, not a hard-coded 1.0.
-- Use a synthetic min-plus-style Combine (mul = add, combine = min) to make the difference
-- observable: if the product fold still started from a literal 1.0, this would wrongly give
-- combine(unit0, 1.0) = min(+inf, 1.0) = 1.0 instead of the correct min(+inf, 0.0) = 0.0.
run_cmd do
  let minPlus : Combine := { mul := (· + ·), combine := Min.min, unit0 := 1.0 / 0.0, unit1 := 0.0 }
  let env : HashMap String DenseTensor := {}
  let rhs : RHSExpr := { body := { terms := [{ factors := [] }] }, nonlin := .identity }
  match evalAssignWith minPlus.mul minPlus.combine minPlus.unit0 minPlus.unit1 env {} "Z" [] rhs with
  | .error e => throwError s!"4b empty-product: unexpected error {e}"
  | .ok (_, Z) => unless DenseTensor.approxEq Z (tensorOf [] [0.0]) do
      throwError s!"4b empty-product: got {repr Z.data}, want [0.0] (unit1 not threaded through)"

-- 4a: an out-of-range seed coordinate must be rejected.
-- (mul/combine bound to explicitly-typed `let`s, and LHSSlot/Except spelled out rather than
-- dot notation — passing `(· * ·)`/`(· + ·)` inline stalls expected-type propagation for the
-- `slots` argument, breaking plain `.iterAt`/`.free`/`.error`/`.ok`; caught while executing Task 1.)
run_cmd do
  let k := ax "k" 2
  let X := tensorOf [2] [1, 2]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes : HashMap UID Nat := ({} : HashMap UID Nat).insert 2 2
  let seed : HashMap UID Int := ({} : HashMap UID Int).insert 2 5   -- 5 ∉ [0, 2)
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis k]] }] }, nonlin := .identity }
  let mul : Float → Float → Float := (· * ·)
  let combine : Float → Float → Float := (· + ·)
  match evalAssignSeeded mul combine 0.0 1.0 env sizes seed "Y" [LHSSlot.iterAt k 0] rhs with
  | Except.error (.invalidSeed "Y" 2 5 2) => pure ()
  | Except.error e => throwError s!"4a: wrong error for out-of-range seed: {e}"
  | Except.ok _    => throwError "4a: expected rejection of out-of-range seed coordinate 5 ∉ [0, 2)"

-- 4a: empty seed gives the same result as the unseeded wrapper (evalAssignWith IS
-- evalAssignSeeded with seed = {} — this is the definitional check for the unification).
run_cmd do
  let i := ax "i" 1
  let A := tensorOf [3] [1, 2, 3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "A" A
  let sizes : HashMap UID Nat := ({} : HashMap UID Nat).insert 1 3
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "A" [.axis i]] }] }, nonlin := .identity }
  let mul : Float → Float → Float := (· * ·)
  let combine : Float → Float → Float := (· + ·)
  match evalAssignWith mul combine 0.0 1.0 env sizes "Y" [LHSSlot.free i] rhs,
        evalAssignSeeded mul combine 0.0 1.0 env sizes {} "Y" [LHSSlot.free i] rhs with
  | Except.ok (_, a), Except.ok (_, b) => unless DenseTensor.approxEq a b do
      throwError s!"4a: evalAssignWith {repr a.data} ≠ evalAssignSeeded-with-empty-seed {repr b.data}"
  | _, _ => throwError "4a: one of the two calls errored unexpectedly"
end LeanNCD.Eval
