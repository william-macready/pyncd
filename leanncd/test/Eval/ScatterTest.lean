import LeanNCD.Eval.Scatter
namespace LeanNCD.Eval
open Std
private def ax (nm : String) (u : Nat) : AxisSpec := { name := nm, uid := u, kind := .real }
private def tensorOf (shape : List Nat) (xs : List Float) : DenseTensor := ⟨shape, xs.toArray⟩
-- `evalScatter` refuses a binary32-committed name (undeclared names are binary32 since the F32
-- flip), so every fixture below spells its involved names `f64` explicitly.
private def f64Decls : List Decl :=
  ["Out", "X", "A", "B"].map (fun n => Decl.typedTensor .f64 n [])

-- upsample: Out[2*i, 2*j] := X[i,j], X = [[1,2],[3,4]] (2×2) ⇒ 4×4 with X at even coords, 0 elsewhere.
run_cmd do
  let i := ax "i" 1; let j := ax "j" 2
  let X := tensorOf [2,2] [1,2, 3,4]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let slots : List LHSSlot := [.affine (.scale 2 i), .affine (.scale 2 j)]
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i, .axis j]] }] }, nonlin := .identity }
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 2 2   -- i↦2, j↦2
  match evalScatter f64Decls env sizes "Out" slots rhs { fill := 0, reduce := .rejectCollisions } [4,4] with
  | .error e => throwError (toString e)
  | .ok (_, Out) =>
      -- X values at even coords:
      unless Out.get! [0,0] == 1.0 && Out.get! [0,2] == 2.0 && Out.get! [2,0] == 3.0 && Out.get! [2,2] == 4.0 do
        throwError s!"upsample even coords wrong: {repr Out.data}"
      -- odd coords are fill (0):
      unless Out.get! [0,1] == 0.0 && Out.get! [1,1] == 0.0 && Out.get! [3,3] == 0.0 do throwError "upsample fill wrong"

-- reduce sum: two source axes mapping onto the SAME output coord should accumulate.
-- Out[0,0] := X[i,j] for all i,j with reduce sum ⇒ sum of all X = 1+2+3+4 = 10.
run_cmd do
  let i := ax "i" 1; let j := ax "j" 2
  let X := tensorOf [2,2] [1,2, 3,4]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let slots : List LHSSlot := [.affine (.const 0), .affine (.const 0)]
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i, .axis j]] }] }, nonlin := .identity }
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 2 2
  match evalScatter f64Decls env sizes "Out" slots rhs { fill := 0, reduce := .sum } [4,4] with
  | .error e => throwError (toString e)
  | .ok (_, Out) =>
      unless Out.get! [0,0] == 10.0 do throwError s!"reduce sum wrong: {repr Out.data}"

-- FAIL-LOUD: an unsized source axis (here `j`, uid 2, missing from `sizes`) must error rather
-- than silently iterating it once (the former `.getD 1`), which would drop source coordinates.
run_cmd do
  let i := ax "i" 1; let j := ax "j" 2
  let X := tensorOf [2,2] [1,2, 3,4]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let slots : List LHSSlot := [.affine (.scale 2 i), .affine (.scale 2 j)]
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i, .axis j]] }] }, nonlin := .identity }
  let sizes := ({} : HashMap UID Nat).insert 1 2          -- i↦2, but j (uid 2) deliberately unsized
  match evalScatter f64Decls env sizes "Out" slots rhs { fill := 0, reduce := .rejectCollisions } [4,4] with
  | .error _ => pure ()                                   -- expected
  | .ok _    => throwError "expected evalScatter to reject an unsized source axis"

-- 4g regression: evalScatter ignores rhs.agg entirely — it hardcodes real sum-of-products for
-- every RHS term regardless of the declared aggregation. A maxreduce-style scatter RHS must use
-- tropical max, not silently compute a real sum instead. A[i]=[1,5,2], B[i]=[10,-1,-1]; per-
-- position max = [10,5,2] (today's real sum would wrongly give [11,4,1]).
run_cmd do
  let i := ax "i" 1
  let A := tensorOf [3] [1, 5, 2]
  let B := tensorOf [3] [10, -1, -1]
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "A" A).insert "B" B
  let slots : List LHSSlot := [.affine (.axis i)]
  let rhs : RHSExpr :=
    { body := { terms := [{ factors := [.read "A" [.axis i]] }, { factors := [.read "B" [.axis i]] }] },
      nonlin := .identity, agg := .max }
  let sizes := ({} : HashMap UID Nat).insert 1 3
  match evalScatter f64Decls env sizes "Out" slots rhs { fill := 0, reduce := .rejectCollisions } [3] with
  | .error e => throwError (toString e)
  | .ok (_, Out) => unless DenseTensor.approxEq Out (tensorOf [3] [10, 5, 2]) do
      throwError s!"4g regression: expected per-position max(A,B) = [10,5,2] (agg = .max), got \
{repr Out.data} (evalScatter ignores rhs.agg and always computes a real sum, which gives [11,4,1])"

-- 4g: two source coords writing the same output coord under the default (.rejectCollisions)
-- policy must error, naming both conflicting source coordinates.
run_cmd do
  let i := ax "i" 1; let j := ax "j" 2
  let X := tensorOf [2,2] [1,2, 3,4]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let slots : List LHSSlot := [.affine (.const 0), .affine (.const 0)]
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i, .axis j]] }] }, nonlin := .identity }
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 2 2
  match evalScatter f64Decls env sizes "Out" slots rhs { fill := 0, reduce := .rejectCollisions } [4,4] with
  | .error e =>
      -- Typed check (4h): the collision must be `EvalError.scatterCollision "Out" [0,0] .. ..`
      -- (both source coords collapse to output coord [0,0] under `.affine (.const 0)` slots).
      -- Source-coordinate fields are left as wildcards — WHICH of the two colliding coords is
      -- "first" vs "second" is an iteration-order detail (`cartesian srcSizes`), not part of
      -- this test's actual assertion. Retained renderer check (byte-identical text) alongside.
      match e with
      | .scatterCollision nm outCoord _ _ =>
          unless nm == "Out" && outCoord == [0,0] do
            throwError s!"4g: wrong collision fields: nm={nm} outCoord={outCoord}"
      | _ => throwError s!"4g: expected a scatterCollision error, got: {e}"
      unless ((toString e).splitOn "collision").length > 1 do throwError s!"4g: wrong error: {e}"
  | .ok _ => throwError "4g: expected rejectCollisions to error on a genuine collision"

-- 4g: .min collision policy folds every write (min), not just the last one — the never-before-
-- reachable case that used to silently fall through to overwrite.
run_cmd do
  let i := ax "i" 1
  let X := tensorOf [3] [5, -8, 2]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let slots : List LHSSlot := [.affine (.const 0)]   -- every source coord collides at output 0
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .identity }
  let sizes := ({} : HashMap UID Nat).insert 1 3
  match evalScatter f64Decls env sizes "Out" slots rhs { fill := 0, reduce := .min } [1] with
  | .error e => throwError (toString e)
  | .ok (_, Out) => unless Out.get! [0] == -8.0 do
      throwError s!"4g: min collision should give -8, got {repr Out.data}"

-- F32 refusal at the ENTRY: the reference evaluator is binary64-only, so `evalScatter` refuses a
-- name committed to binary32 (undeclared included) with `unsupportedDtype`, like every sibling
-- entry (`rejectUnsupportedStorage`), before any gathering / nonlinearity work. Shared program:
-- the upsample of the first fixture (`Out[2*i, 2*j] := X[i,j]`), with `rhs.nonlin` selectable.
private def f32Program (nonlin : Nonlin) (decls : List Decl) :
    Except EvalError (String × DenseTensor) :=
  let i := ax "i" 1; let j := ax "j" 2
  let env : HashMap String DenseTensor :=
    ({} : HashMap String DenseTensor).insert "X" (tensorOf [2,2] [1,2, 3,4])
  let slots : List LHSSlot := [.affine (.scale 2 i), .affine (.scale 2 j)]
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i, .axis j]] }] }, nonlin := nonlin }
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 2 2
  evalScatter decls env sizes "Out" slots rhs { fill := 0, reduce := .rejectCollisions } [4,4]

-- PIN: undeclared names are binary32; the destination is reported first.
run_cmd do
  match f32Program .identity [] with
  | .error (.unsupportedDtype "Out") => pure ()
  | .error e => throwError s!"F32-a: expected unsupportedDtype \"Out\", got: {e}"
  | .ok _ => throwError "F32-a: expected evalScatter [] (undeclared = binary32) to be refused"

-- PIN: an f64 destination does not excuse an f32 read source; the READ name is reported.
run_cmd do
  match f32Program .identity [Decl.typedTensor .f64 "Out" [], Decl.typedTensor .f32 "X" []] with
  | .error (.unsupportedDtype "X") => pure ()
  | .error e => throwError s!"F32-b: expected unsupportedDtype \"X\", got: {e}"
  | .ok _ => throwError "F32-b: expected an f32 read source to be refused"

-- ACCEPT NEIGHBOUR: the same program with every involved name `f64` is evaluated (not refused).
run_cmd do
  match f32Program .identity f64Decls with
  | .error e => throwError s!"F32-c: f64 neighbour must evaluate, got: {e}"
  | .ok (_, Out) =>
      unless Out.get! [0,0] == 1.0 && Out.get! [2,2] == 4.0 && Out.get! [1,1] == 0.0 do
        throwError s!"F32-c: wrong value: {repr Out.data}"

-- ORDER: storage is refused BEFORE the non-identity-nonlin check (as in the siblings: the guard
-- precedes nonlinearity work); with f64 decls the same program reaches `unsupportedScatterNonlin`.
run_cmd do
  match f32Program (.pointwise .relu) [] with
  | .error (.unsupportedDtype "Out") => pure ()
  | .error e => throwError s!"F32-d: f32 + relu must report unsupportedDtype \"Out\" first, got: {e}"
  | .ok _ => throwError "F32-d: expected refusal"
  match f32Program (.pointwise .relu) f64Decls with
  | .error (.unsupportedScatterNonlin "Out") => pure ()
  | .error e => throwError s!"F32-d: f64 + relu must reach unsupportedScatterNonlin, got: {e}"
  | .ok _ => throwError "F32-d: expected nonlin rejection"

end LeanNCD.Eval
