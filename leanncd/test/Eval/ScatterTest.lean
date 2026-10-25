import LeanNCD.Eval.Scatter
import Eval.Portfolio.Harness
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
  match evalScatter f64Decls env sizes "Out" slots rhs [4,4] with
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
  match evalScatter f64Decls env sizes "Out" slots rhs [4,4] with
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
  match evalScatter f64Decls env sizes "Out" slots rhs [4,4] with
  | .error _ => pure ()                                   -- expected
  | .ok _    => throwError "expected evalScatter to reject an unsized source axis"

-- 4g regression: evalScatter once ignored rhs.agg entirely — it hardcoded real sum-of-products for
-- every RHS term regardless of the declared aggregation. A maxreduce-style scatter RHS must use
-- tropical max, not silently compute a real sum instead. A[i]=[1,5,2], B[i]=[10,-1,-1]; per-
-- position max = [10,5,2] (the real sum would wrongly give [11,4,1]). S3b: the destination now
-- starts from 0_K = -inf instead of 0 and folds with the same max; every cell is written, so the
-- expected value is unchanged (the min-plus twin on negated data follows).
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
  match evalScatter f64Decls env sizes "Out" slots rhs [3] with
  | .error e => throwError (toString e)
  | .ok (_, Out) => unless DenseTensor.approxEq Out (tensorOf [3] [10, 5, 2]) do
      throwError s!"4g regression: expected per-position max(A,B) = [10,5,2] (agg = .max), got \
{repr Out.data} (evalScatter ignores rhs.agg and always computes a real sum, which gives [11,4,1])"

-- S3a (⊕): two source coords writing the same output coord are MERGED with the destination's
-- additive monoid (real: `+`), not an error. Out[0,0] := X[i,j] under default opts, X = [[1,2],[3,4]]
-- ⇒ Out[0,0] = 1+2+3+4 = 10; the other cells stay 0_K = 0.
run_cmd do
  let i := ax "i" 1; let j := ax "j" 2
  let X := tensorOf [2,2] [1,2, 3,4]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let slots : List LHSSlot := [.affine (.const 0), .affine (.const 0)]
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i, .axis j]] }] }, nonlin := .identity }
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 2 2
  match evalScatter f64Decls env sizes "Out" slots rhs [4,4] with
  | .error e => throwError s!"S3a: a collision must sum under the default opts, got: {e}"
  | .ok (_, Out) =>
      unless Out.get! [0,0] == 10.0 && Out.get! [0,1] == 0.0 && Out.get! [3,3] == 0.0 do
        throwError s!"S3a: collision sum wrong: {repr Out.data}"

-- 4g regression, min-plus twin: negated data A = [-1,-5,-2], B = [-10,1,1]; per-position min =
-- [-10,-5,-2] (the destination starts from +inf; a start of 0 would wrongly cap the cells at 0).
run_cmd do
  let i := ax "i" 1
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "A" (tensorOf [3] [-1, -5, -2])).insert "B"
      (tensorOf [3] [-10, 1, 1])
  let rhs : RHSExpr :=
    { body := { terms := [{ factors := [.read "A" [.axis i]] }, { factors := [.read "B" [.axis i]] }] },
      nonlin := .identity, agg := .min }
  let sizes := ({} : HashMap UID Nat).insert 1 3
  match evalScatter f64Decls env sizes "Out" [.affine (.axis i)] rhs [3] with
  | .error e => throwError (toString e)
  | .ok (_, Out) => unless Out.data == #[-10, -5, -2] do
      throwError s!"4g regression min twin: expected [-10,-5,-2], got {repr Out.data}"

-- S3b: top-level tropical scatter. `Out[2*i] := agg(X[i,j])`, source axes i (uid 1, extent 3) and
-- j (uid 2, extent 2); `j` is absent from the LHS, so the two `j` writes of one `i` COLLIDE on the
-- cell `2*i`, and the odd cells are the EMPTY fibre. Donor: the S3a sum-collision fixture above.
-- A max-plus scatter starts at -inf and folds with max; min-plus starts at +inf and folds with min.
private def ninf : Float := -1.0 / 0.0
private def pinf : Float := 1.0 / 0.0

private def s3bRhs (agg : AggOp) (twoFactor : Bool) : RHSExpr :=
  let i := ax "i" 1; let j := ax "j" 2
  { body := { terms := [{ factors :=
      if twoFactor then [.read "X" [.axis i, .axis j], .read "Y" [.axis j]]
      else [.read "X" [.axis i, .axis j]] }] }
    nonlin := .identity, agg := agg }

private def s3bRun (agg : AggOp) (twoFactor : Bool) (X Y : List Float) :
    Except EvalError (String × DenseTensor) :=
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "X" (tensorOf [3, 2] X)).insert "Y" (tensorOf [2] Y)
  let sizes := (({} : HashMap UID Nat).insert 1 3).insert 2 2
  evalScatter (f64Decls ++ [Decl.typedTensor .f64 "Y" []]) env sizes "Out"
    [.affine (.scale 2 (ax "i" 1))] (s3bRhs agg twoFactor) [6]

-- (a) collision = max, not the sum [6,.,10,.,6,.] and not an overwrite; unwritten = -inf.
run_cmd do
  match s3bRun .max false [5, 1, 3, 7, 2, 4] [0, 0] with
  | .error e => throwError s!"S3b max collision: {e}"
  | .ok (_, Out) => unless Out.shape == [6] && Out.data == #[5, ninf, 7, ninf, 4, ninf] do
      throwError s!"S3b max collision: {repr Out.shape} {repr Out.data}"
-- min-plus twin from negated data.
run_cmd do
  match s3bRun .min false [-5, -1, -3, -7, -2, -4] [0, 0] with
  | .error e => throwError s!"S3b min collision: {e}"
  | .ok (_, Out) => unless Out.shape == [6] && Out.data == #[-5, pinf, -7, pinf, -4, pinf] do
      throwError s!"S3b min collision: {repr Out.shape} {repr Out.data}"

-- (b) F4: the CONTRACTED source axis `j` with an empty fibre, direct `evalScatter` against the raw
-- checked plan, is `ScatterDenseTest` fixture 7 (same data): both give the same cells.

-- (e) NaN in a colliding write propagates (f64 only): row 0 = [5, nan] (NaN second), row 2 =
-- [nan, 4] (NaN first); the NaN-free row keeps its max and the empty fibre stays -inf.
run_cmd do
  let nan : Float := 0.0 / 0.0
  match s3bRun .max false [5, nan, 3, 7, nan, 4] [0, 0] with
  | .error e => throwError s!"S3b NaN: {e}"
  | .ok (_, Out) =>
      unless Out.data[0]!.isNaN && Out.data[4]!.isNaN && Out.data[2]! == 7 && Out.data[1]! == ninf do
        throwError s!"S3b NaN must propagate through the collision fold: {repr Out.data}"

-- (f) multi-factor source `maxreduce(X[i,j] * Y[j])`: the tropical ⊗ is `+`, so each write is
-- X[i,j] + Y[j] (a real product would give 50/100/...): row 0 = max(5+10, 1+100) = 101, row 1 =
-- max(3+10, 7+100) = 107, row 2 = max(2+10, 4+100) = 104.
run_cmd do
  match s3bRun .max true [5, 1, 3, 7, 2, 4] [10, 100] with
  | .error e => throwError s!"S3b multi-factor max: {e}"
  | .ok (_, Out) => unless Out.data == #[101, ninf, 107, ninf, 104, ninf] do
      throwError s!"S3b multi-factor max: {repr Out.data}"
-- twin: negated data, min-plus: row 0 = min(-5-10, -1-100) = -101, row 1 = -107, row 2 = -104.
run_cmd do
  match s3bRun .min true [-5, -1, -3, -7, -2, -4] [-10, -100] with
  | .error e => throwError s!"S3b multi-factor min: {e}"
  | .ok (_, Out) => unless Out.data == #[-101, pinf, -107, pinf, -104, pinf] do
      throwError s!"S3b multi-factor min: {repr Out.data}"

-- (d) real and predicate neighbours are unchanged: the real sum collision above (S3a) still sums
-- (10), and the predicate collision below still folds with the Boolean OR (1).

-- S3a (bool ⊕ = ∨): into a `predicate` destination colliding writes fold with `max`, staying in
-- {0,1}. X = [1,1,0] all colliding ⇒ 1 (a real `+` would give 2).
run_cmd do
  let i := ax "i" 1
  let X := tensorOf [3] [1, 1, 0]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let slots : List LHSSlot := [.affine (.const 0)]
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .identity }
  let sizes := ({} : HashMap UID Nat).insert 1 3
  let decls : List Decl := [Decl.predicate "Out" [], Decl.typedTensor .f64 "X" []]
  match evalScatter decls env sizes "Out" slots rhs [1] with
  | .error e => throwError (toString e)
  | .ok (_, Out) => unless Out.get! [0] == 1.0 do
      throwError s!"S3a: bool collision must fold with ∨ (1), got {repr Out.data}"

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
  evalScatter decls env sizes "Out" slots rhs [4,4]

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

-- B6: an out-of-range scatter write is an ERROR (it was a silent skip, a vestige of overwrite
-- semantics). Shared fixture: `Out[<slot>] := X[i]` with X = [10,20,30] (i ↦ 3), run through
-- `evalPlain` so the destination extent is the DERIVED one (`scatterOutShape` → `outExtent`).
-- `n` is X's length (X is sized to match, so `n = 0` is the empty source box).
private def b6Run (slot : LHSSlot) (n : Nat) : Except EvalError (String × DenseTensor) :=
  let i := ax "i" 1
  let X := tensorOf [n] ([10, 20, 30].take n)
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .identity }
  evalPlain f64Decls env (({} : HashMap UID Nat).insert 1 n) (.scatter "Out" [slot] rhs)

-- B6-a (hand AST, negative bias): `Out[i-1]`. The derived extent is `3 - 1 = 2`; source i = 0
-- writes coordinate -1.
run_cmd do
  match b6Run (.affine (.shift (ax "i" 1) (-1))) 3 with
  | .error (.scatterWriteOutOfRange "Out" [-1] [0]) => pure ()
  | .error e => throwError s!"B6-a: expected scatterWriteOutOfRange \"Out\" [-1] [0], got: {e}"
  | .ok (_, o) => throwError s!"B6-a: expected rejection, got {repr o.shape} {repr o.data}"

-- B6-b (zero coefficient, surface-reachable): `Out[0*i+5]`. `outExtent` derives 5 (`5 + 0·3`), so
-- the write at coordinate 5 is one past the end.
run_cmd do
  match b6Run (.affine (.affine 5 [(0, ax "i" 1)])) 3 with
  | .error (.scatterWriteOutOfRange "Out" [5] [0]) => pure ()
  | .error e => throwError s!"B6-b: expected scatterWriteOutOfRange \"Out\" [5] [0], got: {e}"
  | .ok (_, o) => throwError s!"B6-b: expected rejection, got {repr o.shape} {repr o.data}"

-- B6-c (zero coefficient, no bias, surface-reachable): `Out[0*i]`. The derived extent is 0, so
-- the write at coordinate 0 lands in a zero-extent destination.
run_cmd do
  match b6Run (.affine (.scale 0 (ax "i" 1))) 3 with
  | .error (.scatterWriteOutOfRange "Out" [0] [0]) => pure ()
  | .error e => throwError s!"B6-c: expected scatterWriteOutOfRange \"Out\" [0] [0], got: {e}"
  | .ok (_, o) => throwError s!"B6-c: expected rejection, got {repr o.shape} {repr o.data}"

-- B6-d (hand AST, negative coefficient): `Out[-i]`. The derived extent clamps to 0, so even i = 0
-- (coordinate 0) is out of range.
run_cmd do
  match b6Run (.affine (.scale (-1) (ax "i" 1))) 3 with
  | .error (.scatterWriteOutOfRange "Out" [0] [0]) => pure ()
  | .error e => throwError s!"B6-d: expected scatterWriteOutOfRange \"Out\" [0] [0], got: {e}"
  | .ok (_, o) => throwError s!"B6-d: expected rejection, got {repr o.shape} {repr o.data}"

-- B6-e (explicit smaller destination, direct entry): `Out[i]` into a 2-cell `outShape`. The
-- offending write is the first one past the end, source i = 2 → coordinate 2.
run_cmd do
  let i := ax "i" 1
  let env : HashMap String DenseTensor :=
    ({} : HashMap String DenseTensor).insert "X" (tensorOf [3] [10, 20, 30])
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .identity }
  match evalScatter f64Decls env (({} : HashMap UID Nat).insert 1 3) "Out" [.affine (.axis i)] rhs [2] with
  | .error (.scatterWriteOutOfRange "Out" [2] [2]) => pure ()
  | .error e => throwError s!"B6-e: expected scatterWriteOutOfRange \"Out\" [2] [2], got: {e}"
  | .ok _ => throwError "B6-e: expected rejection"

-- B6 ACCEPT NEIGHBOURS: the nearest legal programs still succeed with unchanged values.
-- Injective stride `Out[2*i]`: derived extent 6, X at the even cells.
run_cmd do
  match b6Run (.affine (.scale 2 (ax "i" 1))) 3 with
  | .error e => throwError s!"B6-f: Out[2*i] must evaluate, got: {e}"
  | .ok (_, o) => unless o.shape == [6] && o.data == #[10, 0, 20, 0, 30, 0] do
      throwError s!"B6-f: wrong value: {repr o.shape} {repr o.data}"

-- Offset `Out[i+1]`: derived extent 4, cell 0 stays 0_K.
run_cmd do
  match b6Run (.affine (.shift (ax "i" 1) 1)) 3 with
  | .error e => throwError s!"B6-g: Out[i+1] must evaluate, got: {e}"
  | .ok (_, o) => unless o.shape == [4] && o.data == #[0, 10, 20, 30] do
      throwError s!"B6-g: wrong value: {repr o.shape} {repr o.data}"

-- Const slot `Out[2]`: extent `2 + 1 = 3`; the three writes collide at cell 2 and sum (S3a).
run_cmd do
  match b6Run (.affine (.const 2)) 3 with
  | .error e => throwError s!"B6-h: Out[2] must evaluate, got: {e}"
  | .ok (_, o) => unless o.shape == [3] && o.data == #[0, 0, 60] do
      throwError s!"B6-h: wrong value: {repr o.shape} {repr o.data}"

-- Empty source box (i ↦ 0) writes nothing, so even the zero-extent `Out[0*i]` of B6-c is fine.
run_cmd do
  match b6Run (.affine (.scale 0 (ax "i" 1))) 0 with
  | .error e => throwError s!"B6-i: an empty source box writes nothing, got: {e}"
  | .ok (_, o) => unless o.shape == [0] && o.data == #[] do
      throwError s!"B6-i: wrong value: {repr o.shape} {repr o.data}"

-- B6 through the SURFACE syntax (`elabTLLHSSlot` accepts `n*x+m` and `n*x`, including n = 0).
run_cmd (assertEvalError "B6-surface-a" (tlprog!{ Out[0 * i + 5] := X[i] })
  (HashMap.ofList [("X", tl [3] [10, 20, 30])]) "outside the destination extent")
run_cmd (assertEvalError "B6-surface-b" (tlprog!{ Out[0 * i] := X[i] })
  (HashMap.ofList [("X", tl [3] [10, 20, 30])]) "outside the destination extent")
run_cmd (assertEval "B6-surface-accept" (tlprog!{ tensor f64 Out(i)
                                                  Out[2 * i] := X[i] })
  (HashMap.ofList [("X", tl [3] [10, 20, 30])]) "Out" (tl [6] [10, 0, 20, 0, 30, 0]))

-- S3b-ii T3a (D1, reference side): a scatter into a `predicate` destination reads a real source
-- with the `real -> bool` coerce (stored != 0; NaN reads true, the existing convention, pinned not
-- endorsed). Out[2*i] := X[i], X = [0.25, 0.75, 0, NaN, -2] ⇒ [1,0, 1,0, 0,0, 1,0, 1,0]
-- (uncoerced the written cells would carry the raw 0.25, 0.75, NaN, -2).
run_cmd do
  let i := ax "i" 1
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X"
    (tensorOf [5] [0.25, 0.75, 0, 0.0 / 0.0, -2])
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .identity }
  let sizes := ({} : HashMap UID Nat).insert 1 5
  let decls : List Decl := [Decl.predicate "Out" [], Decl.typedTensor .f64 "X" []]
  match evalScatter decls env sizes "Out" [.affine (.scale 2 i)] rhs [10] with
  | .error e => throwError s!"D1 scatter: {e}"
  | .ok (_, Out) => unless Out.data == #[1, 0, 1, 0, 0, 0, 1, 0, 1, 0] do
      throwError s!"D1 scatter must coerce a real read: {repr Out.data}"
  -- the same scatter with a predicate SOURCE reads it as stored (bool -> bool unchanged)
  match evalScatter [Decl.predicate "Out" [], Decl.predicate "X" []] env sizes "Out"
      [.affine (.scale 2 i)] rhs [10] with
  | .error e => throwError s!"D1 scatter bool source: {e}"
  | .ok (_, Out) => unless Out.data[0]! == 0.25 && Out.data[2]! == 0.75 do
      throwError s!"D1 scatter bool source must stay uncoerced: {repr Out.data}"


end LeanNCD.Eval
