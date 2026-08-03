import LeanNCD.Eval.Scan
namespace LeanNCD.Eval
open Std

/-! # Wave B regression freeze (Stage 0)

Three confirmed defects, corroborated against HEAD by `papers/copilot_code_analysis.md`'s
"Spike 4 assessment". Each `run_cmd` below asserts the CORRECT behavior and is expected to fail
today for the stated reason — Task 3 (4a) turns #1 and #2 green; Task 5 (4c) turns #3 green.
Do not weaken these into "assert current behavior" — that would freeze the bug, not the fix. -/

private def ax (nm : String) (u : Nat) : AxisSpec := { name := nm, uid := u, kind := .real }
private def tensorOf (shape : List Nat) (xs : List Float) : DenseTensor := ⟨shape, xs.toArray⟩

-- #1 (evalAssignSeeded): an unseeded free output axis absent from `sizes` must be REJECTED, not
-- silently produce an empty shape-[0] tensor. i (free, uid 1) genuinely reads X and would be
-- correctly sized by `inferAxisSizes` in the normal compiled path; here we call the seeded
-- worker directly with an incomplete `sizes` map — exactly what a solver gap or a malformed
-- direct call currently produces undetected.
run_cmd do
  let i := ax "i" 1; let k := ax "k" 2
  let X := tensorOf [3] [10, 20, 30]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes : HashMap UID Nat := ({} : HashMap UID Nat).insert 2 2   -- k (seeded) sized; i (free) deliberately absent
  let seed : HashMap UID Int := ({} : HashMap UID Int).insert 2 0
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .identity }
  let mul : Float → Float → Float := (· * ·)
  let combine : Float → Float → Float := (· + ·)
  match evalAssignSeeded mul combine 0.0 1.0 env sizes seed "Y" [LHSSlot.free i, LHSSlot.iterAt k 0] rhs with
  | Except.error (.shape (.unsizedAxis 1 (.assignOutput "Y"))) => pure ()
  | Except.error e => throwError s!"Wave-B #1: wrong rejection reason, got: {e}"
  | Except.ok (_, Y) => throwError
      s!"Wave-B #1: expected rejection of missing free-axis size, got shape {Y.shape} \
(evalAssignSeeded has no free-axis size check today, unlike evalAssignWith)"

-- #2 (evalAssign / evalAssignWith): a contracted axis absent from `sizes` must be REJECTED, not
-- silently contracted at extent one. `sum k, X[k]` with X = [1,2,3]: today this returns `1.0`
-- (the k=0 term only) instead of erroring on the malformed context (the correct sum, 6.0, is
-- NOT what this test asserts — the point is the evaluator must not guess a missing size).
run_cmd do
  let k := ax "k" 2
  let X := tensorOf [3] [1, 2, 3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes : HashMap UID Nat := {}   -- k deliberately absent
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis k]] }] }, nonlin := .identity }
  match evalAssign env sizes "Y" [] rhs with
  | .error (.shape (.unsizedAxis 2 (.assignContracted "Y"))) => pure ()
  | .error e => throwError s!"Wave-B #2: wrong rejection reason, got: {e}"
  | .ok (_, Y) => throwError
      s!"Wave-B #2: expected rejection of missing contracted-axis size, got {repr Y.data} \
(evalAssignWith/evalAssignSeeded default a missing contracted axis to extent 1 today)"

-- #3 (evalAssignDtyped vs evalStmtSliceSeeded): a predicate contraction with two satisfying
-- assignments must agree between the plain path (Boolean OR-AND, via evalAssignDtyped) and the
-- one-step-scan path (currently always real sum-product — evalStmtSliceSeeded has no `decls`
-- parameter today and so cannot see that "Result" is declared `.predicate`).
run_cmd do
  let t := ax "t" 1; let i := ax "i" 2; let j := ax "j" 3
  let F := tensorOf [1, 2] [1, 1]
  let edge := tensorOf [2, 2] [1, 0, 0, 1]
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "F" F).insert "edge" edge
  let sizes : HashMap UID Nat :=
    ((({} : HashMap UID Nat).insert 1 1).insert 2 2).insert 3 2
  let rhs : RHSExpr :=
    { body := { terms := [{ factors :=
        [.read "F" [.axis t, .axis i], .read "F" [.axis t, .axis j], .read "edge" [.axis i, .axis j]] }] },
      nonlin := .identity }
  match evalAssignDtyped [.predicate "Result" []] env sizes "Result" [] rhs with
  | .error e => throwError s!"Wave-B #3: plain (predicate) path errored: {e}"
  | .ok (_, plainR) =>
      match evalStmtSliceSeeded [.predicate "Result" []] env sizes {} (.assign "Result" [] rhs) with
      | .error e => throwError s!"Wave-B #3: scan-slice path errored: {e}"
      | .ok (_, scanR) =>
          unless DenseTensor.approxEq plainR scanR do
            throwError s!"Wave-B #3: plain path gave {repr plainR.data}, scan-slice path gave \
{repr scanR.data} — predicate dtype is lost on the scan path (always real sum-product there)"

end LeanNCD.Eval
