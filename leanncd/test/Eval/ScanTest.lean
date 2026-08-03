import LeanNCD.Eval.Scan
namespace LeanNCD.Eval
open Std
private def ax (nm : String) (u : Nat) : AxisSpec := { name := nm, uid := u, kind := .real }
private def tensorOf (shape : List Nat) (xs : List Float) : DenseTensor := ⟨shape, xs.toArray⟩

-- LINEAR scan, single state: S[j,0] := X[j]; S[j,l+1] := S[j,l] · A[j]   (elementwise, no contraction)
--   X = [1, 10] (j=0,1), A = [2, 3], L = 3  ⇒  S[:,0]=[1,10], S[:,1]=[2,30], S[:,2]=[4,90].
run_cmd do
  let j := ax "j" 1; let l := ax "l" 9
  let X := tensorOf [2] [1, 10]; let A := tensorOf [2] [2, 3]
  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "X" X).insert "A" A
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 9 3   -- j↦2, l↦3
  let base : Stmt := .assign "S" [.free j, .iterAt l 0] { body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .identity }
  let recur : Stmt := .assign "S" [.free j, .iterNext l] { body := { terms := [{ factors := [.read "S" [.axis j, .axis l], .read "A" [.axis j]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [base] [recur] false) with
  | .error e => throwError (toString e)
  | .ok outs =>
      match outs.find? (·.1 == "S") with
      | some (_, S) =>
          unless DenseTensor.approxEq S (tensorOf [2,3] [1,2,4, 10,30,90]) do throwError s!"linear scan wrong: {repr S.data}"
      | none => throwError "no S"

-- relu scan, single state: S[j,0]:=X[j]; S[j,l+1] := relu(S[j,l]·A[j])  with A negative ⇒ clamped to 0
--   X=[1], A=[-1], L=2 ⇒ S[:,0]=[1], S[:,1]=relu(1·-1)=relu(-1)=0.
run_cmd do
  let j := ax "j" 1; let l := ax "l" 9
  let X := tensorOf [1] [1]; let A := tensorOf [1] [-1]
  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "X" X).insert "A" A
  let sizes := (({} : HashMap UID Nat).insert 1 1).insert 9 2
  let base : Stmt := .assign "S" [.free j, .iterAt l 0] { body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .identity }
  let recur : Stmt := .assign "S" [.free j, .iterNext l] { body := { terms := [{ factors := [.read "S" [.axis j, .axis l], .read "A" [.axis j]] }] }, nonlin := .pointwise .relu }
  match evalScan [] env sizes (.scan "S" [l] [base] [recur] false) with
  | .error e => throwError (toString e)
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) => unless DenseTensor.approxEq S (tensorOf [1,2] [1, 0]) do throwError s!"relu scan wrong: {repr S.data}"
    | none => throwError "no S"

-- COUPLED scan: two states G,H sharing l, each recur reading both.
--   G[0]:=1; H[0]:=1; G[l+1]:=G[l]+H[l]; H[l+1]:=G[l]  (Fibonacci-ish), L=4 (scalar, single axis l)
--   G: 1, 1+1=2, 2+1=3, 3+2=5  => [1,2,3,5]
--   H: 1, 1,     2,     3       => [1,1,2,3]
run_cmd do
  let l := ax "l" 9
  let one := tensorOf [] [1]
  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "C" one)
  let sizes := (({} : HashMap UID Nat).insert 9 4)
  let baseG : Stmt := .assign "G" [.iterAt l 0] { body := { terms := [{ factors := [.read "C" []] }] }, nonlin := .identity }
  let baseH : Stmt := .assign "H" [.iterAt l 0] { body := { terms := [{ factors := [.read "C" []] }] }, nonlin := .identity }
  let recurG : Stmt := .assign "G" [.iterNext l] { body := { terms := [{ factors := [.read "G" [.axis l]] }, { factors := [.read "H" [.axis l]] }] }, nonlin := .identity }
  let recurH : Stmt := .assign "H" [.iterNext l] { body := { terms := [{ factors := [.read "G" [.axis l]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "G" [l] [baseG, baseH] [recurG, recurH] false) with
  | .error e => throwError (toString e)
  | .ok outs =>
      match outs.find? (·.1 == "G"), outs.find? (·.1 == "H") with
      | some (_, G), some (_, H) =>
          unless DenseTensor.approxEq G (tensorOf [4] [1,2,3,5]) do throwError s!"coupled G wrong: {repr G.data}"
          unless DenseTensor.approxEq H (tensorOf [4] [1,1,2,3]) do throwError s!"coupled H wrong: {repr H.data}"
      | _, _ => throwError "missing G or H"

-- plain errors (handled by evalScheduled, not evalScan)
run_cmd do
  match evalScan [] {} {} (.plain (.assign "x" [] { body := { terms := [] }, nonlin := .identity })) with
  | .error _ => pure ()
  | .ok _ => throwError "expected plain to error"

-- 4c: a predicate contraction inside a one-step "scan" (empty seed) must agree with the plain
-- path — both now route through combineFor via evalAssignDtypedSeeded.
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
  let decls := [Decl.predicate "Result" []]
  match evalAssignDtyped decls env sizes "Result" [] rhs,
        evalStmtSliceSeeded decls env sizes {} (.assign "Result" [] rhs) with
  | .ok (_, plainR), .ok (_, scanR) =>
      unless DenseTensor.approxEq plainR scanR do
        throwError s!"4c: plain {repr plainR.data} ≠ scan-slice {repr scanR.data}"
  | .error e, _ => throwError s!"4c: plain path errored: {e}"
  | _, .error e => throwError s!"4c: scan-slice path errored: {e}"

-- 4c mutation check: if the scan path ever regresses to always using Combine.real (i.e. loses
-- decls), the test above must fail. Confirm directly: Combine.real on this same rhs gives 2.0
-- (real sum-product over 2 satisfying assignments), not the correct Boolean-OR-AND 1.0.
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
  match evalAssignSeeded Combine.real.mul Combine.real.combine Combine.real.unit0
      Combine.real.unit1 env sizes {} "Result" [] rhs with
  | .error e => throwError s!"4c mutation check: unexpected error {e}"
  | .ok (_, R) => unless DenseTensor.approxEq R (tensorOf [] [2.0]) do
      throwError s!"4c mutation check: Combine.real should give 2.0 on this rhs, got {repr R.data} \
(if this fails, the test above may be passing for the wrong reason)"

-- scan/scatter boundary check (found while writing the 4g plan, not a 4g bug): a scatter-shaped
-- LHS combined with an iteration slot (e.g. `Out[2*i, l+1] := X[i,l]`) compiles successfully today
-- — lowerArith reclassifies the whole slot list to Stmt.scatter regardless of the iteration slot
-- riding on another dimension, and finalizeScans groups it into a scan's base/recur list with
-- nothing rejecting the combination at compile time. evalStmtSliceSeeded is what actually rejects
-- it, at eval time. This test locks in that rejection so evalScatter/CollisionReduce changes in
-- this plan (Tasks 2-3) can't silently make evalScatter reachable from inside a scan.
run_cmd do
  let i := ax "i" 1; let l := ax "l" 9
  let X := tensorOf [2] [1, 2]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 9 3
  let slots : List LHSSlot := [.affine (.scale 2 i), .iterNext l]
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .identity }
  match evalStmtSliceSeeded [] env sizes {} (.scatter "Out" slots rhs { fill := 0, reduce := .rejectCollisions }) with
  | .error (.invalidScanNode .onlyAssignInSlice) => pure ()
  | .error e => throwError s!"scan/scatter boundary: wrong error message: {e}"
  | .ok _ => throwError "scan/scatter boundary: expected evalStmtSliceSeeded to reject a scatter stmt"

end LeanNCD.Eval
