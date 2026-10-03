import LeanNCD.Eval.Scan
import LeanNCD.Eval.Eval   -- `evalPlain`, exercised directly by the f32 entry-guard fixtures below
namespace LeanNCD.Eval
open Std
private def ax (nm : String) (u : Nat) : AxisSpec := { name := nm, uid := u, kind := .real }
private def tensorOf (shape : List Nat) (xs : List Float) : DenseTensor := ⟨shape, xs.toArray⟩

-- helpers of the reference-alignment structural-rejection fixtures at the end of this file
private def raRhs (nm : String) (idx : List IdxExpr) : RHSExpr :=
  { body := { terms := [{ factors := [.read nm idx] }] }, nonlin := .identity }

private def raAccepted (outs : List (String × DenseTensor)) : String :=
  s!"expected a rejection, but the scan was accepted: {outs.map (fun (n, t) => (n, t.shape, t.data))}"

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

-- A scatter-shaped per-step scratch is outside S-B: only persistent state writes may place an
-- affine dense source slice. Reject it before evaluating the scratch RHS, even when the extent-one
-- scan has no dynamic recurrence iterations.
run_cmd do
  let i := ax "i" 1; let l := ax "l" 9
  let Z := tensorOf [] [0]; let X := tensorOf [2] [1, 2]
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "Z" Z).insert "X" X
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 9 1
  let base : Stmt := .assign "S" [.iterAt l 0]
    { body := { terms := [{ factors := [.read "Z" []] }] }, nonlin := .identity }
  let scratch : Stmt := .scatter "Tmp" [.affine (.scale 2 i)]
    { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis l]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [base] [scratch, recur] false) with
  | .error (.invalidScanNode .onlyAssignInSlice) => pure ()
  | .error e => throwError s!"scan-scatter scratch: wrong error: {e}"
  | .ok _ => throwError "scan-scatter scratch: expected rejection"

-- (a) External read at the CURRENT coordinate: S[l+1] := S[l] + X[l], X plain, indexed by the
-- loop axis itself (distinct from RC4's rejected look-AHEAD X[l+1] case). Verified: S=[1,11,31].
run_cmd do
  let l := ax "l" 9
  let S0 := tensorOf [] [1]; let X := tensorOf [3] [10, 20, 30]
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "S0" S0).insert "X" X
  let sizes := (({} : HashMap UID Nat).insert 9 3)
  let base : Stmt := .assign "S" [.iterAt l 0] { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }
  let recur : Stmt := .assign "S" [.iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis l]] }, { factors := [.read "X" [.axis l]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [base] [recur] false) with
  | .error e => throwError (toString e)
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) => unless DenseTensor.approxEq S (tensorOf [3] [1,11,31]) do throwError s!"external-read wrong: {repr S.data}"
    | none => throwError "no S"

-- (b) Deep history look-back (k=2): G[l+1] := G[l-2], base G[0]=5, axis size 5. q=0/1 read
-- out-of-range (zero pad); q=2 reads G[0]=5; q=3 reads G[1]=0 (the padded value from q=0).
-- Verified: G=[5,0,0,5,0].
run_cmd do
  let l := ax "l" 9
  let G0 := tensorOf [] [5]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "G0" G0
  let sizes := (({} : HashMap UID Nat).insert 9 5)
  let base : Stmt := .assign "G" [.iterAt l 0] { body := { terms := [{ factors := [.read "G0" []] }] }, nonlin := .identity }
  let recur : Stmt := .assign "G" [.iterNext l]
    { body := { terms := [{ factors := [.read "G" [.shift l (-2)]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "G" [l] [base] [recur] false) with
  | .error e => throwError (toString e)
  | .ok outs => match outs.find? (·.1 == "G") with
    | some (_, G) => unless DenseTensor.approxEq G (tensorOf [5] [5,0,0,5,0]) do throwError s!"deep-history wrong: {repr G.data}"
    | none => throwError "no G"

-- (c) Extent one (base-only): axis size 1, recurrence domain empty (`stepExtents = [0]`); the
-- state must equal exactly its base value. Verified: S=[7].
run_cmd do
  let l := ax "l" 9
  let S0 := tensorOf [] [7]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "S0" S0
  let sizes := (({} : HashMap UID Nat).insert 9 1)
  let base : Stmt := .assign "S" [.iterAt l 0] { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }
  let recur : Stmt := .assign "S" [.iterNext l] { body := { terms := [{ factors := [.read "S" [.axis l]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [base] [recur] false) with
  | .error e => throwError (toString e)
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) => unless DenseTensor.approxEq S (tensorOf [1] [7]) do throwError s!"extent-one wrong: {repr S.data}"
    | none => throwError "no S"

-- (d) Extent zero: axis size 0. `evalScan`'s own comment flags this as an "untested adjacent
-- case" -- observed (not assumed): a graceful `Except.error` from the base write's coordinate-
-- range check ("seed coordinate 0 for axis ... is out of range [0, 0)"), not a panic. Pins
-- CURRENT behavior; Wave F's typed rejection (§5.3) replaces this ad hoc bounds error with a
-- named `ScanPlanError` constructor -- it does not fix a crash, because there is none.
run_cmd do
  let l := ax "l" 9
  let S0 := tensorOf [] [7]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "S0" S0
  let sizes := (({} : HashMap UID Nat).insert 9 0)
  let base : Stmt := .assign "S" [.iterAt l 0] { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }
  let recur : Stmt := .assign "S" [.iterNext l] { body := { terms := [{ factors := [.read "S" [.axis l]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [base] [recur] false) with
  | .error _ => pure ()
  | .ok _ => throwError "extent-zero: expected an error (out-of-range base coordinate), got ok"

-- Zero pin: S[j, iterAt l 0] := W[j, l]. The base RHS reads W indexed by the SAME axis it pins to
-- a literal -- confirms the pin substitutes into the read, not just the write coordinate. The
-- recur is an identity copy (S[j,l+1] := S[j,l]), so the base value propagates across the whole
-- history -- this is why the verified result has constant columns per row, not a coincidence.
-- Verified: S[0,:] = [10,10,10] (= W[0,0] repeated), S[1,:] = [20,20,20] (= W[1,0] repeated).
run_cmd do
  let j := ax "j" 1; let l := ax "l" 9
  let W := tensorOf [2, 3] [10, 11, 12, 20, 21, 22]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "W" W
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 9 3
  let base : Stmt := .assign "S" [.free j, .iterAt l 0]
    { body := { terms := [{ factors := [.read "W" [.axis j, .axis l]] }] }, nonlin := .identity }
  let recur : Stmt := .assign "S" [.free j, .iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis j, .axis l]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [base] [recur] false) with
  | .error e => throwError (toString e)
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) => unless DenseTensor.approxEq S (tensorOf [2,3] [10,10,10, 20,20,20]) do
        throwError s!"zero-pin wrong: {repr S.data}"
    | none => throwError "no S"

-- Nonzero pin, tested directly via `evalStmtSliceSeeded` (the exact primitive a compiler-inserted
-- point-override write, e.g. `dp[1,0]`, would drive): seed l=2 into a base-shaped statement that
-- reads W indexed by that same axis. Verified: slice = [W[0,2], W[1,2]] = [12, 22].
run_cmd do
  let j := ax "j" 1; let l := ax "l" 9
  let W := tensorOf [2, 3] [10, 11, 12, 20, 21, 22]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "W" W
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 9 3
  let base : Stmt := .assign "S" [.free j, .iterAt l 2]
    { body := { terms := [{ factors := [.read "W" [.axis j, .axis l]] }] }, nonlin := .identity }
  match evalStmtSliceSeeded [] env sizes (({} : HashMap UID Int).insert 9 2) base with
  | .error e => throwError (toString e)
  | .ok (_, slice) => unless DenseTensor.approxEq slice (tensorOf [2] [12, 22]) do
      throwError s!"nonzero-pin wrong: {repr slice.data}"

-- === Wave F F0 Task 3: Jacobi/Gauss-Seidel snapshot-safety discriminator ===
-- A[l+1] := A[l] + ONE (ordinary predecessor read); B[l+1] := A[.const 1] (a FIXED literal read
-- of A's position 1, ignoring the loop axis entirely). readsIterAhead only matches `.shift a n,
-- n > 0`, so this constant read is not flagged as look-ahead by the source pipeline's causality
-- check. recur order [recurA, recurB]: at q=0 (writing position 1 for both), recurA runs first
-- and writes stepEnv["A"][1]=1 BEFORE recurB reads it -- so B[1] observes the just-written value,
-- not the pre-step zero. Verified: A=[0,1,2], B=[0,1,1].
run_cmd do
  let l := ax "l" 9
  let zero := tensorOf [] [0]; let one := tensorOf [] [1]
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "Z" zero).insert "ONE" one
  let sizes := (({} : HashMap UID Nat).insert 9 3)
  let baseA : Stmt := .assign "A" [.iterAt l 0] { body := { terms := [{ factors := [.read "Z" []] }] }, nonlin := .identity }
  let baseB : Stmt := .assign "B" [.iterAt l 0] { body := { terms := [{ factors := [.read "Z" []] }] }, nonlin := .identity }
  let recurA : Stmt := .assign "A" [.iterNext l]
    { body := { terms := [{ factors := [.read "A" [.axis l]] }, { factors := [.read "ONE" []] }] }, nonlin := .identity }
  let recurB : Stmt := .assign "B" [.iterNext l]
    { body := { terms := [{ factors := [.read "A" [.const 1]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "A" [l] [baseA, baseB] [recurA, recurB] false) with
  | .error e => throwError (toString e)
  | .ok outs =>
      match outs.find? (·.1 == "A"), outs.find? (·.1 == "B") with
      | some (_, A), some (_, B) =>
          unless DenseTensor.approxEq A (tensorOf [3] [0,1,2]) do throwError s!"jacobi A wrong: {repr A.data}"
          unless DenseTensor.approxEq B (tensorOf [3] [0,1,1]) do throwError s!"jacobi B wrong: {repr B.data}"
      | _, _ => throwError "missing A or B"

-- Mutation: swap recur order to [recurB, recurA] (B evaluated BEFORE A writes this step). If the
-- leak above is genuinely order-sensitive, B[1] must now read A's still-zero value: B=[0,0,1].
run_cmd do
  let l := ax "l" 9
  let zero := tensorOf [] [0]; let one := tensorOf [] [1]
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "Z" zero).insert "ONE" one
  let sizes := (({} : HashMap UID Nat).insert 9 3)
  let baseA : Stmt := .assign "A" [.iterAt l 0] { body := { terms := [{ factors := [.read "Z" []] }] }, nonlin := .identity }
  let baseB : Stmt := .assign "B" [.iterAt l 0] { body := { terms := [{ factors := [.read "Z" []] }] }, nonlin := .identity }
  let recurA : Stmt := .assign "A" [.iterNext l]
    { body := { terms := [{ factors := [.read "A" [.axis l]] }, { factors := [.read "ONE" []] }] }, nonlin := .identity }
  let recurB : Stmt := .assign "B" [.iterNext l]
    { body := { terms := [{ factors := [.read "A" [.const 1]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "A" [l] [baseA, baseB] [recurB, recurA] false) with
  | .error e => throwError (toString e)
  | .ok outs =>
      match outs.find? (·.1 == "B") with
      | some (_, B) => unless DenseTensor.approxEq B (tensorOf [3] [0,0,1]) do
          throwError s!"jacobi mutation: order-sensitivity not observed, B = {repr B.data}"
      | none => throwError "missing B"

-- Two same-named base statements for state "dp": a row-0 face write (free over column) plus a
-- fully-pinned point override at (1,0) -- the accepted shape from
-- papers/wave_f_scanplan_proposal.md §5.1. Verified: dp = [[0,1],[1,1]] (row-major [0,1,1,1]) --
-- the row-0 face [0,1], the point override at (1,0)=1, and the single fully-advanced recur cell
-- dp[1,1] = dp[0,0] + T[0,0] = 0 + 1 = 1.
run_cmd do
  let r := ax "r" 1; let c := ax "c" 2
  let rowFace := tensorOf [2] [0, 1]; let one := tensorOf [] [1]; let ones2 := tensorOf [2,2] [1,1,1,1]
  let env : HashMap String DenseTensor :=
    ((({} : HashMap String DenseTensor).insert "ROWFACE" rowFace).insert "ONE" one).insert "T" ones2
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 2 2
  let baseFace : Stmt := .assign "dp" [.iterAt r 0, .free c]
    { body := { terms := [{ factors := [.read "ROWFACE" [.axis c]] }] }, nonlin := .identity }
  let basePoint : Stmt := .assign "dp" [.iterAt r 1, .iterAt c 0]
    { body := { terms := [{ factors := [.read "ONE" []] }] }, nonlin := .identity }
  let recur : Stmt := .assign "dp" [.iterNext r, .iterNext c]
    { body := { terms := [{ factors := [.read "dp" [.axis r, .axis c]] }, { factors := [.read "T" [.axis r, .axis c]] }] },
      nonlin := .identity }
  match evalScan [] env sizes (.scan "dp" [r, c] [baseFace, basePoint] [recur] false) with
  | .error e => throwError (toString e)
  | .ok outs => match outs.find? (·.1 == "dp") with
    | some (_, dp) => unless DenseTensor.approxEq dp (tensorOf [2,2] [0,1,1,1]) do
        throwError s!"multi-base wrong: {repr dp.data}"
    | none => throwError "no dp"

-- Collision mutation: shrink the point override so it collides with the face write, both landing
-- on (0,0). Wave F's checker will reject this outright (§5.1); the LEGACY evaluator has no such
-- check and silently applies last-write-wins in declared order (basePoint overwrites baseFace's
-- value at (0,0)). Verified: dp = [[1,1],[0,2]] (row-major [1,1,0,2]) -- (0,0) is now 1 (the
-- point override, applied second), and the recur cell becomes dp[0,0]+T[0,0] = 1+1 = 2.
run_cmd do
  let r := ax "r" 1; let c := ax "c" 2
  let rowFace := tensorOf [2] [0, 1]; let one := tensorOf [] [1]; let ones2 := tensorOf [2,2] [1,1,1,1]
  let env : HashMap String DenseTensor :=
    ((({} : HashMap String DenseTensor).insert "ROWFACE" rowFace).insert "ONE" one).insert "T" ones2
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 2 2
  let baseFace : Stmt := .assign "dp" [.iterAt r 0, .free c]
    { body := { terms := [{ factors := [.read "ROWFACE" [.axis c]] }] }, nonlin := .identity }
  let collidingPoint : Stmt := .assign "dp" [.iterAt r 0, .iterAt c 0]
    { body := { terms := [{ factors := [.read "ONE" []] }] }, nonlin := .identity }
  let recur : Stmt := .assign "dp" [.iterNext r, .iterNext c]
    { body := { terms := [{ factors := [.read "dp" [.axis r, .axis c]] }, { factors := [.read "T" [.axis r, .axis c]] }] },
      nonlin := .identity }
  -- FLIPPED (reference-alignment, shape 5): this used to assert last-write-wins, dp = [1,1,0,2]
  -- (old value, observed). The reference now refuses overlapping base writes outright, matching
  -- the checked backend's `baseWritesOverlap`; there is no declared-order precedence.
  match evalScan [] env sizes (.scan "dp" [r, c] [baseFace, collidingPoint] [recur] false) with
  | .error (.baseWritesOverlap "dp" "dp" 0 1) => pure ()
  | .error e => throwError s!"collision mutation: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)

-- S-B 1: a strided base computes X[j] densely, places it at even state coordinates, then a dense
-- recurrence copies the complete six-cell state slice through history.
run_cmd do
  let j := ax "j" 1; let o := ax "o" 2; let l := ax "l" 9
  let X := tensorOf [3] [1, 2, 3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes := ((({} : HashMap UID Nat).insert 1 3).insert 2 6).insert 9 3
  let base : Stmt := .scatter "S" [.affine (.scale 2 j), .iterAt l 0]
    { body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.free o, .iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis o, .axis l]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [base] [recur] false) with
  | .error e => throwError s!"S-B strided base errored: {e}"
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) =>
        unless S.shape == [6,3] do throwError s!"S-B strided base shape: {S.shape}"
        unless DenseTensor.approxEq S
            (tensorOf [6,3] [1,1,1, 0,0,0, 2,2,2, 0,0,0, 3,3,3, 0,0,0]) do
          throwError s!"S-B strided base data: {repr S.data}"
    | none => throwError "S-B strided base: no S"

-- S-B 2: a dense base initializes all six state coordinates; the recurrence computes three dense
-- source values and places them at odd coordinates `2*j+1`.
run_cmd do
  let j := ax "j" 1; let o := ax "o" 2; let l := ax "l" 9
  let X := tensorOf [6] [1, 2, 3, 4, 5, 6]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes := ((({} : HashMap UID Nat).insert 1 3).insert 2 6).insert 9 3
  let base : Stmt := .assign "S" [.free o, .iterAt l 0]
    { body := { terms := [{ factors := [.read "X" [.axis o]] }] }, nonlin := .identity }
  let recur : Stmt := .scatter "S" [.affine (.affine 1 [(2, j)]), .iterNext l]
    { body := { terms := [{ factors := [.read "S" [.scale 2 j, .axis l]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  match evalScan [] env sizes (.scan "S" [l] [base] [recur] false) with
  | .error e => throwError s!"S-B strided recurrence errored: {e}"
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) =>
        unless S.shape == [6,3] do throwError s!"S-B strided recurrence shape: {S.shape}"
        unless DenseTensor.approxEq S
            (tensorOf [6,3] [1,0,0, 2,1,0, 3,0,0, 4,3,0, 5,0,0, 6,5,0]) do
          throwError s!"S-B strided recurrence data: {repr S.data}"
    | none => throwError "S-B strided recurrence: no S"

-- S-B 3: two source-ordered base contributions interleave even and odd coordinates. Neither base
-- may reinitialize the persistent state before overlay; the dense recurrence copies the result.
run_cmd do
  let j := ax "j" 1; let o := ax "o" 2; let l := ax "l" 9
  let E := tensorOf [3] [1, 2, 3]; let O := tensorOf [3] [10, 20, 30]
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "E" E).insert "O" O
  let sizes := ((({} : HashMap UID Nat).insert 1 3).insert 2 6).insert 9 2
  let evenBase : Stmt := .scatter "S" [.affine (.scale 2 j), .iterAt l 0]
    { body := { terms := [{ factors := [.read "E" [.axis j]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let oddBase : Stmt := .scatter "S" [.affine (.affine 1 [(2, j)]), .iterAt l 0]
    { body := { terms := [{ factors := [.read "O" [.axis j]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.free o, .iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis o, .axis l]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [evenBase, oddBase] [recur] false) with
  | .error e => throwError s!"S-B base interleave errored: {e}"
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) =>
        unless S.shape == [6,2] do throwError s!"S-B base interleave shape: {S.shape}"
        unless DenseTensor.approxEq S
            (tensorOf [6,2] [1,1, 10,10, 2,2, 20,20, 3,3, 30,30]) do
          throwError s!"S-B base interleave data: {repr S.data}"
    | none => throwError "S-B base interleave: no S"

-- S-B 4: k is RHS-only. The evaluator must contract k into one dense value per j before affine
-- placement, rather than treating k as another placement coordinate.
run_cmd do
  let j := ax "j" 1; let o := ax "o" 2; let k := ax "k" 3; let l := ax "l" 9
  let X := tensorOf [3,2] [1,10, 2,20, 3,30]; let W := tensorOf [2] [1,2]
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "X" X).insert "W" W
  let sizes := (((({} : HashMap UID Nat).insert 1 3).insert 2 6).insert 3 2).insert 9 2
  let base : Stmt := .scatter "S" [.affine (.scale 2 j), .iterAt l 0]
    { body := { terms := [{ factors := [.read "X" [.axis j, .axis k], .read "W" [.axis k]] }] },
      nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.free o, .iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis o, .axis l]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [base] [recur] false) with
  | .error e => throwError s!"S-B contracted base errored: {e}"
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) =>
        unless S.shape == [6,2] do throwError s!"S-B contracted base shape: {S.shape}"
        unless DenseTensor.approxEq S
            (tensorOf [6,2] [21,21, 0,0, 42,42, 0,0, 63,63, 0,0]) do
          throwError s!"S-B contracted base data: {repr S.data}"
    | none => throwError "S-B contracted base: no S"

-- S-B 5: the scan dimension is first, before the affine state dimension. Placement follows the
-- original slot order rather than assuming iteration axes trail the dense source slice.
run_cmd do
  let j := ax "j" 1; let o := ax "o" 2; let l := ax "l" 9
  let X := tensorOf [3] [4, 5, 6]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes := ((({} : HashMap UID Nat).insert 1 3).insert 2 6).insert 9 3
  let base : Stmt := .scatter "S" [.iterAt l 0, .affine (.affine 1 [(2, j)])]
    { body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.iterNext l, .free o]
    { body := { terms := [{ factors := [.read "S" [.axis l, .axis o]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [base] [recur] false) with
  | .error e => throwError s!"S-B non-trailing scan dimension errored: {e}"
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) =>
        unless S.shape == [3,6] do throwError s!"S-B non-trailing scan dimension shape: {S.shape}"
        unless DenseTensor.approxEq S
            (tensorOf [3,6] [0,4,0,5,0,6, 0,4,0,5,0,6, 0,4,0,5,0,6]) do
          throwError s!"S-B non-trailing scan dimension data: {repr S.data}"
    | none => throwError "S-B non-trailing scan dimension: no S"

/-! ### f32 Task 1, fixtures 11-13: each public scan-path entry refuses f32 on its own

All three reuse "S-B 1: a strided base" above. That fixture passes `decls := []`, so the f32
declarations for `X` and `S` are constructed explicitly here; each fixture additionally plants a
COMPETING defect that the entry would otherwise report first, which is what makes the ordering
observable rather than merely the rejection. -/

-- Fixture 11: S-B 1's `base` scatter statement, called directly through `evalPlain`, with the
-- output axis `j` unsized. `evalPlain`'s scatter arm computes `scatterOutShape` before anything
-- else, so without an ENTRY guard this would report `.shape (.unsizedScatterOutput …)`.
run_cmd do
  let j := ax "j" 1; let o := ax "o" 2; let l := ax "l" 9
  let X := tensorOf [3] [1, 2, 3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes := (({} : HashMap UID Nat).insert 2 6).insert 9 3   -- `j` (uid 1) deliberately unsized
  let base : Stmt := .scatter "S" [.affine (.scale 2 j), .iterAt l 0]
    { body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let decls : List Decl := [.typedTensor .f32 "X" [j], .typedTensor .f32 "S" [o, l]]
  match evalPlain decls env sizes base with
  | Except.error (.unsupportedDtype "S") => pure ()
  | Except.error e => throwError s!"fixture 11: expected the dtype refusal before scatterOutShape, got {e}"
  | Except.ok _ => throwError "fixture 11: an f32 scatter was evaluated by evalPlain"
-- Control: with the same statement declared f64, `evalPlain` reaches and reports the planted
-- unsized-output defect — so fixture 11's ordering claim is about precedence, not about the
-- competing error being absent.
run_cmd do
  let j := ax "j" 1; let o := ax "o" 2; let l := ax "l" 9
  let X := tensorOf [3] [1, 2, 3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes := (({} : HashMap UID Nat).insert 2 6).insert 9 3
  let base : Stmt := .scatter "S" [.affine (.scale 2 j), .iterAt l 0]
    { body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  match evalPlain [.tensor "X" [j], .tensor "S" [o, l]] env sizes base with
  | Except.error (.shape (.unsizedScatterOutput _)) => pure ()
  | Except.error e => throwError s!"fixture 11 control: expected the unsized-output error, got {e}"
  | Except.ok _ => throwError "fixture 11 control: the planted unsized output was not reported"

-- Fixture 12: the SAME S-B 1 `base` statement through `evalStmtSliceSeeded`, carrying a
-- non-identity scatter nonlinearity. The scatter arm checks that nonlinearity itself and never
-- reaches `evalAssignDtypedSeeded`'s guard, so the refusal has to come from the public entry.
run_cmd do
  let j := ax "j" 1; let o := ax "o" 2; let l := ax "l" 9
  let X := tensorOf [3] [1, 2, 3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes := ((({} : HashMap UID Nat).insert 1 3).insert 2 6).insert 9 3
  let base : Stmt := .scatter "S" [.affine (.scale 2 j), .iterAt l 0]
    { body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .pointwise .relu }
    { fill := 0, reduce := .rejectCollisions }
  let seed : HashMap UID Int := {}
  match evalStmtSliceSeeded [.typedTensor .f32 "X" [j], .typedTensor .f32 "S" [o, l]]
      env sizes seed base with
  | Except.error (.unsupportedDtype "S") => pure ()
  | Except.error e =>
      throwError s!"fixture 12: expected the dtype refusal before unsupportedScatterNonlin, got {e}"
  | Except.ok _ => throwError "fixture 12: an f32 scatter slice was evaluated"
-- Control: the same statement declared f64 reaches and reports the planted nonlinearity defect.
run_cmd do
  let j := ax "j" 1; let o := ax "o" 2; let l := ax "l" 9
  let X := tensorOf [3] [1, 2, 3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes := ((({} : HashMap UID Nat).insert 1 3).insert 2 6).insert 9 3
  let base : Stmt := .scatter "S" [.affine (.scale 2 j), .iterAt l 0]
    { body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .pointwise .relu }
    { fill := 0, reduce := .rejectCollisions }
  let seed : HashMap UID Int := {}
  match evalStmtSliceSeeded [.tensor "X" [j], .tensor "S" [o, l]] env sizes seed base with
  | Except.error (.unsupportedScatterNonlin "S") => pure ()
  | Except.error e => throwError s!"fixture 12 control: expected unsupportedScatterNonlin, got {e}"
  | Except.ok _ => throwError "fixture 12 control: the planted scatter nonlinearity was not reported"

-- Fixture 13: the complete S-B 1 `evalScan` fixture, with f32 declarations replacing its empty
-- declaration list and the scan iteration axis `l` removed from `sizes`. `evalScan` raises the
-- unsized-iteration error itself, before any (also-guarded) `evalStmtSliceSeeded` call, so this
-- pins `evalScan`'s own public door rather than inheriting a deeper one.
run_cmd do
  let j := ax "j" 1; let o := ax "o" 2; let l := ax "l" 9
  let X := tensorOf [3] [1, 2, 3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes := (({} : HashMap UID Nat).insert 1 3).insert 2 6   -- `l` (uid 9) deliberately unsized
  let base : Stmt := .scatter "S" [.affine (.scale 2 j), .iterAt l 0]
    { body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.free o, .iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis o, .axis l]] }] }, nonlin := .identity }
  let decls : List Decl := [.typedTensor .f32 "X" [j], .typedTensor .f32 "S" [o, l]]
  match evalScan decls env sizes (.scan "S" [l] [base] [recur] false) with
  | Except.error (.unsupportedDtype "S") => pure ()
  | Except.error e =>
      throwError s!"fixture 13: expected the dtype refusal before the unsized-iteration error, got {e}"
  | Except.ok _ => throwError "fixture 13: an f32 scan was evaluated"
-- Control: the same scan declared f64 reaches and reports the planted unsized-iteration error.
run_cmd do
  let j := ax "j" 1; let o := ax "o" 2; let l := ax "l" 9
  let X := tensorOf [3] [1, 2, 3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes := (({} : HashMap UID Nat).insert 1 3).insert 2 6
  let base : Stmt := .scatter "S" [.affine (.scale 2 j), .iterAt l 0]
    { body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.free o, .iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis o, .axis l]] }] }, nonlin := .identity }
  match evalScan [.tensor "X" [j], .tensor "S" [o, l]] env sizes
      (.scan "S" [l] [base] [recur] false) with
  | Except.error (.shape (.unsizedAxis 9 (.scanIteration "l"))) => pure ()
  | Except.error e => throwError s!"fixture 13 control: expected the unsized-iteration error, got {e}"
  | Except.ok _ => throwError "fixture 13 control: the planted unsized iteration axis was not reported"

/-! ### Reference-alignment, scan group: structural rejections

The checked backend rejects these scans on principle (`ScanCompileError`); the reference used to
evaluate them to a silently wrong or order-dependent value. Each REJECT fixture pins the typed
`EvalError` constructor and payload, and sits next to an ACCEPT fixture for its nearest legal
neighbour so the guard cannot be satisfied by rejecting more than it should. Accepted values were
observed from a real run, never hand-derived. -/

-- Shape 4. REJECT donor: "COUPLED scan" fixture above, cloned to ONE state `h` with lag 2
--   (`h[l+1] := h[l] + h[l-1]`), change: add a second base pinned at index 1 (`h1 = 5`, L = 4).
--   The step overwrites index 1, so the seed `5` is silently lost (the old reference answered
--   [1, 1, 2, 3], identical to the run without that base).
run_cmd do
  let l := ax "l" 9
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "H0" (tensorOf [] [1])).insert "H1" (tensorOf [] [5])
  let sizes := (({} : HashMap UID Nat).insert 9 4)
  let recur : Stmt := .assign "h" [.iterNext l]
    { body := { terms := [{ factors := [.read "h" [.axis l]] }, { factors := [.read "h" [.shift l (-1)]] }] }, nonlin := .identity }
  let b0 : Stmt := .assign "h" [.iterAt l 0] (raRhs "H0" [])
  let b1 : Stmt := .assign "h" [.iterAt l 1] (raRhs "H1" [])
  match evalScan [] env sizes (.scan "h" [l] [b0, b1] [recur] false) with
  | .error (.baseWriteNotAtBoundary "h" "h" 1) => pure ()
  | .error e => throwError s!"shape 4: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- ACCEPT neighbour: same program with only the boundary base (clone, drop `b1`).
  match evalScan [] env sizes (.scan "h" [l] [b0] [recur] false) with
  | .error e => throwError s!"shape 4 accept: {e}"
  | .ok outs => match outs.find? (·.1 == "h") with
    | some (_, h) => unless DenseTensor.approxEq h (tensorOf [4] [1, 1, 2, 3]) do
        throwError s!"shape 4 accept: lag-2 scan wrong: {repr h.data}"
    | none => throwError "shape 4 accept: no h"

-- Shape 4, ACCEPT neighbour in 2-D. Donor: none in this file (first 2-D scan here); the base is
--   pinned at index 1 on `c` but at index 0 on `r`, so it DOES touch the boundary and is legal.
--   `G[0, 1] := Y[0]`, recurrence `G[r+1, c+1] := G[r, c]`, r = c = 3.
run_cmd do
  let r := ax "r" 1; let c := ax "c" 2
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "Y" (tensorOf [3] [10, 20, 30])
  let sizes := (({} : HashMap UID Nat).insert 1 3).insert 2 3
  let recur : Stmt := .assign "G" [.iterNext r, .iterNext c] (raRhs "G" [.axis r, .axis c])
  let pt : Stmt := .assign "G" [.iterAt r 0, .iterAt c 1] (raRhs "Y" [.const 0])
  match evalScan [] env sizes (.scan "G" [r, c] [pt] [recur] false) with
  | .error e => throwError s!"shape 4 2-D accept: {e}"
  | .ok outs => match outs.find? (·.1 == "G") with
    | some (_, G) => unless DenseTensor.approxEq G (tensorOf [3, 3] [0, 10, 0, 0, 0, 10, 0, 0, 0]) do
        throwError s!"shape 4 2-D accept: wrong: {repr G.data}"
    | none => throwError "shape 4 2-D accept: no G"

-- Shape 5. 2-D state G[r, c] (axes r, c; r = c = 3), recurrence `G[r+1, c+1] := G[r, c]`.
--   `face0` = `G[r, 0] := Z[r]` (column 0), `row0` = `G[0, c] := Y[c]` (row 0), `pt` = `G[0, 1] := Y[0]`.
--   Z[0] = 1 and Y[0] = 10 differ, so at the shared corner G[0, 0] "last write wins" (10) and
--   "first wins" (1) disagree: the decided behaviour is a refusal with NO declared-order precedence.
private def raFaceEnv : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "Z" (tensorOf [3] [1, 2, 3])).insert "Y" (tensorOf [3] [10, 20, 30])

run_cmd do
  let r := ax "r" 1; let c := ax "c" 2
  let sizes := (({} : HashMap UID Nat).insert 1 3).insert 2 3
  let recur : Stmt := .assign "G" [.iterNext r, .iterNext c] (raRhs "G" [.axis r, .axis c])
  let face0 : Stmt := .assign "G" [.free r, .iterAt c 0] (raRhs "Z" [.axis r])
  let row0 : Stmt := .assign "G" [.iterAt r 0, .free c] (raRhs "Y" [.axis c])
  let pt : Stmt := .assign "G" [.iterAt r 0, .iterAt c 1] (raRhs "Y" [.const 0])
  -- REJECT: corner overlap (row 0 x column 0 share G[0, 0]).
  match evalScan [] raFaceEnv sizes (.scan "G" [r, c] [face0, row0] [recur] false) with
  | .error (.baseWritesOverlap "G" "G" 0 1) => pure ()
  | .error e => throwError s!"shape 5 corner: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- REJECT: exact duplicate (clone, change: second base is a copy of the first).
  match evalScan [] raFaceEnv sizes (.scan "G" [r, c] [face0, face0] [recur] false) with
  | .error (.baseWritesOverlap "G" "G" 0 1) => pure ()
  | .error e => throwError s!"shape 5 duplicate: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- ACCEPT neighbour: disjoint face + point (clone of the corner fixture, change: `row0` -> `pt`,
  --   whose column pin 1 differs from the face's column pin 0).
  match evalScan [] raFaceEnv sizes (.scan "G" [r, c] [face0, pt] [recur] false) with
  | .error e => throwError s!"shape 5 accept: {e}"
  | .ok outs => match outs.find? (·.1 == "G") with
    | some (_, G) =>
        unless DenseTensor.approxEq G (tensorOf [3, 3] [1, 10, 0, 2, 1, 10, 3, 2, 1]) do
          throwError s!"shape 5 accept: wrong: {repr G.data}"
    | none => throwError "shape 5 accept: no G"

-- Shape 6. REJECT donor: "COUPLED scan" fixture, cloned to ONE scalar state `S` (L = 3, base
--   `S[0] := C`, C = 1), change: TWO results with different bodies, `rA: S[l+1] := S[l]` and
--   `rB: S[l+1] := S[l] + S[l]`. Single-result runs give [1,1,1] (rA) and [1,2,4] (rB), so
--   "second wins" (old behaviour, [1,2,4]) and "first wins" differ: refusal pins neither.
run_cmd do
  let l := ax "l" 9
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "C" (tensorOf [] [1])
  let sizes := (({} : HashMap UID Nat).insert 9 3)
  let b : Stmt := .assign "S" [.iterAt l 0] (raRhs "C" [])
  let rA : Stmt := .assign "S" [.iterNext l] (raRhs "S" [.axis l])
  let rB : Stmt := .assign "S" [.iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis l]] }, { factors := [.read "S" [.axis l]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [b] [rA, rB] false) with
  | .error (.duplicateStateResult "S" "S" 0 1) => pure ()
  | .error e => throwError s!"shape 6: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- ACCEPT neighbour: the same scan with only the second result (clone, drop `rA`).
  match evalScan [] env sizes (.scan "S" [l] [b] [rB] false) with
  | .error e => throwError s!"shape 6 accept: {e}"
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) => unless DenseTensor.approxEq S (tensorOf [3] [1, 2, 4]) do
        throwError s!"shape 6 accept: wrong: {repr S.data}"
    | none => throwError "shape 6 accept: no S"

-- Shape 6, scan-local SCATTER results (probe C13). Donor: the fixture above, change: state `S`
--   is 6 wide, two parity-split base scatters `S[2*j,0] := X[j]`, `S[2*j+1,0] := Y[j]` (residue-
--   disjoint, legal) and two parity-split scatter results `S[2*j,l+1] := S[2*j,l]`,
--   `S[2*j+1,l+1] := S[2*j+1,l]` (j = 3, L = 3). Each result alone is legal and leaves the other
--   parity frozen at its base; the pair is a duplicate result for the state, whatever the cells.
run_cmd do
  let j := ax "j" 1; let l := ax "l" 9
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "X" (tensorOf [3] [1, 2, 3])).insert "Y" (tensorOf [3] [10, 20, 30])
  let sizes := (({} : HashMap UID Nat).insert 1 3).insert 9 3
  let ev := IdxExpr.scale 2 j
  let od := IdxExpr.affine 1 [(2, j)]
  let opts : ScatterOpts := { fill := 0, reduce := .rejectCollisions }
  let bE : Stmt := .scatter "S" [.affine ev, .iterAt l 0] (raRhs "X" [.axis j]) opts
  let bO : Stmt := .scatter "S" [.affine od, .iterAt l 0] (raRhs "Y" [.axis j]) opts
  let rE : Stmt := .scatter "S" [.affine ev, .iterNext l] (raRhs "S" [ev, .axis l]) opts
  let rO : Stmt := .scatter "S" [.affine od, .iterNext l] (raRhs "S" [od, .axis l]) opts
  match evalScan [] env sizes (.scan "S" [l] [bE, bO] [rE, rO] false) with
  | .error (.duplicateStateResult "S" "S" 0 1) => pure ()
  | .error e => throwError s!"shape 6 scatter: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- ACCEPT neighbour: only the even-parity result (clone, drop `rO`).
  match evalScan [] env sizes (.scan "S" [l] [bE, bO] [rE] false) with
  | .error e => throwError s!"shape 6 scatter accept: {e}"
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) =>
        unless DenseTensor.approxEq S (tensorOf [6, 3] [1, 1, 1, 10, 0, 0, 2, 2, 2, 20, 0, 0, 3, 3, 3, 30, 0, 0]) do
          throwError s!"shape 6 scatter accept: wrong: {repr S.data}"
    | none => throwError "shape 6 scatter accept: no S"

-- Shape 7. REJECT donor: the shape 6 fixture, cloned to a 2-wide state `S[j,l]` (j = 2, L = 3,
--   base `S[j,0] := X0[j]`, X0 = [1, 10]), change: the step block is `T := S[l]; U := T; T := X0;
--   S[l+1] := U + T`. `T` is produced at recurrence positions 0 and 2 with a READ of it between,
--   so only a count over the whole block (not adjacent pairs) sees it. The old reference ran `T`
--   as a mutable variable and answered [1,2,3, 10,20,30] (U saw the first T, the sum the second).
run_cmd do
  let j := ax "j" 1; let l := ax "l" 9
  let env : HashMap String DenseTensor :=
    ({} : HashMap String DenseTensor).insert "X0" (tensorOf [2] [1, 10])
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 9 3
  let b : Stmt := .assign "S" [.free j, .iterAt l 0] (raRhs "X0" [.axis j])
  let t0 : Stmt := .assign "T" [.free j] (raRhs "S" [.axis j, .axis l])
  let u1 : Stmt := .assign "U" [.free j] (raRhs "T" [.axis j])
  let t2 : Stmt := .assign "T" [.free j] (raRhs "X0" [.axis j])
  let v2 : Stmt := .assign "V" [.free j] (raRhs "X0" [.axis j])
  let sum (x y : String) : Stmt := .assign "S" [.free j, .iterNext l]
    { body := { terms := [{ factors := [.read x [.axis j]] }, { factors := [.read y [.axis j]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "S" [l] [b] [t0, u1, t2, sum "U" "T"] false) with
  | .error (.duplicateScratchProducer "S" "T" 0 2) => pure ()
  | .error e => throwError s!"shape 7: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- ADJACENT duplicate (clone, change: `T := S[l]; T := X0; S[l+1] := T + T`, no read between).
  match evalScan [] env sizes (.scan "S" [l] [b] [t0, t2, sum "T" "T"] false) with
  | .error (.duplicateScratchProducer "S" "T" 0 1) => pure ()
  | .error e => throwError s!"shape 7 adjacent: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- ACCEPT neighbour: the second producer renamed (clone, change: `t2` -> `v2`, sum `U + V`).
  match evalScan [] env sizes (.scan "S" [l] [b] [t0, u1, v2, sum "U" "V"] false) with
  | .error e => throwError s!"shape 7 accept: {e}"
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) => unless DenseTensor.approxEq S (tensorOf [2, 3] [1, 2, 3, 10, 20, 30]) do
        throwError s!"shape 7 accept: wrong: {repr S.data}"
    | none => throwError "shape 7 accept: no S"

-- Shape 8. REJECT donor: the shape 6 scatter fixture, cloned to ONE stride-2 base scatter
--   `S[2*j,0] := X[j]` (j = 3, so 6 wide) and an ordinary result `S[k,l+1] := S[k,l]` over a
--   declared axis `k` (L = 3), change: `k` is 5 or 7 instead of 6. The old reference allocated the
--   BASE shape and silently cropped the result: a [6,3] state, identical for k = 5, 6 and 7.
run_cmd do
  let j := ax "j" 1; let k := ax "k" 2; let l := ax "l" 9
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" (tensorOf [3] [1, 2, 3])
  let opts : ScatterOpts := { fill := 0, reduce := .rejectCollisions }
  let b : Stmt := .scatter "S" [.affine (.scale 2 j), .iterAt l 0] (raRhs "X" [.axis j]) opts
  let r : Stmt := .assign "S" [.free k, .iterNext l] (raRhs "S" [.axis k, .axis l])
  let run (kk : Nat) := evalScan [] env ((({} : HashMap UID Nat).insert 1 3).insert 2 kk |>.insert 9 3)
    (.scan "S" [l] [b] [r] false)
  match run 5 with
  | .error (.inconsistentStateExtent "S" "S" 0 6 5) => pure ()
  | .error e => throwError s!"shape 8 k=5: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  match run 7 with
  | .error (.inconsistentStateExtent "S" "S" 0 6 7) => pure ()
  | .error e => throwError s!"shape 8 k=7: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- ACCEPT neighbour: k = 6 = 2 * j (clone, change: k).
  match run 6 with
  | .error e => throwError s!"shape 8 accept: {e}"
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) =>
        unless DenseTensor.approxEq S (tensorOf [6, 3] [1, 1, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 3, 3, 3, 0, 0, 0]) do
          throwError s!"shape 8 accept: wrong: {repr S.data}"
    | none => throwError "shape 8 accept: no S"
  -- EVERY base counts, not just the first: a second base `S[2*m+1,0] := Y[m]` (residue-disjoint
  --   from the first, so shapes 4/5 stay quiet) is 4 wide for m = 2, and the first base and the
  --   result agree at 6. The old reference let the LAST base's shape win ([4,3], cropping the
  --   first base's rows). Accept neighbour: m = 3 makes it 6 wide.
  let m := ax "m" 3
  let b2 : Stmt := .scatter "S" [.affine (.affine 1 [(2, m)]), .iterAt l 0] (raRhs "Y" [.axis m]) opts
  let env2 := env.insert "Y" (tensorOf [3] [10, 20, 30])
  let run2 (mm : Nat) := evalScan [] env2 (((({} : HashMap UID Nat).insert 1 3).insert 2 6).insert 3 mm |>.insert 9 3)
    (.scan "S" [l] [b, b2] [r] false)
  match run2 2 with
  | .error (.inconsistentStateExtent "S" "S" 0 6 4) => pure ()
  | .error e => throwError s!"shape 8 second base: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  match run2 3 with
  | .error e => throwError s!"shape 8 second base accept: {e}"
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) =>
        unless DenseTensor.approxEq S (tensorOf [6, 3] [1, 1, 1, 10, 10, 10, 2, 2, 2, 20, 20, 20, 3, 3, 3, 30, 30, 30]) do
          throwError s!"shape 8 second base accept: wrong: {repr S.data}"
    | none => throwError "shape 8 second base accept: no S"

-- Shape 9. REJECT donor: the shape 8 fixture, change: the base is the ZERO-SCALE write
--   `S[0*j,0] := X[j]` (names no source axis) with `k = 3`. The old reference allocated an EMPTY
--   `[0,3]` state and returned it. Variants: the same row as the SECOND base (index 1), and as the
--   recurrence RESULT placement (`isBase = false`).
run_cmd do
  let j := ax "j" 1; let k := ax "k" 2; let l := ax "l" 9
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" (tensorOf [3] [1, 2, 3])
  let sizes := ((({} : HashMap UID Nat).insert 1 3).insert 2 3).insert 9 3
  let opts : ScatterOpts := { fill := 0, reduce := .rejectCollisions }
  let wr (c : Int) (lit : Nat) : Stmt :=
    .scatter "S" [.affine (.scale c j), .iterAt l lit] (raRhs "X" [.axis j]) opts
  let r : Stmt := .assign "S" [.free k, .iterNext l] (raRhs "S" [.axis k, .axis l])
  match evalScan [] env sizes (.scan "S" [l] [wr 0 0] [r] false) with
  | .error (.scanWriteRowNotAdmitted "S" "S" true 0 0) => pure ()
  | .error e => throwError s!"shape 9: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- second base (clone, change: a legal stride-2 base first, k = 6; the zero-scale base second).
  let sizes6 := ((({} : HashMap UID Nat).insert 1 3).insert 2 6).insert 9 3
  match evalScan [] env sizes6 (.scan "S" [l] [wr 2 0, wr 0 0] [r] false) with
  | .error (.scanWriteRowNotAdmitted "S" "S" true 1 0) => pure ()
  | .error e => throwError s!"shape 9 second base: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- result placement (clone, change: the result is the zero-scale scatter).
  let rz : Stmt := .scatter "S" [.affine (.scale 0 j), .iterNext l] (raRhs "S" [.axis j, .axis l]) opts
  match evalScan [] env sizes6 (.scan "S" [l] [wr 2 0] [rz] false) with
  | .error (.scanWriteRowNotAdmitted "S" "S" false 0 0) => pure ()
  | .error e => throwError s!"shape 9 result: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- ACCEPT neighbour: scale 1 instead of 0 (clone, change: `wr 0 0` -> `wr 1 0`).
  match evalScan [] env sizes (.scan "S" [l] [wr 1 0] [r] false) with
  | .error e => throwError s!"shape 9 accept: {e}"
  | .ok outs => match outs.find? (·.1 == "S") with
    | some (_, S) =>
        unless DenseTensor.approxEq S (tensorOf [3, 3] [1, 1, 1, 2, 2, 2, 3, 3, 3]) do
          throwError s!"shape 9 accept: wrong: {repr S.data}"
    | none => throwError "shape 9 accept: no S"

-- Shape 10. REJECT donor: "COUPLED scan" fixture, cloned to two 2-wide states A, B (j = 2, L = 3,
--   X0 = [1, 10]): `A[j,l+1] := A[j,l]`, `B[j,l+1] := B[j,l] + A[j,l]`, base `A[j,0] := X0[j]`;
--   change: base `B[j,0] := A[j,0]` READS state A instead of X0. The old reference's value depended
--   on base statement ORDER (A-before-B seeded B from A's seed, B-before-A from zeros), so BOTH
--   orders are refused; the payload names the reading base's index.
run_cmd do
  let j := ax "j" 1; let l := ax "l" 9
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X0" (tensorOf [2] [1, 10])
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 9 3
  let baseA : Stmt := .assign "A" [.free j, .iterAt l 0] (raRhs "X0" [.axis j])
  let baseBReadsA : Stmt := .assign "B" [.free j, .iterAt l 0] (raRhs "A" [.axis j, .const 0])
  let baseB : Stmt := .assign "B" [.free j, .iterAt l 0] (raRhs "X0" [.axis j])
  let recA : Stmt := .assign "A" [.free j, .iterNext l] (raRhs "A" [.axis j, .axis l])
  let recB : Stmt := .assign "B" [.free j, .iterNext l]
    { body := { terms := [{ factors := [.read "B" [.axis j, .axis l]] }, { factors := [.read "A" [.axis j, .axis l]] }] }, nonlin := .identity }
  match evalScan [] env sizes (.scan "A" [l] [baseA, baseBReadsA] [recA, recB] false) with
  | .error (.stateReadInBaseBlock "A" 1 "A") => pure ()
  | .error e => throwError s!"shape 10 A-before-B: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  match evalScan [] env sizes (.scan "A" [l] [baseBReadsA, baseA] [recA, recB] false) with
  | .error (.stateReadInBaseBlock "A" 0 "A") => pure ()
  | .error e => throwError s!"shape 10 B-before-A: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  -- ACCEPT neighbour: independent bases (clone, change: `baseBReadsA` -> `baseB`, reads X0).
  match evalScan [] env sizes (.scan "A" [l] [baseA, baseB] [recA, recB] false) with
  | .error e => throwError s!"shape 10 accept: {e}"
  | .ok outs =>
      match outs.find? (·.1 == "A"), outs.find? (·.1 == "B") with
      | some (_, A), some (_, B) =>
          unless DenseTensor.approxEq A (tensorOf [2, 3] [1, 1, 1, 10, 10, 10]) do
            throwError s!"shape 10 accept: A wrong: {repr A.data}"
          unless DenseTensor.approxEq B (tensorOf [2, 3] [1, 2, 3, 10, 20, 30]) do
            throwError s!"shape 10 accept: B wrong: {repr B.data}"
      | _, _ => throwError "shape 10 accept: missing A or B"

-- CHECK ORDER (multi-fault). Each program has TWO faults; the first listed check in
--   `checkScanStructure`'s documented order must win, so flipping any adjacent pair changes the
--   constructor. Scalar-over-`j` state `S` (j = 2, k = 5, L = 3), donor: shape 6/7/8/9/10 fixtures.
--   (a) shape 6 over 4: two results AND a base pinned at index 1 only.
--   (b) shape 6 over 8: two results, the first of which is 5 wide against a 2-wide base.
--   (c) shape 7 over 6, and 6 over 7: whichever repeat appears first in `recur` order wins.
--   (d) shape 9 over 10: a zero-scale base that also reads the state.
--   (e) shape 10 over 4: a base reading the state AND pinned at index 1 only.
run_cmd do
  let j := ax "j" 1; let k := ax "k" 2; let l := ax "l" 9
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X0" (tensorOf [2] [1, 10])
  let sizes := ((({} : HashMap UID Nat).insert 1 2).insert 2 5).insert 9 3
  let opts : ScatterOpts := { fill := 0, reduce := .rejectCollisions }
  let b0 : Stmt := .assign "S" [.free j, .iterAt l 0] (raRhs "X0" [.axis j])
  let b1 : Stmt := .assign "S" [.free j, .iterAt l 1] (raRhs "X0" [.axis j])
  let step : Stmt := .assign "S" [.free j, .iterNext l] (raRhs "S" [.axis j, .axis l])
  let stepK : Stmt := .assign "S" [.free k, .iterNext l] (raRhs "S" [.axis k, .axis l])
  let tS : Stmt := .assign "T" [.free j] (raRhs "S" [.axis j, .axis l])
  let scanOf (b r : List Stmt) := evalScan [] env sizes (.scan "S" [l] b r false)
  match scanOf [b1] [step, step] with
  | .error (.duplicateStateResult "S" "S" 0 1) => pure ()
  | .error e => throwError s!"order (a): wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  match scanOf [b0] [stepK, stepK] with
  | .error (.duplicateStateResult "S" "S" 0 1) => pure ()
  | .error e => throwError s!"order (b): wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  match scanOf [b0] [tS, tS, step, step] with
  | .error (.duplicateScratchProducer "S" "T" 0 1) => pure ()
  | .error e => throwError s!"order (c) scratch first: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  match scanOf [b0] [step, step, tS, tS] with
  | .error (.duplicateStateResult "S" "S" 0 1) => pure ()
  | .error e => throwError s!"order (c) state first: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  let zeroReads : Stmt := .scatter "S" [.affine (.scale 0 j), .iterAt l 0] (raRhs "S" [.axis j, .const 0]) opts
  match scanOf [zeroReads] [step] with
  | .error (.scanWriteRowNotAdmitted "S" "S" true 0 0) => pure ()
  | .error e => throwError s!"order (d): wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  let readsAt1 : Stmt := .assign "S" [.free j, .iterAt l 1] (raRhs "S" [.axis j, .const 0])
  match scanOf [readsAt1] [step] with
  | .error (.stateReadInBaseBlock "S" 0 "S") => pure ()
  | .error e => throwError s!"order (e): wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)

-- Shapes 3 + 11 (reduction-marker agreement). Helper: one statement through `evalPlain`.
private def mkRhs (nm : String) (idx : List IdxExpr) (nl : Nonlin) : RHSExpr :=
  { body := { terms := [{ factors := [.read nm idx] }] }, nonlin := nl }

private def mkPlain (stmt : Stmt) (env : List (String × DenseTensor)) (sizes : List (Nat × Nat)) :
    Except EvalError (String × DenseTensor) :=
  evalPlain [] (HashMap.ofList env) (HashMap.ofList sizes) stmt

-- Shape 3 (marker on a non-axiswise statement). REJECT donor: "f32 entry-guard" is unrelated, so
--   the donor is the NonlinCompileTest `spuriousMarkerPointwise` program, cloned from surface
--   syntax to a hand-built `Stmt`; changes: identity/pointwise/scatter variants. The old reference
--   ignored the marker, so each of these evaluated exactly as its unmarked twin.
run_cmd do
  let i := ax "i" 1; let j := ax "j" 2
  let X := tensorOf [3] [1, -2, 3]
  -- plain identity: `Y[i.] := X[i]`
  match mkPlain (.assign "Y" [.freeNorm i] (mkRhs "X" [.axis i] .identity)) [("X", X)] [(1, 3)] with
  | .error (.unmarkedReductionAxis "Y" 0) => pure ()
  | .error e => throwError s!"shape 3 identity: wrong rejection: {e}"
  | .ok (_, Y) => throwError s!"shape 3 identity: accepted: {repr Y.data}"
  -- plain pointwise: `Y[i.] := relu(X[i])`
  match mkPlain (.assign "Y" [.freeNorm i] (mkRhs "X" [.axis i] (.pointwise .relu))) [("X", X)] [(1, 3)] with
  | .error (.unmarkedReductionAxis "Y" 0) => pure ()
  | .error e => throwError s!"shape 3 pointwise: wrong rejection: {e}"
  | .ok (_, Y) => throwError s!"shape 3 pointwise: accepted: {repr Y.data}"
  -- ACCEPT neighbour (clone, change: pointwise -> axiswise normalize): the marker is the reduction
  --   axis. `Y[i.] := normalize(X[i])` over X = [1,2,3] gives [1/6, 1/3, 1/2].
  match mkPlain (.assign "Y" [.freeNorm i] (mkRhs "X" [.axis i] (.axiswise .normalize none)))
      [("X", tensorOf [3] [1, 2, 3])] [(1, 3)] with
  | .error e => throwError s!"shape 3 accept: {e}"
  | .ok (_, Y) =>
      unless DenseTensor.approxEq Y (tensorOf [3] [1/6, 2/6, 3/6]) do
        throwError s!"shape 3 accept: wrong: {repr Y.data}"
  -- marker position is the index into the WHOLE slot list: `Y[i, j.]` -> 1
  match mkPlain (.assign "Y" [.free i, .freeNorm j] (mkRhs "A" [.axis i, .axis j] .identity))
      [("A", tensorOf [2, 2] [1, 2, 3, 4])] [(1, 2), (2, 2)] with
  | .error (.unmarkedReductionAxis "Y" 1) => pure ()
  | .error e => throwError s!"shape 3 position: wrong rejection: {e}"
  | .ok (_, Y) => throwError s!"shape 3 position: accepted: {repr Y.data}"

-- Shape 11 (two markers on an axiswise statement). REJECT donor: NonlinCompileTest
--   `doubleMarkerAxiswise` (`Y[q., s.] := normalize(A[q, s])`, A = [[1,3],[2,2]]), as a `Stmt`.
--   The old reference reduced along the FIRST marked axis (`q`: columns [1/3,3/5 ; 2/3,2/5]);
--   marking only `s` reduces rows ([1/4,3/4 ; 1/2,1/2]), so the two readings differ.
run_cmd do
  let q := ax "q" 1; let s := ax "s" 2
  let A := tensorOf [2, 2] [1, 3, 2, 2]
  let rhs := mkRhs "A" [.axis q, .axis s] (.axiswise .normalize none)
  match mkPlain (.assign "Y" [.freeNorm q, .freeNorm s] rhs) [("A", A)] [(1, 2), (2, 2)] with
  | .error (.multipleMarkedReductionAxes "Y" 0 1) => pure ()
  | .error e => throwError s!"shape 11: wrong rejection: {e}"
  | .ok (_, Y) => throwError s!"shape 11: accepted: {repr Y.data}"
  -- ACCEPT neighbour (clone, change: drop the marker on q): reduces along s.
  match mkPlain (.assign "Y" [.free q, .freeNorm s] rhs) [("A", A)] [(1, 2), (2, 2)] with
  | .error e => throwError s!"shape 11 accept: {e}"
  | .ok (_, Y) =>
      unless DenseTensor.approxEq Y (tensorOf [2, 2] [0.25, 0.75, 0.5, 0.5]) do
        throwError s!"shape 11 accept: wrong: {repr Y.data}"

-- Shape 3 through the SCATTER arms (the audit finding): `evalPlain`'s scatter arm and the scan-local
--   scatter arm never call `resolveNonlin`, so a check there alone is blind. REJECT donor: the
--   "upsample" fixture in ScatterTest (`Out[2*i, 2*j] := X[i,j]`), changed: slot 1 is `.freeNorm j`
--   (`Out[2*i, j.] := X[i,j]`, one affine slot + one marked free slot).
run_cmd do
  let i := ax "i" 1; let j := ax "j" 2
  let X := tensorOf [2, 2] [1, 2, 3, 4]
  let rhs := mkRhs "X" [.axis i, .axis j] .identity
  let opts : ScatterOpts := { fill := 0, reduce := .rejectCollisions }
  match mkPlain (.scatter "Out" [.affine (.scale 2 i), .freeNorm j] rhs opts) [("X", X)] [(1, 2), (2, 2)] with
  | .error (.unmarkedReductionAxis "Out" 1) => pure ()
  | .error e => throwError s!"shape 3 scatter: wrong rejection: {e}"
  | .ok (_, Out) => throwError s!"shape 3 scatter: accepted: {repr Out.data}"
  -- ACCEPT neighbour (clone, change: `.freeNorm j` -> `.free j`).
  match mkPlain (.scatter "Out" [.affine (.scale 2 i), .free j] rhs opts) [("X", X)] [(1, 2), (2, 2)] with
  | .error e => throwError s!"shape 3 scatter accept: {e}"
  | .ok (_, Out) =>
      unless Out.shape == [4, 2] && Out.data == #[1, 2, 0, 0, 3, 4, 0, 0] do
        throwError s!"shape 3 scatter accept: wrong: {Out.shape} {repr Out.data}"
  -- scan-local scatter arm, called directly (`evalStmtSliceSeeded`): base `S[2*j, k., 0] := X[j,k]`.
  let k := ax "k" 3; let l := ax "l" 9
  let seed : HashMap UID Int := ({} : HashMap UID Int).insert 9 0
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes := ((({} : HashMap UID Nat).insert 2 2).insert 3 2).insert 9 3
  let sc (m : LHSSlot) : Stmt :=
    .scatter "S" [.affine (.scale 2 j), m, .iterAt l 0] (mkRhs "X" [.axis j, .axis k] .identity) opts
  match evalStmtSliceSeeded [] env sizes seed (sc (.freeNorm k)) with
  | .error (.unmarkedReductionAxis "S" 1) => pure ()
  | .error e => throwError s!"shape 3 scan scatter: wrong rejection: {e}"
  | .ok (_, t) => throwError s!"shape 3 scan scatter: accepted: {repr t.data}"
  match evalStmtSliceSeeded [] env sizes seed (sc (.free k)) with
  | .error e => throwError s!"shape 3 scan scatter accept: {e}"
  | .ok _ => pure ()

-- Shapes 3 + 11 inside a scan (scan-local assigns), the realistic trigger: a softmax scan whose BASE
--   carries a stray marker. REJECT donor: "LINEAR scan" (`S[j,0] := X[j]`, X = [1,10], L = 3 ... ),
--   changed: base slot `.free j` -> `.freeNorm j` (`S[j.,0] := X0[j]`), and separately a step
--   with two markers. ACCEPT neighbour: the unmarked base, and a step marked once.
run_cmd do
  let j := ax "j" 1; let l := ax "l" 9
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X0" (tensorOf [2] [1, 10])
  let sizes := (({} : HashMap UID Nat).insert 1 2).insert 9 3
  let base (m : LHSSlot) : Stmt := .assign "S" [m, .iterAt l 0] (raRhs "X0" [.axis j])
  let step (m : LHSSlot) (nl : Nonlin) : Stmt :=
    .assign "S" [m, .iterNext l] (mkRhs "S" [.axis j, .axis l] nl)
  let soft := Nonlin.axiswise .softmax none
  let scanOf (b r : Stmt) := evalScan [] env sizes (.scan "S" [l] [b] [r] false)
  match scanOf (base (.freeNorm j)) (step (.free j) .identity) with
  | .error (.unmarkedReductionAxis "S" 0) => pure ()
  | .error e => throwError s!"shape 3 scan base: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  match scanOf (base (.free j)) (step (.freeNorm j) (.pointwise .relu)) with
  | .error (.unmarkedReductionAxis "S" 0) => pure ()
  | .error e => throwError s!"shape 3 scan step: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  match scanOf (base (.free j)) (step (.free j) .identity) with
  | .error e => throwError s!"shape 3 scan accept (unmarked): {e}"
  | .ok _ => pure ()
  match scanOf (base (.free j)) (step (.freeNorm j) soft) with
  | .error e => throwError s!"shape 3 scan accept (softmax step): {e}"
  | .ok _ => pure ()
  -- two markers on one scan step: both slots are retained axes (`S[p., j., l+1]`)
  let p := ax "p" 4
  let env2 := env.insert "X1" (tensorOf [2, 2] [1, 2, 3, 4])
  let sizes2 := sizes.insert 4 2
  let base2 : Stmt := .assign "S" [.free p, .free j, .iterAt l 0] (raRhs "X1" [.axis p, .axis j])
  let step2 (m1 m2 : LHSSlot) : Stmt :=
    .assign "S" [m1, m2, .iterNext l] (mkRhs "S" [.axis p, .axis j, .axis l] soft)
  match evalScan [] env2 sizes2 (.scan "S" [l] [base2] [step2 (.freeNorm p) (.freeNorm j)] false) with
  | .error (.multipleMarkedReductionAxes "S" 0 1) => pure ()
  | .error e => throwError s!"shape 11 scan: wrong rejection: {e}"
  | .ok outs => throwError (raAccepted outs)
  match evalScan [] env2 sizes2 (.scan "S" [l] [base2] [step2 (.free p) (.freeNorm j)] false) with
  | .error e => throwError s!"shape 11 scan accept: {e}"
  | .ok _ => pure ()

-- Shape 1 (top-level max/min scatter whose fill is not the aggregation identity). REJECT donor:
--   ScatterTest "upsample"/"4g regression" scatter, here as an `evalPlain` `.scatter` statement
--   `Out[2*i] := maxreduce(X[i])`, X = [-1,-2,-3]; the old reference filled the gaps with 0 and
--   returned [-1,0,-2,0,-3,0], which is NOT the max identity. The checked path refuses every
--   top-level max/min scatter (`scatterFillOrFail`: no finite fill is -inf).
run_cmd do
  let i := ax "i" 1
  let X := tensorOf [3] [-1, -2, -3]
  let opts : ScatterOpts := { fill := 0, reduce := .rejectCollisions }
  let rhsAgg (agg : AggOp) : RHSExpr := { mkRhs "X" [.axis i] .identity with agg := agg }
  let stmtAgg (agg : AggOp) : Stmt := .scatter "Out" [.affine (.scale 2 i)] (rhsAgg agg) opts
  match mkPlain (stmtAgg .max) [("X", X)] [(1, 3)] with
  | .error (.scatterFillNotIdentity "Out" .max) => pure ()
  | .error e => throwError s!"shape 1 max: wrong rejection: {e}"
  | .ok (_, Out) => throwError s!"shape 1 max: accepted: {repr Out.data}"
  match mkPlain (stmtAgg .min) [("X", X)] [(1, 3)] with
  | .error (.scatterFillNotIdentity "Out" .min) => pure ()
  | .error e => throwError s!"shape 1 min: wrong rejection: {e}"
  | .ok (_, Out) => throwError s!"shape 1 min: accepted: {repr Out.data}"
  -- ACCEPT neighbour (clone, change: agg .max -> .sum): a sum scatter's identity IS the fill 0.
  match mkPlain (stmtAgg .sum) [("X", X)] [(1, 3)] with
  | .error e => throwError s!"shape 1 accept (sum): {e}"
  | .ok (_, Out) =>
      unless Out.data == #[-1, 0, -2, 0, -3, 0] do throwError s!"shape 1 accept (sum): {repr Out.data}"
  -- ACCEPT: the one fill that denotes -inf (`Float.ofInt (-(2^1024))` overflows) agrees with the
  --   identity, exactly as `scatterFillOrFail`'s binary64 arm does; the gaps then hold -inf.
  let optsInf : ScatterOpts := { fill := -(2 ^ 1024), reduce := .rejectCollisions }
  match mkPlain (.scatter "Out" [.affine (.scale 2 i)] (rhsAgg .max) optsInf) [("X", X)] [(1, 3)] with
  | .error e => throwError s!"shape 1 accept (-inf fill): {e}"
  | .ok (_, Out) =>
      unless Out.get! [0] == -1 && Out.get! [1] == -1.0 / 0.0 && Out.get! [4] == -3 do
        throwError s!"shape 1 accept (-inf fill): {repr Out.data}"

-- Shape 1, the `+`-joined two-term max (the only case where a scatter max is meaningful: no gap
--   cells when the terms cover every output cell). Donor: ScatterTest '4g regression' (A = [1,5,2],
--   B = [10,-1,-1], `Out[i] := A[i] + B[i]` with agg .max, per-position max [10,5,2]). The checked
--   rule refuses it all the same: the algebra comes from `agg`, and `scatterFillOrFail` never looks
--   at coverage, so the reference refuses it too (stricter than meaningful, but checked-aligned).
--   The same scan-LOCAL scatter stays accepted (below).
run_cmd do
  let i := ax "i" 1
  let env := [("A", tensorOf [3] [1, 5, 2]), ("B", tensorOf [3] [10, -1, -1])]
  let rhs : RHSExpr :=
    { body := { terms := [{ factors := [.read "A" [.axis i]] }, { factors := [.read "B" [.axis i]] }] }
      nonlin := .identity, agg := .max }
  let opts : ScatterOpts := { fill := 0, reduce := .rejectCollisions }
  match mkPlain (.scatter "Out" [.affine (.axis i)] rhs opts) env [(1, 3)] with
  | .error (.scatterFillNotIdentity "Out" .max) => pure ()
  | .error e => throwError s!"shape 1 joined: wrong rejection: {e}"
  | .ok (_, Out) => throwError s!"shape 1 joined: accepted: {repr Out.data}"
  -- ACCEPT: the SCAN-LOCAL max-reduce scatter (the checked path accepts it; the check is not in
  --   `evalScatter` nor in the scan arm): slice `S[2*j, 0]` with agg .max over X = [3, 7].
  let j := ax "j" 2; let l := ax "l" 9
  let seed : HashMap UID Int := ({} : HashMap UID Int).insert 9 0
  let senv : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" (tensorOf [2] [3, 7])
  let ssizes := (({} : HashMap UID Nat).insert 2 2).insert 9 3
  let sstmt : Stmt := .scatter "S" [.affine (.scale 2 j), .iterAt l 0]
    { mkRhs "X" [.axis j] .identity with agg := .max } opts
  match evalStmtSliceSeeded [] senv ssizes seed sstmt with
  | .error e => throwError s!"shape 1 scan-local max scatter: {e}"
  | .ok (_, t) =>
      unless t.data == #[3, 7] do throwError s!"shape 1 scan-local max scatter: {repr t.data}"
  -- ACCEPT: a plain max over a CONTRACTION axis (not a scatter): `Y[q] := maxreduce(A[q, r])`.
  let q := ax "q" 3; let r := ax "r" 4
  match mkPlain (.assign "Y" [.free q] { mkRhs "A" [.axis q, .axis r] .identity with agg := .max })
      [("A", tensorOf [2, 2] [1, 9, 4, 2])] [(3, 2), (4, 2)] with
  | .error e => throwError s!"shape 1 accept (plain max): {e}"
  | .ok (_, Y) => unless Y.data == #[9, 4] do throwError s!"shape 1 accept (plain max): {repr Y.data}"

-- Shape 2 (top-level scatter into a `predicate` destination). `evalScatter` took no declarations,
--   so it always ran the real (×, Σ) algebra and left {0,1}. Donor: the CompileTest
--   `predicateScatterDest` program `predicate Out(i); Out[2*i] := E[i] + E[i]`, E = [1,0,1] (the
--   checked path still REFUSES it, `predicateScatterDest`; this is the reference's own semantics).
--   The two readings differ: real sum doubles to [2,0,0,0,2,0]; Boolean ∃ keeps [1,0,0,0,1,0].
private def mkPlainD (decls : List Decl) (stmt : Stmt) (env : List (String × DenseTensor))
    (sizes : List (Nat × Nat)) : Except EvalError (String × DenseTensor) :=
  evalPlain decls (HashMap.ofList env) (HashMap.ofList sizes) stmt

run_cmd do
  let i := ax "i" 1
  let E := tensorOf [3] [1, 0, 1]
  let opts : ScatterOpts := { fill := 0, reduce := .rejectCollisions }
  let rhs : RHSExpr :=
    { body := { terms := [{ factors := [.read "E" [.axis i]] }, { factors := [.read "E" [.axis i]] }] }
      nonlin := .identity }
  let st : Stmt := .scatter "Out" [.affine (.scale 2 i)] rhs opts
  match mkPlainD [.predicate "Out" [i]] st [("E", E)] [(1, 3)] with
  | .error e => throwError s!"shape 2 predicate: {e}"
  | .ok (_, Out) =>
      unless Out.shape == [6] && Out.data == #[1, 0, 0, 0, 1, 0] do
        throwError s!"shape 2 predicate: {Out.shape} {repr Out.data}"
  -- ACCEPT neighbour / contrast (clone, change: declaration `predicate` -> `tensor`): a real
  --   destination still sums, so the dtype is what changed the answer.
  match mkPlainD [.tensor "Out" [i]] st [("E", E)] [(1, 3)] with
  | .error e => throwError s!"shape 2 real twin: {e}"
  | .ok (_, Out) =>
      unless Out.data == #[2, 0, 0, 0, 2, 0] do throwError s!"shape 2 real twin: {repr Out.data}"
  -- The `.sum` COLLISION policy into a predicate: `Out[0] := E[i]` folds three writes (1,0,1).
  --   Real fold gives 2; the Boolean destination folds with ∃ and stays 1.
  let collide (decls : List Decl) :=
    mkPlainD decls (.scatter "Out" [.affine (.const 0)]
      { body := { terms := [{ factors := [.read "E" [.axis i]] }] }, nonlin := .identity }
      { fill := 0, reduce := .sum }) [("E", E)] [(1, 3)]
  match collide [.predicate "Out" [i]] with
  | .error e => throwError s!"shape 2 collide predicate: {e}"
  | .ok (_, Out) => unless Out.data == #[1] do throwError s!"shape 2 collide predicate: {repr Out.data}"
  match collide [] with
  | .error e => throwError s!"shape 2 collide real: {e}"
  | .ok (_, Out) => unless Out.data == #[2] do throwError s!"shape 2 collide real: {repr Out.data}"

-- Shape 2, the diagonal shape the Boolean path was always meant for: `predicate Eye(i,j);
--   Eye[i,i] := V[i]`, V = [1,1,1] is still the identity matrix (unchanged by the fix).
run_cmd do
  let i := ax "i" 1; let j := ax "j" 2
  let V := tensorOf [3] [1, 1, 1]
  let st : Stmt := .scatter "Eye" [.free i, .free i]
    { body := { terms := [{ factors := [.read "V" [.axis i]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  match mkPlainD [.predicate "Eye" [i, j]] st [("V", V)] [(1, 3)] with
  | .error e => throwError s!"shape 2 eye: {e}"
  | .ok (_, Eye) =>
      unless Eye.shape == [3, 3] && Eye.data == #[1, 0, 0, 0, 1, 0, 0, 0, 1] do
        throwError s!"shape 2 eye: {Eye.shape} {repr Eye.data}"

end LeanNCD.Eval
