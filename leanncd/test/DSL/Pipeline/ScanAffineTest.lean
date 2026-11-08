-- test/DSL/Pipeline/ScanAffineTest.lean
import LeanNCD.DSL.Compile
namespace LeanNCD
open Lean

-- helper: compile + check whether any routed step has the given op
private def hasOp (p : TLProgram) (op : BrOp) : Bool :=
  match TLProgram.compile p |>.run 0 with
  | .ok tc _ => tc.steps.any (·.op == op)
  | .error _ _ => false

-- AFFINE scan: identity-nonlin recurrence ⇒ op = .scanAffine.
private def affineScan : TLProgram := tlprog!{
  iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l] · A[j, k]
}
#guard hasOp affineScan BrOp.scanAffine
#guard ! hasOp affineScan BrOp.scan          -- not the plain tag

-- NONLINEAR scan: relu recurrence ⇒ op = .scan (NOT .scanAffine).
private def reluScan : TLProgram := tlprog!{
  iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := relu(S[j, l] · A[j, k])
}
#guard hasOp reluScan .scan
#guard ! hasOp reluScan .scanAffine

-- Affine-ness is decided by the recurrence body only. A nonlinear POST-SCAN statement (it does not
-- feed the recurrence, so it is emitted after the scan, not folded into the body) must not make the
-- scan non-affine: the scratch `Sc` and the read-out table `Yr` are both post.
private def affineScanNonlinPost : TLProgram := tlprog!{
  iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l] · A[j, k]
  Sc[j]      := relu(S[j, l])
  Yr[j, l]   := relu(S[j, l])
}
#guard hasOp affineScanNonlinPost .scanAffine
#guard ! hasOp affineScanNonlinPost .scan

-- Neighbour: the SAME nonlinear statement, once the recurrence reads it (a per-step intermediate in
-- the body), does make the scan non-affine.
private def reluScanFedInter : TLProgram := tlprog!{
  iter l = 3
  S[j, 0]    := X[j]
  T[j]       := relu(S[j, l])
  S[j, l +1] := T[j]
}
#guard hasOp reluScanFedInter .scan
#guard ! hasOp reluScanFedInter .scanAffine
end LeanNCD
