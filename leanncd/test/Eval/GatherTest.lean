import LeanNCD.Eval.Gather
namespace LeanNCD.Eval
open Std
private def ax (u : Nat) : AxisSpec := { name := "x", uid := u, kind := .real }
private def coordOf (ps : List (Nat × Int)) : HashMap UID Int := ps.foldl (fun m (u,v) => m.insert u v) {}
-- evalIdx:
#guard evalIdx (coordOf [(1,3),(2,1)]) (.affine 0 [(2, ax 1), (1, ax 2)]) == 7   -- 2*3 + 1
#guard evalIdx (coordOf [(1,0)]) (.shift (ax 1) (-1)) == -1                      -- look-back
#guard evalIdx (coordOf [(1,4)]) (.scale 2 (ax 1)) == 8
-- evalBool: |i - j| ≤ 1 at i=0,j=2 is false; at i=1,j=2 true
#guard ! evalBool (coordOf [(1,0),(2,2)]) (.rel .le (.iabs (.embed (.affine 0 [(1, ax 1),(-1, ax 2)]))) (.embed (.const 1)))
#guard   evalBool (coordOf [(1,1),(2,2)]) (.rel .le (.iabs (.embed (.affine 0 [(1, ax 1),(-1, ax 2)]))) (.embed (.const 1)))
-- gather: in-range read, out-of-range pad, iverson
run_cmd do
  let X := (DenseTensor.zeros [3]).set! [1] 5.0    -- X = [0,5,0]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  -- read X[i] at i=1 ⇒ 5.0
  match gather 0.0 1.0 env (coordOf [(1,1)]) (.read "X" [.axis (ax 1)]) with | .ok v => unless v == 5.0 do throwError "read" | .error e => throwError (toString e)
  -- read X[i-1] at i=0 ⇒ out of range ⇒ 0.0
  match gather 0.0 1.0 env (coordOf [(1,0)]) (.read "X" [.shift (ax 1) (-1)]) with | .ok v => unless v == 0.0 do throwError "pad" | .error e => throwError (toString e)
  -- iverson [i ≤ 2] at i=1 ⇒ 1.0
  match gather 0.0 1.0 env (coordOf [(1,1)]) (.iverson (.rel .le (.embed (.axis (ax 1))) (.embed (.const 2)))) with | .ok v => unless v == 1.0 do throwError "iverson" | .error e => throwError (toString e)

-- S3b T2: the statement's (0_K, 1_K) reach `gather`. A BARE out-of-range read pads with 0_K, an Iverson
-- factor is 1_K / 0_K, and an out-of-range read UNDER a `.unaryFn` is 0_K too in a tropical sort (the
-- function is not applied) but `f(0.0)` in a real/bool sort. Each max-plus row has a min-plus duality twin; the real/bool rows (0.0, 1.0) are the unchanged
-- accept-neighbours (they are the existing rows above, which now pass the real/bool constants).
private def negInf : Float := -1.0 / 0.0
private def posInf : Float := 1.0 / 0.0
private def okIs (r : Except EvalError Float) (x : Float) : Bool :=
  match r with | .ok v => v == x | .error _ => false
private def gEnv : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ((DenseTensor.zeros [3]).set! [1] 5.0)
private def padRead : Factor := .read "X" [.shift (ax 1) (-1)]          -- at i=0: out of range
private def inRead  : Factor := .read "X" [.axis (ax 1)]
private def padExp  : Factor := .unaryFn .exp "X" [.shift (ax 1) (-1)]  -- at i=0: exp of the pad
private def ivLe    : Factor := .iverson (.rel .le (.embed (.axis (ax 1))) (.embed (.const 2)))
private def ivGt    : Factor := .iverson (.rel .gt (.embed (.axis (ax 1))) (.embed (.const 2)))
-- bare OOB read: pad = 0_K
#guard okIs (gather negInf 0.0 gEnv (coordOf [(1,0)]) padRead) negInf   -- max-plus
#guard okIs (gather posInf 0.0 gEnv (coordOf [(1,0)]) padRead) posInf   -- min-plus
#guard okIs (gather 0.0 1.0 gEnv (coordOf [(1,0)]) padRead) 0.0         -- real / bool
-- in-range read is untouched by the sort
#guard okIs (gather negInf 0.0 gEnv (coordOf [(1,1)]) inRead) 5.0
#guard okIs (gather posInf 0.0 gEnv (coordOf [(1,1)]) inRead) 5.0
-- OOB read under a unary: 0_K, `exp` not applied, in a tropical sort (the pre-fix value was exp 0.0 = 1.0)
#guard okIs (gather negInf 0.0 gEnv (coordOf [(1,0)]) padExp) negInf
#guard okIs (gather posInf 0.0 gEnv (coordOf [(1,0)]) padExp) posInf
-- real / bool neighbour: the pad is the real 0.0 and `exp` is applied, exp 0.0 = 1.0 still contributes
#guard okIs (gather 0.0 1.0 gEnv (coordOf [(1,0)]) padExp) 1.0
-- in-range value under a unary in a tropical sort is still `exp` of the value (X[1] = 5.0), and a
-- stored -inf in range is NOT the OOB case: exp(-inf) = 0.0 is applied
#guard okIs (gather negInf 0.0 gEnv (coordOf [(1,1)]) (.unaryFn .exp "X" [.axis (ax 1)])) (Float.exp 5.0)
#guard okIs (gather negInf 0.0 (gEnv.insert "X" ((DenseTensor.zeros [3]).set! [1] negInf)) (coordOf [(1,1)])
  (.unaryFn .exp "X" [.axis (ax 1)])) 0.0
-- Iverson: true = 1_K, false = 0_K
#guard okIs (gather negInf 0.0 gEnv (coordOf [(1,1)]) ivLe) 0.0         -- max-plus true
#guard okIs (gather negInf 0.0 gEnv (coordOf [(1,1)]) ivGt) negInf      -- max-plus false
#guard okIs (gather posInf 0.0 gEnv (coordOf [(1,1)]) ivLe) 0.0         -- min-plus true
#guard okIs (gather posInf 0.0 gEnv (coordOf [(1,1)]) ivGt) posInf      -- min-plus false
#guard okIs (gather 0.0 1.0 gEnv (coordOf [(1,1)]) ivLe) 1.0            -- real / bool true
#guard okIs (gather 0.0 1.0 gEnv (coordOf [(1,1)]) ivGt) 0.0            -- real / bool false

-- `.ieq` semantics (the DSL's intended *modular* equality, currently APPROXIMATED by structural
-- Int `==`; see `evalBool` in Gather.lean). These lock in the actual behavior so a future switch
-- to faithful modular equality is a conscious, test-breaking change rather than silent drift.
-- equal values ⇒ true:
#guard   evalBool (coordOf [(1,3),(2,3)]) (.ieq (.embed (.axis (ax 1))) (.embed (.axis (ax 2))))
-- unequal values ⇒ false:
#guard ! evalBool (coordOf [(1,3),(2,4)]) (.ieq (.embed (.axis (ax 1))) (.embed (.axis (ax 2))))
-- APPROXIMATION BOUNDARY: 256 and 0 are equal mod 256 but not structurally; current Int-`==`
-- semantics ⇒ FALSE. A faithful modular `.ieq` would make this TRUE — that change must flip this guard.
#guard ! evalBool (coordOf [(1,256),(2,0)]) (.ieq (.embed (.axis (ax 1))) (.embed (.axis (ax 2))))
-- `.ieq` currently coincides with `.rel .eq` on non-wrapping values:
#guard (evalBool (coordOf [(1,5),(2,5)]) (.ieq (.embed (.axis (ax 1))) (.embed (.axis (ax 2))))
        == evalBool (coordOf [(1,5),(2,5)]) (.rel .eq (.embed (.axis (ax 1))) (.embed (.axis (ax 2)))))
end LeanNCD.Eval
