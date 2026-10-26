import Eval.Portfolio.Harness
import LSpec
/-!
# Portfolio §5 — Convolution & pooling

Numeric cross-checks for affine (windowed/dilated/strided) reads, max-pooling via
`maxreduce`, avg-pooling as a weighted sum, global sum-pool, and depthwise vs full
multi-channel convolution.  (CV3 strided conv is already covered by
`Eval.EvalExamplesTest`; not re-authored here.)
-/
namespace LeanNCD.Eval
open Std LSpec

#lspec group "§5 — Convolution & pooling" <|
-- CV1  1-D valid convolution: Y[i] = Σ_p W[p]·X[i+p] = X[i]+X[i+1]
--   X=[1,2,3,4] ⇒ [1+2, 2+3, 3+4] = [3,5,7]
test "CV1 conv1d"
    (evalEqB (tlprog!{ Y[i] := W[p] · X[i + p] })
      (HashMap.ofList [("W", tl [2] [1,1]), ("X", tl [4] [1,2,3,4])])
      "Y" (tl [3] [3,5,7])) $

-- CV2  2-D convolution with W=I₂: Y[i,j] = X[i,j] + X[i+1,j+1]
--   X=[[1,2,3],[4,5,6],[7,8,9]] ⇒ [[1+5,2+6],[4+8,5+9]] = [[6,8],[12,14]]
test "CV2 conv2d"
    (evalEqB (tlprog!{ Y[i, j] := W[p, q] · X[i + p, j + q] })
      (HashMap.ofList [("W", tl [2,2] [1,0, 0,1]),
                   ("X", tl [3,3] [1,2,3, 4,5,6, 7,8,9])])
      "Y" (tl [2,2] [6,8, 12,14])) $

-- CV4  dilated conv (dilation 2): Y[i] = Σ_p W[p]·X[i+2p] = X[i]+X[i+2]
--   X=[0,1,2,3,4] ⇒ [0+2, 1+3, 2+4] = [2,4,6]
test "CV4 dilated-conv"
    (evalEqB (tlprog!{ Y[i] := W[p] · X[i + 2 * p] })
      (HashMap.ofList [("W", tl [2] [1,1]), ("X", tl [5] [0,1,2,3,4])])
      "Y" (tl [3] [2,4,6])) $

-- CV5  max-pool stride-2 window-2: P[i] = max_p X[2i+p], p∈{0,1}.
--   p is otherwise unconstrained (single affine read over two free axes ⇒ solver
--   underdetermined), so it is pinned with `axis p : ℕ = 2` per the DSL reminder.
--   X=[1,3,2,5] ⇒ [max(1,3), max(2,5)] = [3,5]
test "CV5 maxpool"
    (evalEqB (tlprog!{
    axis p : ℕ = 2
    P[i] := maxreduce(X[2 * i + p])
  })
      (HashMap.ofList [("X", tl [4] [1,3,2,5])])
      "P" (tl [2] [3,5])) $

-- CV5o  S3b T2: max-pool whose window runs off the end. A bare out-of-range read is padded with 0_K
--   of the statement's sort (`−∞` for max-plus), so the padded cell never wins. Window 3 stride 2:
--   P[i] = max_p X[2i+p], p∈{0,1,2}; X=[-1,-3,-2,-5] all negative, i=1 reads X[2],X[3],X[4] (X[4] is
--   out of range) ⇒ P = [max(-1,-3,-2), max(-2,-5,pad)] = [-1,-2]. (Before T2 the pad was the real 0
--   and won: P = [-1, 0].)
test "CV5o maxpool, padded window (max-plus pad -inf)"
    (evalEqB (tlprog!{
    axis i : ℕ = 2, p : ℕ = 3
    P[i] := maxreduce(X[2 * i + p])
  })
      (HashMap.ofList [("X", tl [4] [-1,-3,-2,-5])])
      "P" (tl [2] [-1,-2])) $

-- CV5od  duality twin of CV5o: min-pool on the negated data, pad `+∞`; P = [1, 2].
test "CV5od minpool, padded window (min-plus pad +inf)"
    (evalEqB (tlprog!{
    axis i : ℕ = 2, p : ℕ = 3
    P[i] := minreduce(X[2 * i + p])
  })
      (HashMap.ofList [("X", tl [4] [1,3,2,5])])
      "P" (tl [2] [1,2])) $

-- CV5r  accept-neighbour, real statement: the same padded window under a sum keeps the real pad 0:
--   P = [1+3+2, 2+5+0] = [6,7].
test "CV5r sum over padded window (real pad 0)"
    (evalEqB (tlprog!{
    axis i : ℕ = 2, p : ℕ = 3
    P[i] := X[2 * i + p]
  })
      (HashMap.ofList [("X", tl [4] [1,3,2,5])])
      "P" (tl [2] [6,7])) $

-- CV5b  accept-neighbour, bool statement: the pad is `false`. E=[1,0,0,0]: B[0]=∃p E[p]=1, and
--   B[1]=∃p E[2+p] reads E[2],E[3],pad = 0 (a `true` pad would make it 1) ⇒ B=[1,0].
test "CV5b bool statement pads false"
    (evalEqB (tlprog!{
    axis i : ℕ = 2, p : ℕ = 3
    predicate E(j), B(i)
    B[i] := E[2 * i + p]
  })
      (HashMap.ofList [("E", tl [4] [1,0,0,0])])
      "B" (tl [2] [1,0])) $

-- CV5u  OOB under a UNARY inside a tropical statement is 0_K, NOT f(0): the factor is absent and `exp`
--   is not applied to the pad. max-plus, X=[-1,-3,-2,-5]: P[0]=max(e^-1,e^-3,e^-2)=e^-1≈0.3678794,
--   P[1]=max(e^-2,e^-5,absent)=e^-2≈0.1353 (the pre-fix `exp(0)=1` pad would have WON: P[1]=1).
test "CV5u OOB under exp in max-plus is absent (0_K), exp(0) does not win"
    (evalEqB (tlprog!{
    axis i : ℕ = 2, p : ℕ = 3
    P[i] := maxreduce(exp(X[2 * i + p]))
  })
      (HashMap.ofList [("X", tl [4] [-1,-3,-2,-5])])
      "P" (tl [2] [0.36787944117144233, 0.1353352832366127])) $

-- CV5ud  min-plus twin: X=[1,3,2,5], P[0]=min(e,e^3,e^2)=e≈2.7182818, P[1]=min(e^2,e^5,absent)=e^2≈7.389
--   (the pre-fix `exp(0)=1` pad would have WON: P[1]=1).
test "CV5ud OOB under exp in min-plus is absent (0_K), exp(0) does not win"
    (evalEqB (tlprog!{
    axis i : ℕ = 2, p : ℕ = 3
    P[i] := minreduce(exp(X[2 * i + p]))
  })
      (HashMap.ofList [("X", tl [4] [1,3,2,5])])
      "P" (tl [2] [2.718281828459045, 7.38905609893065])) $

-- CV5ur  accept-neighbour, REAL statement: the same padded window under `exp` and a sum keeps the real pad
--   0 then applies `exp`: X=0, P[0]=3, P[1]=exp(0)+exp(0)+exp(pad 0)=3 (an absent pad would give 2).
test "CV5ur sum of exp over padded window (pad 0, exp(0)=1 contributes)"
    (evalEqB (tlprog!{
    axis i : ℕ = 2, p : ℕ = 3
    P[i] := exp(X[2 * i + p])
  })
      (HashMap.ofList [("X", tl [4] [0,0,0,0])])
      "P" (tl [2] [3,3])) $

-- CV6  avg-pool as weighted sum: P[i] = Σ_p X[2i+p]·w[p]
--   w=[0.5,0.5], X=[2,4,6,8] ⇒ [0.5·2+0.5·4, 0.5·6+0.5·8] = [3,7]
test "CV6 avgpool"
    (evalEqB (tlprog!{ P[i] := X[2 * i + p] · w[p] })
      (HashMap.ofList [("w", tl [2] [0.5,0.5]), ("X", tl [4] [2,4,6,8])])
      "P" (tl [2] [3,7])) $

-- CV7  global sum-pool (contract all): s = Σ_i X[i]
--   X=[1,2,3,4] ⇒ 1+2+3+4 = 10
test "CV7 sumpool"
    (evalEqB (tlprog!{ s[] := X[i] })
      (HashMap.ofList [("X", tl [4] [1,2,3,4])])
      "s" (tl [] [10])) $

-- CV8  depthwise conv: channel c free on BOTH W and X, only p contracted.
--   Y[c,i] = Σ_p W[c,p]·X[c,i+p]
--   c=0: W[0]=[1,1]  ⇒ [X00+X01, X01+X02] = [1+2, 2+3] = [3,5]
--   c=1: W[1]=[1,-1] ⇒ [X10−X11, X11−X12] = [4−5, 5−6] = [-1,-1]
test "CV8 depthwise"
    (evalEqB (tlprog!{ Y[c, i] := W[c, p] · X[c, i + p] })
      (HashMap.ofList [("W", tl [2,2] [1,1, 1,-1]),
                   ("X", tl [2,3] [1,2,3, 4,5,6])])
      "Y" (tl [2,2] [3,5, -1,-1])) $

-- CV9  full multi-channel conv: contracts input-channel ci AND kernel p; out-channel co free.
--   Y[co,i] = Σ_{ci,p} W[co,ci,p]·X[ci,i+p].  W[0]=[[1,0],[0,1]] (indexed [ci,p])
--   ⇒ Y[0,i] = X[0,i] + X[1,i+1] = [1+5, 2+6] = [6,8]
test "CV9 multichannel"
    (evalEqB (tlprog!{ Y[co, i] := W[co, ci, p] · X[ci, i + p] })
      (HashMap.ofList [("W", tl [1,2,2] [1,0, 0,1]),
                   ("X", tl [2,3] [1,2,3, 4,5,6])])
      "Y" (tl [1,2] [6,8]))

end LeanNCD.Eval
