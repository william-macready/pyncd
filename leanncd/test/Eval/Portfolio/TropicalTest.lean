import Eval.Portfolio.Harness
import LSpec
/-!
# Portfolio §11 — Tropical / max-plus & min-plus semirings

`maxreduce`/`minreduce` combined with products for best/worst-path reachability. Since S3b-i
(task T1) the two aggregations are the true semirings max-plus `(+, max, −∞, 0)` and min-plus
`(+, min, +∞, 0)`: the factors of a term ADD (the surface `·` of a tropical statement is the
semiring product), then the NaN-propagating max/min is taken across terms and contracted axes.
(TR1/TR2/TR4 basic max-reductions are already covered elsewhere; not re-authored here.)
Each max-plus fixture has a negation-duality twin (`min-plus(x) = −max-plus(−x)`): the two
directions share one definition per layer, so a symmetric bug would pass a one-sorted suite.
-/
namespace LeanNCD.Eval
open Std LSpec

#lspec group "§11 — Tropical / max-plus & min-plus semirings" <|
-- TR3  max-plus "best path" 2-hop score: R[i,k]=max_j P[i,j]+P[j,k], P=[[0,0.9],[0.8,0]].
--   R[0,0]=max(0+0, 0.9+0.8)=1.7,  R[0,1]=max(0+0.9, 0.9+0)=0.9,
--   R[1,0]=max(0.8+0, 0+0.8)=0.8,  R[1,1]=max(0.8+0.9, 0+0)=1.7.
--   (Before S3b-i this was max-TIMES: [0.72, 0, 0, 0.72].)
test "TR3 best-path"
    (evalEqB (tlprog!{ R[i, k] := maxreduce(P[i, j] · P[j, k]) })
      (HashMap.ofList [("P", tl [2,2] [0,0.9, 0.8,0])])
      "R" (tl [2,2] [1.7,0.9, 0.8,1.7])) $

-- TR3d  duality twin of TR3: min-plus on the NEGATED data, expectation negated.
test "TR3d min-plus twin of TR3"
    (evalEqB (tlprog!{ R[i, k] := minreduce(P[i, j] · P[j, k]) })
      (HashMap.ofList [("P", tl [2,2] [0,-0.9, -0.8,0])])
      "R" (tl [2,2] [-1.7,-0.9, -0.8,-1.7])) $

-- TR6  basic min-reduction (min analog of TR1): C[i] = min_k A[i,k].
--   A=[[3,1,4],[1,5,9]] ⇒ C=[min(3,1,4), min(1,5,9)] = [1,1].
test "TR6 min-reduction"
    (evalEqB (tlprog!{ C[i] := minreduce(A[i, k]) })
      (HashMap.ofList [("A", tl [2,3] [3,1,4, 1,5,9])])
      "C" (tl [2] [1,1])) $

-- TR7  min-plus combine (min analog of TR2): C[i] = min_k A[i,k]+B[k].
--   A=[[3,1,4],[2,2,2]], B=[2,5,1] ⇒ sums row0=[5,6,5]→5, row1=[4,7,3]→3 ⇒ C=[5,3].
--   (Before S3b-i this was min-TIMES: [4, 2].)
test "TR7 min-plus"
    (evalEqB (tlprog!{ C[i] := minreduce(A[i, k] · B[k]) })
      (HashMap.ofList [("A", tl [2,3] [3,1,4, 2,2,2]), ("B", tl [3] [2,5,1])])
      "C" (tl [2] [5,3])) $

-- TR7d  duality twin of TR7: max-plus on the NEGATED data, expectation negated.
test "TR7d max-plus twin of TR7"
    (evalEqB (tlprog!{ C[i] := maxreduce(A[i, k] · B[k]) })
      (HashMap.ofList [("A", tl [2,3] [-3,-1,-4, -2,-2,-2]), ("B", tl [3] [-2,-5,-1])])
      "C" (tl [2] [-5,-3])) $

-- TR9  single-factor `maxreduce` (accept-neighbour: unchanged by the flip, there is no ⊗ to apply):
--   C[i] = max_k A[i,k], A=[[3,1,4],[-2,-5,-9]] ⇒ [4,-2]; TR9d is the min-plus twin on −A.
test "TR9 single-factor maxreduce"
    (evalEqB (tlprog!{ C[i] := maxreduce(A[i, k]) })
      (HashMap.ofList [("A", tl [2,3] [3,1,4, -2,-5,-9])])
      "C" (tl [2] [4,-2])) $

test "TR9d single-factor minreduce, negated twin"
    (evalEqB (tlprog!{ C[i] := minreduce(A[i, k]) })
      (HashMap.ofList [("A", tl [2,3] [-3,-1,-4, 2,5,9])])
      "C" (tl [2] [-4,2])) $

-- TR5  min-plus shortest path (Viterbi/Bellman step): D2[i,k] = min_j D[i,j]+D[j,k] on the 3-node
--   graph D=[[0,1,5],[9,0,2],[3,9,0]]. It was an [F] gap (min-plus needed `+` as the within-term
--   combine); with S3b-i it is the same `minreduce(A · B)` surface. Two-hop improvements:
--   D2[0,2]=min(0+5, 1+2, 5+0)=3 (via node 1) and D2[1,0]=min(9+0, 0+9, 2+3)=5 (via node 2).
--   row0=[0,1,3], row1=[5,0,2], row2=[3,4,0].
test "TR5 min-plus shortest path"
    (evalEqB (tlprog!{ D2[i, k] := minreduce(D[i, j] · D[j, k]) })
      (HashMap.ofList [("D", tl [3,3] [0,1,5, 9,0,2, 3,9,0])])
      "D2" (tl [3,3] [0,1,3, 5,0,2, 3,4,0])) $

-- TR5d  duality twin of TR5: max-plus (longest 2-hop path) on the negated graph, negated.
test "TR5d max-plus twin of TR5"
    (evalEqB (tlprog!{ D2[i, k] := maxreduce(D[i, j] · D[j, k]) })
      (HashMap.ofList [("D", tl [3,3] [0,-1,-5, -9,0,-2, -3,-9,0])])
      "D2" (tl [3,3] [0,-1,-3, -5,0,-2, -3,-4,0]))

end LeanNCD.Eval
