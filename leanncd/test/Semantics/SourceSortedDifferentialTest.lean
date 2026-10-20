import LeanNCD.Semantics.Source.Admission

/-! S2b P2 (prototype): single-sort programs end to end (admission + selection -> oracle -> Core
leg -> ExtVal observation -> tropical profile -> production bits).

Declarations: axes `a` (4), `b` (3), `k` (7); `X[a] = [1,2,3,4]` (3), `W[b] = [1,10,100]` (4),
`Z[a,b] = 10a + b - 5` (5); `Y` (6). -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open Oracle

namespace SourceSortedDifferentialTest

private def a : AxisSpec := ⟨"a", 7, .real⟩
private def b : AxisSpec := ⟨"b", 8, .real⟩
private def k : AxisSpec := ⟨"k", 9, .real⟩

private def rhs (agg : AggOp) (terms : List (List Factor)) : RHSExpr :=
  ⟨⟨terms.map ProdTerm.mk⟩, .identity, agg⟩

private def zValues : List ℚ := [-5, -4, -3, 5, 6, 7, 15, 16, 17, 25, 26, 27]

private def snap (yAxes : List AxisSpec) (stmts : List Stmt)
    (xValues : List ℚ := [1, 2, 3, 4]) : SourceSnapshot :=
  let extent (ax : AxisSpec) : Nat := if ax.uid = 7 then 4 else if ax.uid = 8 then 3 else 7
  { resolved := {
      decls := [.axis a (some 4), .axis b (some 3), .axis k (some 7),
        .typedTensor .f64 "X" [a], .typedTensor .f64 "W" [b], .typedTensor .f64 "Z" [a, b],
        .typedTensor .f64 "Y" yAxes]
      stmts := stmts
      env := {}, extNames := ∅ }
    specs := [⟨3, .input, [4]⟩, ⟨4, .input, [3]⟩, ⟨5, .input, [4, 3]⟩,
      ⟨6, .output, yAxes.map extent⟩]
    inputs := [⟨3, [4], xValues⟩, ⟨4, [3], [1, 10, 100]⟩, ⟨5, [4, 3], zValues⟩] }

private def single (agg : AggOp) : SourceSnapshot :=
  snap [a] [.assign "Y" [.free a] (rhs agg [[.read "Z" [.axis a, .axis b]]])]

private def product (agg : AggOp) (xValues : List ℚ := [1, 2, 3, 4]) : SourceSnapshot :=
  snap [a] [.assign "Y" [.free a] (rhs agg [[.read "X" [.axis a], .read "W" [.axis b]]])]
    xValues

/-- `Y[2*a] := max X[a]` as a hand-built affine `.assign`: odd cells are empty fibers. -/
private def strided (agg : AggOp) : SourceSnapshot :=
  snap [k] [.assign "Y" [.affine (.scale 2 a)] (rhs agg [[.read "X" [.axis a]]])]

private def carrierOf (s : SourceSnapshot) : String :=
  match admitSourceSorted s with
  | .ok (_, S) => S.name
  | .error d => s!"refused {repr d.cause}"

/-! Q6: selection and admission. -/
/-- info: "real" -/
#guard_msgs in #eval carrierOf (single .sum)
/-- info: "maxPlus" -/
#guard_msgs in #eval carrierOf (single .max)
/-- info: "minPlus" -/
#guard_msgs in #eval carrierOf (single .min)
/-- info: "refused LeanNCD.Semantics.Source.SourceCause.sortSelection\n  (LeanNCD.Semantics.Source.Oracle.SelectionError.mixedSorts [LeanNCD.AggOp.sum, LeanNCD.AggOp.max])" -/
#guard_msgs in #eval carrierOf (snap [a] [.assign "Y" [.free a] (rhs .sum [[.read "X" [.axis a]]]),
  .assign "Y" [.free a] (rhs .max [[.read "Z" [.axis a, .axis b]]])])
/-- info: false -/
#guard_msgs in #eval (admitSourceAffine (single .max)).toOption.isSome
/-- info: "refused LeanNCD.Semantics.Source.SourceCause.unsupported (LeanNCD.Semantics.Source.UnsupportedSource.scatterPolicy)" -/
#guard_msgs in #eval carrierOf (snap [k] [.scatter "Y" [.affine (.scale 2 a)] (rhs .max [[.read "X" [.axis a]]])
  { reduce := .rejectCollisions }])

end SourceSortedDifferentialTest
