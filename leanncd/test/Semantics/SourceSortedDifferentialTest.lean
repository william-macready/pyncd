import LeanNCD.Semantics.Source.SortedDifferential

/-! S2b: single-sort programs end to end (admission + selection -> oracle -> Core
leg -> ExtVal observation -> tropical profile -> production bits).

Declarations: axes `a` (4), `b` (3), `k` (7); `X[a] = [1,2,3,4]` (3), `W[b] = [1,10,100]` (4),
`Z[a,b] = 10a + b - 5` (5); `Y` (6). -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open Oracle SortedDifferential

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

private def run (s : SourceSnapshot) : Except SourceDiagnostic SortedRun :=
  compareSortedSource s (some [6])

private def yCore (s : SourceSnapshot) : String :=
  match run s with
  | .ok r => match r.core with
    | .ok ts => toString (repr ((ts.find? (·.declaration == 6)).map (·.values)))
    | .error e => e
  | .error d => s!"refused {repr d.cause}"

private def classOf (s : SourceSnapshot) : String :=
  match run s with
  | .ok r => toString (repr r.classification)
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

/-! Q5: Core leg values (must equal the oracle: `published` agreement is in the classification). -/
/-- info: "some [some -3, some 7, some 17, some 27]" -/
#guard_msgs in #eval yCore (single .max)
/-- info: "some [some -5, some 5, some 15, some 25]" -/
#guard_msgs in #eval yCore (single .min)
/-- info: "some [some 101, some 102, some 103, some 104]" -/
#guard_msgs in #eval yCore (product .max)
/-- info: "some [some 1, some -inf, some 2, some -inf, some 3, some -inf, some 4]" -/
#guard_msgs in #eval yCore (strided .max)
/-- info: "some [some 1, some +inf, some 2, some +inf, some 3, some +inf, some 4]" -/
#guard_msgs in #eval yCore (strided .min)
/-- info: "some [some -12, some 18, some 48, some 78]" -/
#guard_msgs in #eval yCore (single .sum)

/-! Q7/Q8: classification against production. -/
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (single .sum)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (single .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (single .min)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.nativeDiscrepancy\n  (LeanNCD.Semantics.Source.SortedDifferential.LegResult.mismatch\n    { declaration := 6, coordinate := [0], expected := 4636807660098813952, observed := 4636737291354636288 })\n  (LeanNCD.Semantics.Source.SortedDifferential.LegResult.mismatch\n    { declaration := 6, coordinate := [0], expected := 4636807660098813952, observed := 4636737291354636288 })" -/
#guard_msgs in #eval classOf (product .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.nativeDiscrepancy\n  (LeanNCD.Semantics.Source.SortedDifferential.LegResult.mismatch\n    { declaration := 6, coordinate := [0], expected := 4611686018427387904, observed := 4607182418800017408 })\n  (LeanNCD.Semantics.Source.SortedDifferential.LegResult.mismatch\n    { declaration := 6, coordinate := [0], expected := 4611686018427387904, observed := 4607182418800017408 })" -/
#guard_msgs in #eval classOf (product .min)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.nativeFailure\n  (LeanNCD.Semantics.Source.SortedDifferential.LegResult.failure\n    \"legacy evalPlain: scatter Y aggregates with max but fills unwritten cells with a finite value, not the -inf identity\")\n  (LeanNCD.Semantics.Source.SortedDifferential.LegResult.failure \"checked preparation\")" -/
#guard_msgs in #eval classOf (strided .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.unsupportedNumericalProfile\n  (LeanNCD.Semantics.Source.NumericalProfile.Unsupported.outsideEnvelope\n    { origin := { side := LeanNCD.Semantics.Source.SourceSide.read,\n                  declaration := none,\n                  statement := some 0,\n                  term := some 0,\n                  factor := none,\n                  slot := none },\n      coordinate := [0],\n      assignment := [(7, 0), (8, 0)],\n      slots := [],\n      cell := none }\n    (LeanNCD.Semantics.Source.NumericalProfile.ValueKind.subsetProductBound)\n    1048577\n    1048576)" -/
#guard_msgs in #eval classOf (product .max [1048576, 2, 3, 4])

/-! Q8: the existing real harness still refuses a tropical program loudly at admission. -/
/-- info: "LeanNCD.Semantics.Source.SourceCause.unsupported (LeanNCD.Semantics.Source.UnsupportedSource.nonSum)" -/
#guard_msgs in #eval match compareSource (single .max) (some [6]) with
  | .error (.admission d) => toString (repr d.cause)
  | _ => "ran"

/-! The `±inf` bit patterns, pinned against Lean's own IEEE `Float`. No row above compares an
infinite cell with production (production refuses every program that yields one). -/
#guard ExtClass.negInf.bits == (-(1.0 / 0.0) : Float).toBits
#guard ExtClass.posInf.bits == (1.0 / 0.0 : Float).toBits

end SourceSortedDifferentialTest
