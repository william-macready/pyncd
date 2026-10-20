import LeanNCD.Semantics.Source.Admission

/-! S2b: audit rows for the sorted admission entry (plan section 3, rows 7, 9, 10, 13): the cells
that the Q6 rows of `SourceSortedDifferentialTest` leave without a fixture. The helpers are cloned
from that file (same declarations: axes `a` (4), `b` (3), `k` (7); inputs `X`, `W`, `Z`; output `Y`). -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open Oracle

namespace SourceSortedAuditTest

private def a : AxisSpec := ⟨"a", 7, .real⟩
private def b : AxisSpec := ⟨"b", 8, .real⟩
private def k : AxisSpec := ⟨"k", 9, .real⟩

private def rhs (agg : AggOp) (terms : List (List Factor)) : RHSExpr :=
  ⟨⟨terms.map ProdTerm.mk⟩, .identity, agg⟩

private def zValues : List ℚ := [-5, -4, -3, 5, 6, 7, 15, 16, 17, 25, 26, 27]

private def snap (yAxes : List AxisSpec) (stmts : List Stmt) : SourceSnapshot :=
  let extent (ax : AxisSpec) : Nat := if ax.uid = 7 then 4 else if ax.uid = 8 then 3 else 7
  { resolved := {
      decls := [.axis a (some 4), .axis b (some 3), .axis k (some 7),
        .typedTensor .f64 "X" [a], .typedTensor .f64 "W" [b], .typedTensor .f64 "Z" [a, b],
        .typedTensor .f64 "Y" yAxes]
      stmts := stmts
      env := {}, extNames := ∅ }
    specs := [⟨3, .input, [4]⟩, ⟨4, .input, [3]⟩, ⟨5, .input, [4, 3]⟩,
      ⟨6, .output, yAxes.map extent⟩]
    inputs := [⟨3, [4], [1, 2, 3, 4]⟩, ⟨4, [3], [1, 10, 100]⟩, ⟨5, [4, 3], zValues⟩] }

private def strided (agg : AggOp) : SourceSnapshot :=
  snap [k] [.assign "Y" [.affine (.scale 2 a)] (rhs agg [[.read "X" [.axis a]]])]

/-- A bare-slot (`Y[a]`) scatter of `Z[a,b]`, reducing with `reduce`. -/
private def bareScatter (agg : AggOp) : SourceSnapshot :=
  snap [a] [.scatter "Y" [.free a] (rhs agg [[.read "Z" [.axis a, .axis b]]])
    { reduce := .rejectCollisions }]

private def isPolicy : SourceCause → Bool | .unsupported .scatterPolicy => true | _ => false
private def isNonSum : SourceCause → Bool | .unsupported .nonSum => true | _ => false

private def causeIs {α : Type _} (p : SourceCause → Bool) : Except SourceDiagnostic α → Bool
  | .error d => p d.cause
  | .ok _ => false

private def selected (s : SourceSnapshot) : String :=
  match admitSourceSorted s with
  | .ok (_, S) => S.name
  | .error d => s!"refused {repr d.cause}"

/-! Row 7: admission refuses before selection. A sum assign followed by an affine max scatter is
BOTH a mix and a policy refusal; the statement's own cause (`scatterPolicy`) is reported, never
`sortSelection`. -/
#guard causeIs isPolicy (admitSourceSorted (snap [a]
  [.assign "Y" [.free a] (rhs .sum [[.read "X" [.axis a]]]),
   .scatter "Y" [.affine (.scale 2 a)] (rhs .max [[.read "X" [.axis a]]])
     { reduce := .rejectCollisions }]))

/-! Row 9: the tropical scatter guard fires before the bare/affine slot split. -/
#guard causeIs isPolicy (admitSourceSorted (bareScatter .max))
#guard causeIs isPolicy (admitSourceSorted (bareScatter .min))

/-! Row 10: accept-neighbour. The same bare scatter with `sum` is still admitted and selects `real`:
the sorted flag must not over-refuse. -/
#guard selected (bareScatter .sum) == "real"

/-! Row 13: the unsorted affine entry refuses a tropical affine `.assign` at its SECOND `nonSum`
site (`admitAffineWrite`). -/
#guard causeIs isNonSum (admitSourceAffine (strided .max))
#guard causeIs isNonSum (admitSourceAffine (strided .min))

end SourceSortedAuditTest
