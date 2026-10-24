import LeanNCD.Semantics.Source.Admission

/-! S2a admission of non-bare writes (`admitSourceAffine`).

Every refusal has an accept-neighbour differing in one field (the destination axis extent, a
slot constant, a scatter option or a read slot). The default entry `admitSource` keeps refusing
affine and scatter writes with its old causes. -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source

namespace SourceAdmissionAffineTest

private def a : AxisSpec := ⟨"a", 7, .real⟩
private def b : AxisSpec := ⟨"b", 8, .real⟩
private def k : AxisSpec := ⟨"k", 9, .real⟩

private def rhs (terms : List (List Factor)) : RHSExpr :=
  ⟨⟨terms.map ProdTerm.mk⟩, .identity, .sum⟩

private def readX : RHSExpr := rhs [[.read "X" [.axis a]]]

/-- `|a| = 2`, `|b| = 3`, `|k| = kExtent`; input `X[a] = [3, 5]` (declaration 3), output `Y`
over `yAxes` (declaration 4). -/
private def snap (kExtent : Nat) (yAxes : List AxisSpec) (stmt : Stmt) : SourceSnapshot :=
  let extent (ax : AxisSpec) : Nat :=
    if ax.uid = 7 then 2 else if ax.uid = 8 then 3 else kExtent
  { resolved := {
      decls := [.axis a (some 2), .axis b (some 3), .axis k (some kExtent),
        .typedTensor .f64 "X" [a], .typedTensor .f64 "Y" yAxes]
      stmts := [stmt]
      env := {}, extNames := ∅ }
    specs := [⟨3, .input, [2]⟩, ⟨4, .output, yAxes.map extent⟩]
    inputs := [⟨3, [2], [3, 5]⟩] }

private def coords : (sh : Shape) → List (Coord sh)
  | [] => [()]
  | ax :: sh => (List.finRange ax.extent).flatMap fun i => (coords sh).map fun w => (i, w)

/-- Forms, support indices, the distinct destination images over the source box, and whether
the forms reproduce `dest` at every source coordinate (`FormsSpec`, checked numerically). -/
private def view (r : Except SourceDiagnostic AdmittedSource) :
    Option (List (List WriteForm × List UID × List (List Int) × Bool)) :=
  r.toOption.map fun s => s.statements.map fun st =>
    let images := (coords s.source.context.axes).map fun w =>
      (coordValues (st.output.dest (st.output.sourceSlots.project w)),
        st.output.forms.map (writeValue · (coordLookup w)))
    (st.output.forms, st.output.indices, (images.map Prod.fst).dedup,
      images.all fun (d, f) => d == f)

private def refused (r : Except SourceDiagnostic AdmittedSource) (origin : SourceOrigin)
    (p : SourceCause → Bool) : Bool :=
  match r with
  | .error e => e.origin == origin && p e.cause
  | .ok _ => false

private def outSlot (j : Nat) : SourceOrigin :=
  { side := .output, declaration := some 4, statement := some 0, slot := some j }

private def isOutOfRange : SourceCause → Bool | .writeOutOfRange => true | _ => false
private def isAffine : SourceCause → Bool | .unsupported .affine => true | _ => false
private def isScatter : SourceCause → Bool | .unsupported .scatter => true | _ => false
private def isNonSum : SourceCause → Bool | .unsupported .nonSum => true | _ => false
private def nonSumOrigin : SourceOrigin := { side := .output, statement := some 0 }

/-! (a) FLIP. `Y[a+1] := X[a]`, `Y` over `a` (extent 2): images 1, 2; 2 is out of range. -/
private def shifted : SourceSnapshot := snap 3 [a] (.assign "Y" [.affine (.shift a 1)] readX)

#guard refused (admitSourceAffine shifted) (outSlot 0) isOutOfRange
#guard refused (admitSource shifted) (outSlot 0) isAffine

/-! (b) accept-neighbour: the same write into `Y` over `k`, extent 3 (2 refuses). -/
#guard view (admitSourceAffine (snap 3 [k] (.assign "Y" [.affine (.shift a 1)] readX))) ==
  some [([(1, [(1, 7)])], [7], [[1], [2]], true)]
#guard refused (admitSourceAffine (snap 2 [k] (.assign "Y" [.affine (.shift a 1)] readX)))
  (outSlot 0) isOutOfRange
#guard refused (admitSource (snap 3 [k] (.assign "Y" [.affine (.shift a 1)] readX)))
  (outSlot 0) isAffine

/-! (c) `.scale`, `.const`, two-axis and diagonal slots. -/
-- `Y[2*a] := X[a]`, `|k| = 3`: images 0, 2. `|k| = 2` refuses.
#guard view (admitSourceAffine (snap 3 [k] (.assign "Y" [.affine (.scale 2 a)] readX))) ==
  some [([(0, [(2, 7)])], [7], [[0], [2]], true)]
#guard refused (admitSourceAffine (snap 2 [k] (.assign "Y" [.affine (.scale 2 a)] readX)))
  (outSlot 0) isOutOfRange

-- `Y[2, a] := X[a]`, `Y` over `[k, a]`, `|k| = 3`: constant row 2. `Y[3, a]` refuses at slot 0.
#guard view (admitSourceAffine (snap 3 [k, a]
    (.assign "Y" [.affine (.const 2), .free a] readX))) ==
  some [([(2, []), (0, [(1, 7)])], [7], [[2, 0], [2, 1]], true)]
#guard refused (admitSourceAffine (snap 3 [k, a]
    (.assign "Y" [.affine (.const 3), .free a] readX))) (outSlot 0) isOutOfRange

-- `Y[a+b] := X[a]`, `|k| = 4`: images 0..3, support [a, b]. `|k| = 3` refuses.
#guard view (admitSourceAffine (snap 4 [k]
    (.assign "Y" [.affine (.affine 0 [(1, a), (1, b)])] readX))) ==
  some [([(0, [(1, 7), (1, 8)])], [7, 8], [[0], [1], [2], [3]], true)]
#guard refused (admitSourceAffine (snap 3 [k]
    (.assign "Y" [.affine (.affine 0 [(1, a), (1, b)])] readX))) (outSlot 0) isOutOfRange

-- Diagonal `Y[a, a] := X[a]`: already admitted by `admitSource` before S2a (bare path,
-- `dest = id`); both entries agree, with single forms.
private def diagonal : SourceSnapshot := snap 3 [a, a] (.assign "Y" [.free a, .free a] readX)
#guard view (admitSource diagonal) ==
  some [([(0, [(1, 7)]), (0, [(1, 7)])], [7, 7], [[0, 0], [1, 1]], true)]
#guard view (admitSourceAffine diagonal) == view (admitSource diagonal)

/-! (d) scatter. Collisions sum (S3a; the `fill`/`reduce` options are gone), so a scatter on a real
program is admitted with the same forms and images as an assign, and (S3b T7) so is a `max`/`min`
scatter under a sorted (tropical) program. -/
private def scatter : SourceSnapshot :=
  snap 3 [k] (.scatter "Y" [.affine (.scale 2 a)] readX)

private def policyOrigin : SourceOrigin := { statement := some 0 }

private def scaleView : Option (List (List WriteForm × List UID × List (List Int) × Bool)) :=
  some [([(0, [(2, 7)])], [7], [[0], [2]], true)]

#guard view (admitSourceAffine scatter) == scaleView
#guard refused (admitSource scatter) policyOrigin isScatter

-- S3b T7: a `max` aggregation on a `.scatter` under `sorted` is ADMITTED as its sort-free
-- structure (the same view as the `sum` scatter; the aggregation is the carrier key). Neighbours:
-- the same statement unsorted (refused, `nonSum`), and a `sum` aggregation sorted (admits).
private def maxRhs : RHSExpr := ⟨⟨[⟨[.read "X" [.axis a]]⟩]⟩, .identity, .max⟩
private def maxScatter : SourceSnapshot :=
  snap 3 [k] (.scatter "Y" [.affine (.scale 2 a)] maxRhs)
#guard view (admitSourceAffine maxScatter (sorted := true)) == scaleView
#guard refused (admitSourceAffine maxScatter) nonSumOrigin isNonSum   -- unsorted: `nonSum`
#guard view (admitSourceAffine scatter (sorted := true)) == scaleView
-- A bare scatter goes through the bare path.
#guard view (admitSourceAffine (snap 3 [a] (.scatter "Y" [.free a] readX))) ==
  some [([(0, [(1, 7)])], [7], [[0], [1]], true)]

/-! (e) affine READ slots stay refused under both entries (neighbour: the `.scale` fixture in
(c), which reads `X[a]`). -/
private def readOrigin : SourceOrigin :=
  { side := .read, declaration := some 3, statement := some 0, term := some 0,
    factor := some 0, slot := some 0 }

private def shiftedRead : RHSExpr := rhs [[.read "X" [.shift a 1]]]

#guard refused (admitSource (snap 3 [a] (.assign "Y" [.free a] shiftedRead))) readOrigin isAffine
#guard refused (admitSourceAffine (snap 3 [a] (.assign "Y" [.free a] shiftedRead)))
  readOrigin isAffine
#guard refused (admitSourceAffine (snap 3 [k] (.assign "Y" [.affine (.scale 2 a)] shiftedRead)))
  readOrigin isAffine

/-! (f) the BLAMED destination slot and the rank check (added after mutation cycles T2-M1 and
T2-M10 survived: every earlier out-of-range fixture failed at slot 0, and no fixture wrote a
different number of slots than the destination's rank). -/
private def isRank (expected actual : Nat) : SourceCause → Bool
  | .rank e r => e == expected && r == actual
  | _ => false

-- `Y[a, a+1] := X[a]`, `Y` over `[a, k]`: slot 0 fits, slot 1 images 1, 2 (`|k| = 2`).
-- The blame is slot 1, not slot 0. Neighbour: `|k| = 3` admits.
#guard refused (admitSourceAffine (snap 2 [a, k]
    (.assign "Y" [.free a, .affine (.shift a 1)] readX))) (outSlot 1) isOutOfRange
#guard view (admitSourceAffine (snap 3 [a, k]
    (.assign "Y" [.free a, .affine (.shift a 1)] readX))) ==
  some [([(0, [(1, 7)]), (1, [(1, 7)])], [7], [[0, 1], [1, 2]], true)]

-- Rank: two slots written into a rank-1 `Y`, and one slot into a rank-2 `Y`. The refusal is
-- `.rank <destination rank> <slot count>` at slot `min` of the two. Neighbour: the matching
-- rank (the `.scale` fixture in (c)) admits.
#guard refused (admitSourceAffine (snap 3 [k]
    (.assign "Y" [.free a, .affine (.scale 1 a)] readX))) (outSlot 1) (isRank 1 2)
#guard refused (admitSourceAffine (snap 3 [a, k]
    (.assign "Y" [.affine (.shift a 0)] readX))) (outSlot 1) (isRank 2 1)

end SourceAdmissionAffineTest

namespace SourceAdmissionAffineTest

/-! (g) NEGATIVE and MIXED-SIGN images (added after the T2 review: every earlier fixture had
non-negative coefficients and failed only the UPPER bound). `|a| = 2`, `|b| = 3`. -/

-- `Y[a-1] := X[a]` into `|k| = 9`: images -1, 0. The upper bound is far away, so only the lower
-- bound `0 ≤ image` refuses (kills: deleting the `0 ≤` conjunct, which `Int.toNat` would turn
-- into a silent alias of cell 0). Neighbour: `Y[a+0]` into the same `Y` admits.
#guard refused (admitSourceAffine (snap 9 [k] (.assign "Y" [.affine (.shift a (-1))] readX)))
  (outSlot 0) isOutOfRange
#guard view (admitSourceAffine (snap 9 [k] (.assign "Y" [.affine (.shift a 0)] readX))) ==
  some [([(0, [(1, 7)])], [7], [[0], [1]], true)]
-- Negative scale: `Y[-a]`, images 0, -1.
#guard refused (admitSourceAffine (snap 9 [k] (.assign "Y" [.affine (.scale (-1) a)] readX)))
  (outSlot 0) isOutOfRange

-- Mixed sign `Y[a-b] := X[a]`, `|k| = 9`: images -2..1, the minimum at the corner (a, b) = (0, 2).
-- Refused although the maximum (1) fits. Neighbour `Y[2+a-b]`: images 0..3, admitted at
-- `|k| = 4` and refused at `|k| = 3` (image 3, the maximum at the corner (1, 0)).
#guard refused (admitSourceAffine (snap 9 [k]
    (.assign "Y" [.affine (.affine 0 [(1, a), (-1, b)])] readX))) (outSlot 0) isOutOfRange
#guard view (admitSourceAffine (snap 4 [k]
    (.assign "Y" [.affine (.affine 2 [(1, a), (-1, b)])] readX))) ==
  some [([(2, [(1, 7), (-1, 8)])], [7, 8], [[0], [3], [2], [1]], true)]
#guard refused (admitSourceAffine (snap 3 [k]
    (.assign "Y" [.affine (.affine 2 [(1, a), (-1, b)])] readX))) (outSlot 0) isOutOfRange

-- Negative coefficient whose image fits: `Y[3-a] := X[a]`, images 3, 2. Admitted at `|k| = 4`,
-- refused at `|k| = 3`: the maximum 3 sits at a = 0, the ORIGIN, while the far corner a = 1 gives
-- 2 and fits, so a corner-only (max-coordinate) enumeration would wrongly admit the `|k| = 3`
-- case. Kills: replacing `coordAll` by a far-corner check; a sign-blind range check.
#guard view (admitSourceAffine (snap 4 [k]
    (.assign "Y" [.affine (.affine 3 [(-1, a)])] readX))) ==
  some [([(3, [(-1, 7)])], [7], [[3], [2]], true)]
#guard refused (admitSourceAffine (snap 3 [k]
    (.assign "Y" [.affine (.affine 3 [(-1, a)])] readX))) (outSlot 0) isOutOfRange

/-! (h) BARE-slot scatter: an all-free `.scatter` with a `max` aggregation under `sorted` is
admitted through the bare path with the same structure as a bare `sum` scatter (S3b T7: the sorted
scatter refusal is gone); unsorted it is still refused (`nonSum`). -/
private def bareScatter : SourceSnapshot :=
  snap 3 [a] (.scatter "Y" [.free a] readX)

private def bareMaxScatter : SourceSnapshot :=
  snap 3 [a] (.scatter "Y" [.free a] maxRhs)
private def bareView : Option (List (List WriteForm × List UID × List (List Int) × Bool)) :=
  some [([(0, [(1, 7)])], [7], [[0], [1]], true)]

#guard view (admitSourceAffine bareMaxScatter (sorted := true)) == bareView
#guard refused (admitSourceAffine bareMaxScatter) nonSumOrigin isNonSum   -- unsorted: `nonSum`
#guard view (admitSourceAffine bareScatter) == bareView

/-! (i) `.freeNorm` and scan slots under `admitSourceAffine`: refused by `outputForms` at the
blamed slot with today's causes, before any range check (the `.iter` declaration refusal is the
earlier `checkAxes` stage and is covered under `admitSource`). Observed: all of these reach
`outputForms` (slot-level origin, stage `.output`). Neighbour: `Y[a+0, a]` admits. -/
private def isMarked : SourceCause → Bool | .unsupported .marked => true | _ => false
private def isScanSlot : SourceCause → Bool | .unsupported .scanSlot => true | _ => false

#guard refused (admitSourceAffine (snap 3 [a] (.assign "Y" [.freeNorm a] readX)))
  (outSlot 0) isMarked
#guard refused (admitSourceAffine (snap 3 [k, a]
    (.assign "Y" [.affine (.shift a 0), .freeNorm a] readX))) (outSlot 1) isMarked
#guard refused (admitSourceAffine (snap 3 [a] (.assign "Y" [.iterNext a] readX)))
  (outSlot 0) isScanSlot
#guard refused (admitSourceAffine (snap 3 [k, a]
    (.assign "Y" [.affine (.shift a 0), .iterNext a] readX))) (outSlot 1) isScanSlot
#guard refused (admitSourceAffine (snap 3 [k, a]
    (.assign "Y" [.affine (.shift a 0), .iterAt a 0] readX))) (outSlot 1) isScanSlot
-- Slot 0 (`const 5`, `|k| = 3`) would fail the range check, yet the scan slot at 1 is blamed:
-- `outputForms` runs before the range check.
#guard refused (admitSourceAffine (snap 3 [k, a]
    (.assign "Y" [.affine (.const 5), .iterNext a] readX))) (outSlot 1) isScanSlot
#guard view (admitSourceAffine (snap 3 [k, a]
    (.assign "Y" [.affine (.shift a 0), .free a] readX))) ==
  some [([(0, [(1, 7)]), (0, [(1, 7)])], [7], [[0, 0], [1, 1]], true)]

end SourceAdmissionAffineTest
