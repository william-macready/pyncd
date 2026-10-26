import LeanNCD.Semantics.Source.SortedDifferential

/-! S2b: single-sort programs end to end (admission + selection -> oracle -> Core
leg -> ExtVal observation -> tropical profile -> production bits).

Declarations: axes `a` (4), `b` (3), `k` (8: the extent production derives for the `2*a` write); `X[a] = [1,2,3,4]` (3), `W[b] = [1,10,100]` (4),
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
  let extent (ax : AxisSpec) : Nat := if ax.uid = 7 then 4 else if ax.uid = 8 then 3 else 8
  { resolved := {
      decls := [.axis a (some 4), .axis b (some 3), .axis k (some 8),
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

/-- `Y[2*a] := max X[a]` as a hand-built affine `.assign`: odd cells (and cell 7) are empty fibers. -/
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
-- S3b T7: a tropical `.scatter` is admitted (formerly refused, `scatterPolicy`) and selects its carrier.
/-- info: "maxPlus" -/
#guard_msgs in #eval carrierOf (snap [k] [.scatter "Y" [.affine (.scale 2 a)] (rhs .max [[.read "X" [.axis a]]])])

/-! Q5: Core leg values (must equal the oracle: `published` agreement is in the classification). -/
/-- info: "some [some -3, some 7, some 17, some 27]" -/
#guard_msgs in #eval yCore (single .max)
/-- info: "some [some -5, some 5, some 15, some 25]" -/
#guard_msgs in #eval yCore (single .min)
/-- info: "some [some 101, some 102, some 103, some 104]" -/
#guard_msgs in #eval yCore (product .max)
/-- info: "some [some 1, some -inf, some 2, some -inf, some 3, some -inf, some 4, some -inf]" -/
#guard_msgs in #eval yCore (strided .max)
/-- info: "some [some 1, some +inf, some 2, some +inf, some 3, some +inf, some 4, some +inf]" -/
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
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (product .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (product .min)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (strided .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.unsupportedNumericalProfile\n  (LeanNCD.Semantics.Source.NumericalProfile.Unsupported.outsideEnvelope\n    { origin := { side := LeanNCD.Semantics.Source.SourceSide.read,\n                  declaration := none,\n                  statement := some 0,\n                  term := some 0,\n                  factor := none,\n                  slot := none },\n      coordinate := [0],\n      assignment := [(7, 0), (8, 0)],\n      slots := [],\n      cell := none }\n    (LeanNCD.Semantics.Source.NumericalProfile.ValueKind.subsetProductBound)\n    1048577\n    1048576)" -/
#guard_msgs in #eval classOf (product .max [1048576, 2, 3, 4])

/-! Q8: the existing real harness still refuses a tropical program loudly at admission. -/
/-- info: "LeanNCD.Semantics.Source.SourceCause.unsupported (LeanNCD.Semantics.Source.UnsupportedSource.nonSum)" -/
#guard_msgs in #eval match compareSource (single .max) (some [6]) with
  | .error (.admission d) => toString (repr d.cause)
  | _ => "ran"

/-! The `±inf` bit patterns, pinned against Lean's own IEEE `Float`. The `strided` rows above and the
extent-0 rows below compare infinite cells with production. -/
#guard ExtClass.negInf.bits == (-(1.0 / 0.0) : Float).toBits
#guard ExtClass.posInf.bits == (1.0 / 0.0 : Float).toBits

/-! Extent-0 reduction axis (probe, 2026-10-20). With `|b| = 0`, `Y[a] := agg Z[a,b]` reduces over an
EMPTY axis, so every cell is the empty reduction: `-inf` (max) or `+inf` (min). Production's two
legs agree with the oracle on the `±inf` bit patterns. `Y` is declaration 3
here (axes 0-1, `Z` 2). -/
private def empty0 (agg : AggOp) : SourceSnapshot :=
  { resolved := {
      decls := [.axis a (some 4), .axis b (some 0),
        .typedTensor .f64 "Z" [a, b], .typedTensor .f64 "Y" [a]]
      stmts := [.assign "Y" [.free a] (rhs agg [[.read "Z" [.axis a, .axis b]]])]
      env := {}, extNames := ∅ }
    specs := [⟨2, .input, [4, 0]⟩, ⟨3, .output, [4]⟩]
    inputs := [⟨2, [4, 0], []⟩] }

private def classOf0 (s : SourceSnapshot) : String :=
  match compareSortedSource s (some [3]) with
  | .ok r => toString (repr r.classification)
  | .error d => s!"refused {repr d.cause}"

private def yCore0 (s : SourceSnapshot) : String :=
  match compareSortedSource s (some [3]) with
  | .ok r => match r.core with
    | .ok ts => toString (repr ((ts.find? (·.declaration == 3)).map (·.values)))
    | .error e => e
  | .error d => s!"refused {repr d.cause}"

/-- info: "some [some -inf, some -inf, some -inf, some -inf]" -/
#guard_msgs in #eval yCore0 (empty0 .max)
/-- info: "some [some +inf, some +inf, some +inf, some +inf]" -/
#guard_msgs in #eval yCore0 (empty0 .min)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf0 (empty0 .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf0 (empty0 .min)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf0 (empty0 .sum)

/-! Multi-tensor programs (S3b T7). These were the T4B known-difference fixtures
(`tropicalMultiFactor`, `tropicalScatterFill`: production multiplied tropical factors, refused a
tropical affine write, and gave an empty product `1.0`). Production now computes `⊗` as `+`, fills
an empty fiber with `0_K` and gives an empty product `1_K = 0`, so the conditions and their
confirmers are gone and every program here is a plain four-leg parity row: any divergence on
either tensor is a real `nativeDiscrepancy`/`nativeFailure`. Two outputs: `Y` is declaration 6,
`V` declaration 7. -/
private def snap2 (yAxes vAxes : List AxisSpec) (stmts : List Stmt) : SourceSnapshot :=
  let base := snap yAxes stmts
  let extent (ax : AxisSpec) : Nat := if ax.uid = 7 then 4 else if ax.uid = 8 then 3 else 8
  { base with
    resolved := { base.resolved with
      decls := base.resolved.decls ++ [.typedTensor .f64 "V" vAxes] }
    specs := base.specs ++ [⟨7, .output, vAxes.map extent⟩] }

private def bareY : Stmt := .assign "Y" [.free a] (rhs .max [[.read "Z" [.axis a, .axis b]]])
private def multiY : Stmt := .assign "Y" [.free a] (rhs .max [[.read "X" [.axis a], .read "W" [.axis b]]])
private def bareV : Stmt := .assign "V" [.free a] (rhs .max [[.read "Z" [.axis a, .axis b]]])
private def multiV : Stmt := .assign "V" [.free a] (rhs .max [[.read "X" [.axis a], .read "W" [.axis b]]])
private def stridedY : Stmt := .assign "Y" [.affine (.scale 2 a)] (rhs .max [[.read "X" [.axis a]]])
private def stridedV : Stmt := .assign "V" [.affine (.scale 2 a)] (rhs .max [[.read "X" [.axis a]]])
/-- A zero-factor `max` term: the empty product `1_K = 0` in every cell. -/
private def zeroV : Stmt := .assign "V" [.free a] (rhs .max [[]])

private def tagOf (s : SourceSnapshot) (order : List Nat := [6, 7]) : String :=
  match compareSortedSource s (some order) with
  | .ok r => match r.classification with
    | .fourLegParity => "parity"
    | .nativeDiscrepancy (.mismatch l) _ => s!"nativeDiscrepancy at {l.declaration}, bits {l.observed}"
    | c => s!"other {repr c}"
  | .error d => s!"refused {repr d.cause}"

-- formerly `scatterFill (some 6)`
/-- info: "parity" -/
#guard_msgs in #eval tagOf (strided .min) [6]
-- formerly `multiFactor (some 7)`, `(some 6)`, `(some 6)`
/-- info: "parity" -/
#guard_msgs in #eval tagOf (snap2 [a] [a] [bareY, multiV])
/-- info: "parity" -/
#guard_msgs in #eval tagOf (snap2 [a] [a] [multiY, bareV])
/-- info: "parity" -/
#guard_msgs in #eval tagOf (snap2 [a] [a] [multiY, multiV])
/-- info: "parity" -/
#guard_msgs in #eval tagOf (snap2 [a] [a] [bareY, bareV])
-- formerly `scatterFill (some 6)`, `(some 7)`, `(some 6)`, `(some 6)`
/-- info: "parity" -/
#guard_msgs in #eval tagOf (snap2 [k] [a] [stridedY, bareV])
/-- info: "parity" -/
#guard_msgs in #eval tagOf (snap2 [a] [k] [bareY, stridedV])
/-- info: "parity" -/
#guard_msgs in #eval tagOf (snap2 [k] [k] [stridedY, stridedV])
/-- info: "parity" -/
#guard_msgs in #eval tagOf (snap2 [k] [a] [stridedY, multiV])
-- the zero-factor term (formerly `nativeDiscrepancy at 7`: production's empty product was `1.0`)
/-- info: "parity" -/
#guard_msgs in #eval tagOf (snap2 [a] [a] [bareY, zeroV])
/-- info: "parity" -/
#guard_msgs in #eval tagOf (snap2 [a] [a] [multiY, zeroV])
-- statement order differs from declaration order
/-- info: "parity" -/
#guard_msgs in #eval tagOf (snap2 [a] [a] [multiV, multiY])

/-! S3b T7 parity rows: each value differs from what the pre-S3b production computed (max-times
`⊗`, scatter fill `0`, empty product `1`), so each row fails against that semantics. -/

/-- (a) A tropical scatter: the three `b` writes of each `a` collide in cell `2a` (combined with
`⊕`), and the odd cells and cell 7 are never written (`0_K`). Donor: `ScatterCompileTest` S11
(`Out[2*i] := maxreduce(X[i, j])`). Max over `b` of `Z`: `-3, 7, 17, 27`; min: `-5, 5, 15, 25`. -/
private def collide (agg : AggOp) : SourceSnapshot :=
  snap [k] [.scatter "Y" [.affine (.scale 2 a)] (rhs agg [[.read "Z" [.axis a, .axis b]]])]

/-- info: "some [some -3, some -inf, some 7, some -inf, some 17, some -inf, some 27, some -inf]" -/
#guard_msgs in #eval yCore (collide .max)
/-- info: "some [some -5, some +inf, some 5, some +inf, some 15, some +inf, some 25, some +inf]" -/
#guard_msgs in #eval yCore (collide .min)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (collide .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (collide .min)

/-- (b) A multi-factor contraction over the shared axis `b`: `Y[a] = ⊕_b Z[a,b] ⊗ W[b]`. Donors: the
`product` rows above and the TR3/TR7 shape. Max-plus: `Z[a,2] + 100` = `97, 107, 117, 127`
(max-times would give `-5, 50, 1500, 2500`); min-plus: `Z[a,0] + 1` = `-4, 6, 16, 26`. -/
private def contract (agg : AggOp) : SourceSnapshot :=
  snap [a] [.assign "Y" [.free a] (rhs agg [[.read "Z" [.axis a, .axis b], .read "W" [.axis b]]])]

/-- info: "some [some 97, some 107, some 117, some 127]" -/
#guard_msgs in #eval yCore (contract .max)
/-- info: "some [some -4, some 6, some 16, some 26]" -/
#guard_msgs in #eval yCore (contract .min)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (contract .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (contract .min)

/-- (c) The empty product alone: `Y[a] := agg ()` is `1_K = 0` in every cell, for both sorts. -/
private def zeroY (agg : AggOp) : SourceSnapshot :=
  snap [a] [.assign "Y" [.free a] (rhs agg [[]])]

/-- info: "some [some 0, some 0, some 0, some 0]" -/
#guard_msgs in #eval yCore (zeroY .max)
/-- info: "some [some 0, some 0, some 0, some 0]" -/
#guard_msgs in #eval yCore (zeroY .min)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (zeroY .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (zeroY .min)

/-! (d) Negative inputs, where max-times and max-plus disagree: `X = [-1,-2,-3,-4]`,
`Y[a] = ⊕_b X[a] ⊗ W[b]`. Max-plus `X[a] + 100` = `99, 98, 97, 96` (max-times: `-1, -2, -3, -4`);
min-plus `X[a] + 1` = `0, -1, -2, -3` (min-times: `-100, -200, -300, -400`). -/
/-- info: "some [some 99, some 98, some 97, some 96]" -/
#guard_msgs in #eval yCore (product .max [-1, -2, -3, -4])
/-- info: "some [some 0, some -1, some -2, some -3]" -/
#guard_msgs in #eval yCore (product .min [-1, -2, -3, -4])
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (product .max [-1, -2, -3, -4])
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (product .min [-1, -2, -3, -4])


/-! S3b-ii T4: TWO writers of one tensor (the Bellman shape), no oracle or production change. The
oracle collects by target and picks one carrier, so an all-max / all-min program is a plain four-leg
parity row. `Y` is written by a contraction `Y[a] := agg_b Z[a,b]` and by a terminal/source value
`Y[a] := agg X[a]` with `X = [20, 2, 3, 40]`, so the second writer wins in some cells and loses in
others: max-plus `[max(-3,20), max(7,2), max(17,3), max(27,40)] = [20, 7, 17, 40]`, min-plus
`[min(-5,20), min(5,2), min(15,3), min(25,40)] = [-5, 2, 3, 25]` (observed from the Core leg; production
agrees on the bits, `fourLegParity`). The sum-annotated COPY form the user prefers
(`Y[a] := X[a]` beside a `max`) is NOT a four-leg row: the oracle selects its carrier from every
statement's annotation, so it refuses a mixed group at admission (`sortSelection (mixedSorts ..)`),
while production accepts it (the neutral copy abstains). The oracle therefore covers only the
all-annotated spelling of the Bellman programs; the copy form and every mixed group are
production-only (`CollectPlanTest`). -/
private def contY (agg : AggOp) : Stmt :=
  .assign "Y" [.free a] (rhs agg [[.read "Z" [.axis a, .axis b]]])
private def termY (agg : AggOp) : Stmt := .assign "Y" [.free a] (rhs agg [[.read "X" [.axis a]]])
private def bellman (s1 s2 : AggOp) : SourceSnapshot :=
  snap [a] [contY s1, termY s2] [20, 2, 3, 40]

/-- info: "maxPlus" -/
#guard_msgs in #eval carrierOf (bellman .max .max)
/-- info: "some [some 20, some 7, some 17, some 40]" -/
#guard_msgs in #eval yCore (bellman .max .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (bellman .max .max)
/-- info: "minPlus" -/
#guard_msgs in #eval carrierOf (bellman .min .min)
/-- info: "some [some -5, some 2, some 3, some 25]" -/
#guard_msgs in #eval yCore (bellman .min .min)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval classOf (bellman .min .min)
-- mixed groups: refused by this typed single-sort path at admission, in both orders. Production
-- accepts all of them (the min or sum copy is neutral, abstains, and runs in the group's sort), and
-- refuses only a group of two non-neutral voters that disagree; the per-tensor-sort oracle
-- (`compareMixedSource`, `OracleMixedValueTest`) pins their values
/-- info: "refused LeanNCD.Semantics.Source.SourceCause.sortSelection\n  (LeanNCD.Semantics.Source.Oracle.SelectionError.mixedSorts [LeanNCD.AggOp.max, LeanNCD.AggOp.min])" -/
#guard_msgs in #eval classOf (bellman .max .min)
/-- info: "refused LeanNCD.Semantics.Source.SourceCause.sortSelection\n  (LeanNCD.Semantics.Source.Oracle.SelectionError.mixedSorts [LeanNCD.AggOp.max, LeanNCD.AggOp.sum])" -/
#guard_msgs in #eval classOf (bellman .max .sum)

end SourceSortedDifferentialTest
