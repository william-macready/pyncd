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
#guard_msgs in #eval carrierOf (snap [k] [.scatter "Y" [.affine (.scale 2 a)] (rhs .max [[.read "X" [.axis a]]])])

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
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.knownContractDifference\n  (LeanNCD.Semantics.Source.NumericalProfile.StructuralCondition.tropicalMultiFactor\n    { side := LeanNCD.Semantics.Source.SourceSide.output,\n      declaration := some 6,\n      statement := some 0,\n      term := none,\n      factor := none,\n      slot := none })" -/
#guard_msgs in #eval classOf (product .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.knownContractDifference\n  (LeanNCD.Semantics.Source.NumericalProfile.StructuralCondition.tropicalMultiFactor\n    { side := LeanNCD.Semantics.Source.SourceSide.output,\n      declaration := some 6,\n      statement := some 0,\n      term := none,\n      factor := none,\n      slot := none })" -/
#guard_msgs in #eval classOf (product .min)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.knownContractDifference\n  (LeanNCD.Semantics.Source.NumericalProfile.StructuralCondition.tropicalScatterFill\n    { side := LeanNCD.Semantics.Source.SourceSide.output,\n      declaration := some 6,\n      statement := some 0,\n      term := none,\n      factor := none,\n      slot := none })" -/
#guard_msgs in #eval classOf (strided .max)
/-- info: "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.unsupportedNumericalProfile\n  (LeanNCD.Semantics.Source.NumericalProfile.Unsupported.outsideEnvelope\n    { origin := { side := LeanNCD.Semantics.Source.SourceSide.read,\n                  declaration := none,\n                  statement := some 0,\n                  term := some 0,\n                  factor := none,\n                  slot := none },\n      coordinate := [0],\n      assignment := [(7, 0), (8, 0)],\n      slots := [],\n      cell := none }\n    (LeanNCD.Semantics.Source.NumericalProfile.ValueKind.subsetProductBound)\n    1048577\n    1048576)" -/
#guard_msgs in #eval classOf (product .max [1048576, 2, 3, 4])

/-! Q8: the existing real harness still refuses a tropical program loudly at admission. -/
/-- info: "LeanNCD.Semantics.Source.SourceCause.unsupported (LeanNCD.Semantics.Source.UnsupportedSource.nonSum)" -/
#guard_msgs in #eval match compareSource (single .max) (some [6]) with
  | .error (.admission d) => toString (repr d.cause)
  | _ => "ran"

/-! The `±inf` bit patterns, pinned against Lean's own IEEE `Float`. No row above compares an
infinite cell with production (an affine write that yields one is refused); the extent-0 rows do. -/
#guard ExtClass.negInf.bits == (-(1.0 / 0.0) : Float).toBits
#guard ExtClass.posInf.bits == (1.0 / 0.0 : Float).toBits

/-! Extent-0 reduction axis (probe, 2026-10-20). With `|b| = 0`, `Y[a] := agg Z[a,b]` reduces over an
EMPTY axis, so every cell is the empty reduction: `-inf` (max) or `+inf` (min). Unlike the strided
write this is admitted AND runs in production, whose two legs agree with the oracle on the `±inf` bit
patterns: these rows are the only place `ExtClass.bits` meets production output. `Y` is declaration 3
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

/-! T4B: the two structural known-difference conditions (`tropicalMultiFactor`,
`tropicalScatterFill`). The `product`/`strided` rows above carry the full classification; these
rows bind each condition to its own tensor. Two outputs: `Y` is declaration 6, `V` declaration 7. -/
private def snap2 (yAxes vAxes : List AxisSpec) (stmts : List Stmt) : SourceSnapshot :=
  let base := snap yAxes stmts
  let extent (ax : AxisSpec) : Nat := if ax.uid = 7 then 4 else if ax.uid = 8 then 3 else 7
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

private def known (s : SourceSnapshot) (order : List Nat := [6]) : String :=
  match compareSortedSource s (some order) with
  | .ok r => match r.classification with
    | .knownContractDifference (.tropicalMultiFactor o) => s!"multiFactor {o.declaration}"
    | .knownContractDifference (.tropicalScatterFill o) => s!"scatterFill {o.declaration}"
    | .knownContractDifference _ => "other condition"
    | c => s!"not known: {repr c}"
  | .error d => s!"refused {repr d.cause}"

/-- info: "scatterFill (some 6)" -/
#guard_msgs in #eval known (strided .min)
-- differing origin: only `V` (declaration 7) is multi-factor, the condition binds to it
/-- info: "multiFactor (some 7)" -/
#guard_msgs in #eval known (snap2 [a] [a] [bareY, multiV]) [6, 7]
/-- info: "multiFactor (some 6)" -/
#guard_msgs in #eval known (snap2 [a] [a] [multiY, bareV]) [6, 7]
-- both multi-factor: the head (declaration 6) is confirmed, as in the real harness
/-- info: "multiFactor (some 6)" -/
#guard_msgs in #eval known (snap2 [a] [a] [multiY, multiV]) [6, 7]
-- accept-neighbour: no condition, plain parity
/-- info: "not known: LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.fourLegParity" -/
#guard_msgs in #eval known (snap2 [a] [a] [bareY, bareV]) [6, 7]
/-- info: "scatterFill (some 6)" -/
#guard_msgs in #eval known (snap2 [k] [a] [stridedY, bareV]) [6, 7]
-- only `V` is strided: bound to declaration 7
/-- info: "scatterFill (some 7)" -/
#guard_msgs in #eval known (snap2 [a] [k] [bareY, stridedV]) [6, 7]
/-- info: "scatterFill (some 6)" -/
#guard_msgs in #eval known (snap2 [k] [k] [stridedY, stridedV]) [6, 7]
-- both shapes: scatter-fill precedes the value comparison (pipeline order), head only
/-- info: "scatterFill (some 6)" -/
#guard_msgs in #eval known (snap2 [k] [a] [stridedY, multiV]) [6, 7]

/-! The confirmer on its own (`confirmsSorted`): each leg of each binding is pinned separately, with
natives from two programs that differ only in WHICH tensor is strided (`nY`: `Y`, `nV`: `V`). The
mixed natives carry one leg of each, so a confirmer that ignored the owner on one leg would accept. -/
private def nativeOf (s : SourceSnapshot) : Option NativeLegs.NativeRun :=
  (NativeLegs.runNative s (sorted := true)).toOption

private def originOf (d : Nat) : SourceOrigin := { side := .output, declaration := some d }

private def fills (n : Option NativeLegs.NativeRun) (d : Nat) : Bool :=
  match n with
  | some n => confirmsSorted n .agrees .agrees (.tropicalScatterFill (originOf d))
  | none => false

private def nY := nativeOf (snap2 [k] [a] [stridedY, bareV])
private def nV := nativeOf (snap2 [a] [k] [bareY, stridedV])

#guard fills nY 6
#guard fills nV 7
#guard !fills nY 7   -- same cause, other tensor
#guard !fills nY 3   -- a tensor that is not written at all
#guard !fills (nY.bind fun y => nV.map fun v => { y with checked := v.checked }) 6
#guard !fills (nY.bind fun y => nV.map fun v => { y with legacy := v.legacy }) 6

/-- Multi-factor: both legs must mismatch at the origin's declaration (`oneSided`: only the legacy leg). -/
private def multi (origin : Nat) (oneSided : Bool := false) : Bool :=
  let s := snap2 [a] [a] [bareY, multiV]
  match nativeOf s, compareSortedSource s (some [6, 7]) with
  | some n, .ok r => confirmsSorted n r.legacy (if oneSided then .agrees else r.checked)
      (.tropicalMultiFactor (originOf origin))
  | _, _ => false

#guard multi 7
#guard !multi 6   -- the mismatch is on `V`, not `Y`: a condition elsewhere hides nothing
#guard !multi 7 (oneSided := true)

/-! T4B review fixes. Unexplained divergence: a zero-factor `max` term is `1_K = 0` for the oracle
and `1.0` for production, a mismatch no condition explains. Beside a multi-factor tensor it must
stay reported (the first mismatch is the multi-factor tensor's, declaration 6). -/
private def zeroV : Stmt := .assign "V" [.free a] (rhs .max [[]])

private def tagOf (s : SourceSnapshot) (order : List Nat := [6, 7]) : String :=
  match compareSortedSource s (some order) with
  | .ok r => match r.classification with
    | .fourLegParity => "parity"
    | .knownContractDifference (.tropicalMultiFactor o) => s!"multiFactor {o.declaration}"
    | .knownContractDifference (.tropicalScatterFill o) => s!"scatterFill {o.declaration}"
    | .nativeDiscrepancy (.mismatch l) _ => s!"nativeDiscrepancy at {l.declaration}, bits {l.observed}"
    | _ => "other"
  | .error d => s!"refused {repr d.cause}"

/-- info: "nativeDiscrepancy at 7, bits 4607182418800017408" -/
#guard_msgs in #eval tagOf (snap2 [a] [a] [bareY, zeroV])
/-- info: "multiFactor (some 6)" -/
#guard_msgs in #eval tagOf (snap2 [a] [a] [multiY, bareV])
-- the same multi-factor tensor with the unexplained zero-factor divergence beside it is NOT known
#guard (tagOf (snap2 [a] [a] [multiY, zeroV])).startsWith "nativeDiscrepancy"
-- statement order differs from declaration order: the matching condition is found, not just the head
/-- info: "multiFactor (some 6)" -/
#guard_msgs in #eval tagOf (snap2 [a] [a] [multiV, multiY])

-- both legs must show the SAME first mismatch: a checked leg with other bits is not explained
#guard !(match nativeOf (snap2 [a] [a] [bareY, multiV]), compareSortedSource (snap2 [a] [a] [bareY, multiV]) (some [6, 7]) with
  | some n, .ok r => match r.checked with
    | .mismatch c => confirmsSorted n r.legacy (.mismatch { c with observed := c.observed + 1 })
        (.tropicalMultiFactor (originOf 7))
    | _ => true
  | _, _ => true)

/-- `unexplainedAgree` on the legacy observation of `[bareY, multiV]`: excluding the multi-factor
tensor (declaration 7) leaves only `Y`, which agrees; corrupting `Y`'s expected cell is seen unless
`Y` is excluded too. -/
private def unexplained (explained : List Nat) (corrupt : Bool) : Bool :=
  let s := snap2 [a] [a] [bareY, multiV]
  match nativeOf s, compareSortedSource s (some [6, 7]) with
  | some n, .ok r => match n.legacy, r.profile with
    | .observed o, .ok cells =>
      unexplainedAgree explained
        (if corrupt then cells.map (fun c => if c.declaration == 6 then { c with expected := .posInf } else c) else cells) o
    | _, _ => false
  | _, _ => false

#guard unexplained [7] false
#guard !unexplained [7] true
#guard unexplained [6, 7] true

end SourceSortedDifferentialTest
