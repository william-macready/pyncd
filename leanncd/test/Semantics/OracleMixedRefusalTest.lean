import Semantics.OracleMixedDifferential

/-! Oracle sorts T2: refusal-parity rows. For each program production refuses (observed in
`papers/semantics/oracle_sorts_plan_facts.md` section 5), the independent predictor names the
refusal, both native legs refuse with the same `CompileError` constructor, and `classifyRefusal`
reports `refusalParity`. Negative controls doctor the prediction and must flip to `refusalMismatch`.
The D7 rows also pin the typed path's false `nativeFailure` as the contrast. -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open NativeLegs SortedDifferential LeanNCD.OracleSorts OracleMixed

namespace OracleMixedRefusalTest

private def parity (ctor : String) : String :=
  s!"OracleMixed.MixedClassification.refusalParity \"{ctor}\""

/-- The classification under a given prediction of the snapshot's refusals; `none` is printed as
`"none"` (no refusal verdict: the accepted path continues to value comparison). -/
private def classWith (s : SourceSnapshot) (adjust : Prediction → Prediction) : String :=
  match runNative s (sorted := true) with
  | .ok run =>
    match classifyRefusal (adjust (predict s.resolved.decls s.resolved.stmts)) run with
    | some k => toString (repr k)
    | none => "none"
  | .error d => s!"refused {repr d.cause}"

private def classOf (s : SourceSnapshot) : String := classWith s id

/-- The typed path's verdict, for contrast. -/
private def sortedOf (s : SourceSnapshot) (order : List Nat) : String :=
  match compareSortedSource s (some order) with
  | .ok r => toString (repr r.classification)
  | .error d => s!"refused {repr d.cause}"

/-! R16: two non-neutral voters that disagree. -/
private def r16Ts : List T := [tZ, tQ, tOut "Y"]
private def r16a : SourceSnapshot :=
  mk r16Ts [st "Y" .sum (rd "Z" [axA, axB]), st "Y" .max (rd "Q" [axA, axB])]
private def r16b : SourceSnapshot :=
  mk r16Ts [st "Y" .max (rd "Z" [axA, axB]), st "Y" .min (rd "Q" [axA, axB])]

#guard classOf r16a == parity "multiWriterAlgebra"
#guard classOf r16b == parity "multiWriterAlgebra"

/-! R10: both writers of `T` are neutral copies voting max and min over a min-plus `N`. -/
private def r10Ts : List T := [tZ, tX, tDef "N", tOut "T"]
private def r10Max : Stmt := st "T" .max (rd "N" [axA])
private def r10Min : Stmt := st "T" .min (rd "X" [axA])
private def nStmt : Stmt := st "N" .min (rd "Z" [axA, axB])
private def r10MaxFirst : SourceSnapshot := mk r10Ts [nStmt, r10Max, r10Min]
private def r10MinFirst : SourceSnapshot := mk r10Ts [nStmt, r10Min, r10Max]

#guard classOf r10MaxFirst == parity "multiWriterAlgebra"
#guard classOf r10MinFirst == parity "multiWriterAlgebra"

/-! Cast decision A: a max-plus tensor read by a min-plus statement is refused; laundering the
read through a real copy is accepted. -/
private def castDirect : SourceSnapshot :=
  mk [tZ, tDef "M", tOut "O"]
    [st "M" .max (rd "Z" [axA, axB]), st "O" .min (rd "M" [axA])]
private def castLaundered : SourceSnapshot :=
  mk [tZ, tDef "M", tDef "R", tOut "O"]
    [st "M" .max (rd "Z" [axA, axB]), st "R" .sum (rd "M" [axA]), st "O" .min (rd "R" [axA])]

#guard classOf castDirect == parity "sortCastUnsupported"

/-- A single-writer neutral max copy is max-plus by its own annotation. -/
private def neutralCopyRead : SourceSnapshot :=
  mk [tX, tDef "T", tOut "O"] [st "T" .max (rd "X" [axA]), st "O" .min (rd "T" [axA])]

#guard classOf neutralCopyRead == parity "sortCastUnsupported"

/-! D7: a multi-writer group holding a scatter or an affine write is refused as
`multiWriterScatter`; the typed path reports a false `nativeFailure`. -/
private def d7ScatterTs : List T := [tZ, tQ, tOut "Y"]
private def d7Scatter : SourceSnapshot :=
  mk d7ScatterTs [st "Y" .max (rd "Z" [axA, axB]),
    .scatter "Y" free1 (rhs .max [[rd "Q" [axA, axB]]])]
private def d7AffTs : List T := [tX, tW8, tOut "Y" [axK]]
private def affine2 : Stmt := zR "Y" [.affine (.scale 2 axA)] .max [rd "X" [axA]]
private def d7TwoAffine : SourceSnapshot := mk d7AffTs [affine2, affine2]
private def d7AffineBare : SourceSnapshot :=
  mk d7AffTs [affine2, zR "Y" [.free axK] .max [rd "W8" [axK]]]

#guard classOf d7Scatter == parity "multiWriterScatter"
#guard classOf d7TwoAffine == parity "multiWriterScatter"
#guard classOf d7AffineBare == parity "multiWriterScatter"

/-- The typed path's false report for the D7 rows (contrast pins). -/
private def falseNativeFailure : String :=
  "LeanNCD.Semantics.Source.SortedDifferential.SortedClassification.nativeFailure\n  (LeanNCD.Semantics.Source.SortedDifferential.LegResult.failure\n    \"legacy compile failed: LeanNCD.CompileError.multiWriterScatter \\\"Y\\\"\")\n  (LeanNCD.Semantics.Source.SortedDifferential.LegResult.failure \"checked preparation\")"

#guard sortedOf d7Scatter (orderOf d7ScatterTs) == falseNativeFailure
#guard sortedOf d7TwoAffine (orderOf d7AffTs) == falseNativeFailure
#guard sortedOf d7AffineBare (orderOf d7AffTs) == falseNativeFailure

/-! Accept neighbour: the laundered cast is accepted, so with the true (empty) prediction
`classifyRefusal` reports no verdict (`none`, not a `refusalMismatch`). -/
#guard classOf castLaundered == "none"

/-! Negative controls: a doctored prediction is a mismatch, never a parity. -/
private def predictAccepted : Prediction → Prediction := fun p => { p with refusals := [] }
private def predictCast : Prediction → Prediction :=
  fun p => { p with refusals := [("sortCastUnsupported", "Y")] }
private def predictVote : Prediction → Prediction :=
  fun p => { p with refusals := [("multiWriterAlgebra", "M")] }

#guard classWith r16a predictAccepted == "OracleMixed.MixedClassification.refusalMismatch [] \"multiWriterAlgebra\""
#guard classWith d7Scatter predictCast ==
  "OracleMixed.MixedClassification.refusalMismatch [(\"sortCastUnsupported\", \"Y\")] \"multiWriterScatter\""
#guard classWith castLaundered predictVote ==
  "OracleMixed.MixedClassification.refusalMismatch [(\"multiWriterAlgebra\", \"M\")] \"accepted\""

/-! Two legs that refuse with DIFFERENT constructors are never `refusalParity`, even when one of the
constructors is predicted: a run is assembled from the legacy leg of one real refusal and the checked
leg of another. -/
private def splitRun (legacySide checkedSide : SourceSnapshot) : Option NativeRun :=
  match runNative legacySide (sorted := true), runNative checkedSide (sorted := true) with
  | .ok a, .ok b => some { a with checked := b.checked }
  | _, _ => none

private def splitClass (p : Prediction) : Option NativeRun → String
  | some run => match classifyRefusal p run with
    | some k => toString (repr k)
    | none => "none"
  | none => "no run"

private def predictScatter : Prediction :=
  { refusals := [("multiWriterScatter", "Y")], sorts := [], stmtSorts := [] }

-- legacy `multiWriterScatter`, checked `multiWriterAlgebra`; the scatter is predicted
#guard splitClass predictScatter (splitRun d7Scatter r16a) ==
  "OracleMixed.MixedClassification.refusalMismatch\n  [(\"multiWriterScatter\", \"Y\")]\n  \"legacy multiWriterScatter, checked multiWriterAlgebra\""
-- the same legs from one program are parity
#guard splitClass predictScatter (splitRun d7Scatter d7Scatter) == parity "multiWriterScatter"

end OracleMixedRefusalTest
