import Semantics.OracleMixedDifferential

/-! Oracle sorts T2: refusal-parity rows and B5's migrated four-leg value donors.
For each program production refuses (observed in
`papers/semantics/oracle_sorts_plan_facts.md` section 5), the independent predictor names the
refusal, both native legs refuse with the same `CompileError` constructor, and `classifyRefusal`
reports `refusalParity`. Negative controls doctor the prediction and must flip to `refusalMismatch`.
(Slice B removed the unsupported-geometry rows: multi-axis and constant groups are admitted.) -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open NativeLegs SortedDifferential LeanNCD.OracleSorts OracleMixed Oracle

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

/-! D7: the three shape-correct former refusal donors now require actual four-leg values. -/
private def d7ScatterTs : List T := [tZ, tQ, tOut "Y"]
private def d7Scatter : SourceSnapshot :=
  mk d7ScatterTs [st "Y" .max (rd "Z" [axA, axB]),
    .scatter "Y" free1 (rhs .max [[rd "Q" [axA, axB]]])]
private def d7AffTs : List T := [tX, tW8, tOut "Y" [axK]]
private def affine2 : Stmt := zR "Y" [.affine (.scale 2 axA)] .max [rd "X" [axA]]
private def d7TwoAffine : SourceSnapshot := mk d7AffTs [affine2, affine2]
private def d7AffineBare : SourceSnapshot :=
  mk d7AffTs [affine2, zR "Y" [.free axK] .max [rd "W8" [axK]]]

private def mixed (s : SourceSnapshot) (ts : List T) : Except String MixedRun :=
  (compareMixedSource s (some (orderOf ts))).mapError (fun d => s!"{repr d.cause}")

private def valueParity (s : SourceSnapshot) (ts : List T) (sort : MSort)
    (expected : List ExtVal) : Bool :=
  match mixed s ts with
  | .error _ => false
  | .ok r =>
    let cells := r.oracle.toOption.map (fun tensors =>
      tensors.filterMap fun t => if t.name == some "Y" then some t.values else none)
    let core := r.core.bind (fun c => c.toOption.map fun tensors =>
      tensors.filterMap fun t => if t.name == some "Y" then some t.values else none)
    (match r.classification with | .fourLegParity => true | _ => false) &&
      r.prediction.stmtSorts == [sort, sort] &&
      cells == some [expected.map some] && core == some [expected.map some]

private def overlap (ag : AggOp) : SourceSnapshot :=
  mk [tZ, tX, tOut "Y" [axK]]
    [.scatter "Y" [.affine (.scale 2 axA)] (rhs ag [[rd "Z" [axA, axB]]]),
     .scatter "Y" [.affine (.scale 2 axA)] (rhs .sum [[rd "X" [axA]]])]

#guard valueParity d7Scatter d7ScatterTs .maxPlus ([9, 8, 17, 27].map ExtVal.fin)
#guard valueParity d7TwoAffine d7AffTs .maxPlus
  [.fin 20, .negInf, .fin 2, .negInf, .fin 3, .negInf, .fin 40, .negInf]
#guard valueParity d7AffineBare d7AffTs .maxPlus
  ([20, 0, 2, 3, 4, 5, 40, 7].map ExtVal.fin)
#guard valueParity (overlap .sum) [tZ, tX, tOut "Y" [axK]] .real
  ([8, 0, 20, 0, 51, 0, 118, 0].map ExtVal.fin)
#guard valueParity (overlap .max) [tZ, tX, tOut "Y" [axK]] .maxPlus
  [.fin 20, .negInf, .fin 7, .negInf, .fin 17, .negInf, .fin 40, .negInf]
#guard valueParity (overlap .min) [tZ, tX, tOut "Y" [axK]] .minPlus
  [.fin (-5), .posInf, .fin 2, .posInf, .fin 3, .posInf, .fin 25, .posInf]

/-! B5b: the same overlap donors under a pinned box (extent 10) larger than the realized extent 8.
The two trailing cells are holes holding the sort's `0_K`. -/
private def extBox (ax : AxisSpec) : Nat := if ax.uid = 9 then 10 else ext ax
private def mkBox (ts : List T) (stmts : List Stmt) : SourceSnapshot :=
  { resolved := { decls := [.axis axA (some 4), .axis axB (some 3), .axis axK (some 10)]
                    ++ ts.map (fun t => .typedTensor .f64 t.name t.axes)
                  stmts := stmts, env := {}, extNames := ∅ }
    specs := ts.zipIdx.map (fun (t, i) => ⟨i + 3, t.role, t.axes.map extBox⟩)
    inputs := (ts.zipIdx.filter (fun (t, _) => t.role == .input)).map
      (fun (t, i) => ⟨i + 3, t.axes.map extBox, t.vals⟩) }
private def overlapBox (ag : AggOp) : SourceSnapshot :=
  mkBox [tZ, tX, tOut "Y" [axK]] (overlap ag).resolved.stmts
private def boxTs : List T := [tZ, tX, tOut "Y" [axK]]

#guard valueParity (overlapBox .sum) boxTs .real
  ([8, 0, 20, 0, 51, 0, 118, 0, 0, 0].map ExtVal.fin)
#guard valueParity (overlapBox .max) boxTs .maxPlus
  [.fin 20, .negInf, .fin 7, .negInf, .fin 17, .negInf, .fin 40, .negInf, .negInf, .negInf]
#guard valueParity (overlapBox .min) boxTs .minPlus
  [.fin (-5), .posInf, .fin 2, .posInf, .fin 3, .posInf, .fin 25, .posInf, .posInf, .posInf]

/-! Slice B (B-D1): a multi-axis or constant scatter group is ADMITTED, so these two former
unsupported-geometry controls (they were `multiWriterScatter` refusal parity, with the typed path's
false `nativeFailure` as the contrast) are now accept neighbours: no refusal verdict. The only
surviving `multiWriterScatter` refusal is a predicate destination, which the source oracle does not
admit (`UnsupportedSource.predicate`), so no source-admitted program reaches that refusal here; its
predictor coverage is the predicate row of `OracleSortRulesTest`. -/
private def multiAxis : SourceSnapshot :=
  mk [tZ, tQ, tOut "Y" [axK]]
    [.scatter "Y" [.affine (.affine 0 [(1, axA), (1, axB)])]
      (rhs .max [[rd "Z" [axA, axB]]]),
     .scatter "Y" [.affine (.affine 0 [(1, axA), (1, axB)])]
      (rhs .max [[rd "Q" [axA, axB]]])]
private def constant : SourceSnapshot :=
  mk d7AffTs (List.replicate 2 (.scatter "Y" [.affine (.const 3)] (rhs .max [[rd "X" [axA]]])))

#guard classOf multiAxis == "none"
#guard classOf constant == "none"

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
#guard classWith multiAxis predictCast ==
  "OracleMixed.MixedClassification.refusalMismatch [(\"sortCastUnsupported\", \"Y\")] \"accepted\""
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

private def predictCastY : Prediction :=
  { refusals := [("sortCastUnsupported", "Y")], sorts := [], stmtSorts := [] }

-- (slice B: was `multiAxis`/`multiWriterScatter`, which is now admitted; donor `castDirect`)
-- legacy `sortCastUnsupported`, checked `multiWriterAlgebra`; the cast is predicted
#guard splitClass predictCastY (splitRun castDirect r16a) ==
  "OracleMixed.MixedClassification.refusalMismatch\n  [(\"sortCastUnsupported\", \"Y\")]\n  \"legacy sortCastUnsupported, checked multiWriterAlgebra\""
-- the same legs from one program are parity
#guard splitClass predictCastY (splitRun castDirect castDirect) == parity "sortCastUnsupported"

end OracleMixedRefusalTest
