import LeanNCD.Eval.Plan.Compile
import LeanNCD.Eval.Plan.Dense
import Eval.Plan.CompileTest
import Eval.Plan.ScanCompileTest
import Eval.Plan.DifferentialTest
import Eval.Portfolio.Harness

namespace LeanNCD.Eval.Plan.PredicateCoordinateSpikeTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

private def iversonData (shape : List Nat) (e : PosBoolExpr) :
    Except PosPredicateError (Array Float) :=
  (allCoords shape).mapM (fun c => evalPosIverson c.toArray e) |>.map List.toArray

-- T1-F1: Portfolio/RelationalTest RL1, copied exactly.
private def rl1Prog : TLProgram := tlprog!{
  axis i : ℕ = 3, j : ℕ = 3
  I[i, j] := [i = j]
}
private def f1i : AxisSpec := ⟨"i", 1101, .nat⟩
private def f1j : AxisSpec := ⟨"j", 1102, .nat⟩
private def f1pred : BoolExpr :=
  .rel .eq (.embed (.axis f1i)) (.embed (.axis f1j))
private def f1term : ProdTerm := { factors := [.iverson f1pred] }

run_cmd do
  let expected : DenseTensor := ⟨[3, 3], #[1,0,0, 0,1,0, 0,0,1]⟩
  match TLProgram.eval rl1Prog (HashMap.ofList []) with
  | .error e => throwError s!"T1-F1 source failed: {e}"
  | .ok report =>
      match report.env["I"]? with
      | some actual =>
          unless actual.shape == expected.shape && DenseTensor.approxEq actual expected do
            throwError s!"T1-F1 source value: {repr actual.data}"
      | none => throwError "T1-F1 source output missing"
  let lowered := lowerFactorPredicate [] [f1i.uid, f1j.uid] {} f1term f1pred
  unless lowered.initialBasis == [f1i.uid, f1j.uid] &&
      lowered.residualBasis == [f1i.uid, f1j.uid] do
    throwError s!"T1-F1 basis: {repr lowered}"
  match iversonData [3, 3] lowered.expression with
  | .error e => throwError s!"T1-F1 positional error: {repr e}"
  | .ok data =>
      unless data == expected.data do
        throwError s!"T1-F1 positional value: {repr data}"

-- T1-F2: Portfolio/RecurrenceTest RC3, copied exactly.
private def rc3Prog : TLProgram := tlprog!{
  axis i : ℕ = 3, j : ℕ = 3
  C[i] := X[j] · [j ≤ i]
}
private def f2i : AxisSpec := ⟨"i", 1201, .nat⟩
private def f2j : AxisSpec := ⟨"j", 1202, .nat⟩
private def f2pred : BoolExpr :=
  .rel .le (.embed (.axis f2j)) (.embed (.axis f2i))
private def f2term : ProdTerm :=
  { factors := [.read "X" [.axis f2j], .iverson f2pred] }

run_cmd do
  let inputs := HashMap.ofList [("X", (⟨[3], #[1,2,3]⟩ : DenseTensor))]
  let expected : DenseTensor := ⟨[3], #[1,3,6]⟩
  match TLProgram.eval rc3Prog inputs with
  | .error e => throwError s!"T1-F2 source failed: {e}"
  | .ok report =>
      match report.env["C"]? with
      | some actual =>
          unless actual.shape == expected.shape && DenseTensor.approxEq actual expected do
            throwError s!"T1-F2 source value: {repr actual.data}"
      | none => throwError "T1-F2 source output missing"
  let lowered := lowerFactorPredicate [] [f2i.uid] {} f2term f2pred
  unless lowered.initialBasis == [f2i.uid, f2j.uid] do
    throwError s!"T1-F2 basis: {repr lowered.initialBasis}"
  match evalPosBool #[0, 1] lowered.expression, evalPosBool #[1, 0] lowered.expression with
  | .ok false, .ok true => pure ()
  | a, b => throwError s!"T1-F2 values at [i,j]=[0,1]/[1,0]: {repr a}, {repr b}"

-- T1-F3: CompileTest.multiReductionSched with `[j < k]` appended as its last factor.
private def f3pred : BoolExpr :=
  .rel .lt (.embed (.axis CompileTest.axJ2b)) (.embed (.axis CompileTest.axK2b))
private def f3term? : Option ProdTerm :=
  match CompileTest.multiReductionSched.stmts with
  | [.plain (.assign _ _ rhs)] =>
      match rhs.body.terms with
      | [t] => some { t with factors := t.factors ++ [.iverson f3pred] }
      | _ => none
  | _ => none

run_cmd do
  match f3term? with
  | none => throwError "T1-F3 donor shape changed"
  | some term =>
      unless term.factors.getLast? == some (.iverson f3pred) do
        throwError "T1-F3 predicate was not retained as the last factor"
      let lowered := lowerFactorPredicate [] [CompileTest.axI2b.uid] {} term f3pred
      unless lowered.initialBasis ==
          [CompileTest.axI2b.uid, CompileTest.axJ2b.uid, CompileTest.axK2b.uid] do
        throwError s!"T1-F3 basis: {repr lowered.initialBasis}"
      match evalPosBool #[0, 0, 1] lowered.expression,
            evalPosBool #[0, 1, 0] lowered.expression with
      | .ok true, .ok false => pure ()
      | a, b => throwError s!"T1-F3 values at [i,j,k]=[0,0,1]/[0,1,0]: {repr a}, {repr b}"

-- T1-F4: DifferentialTest.sameAxisNameSched's exact private donor, temporarily exposed.
private def f4pred : BoolExpr :=
  .rel .lt (.embed (.axis DifferentialTest.sameNameIter))
    (.embed (.axis DifferentialTest.sameNameFree))
private def f4term? : Option ProdTerm :=
  match DifferentialTest.sameAxisNameSched.stmts with
  | [.scan _ _ _ recur _] =>
      match recur with
      | .assign _ _ rhs :: _ =>
          match rhs.body.terms with
          | t :: _ => some { t with factors := t.factors ++ [.iverson f4pred] }
          | _ => none
      | _ => none
  | _ => none

run_cmd do
  match f4term? with
  | none => throwError "T1-F4 donor shape changed"
  | some term =>
      let lowered := lowerFactorPredicate [DifferentialTest.sameNameIter.uid]
        [DifferentialTest.sameNameFree.uid] {} term f4pred
      unless lowered.initialBasis ==
          [DifferentialTest.sameNameIter.uid, DifferentialTest.sameNameFree.uid] do
        throwError s!"T1-F4 UID basis: {repr lowered.initialBasis}"
      unless lowered.expression ==
          .rel .lt (.affine ⟨#[1, 0], 0⟩) (.affine ⟨#[0, 1], 0⟩) do
        throwError s!"T1-F4 name-based densification: {repr lowered.expression}"
      match evalPosBool #[0, 1] lowered.expression with
      | .ok true => pure ()
      | value => throwError s!"T1-F4 value at [context l, output l]=[0,1]: {repr value}"

-- T1-F5: second base assignment of ScanCompileTest.multiBaseSched, with a pinned predicate.
private def f5pred : BoolExpr :=
  .ieq
    (.iabs (.mul (.embed (.axis ScanCompileTest.axR))
      (.embed (.shift ScanCompileTest.axR (-2)))))
    (.embed (.const 1))
private def f5term? : Option ProdTerm :=
  match ScanCompileTest.multiBaseSched.stmts with
  | [.scan _ _ base _ _] =>
      match base with
      | _ :: .assign _ _ rhs :: _ =>
          match rhs.body.terms with
          | [t] => some { t with factors := t.factors ++ [.iverson f5pred] }
          | _ => none
      | _ => none
  | _ => none

run_cmd do
  match f5term? with
  | none => throwError "T1-F5 donor shape changed"
  | some term =>
      let pins := ({} : HashMap UID Int).insert ScanCompileTest.axR.uid 1
      let lowered := lowerFactorPredicate [] [] pins term f5pred
      unless lowered.initialBasis == [ScanCompileTest.axR.uid] &&
          lowered.residualBasis == [] do
        throwError s!"T1-F5 basis: {repr lowered}"
      unless lowered.expression ==
          .ieq (.iabs (.mul (.affine ⟨#[], 1⟩) (.affine ⟨#[], -1⟩)))
            (.affine ⟨#[], 1⟩) do
        throwError s!"T1-F5 structure: {repr lowered.expression}"
      match evalPosBool #[] lowered.expression with
      | .ok true => pure ()
      | value => throwError s!"T1-F5 value: {repr value}"

-- Width mismatch is a diagnostic, never a truncating zip or default coordinate.
#guard evalPosBool #[7] (.ieq (.affine ⟨#[1, 2], 0⟩) (.affine ⟨#[0, 0], 0⟩)) ==
  .error (.affineWidthMismatch 2 1)

-- The mask wrapper has a complete local output basis and deliberately no seeded coordinate.
#guard
  let mask := lowerMaskPredicate [f2i.uid]
    (.rel .eq (.embed (.axis f2i)) (.embed (.axis f2j)))
  mask.initialBasis == [f2i.uid] && mask.residualBasis == [f2i.uid] &&
    evalPosBool #[2] mask.expression == .ok false

end LeanNCD.Eval.Plan.PredicateCoordinateSpikeTest
