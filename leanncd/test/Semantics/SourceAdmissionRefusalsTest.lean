import Semantics.SourceAdmissionFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures

namespace SourceAdmissionRefusalsFixtures

private def wrongShapeAndLength : SourceSnapshot :=
  { snapshot with
    inputs := inputs.map fun binding =>
      if binding.declaration == 3 then
        { binding with shape := [3, 2], values := [1, 2, 3, 4, 5] }
      else binding }

def A16 : Except SourceDiagnostic AdmittedSource :=
  admitSource wrongShapeAndLength

#guard (admissionView snapshot).isSome
#guard wrongShapeAndLength.inputs.map (fun binding =>
    (binding.declaration, binding.shape, binding.values.length)) =
  [(3, [3, 2], 5), (4, [2], 2), (6, [0], 0)]

#guard match A16 with
  | .error diagnostic =>
    match diagnostic.cause with
    | .shape expected actual =>
      diagnostic.stage == .inputs && expected == [2, 3] && actual == [3, 2] &&
        diagnostic.origin == { side := .input, declaration := some 3 }
    | _ => false
  | .ok _ => false

#guard match admitSource { wrongShapeAndLength with
    inputs := wrongShapeAndLength.inputs.map fun binding =>
      if binding.declaration == 3 then { binding with shape := [2, 3] }
      else binding } with
  | .error diagnostic =>
    match diagnostic.cause with
    | .length expected actual =>
      diagnostic.stage == .inputs && expected == 6 && actual == 5 &&
        diagnostic.origin == { side := .input, declaration := some 3 }
    | _ => false
  | .ok _ => false

#eval match A16 with
  | .error diagnostic => IO.println (reprStr diagnostic)
  | .ok _ => throw (IO.userError "A16: expected shape refusal")

private def scalarSnapshot (factor : Factor) : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Scalar" []]
      stmts := stmts ++ [
        .assign "Scalar" [] (rhs [
          [.read "A" [.axis i, .axis k]],
          [.read "A" [.axis i, .axis k], .read "B" [.axis i],
           factor, .read "B" [.axis i]]])] }
    specs := specs ++ [⟨8, .output, []⟩] }

-- Distinct nonzero locators separate statement, term, and factor provenance.
#guard ((admissionView (scalarSnapshot (.read "A" [.axis i, .axis k]))).map
    fun view => view.2.2.drop 3) = some [
  (⟨3, [], [], [
    ⟨[7, 3], .pure, [(some 0, some 0, [7, 3])]⟩,
    ⟨[7, 3], .pure, [
      (some 1, some 0, [7, 3]), (some 1, some 1, [7]),
      (some 1, some 2, [7, 3]), (some 1, some 3, [7])]⟩]⟩ : StatementView)]

#eval ((admissionView (scalarSnapshot (.read "A" [.axis i, .axis k]))).map
  fun view => view.2.2.drop 3)

def A17 : Except SourceDiagnostic AdmittedSource :=
  admitSource (scalarSnapshot
    (.iverson (.rel .lt (.embed (.axis i)) (.embed (.axis k)))))

#guard match A17 with
  | .error diagnostic =>
    match diagnostic.cause with
    | .unsupported .iverson =>
      diagnostic.stage == .read &&
        diagnostic.origin == {
          side := .read, statement := some 3, term := some 1, factor := some 2 }
    | _ => false
  | .ok _ => false

#eval match A17 with
  | .error diagnostic => IO.println (reprStr diagnostic)
  | .ok _ => throw (IO.userError "A17: expected Iverson refusal")

def A18 : Except SourceDiagnostic AdmittedSource :=
  admitSource (scalarSnapshot (.unaryFn .log "A" [.axis i, .axis k]))

#guard match A18 with
  | .error diagnostic =>
    match diagnostic.cause with
    | .unsupported .unary =>
      diagnostic.stage == .read &&
        diagnostic.origin == {
          side := .read, statement := some 3, term := some 1, factor := some 2 }
    | _ => false
  | .ok _ => false

#eval match A18 with
  | .error diagnostic => IO.println (reprStr diagnostic)
  | .ok _ => throw (IO.userError "A18: expected unary refusal")

end SourceAdmissionRefusalsFixtures
