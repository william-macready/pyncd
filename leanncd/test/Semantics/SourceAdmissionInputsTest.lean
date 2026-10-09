import Semantics.SourceAdmissionFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source SourceAdmissionFixtures

namespace SourceAdmissionInputsFixtures

private def scalarWithUnused : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Unused" [i], .tensor "Scalar" []]
      stmts := [.assign "Scalar" [] (rhs [[]])] }
    specs := specs ++ [⟨8, .input, [2]⟩, ⟨9, .output, []⟩] }

private def scalarWithUnusedBound : SourceSnapshot :=
  { scalarWithUnused with inputs := inputs ++ [⟨8, [2], [31, 47]⟩] }

private structure InputView where
  declaration : Nat
  axes : List (UID × Nat)
  count : Nat
  values : List ℚ
  coordinateValues : List ℚ
  deriving DecidableEq, Repr

private def inputView (s : SourceSnapshot) : Option (List InputView) :=
  (admitSource s).toOption.map fun admitted =>
    (List.finRange admitted.source.table.entries.length).filterMap fun t =>
      let entry := admitted.source.table.entry t
      if h : entry.role = .input then
        let buffer := admitted.source.inputs.buffers t h
        some ⟨entry.declaration, entry.axes.map (fun a => (a.uid, a.extent)),
          (canonicalLayout entry.axes).count, buffer.values,
          (List.finRange (canonicalLayout entry.axes).count).map fun p =>
            buffer.value ((canonicalLayout entry.axes).enumerate p)⟩
      else none

private def failure (result : Except SourceDiagnostic α) : Option SourceDiagnostic :=
  match result with
  | .error diagnostic => some diagnostic
  | .ok _ => none

private def expectedInputs : List InputView :=
  [⟨3, [(7, 2), (3, 3)], 6, [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6]⟩,
   ⟨4, [(7, 2)], 2, [10, 20], [10, 20]⟩,
   ⟨6, [(11, 0)], 0, [], []⟩]

def a13 := admitSource scalarWithUnused

#guard match a13 with
  | .error diagnostic =>
    match diagnostic.cause with
    | .missingInput declaration =>
      declaration == 8 && diagnostic.stage == .inputs &&
        diagnostic.origin == { side := .input, declaration := some 8 }
    | _ => false
  | .ok _ => false

#guard inputView scalarWithUnusedBound =
  some (expectedInputs ++ [⟨8, [(7, 2)], 2, [31, 47], [31, 47]⟩])

set_option synthInstance.maxSize 512 in
#guard admissionView scalarWithUnusedBound = some
  ([7, 3, 11],
   [(3, .input, [2, 3]), (4, .input, [2]), (5, .output, [2]),
    (6, .input, [0]), (7, .defined, [2, 2]), (8, .input, [2]), (9, .output, [])],
   [⟨0, [], [], [⟨[], .pure, []⟩]⟩])

#eval failure a13
#eval inputView scalarWithUnusedBound

private def withoutEmptyBinding : SourceSnapshot :=
  { snapshot with inputs := inputs.filter (fun binding => binding.declaration != 6) }

def a14 := admitSource withoutEmptyBinding

#guard match a14 with
  | .error diagnostic =>
    match diagnostic.cause with
    | .missingInput declaration =>
      declaration == 6 && diagnostic.stage == .inputs &&
        diagnostic.origin == { side := .input, declaration := some 6 }
    | _ => false
  | .ok _ => false

#guard inputView { withoutEmptyBinding with inputs := inputs } = some expectedInputs

#eval failure a14
#eval inputView { withoutEmptyBinding with inputs := inputs }

private def shortMatrixBinding : SourceSnapshot :=
  { snapshot with inputs := [⟨3, [2, 3], [1, 2, 3, 4, 5]⟩] ++ inputs.drop 1 }

def a15 := admitSource shortMatrixBinding

#guard match a15 with
  | .error diagnostic =>
    match diagnostic.cause with
    | .length expected actual =>
      expected == 6 && actual == 5 && diagnostic.stage == .inputs &&
        diagnostic.origin == { side := .input, declaration := some 3 }
    | _ => false
  | .ok _ => false

#guard inputView { shortMatrixBinding with inputs := inputs } = some expectedInputs

#eval failure a15
#eval inputView { shortMatrixBinding with inputs := inputs }

end SourceAdmissionInputsFixtures
