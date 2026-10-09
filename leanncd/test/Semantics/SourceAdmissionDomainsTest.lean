import Semantics.SourceAdmissionFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures

namespace SourceAdmissionDomainsFixtures

private def readSnapshot (first : AxisSpec) : SourceSnapshot :=
  { snapshot with resolved := { snapshot.resolved with
      stmts := stmts.take 2 ++
        [.assign "Y" [.free i] (rhs
          [[.read "B" [.axis i]],
           [.read "B" [.axis i], .read "A" [.axis first, .axis k]]])] } }

def a1 : Except SourceDiagnostic AdmittedSource := admitSource (readSnapshot k)

#guard (List.range 3).take 2 = List.range 2
#guard match a1 with
  | .error diagnostic =>
    diagnostic.stage == .read &&
    diagnostic.origin ==
      { side := .read, declaration := some 3, statement := some 2,
        term := some 1, factor := some 1, slot := some 0 } &&
    match diagnostic.cause with
    | .domain uid expected actual => uid == 3 && expected == 2 && actual == 3
    | _ => false
  | .ok _ => false

#eval a1.map (fun admitted => admitted.statements.map (fun st => st.original))

def a2 := admissionView (readSnapshot i)

set_option synthInstance.maxSize 512 in
#guard a2 = some
  ([7, 3, 11],
   [(3, .input, [2, 3]), (4, .input, [2]), (5, .output, [2]),
    (6, .input, [0]), (7, .defined, [2, 2])],
   [⟨0, [7], [7], [⟨[3], .pure, [(some 0, some 0, [7, 3])]⟩,
                    ⟨[], .pure, [(some 1, some 0, [7])]⟩]⟩,
    ⟨1, [7, 7], [7], [⟨[], .broadcast, []⟩]⟩,
    ⟨2, [7], [7], [⟨[], .pure, [(some 0, some 0, [7])]⟩,
                    ⟨[3], .pure, [(some 1, some 0, [7]),
                                   (some 1, some 1, [7, 3])]⟩]⟩])

#eval a2

private def outputSnapshot (slots : List LHSSlot) : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      stmts := stmts.take 2 ++ [.assign "A" slots (rhs [])] }
    specs := specs.map (fun spec =>
      if spec.declaration == 3 then { spec with role := .defined } else spec)
    inputs := inputs.filter (fun binding => binding.declaration != 3) }

-- The final output has both a wrong second domain and an extra third slot.
def a3 : Except SourceDiagnostic AdmittedSource :=
  admitSource (outputSnapshot [.free i, .free i, .free k])

#guard match a3 with
  | .error diagnostic =>
    diagnostic.stage == .output &&
    diagnostic.origin ==
      { side := .output, declaration := some 3, statement := some 2,
        slot := some 1 } &&
    match diagnostic.cause with
    | .domain uid expected actual => uid == 7 && expected == 3 && actual == 2
    | _ => false
  | .ok _ => false

#eval a3.map (fun admitted => admitted.statements.map (fun st => st.original))

#guard match admitSource (outputSnapshot [.free k, .free i, .free e]) with
  | .error diagnostic =>
    diagnostic.stage == .output &&
    diagnostic.origin ==
      { side := .output, declaration := some 3, statement := some 2,
        slot := some 0 } &&
    match diagnostic.cause with
    | .domain uid expected actual => uid == 3 && expected == 2 && actual == 3
    | _ => false
  | .ok _ => false

#eval (admitSource (outputSnapshot [.free k, .free i, .free e])).map
  (fun admitted => admitted.statements.map (fun st => st.original))

#guard match admitSource (outputSnapshot [.free i, .free k, .free e]) with
  | .error diagnostic =>
    diagnostic.stage == .output &&
    diagnostic.origin ==
      { side := .output, declaration := some 3, statement := some 2,
        slot := some 2 } &&
    match diagnostic.cause with
    | .rank expected actual => expected == 2 && actual == 3
    | _ => false
  | .ok _ => false

#eval (admitSource (outputSnapshot [.free i, .free k, .free e])).map
  (fun admitted => admitted.statements.map (fun st => st.original))

#guard match admitSource (outputSnapshot [.free i]) with
  | .error diagnostic =>
    diagnostic.stage == .output &&
    diagnostic.origin ==
      { side := .output, declaration := some 3, statement := some 2,
        slot := some 1 } &&
    match diagnostic.cause with
    | .rank expected actual => expected == 2 && actual == 1
    | _ => false
  | .ok _ => false

#eval (admitSource (outputSnapshot [.free i])).map
  (fun admitted => admitted.statements.map (fun st => st.original))

set_option synthInstance.maxSize 512 in
#guard admissionView (outputSnapshot [.free i, .free k]) = some
  ([7, 3, 11],
   [(3, .defined, [2, 3]), (4, .input, [2]), (5, .output, [2]),
    (6, .input, [0]), (7, .defined, [2, 2])],
   [⟨0, [7], [7], [⟨[3], .pure, [(some 0, some 0, [7, 3])]⟩,
                    ⟨[], .pure, [(some 1, some 0, [7])]⟩]⟩,
    ⟨1, [7, 7], [7], [⟨[], .broadcast, []⟩]⟩,
    ⟨2, [7, 3], [7, 3], []⟩])

#eval admissionView (outputSnapshot [.free i, .free k])

end SourceAdmissionDomainsFixtures
