import Semantics.SourceAdmissionFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures

namespace SourceAdmissionRolesFixtures

private def diagnosticIs (result : Except SourceDiagnostic α) (stage : SourceStage)
    (origin : SourceOrigin) (cause : SourceCause → Bool) : Bool :=
  match result with
  | .error d => d.stage == stage && d.origin == origin && cause d.cause
  | .ok _ => false

private def originals (s : SourceSnapshot) : Except SourceDiagnostic (List Nat) :=
  (admitSource s).map fun a => a.statements.map (·.original)

private def duplicateSnapshot : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with decls := decls ++ [.tensor "A" [k]] }
    specs := specs ++ [⟨8, .defined, [3]⟩] }

private def uniqueSnapshot : SourceSnapshot :=
  { duplicateSnapshot with
    resolved := { snapshot.resolved with decls := decls ++ [.tensor "Other" [k]] } }

private def raw (s : SourceSnapshot) : TLProgram :=
  ⟨s.resolved.decls, s.resolved.stmts⟩

def a10 : Bool :=
  diagnosticIs (admitSource duplicateSnapshot) .declarations
    { side := .declaration, declaration := some 8 }
    (fun c => match c with | .duplicateTensor name => name == "A" | _ => false) &&
  diagnosticIs (admitRawSource (raw duplicateSnapshot) duplicateSnapshot.specs
    duplicateSnapshot.inputs) .resolution
    { side := .declaration, declaration := some 8 }
    (fun c => match c with
      | .resolution (.duplicateTensorDecl name) => name == "A"
      | _ => false) &&
  (match admitSource uniqueSnapshot with
    | .error _ => false
    | .ok a =>
      a.source.table.entries.map (fun t => (t.declaration, t.name, t.axes.map Axis.extent)) ==
        [(3, "A", [2, 3]), (4, "B", [2]), (5, "Y", [2]), (6, "Empty", [0]),
         (7, "Diagonal", [2, 2]), (8, "Other", [3])] &&
      a.statements.map (·.original) == [0, 1, 2] &&
      (a.statements.flatMap fun st => st.terms.flatMap fun term =>
        term.sourceReads.map (·.origin.declaration)) == [some 3, some 4]) &&
  (match admitRawSource (raw uniqueSnapshot) uniqueSnapshot.specs uniqueSnapshot.inputs with
    | .error _ => false
    | .ok a => a.statements.map (·.original) == [0, 1, 2])

#guard a10
#eval a10
#eval originals duplicateSnapshot
#eval (admitRawSource (raw duplicateSnapshot) duplicateSnapshot.specs
  duplicateSnapshot.inputs).map fun a => a.statements.map (·.original)

private def scalarSnapshot (role : TensorRole) : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls.map fun d => match d with
        | .tensor "B" _ => .tensor "B" []
        | .tensor "Y" _ => .tensor "Y" []
        | _ => d
      stmts := [.assign "Diagonal" [.free i, .free i] (rhs [[]]),
        .assign "Y" [] (rhs [[.read "B" []]])] }
    specs := specs.map fun s =>
      if s.declaration == 4 then ⟨4, .input, []⟩
      else if s.declaration == 5 then ⟨5, role, []⟩ else s
    inputs := (inputs.map fun b =>
      if b.declaration == 4 then ⟨4, [], [10]⟩ else b) ++
      (if role == .input then [⟨5, [], [99]⟩] else []) }

def a11 : Bool :=
  diagnosticIs (admitSource (scalarSnapshot .input)) .output
    { side := .output, declaration := some 5, statement := some 1 }
    (fun c => match c with
      | .role expected actual => expected == .defined && actual == .input
      | _ => false) &&
  (match adaptSource (scalarSnapshot .input) with
    | .error _ => false
    | .ok a =>
      a.table.entries.map (fun t => (t.declaration, t.role, t.axes.map Axis.extent)) ==
        [(3, .input, [2, 3]), (4, .input, []), (5, .input, []), (6, .input, [0]),
         (7, .defined, [2, 2])]) &&
  (match admissionView (scalarSnapshot .output), admissionView (scalarSnapshot .defined) with
    | some (_, _, out), some (_, _, defined) =>
      out == defined && out ==
        [⟨0, [7, 7], [7], [⟨[], .broadcast, []⟩]⟩,
         ⟨1, [], [], [⟨[], .pure, [(some 0, some 0, [])]⟩]⟩]
    | _, _ => false)

#guard a11
#eval a11
#eval originals (scalarSnapshot .input)
#eval originals (scalarSnapshot .output)
#eval originals (scalarSnapshot .defined)

private def j : AxisSpec := ⟨"j", 13, .nat⟩

private def matrixSnapshot (domain : Option Nat) : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := (decls.map fun d => match d with
        | .axis a _ => if a.uid == k.uid then .axis a domain else d
        | .tensor "B" _ => .tensor "B" [k, j]
        | .tensor "Y" _ => .tensor "Y" [i, j]
        | _ => d) ++ [.axis j (some 4)]
      stmts := [.assign "Diagonal" [.free i, .free i] (rhs [[]]),
        .assign "Y" [.free i, .free j]
          (rhs [[.read "A" [.axis i, .axis k], .read "B" [.axis k, .axis j]]])] }
    specs := specs.map fun s =>
      if s.declaration == 4 then ⟨4, .input, [3, 4]⟩
      else if s.declaration == 5 then ⟨5, .output, [2, 4]⟩ else s
    inputs := inputs.map fun b =>
      if b.declaration == 4 then
        ⟨4, [3, 4], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]⟩ else b }

def a12 : Bool :=
  diagnosticIs (admitSource (matrixSnapshot none)) .declarations
    { side := .declaration, declaration := some 1 }
    (fun c => match c with | .missingDomain uid => uid == 3 | _ => false) &&
  (matrixSnapshot none).inputs.map (fun b => (b.declaration, b.shape, b.values.length)) ==
    [(3, [2, 3], 6), (4, [3, 4], 12), (6, [0], 0)] &&
  (match admissionView (matrixSnapshot (some 3)) with
    | some (axes, table, statements) =>
      axes == [7, 3, 11, 13] &&
      table == [(3, .input, [2, 3]), (4, .input, [3, 4]), (5, .output, [2, 4]),
        (6, .input, [0]), (7, .defined, [2, 2])] &&
      statements ==
        [⟨0, [7, 7], [7], [⟨[], .broadcast, []⟩]⟩,
         ⟨1, [7, 13], [7, 13],
          [⟨[3], .pure, [(some 0, some 0, [7, 3]), (some 0, some 1, [3, 13])]⟩]⟩]
    | none => false)

#guard a12
#eval a12
#eval originals (matrixSnapshot none)
#eval admissionView (matrixSnapshot (some 3))

end SourceAdmissionRolesFixtures
