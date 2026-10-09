import Semantics.SourceProgramFixtures
import LeanNCD.Semantics.Source.Provenance

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Program.Executor
open SourceAdmissionFixtures SourceProgramFixtures

namespace SourceProgramCollectionTest

private structure ContributionView where
  uid : Nat
  declaration : Nat
  sourceIndex : Nat
  identity : Nat × List (UID × Nat)
  destination : List Nat
  reads : List (Nat × List Nat)
  value : Rat
  deriving DecidableEq, Repr

private structure PublicationView where
  uid : Nat
  declaration : Nat
  coordinate : List Nat
  value : Rat
  deriving DecidableEq, Repr

private structure ExecutionView where
  observation : SourceProgramFixtures.Observation
  contributions : List ContributionView
  publications : List PublicationView
  deriving DecidableEq, Repr

private def execution (snapshot : SourceSnapshot) :
    Except ObservationError ExecutionView := do
  let identified ← (admitIdentifiedSource snapshot).mapError ObservationError.admission
  let source := identified.admitted
  let result ← (runSource source).mapError fun t =>
    .validation t.val (source.source.table.entry t).declaration
  let contributions := result.result.events.filterMap fun event =>
    match event with
    | .contribution t o value =>
      let tag := source.statementTag RationalReference.registry t o.1
      some (⟨t.val.val, (source.source.table.entry t.val).declaration,
        tag.sourceIndex.val, tag.occurrenceIdentity o.2.val,
        coordList _ ((elaborateSource source).destination t o.1 o.2),
        (footprint ((elaborateSource source).body t o.1) o.2).map
          (fun a => (a.1.val, coordList _ a.2)), value⟩ : ContributionView)
    | .publication .. | .undefined .. => none
  let publications := result.result.events.filterMap fun event =>
    match event with
    | .publication t p value =>
      some (⟨t.val.val, (source.source.table.entry t.val).declaration,
        coordList _ p, value⟩ : PublicationView)
    | .contribution .. | .undefined .. => none
  pure ⟨⟨outcomeKind source result.result.outcome,
      tensorObservations source result.result.outcome, result.result.events.length⟩,
    contributions, publications⟩

private def oracleMatches (actual : SourceProgramFixtures.Observation)
    (oracle : Oracle.Result) : Bool :=
  actual.tensors.map (fun t => (t.declaration, t.name, t.shape, t.values)) ==
    oracle.tensors.map (fun t => (t.declaration, t.name, t.shape, t.values.map some))

private def baseTensors (y diagonal : List Rat) : List TensorObservation :=
  [⟨0, 3, "A", [2, 3], [1, 2, 3, 4, 5, 6].map some⟩,
   ⟨1, 4, "B", [2], [some 10, some 20]⟩,
   ⟨2, 5, "Y", [2], y.map some⟩,
   ⟨3, 6, "Empty", [0], []⟩,
   ⟨4, 7, "Diagonal", [2, 2], diagonal.map some⟩]

private def duplicateStatement : Stmt :=
  .assign "Y" [.free i] (rhs [[.read "B" [.axis i], .read "B" [.axis i]]])

private def duplicate : SourceSnapshot :=
  { snapshot with resolved := { snapshot.resolved with
      stmts := [duplicateStatement, duplicateStatement] } }

private def oneCopy : SourceSnapshot :=
  { duplicate with resolved := { duplicate.resolved with stmts := [duplicateStatement] } }

private def duplicateContributions : List ContributionView :=
  [⟨2, 5, 0, (0, [(7, 0)]), [0], [(1, [0]), (1, [0])], 100⟩,
   ⟨2, 5, 0, (0, [(7, 1)]), [1], [(1, [1]), (1, [1])], 400⟩,
   ⟨2, 5, 1, (1, [(7, 0)]), [0], [(1, [0]), (1, [0])], 100⟩,
   ⟨2, 5, 1, (1, [(7, 1)]), [1], [(1, [1]), (1, [1])], 400⟩]

def P4 : Bool :=
  match execution duplicate, execution oneCopy with
  | .ok actual, .ok neighbor =>
    actual.observation == ⟨.complete, baseTensors [200, 800] [0, 0, 0, 0], 10⟩ &&
    neighbor.observation == ⟨.complete, baseTensors [100, 400] [0, 0, 0, 0], 8⟩ &&
    actual.observation.tensors != neighbor.observation.tensors &&
    actual.contributions == duplicateContributions &&
    neighbor.contributions == duplicateContributions.take 2 &&
    actual.publications.filter (fun p => p.declaration == 5) ==
      [⟨2, 5, [0], 200⟩, ⟨2, 5, [1], 800⟩]
  | _, _ => false

private def chain : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Mid" [i, k], .tensor "End" [k, i]]
      stmts := stmts ++
        [.assign "End" [.free k, .free i]
          (rhs [[.read "Mid" [.axis i, .axis k], .read "B" [.axis i]]]),
         .assign "Mid" [.free i, .free k]
          (rhs [[.read "A" [.axis i, .axis k], .read "B" [.axis i]]])] }
    specs := specs ++ [⟨8, .defined, [2, 3]⟩, ⟨9, .output, [3, 2]⟩] }

private def chainTensors : List TensorObservation :=
  baseTensors [16, 35] [1, 0, 0, 1] ++
    [⟨5, 8, "Mid", [2, 3], [10, 20, 30, 80, 100, 120].map some⟩,
     ⟨6, 9, "End", [3, 2], [100, 1600, 200, 2000, 300, 2400].map some⟩]

private def midPublications : List PublicationView :=
  [⟨5, 8, [0, 0], 10⟩, ⟨5, 8, [0, 1], 20⟩, ⟨5, 8, [0, 2], 30⟩,
   ⟨5, 8, [1, 0], 80⟩, ⟨5, 8, [1, 1], 100⟩, ⟨5, 8, [1, 2], 120⟩]

private def endContributions : List ContributionView :=
  [⟨6, 9, 3, (3, [(3, 0), (7, 0)]), [0, 0], [(5, [0, 0]), (1, [0])], 100⟩,
   ⟨6, 9, 3, (3, [(3, 0), (7, 1)]), [0, 1], [(5, [1, 0]), (1, [1])], 1600⟩,
   ⟨6, 9, 3, (3, [(3, 1), (7, 0)]), [1, 0], [(5, [0, 1]), (1, [0])], 200⟩,
   ⟨6, 9, 3, (3, [(3, 1), (7, 1)]), [1, 1], [(5, [1, 1]), (1, [1])], 2000⟩,
   ⟨6, 9, 3, (3, [(3, 2), (7, 0)]), [2, 0], [(5, [0, 2]), (1, [0])], 300⟩,
   ⟨6, 9, 3, (3, [(3, 2), (7, 1)]), [2, 1], [(5, [1, 2]), (1, [1])], 2400⟩]

def P5 : Bool :=
  match execution chain, admitSource chain with
  | .ok actual, .ok source =>
    match Oracle.run source (some [5, 7, 8, 9]) with
    | .error _ => false
    | .ok oracle =>
      let consumed := actual.contributions.filter (fun c => c.declaration == 9)
      actual.observation == ⟨.complete, chainTensors, 36⟩ &&
      oracleMatches actual.observation oracle &&
      actual.publications.filter (fun p => p.declaration == 8) == midPublications &&
      consumed.length == endContributions.length &&
      endContributions.all (fun c => decide (c ∈ consumed)) &&
      (source.source.table.entries.filter (fun t => t.declaration == 8)).map
        (fun t => t.role) == [.defined]
  | _, _ => false

private def unwritten : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Unwritten" [i, k], .tensor "UnwrittenScalar" [],
        .tensor "UnwrittenOutput" [k], .tensor "WrittenNonoutput" [k, i]]
      stmts := stmts ++
        [.assign "WrittenNonoutput" [.free k, .free i]
          (rhs [[.read "A" [.axis i, .axis k]]]),
         .assign "Y" [.free i] (rhs [[.read "Unwritten" [.axis i, .axis k]]])] }
    specs := specs ++ [⟨8, .defined, [2, 3]⟩, ⟨9, .defined, []⟩,
      ⟨10, .output, [3]⟩, ⟨11, .defined, [3, 2]⟩] }

private def unwrittenTensors : List TensorObservation :=
  baseTensors [16, 35] [1, 0, 0, 1] ++
    [⟨5, 8, "Unwritten", [2, 3], (List.replicate 6 (0 : Rat)).map some⟩,
     ⟨6, 9, "UnwrittenScalar", [], [some 0]⟩,
     ⟨7, 10, "UnwrittenOutput", [3], [some 0, some 0, some 0]⟩,
     ⟨8, 11, "WrittenNonoutput", [3, 2], [1, 4, 2, 5, 3, 6].map some⟩]

private def unwrittenPublications : List PublicationView :=
  [⟨5, 8, [0, 0], 0⟩, ⟨5, 8, [0, 1], 0⟩, ⟨5, 8, [0, 2], 0⟩,
   ⟨5, 8, [1, 0], 0⟩, ⟨5, 8, [1, 1], 0⟩, ⟨5, 8, [1, 2], 0⟩,
   ⟨6, 9, [], 0⟩, ⟨7, 10, [0], 0⟩, ⟨7, 10, [1], 0⟩, ⟨7, 10, [2], 0⟩]

private def unwrittenConsumption : List ContributionView :=
  [⟨2, 5, 4, (4, [(7, 0)]), [0], [(5, [0, 0]), (5, [0, 1]), (5, [0, 2])], 0⟩,
   ⟨2, 5, 4, (4, [(7, 1)]), [1], [(5, [1, 0]), (5, [1, 1]), (5, [1, 2])], 0⟩]

def P6 : Bool :=
  match execution unwritten, admitSource unwritten with
  | .ok actual, .ok source =>
    match Oracle.run source (some [8, 5, 7, 9, 10, 11]) with
    | .error _ => false
    | .ok oracle =>
      actual.observation == ⟨.complete, unwrittenTensors, 36⟩ &&
      oracleMatches actual.observation oracle &&
      actual.publications.length == 22 &&
      actual.publications.filter (fun p =>
        p.declaration == 8 || p.declaration == 9 || p.declaration == 10) ==
        unwrittenPublications &&
      actual.contributions.filter (fun c => c.sourceIndex == 4) == unwrittenConsumption &&
      (source.source.table.entries.filter (fun t =>
        t.declaration == 8 || t.declaration == 9 || t.declaration == 10)).map
        (fun t => t.role) == [.defined, .defined, .output] &&
      (source.statements.filter (fun st =>
        let declaration := (source.source.table.entry st.output.tensor).declaration
        declaration == 8 || declaration == 9 || declaration == 10)).isEmpty
  | _, _ => false

#guard P4
#guard P5
#guard P6

#eval (P4, execution duplicate, execution oneCopy)
#eval (P5, execution chain,
  (admitSource chain).map (fun s => Oracle.run s (some [5, 7, 8, 9])))
#eval (P6, execution unwritten,
  (admitSource unwritten).map (fun s => Oracle.run s (some [8, 5, 7, 9, 10, 11])))

end SourceProgramCollectionTest
