import Semantics.SourceProgramFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Program.Executor
open SourceAdmissionFixtures SourceProgramFixtures

namespace SourceProgramGeometryTest

private inductive KeyView
  | occurrence (uid declaration statement valuation : Nat) (coordinate : List Nat)
  | publication (uid declaration : Nat) (coordinate : List Nat)
  deriving DecidableEq, Repr

private def keyView (source : AdmittedSource) :
    Key (elaborateSource source) → KeyView
  | .occurrence t o =>
    .occurrence t.val.val (source.source.table.entry t.val).declaration o.1.val o.2.val.val
      (coordList _ ((source.statementTag RationalReference.registry t o.1).valuation o.2.val))
  | .publication t p =>
    .publication t.val.val (source.source.table.entry t.val).declaration (coordList _ p)

private theorem canonicalCoverage (source : AdmittedSource) :
    (sourceSchedule source).tensors.Nodup ∧
      (∀ t, t ∈ (sourceSchedule source).tensors) ∧
      (sourceSchedule source).keys.Nodup ∧
      (∀ key, key ∈ (sourceSchedule source).keys) :=
  ⟨(sourceSchedule source).tensors_nodup, (sourceSchedule source).tensors_complete,
    (sourceSchedule source).keys_nodup, (sourceSchedule source).keys_complete⟩

private def geometry : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis k (some 3), .axis e (some 0),
      .tensor "A" [i, k], .tensor "Scalar" [], .tensor "Line" [k],
      .tensor "Grid" [i, k], .tensor "Dead" [i], .tensor "Zero" [e]],
      [.assign "Scalar" [] (rhs [[]]),
       .assign "Line" [.free k] (rhs [[.read "A" [.axis i, .axis k]]]),
       .assign "Grid" [.free i, .free k] (rhs [[.read "A" [.axis i, .axis k]]]),
       .assign "Zero" [.free e] (rhs [[]])], {}, ∅⟩,
    [⟨3, .input, [2, 3]⟩, ⟨4, .defined, []⟩, ⟨5, .output, [3]⟩,
     ⟨6, .output, [2, 3]⟩, ⟨7, .defined, [2]⟩, ⟨8, .output, [0]⟩],
    [⟨3, [2, 3], [1, 2, 3, 4, 5, 6]⟩]⟩

private def scheduleObservation :
    Except SourceDiagnostic (List (Nat × Nat × String × List Nat) × List KeyView) := do
  let source ← admitSource geometry
  let schedule := sourceSchedule source
  pure (schedule.tensors.map (fun t =>
      let entry := source.source.table.entry t
      (t.val, entry.declaration, entry.name, entry.axes.map Axis.extent)),
    schedule.keys.map (keyView source))

private def geometryTensors : List (Nat × Nat × String × List Nat) :=
  [(0, 3, "A", [2, 3]), (1, 4, "Scalar", []), (2, 5, "Line", [3]),
   (3, 6, "Grid", [2, 3]), (4, 7, "Dead", [2]), (5, 8, "Zero", [0])]

private def geometryKeys : List KeyView :=
  [.occurrence 1 4 0 0 [],
   .occurrence 2 5 0 0 [0], .occurrence 2 5 0 1 [1], .occurrence 2 5 0 2 [2],
   .occurrence 3 6 0 0 [0, 0], .occurrence 3 6 0 1 [0, 1],
   .occurrence 3 6 0 2 [0, 2], .occurrence 3 6 0 3 [1, 0],
   .occurrence 3 6 0 4 [1, 1], .occurrence 3 6 0 5 [1, 2],
   .publication 1 4 [],
   .publication 2 5 [0], .publication 2 5 [1], .publication 2 5 [2],
   .publication 3 6 [0, 0], .publication 3 6 [0, 1], .publication 3 6 [0, 2],
   .publication 3 6 [1, 0], .publication 3 6 [1, 1], .publication 3 6 [1, 2],
   .publication 4 7 [0], .publication 4 7 [1]]

def P7 : Bool :=
  match scheduleObservation with
  | .error _ => false
  | .ok (tensors, keys) =>
    tensors == geometryTensors && keys == geometryKeys &&
      decide (tensors.Nodup ∧ keys.Nodup)

#guard P7
#eval P7
#eval scheduleObservation

private def allInputs : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Unused" [i], .tensor "Scalar" []]
      stmts := [.assign "Scalar" [] (rhs [[]])] }
    specs := specs ++ [⟨8, .input, [2]⟩, ⟨9, .output, []⟩]
    inputs := inputs ++ [⟨8, [2], [31, 47]⟩] }

private structure InputView where
  uid : Nat
  declaration : Nat
  present : Bool
  shape : List Nat
  values : List Rat
  deriving DecidableEq, Repr

private def inputPresence : Except SourceDiagnostic (List InputView) := do
  let source ← admitSource allInputs
  pure ((sourceTensors source).map fun t =>
    let entry := source.source.table.entry t
    let layout := canonicalLayout (source.source.table.declarations.signature t).axes
    match sourceInputBinding source t with
    | some value =>
      ⟨t.val, entry.declaration, true, entry.axes.map Axis.extent,
        (List.finRange layout.count).map fun p => value (layout.enumerate p)⟩
    | none => ⟨t.val, entry.declaration, false, entry.axes.map Axis.extent, []⟩)

private def expectedPresence : List InputView :=
  [⟨0, 3, true, [2, 3], [1, 2, 3, 4, 5, 6]⟩,
   ⟨1, 4, true, [2], [10, 20]⟩, ⟨2, 5, false, [2], []⟩,
   ⟨3, 6, true, [0], []⟩, ⟨4, 7, false, [2, 2], []⟩,
   ⟨5, 8, true, [2], [31, 47]⟩, ⟨6, 9, false, [], []⟩]

private def expectedInputStore : SourceProgramFixtures.Observation :=
  ⟨.complete,
    [⟨0, 3, "A", [2, 3], [1, 2, 3, 4, 5, 6].map some⟩,
     ⟨1, 4, "B", [2], [some 10, some 20]⟩,
     ⟨2, 5, "Y", [2], [some 0, some 0]⟩,
     ⟨3, 6, "Empty", [0], []⟩,
     ⟨4, 7, "Diagonal", [2, 2], [some 0, some 0, some 0, some 0]⟩,
     ⟨5, 8, "Unused", [2], [some 31, some 47]⟩,
     ⟨6, 9, "Scalar", [], [some 1]⟩], 8⟩

private def omitInput (declaration : Nat) : SourceSnapshot :=
  { allInputs with
    inputs := allInputs.inputs.filter (fun binding => binding.declaration != declaration) }

private def omissionKeepsOrigin (declaration : Nat) : Bool :=
  match observe (omitInput declaration) with
  | .error (.admission diagnostic) =>
    match diagnostic.cause with
    | .missingInput original =>
      original == declaration && diagnostic.stage == .inputs &&
        diagnostic.origin == { side := .input, declaration := some declaration }
    | _ => false
  | .error (.validation ..) | .ok _ => false

def P8 : Bool :=
  (match inputPresence with
    | .error _ => false
    | .ok actual => actual == expectedPresence) &&
  (match observe allInputs with
    | .error _ => false
    | .ok actual => actual == expectedInputStore) &&
  omissionKeepsOrigin 8 && omissionKeepsOrigin 6

#guard P8
#eval P8
#eval inputPresence
#eval observe allInputs
#eval observe (omitInput 8)
#eval observe (omitInput 6)

private def nested : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis k (some 3), .axis e (some 0),
      .tensor "A" [i, k], .tensor "B" [i], .tensor "S" []],
      [.assign "S" []
        (rhs [[.read "A" [.axis i, .axis k], .read "B" [.axis i],
          .read "A" [.axis i, .axis k]]])], {}, ∅⟩,
    [⟨3, .input, [2, 3]⟩, ⟨4, .input, [2]⟩, ⟨5, .output, []⟩],
    [⟨3, [2, 3], [1 / 3, 2 / 3, 5, 10, 25, 45]⟩, ⟨4, [2], [2, 7]⟩]⟩

private def reductionBounds {σ : Declarations Unit} :
    {Γ : Type} → Expr RationalReference.Carrier σ RationalReference.registry Γ (.scalar ()) →
      List Nat
  | _, .reduce n body => n :: reductionBounds body
  | _, .binary _ left right => reductionBounds left ++ reductionBounds right
  | _, _ => []

private structure AddressView where
  uid : Nat
  declaration : Nat
  coordinate : List Nat
  deriving DecidableEq, Repr

private structure BodyView where
  uid : Nat
  statement : Nat
  valuation : Nat
  destination : List Nat
  binders : List Nat
  value : Option Rat
  reads : List AddressView
  missingReadBlocks : Bool
  deriving DecidableEq, Repr

private def bodyViews (source : AdmittedSource)
    (c : (elaborateSource source).Running) (complete : (elaborateSource source).Complete c) :
    List BodyView :=
  let p := elaborateSource source
  let store := p.finalStore c complete
  (sourceDefined source).flatMap fun t =>
    (sourceOccurrences source t).map fun o =>
      let body := p.body t o.1
      let masked : PartialStore RationalReference.Carrier source.source.table.declarations :=
        fun a => if a.1.val == 0 && coordList _ a.2 == [1, 2] then none else c.published a
      ⟨t.val.val, (source.statementTag RationalReference.registry t o.1).original,
        o.2.val.val, coordList _ (p.destination t o.1 o.2), reductionBounds body,
        interpret RationalReference.ops store body o.2,
        (footprint body o.2).map fun a =>
          ⟨a.1.val, (source.source.table.entry a.1).declaration, coordList _ a.2⟩,
        match evalReady RationalReference.ops masked body o.2 with
        | .notReady => true
        | .evaluated _ => false⟩

private inductive NestedError
  | observation (error : ObservationError)
  | oracle (error : Oracle.Unavailable)
  deriving Repr

private structure NestedView where
  observation : SourceProgramFixtures.Observation
  boundAxes : List (List (UID × Nat))
  bodies : List BodyView
  oracle : Oracle.Result
  deriving Repr

private def nestedObservation : Except NestedError NestedView := do
  let source ← (admitSource nested).mapError (fun d => .observation (.admission d))
  let result ← (runSource source).mapError fun t =>
    .observation (.validation t.val (source.source.table.entry t).declaration)
  let oracle ← (Oracle.run source (some [5])).mapError NestedError.oracle
  let outcome := result.result.outcome
  let bodies := match outcome with
    | .complete c complete => bodyViews source c complete
    | .failed .. | .blocked .. | .exhausted .. => []
  pure ⟨⟨outcomeKind source outcome, tensorObservations source outcome,
      result.result.events.length⟩,
    source.statements.flatMap (fun st =>
      st.terms.map fun term => term.partition.bound.map fun a => (a.uid, a.extent)),
    bodies, oracle⟩

private def nestedReads : List AddressView :=
  [⟨0, 3, [0, 0]⟩, ⟨1, 4, [0]⟩, ⟨0, 3, [0, 0]⟩,
   ⟨0, 3, [0, 1]⟩, ⟨1, 4, [0]⟩, ⟨0, 3, [0, 1]⟩,
   ⟨0, 3, [0, 2]⟩, ⟨1, 4, [0]⟩, ⟨0, 3, [0, 2]⟩,
   ⟨0, 3, [1, 0]⟩, ⟨1, 4, [1]⟩, ⟨0, 3, [1, 0]⟩,
   ⟨0, 3, [1, 1]⟩, ⟨1, 4, [1]⟩, ⟨0, 3, [1, 1]⟩,
   ⟨0, 3, [1, 2]⟩, ⟨1, 4, [1]⟩, ⟨0, 3, [1, 2]⟩]

private def nestedStore : SourceProgramFixtures.Observation :=
  ⟨.complete,
    [⟨0, 3, "A", [2, 3], [1 / 3, 2 / 3, 5, 10, 25, 45].map some⟩,
     ⟨1, 4, "B", [2], [some 2, some 7]⟩,
     ⟨2, 5, "S", [], [some (173710 / 9)]⟩], 2⟩

def P9 : Bool :=
  match nestedObservation with
  | .error _ => false
  | .ok actual =>
    actual.observation == nestedStore &&
    actual.boundAxes == [[(7, 2), (3, 3)]] &&
    actual.bodies == [⟨2, 0, 0, [], [2, 3], some (173710 / 9), nestedReads, true⟩] &&
    actual.oracle.tensors ==
      [⟨3, "A", .input, [2, 3], [1 / 3, 2 / 3, 5, 10, 25, 45]⟩,
       ⟨4, "B", .input, [2], [2, 7]⟩, ⟨5, "S", .output, [], [173710 / 9]⟩] &&
    actual.observation.tensors.map (fun t => (t.declaration, t.name, t.shape, t.values)) ==
      actual.oracle.tensors.map (fun t => (t.declaration, t.name, t.shape, t.values.map some))

#guard P9
#eval P9
#eval nestedObservation

end SourceProgramGeometryTest
