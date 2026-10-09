import Semantics.SourceProgramFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Program.Executor
open SourceAdmissionFixtures SourceProgramFixtures

namespace SourceProgramOutcomesTest

private inductive KeyView
  | occurrence (uid declaration statement valuation : Nat) (destination : List Nat)
  | publication (uid declaration : Nat) (coordinate : List Nat)
  deriving DecidableEq, Repr

private structure AddressView where
  uid : Nat
  declaration : Nat
  coordinate : List Nat
  deriving DecidableEq, Repr

private inductive ReadView
  | unavailable (key : KeyView) (missing : List AddressView)
  | ready (key : KeyView) (value : Option Rat)
  deriving DecidableEq, Repr

private inductive EventView
  | contribution (key : KeyView) (value : Rat)
  | publication (key : KeyView) (value : Rat)
  | undefined (key : KeyView)
  deriving DecidableEq, Repr

private structure EndpointView where
  observation : SourceProgramFixtures.Observation
  pending : List KeyView
  unpublished : List KeyView
  accumulators : List (AddressView × Rat)
  reads : List ReadView
  events : List EventView
  deriving DecidableEq, Repr

private def keyView (source : AdmittedSource) :
    Key (elaborateSource source) → KeyView
  | .occurrence t o =>
    .occurrence t.val.val (source.source.table.entry t.val).declaration
      (source.statementTag RationalReference.registry t o.1).original o.2.val.val
      (coordList _ ((elaborateSource source).destination t o.1 o.2))
  | .publication t p =>
    .publication t.val.val (source.source.table.entry t.val).declaration (coordList _ p)

private def addressView (source : AdmittedSource)
    (a : Address source.source.table.declarations) : AddressView :=
  ⟨a.1.val, (source.source.table.entry a.1).declaration, coordList _ a.2⟩

private def readView (source : AdmittedSource) :
    Program.Executor.Observation (elaborateSource source) → ReadView
  | .unavailable t o missing =>
    .unavailable (keyView source (.occurrence t o)) (missing.map (addressView source))
  | .ready t o value => .ready (keyView source (.occurrence t o)) value

private def eventView (source : AdmittedSource) : Event (elaborateSource source) → EventView
  | .contribution t o value => .contribution (keyView source (.occurrence t o)) value
  | .publication t p value => .publication (keyView source (.publication t p)) value
  | .undefined t o => .undefined (keyView source (.occurrence t o))

private def endpoint (snapshot : SourceSnapshot) (fuel : Option Nat := none) :
    Except ObservationError EndpointView := do
  let source ← (admitSource snapshot).mapError ObservationError.admission
  let result ← (runSourceDebug source fuel).mapError fun t =>
    .validation t.val (source.source.table.entry t).declaration
  let outcome := result.result.outcome
  let c := match outcome with
    | .complete c _ | .failed _ _ c | .blocked c _ _ | .exhausted c => c
  let pending := (sourceSchedule source).keys.filterMap fun key =>
    match key with
    | .occurrence t o => if o ∈ c.pending t then some (keyView source key) else none
    | .publication _ _ => none
  let unpublished := (sourceSchedule source).keys.filterMap fun key =>
    match key with
    | .occurrence _ _ => none
    | .publication t p =>
      if (c.published ⟨t.val, p⟩).isNone then some (keyView source key) else none
  let accumulators := ((sourceDefined source).sigma (sourceCoordinates source)).map fun a =>
    (addressView source ⟨a.1.val, a.2⟩, c.accumulators a.1 a.2)
  let reads := match outcome with
    | .blocked _ diagnostics _ => diagnostics.map (readView source)
    | .complete .. | .failed .. | .exhausted .. => []
  pure ⟨⟨outcomeKind source outcome, tensorObservations source outcome,
      result.result.events.length⟩, pending, unpublished, accumulators, reads,
    result.result.events.map (eventView source)⟩

private def endpointIs (snapshot : SourceSnapshot) (fuel : Option Nat)
    (expected : EndpointView) : Bool :=
  match endpoint snapshot fuel with
  | .error _ => false
  | .ok actual => actual == expected

private def cycle : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis e (some 0), .tensor "C" [i], .tensor "Empty" [e]],
      [.assign "C" [.free i] (rhs [[.read "C" [.axis i]]])], {}, ∅⟩,
    [⟨2, .output, [2]⟩, ⟨3, .input, [0]⟩], [⟨3, [0], []⟩]⟩

private def cycleKeys : List KeyView :=
  [.occurrence 0 2 0 0 [0], .occurrence 0 2 0 1 [1]]

private def cyclePublications : List KeyView :=
  [.publication 0 2 [0], .publication 0 2 [1]]

private def cycleExpected : EndpointView :=
  ⟨⟨.blocked, [⟨0, 2, "C", [2], [none, none]⟩, ⟨1, 3, "Empty", [0], []⟩], 0⟩,
    cycleKeys, cyclePublications, [(⟨0, 2, [0]⟩, 0), (⟨0, 2, [1]⟩, 0)],
    [.unavailable (.occurrence 0 2 0 0 [0]) [⟨0, 2, [0]⟩],
     .unavailable (.occurrence 0 2 0 1 [1]) [⟨0, 2, [1]⟩]], []⟩

private def cycleNeighbor : SourceSnapshot :=
  { cycle with resolved := { cycle.resolved with
      stmts := [.assign "C" [.free i] (rhs [[]])] } }

private def cycleNeighborExpected : EndpointView :=
  ⟨⟨.complete, [⟨0, 2, "C", [2], [some 1, some 1]⟩,
      ⟨1, 3, "Empty", [0], []⟩], 4⟩,
    [], [], [(⟨0, 2, [0]⟩, 1), (⟨0, 2, [1]⟩, 1)], [],
    [.contribution (.occurrence 0 2 0 0 [0]) 1,
     .contribution (.occurrence 0 2 0 1 [1]) 1,
     .publication (.publication 0 2 [0]) 1,
     .publication (.publication 0 2 [1]) 1]⟩

def P10 : Bool :=
  endpointIs cycle none cycleExpected &&
  endpointIs cycle (some 0) cycleExpected &&
  endpointIs cycleNeighbor none cycleNeighborExpected

private def scalar : SourceSnapshot :=
  ⟨⟨[.axis e (some 0), .tensor "Input" [], .tensor "Empty" [e], .tensor "S" []],
      [.assign "S" [] (rhs [[.read "Input" [], .read "Input" []]])], {}, ∅⟩,
    [⟨1, .input, []⟩, ⟨2, .input, [0]⟩, ⟨3, .output, []⟩],
    [⟨1, [], [3 / 2]⟩, ⟨2, [0], []⟩]⟩

private def scalarTensors (value : Option Rat) : List TensorObservation :=
  [⟨0, 1, "Input", [], [some (3 / 2)]⟩, ⟨1, 2, "Empty", [0], []⟩,
   ⟨2, 3, "S", [], [value]⟩]

private def scalarZeroExpected : EndpointView :=
  ⟨⟨.exhausted, scalarTensors none, 0⟩, [.occurrence 2 3 0 0 []],
    [.publication 2 3 []], [(⟨2, 3, []⟩, 0)], [], []⟩

private def scalarOneExpected : EndpointView :=
  ⟨⟨.exhausted, scalarTensors none, 1⟩, [], [.publication 2 3 []],
    [(⟨2, 3, []⟩, 9 / 4)], [], [.contribution (.occurrence 2 3 0 0 []) (9 / 4)]⟩

private def scalarCompleteExpected : EndpointView :=
  ⟨⟨.complete, scalarTensors (some (9 / 4)), 2⟩, [], [],
    [(⟨2, 3, []⟩, 9 / 4)], [],
    [.contribution (.occurrence 2 3 0 0 []) (9 / 4),
     .publication (.publication 2 3 []) (9 / 4)]⟩

private def finiteBudget (snapshot : SourceSnapshot) : Except ObservationError Nat := do
  let source ← (admitSource snapshot).mapError ObservationError.admission
  pure (initialBudget (elaborateSource source))

def P11 : Bool :=
  endpointIs scalar (some 0) scalarZeroExpected &&
  endpointIs scalar (some 1) scalarOneExpected &&
  endpointIs scalar none scalarCompleteExpected &&
  endpointIs scalar (some 2) scalarCompleteExpected &&
  match finiteBudget scalar with
  | .error _ => false
  | .ok budget => budget == 3

private def boundaries : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Scalar" [], .tensor "ZeroOut" [e],
        .tensor "Unwritten" [i], .tensor "EmptyContract" [i]]
      stmts :=
        [.assign "Diagonal" [.free i, .free i] (rhs [[]]),
         .assign "Scalar" [] (rhs [[]]),
         .assign "ZeroOut" [.free e] (rhs [[]]),
         .assign "EmptyContract" [.free i] (rhs [[.read "Empty" [.axis e]]]),
         .assign "Y" [.free i] (rhs [[.read "Diagonal" [.axis i, .axis i]]])] }
    specs := specs ++ [⟨8, .defined, []⟩, ⟨9, .output, [0]⟩,
      ⟨10, .defined, [2]⟩, ⟨11, .defined, [2]⟩] }

private def boundaryKeys : List KeyView :=
  [.occurrence 2 5 4 0 [0], .occurrence 2 5 4 1 [1],
   .occurrence 4 7 0 0 [0, 0], .occurrence 4 7 0 1 [1, 1],
   .occurrence 5 8 1 0 [],
   .occurrence 8 11 3 0 [0], .occurrence 8 11 3 1 [1],
   .publication 2 5 [0], .publication 2 5 [1],
   .publication 4 7 [0, 0], .publication 4 7 [0, 1],
   .publication 4 7 [1, 0], .publication 4 7 [1, 1],
   .publication 5 8 [], .publication 7 10 [0], .publication 7 10 [1],
   .publication 8 11 [0], .publication 8 11 [1]]

private def scheduleRows (snapshot : SourceSnapshot) :
    Except ObservationError (List Nat × List KeyView × List Bool) := do
  let source ← (admitSource snapshot).mapError ObservationError.admission
  pure ((sourceSchedule source).tensors.map Fin.val,
    (sourceSchedule source).keys.map (keyView source),
    (sourceTensors source).map fun t => (sourceInputBinding source t).isSome)

private def boundaryTensors : List TensorObservation :=
  [⟨0, 3, "A", [2, 3], [1, 2, 3, 4, 5, 6].map some⟩,
   ⟨1, 4, "B", [2], [some 10, some 20]⟩,
   ⟨2, 5, "Y", [2], [some 1, some 1]⟩,
   ⟨3, 6, "Empty", [0], []⟩,
   ⟨4, 7, "Diagonal", [2, 2], [some 1, some 0, some 0, some 1]⟩,
   ⟨5, 8, "Scalar", [], [some 1]⟩, ⟨6, 9, "ZeroOut", [0], []⟩,
   ⟨7, 10, "Unwritten", [2], [some 0, some 0]⟩,
   ⟨8, 11, "EmptyContract", [2], [some 0, some 0]⟩]

def P12 : Bool :=
  (match scheduleRows boundaries with
   | .error _ => false
   | .ok (tensors, keys, presence) =>
     tensors == List.range 9 && keys == boundaryKeys &&
     decide keys.Nodup &&
     presence == [true, true, false, true, false, false, false, false, false]) &&
  match endpoint boundaries with
  | .error _ => false
  | .ok actual =>
    actual.observation == ⟨.complete, boundaryTensors, 18⟩ &&
    actual.pending == [] && actual.unpublished == [] && actual.reads == [] &&
    actual.events.filterMap (fun event => match event with
      | .publication key value => some (key, value)
      | .contribution .. | .undefined .. => none) ==
      [(.publication 4 7 [0, 0], 1), (.publication 2 5 [0], 1),
       (.publication 4 7 [0, 1], 0), (.publication 4 7 [1, 0], 0),
       (.publication 4 7 [1, 1], 1), (.publication 2 5 [1], 1),
       (.publication 5 8 [], 1),
       (.publication 7 10 [0], 0), (.publication 7 10 [1], 0),
       (.publication 8 11 [0], 0), (.publication 8 11 [1], 0)]

private theorem boundaryKeys_nodup (source : AdmittedSource)
    (_admitted : admitSource boundaries = .ok source) :
    (sourceSchedule source).keys.Nodup :=
  (sourceSchedule source).keys_nodup

private theorem boundaryKeys_complete (source : AdmittedSource)
    (_admitted : admitSource boundaries = .ok source)
    (key : Key (elaborateSource source)) : key ∈ (sourceSchedule source).keys :=
  (sourceSchedule source).keys_complete key

private theorem boundaryTensors_nodup (source : AdmittedSource)
    (_admitted : admitSource boundaries = .ok source) :
    (sourceSchedule source).tensors.Nodup :=
  (sourceSchedule source).tensors_nodup

private theorem boundaryTensors_complete (source : AdmittedSource)
    (_admitted : admitSource boundaries = .ok source)
    (t : source.source.table.declarations.Tensor) :
    t ∈ (sourceSchedule source).tensors :=
  (sourceSchedule source).tensors_complete t

private theorem boundaryCoordinates_nodup (source : AdmittedSource)
    (_admitted : admitSource boundaries = .ok source)
    (t : (elaborateSource source).Defined) :
    (sourceCoordinates source t).Nodup :=
  sourceCoordinates_nodup source t

private theorem boundaryCoordinates_complete (source : AdmittedSource)
    (_admitted : admitSource boundaries = .ok source)
    (t : (elaborateSource source).Defined)
    (p : Coord (source.source.table.declarations.signature t.val).axes) :
    p ∈ sourceCoordinates source t :=
  sourceCoordinates_complete source t p

private theorem scalarDefault_not_exhausted (source : AdmittedSource)
    (_admitted : admitSource scalar = .ok source) :
    (run (elaborateSource source) RationalReference.ops (sourceSchedule source)
      (sourceInput source)).outcome.isExhausted = false :=
  runSource_not_exhausted source

#eval endpoint cycle
#eval endpoint cycleNeighbor
#eval endpoint scalar (some 0)
#eval endpoint scalar (some 1)
#eval endpoint scalar
#eval finiteBudget scalar
#eval scheduleRows boundaries
#eval endpoint boundaries
#eval (P10, P11, P12)
#guard P10
#guard P11
#guard P12

#print axioms boundaryKeys_nodup
#print axioms boundaryKeys_complete
#print axioms boundaryTensors_nodup
#print axioms boundaryTensors_complete
#print axioms boundaryCoordinates_nodup
#print axioms boundaryCoordinates_complete
#print axioms scalarDefault_not_exhausted

end SourceProgramOutcomesTest
