import Semantics.SourceDiagnosticFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Debug LeanNCD.Semantics.Program.Executor
open SourceAdmissionFixtures SourceDiagnosticFixtures

namespace SourceDiagnosticExecutionTest

private theorem validatedExecution (run : SourceRun) :
    Execution (elaborateSource run.source.admitted) RationalReference.ops
      run.actual.result.events
      (.running ((elaborateSource run.source.admitted).initial run.actual.input))
      run.actual.result.outcome.state :=
  run.actual.result.execution

private def cycle : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis e (some 0),
      .typedTensor .f64 "C" [i], .typedTensor .f64 "Empty" [e]],
    [.assign "C" [.free i] (rhs [[.read "C" [.axis i]]])], {}, ∅⟩,
    [⟨2, .output, [2]⟩, ⟨3, .input, [0]⟩], [⟨3, [0], []⟩]⟩

private def cycleRead : SourceOrigin :=
  { side := .read, declaration := some 2, statement := some 0,
    term := some 0, factor := some 0 }

private def cycleOccurrence (coordinate : Nat) : OccurrenceObservation :=
  ⟨⟨0, [(7, coordinate)]⟩, 0, ⟨0, 2, [coordinate]⟩,
    { side := .output, declaration := some 2, statement := some 0 },
    [⟨{ side := .read, statement := some 0, term := some 0 },
      [(cycleRead, [({ cycleRead with slot := some 0 }, 7)])], [],
      .unobserved .noTermEvaluationHook, .unobserved .noTermEvaluationHook⟩]⟩

private def blockedSnapshot : SnapshotObservation :=
  ⟨[⟨0, 2, some "C", .output, [⟨7, 2⟩], [2], [none, none]⟩,
    ⟨1, 3, some "Empty", .input, [⟨11, 0⟩], [0], []⟩],
    [(⟨0, 2, [0]⟩, 0), (⟨0, 2, [1]⟩, 0)],
    [.occurrence (cycleOccurrence 0), .occurrence (cycleOccurrence 1)],
    [⟨0, 2, [0]⟩, ⟨0, 2, [1]⟩], [],
    [0, 1].map fun coordinate =>
      .unavailable (cycleOccurrence coordinate) [⟨0, 2, [coordinate]⟩]
        [⟨⟨0, 2, [coordinate]⟩, cycleRead,
          [({ cycleRead with slot := some 0 }, 7)]⟩]⟩

def D4 : Bool :=
  match sourceDebug cycle, sourceDebug cycle (some 0) with
  | .ok run, .ok zero =>
    match run.observe.endpoint, zero.observe.endpoint,
        Oracle.run run.source.admitted none,
        Oracle.run run.source.admitted (some [2]) with
    | .blocked actual, .blocked atZero, .error missingOrder, .error cyclicOrder =>
      actual == blockedSnapshot && atZero == blockedSnapshot &&
      run.requestedFuel == none && zero.requestedFuel == some 0 &&
      run.observe.events == [] && zero.observe.events == [] &&
      missingOrder.origin == ({} : SourceOrigin) && missingOrder.cause == .missingOrder &&
      cyclicOrder.origin == cycleRead && cyclicOrder.cause == .dependencyNotEarlier 2 &&
      renderSourceDebug (.ok run) ==
        s!"blocked (no no-model inference)\nendpoint={repr (EndpointObservation.blocked blockedSnapshot)}\nevents={repr ([] : List EventObservation)}"
    | _, _, _, _ => false
  | _, _ => false

private def scalarOccurrence : OccurrenceObservation :=
  ⟨⟨0, []⟩, 0, ⟨1, 1, []⟩,
    { side := .output, declaration := some 1, statement := some 0 },
    [⟨{ side := .read, statement := some 0, term := some 0 },
      [({ side := .read, declaration := some 0, statement := some 0,
          term := some 0, factor := some 0 }, [])], [],
      .unobserved .noTermEvaluationHook, .unobserved .noTermEvaluationHook⟩]⟩

private def scalarTensors (value : Option Rat) : List Debug.TensorObservation :=
  [⟨0, 0, some "A", .input, [], [], [some 3]⟩,
   ⟨1, 1, some "Y", .output, [], [], [value]⟩]

private def scalarZero : SnapshotObservation :=
  ⟨scalarTensors none, [(⟨1, 1, []⟩, 0)],
    [.occurrence scalarOccurrence], [⟨1, 1, []⟩], [.occurrence scalarOccurrence],
    [.ready scalarOccurrence (some 3)]⟩

private def scalarOne : SnapshotObservation :=
  ⟨scalarTensors none, [(⟨1, 1, []⟩, 3)], [], [⟨1, 1, []⟩],
    [.publication ⟨1, 1, []⟩], []⟩

private def scalarComplete : SnapshotObservation :=
  ⟨scalarTensors (some 3), [(⟨1, 1, []⟩, 3)], [], [], [], []⟩

private def scalarEvents : List EventObservation :=
  [.contribution scalarOccurrence 3, .publication ⟨1, 1, []⟩ 3]

def D5 : Bool :=
  match sourceDebug scalarSnapshot (some 0), sourceDebug scalarSnapshot (some 1),
      sourceDebug scalarSnapshot, sourceDebug scalarSnapshot (some 2) with
  | .ok zero, .ok one, .ok full, .ok exact =>
    match zero.observe.endpoint, one.observe.endpoint,
        full.observe.endpoint, exact.observe.endpoint with
    | .exhausted z (some 0) 0, .exhausted o (some 1) 1, .complete f, .complete x =>
      z == scalarZero && o == scalarOne && f == scalarComplete && x == scalarComplete &&
      zero.requestedFuel == some 0 && one.requestedFuel == some 1 &&
      full.requestedFuel == none && exact.requestedFuel == some 2 &&
      zero.observe.events == [] && one.observe.events == scalarEvents.take 1 &&
      full.observe.events == scalarEvents && exact.observe.events == scalarEvents &&
      renderSourceDebug (.ok zero) ==
        s!"exhausted (no no-model inference)\nendpoint={repr (EndpointObservation.exhausted scalarZero (some 0) 0)}\nevents={repr ([] : List EventObservation)}" &&
      renderSourceDebug (.ok one) ==
        s!"exhausted (no no-model inference)\nendpoint={repr (EndpointObservation.exhausted scalarOne (some 1) 1)}\nevents={repr (scalarEvents.take 1)}"
    | _, _, _, _ => false
  | _, _, _, _ => false

private def reorderedSnapshot : SourceSnapshot :=
  { vectorSnapshot with resolved := { vectorSnapshot.resolved with
      stmts := stmts.take 2 ++
        [.assign "Y" [.free i] (rhs [[.read "Empty" [.axis e]]])] } }

private def reorderedRuns : Except ExecutionError (SourceRun × SourceRun) := do
  let forward ← sourceDebug reorderedSnapshot
  let source := forward.source.admitted
  let actual ← (runValidated (elaborateSource source) RationalReference.ops
    (sourceSchedule source).reverse (sourceInputBinding source)).mapError fun t =>
      .inputPresence t.val
        { side := .input, declaration := some (source.source.table.entry t).declaration }
        ((elaborateSource source).input t)
        ((sourceInputBinding source t).isSome)
  pure (forward, ⟨forward.source, actual, none⟩)

private def expectedContributions : List ContributionObservation :=
  [⟨⟨0, [(7, 0)]⟩, ⟨2, 5, [0]⟩, some 16⟩,
   ⟨⟨0, [(7, 1)]⟩, ⟨2, 5, [1]⟩, some 35⟩,
   ⟨⟨1, [(7, 0)]⟩, ⟨4, 7, [0, 0]⟩, some 1⟩,
   ⟨⟨1, [(7, 1)]⟩, ⟨4, 7, [1, 1]⟩, some 1⟩,
   ⟨⟨2, [(7, 0)]⟩, ⟨2, 5, [0]⟩, some 0⟩,
   ⟨⟨2, [(7, 1)]⟩, ⟨2, 5, [1]⟩, some 0⟩]

private def vectorTensors : List Debug.TensorObservation :=
  [⟨0, 3, some "A", .input, [⟨7, 2⟩, ⟨3, 3⟩], [2, 3],
      [1, 2, 3, 4, 5, 6].map some⟩,
   ⟨1, 4, some "B", .input, [⟨7, 2⟩], [2], [some 10, some 20]⟩,
   ⟨2, 5, some "Y", .output, [⟨7, 2⟩], [2], [some 16, some 35]⟩,
   ⟨3, 6, some "Empty", .input, [⟨11, 0⟩], [0], []⟩,
   ⟨4, 7, some "Diagonal", .defined, [⟨7, 2⟩, ⟨7, 2⟩], [2, 2],
      [some 1, some 0, some 0, some 1]⟩]

private def vectorComplete : SnapshotObservation :=
  ⟨vectorTensors,
    [(⟨2, 5, [0]⟩, 16), (⟨2, 5, [1]⟩, 35),
     (⟨4, 7, [0, 0]⟩, 1), (⟨4, 7, [0, 1]⟩, 0),
     (⟨4, 7, [1, 0]⟩, 0), (⟨4, 7, [1, 1]⟩, 1)], [], [], [], []⟩

def D6 : Bool :=
  match reorderedRuns with
  | .error _ => false
  | .ok (forward, reversed) =>
    match forward.observe.endpoint, reversed.observe.endpoint,
        Oracle.run forward.source.admitted (some [7, 5]) with
    | .complete f, .complete r, .ok oracle =>
      match normalizeOracle forward.source.admitted oracle,
          Differential.oracleTensors forward.source.admitted oracle with
      | .ok rows, .ok oracleBindings =>
        f == vectorComplete && r == vectorComplete && oracleBindings == vectorTensors &&
        forward.observe.events.length == 12 && reversed.observe.events.length == 12 &&
        forward.observe.events != reversed.observe.events &&
        (match forward.observe.events.head?, reversed.observe.events.head? with
          | some (.contribution occurrence value), some (.publication address published) =>
            value == 16 && published == 0 && occurrence.key == ⟨0, [(7, 0)]⟩ &&
            occurrence.targetLocal == 0 && occurrence.destination == ⟨2, 5, [0]⟩ &&
            address == ⟨4, 7, [1, 0]⟩
          | _, _ => false) &&
        canonicalContributions forward.observe.events == expectedContributions &&
        canonicalContributions reversed.observe.events == expectedContributions &&
        compareContributions (canonicalContributions forward.observe.events)
          (canonicalContributions reversed.observe.events) == .ok .agreement &&
        rows.map (·.fullCell) == oracle.contributions &&
        rows.map (fun row =>
          (row.fullCell.origin.statement, row.fullCell.coordinate,
            row.fullCell.value, row.occurrence)) ==
          [(some 0, [0], 16, some ⟨⟨0, [(7, 0)]⟩, ⟨2, 5, [0]⟩, some 16⟩),
           (some 0, [1], 35, some ⟨⟨0, [(7, 1)]⟩, ⟨2, 5, [1]⟩, some 35⟩),
           (some 1, [0, 0], 1, some ⟨⟨1, [(7, 0)]⟩, ⟨4, 7, [0, 0]⟩, some 1⟩),
           (some 1, [0, 1], 0, none),
           (some 1, [1, 0], 0, none),
           (some 1, [1, 1], 1, some ⟨⟨1, [(7, 1)]⟩, ⟨4, 7, [1, 1]⟩, some 1⟩),
           (some 2, [0], 0, some ⟨⟨2, [(7, 0)]⟩, ⟨2, 5, [0]⟩, some 0⟩),
           (some 2, [1], 0, some ⟨⟨2, [(7, 1)]⟩, ⟨2, 5, [1]⟩, some 0⟩)] &&
        (rows.filter fun row => row.fullCell.origin.statement == some 2).all
          (fun row => match row.fullCell.terms with
            | [term] => term.occurrences.isEmpty && term.value == 0
            | _ => false) &&
        oracleContributions rows == expectedContributions &&
        compareContributions (canonicalContributions reversed.observe.events)
          (oracleContributions rows) == .ok .agreement &&
        compareTensors f.tensors r.tensors == .ok .agreement &&
        compareTensors r.tensors oracleBindings == .ok .agreement
      | _, _ => false
    | _, _, _ => false

#guard D4
#guard D5
#guard D6

#eval D4
#eval (sourceDebug cycle).map SourceRun.observe
#eval (sourceDebug cycle).map fun run => Oracle.run run.source.admitted none
#eval (sourceDebug cycle).map fun run => Oracle.run run.source.admitted (some [2])
#eval renderSourceDebug (sourceDebug cycle)
#eval D5
#eval (sourceDebug scalarSnapshot (some 0)).map SourceRun.observe
#eval (sourceDebug scalarSnapshot (some 1)).map SourceRun.observe
#eval (sourceDebug scalarSnapshot).map SourceRun.observe
#eval (sourceDebug scalarSnapshot (some 2)).map SourceRun.observe
#eval renderSourceDebug (sourceDebug scalarSnapshot (some 0))
#eval renderSourceDebug (sourceDebug scalarSnapshot (some 1))
#eval D6
#eval reorderedRuns.map fun (forward, reversed) => (forward.observe, reversed.observe)
#eval reorderedRuns.map fun (forward, reversed) =>
  (canonicalContributions forward.observe.events, canonicalContributions reversed.observe.events,
    compareContributions (canonicalContributions forward.observe.events)
      (canonicalContributions reversed.observe.events))
#eval reorderedRuns.map fun (forward, _) =>
  (Oracle.run forward.source.admitted (some [7, 5])).map fun oracle =>
    (oracle, normalizeOracle forward.source.admitted oracle)

end SourceDiagnosticExecutionTest
