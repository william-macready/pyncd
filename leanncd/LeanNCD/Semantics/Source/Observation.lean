import LeanNCD.Semantics.Source.Schedule
import LeanNCD.Semantics.Source.Provenance
import LeanNCD.Semantics.Source.ProgramCorrespondence
import LeanNCD.Semantics.Source.Oracle

namespace LeanNCD.Semantics.Source.Debug

open Program.Executor

inductive UnobservedReason
  | noTermEvaluationHook | noBackendInternalHook | notCompared
  deriving DecidableEq, Repr

inductive Evidence (α : Type)
  | observed (value : α)
  | unobserved (reason : UnobservedReason)
  deriving DecidableEq, Repr

def coordinateList : (sh : Shape) → Coord sh → List Nat
  | [], _ => []
  | _ :: sh, p => p.1.val :: coordinateList sh p.2

structure AddressObservation where
  tensorUID : UID
  declaration : Nat
  coordinate : List Nat
  deriving DecidableEq, Repr

def observeAddress (source : AdmittedSource)
    (a : Address source.source.table.declarations) : AddressObservation :=
  ⟨a.1.val, (source.source.table.entry a.1).declaration, coordinateList _ a.2⟩

structure OccurrenceKey where
  statement : Nat
  assignments : List (UID × Nat)
  deriving DecidableEq, Repr

structure TermObservation where
  origin : SourceOrigin
  factors : List (SourceOrigin × List (SourceOrigin × UID))
  contractedAxes : Shape
  value : Evidence ℚ
  contractedAssignments : Evidence (List (List (UID × Nat)))
  deriving DecidableEq, Repr

structure OccurrenceObservation where
  key : OccurrenceKey
  targetLocal : Nat
  destination : AddressObservation
  origin : SourceOrigin
  terms : List TermObservation
  deriving DecidableEq, Repr

def observeOccurrence (source : AdmittedSource) (t : (elaborateSource source).Defined)
    (o : (elaborateSource source).Occurrence t) : OccurrenceObservation :=
  let tag := source.statementTag RationalReference.registry t o.1
  ⟨⟨tag.original, outputAssignments tag.statement o.2.val⟩, o.1.val,
    observeAddress source ⟨t.val, (elaborateSource source).destination t o.1 o.2⟩,
    tag.statement.output.origin, tag.statement.terms.map fun term =>
      ⟨term.origin, term.sourceReads.map fun read =>
        (read.origin, read.indices.zipIdx.map fun (uid, slot) =>
          ({ read.origin with slot := some slot }, uid)),
        term.partition.bound, .unobserved .noTermEvaluationHook,
        .unobserved .noTermEvaluationHook⟩⟩

structure ReadDependency where
  address : AddressObservation
  origin : SourceOrigin
  slots : List (SourceOrigin × UID)
  deriving DecidableEq, Repr

/-- Metadata projection only; this does not evaluate a term in a partial store. -/
def readDependencies (source : AdmittedSource) (t : (elaborateSource source).Defined)
    (o : (elaborateSource source).Occurrence t) : List ReadDependency :=
  let tag := source.statementTag RationalReference.registry t o.1
  tag.statement.terms.flatMap fun term =>
    let layout := canonicalLayout term.partition.bound
    (List.finRange layout.count).flatMap fun p =>
      let env := term.environment (tag.valuation o.2.val) (layout.enumerate p)
      (List.finRange term.sourceReads.length).map fun i =>
        let read := term.sourceReads.get i
        ⟨observeAddress source ⟨read.read.tensor, (term.reads i).slots.project env⟩,
          read.origin, read.indices.zipIdx.map fun (uid, slot) =>
            ({ read.origin with slot := some slot }, uid)⟩

inductive KeyObservation
  | occurrence (occurrence : OccurrenceObservation)
  | publication (address : AddressObservation)
  deriving DecidableEq, Repr

def observeKey (source : AdmittedSource) : Key (elaborateSource source) → KeyObservation
  | .occurrence t o => .occurrence (observeOccurrence source t o)
  | .publication t p => .publication (observeAddress source ⟨t.val, p⟩)

inductive ReadinessObservation
  | unavailable (occurrence : OccurrenceObservation) (missing : List AddressObservation)
      (sources : List ReadDependency)
  | ready (occurrence : OccurrenceObservation) (value : Option ℚ)
  deriving DecidableEq, Repr

def observeReadiness (source : AdmittedSource) :
    Program.Executor.Observation (elaborateSource source) → ReadinessObservation
  | .unavailable t o missing =>
    let addresses := missing.map (observeAddress source)
    .unavailable (observeOccurrence source t o) addresses
      ((readDependencies source t o).filter fun read => read.address ∈ addresses)
  | .ready t o value => .ready (observeOccurrence source t o) value

inductive EventObservation
  | contribution (occurrence : OccurrenceObservation) (value : ℚ)
  | publication (address : AddressObservation) (value : ℚ)
  | undefined (occurrence : OccurrenceObservation)
  deriving DecidableEq, Repr

def observeEvent (source : AdmittedSource) : Event (elaborateSource source) → EventObservation
  | .contribution t o value => .contribution (observeOccurrence source t o) value
  | .publication t p value => .publication (observeAddress source ⟨t.val, p⟩) value
  | .undefined t o => .undefined (observeOccurrence source t o)

structure TensorObservation where
  tensorUID : UID
  declaration : Nat
  name : Option String
  role : TensorRole
  axes : Shape
  shape : List Nat
  values : List (Option ℚ)
  deriving DecidableEq, Repr

def observeTensors (source : AdmittedSource) (c : (elaborateSource source).Running) :
    List TensorObservation :=
  (sourceTensors source).map fun t =>
    let entry := source.source.table.entry t
    let layout := canonicalLayout entry.axes
    ⟨t.val, entry.declaration, some entry.name, entry.role, entry.axes,
      entry.axes.map Axis.extent,
      (List.finRange layout.count).map fun p => c.published ⟨t, layout.enumerate p⟩⟩

structure SnapshotObservation where
  tensors : List TensorObservation
  accumulators : List (AddressObservation × ℚ)
  pending : List KeyObservation
  unpublished : List AddressObservation
  eligible : List KeyObservation
  readiness : List ReadinessObservation
  deriving DecidableEq, Repr

def observeSnapshot (source : AdmittedSource) (c : (elaborateSource source).Running)
    (reads : List (Program.Executor.Observation (elaborateSource source))) :
    SnapshotObservation :=
  let schedule := sourceSchedule source
  ⟨observeTensors source c,
    ((sourceDefined source).sigma (sourceCoordinates source)).map fun a =>
      (observeAddress source ⟨a.1.val, a.2⟩, c.accumulators a.1 a.2),
    schedule.keys.filterMap fun key => match key with
      | .occurrence t o => if o ∈ c.pending t then some (observeKey source key) else none
      | .publication _ _ => none,
    schedule.keys.filterMap fun key => match key with
      | .occurrence _ _ => none
      | .publication t p =>
        if (c.published ⟨t.val, p⟩).isNone then
          some (observeAddress source ⟨t.val, p⟩) else none,
    schedule.keys.filterMap fun key =>
      if (attempt (elaborateSource source) RationalReference.ops c key).isSome then
        some (observeKey source key) else none,
    reads.map (observeReadiness source)⟩

inductive EndpointObservation
  | complete (snapshot : SnapshotObservation)
  | failed (occurrence : OccurrenceObservation) (snapshot : SnapshotObservation)
  | blocked (snapshot : SnapshotObservation)
  | exhausted (snapshot : SnapshotObservation) (requestedFuel : Option Nat)
      (executedEvents : Nat)
  deriving DecidableEq, Repr

def EndpointObservation.snapshot : EndpointObservation → SnapshotObservation
  | .complete s | .failed _ s | .blocked s | .exhausted s _ _ => s

structure ExecutionObservation where
  endpoint : EndpointObservation
  events : List EventObservation
  deriving DecidableEq, Repr

/-- Keeps the certified identity maps and actual validated execution, not just its rendering. -/
structure SourceRun where
  source : IdentifiedSource
  actual : ActualValidatedResult source.admitted
  requestedFuel : Option Nat

def SourceRun.observe (run : SourceRun) : ExecutionObservation :=
  let source := run.source.admitted
  let events := run.actual.result.events
  let endpoint := match run.actual.result.outcome with
    | .complete c _ => .complete (observeSnapshot source c [])
    | .failed t o c => .failed (observeOccurrence source t o) (observeSnapshot source c [])
    | .blocked c reads _ => .blocked (observeSnapshot source c reads)
    | .exhausted c =>
      .exhausted (observeSnapshot source c
        (observations (elaborateSource source) RationalReference.ops (sourceSchedule source) c))
        run.requestedFuel events.length
  ⟨endpoint, events.map (observeEvent source)⟩

inductive ExecutionError
  | admission (diagnostic : SourceDiagnostic)
  | inputPresence (tensorUID : UID) (origin : SourceOrigin) (expected actual : Bool)
  deriving Repr

def sourceDebug (snapshot : SourceSnapshot) (fuel : Option Nat := none) :
    Except ExecutionError SourceRun := do
  let source ← (admitIdentifiedSource snapshot).mapError ExecutionError.admission
  let actual ← (runSourceDebug source.admitted fuel).mapError fun t =>
    .inputPresence t.val
      { side := .input, declaration := some (source.admitted.source.table.entry t).declaration }
      ((elaborateSource source.admitted).input t)
      ((sourceInputBinding source.admitted t).isSome)
  pure ⟨source, actual, fuel⟩

structure ContributionObservation where
  key : OccurrenceKey
  destination : AddressObservation
  value : Option ℚ
  deriving DecidableEq, Repr

def assignmentsLE : List (UID × Nat) → List (UID × Nat) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a.1 != b.1 then a.1 < b.1
    else if a.2 != b.2 then a.2 < b.2
    else assignmentsLE as bs

def occurrenceKeyLE (a b : OccurrenceKey) : Bool :=
  if a.statement != b.statement then a.statement < b.statement
  else assignmentsLE a.assignments b.assignments

def canonicalizeContributions (rows : List ContributionObservation) :
    List ContributionObservation :=
  rows.mergeSort fun a b => occurrenceKeyLE a.key b.key

def canonicalContributions (events : List EventObservation) : List ContributionObservation :=
  canonicalizeContributions (events.filterMap fun event => match event with
    | .contribution o v => some ⟨o.key, o.destination, some v⟩
    | .undefined o => some ⟨o.key, o.destination, none⟩
    | .publication .. => none)

inductive NormalizationCause
  | missingStatement | unknownStatement (statement : Nat) | ambiguousStatement (statement : Nat)
  | targetDeclaration (expected : Nat) (actual : Option Nat)
  | rank (expected actual : Nat)
  | slotMetadataRank (uidSlots axisSlots coordinateSlots : Nat)
  | coordinateBound (slot coordinate extent : Nat)
  deriving DecidableEq, Repr

structure NormalizationError where
  origin : SourceOrigin
  cause : NormalizationCause
  deriving DecidableEq, Repr

/-- An oracle row is a full cell fiber; an inconsistent repeated output has no occurrence.
An empty contracted fiber still has an output occurrence with contribution zero. -/
structure OracleRow where
  fullCell : Oracle.Contribution
  occurrence : Option ContributionObservation
  deriving DecidableEq, Repr

def normalizeOracleContribution (source : AdmittedSource) (row : Oracle.Contribution) :
    Except NormalizationError OracleRow := do
  let original ← match row.origin.statement with
    | none => throw ⟨row.origin, .missingStatement⟩
    | some i => pure i
  let statement ← match source.statements.filter (fun st => st.original == original) with
    | [] => throw ⟨row.origin, .unknownStatement original⟩
    | [st] => pure st
    | _ => throw ⟨row.origin, .ambiguousStatement original⟩
  let entry := source.source.table.entry statement.output.tensor
  unless row.origin.declaration == some entry.declaration do
    throw ⟨row.origin, .targetDeclaration entry.declaration row.origin.declaration⟩
  unless row.coordinate.length == entry.axes.length do
    throw ⟨row.origin, .rank entry.axes.length row.coordinate.length⟩
  unless statement.output.indices.length == row.coordinate.length do
    throw ⟨row.origin, .rank statement.output.indices.length row.coordinate.length⟩
  let assignment ← assign statement.output.indices entry.axes row.coordinate 0 [] true
  pure ⟨row, assignment.map fun values =>
    ⟨⟨original, values⟩, ⟨statement.output.tensor.val, entry.declaration, row.coordinate⟩,
      some row.value⟩⟩
where
  assign : List UID → Shape → List Nat → Nat → List (UID × Nat) → Bool →
      Except NormalizationError (Option (List (UID × Nat)))
    | [], [], [], _, values, consistent => .ok (if consistent then some values else none)
    | uid :: ids, axis :: axes, coordinate :: coordinates, slot, values, consistent => do
      unless coordinate < axis.extent do
        throw ⟨{ row.origin with slot := some slot },
          .coordinateBound slot coordinate axis.extent⟩
      match values.find? (fun p => p.1 == uid) with
      | none => assign ids axes coordinates (slot + 1) (values ++ [(uid, coordinate)]) consistent
      | some p => assign ids axes coordinates (slot + 1) values (consistent && p.2 == coordinate)
    | ids, axes, coordinates, _, _, _ =>
      .error ⟨row.origin, .slotMetadataRank ids.length axes.length coordinates.length⟩

def normalizeOracle (source : AdmittedSource) (result : Oracle.Result) :
    Except NormalizationError (List OracleRow) :=
  result.contributions.mapM (normalizeOracleContribution source)

end LeanNCD.Semantics.Source.Debug
