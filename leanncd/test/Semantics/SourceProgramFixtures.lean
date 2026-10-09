import LeanNCD.Semantics.Source.Schedule
import LeanNCD.Semantics.Source.Oracle
import Semantics.SourceAdmissionFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Program.Executor

namespace SourceProgramFixtures

inductive ObservationError
  | admission (diagnostic : SourceDiagnostic)
  | validation (tensorUID declaration : Nat)
  deriving Repr

inductive OutcomeKind
  | complete | failed | blocked | exhausted
  deriving DecidableEq, Repr

structure TensorObservation where
  uid : Nat
  declaration : Nat
  name : String
  shape : List Nat
  values : List (Option Rat)
  deriving DecidableEq, Repr

structure Observation where
  kind : OutcomeKind
  tensors : List TensorObservation
  events : Nat
  deriving DecidableEq, Repr

def coordList : (sh : Shape) → Coord sh → List Nat
  | [], _ => []
  | _ :: sh, p => p.1.val :: coordList sh p.2

def coordAssignments : (sh : Shape) → Coord sh → List (UID × Nat)
  | [], _ => []
  | a :: sh, p => (a.uid, p.1.val) :: coordAssignments sh p.2

def published (source : AdmittedSource)
    (outcome : Outcome (elaborateSource source) RationalReference.ops) :=
  match outcome with
  | .complete c _ | .failed _ _ c | .blocked c _ _ | .exhausted c => c.published

def outcomeKind (source : AdmittedSource)
    (outcome : Outcome (elaborateSource source) RationalReference.ops) : OutcomeKind :=
  match outcome with
  | .complete .. => .complete
  | .failed .. => .failed
  | .blocked .. => .blocked
  | .exhausted .. => .exhausted

def tensorObservations (source : AdmittedSource)
    (outcome : Outcome (elaborateSource source) RationalReference.ops) :
    List TensorObservation :=
  (sourceTensors source).map fun t =>
    let entry := source.source.table.entry t
    let layout := canonicalLayout (source.source.table.declarations.signature t).axes
    ⟨t.val, entry.declaration, entry.name, entry.axes.map Axis.extent,
      (List.finRange layout.count).map fun p =>
        published source outcome ⟨t, layout.enumerate p⟩⟩

def observe (snapshot : SourceSnapshot) (fuel : Option Nat := none) :
    Except ObservationError Observation := do
  let source ← (admitSource snapshot).mapError ObservationError.admission
  let result ← (runSourceDebug source fuel).mapError fun t =>
    .validation t.val (source.source.table.entry t).declaration
  pure ⟨outcomeKind source result.result.outcome,
    tensorObservations source result.result.outcome, result.result.events.length⟩

end SourceProgramFixtures
