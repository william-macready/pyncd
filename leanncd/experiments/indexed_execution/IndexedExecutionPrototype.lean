import LeanNCD.Semantics.RationalReference

namespace IndexedExecution

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

variable {σ : Declarations Unit}
variable (P : Program RationalReference.Carrier σ RationalReference.registry)
variable [DecidableEq σ.Tensor]

abbrev Occurrence := (t : P.Defined) × P.Occurrence t
abbrev DefinedAddress := (t : P.Defined) × Coord (σ.signature t.val).axes

def occurrenceEq : DecidableEq (Occurrence P) :=
  letI : ∀ t : P.Defined, DecidableEq (P.Occurrence t) := fun _ => inferInstance
  inferInstance

def definedAddressEq : DecidableEq (DefinedAddress P) :=
  letI : ∀ t : P.Defined, DecidableEq (Coord (σ.signature t.val).axes) :=
    fun t => coordDecidableEq (σ.signature t.val).axes
  inferInstance

def addressOf (a : DefinedAddress P) : Address σ := ⟨a.1.val, a.2⟩

def destination (o : Occurrence P) : DefinedAddress P :=
  ⟨o.1, P.destination o.1 o.2.1 o.2.2⟩

inductive Node
  | evaluate (tag : Occurrence P) (reads : List (Address σ))
      (destination : DefinedAddress P)
  | collect (address : DefinedAddress P) (writers : List (Occurrence P))

structure Fragment where
  nodes : List (Node P)

def Fragment.append (a b : Fragment P) : Fragment P := ⟨a.nodes ++ b.nodes⟩

def occurrences (schedule : Schedule P) : List (Occurrence P) :=
  schedule.keys.filterMap fun
    | .occurrence t o => some ⟨t, o⟩
    | .publication _ _ => none

def writers (schedule : Schedule P) (a : DefinedAddress P) : List (Occurrence P) :=
  letI := definedAddressEq P
  (occurrences P schedule).filter fun o => decide (destination P o = a)

def fragment (schedule : Schedule P) : Fragment P :=
  ⟨schedule.keys.map fun
    | .occurrence t o =>
        .evaluate ⟨t, o⟩ (footprint (P.body t o.1) o.2)
          (destination P ⟨t, o⟩)
    | .publication t p =>
        .collect ⟨t, p⟩ (writers P schedule ⟨t, p⟩)⟩

def sameNode (a b : Node P) : Bool :=
  letI := occurrenceEq P
  letI := definedAddressEq P
  match a, b with
  | .evaluate o _ _, .evaluate v _ _ => decide (o = v)
  | .collect x _, .collect y _ => decide (x = y)
  | _, _ => false

def samePorts (a b : Node P) : Bool :=
  letI := occurrenceEq P
  letI := definedAddressEq P
  letI := Program.Executor.addressEq (σ := σ)
  match a, b with
  | .evaluate o reads dst, .evaluate v expectedReads expectedDst =>
      decide (o = v) && decide (reads = expectedReads) && decide (dst = expectedDst)
  | .collect x writers, .collect y expectedWriters =>
      decide (x = y) && decide (writers = expectedWriters)
  | _, _ => false

inductive GraphError
  | nodeCount
  | duplicateNode
  | missingNode
  | ports
  deriving DecidableEq, Repr

def close (schedule : Schedule P) (f : Fragment P) : Except GraphError (List (Node P)) := Id.run do
  let expected := (fragment P schedule).nodes
  if f.nodes.length != expected.length then return .error .nodeCount
  if f.nodes.any (fun n => (f.nodes.filter (sameNode P n)).length != 1) then
    return .error .duplicateNode
  if expected.any (fun n => !(f.nodes.any (sameNode P n))) then return .error .missingNode
  if f.nodes.any (fun n => !(expected.any (samePorts P n))) then return .error .ports
  return .ok f.nodes

structure State where
  available : PartialStore RationalReference.Carrier σ
  produced : List (Occurrence P × ℚ)
  failure : Option (Occurrence P)

def initial (η : InputBinding (K := RationalReference.Carrier) (σ := σ)) : State P :=
  ⟨fun a => (η a.1).map (fun value => value a.2), [], none⟩

def producedValue (state : State P) (o : Occurrence P) : Option ℚ :=
  letI := occurrenceEq P
  ((state.produced.find? fun row => decide (row.1 = o))).map Prod.snd

def enabled (state : State P) : Node P → Bool
  | .evaluate o reads _ =>
      (producedValue P state o).isNone && reads.all (fun a => (state.available a).isSome)
  | .collect a writers =>
      (state.available (addressOf P a)).isNone &&
        writers.all (fun o => (producedValue P state o).isSome)

def matchesKey (key : Key P) (node : Node P) : Bool :=
  letI := occurrenceEq P
  letI := definedAddressEq P
  match key, node with
  | .occurrence t o, .evaluate tag _ _ => decide (tag = ⟨t, o⟩)
  | .publication t p, .collect a _ => decide (a = ⟨t, p⟩)
  | _, _ => false

def ordered (schedule : Schedule P) (nodes : List (Node P)) : List (Node P) :=
  schedule.keys.filterMap fun key => nodes.find? (matchesKey P key)

def complete (nodes : List (Node P)) (state : State P) : Bool :=
  nodes.all fun
    | .evaluate o _ _ => (producedValue P state o).isSome
    | .collect a _ => (state.available (addressOf P a)).isSome

def missingReads (nodes : List (Node P)) (state : State P) :
    List (Occurrence P × List (Address σ)) :=
  nodes.filterMap fun
    | .evaluate o reads _ =>
        if (producedValue P state o).isSome then none
        else some (o, reads.filter fun a => (state.available a).isNone)
    | .collect _ _ => none

inductive Event
  | produced (o : Occurrence P) (value : ℚ)
  | sealed (a : DefinedAddress P) (value : ℚ)
  | undefined (o : Occurrence P)

inductive Outcome
  | complete (state : State P)
  | failed (o : Occurrence P) (state : State P)
  | blocked (state : State P) (missing : List (Occurrence P × List (Address σ)))
  | exhausted (state : State P)
  | invalidInput (tensor : σ.Tensor)
  | invalidGraph (error : GraphError)
  | contractMismatch (o : Occurrence P) (state : State P)
  | collectorMismatch (a : DefinedAddress P) (state : State P)
  | unsupported (reason : String)

def Outcome.kind : Outcome P → String
  | .complete _ => "complete"
  | .failed _ _ => "failed"
  | .blocked _ _ => "blocked"
  | .exhausted _ => "exhausted"
  | .invalidInput _ => "invalidInput"
  | .invalidGraph _ => "invalidGraph"
  | .contractMismatch _ _ => "contractMismatch"
  | .collectorMismatch _ _ => "collectorMismatch"
  | .unsupported _ => "unsupported"

structure Run where
  outcome : Outcome P
  events : List (Event P)
  states : List (State P)

private def stepFuel (nodes : List (Node P)) : Nat → State P → Run P
  | fuel, state =>
    if complete P nodes state then ⟨.complete state, [], [state]⟩
    else
      match nodes.find? (enabled P state) with
      | none => ⟨.blocked state (missingReads P nodes state), [], [state]⟩
      | some node =>
        match fuel with
        | 0 => ⟨.exhausted state, [], [state]⟩
        | fuel + 1 =>
          match node with
          | .evaluate o _ _ =>
            match evalReady RationalReference.ops state.available
                (P.body o.1 o.2.1) o.2.2 with
            | .notReady => ⟨.contractMismatch o state, [], [state]⟩
            | .evaluated none =>
                let failed := { state with failure := some o }
                ⟨.failed o failed, [.undefined o], [state, failed]⟩
            | .evaluated (some value) =>
                let next := { state with produced := state.produced ++ [(o, value)] }
                let tail := stepFuel nodes fuel next
                ⟨tail.outcome, .produced o value :: tail.events, state :: tail.states⟩
          | .collect a writers =>
            match writers.mapM (producedValue P state) with
            | none => ⟨.collectorMismatch a state, [], [state]⟩
            | some values =>
                let value := values.foldl (· + ·) (0 : ℚ)
                letI := Program.Executor.addressEq (σ := σ)
                let next := { state with
                  available := Function.update state.available (addressOf P a) (some value) }
                let tail := stepFuel nodes fuel next
                ⟨tail.outcome, .sealed a value :: tail.events, state :: tail.states⟩

def run (schedule : Schedule P)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ))
    (f : Fragment P := fragment P schedule) (fuel : Option Nat := none) : Run P :=
  match close P schedule f with
  | .error error => ⟨.invalidGraph error, [], []⟩
  | .ok nodes =>
    match schedule.tensors.find? (fun t => (η t).isSome != P.input t) with
    | some t => ⟨.invalidInput t, [], []⟩
    | none =>
      let priority := ordered P schedule nodes
      stepFuel P priority (fuel.getD (nodes.length + 1)) (initial P η)

def addresses (schedule : Schedule P) : List (Address σ) :=
  schedule.tensors.flatMap fun t =>
    let layout := canonicalLayout (σ.signature t).axes
    (List.finRange layout.count).map fun i => ⟨t, layout.enumerate i⟩

def definedAddresses (schedule : Schedule P) : List (DefinedAddress P) :=
  schedule.keys.filterMap fun
    | .publication t p => some ⟨t, p⟩
    | .occurrence _ _ => none

structure Snapshot where
  presence : List (σ.Tensor × Bool)
  available : List (Address σ × Option ℚ)
  accumulators : List (DefinedAddress P × ℚ)
  pending : List (Occurrence P)

def graphSnapshot (schedule : Schedule P)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ))
    (state : State P) : Snapshot P :=
  ⟨schedule.tensors.map fun t => (t, (η t).isSome),
    (addresses P schedule).map fun a => (a, state.available a),
    (definedAddresses P schedule).map fun a =>
      (a, (writers P schedule a).foldl
        (fun sum o => sum + (producedValue P state o).getD 0) 0),
    (occurrences P schedule).filter fun o => (producedValue P state o).isNone⟩

def referenceSnapshot (schedule : Schedule P) (input : P.Input)
    (state : P.MachineState) : Snapshot P :=
  let c := match state with
    | .running c | .failed _ _ c => c
  ⟨schedule.tensors.map fun t => (t, (input.val t).isSome),
    (addresses P schedule).map fun a => (a, c.published a),
    (definedAddresses P schedule).map fun a => (a, c.accumulators a.1 a.2),
    (occurrences P schedule).filter fun o => o.2 ∈ c.pending o.1⟩

def sameSnapshot (a b : Snapshot P) : Bool :=
  letI := occurrenceEq P
  letI := definedAddressEq P
  letI := Program.Executor.addressEq (σ := σ)
  decide (a.presence = b.presence) &&
    decide (a.available = b.available) &&
    decide (a.accumulators = b.accumulators) &&
    decide (a.pending = b.pending)

abbrev EventRow := String × Option (Occurrence P) × Option (DefinedAddress P) × Option ℚ

def graphEventRow : Event P → EventRow P
  | .produced o v => ("produced", some o, none, some v)
  | .sealed a v => ("sealed", none, some a, some v)
  | .undefined o => ("undefined", some o, none, none)

def referenceEventRow : Program.Executor.Event P → EventRow P
  | .contribution t o v => ("produced", some ⟨t, o⟩, none, some v)
  | .publication t p v => ("sealed", none, some ⟨t, p⟩, some v)
  | .undefined t o => ("undefined", some ⟨t, o⟩, none, none)

def replayReference (start : P.MachineState) :
    List (Program.Executor.Event P) → List P.MachineState
  | [] => [start]
  | e :: events =>
      start :: replayReference
        (match start with
         | .running c => e.effect P c
         | .failed t o c => .failed t o c) events

def sameEvents (left : List (Event P))
    (right : List (Program.Executor.Event P)) : Bool :=
  letI := occurrenceEq P
  letI := definedAddressEq P
  decide (left.map (graphEventRow P) = right.map (referenceEventRow P))

structure Comparison where
  terminal : Bool
  snapshots : Bool
  events : Bool
  blockedReads : Bool
  deriving Repr

def Comparison.agrees (c : Comparison) : Bool :=
  c.terminal && c.snapshots && c.events && c.blockedReads

def compare (schedule : Schedule P)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ))
    (candidate : Run P)
    (reference : Except σ.Tensor (ValidatedResult P RationalReference.ops)) : Comparison :=
  letI := occurrenceEq P
  let invalidInput := match candidate.outcome, reference with
    | .invalidInput t, .error u => decide (t = u)
    | _, _ => false
  match reference with
  | .error _ => ⟨invalidInput, candidate.states.isEmpty, candidate.events.isEmpty, true⟩
  | .ok actual =>
    let refResult := actual.result
    let terminal := match candidate.outcome, refResult.outcome with
      | .complete _, .complete _ _ => true
      | .failed o _, .failed t v _ => decide (o = ⟨t, v⟩)
      | .blocked _ _, .blocked _ _ _ => true
      | _, _ => false
    let referenceStates :=
      replayReference P (.running (P.initial actual.input)) refResult.events
    let snapshots :=
      candidate.states.length == referenceStates.length &&
        (candidate.states.zip referenceStates).all fun (g, r) =>
          sameSnapshot P (graphSnapshot P schedule η g)
            (referenceSnapshot P schedule actual.input r)
    let blockedReads := match candidate.outcome, refResult.outcome with
      | .blocked _ missing, .blocked _ observations _ =>
          letI := Program.Executor.addressEq (σ := σ)
          decide (missing = observations.filterMap fun
            | .unavailable t o addresses => some (⟨t, o⟩, addresses)
            | .ready _ _ _ => none)
      | _, _ => true
    ⟨terminal, snapshots, sameEvents P candidate.events refResult.events, blockedReads⟩

end IndexedExecution
