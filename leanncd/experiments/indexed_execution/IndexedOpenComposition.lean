import LeanNCD.Semantics.RationalReference

namespace IndexedOpenComposition

open LeanNCD.Semantics
open LeanNCD.Semantics.Program

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]

abbrev Body (σ : Declarations Unit) :=
  Expr RationalReference.Carrier σ RationalReference.registry Unit (.scalar ())

structure Writer (σ : Declarations Unit) where
  tag : Nat
  capability : Nat
  destination : Address σ
  reads : List (Address σ)
  body : Body σ

structure Fragment (σ : Declarations Unit) where
  writers : List (Writer σ)

/- Closure is relative to this independently supplied finite contract.
   Public Nat capability IDs are collision-checked, not unforgeable. -/
structure Contract (σ : Declarations Unit) where
  tensors : List σ.Tensor
  input : σ.Tensor → Bool
  collectors : List (Address σ × List Nat)
  readable : List (Address σ)
  outputs : List (Address σ)

inductive Error
  | duplicateTensor | missingTensor | duplicateCollector | missingCollector
  | inputCollector | invalidReadable | invalidOutput
  | duplicateContractCapability | duplicateTag | duplicateCapability
  | missingCapability | extraCapability | wrongDestination
  | badFootprint | unreadableRead | alreadySealed
  deriving DecidableEq, Repr

private def addressEq : DecidableEq (Address σ) :=
  Program.Executor.addressEq (σ := σ)

private def duplicateTags (writers : List (Writer σ)) : Bool :=
  writers.any fun w => (writers.filter fun v => v.tag == w.tag).length > 1

private def duplicateCapabilities (writers : List (Writer σ)) : Bool :=
  writers.any fun w =>
    (writers.filter fun v => v.capability == w.capability).length > 1

def combine (a b : Fragment σ) : Except Error (Fragment σ) :=
  let writers := a.writers ++ b.writers
  if duplicateTags writers then .error .duplicateTag
  else if duplicateCapabilities writers then .error .duplicateCapability
  else .ok ⟨writers⟩

def definedAddresses (contract : Contract σ) : List (Address σ) :=
  (contract.tensors.filter (fun t => !contract.input t)).flatMap
    fun t =>
      let layout := canonicalLayout (σ.signature t).axes
      (List.finRange layout.count).map fun i => ⟨t, layout.enumerate i⟩

private def readable (contract : Contract σ) (a : Address σ) : Bool :=
  letI := addressEq (σ := σ)
  contract.readable.any (fun port => decide (port = a))

inductive Step (σ : Declarations Unit)
  | write (writer : Writer σ)
  | collect (address : Address σ) (capabilities : List Nat)

structure Closed (σ : Declarations Unit) where
  contract : Contract σ
  steps : List (Step σ)

def validateWriter (contract : Contract σ) (w : Writer σ) : Except Error Unit := do
  letI : DecidableEq (Address σ) := addressEq (σ := σ)
  match contract.collectors.find? (fun row => row.2.contains w.capability) with
  | none => throw .extraCapability
  | some row => do
      if !(decide (w.destination = row.1)) then throw .wrongDestination
      if !(decide (w.reads = footprint w.body ())) then throw .badFootprint
      if !(w.reads.all (readable contract)) then throw .unreadableRead
      return ()

def validateWriters (contract : Contract σ) : List (Writer σ) → Except Error Unit
  | [] => .ok ()
  | w :: ws => do
    validateWriter contract w
    validateWriters contract ws

def close (contract : Contract σ) (fragment : Fragment σ) :
    Except Error (Closed σ) :=
  letI : DecidableEq (Address σ) := addressEq (σ := σ)
  Id.run do
    if !(decide (contract.tensors.Nodup)) then return .error .duplicateTensor
    if contract.tensors.length != Fintype.card σ.Tensor then return .error .missingTensor
    let targets := contract.collectors.map Prod.fst
    if !(decide (targets.Nodup)) then return .error .duplicateCollector
    if contract.collectors.any (fun row => contract.input row.1.1) then
      return .error .inputCollector
    if !(definedAddresses contract).all
        (fun a => targets.any (fun target => decide (target = a))) then
      return .error .missingCollector
    if !(decide (contract.readable.Nodup)) ||
        !(contract.readable.all
          (fun a => contract.input a.1 ||
            targets.any (fun target => decide (target = a)))) then
      return .error .invalidReadable
    if !(decide (contract.outputs.Nodup)) ||
        !(contract.outputs.all
          (fun a => targets.any (fun target => decide (target = a)))) then
      return .error .invalidOutput
    let capabilities := contract.collectors.flatMap Prod.snd
    if !(decide (capabilities.Nodup)) then return .error .duplicateContractCapability
    if duplicateTags fragment.writers then return .error .duplicateTag
    if duplicateCapabilities fragment.writers then return .error .duplicateCapability
    if capabilities.any (fun cap =>
        !(fragment.writers.any fun w => w.capability == cap)) then
      return .error .missingCapability
    if fragment.writers.any (fun w => !(capabilities.contains w.capability)) then
      return .error .extraCapability
    if let .error error := validateWriters contract fragment.writers then
      return .error error
    let steps := contract.collectors.flatMap fun row =>
      (row.2.filterMap fun cap =>
        fragment.writers.find? (fun w => w.capability == cap)).map Step.write ++
        [Step.collect row.1 row.2]
    return .ok ⟨contract, steps⟩

inductive Assembly (σ : Declarations Unit)
  | open (fragment : Fragment σ)
  | sealed (graph : Closed σ)

def extend (assembly : Assembly σ) (fragment : Fragment σ) :
    Except Error (Assembly σ) :=
  match assembly with
  | .open existing => (combine existing fragment).map Assembly.open
  | .sealed _ => .error .alreadySealed

def sealAssembly (contract : Contract σ) (assembly : Assembly σ) :
    Except Error (Assembly σ) :=
  match assembly with
  | .open fragment => (close contract fragment).map Assembly.sealed
  | .sealed _ => .error .alreadySealed

structure State (σ : Declarations Unit) where
  available : Address σ → Option ℚ
  produced : List (Nat × ℚ)

def initial (η : InputBinding (K := RationalReference.Carrier) (σ := σ)) : State σ :=
  ⟨fun a => (η a.1).map (fun values => values a.2), []⟩

def producedValue (state : State σ) (capability : Nat) : Option ℚ :=
  (state.produced.find? fun row => row.1 == capability).map Prod.snd

def enabled (state : State σ) : Step σ → Bool
  | .write w =>
      (producedValue state w.capability).isNone &&
        w.reads.all (fun a => (state.available a).isSome)
  | .collect a caps =>
      (state.available a).isNone &&
        caps.all (fun cap => (producedValue state cap).isSome)

def complete (steps : List (Step σ)) (state : State σ) : Bool :=
  steps.all fun
    | .write w => (producedValue state w.capability).isSome
    | .collect a _ => (state.available a).isSome

def missingReads (steps : List (Step σ)) (state : State σ) :
    List (Nat × List (Address σ)) :=
  steps.filterMap fun
    | .write w =>
        if (producedValue state w.capability).isSome then none
        else some (w.tag, w.reads.filter fun a => (state.available a).isNone)
    | .collect _ _ => none

inductive Event (σ : Declarations Unit)
  | produced (tag capability : Nat) (value : ℚ)
  | sealed (address : Address σ) (value : ℚ)
  | undefined (tag : Nat)

inductive Outcome (σ : Declarations Unit)
  | complete (state : State σ)
  | failed (tag : Nat) (state : State σ)
  | blocked (state : State σ) (missing : List (Nat × List (Address σ)))
  | exhausted (state : State σ)
  | invalidInput (tensor : σ.Tensor)
  | invalidGraph (error : Error)
  | contractMismatch (tag : Nat) (state : State σ)
  | collectorMismatch (address : Address σ) (state : State σ)

def Outcome.kind : Outcome σ → String
  | .complete _ => "complete"
  | .failed _ _ => "failed"
  | .blocked _ _ => "blocked"
  | .exhausted _ => "exhausted"
  | .invalidInput _ => "invalidInput"
  | .invalidGraph _ => "invalidGraph"
  | .contractMismatch _ _ => "contractMismatch"
  | .collectorMismatch _ _ => "collectorMismatch"

structure Run (σ : Declarations Unit) where
  outcome : Outcome σ
  events : List (Event σ)
  states : List (State σ)

def stepFuel (steps : List (Step σ)) : Nat → State σ → Run σ
  | fuel, state =>
    if complete steps state then ⟨.complete state, [], [state]⟩
    else
      match steps.find? (enabled state) with
      | none => ⟨.blocked state (missingReads steps state), [], [state]⟩
      | some step =>
        match fuel with
        | 0 => ⟨.exhausted state, [], [state]⟩
        | fuel + 1 =>
          match step with
          | .write w =>
            match evalReady RationalReference.ops state.available w.body () with
            | .notReady => ⟨.contractMismatch w.tag state, [], [state]⟩
            | .evaluated none =>
                ⟨.failed w.tag state, [.undefined w.tag], [state]⟩
            | .evaluated (some value) =>
                let next := { state with
                  produced := state.produced ++ [(w.capability, value)] }
                let tail := stepFuel steps fuel next
                ⟨tail.outcome, .produced w.tag w.capability value :: tail.events,
                  state :: tail.states⟩
          | .collect a caps =>
            match caps.mapM (producedValue state) with
            | none => ⟨.collectorMismatch a state, [], [state]⟩
            | some values =>
                let value := values.foldl (· + ·) (0 : ℚ)
                letI := addressEq (σ := σ)
                let next := { state with
                  available := Function.update state.available a (some value) }
                let tail := stepFuel steps fuel next
                ⟨tail.outcome, .sealed a value :: tail.events, state :: tail.states⟩

def execute (graph : Closed σ)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ))
    (fuel : Option Nat := none) : Run σ :=
  match graph.contract.tensors.find?
      (fun t => (η t).isSome != graph.contract.input t) with
  | some t => ⟨.invalidInput t, [], []⟩
  | none =>
      stepFuel graph.steps (fuel.getD (graph.steps.length + 1)) (initial η)

/- Closed is public data: revalidate its writer claims and ignore supplied
   collector steps before executing the regenerated graph. -/
def run (graph : Closed σ)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ))
    (fuel : Option Nat := none) : Run σ :=
  let writers := graph.steps.filterMap fun
    | .write w => some w
    | .collect _ _ => none
  match close graph.contract ⟨writers⟩ with
  | .error error => ⟨.invalidGraph error, [], []⟩
  | .ok checked => execute checked η fuel

def runChecked (contract : Contract σ) (fragment : Fragment σ)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ))
    (fuel : Option Nat := none) : Run σ :=
  match close contract fragment with
  | .error error => ⟨.invalidGraph error, [], []⟩
  | .ok graph => execute graph η fuel

end IndexedOpenComposition
