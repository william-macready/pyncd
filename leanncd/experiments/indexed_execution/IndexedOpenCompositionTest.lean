import IndexedOpenComposition
import IndexedEffectSequencingTest

namespace IndexedOpenCompositionTest

open LeanNCD.Semantics
open IndexedOpenComposition

def verify (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw (IO.userError s!"indexed-open {name}: failed")
  IO.println s!"indexed-open {name}: pass"

def rejects {α : Type 1} (expected : Error) (result : Except Error α) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

abbrev D := LeanNCD.Semantics.ExecutableReferenceFixtures.declarations
def p0 : Address D := ⟨(), LeanNCD.Semantics.ExecutableReferenceFixtures.point 0⟩
def p1 : Address D := ⟨(), LeanNCD.Semantics.ExecutableReferenceFixtures.point 1⟩
def p2 : Address D := ⟨(), LeanNCD.Semantics.ExecutableReferenceFixtures.point 2⟩

def writer (tag cap : Nat) (dst : Address D) (reads : List (Address D))
    (body : Body D) : Writer D := ⟨tag, cap, dst, reads, body⟩

def contract : Contract D :=
  ⟨[()], fun _ => false, [(p1, [10, 20]), (p2, [30]), (p0, [])],
    [p1, p2], [p2]⟩

def firstWriter : Writer D := writer 1 10 p1 [] (.lit 1)
def secondWriter : Writer D := writer 2 20 p1 [] (.lit (-1))
def squareWriter : Writer D :=
  writer 3 30 p2 [p1]
    (.prim (r := RationalReference.registry) RationalReference.Primitive.square
      (fun _ => LeanNCD.Semantics.ExecutableReferenceFixtures.readAt Unit 1))
def first : Fragment D := ⟨[firstWriter]⟩
def second : Fragment D := ⟨[secondWriter]⟩
def square : Fragment D := ⟨[squareWriter]⟩

def joined : Except Error (Fragment D) := do
  let ab ← combine first second
  combine ab square

def reversed : Except Error (Fragment D) := do
  let cb ← combine square second
  combine cb first

def regrouped : Except Error (Fragment D) := do
  let bc ← combine second square
  combine first bc

def runJoined (fragment : Except Error (Fragment D)) :
    Except Error (Run D) :=
  (fragment.bind (close contract)).map (fun graph => run graph (fun _ => none))

def terminal (result : Except Error (Run D)) :
    String × Option ℚ × Option ℚ × Option ℚ × Nat :=
  match result with
  | .error _ => ("invalidGraph", none, none, none, 0)
  | .ok execution =>
    match execution.outcome with
    | .complete state =>
        ("complete", state.available p0, state.available p1, state.available p2,
          state.produced.length)
    | _ => (execution.outcome.kind, none, none, none, execution.events.length)

#eval verify "open-three-writer-two-target-square-not-premature"
  (terminal (runJoined joined) == ("complete", some 0, some 0, some 0, 3))
#eval verify "intermediate-not-early-readable" <|
  match joined.bind (close contract) with
  | .error _ => false
  | .ok graph =>
    let execution := run graph (fun _ => none)
    match execution.states[1]?, execution.states[2]?, execution.states[3]? with
    | some afterFirst, some afterSecond, some afterCollect =>
        afterFirst.produced == [(10, 1)] &&
        (afterFirst.available p1).isNone &&
        !(enabled afterFirst (.collect p1 [10, 20])) &&
        !(enabled afterFirst (.write squareWriter)) &&
        (afterSecond.available p1).isNone &&
        afterSecond.produced == ([(10, 1), (20, -1)] : List (Nat × ℚ)) &&
        afterCollect.available p1 == some 0
    | _, _, _ => false
#eval verify "reversed-joins-preserve-result"
  (terminal (runJoined reversed) == terminal (runJoined joined))
#eval verify "parenthesized-joins-preserve-result"
  (terminal (runJoined regrouped) == terminal (runJoined joined))

def renamed : Fragment D :=
  ⟨[{firstWriter with tag := 101},
    {secondWriter with tag := 102},
    {squareWriter with tag := 103}]⟩

#eval verify "tag-renaming-preserves-values"
  (terminal (runJoined (.ok renamed)) == terminal (runJoined joined))

def equalWriters : Fragment D :=
  ⟨[writer 1 10 p1 [] (.lit 2), writer 2 20 p1 [] (.lit 2)]⟩
def equalContract : Contract D :=
  ⟨[()], fun _ => false, [(p1, [10, 20]), (p2, []), (p0, [])], [p1], [p1]⟩

#eval verify "equal-values-retain-two-identities" <|
  match close equalContract equalWriters with
  | .error _ => false
  | .ok graph =>
    match (run graph (fun _ => none)).outcome with
    | .complete state =>
        state.available p1 == some 4 &&
          state.produced == [(10, 2), (20, 2)]
    | _ => false

#eval verify "reject-early-closure"
  (rejects .missingCapability ((combine first square).bind (close contract)))
#eval verify "reject-extra-capability"
  (rejects .extraCapability
    (joined.bind fun f =>
      (combine f ⟨[writer 9 99 p1 [] (.lit 7)]⟩).bind (close contract)))
#eval verify "reject-added-after-seal"
  (rejects .alreadySealed
    ((sealAssembly contract (.open renamed)).bind fun phase =>
      extend phase first))
#eval verify "reject-duplicate-tag"
  (rejects .duplicateTag
    (combine first ⟨[{secondWriter with tag := 1}]⟩))
#eval verify "reject-overlapping-capability"
  (rejects .duplicateCapability
    (combine first ⟨[{secondWriter with capability := 10}]⟩))
#eval verify "reject-contract-capability-collision"
  (rejects .duplicateContractCapability
    (close { contract with collectors := [(p1, [10, 20]), (p2, [10]), (p0, [])] }
      renamed))
#eval verify "reject-wrong-declared-target"
  (rejects .wrongDestination
    (close contract ⟨[firstWriter,
      {secondWriter with destination := p2}, squareWriter]⟩))
#eval verify "reject-dropped-read-footprint"
  (rejects .badFootprint
    (close contract ⟨[firstWriter, secondWriter,
      {squareWriter with reads := []}]⟩))
#eval verify "reject-unreadable-consumer"
  (rejects .unreadableRead
    (close contract ⟨[firstWriter, secondWriter,
      writer 3 30 p2 [p0] (LeanNCD.Semantics.ExecutableReferenceFixtures.readAt Unit 0)]⟩))
#eval verify "reject-omitted-nonoutput-collector"
  (rejects .missingCollector
    (close { contract with collectors := [(p1, [10, 20]), (p2, [30])] }
      renamed))
#eval verify "reject-incomplete-tensor-enumeration"
  (rejects .missingTensor (close { contract with tensors := [] } renamed))
#eval verify "invalid-graph-input-and-debug-fuel-distinct" <|
  let badGraph := runChecked contract first (fun _ => some (fun _ => 0))
  let badInput := runChecked contract renamed (fun _ => some (fun _ => 0))
  let noFuel := runChecked contract renamed (fun _ => none) (some 0)
  badGraph.outcome.kind == "invalidGraph" && badGraph.states.isEmpty &&
    badInput.outcome.kind == "invalidInput" && badInput.events.isEmpty &&
    noFuel.outcome.kind == "exhausted"
#eval verify "forged-closed-empty-steps-cannot-complete" <|
  match (run (⟨contract, []⟩ : Closed D) (fun _ => none)).outcome with
  | .invalidGraph .missingCapability => true
  | _ => false
#eval verify "forged-collector-ports-cannot-publish-subtotal" <|
  let forged : Closed D :=
    ⟨contract, [.write firstWriter, .write secondWriter, .collect p1 [10],
      .write squareWriter, .collect p2 [30], .collect p0 []]⟩
  match (run forged (fun _ => none)).outcome with
  | .complete state => state.available p1 == some 0 && state.available p2 == some 0
  | _ => false

def emptyContract : Contract D :=
  ⟨[()], fun _ => false, [(p0, []), (p1, []), (p2, [])], [], [p0]⟩

#eval verify "empty-writer-family-available-zero" <|
  match close emptyContract ⟨[]⟩ with
  | .error _ => false
  | .ok graph =>
    match (run graph (fun _ => none)).outcome with
    | .complete state =>
        state.available p0 == some 0 && state.available p1 == some 0 &&
          state.produced.isEmpty
    | _ => false

abbrev EmptyD := LeanNCD.Semantics.ExecutableReferenceFixtures.emptyDeclarations
def zeroInputContract : Contract EmptyD := ⟨[()], fun _ => true, [], [], []⟩

#eval verify "zero-size-input-presence" <|
  match close zeroInputContract ⟨[]⟩ with
  | .error _ => false
  | .ok graph =>
    (run graph LeanNCD.Semantics.ExecutableReferenceFixtures.presentEmpty).outcome.kind ==
      "complete" &&
    (run graph (fun _ => none)).outcome.kind == "invalidInput"

def cycle : Fragment D :=
  ⟨[writer 1 10 p1 [p1] (LeanNCD.Semantics.ExecutableReferenceFixtures.readAt Unit 1)]⟩
def cycleContract : Contract D :=
  ⟨[()], fun _ => false, [(p1, [10]), (p2, []), (p0, [])], [p1], [p1]⟩

#eval verify "cyclic-value-read-blocks-with-full-footprint" <|
  match close cycleContract cycle with
  | .error _ => false
  | .ok graph =>
    match (run graph (fun _ => none)).outcome with
    | .blocked _ missing => missing == [(1, [p1])]
    | _ => false

def strictWriter (other : ℚ) : Writer D :=
  writer 4 40 p0 [p1]
    (.binary .add (LeanNCD.Semantics.ExecutableReferenceFixtures.readAt Unit 1)
      (IndexedEffectSequencingTest.strictBody other Unit 0))
def shortcutWriter : Writer D :=
  writer 4 40 p0 [p1]
    (.binary .add (LeanNCD.Semantics.ExecutableReferenceFixtures.readAt Unit 1)
      (IndexedEffectSequencingTest.selectedOnlyBody Unit 0))
def strictContract : Contract D :=
  ⟨[()], fun _ => false, [(p1, [10, 20]), (p2, [30]), (p0, [40])],
    [p1, p2], [p2]⟩
def composedStrict (body : Writer D) : Except Error (Run D) :=
  (joined.bind fun f =>
    (combine f ⟨[body]⟩).bind (close strictContract)).map
      (fun graph => run graph (fun _ => none))

#eval verify "strict-nonselected-undefined-survives-composition" <|
  match composedStrict (strictWriter 0) with
  | .ok execution =>
    match execution.outcome with
    | .failed 4 state =>
        state.available p2 == some 0 && (state.available p0).isNone &&
          state.produced == [(10, 1), (20, -1), (30, 0)] &&
          execution.events.length == 6
    | _ => false
  | .error _ => false
#eval verify "strict-body-total-neighbour" <|
  match composedStrict (strictWriter 4) with
  | .ok execution =>
    match execution.outcome with
    | .complete state => state.available p2 == some 0 &&
        state.available p0 == some (1 / 2 : ℚ)
    | _ => false
  | .error _ => false
#eval verify "select-before-assembly-is-forbidden-shortcut" <|
  match composedStrict shortcutWriter with
  | .ok execution =>
    match execution.outcome with
    | .complete state => state.available p0 == some (1 / 2 : ℚ)
    | _ => false
  | .error _ => false
#eval verify "strict-body-waits-for-completed-read" <|
  match composedStrict (strictWriter 0) with
  | .ok execution =>
    match execution.states[1]?, execution.outcome with
    | some state, .failed 4 _ =>
        !(enabled state (.write (strictWriter 0))) && (state.available p1).isNone
    | _, _ => false
  | .error _ => false

def donorParity (n : Nat)
    (body : (Γ : Type) → Fin n →
      Expr RationalReference.Carrier D RationalReference.registry Γ (.scalar ())) : Bool :=
  let P := LeanNCD.Semantics.ExecutableReferenceFixtures.program n body
  let schedule := LeanNCD.Semantics.ExecutableReferenceFixtures.schedule n body
  (IndexedExecution.compare P schedule (fun _ => none)
    (IndexedExecution.run P schedule (fun _ => none))
    (LeanNCD.Semantics.Program.Executor.runValidated P RationalReference.ops
      schedule (fun _ => none))).agrees

#eval verify "existing-duplicate-reference-control"
  (donorParity 2 LeanNCD.Semantics.ExecutableReferenceFixtures.duplicateBody)
#eval verify "existing-strict-reference-control"
  (donorParity 1 (IndexedEffectSequencingTest.strictBody 0))

end IndexedOpenCompositionTest
