import IndexedExecutionPrototype
import Semantics.ExecutableReferenceTest
import Semantics.ExpressionTest

namespace IndexedExecutionTest

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

def verify (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw (IO.userError s!"indexed-execution {name}: failed")
  IO.println s!"indexed-execution {name}: pass"

def rejected {α : Type} (expected : IndexedExecution.GraphError)
    (result : Except IndexedExecution.GraphError α) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

def compareFixture {σ : Declarations Unit} [DecidableEq σ.Tensor]
    (P : Program RationalReference.Carrier σ RationalReference.registry)
    (schedule : Schedule P)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ))
    (f : IndexedExecution.Fragment P := IndexedExecution.fragment P schedule) :
    IndexedExecution.Comparison :=
  IndexedExecution.compare P schedule η (IndexedExecution.run P schedule η f)
    (runValidated P RationalReference.ops schedule η)

def duplicateP :=
  ExecutableReferenceFixtures.program 2 ExecutableReferenceFixtures.duplicateBody
def duplicateSchedule :=
  ExecutableReferenceFixtures.schedule 2 ExecutableReferenceFixtures.duplicateBody
def duplicateRun := IndexedExecution.run duplicateP duplicateSchedule (fun _ => none)

#eval verify "duplicate-parity"
  (compareFixture duplicateP duplicateSchedule (fun _ => none)).agrees
#eval verify "duplicate-exact-store" <|
  match duplicateRun.outcome with
  | .complete state =>
      duplicateRun.events.length == 5 &&
      [ExecutableReferenceFixtures.point 0, ExecutableReferenceFixtures.point 1,
        ExecutableReferenceFixtures.point 2].map (fun p => state.available ⟨(), p⟩) ==
          [some 4, some 0, some 0]
  | _ => false

def taggedP := ExecutableReferenceFixtures.tagged
def taggedSchedule := ExecutableReferenceFixtures.taggedSchedule
def taggedRun := IndexedExecution.run taggedP taggedSchedule (fun _ => none)
def taggedReverse := IndexedExecution.run taggedP taggedSchedule.reverse (fun _ => none)

#eval verify "tagged-parity" (compareFixture taggedP taggedSchedule (fun _ => none)).agrees
#eval verify "tagged-reverse-parity"
  (compareFixture taggedP taggedSchedule.reverse (fun _ => none)).agrees
#eval verify "tagged-final" <|
  match taggedRun.outcome, taggedReverse.outcome with
  | .complete left, .complete right =>
      left.available ⟨(), ExecutableReferenceFixtures.point 1⟩ == some 14 &&
        right.available ⟨(), ExecutableReferenceFixtures.point 1⟩ == some 14 &&
        taggedRun.events.length == 7
  | _, _ => false
#eval verify "reverse-complete-store-invariant" <|
  match taggedRun.outcome, taggedReverse.outcome with
  | .complete left, .complete right =>
      (IndexedExecution.addresses taggedP taggedSchedule).all
        (fun a => left.available a == right.available a)
  | _, _ => false
#eval verify "open-writer-bundle" <|
  match taggedRun.states[1]?, (IndexedExecution.fragment taggedP taggedSchedule).nodes.find? (fun
      | .collect _ writers => writers.length == 4
      | _ => false) with
  | some state, some (.collect a writers) =>
      state.produced.length == 1 && writers.length == 4 &&
        (state.available (IndexedExecution.addressOf taggedP a)).isNone &&
        !(IndexedExecution.enabled taggedP state (.collect a writers))
  | _, _ => false

def failureP :=
  ExecutableReferenceFixtures.program 1 ExecutableReferenceFixtures.failureBody
def failureSchedule :=
  ExecutableReferenceFixtures.schedule 1 ExecutableReferenceFixtures.failureBody
def failureRun := IndexedExecution.run failureP failureSchedule (fun _ => none)

#eval verify "strict-ready-undefined"
  ((compareFixture failureP failureSchedule (fun _ => none)).agrees &&
    failureRun.outcome.kind == "failed" && failureRun.events.length == 1)
#eval verify "retained-failure-snapshot"
  (compareFixture
    (ExecutableReferenceFixtures.program 2 ExecutableReferenceFixtures.failureAfterBody)
    ExecutableReferenceFixtures.failureAfterSchedule (fun _ => none)).agrees
#eval verify "failure-retains-open-bundle" <|
  match (IndexedExecution.run
      (ExecutableReferenceFixtures.program 2 ExecutableReferenceFixtures.failureAfterBody)
      ExecutableReferenceFixtures.failureAfterSchedule (fun _ => none)).outcome with
  | .failed _ state =>
      (state.available ⟨(), ExecutableReferenceFixtures.point 0⟩).isNone &&
        state.available ⟨(), ExecutableReferenceFixtures.point 2⟩ == some 0 &&
        state.produced.length == 1 && state.failure.isSome
  | _ => false

#eval verify "guard-excluded"
  ((compareFixture ExecutableReferenceFixtures.excluded
      ExecutableReferenceFixtures.excludedSchedule (fun _ => none)).agrees &&
    (IndexedExecution.occurrences ExecutableReferenceFixtures.excluded
      ExecutableReferenceFixtures.excludedSchedule).isEmpty)
#eval verify "empty-writer-fibers" <|
  (compareFixture (ExecutableReferenceFixtures.program 0 (fun _ s => nomatch s))
    (ExecutableReferenceFixtures.schedule 0 (fun _ s => nomatch s)) (fun _ => none)).agrees
#eval verify "produced-zero-is-not-missing" <|
  match (IndexedExecution.run
      (ExecutableReferenceFixtures.program 1 ExecutableReferenceFixtures.zeroBody)
      (ExecutableReferenceFixtures.schedule 1 ExecutableReferenceFixtures.zeroBody)
      (fun _ => none)).states[1]? with
  | some state =>
      state.produced.length == 1 &&
        state.produced.head?.map Prod.snd == some 0 &&
        (state.available ⟨(), ExecutableReferenceFixtures.point 0⟩).isNone
  | none => false

#eval verify "empty-input-present"
  (compareFixture (ExecutableReferenceFixtures.emptyRole true)
    (ExecutableReferenceFixtures.emptySchedule true)
    ExecutableReferenceFixtures.presentEmpty).agrees
#eval verify "empty-input-absent"
  (compareFixture (ExecutableReferenceFixtures.emptyRole true)
    (ExecutableReferenceFixtures.emptySchedule true) (fun _ => none)).agrees
#eval verify "empty-defined-complete"
  (compareFixture (ExecutableReferenceFixtures.emptyRole false)
    (ExecutableReferenceFixtures.emptySchedule false) (fun _ => none)).agrees
#eval verify "invalid-input-order" <|
  let binding := ExecutableReferenceFixtures.simultaneous
  (compareFixture (ExecutableReferenceFixtures.scalarRole false)
      (ExecutableReferenceFixtures.scalarSchedule false) binding).agrees &&
    (compareFixture (ExecutableReferenceFixtures.scalarRole false)
      (ExecutableReferenceFixtures.scalarSchedule false).reverse binding).agrees

def internalP := ExecutableReferenceFixtures.scalarRole true
def internalSchedule := ExecutableReferenceFixtures.scalarSchedule true
def internalRun :=
  IndexedExecution.run internalP internalSchedule ExecutableReferenceFixtures.scalarBinding
#eval verify "nonoutput-failure-parity"
  (compareFixture internalP internalSchedule
    ExecutableReferenceFixtures.scalarBinding).agrees
#eval verify "output-only-completion-is-false" <|
  match internalRun.states[2]? with
  | some state =>
      (state.available ⟨1, ()⟩).isSome &&
        !(IndexedExecution.complete internalP
          (IndexedExecution.fragment internalP internalSchedule).nodes state) &&
        (state.available ⟨2, ()⟩).isNone
  | none => false

def chainP :=
  ExecutableReferenceFixtures.routed ExecutableReferenceFixtures.chainBody
def cycleP :=
  ExecutableReferenceFixtures.routed ExecutableReferenceFixtures.cycleBody
def chainSchedule :=
  ExecutableReferenceFixtures.routedSchedule ExecutableReferenceFixtures.chainBody
def cycleSchedule :=
  ExecutableReferenceFixtures.routedSchedule ExecutableReferenceFixtures.cycleBody
def cycleRun := IndexedExecution.run cycleP cycleSchedule (fun _ => none)

#eval verify "coordinate-chain"
  (compareFixture chainP chainSchedule (fun _ => none)).agrees
#eval verify "coordinate-chain-reverse"
  (compareFixture chainP chainSchedule.reverse (fun _ => none)).agrees
#eval verify "chain-sealed-values" <|
  match (IndexedExecution.run chainP chainSchedule (fun _ => none)).outcome with
  | .complete state =>
      state.available ⟨(), ExecutableReferenceFixtures.point 1⟩ == some 3 &&
        state.available ⟨(), ExecutableReferenceFixtures.point 2⟩ == some 4
  | _ => false
#eval verify "unranked-cycle-blocked"
  ((compareFixture cycleP cycleSchedule (fun _ => none)).agrees &&
    cycleRun.outcome.kind == "blocked")
#eval verify "full-footprint-waiting" <|
  match cycleRun.outcome with
  | .blocked state missing =>
      (state.available ⟨(), ExecutableReferenceFixtures.point 0⟩).isSome &&
        (state.available ⟨(), ExecutableReferenceFixtures.point 1⟩).isNone &&
        missing.length == 2 &&
        missing.any (fun (_, reads) =>
          reads.any (fun a => a.2 == ExecutableReferenceFixtures.point 2))
  | _ => false

def reciprocalP :=
  ExecutableReferenceFixtures.program 2 ExecutableReferenceFixtures.reciprocalBody
def reciprocalSchedule :=
  ExecutableReferenceFixtures.schedule 2 ExecutableReferenceFixtures.reciprocalBody
#eval verify "reciprocal-before-collection" <|
  let graph := IndexedExecution.run reciprocalP reciprocalSchedule (fun _ => none)
  (compareFixture reciprocalP reciprocalSchedule (fun _ => none)).agrees &&
    match graph.outcome with
    | .complete state =>
        state.available ⟨(), ExecutableReferenceFixtures.point 0⟩ == some (3 / 4 : ℚ) &&
          state.available ⟨(), ExecutableReferenceFixtures.point 0⟩ != some (1 / 6 : ℚ)
    | _ => false
#eval verify "square-primitive"
  (compareFixture
    (ExecutableReferenceFixtures.program 1 ExecutableReferenceFixtures.squareBody)
    (ExecutableReferenceFixtures.schedule 1 ExecutableReferenceFixtures.squareBody)
    (fun _ => none)).agrees
#eval verify "debug-fuel-is-inconclusive" <|
  (IndexedExecution.run taggedP taggedSchedule (fun _ => none)
    (fuel := some 0)).outcome.kind == "exhausted" &&
    (IndexedExecution.run (ExecutableReferenceFixtures.emptyRole false)
      (ExecutableReferenceFixtures.emptySchedule false) (fun _ => none)
      (fuel := some 0)).outcome.kind == "complete"

def taggedFragment := IndexedExecution.fragment taggedP taggedSchedule
def missingNode : IndexedExecution.Fragment taggedP :=
  ⟨taggedFragment.nodes.drop 1⟩
def duplicateNode : IndexedExecution.Fragment taggedP :=
  ⟨taggedFragment.nodes.take (taggedFragment.nodes.length - 1) ++
    taggedFragment.nodes.take 1⟩
def missingWriter : IndexedExecution.Fragment taggedP :=
  ⟨taggedFragment.nodes.map fun
    | .collect a writers =>
        if writers.length == 4 then .collect a (writers.drop 1) else .collect a writers
    | n => n⟩
def brokenRead : IndexedExecution.Fragment cycleP :=
  ⟨(IndexedExecution.fragment cycleP cycleSchedule).nodes.map fun
    | .evaluate o _ dst => .evaluate o [] dst
    | n => n⟩

#eval verify "fragment-recomposition"
  ((IndexedExecution.close taggedP taggedSchedule
    (IndexedExecution.Fragment.append taggedP
      (⟨taggedFragment.nodes.take 3⟩ : IndexedExecution.Fragment taggedP)
      (⟨taggedFragment.nodes.drop 3⟩ : IndexedExecution.Fragment taggedP))).isOk)
#eval verify "reject-missing-node"
  (rejected .nodeCount (IndexedExecution.close taggedP taggedSchedule missingNode))
#eval verify "reject-duplicate-tag"
  (rejected .duplicateNode (IndexedExecution.close taggedP taggedSchedule duplicateNode))
#eval verify "reject-missing-writer"
  (rejected .ports (IndexedExecution.close taggedP taggedSchedule missingWriter))
#eval verify "reject-dropped-read"
  (rejected .ports (IndexedExecution.close cycleP cycleSchedule brokenRead))
#eval verify "defect-parity-rejected"
  (!(IndexedExecution.compare taggedP taggedSchedule (fun _ => none)
    (IndexedExecution.run taggedP taggedSchedule (fun _ => none) missingWriter)
    (runValidated taggedP RationalReference.ops taggedSchedule (fun _ => none))).agrees)

#eval verify "strict-array-expression-only"
  (LeanNCD.Semantics.Fixtures.readyObservation LeanNCD.Semantics.Fixtures.selected ==
      "notReady" &&
    LeanNCD.Semantics.Fixtures.scalarObservation
      LeanNCD.Semantics.Fixtures.nonselectedUndefined == none &&
    LeanNCD.Semantics.Fixtures.scalarObservation
      LeanNCD.Semantics.Fixtures.outsideEmpty == none &&
    LeanNCD.Semantics.Fixtures.readyObservation LeanNCD.Semantics.Fixtures.zeroStrict ==
      "undefined" &&
    LeanNCD.Semantics.Fixtures.scalarObservation
      LeanNCD.Semantics.Fixtures.emptyReduction == some 0)

def sample : Fin 4 → ℚ := ![2, 2, 5, 5]
def grouped (i : Fin 4) : Fin 2 := if i.val < 2 then 0 else 1
def merged (_ : Fin 2) : Fin 1 := 0

#eval verify "closed-pushforward-grouping" <|
  pushforward grouped sample 0 == 4 &&
    pushforward grouped sample 1 == 10 &&
    pushforward merged (pushforward grouped sample) 0 ==
      pushforward (merged ∘ grouped) sample 0
#eval verify "total-reindex-composition" <|
  let values : Fin 2 → ℚ := ![3, 7]
  let swap : Fin 2 → Fin 2 := fun i => if i == 0 then 1 else 0
  pullback swap (pullback swap values) 0 == values 0 &&
    pullback (swap ∘ swap) values 1 == values 1

end IndexedExecutionTest
