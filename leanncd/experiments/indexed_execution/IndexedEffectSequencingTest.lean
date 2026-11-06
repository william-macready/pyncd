import IndexedExecutionPrototype
import Semantics.ExecutableReferenceTest
import LeanNCD.Semantics.Plan.ScanHistory.Core

namespace IndexedEffectSequencingTest

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

abbrev Shape2 := Program.Plan.ScanHistory.stateShape 2

def twoArray (other : ℚ) (Γ : Type) :
    Expr RationalReference.Carrier ExecutableReferenceFixtures.declarations
      RationalReference.registry Γ (.array () Shape2) :=
  .tab Shape2 (canonicalLayout _)
    (.prim (r := RationalReference.registry) RationalReference.Primitive.reciprocal
      (fun _ => .binary .add (.lit other)
        (.binary .mul (.lit (2 - other))
          (.iverson (fun γ => γ.2.1.val == 0)))))

def strictBody (other : ℚ) (Γ : Type) (_ : Fin 1) :
    Expr RationalReference.Carrier ExecutableReferenceFixtures.declarations
      RationalReference.registry Γ (.scalar ()) :=
  .at (twoArray other Γ) (fun _ => Program.Plan.ScanHistory.stateCoord (d := 2) 0)

def selectedOnlyBody (Γ : Type) (_ : Fin 1) :
    Expr RationalReference.Carrier ExecutableReferenceFixtures.declarations
      RationalReference.registry Γ (.scalar ()) :=
  .prim (r := RationalReference.registry) RationalReference.Primitive.reciprocal
    (fun _ => .lit 2)

abbrev Body := (Γ : Type) → Fin 1 →
    Expr RationalReference.Carrier ExecutableReferenceFixtures.declarations
      RationalReference.registry Γ (.scalar ())

def runCase (body : Body) :=
  let P := ExecutableReferenceFixtures.program 1 body
  IndexedExecution.run P (ExecutableReferenceFixtures.schedule 1 body) (fun _ => none)

def compareCase (body : Body) :=
  let P := ExecutableReferenceFixtures.program 1 body
  let schedule := ExecutableReferenceFixtures.schedule 1 body
  IndexedExecution.compare P schedule (fun _ => none) (runCase body)
    (runValidated P RationalReference.ops schedule (fun _ => none))

def comparisonRow (body : Body) : Bool × Bool × Bool × Bool :=
  let c := compareCase body
  (c.terminal, c.snapshots, c.events, c.blockedReads)

abbrev Row := String × Nat × Nat × List (Option ℚ) × Option Nat

def graphRow (body : Body) : Row :=
  let run := runCase body
  let state := match run.outcome with
    | .complete c | .failed _ c | .blocked c _ | .exhausted c
    | .contractMismatch _ c | .collectorMismatch _ c => some c
    | _ => none
  (run.outcome.kind, run.events.length, run.states.length,
    (match state with
    | some c =>
        [ExecutableReferenceFixtures.point 0, ExecutableReferenceFixtures.point 1,
          ExecutableReferenceFixtures.point 2].map fun p => c.available ⟨(), p⟩
    | none => []),
    match run.outcome with
    | .failed o _ => some o.2.1.val
    | _ => none)

def check {α : Type} [BEq α] [Repr α] (name : String) (actual expected : α) :
    IO Unit := do
  IO.println s!"indexed-effect {name}: {repr actual}"
  unless actual == expected do
    throw (IO.userError s!"indexed-effect {name}: expected {repr expected}, got {repr actual}")

def strict := strictBody 0
def total := strictBody 4
def shortcut := selectedOnlyBody

def graphRetainsFailure : Bool :=
  let P := ExecutableReferenceFixtures.program 1 strict
  letI := IndexedExecution.occurrenceEq P
  match (runCase strict).outcome with
  | .failed o state => decide (state.failure = some o) && o.2.1.val == 0
  | _ => false

def referenceLocatesFailure : Bool :=
  let P := ExecutableReferenceFixtures.program 1 strict
  match runValidated P RationalReference.ops
      (ExecutableReferenceFixtures.schedule 1 strict) (fun _ => none) with
  | .ok result =>
      match result.result.outcome with
      | .failed _ o _ => o.1.val == 0 && o.2.val.val == 0
      | _ => false
  | .error _ => false

#eval check "strict-graph-outcome" (graphRow strict)
  ("failed", 1, 2, [none, none, none], some 0)
#eval check "strict-graph-retained-failure" graphRetainsFailure true
#eval check "strict-reference-outcome" (ExecutableReferenceFixtures.summarize 1 strict)
  ("failed", 1, [none, none, none], 1)
#eval check "strict-reference-located-failure" referenceLocatesFailure true
#eval check "strict-graph-reference-parity" (comparisonRow strict)
  (true, true, true, true)

#eval check "total-graph-outcome" (graphRow total)
  ("complete", 4, 5, [some (1 / 2 : ℚ), some 0, some 0], none)
#eval check "total-reference-outcome" (ExecutableReferenceFixtures.summarize 1 total)
  ("complete", 4, [some (1 / 2 : ℚ), some 0, some 0], 0)
#eval check "total-graph-reference-parity" (comparisonRow total)
  (true, true, true, true)

-- Selecting before evaluating the tabulation is a forbidden transformation.
#eval check "forbidden-select-before-evaluate" (graphRow shortcut)
  ("complete", 4, 5, [some (1 / 2 : ℚ), some 0, some 0], none)
#eval check "forbidden-shortcut-reference-outcome"
  (ExecutableReferenceFixtures.summarize 1 shortcut)
  ("complete", 4, [some (1 / 2 : ℚ), some 0, some 0], 0)
#eval check "forbidden-shortcut-reference-parity" (comparisonRow shortcut)
  (true, true, true, true)
#eval check "shortcut-is-not-strict" (graphRow shortcut != graphRow strict) true

end IndexedEffectSequencingTest
