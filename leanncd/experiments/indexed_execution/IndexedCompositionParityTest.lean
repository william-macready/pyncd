import IndexedOpenComposition
import Semantics.ExecutableReferenceTest
import LeanNCD.Semantics.Plan.ScanHistory.Core

namespace IndexedCompositionParityTest

open LeanNCD.Semantics
open LeanNCD.Semantics.Program.Executor
open IndexedOpenComposition

abbrev D := ExecutableReferenceFixtures.scalarDeclarations
def pre : Address D := ⟨0, ()⟩
def out : Address D := ⟨1, ()⟩
def audit : Address D := ⟨2, ()⟩

def scalarPolicy : ReadPolicy ℚ [] :=
  ⟨fun _ => .at (), by intro p; cases p; rfl⟩
def readScalar (Γ : Type) (t : Fin 3) :
    Expr RationalReference.Carrier D RationalReference.registry Γ (.scalar ()) :=
  .read t ⟨scalarPolicy, fun _ => Fin.elim0, fun _ => .at (), by intro _; rfl⟩

def squareBody (Γ : Type) :
    Expr RationalReference.Carrier D RationalReference.registry Γ (.scalar ()) :=
  .prim (r := RationalReference.registry) RationalReference.Primitive.square
    (fun _ => readScalar Γ 0)

-- Shared strict expression construction; the independently authored program
-- and fragment exercise composition/execution, not different interpreters.
def strictArray (other : ℚ) (Γ : Type) :
    Expr RationalReference.Carrier D RationalReference.registry Γ
      (.array () (LeanNCD.Semantics.Program.Plan.ScanHistory.stateShape 2)) :=
  .tab (LeanNCD.Semantics.Program.Plan.ScanHistory.stateShape 2) (canonicalLayout _)
    (.prim (r := RationalReference.registry) RationalReference.Primitive.reciprocal
      (fun _ => .binary .add (.lit other)
        (.binary .mul (.lit (2 - other))
          (.iverson (fun γ => γ.2.1.val == 0)))))

def auditBody (other : ℚ) (Γ : Type) :
    Expr RationalReference.Carrier D RationalReference.registry Γ (.scalar ()) :=
  .binary .add (readScalar Γ 0)
    (.at (strictArray other Γ)
      (fun _ => LeanNCD.Semantics.Program.Plan.ScanHistory.stateCoord (d := 2) 0))

@[reducible] def reference (other : ℚ) :
    Program RationalReference.Carrier D RationalReference.registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun t => t == 1
  output_defined := by intro _ _; rfl
  statements := fun t => if t.val == 0 then 2 else 1
  valuations := fun _ _ => 1
  guard := fun _ _ _ => true
  destination := fun _ _ _ => ()
  body := fun t s =>
    if t.val == 0 then
      if s.val == 0 then .lit 1 else .lit (-1)
    else if t.val == 1 then squareBody _ else auditBody other _

def refSchedule (other : ℚ) : Schedule (reference other) where
  tensors := [0, 1, 2]
  tensors_nodup := by decide
  tensors_complete := by intro t; fin_cases t <;> simp
  keys := [
    .occurrence ⟨0, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
    .occurrence ⟨0, rfl⟩ ⟨1, ⟨0, rfl⟩⟩,
    .publication ⟨0, rfl⟩ (),
    .occurrence ⟨1, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
    .publication ⟨1, rfl⟩ (),
    .occurrence ⟨2, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
    .publication ⟨2, rfl⟩ ()]
  keys_nodup := by
    simp [List.nodup_cons, Key.occurrence.injEq, Key.publication.injEq, Fin.ext_iff]
    intro h
    have hs : (0 : Fin 2) = 1 := congrArg Sigma.fst h
    exact (by decide : (0 : Fin 2) ≠ 1) hs
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨t, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      have hv' : v = 0 := Subsingleton.elim _ _
      subst v
      fin_cases t <;> fin_cases s <;>
        simp_all [reference] <;>
        (first | exact Or.inl rfl | exact Or.inr rfl | rfl)
    | publication t p =>
      rcases t with ⟨t, ht⟩
      cases p
      fin_cases t <;> simp

-- This mapping is authored from source statement/valuation identities, not
-- computed from the graph or schedule.
def sourceToWriter : List (Nat × Nat × Nat × Nat) :=
  [(0, 0, 10, 101), (0, 1, 11, 102), (1, 0, 20, 201), (2, 0, 30, 301)]

def writerId (t s : Nat) : Except String (Nat × Nat) :=
  match sourceToWriter.find? (fun row => row.1 == t && row.2.1 == s) with
  | some row => .ok (row.2.2.1, row.2.2.2)
  | none => .error s!"unmapped source occurrence tensor={t} statement={s}"

def contract : Contract D :=
  ⟨[0, 1, 2], fun _ => false,
    [(pre, [101, 102]), (out, [201]), (audit, [301])],
    [pre], [out]⟩

def fragment (other : ℚ) : Fragment D :=
  ⟨[⟨10, 101, pre, [], .lit 1⟩,
    ⟨11, 102, pre, [], .lit (-1)⟩,
    ⟨20, 201, out, [pre], squareBody Unit⟩,
    ⟨30, 301, audit, [pre], auditBody other Unit⟩]⟩

def graphRun (other : ℚ) : Run D :=
  runChecked contract (fragment other) (fun _ => none)

def refRun (other : ℚ) :=
  runValidated (reference other) RationalReference.ops
    (refSchedule other) (fun _ => none)

abbrev EventRow := String × Option Nat × Option Nat × Nat × List Nat × Option ℚ

def graphWriter (other : ℚ) (tag : Nat) : Except String (Nat × Nat) :=
  match (fragment other).writers.find? (fun w => w.tag == tag) with
  | some w => .ok (w.capability, w.destination.1.val)
  | none => .error s!"unmapped graph writer tag={tag}"

def graphEvent (other : ℚ) :
    IndexedOpenComposition.Event D → Except String EventRow
  | .produced tag cap value => do
    let id ← graphWriter other tag
    if id.1 != cap then
      .error s!"graph writer tag={tag} has unexpected capability={cap}"
    else
      pure ("write", some tag, some cap, id.2, [], some value)
  | .sealed address value =>
    .ok ("publish", none, none, address.1.val, [], some value)
  | .undefined tag => do
    let id ← graphWriter other tag
    pure ("undefined", some tag, none, id.2, [], none)

def referenceEvent (other : ℚ) :
    LeanNCD.Semantics.Program.Executor.Event (reference other) → Except String EventRow
  | .contribution t o value => do
    let id ← writerId t.val.val o.1.val
    pure ("write", some id.1, some id.2, t.val.val, [], some value)
  | .publication t _ value => .ok ("publish", none, none, t.val.val, [], some value)
  | .undefined t o => do
    let id ← writerId t.val.val o.1.val
    pure ("undefined", some id.1, none, t.val.val, [], none)

abbrev StateRow := List (Option ℚ) × List ℚ × List Nat

def graphState (other : ℚ) (state : IndexedOpenComposition.State D) : StateRow :=
  let sums := contract.collectors.map fun row =>
    row.2.foldl (fun acc cap => acc + (producedValue state cap).getD 0) (0 : ℚ)
  let pending := ((fragment other).writers.filter
    (fun w => (producedValue state w.capability).isNone)).map (·.tag)
  ([state.available pre, state.available out, state.available audit], sums, pending)

def referenceState (other : ℚ) (c : (reference other).Running) : StateRow :=
  let pending :=
    ([(0, 0, 10), (0, 1, 11), (1, 0, 20), (2, 0, 30)] : List (Fin 3 × Nat × Nat)).filterMap
      fun (t, s, tag) =>
        if t.val == 0 then
          if s == 0 then
            if decide (⟨(0 : Fin 2), ⟨(0 : Fin 1), rfl⟩⟩ ∈ c.pending ⟨0, rfl⟩)
              then some tag else none
          else if decide (⟨(1 : Fin 2), ⟨(0 : Fin 1), rfl⟩⟩ ∈ c.pending ⟨0, rfl⟩)
            then some tag else none
        else if t.val == 1 then
          if decide (⟨(0 : Fin 1), ⟨(0 : Fin 1), rfl⟩⟩ ∈ c.pending ⟨1, rfl⟩)
            then some tag else none
        else if decide (⟨(0 : Fin 1), ⟨(0 : Fin 1), rfl⟩⟩ ∈ c.pending ⟨2, rfl⟩)
          then some tag else none
  ([c.published pre, c.published out, c.published audit],
    [c.accumulators ⟨0, rfl⟩ (), c.accumulators ⟨1, rfl⟩ (),
      c.accumulators ⟨2, rfl⟩ ()], pending)

def replay (other : ℚ) (start : (reference other).MachineState) :
    List (LeanNCD.Semantics.Program.Executor.Event (reference other)) →
      List (reference other).MachineState
  | [] => [start]
  | e :: tail =>
    start :: replay other (match start with
      | .running c => e.effect (reference other) c
      | .failed t o c => .failed t o c) tail

def refState (other : ℚ) : (reference other).MachineState → StateRow
  | .running c | .failed _ _ c => referenceState other c

def graphTerminal (other : ℚ) : String × Option Nat × StateRow :=
  let result := graphRun other
  match result.outcome with
  | .complete c => ("complete", none, graphState other c)
  | .failed tag c => ("failed", some tag, graphState other c)
  | .blocked c _ => ("blocked", none, graphState other c)
  | .exhausted c => ("exhausted", none, graphState other c)
  | _ => (result.outcome.kind, none, ([], [], []))

def refTerminal (other : ℚ) : Except String (String × Option Nat × StateRow) :=
  match refRun other with
  | .error _ => .error "reference input validation failed"
  | .ok result =>
    match result.result.outcome with
    | .complete c _ => .ok ("complete", none, referenceState other c)
    | .failed t o c => do
      let id ← writerId t.val.val o.1.val
      pure ("failed", some id.1, referenceState other c)
    | .blocked c _ _ => .ok ("blocked", none, referenceState other c)
    | .exhausted c => .ok ("exhausted", none, referenceState other c)

def parity (other : ℚ) : Bool × Bool × Bool :=
  let graph := graphRun other
  match refRun other with
  | .error _ => (false, false, false)
  | .ok result =>
    let terminalAgrees := match refTerminal other with
      | .ok row => graphTerminal other == row
      | .error _ => false
    let eventsAgree :=
      match graph.events.mapM (graphEvent other),
          result.result.events.mapM (referenceEvent other) with
      | .ok graphRows, .ok refRows => graphRows == refRows
      | _, _ => false
    let refStates := replay other
      (.running ((reference other).initial result.input)) result.result.events
    let refStates := match result.result.outcome with
      | .failed .. => refStates.take (refStates.length - 1)
      | _ => refStates
    (terminalAgrees, eventsAgree,
      graph.states.map (graphState other) ==
        refStates.map (refState other))

def check {α : Type} [BEq α] [Repr α] (name : String) (actual expected : α) :
    IO Unit := do
  IO.println s!"indexed-reference {name}: {repr actual}"
  unless actual == expected do
    throw (IO.userError s!"indexed-reference {name}: expected {repr expected}")

def checkExcept {α : Type} [BEq α] [Repr α] (name : String)
    (actual expected : Except String α) : IO Unit := do
  IO.println s!"indexed-reference {name}: {repr actual}"
  let agrees := match actual, expected with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false
  unless agrees do
    throw (IO.userError s!"indexed-reference {name}: expected {repr expected}, got {repr actual}")

#eval check "source-writer-identity-bijection"
  (sourceToWriter.map (fun x => (x.1, x.2.1)) == [(0, 0), (0, 1), (1, 0), (2, 0)] &&
    (sourceToWriter.map (fun x => x.2.2.1)).Nodup &&
    (sourceToWriter.map (fun x => x.2.2.2)).Nodup &&
    (fragment 0).writers.map (fun w => (w.tag, w.capability)) ==
      sourceToWriter.map (fun x => (x.2.2.1, x.2.2.2)))
  true
#eval check "independent-roles"
  ([((reference 0).input 0), ((reference 0).input 1), ((reference 0).input 2)],
    [((reference 0).output 0), ((reference 0).output 1), ((reference 0).output 2)],
    [contract.input 0, contract.input 1, contract.input 2],
    contract.outputs)
  ([false, false, false], [false, true, false], [false, false, false], [out])
#eval checkExcept "strict-failure-pairs"
  ((refTerminal 0).map fun row => (graphTerminal 0, row))
  (.ok (("failed", some 30, ([some 0, some 0, none], [0, 0, 0], [30])),
    ("failed", some 30, ([some 0, some 0, none], [0, 0, 0], [30]))))
#eval check "strict-failure-parity" (parity 0) (true, true, true)
#eval checkExcept "strict-ordered-events" ((graphRun 0).events.mapM (graphEvent 0))
  (.ok ([("write", some 10, some 101, 0, [], some 1),
    ("write", some 11, some 102, 0, [], some (-1)),
    ("publish", none, none, 0, [], some 0),
    ("write", some 20, some 201, 1, [], some 0),
    ("publish", none, none, 1, [], some 0),
    ("undefined", some 30, none, 2, [], none)] : List EventRow))
#eval checkExcept "total-neighbour-pairs"
  ((refTerminal 4).map fun row => (graphTerminal 4, row))
  (.ok (("complete", none, ([some 0, some 0, some (1 / 2)], [0, 0, 1 / 2], [])),
    ("complete", none, ([some 0, some 0, some (1 / 2)], [0, 0, 1 / 2], []))))
#eval check "total-neighbour-parity" (parity 4) (true, true, true)
#eval checkExcept "total-ordered-events" ((graphRun 4).events.mapM (graphEvent 4))
  (.ok ([("write", some 10, some 101, 0, [], some 1),
    ("write", some 11, some 102, 0, [], some (-1)),
    ("publish", none, none, 0, [], some 0),
    ("write", some 20, some 201, 1, [], some 0),
    ("publish", none, none, 1, [], some 0),
    ("write", some 30, some 301, 2, [], some (1 / 2)),
    ("publish", none, none, 2, [], some (1 / 2))] : List EventRow))
#eval check "exact-event-counts"
  ((graphRun 0).events.length, (graphRun 4).events.length,
    (refRun 0).toOption.map (·.result.events.length),
    (refRun 4).toOption.map (·.result.events.length))
  (6, 7, some 6, some 7)
#eval check "total-reference-model-store"
  (match refRun 4 with
  | .error _ => none
  | .ok result =>
    match result.result.outcome with
    | .complete c h =>
      let store := (reference 4).finalStore c h
      some [store pre, store out, store audit]
    | _ => none)
  (some ([0, 0, (1 / 2 : ℚ)] : List ℚ))
#eval check "failed-reference-has-no-total-store"
  (match refRun 0 with
  | .ok result => match result.result.outcome with
    | .complete .. => false
    | .failed .. => true
    | _ => false
  | .error _ => false) true

def graphShortcut : Fragment D :=
  ⟨[⟨10, 101, pre, [], .lit 1⟩,
    ⟨11, 102, pre, [], .lit (-1)⟩,
    ⟨20, 201, out, [pre], squareBody Unit⟩,
    ⟨30, 301, audit, [pre],
      .binary .add (readScalar Unit 0)
        (.prim (r := RationalReference.registry) RationalReference.Primitive.reciprocal
          (fun _ => .lit 2))⟩]⟩

#eval check "graph-only-strict-bypass-disagrees-with-reference"
  (let mutant := runChecked contract graphShortcut (fun _ => none)
   match mutant.outcome, refRun 0 with
   | .complete c, .ok ref =>
     c.available audit == some (1 / 2 : ℚ) &&
       (match refTerminal 0 with
        | .ok (kind, _, _) => kind == "failed"
        | .error _ => false) &&
       (match mutant.events.mapM (graphEvent 0),
           ref.result.events.mapM (referenceEvent 0) with
        | .ok graphRows, .ok refRows => graphRows != refRows
        | _, _ => false)
   | _, _ => false) true
#eval checkExcept "reject-unmapped-source-occurrence" (writerId 2 1)
  (.error "unmapped source occurrence tensor=2 statement=1")
#eval checkExcept "reject-unmapped-graph-tag"
  (graphEvent 0 (.undefined 999))
  (.error "unmapped graph writer tag=999")
#eval checkExcept "reject-wrong-graph-capability"
  (graphEvent 0 (.produced 10 999 1))
  (.error "graph writer tag=10 has unexpected capability=999")
#eval check "rejected-omitted-writer" (runChecked contract
  ⟨((fragment 0).writers.take 3)⟩ (fun _ => none)).outcome.kind "invalidGraph"

end IndexedCompositionParityTest
