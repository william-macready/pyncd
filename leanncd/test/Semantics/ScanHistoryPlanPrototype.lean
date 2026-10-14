import LeanNCD.Semantics.Plan.ScanHistory.Plan
import LeanNCD.Semantics.Plan.Validity
import Semantics.ScanHistoryRecurrencePrototype
import Semantics.AxiomAudit

namespace LeanNCD.Semantics.ScanHistoryPlanPrototype

open Program Program.Plan Program.Plan.ScanHistory ExecutableReferenceFixtures
open ScanHistoryRecurrencePrototype

/-- Two registered operators: the selected scan operator and an unrelated identity. -/
def registry (d : Nat) (F : State ℚ d → State ℚ d) :
    Registry (Program.Plan.ScanHistory.Carrier ℚ) where
  Op := Bool
  arity := fun _ => 1
  input := fun _ _ => stateTy d
  output := fun _ => stateTy d
  domain := fun _ _ => true
  meaning := fun op xs _ =>
    if op then xs 0 else fun p => F (fun i => xs 0 (stateCoord i)) p.1

def registered (d : Nat) (F : State ℚ d → State ℚ d) : RegisteredF (registry d F) d where
  op := false
  unary := rfl
  input_eq := fun _ => rfl
  output_eq := rfl
  total := fun _ => rfl

def execute {d : Nat} (F : State ℚ d → State ℚ d) (N : Nat) (X Z : State ℚ d) :=
  let π := plan (registered d F) N
  π.runPlan RationalReference.ops (π.Start (input (registered d F) N X Z))

def kind {d : Nat} (F : State ℚ d → State ℚ d) (N : Nat) (X Z : State ℚ d) :
    String × Nat :=
  match execute F N X Z with
  | .done pc _ => ("done", pc)
  | .failed _ pc _ => ("failed", pc)
  | .stuck pc _ => ("stuck", pc)

def decoded {d : Nat} (F : State ℚ d → State ℚ d) (N : Nat) (X Z : State ℚ d) :
    Option (List (List ℚ)) :=
  let π := plan (registered d F) N
  match execute F N X Z with
  | .done pc M => (π.Decode pc M).map fun out =>
      (List.finRange (N + 1)).map fun l =>
        (List.finRange d).map fun i => out ⟨.H, rfl⟩ (historyCoord i l)
  | _ => none

#eval check "scan-prototype-scalar-executor"
  ((plan (registered 1 doubleState) 2).checkPlan, kind doubleState 2 scalarX scalarZ,
    decoded doubleState 2 scalarX scalarZ)
  (true, ("done", 9), some [[5], [12], [26]])

#eval check "scan-prototype-vector-executor-vs-oracle"
  ((plan (registered 2 crossNonlinear) 2).checkPlan,
    kind crossNonlinear 2 vectorX vectorZ,
    decoded crossNonlinear 2 vectorX vectorZ,
    some (trace crossNonlinear vectorX vectorZ 2))
  (true, ("done", 9), some [[4, 7], [16, 30], [63, 482]],
    some [[4, 7], [16, 30], [63, 482]])

#eval check "scan-prototype-whole-prior-slice-footprint"
  ((footprint
      (recurrenceBody (N := 2) (registered 2 crossNonlinear)
        (fun _ : Unit => 0) (fun _ : Unit => 0)) ()).map fun a =>
    ((declarations 2 2).uid a.1,
      (List.finRange ((declarations 2 2).signature a.1).axes.length).map (Coord.raw a.2)))
  [(12, [0, 0]), (12, [1, 0])]

#eval check "scan-prototype-no-transitions"
  ((plan (registered 1 doubleState) 0).checkPlan,
    kind doubleState 0 scalarX scalarZ, decoded doubleState 0 scalarX scalarZ)
  (true, ("done", 3), some [[5]])

#eval check "scan-prototype-empty-history"
  ((plan (registered 0 id) 2).checkPlan,
    (allocation (registered 0 id) 2).buffers.length,
    (allocation (registered 0 id) 2).capacity 0,
    kind id 2 emptyState emptyState, decoded id 2 emptyState emptyState)
  (true, 3, 0, ("done", 9), some [[], [], []])

def scalarPlan := plan (registered 1 doubleState) 2
def scalarInput := input (registered 1 doubleState) 2 scalarX scalarZ
def scalarPrefix (pc : Nat) :=
  scalarPlan.runFrom RationalReference.ops 0 (scalarPlan.Start scalarInput)
    (scalarPlan.commands.take pc)
def scalarMemory (pc : Nat) :=
  match scalarPrefix pc with
  | .done _ M | .failed _ _ M | .stuck _ M => M

#eval check "scan-prototype-retained-prefix-memory"
  ((List.range 10).map fun pc =>
    (List.finRange 3).map fun l => scalarMemory pc (.inr ⟨l, (0 : Fin 1)⟩))
  [[none, none, none], [some 0, none, none], [some 5, none, none],
   [some 5, none, none], [some 5, some 0, none], [some 5, some 12, none],
   [some 5, some 12, none], [some 5, some 12, some 0],
   [some 5, some 12, some 26], [some 5, some 12, some 26]]

#eval check "scan-prototype-inputs-and-published-history"
  (scalarPlan.readPub 9 (scalarMemory 9) ⟨.X, stateCoord 0⟩,
    scalarPlan.readPub 9 (scalarMemory 9) ⟨.Z, stateCoord 0⟩,
    (List.finRange 3).map fun l =>
      scalarPlan.readPub 9 (scalarMemory 9) (historyAddress 1 2 0 l))
  (some 2, some 3, [some 5, some 12, some 26])

def earlyPublish :=
  { scalarPlan with commands :=
      (List.finRange 3).flatMap fun l =>
        [[.initZero (block (registered 1 doubleState) 2 l)],
         [.pub (block (registered 1 doubleState) 2 l)],
         [.acc (group (registered 1 doubleState) 2 l)]] }

#eval check "scan-prototype-early-publication-rejected"
  (earlyPublish.checkSteps, earlyPublish.checkLayouts,
    earlyPublish.checkPlan, scalarPlan.checkPlan)
  (false, true, false, true)

def collapsedAllocation : Allocation (program (registered 1 doubleState) 2) :=
  { allocation (registered 1 doubleState) 2 with
    locate := fun x =>
      ⟨⟨0, ((allocation (registered 1 doubleState) 2).locate x).val.2⟩, rfl⟩ }
def collapsedPlan := { scalarPlan with allocation := collapsedAllocation }

#eval check "scan-prototype-history-alias-rejected"
  (collapsedPlan.checkSteps, collapsedPlan.checkLayouts,
    collapsedPlan.checkPlan, scalarPlan.checkPlan)
  (true, false, false, true)

#eval check "scan-prototype-unchecked-alias-corrupts-history"
  (match collapsedPlan.runPlan RationalReference.ops (collapsedPlan.Start scalarInput) with
   | .done pc M => (pc, (collapsedPlan.Decode pc M).map fun out =>
       (List.finRange 3).map fun l => out ⟨.H, rfl⟩ (historyCoord (0 : Fin 1) l))
   | .failed _ pc _ | .stuck pc _ => (pc, none))
  (9, some [2, 2, 2])

example : scalarPlan.LayoutOK 5 := plan_layout _ _ _
example : scalarPlan.Live 6 (historyAddress 1 2 0 0) :=
  history_live_at_slice_boundary _ _ 2 _ _ (by decide)

end LeanNCD.Semantics.ScanHistoryPlanPrototype

#audit_axioms LeanNCD.Semantics.Program.Plan.ScanHistory
#audit_axioms LeanNCD.Semantics.ScanHistoryPlanPrototype
