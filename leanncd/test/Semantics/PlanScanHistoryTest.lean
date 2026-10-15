import LeanNCD.Semantics.Plan.ScanHistory.Plan
import LeanNCD.Semantics.Plan.ScanHistory.Coverage
import LeanNCD.Semantics.Plan.ScanHistory.Prefix
import LeanNCD.Semantics.Plan.ScanHistory.Validity
import LeanNCD.Semantics.Plan.ScanHistory.Evaluation
import LeanNCD.Semantics.Plan.ScanHistory.Model
import LeanNCD.Semantics.Plan.ScanHistory.Correctness
import LeanNCD.Semantics.Plan.Validity
import Semantics.PlanScanHistoryOracleTest
import Semantics.AxiomAudit

namespace LeanNCD.Semantics.PlanScanHistoryTest

open Program Program.Plan Program.Plan.ScanHistory ExecutableReferenceFixtures
open PlanScanHistoryOracleTest

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

def commandTag {V : Type} {d : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) (N pc : Nat) : String :=
  match (plan f N).commands[pc]? with
  | some [.initZero _] => "init"
  | some [.acc _] => "acc"
  | some [.pub _] => "pub"
  | none => "end"
  | _ => "other"

def scalarPrefixBookkeeping (pc : Nat) :=
  ((scalarPlan.consList pc).length, (scalarPlan.matList pc).length,
    (scalarPlan.pubList pc).length,
    (List.finRange 3).map fun l =>
      (group (registered 1 doubleState) 2 l).all fun x =>
        decide (x ∈ scalarPlan.consList pc),
    (List.finRange 3).map fun l =>
      decide (historyDefAddr (registered 1 doubleState) 2 0 l ∈ scalarPlan.matList pc),
    (List.finRange 3).map fun l =>
      decide (historyDefAddr (registered 1 doubleState) 2 0 l ∈ scalarPlan.pubList pc))

#eval check "scan-prototype-command-phase-tags"
  ((List.range 10).map fun pc => commandTag (registered 1 doubleState) 2 pc)
  ["init", "acc", "pub", "init", "acc", "pub", "init", "acc", "pub", "end"]

#eval check "scan-prototype-all-phase-prefix-bookkeeping"
  ((List.range 10).map scalarPrefixBookkeeping)
  [(0, 0, 0, [false, false, false], [false, false, false], [false, false, false]),
   (0, 1, 0, [false, false, false], [true, false, false], [false, false, false]),
   (2, 1, 0, [true, false, false], [true, false, false], [false, false, false]),
   (2, 1, 1, [true, false, false], [true, false, false], [true, false, false]),
   (2, 2, 1, [true, false, false], [true, true, false], [true, false, false]),
   (4, 2, 1, [true, true, false], [true, true, false], [true, false, false]),
   (4, 2, 2, [true, true, false], [true, true, false], [true, true, false]),
   (4, 3, 2, [true, true, false], [true, true, true], [true, true, false]),
   (6, 3, 2, [true, true, true], [true, true, true], [true, true, false]),
   (6, 3, 3, [true, true, true], [true, true, true], [true, true, true])]

#eval check "scan-prototype-empty-zero-retains-three-commands"
  ((List.range 4).map fun pc => commandTag (registered 0 id) 0 pc,
  (plan (registered 0 id) 0).commands.length,
  (List.range 4).map fun pc =>
    (((plan (registered 0 id) 0).consList pc).isEmpty,
      ((plan (registered 0 id) 0).matList pc).isEmpty,
      ((plan (registered 0 id) 0).pubList pc).isEmpty))
  (["init", "acc", "pub", "end"], 3,
    [(true, true, true), (true, true, true), (true, true, true), (true, true, true)])

#eval check "scan-prototype-nearest-acc-and-pub-boundaries"
  ((scalarPlan.consList 1).length, (scalarPlan.consList 2).length,
    (scalarPlan.pubList 2).length, (scalarPlan.pubList 3).length)
  (0, 2, 0, 1)

theorem generic_command_lookup_pin {V : Type} {d : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).commands[3 * k.val]? = some [.initZero (block f N k)] ∧
    (plan f N).commands[3 * k.val + 1]? = some [.acc (group f N k)] ∧
    (plan f N).commands[3 * k.val + 2]? = some [.pub (block f N k)] ∧
    (plan f N).commands[3 * (N + 1)]? = none :=
  ⟨command_init f N k, command_acc f N k, command_pub f N k, command_end f N⟩

theorem generic_prefix_phase_lists_pin {V : Type} {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (N : Nat) (k : Fin (N + 1)) :
    ((plan f N).consList (3 * k.val), (plan f N).matList (3 * k.val),
      (plan f N).pubList (3 * k.val)) =
      (beforeG f N k.val, beforeB f N k.val, beforeB f N k.val) ∧
    ((plan f N).consList (3 * k.val + 1), (plan f N).matList (3 * k.val + 1),
      (plan f N).pubList (3 * k.val + 1)) =
      (beforeG f N k.val, beforeB f N k.val ++ block f N k, beforeB f N k.val) ∧
    ((plan f N).consList (3 * k.val + 2), (plan f N).matList (3 * k.val + 2),
      (plan f N).pubList (3 * k.val + 2)) =
      (beforeG f N k.val ++ group f N k, beforeB f N k.val ++ block f N k,
        beforeB f N k.val) ∧
    ((plan f N).consList (3 * (k.val + 1)), (plan f N).matList (3 * (k.val + 1)),
      (plan f N).pubList (3 * (k.val + 1))) =
      (beforeG f N (k.val + 1), beforeB f N (k.val + 1), beforeB f N (k.val + 1)) := by
  obtain ⟨h0, h1, h2, h3⟩ := prefix_phase_lists f N k
  exact ⟨by rw [h0.1, h0.2.1, h0.2.2],
    by rw [h1.1, h1.2.1, h1.2.2],
    by rw [h2.1, h2.2.1, h2.2.2],
    by rw [h3.1, h3.2.1, h3.2.2]⟩

theorem generic_boundary_pin (N pc : Nat) (hpc : pc ≤ 3 * (N + 1)) :
    pc = 3 * (N + 1) ∨
      ∃ k : Fin (N + 1), ∃ phase : Fin 3, pc = 3 * k.val + phase.val :=
  boundary_decomposition N pc hpc

theorem generic_retirement_pin {V : Type} {d : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) (N pc : Nat) : (plan f N).retList pc = [] :=
  prefix_retList f N pc

theorem generic_command_index_pin (N pc : Nat) (hpc : pc < 3 * (N + 1)) :
    ∃ k : Fin (N + 1), ∃ phase : Fin 3, pc = 3 * k.val + phase.val :=
  command_index_decomposition N pc hpc

theorem generic_endpoint_lists_pin {V : Type} {d : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) (N : Nat) :
    ((plan f N).consList 0 = [] ∧ (plan f N).matList 0 = [] ∧
      (plan f N).pubList 0 = []) ∧
    ((plan f N).consList (3 * (N + 1)) = (List.finRange (N + 1)).flatMap (group f N) ∧
      (plan f N).matList (3 * (N + 1)) = (List.finRange (N + 1)).flatMap (block f N) ∧
      (plan f N).pubList (3 * (N + 1)) = (List.finRange (N + 1)).flatMap (block f N)) := by
  constructor
  · simp [consList, matList, pubList, prefixAnn]
  · have full : (List.finRange (N + 1)).take (N + 1) = List.finRange (N + 1) :=
      List.take_of_length_le (by simp)
    simpa [beforeB, beforeG, full] using
      And.intro (consList_phase_zero f N (N + 1))
        (And.intro (matList_phase_zero f N (N + 1)) (pubList_phase_zero f N (N + 1)))

theorem empty_zero_commands_pin :
    (plan (registered 0 id) 0).commands = [[.initZero []], [.acc []], [.pub []]] := by
  rfl

theorem no_transition_commands_pin {V : Type} {d : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) :
    (plan f 0).commands[0]? = some [.initZero (block f 0 0)] ∧
    (plan f 0).commands[1]? = some [.acc (group f 0 0)] ∧
    (plan f 0).commands[2]? = some [.pub (block f 0 0)] ∧
    (plan f 0).commands[3]? = none :=
  generic_command_lookup_pin f 0 0

theorem empty_dimension_commands_pin {V : Type} {r : Registry (Carrier V)}
    (f : RegisteredF r 0) (N : Nat) (k : Fin (N + 1)) :
    (plan f N).commands[3 * k.val]? = some [.initZero []] ∧
    (plan f N).commands[3 * k.val + 1]? = some [.acc []] ∧
    (plan f N).commands[3 * k.val + 2]? = some [.pub []] ∧
    (plan f N).commands.length = 3 * (N + 1) := by
  simpa [block, zero_dim_group] using
    And.intro (command_init f N k)
      (And.intro (command_acc f N k) (And.intro (command_pub f N k) (plan_length f N)))


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

/-- Transport the selected operator's signatures inside its existing registry. -/
def selectedF {V : Type} {d : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) (d' : Nat) (signature : stateTy d = stateTy d') :
    RegisteredF r d' where
  op := f.op
  unary := f.unary
  input_eq := fun j => (f.input_eq j).trans signature
  output_eq := f.output_eq.trans signature
  total := f.total

theorem selectedF_arrayExpr_pin {V Γ : Type} {d d' : Nat}
    {r : Registry (Carrier V)} {σ : Declarations Unit}
    (f : RegisteredF r d) (signature : stateTy d = stateTy d')
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (p : PartialStore (Carrier V) σ)
    (arg : Expr (Carrier V) σ r Γ (stateTy d')) (γ : Γ) (x : State V d')
    (harg : evalWith ops p arg γ =
      some (fun c : Coord (stateShape d').axes => x c.1)) :
    evalWith ops p ((selectedF f d' signature).arrayExpr arg) γ =
      some (fun c : Coord (stateShape d').axes =>
        (selectedF f d' signature).transition x c.1) :=
  arrayExpr_eval _ ops p arg γ x harg

theorem selectedF_recurrence_pin {V Γ : Type} {d d' N : Nat}
    {r : Registry (Carrier V)}
    (f : RegisteredF r d) (signature : stateTy d = stateTy d')
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (p : PartialStore (Carrier V) (declarations d' N))
    (i : Γ → Fin d') (l : Γ → Fin (N + 1)) (γ : Γ) (slice : State V d')
    (hpresent : ∀ j, p (historyAddress d' N j (l γ)) = some (slice j)) :
    evalWith ops p (recurrenceBody (selectedF f d' signature) i l) γ =
      some ((selectedF f d' signature).transition slice (i γ)) :=
  recurrenceBody_eval _ ops p i l γ slice hpresent

def priorStore : PartialStore (Carrier ℚ) (declarations 2 2) :=
  fun a => match a with
  | ⟨.H, c⟩ => some (if c.1.val = 0 then 4 else 7)
  | ⟨.X, _⟩ => none
  | ⟨.Z, _⟩ => none

#eval check "scan-prototype-transported-array-and-recurrence"
  (let f := selectedF (registered 2 crossNonlinear) 2 rfl
   ((evalWith RationalReference.ops priorStore
       (f.arrayExpr (priorSlice (fun _ : Unit => (0 : Fin 3)))) ()).map
         (fun xs => [xs (stateCoord 0), xs (stateCoord 1)]),
     evalWith RationalReference.ops priorStore
       (recurrenceBody f (fun _ : Unit => 0) (fun _ : Unit => 0)) (),
     evalWith RationalReference.ops priorStore
       (recurrenceBody f (fun _ : Unit => 1) (fun _ : Unit => 0)) ()))
  (some [15, 28], some 15, some 28)

theorem validatedInput_pin {V : Type} {d N : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) (η : (program f N).Input) :
    η = input f N (inputX η) (inputZ η) :=
  input_reconstruct f N η

def directScalarInput : (program (registered 1 doubleState) 2).Input :=
  ⟨(fun t => match t with
    | .X => some (fun _ => 2)
    | .Z => some (fun _ => 3)
    | .H => none), by intro t; cases t <;> rfl⟩

theorem directScalarInput_pin :
    directScalarInput = input (registered 1 doubleState) 2 scalarX scalarZ :=
  input_reconstruct _ _ directScalarInput

#eval check "scan-prototype-direct-validated-input-extraction"
  (inputX directScalarInput 0, inputZ directScalarInput 0,
    (directScalarInput.val .H).isNone)
  (2, 3, true)

def directEmptyInput : (program (registered 0 id) 0).Input :=
  ⟨(fun t => match t with
    | .X => some (fun c => Fin.elim0 c.1)
    | .Z => some (fun c => Fin.elim0 c.1)
    | .H => none), by intro t; cases t <;> rfl⟩

theorem directEmptyInput_pin :
    directEmptyInput = input (registered 0 id) 0 emptyState emptyState :=
  input_reconstruct _ _ directEmptyInput

theorem guard_partition_pin :
    (List.finRange 3).map (fun l =>
      (statementGuard 2 2 persistentID (valuationIndex (1 : Fin 2) l),
       statementGuard 2 2 initialID (valuationIndex (1 : Fin 2) l),
       statementGuard 2 2 recurrenceID (valuationIndex (1 : Fin 2) l))) =
      [(true, true, true), (true, false, true), (true, false, false)] := by
  decide

theorem classification_pin :
    Function.Bijective (occurrenceRef (registered 2 crossNonlinear) 2) :=
  occurrenceRef_bijective _

theorem target_partition_pin :
    OccRef.target (occurrenceRef (registered 2 crossNonlinear) 2
      (.persistent 1 2)) = historyDefAddr (registered 2 crossNonlinear) 2 1 2 ∧
    OccRef.target (occurrenceRef (registered 2 crossNonlinear) 2
      (.initial 1)) = historyDefAddr (registered 2 crossNonlinear) 2 1 0 ∧
    OccRef.target (occurrenceRef (registered 2 crossNonlinear) 2
      (.recurrence 1 1)) = historyDefAddr (registered 2 crossNonlinear) 2 1 2 := by
  exact ⟨persistent_target _ _ _, initial_target _ _, recurrence_target _ _ _⟩

theorem same_size_wrong_tag_pin :
    (persistentGroup (registered 1 doubleState) 2 0).length =
      (initialGroup (registered 1 doubleState) 2).length ∧
    persistentGroup (registered 1 doubleState) 2 0 ≠
      initialGroup (registered 1 doubleState) 2 := by
  constructor
  · rfl
  · decide

#eval check "scan-prototype-same-size-wrong-source-tags"
  ((persistentGroup (registered 1 doubleState) 2 0).length,
    (initialGroup (registered 1 doubleState) 2).length,
    (persistentGroup (registered 1 doubleState) 2 0).map (fun x => x.2.1.val),
    (initialGroup (registered 1 doubleState) 2).map (fun x => x.2.1.val))
  (1, 1, [0], [1])

theorem no_transition_guard_pin (v : Fin (1 * (0 + 1))) :
    statementGuard 1 0 recurrenceID v = false :=
  no_recurrence_zero v

theorem empty_history_occurrence_pin (x : OccRef (program (registered 0 id) 2)) :
    False :=
  no_occurrence_zero_dim _ _ x

theorem empty_zero_occurrence_pin (x : OccRef (program (registered 0 id) 0)) :
    False :=
  no_occurrence_zero_dim _ _ x

theorem generic_coverage_pin {V : Type} {d N : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) :
    (plan f N).Coverage1 ∧ (plan f N).Coverage2 :=
  ⟨plan_coverage1 f N, plan_coverage2 f N⟩

theorem scalar_coverage_pin :
    scalarPlan.Coverage1 ∧ scalarPlan.Coverage2 :=
  generic_coverage_pin _

theorem vector_coverage_pin :
    (plan (registered 2 crossNonlinear) 2).Coverage1 ∧
      (plan (registered 2 crossNonlinear) 2).Coverage2 :=
  generic_coverage_pin _

theorem no_transition_coverage_pin :
    (plan (registered 1 doubleState) 0).Coverage1 ∧
      (plan (registered 1 doubleState) 0).Coverage2 :=
  generic_coverage_pin _

theorem empty_history_coverage_pin :
    (plan (registered 0 id) 2).Coverage1 ∧ (plan (registered 0 id) 2).Coverage2 :=
  generic_coverage_pin _

theorem empty_zero_coverage_pin :
    (plan (registered 0 id) 0).Coverage1 ∧ (plan (registered 0 id) 0).Coverage2 :=
  generic_coverage_pin _

def collectedStore {d N : Nat} (X Z : State ℚ d)
    (H : Fin d → Fin (N + 1) → ℚ) : Store (Carrier ℚ) (declarations d N)
  | ⟨.X, c⟩ => X c.1
  | ⟨.Z, c⟩ => Z c.1
  | ⟨.H, c⟩ => H c.1 c.2.1

def collectedScalarStore : Store (Carrier ℚ) (declarations 1 2) :=
  collectedStore scalarX scalarZ (fun _ l => ![5, 12, 999] l)

def collectedVectorStore : Store (Carrier ℚ) (declarations 2 2) :=
  collectedStore vectorX vectorZ (fun i l => (![![4, 7], ![16, 30], ![901, 902]] l) i)

def collectedRows {d N : Nat} (F : State ℚ d → State ℚ d)
    (ρ : Store (Carrier ℚ) (declarations d N)) : List (List ℚ) :=
  (List.finRange (N + 1)).map fun l => (List.finRange d).map fun i =>
    (program (registered d F) N).collect RationalReference.ops ρ
      (program_admEnv _ N RationalReference.ops ρ)
      (historyDefined _ N) (historyCoord i l)

theorem generic_admEnv_pin {V : Type} {d N : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) (ops : (s : Unit) → ScalarOps (Carrier V s))
    (ρ : Store (Carrier V) (declarations d N)) :
    (program f N).AdmEnv ops ρ :=
  program_admEnv f N ops ρ

theorem generic_collect_pin {V : Type} [AddCommMonoid V] {d N : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d)
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (ρ : Store (Carrier V) (declarations d N)) :
    (∀ i, (program f N).collect ops ρ (program_admEnv f N ops ρ)
      (historyDefined f N) (historyCoord i 0) =
        ρ ⟨.X, stateCoord i⟩ + ρ ⟨.Z, stateCoord i⟩) ∧
    (∀ (i : Fin d) (k : Fin N), (program f N).collect ops ρ (program_admEnv f N ops ρ)
      (historyDefined f N) (historyCoord i k.succ) =
        ρ ⟨.X, stateCoord i⟩ +
          f.transition (fun j => ρ (historyAddress d N j k.castSucc)) i) :=
  ⟨fun i => collect_zero f ops ρ _ i, fun i k => collect_succ f ops ρ _ i k⟩

theorem collected_scalar_zero_pin :
    (program (registered 1 doubleState) 2).collect RationalReference.ops collectedScalarStore
      (program_admEnv _ 2 RationalReference.ops collectedScalarStore)
      (historyDefined _ 2) (historyCoord 0 0) = 5 := by
  rw [collect_zero]
  norm_num [collectedScalarStore, collectedStore, scalarX, scalarZ]

theorem collected_scalar_succ_pin (k : Fin 2) :
    (program (registered 1 doubleState) 2).collect RationalReference.ops collectedScalarStore
      (program_admEnv _ 2 RationalReference.ops collectedScalarStore)
      (historyDefined _ 2) (historyCoord 0 k.succ) = (![12, 26] k) := by
  rw [collect_succ]
  fin_cases k
  · change (2 : ℚ) + 2 * 5 = 12
    norm_num
  · change (2 : ℚ) + 2 * 12 = 26
    norm_num

theorem collected_vector_zero_pin (i : Fin 2) :
    (program (registered 2 crossNonlinear) 2).collect RationalReference.ops collectedVectorStore
      (program_admEnv _ 2 RationalReference.ops collectedVectorStore)
      (historyDefined _ 2) (historyCoord i 0) = (![4, 7] i) := by
  rw [collect_zero]
  fin_cases i <;> norm_num [collectedVectorStore, collectedStore, vectorX, vectorZ, stateCoord]

theorem collected_vector_succ_pin (i : Fin 2) (k : Fin 2) :
    (program (registered 2 crossNonlinear) 2).collect RationalReference.ops collectedVectorStore
      (program_admEnv _ 2 RationalReference.ops collectedVectorStore)
      (historyDefined _ 2) (historyCoord i k.succ) = ((![![16, 30], ![63, 482]] k) i) := by
  rw [collect_succ]
  change vectorX i + crossNonlinear
    (fun j => (![![4, 7], ![16, 30], ![901, 902]] k.castSucc) j) i =
      ((![![16, 30], ![63, 482]] k) i)
  fin_cases i <;> fin_cases k <;> norm_num [vectorX, crossNonlinear]

theorem collected_empty_admEnv_pin :
    (program (registered 0 id) 2).AdmEnv RationalReference.ops
      (collectedStore emptyState emptyState (fun i _ => Fin.elim0 i)) ∧
    (program (registered 0 id) 0).AdmEnv RationalReference.ops
      (collectedStore emptyState emptyState (fun i _ => Fin.elim0 i)) :=
  ⟨program_admEnv _ _ _ _, program_admEnv _ _ _ _⟩

#eval check "scan-prototype-collected-scalar-direct-store"
  (collectedRows doubleState collectedScalarStore) [[5], [12], [26]]
#eval check "scan-prototype-collected-vector-direct-store"
  (collectedRows crossNonlinear collectedVectorStore) [[4, 7], [16, 30], [63, 482]]
#eval check "scan-prototype-collected-no-transitions"
  (collectedRows doubleState
    (collectedStore (N := 0) scalarX scalarZ (fun _ _ => 999))) [[5]]
#eval check "scan-prototype-collected-empty-history"
  (collectedRows (N := 2) id
    (collectedStore emptyState emptyState (fun i _ => Fin.elim0 i))) [[], [], []]
#eval check "scan-prototype-collected-empty-zero"
  (collectedRows (N := 0) id
    (collectedStore emptyState emptyState (fun i _ => Fin.elim0 i))) [[]]

#eval check "scan-prototype-collected-same-size-wrong-occurrence"
  (let f := registered 1 doubleState
   let P := program f 2
   let h := program_admEnv f 2 RationalReference.ops collectedScalarStore
   let wrong := persistentGroup f 2 0 ++ persistentGroup f 2 0
   ((group f 2 0).length, wrong.length,
     P.collect RationalReference.ops collectedScalarStore h (historyDefined f 2)
       (historyCoord 0 0),
     (wrong.map fun x => P.contribution RationalReference.ops collectedScalarStore h x.1 x.2).sum))
  (2, 2, 5, 4)

def oracleStore {d N : Nat} (F : State ℚ d → State ℚ d) (X Z : State ℚ d) :
    Store (Carrier ℚ) (declarations d N) :=
  collectedStore X Z (fun i l => history F X Z l.val i)

def independentScalarStore := oracleStore (N := 2) doubleState scalarX scalarZ
def independentVectorStore := oracleStore (N := 2) crossNonlinear vectorX vectorZ

def independentOutputRows {d : Nat} (F : State ℚ d → State ℚ d) (N : Nat)
    (η : (program (registered d F) N).Input) : List (List ℚ) :=
  (List.finRange (N + 1)).map fun l => (List.finRange d).map fun i =>
    history_output (registered d F) N η ⟨.H, rfl⟩ (historyCoord i l)

#eval check "scan-prototype-independent-scalar-model-output"
  (independentOutputRows doubleState 2 directScalarInput,
    trace doubleState scalarX scalarZ 2)
  ([[5], [12], [26]], [[5], [12], [26]])
#eval check "scan-prototype-independent-vector-model-output"
  (independentOutputRows crossNonlinear 2
    (input (registered 2 crossNonlinear) 2 vectorX vectorZ),
    trace crossNonlinear vectorX vectorZ 2)
  ([[4, 7], [16, 30], [63, 482]], [[4, 7], [16, 30], [63, 482]])
#eval check "scan-prototype-independent-no-transitions-output"
  (independentOutputRows doubleState 0 (input (registered 1 doubleState) 0 scalarX scalarZ))
  [[5]]
#eval check "scan-prototype-independent-empty-history-output"
  (independentOutputRows id 2 (input (registered 0 id) 2 emptyState emptyState))
  [[], [], []]
#eval check "scan-prototype-independent-empty-zero-output"
  (independentOutputRows id 0 directEmptyInput,
    (directEmptyInput.val .X).isSome, (directEmptyInput.val .Z).isSome,
    (directEmptyInput.val .H).isNone)
  ([[]], true, true, true)

theorem generic_history_model_pin {V : Type} [AddCommMonoid V] {d N : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input) :
    (program f N).Models ops η (historyStore f N η) ∧
      ∀ ρ, (program f N).Models ops η ρ ↔ ρ = historyStore f N η :=
  ⟨historyStore_models f N ops η, models_iff_historyStore f N ops η⟩

theorem generic_history_output_pin {V : Type} [AddCommMonoid V] {d N : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (η : (program f N).Input) :
    ((declarations d N).signature .H).axes.map Axis.extent = [d, N + 1] ∧
    (program f N).output .H = true ∧
    (η.val .X).isSome = true ∧ (η.val .Z).isSome = true ∧
    (η.val .H).isSome = false ∧
    history_output f N η ⟨.H, rfl⟩ =
      (fun c : Coord (historyShape d N) =>
        history f.transition (inputX η) (inputZ η) c.2.1.val c.1) := by
  exact ⟨rfl, rfl, η.property .X, η.property .Z, η.property .H, rfl⟩

theorem independent_scalar_model_pin :
    (program (registered 1 doubleState) 2).Models RationalReference.ops
      directScalarInput independentScalarStore ∧
    ∀ ρ, (program (registered 1 doubleState) 2).Models RationalReference.ops
      directScalarInput ρ ↔ ρ = independentScalarStore := by
  change (program (registered 1 doubleState) 2).Models RationalReference.ops
      directScalarInput (historyStore _ _ directScalarInput) ∧ _
  exact generic_history_model_pin _ _ _

theorem independent_vector_model_pin :
    (program (registered 2 crossNonlinear) 2).Models RationalReference.ops
      (input (registered 2 crossNonlinear) 2 vectorX vectorZ) independentVectorStore ∧
    ∀ ρ, (program (registered 2 crossNonlinear) 2).Models RationalReference.ops
      (input (registered 2 crossNonlinear) 2 vectorX vectorZ) ρ ↔
        ρ = independentVectorStore :=
  generic_history_model_pin _ _ _

theorem independent_scalar_output_pin (i : Fin 1) (l : Fin 3) :
    history_output (registered 1 doubleState) 2 directScalarInput
      ⟨.H, rfl⟩ (historyCoord i l) = (![5, 12, 26] l) := by
  change history doubleState scalarX scalarZ l.val i = (![5, 12, 26] l)
  fin_cases i
  fin_cases l <;> norm_num [history, doubleState, scalarX, scalarZ]

theorem independent_vector_output_pin (i : Fin 2) (l : Fin 3) :
    history_output (registered 2 crossNonlinear) 2
      (input (registered 2 crossNonlinear) 2 vectorX vectorZ)
      ⟨.H, rfl⟩ (historyCoord i l) = ((![![4, 7], ![16, 30], ![63, 482]] l) i) := by
  change history crossNonlinear vectorX vectorZ l.val i =
    ((![![4, 7], ![16, 30], ![63, 482]] l) i)
  fin_cases i <;> fin_cases l <;> norm_num [history, crossNonlinear, vectorX, vectorZ]

theorem independent_no_transition_model_pin :
    (program (registered 1 doubleState) 0).Models RationalReference.ops
      (input (registered 1 doubleState) 0 scalarX scalarZ)
      (oracleStore (N := 0) doubleState scalarX scalarZ) ∧
    ∀ ρ, (program (registered 1 doubleState) 0).Models RationalReference.ops
      (input (registered 1 doubleState) 0 scalarX scalarZ) ρ ↔
        ρ = oracleStore (N := 0) doubleState scalarX scalarZ :=
  generic_history_model_pin _ _ _

theorem independent_no_transition_output_pin :
    history_output (registered 1 doubleState) 0
      (input (registered 1 doubleState) 0 scalarX scalarZ) ⟨.H, rfl⟩ =
        (fun _ => 5) := by
  funext c
  rcases c with ⟨i, l, u⟩
  fin_cases l
  change (2 : ℚ) + 3 = 5
  norm_num

theorem independent_empty_model_pin :
    (program (registered 0 id) 2).Models RationalReference.ops
      (input (registered 0 id) 2 emptyState emptyState)
      (oracleStore (N := 2) id emptyState emptyState) ∧
    ∀ ρ, (program (registered 0 id) 2).Models RationalReference.ops
      (input (registered 0 id) 2 emptyState emptyState) ρ ↔
        ρ = oracleStore (N := 2) id emptyState emptyState :=
  generic_history_model_pin _ _ _

theorem independent_empty_zero_model_pin :
    (program (registered 0 id) 0).Models RationalReference.ops
      directEmptyInput (oracleStore (N := 0) id emptyState emptyState) ∧
    ∀ ρ, (program (registered 0 id) 0).Models RationalReference.ops directEmptyInput ρ ↔
      ρ = oracleStore (N := 0) id emptyState emptyState :=
  generic_history_model_pin _ _ _

theorem independent_empty_output_pin (N : Nat) :
    ((declarations 0 N).signature .H).axes.map Axis.extent = [0, N + 1] ∧
    history_output (registered 0 id) N
      (input (registered 0 id) N emptyState emptyState) ⟨.H, rfl⟩ =
        (fun c => Fin.elim0 c.1) := by
  refine ⟨rfl, ?_⟩
  funext c
  exact Fin.elim0 c.1

#print axioms generic_history_model_pin
#print axioms generic_command_lookup_pin
#print axioms generic_prefix_phase_lists_pin
#print axioms generic_boundary_pin
#print axioms generic_retirement_pin
#print axioms generic_command_index_pin
#print axioms generic_endpoint_lists_pin
#print axioms empty_zero_commands_pin
#print axioms no_transition_commands_pin
#print axioms empty_dimension_commands_pin
#print axioms generic_history_output_pin
#print axioms independent_scalar_model_pin
#print axioms independent_vector_model_pin
#print axioms independent_scalar_output_pin
#print axioms independent_vector_output_pin
#print axioms independent_no_transition_model_pin
#print axioms independent_no_transition_output_pin
#print axioms independent_empty_model_pin
#print axioms independent_empty_zero_model_pin
#print axioms independent_empty_output_pin
#print axioms selectedF_arrayExpr_pin
#print axioms selectedF_recurrence_pin
#print axioms validatedInput_pin
#print axioms directScalarInput_pin
#print axioms directEmptyInput_pin
#print axioms guard_partition_pin
#print axioms classification_pin
#print axioms target_partition_pin
#print axioms same_size_wrong_tag_pin
#print axioms no_transition_guard_pin
#print axioms empty_history_occurrence_pin
#print axioms empty_zero_occurrence_pin
#print axioms generic_coverage_pin
#print axioms scalar_coverage_pin
#print axioms vector_coverage_pin
#print axioms no_transition_coverage_pin
#print axioms empty_history_coverage_pin
#print axioms empty_zero_coverage_pin
#print axioms generic_admEnv_pin
#print axioms generic_collect_pin
#print axioms collected_scalar_zero_pin
#print axioms collected_scalar_succ_pin
#print axioms collected_vector_zero_pin
#print axioms collected_vector_succ_pin
#print axioms collected_empty_admEnv_pin

#eval check "scan-prototype-history-before-and-after-pub"
  (scalarPlan.readPub 2 (scalarMemory 2) (historyAddress 1 2 0 0),
  scalarPlan.readPub 3 (scalarMemory 3) (historyAddress 1 2 0 0),
  scalarPlan.readPub 5 (scalarMemory 5) (historyAddress 1 2 0 1),
  scalarPlan.readPub 6 (scalarMemory 6) (historyAddress 1 2 0 1))
  (none, some 5, none, some 12)

def vectorPlan := plan (registered 2 crossNonlinear) 2
def vectorPrefix (pc : Nat) :=
  vectorPlan.runFrom RationalReference.ops 0
    (vectorPlan.Start (input (registered 2 crossNonlinear) 2 vectorX vectorZ))
    (vectorPlan.commands.take pc)
def vectorMemory (pc : Nat) :=
  match vectorPrefix pc with
  | .done _ M | .failed _ _ M | .stuck _ M => M

def vectorPhysical (pc : Nat) : List (List (Option ℚ)) :=
  (List.finRange 3).map fun l : Fin 3 =>
    (List.finRange 2).map fun i : Fin 2 => vectorMemory pc (.inr ⟨l, i⟩)

#eval check "scan-prototype-vector-retained-all-command-physical-memory"
  ((List.range 10).map vectorPhysical)
  [[[none, none], [none, none], [none, none]],
   [[some 0, some 0], [none, none], [none, none]],
   [[some 4, some 7], [none, none], [none, none]],
   [[some 4, some 7], [none, none], [none, none]],
   [[some 4, some 7], [some 0, some 0], [none, none]],
   [[some 4, some 7], [some 16, some 30], [none, none]],
   [[some 4, some 7], [some 16, some 30], [none, none]],
   [[some 4, some 7], [some 16, some 30], [some 0, some 0]],
   [[some 4, some 7], [some 16, some 30], [some 63, some 482]],
   [[some 4, some 7], [some 16, some 30], [some 63, some 482]]]

def vectorPublished (pc : Nat) (l : Fin 3) : List (Option ℚ) :=
  (List.finRange 2).map fun i =>
    vectorPlan.readPub pc (vectorMemory pc) (historyAddress 2 2 i l)

#eval check "scan-prototype-vector-whole-previous-slice-read-boundaries"
  (vectorPublished 4 0, vectorPublished 5 1, vectorPublished 6 1, vectorPublished 7 1)
  ([some 4, some 7], [none, none], [some 16, some 30], [some 16, some 30])

#eval check "scan-prototype-empty-history-decodes-at-zero"
  (((plan (registered 0 id) 2).Decode 0
    ((plan (registered 0 id) 2).Start
      (input (registered 0 id) 2 emptyState emptyState))).isSome,
  ((plan (registered 0 id) 0).Decode 0
    ((plan (registered 0 id) 0).Start
      (input (registered 0 id) 0 emptyState emptyState))).isSome)
  (true, true)

theorem generic_prefix_membership_pin {V : Type} {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (N pc : Nat)
    (hpc : pc ≤ 3 * (N + 1)) :
    (∀ x, (plan f N).Cons pc x ↔
      ∃ i l, 3 * l.val + 2 ≤ pc ∧ x.target = historyDefAddr f N i l) ∧
    (∀ i l, (plan f N).Mat pc (historyDefAddr f N i l) ↔ 3 * l.val + 1 ≤ pc) ∧
    (∀ i l, (plan f N).Pub pc (historyAddress d N i l) ↔ 3 * (l.val + 1) ≤ pc) :=
  prefix_membership f N pc hpc

theorem generic_history_live_pin {V : Type} {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (N pc : Nat)
    (hpc : pc ≤ 3 * (N + 1)) (i : Fin d) (l : Fin (N + 1)) :
    (plan f N).Live pc (historyAddress d N i l) ↔ 3 * (l.val + 1) ≤ pc :=
  history_live_iff f N pc hpc i l

theorem generic_input_live_pin {V : Type} {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (N pc : Nat) (i : Fin d) :
    ((plan f N).Pub pc ⟨.X, stateCoord i⟩ ∧
      (plan f N).Live pc ⟨.X, stateCoord i⟩) ∧
    ((plan f N).Pub pc ⟨.Z, stateCoord i⟩ ∧
      (plan f N).Live pc ⟨.Z, stateCoord i⟩) :=
  ⟨input_pub_live f N pc _ rfl, input_pub_live f N pc _ rfl⟩

theorem generic_history_endpoints_pin {V : Type} {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (N : Nat)
    (i : Fin d) (l : Fin (N + 1)) :
    ¬ (plan f N).Live 0 (historyAddress d N i l) ∧
      (plan f N).Live (3 * (N + 1)) (historyAddress d N i l) := by
  rw [history_live_iff f N 0 (by omega),
    history_live_iff f N (3 * (N + 1)) (by omega)]
  have := l.isLt
  omega

theorem no_transition_history_live_pin :
    ¬ (plan (registered 1 doubleState) 0).Live 2 (historyAddress 1 0 0 0) ∧
      (plan (registered 1 doubleState) 0).Live 3 (historyAddress 1 0 0 0) := by
  rw [history_live_iff _ 0 2 (by omega), history_live_iff _ 0 3 (by omega)]
  decide

theorem empty_history_roles_pin (N : Nat) :
    (plan (registered 0 id) N).tensors = [.X, .Z, .H] ∧
    (program (registered 0 id) N).input .X = true ∧
    (program (registered 0 id) N).input .Z = true ∧
    (program (registered 0 id) N).input .H = false ∧
    (program (registered 0 id) N).output .H = true ∧
    (plan (registered 0 id) N).commands.length = 3 * (N + 1) :=
  ⟨rfl, rfl, rfl, rfl, rfl, plan_length _ N⟩

#print axioms generic_prefix_membership_pin
#print axioms generic_history_live_pin
#print axioms generic_input_live_pin
#print axioms generic_history_endpoints_pin
#print axioms no_transition_history_live_pin
#print axioms empty_history_roles_pin

theorem generic_side_conditions_pin {V : Type} {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (N : Nat) :
    (∀ pc B, (plan f N).commands[pc]? = some [.initZero B] →
      (plan f N).InitOK pc B) ∧
    (∀ pc G, (plan f N).commands[pc]? = some [.acc G] →
      (plan f N).AccOK pc G) ∧
    (∀ pc B, (plan f N).commands[pc]? = some [.pub B] →
      (plan f N).PubOK pc B) :=
  ⟨plan_initOK f N, plan_accOK f N, plan_pubOK f N⟩

theorem scalar_side_conditions_pin :
    scalarPlan.InitOK 3 (block (registered 1 doubleState) 2 1) ∧
    scalarPlan.AccOK 4 (group (registered 1 doubleState) 2 1) ∧
    scalarPlan.PubOK 5 (block (registered 1 doubleState) 2 1) :=
  ⟨plan_initOK _ _ _ _ (command_init _ _ 1),
    plan_accOK _ _ _ _ (command_acc _ _ 1),
    plan_pubOK _ _ _ _ (command_pub _ _ 1)⟩

theorem vector_side_conditions_pin :
    (plan (registered 2 crossNonlinear) 2).InitOK 6
      (block (registered 2 crossNonlinear) 2 2) ∧
    (plan (registered 2 crossNonlinear) 2).AccOK 7
      (group (registered 2 crossNonlinear) 2 2) ∧
    (plan (registered 2 crossNonlinear) 2).PubOK 8
      (block (registered 2 crossNonlinear) 2 2) :=
  ⟨plan_initOK _ _ _ _ (command_init _ _ 2),
    plan_accOK _ _ _ _ (command_acc _ _ 2),
    plan_pubOK _ _ _ _ (command_pub _ _ 2)⟩

theorem no_transition_side_conditions_pin :
    (plan (registered 1 doubleState) 0).InitOK 0
      (block (registered 1 doubleState) 0 0) ∧
    (plan (registered 1 doubleState) 0).AccOK 1
      (group (registered 1 doubleState) 0 0) ∧
    (plan (registered 1 doubleState) 0).PubOK 2
      (block (registered 1 doubleState) 0 0) :=
  ⟨plan_initOK _ _ _ _ (command_init _ _ 0),
    plan_accOK _ _ _ _ (command_acc _ _ 0),
    plan_pubOK _ _ _ _ (command_pub _ _ 0)⟩

theorem empty_history_side_conditions_pin (N : Nat) (k : Fin (N + 1)) :
    (plan (registered 0 id) N).InitOK (3 * k.val) [] ∧
    (plan (registered 0 id) N).AccOK (3 * k.val + 1) [] ∧
    (plan (registered 0 id) N).PubOK (3 * k.val + 2) [] := by
  simpa only [block, List.finRange_zero, List.map_nil, zero_dim_group] using
    And.intro (plan_initOK_slice (registered 0 id) N k)
      (And.intro (plan_accOK_slice (registered 0 id) N k)
        (plan_pubOK_slice (registered 0 id) N k))

theorem empty_zero_side_conditions_pin :
    (plan (registered 0 id) 0).InitOK 0 [] ∧
    (plan (registered 0 id) 0).AccOK 1 [] ∧
    (plan (registered 0 id) 0).PubOK 2 [] :=
  empty_history_side_conditions_pin 0 0

def wrongTagsPlan :=
  { scalarPlan with
    commands := scheduleCommands (List.finRange 3) (block (registered 1 doubleState) 2)
      (fun l => if l = 0 then
        initialGroup (registered 1 doubleState) 2 ++
          initialGroup (registered 1 doubleState) 2
        else group (registered 1 doubleState) 2 l) }

#eval check "scan-prototype-wrong-tags-coverage-vs-control"
  ((wrongTagsPlan.accFlat.length, wrongTagsPlan.checkCov1Nodup,
      wrongTagsPlan.checkCov1Complete, wrongTagsPlan.checkCov2Complete),
    (scalarPlan.accFlat.length, scalarPlan.checkCov1Nodup,
      scalarPlan.checkCov1Complete, scalarPlan.checkCov2Complete))
  ((6, false, false, true), (6, true, true, true))

#eval check "scan-prototype-wrong-tags-static-components-vs-control"
  ((wrongTagsPlan.checkInit 0 (block (registered 1 doubleState) 2 0),
      wrongTagsPlan.checkAccFresh 1
        (initialGroup (registered 1 doubleState) 2 ++ initialGroup (registered 1 doubleState) 2),
      wrongTagsPlan.checkAccMat 1
        (initialGroup (registered 1 doubleState) 2 ++ initialGroup (registered 1 doubleState) 2),
      wrongTagsPlan.checkPubFresh 2 (block (registered 1 doubleState) 2 0),
      wrongTagsPlan.checkPubMat 2 (block (registered 1 doubleState) 2 0),
      wrongTagsPlan.checkPubOrder 2 (block (registered 1 doubleState) 2 0)),
    (scalarPlan.checkInit 0 (block (registered 1 doubleState) 2 0),
      scalarPlan.checkAccFresh 1 (group (registered 1 doubleState) 2 0),
      scalarPlan.checkAccMat 1 (group (registered 1 doubleState) 2 0),
      scalarPlan.checkPubFresh 2 (block (registered 1 doubleState) 2 0),
      scalarPlan.checkPubMat 2 (block (registered 1 doubleState) 2 0),
      scalarPlan.checkPubOrder 2 (block (registered 1 doubleState) 2 0)))
  ((true, false, true, true, true, false), (true, true, true, true, true, true))

#eval check "scan-prototype-wrong-tags-all-targeting-occurrences"
  (decide (wrongTagsPlan.Cons 2
      ⟨historyDefined (registered 1 doubleState) 2,
        persistentOccurrence (registered 1 doubleState) 2 0 0⟩),
    decide (wrongTagsPlan.Cons 2
      ⟨historyDefined (registered 1 doubleState) 2,
        initialOccurrence (registered 1 doubleState) 2 0⟩),
    wrongTagsPlan.checkSteps, wrongTagsPlan.checkLayouts,
    wrongTagsPlan.checkPlan, scalarPlan.checkPlan)
  (false, true, false, true, false, true)

#print axioms generic_side_conditions_pin
#print axioms scalar_side_conditions_pin
#print axioms vector_side_conditions_pin
#print axioms no_transition_side_conditions_pin
#print axioms empty_history_side_conditions_pin
#print axioms empty_zero_side_conditions_pin

theorem generic_source_footprints_pin {V : Type} {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (N : Nat)
    (i : Fin d) (k : Fin (N + 1)) (l : Fin N) :
    footprint ((program f N).body (historyDefined f N) persistentID)
      (persistentOccurrence f N i k).2 = [⟨.X, stateCoord i⟩] ∧
    footprint ((program f N).body (historyDefined f N) initialID)
      (initialOccurrence f N i).2 = [⟨.Z, stateCoord i⟩] ∧
    footprint ((program f N).body (historyDefined f N) recurrenceID)
      (recurrenceOccurrence f N i l).2 =
      (List.finRange d).map fun j =>
        historyAddress d N j ⟨l.val, Nat.lt_succ_of_lt l.isLt⟩ :=
  ⟨persistentOccurrence_footprint f N i k, initialOccurrence_footprint f N i,
    recurrenceOccurrence_footprint f N i l⟩

theorem generic_readyOK_pin {V : Type} {d : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) (N : Nat) :
    ∀ pc G, (plan f N).commands[pc]? = some [.acc G] →
      (plan f N).ReadyOK pc G :=
  plan_readyOK f N

theorem generic_valid_pin {V : Type} {d : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) (N : Nat) : (plan f N).Valid :=
  plan_valid f N

theorem generic_checkPlan_pin {V : Type} {d : Nat} {r : Registry (Carrier V)}
    (f : RegisteredF r d) (N : Nat) : (plan f N).checkPlan = true :=
  plan_checkPlan f N

theorem generic_zero_transition_validity_pin {V : Type} {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) :
    (plan f 0).ReadyOK 1 (group f 0 0) ∧
    (plan f 0).Valid ∧ (plan f 0).checkPlan = true :=
  ⟨plan_readyOK_slice f 0 0, plan_valid f 0, plan_checkPlan f 0⟩

theorem generic_zero_dimension_validity_pin {V : Type} {r : Registry (Carrier V)}
    (f : RegisteredF r 0) (N : Nat) :
    (∀ k : Fin (N + 1), (plan f N).ReadyOK (3 * k.val + 1) []) ∧
    (plan f N).Valid ∧ (plan f N).checkPlan = true := by
  refine ⟨?_, plan_valid f N, plan_checkPlan f N⟩
  intro k
  simpa only [zero_dim_group] using plan_readyOK_slice f N k

theorem generic_zero_bounds_validity_pin {V : Type} {r : Registry (Carrier V)}
    (f : RegisteredF r 0) :
    (plan f 0).ReadyOK 1 [] ∧ (plan f 0).Valid ∧ (plan f 0).checkPlan = true :=
  ⟨(generic_zero_dimension_validity_pin f 0).1 0, plan_valid f 0, plan_checkPlan f 0⟩

#print axioms generic_source_footprints_pin
#print axioms generic_readyOK_pin
#print axioms generic_valid_pin
#print axioms generic_checkPlan_pin
#print axioms generic_zero_transition_validity_pin
#print axioms generic_zero_dimension_validity_pin
#print axioms generic_zero_bounds_validity_pin

theorem generic_prefix_done_R_pin {V : Type} [AddCommMonoid V] {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input)
    (pc : Nat) (hpc : pc ≤ 3 * (N + 1)) :
    ∃ M c,
      (plan f N).runFrom ops 0 ((plan f N).Start η)
        ((plan f N).commands.take pc) = .done pc M ∧
      (plan f N).refState ops η pc = some c ∧ (plan f N).R ops η pc M c :=
  prefix_done_R f N ops η pc hpc

theorem generic_history_retained_all_boundaries_pin {V : Type} [AddCommMonoid V]
    {d : Nat} {r : Registry (Carrier V)} (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input)
    (pc : Nat) (hpc : pc ≤ 3 * (N + 1)) :
    ∃ M c,
      (plan f N).runFrom ops 0 ((plan f N).Start η)
        ((plan f N).commands.take pc) = .done pc M ∧
      (plan f N).refState ops η pc = some c ∧ (plan f N).R ops η pc M c ∧
      ∀ (i : Fin d) (l : Fin (N + 1)), 3 * (l.val + 1) ≤ pc →
        readSlot (allocation f N) M (historyAddress d N i l) =
            some (history f.transition (inputX η) (inputZ η) l.val i) ∧
        (plan f N).readPub pc M (historyAddress d N i l) =
            some (history f.transition (inputX η) (inputZ η) l.val i) ∧
        M (.inr ⟨l, i⟩) =
            some (history f.transition (inputX η) (inputZ η) l.val i) := by
  obtain ⟨M, c, hr, hc, hR⟩ := prefix_done_R f N ops η pc hpc
  exact ⟨M, c, hr, hc, hR, fun i l hl => history_retained f N ops η pc hpc hr i l hl⟩

theorem generic_history_retained_later_pin {V : Type} [AddCommMonoid V]
    {d : Nat} {r : Registry (Carrier V)} (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input)
    (pc pc' : Nat) (hpc' : pc' ≤ 3 * (N + 1)) (hle : pc ≤ pc') :
    ∃ M M',
      (plan f N).runFrom ops 0 ((plan f N).Start η)
        ((plan f N).commands.take pc) = .done pc M ∧
      (plan f N).runFrom ops 0 ((plan f N).Start η)
        ((plan f N).commands.take pc') = .done pc' M' ∧
      ∀ (i : Fin d) (l : Fin (N + 1)), 3 * (l.val + 1) ≤ pc →
        M' (.inr ⟨l, i⟩) =
            some (history f.transition (inputX η) (inputZ η) l.val i) ∧
        M' (.inr ⟨l, i⟩) = M (.inr ⟨l, i⟩) ∧
        readSlot (allocation f N) M' (historyAddress d N i l) =
          readSlot (allocation f N) M (historyAddress d N i l) ∧
        (plan f N).readPub pc' M' (historyAddress d N i l) =
          (plan f N).readPub pc M (historyAddress d N i l) := by
  obtain ⟨M, _, hr, -⟩ := prefix_done_R f N ops η pc (Nat.le_trans hle hpc')
  obtain ⟨M', _, hr', -⟩ := prefix_done_R f N ops η pc' hpc'
  exact ⟨M, M', hr, hr', fun i l hl =>
    history_retained_later f N ops η pc pc' hpc' hle hr hr' i l hl⟩

theorem zero_transition_prefix_done_R_pin {V : Type} [AddCommMonoid V] {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f 0).Input)
    (pc : Nat) (hpc : pc ≤ 3) :
    ∃ M c,
      (plan f 0).runFrom ops 0 ((plan f 0).Start η)
        ((plan f 0).commands.take pc) = .done pc M ∧
      (plan f 0).refState ops η pc = some c ∧ (plan f 0).R ops η pc M c :=
  prefix_done_R f 0 ops η pc (by simpa using hpc)

theorem zero_dimension_prefix_done_R_pin {V : Type} [AddCommMonoid V]
    {r : Registry (Carrier V)} (f : RegisteredF r 0) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input)
    (pc : Nat) (hpc : pc ≤ 3 * (N + 1)) :
    ∃ M c,
      (plan f N).runFrom ops 0 ((plan f N).Start η)
        ((plan f N).commands.take pc) = .done pc M ∧
      (plan f N).refState ops η pc = some c ∧ (plan f N).R ops η pc M c :=
  prefix_done_R f N ops η pc hpc

theorem zero_bounds_prefix_done_R_pin {V : Type} [AddCommMonoid V]
    {r : Registry (Carrier V)} (f : RegisteredF r 0)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f 0).Input)
    (pc : Nat) (hpc : pc ≤ 3) :
    ∃ M c,
      (plan f 0).runFrom ops 0 ((plan f 0).Start η)
        ((plan f 0).commands.take pc) = .done pc M ∧
      (plan f 0).refState ops η pc = some c ∧ (plan f 0).R ops η pc M c :=
  zero_transition_prefix_done_R_pin f ops η pc hpc

#print axioms generic_prefix_done_R_pin
#print axioms generic_history_retained_all_boundaries_pin
#print axioms generic_history_retained_later_pin
#print axioms zero_transition_prefix_done_R_pin
#print axioms zero_dimension_prefix_done_R_pin
#print axioms zero_bounds_prefix_done_R_pin

/-- Keep the actual typed Option: empty coordinate tables must not mask failure. -/
def decodedOutput {d : Nat} (F : State ℚ d → State ℚ d) (N : Nat) (X Z : State ℚ d) :
    Option (program (registered d F) N).Output :=
  let π := plan (registered d F) N
  match execute F N X Z with
  | .done pc M => π.Decode pc M
  | _ => none

theorem decodedOutput_history {d : Nat} (F : State ℚ d → State ℚ d) (N : Nat)
    (X Z : State ℚ d) :
    decodedOutput F N X Z =
      some (history_output (registered d F) N (input (registered d F) N X Z)) := by
  obtain ⟨M, hr, hd⟩ := scan_decode_history (registered d F) N RationalReference.ops
    (input (registered d F) N X Z)
  unfold decodedOutput execute
  rw [hr]
  exact hd

theorem scalar_full_decode_pin :
    decodedOutput doubleState 2 scalarX scalarZ =
      some (history_output (registered 1 doubleState) 2 directScalarInput) :=
  decodedOutput_history _ _ _ _

theorem nonlinear_full_decode_pin :
    decodedOutput crossNonlinear 2 vectorX vectorZ =
      some (history_output (registered 2 crossNonlinear) 2
        (input (registered 2 crossNonlinear) 2 vectorX vectorZ)) :=
  decodedOutput_history _ _ _ _

theorem scalar_decode_function_pin :
    (decodedOutput doubleState 2 scalarX scalarZ).map (fun out => out ⟨.H, rfl⟩) =
      some (fun c : Coord (historyShape 1 2) => (![5, 12, 26] c.2.1 : ℚ)) := by
  rw [decodedOutput_history]
  apply congrArg some
  funext c
  rcases c with ⟨i, l, u⟩
  cases u
  exact independent_scalar_output_pin i l

theorem nonlinear_decode_function_pin :
    (decodedOutput crossNonlinear 2 vectorX vectorZ).map (fun out => out ⟨.H, rfl⟩) =
      some (fun c : Coord (historyShape 2 2) =>
        ((![![4, 7], ![16, 30], ![63, 482]] c.2.1) c.1 : ℚ)) := by
  rw [decodedOutput_history]
  apply congrArg some
  funext c
  rcases c with ⟨i, l, u⟩
  cases u
  exact independent_vector_output_pin i l

theorem no_transition_decode_function_pin :
    (decodedOutput doubleState 0 scalarX scalarZ).map (fun out => out ⟨.H, rfl⟩) =
      some (fun _ : Coord (historyShape 1 0) => (5 : ℚ)) := by
  rw [decodedOutput_history]
  exact congrArg some independent_no_transition_output_pin

theorem empty_decode_function_pin (N : Nat) :
    (decodedOutput id N emptyState emptyState).map (fun out => out ⟨.H, rfl⟩) =
      some (fun c : Coord (historyShape 0 N) => (Fin.elim0 c.1 : ℚ)) := by
  rw [decodedOutput_history]
  exact congrArg some (independent_empty_output_pin N).2

theorem combined_zero_decode_pin :
    decodedOutput id 0 emptyState emptyState =
      some (history_output (registered 0 id) 0 directEmptyInput) :=
  decodedOutput_history _ _ _ _

theorem combined_zero_decode_function_pin :
    (decodedOutput id 0 emptyState emptyState).map (fun out => out ⟨.H, rfl⟩) =
      some (fun c : Coord (historyShape 0 0) => (Fin.elim0 c.1 : ℚ)) :=
  empty_decode_function_pin 0

#eval check "scan-prototype-full-history-equality-scalar"
  (decoded doubleState 2 scalarX scalarZ == some (trace doubleState scalarX scalarZ 2))
  true
#eval check "scan-prototype-full-history-equality-nonlinear"
  (decoded crossNonlinear 2 vectorX vectorZ ==
    some (trace crossNonlinear vectorX vectorZ 2)) true
#eval check "scan-prototype-combined-zero-successful-decode"
  (kind id 0 emptyState emptyState, (decodedOutput id 0 emptyState emptyState).isSome,
    decoded id 0 emptyState emptyState)
  (("done", 3), true, some [[]])

/-- A terminal-only observer cannot detect omitted earlier slices.
    Whole-history equality must reject this despite the correct last state. -/
def terminalOnlyHistory : List (List ℚ) := [[26]]

#eval check "scan-prototype-terminal-only-observation-control"
  (terminalOnlyHistory.getLast? == (trace doubleState scalarX scalarZ 2).getLast?,
    terminalOnlyHistory == trace doubleState scalarX scalarZ 2,
    decoded doubleState 2 scalarX scalarZ == some terminalOnlyHistory)
  (true, false, false)

#print axioms decodedOutput_history
#print axioms scalar_full_decode_pin
#print axioms nonlinear_full_decode_pin
#print axioms scalar_decode_function_pin
#print axioms nonlinear_decode_function_pin
#print axioms no_transition_decode_function_pin
#print axioms empty_decode_function_pin
#print axioms combined_zero_decode_pin
#print axioms combined_zero_decode_function_pin

theorem generic_scan_done_pin {V : Type} [AddCommMonoid V] {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input) :
    ∃ M, (plan f N).runPlan ops ((plan f N).Start η) = .done (3 * (N + 1)) M :=
  scan_done f N ops η

theorem generic_scan_decode_history_pin {V : Type} [AddCommMonoid V] {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input) :
    ((declarations d N).signature .H).axes.map Axis.extent = [d, N + 1] ∧
    ∃ M, (plan f N).runPlan ops ((plan f N).Start η) = .done (3 * (N + 1)) M ∧
      (plan f N).Decode (3 * (N + 1)) M =
        some (history_output f N η : (program f N).Output) :=
  ⟨(generic_history_output_pin f η).1, scan_decode_history f N ops η⟩

theorem generic_scan_denotation_history_pin {V : Type} [AddCommMonoid V] {d : Nat}
    {r : Registry (Carrier V)} (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input) :
    (program f N).denotation ops η (scan_admInput f N ops η) =
      (history_output f N η : (program f N).Output) :=
  scan_denotation_history f N ops η

theorem zero_transition_scan_decode_history_pin {V : Type} [AddCommMonoid V]
    {d : Nat} {r : Registry (Carrier V)} (f : RegisteredF r d)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f 0).Input) :
    ((declarations d 0).signature .H).axes.map Axis.extent = [d, 1] ∧
    ∃ M, (plan f 0).runPlan ops ((plan f 0).Start η) = .done 3 M ∧
      (plan f 0).Decode 3 M = some (history_output f 0 η : (program f 0).Output) :=
  generic_scan_decode_history_pin f 0 ops η

theorem zero_dimension_scan_decode_history_pin {V : Type} [AddCommMonoid V]
    {r : Registry (Carrier V)} (f : RegisteredF r 0) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input) :
    ((declarations 0 N).signature .H).axes.map Axis.extent = [0, N + 1] ∧
    ∃ M, (plan f N).runPlan ops ((plan f N).Start η) = .done (3 * (N + 1)) M ∧
      (plan f N).Decode (3 * (N + 1)) M =
        some (history_output f N η : (program f N).Output) :=
  generic_scan_decode_history_pin f N ops η

theorem zero_bounds_scan_decode_history_pin {V : Type} [AddCommMonoid V]
    {r : Registry (Carrier V)} (f : RegisteredF r 0)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f 0).Input) :
    ((declarations 0 0).signature .H).axes.map Axis.extent = [0, 1] ∧
    ∃ M, (plan f 0).runPlan ops ((plan f 0).Start η) = .done 3 M ∧
      (plan f 0).Decode 3 M = some (history_output f 0 η : (program f 0).Output) :=
  zero_dimension_scan_decode_history_pin f 0 ops η

#print axioms generic_scan_done_pin
#print axioms generic_scan_decode_history_pin
#print axioms generic_scan_denotation_history_pin
#print axioms zero_transition_scan_decode_history_pin
#print axioms zero_dimension_scan_decode_history_pin
#print axioms zero_bounds_scan_decode_history_pin

def rawRoleInput {d : Nat} (N : Nat) (X Z : State ℚ d)
    (hasX hasZ hasH : Bool) : InputBinding (K := Carrier ℚ) (σ := declarations d N) :=
  fun t => match t with
  | .X => if hasX then some (fun p => X p.1) else none
  | .Z => if hasZ then some (fun p => Z p.1) else none
  | .H => if hasH then some (fun _ => 37) else none

def rawValidationRole {d : Nat} {r : Registry (Carrier ℚ)} (f : RegisteredF r d)
    (N : Nat) (η : InputBinding (K := Carrier ℚ) (σ := declarations d N)) : String :=
  match (plan f N).validateInput η with
  | .ok _ => "accepted"
  | .error .X => "X"
  | .error .Z => "Z"
  | .error .H => "H"

def rawRoleNeighbours {d : Nat} (F : State ℚ d → State ℚ d)
    (N : Nat) (X Z : State ℚ d) : List (String × String) :=
  [(false, true, false), (true, false, false), (true, true, true)].map fun flags =>
    (rawValidationRole (registered d F) N (rawRoleInput N X Z flags.1 flags.2.1 flags.2.2),
      rawValidationRole (registered d F) N (rawRoleInput N X Z true true false))

#eval check "scan-regression-raw-input-role-neighbours"
  (rawRoleNeighbours doubleState 2 scalarX scalarZ)
  [("X", "accepted"), ("Z", "accepted"), ("H", "accepted")]

#eval check "scan-regression-empty-raw-input-role-neighbours"
  (rawRoleNeighbours id 0 emptyState emptyState)
  [("X", "accepted"), ("Z", "accepted"), ("H", "accepted")]

#eval check "scan-regression-empty-inputs-present-at-tensor-role"
  (let η := rawRoleInput 0 emptyState emptyState true true false
  ((η .X).isSome, (η .Z).isSome, (η .H).isSome))
  (true, true, false)

#eval check "scan-regression-combined-zero-check-done-full-decode"
  ((plan (registered 0 id) 0).checkPlan,
  kind id 0 emptyState emptyState, (decodedOutput id 0 emptyState emptyState).isSome,
  decoded id 0 emptyState emptyState, some (trace id emptyState emptyState 0))
  (true, ("done", 3), true, some [[]], some [[]])

#eval check "scan-regression-extended-nonlinear-check-done-full-decode"
  ((plan (registered 2 crossNonlinear) 3).checkPlan,
  kind crossNonlinear 3 vectorX vectorZ,
  (decodedOutput crossNonlinear 3 vectorX vectorZ).isSome,
  decoded crossNonlinear 3 vectorX vectorZ, some (trace crossNonlinear vectorX vectorZ 3))
  (true, ("done", 12), true,
    some [[4, 7], [16, 30], [63, 482], [609, 30368]],
    some [[4, 7], [16, 30], [63, 482], [609, 30368]])

theorem extended_nonlinear_decode_function_pin :
    (decodedOutput crossNonlinear 3 vectorX vectorZ).map (fun out => out ⟨.H, rfl⟩) =
      some (fun c : Coord (historyShape 2 3) =>
        ((![![4, 7], ![16, 30], ![63, 482], ![609, 30368]] c.2.1) c.1 : ℚ)) := by
  rw [decodedOutput_history]
  apply congrArg some
  funext c
  rcases c with ⟨i, l, u⟩
  cases u
  change history crossNonlinear vectorX vectorZ l.val i = _
  exact congrFun (congrFun extended_nonlinear_full_history_pin l) i

/-- Only the selected array operator is unary and total; the scalar binary entry is partial. -/
def mixedRegistry (d : Nat) (F : State ℚ d → State ℚ d) : Registry (Carrier ℚ) where
  Op := Bool
  arity := fun | false => 1 | true => 2
  input := fun op _ => match op with | false => stateTy d | true => .scalar ()
  output := fun | false => stateTy d | true => .scalar ()
  domain := fun op _ => !op
  meaning := fun op => match op with
    | false => fun xs _ p => F (fun i => xs 0 (stateCoord i)) p.1
    | true => fun xs _ => (xs 0 : ℚ) + (xs 1 : ℚ)

def mixedRegistered (d : Nat) (F : State ℚ d → State ℚ d) :
    RegisteredF (mixedRegistry d F) d where
  op := false
  unary := rfl
  input_eq := fun _ => rfl
  output_eq := rfl
  total := fun _ => rfl

def mixedSelected := selectedF (mixedRegistered 2 crossNonlinear) 2 rfl
def mixedInput := input mixedSelected 2 vectorX vectorZ
def mixedExecute :=
  (plan mixedSelected 2).runPlan RationalReference.ops ((plan mixedSelected 2).Start mixedInput)

def mixedDecodedOutput : Option (program mixedSelected 2).Output :=
  match mixedExecute with
  | .done pc M => (plan mixedSelected 2).Decode pc M
  | _ => none

def mixedDecoded : Option (List (List ℚ)) :=
  mixedDecodedOutput.map fun out =>
    (List.finRange 3).map fun l =>
      (List.finRange 2).map fun i => out ⟨.H, rfl⟩ (historyCoord i l)

#eval check (α := Nat × Nat × String × String × Bool × Option ℚ)
  "scan-regression-mixed-registry-binary-scalar-unused-partial"
  ((mixedRegistry 2 crossNonlinear).arity false,
  (mixedRegistry 2 crossNonlinear).arity true,
  (match (mixedRegistry 2 crossNonlinear).input true (0 : Fin 2) with
   | .scalar _ => "scalar" | .array _ _ => "array"),
  (match (mixedRegistry 2 crossNonlinear).output true with
   | .scalar _ => "scalar" | .array _ _ => "array"),
  (mixedRegistry 2 crossNonlinear).domain true (fun _ => (7 : ℚ)),
  (mixedRegistry 2 crossNonlinear).apply true (fun _ => (7 : ℚ)))
  (1, 2, "scalar", "scalar", false, none)

#eval check "scan-regression-mixed-registry-check-done-full-decode"
  ((plan mixedSelected 2).checkPlan,
  (match mixedExecute with
   | .done pc _ => ("done", pc)
   | .failed _ pc _ => ("failed", pc)
   | .stuck pc _ => ("stuck", pc)),
  mixedDecodedOutput.isSome, mixedDecoded, some (trace crossNonlinear vectorX vectorZ 2))
  (true, ("done", 9), true, some [[4, 7], [16, 30], [63, 482]],
    some [[4, 7], [16, 30], [63, 482]])

#eval check "scan-regression-mixed-selected-nonlinear-transition"
  ((mixedSelected.transition (history crossNonlinear vectorX vectorZ 0) 0),
  (mixedSelected.transition (history crossNonlinear vectorX vectorZ 0) 1))
  (15, 28)

theorem mixed_selected_scan_decode_pin (N : Nat) (η : (program mixedSelected N).Input) :
    ∃ M, (plan mixedSelected N).runPlan RationalReference.ops
        ((plan mixedSelected N).Start η) = .done (3 * (N + 1)) M ∧
      (plan mixedSelected N).Decode (3 * (N + 1)) M =
        some (history_output mixedSelected N η) :=
  (generic_scan_decode_history_pin mixedSelected N RationalReference.ops η).2

theorem mixed_decoded_history_pin :
    mixedDecodedOutput = some (history_output mixedSelected 2 mixedInput) := by
  obtain ⟨M, hr, hd⟩ := mixed_selected_scan_decode_pin 2 mixedInput
  unfold mixedDecodedOutput mixedExecute
  rw [hr]
  exact hd

theorem mixed_decode_function_pin :
    mixedDecodedOutput.map (fun out => out ⟨.H, rfl⟩) =
      some (fun c : Coord (historyShape 2 2) =>
        ((![![4, 7], ![16, 30], ![63, 482]] c.2.1) c.1 : ℚ)) := by
  rw [mixed_decoded_history_pin]
  apply congrArg some
  funext c
  rcases c with ⟨i, l, u⟩
  cases u
  change history crossNonlinear vectorX vectorZ l.val i = _
  exact congrFun (congrFun nonlinear_full_history_pin l) i

#print axioms extended_nonlinear_decode_function_pin
#print axioms mixed_selected_scan_decode_pin
#print axioms mixed_decoded_history_pin
#print axioms mixed_decode_function_pin

end LeanNCD.Semantics.PlanScanHistoryTest

#audit_axioms LeanNCD.Semantics.Program.Plan.ScanHistory
#audit_axioms LeanNCD.Semantics.PlanScanHistoryTest
#audit_axioms LeanNCD.Semantics.PlanScanHistoryOracleTest
