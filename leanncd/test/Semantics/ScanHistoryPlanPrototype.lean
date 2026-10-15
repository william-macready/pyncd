import LeanNCD.Semantics.Plan.ScanHistory.Plan
import LeanNCD.Semantics.Plan.ScanHistory.Coverage
import LeanNCD.Semantics.Plan.ScanHistory.Evaluation
import LeanNCD.Semantics.Plan.ScanHistory.Model
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

end LeanNCD.Semantics.ScanHistoryPlanPrototype

#audit_axioms LeanNCD.Semantics.Program.Plan.ScanHistory
#audit_axioms LeanNCD.Semantics.ScanHistoryPlanPrototype
