import IndexedAffineScanInterpretation

namespace IndexedExecutionExperiment.AffineScan.HistoryTest

open LeanNCD.Semantics LeanNCD.Eval.Plan
open IndexedComponentExecution IndexedOpenComposition
open History Interpretation

def rationalInput (p : Profile d n) : (program p).Input :=
  input p fun slot q =>
    let coordinate := (List.ofFn (Coord.raw q)).getD 0 0
    (coordinate + 1 : ℚ) / (if (outerSlot p slot).val = 0 then 2 else 3)

/-- An observation of the existing default rational semantic executor, not a scan executor. -/
def rationalHistory (p : Profile d n) : Except String (List ℚ) :=
  match (runChecked (contract p) (fragment p) (rationalInput p).val).outcome with
  | .complete g =>
      (List.finRange (canonicalLayout (historyShape d n)).count).mapM fun s =>
        match g.available ⟨.inr (), (canonicalLayout (historyShape d n)).enumerate s⟩ with
        | some value => .ok value
        | none => .error "completed semantic run omitted a materialized history address"
  | .failed _ _ => .error "pure rational semantic run failed"
  | .blocked _ _ => .error "ranked rational semantic run blocked"
  | .invalidInput _ => .error "validated rational input rejected"
  | .invalidGraph _ => .error "constructed semantic graph rejected"
  | .contractMismatch _ _ => .error "constructed semantic source-contract mismatch"
  | .collectorMismatch _ _ => .error "constructed semantic collector mismatch"
  | .exhausted _ => .error "default rational semantic run exhausted"

theorem rationalHistory_solution (p : Profile d n) :
    rationalHistory p =
      .ok ((List.finRange (canonicalLayout (historyShape d n)).count).map fun s =>
        wholeStore p (rationalInput p)
          ⟨.inr (), (canonicalLayout (historyShape d n)).enumerate s⟩) := by
  obtain ⟨g, c, finished, done, reference, related, full, final⟩ :=
    default_full_history p (rationalInput p)
  unfold rationalHistory
  rw [done]
  have all : ∀ ss : List (Fin (canonicalLayout (historyShape d n)).count),
      (ss.mapM fun s =>
        match g.available ⟨.inr (), (canonicalLayout (historyShape d n)).enumerate s⟩ with
        | some value => (Except.ok value : Except String ℚ)
        | none => .error "completed semantic run omitted a materialized history address") =
      .ok (ss.map fun s => wholeStore p (rationalInput p)
        ⟨.inr (), (canonicalLayout (historyShape d n)).enumerate s⟩) := by
    intro ss
    induction ss with
    | nil => rfl
    | cons s ss ih =>
        rw [List.mapM_cons, ih, full]
        rfl
  exact all _

def referenceHistory (p : Profile d n) : Except String (List ℚ) :=
  match (Program.Executor.run (program p) RationalReference.ops (schedule p)
      (rationalInput p)).outcome with
  | .complete c finished =>
      .ok ((List.finRange (canonicalLayout (historyShape d n)).count).map fun s =>
        (program p).finalStore c finished
          ⟨.inr (), (canonicalLayout (historyShape d n)).enumerate s⟩)
  | .failed _ _ _ => .error "pure rational reference run failed"
  | .blocked _ _ _ => .error "ranked rational reference run blocked"
  | .exhausted _ => .error "default rational reference run exhausted"

theorem referenceHistory_solution (p : Profile d n) :
    referenceHistory p =
      .ok ((List.finRange (canonicalLayout (historyShape d n)).count).map fun s =>
        wholeStore p (rationalInput p)
          ⟨.inr (), (canonicalLayout (historyShape d n)).enumerate s⟩) := by
  obtain ⟨g, c, finished, done, reference, related, full, final⟩ :=
    default_full_history p (rationalInput p)
  unfold referenceHistory
  rw [reference]
  change Except.ok ((List.finRange (canonicalLayout (historyShape d n)).count).map
      (fun s => (program p).finalStore c finished
        ⟨.inr (), (canonicalLayout (historyShape d n)).enumerate s⟩)) = _
  rw [final]

theorem actual_executor_agreement (p : Profile d n) :
    rationalHistory p = referenceHistory p :=
  (rationalHistory_solution p).trans (referenceHistory_solution p).symm

end IndexedExecutionExperiment.AffineScan.HistoryTest

#audit_axioms IndexedExecutionExperiment.AffineScan.HistoryTest
