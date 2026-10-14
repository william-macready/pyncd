import LeanNCD.Semantics.Plan.ScanHistory.Recurrence
import Semantics.ExecutableReferenceTest

namespace LeanNCD.Semantics.ScanHistoryRecurrencePrototype

open Program.Plan.ScanHistory ExecutableReferenceFixtures

def scalarX : State ℚ 1 := fun _ => 2
def scalarZ : State ℚ 1 := fun _ => 3
def doubleState : State ℚ 1 → State ℚ 1 := fun h i => 2 * h i

def trace {d : Nat} (F : State ℚ d → State ℚ d) (X Z : State ℚ d) (N : Nat) :
    List (List ℚ) :=
  (List.range (N + 1)).map fun n => (List.finRange d).map (history F X Z n)

#eval check "scan-oracle-scalar-full-history"
  (trace doubleState scalarX scalarZ 2) [[5], [12], [26]]

#eval check "scan-oracle-no-transitions"
  (trace doubleState scalarX scalarZ 0) [[5]]

def vectorX : State ℚ 2 := ![1, 2]
def vectorZ : State ℚ 2 := ![3, 5]
def crossNonlinear : State ℚ 2 → State ℚ 2 :=
  fun h => ![2 * h 0 + h 1, h 0 * h 1]

#eval check "scan-oracle-cross-coordinate-nonlinear"
  (trace crossNonlinear vectorX vectorZ 2) [[4, 7], [16, 30], [63, 482]]

def emptyState : State ℚ 0 := Fin.elim0

#eval check "scan-oracle-empty-state"
  (trace id emptyState emptyState 2) [[], [], []]

example : (history doubleState scalarX scalarZ 2) 0 = 26 := by
  norm_num [history, doubleState, scalarX, scalarZ]
example : (history crossNonlinear vectorX vectorZ 2) 1 = 482 := by
  norm_num [history, crossNonlinear, vectorX, vectorZ]

end LeanNCD.Semantics.ScanHistoryRecurrencePrototype
