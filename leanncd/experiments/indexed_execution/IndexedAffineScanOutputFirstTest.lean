import IndexedAffineScanHistoryTest
import IndexedAffineScanCompilerExamples

/-! The compiler always places context positions before output positions, so an output-first term
arises only from a hand-built plan. These controls flip real compiled donors to the other ordering
(iteration shape `[d, n]`, output position 0, context position 1, coefficient columns swapped so the
meaning is unchanged) and require that the unchanged checker, the profile and the exact-rational whole
history all agree with the original. A flip that leaves the columns alone changes the meaning and must
not reproduce the original history. Exact-rational semantics only; no Float `runDenseScan` claim. -/

namespace IndexedExecutionExperiment.AffineScan.OutputFirstTest

open LeanNCD.Eval.Plan
open CompilerExamples HistoryTest

/-- Swap the term's position order; `swapColumns` also swaps every read's coefficient columns. -/
def flipTerm (swapColumns : Bool) (t : TermPlan) : TermPlan :=
  { t with
    iterationShape := t.iterationShape.reverse
    contextPos := t.outputPos.map (fun _ => 1)
    outputPos := t.contextPos.map (fun _ => 0)
    factors := t.factors.map fun
      | .read r =>
          if swapColumns then
            .read { r with map := { r.map with coeffs := r.map.coeffs.map fun row =>
              #[row.getD 1 0, row.getD 0 0] } }
          else .read r
      | x => x }

def flipRaw (swapColumns : Bool) (raw : RawScanPlan) : RawScanPlan :=
  { raw with stepBlock := { raw.stepBlock with
    steps := raw.stepBlock.steps.map fun
      | .assign a => .assign { a with terms := a.terms.map (flipTerm swapColumns) }
      | x => x } }

def stepTerms (raw : RawScanPlan) : Array TermPlan :=
  (((raw.stepBlock.steps.getD 0 default).assign?).map (·.terms)).getD #[]

def history (label : String) (p : Profile d n) : IO (List ℚ) :=
  match rationalHistory p with
  | .ok values => pure values
  | .error message => throw (IO.userError s!"{label}: {message}")

/-- The output-first variant of a real donor is admitted by the unchanged checker and the profile,
and has the same exact-rational whole history; the column-preserving flip does not. -/
def check (label : String) (result : Except String (CompiledExample d n)) : IO Unit := do
  let e ← match result with
    | .ok e => pure e
    | .error message => throw (IO.userError s!"{label}: compiler rejected: {message}")
  let sigs := e.prepared.plan.raw.tensorSigs
  let raw := flipRaw true e.raw
  let terms := stepTerms raw
  unless !terms.isEmpty && terms.all (fun t => t.contextPos == #[1] && t.outputPos == #[0]) do
    throw (IO.userError s!"{label}: flipped terms are not output-first (vacuous control)")
  unless (checkScanPlan sigs raw).isOk do
    throw (IO.userError s!"{label}: the unchanged checker refused the output-first plan")
  let flipped ← match certifyProfile sigs raw d n with
    | .ok p => pure p
    | .error error => throw (IO.userError s!"{label}: profile refused output-first: {repr error}")
  let original ← history label e.profile
  let reordered ← history s!"{label} (output-first)" flipped
  unless reordered.length == d * (n + 1) do
    throw (IO.userError s!"{label}: output-first history lost coordinates")
  unless reordered == original do
    throw (IO.userError s!"{label}: output-first history differs from the original")
  -- Wrong flip: positions reordered but columns kept, so the meaning changes.
  let wrong := flipRaw false e.raw
  match certifyProfile sigs wrong d n with
  | .error _ => pure ()
  | .ok p =>
    let values ← history s!"{label} (wrong flip)" p
    unless values != original do
      throw (IO.userError s!"{label}: column-preserving flip reproduced the original history")
  IO.println s!"{label}: output-first ordering admitted, same exact-rational history; wrong flip distinguished"

def checkAll : IO Unit := do
  check "shift" shiftExample
  check "mixed" mixedExample
  check "deep" deepExample

end IndexedExecutionExperiment.AffineScan.OutputFirstTest

run_cmd IndexedExecutionExperiment.AffineScan.OutputFirstTest.checkAll

#audit_axioms IndexedExecutionExperiment.AffineScan.OutputFirstTest
