import IndexedAffineScanHistoryTest
import IndexedAffineScanMixedCompilerCertificate

namespace IndexedExecutionExperiment.AffineScan.CompilerHistoryTest

open LeanNCD.Semantics LeanNCD.Eval.Plan
open IndexedComponentExecution IndexedOpenComposition
open IndexedWitness CategoryTheory
open CompilerExamples History Interpretation HistoryTest

/-- Consumers use the actual compiler-returned profile, not an assumed model or run agreement. -/
theorem compiler_models (e : CompiledExample d n) (η : (program e.profile).Input) :
    ∃! ρ : FullStore e.profile, Recurrence e.profile η ρ :=
  exists_unique_whole_history e.profile η

theorem compiler_execution (e : CompiledExample d n) (η : (program e.profile).Input) :
    ∃ (g : State (declarations e.profile)) (c : (program e.profile).Running)
        (finished : (program e.profile).Complete c),
      (runChecked (contract e.profile) (fragment e.profile) η.val).outcome = .complete g ∧
      (Program.Executor.run (program e.profile) RationalReference.ops (schedule e.profile)
        η).outcome = .complete c finished ∧
      Relation (sourceMatch e.profile) g c ∧
      (∀ a, g.available a = some (wholeStore e.profile η a)) ∧
      (program e.profile).finalStore c finished = wholeStore e.profile η :=
  default_full_history e.profile η

theorem compiler_category (e : CompiledExample d n) :
    witnessArrow e.profile = (Quotient.mk _ (componentSpan (component e.profile)) :
      inputInterface (component e.profile) ⟶ outputInterface (component e.profile)) :=
  categorical_whole_history e.profile

theorem shift_unique_history :
    ∃! ρ : FullStore shiftCertifiedProfile,
      Recurrence shiftCertifiedProfile (rationalInput shiftCertifiedProfile) ρ :=
  compiler_models shiftCompiled (rationalInput shiftCertifiedProfile)

theorem shift_exact_model :
    (program shiftCertifiedProfile).Models RationalReference.ops
      (rationalInput shiftCertifiedProfile)
      (wholeStore shiftCertifiedProfile (rationalInput shiftCertifiedProfile)) :=
  wholeStore_model shiftCertifiedProfile (rationalInput shiftCertifiedProfile)

theorem shift_category :
    witnessArrow shiftCertifiedProfile =
      (Quotient.mk _ (componentSpan (component shiftCertifiedProfile)) :
        inputInterface (component shiftCertifiedProfile) ⟶
          outputInterface (component shiftCertifiedProfile)) :=
  compiler_category shiftCompiled

theorem shift_exact_executor_agreement :
    rationalHistory shiftCertifiedProfile = referenceHistory shiftCertifiedProfile :=
  actual_executor_agreement shiftCertifiedProfile

theorem shift_default_full_store :
    ∃ g, (runChecked (contract shiftCertifiedProfile) (fragment shiftCertifiedProfile)
      (rationalInput shiftCertifiedProfile).val).outcome = .complete g ∧
      ∀ a, g.available a =
        some (wholeStore shiftCertifiedProfile (rationalInput shiftCertifiedProfile) a) := by
  obtain ⟨g, c, finished, done, reference, related, full, final⟩ :=
    compiler_execution shiftCompiled (rationalInput shiftCertifiedProfile)
  exact ⟨g, done, full⟩

theorem shift_reference_full_store :
    ∃ (c : (program shiftCertifiedProfile).Running)
        (finished : (program shiftCertifiedProfile).Complete c),
      (Program.Executor.run (program shiftCertifiedProfile) RationalReference.ops
        (schedule shiftCertifiedProfile) (rationalInput shiftCertifiedProfile)).outcome =
          .complete c finished ∧
      (program shiftCertifiedProfile).finalStore c finished =
        wholeStore shiftCertifiedProfile (rationalInput shiftCertifiedProfile) := by
  obtain ⟨g, c, finished, done, reference, related, full, final⟩ :=
    compiler_execution shiftCompiled (rationalInput shiftCertifiedProfile)
  exact ⟨c, finished, reference, final⟩

def certifiedExamples : List (Σ d : Nat, Σ n : Nat, CompiledExample d n) :=
  [⟨4, 3, shiftCompiled⟩, ⟨4, 3, strideCompiled⟩,
   ⟨4, 3, reversalCompiled⟩, ⟨4, 3, mixedCompiled⟩,
   ⟨4, 3, deepCompiled⟩, ⟨2, 2, boundaryCompiled⟩,
   ⟨2, 0, zeroRecurrenceCompiled⟩, ⟨0, 2, emptySpatialCompiled⟩,
   ⟨0, 0, emptyBothCompiled⟩]

theorem certified_examples_count : certifiedExamples.length = 9 := rfl

/-- For each of the nine closed compiler donors: a unique whole-history model, the categorical
comparison arrow, and both default executions with their full stores. Exact-rational semantic
interpretation of the returned plan tables only; no Float `runDenseScan` claim. -/
theorem certified_examples_full_meaning (e : CompiledExample d n)
    (_certified : ⟨d, n, e⟩ ∈ certifiedExamples) (η : (program e.profile).Input) :
    (∃! ρ : FullStore e.profile, Recurrence e.profile η ρ) ∧
    witnessArrow e.profile = (Quotient.mk _ (componentSpan (component e.profile)) :
      inputInterface (component e.profile) ⟶ outputInterface (component e.profile)) ∧
    ∃ (g : State (declarations e.profile)) (c : (program e.profile).Running)
        (finished : (program e.profile).Complete c),
      (runChecked (contract e.profile) (fragment e.profile) η.val).outcome = .complete g ∧
      (Program.Executor.run (program e.profile) RationalReference.ops (schedule e.profile)
        η).outcome = .complete c finished ∧
      Relation (sourceMatch e.profile) g c ∧
      (∀ a, g.available a = some (wholeStore e.profile η a)) ∧
      (program e.profile).finalStore c finished = wholeStore e.profile η :=
  ⟨compiler_models e η, compiler_category e, compiler_execution e η⟩

def observeExample (label : String) (result : Except String (CompiledExample d n))
    (expected : List ℚ) (expectedInputs : List (List Nat)) : IO Unit := do
  let e ← match result with
    | .ok e => pure e
    | .error message => throw (IO.userError s!"{label}: compiler/profile rejected: {message}")
  let values ← match rationalHistory e.profile with
    | .ok values => pure values
    | .error message => throw (IO.userError s!"{label}: {message}")
  let reference ← match referenceHistory e.profile with
    | .ok values => pure values
    | .error message => throw (IO.userError s!"{label}: {message}")
  unless values == reference do
    throw (IO.userError s!"{label}: actual default semantic/reference whole histories differ")
  unless values == expected do
    throw (IO.userError s!"{label}: exact rational full history changed: {repr values}")
  unless values.length == d * (n + 1) do
    throw (IO.userError s!"{label}: materialized history coordinate count changed")
  let inputShapes := (component e.profile).inputs.map fun port => port.axes.map Axis.extent
  unless inputShapes == expectedInputs do
    throw (IO.userError s!"{label}: actual external capture metadata changed: {repr inputShapes}")
  let outputShapes := (component e.profile).outputs.map fun port => port.axes.map Axis.extent
  unless outputShapes == [[d, n + 1]] do
    throw (IO.userError s!"{label}: complete history port metadata was erased or changed")
  IO.println s!"{label}: exact rational history = {repr values}"

def observeAll : IO Unit := do
  observeExample "shift" shiftExample
    [1 / 2, 0, 0, 0, 1, 1 / 2, 0, 0, 3 / 2, 1, 1 / 2, 0, 2, 3 / 2, 1, 1 / 2] [[4]]
  observeExample "stride" strideExample
    [1 / 2, 1 / 2, 1 / 2, 1 / 2, 1, 3 / 2, 0, 0, 3 / 2, 0, 0, 0, 2, 0, 0, 0] [[4]]
  observeExample "reversal" reversalExample
    [1 / 2, 2, 1 / 2, 2, 1, 3 / 2, 1, 3 / 2, 3 / 2, 1, 3 / 2, 1, 2, 1 / 2, 2, 1 / 2] [[4]]
  observeExample "mixed" mixedExample
    [1 / 2, 1 / 2, 88 / 9, 14523712 / 27, 1, 8 / 3, 425 / 4, 0,
      3 / 2, 15 / 2, 1904 / 3, 0, 2, 16, 0, 0] [[4], [9]]
  observeExample "deep" deepExample
    [1 / 2, 1 / 2, 1 / 2, 1, 1, 1, 1, 2, 3 / 2, 3 / 2, 3 / 2, 3, 2, 2, 2, 4] [[4]]
  observeExample "zero recurrence"
    (compileExample (Prototype.spatialSched 2 0) (Prototype.spatialInputs 2) 2 0) [1 / 2, 1] [[2]]
  observeExample "empty spatial"
    (compileExample (Prototype.spatialSched 0 2) (Prototype.spatialInputs 0) 0 2) [] [[0]]
  observeExample "empty spatial and zero recurrence"
    (compileExample (Prototype.spatialSched 0 0) (Prototype.spatialInputs 0) 0 0) [] [[0]]

def checkNegativeControls : IO Unit := do
  let e ← match mixedExample with
    | .ok e => pure e
    | .error message => throw (IO.userError message)
  let baseline ← match rationalHistory e.profile with
    | .ok values => pure values
    | .error message => throw (IO.userError message)
  for (label, result) in [("wrong basis columns", wrongBasisExample),
      ("wrong spatial map", wrongMapExample), ("wrong multiplicity", wrongMultiplicityExample)] do
    let p ← match result with
      | .ok p => pure p
      | .error message => throw (IO.userError s!"{label}: {message}")
    let values ← match rationalHistory p with
      | .ok values => pure values
      | .error message => throw (IO.userError s!"{label}: {message}")
    unless values != baseline do
      throw (IO.userError s!"{label}: full rational history did not distinguish the wrong table")
    unless observedFootprint p 1 2 != observedFootprint e.profile 1 2 do
      throw (IO.userError s!"{label}: ordered actual-table footprint did not distinguish the wrong table")
  let reordered ← match wrongOrderExample with
    | .ok p => pure p
    | .error message => throw (IO.userError message)
  unless rationalHistory reordered == .ok baseline do
    throw (IO.userError "rational commutativity control unexpectedly changed values")
  unless observedFootprint reordered 1 2 != observedFootprint e.profile 1 2 do
    throw (IO.userError "factor reordering was incorrectly erased from the ordered footprint")
  unless missingFactorValue e.profile 0 0 2 2 == some 0 do
    throw (IO.userError "actual mixed state factor is not padded zero at i=2,t=2")
  unless missingFactorValue e.profile 0 1 2 2 == none do
    throw (IO.userError "actual mixed external factor was not a demanded unavailable read")
  unless missingStepValue e.profile 2 2 == none do
    throw (IO.userError "zero-valued state factors erased an unavailable external demand")
  unless missingStepValue e.profile 3 2 == some 0 do
    throw (IO.userError "all-padded actual factors were confused with unavailable reads")
  -- The unchanged checker admits a plan whose step state capture is retargeted to the history's
  -- own outer slot as an external capture; the profile must refuse it explicitly rather than model
  -- the scan's own output as a free external input.
  let shiftE ← match shiftExample with
    | .ok e => pure e
    | .error message => throw (IO.userError message)
  let dest := (shiftE.raw.states.getD 0 default).destSlot
  let aliased := { shiftE.raw with stepCaptures := shiftE.raw.stepCaptures.map fun c =>
    match c.source with
    | .state _ => { c with source := .external dest }
    | _ => c }
  let sigs := shiftE.prepared.plan.raw.tensorSigs
  unless (checkScanPlan sigs aliased).isOk do
    throw (IO.userError "alias control setup: the checker no longer admits the aliasing plan")
  match certifyProfile sigs aliased 4 3 with
  | .error .unsupported => pure ()
  | .error other => throw (IO.userError s!"alias control: expected unsupported, got {repr other}")
  | .ok _ => throw (IO.userError "alias control: step capture of the history's own slot was admitted")
  IO.println "rational whole-history wrong-table, order/multiplicity, strict-padding and history-slot alias controls passed"

end IndexedExecutionExperiment.AffineScan.CompilerHistoryTest

run_cmd do
  IndexedExecutionExperiment.AffineScan.CompilerHistoryTest.observeAll
  IndexedExecutionExperiment.AffineScan.CompilerHistoryTest.checkNegativeControls

#audit_axioms IndexedExecutionExperiment.AffineScan.CompilerHistoryTest
