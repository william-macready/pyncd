import LeanNCD.Semantics.Source.NativeLegs

namespace LeanNCD.Semantics.Source.Differential

open Debug NativeLegs NumericalProfile

inductive TensorAdapterError
  | unknownDeclaration (binding : Oracle.Tensor)
  | metadata (binding : Oracle.Tensor) (expected : TensorObservation)
  | accumulator (address : AddressObservation) (found : List ℚ)
  deriving Repr

/-- Only original metadata is shared; cell data and packing come from the independent oracle. -/
def oracleTensors (source : AdmittedSource) (result : Oracle.Result) :
    Except TensorAdapterError (List TensorObservation) :=
  result.tensors.mapM fun binding => do
    let t ← match (List.finRange source.source.table.entries.length).find? (fun t =>
        (source.source.table.entry t).declaration == binding.declaration) with
      | none => throw (.unknownDeclaration binding)
      | some t => pure t
    let entry := source.source.table.entry t
    let observed : TensorObservation :=
      ⟨t.val, entry.declaration, some entry.name, entry.role, entry.axes,
        binding.shape, binding.values.map some⟩
    unless binding.name == entry.name && binding.role == entry.role do
      throw (.metadata binding observed)
    pure observed

def definedTensors (tensors : List TensorObservation) : List TensorObservation :=
  tensors.filter (fun binding => binding.role != .input)

private def accumulatorTensors (snapshot : SnapshotObservation) :
    Except TensorAdapterError (List TensorObservation) :=
  (definedTensors snapshot.tensors).mapM fun binding => do
    let values ← (Oracle.coordinates binding.shape).mapM fun coordinate => do
      let address : AddressObservation := ⟨binding.tensorUID, binding.declaration, coordinate⟩
      let found := snapshot.accumulators.filterMap fun (a, v) =>
        if a == address then some v else none
      match found with
      | [value] => pure (some value)
      | _ => throw (.accumulator address found)
    pure { binding with values := values }

inductive ReferenceComparisonError
  | adapter (error : TensorAdapterError)
  | normalization (error : NormalizationError)
  | comparison (error : ComparisonError)
  deriving Repr

structure ReferenceComparison where
  tensors : Except TensorAdapterError (List TensorObservation)
  rows : Except NormalizationError (List OracleRow)
  published : Except ReferenceComparisonError (Comparison TensorDifference)
  collection : Except ReferenceComparisonError (Comparison TensorDifference)
  body : Except ReferenceComparisonError (Comparison ContributionDifference)

def compareReference (run : SourceRun) (oracle : Oracle.Result) : ReferenceComparison :=
  let snapshot := run.observe.endpoint.snapshot
  let tensors := oracleTensors run.source.admitted oracle
  let rows := normalizeOracle run.source.admitted oracle
  let published := do
    let expected ← tensors.mapError ReferenceComparisonError.adapter
    (compareTensors (definedTensors snapshot.tensors) (definedTensors expected)).mapError
      ReferenceComparisonError.comparison
  let collection := do
    let expected ← tensors.mapError ReferenceComparisonError.adapter
    let observed ← (accumulatorTensors snapshot).mapError ReferenceComparisonError.adapter
    (compareTensors observed (definedTensors expected)).mapError ReferenceComparisonError.comparison
  let body := do
    let normalized ← rows.mapError ReferenceComparisonError.normalization
    (compareContributions (canonicalContributions run.observe.events)
      (oracleContributions normalized)).mapError ReferenceComparisonError.comparison
  ⟨tensors, rows, published, collection, body⟩

inductive NativeDifference
  | bindingIssues (issues : List BindingIssue)
  | missing (expected : TensorOrigin)
  | extra (actual : OutputBinding)
  | identity (expected : TensorOrigin) (actual : OutputBinding)
  | shape (expected : TensorOrigin) (actual : OutputBinding) (expectedLength : Nat)
  | length (expected : TensorOrigin) (actual : OutputBinding) (expectedLength : Nat)
  | cell (binding : TensorOrigin) (coordinate : List Nat)
      (expected : CheckedValue) (bits : BitComparison)
  deriving Repr

inductive NativeComparisonError
  | duplicateBinding (tensorUID : UID)
  | expectedCell (binding : TensorOrigin) (coordinate : List Nat) (found : Nat)
  | cellCoverage (binding : TensorOrigin) (coordinates bits : Nat)
  deriving Repr

private def compareNativeCells (profile : EligibleProfile source) (binding : TensorOrigin) :
    List (List Nat) → List UInt64 →
      Except NativeComparisonError (Comparison NativeDifference)
  | [], [] => .ok .agreement
  | coordinate :: coordinates, bits :: rest => do
    let found := profile.values.filter fun value =>
      value.kind == .tensorCell &&
      value.site.origin.declaration == some binding.declaration &&
      value.site.coordinate == coordinate
    let expected ← match found with
      | [value] => pure value
      | _ => throw (.expectedCell binding coordinate found.length)
    let comparison := compareBits expected.integer bits
    if comparison.agrees then compareNativeCells profile binding coordinates rest
    else pure (.disagreement (.cell binding coordinate expected comparison))
  | coordinates, bits => .error (.cellCoverage binding coordinates.length bits.length)

/-- Full desired output structure precedes every bit comparison, including later bindings.
Observed bits remain untouched; zero normalization is confined to compareBits. -/
def compareNative (profile : EligibleProfile source) (observation : NativeObservation) :
    Except NativeComparisonError (Comparison NativeDifference) := do
  let actual ← match observation.outputs with
    | .error issues => return .disagreement (.bindingIssues issues)
    | .ok bindings => pure bindings
  let mut seen : List UID := []
  for binding in actual do
    if binding.metadata.tensorUID ∈ seen then
      throw (.duplicateBinding binding.metadata.tensorUID)
    seen := seen ++ [binding.metadata.tensorUID]
  let desired := outputOrigins source
  let actual := actual.mergeSort fun a b => a.metadata.tensorUID ≤ b.metadata.tensorUID
  let structural ← checkStructure desired actual
  match structural with
  | .agreement => compareValues desired actual
  | other => pure other
where
  checkStructure : List TensorOrigin → List OutputBinding →
      Except NativeComparisonError (Comparison NativeDifference)
    | [], [] => .ok .agreement
    | expected :: _, [] => .ok (.disagreement (.missing expected))
    | [], observed :: _ => .ok (.disagreement (.extra observed))
    | expected :: es, observed :: os => do
      if expected.tensorUID < observed.metadata.tensorUID then
        return .disagreement (.missing expected)
      if observed.metadata.tensorUID < expected.tensorUID then
        return .disagreement (.extra observed)
      if expected != observed.metadata then return .disagreement (.identity expected observed)
      let count := Oracle.cellCount expected.shape
      if expected.shape != observed.shape then
        return .disagreement (.shape expected observed count)
      if count != observed.bits.size then
        return .disagreement (.length expected observed count)
      checkStructure es os
  compareValues : List TensorOrigin → List OutputBinding →
      Except NativeComparisonError (Comparison NativeDifference)
    | [], [] => .ok .agreement
    | expected :: es, observed :: os => do
      let cells ← compareNativeCells profile expected (Oracle.coordinates expected.shape)
        observed.bits.toList
      match cells with
      | .agreement => compareValues es os
      | other => pure other
    | expected :: _, [] => .ok (.disagreement (.missing expected))
    | [], observed :: _ => .ok (.disagreement (.extra observed))

inductive NativeComparisonUnavailable
  | profile (reason : Unsupported)
  | legNotObserved
  | admission (diagnostic : SourceDiagnostic)
  deriving Repr

inductive NativeComparison
  | unavailable (reason : NativeComparisonUnavailable)
  | compared (result : Except NativeComparisonError (Comparison NativeDifference))
  deriving Repr

inductive Classification
  | fourLegParity
  | referenceIncomplete (endpoint : CoreEndpoint)
  | oracleUnavailable (reason : Oracle.Unavailable)
  | referenceDiscrepancy
  | comparisonRefused
  | knownContractDifference (condition : StructuralCondition)
  | unsupportedNumericalProfile (reason : Unsupported)
  | nativeUnavailable
  | nativeFailure
  | nativeDiscrepancy
  deriving Repr

structure ComparisonRun where
  reference : SourceRun
  fixtureDependencyOrder : Option (List Nat)
  oracle : Except Oracle.Unavailable Oracle.Result
  native : Except SourceDiagnostic NativeRun
  profile : Except Unsupported (EligibleProfile reference.source.admitted)
  referenceComparison : Option ReferenceComparison
  legacyComparison : NativeComparison
  checkedComparison : NativeComparison

private def agrees : Except ε (Comparison δ) → Bool
  | .ok .agreement => true
  | _ => false

private def referenceAgrees (comparison : ReferenceComparison) : Bool :=
  agrees comparison.published && agrees comparison.collection && agrees comparison.body

private def nativeAgrees : NativeComparison → Bool
  | .compared result => agrees result
  | _ => false

private def legacyComparison (profile : Except Unsupported (EligibleProfile source))
    (native : Except SourceDiagnostic NativeRun) : NativeComparison :=
  match native with
  | .error diagnostic => .unavailable (.admission diagnostic)
  | .ok native => match native.legacy with
    | .observed observation => match profile with
      | .error reason => .unavailable (.profile reason)
      | .ok profile => .compared (compareNative profile observation)
    | _ => .unavailable .legNotObserved

private def checkedComparison (profile : Except Unsupported (EligibleProfile source))
    (native : Except SourceDiagnostic NativeRun) : NativeComparison :=
  match native with
  | .error diagnostic => .unavailable (.admission diagnostic)
  | .ok native => match native.checked with
    | .observed observation _ => match profile with
      | .error reason => .unavailable (.profile reason)
      | .ok profile => .compared (compareNative profile observation)
    | _ => .unavailable .legNotObserved

def ComparisonRun.classification (run : ComparisonRun) : Classification := Id.run do
  match run.reference.observe.endpoint with
  | .failed .. => return .referenceIncomplete .failed
  | .blocked .. => return .referenceIncomplete .blocked
  | .exhausted .. => return .referenceIncomplete .exhausted
  | .complete _ => pure ()
  match run.oracle with
  | .error reason => return .oracleUnavailable reason
  | .ok _ => pure ()
  match run.referenceComparison with
  | none => return .comparisonRefused
  | some comparison =>
    match comparison.published, comparison.collection, comparison.body with
    | .error _, _, _ | _, .error _, _ | _, _, .error _ => return .comparisonRefused
    | _, _, _ => unless referenceAgrees comparison do return .referenceDiscrepancy
  match run.profile with
  | .error (.structural condition) => return .knownContractDifference condition
  | .error reason => return .unsupportedNumericalProfile reason
  | .ok _ => pure ()
  match run.native with
  | .error _ => return .nativeUnavailable
  | .ok native =>
    match native.legacy, native.checked with
    | .unavailable _, _ | _, .unavailable _ => return .nativeUnavailable
    | .failure _, _ | _, .sourceCompilation _ | _, .preparation _ | _, .runtime _ =>
      return .nativeFailure
    | .observed _, .observed _ _ => pure ()
  if nativeAgrees run.legacyComparison && nativeAgrees run.checkedComparison then
    return .fourLegParity
  match run.legacyComparison, run.checkedComparison with
  | .compared (.error _), _ | _, .compared (.error _) => return .comparisonRefused
  | .unavailable _, _ | _, .unavailable _ => return .nativeUnavailable
  | _, _ => return .nativeDiscrepancy

private def layer : Except ε (Comparison δ) → LayerObservation
  | .ok .agreement => .observedAgreement
  | .ok (.disagreement _) => .observedDisagreement
  | _ => .unobserved .notCompared

def ComparisonRun.localization (run : ComparisonRun) : Localization :=
  match run.reference.observe.endpoint, run.referenceComparison with
  | .complete _, some comparison =>
    { body := layer comparison.body, collection := layer comparison.collection,
      publication := layer comparison.published, readiness := .unobserved .notCompared }
  | _, _ => { readiness := .unobserved .notCompared }

def nativeLocalization : Localization :=
  { body := .unobserved .noBackendInternalHook,
    collection := .unobserved .noBackendInternalHook,
    readiness := .unobserved .noBackendInternalHook,
    publication := .unobserved .noBackendInternalHook,
    backendArithmetic := .unobserved .noBackendInternalHook }

private def renderPreparationCause : LeanNCD.Eval.Plan.PlanCompileCause → String
  | .inputSignature cause => s!"inputSignature: {repr cause}"
  | .capability cause => s!"capability: {repr cause}"
  | .shape cause => s!"shape: {cause}"
  | .scan cause => s!"scan: {repr cause}"
  | .invalidPlan cause => s!"invalidPlan: {repr cause}"
  | .bindings cause => s!"bindings: {repr cause}"
  | .nonlin cause => s!"nonlin: {repr cause}"
  | .sourceInvariant cause => s!"sourceInvariant: {repr cause}"

def renderNativeObservation (observation : NativeObservation) : String :=
  let bindings := observation.report.env.toList.mergeSort (fun a b => a.1 ≤ b.1)
  let raw := bindings.map fun (name, binding) =>
    (name, binding.shape, binding.data.map Float.toBits)
  s!"outputs={repr observation.outputs}\nrawEnvBits={repr raw}\nwarnings={observation.report.warnings.map toString}\nbackendInternals={repr observation.backendInternals}"

def renderLegacy : LegacyOutcome → String
  | .unavailable reason => s!"legacy unavailable: {repr reason}"
  | .failure error =>
    s!"legacy phase={repr error.phase} cause={error.original.error}\nwarnings={error.original.warnings.map toString}\nmappings={repr error.mappings}"
  | .observed observation => s!"legacy observed:\n{renderNativeObservation observation}"

def renderChecked : CheckedOutcome → String
  | .unavailable reason => s!"checked unavailable: {repr reason}"
  | .sourceCompilation error =>
    s!"checked sourceCompilation: cause={repr error.cause}\nwarningAvailability={repr error.warnings}\nmappings={repr error.mappings}"
  | .preparation error =>
    s!"checked preparation: cause={renderPreparationCause error.original.cause}\nwarnings={error.original.warnings.map toString}\nmappings={repr error.mappings}"
  | .runtime error =>
    s!"checked runtime: cause={repr error.original.cause}\nwarnings={error.original.warnings.map toString}\nmappings={repr error.mappings}"
  | .observed observation mappings =>
    s!"checked observed:\n{renderNativeObservation observation}\nmappings={repr mappings}"

def renderComparisonRun (run : ComparisonRun) : String :=
  let reference := renderExecutionObservation run.reference.observe
  let compared := match run.referenceComparison with
    | none => "reference/oracle comparison unavailable (see original oracle reason)"
    | some comparison =>
      s!"published={repr comparison.published}\ncollection={repr comparison.collection}\nbody={repr comparison.body}\noracleTensors={repr comparison.tensors}\nnormalizedOracleRows={repr comparison.rows}"
  let native := match run.native with
    | .error diagnostic => renderSourceDiagnostic diagnostic
    | .ok native =>
      s!"nativeIdentity={repr native.identity}\nsharedStructure={repr native.shared}\n{renderLegacy native.legacy}\n{renderChecked native.checked}"
  let profile := match run.profile with
    | .error reason => s!"profile unsupported: {repr reason}"
    | .ok profile =>
      s!"profile certified bounded integers (not a backend refinement theorem): shared={repr profile.shared}; checkedValues={repr profile.values}"
  let origins := run.reference.source.admitted.statements.map fun statement =>
    (statement.original, statement.output.origin)
  s!"classification={repr run.classification}\nfixtureDependencyOrder={repr run.fixtureDependencyOrder}\noriginalStatements={repr origins}\nreference:\n{reference}\noracle={repr run.oracle}\n{compared}\n{profile}\n{native}\nlegacyComparison={repr run.legacyComparison}\ncheckedComparison={repr run.checkedComparison}\nreference/oracle aggregate localization (NOT native causal localization):\n{renderLocalization run.localization}\nnative internal localization (no backend hook):\n{renderLocalization nativeLocalization}"

end LeanNCD.Semantics.Source.Differential

namespace LeanNCD.Semantics.Source

def compareSource (snapshot : SourceSnapshot) (fixtureDependencyOrder : Option (List Nat))
    (fuel : Option Nat := none) : Except Debug.ExecutionError Differential.ComparisonRun := do
  let reference ← Debug.sourceDebug snapshot fuel
  let oracle := Oracle.run reference.source.admitted fixtureDependencyOrder
  let native := NativeLegs.runNative snapshot
  let profile := NumericalProfile.checkRunProfile reference oracle
  let comparison := match oracle with
    | .error _ => none
    | .ok result => some (Differential.compareReference reference result)
  pure ⟨reference, fixtureDependencyOrder, oracle, native, profile, comparison,
    Differential.legacyComparison profile native, Differential.checkedComparison profile native⟩

def renderSourceComparison (result : Except Debug.ExecutionError Differential.ComparisonRun) :
    String :=
  match result with
  | .error error => Debug.renderExecutionError error
  | .ok run => Differential.renderComparisonRun run

end LeanNCD.Semantics.Source
