import LeanNCD.Semantics.Source.Observation

namespace LeanNCD.Semantics.Source.Debug

inductive Comparison (δ : Type)
  | agreement
  | disagreement (difference : δ)
  | unobserved (reason : UnobservedReason)
  deriving DecidableEq, Repr

inductive LayerObservation
  | observedAgreement | observedDisagreement
  | unobserved (reason : UnobservedReason)
  deriving DecidableEq, Repr

structure Localization where
  body : LayerObservation := .unobserved .notCompared
  collection : LayerObservation := .unobserved .notCompared
  readiness : LayerObservation := .unobserved .noBackendInternalHook
  publication : LayerObservation := .unobserved .notCompared
  backendArithmetic : LayerObservation := .unobserved .noBackendInternalHook
  deriving DecidableEq, Repr

inductive ComparisonSide
  | left | right
  deriving DecidableEq, Repr

inductive ComparisonCause
  | duplicateTensor (tensorUID : UID)
  | shapeMetadata (tensor : TensorObservation)
  | bufferLength (tensor : TensorObservation) (expected actual : Nat)
  | duplicateOccurrence (key : OccurrenceKey)
  | coordinateLength (tensorUID : UID) (coordinates values : Nat)
  deriving DecidableEq, Repr

structure ComparisonError where
  side : ComparisonSide
  cause : ComparisonCause
  deriving DecidableEq, Repr

inductive TensorDifference
  | missing (tensor : TensorObservation)
  | extra (tensor : TensorObservation)
  | identity (left right : TensorObservation)
  | shape (left right : TensorObservation)
  | length (left right : TensorObservation)
  | cell (address : AddressObservation) (left right : Option ℚ)
  deriving DecidableEq, Repr

inductive ContributionDifference
  | missing (row : ContributionObservation)
  | extra (row : ContributionObservation)
  | value (left right : ContributionObservation)
  deriving DecidableEq, Repr

def outputObservations (tensors : List TensorObservation) : List TensorObservation :=
  tensors.filter (fun t => t.role == .output)

private def checkTensorUIDs (side : ComparisonSide) (tensors : List TensorObservation) :
    Except ComparisonError Unit := do
  let mut seen : List UID := []
  for tensor in tensors do
    if tensor.tensorUID ∈ seen then throw ⟨side, .duplicateTensor tensor.tensorUID⟩
    seen := seen ++ [tensor.tensorUID]

private def checkBuffer (side : ComparisonSide) (tensor : TensorObservation) :
    Except ComparisonError Unit := do
  unless tensor.axes.map Axis.extent == tensor.shape do
    throw ⟨side, .shapeMetadata tensor⟩
  unless tensor.values.length == Oracle.cellCount tensor.shape do
    throw ⟨side, .bufferLength tensor (Oracle.cellCount tensor.shape) tensor.values.length⟩

private def compareCells (tensor : TensorObservation) :
    List (List Nat) → List (Option ℚ) → List (Option ℚ) →
      Except ComparisonError (Comparison TensorDifference)
  | [], [], [] => .ok .agreement
  | coordinate :: coordinates, l :: ls, r :: rs =>
    if l == r then compareCells tensor coordinates ls rs
    else .ok (.disagreement (.cell
      ⟨tensor.tensorUID, tensor.declaration, coordinate⟩ l r))
  | coordinates, ls, rs =>
    .error ⟨if ls.length != coordinates.length then .left else .right,
      .coordinateLength tensor.tensorUID coordinates.length
        (if ls.length != coordinates.length then ls.length else rs.length)⟩

/-- Inputs are not result bindings. Callers select outputs or all defined cells explicitly.
Shape and buffer checks precede any cell comparison; no prefix zip is used. -/
def compareTensors (left right : List TensorObservation) :
    Except ComparisonError (Comparison TensorDifference) := do
  checkTensorUIDs .left left
  checkTensorUIDs .right right
  let left := left.mergeSort fun a b => a.tensorUID ≤ b.tensorUID
  let right := right.mergeSort fun a b => a.tensorUID ≤ b.tensorUID
  let structural ← checkStructure left right
  match structural with
  | .agreement => compareValues left right
  | other => pure other
where
  checkStructure : List TensorObservation → List TensorObservation →
      Except ComparisonError (Comparison TensorDifference)
    | [], [] => .ok .agreement
    | l :: _, [] => .ok (.disagreement (.missing l))
    | [], r :: _ => .ok (.disagreement (.extra r))
    | l :: ls, r :: rs => do
      if l.tensorUID < r.tensorUID then return .disagreement (.missing l)
      if r.tensorUID < l.tensorUID then return .disagreement (.extra r)
      if l.shape != r.shape then return .disagreement (.shape l r)
      if l.values.length != r.values.length then return .disagreement (.length l r)
      checkBuffer .left l
      checkBuffer .right r
      if l.declaration != r.declaration || l.axes != r.axes || l.role != r.role then
        return .disagreement (.identity l r)
      checkStructure ls rs
  compareValues : List TensorObservation → List TensorObservation →
      Except ComparisonError (Comparison TensorDifference)
    | [], [] => .ok .agreement
    | l :: _, [] => .ok (.disagreement (.missing l))
    | [], r :: _ => .ok (.disagreement (.extra r))
    | l :: ls, r :: rs => do
      let cells ← compareCells l (Oracle.coordinates l.shape) l.values r.values
      match cells with
      | .agreement => compareValues ls rs
      | other => pure other

private def checkOccurrenceKeys (side : ComparisonSide) (rows : List ContributionObservation) :
    Except ComparisonError Unit := do
  let mut seen : List OccurrenceKey := []
  for row in rows do
    if row.key ∈ seen then throw ⟨side, .duplicateOccurrence row.key⟩
    seen := seen ++ [row.key]

def compareContributions (left right : List ContributionObservation) :
    Except ComparisonError (Comparison ContributionDifference) := do
  checkOccurrenceKeys .left left
  checkOccurrenceKeys .right right
  go (canonicalizeContributions left) (canonicalizeContributions right)
where
  go : List ContributionObservation → List ContributionObservation →
      Except ComparisonError (Comparison ContributionDifference)
    | [], [] => .ok .agreement
    | l :: _, [] => .ok (.disagreement (.missing l))
    | [], r :: _ => .ok (.disagreement (.extra r))
    | l :: ls, r :: rs =>
      if l.key == r.key then
        if l.destination == r.destination && l.value == r.value then go ls rs
        else .ok (.disagreement (.value l r))
      else if occurrenceKeyLE l.key r.key then .ok (.disagreement (.missing l))
      else .ok (.disagreement (.extra r))

def oracleContributions (rows : List OracleRow) : List ContributionObservation :=
  canonicalizeContributions (rows.filterMap (·.occurrence))

def renderExecutionError : ExecutionError → String
  | .admission d => s!"admission: stage={repr d.stage} origin={repr d.origin} cause={repr d.cause}"
  | .inputPresence uid origin expected actual =>
    s!"input presence: tensorUID={uid} origin={repr origin} expected={expected} actual={actual}"

def renderExecutionObservation (observation : ExecutionObservation) : String :=
  let kind := match observation.endpoint with
    | .complete _ => "complete (actual reached execution retained in SourceRun)"
    | .failed _ _ => "failed (actual endpoint; ready undefinedness, not missing reads)"
    | .blocked _ => "blocked (no no-model inference)"
    | .exhausted _ _ _ => "exhausted (no no-model inference)"
  s!"{kind}\nendpoint={repr observation.endpoint}\nevents={repr observation.events}"

def renderLocalization (localization : Localization) : String :=
  s!"body={repr localization.body}\ncollection={repr localization.collection}\nreadiness={repr localization.readiness}\npublication={repr localization.publication}\nbackendArithmetic={repr localization.backendArithmetic}"

end LeanNCD.Semantics.Source.Debug

namespace LeanNCD.Semantics.Source

def renderSourceDiagnostic (diagnostic : SourceDiagnostic) : String :=
  Debug.renderExecutionError (.admission diagnostic)

def renderSourceDebug (result : Except Debug.ExecutionError Debug.SourceRun) : String :=
  match result with
  | .error error => Debug.renderExecutionError error
  | .ok run => Debug.renderExecutionObservation run.observe

end LeanNCD.Semantics.Source
