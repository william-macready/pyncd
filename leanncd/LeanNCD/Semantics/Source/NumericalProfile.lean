import LeanNCD.Semantics.Source.Diagnostics

namespace LeanNCD.Semantics.Source.NumericalProfile

def limit : Nat := 2 ^ 20

inductive ValueKind
  | input | read | partialProduct | product | partialFiber | fiber
  | partialStatement | statement | partialCollection | collection | tensorCell
  | subsetProductBound | fiberAbsoluteBound | statementAbsoluteBound | collectionAbsoluteBound
  | coreContribution | corePublication | coreAccumulator
  deriving DecidableEq, Repr

structure Site where
  origin : SourceOrigin := {}
  coordinate : List Nat := []
  assignment : List (UID × Nat) := []
  slots : List (SourceOrigin × UID) := []
  cell : Option Nat := none
  deriving DecidableEq, Repr

inductive StructuralCondition
  | usedDType (origin : SourceOrigin) (name : String) (actual : TensorElementType)
  | crossStatementOverwrite (declaration : Nat) (definitions : List SourceOrigin)
  deriving DecidableEq, Repr

inductive ReceiptCondition
  | tensorDeclarations (expected actual : List Nat)
  | tensorMetadata (declaration : Nat)
  | rows (expected actual : List (SourceOrigin × List Nat))
  | terms (expected actual : List SourceOrigin)
  | occurrences (expected actual : Nat)
  | assignment | duplicateAssignment | outputCoordinate
  | reads (expected actual : List SourceOrigin)
  | readDeclaration (expected actual : Nat)
  | readCoordinate (expected actual : List Nat)
  | value (expected actual : ℚ)
  | normalization (error : Debug.NormalizationError)
  | lookup (error : Oracle.Unavailable)
  deriving DecidableEq, Repr

inductive CoreEndpoint
  | failed | blocked | exhausted | undefinedEvent
  deriving DecidableEq, Repr

inductive Unsupported
  | structural (condition : StructuralCondition)
  | nonIntegral (site : Site) (kind : ValueKind) (numerator : Int) (denominator : Nat)
  | outsideEnvelope (site : Site) (kind : ValueKind) (value : ℚ) (maximum : Nat)
  | oracleUnavailable (reason : Oracle.Unavailable)
  | receipt (site : Site) (condition : ReceiptCondition)
  | coreNotComplete (endpoint : CoreEndpoint)
  deriving DecidableEq, Repr

structure BoundedInteger where
  value : Int
  bounded : value.natAbs ≤ limit
  deriving Repr

/-- Integer-only binary64 encoding. The profile bound leaves at most 21 significant bits. -/
def expectedBits (integer : BoundedInteger) : UInt64 :=
  let magnitude := integer.value.natAbs
  if magnitude == 0 then 0 else
    let exponent := magnitude.log2
    let sign : UInt64 := if integer.value < 0 then 0x8000000000000000 else 0
    let biased := UInt64.ofNat (exponent + 1023)
    let fraction := UInt64.ofNat (magnitude - 2 ^ exponent)
    sign ||| (biased <<< 52) ||| (fraction <<< UInt64.ofNat (52 - exponent))

def normalizeZeroBits (bits : UInt64) : UInt64 :=
  if bits &&& 0x7fffffffffffffff == 0 then 0 else bits

structure BitComparison where
  expectedOriginalBits : UInt64
  expectedNormalizedBits : UInt64
  observedOriginalBits : UInt64
  observedNormalizedBits : UInt64
  deriving DecidableEq, Repr

def BitComparison.agrees (comparison : BitComparison) : Bool :=
  comparison.expectedNormalizedBits == comparison.observedNormalizedBits

def compareBits (integer : BoundedInteger) (observedBits : UInt64) : BitComparison :=
  let expected := expectedBits integer
  ⟨expected, normalizeZeroBits expected, observedBits, normalizeZeroBits observedBits⟩

def compareFloat (integer : BoundedInteger) (observed : Float) : BitComparison :=
  compareBits integer observed.toBits

structure CheckedValue where
  site : Site
  kind : ValueKind
  exact : ℚ
  integer : BoundedInteger
  bits : UInt64
  deriving Repr

def checkValue (site : Site) (kind : ValueKind) (value : ℚ) :
    Except Unsupported CheckedValue := do
  unless value.den == 1 do
    throw (.nonIntegral site kind value.num value.den)
  if h : value.num.natAbs ≤ limit then
    let integer : BoundedInteger := ⟨value.num, h⟩
    pure ⟨site, kind, value, integer, expectedBits integer⟩
  else
    throw (.outsideEnvelope site kind value limit)

structure SharedFragment where
  usedDeclarations : List Nat
  definitions : List (Nat × SourceOrigin)
  deriving DecidableEq, Repr

/-- Admission already pins domains and excludes contexts/scans and non-sum/identity forms.
Only cross-statement definitions and used tensor dtypes are extra structural restrictions. -/
def checkStructure (source : AdmittedSource) : Except Unsupported SharedFragment := do
  let mut used : List Nat := []
  let mut definitions : List (Nat × SourceOrigin) := []
  for statement in source.statements do
    let output := source.source.table.entry statement.output.tensor
    let previous := definitions.filter (fun p => p.1 == output.declaration)
    unless previous.isEmpty do
      throw (.structural (.crossStatementOverwrite output.declaration
        (previous.map Prod.snd ++ [statement.output.origin])))
    definitions := definitions ++ [(output.declaration, statement.output.origin)]
    unless output.elementType == .f64 do
      throw (.structural (.usedDType statement.output.origin output.name output.elementType))
    used := used ++ [output.declaration]
    for term in statement.terms do
      for read in term.sourceReads do
        let entry := source.source.table.entry read.read.tensor
        unless entry.elementType == .f64 do
          throw (.structural (.usedDType read.origin entry.name entry.elementType))
        used := used ++ [entry.declaration]
  pure ⟨used.reverse.dedup.reverse, definitions⟩

private def sameValue (site : Site) (expected actual : ℚ) : Except Unsupported Unit := do
  unless expected == actual do throw (.receipt site (.value expected actual))

private def tensorAt (result : Oracle.Result) (site : Site) (declaration : Nat) :
    Except Unsupported Oracle.Tensor :=
  match result.tensors.find? (fun t => t.declaration == declaration) with
  | some tensor => .ok tensor
  | none => .error (.receipt site (.lookup ⟨site.origin, .missingTensor declaration⟩))

private def coordinateAt (site : Site) (assignment : List (UID × Nat))
    (indices : List UID) : Except Unsupported (List Nat) :=
  indices.zipIdx.mapM fun (uid, slot) =>
    match assignment.find? (fun p => p.1 == uid) with
    | some pair => .ok pair.2
    | none => .error (.receipt { site with origin := { site.origin with slot := some slot } }
        (.lookup ⟨{ site.origin with slot := some slot }, .missingUID uid⟩))

private def checkOccurrence (source : AdmittedSource) (result : Oracle.Result)
    (term : Term source.source.context out source.source.table.declarations)
    (coordinate : List Nat) (occurrence : Oracle.Occurrence) :
    Except Unsupported (List CheckedValue) := do
  let site : Site := ⟨term.origin, coordinate, occurrence.assignment, [], none⟩
  unless occurrence.output == coordinate do throw (.receipt site .outputCoordinate)
  unless occurrence.reads.map (·.origin) == term.sourceReads.map (·.origin) do
    throw (.receipt site (.reads (term.sourceReads.map (·.origin))
      (occurrence.reads.map (·.origin))))
  let mut values := []
  let mut product : ℚ := 1
  let mut envelope : ℚ := 1
  for (read, actual) in term.sourceReads.zip occurrence.reads do
    let entry := source.source.table.entry read.read.tensor
    let here : Site := { site with
      origin := read.origin
      coordinate := actual.coordinate
      slots := read.indices.zipIdx.map fun (uid, slot) =>
        ({ read.origin with slot := some slot }, uid) }
    unless actual.declaration == entry.declaration do
      throw (.receipt here (.readDeclaration entry.declaration actual.declaration))
    let expectedCoordinate ← coordinateAt here occurrence.assignment read.indices
    unless actual.coordinate == expectedCoordinate do
      throw (.receipt here (.readCoordinate expectedCoordinate actual.coordinate))
    let tensor ← tensorAt result here entry.declaration
    let expected ← (Oracle.lookup read.origin (entry.axes.map (·.extent)) tensor
      actual.coordinate).mapError (fun error => .receipt here (.lookup error))
    sameValue here expected actual.value
    values := values ++ [← checkValue here .read actual.value]
    product := product * actual.value
    values := values ++ [← checkValue here .partialProduct product]
    -- A later zero cannot hide a large subset product in an opaque multiplier order.
    envelope := envelope * max 1 |actual.value|
    values := values ++ [← checkValue here .subsetProductBound envelope]
  sameValue site product occurrence.value
  values := values ++ [← checkValue site .product occurrence.value,
    ← checkValue site .subsetProductBound envelope]
  pure values

private def checkFiber (source : AdmittedSource) (result : Oracle.Result)
    (statement : AdmittedStatement source.source)
    (term : Term source.source.context statement.output.context source.source.table.declarations)
    (row : Debug.OracleRow) (fiber : Oracle.TermFiber) :
    Except Unsupported (List CheckedValue × ℚ) := do
  let site : Site := { origin := term.origin, coordinate := row.fullCell.coordinate }
  let axes := source.source.context.axes.filter
    (fun a => a.uid ∈ statement.output.indices ++ term.sourceReads.flatMap (·.indices))
  let expectedCount := if row.occurrence.isSome then
    Oracle.cellCount (term.partition.bound.map (·.extent)) else 0
  unless fiber.occurrences.length == expectedCount do
    throw (.receipt site (.occurrences expectedCount fiber.occurrences.length))
  let mut seen : List (List (UID × Nat)) := []
  let mut total : ℚ := 0
  let mut absoluteSum : ℚ := 0
  let mut values := []
  for occurrence in fiber.occurrences do
    let here := { site with assignment := occurrence.assignment }
    unless occurrence.origin == term.origin &&
        occurrence.assignment.map Prod.fst == axes.map Axis.uid do
      throw (.receipt here .assignment)
    if occurrence.assignment ∈ seen then throw (.receipt here .duplicateAssignment)
    seen := seen ++ [occurrence.assignment]
    for (axis, pair) in axes.zip occurrence.assignment do
      unless pair.2 < axis.extent do throw (.receipt here .assignment)
    let expectedOutput ← coordinateAt here occurrence.assignment statement.output.indices
    unless expectedOutput == row.fullCell.coordinate do throw (.receipt here .outputCoordinate)
    values := values ++ (← checkOccurrence source result term row.fullCell.coordinate occurrence)
    total := total + occurrence.value
    absoluteSum := absoluteSum + |occurrence.value|
    values := values ++ [← checkValue here .partialFiber total,
      ← checkValue here .fiberAbsoluteBound absoluteSum]
  sameValue site total fiber.value
  values := values ++ [← checkValue site .fiber fiber.value,
    ← checkValue site .fiberAbsoluteBound absoluteSum]
  pure (values, absoluteSum)

private def checkRow (source : AdmittedSource) (result : Oracle.Result)
    (statement : AdmittedStatement source.source) (row : Debug.OracleRow) :
    Except Unsupported (List CheckedValue × ℚ) := do
  let site : Site := { origin := row.fullCell.origin, coordinate := row.fullCell.coordinate }
  unless row.fullCell.terms.map (·.origin) == statement.terms.map (·.origin) do
    throw (.receipt site (.terms (statement.terms.map (·.origin))
      (row.fullCell.terms.map (·.origin))))
  let mut values := []
  let mut total : ℚ := 0
  let mut absoluteSum : ℚ := 0
  for (term, fiber) in statement.terms.zip row.fullCell.terms do
    let checked ← checkFiber source result statement term row fiber
    values := values ++ checked.1
    total := total + fiber.value
    absoluteSum := absoluteSum + checked.2
    values := values ++ [← checkValue { site with origin := term.origin } .partialStatement total,
      ← checkValue { site with origin := term.origin } .statementAbsoluteBound absoluteSum]
  sameValue site total row.fullCell.value
  values := values ++ [← checkValue site .statement row.fullCell.value,
    ← checkValue site .statementAbsoluteBound absoluteSum]
  pure (values, absoluteSum)

private def checkInputs (source : AdmittedSource) : Except Unsupported (List CheckedValue) := do
  let mut values := []
  for t in List.finRange source.source.table.entries.length do
    let entry := source.source.table.entry t
    if h : entry.role = .input then
      for (value, cell) in (source.source.inputs.buffers t h).values.zipIdx do
        values := values ++ [← checkValue
          { origin := { side := .input, declaration := some entry.declaration }, cell := some cell }
          .input value]
  pure values

private def checkOracle (source : AdmittedSource) (result : Oracle.Result) :
    Except Unsupported (List Debug.OracleRow × List CheckedValue) := do
  let expectedDeclarations := source.source.table.entries.map (·.declaration)
  unless result.tensors.map (·.declaration) == expectedDeclarations do
    throw (.receipt {} (.tensorDeclarations expectedDeclarations
      (result.tensors.map (·.declaration))))
  let rows ← (Debug.normalizeOracle source result).mapError
    (fun error => .receipt { origin := error.origin } (.normalization error))
  let expectedRows := source.statements.flatMap fun statement =>
    (Oracle.coordinates ((source.source.table.entry statement.output.tensor).axes.map
      (·.extent))).map fun coordinate => (statement.output.origin, coordinate)
  let actualRows := rows.map fun row => (row.fullCell.origin, row.fullCell.coordinate)
  unless actualRows == expectedRows do throw (.receipt {} (.rows expectedRows actualRows))
  let mut checkedRows : List (Debug.OracleRow × ℚ) := []
  let mut values := []
  for statement in source.statements do
    for row in rows.filter (fun r => r.fullCell.origin.statement == some statement.original) do
      let checked ← checkRow source result statement row
      values := values ++ checked.1
      checkedRows := checkedRows ++ [(row, checked.2)]
  for t in List.finRange source.source.table.entries.length do
    let entry := source.source.table.entry t
    let site : Site := { origin := { side := .declaration, declaration := some entry.declaration } }
    let tensor ← tensorAt result site entry.declaration
    unless tensor.name == entry.name && tensor.role == entry.role &&
        tensor.shape == entry.axes.map (·.extent) &&
        tensor.values.length == Oracle.cellCount tensor.shape do
      throw (.receipt site (.tensorMetadata entry.declaration))
    for (coordinate, value) in (Oracle.coordinates tensor.shape).zip tensor.values do
      let here := { site with coordinate := coordinate }
      if h : entry.role = .input then
        let input : Oracle.Tensor := ⟨entry.declaration, entry.name, entry.role, tensor.shape,
          (source.source.inputs.buffers t h).values⟩
        let expected ← (Oracle.lookup site.origin tensor.shape input coordinate).mapError
          (fun error => .receipt here (.lookup error))
        sameValue here expected value
      else
        let mut total : ℚ := 0
        let mut absoluteSum : ℚ := 0
        for (row, bound) in checkedRows do
          if row.fullCell.origin.declaration == some entry.declaration &&
              row.fullCell.coordinate == coordinate then
            total := total + row.fullCell.value
            absoluteSum := absoluteSum + bound
            values := values ++ [← checkValue { here with origin := row.fullCell.origin }
              .partialCollection total,
              ← checkValue here .collectionAbsoluteBound absoluteSum]
        sameValue here total value
        values := values ++ [← checkValue here .collection value,
          ← checkValue here .collectionAbsoluteBound absoluteSum]
      values := values ++ [← checkValue here .tensorCell value]
  pure (rows, values)

private def checkActual (source : AdmittedSource) (actual : ActualValidatedResult source) :
    Except Unsupported (List CheckedValue) := do
  let mut values := []
  for event in actual.result.events do
    match Debug.observeEvent source event with
    | .contribution occurrence value =>
      values := values ++ [← checkValue
        { origin := occurrence.origin, coordinate := occurrence.destination.coordinate,
          assignment := occurrence.key.assignments } .coreContribution value]
    | .publication address value =>
      values := values ++ [← checkValue
        { origin := { side := .output, declaration := some address.declaration },
          coordinate := address.coordinate } .corePublication value]
    | .undefined _ => throw (.coreNotComplete .undefinedEvent)
  match actual.result.outcome with
  | .complete running _ =>
    for (address, value) in (Debug.observeSnapshot source running []).accumulators do
      values := values ++ [← checkValue
        { origin := { side := .output, declaration := some address.declaration },
          coordinate := address.coordinate } .coreAccumulator value]
    pure values
  | .failed .. => throw (.coreNotComplete .failed)
  | .blocked .. => throw (.coreNotComplete .blocked)
  | .exhausted .. => throw (.coreNotComplete .exhausted)

structure EligibleProfile (source : AdmittedSource) where
  shared : SharedFragment
  oracle : Oracle.Result
  rows : List Debug.OracleRow
  values : List CheckedValue
  actual : Option (ActualValidatedResult source)

/-- A checked runtime profile, not numerical agreement or a native-Float semiring theorem.
Pass the actual independent Oracle.run receipt, including its unavailable branch. -/
def checkProfile (source : AdmittedSource) (oracle : Except Oracle.Unavailable Oracle.Result)
    (actual : Option (ActualValidatedResult source) := none) :
    Except Unsupported (EligibleProfile source) := do
  let shared ← checkStructure source
  let inputs ← checkInputs source
  let result ← oracle.mapError Unsupported.oracleUnavailable
  let checked ← checkOracle source result
  let observed ← match actual with
    | none => pure []
    | some run => checkActual source run
  pure ⟨shared, result, checked.1, inputs ++ checked.2 ++ observed, actual⟩

def checkRunProfile (run : Debug.SourceRun) (oracle : Except Oracle.Unavailable Oracle.Result) :
    Except Unsupported (EligibleProfile run.source.admitted) :=
  checkProfile run.source.admitted oracle (some run.actual)

end LeanNCD.Semantics.Source.NumericalProfile
