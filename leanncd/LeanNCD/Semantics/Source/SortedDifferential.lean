import LeanNCD.Semantics.Source.Differential

/-! S2b P2 (prototype): the differential for a selected carrier.

Pipeline: `admitSourceSorted` (single-sort selection) -> `Oracle.runWith S.carrier` -> Core leg
`runSourceAt S.carrier` at `Registry.none` -> both observed into `Oracle.ExtVal` -> published
comparison -> tropical numerical profile (finite integers in the envelope, `±inf` an explicit
non-finite class) -> native bit comparison. The real path (`compareSource`) is untouched. -/

namespace LeanNCD.Semantics.Source.SortedDifferential

open Debug NativeLegs NumericalProfile Oracle

private def definedOnly {V : Type} (ts : List (TensorObservation V)) : List (TensorObservation V) :=
  ts.filter (·.role != .input)

/-- Oracle tensors of a carrier run, observed into `ExtVal` (metadata from the admitted table). -/
def oracleTensorsAt {K : Type} (obs : K → ExtVal) (source : AdmittedSource)
    (result : Oracle.Result K) : Except String (List (TensorObservation ExtVal)) :=
  result.tensors.mapM fun binding =>
    match (List.finRange source.source.table.entries.length).find? (fun t =>
        (source.source.table.entry t).declaration == binding.declaration) with
    | none => .error s!"unknown declaration {binding.declaration}"
    | some t =>
      let entry := source.source.table.entry t
      .ok ⟨t.val, entry.declaration, some entry.name, entry.role, entry.axes, binding.shape,
        binding.values.map (some ∘ obs)⟩

/-- The Core leg at the selected carrier: no primitive registry, inputs through `ofRat`. -/
def coreTensorsAt (S : Sorted) (source : AdmittedSource) :
    Except String (List (TensorObservation ExtVal)) :=
  match runSourceAt S.carrier source (Registry.none S.K) with
  | .error t => .error s!"input presence {t.val}"
  | .ok result => match result.result.outcome with
    | .complete c _ => .ok (observeTensorsAt source (Registry.none S.K) S.carrier.observe c)
    | _ => .error "core leg incomplete"

/-! ### Tropical numerical profile (Q7)

A tropical value is a sum of input integers (`⊗` is `+`) selected by `max`/`min` (`⊕`): selection
adds no magnitude, so the only envelope is per occurrence, `Σ |read|` over its finite reads, plus
every finite input and output cell in `[-limit, limit]`. `±inf` is not an envelope violation: it is
its own class with the IEEE bits `0xFFF0…` / `0x7FF0…`. -/

inductive ExtClass
  | finite (checked : CheckedValue)
  | negInf
  | posInf
  deriving Repr

def ExtClass.bits : ExtClass → UInt64
  | .finite c => c.bits
  | .negInf => 0xFFF0000000000000
  | .posInf => 0x7FF0000000000000

def checkExt (site : Site) (kind : ValueKind) : ExtVal → Except Unsupported ExtClass
  | .fin q => .finite <$> checkValue site kind q
  | .negInf => .ok .negInf
  | .posInf => .ok .posInf

/-- The profile's output cells: `(declaration, coordinate, class)`. -/
structure SortedCell where
  declaration : Nat
  coordinate : List Nat
  expected : ExtClass
  deriving Repr

def checkSortedProfile {K : Type} (obs : K → ExtVal) (source : AdmittedSource)
    (result : Oracle.Result K) : Except Unsupported (List SortedCell) := do
  let _ ← checkStructure source
  -- every occurrence: its finite reads' absolute sum is the tropical analogue of the product bound
  for row in result.contributions do
    for fiber in row.terms do
      for o in fiber.occurrences do
        let site : Site := ⟨fiber.origin, row.coordinate, o.assignment, [], none⟩
        let mut bound : ℚ := 0
        for read in o.reads do
          match obs read.value with
          | .fin q =>
            let _ ← checkValue { site with origin := read.origin } .read q
            bound := bound + |q|
            let _ ← checkValue site .subsetProductBound bound
          | _ => pure ()
  let mut cells := []
  for out in result.tensors do
    if out.role != .input then
      for (coordinate, value) in (Oracle.coordinates out.shape).zip out.values do
        let origin : SourceOrigin := { side := .output, declaration := some out.declaration }
        let site : Site := { origin := origin, coordinate := coordinate }
        let expected ← checkExt site .tensorCell (obs value)
        cells := cells ++ [(⟨out.declaration, coordinate, expected⟩ : SortedCell)]
  pure cells

/-! ### Native comparison and classification (Q8) -/

structure CellMismatch where
  declaration : Nat
  coordinate : List Nat
  expected : UInt64
  observed : UInt64
  deriving Repr

def compareBindings (cells : List SortedCell) (bindings : List OutputBinding) :
    Except String (Option CellMismatch) := do
  for b in bindings do
    let mine := cells.filter (·.declaration == b.metadata.declaration)
    unless mine.length == b.bits.size do
      throw s!"cell coverage {b.metadata.declaration}: {mine.length} vs {b.bits.size}"
    for (cell, bits) in mine.zip b.bits.toList do
      unless normalizeZeroBits cell.expected.bits == normalizeZeroBits bits do
        return some ⟨cell.declaration, cell.coordinate, cell.expected.bits, bits⟩
  return none

inductive LegResult
  | agrees
  | mismatch (cell : CellMismatch)
  | failure (message : String)
  | unavailable
  deriving Repr

inductive SortedClassification
  | fourLegParity
  | referenceUnavailable (reason : String)
  | referenceDiscrepancy
  | unsupportedNumericalProfile (reason : Unsupported)
  | nativeUnavailable
  | nativeFailure (legacy checked : LegResult)
  | nativeDiscrepancy (legacy checked : LegResult)
  deriving Repr

structure SortedRun where
  carrier : String
  core : Except String (List (TensorObservation ExtVal))
  oracle : Except String (List (TensorObservation ExtVal))
  published : Except String (Comparison (TensorDifference ExtVal))
  profile : Except Unsupported (List SortedCell)
  legacy : LegResult
  checked : LegResult
  classification : SortedClassification
  deriving Repr

private def legOf (cells : Except Unsupported (List SortedCell)) :
    Option NativeObservation → String → LegResult
  | none, "" => .unavailable
  | none, message => .failure message
  | some observation, _ =>
    match cells, observation.outputs with
    | .error _, _ => .unavailable
    | _, .error issues => .failure s!"binding issues {repr issues}"
    | .ok cells, .ok bindings =>
      match compareBindings cells bindings with
      | .error message => .failure message
      | .ok none => .agrees
      | .ok (some cell) => .mismatch cell

/-- The tropical/real single-sort differential. `table` is the carrier selection table. -/
def compareSortedSource (snapshot : SourceSnapshot) (order : Option (List Nat))
    (table : List Sorted := standardCarriers) : Except SourceDiagnostic SortedRun :=
  match admitSourceSorted snapshot table with
  | .error e => .error e
  | .ok (source, S) =>
    let oracleRun := Oracle.runWith S.carrier source order
    let oracle := match oracleRun with
      | .error u => .error s!"oracle unavailable {repr u}"
      | .ok r => oracleTensorsAt S.carrier.observe source r
    let core := coreTensorsAt S source
    let published := match core, oracle with
      | .ok c, .ok o => (compareTensors (definedOnly c) (definedOnly o)).mapError (s!"{repr ·}")
      | .error e, _ | _, .error e => .error e
    let profile := match oracleRun with
      | .error u => .error (.oracleUnavailable u)
      | .ok r => checkSortedProfile S.carrier.observe source r
    let native := runNative snapshot (sorted := true)
    let (legacy, checked) := match native with
      | .error _ => (LegResult.unavailable, LegResult.unavailable)
      | .ok n =>
        (match n.legacy with
          | .observed o => legOf profile (some o) ""
          | .failure e => legOf profile none s!"legacy {e.original.error}"
          | .unavailable _ => .unavailable,
         match n.checked with
          | .observed o _ => legOf profile (some o) ""
          | .sourceCompilation e => legOf profile none s!"checked compile {repr e.cause}"
          | .preparation _ => legOf profile none "checked preparation"
          | .runtime e => legOf profile none s!"checked runtime {repr e.original.cause}"
          | .unavailable _ => .unavailable)
    let classification : SortedClassification :=
      match published with
      | .error e => .referenceUnavailable e
      | .ok (.disagreement _) | .ok (.unobserved _) => .referenceDiscrepancy
      | .ok .agreement =>
        match profile with
        | .error reason => .unsupportedNumericalProfile reason
        | .ok _ =>
          match legacy, checked with
          | .agrees, .agrees => .fourLegParity
          | .unavailable, _ | _, .unavailable => .nativeUnavailable
          | .failure _, _ | _, .failure _ => .nativeFailure legacy checked
          | _, _ => .nativeDiscrepancy legacy checked
    .ok ⟨S.name, core, oracle, published, profile, legacy, checked, classification⟩

end LeanNCD.Semantics.Source.SortedDifferential
