import Semantics.SourceDifferentialFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures

namespace SourceDifferentialCorpusTest

set_option synthInstance.maxSize 512
set_option maxRecDepth 4096
set_option maxHeartbeats 0

inductive Configuration
  | scalar (factors : Nat)
  | tensor (rank extent factors : Nat)
  deriving DecidableEq, Repr

def configurations : List Configuration :=
  [1, 2].map Configuration.scalar ++
    [1, 2].flatMap fun rank =>
      [0, 1, 2, 3].flatMap fun extent =>
        [1, 2].map (Configuration.tensor rank extent)

private def configurationLabel : Configuration → String
  | .scalar factors => s!"scalar-f{factors}"
  | .tensor rank extent factors => s!"rank{rank}-extent{extent}-f{factors}"

private def factorCount : Configuration → Nat
  | .scalar factors | .tensor _ _ factors => factors

private def fixtureAxes : Configuration → List AxisSpec
  | .scalar _ => []
  | .tensor rank _ _ => [i, SourceDifferentialFixtures.j].take rank

private def fixtureShape : Configuration → List Nat
  | .scalar _ => []
  | .tensor rank extent _ => List.replicate rank extent

def generatedSnapshot (configuration : Configuration) : SourceSnapshot :=
  let axes := fixtureAxes configuration
  let shape := fixtureShape configuration
  let count := shape.foldl (· * ·) 1
  let factors := factorCount configuration
  let label := configurationLabel configuration
  let name : Nat → String := fun f => s!"A{f}-{label}"
  let output := s!"Y-{label}"
  let extent := match configuration with
    | .scalar _ => 0
    | .tensor _ extent _ => extent
  let declarations : List Decl :=
    axes.map (fun ax => Decl.axis ax (some extent)) ++
      (List.range factors).map (fun f => .typedTensor .f64 (name f) axes) ++
      [.typedTensor .f64 output axes]
  let inputs : List InputBinding := (List.range factors).map fun f =>
    (⟨axes.length + f, shape,
      (List.range count).map fun cell =>
        ((f + 2 + (f + 1) * cell : Nat) : Rat)⟩ : InputBinding)
  ⟨⟨declarations,
    [.assign output (axes.map LHSSlot.free)
      (rhs [(List.range factors).map fun f => .read (name f) (axes.map IdxExpr.axis)])],
    {}, ∅⟩,
    (List.range factors).map (fun f => ⟨axes.length + f, .input, shape⟩) ++
      [⟨axes.length + factors, .output, shape⟩], inputs⟩

-- Expected cells enumerate rank-specific coordinates, not oracle/dense packing helpers.
private def expectedCells (configuration : Configuration) (cellValue : Nat → Nat) : List Nat :=
  match configuration with
  | .scalar _ => [cellValue 0]
  | .tensor 1 extent _ => (List.range extent).map cellValue
  | .tensor 2 extent _ =>
    (List.range extent).flatMap fun row =>
      (List.range extent).map fun column => cellValue (row * extent + column)
  | .tensor _ _ _ => []

private def generatedExpected (configuration : Configuration) : List Oracle.Tensor :=
  let label := configurationLabel configuration
  let rank := (fixtureAxes configuration).length
  let shape := fixtureShape configuration
  let a : List Nat := expectedCells configuration (fun p => p + 2)
  let b : List Nat := expectedCells configuration (fun p => 2 * p + 3)
  let output : List Nat := expectedCells configuration fun p =>
    if factorCount configuration == 1 then p + 2
    else 2 * p * p + 7 * p + 6
  [⟨rank, s!"A0-{label}", .input, shape, a.map (fun n => (n : Rat))⟩] ++
    (if factorCount configuration == 2 then
      [⟨rank + 1, s!"A1-{label}", .input, shape, b.map (fun n => (n : Rat))⟩]
    else []) ++
    [⟨rank + factorCount configuration, s!"Y-{label}", .output, shape,
      output.map (fun n => (n : Rat))⟩]

structure Receipt where
  label : String
  snapshot : SourceSnapshot
  dependencyOrder : List Nat
  actual : Except Debug.ExecutionError Differential.ComparisonRun

private def receipt (label : String) (snapshot : SourceSnapshot) (order : List Nat) : Receipt :=
  ⟨label, snapshot, order, compareSource snapshot (some order)⟩

def F16Receipts : List Receipt :=
  configurations.map fun configuration =>
    receipt (s!"F16/{configurationLabel configuration}") (generatedSnapshot configuration)
      [(fixtureAxes configuration).length + factorCount configuration]

private def referenceExact (run : Differential.ComparisonRun)
    (expected : List Oracle.Tensor) : Bool :=
  let actual : List Debug.TensorObservation := run.reference.observe.endpoint.snapshot.tensors
  let metadata : List (Nat × Option String × TensorRole × List Nat × List (Option Rat)) :=
    actual.map fun t =>
      (t.declaration, t.name, t.role, t.shape, t.values)
  let wanted : List (Nat × Option String × TensorRole × List Nat × List (Option Rat)) :=
    expected.map fun t =>
      (t.declaration, some t.name, t.role, t.shape, t.values.map some)
  let complete := match run.reference.observe.endpoint with
    | .complete _ => true
    | _ => false
  let oracle := match run.oracle with
    | .ok result => result.tensors == expected
    | .error _ => false
  let compared := match run.referenceComparison with
    | some comparison =>
      match comparison.published, comparison.collection, comparison.body with
      | .ok .agreement, .ok .agreement, .ok .agreement => true
      | _, _, _ => false
    | none => false
  complete && decide (metadata = wanted) && oracle && compared

private def smallIntegerBits (value : Rat) : Option UInt64 :=
  if value.den != 1 || value.num < 0 || value.num > 1024 then none
  else
    let n := value.num.toNat
    if n == 0 then some 0 else
      let exponent := n.log2
      some (UInt64.ofNat (exponent + 1023) <<< 52 |||
        UInt64.ofNat (n - 2 ^ exponent) <<< UInt64.ofNat (52 - exponent))

private def nativeExact (observation : NativeLegs.NativeObservation)
    (expected : List Oracle.Tensor) : Bool :=
  match observation.outputs with
  | .error _ => false
  | .ok outputs =>
    let wanted : List Oracle.Tensor := expected.filter (fun t => t.role == .output)
    outputs.length == wanted.length &&
      (outputs.zip wanted).all fun (actual, binding) =>
        actual.metadata.declaration == binding.declaration &&
        actual.metadata.name == binding.name &&
        actual.metadata.shape == binding.shape &&
        actual.shape == binding.shape &&
        actual.bits.size == binding.values.length &&
        actual.bits.toList.map some == binding.values.map smallIntegerBits

private def observedNativeExact (run : Differential.ComparisonRun)
    (expected : List Oracle.Tensor) : Bool :=
  match run.native with
  | .error _ => false
  | .ok native =>
    let legacy := match native.legacy with
      | .observed observation => nativeExact observation expected
      | .unavailable _ | .failure _ => true
    let checked := match native.checked with
      | .observed observation _ => nativeExact observation expected
      | .unavailable _ | .sourceCompilation _ | .preparation _ | .runtime _ => true
    legacy && checked

-- Rejections remain labeled typed receipts, never successful four-leg samples.
private def parityOrExplicitRejection (run : Differential.ComparisonRun) : Bool :=
  match run.classification with
  | .fourLegParity => true
  | .unsupportedNumericalProfile _ => true
  | .nativeUnavailable =>
    match run.native with
    | .ok native =>
      match native.legacy, native.checked with
      | .unavailable _, _ | _, .unavailable _ => true
      | _, _ => false
    | .error _ => false
  | .nativeFailure =>
    match run.native with
    | .ok native =>
      match native.legacy, native.checked with
      | .failure _, _ | _, .sourceCompilation _ | _, .preparation _ | _, .runtime _ => true
      | _, _ => false
    | .error _ => false
  | _ => false

private def exactReceipt (r : Receipt) (expected : List Oracle.Tensor) : Bool :=
  match r.actual with
  | .error _ => false
  | .ok run =>
    run.fixtureDependencyOrder == some r.dependencyOrder &&
      referenceExact run expected && observedNativeExact run expected &&
      parityOrExplicitRejection run

def F16 : Bool :=
  configurations.length == 18 &&
    decide (configurations.Nodup) &&
    decide (configurations =
      [.scalar 1, .scalar 2,
       .tensor 1 0 1, .tensor 1 0 2, .tensor 1 1 1, .tensor 1 1 2,
       .tensor 1 2 1, .tensor 1 2 2, .tensor 1 3 1, .tensor 1 3 2,
       .tensor 2 0 1, .tensor 2 0 2, .tensor 2 1 1, .tensor 2 1 2,
       .tensor 2 2 1, .tensor 2 2 2, .tensor 2 3 1, .tensor 2 3 2]) &&
    decide ((configurations.map fun c => (generatedSnapshot c).resolved.decls).Nodup) &&
    decide ((configurations.map fun c => (generatedSnapshot c).resolved.stmts).Nodup) &&
    F16Receipts.length == 18 &&
    (F16Receipts.zip configurations).all fun (r, configuration) =>
      exactReceipt r (generatedExpected configuration)

private def chain : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis k (some 3),
      .typedTensor .f64 "A" [i, k], .typedTensor .f64 "B" [i],
      .typedTensor .f64 "Y" [i], .typedTensor .f64 "Mid" [i],
      .typedTensor .f64 "End" [i], .typedTensor .f64 "Spare" [i, k]],
    [.assign "Y" [.free i] (rhs [[.read "End" [.axis i]], [.read "B" [.axis i]]]),
     .assign "End" [.free i] (rhs [[.read "Mid" [.axis i], .read "B" [.axis i]]]),
     .assign "Mid" [.free i] (rhs [[.read "A" [.axis i, .axis k]]])], {}, ∅⟩,
    [⟨2, .input, [2, 3]⟩, ⟨3, .input, [2]⟩, ⟨4, .output, [2]⟩,
     ⟨5, .defined, [2]⟩, ⟨6, .output, [2]⟩, ⟨7, .defined, [2, 3]⟩],
    [⟨2, [2, 3], [1, 2, 3, 4, 5, 6]⟩, ⟨3, [2], [2, 5]⟩]⟩

private def chainExpected : List Oracle.Tensor :=
  [⟨2, "A", .input, [2, 3], [1, 2, 3, 4, 5, 6]⟩,
   ⟨3, "B", .input, [2], [2, 5]⟩,
   ⟨4, "Y", .output, [2], [14, 80]⟩,
   ⟨5, "Mid", .defined, [2], [6, 15]⟩,
   ⟨6, "End", .output, [2], [12, 75]⟩,
   ⟨7, "Spare", .defined, [2, 3], [0, 0, 0, 0, 0, 0]⟩]

def F17Receipt : Receipt :=
  receipt "F17/consumer-first-chain-and-unwritten-nonoutput" chain [7, 5, 6, 4]

def F17 : Bool :=
  exactReceipt F17Receipt chainExpected &&
    match F17Receipt.actual with
    | .error _ => false
    | .ok run =>
      let admitted := run.reference.source.admitted
      admitted.statements.map (·.original) == [0, 1, 2] &&
        admitted.statements.map
          (fun st => (admitted.source.table.entry st.output.tensor).declaration) == [4, 6, 5] &&
        (run.reference.observe.endpoint.snapshot.tensors.filter
          (fun t => t.role != .input)).length == 4

private def sameFirst : AxisSpec := ⟨"same", 7, .nat⟩
private def sameSecond : AxisSpec := ⟨"same", 19, .nat⟩

private def sameNameResolved : SourceSnapshot :=
  ⟨⟨[.axis sameFirst (some 2), .axis sameSecond (some 3),
      .typedTensor .f64 "A" [sameFirst, sameSecond],
      .typedTensor .f64 "B" [sameSecond, sameFirst],
      .typedTensor .f64 "Y" [sameFirst, sameSecond]],
    [.assign "Y" [.free sameFirst, .free sameSecond]
      (rhs [[.read "A" [.axis sameFirst, .axis sameSecond],
             .read "B" [.axis sameSecond, .axis sameFirst]]])], {}, ∅⟩,
    [⟨2, .input, [2, 3]⟩, ⟨3, .input, [3, 2]⟩, ⟨4, .output, [2, 3]⟩],
    [⟨2, [2, 3], [2, 3, 5, 7, 11, 13]⟩,
     ⟨3, [3, 2], [17, 19, 23, 29, 31, 37]⟩]⟩

private def sameNameExpected : List Oracle.Tensor :=
  [⟨2, "A", .input, [2, 3], [2, 3, 5, 7, 11, 13]⟩,
   ⟨3, "B", .input, [3, 2], [17, 19, 23, 29, 31, 37]⟩,
   ⟨4, "Y", .output, [2, 3], [34, 69, 155, 133, 319, 481]⟩]

def F18Receipt : Receipt :=
  receipt "F18/resolved-same-name-distinct-UID-reference-only" sameNameResolved [4]

private def identityIsExpected : NativeLegs.IdentityRefusal → Bool
  | .sameNameDistinctUID first second =>
    decide (first = sameFirst ∧ second = sameSecond)
  | .sameUIDDistinctName _ _ => false

private def expectedUIDRows : List (Debug.OccurrenceKey × List Nat × Option Rat) :=
  [ (⟨0, [(7, 0), (19, 0)]⟩, [0, 0], some 34),
    (⟨0, [(7, 0), (19, 1)]⟩, [0, 1], some 69),
    (⟨0, [(7, 0), (19, 2)]⟩, [0, 2], some 155),
    (⟨0, [(7, 1), (19, 0)]⟩, [1, 0], some 133),
    (⟨0, [(7, 1), (19, 1)]⟩, [1, 1], some 319),
    (⟨0, [(7, 1), (19, 2)]⟩, [1, 2], some 481) ]

def F18 : Bool :=
  match F18Receipt.actual with
  | .error _ => false
  | .ok run =>
    let actual := (Debug.canonicalContributions run.reference.observe.events).map fun row =>
      (row.key, row.destination.coordinate, row.value)
    let oracleAssignments := match run.oracle with
      | .error _ => false
      | .ok result =>
        (result.contributions.flatMap
          (fun contribution => contribution.terms.flatMap (·.occurrences))).map
          (fun occurrence => (occurrence.assignment, occurrence.output, some occurrence.value)) ==
        expectedUIDRows.map (fun (key, coordinate, value) =>
          (key.assignments, coordinate, value))
    let reads := match run.oracle with
      | .error _ => false
      | .ok result =>
        (result.contributions.flatMap
          (fun contribution => contribution.terms.flatMap (·.occurrences))).map
          (fun occurrence => occurrence.reads.map
            (fun read => (read.declaration, read.coordinate, read.value))) ==
        ([[(2, [0, 0], 2), (3, [0, 0], 17)],
          [(2, [0, 1], 3), (3, [1, 0], 23)],
          [(2, [0, 2], 5), (3, [2, 0], 31)],
          [(2, [1, 0], 7), (3, [0, 1], 19)],
          [(2, [1, 1], 11), (3, [1, 1], 29)],
          [(2, [1, 2], 13), (3, [2, 1], 37)]] :
          List (List (Nat × List Nat × Rat)))
    let identity := match run.native with
      | .error _ => false
      | .ok native =>
        let declared := match native.identity with
          | .error reason => identityIsExpected reason
          | .ok _ => false
        let legacy := match native.legacy with
          | .unavailable (.identity reason) => identityIsExpected reason
          | _ => false
        let checked := match native.checked with
          | .unavailable (.identity reason) => identityIsExpected reason
          | _ => false
        declared && legacy && checked
    let classification := match run.classification with
      | .nativeUnavailable => true
      | _ => false
    referenceExact run sameNameExpected && decide (actual = expectedUIDRows) &&
      oracleAssignments && reads && identity && classification &&
      run.reference.source.admitted.source.context.axes.map
        (fun ax => (ax.uid, ax.extent)) == [(7, 2), (19, 3)] &&
      run.reference.observe.endpoint.snapshot.tensors.map
        (fun binding => (binding.tensorUID, binding.axes.map (fun ax => (ax.uid, ax.extent)))) ==
        [(0, [(7, 2), (19, 3)]), (1, [(19, 3), (7, 2)]), (2, [(7, 2), (19, 3)])]

private def renderReceipt (r : Receipt) : String :=
  s!"{r.label}\noriginalDecls={repr r.snapshot.resolved.decls}\noriginalStmts={repr r.snapshot.resolved.stmts}\n{renderSourceComparison r.actual}"

def F16ParityLabels : List String :=
  F16Receipts.filterMap fun r =>
    match r.actual with
    | .ok run =>
      match run.classification with
      | .fourLegParity => some r.label
      | _ => none
    | .error _ => none

#guard F16
#guard F17
#guard F18

#eval F16Receipts.map renderReceipt
#eval F16ParityLabels
#eval renderReceipt F17Receipt
#eval renderReceipt F18Receipt

end SourceDifferentialCorpusTest
