import Semantics.SourceDifferentialFixtures
import Semantics.SourceDiagnosticFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Debug
open LeanNCD.Semantics.Source.NativeLegs
open LeanNCD.Semantics.Source.Differential
open LeanNCD.Semantics.Source.NumericalProfile
open SourceAdmissionFixtures

namespace SourceDifferentialPolicyTest

private def referenceAgreement (comparison : ReferenceComparison) : Bool :=
  match comparison.published, comparison.collection, comparison.body with
  | .ok .agreement, .ok .agreement, .ok .agreement => true
  | _, _, _ => false

private def completeValues (run : SourceRun)
    (expected : List (Nat × Nat × List Nat × List Rat)) : Bool :=
  match run.observe.endpoint with
  | .complete snapshot =>
    snapshot.tensors.map (fun t => (t.tensorUID, t.declaration, t.shape, t.values)) ==
      expected.map (fun (uid, declaration, shape, values) =>
        (uid, declaration, shape, values.map some)) &&
      snapshot.pending == [] && snapshot.unpublished == []
  | _ => false

private def originalNative (native : NativeRun) (snapshot : SourceSnapshot) : Bool :=
  native.source.snapshot.resolved.decls == snapshot.resolved.decls &&
    native.source.snapshot.resolved.stmts == snapshot.resolved.stmts &&
    native.source.program.decls == snapshot.resolved.decls &&
    native.source.program.stmts == snapshot.resolved.stmts &&
    native.source.snapshot.inputs.map (fun b => (b.declaration, b.shape, b.values)) ==
      snapshot.inputs.map (fun b => (b.declaration, b.shape, b.values))

private def observedOutput (actual : NativeObservation) (uid declaration : Nat)
    (shape : List Nat) (bits : Array UInt64) : Bool :=
  match actual.outputs, actual.report.env["Y"]? with
  | .ok [output], some binding =>
    output.metadata.tensorUID == uid && output.metadata.declaration == declaration &&
      output.metadata.name == "Y" &&
      output.metadata.origin == { side := .declaration, declaration := some declaration } &&
      output.metadata.axes.map Axis.extent == shape && output.metadata.shape == shape &&
      output.shape == shape && output.bits.size == bits.size && output.bits == bits &&
      binding.shape == shape && binding.data.size == bits.size &&
      binding.data.map Float.toBits == bits &&
      actual.report.warnings == [] &&
      actual.backendInternals == .unobserved .noBackendInternalHook
  | _, _ => false

private def defaultF32 : SourceSnapshot :=
  { SourceDiagnosticFixtures.scalarSnapshot with
    resolved := { SourceDiagnosticFixtures.scalarSnapshot.resolved with
      decls := [.tensor "A" [], .tensor "Y" []] } }

private def f32Refusal : Bool :=
  match compareSource defaultF32 (some [1]) with
  | .ok run =>
    let origin : SourceOrigin :=
      { side := .output, declaration := some 1, statement := some 0 }
    let condition : StructuralCondition := .usedDType origin "Y" .f32
    run.fixtureDependencyOrder == some [1] &&
      completeValues run.reference [(0, 0, [], [3]), (1, 1, [], [3])] &&
      run.reference.source.admitted.statements.map (·.original) == [0] &&
      (match run.classification with
      | .knownContractDifference actual => actual == condition
      | _ => false) &&
      (match run.profile with
      | .error reason => reason == .structural condition
      | _ => false) &&
      (match run.oracle, run.referenceComparison with
      | .ok oracle, some comparison =>
        oracle.tensors.map (fun t => (t.declaration, t.shape, t.values)) ==
          [(0, [], [3]), (1, [], [3])] && referenceAgreement comparison
      | _, _ => false) &&
      (match run.native with
      | .ok native =>
        originalNative native defaultF32 &&
          native.source.admitted.source.table.entries.map (·.elementType) == [.f32, .f32] &&
          native.shared == .error (.structural condition) &&
          (match native.legacy, native.checked with
          | .failure legacy, .preparation checked =>
            (match legacy.original.error with
            | .unsupportedDtype "A" => true
            | _ => false) &&
              legacy.phase == .scheduledEvaluation &&
              checked.original.cause == .inputSignature (.dtypeMismatch "A" .f32 .f64) &&
              legacy.original.warnings == [] && checked.original.warnings == [] &&
              legacy.mappings ==
                [⟨"Y", [{ side := .output, declaration := some 1, statement := some 0 }], none⟩] &&
              checked.mappings ==
                [⟨"Y", [{ side := .output, declaration := some 1, statement := some 0 }], some 0⟩] &&
              (match run.legacyComparison, run.checkedComparison with
              | .unavailable .legNotObserved, .unavailable .legNotObserved => true
              | _, _ => false)
          | _, _ => false)
      | _ => false)
  | _ => false

private def f64Neighbor : Bool :=
  let snapshot := SourceDiagnosticFixtures.scalarSnapshot
  match compareSource snapshot (some [1]) with
  | .ok run =>
    match run.classification, run.profile, run.native, run.oracle with
    | .fourLegParity, .ok profile, .ok native, .ok oracle =>
      snapshot.resolved.decls == [.typedTensor .f64 "A" [], .typedTensor .f64 "Y" []] &&
        snapshot.resolved.stmts == defaultF32.resolved.stmts &&
        snapshot.inputs.map (fun b => (b.declaration, b.shape, b.values)) ==
          defaultF32.inputs.map (fun b => (b.declaration, b.shape, b.values)) &&
        run.fixtureDependencyOrder == some [1] &&
        completeValues run.reference [(0, 0, [], [3]), (1, 1, [], [3])] &&
        oracle.tensors.map (fun t => (t.declaration, t.shape, t.values)) ==
          [(0, [], [3]), (1, [], [3])] &&
        profile.actual.isSome && originalNative native snapshot &&
        (match native.shared with | .ok _ => true | _ => false) &&
        (match run.referenceComparison with
        | some comparison => referenceAgreement comparison
        | _ => false) &&
        (match run.legacyComparison, run.checkedComparison with
        | .compared (.ok .agreement), .compared (.ok .agreement) => true
        | _, _ => false) &&
        (match native.legacy, native.checked with
        | .observed legacy, .observed checked _ =>
          observedOutput legacy 1 1 [] #[0x4008000000000000] &&
            observedOutput checked 1 1 [] #[0x4008000000000000]
        | _, _ => false)
    | _, _, _, _ => false
  | _ => false

def F13 : Bool := f32Refusal && f64Neighbor

private def multiDefinition : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .typedTensor .f64 "A" [i],
      .typedTensor .f64 "B" [i], .typedTensor .f64 "Y" [i]],
    [.assign "Y" [.free i] (rhs [[.read "A" [.axis i]]]),
     .assign "Y" [.free i] (rhs [[.read "B" [.axis i]]])], {}, ∅⟩,
    [⟨1, .input, [2]⟩, ⟨2, .input, [2]⟩, ⟨3, .output, [2]⟩],
    [⟨1, [2], [5, 9]⟩, ⟨2, [2], [2, 4]⟩]⟩

private def outputOrigin (statement : Nat) : SourceOrigin :=
  { side := .output, declaration := some 3, statement := some statement }

private def statementContributions (statement : Nat) (values : List Rat) :
    List ContributionObservation :=
  values.zipIdx.map fun (value, coordinate) =>
    ⟨⟨statement, [(7, coordinate)]⟩, ⟨2, 3, [coordinate]⟩, some value⟩

private def overwriteRefusal (run : ComparisonRun) (origins : List SourceOrigin) : Bool :=
  let condition : StructuralCondition := .crossStatementOverwrite 3 origins
  (match run.classification with
  | .knownContractDifference actual => actual == condition
  | _ => false) &&
    (match run.profile with
    | .error reason => reason == .structural condition
    | _ => false) &&
    (match run.native with
    | .ok native => native.shared == .error (.structural condition)
    | _ => false) &&
    (match run.legacyComparison, run.checkedComparison with
    | .unavailable (.profile left), .unavailable (.profile right) =>
      left == .structural condition && right == .structural condition
    | _, _ => false)

def F14 : Bool :=
  match compareSource multiDefinition (some [3]) with
  | .ok run =>
    run.fixtureDependencyOrder == some [3] &&
      overwriteRefusal run [outputOrigin 0, outputOrigin 1] &&
      completeValues run.reference
        [(0, 1, [2], [5, 9]), (1, 2, [2], [2, 4]), (2, 3, [2], [7, 13])] &&
      run.reference.source.admitted.statements.map (·.original) == [0, 1] &&
      canonicalContributions run.reference.observe.events ==
        statementContributions 0 [5, 9] ++ statementContributions 1 [2, 4] &&
      (match run.oracle, run.referenceComparison with
      | .ok oracle, some comparison =>
        oracle.tensors.map (fun t => (t.declaration, t.shape, t.values)) ==
          [(1, [2], [5, 9]), (2, [2], [2, 4]), (3, [2], [7, 13])] &&
          referenceAgreement comparison
      | _, _ => false) &&
      (match run.native with
      | .ok native =>
        originalNative native multiDefinition &&
          native.source.admitted.statements.map (·.original) == [0, 1] &&
          (match native.legacy, native.checked with
          | .observed legacy, .observed checked mappings =>
            observedOutput legacy 2 3 [2] #[0x4000000000000000, 0x4010000000000000] &&
              observedOutput checked 2 3 [2] #[0x4000000000000000, 0x4010000000000000] &&
              !mappings.isEmpty && mappings.all (fun mapping =>
                mapping.name == "Y" && mapping.originals == [outputOrigin 0, outputOrigin 1] &&
                  mapping.scheduledIndex.isSome)
          | _, _ => false)
      | _ => false)
  | _ => false

private def duplicateDefinition : SourceSnapshot :=
  { multiDefinition with
    resolved := { multiDefinition.resolved with stmts :=
      multiDefinition.resolved.stmts ++
        [.assign "Y" [.free i] (rhs [[.read "A" [.axis i]]])] } }

-- This path executes already-identified statements; it never re-admits reordered raw syntax.
private def derivedSourceRun (source : IdentifiedSource) : Except ExecutionError SourceRun := do
  let actual ← (runSourceDebug source.admitted).mapError fun t =>
    .inputPresence t.val
      { side := .input, declaration := some (source.admitted.source.table.entry t).declaration }
      ((elaborateSource source.admitted).input t)
      ((sourceInputBinding source.admitted t).isSome)
  pure ⟨source, actual, none⟩

private def compareDebug (before after : SourceRun) : Bool :=
  compareContributions (canonicalContributions before.observe.events)
    (canonicalContributions after.observe.events) == .ok .agreement &&
    compareTensors before.observe.endpoint.snapshot.tensors
      after.observe.endpoint.snapshot.tensors == .ok .agreement

private def expectedOccurrence (statement localIndex coordinate donor : Nat) :
    OccurrenceObservation :=
  let readOrigin : SourceOrigin :=
    { side := .read, declaration := some donor, statement := some statement,
      term := some 0, factor := some 0 }
  ⟨⟨statement, [(7, coordinate)]⟩, localIndex, ⟨2, 3, [coordinate]⟩,
    outputOrigin statement,
    [⟨{ side := .read, statement := some statement, term := some 0 },
      [(readOrigin, [({ readOrigin with slot := some 0 }, 7)])], [],
      .unobserved .noTermEvaluationHook, .unobserved .noTermEvaluationHook⟩]⟩

private def contributionEvents (run : SourceRun) : List (OccurrenceObservation × Rat) :=
  run.observe.events.filterMap fun event => match event with
    | .contribution occurrence value => some (occurrence, value)
    | _ => none

private def originalLocals (source : IdentifiedSource) : List (Nat × Nat × Nat) :=
  (List.finRange source.admitted.statements.length).map fun position =>
    let original := source.originalEquiv position
    let localTag := source.originalToLocal original
    (original.val, localTag.1.val, localTag.2.val)

private def explicitOracle (run : SourceRun) : Bool :=
  match Oracle.run run.source.admitted (some [3]), Oracle.run run.source.admitted none with
  | .ok oracle, .error missing =>
    oracle.tensors.map (fun t => (t.declaration, t.shape, t.values)) ==
      [(1, [2], [5, 9]), (2, [2], [2, 4]), (3, [2], [12, 22])] &&
      referenceAgreement (compareReference run oracle) && missing.cause == .missingOrder
  | _, _ => false

def F15 : Bool :=
  match compareSource duplicateDefinition (some [3]) with
  | .ok original =>
    let before := original.reference
    let permutation := permuteStatements before.source.admitted
      { toFun := Fin.rev, invFun := Fin.rev,
        left_inv := Fin.rev_rev, right_inv := Fin.rev_rev }
    let identified := StatementPermutation.identified before.source permutation
    match derivedSourceRun identified with
    | .ok after =>
      let expected := statementContributions 0 [5, 9] ++
        statementContributions 1 [2, 4] ++ statementContributions 2 [5, 9]
      let whole : List (Nat × Nat × List Nat × List Rat) :=
        [(0, 1, [2], [5, 9]), (1, 2, [2], [2, 4]), (2, 3, [2], [12, 22])]
      original.fixtureDependencyOrder == some [3] &&
        duplicateDefinition.resolved.stmts.length == 3 &&
        duplicateDefinition.resolved.stmts[0]? == duplicateDefinition.resolved.stmts[2]? &&
        overwriteRefusal original [outputOrigin 0, outputOrigin 1] &&
        checkStructure after.source.admitted ==
          .error (.structural (.crossStatementOverwrite 3 [outputOrigin 2, outputOrigin 1])) &&
        before.source.admitted.statements.map (·.original) == [0, 1, 2] &&
        after.source.admitted.statements.map (·.original) == [2, 1, 0] &&
        originalLocals before.source == [(0, 2, 0), (1, 2, 1), (2, 2, 2)] &&
        originalLocals after.source == [(2, 2, 0), (1, 2, 1), (0, 2, 2)] &&
        completeValues before whole && completeValues after whole &&
        canonicalContributions before.observe.events == expected &&
        canonicalContributions after.observe.events == expected &&
        ((canonicalContributions after.observe.events).map (·.key)).eraseDups.length == 6 &&
        contributionEvents before ==
          [(expectedOccurrence 0 0 0 1, 5), (expectedOccurrence 0 0 1 1, 9),
           (expectedOccurrence 1 1 0 2, 2), (expectedOccurrence 1 1 1 2, 4),
           (expectedOccurrence 2 2 0 1, 5), (expectedOccurrence 2 2 1 1, 9)] &&
        contributionEvents after ==
          [(expectedOccurrence 2 0 0 1, 5), (expectedOccurrence 2 0 1 1, 9),
           (expectedOccurrence 1 1 0 2, 2), (expectedOccurrence 1 1 1 2, 4),
           (expectedOccurrence 0 2 0 1, 5), (expectedOccurrence 0 2 1 1, 9)] &&
        compareDebug before after && explicitOracle before && explicitOracle after &&
        (match original.native with
        | .ok native =>
          originalNative native duplicateDefinition &&
            native.source.admitted.statements.map (·.original) == [0, 1, 2] &&
            (match native.legacy, native.checked with
            | .observed legacy, .observed checked mappings =>
              observedOutput legacy 2 3 [2] #[0x4014000000000000, 0x4022000000000000] &&
                observedOutput checked 2 3 [2] #[0x4014000000000000, 0x4022000000000000] &&
                !mappings.isEmpty && mappings.all (fun mapping =>
                  mapping.name == "Y" &&
                    mapping.originals == [outputOrigin 0, outputOrigin 1, outputOrigin 2] &&
                    mapping.scheduledIndex.isSome)
            | _, _ => false)
        | _ => false)
    | _ => false
  | _ => false

#guard F13
#guard F14
#guard F15

end SourceDifferentialPolicyTest
