import Semantics.SourceDiagnosticFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Differential
open LeanNCD.Semantics.Source.NativeLegs
open SourceAdmissionFixtures

namespace SourceDiagnosticAdmissionFixtures

private def unsupportedSnapshot (factor : Factor) : SourceSnapshot :=
  { SourceDiagnosticFixtures.vectorSnapshot with
    resolved := { SourceDiagnosticFixtures.vectorSnapshot.resolved with
      decls := SourceDiagnosticFixtures.vectorSnapshot.resolved.decls ++
        [.typedTensor .f64 "Scalar" []]
      stmts := stmts ++ [
        .assign "Scalar" [] (rhs [
          [.read "A" [.axis i, .axis k]],
          [.read "A" [.axis i, .axis k], .read "B" [.axis i],
           factor, .read "B" [.axis i]]])] }
    specs := specs ++ [⟨8, .output, []⟩] }

private def unsupportedRefusal (factor : Factor) (form : UnsupportedSource) : Bool :=
  match compareSource (unsupportedSnapshot factor) (some [5, 7, 8]) with
  | .error (.admission diagnostic) =>
    match diagnostic.cause with
    | .unsupported actual =>
      actual == form && diagnostic.stage == .read &&
        diagnostic.origin == {
          side := .read, statement := some 3, term := some 1, factor := some 2 } &&
        renderSourceComparison (.error (.admission diagnostic)) ==
          s!"admission: stage={repr diagnostic.stage} origin={repr diagnostic.origin} cause={repr diagnostic.cause}"
    | _ => false
  | _ => false

private def defaultF32Snapshot : SourceSnapshot :=
  { SourceDiagnosticFixtures.scalarSnapshot with
    resolved := { SourceDiagnosticFixtures.scalarSnapshot.resolved with
      decls := [.tensor "A" [], .tensor "Y" []] } }

private def defaultF32Comparison :=
  compareSource defaultF32Snapshot (some [1])

private def acceptedF32 : Bool :=
  match defaultF32Comparison with
  | .ok run =>
    match run.classification, run.profile, run.reference.observe.endpoint, run.oracle with
    | .knownContractDifference (.usedDType origin "Y" .f32),
      .error (.structural (.usedDType profileOrigin "Y" .f32)), .complete snapshot,
      .ok oracle =>
      origin == { side := .output, declaration := some 1, statement := some 0 } &&
        profileOrigin == origin &&
        snapshot.tensors.map (fun t => (t.tensorUID, t.declaration, t.shape, t.values)) ==
          [(0, 0, [], [some 3]), (1, 1, [], [some 3])] &&
        oracle.tensors.map (fun t => (t.declaration, t.shape, t.values)) ==
          [(0, [], [3]), (1, [], [3])] &&
        run.reference.actual.result.events.length == 2 &&
        (match run.referenceComparison with
        | some comparison =>
          match comparison.published, comparison.collection, comparison.body with
          | .ok .agreement, .ok .agreement, .ok .agreement => true
          | _, _, _ => false
        | none => false)
    | _, _, _, _ => false
  | _ => false

private def nonsharedSnapshot : SourceSnapshot :=
  { SourceDiagnosticFixtures.scalarSnapshot with
    resolved := { SourceDiagnosticFixtures.scalarSnapshot.resolved with
      stmts := SourceDiagnosticFixtures.scalarSnapshot.resolved.stmts ++
        SourceDiagnosticFixtures.scalarSnapshot.resolved.stmts } }

private def acceptedNonshared : Bool :=
  match compareSource nonsharedSnapshot (some [1]) with
  | .ok run =>
    match run.classification, run.profile, run.reference.observe.endpoint, run.oracle with
    | .knownContractDifference (.crossStatementOverwrite 1 origins),
      .error (.structural (.crossStatementOverwrite 1 profileOrigins)), .complete snapshot,
      .ok oracle =>
      origins == [
        { side := .output, declaration := some 1, statement := some 0 },
        { side := .output, declaration := some 1, statement := some 1 }] &&
        profileOrigins == origins &&
        snapshot.tensors.map (fun t => (t.tensorUID, t.declaration, t.values)) ==
          [(0, 0, [some 3]), (1, 1, [some 6])] &&
        oracle.tensors.map (fun t => (t.declaration, t.values)) ==
          [(0, [3]), (1, [6])] &&
        oracle.contributions.map (·.value) == [3, 3] &&
        run.reference.source.admitted.statements.map (·.original) == [0, 1] &&
        (match run.referenceComparison with
        | some comparison =>
          match comparison.published, comparison.collection, comparison.body with
          | .ok .agreement, .ok .agreement, .ok .agreement => true
          | _, _, _ => false
        | none => false) &&
        (match run.native with
        | .ok native =>
          match native.legacy, native.checked with
          | .observed legacy, .observed checked _ =>
            native.source.snapshot.resolved.decls ==
              SourceDiagnosticFixtures.scalarSnapshot.resolved.decls &&
            native.source.snapshot.resolved.stmts == nonsharedSnapshot.resolved.stmts &&
            (match legacy.outputs, checked.outputs with
            | .ok [l], .ok [c] =>
              l.metadata.declaration == 1 && c.metadata == l.metadata &&
                l.shape == [] && c.shape == [] &&
                l.bits == #[0x4008000000000000] && c.bits == l.bits
            | _, _ => false)
          | _, _ => false
        | _ => false)
    | _, _, _, _ => false
  | _ => false

private def rationalSnapshot : SourceSnapshot :=
  { SourceDiagnosticFixtures.scalarSnapshot with inputs := [⟨0, [], [3 / 2]⟩] }

private def acceptedNonintegral : Bool :=
  match SourceProgramFixtures.observe rationalSnapshot,
      compareSource rationalSnapshot (some [1]) with
  | .ok control, .ok run =>
    control.kind == .complete &&
    control.tensors.map (fun t => (t.uid, t.declaration, t.values)) ==
      [(0, 0, [some (3 / 2)]), (1, 1, [some (3 / 2)])] &&
    (match run.classification, run.profile, run.reference.observe.endpoint, run.oracle with
    | .unsupportedNumericalProfile reason,
      .error (.nonIntegral site .input 3 2), .complete snapshot, .ok oracle =>
      reason == .nonIntegral site .input 3 2 &&
        site == { origin := { side := .input, declaration := some 0 }, cell := some 0 } &&
        snapshot.tensors.map (fun t => (t.tensorUID, t.declaration, t.values)) ==
          [(0, 0, [some (3 / 2)]), (1, 1, [some (3 / 2)])] &&
        oracle.tensors.map (·.values) == [[3 / 2], [3 / 2]] &&
        oracle.contributions.map (·.value) == [3 / 2] &&
        run.reference.actual.result.events.length == 2 &&
        (match run.native with
        | .ok native =>
          match native.inputs, native.legacy, native.checked with
          | .error inputReason, .unavailable (.input legacyReason),
            .unavailable (.input checkedReason) =>
            inputReason == reason && legacyReason == reason && checkedReason == reason &&
              native.source.snapshot.inputs.map (·.values) == [[3 / 2]]
          | _, _, _ => false
        | _ => false)
    | _, _, _, _ => false)
  | _, _ => false

private def otherI : AxisSpec := ⟨"i", 99, .nat⟩

private def sameNameSnapshot : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis otherI (some 2),
      .typedTensor .f64 "A" [i], .typedTensor .f64 "Y" [otherI]],
    [.assign "Y" [.free otherI] (rhs [[.read "A" [.axis i]]])], {}, ∅⟩,
    [⟨2, .input, [2]⟩, ⟨3, .output, [2]⟩], [⟨2, [2], [5, 9]⟩]⟩

private def referenceOnlyIdentity : Bool :=
  match compareSource sameNameSnapshot (some [3]) with
  | .ok run =>
    match run.classification, run.reference.observe.endpoint, run.oracle, run.profile,
        run.native with
    | .nativeUnavailable, .complete snapshot, .ok oracle, .ok _,
      .ok native =>
      snapshot.tensors.map (fun t => (t.tensorUID, t.declaration, t.axes.map Axis.uid,
        t.values)) == [(0, 2, [7], [some 5, some 9]), (1, 3, [99], [some 14, some 14])] &&
        oracle.tensors.map (fun t => (t.declaration, t.values)) == [(2, [5, 9]), (3, [14, 14])] &&
        (match native.identity, native.legacy, native.checked with
        | .error (.sameNameDistinctUID first second),
          .unavailable (.identity legacyReason), .unavailable (.identity checkedReason) =>
          first == i && second == otherI &&
            legacyReason == .sameNameDistinctUID i otherI &&
            checkedReason == .sameNameDistinctUID i otherI
        | _, _, _ => false)
    | _, _, _, _, _ => false
  | _ => false

def D10 : Bool :=
  unsupportedRefusal (.iverson (.rel .lt (.embed (.axis i)) (.embed (.axis k)))) .iverson &&
    unsupportedRefusal (.unaryFn .log "A" [.axis i, .axis k]) .unary &&
    acceptedNonshared && acceptedF32 && acceptedNonintegral && referenceOnlyIdentity

#guard D10

private def cyclicSnapshot : SourceSnapshot :=
  ⟨⟨[.typedTensor .f64 "A" [], .typedTensor .f64 "B" []],
    [.assign "A" [] (rhs [[.read "B" []]]),
     .assign "B" [] (rhs [[.read "A" []]])], {}, ∅⟩,
    [⟨0, .defined, []⟩, ⟨1, .output, []⟩], []⟩

def D11 : Bool :=
  match compareSource cyclicSnapshot (some [0, 1]) with
  | .ok run =>
    match run.classification, run.reference.observe.endpoint, run.oracle, run.native with
    | .referenceIncomplete .blocked, .blocked snapshot, .error oracle, .ok native =>
      run.fixtureDependencyOrder == some [0, 1] &&
        run.reference.actual.result.events.length == 0 &&
        snapshot.tensors.map (fun t => (t.declaration, t.values)) ==
          [(0, [none]), (1, [none])] &&
        snapshot.pending.length == 2 && snapshot.eligible == [] &&
        oracle.cause == .dependencyNotEarlier 1 &&
        oracle.origin == { side := .read, declaration := some 1, statement := some 0, term := some 0, factor := some 0 } &&
        run.referenceComparison.isNone &&
        (match run.profile with
        | .error (.oracleUnavailable reason) => reason == oracle
        | _ => false) &&
        (match native.legacy, native.checked with
        | .failure legacy, .sourceCompilation checked =>
          match legacy.original.error, checked.cause with
          | .compile (.cyclicDataflow legacyCause), .cyclicDataflow checkedCause =>
            legacyCause == "schedule: cyclic dataflow" && checkedCause == legacyCause &&
              legacy.phase == .compilation && legacy.original.warnings == [] &&
              checked.warnings == .unavailableAtSourceCompilation &&
              legacy.mappings == [
                ⟨"A", [{ side := .output, declaration := some 0, statement := some 0 }], none⟩,
                ⟨"B", [{ side := .output, declaration := some 1, statement := some 1 }], none⟩] &&
              checked.mappings == legacy.mappings &&
              native.source.snapshot.resolved.decls == cyclicSnapshot.resolved.decls &&
              native.source.snapshot.resolved.stmts == cyclicSnapshot.resolved.stmts &&
              (let text := renderSourceComparison (.ok run)
               (text.splitOn s!"legacy phase={repr LegacyPhase.compilation} cause={legacy.original.error}").length > 1 &&
                 (text.splitOn s!"checked sourceCompilation: cause={repr checked.cause}").length > 1 &&
                 (text.splitOn s!"warningAvailability={repr checked.warnings}").length > 1 &&
                 (text.splitOn "warnings=[]").length > 1 &&
                 (text.splitOn s!"mappings={repr checked.mappings}").length > 1 &&
                 (text.splitOn "blocked (no no-model inference)").length > 1)
          | _, _ => false
        | _, _ => false)
    | _, _, _, _ => false
  | _ => false

#guard D11

#eval match compareSource cyclicSnapshot (some [0, 1]) with
  | .error error => reprStr error
  | .ok run =>
    reprStr (run.classification, run.oracle) ++ "\n" ++
      (match run.profile with | .error error => reprStr error | .ok _ => "profile eligible") ++ "\n" ++
      (match run.native with
      | .error error => reprStr error
      | .ok native => renderLegacy native.legacy ++ "\n" ++ renderChecked native.checked)

private def preparationRetained : Bool :=
  match defaultF32Comparison with
  | .ok run =>
    match run.native with
    | .ok native =>
      match native.legacy, native.checked with
      | .failure legacy, .preparation checked =>
        match legacy.original.error, checked.original.cause with
        | .unsupportedDtype "A", .inputSignature inputCause =>
          inputCause == .dtypeMismatch "A" .f32 .f64 &&
            legacy.phase == .scheduledEvaluation &&
            legacy.original.warnings == [] && checked.original.warnings == [] &&
            legacy.mappings == [
              ⟨"Y", [{ side := .output, declaration := some 1, statement := some 0 }], none⟩] &&
            checked.mappings == [
              ⟨"Y", [{ side := .output, declaration := some 1, statement := some 0 }], some 0⟩] &&
            native.source.snapshot.resolved.decls == [.tensor "A" [], .tensor "Y" []] &&
            native.source.program.decls == defaultF32Snapshot.resolved.decls &&
            native.source.program.stmts == defaultF32Snapshot.resolved.stmts &&
            native.source.admitted.source.table.entries.map (·.elementType) == [.f32, .f32] &&
            (let text := renderSourceComparison (.ok run)
             (text.splitOn s!"legacy phase={repr LegacyPhase.scheduledEvaluation} cause={legacy.original.error}").length > 1 &&
               (text.splitOn "unsupported dtype: tensor A is declared f32").length > 1 &&
               (text.splitOn s!"checked preparation: cause=inputSignature: {repr inputCause}").length > 1 &&
               (text.splitOn "warnings=[]").length > 1 &&
               (text.splitOn s!"mappings={repr legacy.mappings}").length > 1 &&
               (text.splitOn s!"mappings={repr checked.mappings}").length > 1)
        | _, _ => false
      | _, _ => false
    | _ => false
  | _ => false

private def explicitF64Neighbor : Bool :=
  match compareSource SourceDiagnosticFixtures.scalarSnapshot (some [1]) with
  | .ok run =>
    match run.classification, run.reference.observe.endpoint, run.profile, run.native with
    | .fourLegParity, .complete snapshot, .ok profile, .ok native =>
      snapshot.tensors.map (fun t => (t.declaration, t.values)) ==
        [(0, [some 3]), (1, [some 3])] &&
        profile.actual.isSome &&
        (match run.oracle with
        | .ok oracle => oracle.tensors.map (·.values) == [[3], [3]]
        | _ => false) &&
        (match run.legacyComparison, run.checkedComparison with
        | .compared (.ok .agreement), .compared (.ok .agreement) => true
        | _, _ => false) &&
        native.source.snapshot.resolved.decls ==
          [.typedTensor .f64 "A" [], .typedTensor .f64 "Y" []] &&
        native.source.program.decls == SourceDiagnosticFixtures.scalarSnapshot.resolved.decls &&
        native.source.program.stmts == SourceDiagnosticFixtures.scalarSnapshot.resolved.stmts &&
        native.source.snapshot.inputs.map (·.values) == [[3]] &&
        (match native.legacy, native.checked with
        | .observed legacy, .observed checked mappings =>
          legacy.report.warnings == [] && checked.report.warnings == [] &&
            mappings == [
              ⟨"Y", [{ side := .output, declaration := some 1, statement := some 0 }], some 0⟩] &&
            (match legacy.outputs, checked.outputs with
            | .ok [l], .ok [c] =>
              l.metadata.tensorUID == 1 && l.metadata.declaration == 1 &&
                l.metadata.origin == { side := .declaration, declaration := some 1 } &&
                l.metadata.axes == [] && l.shape == [] &&
                c.metadata == l.metadata && c.shape == [] &&
                l.bits == #[0x4008000000000000] && c.bits == l.bits
            | _, _ => false)
        | _, _ => false)
    | _, _, _, _ => false
  | _ => false

def D12 : Bool :=
  acceptedF32 && preparationRetained && explicitF64Neighbor

#guard D12

end SourceDiagnosticAdmissionFixtures
