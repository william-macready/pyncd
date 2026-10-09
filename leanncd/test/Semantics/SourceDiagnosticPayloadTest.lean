import Semantics.SourceDiagnosticFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Debug LeanNCD.Semantics.Source.NumericalProfile
open SourceAdmissionFixtures SourceDiagnosticFixtures

namespace SourceDiagnosticPayloadTest

private def outputPayloadSnapshot (slots : List LHSSlot) : SourceSnapshot :=
  { vectorSnapshot with
    resolved := { vectorSnapshot.resolved with
      stmts := stmts.take 2 ++ [.assign "A" slots (rhs [])] }
    specs := specs.map fun spec =>
      if spec.declaration == 3 then { spec with role := .defined } else spec
    inputs := inputs.filter fun binding => binding.declaration != 3 }

private def readPayloadSnapshot : SourceSnapshot :=
  { vectorSnapshot with resolved := { vectorSnapshot.resolved with
      stmts := stmts.take 2 ++ [.assign "Y" [.free i] (rhs
        [[.read "B" [.axis i]],
         [.read "B" [.axis i], .read "A" [.axis i, .axis i, .axis e]]])] } }

private def domainPayload (snapshot : SourceSnapshot) (stage : SourceStage)
    (origin : SourceOrigin) (uid : UID) (expected actual : Nat) : Bool :=
  match sourceDebug snapshot with
  | .error (.admission diagnostic) =>
    diagnostic.stage == stage && diagnostic.origin == origin &&
    (match diagnostic.cause with
      | .domain found wanted got => found == uid && wanted == expected && got == actual
      | _ => false) &&
    renderSourceDiagnostic diagnostic ==
      s!"admission: stage={repr stage} origin={repr origin} cause={repr (SourceCause.domain uid expected actual)}" &&
    renderSourceDebug (.error (.admission diagnostic)) == renderSourceDiagnostic diagnostic
  | _ => false

def D1 : Bool :=
  domainPayload (outputPayloadSnapshot [.free i, .free i, .free k]) .output
    { side := .output, declaration := some 3, statement := some 2, slot := some 1 }
    7 3 2 &&
  domainPayload readPayloadSnapshot .read
    { side := .read, declaration := some 3, statement := some 2,
      term := some 1, factor := some 1, slot := some 1 }
    7 3 2 &&
  (match sourceDebug (outputPayloadSnapshot [.free i, .free k, .free e]) with
    | .error (.admission diagnostic) =>
      let origin : SourceOrigin :=
        { side := .output, declaration := some 3, statement := some 2, slot := some 2 }
      diagnostic.stage == .output && diagnostic.origin == origin &&
      (match diagnostic.cause with
        | .rank expected actual => expected == 2 && actual == 3
        | _ => false) &&
      renderSourceDiagnostic diagnostic ==
        s!"admission: stage={repr SourceStage.output} origin={repr origin} cause={repr (SourceCause.rank 2 3)}"
    | _ => false) &&
  (match sourceDebug (outputPayloadSnapshot [.free i, .free k]) with
    | .ok run => match run.actual.result.outcome with
      | .complete .. => true
      | _ => false
    | .error _ => false)

private def completePayloadSnapshot : SourceSnapshot :=
  { vectorSnapshot with
    resolved := { vectorSnapshot.resolved with
      decls := vectorSnapshot.resolved.decls ++
        [.typedTensor .f64 "Unwritten" [i], .typedTensor .f64 "Scalar" []] }
    specs := specs ++ [⟨8, .defined, [2]⟩, ⟨9, .defined, []⟩] }

def D2 : Bool :=
  match sourceDebug completePayloadSnapshot,
      SourceProgramFixtures.observe completePayloadSnapshot with
  | .ok run, .ok fixtureProjection =>
    match run.actual.result.outcome, run.observe.endpoint with
    | .complete .., .complete snapshot =>
      snapshot.tensors.map (fun t =>
        (t.tensorUID, t.declaration, t.role, t.shape, t.values)) ==
        [(0, 3, .input, [2, 3], [1, 2, 3, 4, 5, 6].map some),
         (1, 4, .input, [2], [some 10, some 20]),
         (2, 5, .output, [2], [some 16, some 35]),
         (3, 6, .input, [0], []),
         (4, 7, .defined, [2, 2], [some 1, some 0, some 0, some 1]),
         (5, 8, .defined, [2], [some 0, some 0]),
         (6, 9, .defined, [], [some 0])] &&
      snapshot.tensors.map (fun t => t.axes.map Axis.uid) ==
        [[7, 3], [7], [7], [11], [7, 7], [7], []] &&
      snapshot.accumulators ==
        [(⟨2, 5, [0]⟩, 16), (⟨2, 5, [1]⟩, 35),
         (⟨4, 7, [0, 0]⟩, 1), (⟨4, 7, [0, 1]⟩, 0),
         (⟨4, 7, [1, 0]⟩, 0), (⟨4, 7, [1, 1]⟩, 1),
         (⟨5, 8, [0]⟩, 0), (⟨5, 8, [1]⟩, 0), (⟨6, 9, []⟩, 0)] &&
      snapshot.pending.isEmpty && snapshot.unpublished.isEmpty &&
      snapshot.eligible.isEmpty && snapshot.readiness.isEmpty &&
      canonicalContributions run.observe.events ==
        [⟨⟨0, [(7, 0)]⟩, ⟨2, 5, [0]⟩, some 16⟩,
         ⟨⟨0, [(7, 1)]⟩, ⟨2, 5, [1]⟩, some 35⟩,
         ⟨⟨1, [(7, 0)]⟩, ⟨4, 7, [0, 0]⟩, some 1⟩,
         ⟨⟨1, [(7, 1)]⟩, ⟨4, 7, [1, 1]⟩, some 1⟩,
         ⟨⟨2, [(7, 0)]⟩, ⟨2, 5, [0]⟩, some 0⟩,
         ⟨⟨2, [(7, 1)]⟩, ⟨2, 5, [1]⟩, some 0⟩] &&
      (run.observe.events.filterMap fun event => match event with
        | .publication address value => some (address, value)
        | _ => none) == snapshot.accumulators &&
      run.observe.events.length == 15 &&
      run.observe.events == run.actual.result.events.map (observeEvent run.source.admitted) &&
      fixtureProjection.kind == .complete && fixtureProjection.events == 15 &&
      fixtureProjection.tensors.map (fun t => (t.uid, t.declaration, t.shape, t.values)) ==
        snapshot.tensors.map (fun t => (t.tensorUID, t.declaration, t.shape, t.values)) &&
      (List.finRange run.source.admitted.statements.length).map (fun index =>
        let original := run.source.originalEquiv index
        let localTag := run.source.originalToLocal original
        (original.val, localTag.1.val, localTag.2.val)) ==
        [(0, 2, 0), (1, 4, 0), (2, 2, 1)] &&
      renderSourceDebug (.ok run) ==
        s!"complete (actual reached execution retained in SourceRun)\nendpoint={repr run.observe.endpoint}\nevents={repr run.observe.events}"
    | _, _ => false
  | _, _ => false

private theorem completePayload_globalModel (run : SourceRun)
    (_reached : sourceDebug completePayloadSnapshot = .ok run) (c complete)
    (h : run.actual.result.outcome = .complete c complete) :
    run.source.admitted.GlobalModels (r := RationalReference.registry) run.actual.input
      ((elaborateSource run.source.admitted).finalStore c complete) :=
  sourceResult_globalModel run.source.admitted run.actual c complete h

-- Renderer protocol only: this injected observation has no Execution/no-model witness.
def D3 : Bool :=
  match sourceDebug scalarSnapshot (some 0) with
  | .error _ => false
  | .ok run =>
    match run.observe.endpoint with
    | .exhausted before (some 0) 0 =>
      match before.readiness with
      | [.ready occurrence (some readyValue)] =>
        let preFailure := { before with readiness := [.ready occurrence none] }
        let injected : ExecutionObservation :=
          ⟨.failed occurrence preFailure, [.undefined occurrence]⟩
        let label := "UNREACHED renderer-protocol injection; no Execution or no-model proof\n"
        readyValue == 3 &&
        occurrence.key == ⟨0, []⟩ && occurrence.targetLocal == 0 &&
        occurrence.destination == ⟨1, 1, []⟩ &&
        occurrence.origin == { side := .output, declaration := some 1, statement := some 0 } &&
        occurrence.terms.map (fun term => (term.origin, term.factors)) ==
          [({ side := .read, statement := some 0, term := some 0 },
            [({ side := .read, declaration := some 0, statement := some 0,
                term := some 0, factor := some 0 }, [])])] &&
        occurrence.terms.all (fun term =>
          term.value == .unobserved .noTermEvaluationHook &&
          term.contractedAssignments == .unobserved .noTermEvaluationHook) &&
        before.tensors.map (·.values) == [[some 3], [none]] &&
        before.accumulators == [(⟨1, 1, []⟩, 0)] &&
        before.pending == [.occurrence occurrence] &&
        before.unpublished == [⟨1, 1, []⟩] &&
        before.eligible == [.occurrence occurrence] &&
        run.observe.events.isEmpty &&
        (match injected.endpoint with
          | .failed failed snapshot =>
            failed == occurrence && snapshot.tensors == before.tensors &&
            snapshot.accumulators == before.accumulators &&
            snapshot.pending == before.pending && snapshot.unpublished == before.unpublished &&
            snapshot.eligible == before.eligible &&
            snapshot.readiness == [.ready failed none] &&
            !(snapshot.readiness.any fun readiness => match readiness with
              | .unavailable own _ _ => own.key == failed.key
              | .ready _ _ => false)
          | _ => false) &&
        injected.events == [.undefined occurrence] &&
        label ++ renderExecutionObservation injected ==
          label ++ s!"failed (actual endpoint; ready undefinedness, not missing reads)\nendpoint={repr (EndpointObservation.failed occurrence preFailure)}\nevents={repr ([EventObservation.undefined occurrence])}"
      | _ => false
    | _ => false

private def profileSnapshot (values : List ℚ) (terms : List (List Nat)) : SourceSnapshot :=
  let names := (List.range values.length).map fun index => s!"I{index}"
  ⟨⟨names.map (fun name => .typedTensor .f64 name []) ++ [.typedTensor .f64 "O" []],
      [.assign "O" [] (rhs (terms.map fun term =>
        term.map fun index => .read s!"I{index}" []))], {}, ∅⟩,
    (List.range values.length).map (fun index => ⟨index, .input, []⟩) ++
      [⟨values.length, .output, []⟩],
    values.zipIdx.map fun (value, index) => ⟨index, [], [value]⟩⟩

private def profileNeighbour (inputs : List ℚ) (terms : List (List Nat))
    (products subsets statementPrefixes statementBounds : List ℚ) (expected : ℚ) : Bool :=
  match sourceDebug (profileSnapshot inputs terms) with
  | .error _ => false
  | .ok run =>
    match run.actual.result.outcome, Oracle.run run.source.admitted (some [inputs.length]) with
    | .complete .., .ok oracle =>
      match checkRunProfile run (.ok oracle) with
      | .error _ => false
      | .ok profile =>
        profile.actual.isSome &&
        profile.oracle == oracle &&
        (profile.values.filter (fun v => v.kind == .partialProduct)).map (·.exact) == products &&
        (profile.values.filter (fun v => v.kind == .subsetProductBound)).map (·.exact) == subsets &&
        (profile.values.filter (fun v => v.kind == .partialStatement)).map (·.exact) ==
          statementPrefixes &&
        (profile.values.filter (fun v => v.kind == .statementAbsoluteBound)).map (·.exact) ==
          statementBounds &&
        (profile.values.filter (fun v => v.kind == .coreContribution)).map (·.exact) == [expected] &&
        (profile.values.filter (fun v => v.kind == .corePublication)).map (·.exact) == [expected] &&
        (profile.values.filter (fun v => v.kind == .coreAccumulator)).map (·.exact) == [expected] &&
        canonicalContributions run.observe.events ==
          [⟨⟨0, []⟩, ⟨inputs.length, inputs.length, []⟩, some expected⟩] &&
        run.observe.endpoint.snapshot.tensors.map (·.values) ==
          inputs.map (fun value => [some value]) ++ [[some expected]]
    | _, _ => false

private def zeroFinalHazard (inputs : List ℚ) (terms : List (List Nat))
    (occurrences : List (List ℚ × ℚ)) (site : Site) (kind : ValueKind) : Bool :=
  match sourceDebug (profileSnapshot inputs terms) with
  | .error _ => false
  | .ok run =>
    match run.actual.result.outcome, Oracle.run run.source.admitted (some [inputs.length]) with
    | .complete .., .ok oracle =>
      oracle.contributions.map (·.value) == [0] &&
      oracle.contributions.map (fun row =>
        row.terms.flatMap fun fiber => fiber.occurrences.map fun occurrence =>
          (occurrence.reads.map (·.value), occurrence.value)) == [occurrences] &&
      canonicalContributions run.observe.events ==
        [⟨⟨0, []⟩, ⟨inputs.length, inputs.length, []⟩, some 0⟩] &&
      run.observe.endpoint.snapshot.tensors.map (·.values) ==
        inputs.map (fun value => [some value]) ++ [[some 0]] &&
      (match checkRunProfile run (.ok oracle) with
        | .error (.outsideEnvelope found actualKind value maximum) =>
          found == site && actualKind == kind && value == 2097152 && maximum == 1048576
        | _ => false)
    | _, _ => false

private def supplementaryProfileNeighbours : Bool :=
  limit == 1048576 &&
  profileNeighbour [1024, 1024] [[0, 1]]
    [1024, 1048576] [1024, 1048576, 1048576] [1048576]
    [1048576, 1048576] 1048576 &&
  profileNeighbour [-1024, 1024] [[0, 1]]
    [-1024, -1048576] [1024, 1048576, 1048576] [-1048576]
    [1048576, 1048576] (-1048576) &&
  profileNeighbour [0, 1024, 1024] [[0, 1, 2]]
    [0, 0, 0] [1, 1024, 1048576, 1048576] [0] [0, 0] 0 &&
  profileNeighbour [524288, -524288] [[0], [1]]
    [524288, -524288] [524288, 524288, 524288, 524288]
    [524288, 0] [524288, 1048576, 1048576] 0

private def supplementaryProfileHazards : Bool :=
  zeroFinalHazard [1048576, 2, 0] [[0, 1, 2]]
    [([1048576, 2, 0], 0)]
    { origin := { side := .read, declaration := some 1, statement := some 0, term := some 0, factor := some 1 } } .partialProduct &&
  zeroFinalHazard [0, 1048576, 2] [[0, 1, 2]]
    [([0, 1048576, 2], 0)]
    { origin := { side := .read, declaration := some 2, statement := some 0, term := some 0, factor := some 2 } } .subsetProductBound &&
  zeroFinalHazard [1048576, -1048576] [[0], [1]]
    [([1048576], 1048576), ([-1048576], -1048576)]
    { origin := { side := .read, statement := some 0, term := some 1 } }
    .statementAbsoluteBound

private def supplementaryCoreAvailable : Bool :=
  (match sourceDebug (profileSnapshot [1048577] [[0]]) with
    | .error _ => false
    | .ok run =>
      match run.actual.result.outcome with
      | .complete .. =>
        run.observe.endpoint.snapshot.tensors.map (·.values) ==
          [[some 1048577], [some 1048577]] &&
        (match checkRunProfile run (Oracle.run run.source.admitted (some [1])) with
          | .error (.outsideEnvelope site .input value maximum) =>
            site == { origin := { side := .input, declaration := some 0 }, cell := some 0 } &&
            value == 1048577 && maximum == 1048576
          | _ => false)
      | _ => false) &&
  (match sourceDebug (profileSnapshot [1 / 3] [[0]]) with
    | .error _ => false
    | .ok run =>
      match run.actual.result.outcome with
      | .complete .. =>
        run.observe.endpoint.snapshot.tensors.map (·.values) ==
          [[some (1 / 3)], [some (1 / 3)]] &&
        canonicalContributions run.observe.events ==
          [⟨⟨0, []⟩, ⟨1, 1, []⟩, some (1 / 3)⟩] &&
        (match checkRunProfile run (Oracle.run run.source.admitted (some [1])) with
          | .error (.nonIntegral site .input numerator denominator) =>
            site == { origin := { side := .input, declaration := some 0 }, cell := some 0 } &&
            numerator == 1 && denominator == 3
          | _ => false)
      | _ => false)

private def supplementaryExactBits : Bool :=
  match checkValue {} .tensorCell (-1048576), checkValue {} .tensorCell (-3),
      checkValue {} .tensorCell 0 with
  | .ok boundary, .ok negative, .ok zero =>
    boundary.bits == 0xc130000000000000 &&
    negative.bits == 0xc008000000000000 &&
    (compareBits boundary.integer 0xc130000000000000).agrees &&
    (compareBits negative.integer 0xc008000000000000).agrees &&
    !(compareBits negative.integer 0xc008000000000001).agrees &&
    compareBits zero.integer 0x8000000000000000 ==
      ⟨0, 0, 0x8000000000000000, 0⟩ &&
    (compareBits zero.integer 0x8000000000000000).agrees &&
    (compareBits zero.integer 0).agrees &&
    !(compareBits zero.integer 1).agrees
  | _, _, _ => false

#guard D1
#guard D2
#guard D3

-- Supplementary F11/F12-style witnesses, not named F11/F12 completion receipts.
#guard supplementaryProfileNeighbours
#guard supplementaryProfileHazards
#guard supplementaryCoreAvailable
#guard supplementaryExactBits

end SourceDiagnosticPayloadTest
