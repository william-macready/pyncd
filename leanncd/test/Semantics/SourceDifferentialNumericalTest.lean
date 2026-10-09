import Semantics.SourceDifferentialFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Debug LeanNCD.Semantics.Source.NativeLegs
open LeanNCD.Semantics.Source.Differential LeanNCD.Semantics.Source.NumericalProfile
open SourceAdmissionFixtures

namespace SourceDifferentialNumericalTest

private def scalarSnapshot (inputs : List ℚ) (terms : List (List Nat)) : SourceSnapshot :=
  let names := (List.range inputs.length).map fun index => s!"I{index}"
  ⟨⟨names.map (fun name => .typedTensor .f64 name []) ++ [.typedTensor .f64 "O" []],
      [.assign "O" [] (rhs (terms.map fun term =>
        term.map fun index => .read s!"I{index}" []))], {}, ∅⟩,
    (List.range inputs.length).map (fun index => ⟨index, .input, []⟩) ++
      [⟨inputs.length, .output, []⟩],
    inputs.zipIdx.map fun (value, index) => ⟨index, [], [value]⟩⟩

private def referenceCells (run : ComparisonRun) (inputs : List ℚ) (expected : ℚ) : Bool :=
  match run.reference.actual.result.outcome, run.reference.observe.endpoint,
      run.oracle, run.referenceComparison with
  | .complete .., .complete snapshot, .ok oracle, some comparison =>
    let declarations := List.range (inputs.length + 1)
    let names := (List.range inputs.length).map (fun index => s!"I{index}") ++ ["O"]
    let roles := List.replicate inputs.length TensorRole.input ++ [.output]
    let values := inputs.map (fun value => [value]) ++ [[expected]]
    run.fixtureDependencyOrder == some [inputs.length] &&
    snapshot.tensors.map (·.tensorUID) == declarations &&
    snapshot.tensors.map (·.declaration) == declarations &&
    snapshot.tensors.map (·.name) == names.map some &&
    snapshot.tensors.map (·.role) == roles &&
    snapshot.tensors.map (·.axes) == List.replicate (inputs.length + 1) [] &&
    snapshot.tensors.map (·.shape) == List.replicate (inputs.length + 1) [] &&
    snapshot.tensors.map (·.values) == values.map (List.map some) &&
    oracle.tensors.map (·.declaration) == declarations &&
    oracle.tensors.map (·.name) == names &&
    oracle.tensors.map (·.role) == roles &&
    oracle.tensors.map (·.shape) == List.replicate (inputs.length + 1) [] &&
    oracle.tensors.map (·.values) == values &&
    oracle.contributions.map (·.value) == [expected] &&
    canonicalContributions run.reference.observe.events ==
      [⟨⟨0, []⟩, ⟨inputs.length, inputs.length, []⟩, some expected⟩] &&
    (match comparison.published, comparison.collection, comparison.body with
      | .ok .agreement, .ok .agreement, .ok .agreement => true
      | _, _, _ => false)
  | _, _, _, _ => false

private def nativeCells (observation : NativeObservation) (inputBits : List UInt64)
    (expectedBits : UInt64) : Bool :=
  match observation.outputs, observation.report.env["O"]? with
  | .ok [binding], some output =>
    binding.metadata ==
      ⟨inputBits.length, inputBits.length, "O",
        { side := .declaration, declaration := some inputBits.length }, [], []⟩ &&
    binding.shape == [] && binding.bits.size == 1 && binding.bits == #[expectedBits] &&
    output.shape == [] && output.data.size == 1 &&
    output.data.map Float.toBits == #[expectedBits] &&
    observation.report.env.size == inputBits.length + 1 &&
    (inputBits.zipIdx.all fun (bits, index) =>
      match observation.report.env[s!"I{index}"]? with
      | some input =>
        input.shape == [] && input.data.size == 1 && input.data.map Float.toBits == #[bits]
      | none => false)
  | _, _ => false

private def exactProfile (run : ComparisonRun) (inputs : List ℚ)
    (inputBits : List UInt64) (expected : ℚ) (bits : UInt64) : Bool :=
  match run.classification, run.profile, run.native with
  | .fourLegParity, .ok profile, .ok native =>
    match run.oracle, native.legacy, native.checked with
    | .ok oracle, .observed legacy, .observed checked _ =>
      inputs.length == inputBits.length && referenceCells run inputs expected &&
      native.source.snapshot.inputs.map (·.values) == inputs.map (fun value => [value]) &&
      native.source.snapshot.inputs.map (·.declaration) == List.range inputs.length &&
      native.source.snapshot.inputs.map (·.shape) == List.replicate inputs.length [] &&
      profile.actual.isSome && profile.oracle == oracle &&
      (profile.values.filter (fun value => value.kind == .input)).map (·.exact) == inputs &&
      (profile.values.filter (fun value => value.kind == .input)).map (·.site) ==
        (List.range inputs.length).map (fun index =>
          { origin := { side := .input, declaration := some index }, cell := some 0 }) &&
      (profile.values.filter (fun value => value.kind == .tensorCell)).map (·.exact) ==
        inputs ++ [expected] &&
      (profile.values.filter (fun value => value.kind == .tensorCell)).map (·.bits) ==
        inputBits ++ [bits] &&
      (profile.values.filter (fun value => value.kind == .coreContribution)).map (·.exact) ==
        [expected] &&
      (profile.values.filter (fun value => value.kind == .corePublication)).map (·.exact) ==
        [expected] &&
      (profile.values.filter (fun value => value.kind == .coreAccumulator)).map (·.exact) ==
        [expected] &&
      nativeCells legacy inputBits bits && nativeCells checked inputBits bits
    | _, _, _ => false
  | _, _, _ => false

private def scalarParity (inputs : List ℚ) (terms : List (List Nat))
    (inputBits : List UInt64) (expected : ℚ) (bits : UInt64) : Bool :=
  match compareSource (scalarSnapshot inputs terms) (some [inputs.length]) with
  | .ok run => exactProfile run inputs inputBits expected bits
  | .error _ => false

def F10 : Bool :=
  identityCase [[]] 1 0x3ff0000000000000 [[([], 1)]] &&
  identityCase [] 0 0 []
where
  identityCase (terms : List (List Nat)) (expected : ℚ) (bits : UInt64)
      (fibers : List (List (List ℚ × ℚ))) : Bool :=
    let snapshot := scalarSnapshot [] terms
    snapshot.resolved.stmts == [.assign "O" [] (rhs (terms.map fun _ => []))] &&
    match compareSource snapshot (some [0]) with
    | .ok run =>
      exactProfile run [] [] expected bits &&
      (match run.oracle with
        | .ok oracle =>
          oracle.contributions.map (fun row => row.terms.map fun fiber =>
            fiber.occurrences.map fun occurrence =>
              (occurrence.reads.map (·.value), occurrence.value)) == [fibers]
        | .error _ => false)
    | .error _ => false

-- Only the supplied observation is injected; this is not a backend negative-zero receipt.
private def injectedNegativeZero : Bool :=
  match compareSource (scalarSnapshot [0, 7] [[0, 1]]) (some [2]) with
  | .ok run =>
    match run.profile, run.native with
    | .ok profile, .ok native =>
      match native.legacy with
      | .observed original =>
        match original.outputs with
        | .ok [binding] =>
          let report := { original.report with
            env := original.report.env.insert "O" ⟨[], #[Float.ofBits 0x8000000000000000]⟩ }
          let injected := observeBindings run.reference.source.admitted report
          let zeros := profile.values.filter fun value =>
            value.kind == .tensorCell && value.site.origin.declaration == some 2
          exactProfile run [0, 7] [0, 0x401c000000000000] 0 0 &&
          injected.outputs == .ok [{ binding with bits := #[0x8000000000000000] }] &&
          injected.report.warnings == original.report.warnings &&
          (match injected.report.env["O"]? with
            | some output =>
              output.shape == [] && output.data.size == 1 &&
              output.data.map Float.toBits == #[0x8000000000000000]
            | none => false) &&
          (match zeros with
            | [zero] =>
              zero.site.coordinate == [] && zero.exact == 0 && zero.integer.value == 0 &&
              zero.bits == 0 &&
              compareBits zero.integer 0x8000000000000000 ==
                ⟨0, 0, 0x8000000000000000, 0⟩ &&
              (compareBits zero.integer 0x8000000000000000).agrees &&
              !(compareBits zero.integer 1).agrees
            | _ => false) &&
          (match compareNative profile injected with
            | .ok .agreement => true
            | _ => false)
        | _ => false
      | _ => false
    | _, _ => false
  | .error _ => false

def F11 : Bool :=
  scalarParity [-3, 7] [[0, 1]]
    [0xc008000000000000, 0x401c000000000000] (-21) 0xc035000000000000 &&
  scalarParity [0, 7] [[0, 1]] [0, 0x401c000000000000] 0 0 &&
  ([(1048576, 0x4130000000000000), (1048575, 0x412ffffe00000000),
    (-1048576, 0xc130000000000000), (-1048575, 0xc12ffffe00000000),
    (1, 0x3ff0000000000000), (-1, 0xbff0000000000000), (0, 0)] :
      List (ℚ × UInt64)).all (fun (value, bits) =>
        scalarParity [value] [[0]] [bits] value bits) &&
  injectedNegativeZero

private def envelopeNeighbour (inputs : List ℚ) (terms : List (List Nat))
    (inputBits : List UInt64) (expected : ℚ) (bits : UInt64)
    (products subsets prefixes bounds : List ℚ) : Bool :=
  match compareSource (scalarSnapshot inputs terms) (some [inputs.length]) with
  | .ok run =>
    exactProfile run inputs inputBits expected bits &&
    (match run.profile with
      | .ok profile =>
        (profile.values.filter (fun value => value.kind == .partialProduct)).map (·.exact) ==
          products &&
        (profile.values.filter (fun value => value.kind == .subsetProductBound)).map (·.exact) ==
          subsets &&
        (profile.values.filter (fun value => value.kind == .partialStatement)).map (·.exact) ==
          prefixes &&
        (profile.values.filter (fun value => value.kind == .statementAbsoluteBound)).map (·.exact) ==
          bounds
      | .error _ => false)
  | .error _ => false

private def envelopeRefusal (inputs : List ℚ) (terms : List (List Nat))
    (expected : ℚ) (nativeBits : Option (List UInt64 × UInt64))
    (occurrences : List (List ℚ × ℚ)) (site : Site) (kind : ValueKind)
    (overshoot : ℚ) : Bool :=
  let reason : Unsupported := .outsideEnvelope site kind overshoot 1048576
  match compareSource (scalarSnapshot inputs terms) (some [inputs.length]) with
  | .ok run =>
    referenceCells run inputs expected &&
    (match run.profile, run.classification with
      | .error actual, .unsupportedNumericalProfile classified =>
        actual == reason && classified == reason
      | _, _ => false) &&
    (if kind == .input then
      match run.legacyComparison, run.checkedComparison with
      | .unavailable .legNotObserved, .unavailable .legNotObserved => true
      | _, _ => false
    else
      match run.legacyComparison, run.checkedComparison with
      | .unavailable (.profile left), .unavailable (.profile right) =>
        left == reason && right == reason
      | _, _ => false) &&
    (match run.oracle with
      | .ok oracle =>
        oracle.contributions.map (fun row => row.terms.flatMap fun fiber =>
          fiber.occurrences.map fun occurrence =>
            (occurrence.reads.map (·.value), occurrence.value)) == [occurrences]
      | .error _ => false) &&
    (match run.native with
      | .ok native =>
        native.source.snapshot.inputs.map (·.values) == inputs.map (fun value => [value]) &&
        native.source.snapshot.inputs.map (·.declaration) == List.range inputs.length &&
        native.source.snapshot.inputs.map (·.shape) == List.replicate inputs.length [] &&
        if kind == .input then
          match native.inputs, native.legacy, native.checked with
          | .error input, .unavailable (.input legacy), .unavailable (.input checked) =>
            nativeBits.isNone && input == reason && legacy == reason && checked == reason
          | _, _, _ => false
        else
          match nativeBits, native.inputs, native.legacy, native.checked with
          | some (inputBits, bits), .ok _, .observed legacy, .observed checked _ =>
            inputs.length == inputBits.length &&
            nativeCells legacy inputBits bits && nativeCells checked inputBits bits
          | _, _, _, _ => false
      | .error _ => false)
  | .error _ => false

def F12 : Bool :=
  limit == 1048576 &&
  envelopeNeighbour [1024, 1024] [[0, 1]]
    [0x4090000000000000, 0x4090000000000000] 1048576 0x4130000000000000
    [1024, 1048576] [1024, 1048576, 1048576] [1048576]
    [1048576, 1048576] &&
  envelopeNeighbour [-1024, 1024] [[0, 1]]
    [0xc090000000000000, 0x4090000000000000] (-1048576) 0xc130000000000000
    [-1024, -1048576] [1024, 1048576, 1048576] [-1048576]
    [1048576, 1048576] &&
  envelopeNeighbour [0, 1024, 1024] [[0, 1, 2]]
    [0, 0x4090000000000000, 0x4090000000000000] 0 0
    [0, 0, 0] [1, 1024, 1048576, 1048576] [0] [0, 0] &&
  envelopeNeighbour [524288, -524288] [[0], [1]]
    [0x4120000000000000, 0xc120000000000000] 0 0
    [524288, -524288] [524288, 524288, 524288, 524288] [524288, 0]
    [524288, 1048576, 1048576] &&
  envelopeRefusal [1048577] [[0]] 1048577 none
    [([1048577], 1048577)]
    { origin := { side := .input, declaration := some 0 }, cell := some 0 }
    .input 1048577 &&
  envelopeRefusal [-1048577] [[0]] (-1048577) none
    [([-1048577], -1048577)]
    { origin := { side := .input, declaration := some 0 }, cell := some 0 }
    .input (-1048577) &&
  envelopeRefusal [1024, 1025] [[0, 1]] 1049600
    (some ([0x4090000000000000, 0x4090040000000000], 0x4130040000000000))
    [([1024, 1025], 1049600)]
    { origin := { side := .read, declaration := some 1, statement := some 0, term := some 0, factor := some 1 } }
    .partialProduct 1049600 &&
  envelopeRefusal [1048576, 2, 0] [[0, 1, 2]] 0
    (some ([0x4130000000000000, 0x4000000000000000, 0], 0))
    [([1048576, 2, 0], 0)]
    { origin := { side := .read, declaration := some 1, statement := some 0, term := some 0, factor := some 1 } }
    .partialProduct 2097152 &&
  envelopeRefusal [0, 1048576, 2] [[0, 1, 2]] 0
    (some ([0, 0x4130000000000000, 0x4000000000000000], 0))
    [([0, 1048576, 2], 0)]
    { origin := { side := .read, declaration := some 2, statement := some 0, term := some 0, factor := some 2 } }
    .subsetProductBound 2097152 &&
  envelopeRefusal [1048576, -1048576] [[0], [1]] 0
    (some ([0x4130000000000000, 0xc130000000000000], 0))
    [([1048576], 1048576), ([-1048576], -1048576)]
    { origin := { side := .read, statement := some 0, term := some 1 } }
    .statementAbsoluteBound 2097152

#guard F10
#guard F11
#guard F12

#eval ("F10 direct AST empty-product one / empty-term-list zero", F10)
#eval ("F11 actual negative/zero profile; INJECTED negative-zero comparison only", F11)
#eval ("F12 actual exact boundary and typed intermediate-envelope refusals", F12)

end SourceDifferentialNumericalTest
