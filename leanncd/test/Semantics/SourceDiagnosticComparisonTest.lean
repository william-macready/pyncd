import Semantics.SourceDiagnosticFixtures
import LeanNCD.Semantics.Source.Permutation

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Debug
open LeanNCD.Semantics.Source.Differential
open LeanNCD.Semantics.Source.NativeLegs
open SourceAdmissionFixtures SourceDiagnosticFixtures

namespace SourceDiagnosticComparisonTest

private def j : AxisSpec := ⟨"j", 19, .nat⟩

private def matrixSnapshot : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis k (some 3), .axis j (some 4),
      .typedTensor .f64 "W" [i, k], .typedTensor .f64 "X" [k, j],
      .typedTensor .f64 "Y" [i, j], .typedTensor .f64 "Z" [i, j]],
    [.assign "Y" [.free i, .free j]
      (rhs [[.read "W" [.axis i, .axis k], .read "X" [.axis k, .axis j]]]),
     .assign "Z" [.free i, .free j] (rhs [[.read "Y" [.axis i, .axis j]]])],
    {}, ∅⟩,
    [⟨3, .input, [2, 3]⟩, ⟨4, .input, [3, 4]⟩,
     ⟨5, .output, [2, 4]⟩, ⟨6, .output, [2, 4]⟩],
    [⟨3, [2, 3], [1, 2, 3, 4, 5, 6]⟩,
     ⟨4, [3, 4], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]⟩]⟩

private def matrixValues : List (Option ℚ) :=
  [38, 44, 50, 56, 83, 98, 113, 128].map some

private def matrixBits : Array UInt64 :=
  #[0x4043000000000000, 0x4046000000000000, 0x4049000000000000,
    0x404c000000000000, 0x4054c00000000000, 0x4058800000000000,
    0x405c400000000000, 0x4060000000000000]

private def injectedBits : Array UInt64 :=
  #[0x4043000000000000, 0x4046000000000000, 0x4049000000000000,
    0x404c000000000000, 0x4054c00000000000, 0x4058800000000000,
    0x405c800000000000, 0x4060000000000000]

-- The altered compared observations below are protocol injections, not backend bug receipts.
def D7 : Bool :=
  match compareSource matrixSnapshot (some [5, 6]) with
  | .ok run =>
    match run.classification, run.profile, run.native with
    | .fourLegParity, .ok profile, .ok native =>
      match native.legacy, native.checked,
          outputObservations run.reference.observe.endpoint.snapshot.tensors with
      | .observed original, .observed checked _, [y, z] =>
        match original.outputs, checked.outputs with
        | .ok [nativeY, nativeZ], .ok checkedOutputs =>
          let changed := { y with values := [38, 44, 50, 56, 83, 98, 114, 128].map some }
          let report := { original.report with
            env := original.report.env.insert "Y" ⟨[2, 4], injectedBits.map Float.ofBits⟩ }
          let injected := observeBindings run.reference.source.admitted report
          let difference := compareNative profile injected
          let injectedRun := { run with
            native := .ok { native with legacy := .observed injected }
            legacyComparison := .compared difference }
          let text := renderSourceComparison (.ok injectedRun)
          y.tensorUID == 2 && y.declaration == 5 && y.shape == [2, 4] &&
          y.axes.map Axis.uid == [7, 19] && y.values == matrixValues &&
          z.tensorUID == 3 && z.declaration == 6 && z.values == matrixValues &&
          nativeY.bits == matrixBits && nativeZ.bits == matrixBits &&
          checkedOutputs == [nativeY, nativeZ] &&
          injected.outputs == .ok [{ nativeY with bits := injectedBits }, nativeZ] &&
          compareTensors [z, y] [z, changed] ==
            .ok (.disagreement (.cell ⟨2, 5, [1, 2]⟩ (some 113) (some 114))) &&
          (match difference with
          | .ok (.disagreement (.cell binding coordinate expected bits)) =>
            binding == nativeY.metadata &&
            binding.tensorUID == 2 && binding.declaration == 5 &&
            binding.origin == { side := .declaration, declaration := some 5 } &&
            coordinate == [1, 2] &&
            expected.kind == .tensorCell && expected.exact == 113 &&
            expected.integer.value == 113 &&
            expected.site.origin.declaration == some 5 &&
            expected.site.coordinate == [1, 2] &&
            expected.bits == 0x405c400000000000 &&
            bits == ⟨0x405c400000000000, 0x405c400000000000,
              0x405c800000000000, 0x405c800000000000⟩ &&
            Float.ofBits bits.expectedOriginalBits == (113 : Float) &&
            (Float.ofBits bits.observedOriginalBits).toBits == 0x405c800000000000 &&
            Float.ofBits bits.observedOriginalBits == (114 : Float)
          | _ => false) &&
          (match injectedRun.classification with | .nativeDiscrepancy => true | _ => false) &&
          (text.splitOn "coordinate").length > 1 &&
          (text.splitOn "[1, 2]").length > 1 &&
          (text.splitOn s!"expectedOriginalBits := {(0x405c400000000000 : UInt64)}").length > 1 &&
          (text.splitOn s!"observedOriginalBits := {(0x405c800000000000 : UInt64)}").length > 1
        | _, _ => false
      | _, _, _ => false
    | _, _, _ => false
  | .error _ => false

def D8 : Bool :=
  match compareSource matrixSnapshot (some [5, 6]) with
  | .ok run =>
    match run.classification, run.profile, run.native with
    | .fourLegParity, .ok profile, .ok native =>
      match native.legacy, outputObservations run.reference.observe.endpoint.snapshot.tensors with
      | .observed original, [y, z] =>
        match original.outputs with
        | .ok [nativeY, nativeZ] =>
          let prefixTensor := { y with shape := [2, 3], values := y.values.take 6 }
          let reshaped := { y with shape := [4, 2] }
          let short := { y with values := y.values.take 7 }
          let wrong := { y with values := List.replicate 8 (some 0) }
          let laterShape := { z with shape := [4, 2] }
          let laterShort := { z with values := z.values.take 7 }
          let extra := { z with tensorUID := 4, declaration := 7, name := some "Ghost" }
          let changedY := { nativeY with bits := Array.replicate 8 0 }
          let prefixNativeY :=
            { nativeY with shape := [2, 3], bits := (nativeY.bits.toList.take 6).toArray }
          let shapedZ := { nativeZ with shape := [4, 2] }
          let shortZ := { nativeZ with bits := (nativeZ.bits.toList.take 7).toArray }
          let extraMetadata := { nativeZ.metadata with
            tensorUID := 4
            declaration := 7
            name := "Ghost"
            origin := { side := .declaration, declaration := some 7 } }
          let extraNative := { nativeZ with metadata := extraMetadata }
          let missingReport := { original.report with env := original.report.env.erase "Z" }
          let extraReport := { original.report with
            env := original.report.env.insert "Ghost" ⟨[], #[Float.ofBits 0x3ff0000000000000]⟩ }
          let issues : List BindingIssue :=
            [.shape nativeZ.metadata [2, 4] [4, 2] 8 8]
          original.report.env.contains "W" && original.report.env.contains "X" &&
          (observeBindings run.reference.source.admitted original.report).outputs ==
            .ok [nativeY, nativeZ] &&
          (observeBindings run.reference.source.admitted missingReport).outputs ==
            .error [.missingOutput nativeZ.metadata] &&
          (observeBindings run.reference.source.admitted extraReport).outputs ==
            .error [.extraOutput "Ghost" [] 1] &&
          compareTensors [y] [prefixTensor] == .ok (.disagreement (.shape y prefixTensor)) &&
          compareTensors [y] [reshaped] == .ok (.disagreement (.shape y reshaped)) &&
          compareTensors [y] [short] == .ok (.disagreement (.length y short)) &&
          compareTensors [short] [short] == .error ⟨.left, .bufferLength short 8 7⟩ &&
          compareTensors [reshaped] [reshaped] == .error ⟨.left, .shapeMetadata reshaped⟩ &&
          compareTensors [z, y] [laterShape, wrong] ==
            .ok (.disagreement (.shape z laterShape)) &&
          compareTensors [y, z] [wrong, laterShort] ==
            .ok (.disagreement (.length z laterShort)) &&
          compareTensors [y, z] [wrong] == .ok (.disagreement (.missing z)) &&
          compareTensors [y, z] [wrong, z, extra] == .ok (.disagreement (.extra extra)) &&
          compareTensors [y, z] [y, z, z] == .error ⟨.right, .duplicateTensor 3⟩ &&
          compareTensors (outputObservations run.reference.observe.endpoint.snapshot.tensors)
            [z, y] == .ok .agreement &&
          (match compareNative profile { original with outputs := .ok [prefixNativeY, nativeZ] } with
          | .ok (.disagreement (.shape expected actual count)) =>
            expected == nativeY.metadata && actual.shape == [2, 3] &&
            actual.bits.toList == matrixBits.toList.take 6 && count == 8
          | _ => false) &&
          (match compareNative profile { original with outputs := .ok [changedY, shapedZ] } with
          | .ok (.disagreement (.shape expected actual count)) =>
            expected == nativeZ.metadata && actual == shapedZ && count == 8
          | _ => false) &&
          (match compareNative profile { original with outputs := .ok [changedY, shortZ] } with
          | .ok (.disagreement (.length expected actual count)) =>
            expected == nativeZ.metadata && actual == shortZ && count == 8
          | _ => false) &&
          (match compareNative profile { original with outputs := .ok [changedY] } with
          | .ok (.disagreement (.missing expected)) => expected == nativeZ.metadata
          | _ => false) &&
          (match compareNative profile { original with outputs := .ok [extraNative, nativeZ, changedY] } with
          | .ok (.disagreement (.extra actual)) => actual == extraNative
          | _ => false) &&
          (match compareNative profile { original with outputs := .error issues } with
          | .ok (.disagreement (.bindingIssues actual)) => actual == issues
          | _ => false) &&
          (match compareNative profile { original with outputs := .ok [nativeY, nativeZ, nativeZ] } with
          | .error (.duplicateBinding uid) => uid == 3
          | _ => false)
        | .error _ => false
        | .ok _ => false
      | _, _ => false
    | _, _, _ => false
  | .error _ => false

private def interleaved : SourceSnapshot :=
  { vectorSnapshot with resolved := { vectorSnapshot.resolved with stmts :=
    [.assign "Diagonal" [.free i, .free i] (rhs []),
     .assign "Y" [.free i] (rhs [[.read "B" [.axis i]]]),
     .assign "Diagonal" [.free i, .free i] (rhs [[]]),
     .assign "Y" [.free i] (rhs [[.read "B" [.axis i], .read "B" [.axis i]]])] } }

private def expectedY (statement localIndex coordinate factors : Nat) : OccurrenceObservation :=
  ⟨⟨statement, [(7, coordinate)]⟩, localIndex, ⟨2, 5, [coordinate]⟩,
    { side := .output, declaration := some 5, statement := some statement },
    [⟨{ side := .read, statement := some statement, term := some 0 },
      (List.range factors).map fun factor =>
        let origin : SourceOrigin :=
          { side := .read, declaration := some 4, statement := some statement,
            term := some 0, factor := some factor }
        (origin, [({ origin with slot := some 0 }, 7)]),
      [], .unobserved .noTermEvaluationHook, .unobserved .noTermEvaluationHook⟩]⟩

private def expectedContributions : List ContributionObservation :=
  [⟨⟨0, [(7, 0)]⟩, ⟨4, 7, [0, 0]⟩, some 0⟩,
   ⟨⟨0, [(7, 1)]⟩, ⟨4, 7, [1, 1]⟩, some 0⟩,
   ⟨⟨1, [(7, 0)]⟩, ⟨2, 5, [0]⟩, some 10⟩,
   ⟨⟨1, [(7, 1)]⟩, ⟨2, 5, [1]⟩, some 20⟩,
   ⟨⟨2, [(7, 0)]⟩, ⟨4, 7, [0, 0]⟩, some 1⟩,
   ⟨⟨2, [(7, 1)]⟩, ⟨4, 7, [1, 1]⟩, some 1⟩,
   ⟨⟨3, [(7, 0)]⟩, ⟨2, 5, [0]⟩, some 100⟩,
   ⟨⟨3, [(7, 1)]⟩, ⟨2, 5, [1]⟩, some 400⟩]

def D9 : Bool :=
  match Debug.sourceDebug interleaved, SourceProgramFixtures.observe interleaved with
  | .ok before, .ok whole =>
    let permutation := permuteStatements before.source.admitted
      { toFun := Fin.rev, invFun := Fin.rev,
        left_inv := Fin.rev_rev, right_inv := Fin.rev_rev }
    let reordered := StatementPermutation.identified before.source permutation
    match runSourceDebug reordered.admitted with
    | .ok actual =>
      let after : Debug.SourceRun := ⟨reordered, actual, none⟩
      let yBefore := before.observe.events.filterMap fun event => match event with
        | .contribution occurrence value =>
          if occurrence.destination.tensorUID == 2 then some (occurrence, value) else none
        | _ => none
      let yAfter := after.observe.events.filterMap fun event => match event with
        | .contribution occurrence value =>
          if occurrence.destination.tensorUID == 2 then some (occurrence, value) else none
        | _ => none
      let textBefore := renderSourceDebug (.ok before)
      let textAfter := renderSourceDebug (.ok after)
      (match before.observe.endpoint, after.observe.endpoint with
      | .complete _, .complete _ => true
      | _, _ => false) &&
      whole.kind == .complete &&
      whole.tensors == [
        ⟨0, 3, "A", [2, 3], [1, 2, 3, 4, 5, 6].map some⟩,
        ⟨1, 4, "B", [2], [some 10, some 20]⟩,
        ⟨2, 5, "Y", [2], [some 110, some 420]⟩,
        ⟨3, 6, "Empty", [0], []⟩,
        ⟨4, 7, "Diagonal", [2, 2], [some 1, some 0, some 0, some 1]⟩] &&
      before.source.admitted.statements.map (·.original) == [0, 1, 2, 3] &&
      reordered.admitted.statements.map (·.original) == [3, 2, 1, 0] &&
      yBefore == [(expectedY 1 0 0 1, 10), (expectedY 1 0 1 1, 20),
        (expectedY 3 1 0 2, 100), (expectedY 3 1 1 2, 400)] &&
      yAfter == [(expectedY 3 0 0 2, 100), (expectedY 3 0 1 2, 400),
        (expectedY 1 1 0 1, 10), (expectedY 1 1 1 1, 20)] &&
      canonicalContributions before.observe.events == expectedContributions &&
      canonicalContributions after.observe.events == expectedContributions &&
      compareContributions (canonicalContributions before.observe.events)
        (canonicalContributions after.observe.events) == .ok .agreement &&
      compareTensors before.observe.endpoint.snapshot.tensors
        after.observe.endpoint.snapshot.tensors == .ok .agreement &&
      ((canonicalContributions before.observe.events).map (·.key)).eraseDups.length == 8 &&
      [textBefore, textAfter].all (fun text =>
        (text.splitOn "statement := 1").length > 1 &&
        (text.splitOn "statement := 3").length > 1 &&
        (text.splitOn "targetLocal := 0").length > 1 &&
        (text.splitOn "targetLocal := 1").length > 1 &&
        (text.splitOn "declaration := some 5").length > 1 &&
        (text.splitOn "noTermEvaluationHook").length > 1)
    | .error _ => false
  | _, _ => false

#guard D7
#guard D8
#guard D9

end SourceDiagnosticComparisonTest
