import Semantics.SourceDiagnosticFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Debug
open LeanNCD.Semantics.Source.NativeLegs
open LeanNCD.Semantics.Source.Differential
open LeanNCD.Eval LeanNCD.Eval.Plan
open SourceAdmissionFixtures SourceDiagnosticFixtures

namespace SourceDiagnosticNativeTest

def protocolWarning : EvalWarning := .paddedAccess "A" 2 2

-- D13 injects an existing runtime wrapper, not an observed backend fault or reached source failure.
def D13 : Bool :=
  match runNative scalarSnapshot with
  | .ok native => match native.checked with
    | .observed _ mappings =>
      let original : PlanRunFailure :=
        ⟨.storageKindMismatch .float64 .float32, [protocolWarning]⟩
      let injected : CheckedOutcome := .runtime ⟨original, mappings⟩
      let typed := match injected with
        | .runtime failure =>
          (match failure.original.cause with
          | .storageKindMismatch .float64 .float32 => true
          | _ => false) &&
          failure.original.warnings == [protocolWarning] &&
          failure.mappings == mappings &&
          mappings == [⟨"Y",
            [{ side := .output, declaration := some 1, statement := some 0 }], some 0⟩]
        | _ => false
      let rendered := renderChecked injected
      typed && (rendered.splitOn "checked runtime:").length == 2 &&
        (rendered.splitOn s!"cause={repr original.cause}").length == 2 &&
        (rendered.splitOn (toString protocolWarning)).length == 2 &&
        (rendered.splitOn s!"mappings={repr mappings}").length == 2
    | _ => false
  | _ => false

#guard D13

def diagonalWrite : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .typedTensor .f64 "A" [i], .typedTensor .f64 "Y" [i, i]],
    [.assign "Y" [.free i, .free i] (rhs [[.read "A" [.axis i]]])], {}, ∅⟩,
    [⟨1, .input, [2]⟩, ⟨2, .output, [2, 2]⟩], [⟨1, [2], [5, 9]⟩]⟩

-- D14 changes only a supplied output observation after requiring genuine four-leg agreement.
def D14 : Bool :=
  match compareSource diagonalWrite (some [2]) with
  | .ok run => match run.classification, run.profile, run.native with
    | .fourLegParity, .ok profile, .ok native =>
      match native.legacy, native.checked with
      | .observed legacy, .observed checked _ =>
        match legacy.outputs, checked.outputs, legacy.report.env["Y"]? with
        | .ok [left], .ok [right], some actual =>
          if left.bits != #[0x4014000000000000, 0, 0, 0x4022000000000000] ||
              right.bits != left.bits || actual.shape != [2, 2] || actual.data.size != 4 then
            false
          else
            let altered := { actual with data := actual.data.set! 2 (Float.ofBits 0x4000000000000000) }
            let report : EvalReport :=
              { legacy.report with env := legacy.report.env.insert "Y" altered }
            let supplied := observeBindings run.reference.source.admitted report
            let difference := compareNative profile supplied
            let exact := match difference with
              | .ok (.disagreement (.cell binding coordinate expected bits)) =>
                binding.tensorUID == 1 && binding.declaration == 2 && binding.name == "Y" &&
                binding.origin == { side := .declaration, declaration := some 2 } &&
                binding.axes.map Axis.uid == [i.uid, i.uid] &&
                binding.axes.map Axis.extent == [2, 2] && binding.shape == [2, 2] &&
                coordinate == [1, 0] && expected.kind == .tensorCell &&
                expected.site.origin.declaration == some 2 &&
                expected.site.coordinate == [1, 0] && expected.exact == 0 &&
                expected.integer.value == 0 && expected.bits == 0 &&
                bits.expectedOriginalBits == 0 && bits.expectedNormalizedBits == 0 &&
                bits.observedOriginalBits == 0x4000000000000000 &&
                bits.observedNormalizedBits == 0x4000000000000000 && !bits.agrees
              | _ => false
            let retained := match supplied.outputs with
              | .ok [binding] =>
                binding.metadata == left.metadata && binding.shape == left.shape &&
                binding.bits == #[0x4014000000000000, 0, 0x4000000000000000, 0x4022000000000000]
              | _ => false
            let injected := { run with
              native := .ok { native with legacy := .observed supplied }
              legacyComparison := .compared difference }
            let classified := match injected.classification, injected.checkedComparison with
              | .nativeDiscrepancy, .compared (.ok .agreement) => true
              | _, _ => false
            let internalLayers := [nativeLocalization.body, nativeLocalization.collection,
              nativeLocalization.readiness, nativeLocalization.publication,
              nativeLocalization.backendArithmetic]
            let unobserved := internalLayers == List.replicate 5
                (.unobserved .noBackendInternalHook) &&
              supplied.backendInternals == .unobserved .noBackendInternalHook
            let rendered := renderSourceComparison (.ok injected)
            let rendering := (rendered.splitOn
                s!"legacyComparison={repr (.compared difference : NativeComparison)}").length == 2 &&
              (["body", "collection", "readiness", "publication", "backendArithmetic"].all fun label =>
                (rendered.splitOn s!"{label}={repr (LayerObservation.unobserved .noBackendInternalHook)}").length >= 2)
            exact && retained && classified && unobserved && rendering &&
              injected.localization.body == .observedAgreement &&
              injected.localization.collection == .observedAgreement &&
              injected.localization.publication == .observedAgreement
        | _, _, _ => false
      | _, _ => false
    | _, _, _ => false
  | _ => false

#guard D14

-- D15's warning is protocol-injected; no actual warning receipt is asserted.
def D15 : Bool :=
  match compareSource scalarSnapshot (some [1]) with
  | .ok run => match run.classification, run.profile, run.native with
    | .fourLegParity, .ok profile, .ok native =>
      match native.legacy, native.checked with
      | .observed actual, .observed _ mappings =>
        let report : EvalReport := { actual.report with warnings := [protocolWarning] }
        let success := observeBindings run.reference.source.admitted report
        let missingReport : EvalReport := { report with env := report.env.erase "Y" }
        let missing := observeBindings run.reference.source.admitted missingReport
        let legacyFailure : EvalFailure := ⟨.unsupportedDtype "A", [protocolWarning]⟩
        let preparationFailure : PlanCompileFailure :=
          ⟨.inputSignature (.dtypeMismatch "A" .f32 .f64), [protocolWarning]⟩
        let runtimeFailure : PlanRunFailure :=
          ⟨.storageKindMismatch .float64 .float32, [protocolWarning]⟩
        let legacyError : LegacyOutcome :=
          .failure ⟨.scheduledEvaluation, legacyFailure, sourceMappings native.source⟩
        let preparationError : CheckedOutcome := .preparation ⟨preparationFailure, mappings⟩
        let runtimeError : CheckedOutcome := .runtime ⟨runtimeFailure, mappings⟩
        let typedSuccess := match success.outputs, compareNative profile success with
          | .ok [binding], .ok .agreement =>
            binding.metadata.declaration == 1 && binding.shape == [] &&
              binding.bits == #[0x4008000000000000] &&
              success.report.warnings == [protocolWarning]
          | _, _ => false
        let typedMissing := match missing.outputs, compareNative profile missing with
          | .error [.missingOutput origin],
              .ok (.disagreement (.bindingIssues [.missingOutput comparedOrigin])) =>
            origin == comparedOrigin && origin.declaration == 1 &&
              missing.report.warnings == [protocolWarning]
          | _, _ => false
        let typedErrors := match legacyError, preparationError, runtimeError with
          | .failure legacy, .preparation preparation, .runtime runtime =>
            legacy.phase == .scheduledEvaluation &&
              (match legacy.original.error with | .unsupportedDtype "A" => true | _ => false) &&
              legacy.original.warnings == [protocolWarning] &&
              legacy.mappings == sourceMappings native.source &&
              preparation.original.cause == .inputSignature (.dtypeMismatch "A" .f32 .f64) &&
              preparation.original.warnings == [protocolWarning] &&
              preparation.mappings == mappings &&
              runtime.original.cause == .storageKindMismatch .float64 .float32 &&
              runtime.original.warnings == [protocolWarning] && runtime.mappings == mappings
          | _, _, _ => false
        let renderings := [
          renderNativeObservation success, renderNativeObservation missing,
          renderLegacy (.observed success), renderChecked (.observed success mappings),
          renderLegacy legacyError, renderChecked preparationError, renderChecked runtimeError]
        let renderedWarnings := renderings.all fun text =>
          (text.splitOn (toString protocolWarning)).length == 2
        let injected := { run with native := .ok { native with
          legacy := .observed success, checked := .observed success mappings } }
        typedSuccess && typedMissing && typedErrors && renderedWarnings &&
          ((renderSourceComparison (.ok injected)).splitOn (toString protocolWarning)).length == 3
      | _, _ => false
    | _, _, _ => false
  | _ => false

#guard D15

end SourceDiagnosticNativeTest
