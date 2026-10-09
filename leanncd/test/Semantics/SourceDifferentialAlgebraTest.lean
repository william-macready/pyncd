import Semantics.SourceDifferentialFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Debug
open LeanNCD.Semantics.Source.NativeLegs
open LeanNCD.Semantics.Source.NumericalProfile
open LeanNCD.Semantics.Source.Differential
open SourceAdmissionFixtures SourceDifferentialFixtures

namespace SourceDifferentialAlgebraTest

private def termOrigin (term : Nat) : SourceOrigin :=
  { side := .read, statement := some 0, term := some term }

private def outputOrigin (declaration : Nat) : SourceOrigin :=
  { side := .output, declaration := some declaration, statement := some 0 }

private def fiberOccurrence (term : Nat) (assignment : List (UID × Nat))
    (output : List Nat) (reads : List (Nat × List Nat × ℚ)) (value : ℚ) :
    Oracle.Occurrence :=
  ⟨termOrigin term, assignment, output, reads.zipIdx.map (fun (read, factor) =>
    ⟨{ (termOrigin term) with declaration := some read.1, factor := some factor },
      read.1, read.2.1, read.2.2⟩), value⟩

private def observedTerm (term : Nat) (bound : Shape)
    (reads : List (Nat × List UID)) : TermObservation :=
  ⟨termOrigin term, reads.zipIdx.map (fun (read, factor) =>
    let origin := { (termOrigin term) with declaration := some read.1, factor := some factor }
    (origin, read.2.zipIdx.map fun (uid, slot) =>
      ({ origin with slot := some slot }, uid))),
    bound, .unobserved .noTermEvaluationHook, .unobserved .noTermEvaluationHook⟩

private def nativeBuffer (observation : NativeObservation) (metadata : TensorOrigin)
    (bits : Array UInt64) : Bool :=
  match observation.outputs, observation.report.env[metadata.name]? with
  | .ok [binding], some raw =>
    binding.metadata == metadata && binding.shape == metadata.shape &&
      binding.bits.size == bits.size && binding.bits == bits &&
      raw.shape == metadata.shape && raw.data.size == bits.size &&
      raw.data.map Float.toBits == bits &&
      observation.backendInternals == .unobserved .noBackendInternalHook &&
      ((renderNativeObservation observation).splitOn
        s!"warnings={observation.report.warnings.map toString}").length == 2
  | _, _ => false

private def originalSnapshot (original retained : SourceSnapshot) : Bool :=
  retained.resolved.decls == original.resolved.decls &&
    retained.resolved.stmts == original.resolved.stmts &&
    retained.resolved.extNames == original.resolved.extNames &&
    retained.resolved.env.toList.isEmpty && original.resolved.env.toList.isEmpty &&
    retained.specs.map (fun s => (s.declaration, s.role, s.shape)) ==
      original.specs.map (fun s => (s.declaration, s.role, s.shape)) &&
    retained.inputs.map (fun b => (b.declaration, b.shape, b.values)) ==
      original.inputs.map (fun b => (b.declaration, b.shape, b.values))

private def fourLegs (original : SourceSnapshot) (run : ComparisonRun)
    (uid declaration : Nat) (axes : Shape) (values : List ℚ) (bits : Array UInt64)
    (assignments : List (List (UID × Nat))) (terms : List TermObservation)
    (oracleRows : List Oracle.Contribution) (used : List Nat) : Bool :=
  let shape := axes.map Axis.extent
  let coordinates := Oracle.coordinates shape
  if coordinates.length != values.length || assignments.length != values.length ||
      bits.size != values.length then false
  else
    let expected : Debug.TensorObservation :=
      ⟨uid, declaration, some "Y", .output, axes, shape, values.map some⟩
    let metadata : TensorOrigin :=
      ⟨uid, declaration, "Y", { side := .declaration, declaration := some declaration },
        axes, shape⟩
    let contributions : List ContributionObservation :=
      ((coordinates.zip assignments).zip values).map fun ((coordinate, assignment), value) =>
        ⟨⟨0, assignment⟩, ⟨uid, declaration, coordinate⟩, some value⟩
    let published := (coordinates.zip values).map fun (coordinate, value) =>
      ((⟨uid, declaration, coordinate⟩ : AddressObservation), value)
    match run.classification, run.reference.observe.endpoint, run.oracle,
        run.referenceComparison, run.profile, run.native with
    | .fourLegParity, .complete snapshot, .ok oracle, some comparison,
        .ok profile, .ok native =>
      let fiberValues := oracleRows.flatMap fun row => row.terms.map fun term =>
        (term.origin, row.coordinate, term.value)
      let productValues := oracleRows.flatMap fun row => row.terms.flatMap fun term =>
        term.occurrences.map fun occurrence =>
          (term.origin, row.coordinate, occurrence.assignment, occurrence.value)
      let sourceTerms := run.reference.observe.events.filterMap fun event => match event with
        | .contribution occurrence _ => some occurrence.terms
        | _ => none
      let publications := run.reference.observe.events.filterMap fun event => match event with
        | .publication address value => some (address, value)
        | _ => none
      let agreements := match comparison.body, comparison.collection, comparison.published,
          run.legacyComparison, run.checkedComparison with
        | .ok .agreement, .ok .agreement, .ok .agreement,
            .compared (.ok .agreement), .compared (.ok .agreement) => true
        | _, _, _, _, _ => false
      let normalized := match comparison.rows, comparison.tensors with
        | .ok rows, .ok tensors =>
          rows.map (·.fullCell) == oracleRows &&
            oracleContributions rows == contributions &&
            definedTensors tensors == [expected]
        | _, _ => false
      let profileMetadata :=
        profile.oracle == oracle && profile.rows.map (·.fullCell) == oracleRows &&
        oracleContributions profile.rows == contributions && profile.actual.isSome &&
        profile.shared == ⟨used, [(declaration, outputOrigin declaration)]⟩ &&
        (profile.values.filter (fun v => v.kind == .fiber)).map
          (fun v => (v.site.origin, v.site.coordinate, v.exact)) == fiberValues &&
        (profile.values.filter (fun v => v.kind == .product)).map
          (fun v => (v.site.origin, v.site.coordinate, v.site.assignment, v.exact)) ==
            productValues &&
        (profile.values.filter (fun v =>
          v.kind == .tensorCell && v.site.origin.declaration == some declaration)).map
          (fun v => (v.site.coordinate, v.exact, v.bits)) ==
            ((coordinates.zip values).zip bits.toList).map
              (fun ((coordinate, value), encoding) => (coordinate, value, encoding))
      let nativeMetadata := match native.identity, native.shared, native.inputs,
          native.legacy, native.checked with
        | .ok _, .ok shared, .ok _, .observed legacy, .observed checked mappings =>
          shared == profile.shared &&
            originalSnapshot original native.source.snapshot &&
            native.source.program.decls == original.resolved.decls &&
            native.source.program.stmts == original.resolved.stmts &&
            mappings == [⟨"Y", [outputOrigin declaration], some 0⟩] &&
            nativeBuffer legacy metadata bits && nativeBuffer checked metadata bits
        | _, _, _, _, _ => false
      agreements && normalized && profileMetadata && nativeMetadata &&
        run.fixtureDependencyOrder == some [declaration] &&
        run.reference.requestedFuel.isNone &&
        run.reference.source.admitted.source.statements ==
          original.resolved.stmts.zipIdx.map (fun (statement, index) => (index, statement)) &&
        definedTensors snapshot.tensors == [expected] &&
        snapshot.accumulators == published && publications == published &&
        snapshot.pending.isEmpty && snapshot.unpublished.isEmpty &&
        canonicalContributions run.reference.observe.events == contributions &&
        sourceTerms == values.map (fun _ => terms) &&
        oracle.tensors.filter (fun t => t.role != .input) ==
          [⟨declaration, "Y", .output, shape, values⟩] &&
        oracle.contributions == oracleRows &&
        run.localization.body == .observedAgreement &&
        run.localization.collection == .observedAgreement &&
        run.localization.publication == .observedAgreement &&
        nativeLocalization ==
          ⟨.unobserved .noBackendInternalHook, .unobserved .noBackendInternalHook,
            .unobserved .noBackendInternalHook, .unobserved .noBackendInternalHook,
            .unobserved .noBackendInternalHook⟩
    | _, _, _, _, _, _ => false

private def matmulRows : List Oracle.Contribution :=
  ([(0, 0, [1, 2, 3], [1, 0, 1], 4),
    (0, 1, [1, 2, 3], [0, 1, 1], 5),
    (1, 0, [4, 5, 6], [1, 0, 1], 10),
    (1, 1, [4, 5, 6], [0, 1, 1], 11)] :
      List (Nat × Nat × List ℚ × List ℚ × ℚ)).map
    fun (row, column, weights, inputs, total) =>
      let coordinate := [row, column]
      let occurrences := ((weights.zip inputs).zipIdx).map fun ((w, x), contracted) =>
        fiberOccurrence 0 [(7, row), (19, column), (3, contracted)]
          coordinate [(3, [row, contracted], w), (4, [contracted, column], x)] (w * x)
      ⟨outputOrigin 5, coordinate, [⟨termOrigin 0, occurrences, total⟩], total⟩

def F1 : Bool :=
  match compareSource matmul (some [5]) with
  | .ok run =>
    fourLegs matmul run 2 5 [⟨7, 2⟩, ⟨19, 2⟩] [4, 5, 10, 11]
      #[0x4010000000000000, 0x4014000000000000, 0x4024000000000000, 0x4026000000000000]
      [[(7, 0), (19, 0)], [(7, 0), (19, 1)], [(7, 1), (19, 0)], [(7, 1), (19, 1)]]
      [observedTerm 0 [⟨3, 3⟩] [(3, [7, 3]), (4, [3, 19])]] matmulRows [5, 3, 4]
  | .error _ => false

#guard F1
#eval renderSourceComparison (compareSource matmul (some [5]))

private def biasRows : List Oracle.Contribution :=
  ([(0, [1, 2, 3], 7, 6, 13), (1, [4, 5, 6], 9, 15, 24)] :
      List (Nat × List ℚ × ℚ × ℚ × ℚ)).map
    fun (free, weights, biasValue, contraction, total) =>
      let products := weights.zipIdx.map fun (w, contracted) =>
        fiberOccurrence 0 [(7, free), (3, contracted)] [free]
          [(2, [free, contracted], w), (3, [contracted], 1)] w
      let singleton := fiberOccurrence 1 [(7, free)] [free] [(4, [free], biasValue)] biasValue
      ⟨outputOrigin 5, [free],
        [⟨termOrigin 0, products, contraction⟩, ⟨termOrigin 1, [singleton], biasValue⟩], total⟩

def F2 : Bool :=
  match compareSource biasSnapshot (some [5]) with
  | .ok run =>
    fourLegs biasSnapshot run 3 5 [⟨7, 2⟩] [13, 24]
      #[0x402a000000000000, 0x4038000000000000] [[(7, 0)], [(7, 1)]]
      [observedTerm 0 [⟨3, 3⟩] [(2, [7, 3]), (3, [3])],
       observedTerm 1 [] [(4, [7])]] biasRows [5, 2, 3, 4]
  | .error _ => false

#guard F2
#eval renderSourceComparison (compareSource biasSnapshot (some [5]))

private def diagonalRows : List Oracle.Contribution :=
  let occurrences :=
    [fiberOccurrence 0 [(7, 0)] [] [(1, [0, 0], 2)] 2,
     fiberOccurrence 0 [(7, 1)] [] [(1, [1, 1], 11)] 11]
  [⟨outputOrigin 2, [], [⟨termOrigin 0, occurrences, 13⟩], 13⟩]

-- This valid reference neighbor cannot be represented by the native name resolver.
private def independentSlotNeighbor : SourceSnapshot :=
  let other : AxisSpec := ⟨"i", 19, .nat⟩
  ⟨⟨[.axis i (some 2), .axis other (some 2),
      .typedTensor .f64 "A" [i, other], .typedTensor .f64 "Y" []],
    [.assign "Y" [] (rhs [[.read "A" [.axis i, .axis other]]])], {}, ∅⟩,
    [⟨2, .input, [2, 2]⟩, ⟨3, .output, []⟩], [⟨2, [2, 2], [2, 3, 5, 11]⟩]⟩

private def independentRows : List Oracle.Contribution :=
  let occurrences := ([(0, 0, 2), (0, 1, 3), (1, 0, 5), (1, 1, 11)] :
      List (Nat × Nat × ℚ)).map
    fun (left, right, value) =>
      fiberOccurrence 0 [(7, left), (19, right)] [] [(2, [left, right], value)] value
  [⟨outputOrigin 3, [], [⟨termOrigin 0, occurrences, 21⟩], 21⟩]

private def refusedIndependentNeighbor : Bool :=
  match compareSource independentSlotNeighbor (some [3]) with
  | .ok run =>
    match run.classification, run.reference.observe.endpoint, run.oracle,
        run.referenceComparison, run.profile, run.native with
    | .nativeUnavailable, .complete snapshot, .ok oracle, some comparison,
        .ok profile, .ok native =>
      let reference := match comparison.body, comparison.collection, comparison.published with
        | .ok .agreement, .ok .agreement, .ok .agreement => true
        | _, _, _ => false
      let refusal := match native.identity, native.legacy, native.checked with
        | .error (.sameNameDistinctUID first second),
            .unavailable (.identity (.sameNameDistinctUID legacyFirst legacySecond)),
            .unavailable (.identity (.sameNameDistinctUID checkedFirst checkedSecond)) =>
          first == i && second == (⟨"i", 19, .nat⟩ : AxisSpec) &&
            legacyFirst == first && legacySecond == second &&
            checkedFirst == first && checkedSecond == second
        | _, _, _ => false
      reference && refusal && profile.actual.isSome && profile.oracle == oracle &&
        profile.rows.map (·.fullCell) == independentRows &&
        oracle.contributions == independentRows &&
        definedTensors snapshot.tensors ==
          [⟨1, 3, some "Y", .output, [], [], [some 21]⟩] &&
        snapshot.accumulators == [(⟨1, 3, []⟩, 21)] &&
        canonicalContributions run.reference.observe.events ==
          [⟨⟨0, []⟩, ⟨1, 3, []⟩, some 21⟩] &&
        (match run.legacyComparison, run.checkedComparison with
        | .unavailable .legNotObserved, .unavailable .legNotObserved => true
        | _, _ => false)
    | _, _, _, _, _, _ => false
  | .error _ => false

def F3 : Bool :=
  match compareSource diagonalRead (some [2]) with
  | .ok run =>
    fourLegs diagonalRead run 1 2 [] [13] #[0x402a000000000000] [[]]
      [observedTerm 0 [⟨7, 2⟩] [(1, [7, 7])]] diagonalRows [2, 1] &&
      refusedIndependentNeighbor
  | .error _ => false

#guard F3
#eval renderSourceComparison (compareSource diagonalRead (some [2]))
#eval renderSourceComparison (compareSource independentSlotNeighbor (some [3]))

end SourceDifferentialAlgebraTest
