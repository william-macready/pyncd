import Semantics.SourceDifferentialFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Debug
open LeanNCD.Semantics.Source.NativeLegs
open LeanNCD.Semantics.Source.Differential
open SourceAdmissionFixtures

namespace SourceDifferentialGeometryTest

def diagonalRun := compareSource SourceDifferentialFixtures.diagonalWrite (some [2])
def emptyRun := compareSource SourceDifferentialFixtures.emptyContraction (some [3])
def scalarRun := compareSource SourceDifferentialFixtures.scalar (some [2])

private def outputOrigin (declaration : Nat) : SourceOrigin :=
  { side := .output, declaration := some declaration, statement := some 0 }

private def termOrigin : SourceOrigin :=
  { side := .read, statement := some 0, term := some 0 }

private def readOrigin (declaration factor : Nat) : SourceOrigin :=
  { termOrigin with declaration := some declaration, factor := some factor }

private def cell (declaration : Nat) (coordinate : List Nat) (value : ℚ)
    (occurrences : List Oracle.Occurrence) : Oracle.Contribution :=
  ⟨outputOrigin declaration, coordinate, [⟨termOrigin, occurrences, value⟩], value⟩

private def contribution (uid : UID) (declaration : Nat)
    (assignment : List (UID × Nat)) (coordinate : List Nat) (value : ℚ) :
    ContributionObservation :=
  ⟨⟨0, assignment⟩, ⟨uid, declaration, coordinate⟩, some value⟩

private def nativeOutput (observation : NativeObservation) (uid : UID)
    (declaration : Nat) (axes : List (UID × Nat)) (shape : List Nat)
    (bits : Array UInt64) : Bool :=
  match observation.outputs, observation.report.env["Y"]?, observation.backendInternals with
  | .ok [binding], some actual, .unobserved .noBackendInternalHook =>
    binding.metadata.tensorUID == uid && binding.metadata.declaration == declaration &&
    binding.metadata.name == "Y" &&
    binding.metadata.origin == { side := .declaration, declaration := some declaration } &&
    binding.metadata.axes.map (fun a => (a.uid, a.extent)) == axes &&
    binding.metadata.shape == shape && binding.shape == shape && actual.shape == shape &&
    binding.bits.size == bits.size && actual.data.size == bits.size &&
    binding.bits == bits && actual.data.map Float.toBits == bits
  | _, _, _ => false

private def geometry (run : ComparisonRun) (inputs : List Oracle.Tensor)
    (uid : UID) (declaration : Nat) (axes : List (UID × Nat)) (shape : List Nat)
    (values : List ℚ) (bits : Array UInt64) (cells : List Oracle.Contribution)
    (normalized : List (Option ContributionObservation)) : Bool :=
  match run.classification, run.oracle, run.profile, run.native,
      run.reference.observe.endpoint, run.referenceComparison with
  | .fourLegParity, .ok oracle, .ok profile, .ok native, .complete final, some comparison =>
    match comparison.tensors, comparison.rows, native.shared, native.identity, native.inputs,
        native.legacy, native.checked, definedTensors final.tensors with
    | .ok tensors, .ok rows, .ok shared, .ok identities, .ok _,
        .observed legacy, .observed checked mappings, [output] =>
      let publications := run.reference.observe.events.filterMap fun event =>
        match event with
        | .publication address value => some (address, value)
        | _ => none
      let expectedPublications : List (AddressObservation × ℚ) := cells.map fun c =>
        (⟨uid, declaration, c.coordinate⟩, c.value)
      let original := native.source.program
      let originalAxes :=
        original.decls.flatMap (fun d =>
          (Decl.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) d).run) ++
        original.stmts.flatMap (fun s =>
          (Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run)
      shape.foldl (· * ·) 1 == values.length &&
      cells.length == values.length && normalized.length == cells.length &&
      bits.size == values.length &&
      oracle.tensors == inputs ++ [⟨declaration, "Y", .output, shape, values⟩] &&
      oracle.contributions == cells &&
      profile.oracle == oracle && profile.rows == rows && profile.actual.isSome &&
      rows.map (·.fullCell) == cells && rows.map (·.occurrence) == normalized &&
      canonicalContributions run.reference.observe.events == normalized.filterMap id &&
      final.tensors == tensors && output.tensorUID == uid &&
      output.declaration == declaration && output.name == some "Y" &&
      output.role == .output && output.shape == shape &&
      output.axes.map (fun a => (a.uid, a.extent)) == axes &&
      output.values.length == values.length && output.values == values.map some &&
      publications.length == expectedPublications.length &&
      expectedPublications.all (fun p => publications.contains p) &&
      final.pending.isEmpty && final.unpublished.isEmpty &&
      profile.shared == shared &&
      shared.usedDeclarations == declaration :: inputs.map (·.declaration) &&
      shared.definitions == [(declaration, outputOrigin declaration)] &&
      identities == originalAxes &&
      (identities.map (·.uid)).reverse.dedup.reverse ==
        run.reference.source.admitted.source.context.axes.map Axis.uid &&
      mappings == [⟨"Y", [outputOrigin declaration], some 0⟩] &&
      nativeOutput legacy uid declaration axes shape bits &&
      nativeOutput checked uid declaration axes shape bits
    | _, _, _, _, _, _, _, _ => false
  | _, _, _, _, _, _ => false

-- Repeated output slots enumerate one UID, but publication still covers the full square.
def F4 : Bool :=
  match diagonalRun with
  | .ok run =>
    let low := contribution 1 2 [(7, 0)] [0, 0] 5
    let high := contribution 1 2 [(7, 1)] [1, 1] 9
    let cells :=
      [cell 2 [0, 0] 5 [⟨termOrigin, [(7, 0)], [0, 0],
         [⟨readOrigin 1 0, 1, [0], 5⟩], 5⟩],
       cell 2 [0, 1] 0 [],
       cell 2 [1, 0] 0 [],
       cell 2 [1, 1] 9 [⟨termOrigin, [(7, 1)], [1, 1],
         [⟨readOrigin 1 0, 1, [1], 9⟩], 9⟩]]
    geometry run [⟨1, "A", .input, [2], [5, 9]⟩]
      1 2 [(7, 2), (7, 2)] [2, 2] [5, 0, 0, 9]
      #[0x4014000000000000, 0, 0, 0x4022000000000000]
      cells [some low, none, none, some high] &&
    run.fixtureDependencyOrder == some [2] &&
    match run.reference.source.admitted.statements with
    | [statement] =>
      statement.original == 0 && statement.output.indices == [7, 7] &&
      statement.output.context.axes.map Axis.uid == [7] &&
      statement.terms.map (fun term => term.partition.bound.map Axis.uid) == [[]]
    | _ => false
  | _ => false

#guard F4

private def zeroOutput : SourceSnapshot :=
  ⟨⟨[.axis k (some 0), .typedTensor .f64 "A" [k], .typedTensor .f64 "Y" [k]],
    [.assign "Y" [.free k] (rhs [[.read "A" [.axis k]]])], {}, ∅⟩,
    [⟨1, .input, [0]⟩, ⟨2, .output, [0]⟩], [⟨1, [0], []⟩]⟩

private def zeroOutputRun := compareSource zeroOutput (some [2])

private def zeroOutputGeometry : Bool :=
  match zeroOutputRun with
  | .ok run =>
    geometry run [⟨1, "A", .input, [0], []⟩]
      1 2 [(3, 0)] [0] [] #[] [] [] &&
    run.reference.source.admitted.source.context.axes.map (fun a => (a.uid, a.extent)) ==
      [(3, 0)]
  | _ => false

-- An empty contracted fiber contributes zero at each of two existing output occurrences.
def F5 : Bool :=
  match emptyRun with
  | .ok run =>
    geometry run [⟨2, "A", .input, [2, 0], []⟩]
      1 3 [(7, 2)] [2] [0, 0] #[0, 0]
      [cell 3 [0] 0 [], cell 3 [1] 0 []]
      [some (contribution 1 3 [(7, 0)] [0] 0),
       some (contribution 1 3 [(7, 1)] [1] 0)] &&
    run.fixtureDependencyOrder == some [3] &&
    run.reference.source.admitted.source.context.axes.map (fun a => (a.uid, a.extent)) ==
      [(7, 2), (3, 0)] &&
    zeroOutputGeometry &&
    (match run.native with
    | .ok native => match native.inputs with
      | .ok inputs => match inputs.env["A"]? with
        | some input => input.shape == [2, 0] && input.data.size == 0
        | none => false
      | _ => false
    | _ => false) &&
    match run.reference.source.admitted.statements with
    | [statement] =>
      statement.original == 0 && statement.output.indices == [7] &&
      statement.output.context.axes.map Axis.uid == [7] &&
      statement.terms.map (fun term =>
        term.partition.bound.map (fun a => (a.uid, a.extent))) == [[(3, 0)]]
    | _ => false
  | _ => false

#guard F5

private def scalarIdentity : SourceSnapshot :=
  ⟨⟨[.typedTensor .f64 "Y" []], [.assign "Y" [] (rhs [[]])], {}, ∅⟩,
    [⟨0, .output, []⟩], []⟩

private def scalarIdentityRun := compareSource scalarIdentity (some [0])

private def scalarIdentityGeometry : Bool :=
  match scalarIdentityRun with
  | .ok run =>
    geometry run [] 0 0 [] [] [1] #[0x3ff0000000000000]
      [cell 0 [] 1 [⟨termOrigin, [], [], [], 1⟩]]
      [some (contribution 0 0 [] [] 1)]
  | _ => false

-- Rank zero has exactly one empty assignment, not zero output cells.
def F6 : Bool :=
  match scalarRun with
  | .ok run =>
    geometry run [⟨0, "A", .input, [], [3]⟩, ⟨1, "B", .input, [], [7]⟩]
      2 2 [] [] [21] #[0x4035000000000000]
      [cell 2 [] 21 [⟨termOrigin, [], [],
        [⟨readOrigin 0 0, 0, [], 3⟩, ⟨readOrigin 1 1, 1, [], 7⟩], 21⟩]]
      [some (contribution 2 2 [] [] 21)] &&
    run.fixtureDependencyOrder == some [2] &&
    run.reference.source.admitted.source.context.axes.isEmpty &&
    scalarIdentityGeometry &&
    match run.reference.source.admitted.statements with
    | [statement] =>
      statement.original == 0 && statement.output.indices.isEmpty &&
      statement.output.context.axes.isEmpty &&
      statement.terms.map (fun term => term.partition.bound.map Axis.uid) == [[]]
    | _ => false
  | _ => false

#guard F6

end SourceDifferentialGeometryTest
