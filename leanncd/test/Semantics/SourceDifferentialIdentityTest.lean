import Semantics.SourceDifferentialFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Debug
open LeanNCD.Semantics.Source.Differential
open LeanNCD.Semantics.Source.NativeLegs
open SourceAdmissionFixtures SourceDifferentialFixtures

namespace SourceDifferentialIdentityTest

private def expectedContributions (tensorUID declaration : Nat) (uids : List UID)
    (cells : List (List Nat × ℚ)) : List ContributionObservation :=
  cells.map fun (coordinate, value) =>
    ⟨⟨0, uids.zip coordinate⟩, ⟨tensorUID, declaration, coordinate⟩, some value⟩

private def exactFourLeg (run : ComparisonRun) (tensorUID declaration : Nat)
    (axes : Shape) (values : List ℚ) (bits : Array UInt64)
    (contributions : List ContributionObservation) : Bool :=
  match run.classification, run.oracle, run.native, run.profile, run.referenceComparison with
  | .fourLegParity, .ok oracle, .ok native, .ok _, some comparison =>
    match run.reference.observe.endpoint, native.legacy, native.checked,
        comparison.published, comparison.collection, comparison.body, comparison.rows,
        native.identity, native.shared, native.inputs with
    | .complete snapshot, .observed legacy, .observed checked _,
        .ok .agreement, .ok .agreement, .ok .agreement, .ok rows,
        .ok _, .ok _, .ok _ =>
      match legacy.outputs, checked.outputs with
      | .ok [left], .ok [right] =>
        let shape := axes.map Axis.extent
        let count := shape.foldl (· * ·) 1
        definedTensors snapshot.tensors ==
          [⟨tensorUID, declaration, some "Y", .output, axes, shape, values.map some⟩] &&
        oracle.tensors.filter (fun t => t.role != .input) ==
          [⟨declaration, "Y", .output, shape, values⟩] &&
        canonicalContributions run.reference.observe.events == contributions &&
        oracleContributions rows == contributions &&
        values.length == count && bits.size == count &&
        left.metadata.tensorUID == tensorUID && left.metadata.declaration == declaration &&
        left.metadata.name == "Y" && left.metadata.axes == axes &&
        left.metadata.shape == shape && right.metadata == left.metadata &&
        left.shape == shape && right.shape == shape &&
        left.bits.size == count && right.bits.size == count &&
        left.bits == bits && right.bits == bits
      | _, _ => false
    | _, _, _, _, _, _, _, _, _, _ => false
  | _, _, _, _, _ => false

private def duplicateTerms : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .typedTensor .f64 "A" [i], .typedTensor .f64 "Y" [i]],
    [.assign "Y" [.free i]
      (rhs [[.read "A" [.axis i]], [.read "A" [.axis i]]])], {}, ∅⟩,
    [⟨1, .input, [2]⟩, ⟨2, .output, [2]⟩], [⟨1, [2], [5, 9]⟩]⟩

private def duplicateTermOrigins (run : ComparisonRun) : Bool :=
  match run.reference.source.admitted.statements, run.oracle with
  | [statement], .ok oracle =>
    statement.original == 0 &&
    statement.terms.map (fun t => (t.origin.statement, t.origin.term)) ==
      [(some 0, some 0), (some 0, some 1)] &&
    statement.terms.map (fun t => t.sourceReads.map fun r =>
      (r.origin.statement, r.origin.term, r.origin.factor, r.indices)) ==
      [[(some 0, some 0, some 0, [7])], [(some 0, some 1, some 0, [7])]] &&
    oracle.contributions.map (fun c =>
      (c.origin.statement, c.coordinate, c.terms.map fun t =>
        (t.origin.statement, t.origin.term, t.value))) ==
      [(some 0, [0], [(some 0, some 0, 5), (some 0, some 1, 5)]),
       (some 0, [1], [(some 0, some 0, 9), (some 0, some 1, 9)])]
  | _, _ => false

def F7 : Bool :=
  match compareSource duplicateTerms (some [2]) with
  | .ok run =>
    duplicateTermOrigins run &&
    exactFourLeg run 1 2 [⟨7, 2⟩] [10, 18]
      #[0x4024000000000000, 0x4032000000000000]
      (expectedContributions 1 2 [7] [([0], 10), ([1], 18)])
  | .error _ => false

#guard F7

private def k2 : AxisSpec := ⟨"k", 3, .nat⟩
private def j3 : AxisSpec := ⟨"j", 19, .nat⟩

private def packedMatrix (reordered : Bool) : SourceSnapshot :=
  let xAxes := if reordered then [j3, k2] else [k2, j3]
  let xSlots := xAxes.map IdxExpr.axis
  let xShape := if reordered then [3, 2] else [2, 3]
  let xValues : List ℚ :=
    if reordered then [5, 7, 17, 19, 29, 31] else [5, 17, 29, 7, 19, 31]
  ⟨⟨[.axis j3 (some 3), .axis k2 (some 2), .axis i (some 2),
      .typedTensor .f64 "W" [i, k2], .typedTensor .f64 "X" xAxes,
      .typedTensor .f64 "Y" [i, j3]],
    [.assign "Y" [.free i, .free j3]
      (rhs [[.read "W" [.axis i, .axis k2], .read "X" xSlots]])], {}, ∅⟩,
    [⟨3, .input, [2, 2]⟩, ⟨4, .input, xShape⟩, ⟨5, .output, [2, 3]⟩],
    [⟨3, [2, 2], [2, 3, 11, 13]⟩, ⟨4, xShape, xValues⟩]⟩

private def matrixCells : List (List Nat × ℚ) :=
  [([0, 0], 31), ([0, 1], 91), ([0, 2], 151),
   ([1, 0], 146), ([1, 1], 434), ([1, 2], 722)]

private def matrixBits : Array UInt64 :=
  #[0x403f000000000000, 0x4056c00000000000, 0x4062e00000000000,
    0x4062400000000000, 0x407b200000000000, 0x4086900000000000]

private def independentPacking (run : ComparisonRun) (reordered : Bool) : Bool :=
  match run.oracle with
  | .ok oracle =>
    match oracle.tensors.filter (fun t => t.role == .input) with
    | [w, x] =>
      let shape := if reordered then [3, 2] else [2, 3]
      let values : List ℚ :=
        if reordered then [5, 7, 17, 19, 29, 31] else [5, 17, 29, 7, 19, 31]
      let probes : List (List Nat × ℚ) :=
        if reordered then
          [([0, 0], 5), ([0, 1], 7), ([1, 0], 17),
           ([1, 1], 19), ([2, 0], 29), ([2, 1], 31)]
        else
          [([0, 0], 5), ([0, 1], 17), ([0, 2], 29),
           ([1, 0], 7), ([1, 1], 19), ([1, 2], 31)]
      let wProbes : List (List Nat × ℚ) :=
        [([0, 0], 2), ([0, 1], 3), ([1, 0], 11), ([1, 1], 13)]
      w == ⟨3, "W", .input, [2, 2], [2, 3, 11, 13]⟩ &&
      x == ⟨4, "X", .input, shape, values⟩ &&
      probes.all (fun (coordinate, value) =>
        Oracle.lookup {} shape x coordinate == .ok value) &&
      wProbes.all
        (fun (coordinate, value) => Oracle.lookup {} [2, 2] w coordinate == .ok value) &&
      (if reordered then
        match Oracle.lookup {} [3, 2] x [3, 0] with
        | .error error => error.cause == .coordinateBound 0 3 3
        | .ok _ => false
       else true)
    | _ => false
  | .error _ => false

private def packedMetadata (run : ComparisonRun) (reordered : Bool) : Bool :=
  let source := run.reference.source.admitted
  source.source.context.axes == [⟨19, 3⟩, ⟨3, 2⟩, ⟨7, 2⟩] &&
  source.source.table.entries.map (fun t => (t.declaration, t.axes)) ==
    [(3, [⟨7, 2⟩, ⟨3, 2⟩]),
     (4, if reordered then [⟨19, 3⟩, ⟨3, 2⟩] else [⟨3, 2⟩, ⟨19, 3⟩]),
     (5, [⟨7, 2⟩, ⟨19, 3⟩])] &&
  source.statements.map (fun s =>
    (s.original, s.output.indices, s.terms.map fun t => t.sourceReads.map (·.indices))) ==
    [(0, [7, 19], [[[7, 3], if reordered then [19, 3] else [3, 19]]])]

def F8 : Bool :=
  match compareSource (packedMatrix false) (some [5]),
      compareSource (packedMatrix true) (some [5]) with
  | .ok original, .ok reordered =>
    let rows := expectedContributions 2 5 [7, 19] matrixCells
    let values := matrixCells.map Prod.snd
    exactFourLeg original 2 5 [⟨7, 2⟩, ⟨19, 3⟩] values matrixBits rows &&
    exactFourLeg reordered 2 5 [⟨7, 2⟩, ⟨19, 3⟩] values matrixBits rows &&
    independentPacking original false && independentPacking reordered true &&
    packedMetadata original false && packedMetadata reordered true &&
    canonicalContributions original.reference.observe.events ==
      canonicalContributions reordered.reference.observe.events &&
    values != [67, 101, 127, 302, 454, 590]
  | _, _ => false

#guard F8

private def alphaContext : Context := ⟨[⟨7, 2⟩, ⟨19, 2⟩, ⟨3, 3⟩], by decide⟩

private def alphaScope : BinderScope alphaContext where
  source := []
  output := [7, 19]
  free := [7, 19]
  generated := [3]
  covers := by
    intro u
    have h := u.property
    simp [alphaContext] at h
    rcases h with h | h | h <;> simp [h]
  generatedOnly := by
    intro u hu
    simp at hu
    subst u
    decide

private def renameAxis (a : AxisSpec) : AxisSpec :=
  if a.uid == 3 then
    { a with uid := alphaScope.renameUID a.uid, name := "contracted_renamed" }
  else a

private def renamedMatrix : SourceSnapshot :=
  { matmul with resolved := { matmul.resolved with
      decls := matmul.resolved.decls.map (Decl.traverseAxes (f := Id) renameAxis)
      stmts := matmul.resolved.stmts.map (Stmt.traverseAxes (f := Id) renameAxis) } }

example (u : alphaContext.Key) :
    (renameBinders alphaContext alphaScope).domain
        ((binderTransport alphaContext alphaScope).equiv u) = alphaContext.domain u :=
  (binderTransport alphaContext alphaScope).domain u

private def alphaMetadata (original renamed : ComparisonRun) : Bool :=
  let before := original.reference.source.admitted
  let after := renamed.reference.source.admitted
  before.source.context.axes == alphaContext.axes &&
  after.source.context.axes == (renameBinders alphaContext alphaScope).axes &&
  after.source.context.axes == [⟨7, 2⟩, ⟨19, 2⟩, ⟨23, 3⟩] &&
  before.source.context.axes.map Axis.extent == after.source.context.axes.map Axis.extent &&
  before.statements.map (·.original) == [0] && after.statements.map (·.original) == [0] &&
  before.source.table.entries.map (fun t => (t.declaration, t.name, t.role)) ==
    after.source.table.entries.map (fun t => (t.declaration, t.name, t.role)) &&
  before.statements.map (fun s => s.output.indices) == [[7, 19]] &&
  after.statements.map (fun s => s.output.indices) == [[7, 19]] &&
  before.statements.map (fun s => s.terms.map fun t =>
    (t.origin, t.partition.bound, t.sourceReads.map (·.indices))) ==
    [[({ side := .read, statement := some 0, term := some 0 },
      [⟨3, 3⟩], [[7, 3], [3, 19]])]] &&
  after.statements.map (fun s => s.terms.map fun t =>
    (t.origin, t.partition.bound, t.sourceReads.map (·.indices))) ==
    [[({ side := .read, statement := some 0, term := some 0 },
      [⟨23, 3⟩], [[7, 23], [23, 19]])]] &&
  after.source.table.entries.map (·.axes) ==
    [[⟨7, 2⟩, ⟨23, 3⟩], [⟨23, 3⟩, ⟨19, 2⟩], [⟨7, 2⟩, ⟨19, 2⟩]]

private def parsedOriginal : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  axis k : ℕ = 3
  tensor f64 W(i, k), X(k, j), Y(i, j)
  Y[i, j] := W[i, k] · X[k, j]
}

private def parsedRenamed : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  axis contracted_renamed : ℕ = 3
  tensor f64 W(i, contracted_renamed), X(contracted_renamed, j), Y(i, j)
  Y[i, j] := W[i, contracted_renamed] · X[contracted_renamed, j]
}

private def parsedNames (run : ComparisonRun) (contractedName : String) : Bool :=
  match run.native with
  | .ok native =>
    match native.identity with
    | .ok axes =>
      axes.any (fun a => a.name == contractedName && a.uid == 3) &&
      axes.all (fun a =>
        (a.name == "i" && a.uid == 1) || (a.name == "j" && a.uid == 2) ||
        (a.name == contractedName && a.uid == 3))
    | .error _ => false
  | .error _ => false

private def alphaBoundary : Bool :=
  let capture : SourceSnapshot :=
    { matmul with resolved := { matmul.resolved with
        decls := matmul.resolved.decls.map
          (Decl.traverseAxes (f := Id) (fun a => if a.uid == 3 then i else a))
        stmts := matmul.resolved.stmts.map
          (Stmt.traverseAxes (f := Id) (fun a => if a.uid == 3 then i else a)) } }
  let changedDomain : SourceSnapshot :=
    { matmul with resolved := { matmul.resolved with
        decls := [.axis i (some 2), .axis j (some 2), .axis k (some 4),
          .typedTensor .f64 "W" [i, k], .typedTensor .f64 "X" [k, j],
          .typedTensor .f64 "Y" [i, j]] } }
  (match admitSource capture with
  | .error diagnostic =>
    match diagnostic.stage, diagnostic.cause with
    | .declarations, .duplicateAxis 7 => true
    | _, _ => false
  | .ok _ => false) &&
  (match admitSource changedDomain with
  | .error diagnostic =>
    match diagnostic.stage, diagnostic.cause with
    | .signatures, .shape [2, 4] [2, 3] => true
    | _, _ => false
  | .ok _ => false)

def F9 : Bool :=
  match compareSource matmul (some [5]), compareSource renamedMatrix (some [5]),
      resolveSource parsedOriginal matmul.specs matmul.inputs,
      resolveSource parsedRenamed matmul.specs matmul.inputs with
  | .ok original, .ok renamed, .ok parsedBefore, .ok parsedAfter =>
    let values : List ℚ := [4, 5, 10, 11]
    let bits := #[0x4010000000000000, 0x4014000000000000,
      0x4024000000000000, 0x4026000000000000]
    let cells : List (List Nat × ℚ) :=
      [([0, 0], 4), ([0, 1], 5), ([1, 0], 10), ([1, 1], 11)]
    let rows := expectedContributions 2 5 [7, 19] cells
    exactFourLeg original 2 5 [⟨7, 2⟩, ⟨19, 2⟩] values bits rows &&
    exactFourLeg renamed 2 5 [⟨7, 2⟩, ⟨19, 2⟩] values bits rows &&
    alphaMetadata original renamed && alphaBoundary &&
    canonicalContributions original.reference.observe.events ==
      canonicalContributions renamed.reference.observe.events &&
    definedTensors original.reference.observe.endpoint.snapshot.tensors ==
      definedTensors renamed.reference.observe.endpoint.snapshot.tensors &&
    (match compareSource parsedBefore (some [5]), compareSource parsedAfter (some [5]) with
    | .ok before, .ok after =>
      let parsedRows := expectedContributions 2 5 [1, 2] cells
      exactFourLeg before 2 5 [⟨1, 2⟩, ⟨2, 2⟩] values bits parsedRows &&
      exactFourLeg after 2 5 [⟨1, 2⟩, ⟨2, 2⟩] values bits parsedRows &&
      parsedNames before "k" && parsedNames after "contracted_renamed"
    | _, _ => false)
  | _, _, _, _ => false

#guard F9

end SourceDifferentialIdentityTest
