import Semantics.SourceCorrespondenceFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Program.Executor
open SourceAdmissionFixtures SourceProgramFixtures SourceCorrespondenceFixtures

namespace SourceCorrespondenceCollectionTest

private structure TermRow (K : Type) where
  globalAxes : List (UID × Nat)
  bound : List (UID × Nat)
  body : List (Option K)
  collected : List (Option K)
  global : List K
  deriving DecidableEq, Repr

private def termRows {K : Type} [Semiring K] (r : Registry (fun _ : Unit => K))
    (source : AdmittedSource) (ρ : Store (fun _ => K) source.source.table.declarations) :
    List (List (TermRow K)) :=
  source.statements.map fun statement =>
    let output := statement.output
    let layout := canonicalLayout (source.source.table.declarations.signature output.tensor).axes
    statement.terms.map fun term =>
      ⟨term.globalContext.axes.map (fun a => (a.uid, a.extent)),
        term.partition.bound.map (fun a => (a.uid, a.extent)),
        (List.finRange (canonicalLayout output.context.axes).count).map fun n =>
          interpret semiringOps ρ (term.body (r := r) id)
            ((canonicalLayout output.context.axes).enumerate n),
        (List.finRange layout.count).map fun n =>
          term.collectedBody (r := r) output ρ (layout.enumerate n),
        (List.finRange layout.count).map fun n =>
          term.globalFiber output ρ (layout.enumerate n)⟩

def j : AxisSpec := ⟨"j", 19, .nat⟩

def B4_snapshot : SourceSnapshot :=
  ⟨⟨decls ++ [.axis j (some 4), .tensor "C" [i, j]],
    [.assign "Y" [.free i] (rhs [
      [.read "A" [.axis i, .axis k]],
      [.read "C" [.axis i, .axis j]],
      [.read "A" [.axis i, .axis k], .read "C" [.axis i, .axis j]],
      [.read "B" [.axis i]]])], {}, ∅⟩,
    specs ++ [⟨9, .input, [2, 4]⟩],
    inputs ++ [⟨9, [2, 4], [2, 4, 8, 16, 3, 9, 27, 81]⟩]⟩

private def B4_expectedTerms {K : Type} [Semiring K] : List (List (TermRow K)) :=
  [[⟨[(7, 2), (3, 3)], [(3, 3)], [some 6, some 15],
       [some 6, some 15], [6, 15]⟩,
    ⟨[(7, 2), (19, 4)], [(19, 4)], [some 30, some 120],
       [some 30, some 120], [30, 120]⟩,
    ⟨[(7, 2), (3, 3), (19, 4)], [(3, 3), (19, 4)], [some 180, some 1800],
       [some 180, some 1800], [180, 1800]⟩,
    ⟨[(7, 2)], [], [some 10, some 20], [some 10, some 20], [10, 20]⟩]]

private def B4_expectedFibers {K : Type} [Semiring K] : List (FiberRow K) :=
  [⟨5, "Y", [2], [226, 1955], [226, 1955]⟩,
   ⟨7, "Diagonal", [2, 2], [0, 0, 0, 0], [0, 0, 0, 0]⟩]

def B4 := (admitSource B4_snapshot).toOption.map fun source =>
  (termRows natRegistry source (natStore source),
   fiberRows natRegistry source (natStore source),
   termRows RationalReference.registry source (ratStore source),
   fiberRows RationalReference.registry source (ratStore source),
   source.source.context.axes.map (fun a => (a.uid, a.extent)))

set_option synthInstance.maxSize 1024 in
#guard B4 = some (B4_expectedTerms, B4_expectedFibers,
  B4_expectedTerms, B4_expectedFibers, [(7, 2), (3, 3), (11, 0), (19, 4)])

theorem B4_nested_body (source : AdmittedSource)
    (_admission : admitSource B4_snapshot = .ok source)
    (s : Fin source.statements.length)
    (n : Fin (source.statements.get s).terms.length)
    (x : Coord (source.statements.get s).output.context.axes) :
    let term := (source.statements.get s).terms.get n
    interpret semiringOps (natStore source) (term.body (r := natRegistry) id) x =
      some (∑ v : UIDVal term.globalContext,
        if (term.partitionCoordEquiv v).1 = x then term.globalProduct (natStore source) v else 0) :=
  ((source.statements.get s).terms.get n).body_correspondence (natStore source) id x

theorem B4_term_fiber (source : AdmittedSource)
    (_admission : admitSource B4_snapshot = .ok source)
    (s : Fin source.statements.length)
    (n : Fin (source.statements.get s).terms.length) (p) :
    let statement := source.statements.get s
    let term := statement.terms.get n
    term.collectedBody (r := RationalReference.registry) statement.output (ratStore source) p =
      some (term.globalFiber statement.output (ratStore source) p) :=
  ((source.statements.get s).terms.get n).collectedBody_correspondence
    (source.statements.get s).output (ratStore source) p

theorem B4_program_fiber (source : AdmittedSource)
    (_admission : admitSource B4_snapshot = .ok source)
    (t : (source.program natRegistry).Defined) (p) :
    (source.program natRegistry).collect semiringOps (natStore source)
      (source.total_admEnv (natStore source)) t p = source.globalFiber (natStore source) t.val p :=
  source.collect_correspondence (natStore source) (source.total_admEnv (natStore source)) t p

def B5_snapshot : SourceSnapshot :=
  ⟨⟨[.axis j (some 4), .axis k (some 3), .axis e (some 0), .axis i (some 2),
      .tensor "A" [i, k], .tensor "W" [k, j], .tensor "Z" [i, j]],
    [.assign "Z" [.free i, .free j]
      (rhs [[.read "A" [.axis i, .axis k], .read "W" [.axis k, .axis j]]])],
    {}, ∅⟩,
    [⟨4, .input, [2, 3]⟩, ⟨5, .input, [3, 4]⟩, ⟨6, .output, [2, 4]⟩],
    [⟨4, [2, 3], [1, 2, 3, 4, 5, 6]⟩,
     ⟨5, [3, 4], [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]⟩]⟩

private def B5_values {K : Type} [Semiring K] : List K :=
  [93, 116, 132, 156, 201, 251, 291, 345]

def B5 := (admitSource B5_snapshot).toOption.map fun source =>
  (termRows RationalReference.registry source (ratStore source),
   fiberRows RationalReference.registry source (ratStore source))

#guard B5 = some
  ([[⟨[(19, 4), (3, 3), (7, 2)], [(3, 3)], (B5_values).map some,
      (B5_values).map some, B5_values⟩]],
   [⟨6, "Z", [2, 4], B5_values, B5_values⟩])

private structure LocatorRow where
  assignment : List (UID × Nat)
  output : List Nat
  contracted : List Nat
  destination : List Nat
  product : Rat
  inverse : Bool
  deriving DecidableEq, Repr

def B5_locators := (admitSource B5_snapshot).toOption.map fun (source : AdmittedSource) =>
  source.statements.map fun (statement : AdmittedStatement source.source) =>
    statement.terms.map fun (term : Term source.source.context statement.output.context
        source.source.table.declarations) =>
      (List.finRange (canonicalLayout term.globalContext.axes).count).map fun n =>
        let v : UIDVal term.globalContext := (uidCoordEquiv term.globalContext).invFun
          ((canonicalLayout term.globalContext.axes).enumerate.toFun n)
        let xy := term.partitionEquiv v
        (⟨coordAssignments _ ((uidCoordEquiv term.globalContext).toFun v),
          coordList _ ((uidCoordEquiv statement.output.context).toFun xy.1),
          coordList _ ((uidCoordEquiv term.contractedContext).toFun xy.2),
          coordList _ (term.globalDestination statement.output v),
          term.globalProduct (ratStore source) v,
          decide ((uidCoordEquiv term.globalContext).toFun (term.partitionEquiv.symm xy) =
            (uidCoordEquiv term.globalContext).toFun v)⟩ : LocatorRow)

#guard B5_locators.map (fun rows => rows.flatten.flatten.map LocatorRow.product) =
  some [2, 8, 22, 55, 69, 138, 3, 12, 26, 65, 87, 174,
    5, 20, 34, 85, 93, 186, 7, 28, 38, 95, 111, 222]
#guard B5_locators.map (fun rows => rows.flatten.flatten.all LocatorRow.inverse) = some true
#guard B5_locators.map (fun rows =>
  let cells := rows.flatten.flatten
  (cells[0]?, cells[1]?, cells[6]?, cells[23]?)) = some
  (some ⟨[(19, 0), (3, 0), (7, 0)], [0, 0], [0], [0, 0], 2, true⟩,
   some ⟨[(19, 0), (3, 0), (7, 1)], [1, 0], [0], [1, 0], 8, true⟩,
   some ⟨[(19, 1), (3, 0), (7, 0)], [0, 1], [0], [0, 1], 3, true⟩,
   some ⟨[(19, 3), (3, 2), (7, 1)], [1, 3], [2], [1, 3], 222, true⟩)

theorem B5_original_fiber (source : AdmittedSource)
    (_admission : admitSource B5_snapshot = .ok source)
    (t : (source.program RationalReference.registry).Defined) (p) :
    (source.program RationalReference.registry).collect semiringOps (ratStore source)
      (source.total_admEnv (ratStore source)) t p = source.globalFiber (ratStore source) t.val p :=
  source.collect_correspondence (ratStore source) (source.total_admEnv (ratStore source)) t p

private def duplicate : Stmt :=
  .assign "Y" [.free i] (rhs [[.read "B" [.axis i], .read "B" [.axis i]]])

def B6_snapshot : SourceSnapshot :=
  ⟨⟨decls,
    [.assign "Diagonal" [.free i, .free i] (rhs [[]]),
     duplicate, duplicate,
     .assign "Y" [.free i] (rhs [[.read "A" [.axis i, .axis k]]])], {}, ∅⟩,
    specs, inputs⟩

private def reverse (source : AdmittedSource) : StatementPermutation source :=
  permuteStatements source
    { toFun := Fin.rev, invFun := Fin.rev,
      left_inv := Fin.rev_rev, right_inv := Fin.rev_rev }

private structure CollisionView where
  rows : List (FiberRow Rat)
  originals : List (List Rat)
  ids : List Nat
  reversedIds : List Nat
  inverse : List (Nat × Nat × Nat × Nat)
  contributions : List (List (Nat × List Nat × Rat))
  reversedRows : List (FiberRow Rat)
  deriving DecidableEq, Repr

def B6 := (admitIdentifiedSource B6_snapshot).toOption.map fun identified =>
  let source := identified.admitted
  let ρ := ratStore source
  let permutation := reverse source
  (⟨fiberRows RationalReference.registry source ρ,
    (sourceDefined source).map fun t =>
      let layout := canonicalLayout (source.source.table.declarations.signature t.val).axes
      (List.finRange layout.count).map fun n =>
        identified.originalGlobalFiber ρ t.val (layout.enumerate n),
    source.statements.map AdmittedStatement.original,
    permutation.reordered.statements.map AdmittedStatement.original,
    (List.finRange source.statements.length).map fun n =>
      let original := identified.originalEquiv n
      let tag := identified.originalTagEquiv original
      (original.val, (identified.originalEquiv.symm original).val,
        tag.2.original, (identified.originalTagEquiv.symm tag).val),
    (sourceDefined source).map fun t =>
      (sourceOccurrences source t).map fun occurrence =>
        ((source.statementTag RationalReference.registry t occurrence.1).original,
          coordList _ ((elaborateSource source).destination t occurrence.1 occurrence.2),
          (elaborateSource source).contribution semiringOps ρ
            (source.total_admEnv ρ) t occurrence),
    fiberRows RationalReference.registry permutation.reordered ρ⟩ : CollisionView)

private def B6_expectedRows : List (FiberRow Rat) :=
  [⟨5, "Y", [2], [206, 815], [206, 815]⟩,
   ⟨7, "Diagonal", [2, 2], [1, 0, 0, 1], [1, 0, 0, 1]⟩]

set_option synthInstance.maxSize 1024 in
#guard B6 = some
  ⟨B6_expectedRows, [[206, 815], [1, 0, 0, 1]], [0, 1, 2, 3], [3, 2, 1, 0],
    [(0, 0, 0, 0), (1, 1, 1, 1), (2, 2, 2, 2), (3, 3, 3, 3)],
    [[(1, [0], 100), (1, [1], 400), (2, [0], 100), (2, [1], 400),
      (3, [0], 6), (3, [1], 15)],
     [(0, [0, 0], 1), (0, [1, 1], 1)]], B6_expectedRows⟩

#guard (observe B6_snapshot).toOption.map (fun o => (o.kind, o.tensors)) = some
  (.complete,
   [⟨0, 3, "A", [2, 3], [some 1, some 2, some 3, some 4, some 5, some 6]⟩,
    ⟨1, 4, "B", [2], [some 10, some 20]⟩,
    ⟨2, 5, "Y", [2], [some 206, some 815]⟩,
    ⟨3, 6, "Empty", [0], []⟩,
    ⟨4, 7, "Diagonal", [2, 2], [some 1, some 0, some 0, some 1]⟩])

theorem B6_original_collection (source : IdentifiedSource)
    (_admission : admitIdentifiedSource B6_snapshot = .ok source)
    (t : (source.admitted.program RationalReference.registry).Defined) (p) :
    (source.admitted.program RationalReference.registry).collect semiringOps
      (ratStore source.admitted) (source.admitted.total_admEnv (ratStore source.admitted)) t p =
        source.originalGlobalFiber (ratStore source.admitted) t.val p :=
  source.collect_correspondence (ratStore source.admitted)
    (source.admitted.total_admEnv (ratStore source.admitted)) t p

theorem B6_permutation_fiber (source : IdentifiedSource)
    (_admission : admitIdentifiedSource B6_snapshot = .ok source)
    (t : (source.admitted.program RationalReference.registry).Defined) (p) :
    (reverse source.admitted).reordered.globalFiber (ratStore source.admitted) t.val p =
      source.originalGlobalFiber (ratStore source.admitted) t.val p := by
  rw [(reverse source.admitted).globalFiber (r := RationalReference.registry),
    source.globalFiber_original]

theorem B6_reached_wholeModel (source : AdmittedSource)
    (_admission : admitSource B6_snapshot = .ok source) (c complete)
    (h : (run (elaborateSource source) RationalReference.ops (sourceSchedule source)
      (sourceInput source)).outcome = .complete c complete) :
    source.GlobalModels (r := RationalReference.registry) (sourceInput source)
      ((elaborateSource source).finalStore c complete) :=
  sourceResult_globalModel source
    ⟨sourceInput source, run (elaborateSource source) RationalReference.ops
      (sourceSchedule source) (sourceInput source)⟩ c complete h

end SourceCorrespondenceCollectionTest
