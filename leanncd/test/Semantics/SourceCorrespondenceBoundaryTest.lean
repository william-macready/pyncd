import Semantics.SourceCorrespondenceFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures SourceProgramFixtures SourceCorrespondenceFixtures

namespace SourceCorrespondenceBoundaryTest

private def scalar : SourceSnapshot :=
  ⟨⟨[.tensor "L" [], .tensor "R" [], .tensor "Scalar" []],
      [.assign "Scalar" [] (rhs [[.read "L" [], .read "R" []]])], {}, ∅⟩,
    [⟨0, .input, []⟩, ⟨1, .input, []⟩, ⟨2, .output, []⟩],
    [⟨0, [], [2 / 3]⟩, ⟨1, [], [5 / 7]⟩]⟩

private def zeroContraction : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis e (some 0),
      .tensor "Empty" [e], .tensor "B" [i], .tensor "Y" [i],
      .tensor "Positive" [i]],
      [.assign "Y" [.free i]
        (rhs [[.read "Empty" [.axis e], .read "B" [.axis i]]]),
       .assign "Positive" [.free i] (rhs [[.read "B" [.axis i]]])], {}, ∅⟩,
    [⟨2, .input, [0]⟩, ⟨3, .input, [2]⟩,
      ⟨4, .output, [2]⟩, ⟨5, .output, [2]⟩],
    [⟨2, [0], []⟩, ⟨3, [2], [2 / 3, 5 / 7]⟩]⟩

private def repeatedOutput : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .tensor "L" [i], .tensor "R" [i],
      .tensor "Diagonal" [i, i]],
      [.assign "Diagonal" [.free i, .free i]
        (rhs [[.read "L" [.axis i], .read "R" [.axis i]]])], {}, ∅⟩,
    [⟨1, .input, [2]⟩, ⟨2, .input, [2]⟩, ⟨3, .output, [2, 2]⟩],
    [⟨1, [2], [2 / 3, 5 / 7]⟩, ⟨2, [2], [3 / 5, 11 / 13]⟩]⟩

private structure TermView where
  outputSlots : List UID
  outputDomain : List (UID × Nat)
  globalDomain : List (UID × Nat)
  boundDomain : List (UID × Nat)
  readSlots : List (List UID)
  cardinalities : Nat × Nat × Nat
  twoReadProduct : Bool
  outerReduction : Option Nat
  body : List (Option Rat)
  products : List Rat
  destinations : List (List Nat)
  coordinates : List (List Nat)
  fiberCardinalities : List Nat
  global : List Rat
  collected : List (Option Rat)
  deriving DecidableEq, Repr

private def termViews (snapshot : SourceSnapshot) :
    Except SourceDiagnostic (List (List TermView)) :=
  (admitSource snapshot).map fun (source : AdmittedSource) =>
    let store := ratStore source
    source.statements.map fun (statement : AdmittedStatement source.source) =>
      statement.terms.map fun (term : Term source.source.context statement.output.context
          source.source.table.declarations) =>
        let output := statement.output
        let outputLayout := canonicalLayout output.context.axes
        let globalLayout := canonicalLayout term.globalContext.axes
        let fullLayout :=
          canonicalLayout (source.source.table.declarations.signature output.tensor).axes
        let valuations := (List.finRange globalLayout.count).map fun n =>
          (uidCoordEquiv term.globalContext).invFun (globalLayout.enumerate.toFun n)
        let destinations := valuations.map fun v =>
          coordList _ (term.globalDestination output v)
        let coordinates := (List.finRange fullLayout.count).map fun n =>
          coordList _ (fullLayout.enumerate n)
        let body := term.body (r := RationalReference.registry) id
        ⟨output.indices, output.context.axes.map (fun a => (a.uid, a.extent)),
          term.globalContext.axes.map (fun a => (a.uid, a.extent)),
          term.partition.bound.map (fun a => (a.uid, a.extent)),
          term.sourceReads.map CheckedRead.indices,
          (outputLayout.count, globalLayout.count,
            (canonicalLayout term.partition.bound).count),
          (match body with
          | .binary .mul (.read ..) (.binary .mul (.read ..) (.lit one)) => one == 1
          | _ => false),
          (match body with | .reduce n _ => some n | _ => none),
          (List.finRange outputLayout.count).map fun n =>
            interpret semiringOps store body (outputLayout.enumerate n),
          valuations.map (term.globalProduct store), destinations, coordinates,
          coordinates.map (fun p => (destinations.filter (· == p)).length),
          (List.finRange fullLayout.count).map fun n =>
            term.globalFiber output store (fullLayout.enumerate n),
          (List.finRange fullLayout.count).map fun n =>
            term.collectedBody (r := RationalReference.registry) output store
              (fullLayout.enumerate n)⟩

private def occurrenceViews (snapshot : SourceSnapshot) :
    Except SourceDiagnostic (List (Nat × Nat × List Nat × Option Rat × Rat)) :=
  (admitSource snapshot).map fun source =>
    let program := elaborateSource source
    let store := ratStore source
    (sourceDefined source).flatMap fun t =>
      (sourceOccurrences source t).map fun o =>
        ((source.statementTag RationalReference.registry t o.1).original,
          o.2.val.val, coordList _ (program.destination t o.1 o.2),
          program.outcome semiringOps store t o,
          program.contribution semiringOps store (source.total_admEnv store) t o)

private def scalarTerms : List (List TermView) :=
  [[{ outputSlots := [], outputDomain := [], globalDomain := [], boundDomain := [],
      readSlots := [[], []], cardinalities := (1, 1, 1),
      twoReadProduct := true, outerReduction := none,
      body := [some (10 / 21)], products := [10 / 21], destinations := [[]],
      coordinates := [[]], fiberCardinalities := [1],
      global := [10 / 21], collected := [some (10 / 21)] }]]

def B1 : Bool :=
  (termViews scalar).toOption == some scalarTerms &&
  (occurrenceViews scalar).toOption == some [(0, 0, [], some (10 / 21), 10 / 21)] &&
  ((admitSource scalar).toOption.map fun source =>
    fiberRows RationalReference.registry source (ratStore source)) ==
      some [⟨2, "Scalar", [], [10 / 21], [10 / 21]⟩] &&
  (observe scalar).toOption.map (fun o => o.kind) == some .complete &&
  (observe scalar).toOption.map (fun o => o.tensors) ==
    some [⟨0, 0, "L", [], [some (2 / 3)]⟩,
      ⟨1, 1, "R", [], [some (5 / 7)]⟩,
      ⟨2, 2, "Scalar", [], [some (10 / 21)]⟩]

private def zeroTerms : List (List TermView) :=
  [[{ outputSlots := [7], outputDomain := [(7, 2)],
      globalDomain := [(7, 2), (11, 0)], boundDomain := [(11, 0)],
      readSlots := [[11], [7]], cardinalities := (2, 0, 0),
      twoReadProduct := false, outerReduction := some 0,
      body := [some 0, some 0], products := [], destinations := [],
      coordinates := [[0], [1]], fiberCardinalities := [0, 0],
      global := [0, 0], collected := [some 0, some 0] }],
   [{ outputSlots := [7], outputDomain := [(7, 2)],
      globalDomain := [(7, 2)], boundDomain := [],
      readSlots := [[7]], cardinalities := (2, 2, 1),
      twoReadProduct := false, outerReduction := none,
      body := [some (2 / 3), some (5 / 7)], products := [2 / 3, 5 / 7],
      destinations := [[0], [1]], coordinates := [[0], [1]],
      fiberCardinalities := [1, 1], global := [2 / 3, 5 / 7],
      collected := [some (2 / 3), some (5 / 7)] }]]

def B2 : Bool :=
  (termViews zeroContraction).toOption == some zeroTerms &&
  (occurrenceViews zeroContraction).toOption ==
    some [(0, 0, [0], some 0, 0), (0, 1, [1], some 0, 0),
      (1, 0, [0], some (2 / 3), 2 / 3), (1, 1, [1], some (5 / 7), 5 / 7)] &&
  ((admitSource zeroContraction).toOption.map fun source =>
    fiberRows RationalReference.registry source (ratStore source)) ==
      some [⟨4, "Y", [2], [0, 0], [0, 0]⟩,
        ⟨5, "Positive", [2], [2 / 3, 5 / 7], [2 / 3, 5 / 7]⟩] &&
  (observe zeroContraction).toOption.map (fun o => o.kind) == some .complete &&
  (observe zeroContraction).toOption.map (fun o => o.tensors) ==
    some [⟨0, 2, "Empty", [0], []⟩,
      ⟨1, 3, "B", [2], [some (2 / 3), some (5 / 7)]⟩,
      ⟨2, 4, "Y", [2], [some 0, some 0]⟩,
      ⟨3, 5, "Positive", [2], [some (2 / 3), some (5 / 7)]⟩]

private def repeatedTerms : List (List TermView) :=
  [[{ outputSlots := [7, 7], outputDomain := [(7, 2)],
      globalDomain := [(7, 2)], boundDomain := [],
      readSlots := [[7], [7]], cardinalities := (2, 2, 1),
      twoReadProduct := true, outerReduction := none,
      body := [some (2 / 5), some (55 / 91)], products := [2 / 5, 55 / 91],
      destinations := [[0, 0], [1, 1]],
      coordinates := [[0, 0], [0, 1], [1, 0], [1, 1]],
      fiberCardinalities := [1, 0, 0, 1], global := [2 / 5, 0, 0, 55 / 91],
      collected := [some (2 / 5), some 0, some 0, some (55 / 91)] }]]

def B3 : Bool :=
  (termViews repeatedOutput).toOption == some repeatedTerms &&
  (occurrenceViews repeatedOutput).toOption ==
    some [(0, 0, [0, 0], some (2 / 5), 2 / 5),
      (0, 1, [1, 1], some (55 / 91), 55 / 91)] &&
  ((admitSource repeatedOutput).toOption.map fun source =>
    fiberRows RationalReference.registry source (ratStore source)) ==
      some [⟨3, "Diagonal", [2, 2], [2 / 5, 0, 0, 55 / 91],
        [2 / 5, 0, 0, 55 / 91]⟩] &&
  (observe repeatedOutput).toOption.map (fun o => o.kind) == some .complete &&
  (observe repeatedOutput).toOption.map (fun o => o.tensors) ==
    some [⟨0, 1, "L", [2], [some (2 / 3), some (5 / 7)]⟩,
      ⟨1, 2, "R", [2], [some (3 / 5), some (11 / 13)]⟩,
      ⟨2, 3, "Diagonal", [2, 2], [some (2 / 5), some 0, some 0, some (55 / 91)]⟩]

set_option synthInstance.maxSize 1024 in
#guard B1
set_option synthInstance.maxSize 1024 in
#guard B2
set_option synthInstance.maxSize 1024 in
#guard B3

theorem B1_bodyBridge (source : AdmittedSource) (_ : admitSource scalar = .ok source)
    (s : Fin source.statements.length) (t : Fin (source.statements.get s).terms.length)
    (p : Coord (source.source.table.declarations.signature
      (source.statements.get s).output.tensor).axes) :
    ((source.statements.get s).terms.get t).collectedBody
      (r := RationalReference.registry) (source.statements.get s).output
      (ratStore source) p =
      some (((source.statements.get s).terms.get t).globalFiber
        (source.statements.get s).output (ratStore source) p) :=
  ((source.statements.get s).terms.get t).collectedBody_correspondence
    (source.statements.get s).output (ratStore source) p

theorem B2_bodyBridge (source : AdmittedSource)
    (_ : admitSource zeroContraction = .ok source)
    (s : Fin source.statements.length) (t : Fin (source.statements.get s).terms.length)
    (p : Coord (source.source.table.declarations.signature
      (source.statements.get s).output.tensor).axes) :
    ((source.statements.get s).terms.get t).collectedBody
      (r := RationalReference.registry) (source.statements.get s).output
      (ratStore source) p =
      some (((source.statements.get s).terms.get t).globalFiber
        (source.statements.get s).output (ratStore source) p) :=
  ((source.statements.get s).terms.get t).collectedBody_correspondence
    (source.statements.get s).output (ratStore source) p

theorem B3_bodyBridge (source : AdmittedSource)
    (_ : admitSource repeatedOutput = .ok source)
    (s : Fin source.statements.length) (t : Fin (source.statements.get s).terms.length)
    (p : Coord (source.source.table.declarations.signature
      (source.statements.get s).output.tensor).axes) :
    ((source.statements.get s).terms.get t).collectedBody
      (r := RationalReference.registry) (source.statements.get s).output
      (ratStore source) p =
      some (((source.statements.get s).terms.get t).globalFiber
        (source.statements.get s).output (ratStore source) p) :=
  ((source.statements.get s).terms.get t).collectedBody_correspondence
    (source.statements.get s).output (ratStore source) p

theorem B3_collectBridge (source : AdmittedSource)
    (_ : admitSource repeatedOutput = .ok source)
    (t : (source.program RationalReference.registry).Defined)
    (p : Coord (source.source.table.declarations.signature t.val).axes) :
    (source.program RationalReference.registry).collect semiringOps (ratStore source)
      (source.total_admEnv (ratStore source)) t p =
      source.globalFiber (ratStore source) t.val p :=
  source.collect_correspondence (ratStore source) (source.total_admEnv (ratStore source)) t p

end SourceCorrespondenceBoundaryTest
