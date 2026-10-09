import LeanNCD.Semantics.Source.Oracle
import Semantics.SourceAdmissionFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures

namespace SourceOracleTest

private def evaluate (s : SourceSnapshot) (order : Option (List Nat)) :
    Except String Oracle.Result := do
  let admitted ← (admitSource s).mapError reprStr
  (Oracle.run admitted order).mapError reprStr

private def values (result : Oracle.Result) (declaration : Nat) : Option (List ℚ) :=
  (result.tensors.find? (fun t => t.declaration == declaration)).map (·.values)

private def contributionAt (result : Oracle.Result) (statement : Nat) (coordinate : List Nat) :
    Option Oracle.Contribution :=
  result.contributions.find? (fun c =>
    c.origin.statement == some statement && c.coordinate == coordinate)

private def asymmetricCells : List ℚ := [1 / 3, 2 / 3, 5, 10, 25, 45]

private def asymmetric : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Packed" [i, k], .tensor "Transpose" [k, i]]
      stmts := stmts ++
        [.assign "Y" [.free i]
          (rhs [[.read "A" [.axis i, .axis k]], [.read "B" [.axis i]]]),
         .assign "Packed" [.free i, .free k] (rhs [[.read "A" [.axis i, .axis k]]]),
         .assign "Transpose" [.free k, .free i] (rhs [[.read "A" [.axis i, .axis k]]])] }
    specs := specs ++ [⟨8, .output, [2, 3]⟩, ⟨9, .output, [3, 2]⟩]
    inputs := [⟨3, [2, 3], asymmetricCells⟩, ⟨4, [2], [10, 20]⟩, ⟨6, [0], []⟩] }

private def readOrigin : SourceOrigin :=
  { side := .read, declaration := some 3, statement := some 0,
    term := some 0, factor := some 0 }

private def packingGuards : Bool :=
  let tensor : Oracle.Tensor := ⟨3, "A", .input, [2, 3], asymmetricCells⟩
  (Oracle.coordinates [2, 3] ==
    [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2]]) &&
  (Oracle.coordinates [] == [[]]) &&
  (Oracle.coordinates [2, 0, 3] == []) &&
  ((Oracle.coordinates [2, 3]).mapM (Oracle.lookup readOrigin [2, 3] tensor) ==
    .ok asymmetricCells) &&
  (Oracle.lookup readOrigin [2, 3] { tensor with shape := [3, 2] } [0, 0] ==
    .error ⟨readOrigin, .shape [2, 3] [3, 2]⟩) &&
  (Oracle.lookup readOrigin [2, 3] { tensor with values := asymmetricCells.take 5 } [0, 0] ==
    .error ⟨readOrigin, .length 6 5⟩) &&
  (Oracle.lookup readOrigin [2, 3] tensor [1] ==
    .error ⟨readOrigin, .coordinateRank 2 1⟩) &&
  (Oracle.lookup readOrigin [2, 3] tensor [1, 3] ==
    .error ⟨{ readOrigin with slot := some 1 }, .coordinateBound 1 3 3⟩)

def AsymmetricPackingFiber : Bool :=
  packingGuards && match evaluate asymmetric (some [5, 7, 8, 9]) with
  | .error _ => false
  | .ok result =>
    values result 8 == some asymmetricCells &&
    values result 9 == some [1 / 3, 10, 2 / 3, 25, 5, 45] &&
    values result 5 == some [32, 200] &&
    result.tensors.map (·.declaration) == [3, 4, 5, 6, 7, 8, 9] &&
    result.contributions.map (·.origin.statement) ==
      [some 0, some 0, some 1, some 1, some 1, some 1, some 2, some 2,
       some 3, some 3, some 4, some 4, some 4, some 4, some 4, some 4,
       some 5, some 5, some 5, some 5, some 5, some 5] &&
    match contributionAt result 0 [0], contributionAt result 3 [0],
        contributionAt result 2 [0] with
    | some c, some duplicate, some empty =>
      c.origin == { side := .output, declaration := some 5, statement := some 0 } &&
      c.value == 16 && duplicate.value == 16 && empty.value == 0 && empty.terms == [] &&
      match c.terms with
      | [fiber, bias] =>
        fiber.value == 6 && bias.value == 10 &&
        fiber.origin == { side := .read, statement := some 0, term := some 0 } &&
        fiber.occurrences.map (·.assignment) ==
          [[(7, 0), (3, 0)], [(7, 0), (3, 1)], [(7, 0), (3, 2)]] &&
        fiber.occurrences.map (·.output) == [[0], [0], [0]] &&
        fiber.occurrences.map (·.reads) ==
          [[⟨readOrigin, 3, [0, 0], 1 / 3⟩],
           [⟨readOrigin, 3, [0, 1], 2 / 3⟩],
           [⟨readOrigin, 3, [0, 2], 5⟩]] &&
        bias.occurrences.map (·.assignment) == [[(7, 0)]]
      | _ => false
    | _, _, _ => false

private def boundaries : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Scalar" [], .tensor "Zero" [e],
        .tensor "Unwritten" [i], .tensor "D" [i, i],
        .tensor "Squared" [i], .tensor "ScalarZero" [], .tensor "UnwrittenOutput" [i]]
      stmts := stmts ++
        [.assign "Scalar" [] (rhs [[]]),
         .assign "Zero" [.free e] (rhs [[]]),
         .assign "Squared" [.free i]
           (rhs [[.read "D" [.axis i, .axis i],
             .read "B" [.axis i], .read "B" [.axis i]]]),
         .assign "ScalarZero" [] (rhs [[.read "Empty" [.axis e]]]),
         .assign "Scalar" [] (rhs []),
         .assign "Scalar" [] (rhs [[.read "B" [.axis i]], []])] }
    specs := specs ++ [⟨8, .output, []⟩, ⟨9, .output, [0]⟩,
      ⟨10, .defined, [2]⟩, ⟨11, .input, [2, 2]⟩,
      ⟨12, .output, [2]⟩, ⟨13, .output, []⟩, ⟨14, .output, [2]⟩]
    inputs := inputs ++ [⟨11, [2, 2], [2, 99, 101, 3]⟩] }

def ScalarZeroRepeatedAndBias : Bool :=
  match evaluate boundaries (some [5, 7, 8, 9, 10, 12, 13, 14]) with
  | .error _ => false
  | .ok result =>
    values result 5 == some [16, 35] &&
    values result 7 == some [1, 0, 0, 1] &&
    values result 8 == some [32] &&
    values result 9 == some [] &&
    values result 10 == some [0, 0] &&
    values result 12 == some [200, 1200] &&
    values result 13 == some [0] &&
    values result 14 == some [0, 0] &&
    match contributionAt result 1 [0, 1], contributionAt result 3 [],
        contributionAt result 5 [1], contributionAt result 6 [],
        contributionAt result 7 [], contributionAt result 8 [] with
    | some offDiagonal, some identity, some repeated,
        some zero, some emptySum, some bias =>
      offDiagonal.value == 0 &&
      offDiagonal.terms.map (·.occurrences) == [[]] &&
      identity.value == 1 &&
      identity.terms.map (fun t => t.occurrences.map (·.assignment)) == [[[]]] &&
      identity.terms.map (fun t => t.occurrences.map (·.reads)) == [[[]]] &&
      zero.value == 0 && zero.terms.map (·.occurrences) == [[]] &&
      emptySum.value == 0 && emptySum.terms == [] &&
      bias.terms.map (·.value) == [30, 1] &&
      bias.terms.map (fun t => t.occurrences.map (·.assignment)) ==
        [[[(7, 0)], [(7, 1)]], [[]]] &&
      match repeated.terms with
      | [term] =>
        match term.occurrences with
        | [occurrence] =>
          occurrence.value == 1200 &&
          occurrence.reads.map (·.coordinate) == [[1, 1], [1], [1]] &&
          occurrence.reads.map (·.value) == [3, 20, 20] &&
          occurrence.reads.map (·.origin.factor) == [some 0, some 1, some 2]
        | _ => false
      | _ => false
    | _, _, _, _, _, _ => false

private def chain : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Mid" [i], .tensor "End" [i], .tensor "Unwritten" [i]]
      stmts := stmts ++
        [.assign "Mid" [.free i] (rhs [[.read "B" [.axis i]]]),
         .assign "Mid" [.free i] (rhs [[.read "B" [.axis i]]]),
         .assign "End" [.free i] (rhs [[.read "Mid" [.axis i], .read "B" [.axis i]]])] }
    specs := specs ++ [⟨8, .defined, [2]⟩, ⟨9, .output, [2]⟩, ⟨10, .defined, [2]⟩] }

private def dependencyOrigin : SourceOrigin :=
  { side := .read, declaration := some 8, statement := some 5,
    term := some 0, factor := some 0 }

private def cycleOrigin : SourceOrigin :=
  { side := .read, declaration := some 9, statement := some 3,
    term := some 0, factor := some 0 }

private def cyclic : SourceSnapshot :=
  { chain with resolved := { chain.resolved with
      stmts := stmts ++
        [.assign "Mid" [.free i] (rhs [[.read "End" [.axis i]]]),
         .assign "Mid" [.free i] (rhs [[.read "B" [.axis i]]]),
         .assign "End" [.free i] (rhs [[.read "Mid" [.axis i]]])] } }

def ExplicitDependencyOrder : Bool :=
  match admitSource chain, admitSource cyclic with
  | .ok admitted, .ok cycle =>
    (Oracle.run admitted none == .error ⟨{}, .missingOrder⟩) &&
    (Oracle.run admitted (some [5, 7, 8, 8, 9, 10]) ==
      .error ⟨{ side := .declaration, declaration := some 8 }, .duplicateTarget 8⟩) &&
    (Oracle.run admitted (some [5, 7, 8, 9]) ==
      .error ⟨{ side := .declaration, declaration := some 10 }, .omittedTarget 10⟩) &&
    (Oracle.run admitted (some [3, 5, 7, 8, 9, 10]) ==
      .error ⟨{ side := .declaration, declaration := some 3 }, .unexpectedTarget 3⟩) &&
    (Oracle.run admitted (some [5, 7, 9, 8, 10]) ==
      .error ⟨dependencyOrigin, .dependencyNotEarlier 8⟩) &&
    (Oracle.run cycle (some [5, 7, 8, 9, 10]) ==
      .error ⟨cycleOrigin, .dependencyNotEarlier 9⟩) &&
    match Oracle.run admitted (some [5, 7, 8, 9, 10]),
        Oracle.run admitted (some [10, 8, 5, 9, 7]) with
    | .ok result, .ok reordered =>
      result == reordered &&
      values result 8 == some [20, 40] &&
      values result 9 == some [200, 800] &&
      values result 10 == some [0, 0] &&
      result.tensors.map (·.declaration) == [3, 4, 5, 6, 7, 8, 9, 10]
    | _, _ => false
  | _, _ => false

#guard AsymmetricPackingFiber
#eval AsymmetricPackingFiber
#guard ScalarZeroRepeatedAndBias
#eval ScalarZeroRepeatedAndBias
#guard ExplicitDependencyOrder
#eval ExplicitDependencyOrder

end SourceOracleTest
