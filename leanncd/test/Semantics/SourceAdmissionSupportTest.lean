import Semantics.SourceAdmissionFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures

namespace SourceAdmissionSupportTest

def A4 : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Ordered" [k, i, k]]
      stmts := stmts.take 1 ++
        [.assign "Ordered" [.free k, .free i, .free k]
          (rhs [[.read "A" [.axis i, .axis k]]])] }
    specs := specs ++ [⟨8, .output, [3, 2, 3]⟩] }

def A5 : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "K" [k]]
      stmts := stmts.take 2 ++
        [.assign "Y" [.free i]
          (rhs [[.read "K" [.axis k]], [.read "B" [.axis i]]])] }
    specs := specs ++ [⟨8, .input, [3]⟩]
    inputs := inputs ++ [⟨8, [3], [7, 11, 13]⟩] }

def A6 : SourceSnapshot :=
  { snapshot with resolved := { snapshot.resolved with
    stmts := stmts ++ [.assign "Y" [.free i]
      (rhs [[.read "A" [.axis i, .axis k]], [.read "B" [.axis i]]])] } }

private def statementView (s : SourceSnapshot) (index : Nat) : Option StatementView := do
  let (_, _, statements) ← admissionView s
  statements[index]?

private structure SupportView where
  origin : SourceOrigin
  readOrigins : List SourceOrigin
  support : List UID
  bound : List (UID × Nat)
  context : List (UID × Nat)
  localReads : List (List UID)
  pure : Bool
  deriving DecidableEq, Repr

private def supportView (s : SourceSnapshot) (index : Nat) : Option (List SupportView) := do
  let admitted ← (admitSource s).toOption
  let statement ← admitted.statements[index]?
  pure (statement.terms.map fun term =>
    ⟨term.origin, term.sourceReads.map CheckedRead.origin, term.support,
     term.partition.bound.map (fun a => (a.uid, a.extent)),
     term.partition.context.axes.map (fun a => (a.uid, a.extent)),
     term.operands.map (fun read => read.slots.uids), admitPure term⟩)

private def projectAt (slots : Slots ctx sh) (index : Nat) : Option (List Int) :=
  let layout := canonicalLayout ctx
  if h : index < layout.count then
    some (List.ofFn (slots.project (layout.enumerate ⟨index, h⟩)).raw)
  else none

private structure DestinationView where
  origin : SourceOrigin
  shape : List Nat
  context : List (UID × Nat)
  sourceSlots : List UID
  slots : List UID
  projection : Option (List Int)
  readProjections : List (List (Option (List Int)))
  deriving DecidableEq, Repr

private def destinationView (s : SourceSnapshot) (index : Nat) :
    Option DestinationView := do
  let admitted ← (admitSource s).toOption
  let statement ← admitted.statements[index]?
  let output := statement.output
  pure ⟨output.origin,
    (admitted.source.table.declarations.signature output.tensor).axes.map Axis.extent,
    output.context.axes.map (fun a => (a.uid, a.extent)),
    output.sourceSlots.uids, output.slots.uids, projectAt output.slots 5,
    statement.terms.map fun term =>
      term.operands.map fun read => projectAt read.slots 5⟩

#guard statementView A4 1 =
  some ⟨1, [3, 7, 3], [3, 7],
    [⟨[], .pure, [(some 0, some 0, [7, 3])]⟩]⟩

#guard destinationView A4 1 = some
  ⟨⟨.output, some 8, some 1, none, none, none⟩,
   [3, 2, 3], [(3, 3), (7, 2)], [3, 7, 3], [3, 7, 3],
   some [2, 1, 2], [[some [1, 2]]]⟩

#guard supportView A4 1 = some
  [⟨⟨.read, none, some 1, some 0, none, none⟩,
    [⟨.read, some 3, some 1, some 0, some 0, none⟩],
    [7, 3], [], [(3, 3), (7, 2)], [[7, 3]], true⟩]

#guard statementView A5 2 =
  some ⟨2, [7], [7],
    [⟨[3], .broadcast, [(some 0, some 0, [3])]⟩,
     ⟨[], .pure, [(some 1, some 0, [7])]⟩]⟩

#guard supportView A5 2 = some
  [⟨⟨.read, none, some 2, some 0, none, none⟩,
    [⟨.read, some 8, some 2, some 0, some 0, none⟩],
    [3], [(3, 3)], [(7, 2), (3, 3)], [[3]], false⟩,
   ⟨⟨.read, none, some 2, some 1, none, none⟩,
    [⟨.read, some 4, some 2, some 1, some 0, none⟩],
    [7], [], [(7, 2)], [[7]], true⟩]

#guard statementView A6 3 =
  some ⟨3, [7], [7],
    [⟨[3], .pure, [(some 0, some 0, [7, 3])]⟩,
     ⟨[], .pure, [(some 1, some 0, [7])]⟩]⟩

#guard supportView A6 3 = some
  [⟨⟨.read, none, some 3, some 0, none, none⟩,
    [⟨.read, some 3, some 3, some 0, some 0, none⟩],
    [7, 3], [(3, 3)], [(7, 2), (3, 3)], [[7, 3]], true⟩,
   ⟨⟨.read, none, some 3, some 1, none, none⟩,
    [⟨.read, some 4, some 3, some 1, some 0, none⟩],
    [7], [], [(7, 2)], [[7]], true⟩]

#eval ("A4", statementView A4 1, destinationView A4 1, supportView A4 1)
#eval ("A5", statementView A5 2, supportView A5 2)
#eval ("A6", statementView A6 3, supportView A6 3)

end SourceAdmissionSupportTest
