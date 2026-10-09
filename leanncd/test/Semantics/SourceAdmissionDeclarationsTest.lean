import Semantics.SourceAdmissionFixtures
import LeanNCD.Semantics.RationalReference

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures

namespace SourceAdmissionDeclarationsTest

private def identitySnapshot : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Scalar" []]
      stmts := stmts ++ [.assign "Scalar" [] (rhs [[]])] }
    specs := specs ++ [⟨8, .output, []⟩] }

private def statementViewAt (s : SourceSnapshot) (original : Nat) :
    Option StatementView := do
  let (_, _, statements) ← admissionView s
  statements.find? (fun st => st.original == original)

private def statementValues (source : AdaptedSource) (st : AdmittedStatement source) :
    List (Option ℚ) :=
  let layout := canonicalLayout st.output.context.axes
  let store : Store RationalReference.Carrier source.table.declarations := fun _ => 37
  List.ofFn fun p : Fin layout.count =>
    foldValues (RationalReference.ops ()) (st.terms.map fun term =>
      interpret RationalReference.ops store
        (contract (r := RationalReference.registry) term.partition.bound term.operands
          (fun (_ : Unit) bound =>
            term.partition.context_axes.symm ▸
              (appendEquiv st.output.context.axes term.partition.bound).symm
                (layout.enumerate p, bound))) ())

private def statementValuesAt (s : SourceSnapshot) (original : Nat) :
    Option (List (Option ℚ)) := do
  let admitted ← (admitSource s).toOption
  let statement ← admitted.statements.find? (fun st => st.original == original)
  pure (statementValues admitted.source statement)

def A7 : Option (StatementView × List (Option ℚ) × StatementView × List (Option ℚ)) := do
  let broadcast ← statementViewAt identitySnapshot 1
  let broadcastValues ← statementValuesAt identitySnapshot 1
  let scalar ← statementViewAt identitySnapshot 3
  let scalarValues ← statementValuesAt identitySnapshot 3
  pure (broadcast, broadcastValues, scalar, scalarValues)

set_option synthInstance.maxSize 512 in
#guard A7 = some
  (⟨1, [7, 7], [7], [⟨[], .broadcast, []⟩]⟩, [some 1, some 1],
   ⟨3, [], [], [⟨[], .pure, []⟩]⟩, [some 1])

#eval A7

def A8 : Option (StatementView × List (Option ℚ)) := do
  let statement ← statementViewAt snapshot 2
  let values ← statementValuesAt snapshot 2
  pure (statement, values)

#guard A8 = some (⟨2, [7], [7], []⟩, [some 0, some 0])

#eval A8

private def duplicateAxisSnapshot : SourceSnapshot :=
  { snapshot with resolved := { snapshot.resolved with
    decls := decls ++ [.axis i (some 2)] } }

def A9 : Bool :=
  match admitSource duplicateAxisSnapshot with
  | .ok _ => false
  | .error diagnostic =>
    match diagnostic.cause with
    | .duplicateAxis uid =>
      uid == 7 && diagnostic.stage == .declarations &&
        diagnostic.origin == { side := .declaration, declaration := some 8 }
    | _ => false

#guard A9

#eval match admitSource duplicateAxisSnapshot with
  | .error diagnostic => reprStr diagnostic
  | .ok _ => "unexpected duplicate axis admission"

private def distinctAxisSnapshot : SourceSnapshot :=
  { snapshot with resolved := { snapshot.resolved with
    decls := decls ++ [.axis { i with uid := 13 } (some 2)] } }

#guard (admitSource distinctAxisSnapshot).isOk

#guard (admissionView distinctAxisSnapshot).map (fun (axes, _, _) => axes) =
  some [7, 3, 11, 13]

set_option synthInstance.maxSize 512 in
#guard (admissionView distinctAxisSnapshot).map (fun (_, table, statements) =>
    (table, statements)) =
  (admissionView snapshot).map (fun (_, table, statements) => (table, statements))

end SourceAdmissionDeclarationsTest
