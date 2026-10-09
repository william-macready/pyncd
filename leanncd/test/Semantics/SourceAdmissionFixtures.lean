import LeanNCD.Semantics.Source.Admission

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source

namespace SourceAdmissionFixtures

def i : AxisSpec := ⟨"i", 7, .nat⟩
def k : AxisSpec := ⟨"k", 3, .nat⟩
def e : AxisSpec := ⟨"empty", 11, .nat⟩

def decls : List Decl :=
  [.axis i (some 2), .axis k (some 3), .axis e (some 0),
   .tensor "A" [i, k], .tensor "B" [i], .tensor "Y" [i],
   .tensor "Empty" [e], .tensor "Diagonal" [i, i]]

def rhs (terms : List (List Factor)) : RHSExpr :=
  ⟨⟨terms.map ProdTerm.mk⟩, .identity, .sum⟩

def stmts : List Stmt :=
  [.assign "Y" [.free i] (rhs [[.read "A" [.axis i, .axis k]], [.read "B" [.axis i]]]),
   .assign "Diagonal" [.free i, .free i] (rhs [[]]),
   .assign "Y" [.free i] (rhs [])]

def specs : List TensorSpec :=
  [⟨3, .input, [2, 3]⟩, ⟨4, .input, [2]⟩, ⟨5, .output, [2]⟩,
   ⟨6, .input, [0]⟩, ⟨7, .defined, [2, 2]⟩]

def inputs : List InputBinding :=
  [⟨3, [2, 3], [1, 2, 3, 4, 5, 6]⟩, ⟨4, [2], [10, 20]⟩, ⟨6, [0], []⟩]

def snapshot : SourceSnapshot := ⟨⟨decls, stmts, {}, ∅⟩, specs, inputs⟩

structure TermView where
  bound : List UID
  classification : TermClass
  reads : List (Option Nat × Option Nat × List UID)
  deriving DecidableEq, Repr

structure StatementView where
  original : Nat
  slots : List UID
  context : List UID
  terms : List TermView
  deriving DecidableEq, Repr

def admissionView (s : SourceSnapshot) :
    Option (List UID × List (Nat × TensorRole × List Nat) × List StatementView) :=
  (admitSource s).toOption.map fun admitted =>
    (admitted.source.context.axes.map Axis.uid,
     admitted.source.table.entries.map (fun t => (t.declaration, t.role, t.axes.map Axis.extent)),
     admitted.statements.map fun st =>
       (⟨st.original, st.output.indices, st.output.context.axes.map Axis.uid,
        st.terms.map fun term =>
          ⟨term.partition.bound.map Axis.uid, term.classification,
           term.sourceReads.map fun r => (r.origin.term, r.origin.factor, r.indices)⟩⟩ :
         StatementView))

end SourceAdmissionFixtures
