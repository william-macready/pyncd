import LeanNCD.DSL.Elab

namespace LeanNCD

-- The term macro: parse a whole program into a TLProgram value (embedded via ToExpr).
private def prog : TLProgram := tlprog!{
  tensor A(q, s)
  A[q, s.] := softmax(where s ≤ q)(Q[q, d] · K[s, d])
}

#guard prog.decls.length == 1
#guard prog.stmts.length == 1

-- a scan-step LHS (`l +1`, spaced) and a base-case (`0`) parse:
private def scanprog : TLProgram := tlprog!{
  G[j, 0]   := X[j]
  G[j, l +1] := relu(G[j, l] · W[j, k])
}
#guard scanprog.stmts.length == 2

/-! ## Explicit tensor element types (`tensor f32 …`) -/

-- Fixture 1: `prog`'s ordinary single-tensor declaration, with `f32` inserted and a SECOND
-- comma-separated shape in the same declaration — the element type applies to every shape in the
-- group, and each shape keeps its own axis list in source order.
private def f32prog : TLProgram := tlprog!{
  tensor f32 A(q, s), B(x, y)
  A[q, s.] := softmax(where s ≤ q)(Q[q, d] · K[s, d])
}

private def ax0 (nm : String) : AxisSpec := { name := nm, uid := 0, kind := .real }

#guard f32prog.decls ==
  [ Decl.typedTensor .f32 "A" [ax0 "q", ax0 "s"]
  , Decl.typedTensor .f32 "B" [ax0 "x", ax0 "y"] ]
#guard f32prog.stmts.length == 1

-- Fixture 2 (elaboration half; the grammar half is in `SyntaxTest.lean`): the SAME declaration
-- with `f32` removed still elaborates to the original `Decl.tensor`, unchanged — the new element
-- type is a separate constructor, not a reinterpretation of the existing spelling.
private def plainprog : TLProgram := tlprog!{
  tensor A(q, s), B(x, y)
  A[q, s.] := softmax(where s ≤ q)(Q[q, d] · K[s, d])
}

#guard plainprog.decls ==
  [ Decl.tensor "A" [ax0 "q", ax0 "s"], Decl.tensor "B" [ax0 "x", ax0 "y"] ]
#guard prog.decls == [Decl.tensor "A" [ax0 "q", ax0 "s"]]

end LeanNCD
