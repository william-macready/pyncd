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

/-! ## The `f64` element-type spelling and the non-reserved element-type tokens -/

-- `f32prog` with exactly one field changed (`f32` -> `f64`): the new spelling elaborates to
-- `.typedTensor .f64`, for every shape in the group. Without the `f64` grammar arm this does not
-- parse at all, and without its `elabTLElemType` arm it is an error, not a silent `.f32`.
private def f64prog : TLProgram := tlprog!{
  tensor f64 A(q, s), B(x, y)
  A[q, s.] := softmax(where s ≤ q)(Q[q, d] · K[s, d])
}

#guard f64prog.decls ==
  [ Decl.typedTensor .f64 "A" [ax0 "q", ax0 "s"]
  , Decl.typedTensor .f64 "B" [ax0 "x", ax0 "y"] ]
#guard f64prog.stmts.length == 1
#guard f64prog.decls != f32prog.decls

-- The element-type words are NOT reserved tokens (`SyntaxTest.lean` pins that a `def f64` still
-- parses). As a tensor NAME, with no element type, `f64` is a plain tensor called `f64`: the typed
-- rule needs an identifier after the element type, so `f64(i)` can only be a named shape.
private def namedF64prog : TLProgram := tlprog!{
  tensor f64(i)
  Y[i] := f64[i]
}
#guard namedF64prog.decls == [Decl.tensor "f64" [ax0 "i"]]

private def namedF32prog : TLProgram := tlprog!{
  tensor f32(i)
  Y[i] := f32[i]
}
#guard namedF32prog.decls == [Decl.tensor "f32" [ax0 "i"]]

end LeanNCD
