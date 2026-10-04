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

-- The typed form whose ITEM is named like an element word: the first word is the element type, the
-- second the name (the typed rule consumes the element type first, so no ambiguity).
private def typedNamedF32prog : TLProgram := tlprog!{
  tensor f32 f32(i)
  Y[i] := f32[i]
}
#guard typedNamedF32prog.decls == [Decl.typedTensor .f32 "f32" [ax0 "i"]]

-- Element words are legal AXIS names too (they are ordinary identifiers).
private def axisNamedF32prog : TLProgram := tlprog!{
  tensor A(f32, i)
  Y[f32, i] := A[f32, i]
}
#guard axisNamedF32prog.decls == [Decl.tensor "A" [ax0 "f32", ax0 "i"]]

/-! ## The typed linear form (`linear f64 W(a, b) bias, V(c, d)`) -/

-- Grouped, with and without `bias`: the element type applies to EVERY item in the group, and each
-- item keeps its own axis list and its own bias flag.
private def typedLinProg : TLProgram := tlprog!{
  linear f64 W(a, b) bias, V(c, d)
  Y[a] := W[a, b] · X[b]
}

#guard typedLinProg.decls ==
  [ Decl.typedLinear .f64 "W" [ax0 "a", ax0 "b"] true
  , Decl.typedLinear .f64 "V" [ax0 "c", ax0 "d"] false ]
#guard typedLinProg.stmts.length == 1

private def typedLinF32Prog : TLProgram := tlprog!{
  linear f32 W(a, b)
  Y[a] := W[a, b] · X[b]
}
#guard typedLinF32Prog.decls == [Decl.typedLinear .f32 "W" [ax0 "a", ax0 "b"] false]

-- The same group with the element type removed is still the untyped `Decl.linear`, unchanged
-- (binary64): the typed form is a separate constructor, not a reinterpretation of the old one.
private def plainLinProg : TLProgram := tlprog!{
  linear W(a, b) bias, V(c, d)
  Y[a] := W[a, b] · X[b]
}
#guard plainLinProg.decls ==
  [ Decl.linear "W" [ax0 "a", ax0 "b"] true, Decl.linear "V" [ax0 "c", ax0 "d"] false ]

-- A linear item NAMED `f64` (no element type) is a plain linear named `f64`, exactly as for
-- `tensor`: the typed rule needs a further item after the element type.
private def namedF64LinProg : TLProgram := tlprog!{
  linear f64(a, b)
  Y[a] := f64[a, b] · X[b]
}
#guard namedF64LinProg.decls == [Decl.linear "f64" [ax0 "a", ax0 "b"] false]

-- The typed linear form whose ITEM is named `f64`: element type first, then the name.
private def typedNamedF64LinProg : TLProgram := tlprog!{
  linear f64 f64(a, b)
  Y[a] := f64[a, b] · X[b]
}
#guard typedNamedF64LinProg.decls == [Decl.typedLinear .f64 "f64" [ax0 "a", ax0 "b"] false]

/-! ## The complex element-type spellings (`complex64`, `complex128`)

JAX/NumPy TOTAL-bit names. They ELABORATE like `f32`/`f64` (one `TensorElementType` constructor
each); every such declaration is then rejected at compile (`ComplexElementTypeTest.lean`). -/

-- `f32prog` with the element type changed: one shape, then a two-shape group.
private def c64prog : TLProgram := tlprog!{
  tensor complex64 A(i)
  Y[i] := A[i]
}
#guard c64prog.decls == [Decl.typedTensor .complex64 "A" [ax0 "i"]]

private def c128prog : TLProgram := tlprog!{
  tensor complex128 A(i), B(j)
  Y[i] := A[i]
}
#guard c128prog.decls ==
  [Decl.typedTensor .complex128 "A" [ax0 "i"], Decl.typedTensor .complex128 "B" [ax0 "j"]]

-- `typedLinF32Prog` with the element type changed, plus `bias`.
private def c64LinProg : TLProgram := tlprog!{
  linear complex64 W(a, b) bias
  Y[a] := W[a, b] · X[b]
}
#guard c64LinProg.decls == [Decl.typedLinear .complex64 "W" [ax0 "a", ax0 "b"] true]

-- A tensor NAMED `complex128` (no element type) is a plain tensor, exactly as for `f64`.
private def namedC128prog : TLProgram := tlprog!{
  tensor complex128(i)
  Y[i] := complex128[i]
}
#guard namedC128prog.decls == [Decl.tensor "complex128" [ax0 "i"]]

end LeanNCD
