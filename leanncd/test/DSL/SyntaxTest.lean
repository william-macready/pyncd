import LeanNCD.DSL.Syntax

namespace LeanNCD

-- The categories + rules PARSE (quotation elaborates to Syntax). No elaborator yet.
#check (`(tl_decl| tensor A(i)) : Lean.MacroM _)           -- tensor shapes list axis NAMES only
-- Fixture 2 (grammar half): the SAME production with an explicit element type parses too. What
-- the two spellings ELABORATE to (`Decl.typedTensor .f32 …` vs. the unchanged `Decl.tensor …`) is
-- pinned in `ParseProgramTest.lean`; this file declares only the grammar and has no elaborator.
#check (`(tl_decl| tensor f32 A(i)) : Lean.MacroM _)
#check (`(tl_decl| tensor f64 A(i)) : Lean.MacroM _)       -- the explicit spelling of the default

-- The element-type words are NOT reserved tokens (`declare_syntax_cat tl_elem_type (behavior :=
-- symbol)` with `&"f32"`/`&"f64"`): they stay ordinary Lean identifiers in any file that imports
-- this grammar. As reserved tokens these two `def`s were a parse error ("unexpected token 'f32'").
private def f32 : Nat := 1
private def f64 : Nat := 1
#guard f32 + f64 == 2
-- The complex words (spelled, then rejected at compile — `ComplexElementTypeTest.lean`) follow the
-- same non-reserved form: they parse as element types AND stay ordinary identifiers.
#check (`(tl_decl| tensor complex64 A(i)) : Lean.MacroM _)
#check (`(tl_decl| tensor complex128 A(i)) : Lean.MacroM _)
private def complex64 : Nat := 1
private def complex128 : Nat := 1
#guard complex64 + complex128 == 2
#check (`(tl_decl| axis l : ℕ = 3) : Lean.MacroM _)        -- an axis-size declaration
#check (`(tl_stmt| A[q, s.] := softmax(Q[q, d])) : Lean.MacroM _)  -- `s.` marks the norm axis
#check (`(tl_stmt| Y[i, j] := W[i, k] · X[k, j]) : Lean.MacroM _)
#check (`(tl_bool_expr| s ≤ q) : Lean.MacroM _)
#check (`(tl_rhs| softmax(where s ≤ q)(Q[q, d] · K[s, d])) : Lean.MacroM _)

end LeanNCD
