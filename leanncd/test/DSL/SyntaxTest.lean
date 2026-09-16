import LeanNCD.DSL.Syntax

namespace LeanNCD

-- The categories + rules PARSE (quotation elaborates to Syntax). No elaborator yet.
#check (`(tl_decl| tensor A(i)) : Lean.MacroM _)           -- tensor shapes list axis NAMES only
-- Fixture 2 (grammar half): the SAME production with an explicit element type parses too. What
-- the two spellings ELABORATE to (`Decl.typedTensor .f32 …` vs. the unchanged `Decl.tensor …`) is
-- pinned in `ParseProgramTest.lean`; this file declares only the grammar and has no elaborator.
#check (`(tl_decl| tensor f32 A(i)) : Lean.MacroM _)
#check (`(tl_decl| axis l : ℕ = 3) : Lean.MacroM _)        -- an axis-size declaration
#check (`(tl_stmt| A[q, s.] := softmax(Q[q, d])) : Lean.MacroM _)  -- `s.` marks the norm axis
#check (`(tl_stmt| Y[i, j] := W[i, k] · X[k, j]) : Lean.MacroM _)
#check (`(tl_bool_expr| s ≤ q) : Lean.MacroM _)
#check (`(tl_rhs| softmax(where s ≤ q)(Q[q, d] · K[s, d])) : Lean.MacroM _)

end LeanNCD
