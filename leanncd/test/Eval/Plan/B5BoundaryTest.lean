import Eval.Plan.B5NativeTest

namespace LeanNCD.Eval.Plan.B5BoundaryTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan.B5NativeTest Std

private def i : AxisSpec := ⟨"i", 90, .nat⟩
private def j : AxisSpec := ⟨"j", 91, .nat⟩

private def withPlacement (p : TLProgram) (slot : LHSSlot) : TLProgram :=
  { p with stmts := p.stmts.map fun
    | .assign n _ r | .scatter n _ r => .scatter n [slot] r
    | s => s }

-- Clone overlap; the extra source axis cancels before geometry classification.
def cancellation : TLProgram :=
  withPlacement { overlap with decls := overlap.decls ++ [.axis j (some 1)] }
    (.affine (.affine 0 [(2, i), (1, j), (-1, j)]))

-- Clone cancellation; keep two nonzero coefficients and match the declared extent.
def twoAxes : TLProgram :=
  withPlacement
    { cancellation with decls := cancellation.decls.map fun
      | .axis a n => if a.name == "k" then .axis a (some 3) else .axis a n
      | d => d }
    (.affine (.affine 0 [(1, i), (1, j)]))

-- Clone overlap; explicit scatter bypasses the surface assignment's constant guard.
def explicitConstant : TLProgram :=
  withPlacement
    { overlap with decls := overlap.decls.map fun
      | .axis a n => if a.name == "k" then .axis a (some 2) else .axis a n
      | d => d }
    (.affine (.const 1))

def predicateDest : TLProgram :=
  { interleave with decls := interleave.decls.map fun
    | .typedTensor _ "S" axes => .predicate "S" axes
    | d => d }

-- Clone undeclared mixed; a bare explicit scatter is not a fallback assign.
def bareScatterFallback : TLProgram :=
  { undeclare mixed with stmts := mixed.stmts.map fun
    | .assign n slots rhs => .scatter n slots rhs
    | s => s }

def lateMismatch : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 4
  axis l : ℕ = 3
  axis m : ℕ = 2
  tensor f32 A(i, l), B(i, l), Extra(k, m), S(k, l)
  S[2*i, l] := A[i, l]
  S[2*i, l] := B[i, l]
  S[k, m] := Extra[k, m]
}

def late64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "A" ⟨[2, 3], #[1, 2, 3, 4, 5, 6]⟩
    |>.insert "B" ⟨[2, 3], #[1, 2, 3, 4, 5, 6]⟩
    |>.insert "Extra" ⟨[4, 2], #[1, 2, 3, 4, 5, 6, 7, 8]⟩
def late32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[2, 3], #[1, 2, 3, 4, 5, 6]⟩
    |>.insert "B" ⟨[2, 3], #[1, 2, 3, 4, 5, 6]⟩
    |>.insert "Extra" ⟨[4, 2], #[1, 2, 3, 4, 5, 6, 7, 8]⟩

#eval sourceError cancellation
#eval obs cancellation
#eval sourceError twoAxes
#eval sourceError explicitConstant
#eval sourceError predicateDest
#eval sourceError bareScatterFallback
#eval refShape lateMismatch late64
#eval planShape lateMismatch late64
#eval planShape32 lateMismatch late32

#guard sourceError cancellation == none
#guard agree cancellation in64 in32 #[-12, 0, -5, 0] #[-12, 0, -5, 0]
#guard sourceError twoAxes == some (.multiWriterScatter "S")
#guard sourceError explicitConstant == some (.multiWriterScatter "S")
#guard sourceError predicateDest == some (.multiWriterScatter "S")
#guard sourceError bareScatterFallback == some (.multiWriterNeedsDeclaredShape "S")
#guard refShape lateMismatch late64 == some (.writerExtentMismatch "S" 3 1 3 2)
#guard planShape lateMismatch late64 == some (.writerExtentMismatch "S" 3 1 3 2)
#guard planShape32 lateMismatch late32 == some (.writerExtentMismatch "S" 3 1 3 2)

end LeanNCD.Eval.Plan.B5BoundaryTest
