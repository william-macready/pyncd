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

private def k : AxisSpec := ⟨"k", 92, .nat⟩
private def a : AxisSpec := ⟨"a", 93, .nat⟩

-- Direct schedules keep iteration slots plain instead of compiling them into scans.
def directMixed (source : AxisSpec) (extent : Nat) (slot : LHSSlot)
    (nonlin : Nonlin := .identity) : ScheduledProgram :=
  { decls := [.axis k (some 2), .axis source (some extent),
      .typedTensor .f64 "S" [k], .typedTensor .f64 "Y" [k],
      .typedTensor .f64 "X" [source]]
    stmts := [
      .plain (.scatter "S" [.free k]
        { body := { terms := [{ factors := [.read "Y" [.axis k]] }] },
          nonlin := .identity }),
      .plain (.assign "S" [slot]
        { body := { terms := [{ factors := [.read "X" [.axis source]] }] }, nonlin })]
    env := {}, extNames := ∅, explicitSizes := {} }

def directInputs (xs : Array Float) : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "Y" ⟨[2], #[10, 20]⟩
    |>.insert "X" ⟨[xs.size], xs⟩

def directSourceErrors (s : ScheduledProgram) (inputs : NamedDenseEnv) :
    Option CompileError × Option CompileError :=
  (match evalScheduled s inputs with
   | .error f => match f.error with | .compile e => some e | _ => none
   | .ok _ => none,
   match prepareEvalPlan s (InputSignature.ofDenseInputs inputs) with
   | .error f => match f.cause with | .sourceInvariant e => some e | _ => none
   | .ok _ => none)

def directBits (s : ScheduledProgram) (inputs : NamedDenseEnv) :=
  (((evalScheduled s inputs).toOption.bind fun r =>
      r.env["S"]?.map fun t => t.data.map Float.toBits),
   ((prepareEvalPlan s (InputSignature.ofDenseInputs inputs)).toOption.bind fun pp =>
      (runPreparedDense pp inputs).toOption.bind fun r =>
        r.env["S"]?.map fun t => t.data.map Float.toBits))

#eval directSourceErrors (directMixed a 3 (.iterAt a 1)) (directInputs #[1, 2, 99])
#eval directSourceErrors (directMixed a 3 (.iterNext a)) (directInputs #[1, 2, 99])

-- Both boundaries must reject before either scratch allocation or capability preflight.
#guard directSourceErrors (directMixed a 3 (.iterAt a 1)) (directInputs #[1, 2, 99]) ==
  (some (.multiWriterScatter "S"), some (.multiWriterScatter "S"))
#guard directSourceErrors (directMixed a 3 (.iterNext a)) (directInputs #[1, 2, 99]) ==
  (some (.multiWriterScatter "S"), some (.multiWriterScatter "S"))

-- Without a scatter writer, retain the legacy positional diagnostic.
#guard
  let s := directMixed a 3 (.iterAt a 1)
  let bare := { s with stmts := s.stmts.map fun
    | .plain (.scatter n ls r) => .plain (.assign n ls r)
    | stmt => stmt }
  directSourceErrors bare (directInputs #[1, 2, 99]) ==
    (some (.writerShapeMismatch "S" 2 0), some (.writerShapeMismatch "S" 2 0))

-- Distinct ordinary placement UIDs remain legal when their full extents agree.
#guard directBits (directMixed a 2 (.free a)) (directInputs #[1, 2]) ==
  (some (#[11, 22].map Float.toBits), some (#[11, 22].map Float.toBits))

private def normA : AxisSpec := { a with kind := .real }
#guard directBits (directMixed normA 2 (.freeNorm normA) (.axiswise .normalize none))
    (directInputs #[1, 3]) ==
  (some (#[10.25, 20.75].map Float.toBits), some (#[10.25, 20.75].map Float.toBits))

end LeanNCD.Eval.Plan.B5BoundaryTest
