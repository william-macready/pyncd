import Eval.Plan.B5NativeTest

/-!
# Scatter geometry slice B (surface): multi-axis `Y[a + b]` and constant `S[=3]` through `tlprog!`

The parse/elab pins live in `DSL/ParseProgramTest.lean`; this module runs SURFACE-written programs
end to end (reference evaluator, checked binary64 plan, checked binary32 plan) and compares them with
the hand-built forms of `ScatterGeometryTest`. It imports only `B5NativeTest` so a mutant in an older
test module cannot mask a fixture here.

Inputs: `A[a] = [1,2,3,4]`, `B[b] = [1,10,100]`, as in `ScatterGeometryTest`.
-/

namespace LeanNCD.Eval.Plan.ScatterSurfaceTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.Eval.Plan.B5NativeTest Std

private def a : AxisSpec := ⟨"a", 90, .nat⟩
private def b : AxisSpec := ⟨"b", 91, .nat⟩
private def k : AxisSpec := ⟨"k", 92, .nat⟩

def convIn64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "A" ⟨[4], #[1, 2, 3, 4]⟩ |>.insert "B" ⟨[3], #[1, 10, 100]⟩
def convIn32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[4], #[1, 2, 3, 4]⟩ |>.insert "B" ⟨[3], #[1, 10, 100]⟩

/-- Shape and cells of `S` in the three legs (bits, so `-0`/NaN cannot hide a difference). -/
def cells (p : TLProgram) (i := convIn64) (j := convIn32) :=
  ((ref64 p i).bind fun e => e["S"]?.map fun t => (t.shape, t.data.map Float.toBits),
   (run64 p i).bind fun e => e["S"]?.map fun t => (t.shape, t.data.map Float.toBits),
   (run32 p j).bind fun e => e["S"]?.map fun t => (t.shape, t.data.map Float32.toBits))

/-- Why compilation (or the capability preflight) refuses `p`; `none` if it is accepted. -/
def compErr (p : TLProgram) : Option String :=
  match p.compileToScheduled.run 0 with
  | .ok s _ => match capabilityPreflight s with
      | .error e => some s!"preflight {repr e}"
      | .ok _ => none
  | .error e _ => some s!"compile {repr e}"

/-- Donor: `ScatterGeometryTest.convOf sumSlot`, hand-built (UIDs 90/91/92). -/
def convProg : TLProgram :=
  { decls := [.axis a (some 4), .axis b (some 3), .axis k none,
      .typedTensor .f32 "A" [a], .typedTensor .f32 "B" [b], .typedTensor .f32 "S" [k]]
    stmts := [.scatter "S" [.affine (.affine 0 [(1, a), (1, b)])]
      { body := { terms := [{ factors := [.read "A" [.axis a], .read "B" [.axis b]] }] }
        nonlin := .identity, agg := .sum }] }

-- U4: the SURFACE `Y[a + b]` equals the programmatic `conv` in shape and cells in all three legs, and
-- is the polynomial product (reach 0..5, extent 6). A surface arm that dropped a term or read it as
-- `.shift` would change the cells.
def convSurf : TLProgram := tlprog!{
  axis a : ℕ = 4, b : ℕ = 3, k : ℕ
  tensor f32 A(a), B(b), S(k)
  S[a + b] := A[a] · B[b]
}
#guard cells convSurf == cells convProg
#guard agree convSurf convIn64 convIn32 #[1, 12, 123, 234, 340, 400] #[1, 12, 123, 234, 340, 400]
#guard (cells convSurf).1.map (·.1) == some [6]

-- U4 (bias and coefficient together): `2*a + b + 1` has extent 10 (cells below, observed); a dropped
-- bias shifts every cell by one, a dropped coefficient collapses the stride.
def biasSurf : TLProgram := tlprog!{
  axis a : ℕ = 4, b : ℕ = 3, k : ℕ
  tensor f32 A(a), B(b), S(k)
  S[2*a + b + 1] := A[a] · B[b]
}
#guard agree biasSurf convIn64 convIn32 #[0, 1, 10, 102, 20, 203, 30, 304, 40, 400]
  #[0, 1, 10, 102, 20, 203, 30, 304, 40, 400]
#guard (cells biasSurf).1.map (·.1) == some [10]

-- U4 (constant-writer group): the surface spelling of the engine fixture F1 (two `S[=3]` writers plus a
-- bare writer into a pinned declaration `k = 8`). Collisions SUM: cell 3 is 10 + 10 + 4 = 24. An
-- overwrite reading gives 4 or 10; reading `=3` as the lone numeral `3` is a scan base and is refused.
def f1Surf : TLProgram := tlprog!{
  axis a : ℕ = 4, k : ℕ = 8
  tensor f32 A(a), S(k)
  S[=3] := A[a]
  S[=3] := A[a]
  S[a] := A[a]
}
#guard compErr f1Surf == none
#guard agree f1Surf convIn64 convIn32 #[1, 2, 3, 24, 0, 0, 0, 0] #[1, 2, 3, 24, 0, 0, 0, 0]
#guard (cells f1Surf).1.map (·.1) == some [8]

-- U3 (end to end): a lone `=5` writer into the pinned declaration writes the sum of `A` at cell 5.
def constPinSurf : TLProgram := tlprog!{
  axis a : ℕ = 4, k : ℕ = 8
  tensor f32 A(a), S(k)
  S[=5] := A[a]
}
#guard agree constPinSurf convIn64 convIn32 #[0, 0, 0, 0, 0, 10, 0, 0] #[0, 0, 0, 0, 0, 10, 0, 0]
-- ... and `S[3]` (no `=`) is the scan base case: refused, there is no advancing step.
def constLoneSurf : TLProgram := tlprog!{
  axis a : ℕ = 4, k : ℕ = 8
  tensor f32 A(a), S(k)
  S[3] := A[a]
}
#guard compErr constLoneSurf == some "preflight LeanNCD.Eval.Plan.CapabilityError.noAdvancingAxis \"S\""

-- U5 (observed, documented behaviour; no new validation).
-- A repeated axis `a + a` is ACCEPTED and behaves as `2*a`: extent 8 (stride-2 rule, as `Out[2*i]`),
-- `b` summed into each cell: A[a] * (1+10+100).
def aaSurf : TLProgram := tlprog!{
  axis a : ℕ = 4, b : ℕ = 3, k : ℕ
  tensor f32 A(a), B(b), S(k)
  S[a + a] := A[a] · B[b]
}
#guard compErr aaSurf == none
#guard agree aaSurf convIn64 convIn32 #[111, 0, 222, 0, 333, 0, 444, 0] #[111, 0, 222, 0, 333, 0, 444, 0]
-- A zero coefficient `0*a + b` is ACCEPTED: `a` no longer places the write, so it is a collision axis
-- summed into cell b (10 * B[b]); extent 3. (The single-axis `Out[0*i]` is rejected as out of range; the
-- multi-axis form is not, because `b` still places the write.)
def zcSurf : TLProgram := tlprog!{
  axis a : ℕ = 4, b : ℕ = 3, k : ℕ
  tensor f32 A(a), B(b), S(k)
  S[0*a + b] := A[a] · B[b]
}
#guard compErr zcSurf == none
#guard agree zcSurf convIn64 convIn32 #[10, 100, 1000] #[10, 100, 1000]
-- An axis left UNSIZED in its declaration (`a`, `b` without `= n`) is sized from the inputs: the same
-- cells as `convSurf`.
def unsizedSurf : TLProgram := tlprog!{
  axis a : ℕ, b : ℕ, k : ℕ
  tensor f32 A(a), B(b), S(k)
  S[a + b] := A[a] · B[b]
}
#guard cells unsizedSurf == cells convProg
-- An EMPTY axis (`b = 0`, input `B = []`) is accepted: shape `[4]`, all cells 0 in all three legs.
def emptySurf : TLProgram := tlprog!{
  axis a : ℕ = 4, b : ℕ = 0, k : ℕ
  tensor f32 A(a), B(b), S(k)
  S[a + b] := A[a] · B[b]
}
def emptyIn64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "A" ⟨[4], #[1, 2, 3, 4]⟩ |>.insert "B" ⟨[0], #[]⟩
def emptyIn32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[4], #[1, 2, 3, 4]⟩ |>.insert "B" ⟨[0], #[]⟩
#guard agree emptySurf emptyIn64 emptyIn32 #[0, 0, 0, 0] #[0, 0, 0, 0]
#guard (cells emptySurf emptyIn64 emptyIn32).1.map (·.1) == some [4]

-- U6: a `[=n]` slot or a multi-axis slot inside a SCAN statement fails loudly when built from the
-- surface (the existing programmatic pins are in `CompileTest`; these exercise `lowerArith` too).
-- Linear bodies, so the nonlinear-scatter refusal does not mask the slot refusal. Baseline accepted.
def scanBase : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(j, l), X(j), W(j, k)
  G[j, 0] := X[j]
  G[j, l +1] := G[j, l] · W[j, k]
}
#guard compErr scanBase == none
def scanConstStep : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(j, l), X(j), W(j, k)
  G[j, 0] := X[j]
  G[=2, l +1] := G[j, l] · W[j, k]
}
#guard compErr scanConstStep == some "compile LeanNCD.CompileError.overlappingScatter \"G\""
def scanConstBase : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(j, l), X(j), W(j, k)
  G[=1, 0] := X[j]
  G[j, l +1] := G[j, l] · W[j, k]
}
#guard compErr scanConstBase == some "compile LeanNCD.CompileError.overlappingScatter \"G\""
def scanMultiStep : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(j, l), X(j), W(j, k)
  G[j, 0] := X[j]
  G[j + k, l +1] := G[j, l] · W[j, k]
}
#guard compErr scanMultiStep ==
  some "preflight LeanNCD.Eval.Plan.CapabilityError.multiAxisScatterLhs \"G: affine LHS slot\""

end LeanNCD.Eval.Plan.ScatterSurfaceTest
