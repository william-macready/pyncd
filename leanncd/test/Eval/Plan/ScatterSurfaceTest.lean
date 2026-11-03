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
-- F3-b stage 1: a scan statement may carry a surface constant slot `[=n]`, lowered to a unit-axis
-- placement (extent n + 1) exactly as at top level. Inputs: `X(j) = [1,2,3]`, `W(j,k) = 1..6` (3x2).
def scanIn64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "X" ⟨[3], #[1, 2, 3]⟩ |>.insert "W" ⟨[3, 2], #[1, 2, 3, 4, 5, 6]⟩
def scanIn32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "X" ⟨[3], #[1, 2, 3]⟩ |>.insert "W" ⟨[3, 2], #[1, 2, 3, 4, 5, 6]⟩
/-- Like `cells` but for the tensor named `nm` (the scan state), under the scan inputs. -/
def cellsOf (nm : String) (p : TLProgram) (i := scanIn64) (j := scanIn32) :=
  ((ref64 p i).bind fun e => e[nm]?.map fun t => (t.shape, t.data.map Float.toBits),
   (run64 p i).bind fun e => e[nm]?.map fun t => (t.shape, t.data.map Float.toBits),
   (run32 p j).bind fun e => e[nm]?.map fun t => (t.shape, t.data.map Float32.toBits))
/-- The state `nm` has shape `sh` and bit-equal cells `x` in the reference, the binary64 plan and (as
    `Float32`) the binary32 plan. -/
def agreeOf (nm : String) (p : TLProgram) (sh : List Nat) (x : Array Float) (y : Array Float32)
    (i := scanIn64) (j := scanIn32) : Bool :=
  cellsOf nm p i j == (some (sh, x.map Float.toBits), some (sh, x.map Float.toBits),
                       some (sh, y.map Float32.toBits))

/-- Why the reference evaluator refuses `p`; `none` if it runs. -/
def refErr (p : TLProgram) (i := scanIn64) : Option String :=
  (scheduled (as64 p)).bind fun s => match evalScheduled s i with
    | .error e => some (toString e)
    | .ok _ => none
/-- The cause when preparing the checked binary64 plan for `p` refuses it; `some none` if it prepares,
    `none` if the program does not even schedule. -/
def planErr64 (p : TLProgram) (i := scanIn64) : Option (Option PlanCompileCause) :=
  (scheduled (as64 p)).map fun s => match prepareEvalPlan s (InputSignature.ofDenseInputs i) with
    | .error e => some e.cause
    | .ok _ => none
/-- `planErr64` for the binary32 plan (`none` also if the input signature is refused). -/
def planErr32 (p : TLProgram) (i := scanIn32) : Option (Option PlanCompileCause) :=
  (scheduled p).bind fun s => (InputSignature.ofDenseInputs32ForDecls s.decls i).toOption.map fun sig =>
    match prepareEvalPlan s sig with
    | .error e => some e.cause
    | .ok _ => none
def scanConstStep : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(j, l), X(j), W(j, k)
  G[j, 0] := X[j]
  G[=2, l +1] := G[j, l] · W[j, k]
}
#guard compErr scanConstStep == none
-- Observed (shape [3,3], rows j, cols l): the base writes column 0 = X; the step writes ONLY row 2,
-- cell (2, l+1) = sum_{j,k} G[j,l]·W[j,k]: 1·3 + 2·7 + 3·11 = 50, then 50·11 = 550 (rows 0, 1 keep their
-- base value and are never written again). A write to row `j` instead of row 2 changes the cells.
#guard agreeOf "G" scanConstStep [3, 3] #[1, 0, 0, 2, 0, 0, 3, 50, 550] #[1, 0, 0, 2, 0, 0, 3, 50, 550]
-- A constant `=1` in the base against a free `j` in the step is a typed refusal: the constant's extent is
-- `n + 1 = 2`, the free `j` is 3 wide. The refusal is at evaluation / plan preparation, not at compile.
def scanConstBase : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(j, l), X(j), W(j, k)
  G[=1, 0] := X[j]
  G[j, l +1] := G[j, l] · W[j, k]
}
#guard compErr scanConstBase == none
#guard refErr scanConstBase ==
  some "evalScan G: state G dimension 0 is 2 wide in its first placement but 3 wide in a later one"
#guard planErr64 scanConstBase == some (some (.scan (.inconsistentStateExtent "G" "G" 0 2 3)))
#guard planErr32 scanConstBase == some (some (.scan (.inconsistentStateExtent "G" "G" 0 2 3)))
-- Accept-neighbour: the SAME constant `=2` in base and step (extent 3 = the free `j`). Only row 2 is ever
-- written: base 1+2+3 = 6, then 6·11 = 66, then 66·11 = 726; rows 0, 1 are exactly 0.
def scanConstBoth : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(j, l), X(j), W(j, k)
  G[=2, 0] := X[j]
  G[=2, l +1] := G[j, l] · W[j, k]
}
#guard compErr scanConstBoth == none
#guard agreeOf "G" scanConstBoth [3, 3] #[0, 0, 0, 0, 0, 0, 6, 66, 726] #[0, 0, 0, 0, 0, 0, 6, 66, 726]
-- Tropical state (`maxreduce`, ⊗ = +, unit -inf): every cell never written is -inf, not 0; row 2 is
-- max X = 3, then max_{j,k} (G[j,l] + W[j,k]) = 3 + 6 = 9, then 9 + 6 = 15. A sum-of-products reading gives
-- 0 for the unwritten rows and 6, 66, 726 style values on row 2.
def scanConstTrop : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(j, l), X(j), W(j, k)
  G[=2, 0] := maxreduce(X[j])
  G[=2, l +1] := maxreduce(G[j, l] · W[j, k])
}
#guard compErr scanConstTrop == none
#guard agreeOf "G" scanConstTrop [3, 3]
  #[-(1/0), -(1/0), -(1/0), -(1/0), -(1/0), -(1/0), 3, 9, 15]
  #[-(1/0), -(1/0), -(1/0), -(1/0), -(1/0), -(1/0), 3, 9, 15]
-- Scan axis FIRST (`G(l, j)`, constant in the second slot): shape [3,3] with rows l, cols j; column 2 holds
-- 6, 66, 726 (the same recurrence as `scanConstBoth`, transposed); columns 0 and 1 are 0.
def scanConstFirst : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(l, j), X(j), W(j, k)
  G[0, =2] := X[j]
  G[l +1, =2] := G[l, j] · W[j, k]
}
#guard compErr scanConstFirst == none
#guard agreeOf "G" scanConstFirst [3, 3] #[0, 0, 6, 0, 0, 66, 0, 0, 726] #[0, 0, 6, 0, 0, 66, 0, 0, 726]
-- A constant PAST the reach of the free `j` (`=5`, `j` is 3 wide): extent 6, shape [6,3]. Only row 5
-- is written (the base 6 at l = 0; the step reads rows 0..2, which are 0, so it writes 0 afterwards);
-- rows 0..4 are exactly 0 (real sort 0), they are not -inf, NaN or uninitialised.
def scanConstFar : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(j, l), X(j), W(j, k)
  G[=5, 0] := X[j]
  G[=5, l +1] := G[j, l] · W[j, k]
}
#guard compErr scanConstFar == none
#guard agreeOf "G" scanConstFar [6, 3] #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0]
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0]
def scanTwoConst : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(p, q, l), X(j), V(p, q)
  G[=1, =2, 0] := X[j]
  G[=1, =2, l +1] := G[p, q, l] · V[p, q]
}
def twoIn64 : NamedDenseEnv := scanIn64.insert "V" ⟨[2, 3], #[1, 2, 3, 4, 5, 6]⟩
def twoIn32 : NamedDenseEnv32 := scanIn32.insert "V" ⟨[2, 3], #[1, 2, 3, 4, 5, 6]⟩
-- TWO constants in one scan statement: accepted; shape [2,3,3], only cell (1, 2, l) is written:
-- base 6, then 6·V[1,2] = 36, then 36·6 = 216.
#guard compErr scanTwoConst == none
#guard agreeOf "G" scanTwoConst [2, 3, 3] (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 36, 216])
  (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 36, 216]) twoIn64 twoIn32
def scanCoupled : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(j, l), H(j, l), X(j), W(j, k)
  G[j, 0] := X[j]
  H[=2, 0] := X[j]
  G[j, l +1] := G[j, l] · W[j, k]
  H[=2, l +1] := G[j, l] · W[j, k]
}
-- COUPLED scan, one state with a constant: `G` is free-`j`, `H` writes row 2 and reads `G`. `G`
-- is the base X scaled by the row sums 3, 7, 11 per step; `H[2, l+1] = sum_j G[j,l]·rowsum_j` =
-- 50 then 470 (= 3·3 + 14·7 + 33·11); `H` rows 0, 1 are 0.
#guard compErr scanCoupled == none
#guard agreeOf "G" scanCoupled [3, 3] #[1, 3, 9, 2, 14, 98, 3, 33, 363] #[1, 3, 9, 2, 14, 98, 3, 33, 363]
#guard agreeOf "H" scanCoupled [3, 3] #[0, 0, 0, 0, 0, 0, 6, 50, 470] #[0, 0, 0, 0, 0, 0, 6, 50, 470]
def scanMultiStep : TLProgram := tlprog!{
  iter l = 3
  tensor f32 G(j, l), X(j), W(j, k)
  G[j, 0] := X[j]
  G[j + k, l +1] := G[j, l] · W[j, k]
}
#guard compErr scanMultiStep ==
  some "preflight LeanNCD.Eval.Plan.CapabilityError.multiAxisScatterLhs \"G: affine LHS slot\""
-- KNOWN LIMIT (F3-b stage 1 review R1, parked): a scan state's published extent comes from its slots, not
-- from a pinned declaration of the axis. `j` is declared 3 wide, yet `=1` publishes `G` with 2 rows; the
-- top-level twin `S(j=3)`, `S[=5]` is refused (`writerExtentExceedsBox`), a strided scan slot `G[2*j, ..]`
-- behaves the same way (pre-existing, scan-wide). All three legs agree. If a pinned declaration is ever
-- enforced for scan states, this fixture must flip to a typed refusal deliberately.
def scanConstPinned : TLProgram := tlprog!{
  axis j : ℕ = 3
  iter l = 3
  tensor f32 G(j, l), X(j), W(j, k)
  G[=1, 0] := X[j]
  G[=1, l +1] := G[j, l] · W[j, k]
}
#guard compErr scanConstPinned == none
#guard agreeOf "G" scanConstPinned [2, 3] #[0, 0, 0, 6, 42, 294] #[0, 0, 0, 6, 42, 294]
-- Review R3: a PREDICATE scan state with a constant slot. The reference runs it; both checked plans refuse
-- it at the existing predicate-scatter-destination capability tier (no new geometry; same split as the
-- top-level predicate scatter in `ScanTest`).
def scanConstPred : TLProgram := tlprog!{
  iter l = 3
  predicate G(j, l)
  tensor f32 X(j), W(j, k)
  G[=2, 0] := X[j]
  G[=2, l +1] := G[j, l] · W[j, k]
}
#guard compErr scanConstPred ==
  some "preflight LeanNCD.Eval.Plan.CapabilityError.predicateScatterDest \"G: predicate scatter destination\""
#guard refErr scanConstPred == none
#guard planErr64 scanConstPred ==
  some (some (.capability (.predicateScatterDest "G: predicate scatter destination")))
#guard planErr32 scanConstPred ==
  some (some (.capability (.predicateScatterDest "G: predicate scatter destination")))

-- R1/R2 (D5 pinned observation; review finding L1-1). Donor: the surface fixture `f1Surf` above (same
-- pinned-declaration constant writers), with a rank-2 destination `S(k, b)` where EVERY declared axis is
-- pinned and the row writer carries an IDENTITY slot `b` over its own declared axis. The D5 exclusion fires
-- whenever any declared axis occurs among the writer's own source axes, identity slot included, so the
-- lone writer is NOT boxed and keeps the derived shape [4, 3]; two such writers publish the declared
-- [8, 3]. R1 vs R2 differing is the documented consequence of that exclusion (the writer count changes
-- the shape when a writer has an identity slot over a declared axis), not a bug; if D5 is ever narrowed,
-- R1 must move to [8, 3] deliberately. Cells are OBSERVED (rows of 3, row-major); B = [1, 10, 100], so a
-- transposed or shifted reading differs.
def r1Surf : TLProgram := tlprog!{
  axis k : ℕ = 8, b : ℕ = 3
  tensor f32 B(b), S(k, b)
  S[=3, b] := B[b]
}
#guard compErr r1Surf == none
#guard (cells r1Surf).1.map (·.1) == some [4, 3]
#guard (cells r1Surf).2.1.map (·.1) == some [4, 3]
#guard (cells r1Surf).2.2.map (·.1) == some [4, 3]
#guard agree r1Surf convIn64 convIn32 #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10, 100]
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10, 100]

-- R2: two row writers (`=3` and `=5`) into the same pinned declaration: declared shape [8, 3], row 3 holds
-- B and row 5 holds B again (cells observed). Compare R1: same declaration, shape [4, 3] vs [8, 3].
def r2Surf : TLProgram := tlprog!{
  axis k : ℕ = 8, b : ℕ = 3
  tensor f32 B(b), S(k, b)
  S[=3, b] := B[b]
  S[=5, b] := B[b]
}
#guard compErr r2Surf == none
#guard (cells r2Surf).1.map (·.1) == some [8, 3]
#guard (cells r2Surf).2.1.map (·.1) == some [8, 3]
#guard (cells r2Surf).2.2.map (·.1) == some [8, 3]
#guard agree r2Surf convIn64 convIn32
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10, 100, 0, 0, 0, 1, 10, 100, 0, 0, 0, 0, 0, 0]
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10, 100, 0, 0, 0, 1, 10, 100, 0, 0, 0, 0, 0, 0]

end LeanNCD.Eval.Plan.ScatterSurfaceTest
