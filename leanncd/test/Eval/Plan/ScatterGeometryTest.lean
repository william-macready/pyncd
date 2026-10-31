import Eval.Plan.B5cSingleBoxTest

/-!
# Scatter geometry slice A: multi-axis `Y[a+b]` (programmatic forms)

Hand-built `TLProgram`s (the surface cannot say a multi-axis slot; slice B adds it) with an explicit
`.scatter` statement, run through the real pipeline (`compileToScheduled`, `prepareEvalPlan`,
`runPreparedDense`/`runPreparedDense32`, `evalScheduled`) by the B5 harness (`B5NativeTest`).

Inputs throughout: `A[a] = [1,2,3,4]` (`|a| = 4`), `B[b] = [1,10,100]` (`|b| = 3`). The anti-diagonal
sums of `A[a]*B[b]` are the polynomial product `[1, 12, 123, 234, 340, 400]`, whose exact reach is
`0..5`, so the destination extent is 6 (M1; the legacy sum rule gave 7 and a trailing `0`).
-/

namespace LeanNCD.Eval.Plan.ScatterGeometryTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.Eval.Plan.B5NativeTest Std

private def a : AxisSpec := ⟨"a", 90, .nat⟩
private def b : AxisSpec := ⟨"b", 91, .nat⟩
private def k : AxisSpec := ⟨"k", 92, .nat⟩

/-- Donor: `B5BoundaryTest.twoAxes` reduced to ONE scatter writer. `S` is declared over the
    unpinned axis `k`, so its shape is derived from the write form (no box). -/
def convOf (slot : LHSSlot) (agg : AggOp := .sum) : TLProgram :=
  { decls := [.axis a (some 4), .axis b (some 3), .axis k none,
      .typedTensor .f32 "A" [a], .typedTensor .f32 "B" [b], .typedTensor .f32 "S" [k]]
    stmts := [.scatter "S" [slot]
      { body := { terms := [{ factors := [.read "A" [.axis a], .read "B" [.axis b]] }] }
        nonlin := .identity, agg := agg }] }

def sumSlot : LHSSlot := .affine (.affine 0 [(1, a), (1, b)])
def wideSlot : LHSSlot := .affine (.affine 0 [(1, a), (4, b)])

def conv : TLProgram := convOf sumSlot
def convWide : TLProgram := convOf wideSlot

def convIn64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "A" ⟨[4], #[1, 2, 3, 4]⟩ |>.insert "B" ⟨[3], #[1, 10, 100]⟩
def convIn32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[4], #[1, 2, 3, 4]⟩ |>.insert "B" ⟨[3], #[1, 10, 100]⟩

/-- The reference evaluator's published shape of `S`. -/
def refShapeOf (p : TLProgram) : Option (List Nat) :=
  (ref64 p convIn64).bind fun e => e["S"]?.map (·.shape)

/-- The checked backend's refusal cause at preparation, or `none` if it accepted. -/
def prepCause (p : TLProgram) : Option PlanCompileCause :=
  (scheduled (as64 p)).bind fun s =>
    match prepareEvalPlan s (InputSignature.ofDenseInputs convIn64) with
    | .error f => some f.cause
    | .ok _ => none

-- T1 (M1): the reference publishes the EXACT REACH. `a+b`: 0..5, extent 6 (the legacy rule: 7);
-- `a+4b`: 0..11, extent 12 (legacy 16).
#guard refShapeOf conv == some [6]
#guard refShapeOf convWide == some [12]
-- ... and the values are the polynomial product (no trailing zero cell).
#guard ((ref64 conv convIn64).bind fun e => e["S"]?.map (·.data)) ==
  some #[1, 12, 123, 234, 340, 400]
/-! ## T2: the checked backend admits multi-axis geometry (top level only)

`checkScatterLHSSlot` no longer refuses a multi-axis slot (the constant slot and the scan-local
sibling still refuse). Every program below goes through `compileToScheduled`, `prepareEvalPlan` and both
dtype workers and is compared with `evalScheduled` (the reference) through the B5 harness `agree`:
reference, checked binary64 and checked binary32 must all give the stated cells, bit for bit. -/

/-- The `ScatterPlan` of the program's first step, or `none` if that step is not a scatter. -/
def scatterStepAt (pp : PreparedPlan) (i : Nat) : Option ScatterPlan :=
  match pp.plan.raw.steps[i]? with
  | some (.scatter s) => some s
  | _ => none

def scatterPlanOf (p : TLProgram) : Option ScatterPlan :=
  (prep64 p convIn64).bind (scatterStepAt · 0)

-- Plan fields as observed (`#eval` of the prepared `ScatterPlan`): one placement row per destination
-- dimension, one coefficient per SOURCE axis in `compute.outputShape` order `[a, b] = [4, 3]`; the
-- destination extent is the exact reach.
#guard prepCause conv == none
#guard prepCause convWide == none
#guard (scatterPlanOf conv).map (fun s => (s.outCoeffs, s.outBias, s.destShape, s.compute.outputShape))
  == some (#[#[1, 1]], #[0], #[6], #[4, 3])
#guard (scatterPlanOf convWide).map (fun s => (s.outCoeffs, s.outBias, s.destShape, s.compute.outputShape))
  == some (#[#[1, 4]], #[0], #[12], #[4, 3])

-- Reference, checked binary64 and checked binary32 agree bit for bit. Collisions SUM (S3a): cell 2 is
-- `A2*B0 + A1*B1 + A0*B2 = 3*1 + 2*10 + 1*100 = 123`; a last-write-wins fold would give 3, 20 or 100.
#guard agree conv convIn64 convIn32 #[1, 12, 123, 234, 340, 400] #[1, 12, 123, 234, 340, 400]
-- `a+4b` is collision-free: `b` selects a block of four.
#guard agree convWide convIn64 convIn32
  #[1, 2, 3, 4, 10, 20, 30, 40, 100, 200, 300, 400] #[1, 2, 3, 4, 10, 20, 30, 40, 100, 200, 300, 400]
-- Mixed sign with NON-NEGATIVE minimum (`a - b + 2`, reach 0..5): the cross-correlation. Before M1 its
-- legacy extent was 3 and the row was a range error.
def crossSlot : LHSSlot := .affine (.affine 2 [(1, a), (-1, b)])
#guard agree (convOf crossSlot) convIn64 convIn32 #[100, 210, 321, 432, 43, 4] #[100, 210, 321, 432, 43, 4]

-- Max-plus convolution: `agg max`, ⊗ is `+`, ⊕ is `max`: cell n = max over a+b=n of A[a]+B[b].
-- A=[1,2,3,4], B=[1,10,100]: n0 = 2; n1 = max(3, 11); n2 = max(4, 12, 101); n3 = max(5, 13, 102);
-- n4 = max(14, 103); n5 = 104. Every cell is written, so no `-inf` hole.
def convMax : TLProgram := convOf sumSlot .max
#guard agree convMax convIn64 convIn32 #[2, 11, 101, 102, 103, 104] #[2, 11, 101, 102, 103, 104]

-- B6 in BOTH backends for a mixed-sign row with NEGATIVE minimum (`a - b`, reach -2..3, extent 4):
-- the checked backend refuses at preparation with the range payload (dimension 0, min -2, max 3,
-- extent 4); the reference errors on the first write below zero (source coordinate `[0, 1]` -> `[-1]`).
def signSlot : LHSSlot := .affine (.affine 0 [(1, a), (-1, b)])
def refWriteOutOfRange (p : TLProgram) : Option (String × List Int × List Nat) :=
  (scheduled (as64 p)).bind fun s => match evalScheduled s convIn64 with
    | .error e => match e.error with
        | .scatterWriteOutOfRange nm oc sc => some (nm, oc, sc)
        | _ => none
    | .ok _ => none
#guard refWriteOutOfRange (convOf signSlot) == some ("S", [-1], [0, 1])
#guard prepCause (convOf signSlot) == some (.shape (.scatterImageOutOfRange "S" 0 (-2) 3 4))

-- A constant slot is STILL refused by the top-level preflight (a hand-built schedule that bypassed
-- `lowerArith`); slice B/T3 will change what a constant means, not this arm.
#guard prepCause (convOf (.affine (.const 3))) ==
  some (.capability (.scatterOrAffineLhs "S: constant affine LHS slot"))

-- A multi-writer group containing a multi-axis scatter is still refused (`multiWriterScatter`):
-- donor B5BoundaryTest.twoAxes. Pinned here against the lift (the destination is pinned `k = 6`).
def convTwo : TLProgram :=
  { conv with
    decls := conv.decls.map (fun | .axis ax none => .axis ax (some 6) | d => d)
    stmts := conv.stmts ++ conv.stmts }
#guard sourceError convTwo == some (.multiWriterScatter "S")

-- A BOXED single multi-axis writer keeps the derived shape (B5c D2 residual, closed in slice B): `S`
-- declared over a pinned `k = 8` still publishes `[6]` in all three legs, and the collector does not
-- box it.
def convBoxed : TLProgram :=
  { conv with decls := conv.decls.map (fun | .axis ax none => .axis ax (some 8) | d => d) }
def shapesOf (p : TLProgram) :=
  ((ref64 p convIn64).bind fun e => e["S"]?.map (·.shape),
   (run64 p convIn64).bind fun e => e["S"]?.map (·.shape),
   (run32 p convIn32).bind fun e => e["S"]?.map (·.shape))
#guard shapesOf convBoxed == (some [6], some [6], some [6])
#guard B5cSingleBoxTest.groupsOf convBoxed == []

-- `route` carries no extents and accepts the multi-axis program.
#guard routeError conv == none

/-! ### Binary32 parity with a lane that binary64-then-narrow would get wrong

`agree` above proves the integer cells. For a binary32-discriminating case the reference evaluator is
no help (it refuses every f32 program), so the expectation is assembled from an INDEPENDENT binary32
twin: the same product as an ordinary assignment `T[a,b] := A[a]*B[b]` (the plain F32 path, no
`ScatterPlan`), then anti-diagonal sums written here, in source order (a-major), in binary32 with
`+0` seeds. The pinned bits are the observed values of the native scatter (see the `#eval` that
produced them in the notes), never a narrowing of a binary64 result; one lane is required to differ
from the narrowed binary64 answer so a binary64 worker could not pass. -/

def twin : TLProgram :=
  { decls := [.axis a (some 4), .axis b (some 3), .typedTensor .f32 "A" [a],
      .typedTensor .f32 "B" [b], .typedTensor .f32 "T" [a, b]]
    stmts := [.assign "T" [.free a, .free b]
      { body := { terms := [{ factors := [.read "A" [.axis a], .read "B" [.axis b]] }] }
        nonlin := .identity }] }

def fracIn32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[4], #[0.1, 0.7, 0.3, 0.9]⟩
    |>.insert "B" ⟨[3], #[0.3, 0.1, 0.7]⟩
def fracIn64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "A" ⟨[4], #[0.1, 0.7, 0.3, 0.9]⟩
    |>.insert "B" ⟨[3], #[0.3, 0.1, 0.7]⟩

/-- Anti-diagonal sums of a `[4, 3]` binary32 tensor, source order, `+0` seeds. -/
def antiDiagBits (t : DenseTensor32) : Array UInt32 := Id.run do
  let mut out : Array Float32 := Array.replicate 6 0
  for ai in [0:4] do
    for bi in [0:3] do
      out := out.modify (ai + bi) (· + t.data[ai * 3 + bi]!)
  return out.map Float32.toBits

def nativeBits : Option (Array UInt32) :=
  (run32 conv fracIn32).bind fun e => e["S"]?.map fun t => t.data.map Float32.toBits
def twinBits : Option (Array UInt32) :=
  (run32 twin fracIn32).bind fun e => e["T"]?.map antiDiagBits
/-- The binary64 program's answer, narrowed to binary32 bits. -/
def narrowedBits : Option (Array UInt32) :=
  (run64 conv fracIn64).bind fun e => e["S"]?.map fun t => t.data.map (·.toFloat32.toBits)

-- Observed (`lean-file.sh test/Eval/Plan/ScatterGeometryTest.lean`, `#eval nativeBits` etc.): the
-- native scatter and the independent twin agree on these six words; the narrowed binary64 answer
-- differs in lanes 0, 1 and 3 (`...087`, `...734`, `...001`).
#guard nativeBits == some #[1022739088, 1046562735, 1047233823, 1061830000, 1050253722, 1059145646]
#guard twinBits == nativeBits
#guard narrowedBits == some #[1022739087, 1046562734, 1047233823, 1061830001, 1050253722, 1059145646]
#guard nativeBits != narrowedBits

end LeanNCD.Eval.Plan.ScatterGeometryTest
