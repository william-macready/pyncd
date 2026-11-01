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

-- The constant-slot refusal pin moved to the T3 section (`bypass`): a surface-compiled constant now lowers.

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

/-! ## T3: a constant slot `S[n]` is a unit-axis scatter

`lowerArith` rewrites a constant LHS slot to `n + 1·u` over a fresh axis `u` pinned to size 1
(`lowerConstSlots`), on BOTH the `.assign` and the `.scatter` arm. The image is exactly `{n}`, the
destination extent is `n + 1` in the reference and the checked plan alike, and `u` is never a published
dimension. Inputs: `A = [1,2,3,4]`, `B = [1,10,100]`. -/

private def m : AxisSpec := ⟨"m", 94, .nat⟩

def rhsOf (fs : List Factor) (agg : AggOp := .sum) : RHSExpr :=
  { body := { terms := [{ factors := fs }] }, nonlin := .identity, agg := agg }
def facA : List Factor := [.read "A" [.axis a]]
def facAB : List Factor := [.read "A" [.axis a], .read "B" [.axis b]]

/-- Donor: `convOf`, generalised over destination axes, slots and factors, plus the `.assign` spelling. -/
def cstProg (dst : List AxisSpec) (slots : List LHSSlot) (fs : List Factor)
    (asAssign : Bool := false) (agg : AggOp := .sum) : TLProgram :=
  { decls := [.axis a (some 4), .axis b (some 3)] ++ (dst.filter (· != a)).map (fun ax => .axis ax none) ++
      [.typedTensor .f32 "A" [a], .typedTensor .f32 "B" [b], .typedTensor .f32 "S" dst]
    stmts := [if asAssign then .assign "S" slots (rhsOf fs agg) else .scatter "S" slots (rhsOf fs agg)] }

def cst (n : Int) : LHSSlot := .affine (.const n)
def pinAll (n : Nat) (p : TLProgram) : TLProgram :=
  { p with decls := p.decls.map (fun | .axis ax none => .axis ax (some n) | d => d) }

/-- Shape and cells in the three legs: reference, checked binary64, checked binary32 (bits). -/
def cells (p : TLProgram) :=
  ((ref64 p convIn64).bind fun e => e["S"]?.map fun t => (t.shape, t.data.map Float.toBits),
   (run64 p convIn64).bind fun e => e["S"]?.map fun t => (t.shape, t.data.map Float.toBits),
   (run32 p convIn32).bind fun e => e["S"]?.map fun t => (t.shape, t.data.map Float32.toBits))
def planFields (p : TLProgram) :=
  (scatterPlanOf p).map (fun s => (s.outCoeffs, s.outBias, s.destShape, s.compute.outputShape))

def S3 := cstProg [k] [cst 3] facA
def S3a := cstProg [k] [cst 3] facA (asAssign := true)
def bigIn32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[4], #[16777216, 1, 1, 1]⟩ |>.insert "B" ⟨[3], #[1, 10, 100]⟩
def bigIn64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "A" ⟨[4], #[16777216, 1, 1, 1]⟩ |>.insert "B" ⟨[3], #[1, 10, 100]⟩
def twinS : TLProgram :=
  { decls := [.axis a (some 4), .typedTensor .f32 "A" [a], .typedTensor .f32 "T" [a]]
    stmts := [.assign "T" [.free a] (rhsOf facA)] }

-- Observed (`lean-file.sh test/Eval/Plan/ScatterGeometryTest.lean`, `#eval cells S3` etc.; the pre-T3
-- baseline refused every program below in both checked legs). Reference == checked f64 == checked f32,
-- the shape is `n + 1` and the cells are the sum over the contracted axes at the constant coordinate.
-- `Y[3] := A[a]`: shape [4], cells [0,0,0,10] (1+2+3+4), as the P0 source-level probe
-- `axis u = 1; Y[u+3] := X[a]` observed. The synthetic axis is not a published dimension.
#guard shapesOf S3 == (some [4], some [4], some [4])
#guard shapesOf S3a == (some [4], some [4], some [4])
#guard agree S3 convIn64 convIn32 #[0, 0, 0, 10] #[0, 0, 0, 10]
#guard agree S3a convIn64 convIn32 #[0, 0, 0, 10] #[0, 0, 0, 10]
-- Plan fields: columns are `compute.outputShape = [1 (synthetic u), 4 (a)]`, so the placement row is
-- `[1, 0]` (u with coefficient 1, a with 0), bias 3 (the constant), extent `1*1 + 3 = 4`.
#guard planFields S3 == some (#[#[1, 0]], #[3], #[4], #[1, 4])
#guard planFields S3a == some (#[#[1, 0]], #[3], #[4], #[1, 4])
-- The synthetic axis is declared (pinned to 1, `#const<uid>` name: `#` is not an identifier character,
-- so no source axis can collide) and is the ONLY declaration `lowerArith` added.
#guard ((scheduled (as64 S3)).map fun s => s.decls.map fun
    | .axis ax n => some (ax.name.startsWith constUnitPrefix, n) | _ => none)
  == some [some (false, some 4), some (false, some 3), some (false, none), none, none, none,
    some (true, some 1)]
-- A constant next to a free axis (`S[a, 3] := A[a]`, dst `[a, k]`): shape [4,4], column 3 is `A`.
def colProg := cstProg [a, k] [.free a, cst 3] facA
def colProgA := cstProg [a, k] [.free a, cst 3] facA true
#guard shapesOf colProg == (some [4, 4], some [4, 4], some [4, 4])
#guard agree colProg convIn64 convIn32 #[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4]
  #[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4]
#guard agree colProgA convIn64 convIn32 #[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4]
  #[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4]
-- Two constant slots in one statement (`S[3, 4]`, dst `[k, m]`): shape [4, 5], one nonzero cell, two
-- synthetic axes (one per slot).
def twoConst := cstProg [k, m] [cst 3, cst 4] facA
def twoConstA := cstProg [k, m] [cst 3, cst 4] facA true
#guard shapesOf twoConst == (some [4, 5], some [4, 5], some [4, 5])
#guard planFields twoConst == some (#[#[1, 0, 0], #[0, 1, 0]], #[3, 4], #[4, 5], #[1, 1, 4])
#guard agree twoConst convIn64 convIn32 (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10])
  (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10])
#guard agree twoConstA convIn64 convIn32 (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10])
  (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10])
-- A contracted RHS axis summing (`S[3] := A[a]*B[b]`): (1+2+3+4)*(1+10+100) = 1110.
#guard agree (cstProg [k] [cst 3] facAB) convIn64 convIn32 #[0, 0, 0, 1110] #[0, 0, 0, 1110]
-- Constant 0: extent 1.
#guard shapesOf (cstProg [k] [cst 0] facA) == (some [1], some [1], some [1])
#guard agree (cstProg [k] [cst 0] facA) convIn64 convIn32 #[10] #[10]
-- Max-plus (`agg max`): constant 0 gives max(A) = 4; constant 3 leaves identity-filled (-inf) holes.
#guard agree (cstProg [k] [cst 0] facA (agg := .max)) convIn64 convIn32 #[4] #[4]
#guard agree (cstProg [k] [cst 3] facA (agg := .max)) convIn64 convIn32
  #[-(1/0), -(1/0), -(1/0), 4] #[-(1/0), -(1/0), -(1/0), 4]
-- RISK (ii): a BOXED single constant writer (`k` pinned 8) still publishes the DERIVED shape [4], in all
-- three legs, and the collector does not box it (the synthetic slot is not `boundedScatter`; B5c D2
-- residual, unchanged by T3). Donor: `convBoxed`/`B5cSingleBoxTest.groupsOf`.
#guard shapesOf (pinAll 8 S3) == (some [4], some [4], some [4])
#guard shapesOf (pinAll 8 S3a) == (some [4], some [4], some [4])
#guard B5cSingleBoxTest.groupsOf (pinAll 8 S3) == []
#guard B5cSingleBoxTest.groupsOf (pinAll 8 S3a) == []
-- RISK (i): a multi-writer group with a constant writer is refused exactly as before T3
-- (`multiWriterScatter`; observed on the T2 commit for the `.scatter` pairs). Donor: `convTwo`.
#guard sourceError (pinAll 6 { S3 with stmts := S3.stmts ++ S3.stmts }) == some (.multiWriterScatter "S")
#guard sourceError (pinAll 6 { S3a with stmts := S3a.stmts ++ S3a.stmts }) == some (.multiWriterScatter "S")
#guard sourceError (pinAll 6 { S3 with stmts := S3.stmts ++ conv.stmts }) == some (.multiWriterScatter "S")
-- `route` accepts the constant-slot program.
#guard routeError S3 == none && routeError S3a == none
-- No `EvalWarning` (unused-axis, size inference) mentions the synthetic axis: the reference evaluator
-- emits none for either arm, with the pinned `#const` axis declared.
#guard ((scheduled (as64 S3)).bind fun s => (evalScheduled s convIn64).toOption).map
    (·.warnings.length) == some 0
#guard ((scheduled (as64 S3a)).bind fun s => (evalScheduled s convIn64).toOption).map
    (·.warnings.length) == some 0
-- The hand-built bypass: a raw constant `.scatter` handed STRAIGHT to the preflight (no `lowerArith`)
-- is still refused, `checkScatterAffineExpr`'s top-level `.constant` arm (it now means "a schedule that
-- bypassed `lowerArith`"). Replaces the T2 pin that went through `compileToScheduled`.
def bypass (p : TLProgram) : Option ScheduledProgram :=
  (scheduled (as64 p)).map fun s => { s with stmts := s.stmts.map fun
    | .plain (.scatter nm _ r) => .plain (.scatter nm [cst 3] r)
    | x => x }
#guard ((bypass S3).bind fun s => match prepareEvalPlan s (InputSignature.ofDenseInputs convIn64) with
  | .error f => some f.cause
  | .ok _ => none) == some (.capability (.scatterOrAffineLhs "S: constant affine LHS slot"))
-- Binary32 discriminator (the T2 pattern: independent twin + a lane the narrowed binary64 answer gets
-- wrong). `A = [2^24, 1, 1, 1]`: binary32 absorbs every `+1` (2^24 + 1 ties to even), so the native f32
-- sum is 16777216 (bits 1266679808), the independent twin (ordinary assign `T[a] := A[a]`, summed in
-- binary32 source order with a `+0` seed) is the same word, and the binary64 answer 16777219 narrows to
-- 16777220 (bits 1266679810). All three read from `#eval` of this file, not derived by narrowing.
#guard ((run32 S3 bigIn32).bind fun e => e["S"]?.map fun t => t.data.map Float32.toBits) ==
  some #[0, 0, 0, 1266679808]
#guard ((run32 twinS bigIn32).bind fun e => e["T"]?.map fun t =>
  (t.data.foldl (· + ·) (0 : Float32)).toBits) == some 1266679808
#guard ((run64 S3 bigIn64).bind fun e => e["S"]?.map fun t => t.data.map (·.toFloat32.toBits)) ==
  some #[0, 0, 0, 1266679810]

-- The surface grammar is untouched: a lone numeral in a scan base slot (`S[i, 0]`) is still the scan
-- base case `.iterAt`, never a constant `.affine (.const 0)`, and the program still compiles to a scan.
def scanBase : TLProgram := tlprog!{
  iter l = 3
  S[i, 0] := X[i]
  S[i, l + 1] := S[i, l]
}
#guard (match scanBase.stmts with
  | .assign "S" [_, .iterAt _ 0] _ :: _ => true
  | _ => false)
#guard (match scanBase.compileToScheduled.run 0 with
  | .ok s _ => s.stmts.any (fun | ScanStmt.scan .. => true | _ => false)
  | .error _ _ => false)

/-! ## Review repair A1: an unrelated empty axis does not change a multi-axis extent

`LHSSlot.outExtent` is called on the SPARSE slot by the reference (`derived shape`) and on a DENSE
row over every source axis by the checked path (`scatterDestExtent`). The empty-axis fallback is
tested over the nonzero-coefficient terms only, so the two cannot disagree: `S[a+b] := A[a]*B[b]*C[c]`
with `|c| = 0` has extent 6 on every leg (before the repair the checked legs gave 7). The domain is
empty, so every cell is the identity `0`; the SHAPE is what these rows pin. -/

private def c : AxisSpec := ⟨"c", 93, .nat⟩
private def d : AxisSpec := ⟨"d", 94, .nat⟩

/-- Donor: `convOf sumSlot`, plus an unrelated source axis `c` of size 0 read by the right-hand side. -/
def convEmptyC : TLProgram :=
  { decls := [.axis a (some 4), .axis b (some 3), .axis c (some 0), .axis k none,
      .typedTensor .f32 "A" [a], .typedTensor .f32 "B" [b], .typedTensor .f32 "C" [c],
      .typedTensor .f32 "S" [k]]
    stmts := [.scatter "S" [sumSlot]
      { body := { terms := [{ factors := [.read "A" [.axis a], .read "B" [.axis b],
          .read "C" [.axis c]] }] }
        nonlin := .identity, agg := .sum }] }

/-- Donor: `convEmptyC`, with the empty axis `d` on a separate free destination slot instead. -/
def convEmptyFree : TLProgram :=
  { decls := [.axis a (some 4), .axis b (some 3), .axis d (some 0), .axis k none,
      .typedTensor .f32 "A" [a], .typedTensor .f32 "B" [b], .typedTensor .f32 "D" [d],
      .typedTensor .f32 "S" [k, d]]
    stmts := [.scatter "S" [sumSlot, .free d]
      { body := { terms := [{ factors := [.read "A" [.axis a], .read "B" [.axis b],
          .read "D" [.axis d]] }] }
        nonlin := .identity, agg := .sum }] }

def emptyCIn64 : NamedDenseEnv := convIn64.insert "C" ⟨[0], #[]⟩ |>.insert "D" ⟨[0], #[]⟩
def emptyCIn32 : NamedDenseEnv32 := convIn32.insert "C" ⟨[0], #[]⟩ |>.insert "D" ⟨[0], #[]⟩

/-- The published shape of `S` on the reference, checked binary64 and checked binary32 legs. -/
def emptyShapesOf (p : TLProgram) : Option (List Nat) × Option (List Nat) × Option (List Nat) :=
  ((ref64 p emptyCIn64).bind fun e => e["S"]?.map (·.shape),
   (run64 p emptyCIn64).bind fun e => e["S"]?.map (·.shape),
   (run32 p emptyCIn32).bind fun e => e["S"]?.map (·.shape))

-- The helper pin: the dense row `[1,1,0]` over source shape `[4,3,0]` is the sparse slot `a + b`.
#guard scatterDestExtent #[4, 3, 0] #[1, 1, 0] 0 == some 6
-- Accept-neighbour: the SAME empty axis with a NONZERO coefficient keeps the legacy rule (`4+3+0 = 7`).
#guard scatterDestExtent #[4, 3, 0] #[1, 1, 1] 0 == some 7
#guard emptyShapesOf convEmptyC == (some [6], some [6], some [6])
#guard agree convEmptyC emptyCIn64 emptyCIn32 #[0, 0, 0, 0, 0, 0] #[0, 0, 0, 0, 0, 0]
#guard emptyShapesOf convEmptyFree == (some [6, 0], some [6, 0], some [6, 0])

/-! ## Review repair A2: `#const` is a reserved axis spelling

`IdxExpr.isConstUnit` recognises the unit axes `lowerArith` mints by their `#const` spelling alone.
An ordinary one-axis writer over a source axis so spelled used to be mistaken for a lowered constant
and silently skipped by boxed-single-writer collection (published `[2]` instead of `[8]`).
`checkReservedAxisNames` now rejects the spelling first in both compile chains. -/

def ordAxisBox (i : AxisSpec) : TLProgram :=
  { decls := [.axis i (some 2), .axis k (some 8),
      .typedTensor .f32 "A" [i], .typedTensor .f32 "S" [k]]
    stmts := [.scatter "S" [.affine (.affine 0 [(1, i)])]
      { body := { terms := [{ factors := [.read "A" [.axis i]] }] }
        nonlin := .identity, agg := .sum }] }

def ordIn64 : NamedDenseEnv := ({} : NamedDenseEnv).insert "A" ⟨[2], #[1, 2]⟩
def ordIn32 : NamedDenseEnv32 := ({} : NamedDenseEnv32).insert "A" ⟨[2], #[1, 2]⟩

-- Accept-neighbour: the same program over an ordinarily spelled axis IS collected into the declared
-- box (`k` pinned to 8): every leg publishes eight cells.
#guard agree (ordAxisBox ⟨"constUser", 95, .nat⟩) ordIn64 ordIn32
  #[1, 2, 0, 0, 0, 0, 0, 0] #[1, 2, 0, 0, 0, 0, 0, 0]
-- A near-miss spelling (shorter than the prefix) is not reserved.
#guard (scheduled (ordAxisBox ⟨"#cons", 95, .nat⟩)).isSome
-- The reserved spelling is rejected, with the offending name, before anything is minted.
#guard (match (ordAxisBox ⟨"#constUser", 95, .nat⟩).compileToScheduled.run 0 with
  | .error e _ => e == .reservedAxisName "#constUser"
  | .ok _ _ => false)
#guard (match (ordAxisBox ⟨"#constUser", 95, .nat⟩).compile.run 0 with
  | .error e _ => e == .reservedAxisName "#constUser"
  | .ok _ _ => false)

end LeanNCD.Eval.Plan.ScatterGeometryTest
