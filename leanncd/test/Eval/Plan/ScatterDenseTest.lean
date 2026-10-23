import LeanNCD.Eval.Plan.Dense
import LeanNCD.Eval.Scatter

/-!
# S-A Task 4: the dense scatter worker

**Fixtures 1–5 only:** every expected tensor is the value the REFERENCE evaluator
(`Eval/Scatter.lean`, driven from surface syntax by `Eval/Eval.lean`) was measured to produce for the
same program — the five rows of plan §2.1 — not a value read back from `runDenseScatter`'s own
output. Differential parity against that evaluator is this feature's correctness gate, so a fixture
whose expectation came from the implementation under test would assert nothing.

The collision fixture and the four audit pins after it are NOT measured reference outputs and must
not be read as such: they are hand-derived from `evalScatter`'s algorithm and from
`ScatterCheckTest`'s already-pinned `scatterDestExtent` answers. Three of them are unreachable from
surface syntax at all (`elabTLLHSSlot` parses no negative placement coefficient or bias), and the
tropical unwritten-cell pin asserts a value the reference evaluator provably CANNOT produce — see
its own comment.

Same discipline as `KernelDenseTest` for the value fixtures and as `ScatterCheckTest` for the error
one: the collision fixture asserts the exact `PositionalInputError` constructor AND payload, so a
worker that detects a collision but cannot name both conflicting source coordinates fails here.

The pins after the six fixtures cover the cells that are not plain value fixtures: the out-of-range
placement and the two `.toNat` extent degeneracies (all REJECTED at check time since B6, formerly
silent skips) and a non-real unwritten-cell identity. None of the five measured programs can reach them: they are all in
range, all have a non-empty destination, and all use real sum-product, whose `reduceId` is `0.0` —
the same value a worker that ignored the algebra's identity entirely would use.
-/

namespace LeanNCD.Eval.Plan.ScatterDenseTest
open LeanNCD.Eval LeanNCD.Eval.Plan

/-- Check then run, surfacing either failure as a message — the scatter counterpart of
    `KernelDenseTest.runIt`. -/
def runScatter (sigs : Array TensorSignature) (s : ScatterPlan) (store : Array DenseTensor) :
    Except String DenseTensor :=
  match checkScatter sigs s with
  | .error e => .error s!"check failed: {repr e}"
  | .ok c => match runDenseScatter c store with
             | .error e => .error s!"run failed: {repr e}"
             | .ok d => .ok d

def shapeDataOf : Except String DenseTensor → Option (List Nat × Array Float)
  | .ok d => some (d.shape, d.data)
  | .error _ => none

/-! ## The shared single-source-axis shape

`X : [3]` at slot 0, the scattered destination at slot 1. The compute half's `outputShape` is `#[3]`
— the SOURCE iteration domain — for every fixture below; only `destShape`/`outCoeffs`/`outBias`
change, which is exactly the separation a scatter introduces and an assignment does not have. -/

def srcRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

/-- `:= X[i]` over `i : 3`, one value per source coordinate. -/
def srcCompute : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read srcRead] }]
  , algebra := admittedAlgebra }

/-- The placement map is the only thing that varies across the first four fixtures. -/
def placed (destShape : Array Nat) (coeffs : Array (Array Int)) (bias : Array Int) : ScatterPlan :=
  { compute := srcCompute, destShape := destShape, outCoeffs := coeffs, outBias := bias }

def sigsFor (destShape : Array Nat) : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := destShape, dtype := .f64 } ]

/-- `X = [1,2,3]`, with an empty destination slot the worker never reads. -/
def storeFor (destShape : Array Nat) : Array DenseTensor :=
  #[ { shape := [3], data := #[1.0, 2.0, 3.0] }, { shape := destShape.toList, data := #[] } ]

/-! ## Fixture 1 — `Out[2*i] := X[i]`, the strided upsample

Reference (§2.1): `shape=[6] data=#[1,0,2,0,3,0]`. Source coordinates `0,1,2` carry `1,2,3` and land
at destination `0,2,4`; the three odd cells are never written and keep the identity `0`. The extent is
`outExtent`'s `2·3 = 6`, not max-coordinate + 1 = 5, so the trailing zero is load-bearing: a
destination sized by the deleted `scatterOutDim` duplicate would have length 5 and end at `3`. -/
#guard shapeDataOf (runScatter (sigsFor #[6]) (placed #[6] #[#[2]] #[0]) (storeFor #[6]))
  == some ([6], #[1.0, 0.0, 2.0, 0.0, 3.0, 0.0])

/-! ## Fixture 2 — `Out[2*i+1] := X[i]`, a non-zero placement bias

Reference (§3.1): `shape=[6] data=#[0,1,0,2,0,3]`. The same stride shifted by one, so the values
land at destination `1,3,5` of the stride-aligned extent `6`, with no unreachable trailing cell.
A worker that dropped `outBias` from the placement would reproduce fixture 1 and fail here. -/
#guard shapeDataOf (runScatter (sigsFor #[6]) (placed #[6] #[#[2]] #[1]) (storeFor #[6]))
  == some ([6], #[0.0, 1.0, 0.0, 2.0, 0.0, 3.0])

/-! ## Fixture 3 — `Out[i+2] := X[i]`, a pure shift

Reference (§2.1): `shape=[5] data=#[0,0,1,2,3]`. Coefficient 1 with bias 2, so the values are
contiguous at destination `2,3,4` and only the two leading cells keep the identity. This is the case where
`outExtent` and max-coordinate + 1 agree (both 5) — the reason the extent trap survived every
pre-existing test until a strided write met it. -/
#guard shapeDataOf (runScatter (sigsFor #[5]) (placed #[5] #[#[1]] #[2]) (storeFor #[5]))
  == some ([5], #[0.0, 0.0, 1.0, 2.0, 3.0])

/-! ## Fixture 4 — `Y[i,i] := V[i]`, the diagonal write

Reference (§2.1): `shape=[3,3] data=#[7,0,0, 0,8,0, 0,0,9]`. A rank-2 destination from a rank-1
source: both placement rows are the same single-source-position identity, so source coordinate `i`
lands at `(i,i)` and the six off-diagonal cells keep the identity. This is the only fixture where the
placement map's rank exceeds the source domain's, which is what makes a destination-driven worker
structurally unable to produce it. -/
def diagStore : Array DenseTensor :=
  #[ { shape := [3], data := #[7.0, 8.0, 9.0] }, { shape := [3, 3], data := #[] } ]

#guard shapeDataOf (runScatter (sigsFor #[3, 3]) (placed #[3, 3] #[#[1], #[1]] #[0, 0]) diagStore)
  == some ([3, 3], #[7.0, 0.0, 0.0, 0.0, 8.0, 0.0, 0.0, 0.0, 9.0])

/-! ## Fixture 5 — `Up[2*i] := X[i]` then `Z[k] := Up[k]`, a scatter consumed downstream

Reference (§2.1): `Z: shape=[6] data=#[1,0,2,0,3,0]`. The load-bearing row — sizing flows OUT of a
scatter into a consumer, the pattern `test/Eval/Portfolio/GnnScatterTest.lean` SC1–SC8 guard on the
reference path. Here the scatter's result is installed at its own destination slot and an ordinary
`runDenseAssign` reads it back, so the fixture fails if the worker returns a SOURCE-shaped tensor
(length 3) rather than a destination-shaped one: the downstream read would then see a `[3]` tensor
where the signature says `[6]` and `validateStore` would reject it.

Slot 0 is `X : [3]`, slot 1 is `Up : [6]` (the scatter's destination and the assignment's source),
slot 2 is `Z : [6]`. -/
def chainSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }
   , { shape := #[6], dtype := .f64 }
   , { shape := #[6], dtype := .f64 } ]

def chainScatter : ScatterPlan := placed #[6] #[#[2]] #[0]

/-- `Z[k] := Up[k]` — an identity read of slot 1 over the DESTINATION extent. -/
def chainConsumer : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[6]
  , terms := #[{ iterationShape := #[6], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }
                                    , sourceShape := #[6], oobPolicy := .zeroPad }] }]
  , algebra := admittedAlgebra }

def chainStore : Array DenseTensor :=
  #[ { shape := [3], data := #[1.0, 2.0, 3.0] }
   , { shape := [6], data := #[] }
   , { shape := [6], data := #[] } ]

/-- Run the scatter, install its result at its own destination slot, then run the consumer. -/
def runChain : Except String DenseTensor := do
  let up ← match checkScatter chainSigs chainScatter with
    | .error e => .error s!"scatter check failed: {repr e}"
    | .ok c => (runDenseScatter c chainStore).mapError (fun e => s!"scatter run failed: {repr e}")
  let consumer ← match checkAssign chainSigs chainConsumer with
    | .error e => .error s!"consumer check failed: {repr e}"
    | .ok c => .ok c
  let z := runDenseAssign consumer (chainStore.set! 1 up)
  z.mapError (fun e => s!"consumer run failed: {repr e}")

#guard shapeDataOf runChain == some ([6], #[1.0, 0.0, 2.0, 0.0, 3.0, 0.0])

/-! ## Fixture 6 — `Out[i] := X[i]·Y[j]`, a genuine collision

`X = [1,2,3]`, `Y = [10,100]`. The source domain is the union of the LHS slot's axes with the RHS
read axes, so `j` — which appears on the RHS only — is a SOURCE axis, giving `compute.outputShape =
#[3,2]`. The placement row `#[1,0]` reads `i` and ignores `j`, so the two `j` values land on the same
destination cell: this is the reference's structure exactly, where what reads like "summing over `j`"
is multiple source coordinates colliding, folded with the destination's ⊕ (S3a), here real `+`.

Both `j` values land on destination `[i]`, so each cell is `X[i]·10 + X[i]·100 = 110·X[i]`: the sum
`[110, 220, 330]`, not an error (it was `scatterCollision [0] [0,0] [0,1]` under the retired
`.rejectCollisions` policy). The non-colliding fixtures above are the accept neighbours.

`destShape` is `outExtent`'s `0 + 1·3 + 0·2 = 3`; the zero coefficient on `j` contributes nothing to
the extent, which is the same arithmetic the degeneracy pin below exercises in isolation. -/
def collisionSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }
   , { shape := #[2], dtype := .f64 }
   , { shape := #[3], dtype := .f64 } ]

def collisionCompute : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[3, 2]
  , terms := #[{ iterationShape := #[3, 2], contextPos := #[], outputPos := #[0, 1]
               , reductionPos := #[]
               , factors := #[ .read { sourceSlot := 0, map := { coeffs := #[#[1, 0]], bias := #[0] }
                                     , sourceShape := #[3], oobPolicy := .zeroPad }
                             , .read { sourceSlot := 1, map := { coeffs := #[#[0, 1]], bias := #[0] }
                                     , sourceShape := #[2], oobPolicy := .zeroPad } ] }]
  , algebra := admittedAlgebra }

def collisionScatter : ScatterPlan :=
  { compute := collisionCompute, destShape := #[3], outCoeffs := #[#[1, 0]], outBias := #[0] }

def collisionStore : Array DenseTensor :=
  #[ { shape := [3], data := #[1.0, 2.0, 3.0] }
   , { shape := [2], data := #[10.0, 100.0] }
   , { shape := [3], data := #[] } ]

#guard shapeDataOf (runScatter collisionSigs collisionScatter collisionStore)
  == some ([3], #[110.0, 220.0, 330.0])

/-! ## Runtime case-audit pins

The cells no value fixture above reaches: since B6 the out-of-range placement and the two `.toNat`
extent degeneracies are rejected by `checkScatter` before the worker runs (the worker's own
`scatterPlacementOutOfRange` backstop needs unchecked evidence, and `CheckedScatterPlan.mk` is
private, so no test can construct it), plus the non-real unwritten-cell identity. -/

/- **Out-of-range placement is an ERROR (B6), rejected at CHECK time.** `Out[i-1] := X[i]` over
   `i : 3`: `outExtent` gives `(-1 + 3) = 2`, and source coordinate `0` places at destination `-1`,
   outside `[0, 2)`. The reference raises `EvalError.scatterWriteOutOfRange`; `checkScatter` rejects
   the plan (`scatterWriteOutOfRange dim min max extent` = `0 (-1) 1 2`), so `runScatter` never
   reaches the worker. This fixture USED to assert the silent skip (`some ([2], #[2.0, 3.0])`) and was
   flipped, not weakened: the same plan, now refused. The in-range neighbour right below keeps the
   shifted placement accepted. Programmatic-only: `elabTLLHSSlot` parses no negative bias. -/
def checkErrOf (sigs : Array TensorSignature) (s : ScatterPlan) : Option PlanError :=
  match checkScatter sigs s with
  | .error e => some e
  | .ok _ => none

#guard checkErrOf (sigsFor #[2]) (placed #[2] #[#[1]] #[-1]) == some (.scatterWriteOutOfRange 0 (-1) 1 2)
-- Accept-neighbour: `Out[i+1]` (extent 4, image [1,3]) runs and lands at cells 1..3.
#guard shapeDataOf (runScatter (sigsFor #[4]) (placed #[4] #[#[1]] #[1]) (storeFor #[4]))
  == some ([4], #[0.0, 1.0, 2.0, 3.0])

/- **Degeneracy 1 — a ZERO placement coefficient** (`Out[0*i] := X[i]`). `outExtent` gives `0·3 = 0`
   (`ScatterCheckTest` pins `scatterDestExtent #[3] #[0] 0 == some 0`); every source coordinate
   places at destination `0`, outside the zero-extent dimension, so the plan is now REJECTED
   (`0 0 0 0`) instead of producing the empty tensor. Flipped from `some ([0], #[])`. -/
#guard checkErrOf (sigsFor #[0]) (placed #[0] #[#[0]] #[0]) == some (.scatterWriteOutOfRange 0 0 0 0)

/- **Degeneracy 2 — a NEGATIVE placement coefficient.** `outExtent`'s `(0 + (-1)·3).toNat` clamps to
   `0`; the image is `[-2, 0]`, so the plan is REJECTED (`0 (-2) 0 0`). Distinct from degeneracy 1 in
   origin (`Int.toNat` clamping a negative extent versus a genuinely zero one) and in payload (min
   `-2` versus `0`). Flipped from `some ([0], #[])`. -/
#guard checkErrOf (sigsFor #[0]) (placed #[0] #[#[-1]] #[0]) == some (.scatterWriteOutOfRange 0 (-2) 0 0)

/- **Unwritten cells hold the destination algebra's `reduceId`, not a hard-coded `0.0`.** Fixture
   1's placement under tropical max-product, whose `reduceId` is `-∞`. The three written cells are
   unchanged (`max(-∞, x) = x` through both folds); the three unwritten ones read `-∞`, so a worker
   that initialised the destination to zero, or to the real algebra's identity, fails here while
   passing every fixture above.

   Since S3b this is no longer checked-layer-only: the reference `evalScatter` starts from the same
   0_K and folds with the same ⊕, so a tropical scatter IS a parity-checked entry, empty fibres
   included (fixtures 7 and 8 below, `ScatterTest` and `ScatterCompileTest` S11/S12). Every fixture
   above this one uses real sum-product, whose `reduceId` is `0.0`. -/
def maxScatter : ScatterPlan :=
  { placed #[6] #[#[2]] #[0] with
    compute := { srcCompute with algebra := admittedAlgebraMax } }

#guard shapeDataOf (runScatter (sigsFor #[6]) maxScatter (storeFor #[6]))
  == some ([6], #[1.0, -1.0 / 0.0, 2.0, -1.0 / 0.0, 3.0, -1.0 / 0.0])

/-! ## Fixture 7 — a tropical COLLISION folds with max/min, and the empty fibre is `∓∞` (S3b)

Donor: fixture 6 (`collisionScatter`), algebra moved to max-plus (⊗ is `+`) and the destination
widened to 4 cells with bias 1, so cell 0 is unwritten. `X = [1,2,3]`, `Y = [10,100]`: the two `j`
writes to cell `i+1` are `X[i]+10` and `X[i]+100`; their max is `X[i]+100 = [101,102,103]`, where the
sum fold (`2·X[i]+110`) or an overwrite by the first write (`X[i]+10`) would differ. Min-plus twin from
negated data (`X = [-1,-2,-3]`, `Y = [-10,-100]`): min `= X[i]-100 = [-101,-102,-103]`, cell 0 `+∞`. -/
def tropSigs4 : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[2], dtype := .f64 }, { shape := #[4], dtype := .f64 } ]

def tropCollide (alg : ContractionAlgebra) : ScatterPlan :=
  { collisionScatter with
    compute := { collisionCompute with algebra := alg }
    destShape := #[4], outBias := #[1] }

#guard shapeDataOf (runScatter tropSigs4 (tropCollide admittedAlgebraMax) collisionStore)
  == some ([4], #[-1.0 / 0.0, 101.0, 102.0, 103.0])

def collisionStoreNeg : Array DenseTensor :=
  #[ { shape := [3], data := #[-1.0, -2.0, -3.0] }
   , { shape := [2], data := #[-10.0, -100.0] }
   , { shape := [4], data := #[] } ]

#guard shapeDataOf (runScatter tropSigs4 (tropCollide admittedAlgebraMin) collisionStoreNeg)
  == some ([4], #[1.0 / 0.0, -101.0, -102.0, -103.0])

/-! ## Fixture 8 — F4: the reference and the raw checked plan AGREE on a contracted source axis (S3b)

`Out[i+1] := maxreduce(X[i,j])` over `i : 3`, `j : 2`; `j` is a CONTRACTED source axis (absent from
the LHS) and cell 0 is an empty fibre. Before S3b the direct reference summed the colliding writes
from `0` (`[0,6,10,6]`) while this worker took the max from `-∞`; now `evalScatter` starts at
`Combine.unit0` and folds with `Combine.combine`, so both give `[-∞, 5, 7, 4]`. -/
def f4Read : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[0, 0] }
  , sourceShape := #[3, 2], oobPolicy := .zeroPad }

def f4Scatter (alg : ContractionAlgebra) : ScatterPlan :=
  { compute :=
      { contextShape := #[], destinationSlot := 1, outputShape := #[3, 2]
      , terms := #[{ iterationShape := #[3, 2], contextPos := #[], outputPos := #[0, 1]
                   , reductionPos := #[], factors := #[.read f4Read] }]
      , algebra := alg }
    destShape := #[4], outCoeffs := #[#[1, 0]], outBias := #[1] }

def f4Sigs : Array TensorSignature :=
  #[ { shape := #[3, 2], dtype := .f64 }, { shape := #[4], dtype := .f64 } ]

def f4Store (xs : List Float) : Array DenseTensor :=
  #[ { shape := [3, 2], data := xs.toArray }, { shape := [4], data := #[] } ]

/-- The direct reference `evalScatter` on the same program (`Out[i+1] := agg(X[i,j])`). -/
def f4Reference (agg : AggOp) (xs : List Float) : Option (Array Float) :=
  let i : AxisSpec := { name := "i", uid := 1, kind := .real }
  let j : AxisSpec := { name := "j", uid := 2, kind := .real }
  let env : Std.HashMap String DenseTensor :=
    ({} : Std.HashMap String DenseTensor).insert "X" ⟨[3, 2], xs.toArray⟩
  let rhs : RHSExpr :=
    { body := { terms := [{ factors := [.read "X" [.axis i, .axis j]] }] }, nonlin := .identity, agg := agg }
  let sizes := (({} : Std.HashMap UID Nat).insert 1 3).insert 2 2
  (evalScatter [Decl.typedTensor .f64 "Out" [], Decl.typedTensor .f64 "X" []] env sizes "Out"
    [.affine (.shift i 1)] rhs [4]).toOption.map (·.2.data)

#guard (shapeDataOf (runScatter f4Sigs (f4Scatter admittedAlgebraMax) (f4Store [5, 1, 3, 7, 2, 4]))).map (·.2)
  == some #[-1.0 / 0.0, 5.0, 7.0, 4.0]
#guard f4Reference .max [5, 1, 3, 7, 2, 4] == some #[-1.0 / 0.0, 5.0, 7.0, 4.0]
-- min-plus twin (negated data)
#guard (shapeDataOf (runScatter f4Sigs (f4Scatter admittedAlgebraMin) (f4Store [-5, -1, -3, -7, -2, -4]))).map (·.2)
  == some #[1.0 / 0.0, -5.0, -7.0, -4.0]
#guard f4Reference .min [-5, -1, -3, -7, -2, -4] == some #[1.0 / 0.0, -5.0, -7.0, -4.0]
-- real neighbour (S3a, unchanged): the same program under the real algebra sums.
#guard f4Reference .sum [5, 1, 3, 7, 2, 4] == some #[0.0, 6.0, 10.0, 6.0]
#guard (shapeDataOf (runScatter f4Sigs (f4Scatter admittedAlgebra) (f4Store [5, 1, 3, 7, 2, 4]))).map (·.2)
  == some #[0.0, 6.0, 10.0, 6.0]

end LeanNCD.Eval.Plan.ScatterDenseTest
