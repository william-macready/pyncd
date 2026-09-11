import LeanNCD.Eval.Plan.Dense

/-!
# S-A Task 4: the dense scatter worker

Every expected tensor here is the value the REFERENCE evaluator (`Eval/Scatter.lean`, driven from
surface syntax by `Eval/Eval.lean`) was measured to produce for the same program — the five rows of
plan §2.1 — not a value read back from `runDenseScatter`'s own output. Differential parity against
that evaluator is this feature's correctness gate, so a fixture whose expectation came from the
implementation under test would assert nothing.

Same discipline as `KernelDenseTest` for the value fixtures and as `ScatterCheckTest` for the error
one: the collision fixture asserts the exact `PositionalInputError` constructor AND payload, so a
worker that detects a collision but cannot name both conflicting source coordinates fails here.

The four pins after the six fixtures cover the runtime cells `checkScatter`'s docstring explicitly
leaves to this worker — the silent out-of-range skip, the two `.toNat` extent degeneracies, and a
non-zero `fill`. None of the five measured programs can reach them: they are all in range, all have
a non-empty destination, and all use real sum-product, whose `reduceId` is `0.0` — the same value a
worker that ignored `fill` entirely would use.
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

/-- The runtime error a checked scatter raises, or `none` if it checked and ran. -/
def posErrOf (sigs : Array TensorSignature) (s : ScatterPlan) (store : Array DenseTensor) :
    Option PositionalInputError :=
  match checkScatter sigs s with
  | .error _ => none
  | .ok c => match runDenseScatter c store with
             | .error e => some e
             | .ok _ => none

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
  { compute := srcCompute, destShape := destShape, outCoeffs := coeffs, outBias := bias
  , fill := admittedAlgebra.reduceId, reduce := .rejectCollisions }

def sigsFor (destShape : Array Nat) : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := destShape, dtype := .f64 } ]

/-- `X = [1,2,3]`, with an empty destination slot the worker never reads. -/
def storeFor (destShape : Array Nat) : Array DenseTensor :=
  #[ { shape := [3], data := #[1.0, 2.0, 3.0] }, { shape := destShape.toList, data := #[] } ]

/-! ## Fixture 1 — `Out[2*i] := X[i]`, the strided upsample

Reference (§2.1): `shape=[6] data=#[1,0,2,0,3,0]`. Source coordinates `0,1,2` carry `1,2,3` and land
at destination `0,2,4`; the three odd cells are never written and keep `fill = 0`. The extent is
`outExtent`'s `2·3 = 6`, not max-coordinate + 1 = 5, so the trailing zero is load-bearing: a
destination sized by the deleted `scatterOutDim` duplicate would have length 5 and end at `3`. -/
#guard shapeDataOf (runScatter (sigsFor #[6]) (placed #[6] #[#[2]] #[0]) (storeFor #[6]))
  == some ([6], #[1.0, 0.0, 2.0, 0.0, 3.0, 0.0])

/-! ## Fixture 2 — `Out[2*i+1] := X[i]`, a non-zero placement bias

Reference (§2.1): `shape=[7] data=#[0,1,0,2,0,3,0]`. The same stride shifted by one, so the values
land at destination `1,3,5` of an extent-7 destination (`outExtent` = `1 + 2·3`) and BOTH boundary
cells stay at `fill`. A worker that dropped `outBias` from the placement would reproduce fixture 1's
placement inside a 7-cell destination and fail here. -/
#guard shapeDataOf (runScatter (sigsFor #[7]) (placed #[7] #[#[2]] #[1]) (storeFor #[7]))
  == some ([7], #[0.0, 1.0, 0.0, 2.0, 0.0, 3.0, 0.0])

/-! ## Fixture 3 — `Out[i+2] := X[i]`, a pure shift

Reference (§2.1): `shape=[5] data=#[0,0,1,2,3]`. Coefficient 1 with bias 2, so the values are
contiguous at destination `2,3,4` and only the two leading cells keep `fill`. This is the case where
`outExtent` and max-coordinate + 1 agree (both 5) — the reason the extent trap survived every
pre-existing test until a strided write met it. -/
#guard shapeDataOf (runScatter (sigsFor #[5]) (placed #[5] #[#[1]] #[2]) (storeFor #[5]))
  == some ([5], #[0.0, 0.0, 1.0, 2.0, 3.0])

/-! ## Fixture 4 — `Y[i,i] := V[i]`, the diagonal write

Reference (§2.1): `shape=[3,3] data=#[7,0,0, 0,8,0, 0,0,9]`. A rank-2 destination from a rank-1
source: both placement rows are the same single-source-position identity, so source coordinate `i`
lands at `(i,i)` and the six off-diagonal cells keep `fill`. This is the only fixture where the
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
is multiple source coordinates colliding, resolved by `opts.reduce` rather than by a contraction.

Under `.rejectCollisions` — the only policy `checkScatter` admits — that is an error, not a merge.
Row-major source enumeration reaches `[0,0]` first and `[0,1]` second, both placing at destination
`[0]`, so both conflicting source coordinates are named and `first` is `[0,0]`.

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
  { compute := collisionCompute, destShape := #[3], outCoeffs := #[#[1, 0]], outBias := #[0]
  , fill := admittedAlgebra.reduceId, reduce := .rejectCollisions }

def collisionStore : Array DenseTensor :=
  #[ { shape := [3], data := #[1.0, 2.0, 3.0] }
   , { shape := [2], data := #[10.0, 100.0] }
   , { shape := [3], data := #[] } ]

#guard posErrOf collisionSigs collisionScatter collisionStore
  == some (.scatterCollision [0] [0, 0] [0, 1])

/-! ## Runtime case-audit pins

The four cells `checkScatter`'s docstring hands to this worker, none of which any fixture above can
reach. -/

/- **Out-of-range placement is skipped SILENTLY, not rejected.** `Out[i-1] := X[i]` over `i : 3`:
   `outExtent` gives `(-1 + 3) = 2`, which `checkScatter` accepts, but source coordinate `0` places
   at destination `-1`, outside `[0, 2)`. The reference simply does not write it, with no diagnostic,
   so the result is the two remaining values — NOT an error and NOT `X[0]` aliased onto some valid
   cell, which is what a flat-offset bounds test would produce (`(-1).toNat = 0` flattens to the same
   address as destination `0`). Programmatic-only: `elabTLLHSSlot` parses no negative bias. -/
#guard shapeDataOf (runScatter (sigsFor #[2]) (placed #[2] #[#[1]] #[-1]) (storeFor #[2]))
  == some ([2], #[2.0, 3.0])

/- **Degeneracy 1 — a ZERO placement coefficient.** `outExtent` gives `0·3 = 0`, so the destination
   is empty and `checkScatter` admits the plan (`ScatterCheckTest` pins `scatterDestExtent #[3] #[0]
   0 == some 0`). Every source coordinate places at destination `0`, which is out of range in a
   zero-extent dimension, so the skip above swallows all three writes and the result is the empty
   tensor. This is a reproduced reference degeneracy, not a repaired one. -/
#guard shapeDataOf (runScatter (sigsFor #[0]) (placed #[0] #[#[0]] #[0]) (storeFor #[0]))
  == some ([0], #[])

/- **Degeneracy 2 — a NEGATIVE placement coefficient.** `outExtent`'s `(0 + (-1)·3).toNat` clamps to
   `0`, so again an empty destination that `checkScatter` admits, and again three writes with nowhere
   to go. Distinct from degeneracy 1 in origin (`Int.toNat` clamping a negative extent, versus a
   genuinely zero one) even though both land on the same empty result. -/
#guard shapeDataOf (runScatter (sigsFor #[0]) (placed #[0] #[#[-1]] #[0]) (storeFor #[0]))
  == some ([0], #[])

/- **`fill` is the plan's constant, not a hard-coded `0.0`.** Fixture 1's placement under tropical
   max-product, whose `reduceId` — and therefore, by `checkScatter`'s coherence clause, whose `fill`
   — is `-∞`. The three written cells are unchanged (`max(-∞, x) = x` through both folds); the three
   unwritten ones read `-∞`, so a worker that initialised the destination to zero, or to the real
   algebra's identity, fails here while passing every fixture above. -/
def maxScatter : ScatterPlan :=
  { placed #[6] #[#[2]] #[0] with
    compute := { srcCompute with algebra := admittedAlgebraMax }
    fill := admittedAlgebraMax.reduceId }

#guard shapeDataOf (runScatter (sigsFor #[6]) maxScatter (storeFor #[6]))
  == some ([6], #[1.0, -1.0 / 0.0, 2.0, -1.0 / 0.0, 3.0, -1.0 / 0.0])

end LeanNCD.Eval.Plan.ScatterDenseTest
