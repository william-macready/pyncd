import LeanNCD.Eval.Plan.Check

/-!
# S-A Task 3: `checkScatter` and the `checkAssign` destination-shape extraction

Same discipline as `KernelCheckTest`: one mutation per new `PlanError` branch, asserting the exact
error constructor AND payload, so a checker that rejects for the wrong reason fails here.

Two things are pinned that a value-comparing test would otherwise miss:

* **the extraction's reason for existing** — `checkAssign` on a scatter's compute half WITHOUT
  `destSigShape?` fails with `destinationShapeMismatch #[3] #[6]` (the source iteration domain
  against the destination extent), and succeeds with `some #[6]`. If the parameter were ever
  defaulted the other way, or `checkScatter` stopped passing it, the first of those flips;
* **fill coherence is a rejection, not a normalisation** — `fillMismatchScatter` disagrees with its
  algebra's `reduceId` and asserts `scatterFillNotIdentity`. An implementation that silently rewrote
  `fill` to the identity would return `.ok` here, so the two readings are separable by this fixture.

Every acceptance fixture's `destShape` is the `LHSSlot.outExtent` convention's answer, NOT
max-coordinate + 1 and NOT the memory-sufficient bound `scale * (n - 1) + offset + 1`; `tightBound`
below pins the strided case where all three disagree.
-/

namespace LeanNCD.Eval.Plan.ScatterCheckTest
open LeanNCD.Eval.Plan

def isOk : Except PlanError CheckedScatterPlan → Bool
  | .ok _ => true | .error _ => false

def errOf : Except PlanError CheckedScatterPlan → Option PlanError
  | .ok _ => none | .error e => some e

def assignErrOf : Except PlanError CheckedAssignPlan → Option PlanError
  | .ok _ => none | .error e => some e

def assignIsOk : Except PlanError CheckedAssignPlan → Bool
  | .ok _ => true | .error _ => false

/-! ## `Out[2*i] := X[i]`, `X : [3]` — the reference strided upsample (extent 6) -/

/-- Slot 0 is the source `X : [3]`; slot 1 is the scattered destination `Out : [6]`. -/
def upSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }
   , { shape := #[6], dtype := .f64 } ]

/-- The compute half: one value per SOURCE coordinate `i`, so `outputShape` is `#[3]` — the source
    iteration domain — and NOT the destination's `#[6]`. -/
def upCompute : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
                                    , sourceShape := #[3], oobPolicy := .zeroPad }] }]
  , algebra := admittedAlgebra }

def upScatter : ScatterPlan :=
  { compute := upCompute, destShape := #[6], outCoeffs := #[#[2]], outBias := #[0]
  , fill := admittedAlgebra.reduceId, reduce := .rejectCollisions }

/- The extraction, both directions. Without `destSigShape?`, `checkAssign` compares the registered
   destination signature (`#[6]`) against the compute half's own `outputShape` (`#[3]`) and rejects —
   this is the trap that makes the parameter load-bearing rather than cosmetic. With `some #[6]` the
   same call succeeds, and every other clause is checked unchanged. -/
#guard assignErrOf (checkAssign upSigs upCompute) == some (.destinationShapeMismatch #[3] #[6])
#guard assignIsOk (checkAssign upSigs upCompute (some #[6]))

/- Acceptance 1: the strided upsample. `outExtent` gives `6`, while max-coordinate + 1 and the
   forbidden memory-sufficient bound both give `5` for this placement map. This is the case the
   deleted `scatterOutDim` duplicate got wrong, sizing a downstream reader to `5`; rejection 4 below
   pins that `5` is now refused. -/
#guard isOk (checkScatter upSigs upScatter)

#guard upScatter.destShape == #[6]

/-! ## `Out[2*i+1] := X[i]` — a nonzero placement bias (extent 7) -/

def offsetSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }
   , { shape := #[7], dtype := .f64 } ]

/- Acceptance 2: the same placement scale with a nonzero bias. `outExtent`'s answer is `7`, matching
   the reference evaluator's measured `shape=[7]` for this program, and the bias is carried into the
   derivation rather than dropped — `scatterDestExtent`'s pins at the end of this file separate the
   `outBias := #[0]` and `#[1]` cases directly. -/
#guard isOk (checkScatter offsetSigs
  { upScatter with destShape := #[7], outBias := #[1] })

/-! ## `Y[i,i] := V[i]` — the diagonal trigger, a rank-2 destination -/

def diagSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }
   , { shape := #[3, 3], dtype := .f64 } ]

/- Acceptance 3: two destination dimensions, each placement row spanning the single source axis.
   Both extents come from `outExtent` on their own row, giving `#[3, 3]` — the reference
   evaluator's measured shape for the diagonal write. -/
#guard isOk (checkScatter diagSigs
  { upScatter with destShape := #[3, 3], outCoeffs := #[#[1], #[1]], outBias := #[0, 0] })

/-! ## A tropical destination — fill coherence is not "fill is zero" -/

def maxScatter : ScatterPlan :=
  { upScatter with
    compute := { upCompute with algebra := admittedAlgebraMax }
    fill := admittedAlgebraMax.reduceId }

/- Acceptance 4: tropical max-product, whose `reduceId` is `-∞`, not `0.0`. The fill clause admits
   it because it is checked against `compute.algebra.reduceId` rather than against a constant — a
   checker hard-coding `0.0` would reject this. -/
#guard isOk (checkScatter upSigs maxScatter)

#guard maxScatter.fill == ScalarConst.f64 (Float.toBits (-1.0 / 0.0))

/-! ## Rejections — one per new clause -/

/-- Mutation: a tropical scatter whose `fill` is real sum-product's `0.0`. This is the incoherent
    pair §2.5 names: every unwritten cell would read `0.0` instead of `-∞`, so an all-negative
    output cell reports `0` as its maximum. -/
def fillMismatchScatter : ScatterPlan :=
  { maxScatter with fill := admittedAlgebra.reduceId }

/- Rejection 1 (fill coherence). Asserts the CONSTRUCTOR and both payloads: a checker that silently
   normalised `fill` to the algebra's identity would return `.ok` and fail this `#guard`. -/
#guard errOf (checkScatter upSigs fillMismatchScatter)
  == some (.scatterFillNotIdentity (.f64 (Float.toBits 0.0))
            (.f64 (Float.toBits (-1.0 / 0.0))))

/- Rejection 2 (collision-reduce admission). Only `rejectCollisions` has a worker; `sum`, and the
   three arms beside it, are matched explicitly and thrown on. -/
#guard errOf (checkScatter upSigs { upScatter with reduce := .sum })
  == some (.scatterReduceNotAdmitted .sum)

/- Rejection 3 (placement-row width — unchecked on the existing write path). The source iteration
   basis is `#[3]`, width 1; a two-wide row names a source position that does not exist. -/
#guard errOf (checkScatter upSigs { upScatter with outCoeffs := #[#[2, 0]] })
  == some (.scatterPlacementWidthMismatch 0 1 2)

/- Rejection 4 (destination extent, via `outExtent`). `destShape := #[5]` is exactly what both
   max-coordinate + 1 and the forbidden tighter bound produce for this placement map, and the
   signature table is mutated to agree with it — so the plan is internally consistent everywhere
   EXCEPT against the convention, which is the precise shape of the `scatterOutDim` soundness bug
   (a reader sized to `5` while the evaluator materialises `6`). -/
#guard errOf (checkScatter
  #[ { shape := #[3], dtype := .f64 }, { shape := #[5], dtype := .f64 } ]
  { upScatter with destShape := #[5] })
  == some (.scatterDestExtentMismatch 0 5 6)

/- Rejection 5 (placement-map rank). `outBias` carries two entries for a rank-1 destination; all
   three counts are reported because `outCoeffs` and `outBias` are separate fields and a single
   "actual" would hide which one disagrees. -/
#guard errOf (checkScatter upSigs { upScatter with outBias := #[0, 0] })
  == some (.scatterPlacementRankMismatch 1 1 2)

/- `scatterDestExtentUnknown` is unreachable via `checkScatter` as written: reaching the extent
   derivation requires the width clause above to have already forced `row.size ==
   compute.outputShape.size`, and `scatterPlacementSlot` mints one synthetic axis per row position
   with `uid` equal to that position — so `compute.outputShape[uid]?` is total and `outExtent`'s
   `.affine` arm always returns `some`. Named directly instead, the same way `KernelCheckTest` names
   `constDtypeMismatch` and `policyNotAdmitted`. -/
#guard (PlanError.scatterDestExtentUnknown 0) == PlanError.scatterDestExtentUnknown 0

/-! ## The zero-coefficient degeneracy, pinned

An all-zero placement row is reconstructed as `outExtent`'s `.affine` arm, never its `.const` arm:
the `.const` arm belongs to `LHSSlot.iterAt`, and `checkScatterNoScan` rejects a scatter-shaped LHS
carrying any iteration slot, so it cannot reach a `ScatterPlan`. `Out[0*i]` therefore keeps the
reference evaluator's documented `.toNat` degeneracy — extent `0`, an empty destination — rather
than being re-read as the constant coordinate `0` with extent `1`. -/
#guard scatterDestExtent #[3] #[0] 0 == some 0
#guard scatterDestExtent #[3] #[2] 0 == some 6
#guard scatterDestExtent #[3] #[2] 1 == some 7
#guard scatterDestExtent #[3] #[-1] 0 == some 0

end LeanNCD.Eval.Plan.ScatterCheckTest
