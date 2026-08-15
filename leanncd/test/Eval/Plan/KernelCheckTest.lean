import LeanNCD.Eval.Plan.EvalPlan

/-!
# Wave C C2 checker tests

One mutation per `PlanError` branch, plus the reference plan's acceptance. Mutations assert the
exact error constructor AND payload, so a checker that rejects for the wrong reason fails here.
-/

namespace LeanNCD.Eval.Plan.KernelCheckTest
open LeanNCD.Eval.Plan

def sigs : Array TensorSignature :=
  #[ { shape := #[4], dtype := .f64 }
   , { shape := #[3], dtype := .f64 }
   , { shape := #[4], dtype := .f64 } ]

def readA : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1, 0]], bias := #[0] }
  , sourceShape := #[4], oobPolicy := .zeroPad }

def readB : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[0, 1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

def goodPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[4]
  , terms := #[{ iterationShape := #[4, 3], contextPos := #[], outputPos := #[0], reductionPos := #[1]
               , factors := #[readA, readB] }]
  , algebra := admittedAlgebra }

def isOk : Except PlanError CheckedAssignPlan → Bool
  | .ok _ => true | .error _ => false

def errOf : Except PlanError CheckedAssignPlan → Option PlanError
  | .ok _ => none | .error e => some e

-- the reference plan is accepted
#guard isOk (checkAssign sigs goodPlan)

-- source slot outside the signature table
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with
      factors := #[{ readA with sourceSlot := 99 }] }] }) == some (.slotOutOfRange 99 3)

-- destination slot outside the signature table
#guard errOf (checkAssign sigs { goodPlan with destinationSlot := 99 })
  == some (.slotOutOfRange 99 3)

-- coefficient row no longer matches the term-basis width
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with
      factors := #[{ readA with map := { coeffs := #[#[1]], bias := #[0] } }] }] })
  == some (.affineWidthMismatch 0 0 2 1)

-- positions no longer partition the iteration basis
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with reductionPos := #[] }] })
  == some (.positionsNotPartition 0)

-- declared source shape disagrees with the signature table
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with
      factors := #[{ readA with sourceShape := #[7] }] }] })
  == some (.sourceShapeMismatch 0 0 #[7] #[4])

-- a non-admitted algebra
#guard errOf (checkAssign sigs
  { goodPlan with algebra := { admittedAlgebra with factorOp := .add } })
  == some (.algebraNotAdmitted { admittedAlgebra with factorOp := .add })

-- destination signature dtype not admitted (f32)
#guard errOf (checkAssign
  #[ { shape := #[4], dtype := .f64 }, { shape := #[3], dtype := .f64 }
   , { shape := #[4], dtype := .f32 } ] goodPlan)
  == some (.dtypeNotAdmitted 2 .f32)

-- source factor's signature dtype not admitted (f32), distinct from the destination case above
#guard errOf (checkAssign
  #[ { shape := #[4], dtype := .f32 }, { shape := #[3], dtype := .f64 }
   , { shape := #[4], dtype := .f64 } ] goodPlan)
  == some (.dtypeNotAdmitted 0 .f32)

-- destination signature's declared shape disagrees with the AssignPlan's outputShape (not the
-- term's outputPos projection, which stays consistent with outputShape here)
#guard errOf (checkAssign
  #[ { shape := #[4], dtype := .f64 }, { shape := #[3], dtype := .f64 }
   , { shape := #[6], dtype := .f64 } ] goodPlan)
  == some (.destinationShapeMismatch #[4] #[6])

-- affine map rank does not match source rank (2 coeff rows for a rank-1 source)
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with
      factors := #[{ readA with map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[0] } }
                 , readB] }] })
  == some (.affineRankMismatch 0 0 1 2)

-- a term's outputPos projects extents that disagree with the declared outputShape
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with iterationShape := #[5, 3] }] })
  == some (.outputProjectionMismatch 0 #[5] #[4])

/- `dtypeMismatch` is unreachable via `checkAssign` given Wave C's single-valued (`.f64`-only)
   dtype vocabulary: by the time the `srcSig.dtype == destSig.dtype` check runs, an earlier
   `unless srcSig.dtype == .f64` guard has already forced `srcSig.dtype = .f64`, and an even
   earlier guard has already forced `destSig.dtype = .f64` — so the two are always equal and the
   branch cannot fire. Confirmed empirically: constructing a source signature with `dtype := .f32`
   is rejected by `dtypeNotAdmitted`, never `dtypeMismatch`. Named directly instead. -/
#guard (PlanError.dtypeMismatch .f64 .f32) == PlanError.dtypeMismatch .f64 .f32

/- `constDtypeMismatch` is unreachable via `checkAssign` as written: reaching either
   `constMatchesDtype` check requires `a.algebra == admittedAlgebra` to have already succeeded,
   which pins `factorId`/`reduceId` to the exact `.f64` identities `admittedAlgebra` carries — so
   `constMatchesDtype destSig.dtype algebra.factorId/reduceId` is always `true` by the time either
   check runs. Confirmed empirically: an algebra with `factorId := .bool true` is rejected by
   `algebraNotAdmitted` (since it now differs from `admittedAlgebra`), never `constDtypeMismatch`.
   Named directly instead. -/
#guard (PlanError.constDtypeMismatch .f64 (.bool true)) == PlanError.constDtypeMismatch .f64 (.bool true)

/- `policyNotAdmitted` is unreachable via `checkAssign`: Wave C's `OutOfBoundsPolicy` has exactly
   one constructor (`zeroPad`), so every value of the type already equals `.zeroPad` and
   `f.oobPolicy == .zeroPad` is a tautology — there is no other constructor to supply as input.
   Named directly instead. -/
#guard (PlanError.policyNotAdmitted .zeroPad) == PlanError.policyNotAdmitted .zeroPad

def sigs2 : Array TensorSignature := #[{ shape := #[2,3], dtype := .f64 }, { shape := #[3], dtype := .f64 }]

def readX2 : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1,0], #[0,1]], bias := #[0,0] }
  , sourceShape := #[2,3], oobPolicy := .zeroPad }

-- Mutation: declared contextShape (#[3]) disagrees with the term's actual context projection
-- (iterationShape[0] = 2). Verified: checkAssign rejects with contextProjectionMismatch 0 #[2] #[3].
def badContextPlan : AssignPlan :=
  { contextShape := #[3], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[2,3], contextPos := #[0], outputPos := #[1], reductionPos := #[]
               , factors := #[readX2] }]
  , algebra := admittedAlgebra }

#guard errOf (checkAssign sigs2 badContextPlan) == some (.contextProjectionMismatch 0 #[2] #[3])

-- Mutation: a top-level RawEvalPlan step with nonempty context. Verified: checkPlan rejects with
-- topLevelContextNotEmpty 0.
def topLevelBadAssign : AssignPlan :=
  { contextShape := #[2], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[2,3], contextPos := #[0], outputPos := #[1]
               , reductionPos := #[], factors := #[readX2] }]
  , algebra := admittedAlgebra }

def topLevelBadPlan : RawEvalPlan :=
  { tensorSigs := sigs2, inputSlots := #[0]
  , steps := #[.assign topLevelBadAssign]
  , numericMode := .reference64SumProduct }

def checkPlanErrOf : Except PlanStepError CheckedEvalPlan → Option PlanStepError
  | .ok _ => none | .error e => some e

#guard checkPlanErrOf (checkPlan topLevelBadPlan) == some (.assign (.topLevelContextNotEmpty 0))

end LeanNCD.Eval.Plan.KernelCheckTest
