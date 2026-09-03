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
               , factors := #[.read readA, .read readB] }]
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
      factors := #[.read { readA with sourceSlot := 99 }] }] }) == some (.slotOutOfRange 99 3)

-- destination slot outside the signature table
#guard errOf (checkAssign sigs { goodPlan with destinationSlot := 99 })
  == some (.slotOutOfRange 99 3)

-- coefficient row no longer matches the term-basis width
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with
      factors := #[.read { readA with map := { coeffs := #[#[1]], bias := #[0] } }] }] })
  == some (.affineWidthMismatch 0 0 2 1)

-- positions no longer partition the iteration basis
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with reductionPos := #[] }] })
  == some (.positionsNotPartition 0)

-- declared source shape disagrees with the signature table
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with
      factors := #[.read { readA with sourceShape := #[7] }] }] })
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
      factors := #[.read { readA with map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[0] } }
                 , .read readB] }] })
  == some (.affineRankMismatch 0 0 1 2)

-- a term's outputPos projects extents that disagree with the declared outputShape
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with iterationShape := #[5, 3] }] })
  == some (.outputProjectionMismatch 0 #[5] #[4])

/- Fixture 11: `dtypeMismatch` is no longer produced by `checkAssign` AT ALL — assignment checking
   intentionally dropped source/destination dtype equality as an obligation (Task 4.2): the
   DESTINATION selects the algebra and gathering is dtype-blind, so `bool → f64` and `f64 → bool`
   reads are both admitted (fixtures 2 and 1 above). It is retained as a producer-less compatibility
   constructor. Nonlinearity checking is unaffected and keeps its own separate dtype-equality error,
   `NonlinPlanError.dtypeMismatch` (`Nonlin.lean`, exercised by `NonlinCheckTest`). Named directly
   instead. -/
#guard (PlanError.dtypeMismatch .f64 .f32) == PlanError.dtypeMismatch .f64 .f32

/- `constDtypeMismatch` is unreachable via `checkAssign` as written: reaching either
   `constMatchesDtype` check requires `(admittedAlgebrasFor destSig.dtype).contains a.algebra` to
   have already succeeded, and every algebra in a row carries exactly that row's dtype constants —
   `.f64` identities in the `f64` row, `.bool` identities in the `bool` row — so
   `constMatchesDtype destSig.dtype algebra.factorId/reduceId` is always `true` by the time either
   check runs. Confirmed empirically: an algebra with `factorId := .bool true` under an `f64`
   destination is rejected by `algebraNotAdmitted` (it is in no `f64` row), never
   `constDtypeMismatch`. Named directly instead. -/
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
               , factors := #[.read readX2] }]
  , algebra := admittedAlgebra }

#guard errOf (checkAssign sigs2 badContextPlan) == some (.contextProjectionMismatch 0 #[2] #[3])

-- Mutation: a top-level RawEvalPlan step with nonempty context. Verified: checkPlan rejects with
-- topLevelContextNotEmpty 0.
def topLevelBadAssign : AssignPlan :=
  { contextShape := #[2], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[2,3], contextPos := #[0], outputPos := #[1]
               , reductionPos := #[], factors := #[.read readX2] }]
  , algebra := admittedAlgebra }

def topLevelBadPlan : RawEvalPlan :=
  { tensorSigs := sigs2, inputSlots := #[0]
  , steps := #[.assign topLevelBadAssign]
   }

def checkPlanErrOf : Except PlanStepError CheckedEvalPlan → Option PlanStepError
  | .ok _ => none | .error e => some e

#guard checkPlanErrOf (checkPlan topLevelBadPlan) == some (.assign (.topLevelContextNotEmpty 0))

/-! ## Task 5.1: positional Iverson factors in the checker

Direct hand-built checked-plan fixtures (source Iverson stays rejected; these carry
`FactorPlan.iverson` in a hand-built `AssignPlan`). `goodPlan`'s iteration basis is `#[4, 3]`
(size 2), so a correctly-sized predicate leaf has coefficient width 2. Each locator fixture places a
NON-read factor BEFORE the failing read, so the all-factor index diverges from any filtered-read (or
filtered-predicate) index — today the two coincide in every read-only fixture, so a migration that
reindexed filtered factors would pass silently. -/

-- A predicate true at every coordinate (`0 < 1`), both leaves of the correct width (2).
def truePred2 : PosBoolExpr :=
  .rel .lt (.affine { coeffs := #[0, 0], bias := 0 }) (.affine { coeffs := #[0, 0], bias := 1 })

-- Same predicate, but its FIRST leaf has width 1 (≠ iterationShape.size = 2).
def badWidthPred : PosBoolExpr :=
  .rel .lt (.affine { coeffs := #[0], bias := 0 }) (.affine { coeffs := #[0, 0], bias := 1 })

-- Fixture: accepted positional Iverson. A correctly-sized predicate inserted BETWEEN the two reads
-- (all-factor index 1) — the checker's predicate arm accepts it.
#guard isOk (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with
      factors := #[.read readA, .iverson truePred2, .read readB] }] })

-- Fixture: predicate-width locator. The mis-sized predicate sits at all-factor index 1; the checker
-- reports `affineWidthMismatch 0 1 2 1` — `fi = 1` (all-factor), NOT a filtered-predicate index 0.
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with
      factors := #[.read readA, .iverson badWidthPred, .read readB] }] })
  == some (.affineWidthMismatch 0 1 2 1)

-- Fixture: read-after-predicate locator. Term is `[iverson(ok), read(bad shape)]`; the failing read
-- sits at all-factor index 1, so `sourceShapeMismatch 0 1 #[7] #[4]` reports `fi = 1` (all-factor),
-- NOT filtered-read 0.
#guard errOf (checkAssign sigs
  { goodPlan with terms := #[{ goodPlan.terms[0]! with
      factors := #[.iverson truePred2, .read { readA with sourceShape := #[7] }] }] })
  == some (.sourceShapeMismatch 0 1 #[7] #[4])

/-! ## Task 4.2: Boolean destinations, mixed source dtypes, and `f32` still rejected

`goodPlan` unchanged except for the one field each fixture names. `sigs` is
`[0: A f64 #[4], 1: B f64 #[3], 2: Y f64 #[4]]`; the Boolean variants below retag exactly one slot.
Acceptance means `checkAssign` returns evidence — the Dense semantics these algebras denote are
pinned separately, in `KernelDenseTest`. -/

-- Slot 2 (the destination) retagged `bool`; sources stay `f64`.
def boolDestSigs : Array TensorSignature :=
  #[ { shape := #[4], dtype := .f64 }
   , { shape := #[3], dtype := .f64 }
   , { shape := #[4], dtype := .bool } ]

-- Slot 0 (a source) retagged `bool`; destination stays `f64`.
def boolSrcSigs : Array TensorSignature :=
  #[ { shape := #[4], dtype := .bool }
   , { shape := #[3], dtype := .f64 }
   , { shape := #[4], dtype := .f64 } ]

-- Slot 0 AND slot 2 retagged `bool`.
def boolBothSigs : Array TensorSignature :=
  #[ { shape := #[4], dtype := .bool }
   , { shape := #[3], dtype := .f64 }
   , { shape := #[4], dtype := .bool } ]

def boolPlan : AssignPlan := { goodPlan with algebra := admittedAlgebraBool }

-- Fixture 1: destination signature and assignment algebra Boolean, both sources still `f64`.
-- A real source feeding a predicate destination is admitted — the destination selects the algebra.
#guard isOk (checkAssign boolDestSigs boolPlan)

-- Fixture 2: source slot 0 Boolean, destination `f64`, real sum-product retained. A predicate
-- source feeding a real destination is admitted; source dtype does not change gathering.
#guard isOk (checkAssign boolSrcSigs goodPlan)

-- Fixture 3: Boolean source into the Boolean destination of fixture 1. Fixture 1 is this same plan
-- with source slot 0 restored to `f64`, so the pair pins that BOTH source dtypes reach a predicate
-- destination.
#guard isOk (checkAssign boolBothSigs boolPlan)

-- Fixture 4: fixture 1 with the assignment algebra restored to real sum-product. Algebra admission
-- is destination-specific, so `admittedAlgebra` is NOT admitted at a Boolean destination.
#guard errOf (checkAssign boolDestSigs goodPlan) == some (.algebraNotAdmitted admittedAlgebra)

-- Fixture 4b, the other direction: the Boolean algebra is not admitted at an `f64` destination.
-- Without this, "admit every algebra everywhere" would still pass fixtures 1-4.
#guard errOf (checkAssign sigs boolPlan) == some (.algebraNotAdmitted admittedAlgebraBool)

-- Fixture 5: the two `f32` guards above (destination slot 2, source slot 0) are retained unchanged
-- with their exact `dtypeNotAdmitted` slot payloads. Here is the third, Boolean-path case: `f32` is
-- rejected at a source of a Boolean destination too, i.e. widening reads to `bool` did not widen
-- them to "anything but f64".
#guard errOf (checkAssign
  #[ { shape := #[4], dtype := .f32 }, { shape := #[3], dtype := .f64 }
   , { shape := #[4], dtype := .bool } ] boolPlan)
  == some (.dtypeNotAdmitted 0 .f32)

-- ... and at a Boolean-algebra destination itself: `f32` admits no algebra at all, but the earlier
-- destination-dtype guard is what reports it, naming the slot.
#guard errOf (checkAssign
  #[ { shape := #[4], dtype := .f64 }, { shape := #[3], dtype := .f64 }
   , { shape := #[4], dtype := .f32 } ] boolPlan)
  == some (.dtypeNotAdmitted 2 .f32)

end LeanNCD.Eval.Plan.KernelCheckTest
