import LeanNCD.Eval.Plan.Dense

/-!
# Wave C C2 Dense interpreter tests

Every expected tensor here is hand-computed and independently confirmed against the reference
evaluator's semantics; none was read back from this interpreter's own output.
-/

namespace LeanNCD.Eval.Plan.KernelDenseTest
open LeanNCD.Eval LeanNCD.Eval.Plan

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

/-- `Y[i] := A[i] · B[j]`, contracted over `j`. -/
def contractPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[4]
  , terms := #[{ iterationShape := #[4, 3], contextPos := #[], outputPos := #[0], reductionPos := #[1]
               , factors := #[readA, readB] }]
  , algebra := admittedAlgebra }

def storeAB : Array DenseTensor :=
  #[ { shape := [4], data := #[10.0, 100.0, 1000.0, 10000.0] }
   , { shape := [3], data := #[1.0, 2.0, 3.0] }
   , { shape := [4], data := #[] } ]

/-- Run a plan end-to-end, surfacing either failure as a message. -/
def runIt (sigs : Array TensorSignature) (a : AssignPlan) (store : Array DenseTensor) :
    Except String DenseTensor :=
  match checkAssign sigs a with
  | .error e => .error s!"check failed: {repr e}"
  | .ok c => match runDenseAssign c store with
             | .error e => .error s!"run failed: {repr e}"
             | .ok d => .ok d

def dataOf : Except String DenseTensor → Option (Array Float)
  | .ok d => some d.data
  | .error _ => none

-- ΣB = 6, so Y[i] = A[i] · 6.  Verified by execution and by hand.
#guard dataOf (runIt sigs contractPlan storeAB) == some #[60.0, 600.0, 6000.0, 60000.0]

-- Tropical reductions: clone `contractPlan`, change only the algebra. `Y[i] := A[i] · B[j]` reduced
-- over `j` under max/min instead of sum. The out-of-bounds zero-pad is untouched (there are no OOB
-- reads here); only the reduction identity/operator changes.

-- max over B = [1,2,3] is 3, so Y[i] = A[i] · 3.  Verified by execution.
def maxContractPlan : AssignPlan := { contractPlan with algebra := admittedAlgebraMax }
#guard dataOf (runIt sigs maxContractPlan storeAB) == some #[30.0, 300.0, 3000.0, 30000.0]

-- min over B = [1,2,3] is 1, so Y[i] = A[i] · 1.  Verified by execution.
def minContractPlan : AssignPlan := { contractPlan with algebra := admittedAlgebraMin }
#guard dataOf (runIt sigs minContractPlan storeAB) == some #[10.0, 100.0, 1000.0, 10000.0]

-- Identity is load-bearing: with an all-NEGATIVE `B = [-1,-2,-3]`, max reduces to -1, so
-- Y[i] = A[i]·(-1). Only the `−∞` reduction seed makes this right — a `0` seed would win every
-- column and yield `[0,0,0,0]`. This is the fixture the §3.2 identity mutation flips (and only it,
-- since the two above have positive column maxima the seed never beats). Verified by execution.
def storeNegB : Array DenseTensor :=
  #[ { shape := [4], data := #[10.0, 100.0, 1000.0, 10000.0] }
   , { shape := [3], data := #[-1.0, -2.0, -3.0] }
   , { shape := [4], data := #[] } ]
#guard dataOf (runIt sigs maxContractPlan storeNegB) == some #[-10.0, -100.0, -1000.0, -10000.0]

-- Out-of-bounds interaction with a tropical reduction — the plan's central subtlety, exercised
-- directly. `Y[i] := max_j A[i,j]` with the reduction axis `j` ranging over {0,1,2} but `A` only
-- 2 columns wide, so the read at `j=2` is out of bounds and `zeroPad` returns `0.0`. That `0.0`
-- is a FACTOR value (it flows through `factorFold`'s mul, `1.0 · 0.0 = 0.0`) and so enters the max
-- fold as a genuine term value of `0.0` — it is NOT the reduction identity (which is `−∞`). With
-- all-negative valid data the padded `0.0` therefore WINS the max: `Y[i] = max(A[i,0], A[i,1], 0.0)
-- = 0.0`. This is observable and consistent with the reference's identical zero-extension (the pad
-- affects the result, it just does so the same way in both evaluators), not an implementation
-- divergence. Verified by execution.
def oobSigs : Array TensorSignature :=
  #[ { shape := #[2, 2], dtype := .f64 }, { shape := #[2], dtype := .f64 } ]

def oobReadA : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[0, 0] }
  , sourceShape := #[2, 2], oobPolicy := .zeroPad }

def oobMaxPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[2]
  , terms := #[{ iterationShape := #[2, 3], contextPos := #[], outputPos := #[0], reductionPos := #[1]
               , factors := #[oobReadA] }]
  , algebra := admittedAlgebraMax }

def oobStore : Array DenseTensor :=
  #[ { shape := [2, 2], data := #[-1.0, -2.0, -3.0, -4.0] }, { shape := [2], data := #[] } ]

#guard dataOf (runIt oobSigs oobMaxPlan oobStore) == some #[0.0, 0.0]

/-!
## Additional fixtures (Step 3)
-/

-- identity: Y[i] := X[i].

def identitySigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 } ]

def identityRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

def identityPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[identityRead] }]
  , algebra := admittedAlgebra }

def identityStore : Array DenseTensor :=
  #[ { shape := [3], data := #[7.0, 8.0, 9.0] }, { shape := [3], data := #[] } ]

-- Y[i] := X[i]; hand computation: Y = X = [7, 8, 9].
#guard dataOf (runIt identitySigs identityPlan identityStore) == some #[7.0, 8.0, 9.0]

-- transpose: Y[i,j] := X[j,i] — two output positions, coefficient rows swapped.

def transposeSigs : Array TensorSignature :=
  #[ { shape := #[3, 2], dtype := .f64 }, { shape := #[2, 3], dtype := .f64 } ]

def transposeRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[0, 1], #[1, 0]], bias := #[0, 0] }
  , sourceShape := #[3, 2], oobPolicy := .zeroPad }

def transposePlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[2, 3]
  , terms := #[{ iterationShape := #[2, 3], contextPos := #[], outputPos := #[0, 1], reductionPos := #[]
               , factors := #[transposeRead] }]
  , algebra := admittedAlgebra }

def transposeStore : Array DenseTensor :=
  #[ { shape := [3, 2], data := #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0] }
   , { shape := [2, 3], data := #[] } ]

-- Y[i,j] := X[j,i]; X row-major [j,i]: X[0,*]=(1,2) X[1,*]=(3,4) X[2,*]=(5,6).
-- Y[0,0]=X[0,0]=1 Y[0,1]=X[1,0]=3 Y[0,2]=X[2,0]=5 Y[1,0]=X[0,1]=2 Y[1,1]=X[1,1]=4 Y[1,2]=X[2,1]=6.
#guard dataOf (runIt transposeSigs transposePlan transposeStore) ==
  some #[1.0, 3.0, 5.0, 2.0, 4.0, 6.0]

-- shift: Y[i] := X[i-2] — zero-padding at the LOWER boundary.

def shiftSigs : Array TensorSignature :=
  #[ { shape := #[5], dtype := .f64 }, { shape := #[5], dtype := .f64 } ]

def shiftRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[-2] }
  , sourceShape := #[5], oobPolicy := .zeroPad }

def shiftPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[5]
  , terms := #[{ iterationShape := #[5], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[shiftRead] }]
  , algebra := admittedAlgebra }

def shiftStore : Array DenseTensor :=
  #[ { shape := [5], data := #[10.0, 20.0, 30.0, 40.0, 50.0] }, { shape := [5], data := #[] } ]

-- Y[i] := X[i-2]; i=0,1 read X[-2],X[-1] -> zero-pad (lower boundary);
-- i=2,3,4 read X[0],X[1],X[2] = 10,20,30.
#guard dataOf (runIt shiftSigs shiftPlan shiftStore) == some #[0.0, 0.0, 10.0, 20.0, 30.0]

-- stride: Y[i] := X[2*i] against a source too short for the last output index — zero-padding at
-- the UPPER boundary.

def strideSigs : Array TensorSignature :=
  #[ { shape := #[5], dtype := .f64 }, { shape := #[4], dtype := .f64 } ]

def strideRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[2]], bias := #[0] }
  , sourceShape := #[5], oobPolicy := .zeroPad }

def stridePlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[4]
  , terms := #[{ iterationShape := #[4], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[strideRead] }]
  , algebra := admittedAlgebra }

def strideStore : Array DenseTensor :=
  #[ { shape := [5], data := #[1.0, 2.0, 3.0, 4.0, 5.0] }, { shape := [4], data := #[] } ]

-- Y[i] := X[2i]; i=0,1,2 read X[0],X[2],X[4] = 1,3,5; i=3 reads X[6], out of range (source has
-- only indices 0..4) -> zero-pad (upper boundary).
#guard dataOf (runIt strideSigs stridePlan strideStore) == some #[1.0, 3.0, 5.0, 0.0]

-- multi-axis affine: Y[i,j] := X[2*i + j], one coefficient row #[2, 1].

def maffSigs : Array TensorSignature :=
  #[ { shape := #[5], dtype := .f64 }, { shape := #[2, 3], dtype := .f64 } ]

def maffRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[2, 1]], bias := #[0] }
  , sourceShape := #[5], oobPolicy := .zeroPad }

def maffPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[2, 3]
  , terms := #[{ iterationShape := #[2, 3], contextPos := #[], outputPos := #[0, 1], reductionPos := #[]
               , factors := #[maffRead] }]
  , algebra := admittedAlgebra }

def maffStore : Array DenseTensor :=
  #[ { shape := [5], data := #[100.0, 200.0, 300.0, 400.0, 500.0] }
   , { shape := [2, 3], data := #[] } ]

-- Y[i,j] := X[2i+j]; i=0: j=0,1,2 -> X[0,1,2]=100,200,300; i=1: j=0,1,2 -> X[2,3,4]=300,400,500.
#guard dataOf (runIt maffSigs maffPlan maffStore) ==
  some #[100.0, 200.0, 300.0, 300.0, 400.0, 500.0]

-- multiple terms: Y[i] := A[i] + Σⱼ B[i,j] — term1 (A) has no reduction and lacks the factor
-- term2 (B) has; confirms each term folds once per output coordinate, not once per reduction
-- coordinate of the OTHER term.

def mtermSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }
   , { shape := #[2, 3], dtype := .f64 }
   , { shape := #[2], dtype := .f64 } ]

def mtermReadA : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[2], oobPolicy := .zeroPad }

def mtermReadB : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[0, 0] }
  , sourceShape := #[2, 3], oobPolicy := .zeroPad }

def mtermPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[2]
  , terms := #[ { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
                , factors := #[mtermReadA] }
              , { iterationShape := #[2, 3], contextPos := #[], outputPos := #[0], reductionPos := #[1]
                , factors := #[mtermReadB] } ]
  , algebra := admittedAlgebra }

def mtermStore : Array DenseTensor :=
  #[ { shape := [2], data := #[5.0, 6.0] }
   , { shape := [2, 3], data := #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0] }
   , { shape := [2], data := #[] } ]

-- Y[i] := A[i] + Σⱼ B[i,j]; Y[0] = 5 + (1+2+3) = 11; Y[1] = 6 + (4+5+6) = 21.
-- (If term1 wrongly contributed once per term2's 3 reduction coordinates, Y would be
-- [5*3+6, 6*3+15] = [21, 33] instead.)
#guard dataOf (runIt mtermSigs mtermPlan mtermStore) == some #[11.0, 21.0]

-- per-term contraction difference: Y[i] := u[]·a[i] + W[i,k]·v[k] — term1 has NO contracted axis
-- (a rank-0 scalar factor plus a rank-1 factor over the output axis alone), term2 contracts k.

def ptcSigs : Array TensorSignature :=
  #[ { shape := #[], dtype := .f64 }
   , { shape := #[2], dtype := .f64 }
   , { shape := #[2, 2], dtype := .f64 }
   , { shape := #[2], dtype := .f64 }
   , { shape := #[2], dtype := .f64 } ]

def ptcReadU : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[], bias := #[] }
  , sourceShape := #[], oobPolicy := .zeroPad }

def ptcReadA : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[2], oobPolicy := .zeroPad }

def ptcReadW : ReadPlan :=
  { sourceSlot := 2, map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[0, 0] }
  , sourceShape := #[2, 2], oobPolicy := .zeroPad }

def ptcReadV : ReadPlan :=
  { sourceSlot := 3, map := { coeffs := #[#[0, 1]], bias := #[0] }
  , sourceShape := #[2], oobPolicy := .zeroPad }

def ptcPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 4, outputShape := #[2]
  , terms := #[ { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
                , factors := #[ptcReadU, ptcReadA] }
              , { iterationShape := #[2, 2], contextPos := #[], outputPos := #[0], reductionPos := #[1]
                , factors := #[ptcReadW, ptcReadV] } ]
  , algebra := admittedAlgebra }

def ptcStore : Array DenseTensor :=
  #[ { shape := [], data := #[3.0] }
   , { shape := [2], data := #[1.0, 2.0] }
   , { shape := [2, 2], data := #[1.0, 2.0, 3.0, 4.0] }
   , { shape := [2], data := #[10.0, 20.0] }
   , { shape := [2], data := #[] } ]

-- Y[i] := u·a[i] + Σₖ W[i,k]·v[k]; u=3, a=[1,2], W=[[1,2],[3,4]], v=[10,20].
-- Y[0] = 3*1 + (1*10+2*20) = 3+50 = 53; Y[1] = 3*2 + (3*10+4*20) = 6+110 = 116.
#guard dataOf (runIt ptcSigs ptcPlan ptcStore) == some #[53.0, 116.0]

-- empty factor product: a term with factors := #[], expecting factorId (1.0) per output
-- coordinate.

def efpSigs : Array TensorSignature := #[ { shape := #[3], dtype := .f64 } ]

def efpPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 0, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[] }]
  , algebra := admittedAlgebra }

def efpStore : Array DenseTensor := #[ { shape := [3], data := #[] } ]

-- factors := #[]: the factor-product loop never runs, so prod stays at factorId = 1.0; the (sole,
-- empty) reduction coordinate folds that once into termAcc, so Y[i] = 1.0 for every i.
#guard dataOf (runIt efpSigs efpPlan efpStore) == some #[1.0, 1.0, 1.0]

-- empty term array: terms := #[], expecting reduceId (0.0) per output coordinate.

def etaSigs : Array TensorSignature := #[ { shape := #[2], dtype := .f64 } ]

def etaPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 0, outputShape := #[2], terms := #[]
  , algebra := admittedAlgebra }

def etaStore : Array DenseTensor := #[ { shape := [2], data := #[] } ]

-- terms := #[]: no term to fold, so Y[i] = reduceId = 0.0 for every i.
#guard dataOf (runIt etaSigs etaPlan etaStore) == some #[0.0, 0.0]

-- zero-extent reduction domain: a non-empty term whose reduction position has extent 0, expecting
-- reduceId — distinct from the empty-term-array case above because a real, checker-accepted term
-- with a factor is present here.

def zerdSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }, { shape := #[2], dtype := .f64 } ]

def zerdRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1, 0]], bias := #[0] }
  , sourceShape := #[2], oobPolicy := .zeroPad }

def zerdPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[2]
  , terms := #[{ iterationShape := #[2, 0], contextPos := #[], outputPos := #[0], reductionPos := #[1]
               , factors := #[zerdRead] }]
  , algebra := admittedAlgebra }

def zerdStore : Array DenseTensor :=
  #[ { shape := [2], data := #[7.0, 8.0] }, { shape := [2], data := #[] } ]

-- reductionPos names a basis position of extent 0, so its coordinate domain is empty: the
-- reduction fold never executes and the term contributes reduceId = 0.0 regardless of A's values.
#guard dataOf (runIt zerdSigs zerdPlan zerdStore) == some #[0.0, 0.0]

-- zero output extent: outputShape := #[0], expecting empty data.

def zoeSigs : Array TensorSignature :=
  #[ { shape := #[0], dtype := .f64 }, { shape := #[0], dtype := .f64 } ]

def zoeRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[0], oobPolicy := .zeroPad }

def zoePlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[0]
  , terms := #[{ iterationShape := #[0], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[zoeRead] }]
  , algebra := admittedAlgebra }

def zoeStore : Array DenseTensor :=
  #[ { shape := [0], data := #[] }, { shape := [0], data := #[] } ]

-- outputShape := #[0]: the output-coordinate enumeration is empty, so the outer loop body never
-- runs (regardless of the term's contents) and the resulting data is empty.
#guard dataOf (runIt zoeSigs zoePlan zoeStore) == some #[]

-- fold-order sensitivity: three term values chosen so binary64 addition is non-associative, pinning
-- that terms fold in array order.

def fosSigs : Array TensorSignature :=
  #[ { shape := #[], dtype := .f64 }
   , { shape := #[], dtype := .f64 }
   , { shape := #[], dtype := .f64 }
   , { shape := #[1], dtype := .f64 } ]

def fosRead (slot : TensorSlot) : ReadPlan :=
  { sourceSlot := slot, map := { coeffs := #[], bias := #[] }
  , sourceShape := #[], oobPolicy := .zeroPad }

def fosTerm (slot : TensorSlot) : TermPlan :=
  { iterationShape := #[1], contextPos := #[], outputPos := #[0], reductionPos := #[]
  , factors := #[fosRead slot] }

def fosPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[1]
  , terms := #[fosTerm 0, fosTerm 1, fosTerm 2]
  , algebra := admittedAlgebra }

def fosStore : Array DenseTensor :=
  #[ { shape := [], data := #[1e16] }, { shape := [], data := #[1.0] }
   , { shape := [], data := #[-1e16] }, { shape := [1], data := #[] } ]

-- Terms fold strictly in array order: ((0 + 1e16) + 1.0) + (-1e16). Hand prediction: 1e16 + 1.0
-- rounds (ties-to-even; 1e16's ULP at this magnitude is 2, and 1e16's mantissa is already even) back
-- down to 1e16 exactly, so the middle term has no visible effect on the running sum, and subtracting
-- 1e16 at the end lands on 0.0.
-- Run and confirmed: the result is 0.0, matching the hand prediction above. This rules out the
-- reassociation that groups the two ±1e16 terms together before adding the 1.0 term — that order
-- ((1e16 + -1e16) + 1.0) would yield 1.0, not 0.0 — so this fixture pins that `runDenseAssign` folds
-- terms strictly in `AssignPlan.terms` array order, not in some order that lets equal-magnitude
-- terms cancel first.
#guard dataOf (runIt fosSigs fosPlan fosStore) == some #[0.0]

/-!
## `PositionalInputError` cases
-/

def posErrOf (sigs : Array TensorSignature) (a : AssignPlan) (store : Array DenseTensor) :
    Option PositionalInputError :=
  match checkAssign sigs a with
  | .error _ => none
  | .ok c => match runDenseAssign c store with
             | .error e => some e
             | .ok _ => none

-- missing slot: store provides only slot 0 (A); contractPlan's second factor (readB) needs slot 1,
-- which does not exist in a store of size 1.
def missingSlotStore : Array DenseTensor :=
  #[ { shape := [4], data := #[10.0, 100.0, 1000.0, 10000.0] } ]

#guard posErrOf sigs contractPlan missingSlotStore == some (.missingSlot 1 1)

-- wrong runtime shape: slot 0 (A) has runtime shape [5], but the plan/signature declared [4].
-- readA is checked before readB, so this fires without needing slot 1 to be present at all.
def wrongShapeStore : Array DenseTensor :=
  #[ { shape := [5], data := #[10.0, 100.0, 1000.0, 10000.0, 1.0] } ]

#guard posErrOf sigs contractPlan wrongShapeStore == some (.shapeMismatch 0 #[4] [5])

-- malformed storage: slot 0 (A) declares shape [4] (matching the plan) but its data array holds
-- only 3 elements — shape agrees, storage size does not.
def badDataStore : Array DenseTensor :=
  #[ { shape := [4], data := #[10.0, 100.0, 1000.0] } ]

#guard posErrOf sigs contractPlan badDataStore == some (.storageMismatch 0 [4] 3)

/-!
## Context-sensitive fixtures (Step 3)
-/

def ctxSigs : Array TensorSignature := #[{ shape := #[2,3], dtype := .f64 }, { shape := #[3], dtype := .f64 }]

def ctxReadX : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1,0], #[0,1]], bias := #[0,0] }
  , sourceShape := #[2,3], oobPolicy := .zeroPad }

def ctxPlan : AssignPlan :=
  { contextShape := #[2], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[2,3], contextPos := #[0], outputPos := #[1], reductionPos := #[]
               , factors := #[ctxReadX] }]
  , algebra := admittedAlgebra }

run_cmd do
  match checkAssign ctxSigs ctxPlan with
  | .error e => throwError s!"checkAssign rejected context-sensitive plan: {repr e}"
  | .ok checked =>
      let x : DenseTensor := { shape := [2,3], data := #[1,2,3,4,5,6] }
      let zeros : DenseTensor := { shape := [3], data := #[0,0,0] }
      -- Verified: ctx=0 -> X's row 0 = [1,2,3].
      match runDenseAssignAt checked [0] #[x, zeros] with
      | .error e => throwError s!"ctx=0 failed: {repr e}"
      | .ok y0 => unless y0.data == #[1,2,3] do throwError s!"ctx=0 wrong: {repr y0.data}"
      -- Verified: ctx=1 -> X's row 1 = [4,5,6].
      match runDenseAssignAt checked [1] #[x, zeros] with
      | .error e => throwError s!"ctx=1 failed: {repr e}"
      | .ok y1 => unless y1.data == #[4,5,6] do throwError s!"ctx=1 wrong: {repr y1.data}"
      -- Verified: out-of-range context (contextShape is #[2]) is rejected, not padded, with the
      -- exact `contextShapeMismatch` payload.
      match runDenseAssignAt checked [5] #[x, zeros] with
      | .ok _ => throwError "out-of-range context should have been rejected"
      | .error e =>
          unless e == .contextShapeMismatch #[2] [5] do
            throwError s!"out-of-range context: wrong error {repr e}"
      -- Verified: wrong-rank context (2 components against a 1-D contextShape) is rejected, with
      -- the exact `contextShapeMismatch` payload.
      match runDenseAssignAt checked [0, 0] #[x, zeros] with
      | .ok _ => throwError "wrong-rank context should have been rejected"
      | .error e =>
          unless e == .contextShapeMismatch #[2] [0, 0] do
            throwError s!"wrong-rank context: wrong error {repr e}"

-- Context bound across a NON-trivial reduction: contextShape=#[2]; iterationShape=#[2,3,4]
-- (context, output, reduction); X shape [2,3,4] sequential 0..23 row-major.
-- Y[o] = sum_r X[ctx,o,r]. Verified via `lake env lean`: ctx=0 -> [6,22,38], ctx=1 -> [54,70,86].
def sigsCR : Array TensorSignature := #[{ shape := #[2,3,4], dtype := .f64 }, { shape := #[3], dtype := .f64 }]

def readCR : ReadPlan :=
  { sourceSlot := 0
  , map := { coeffs := #[#[1,0,0], #[0,1,0], #[0,0,1]], bias := #[0,0,0] }
  , sourceShape := #[2,3,4], oobPolicy := .zeroPad }

def crPlan : AssignPlan :=
  { contextShape := #[2], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[2,3,4], contextPos := #[0], outputPos := #[1], reductionPos := #[2]
               , factors := #[readCR] }]
  , algebra := admittedAlgebra }

run_cmd do
  match checkAssign sigsCR crPlan with
  | .error e => throwError s!"checkAssign rejected context+reduction plan: {repr e}"
  | .ok checked =>
      let xdata : Array Float := (Array.range 24).map (fun n => Float.ofNat n)
      let x : DenseTensor := { shape := [2,3,4], data := xdata }
      let zeros : DenseTensor := { shape := [3], data := #[0,0,0] }
      match runDenseAssignAt checked [0] #[x, zeros] with
      | .error e => throwError s!"ctx=0 failed: {repr e}"
      | .ok y0 => unless y0.data == #[6,22,38] do throwError s!"ctx=0 wrong: {repr y0.data}"
      match runDenseAssignAt checked [1] #[x, zeros] with
      | .error e => throwError s!"ctx=1 failed: {repr e}"
      | .ok y1 => unless y1.data == #[54,70,86] do throwError s!"ctx=1 wrong: {repr y1.data}"

/-!
## Fixtures shared with the JAX affine bridge

`experiments/jax_bridge/EvalPlanAffineSmoke.lean` renders these three checked kernels as bridge
fixtures. They live here, in a default Lake target, so an `Eval/Plan` field change breaks
`lake build` rather than only the untargeted bridge driver — which is how Wave F F1's
`contextPos`/`contextShape` addition silently broke every hand-built plan literal in that driver.
Each also carries its own Lean-side expectation, so the fixture is validated whether or not the
bridge runs.
-/

/-! ### Permuted iteration basis

Source signature `[2,3]`, destination `[2]`, with the *reduction* position before the output position
in the iteration basis (`iterationShape = #[3,2]`, `outputPos = #[1]`, `reductionPos = #[0]`). Source
compilation cannot emit output-before-reduction, so this is the only coverage of an interpreter that
must transpose rather than assume canonical order. -/

def permutedSigs : Array TensorSignature :=
  #[ { shape := #[2, 3], dtype := .f64 }, { shape := #[2], dtype := .f64 } ]

def permutedRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[0, 1], #[1, 0]], bias := #[0, 0] }
  , sourceShape := #[2, 3], oobPolicy := .zeroPad }

def permutedPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[2]
  , terms := #[{ iterationShape := #[3, 2], contextPos := #[], outputPos := #[1], reductionPos := #[0]
               , factors := #[permutedRead] }]
  , algebra := admittedAlgebra }

def permutedStore : Array DenseTensor :=
  #[ { shape := [2, 3], data := #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0] }, { shape := [2], data := #[] } ]

-- `Y[o] = Σ_r src[o, r]`: rows [1,2,3] and [4,5,6] sum to 6 and 15. Hand-computed.
#guard (match checkAssign permutedSigs permutedPlan with
        | .error _ => none
        | .ok c => (runDenseAssign c permutedStore).toOption.map DenseTensor.data)
  == some #[6.0, 15.0]

/-! ### Float-sensitive factor order

Three scalar factors whose product differs by one output ULP between declared order `[a,b,c]` and
rotation `[b,c,a]`, without overflow or subnormals. This pins that the factor fold is left-associated
in *stored* order: an interpreter free to reassociate would make both plans agree. -/

def factorOrderSigs : Array TensorSignature :=
  #[ { shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 }
   , { shape := #[], dtype := .f64 }, { shape := #[1], dtype := .f64 } ]

def factorOrderPlanFor (slots : Array TensorSlot) : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[1]
  , terms := #[{ iterationShape := #[1], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := slots.map fosRead }]
  , algebra := admittedAlgebra }

def factorOrderPlan : AssignPlan := factorOrderPlanFor #[0, 1, 2]
def factorOrderReorderedPlan : AssignPlan := factorOrderPlanFor #[1, 2, 0]

def factorOrderStore : Array DenseTensor :=
  #[ { shape := [], data := #[Float.ofBits 0x4b81df8e849782c0] }
   , { shape := [], data := #[Float.ofBits 0x3e8249ed35cbdd0e] }
   , { shape := [], data := #[Float.ofBits 0x48869ebf3614d3eb] }
   , { shape := [1], data := #[] } ]

private def factorOrderBits (a : AssignPlan) : Option UInt64 :=
  match checkAssign factorOrderSigs a with
  | .error _ => none
  | .ok c => ((runDenseAssign c factorOrderStore).toOption.bind
      (fun t => t.data[0]?)).map Float.toBits

-- The two orders differ, and differ by exactly one ULP. Previously these bits were pinned only on
-- the Python side of the bridge; the ordering claim is a Dense claim and belongs here too.
#guard factorOrderBits factorOrderPlan == some 0x52ace21080787dc7
#guard factorOrderBits factorOrderReorderedPlan == some 0x52ace21080787dc6

/-! ### Nonempty output reading empty source storage

The source extent is zero, so every lookup is invalid, but the output extent is two. This is the only
fixture that reaches an interpreter's empty-storage guard: zero-output and zero-reduction cases short
circuit before any gather, whereas this one must produce two zeros from an empty array. -/

def emptySourceSigs : Array TensorSignature :=
  #[ { shape := #[0], dtype := .f64 }, { shape := #[2], dtype := .f64 } ]

def emptySourceRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[0]], bias := #[0] }
  , sourceShape := #[0], oobPolicy := .zeroPad }

def emptySourcePlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[2]
  , terms := #[{ iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[emptySourceRead] }]
  , algebra := admittedAlgebra }

def emptySourceStore : Array DenseTensor :=
  #[ { shape := [0], data := #[] }, { shape := [2], data := #[] } ]

-- Every read is out of bounds against a zero extent, so zero padding gives [0, 0]. Hand-computed.
#guard (match checkAssign emptySourceSigs emptySourcePlan with
        | .error _ => none
        | .ok c => (runDenseAssign c emptySourceStore).toOption.map DenseTensor.data)
  == some #[0.0, 0.0]

/-! ## Scaling probe: one mid-sized contraction

`Y[i] := Σⱼ W[i,j]·x[j]`, `i,j` both ranging over 64 — the same shape as `ptcReadW`/`ptcReadV`'s
2×2 matrix-vector contraction, scaled to a 4,096-coordinate iteration domain (`64 · 64`) instead of
4. This is `papers/jax_evalplan_architecture.md` §7.6 row 2's scaling measurement: the affine-table
lowering renders one safe index and one validity bit per coordinate of the *full* iteration domain,
contracted axis included, so this is the first fixture in the suite big enough to measure that growth
rather than reason about it from code inspection alone. `W` and `x` are all-ones so the expected
output is the trivially hand-computed constant `64.0` at every position, not a value read back from
this interpreter. -/

def scalingProbeSigs : Array TensorSignature :=
  #[ { shape := #[64, 64], dtype := .f64 }
   , { shape := #[64], dtype := .f64 }
   , { shape := #[64], dtype := .f64 } ]

def scalingProbeReadW : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[0, 0] }
  , sourceShape := #[64, 64], oobPolicy := .zeroPad }

def scalingProbeReadX : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[0, 1]], bias := #[0] }
  , sourceShape := #[64], oobPolicy := .zeroPad }

def scalingProbePlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[64]
  , terms := #[{ iterationShape := #[64, 64], contextPos := #[], outputPos := #[0], reductionPos := #[1]
               , factors := #[scalingProbeReadW, scalingProbeReadX] }]
  , algebra := admittedAlgebra }

def scalingProbeStore : Array DenseTensor :=
  #[ { shape := [64, 64], data := (Array.range (64 * 64)).map (fun _ => (1.0 : Float)) }
   , { shape := [64], data := (Array.range 64).map (fun _ => (1.0 : Float)) }
   , { shape := [64], data := #[] } ]

-- Y[i] := Σⱼ W[i,j]·x[j] with W, x all-ones: Y[i] = 64 (one 1.0 per reduction coordinate) for
-- every i. Hand-computed from the constant, not read back from the interpreter.
#guard (match checkAssign scalingProbeSigs scalingProbePlan with
        | .error _ => none
        | .ok c => (runDenseAssign c scalingProbeStore).toOption.map DenseTensor.data)
  == some ((Array.range 64).map (fun _ => (64.0 : Float)))

end LeanNCD.Eval.Plan.KernelDenseTest
