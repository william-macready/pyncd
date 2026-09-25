import LeanNCD.Eval.Plan.Dense
import Eval.Plan.ScatterDenseTest
import Eval.Plan.KernelDense32Test

/-!
# F32-D Task 1: the native binary32 scatter checker and worker

Every plan here is a `ScatterDenseTest` plan with its dtypes, algebra, and `fill` moved to binary32
(donor named per fixture). Values are exact `Float32.toBits` patterns; binary64 contrasts run the
same plan through the Float checker/worker.
-/

namespace LeanNCD.Eval.Plan.ScatterDense32Test
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan
open LeanNCD.Eval.Plan.KernelDense32Test (t32)

def run32 (sigs : Array TensorSignature) (s : ScatterPlan) (store : Array DenseTensor32) :
    Except String DenseTensor32 :=
  match checkScatterF32 sigs s with
  | .error e => .error s!"check failed: {repr e}"
  | .ok c => match runDenseScatter32 c store with
             | .error e => .error s!"run failed: {repr e}"
             | .ok d => .ok d

def shapeBitsOf : Except String DenseTensor32 → Option (List Nat × Array UInt32)
  | .ok d => some (d.shape, d.data.map Float32.toBits)
  | .error _ => none

def errOf32 (sigs : Array TensorSignature) (s : ScatterPlan) (store : Array DenseTensor32) :
    Option PositionalInputError :=
  match checkScatterF32 sigs s with
  | .error _ => none
  | .ok c => match runDenseScatter32 c store with
             | .error e => some e
             | .ok _ => none

def checkErrOf : Except PlanError CheckedScatterPlan → Option PlanError
  | .ok _ => none | .error e => some e

def kindOf : Except PlanError CheckedScatterPlan → Option StorageKind
  | .ok c => some c.storageKind | .error _ => none

/-- `ScatterDenseTest.sigsFor` retagged `f32`. -/
def sigsFor32 (destShape : Array Nat) : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f32 }, { shape := destShape, dtype := .f32 } ]

/-- `ScatterDenseTest.srcCompute` (`:= X[i]`, `i : 3`) under a binary32 algebra. -/
def srcCompute32 (alg : ContractionAlgebra) : AssignPlan :=
  { ScatterDenseTest.srcCompute with algebra := alg }

/-- `ScatterDenseTest.placed #[6] #[#[2]] #[0]` (`Out[2*i] := X[i]`) under `alg`, fill coherent. -/
def upScatter32 (alg : ContractionAlgebra) : ScatterPlan :=
  { ScatterDenseTest.placed #[6] #[#[2]] #[0] with compute := srcCompute32 alg, fill := alg.reduceId }

/-- `X = [1, 2, 3]` as binary32 bits. -/
def store32 : Array DenseTensor32 :=
  #[ t32 [3] #[0x3f800000, 0x40000000, 0x40400000], t32 [6] #[] ]

/-! ## Fixture 1.1 — `Out[2*i] := X[i]` natively (donor: `ScatterDenseTest` fixture 1) -/
#guard shapeBitsOf (run32 (sigsFor32 #[6]) (upScatter32 admittedAlgebraF32) store32)
  == some ([6], #[1065353216, 0, 1073741824, 0, 1077936128, 0])

/-! ## Fixture 1.2 — evidence records the carrier it was checked for -/
#guard kindOf (checkScatterF32 (sigsFor32 #[6]) (upScatter32 admittedAlgebraF32))
  == some StorageKind.float32
#guard kindOf (checkScatter (ScatterDenseTest.sigsFor #[6]) (ScatterDenseTest.placed #[6] #[#[2]] #[0]))
  == some StorageKind.float64
-- The binary32 checker refuses a binary64 table at the destination, through the shared core.
#guard checkErrOf (checkScatterF32 (ScatterDenseTest.sigsFor #[6]) (ScatterDenseTest.placed #[6] #[#[2]] #[0]))
  == some (.dtypeNotAdmitted 1 .f64)

/-! ## Fixture 1.3 — the fill clause runs under binary32: a binary64 `+0` fill is refused -/
#guard checkErrOf (checkScatterF32 (sigsFor32 #[6])
    { upScatter32 admittedAlgebraF32 with fill := admittedAlgebra.reduceId })
  == some (.scatterFillNotIdentity (.f64 0) (.f32 0))
-- ... and so does the collision-policy clause: only `.rejectCollisions` is admitted, per carrier.
#guard checkErrOf (checkScatterF32 (sigsFor32 #[6]) { upScatter32 admittedAlgebraF32 with reduce := .sum })
  == some (.scatterReduceNotAdmitted .sum)

/-! ## Fixture 1.4 — native rounding in the compute half, with an inline unary factor

`Out[2*i] := sqrt(X[i]) + Y[i] + Z[i]`: three terms, each `ScatterDenseTest.srcRead` with its slot
changed, the first carrying `unary := some .sqrt`. Lane 0 is `X = 2^48, Y = 1, Z = -2^24`:
`sqrt = 2^24`, then `2^24 + 1` rounds back to `2^24` in binary32 and `Z` cancels it (`+0`); in
binary64 the lane is `1`, which narrows to `0x3f800000`. Lanes 1-2 (`sqrt 4 + 1 + 0.5 = 3.5`,
`sqrt 9 + 1 + 0.25 = 4.25`) are exact in both. -/
def sumRead (slot : TensorSlot) (u : Option UnaryOp := none) : ReadPlan :=
  { ScatterDenseTest.srcRead with sourceSlot := slot, unary := u }

def sumTerm (r : ReadPlan) : TermPlan :=
  { ScatterDenseTest.srcCompute.terms[0]! with factors := #[.read r] }

def sumCompute (alg : ContractionAlgebra) : AssignPlan :=
  { ScatterDenseTest.srcCompute with
    destinationSlot := 3
    terms := #[sumTerm (sumRead 0 (some .sqrt)), sumTerm (sumRead 1), sumTerm (sumRead 2)]
    algebra := alg }

def sumScatter (alg : ContractionAlgebra) : ScatterPlan :=
  { upScatter32 alg with compute := sumCompute alg }

def sumSigs (d : ScalarDType) : Array TensorSignature :=
  #[ { shape := #[3], dtype := d }, { shape := #[3], dtype := d }, { shape := #[3], dtype := d }
   , { shape := #[6], dtype := d } ]

-- X = [2^48, 4, 9], Y = [1, 1, 1], Z = [-2^24, 0.5, 0.25]
def sumStore32 : Array DenseTensor32 :=
  #[ t32 [3] #[1468006400, 1082130432, 1091567616], t32 [3] #[1065353216, 1065353216, 1065353216]
   , t32 [3] #[3414163456, 1056964608, 1048576000], t32 [6] #[] ]

#guard shapeBitsOf (run32 (sumSigs .f32) (sumScatter admittedAlgebraF32) sumStore32)
  == some ([6], #[0, 0, 1080033280, 0, 1082654720, 0])

-- The binary64 contrast: the same plan and values through `checkScatter`/`runDenseScatter`.
def sumStore64 : Array DenseTensor :=
  sumStore32.map (fun t => { shape := t.shape, data := t.data.map Float32.toFloat })

#guard (match checkScatter (sumSigs .f64) (sumScatter admittedAlgebra) with
  | .error _ => none
  | .ok c => (runDenseScatter c sumStore64).toOption.map (·.data.map Float.toBits))
  == some #[4607182418800017408, 0, 4615063718147915776, 0, 4616471093031469056, 0]
-- ... whose lane 0, narrowed once, is binary32 `1`, not the native `+0` above.
#guard (Float.ofBits 4607182418800017408).toFloat32.toBits == 1065353216

/-! ## Fixture 1.5 — `fill` is decoded by the binary32 carrier: max-product's `-∞`
(donor: `ScatterDenseTest.maxScatter`) -/
#guard shapeBitsOf (run32 (sigsFor32 #[6]) (upScatter32 admittedAlgebraF32Max) store32)
  == some ([6], #[1065353216, 4286578688, 1073741824, 4286578688, 1077936128, 4286578688])

/-! ## Fixture 1.6 — a binary32 collision names both sources
(donor: `ScatterDenseTest.collisionScatter`, algebra and dtypes moved to binary32) -/
def collisionSigs32 : Array TensorSignature :=
  ScatterDenseTest.collisionSigs.map (fun s => { s with dtype := .f32 })

def collisionScatter32 : ScatterPlan :=
  { ScatterDenseTest.collisionScatter with
    compute := { ScatterDenseTest.collisionCompute with algebra := admittedAlgebraF32 }
    fill := admittedAlgebraF32.reduceId }

#guard errOf32 collisionSigs32 collisionScatter32
    #[ t32 [3] #[0x3f800000, 0x40000000, 0x40400000], t32 [2] #[0x41200000, 0x42c80000], t32 [3] #[] ]
  == some (.scatterCollision [0] [0, 0] [0, 1])

/-! ## Fixture 1.7 — both doors check storage kind FIRST

A compute half with `contextShape := #[1]` (`checkScatter` does not check it; `checkPlan` does), run
with an EMPTY store: it violates the worker's context check AND its store check. Wrong-carrier
evidence must report `storageKindMismatch`; the right carrier reports `contextShapeMismatch`, which
proves the plan really does violate the checks the guard must precede. -/
def ctxCompute (alg : ContractionAlgebra) : AssignPlan :=
  { srcCompute32 alg with
    contextShape := #[1]
    terms := #[{ ScatterDenseTest.srcCompute.terms[0]! with
      iterationShape := #[1, 3], contextPos := #[0], outputPos := #[1]
      factors := #[.read { ScatterDenseTest.srcRead with
        map := { ScatterDenseTest.srcRead.map with coeffs := #[#[0, 1]] } }] }] }

def ctxChecked32 : Option CheckedScatterPlan :=
  (checkScatterF32 (sigsFor32 #[6]) { upScatter32 admittedAlgebraF32 with compute := ctxCompute admittedAlgebraF32 }).toOption

def ctxChecked64 : Option CheckedScatterPlan :=
  (checkScatter (ScatterDenseTest.sigsFor #[6])
    { ScatterDenseTest.placed #[6] #[#[2]] #[0] with compute := ctxCompute admittedAlgebra }).toOption

#guard (ctxChecked32.map (fun c => match runDenseScatter c #[] with
  | .error e => some e | .ok _ => none)) == some (some (.storageKindMismatch .float64 .float32))
#guard (ctxChecked32.map (fun c => match runDenseScatter32 c #[] with
  | .error e => some e | .ok _ => none)) == some (some (.contextShapeMismatch #[1] []))
#guard (ctxChecked64.map (fun c => match runDenseScatter32 c #[] with
  | .error e => some e | .ok _ => none)) == some (some (.storageKindMismatch .float32 .float64))
#guard (ctxChecked64.map (fun c => match runDenseScatter c #[] with
  | .error e => some e | .ok _ => none)) == some (some (.contextShapeMismatch #[1] []))

end LeanNCD.Eval.Plan.ScatterDense32Test
