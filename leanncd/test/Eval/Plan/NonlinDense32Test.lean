import LeanNCD.Eval.Plan.Dense32
import Eval.Plan.NonlinDenseTest     -- every plan here is one of its plans, retagged `f32`
import Eval.Plan.KernelDense32Test   -- `t32`
import Eval.Plan.EvalPlan32Test      -- `runGraph32`/`bitsAt`, for the graph fixtures 3.7 and 3.8

/-!
# Native binary32 nonlinearity workers (F32-B Task 3)

Fixtures 3.5-3.9 of F32-B Task 3: the binary32 workers `runDensePointwise32`/`runDenseAxiswise32`
directly, and through `checkPlan`/`runDensePlan32`. Every plan is a `NonlinDenseTest` plan with
ONLY the signature dtypes, the assignment algebra, the function (3.7), and the buffers changed.

Same discipline as `KernelDense32Test`: every expectation is an exact binary32 BIT PATTERN compared
through `Float32.toBits`, buffers are built from bits, and the two discriminators (3.7, 3.8) each
also assert the binary64-then-narrow contrast, so the fixture fails if its lanes ever stop
separating native binary32 from a widened computation.
-/

namespace LeanNCD.Eval.Plan.NonlinDense32Test
open LeanNCD.Eval LeanNCD.Eval.Plan
open LeanNCD.Eval.Plan.NonlinDenseTest
  (oneNodeSigs axiswiseSigs oneNodeSigs32 axiswiseSigs32 probePointwise probeAxiswise
   probeAxiswiseMasked idNode idNode22)
open LeanNCD.Eval.Plan.KernelDense32Test (t32)
open LeanNCD.Eval.Plan.EvalPlan32Test (runGraph32 bitsAt)

/-!
## Fixture 3.5: the binary32 workers refuse binary64 evidence FIRST

`NonlinDenseTest`'s probes through the BINARY64 checkers on their own (binary64) tables, handed to
the binary32 workers. With an EMPTY store the answer must be `storageKindMismatch .float32
.float64`, not `missingSlot 0 0`: the guard's ORDER, not only its presence. A well-formed binary32
store gives the same answer.
-/

def pw32ErrWith (checked : Except NonlinPlanError CheckedPointwisePlan)
    (store : Array DenseTensor32) : Option PositionalInputError :=
  match checked with
  | .error _ => none
  | .ok c => match runDensePointwise32 c store with
             | .error e => some e
             | .ok _ => none

def ax32ErrWith (checked : Except NonlinPlanError CheckedAxiswisePlan)
    (store : Array DenseTensor32) : Option PositionalInputError :=
  match checked with
  | .error _ => none
  | .ok c => match runDenseAxiswise32 c store with
             | .error e => some e
             | .ok _ => none

#guard pw32ErrWith (checkPointwise oneNodeSigs probePointwise) #[]
  == some (.storageKindMismatch .float32 .float64)
#guard pw32ErrWith (checkPointwise oneNodeSigs probePointwise)
    #[ t32 [2] #[3212836864, 1073741824] ]
  == some (.storageKindMismatch .float32 .float64)

#guard ax32ErrWith (checkAxiswise axiswiseSigs probeAxiswise) #[]
  == some (.storageKindMismatch .float32 .float64)
#guard ax32ErrWith (checkAxiswise axiswiseSigs probeAxiswise)
    #[ t32 [2,2] #[1065353216, 1077936128, 1073741824, 1073741824] ]
  == some (.storageKindMismatch .float32 .float64)

/-!
## Fixture 3.6: the binary32 workers re-validate their source slot

`NonlinDenseTest.pwErrOf`/`axErrOf`'s missing, shape, storage, and well-formed cases, over
`DenseTensor32` stores and BINARY32 evidence. Same payloads as the binary64 originals. The
well-formed pointwise case also checks the value: block 6's native sigmoid lanes.
-/

def pw32ErrOf (store : Array DenseTensor32) : Option PositionalInputError :=
  pw32ErrWith (checkPointwiseF32 oneNodeSigs32 probePointwise) store

def ax32ErrOf (store : Array DenseTensor32) : Option PositionalInputError :=
  ax32ErrWith (checkAxiswiseF32 axiswiseSigs32 probeAxiswise) store

#guard pw32ErrOf #[] == some (.missingSlot 0 0)
#guard pw32ErrOf #[ t32 [3] #[1065353216, 1073741824, 1077936128] ]
  == some (.shapeMismatch 0 #[2] [3])
#guard pw32ErrOf #[ t32 [2] #[1065353216] ] == some (.storageMismatch 0 [2] 1)
#guard pw32ErrOf #[ t32 [2] #[3212836864, 1073741824] ] == none

#guard ax32ErrOf #[] == some (.missingSlot 0 0)
#guard ax32ErrOf #[ t32 [2,3] #[1065353216, 1073741824, 1077936128, 1082130432, 1084227584,
                               1086324736] ]
  == some (.shapeMismatch 0 #[2,2] [2,3])
#guard ax32ErrOf #[ t32 [2,2] #[1065353216, 1073741824, 1077936128] ]
  == some (.storageMismatch 0 [2,2] 3)
#guard ax32ErrOf #[ t32 [2,2] #[1065353216, 1077936128, 1073741824, 1073741824] ] == none

/-- Block 6: `sigmoid` over the three lanes `0.7f`, bits `1058161516`, and `-1.25`, natively. -/
def sigs32 : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f32 }, { shape := #[3], dtype := .f32 } ]
def sigmoid3 : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[3], fn := .sigmoid }

#guard match checkPointwiseF32 sigs32 sigmoid3 with
  | .ok c => (runDensePointwise32 c
      #[t32 [3] #[1060320051, 1058161516, 3214934016]]).toOption.map
        (·.data.map Float32.toBits) == some #[1059786330, 1059297860, 1046743937]
  | .error _ => false

/-!
## Fixture 3.7: graph pointwise discriminator

`NonlinDenseTest.pointwisePlan` (`Y := X; Z := f(Y)`) with its signatures `f32`, `idNode` given the
binary32 algebra, and `fn := .sigmoid`, run through `checkPlan`/`runDensePlan32`. With
`X = [0.7f, bits 1058161516]` the native binary32 sigmoid is `[1059786330, 1059297860]`, while the
binary64 sigmoid of the same (widened) inputs, narrowed, is `[1059786331, 1059297859]` — each lane
one ulp away, in opposite directions.
-/

def pointwisePlan32 : RawEvalPlan :=
  { tensorSigs := oneNodeSigs32, inputSlots := #[0]
  , steps := #[.assign { idNode 1 0 with algebra := admittedAlgebraF32 }
              , .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[2], fn := .sigmoid }]
  }

def pointwiseX : Array UInt32 := #[1060320051, 1058161516]

#guard bitsAt (runGraph32 pointwisePlan32 #[t32 [2] pointwiseX]) 2
  == some #[1059786330, 1059297860]

-- The contrast the fixture discriminates against: binary64 sigmoid, then narrow.
#guard (PointwiseFn.sigmoid.apply ⟨[2], pointwiseX.map (Float32.ofBits · |>.toFloat)⟩).data.map
    (·.toFloat32.toBits) == #[1059786331, 1059297859]

/-!
## Fixture 3.8: graph axiswise discriminator

`NonlinDenseTest.axiswisePlan` (`Y := X; Z := normalize(Y, axis 1)`, `#[2, 2]`) retagged, with
`X = [[2²⁴, 1], [1, 1]]`. Natively, row 0's sum `2²⁴ + 1` rounds to `2²⁴`, so it normalizes to
exactly `[1, 2⁻²⁴]`; in binary64 the sum is exact and both quotients narrow one ulp low. Row 1 is
`[0.5, 0.5]` either way. The reduction is along the NON-leading axis, so this also pins binary32
row grouping there.
-/

def axiswisePlan32 : RawEvalPlan :=
  { tensorSigs := axiswiseSigs32, inputSlots := #[0]
  , steps := #[.assign { idNode22 1 0 with algebra := admittedAlgebraF32 }
              , .axiswise { sourceSlot := 1, destinationSlot := 2, shape := #[2,2]
                          , axisPos := 1, fn := .normalize }]
  }

def axiswiseX : Array UInt32 := #[1266679808, 1065353216, 1065353216, 1065353216]

#guard bitsAt (runGraph32 axiswisePlan32 #[t32 [2,2] axiswiseX]) 2
  == some #[1065353216, 864026624, 1056964608, 1056964608]

-- The contrast: binary64 normalize over the widened inputs, then narrow.
#guard (AxiswiseFn.normalize.applyCore 1 (fun _ => true)
    ⟨[2,2], axiswiseX.map (Float32.ofBits · |>.toFloat)⟩).data.map (·.toFloat32.toBits)
  == #[1065353215, 864026623, 1056964608, 1056964608]

/-!
## Fixture 3.9: masked axiswise

`NonlinDenseTest.probeAxiswiseMasked` (normalize along axis 1, `maskExcludeCol0`) through the
BINARY32 checker and worker, over `[[1, 3], [2, 2]]`. Each row's single survivor normalizes to `1`
and the excluded column to `0`: `[0, 1, 0, 1]`.
-/

#guard match checkAxiswiseF32 axiswiseSigs32 probeAxiswiseMasked with
  | .ok c => (runDenseAxiswise32 c
      #[t32 [2,2] #[1065353216, 1077936128, 1073741824, 1073741824]]).toOption.map
        (·.data.map Float32.toBits) == some #[0, 1065353216, 0, 1065353216]
  | .error _ => false

end LeanNCD.Eval.Plan.NonlinDense32Test
