import Eval.Plan.ScanTest
import Eval.PropertyOracle.ScanUnroll
import LeanNCD.Eval.Plan.Adapter32

/-!
# F32-C prototype: native binary32 scans (plan level, graph level, source level) and an
# independent binary32 scan oracle (the S-B unrolling run through the CHECKED binary32 path).

PROTOTYPE — authored by the F32-C explore/prototype dispatch; values below were observed, not derived.
-/

namespace LeanNCD.Eval.Plan.ScanDense32Test
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std
open LeanNCD.Eval.Plan.ScanTest (outerSigs outerSigsF32 linearScan linearScanF32 baseBlock stepBlock stepBlockF32)
open LeanNCD.PropertyOracle (unrollScanNode reconstructHistory Unrolled)

def causeTag : PlanCompileCause → String
  | .inputSignature e => s!"inputSignature {repr e}"
  | .capability e => s!"capability {repr e}"
  | .shape _ => "shape"
  | .scan e => s!"scan {repr e}"
  | .invalidPlan e => s!"invalidPlan {repr e}"
  | .bindings e => s!"bindings {repr e}"
  | .nonlin e => s!"nonlin {repr e}"
  | .sourceInvariant e => s!"sourceInvariant {repr e}"

def bits32 (r : Except PositionalInputError (Array DenseTensor32)) (slot : Nat) : Option (List UInt32) :=
  match r with
  | .ok st => some ((st.getD slot default).data.toList.map Float32.toBits)
  | .error _ => none
def bits64 (r : Except PositionalInputError (Array DenseTensor)) (slot : Nat) : Option (List UInt64) :=
  match r with
  | .ok st => some ((st.getD slot default).data.toList.map Float.toBits)
  | .error _ => none
def err32 (r : Except PositionalInputError (Array DenseTensor32)) : Option PositionalInputError :=
  match r with | .error e => some e | .ok _ => none
def err64 (r : Except PositionalInputError (Array DenseTensor)) : Option PositionalInputError :=
  match r with | .error e => some e | .ok _ => none

/-! ## Part A — plan level. Donor: `ScanTest.linearScan` / `ScanTest.linearScanF32` (f32 fixture 10).
`S[0] := S0`, `S[l+1] := S[l] + X[l]`, `S0 = 2^24`, `X = [1,1,1]`: binary32 absorbs every `+1`
(`2^24 + 1` rounds to even, `2^24`), binary64 does not. -/

def store32 : Array DenseTensor32 :=
  #[⟨[], #[16777216.0]⟩, ⟨[3], #[1.0, 1.0, 1.0]⟩, ⟨[3], #[0.0, 0.0, 0.0]⟩]
def store64 : Array DenseTensor :=
  #[⟨[], #[16777216.0]⟩, ⟨[3], #[1.0, 1.0, 1.0]⟩, ⟨[3], #[0.0, 0.0, 0.0]⟩]

def c32 : Option CheckedScanPlan := (checkScanPlanF32 outerSigsF32 linearScanF32).toOption
def c64 : Option CheckedScanPlan := (checkScanPlan outerSigs linearScan).toOption

-- A1: accepted, stamped `.float32`, native bits
#guard c32.map (·.storageKind) == some LeanNCD.StorageKind.float32
#guard (c32.bind fun c => bits32 (runDenseScan32 outerSigsF32 c store32) 2)
  == some [0x4B800000, 0x4B800000, 0x4B800000]
-- A2: binary64 contrast — the same plan in binary64 keeps every `+1`
#guard c64.map (·.storageKind) == some LeanNCD.StorageKind.float64
#guard (c64.bind fun c => bits64 (runDenseScan outerSigs c store64) 2)
  == some [0x4170000000000000, 0x4170000010000000, 0x4170000020000000]
-- A3: guard first at both scan doors (the last two also violate the signature tie and store arity,
-- so a guard placed after the tie would report `signatureContextMismatch` instead)
#guard (c32.bind fun c => err64 (runDenseScan outerSigsF32 c store64))
  == some (.storageKindMismatch .float64 .float32)
#guard (c64.bind fun c => err32 (runDenseScan32 outerSigs c store32))
  == some (.storageKindMismatch .float32 .float64)
#guard (c64.bind fun c => err32 (runDenseScan32 outerSigsF32 c #[]))
  == some (.storageKindMismatch .float32 .float64)
#guard (c32.bind fun c => err64 (runDenseScan outerSigs c #[]))
  == some (.storageKindMismatch .float64 .float32)
-- A4: the binary32 checker refuses binary64 evidence at the state and at a block
#guard (match checkScanPlanF32 outerSigs linearScan with | .error e => some e | .ok _ => none)
  == some (.stateDtypeNotAdmitted 0 2 .f64)
#guard (match checkScanPlanF32 outerSigsF32 { linearScanF32 with baseBlock := baseBlock } with
        | .error e => some e | .ok _ => none)
  == some (.baseBlockError (.storageKindNotAdmitted .float64))
-- A5: block level
def b32 : Option CheckedPlanBlock := (checkPlanBlockF32 stepBlockF32).toOption
def b64 : Option CheckedPlanBlock := (checkPlanBlock stepBlock).toOption
#guard b32.map (·.storageKind) == some LeanNCD.StorageKind.float32
#guard b64.map (·.storageKind) == some LeanNCD.StorageKind.float64
#guard (b32.bind fun b => err64 (runDenseBlock b [0] #[])) == some (.storageKindMismatch .float64 .float32)
#guard (b64.bind fun b => err32 (runDenseBlock32 b [0] #[])) == some (.storageKindMismatch .float32 .float64)
#guard (match checkPlanBlockF32 stepBlock with | .error e => some e | .ok _ => none)
  == some (.storageKindNotAdmitted .float64)
-- A6: an all-`bool` block constrains no carrier and is admitted under `.float32`
def boolOnlyBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[], dtype := .bool }]
  , inputs := #[0], steps := #[], outputs := #[0] }
#guard ((checkPlanBlockF32 boolOnlyBlock).toOption.map (·.storageKind)) == some LeanNCD.StorageKind.float32
#guard ((checkPlanBlock boolOnlyBlock).toOption.map (·.storageKind)) == some LeanNCD.StorageKind.float64

end LeanNCD.Eval.Plan.ScanDense32Test
