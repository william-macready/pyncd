import LeanNCD.Eval.Plan.Dense32
import Eval.Plan.KernelDense32Test   -- fixture 2's plans, reused as this file's graph twin

/-!
# Native binary32 graph execution (f32 slice, Task 3)

Fixtures 11 and 14 of Task 3, plus fixture 2's graph twin (see below). Same discipline as
`KernelDense32Test`: exact `Float32.toBits` patterns, buffers built from bits, and a binary64
contrast wherever the claim is about rounding rather than about wiring.
-/

namespace LeanNCD.Eval.Plan.EvalPlan32Test
open LeanNCD.Eval LeanNCD.Eval.Plan
open LeanNCD.Eval.Plan.KernelDense32Test (t32)

def runGraph32 (raw : RawEvalPlan) (inputs : Array DenseTensor32) :
    Except String (Array DenseTensor32) :=
  match checkPlan raw with
  | .error e => .error s!"check failed: {repr e}"
  | .ok c => match runDensePlan32 c inputs with
             | .error e => .error s!"run failed: {repr e}"
             | .ok store => .ok store

def bitsAt (store : Except String (Array DenseTensor32)) (slot : TensorSlot) :
    Option (Array UInt32) :=
  match store with
  | .error _ => none
  | .ok s => (s[slot]?).map (fun t => t.data.map Float32.toBits)

/-! ## Fixture 11: the rounded intermediate is what the next step reads

`GraphDenseTest.chainPlan`'s two-step chain, over scalars and binary32: slot 2 materializes
`P := X · X` with `X = 4097`, then slot 3 computes `Y := P + K` with `K = -16785408`.

`4097 · 4097` is the exact integer `16785409`, which is NOT a binary32 value; the binary32 product
is `16785408`. So the native answer is `Y = 16785408 + (-16785408) = +0`.

This is the fixture that separates native per-operation binary32 from a whole-graph binary64
execution that narrows only at the end: that implementation stores the exact `16785409` in slot 2
and returns `Y = 1` (bits `1065353216`). `KernelDense32Test`'s fixture 3 pins the product alone,
which a single narrowing also gets right — it is the CONSUMPTION of the rounded intermediate here
that discriminates. -/

def chainSigs32 : Array TensorSignature :=
  #[ { shape := #[], dtype := .f32 }    -- 0 = X (input)
   , { shape := #[], dtype := .f32 }    -- 1 = K (input)
   , { shape := #[], dtype := .f32 }    -- 2 = P
   , { shape := #[], dtype := .f32 } ]  -- 3 = Y

/-- A scalar read of `slot`: no iteration basis, so no coefficient rows and no bias. -/
def scalarRead (slot : TensorSlot) : ReadPlan :=
  { sourceSlot := slot, map := { coeffs := #[], bias := #[] }
  , sourceShape := #[], oobPolicy := .zeroPad }

def scalarTerm (slot : TensorSlot) : TermPlan :=
  { iterationShape := #[], contextPos := #[], outputPos := #[], reductionPos := #[]
  , factors := #[.read (scalarRead slot)] }

/-- `P := X · X` — one term, two factors, so the binary32 MULTIPLY is what rounds. -/
def productNode : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[]
  , terms := #[{ iterationShape := #[], contextPos := #[], outputPos := #[], reductionPos := #[]
               , factors := #[.read (scalarRead 0), .read (scalarRead 0)] }]
  , algebra := admittedAlgebraF32 }

/-- `Y := P + K` — two terms, so the binary32 ADD across terms is what consumes slot 2's value. -/
def sumNode : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[]
  , terms := #[scalarTerm 2, scalarTerm 1]
  , algebra := admittedAlgebraF32 }

def f32ProductChain : RawEvalPlan :=
  { tensorSigs := chainSigs32, inputSlots := #[0, 1]
  , steps := #[.assign productNode, .assign sumNode] }

/-- Inputs ordered by `inputSlots = #[0, 1]`: `X = 4097`, then `K = -16785408`. -/
def productChainInputs : Array DenseTensor32 :=
  #[ t32 [] #[1166018560], t32 [] #[3414167552] ]

-- Slot 2 holds the ROUNDED binary32 product `16785408`, not the exact integer `16785409`.
#guard bitsAt (runGraph32 f32ProductChain productChainInputs) 2 == some #[1266683904]

-- ... and slot 3, which reads slot 2, is therefore exactly `+0`.
#guard bitsAt (runGraph32 f32ProductChain productChainInputs) 3 == some #[0]

-- Input placement is checked too: both input slots hold what was supplied, in `inputSlots` order.
#guard bitsAt (runGraph32 f32ProductChain productChainInputs) 0 == some #[1166018560]
#guard bitsAt (runGraph32 f32ProductChain productChainInputs) 1 == some #[3414167552]

/-! ### Fixture 2's graph twin

`KernelDense32Test`'s fixture 2 (`[16777216, 1, -16777216]` reduced left to right from the `+0`
seed) wrapped in a one-node graph. It exists so the single "widen the worker to binary64 and narrow
only materialized results" mutation can be observed against BOTH of the plan's stated fixtures: a
per-assignment widening is invisible to fixture 11 (each node materializes, so the narrowing lands
in the same place), and a whole-graph widening is invisible to the local fixture 2 — only running
fixture 2's own reduction THROUGH the graph worker closes that gap. The numeric claim itself is
fixture 2's and is not restated: this asserts the same bits through `runDensePlan32`. -/

def reductionGraphSigs32 : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f32 }, { shape := #[], dtype := .f32 } ]

def f32ReductionGraph : RawEvalPlan :=
  { tensorSigs := reductionGraphSigs32, inputSlots := #[0]
  , steps := #[.assign KernelDense32Test.f32ReductionRounding] }

def reductionGraphInputs : Array DenseTensor32 :=
  #[ t32 [3] #[1266679808, 1065353216, 3414163456] ]

#guard bitsAt (runGraph32 f32ReductionGraph reductionGraphInputs) 1 == some #[0]

/-! ## Fixture 14: the binary32 graph worker's storage-kind door

Fixture 11's chain retagged BINARY64, handed straight to the binary32 graph worker with the WRONG
INPUT ARITY (its `inputSlots` has two entries; zero inputs are supplied). The required answer is
`storageKindMismatch .float32 .float64`, i.e. the storage guard fires before `runDensePlan32`'s
arity check and therefore before any input is read, allocated, or shape-checked.

Like fixture 13, this pins ORDER, not presence: the controls below show each of the three causes the
guard must beat. -/

def chainSigs64 : Array TensorSignature :=
  #[ { shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 }
   , { shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 } ]

/-- Fixture 11's chain with binary64 signatures and the binary64 algebra — the same wiring, the
    other carrier. -/
def f64ProductChain : RawEvalPlan :=
  { tensorSigs := chainSigs64, inputSlots := #[0, 1]
  , steps := #[ .assign { productNode with algebra := admittedAlgebra }
              , .assign { sumNode with algebra := admittedAlgebra } ] }

def planErr32 (raw : RawEvalPlan) (inputs : Array DenseTensor32) : Option PositionalInputError :=
  match checkPlan raw with
  | .error _ => none
  | .ok c => match runDensePlan32 c inputs with
             | .error e => some e
             | .ok _ => none

#guard planErr32 f64ProductChain #[] == some (.storageKindMismatch .float32 .float64)

-- Control: the binary32 chain with the same wrong arity reaches the pre-existing arity check.
#guard planErr32 f32ProductChain #[] == some (.arityMismatch 2 0)

-- Control: a wrong runtime SHAPE on the binary32 chain is reported per input slot, so the guard
-- above beat a check that is genuinely live on this plan.
#guard planErr32 f32ProductChain #[ t32 [1] #[1166018560], t32 [] #[3414167552] ]
  == some (.shapeMismatch 0 #[] [1])

-- Control: malformed storage (shape agrees, buffer length does not) is likewise reported.
#guard planErr32 f32ProductChain #[ t32 [] #[], t32 [] #[3414167552] ]
  == some (.storageMismatch 0 [] 0)

end LeanNCD.Eval.Plan.EvalPlan32Test
