import LeanNCD.Eval.Entry
import LeanNCD.DSL.Compile
import EvalPlanCodegen
import Eval.Plan.KernelDenseTest

/-!
# Wave C affine JAX reference smoke — driver (`docs/superpowers/plans/2026-08-10-jax-full-affine-semantics.md`, Task 2)

Emits static affine plan DATA for the curated Task 2 evidence matrix and the Dense-executed
expected results, for the committed generic runtime (`evalplan_affine_runtime.py`) to interpret and
the verifier (`evalplan_affine_smoke.py`) to compare bit-for-bit. Three boundary entry points, all
from `EvalPlanCodegen` (`JaxBridge`):

* **named `PreparedPlan`** — the nine verified source fixtures (compiled through the real
  `compileToScheduled → prepareEvalPlan → runPreparedDense` pipeline);
* **positional `CheckedAssignPlan`** — the six reused `KernelDenseTest` checked-kernel fixtures plus
  a permuted-iteration-basis case, a three-factor Float-sensitive order pair, and a nonempty output
  reading empty source storage through all-false masks;
* **positional `CheckedEvalPlan`** — a real three-node graph with noncontiguous input slots.

Nothing here computes an affine address: all lookup tables are precomputed in Lean by
`renderAffine*`. Kept out of the default build; run ad hoc via `lake env lean --run`.
-/

namespace JaxBridge.AffineSmoke

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std
open JaxBridge

/-! ## Nine verified source fixtures (named `PreparedPlan` boundary) -/

def shiftProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i + 1]
}
def shiftInputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", ⟨[3], #[1.0, 2.0, 3.0]⟩)]

def scaleProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[2 * i]
}
def scaleInputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", ⟨[3], #[1.0, 2.0, 3.0]⟩)]

def lookbackProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i - 1]
}
def lookbackInputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", ⟨[3], #[1.0, 2.0, 3.0]⟩)]

def multiAxisProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  Y[i, j] := X[2 * i + j]
}
def multiAxisInputs : HashMap String DenseTensor :=
  HashMap.ofList [("X", ⟨[4], #[1.0, 2.0, 3.0, 4.0]⟩)]

def termScopeProg : TLProgram := tlprog!{
  axis i : ℕ = 1
  axis j : ℕ = 2
  Y[i] := A[i] + P[i, j]
}
def termScopeInputs : HashMap String DenseTensor :=
  HashMap.ofList
    [ ("A", ⟨[1], #[10.0]⟩)
    , ("P", ⟨[1, 2], #[1.0, 2.0]⟩) ]

def zeroCoeffRowProg : TLProgram := tlprog!{
  axis i : ℕ = 1
  axis j : ℕ = 3
  Y[i] := A[i] · B[0 * j]
}
def zeroCoeffRowInputs : HashMap String DenseTensor :=
  HashMap.ofList
    [ ("A", ⟨[1], #[2.0]⟩)
    , ("B", ⟨[1], #[5.0]⟩) ]

def reductionOrderProg : TLProgram := tlprog!{
  axis i : ℕ = 1
  axis j : ℕ = 3
  Y[i] := P[i, j]
}
def reductionOrderInputs : HashMap String DenseTensor :=
  HashMap.ofList [("P", ⟨[1, 3], #[1e16, 1.0, 1.0]⟩)]

def zeroOutputProg : TLProgram := tlprog!{
  axis i : ℕ = 0
  Y[i] := A[i]
}
def zeroOutputInputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", ⟨[0], #[]⟩)]

def zeroReductionProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 0
  Y[i] := A[i] · B[j]
}
def zeroReductionInputs : HashMap String DenseTensor :=
  HashMap.ofList
    [ ("A", ⟨[2], #[7.0, 8.0]⟩)
    , ("B", ⟨[0], #[]⟩) ]

/-! ## Local permuted-iteration-basis fixture (positional `CheckedAssignPlan` boundary)

Source signature `[2,3]`, destination `[2]`; `iterationShape = #[3,2]`, `outputPos = #[1]`,
`reductionPos = #[0]`; source-map rows `#[0,1]`/`#[1,0]`; verified `runDenseAssign` output `#[6,15]`
(`Y[o] = Σ_r src[o, r]`, output before reduction is impossible from source compilation, so this
exercises the runtime transpose). -/

def permutedSigs : Array TensorSignature :=
  #[ ⟨#[2, 3], .f64⟩, ⟨#[2], .f64⟩ ]

def permutedRead : ReadPlan :=
  ⟨0, ⟨#[#[0, 1], #[1, 0]], #[0, 0]⟩, #[2, 3], .zeroPad⟩

def permutedPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[2]
  , terms := #[{ iterationShape := #[3, 2], contextPos := #[], outputPos := #[1], reductionPos := #[0]
               , factors := #[permutedRead] }]
  , algebra := admittedAlgebra }

def permutedStore : Array DenseTensor :=
  #[ ⟨[2, 3], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]⟩, ⟨[2], #[]⟩ ]

/-! ## Float-sensitive factor order

The exact input bit patterns below were selected so `[a,b,c]` and `[b,c,a]` differ by one output
ULP without using overflow or subnormals. Both plans are Dense-run below; Python pins their observed
bits under eager and JIT rather than relying on a real-number argument. -/

def factorOrderSigs : Array TensorSignature :=
  #[ ⟨#[], .f64⟩, ⟨#[], .f64⟩, ⟨#[], .f64⟩, ⟨#[1], .f64⟩ ]

def scalarRead (slot : TensorSlot) : ReadPlan :=
  ⟨slot, ⟨#[], #[]⟩, #[], .zeroPad⟩

def factorOrderPlanFor (slots : Array TensorSlot) : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[1]
  , terms := #[{ iterationShape := #[1], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := slots.map scalarRead }]
  , algebra := admittedAlgebra }

def factorOrderPlan : AssignPlan := factorOrderPlanFor #[0, 1, 2]
def factorOrderReorderedPlan : AssignPlan := factorOrderPlanFor #[1, 2, 0]

def factorOrderStore : Array DenseTensor :=
  #[ ⟨[], #[Float.ofBits 0x4b81df8e849782c0]⟩
   , ⟨[], #[Float.ofBits 0x3e8249ed35cbdd0e]⟩
   , ⟨[], #[Float.ofBits 0x48869ebf3614d3eb]⟩
   , ⟨[1], #[]⟩ ]

/-! ## Empty source with a nonempty output

Every lookup is invalid because the source extent is zero, but the output extent is two. This
reaches the runtime's empty-storage guard (unlike zero-output/reduction short circuits), and removal
of that guard attempts index-zero gather from empty storage. -/

def emptySourceSigs : Array TensorSignature :=
  #[ ⟨#[0], .f64⟩, ⟨#[2], .f64⟩ ]

def emptySourceRead : ReadPlan :=
  ⟨0, ⟨#[#[0]], #[0]⟩, #[0], .zeroPad⟩

def emptySourcePlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[2]
  , terms := #[{ iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[emptySourceRead] }]
  , algebra := admittedAlgebra }

def emptySourceStore : Array DenseTensor :=
  #[ ⟨[0], #[]⟩, ⟨[2], #[]⟩ ]

/-! ## Multi-node positional graph

Inputs are supplied in `inputSlots = #[0,4]` order. The first node copies slot 4 to slot 1, the
second can only read that freshly-produced slot, and the third adds slot 2 to slot 0. The expected
full store distinguishes placement (`slot 4`, not slot 1), node order, and final arithmetic. -/

def positionalSigs : Array TensorSignature :=
  Array.replicate 5 ⟨#[2], .f64⟩

def positionalRead (slot : TensorSlot) : ReadPlan :=
  ⟨slot, ⟨#[#[1]], #[0]⟩, #[2], .zeroPad⟩

def positionalCopy (dest source : TensorSlot) : AssignPlan :=
  { contextShape := #[], destinationSlot := dest, outputShape := #[2]
  , terms := #[{ iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[positionalRead source] }]
  , algebra := admittedAlgebra }

def positionalSum : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[2]
  , terms := #[ { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
                , factors := #[positionalRead 2] }
              , { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
                , factors := #[positionalRead 0] } ]
  , algebra := admittedAlgebra }

def positionalRaw : RawEvalPlan :=
  ⟨admittedVersion, positionalSigs, #[0, 4],
    #[positionalCopy 1 4, positionalCopy 2 1, positionalSum], .reference64⟩

def positionalInputs : Array DenseTensor :=
  #[ ⟨[2], #[2.0, 3.0]⟩, ⟨[2], #[5.0, 7.0]⟩ ]

/-! ## Assembly helpers -/

/-- Compile + prepare + Dense-run one source fixture, failing loud with a diagnosable message. -/
def prepareNamed (name : String) (prog : TLProgram) (inputs : HashMap String DenseTensor) :
    IO (PreparedPlan × EvalReport) := do
  let sched ← match prog.compileToScheduled.run 0 with
    | .ok s _ => pure s
    | .error e _ => throw (IO.userError s!"{name} compile failed: {repr e}")
  let prepared ← match prepareEvalPlan sched (InputSignature.ofDenseInputs inputs) with
    | .ok p => pure p
    | .error f => throw (IO.userError s!"{name} prepare failed: {renderCompileCause f.cause}")
  let report ← match runPreparedDense prepared inputs with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{name} Dense run failed: {repr e.cause}")
  pure (prepared, report)

/-- A `{name: tensorEntry, ...}` dict over `requiredInputs`, resolving each concrete tensor. -/
def renderInputsDict (prepared : PreparedPlan) (inputs : HashMap String DenseTensor) :
    IO String := do
  let mut parts : Array String := #[]
  for b in prepared.bindings.requiredInputs do
    let t ← match inputs[b.name]? with
      | some t => pure t
      | none => throw (IO.userError s!"missing fixture input {b.name}")
    parts := parts.push (pyStrLit b.name ++ ": " ++ pyTensorEntry t)
  pure ("{" ++ String.intercalate ", " parts.toList ++ "}")

/-- A `{name: tensorEntry, ...}` dict over `materializedNames`, resolving each Dense output. -/
def renderExpectedDict (prepared : PreparedPlan) (report : EvalReport) : IO String := do
  let mut parts : Array String := #[]
  for b in prepared.bindings.materializedNames do
    let t ← match report.env[b.name]? with
      | some t => pure t
      | none => throw (IO.userError s!"materialized name {b.name} absent from Dense env")
    parts := parts.push (pyStrLit b.name ++ ": " ++ pyTensorEntry t)
  pure ("{" ++ String.intercalate ", " parts.toList ++ "}")

def buildNamedFixture (name : String) (prog : TLProgram) (inputs : HashMap String DenseTensor) :
    IO String := do
  let (prepared, report) ← prepareNamed name prog inputs
  let inputsDict ← renderInputsDict prepared inputs
  let expectedDict ← renderExpectedDict prepared report
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"named\", \"plan\": " ++
    renderAffinePlanNamed prepared ++ ", \"inputs\": " ++ inputsDict ++
    ", \"expected\": " ++ expectedDict ++ "}")

def buildAssignFixture (name : String) (sigs : Array TensorSignature) (a : AssignPlan)
    (store : Array DenseTensor) : IO String := do
  let checked ← match checkAssign sigs a with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"{name} check failed: {repr e}")
  let expected ← match runDenseAssign checked store with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"{name} Dense run failed: {repr e}")
  let storeEntries := String.intercalate ", " (store.toList.map pyTensorEntry)
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"assign\", \"assign\": " ++
    renderAffineAssign checked ++ ", \"store\": [" ++ storeEntries ++ "], \"expected\": " ++
    pyTensorEntry expected ++ "}")

def buildPositionalFixture (name : String) (raw : RawEvalPlan) (inputs : Array DenseTensor) :
    IO String := do
  let checked ← match checkPlan raw with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"{name} graph check failed: {repr e}")
  let expected ← match runDensePlan checked inputs with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name} Dense graph run failed: {repr e}")
  let inputEntries := String.intercalate ", " (inputs.toList.map pyTensorEntry)
  let expectedEntries := String.intercalate ", " (expected.toList.map pyTensorEntry)
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"positional\", \"plan\": " ++
    renderAffinePlanPositional checked ++ ", \"inputs\": [" ++ inputEntries ++
    "], \"expected_store\": [" ++ expectedEntries ++ "]}")

end JaxBridge.AffineSmoke

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std
open JaxBridge JaxBridge.AffineSmoke

def main (args : List String) : IO Unit := do
  let outputPath := args.head?.getD "generated_evalplan_affine_smoke.py"
  let namedFixtures ← #[
      ("shift", shiftProg, shiftInputs),
      ("scale", scaleProg, scaleInputs),
      ("lookback", lookbackProg, lookbackInputs),
      ("multiAxis", multiAxisProg, multiAxisInputs),
      ("termScope", termScopeProg, termScopeInputs),
      ("zeroCoeffRow", zeroCoeffRowProg, zeroCoeffRowInputs),
      ("reductionOrder", reductionOrderProg, reductionOrderInputs),
      ("zeroOutput", zeroOutputProg, zeroOutputInputs),
      ("zeroReduction", zeroReductionProg, zeroReductionInputs)
    ].mapM (fun (nm, p, i) => buildNamedFixture nm p i)
  -- Reused public `KernelDenseTest` checked-kernel fixtures + the local permuted-basis fixture.
  let assignFixtures ← #[
      buildAssignFixture "ptc" KernelDenseTest.ptcSigs KernelDenseTest.ptcPlan KernelDenseTest.ptcStore,
      buildAssignFixture "efp" KernelDenseTest.efpSigs KernelDenseTest.efpPlan KernelDenseTest.efpStore,
      buildAssignFixture "eta" KernelDenseTest.etaSigs KernelDenseTest.etaPlan KernelDenseTest.etaStore,
      buildAssignFixture "zerd" KernelDenseTest.zerdSigs KernelDenseTest.zerdPlan KernelDenseTest.zerdStore,
      buildAssignFixture "zoe" KernelDenseTest.zoeSigs KernelDenseTest.zoePlan KernelDenseTest.zoeStore,
      buildAssignFixture "fos" KernelDenseTest.fosSigs KernelDenseTest.fosPlan KernelDenseTest.fosStore,
      buildAssignFixture "permuted" permutedSigs permutedPlan permutedStore,
      buildAssignFixture "factorOrder" factorOrderSigs factorOrderPlan factorOrderStore,
      buildAssignFixture "factorOrderReordered" factorOrderSigs factorOrderReorderedPlan factorOrderStore,
      buildAssignFixture "emptySourceGuard" emptySourceSigs emptySourcePlan emptySourceStore
    ].mapM id
  let positionalFixture ← buildPositionalFixture "positionalGraph" positionalRaw positionalInputs
  let allFixtures := namedFixtures ++ assignFixtures ++ #[positionalFixture]
  let moduleSrc :=
    "# Generated by EvalPlanAffineSmoke.lean — do not edit.\n" ++
    "FIXTURES = [\n" ++ String.intercalate ",\n" allFixtures.toList ++ "\n]\n"
  IO.FS.writeFile outputPath moduleSrc
  IO.println s!"Generated {outputPath} with {allFixtures.size} fixtures"
