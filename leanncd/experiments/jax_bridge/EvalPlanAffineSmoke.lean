import LeanNCD.Eval.Entry
import LeanNCD.DSL.Compile
import EvalPlanCodegen
import Eval.Plan.KernelDenseTest
import Eval.Plan.GraphDenseTest

/-!
# Wave C affine JAX reference smoke — driver (`docs/superpowers/plans/2026-08-10-jax-full-affine-semantics.md`, Task 2)

Emits static affine plan DATA for the curated Task 2 evidence matrix and the Dense-executed
expected results, for the committed generic runtime (`evalplan_affine_runtime.py`) to interpret and
the verifier (`evalplan_affine_smoke.py`) to compare bit-for-bit. Three boundary entry points, all
from `EvalPlanCodegen` (`JaxBridge`):

* **named `PreparedPlan`** — the nine verified source fixtures (compiled through the real
  `compileToScheduled → prepareEvalPlan → runPreparedDense` pipeline);
* **positional `CheckedAssignPlan`** — ten `KernelDenseTest` checked-kernel fixtures, including a
  permuted-iteration-basis case, a three-factor Float-sensitive order pair, and a nonempty output
  reading empty source storage through all-false masks;
* **positional `CheckedEvalPlan`** — `GraphDenseTest.placementPlan`, a three-node graph with
  noncontiguous input slots.

Nothing here computes an affine address: all lookup tables are precomputed in Lean by
`renderAffine*`. Nothing here declares a plan either — every fixture is imported from `Tests`, which
an ordinary `lake build` typechecks, so an `Eval/Plan` field change cannot break this driver
invisibly. This file itself is still kept out of the default build; run ad hoc via
`lake env lean --run`.
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

/-! ## Checked-plan fixtures

Every hand-built plan this driver renders now lives in the `Tests` library — `KernelDenseTest` for the
checked kernels, `GraphDenseTest` for the positional graph — where an ordinary `lake build` typechecks
it and a Lean-side expectation pins its Dense result. Nothing plan-shaped is declared in this file, so
an `Eval/Plan` field change can no longer break the bridge without also breaking the build. -/

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
private def renderInputsDict (prepared : PreparedPlan) (inputs : HashMap String DenseTensor) :
    IO String := do
  let mut parts : Array String := #[]
  for b in prepared.bindings.requiredInputs.bindings do
    let t ← match inputs[b.name]? with
      | some t => pure t
      | none => throw (IO.userError s!"missing fixture input {b.name}")
    parts := parts.push (pyStrLit b.name ++ ": " ++ pyTensorEntry t)
  pure ("{" ++ String.intercalate ", " parts.toList ++ "}")

/-- A `{name: tensorEntry, ...}` dict over `materializedNames`, resolving each Dense output. -/
private def renderExpectedDict (prepared : PreparedPlan) (report : EvalReport) : IO String := do
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
  -- `renderAffinePlanNamed` is `Except JaxCodegenError String` (it rejects the semantics this
  -- backend implements no lowering for — Boolean dtypes, tropical algebras, unary factors,
  -- contextful assignments, non-assignment steps). Unwrap it and fail loud with the fixture and
  -- mode that produced it; never append the `Except` itself to the emitted Python.
  let planData ← match renderAffinePlanNamed prepared with
    | .ok s => pure s
    | .error e =>
        throw (IO.userError
          s!"{name} affineReference render failed at the named PreparedPlan boundary: {repr e}")
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"named\", \"plan\": " ++
    planData ++ ", \"inputs\": " ++ inputsDict ++
    ", \"expected\": " ++ expectedDict ++ "}")

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
  let planData ← match renderAffinePlanPositional checked with
    | .ok s => pure s
    | .error e =>
        throw (IO.userError
          s!"{name} affineReference render failed at the positional CheckedEvalPlan \
boundary: {repr e}")
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"positional\", \"plan\": " ++
    planData ++ ", \"inputs\": [" ++ inputEntries ++
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
  -- All reused from the `Tests` library; nothing plan-shaped is declared in this driver.
  let assignFixtures ← #[
      buildAssignFixture "ptc" KernelDenseTest.ptcSigs KernelDenseTest.ptcPlan KernelDenseTest.ptcStore,
      buildAssignFixture "efp" KernelDenseTest.efpSigs KernelDenseTest.efpPlan KernelDenseTest.efpStore,
      buildAssignFixture "eta" KernelDenseTest.etaSigs KernelDenseTest.etaPlan KernelDenseTest.etaStore,
      buildAssignFixture "zerd" KernelDenseTest.zerdSigs KernelDenseTest.zerdPlan KernelDenseTest.zerdStore,
      buildAssignFixture "zoe" KernelDenseTest.zoeSigs KernelDenseTest.zoePlan KernelDenseTest.zoeStore,
      buildAssignFixture "fos" KernelDenseTest.fosSigs KernelDenseTest.fosPlan KernelDenseTest.fosStore,
      buildAssignFixture "permuted"
        KernelDenseTest.permutedSigs KernelDenseTest.permutedPlan KernelDenseTest.permutedStore,
      buildAssignFixture "factorOrder"
        KernelDenseTest.factorOrderSigs KernelDenseTest.factorOrderPlan KernelDenseTest.factorOrderStore,
      buildAssignFixture "factorOrderReordered"
        KernelDenseTest.factorOrderSigs KernelDenseTest.factorOrderReorderedPlan
        KernelDenseTest.factorOrderStore,
      buildAssignFixture "emptySourceGuard"
        KernelDenseTest.emptySourceSigs KernelDenseTest.emptySourcePlan KernelDenseTest.emptySourceStore
    ].mapM id
  let positionalFixture ← buildPositionalFixture "positionalGraph"
    GraphDenseTest.placementPlan GraphDenseTest.placementInputs
  let allFixtures := namedFixtures ++ assignFixtures ++ #[positionalFixture]
  let moduleSrc :=
    "# Generated by EvalPlanAffineSmoke.lean — do not edit.\n" ++
    "FIXTURES = [\n" ++ String.intercalate ",\n" allFixtures.toList ++ "\n]\n"
  IO.FS.writeFile outputPath moduleSrc
  IO.println s!"Generated {outputPath} with {allFixtures.size} fixtures"
