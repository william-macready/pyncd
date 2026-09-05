import LeanNCD.Eval.Plan.Adapter
import LeanNCD.DSL.Compile
import EvalPlanCodegen

/-!
# Wave C JAX evaluator smoke test — einsum driver (`docs/superpowers/plans/2026-08-10-jax-evalplan-smoke.md`)

The executable driver for the completed `einsumOnly` smoke. All reusable code generation now lives
in `EvalPlanCodegen.lean` (`JaxBridge` namespace, plan 2026-08-10-jax-full-affine-semantics Task 2);
this file keeps only fixture selection, Dense execution, generated-module assembly, and the
adversarial rejection check. Behavior is unchanged: it still compiles the affine-bias fixture
through `prepareEvalPlan`, emits a real `jnp.einsum` module, and confirms the shifted fixture is
rejected with `nonzeroAffineBias` before any Python is written for it.

Kept out of the default build: registered only in the non-default `JaxExperiment` `lean_lib`, no
`LeanNCD` public API touched, no JAX dependency added anywhere in this project's own toolchain.
-/

namespace LeanNCD.Eval.Plan.JaxSmoke

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

def affineProg : TLProgram := tlprog!{
  Y[i] := W[i, j] · x[j] + b[i]
}

def affineInputs : HashMap String DenseTensor :=
  HashMap.ofList
    [ ("W", ⟨[2, 1], #[2.0, 3.0]⟩)
    , ("x", ⟨[1], #[5.0]⟩)
    , ("b", ⟨[2], #[1.0, 1.0]⟩) ]

def shiftedProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i + 1]
}

end LeanNCD.Eval.Plan.JaxSmoke

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.Eval.Plan.JaxSmoke Std
open JaxBridge

def main (args : List String) : IO Unit := do
  let outputPath := args.head?.getD "generated_evalplan_smoke.py"
  -- Compile + prepare the affine fixture.
  let sched ← match affineProg.compileToScheduled.run 0 with
    | .ok sched _ => pure sched
    | .error e _  => throw (IO.userError s!"affineProg compile failed: {repr e}")
  let prepared ← match prepareEvalPlan sched (InputSignature.ofDenseInputs affineInputs) with
    | .ok p => pure p
    | .error f => throw (IO.userError s!"affineProg prepare failed: {renderCompileCause f.cause}")
  -- Run Dense and require the known-good result.
  let report ← match runPreparedDense prepared affineInputs with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"affineProg Dense run failed: {repr e.cause}")
  let yTensor ← match report.env["Y"]? with
    | some t => pure t
    | none => throw (IO.userError "affineProg Dense run produced no 'Y' tensor")
  unless yTensor.shape == [2] && yTensor.data == #[11.0, 16.0] do
    throw (IO.userError s!"affineProg Dense Y mismatch: shape={yTensor.shape} data={yTensor.data}")
  -- Generate the Python module from the checked, prepared plan only (einsumOnly mode).
  let forwardSrc ← match generateNamed .einsumOnly prepared with
    | .ok src => pure src
    | .error e => throw (IO.userError s!"affineProg codegen failed: {repr e}")
  let inputConsts ← match
      renderInputConstants prepared affineInputs with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"input-constant rendering failed: {repr e}")
  let outputConsts := renderExpectedOutputConstants "Y" yTensor
  let moduleSrc := String.intercalate "\n\n"
    ["import jax.numpy as jnp", inputConsts, outputConsts, forwardSrc]
  IO.FS.writeFile outputPath (moduleSrc ++ "\n")
  IO.println s!"Generated {outputPath}"
  -- Confirm the shifted-affine fixture is rejected by codegen BEFORE any Python is emitted for it.
  let shiftedSched ← match shiftedProg.compileToScheduled.run 0 with
    | .ok sched _ => pure sched
    | .error e _  => throw (IO.userError s!"shiftedProg compile failed: {repr e}")
  let shiftedInputs : HashMap String DenseTensor := HashMap.ofList [("A", ⟨[3], #[1.0, 2.0, 3.0]⟩)]
  let shiftedPrepared ← match prepareEvalPlan shiftedSched (InputSignature.ofDenseInputs shiftedInputs) with
    | .ok p => pure p
    | .error f =>
        throw (IO.userError s!"shiftedProg prepare failed: {renderCompileCause f.cause}")
  match generateNamed .einsumOnly shiftedPrepared with
  | .ok _ => throw (IO.userError "shiftedProg codegen unexpectedly succeeded: expected a nonzeroAffineBias rejection")
  | .error (.nonzeroAffineBias ni ti fi ri biasVal) =>
      IO.println
        s!"shiftedProg correctly rejected: nonzeroAffineBias node={ni} term={ti} factor={fi} \
row={ri} bias={biasVal}"
  | .error other =>
      throw (IO.userError s!"shiftedProg codegen failed with the wrong error: {repr other}")
