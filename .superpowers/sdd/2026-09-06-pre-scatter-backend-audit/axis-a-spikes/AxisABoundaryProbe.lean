import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter
import LeanNCD.Eval.Plan.Executable

/-!
# Axis A construction spikes (pre-Scatter backend audit, 2026-09-06)

FINDINGS-ONLY scratch. Not in `lakefile.toml`, not a test module. Run with:

    cd leanncd && "$HOME/.elan/bin/lake" env lean spikes/AxisABoundaryProbe.lean

Every block PRINTS what actually happened (`IO.println` / `Lean.logInfo`) rather than asserting, so the
audit records observed behavior verbatim instead of a pass/fail bit.
-/

namespace AxisAProbe
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

private def expect (t : Option DenseTensor) : String :=
  match t with
  | some d => s!"shape={d.shape} data={d.data}"
  | none => "<absent>"

-- ─────────────────────────────────────────────────────────────────────────────
-- Fixture 1: asymmetric contraction. `A` retained on `i`, `B` contracted over `j`,
-- so swapping which VALUES land in which SLOT is observable.
--   correct : W = A · ΣB = [10,100] · 3 = [30, 300]
--   swapped : W = B · ΣA = [1,2] · 110 = [110, 220]
-- ─────────────────────────────────────────────────────────────────────────────

private def swapProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  W[i] := A[i] · B[j]
}

private def swapInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[10.0, 100.0]⟩).insert "B" ⟨[2], #[1.0, 2.0]⟩

-- SPIKE 1 — name↔slot swap inside `requiredInputs` (Adapter `packChecked`).
run_cmd do
  match swapProg.compileToScheduled.run 0 with
  | .error e _ => Lean.logInfo s!"S1 compile failed: {repr e}"
  | .ok sched _ =>
    match prepareEvalPlan sched (InputSignature.ofDenseInputs swapInputs) with
    | .error _ => Lean.logInfo "S1 prepare failed"
    | .ok prepared =>
      Lean.logInfo s!"S1 producer bindings   : {repr prepared.bindings.requiredInputs.bindings}"
      Lean.logInfo s!"S1 raw.inputSlots      : {repr prepared.plan.raw.inputSlots}"
      -- Swap only the NAMES; slots are the same multiset, names still Nodup.
      match checkBindings prepared.plan.raw.inputSlots
              #[{ name := "B", slot := 0 }, { name := "A", slot := 1 }] with
      | .error e => Lean.logInfo s!"S1 checkBindings REJECTED the name swap: {repr e}"
      | .ok swappedRB =>
        Lean.logInfo "S1 checkBindings ACCEPTED the name swap"
        let bad : PreparedPlan :=
          { prepared with bindings := { prepared.bindings with requiredInputs := swappedRB } }
        Lean.logInfo s!"S1 checkPreparedBindings on swapped plan: \
{repr (checkPreparedBindings bad |>.toOption.isSome)}"
        Lean.logInfo s!"S1 preparedBindingsTied on swapped plan: {repr (preparedBindingsTied bad)}"
        match runPreparedDense bad swapInputs with
        | .error f => Lean.logInfo s!"S1 runPreparedDense REJECTED: {repr f.cause}"
        | .ok report => Lean.logInfo s!"S1 runPreparedDense .ok  W = {expect report.env["W"]?}  \
(correct is shape=[2] data=#[30.000000, 300.000000])"
        match runPreparedDense prepared swapInputs with
        | .error _ => Lean.logInfo "S1 baseline failed"
        | .ok report => Lean.logInfo s!"S1 baseline (unswapped)  W = {expect report.env["W"]?}"

-- SPIKE 2 — `packChecked`'s `| none => .missingEnvBinding` arm: is a `PreparedPlan` pairing a
-- validly-checked `RequiredBindings` against a DIFFERENT `raw.inputSlots` reachable past
-- `checkPreparedBindings`?
private def oneInputProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  V[i] := A[i]
}

run_cmd do
  match swapProg.compileToScheduled.run 0, oneInputProg.compileToScheduled.run 0 with
  | .ok schedTwo _, .ok schedOne _ =>
    match prepareEvalPlan schedTwo (InputSignature.ofDenseInputs swapInputs),
          prepareEvalPlan schedOne (InputSignature.ofDenseInputs swapInputs) with
    | .ok two, .ok one =>
      let mismatched : PreparedPlan :=
        { two with bindings := { two.bindings with requiredInputs := one.bindings.requiredInputs } }
      Lean.logInfo s!"S2 donor(one-input) requiredInputs: {repr one.bindings.requiredInputs.bindings}"
      Lean.logInfo s!"S2 host(two-input) raw.inputSlots : {repr two.plan.raw.inputSlots}"
      match pack mismatched swapInputs with
      | .ok packed => Lean.logInfo s!"S2 pack .ok (!!) size={packed.size}"
      | .error e => Lean.logInfo s!"S2 pack rejected with: {repr e}"
    | _, _ => Lean.logInfo "S2 prepare failed"
  | _, _ => Lean.logInfo "S2 compile failed"

-- SPIKE 3 — `materializedNames` NAME is unauthenticated: rename the output to an INPUT's name.
run_cmd do
  match swapProg.compileToScheduled.run 0 with
  | .ok sched _ =>
    match prepareEvalPlan sched (InputSignature.ofDenseInputs swapInputs) with
    | .ok prepared =>
      Lean.logInfo s!"S3 producer materializedNames: {repr prepared.bindings.materializedNames}"
      let outSlot := (prepared.bindings.materializedNames[0]!).slot
      let renamed : PreparedPlan :=
        { prepared with bindings := { prepared.bindings with
            materializedNames := #[{ name := "A", slot := outSlot }] } }
      Lean.logInfo s!"S3 checkPreparedBindings on renamed: \
{repr (checkPreparedBindings renamed |>.toOption.isSome)}"
      match runPreparedDense renamed swapInputs with
      | .error f => Lean.logInfo s!"S3 runPreparedDense REJECTED: {repr f.cause}"
      | .ok report =>
          Lean.logInfo s!"S3 .ok  A = {expect report.env["A"]?} (input A was shape=[2] #[10.0, 100.0])"
          Lean.logInfo s!"S3 .ok  W = {expect report.env["W"]?}"
    | .error _ => Lean.logInfo "S3 prepare failed"
  | _ => Lean.logInfo "S3 compile failed"

-- ─────────────────────────────────────────────────────────────────────────────
-- Fixture 2 (BND-01 candidate): a PREDICATE DESTINATION selects the Boolean (min, max) algebra.
-- Inputs are undeclared (`f64`) and carry NON-BINARY floats.
--   P[i] = max_j min(X[i], Y[j])
--   X = [0.5, 0.25], Y = [0.75, 0.1]
--   P[0] = max(min .5 .75, min .5 .1) = max(.5,.1) = 0.5
--   P[1] = max(min .25 .75, min .25 .1) = max(.25,.1) = 0.25
-- ─────────────────────────────────────────────────────────────────────────────

private def predProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  predicate P(i)
  P[i] := X[i] · Y[j]
}

private def fuzzyInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" ⟨[2], #[0.5, 0.25]⟩).insert
    "Y" ⟨[2], #[0.75, 0.1]⟩

-- SPIKE 4 — non-binary values into a Boolean-algebra destination, checked vs legacy.
run_cmd do
  match predProg.compileToScheduled.run 0 with
  | .error e _ => Lean.logInfo s!"S4 compile failed: {repr e}"
  | .ok sched _ =>
    match InputSignature.ofDenseInputsForDecls sched.decls fuzzyInputs with
    | .error e => Lean.logInfo s!"S4 signature failed: {repr e}"
    | .ok sig =>
      match prepareEvalPlan sched sig with
      | .error _ => Lean.logInfo "S4 prepare failed"
      | .ok prepared =>
        Lean.logInfo s!"S4 materializedSignatures: \
{repr (prepared.materializedSignatures.toOption.map (fun a => a.map (fun e => (e.1, e.2.dtype))))}"
        match runPreparedDense prepared fuzzyInputs with
        | .error f => Lean.logInfo s!"S4 checked REJECTED: {repr f.cause}"
        | .ok report => Lean.logInfo s!"S4 CHECKED P = {expect report.env["P"]?}"
        match TLProgram.eval predProg fuzzyInputs with
        | .error e => Lean.logInfo s!"S4 legacy failed: {e.error}"
        | .ok r => Lean.logInfo s!"S4 LEGACY  P = {expect r.env["P"]?}"

-- SPIKE 5 — does an INPUT slot's `bool` dtype tag change any Dense behavior?
-- `Z` declared predicate (input signature `bool`) vs undeclared (`f64`), identical Float data.
private def boolInputProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  predicate Z(i)
  Q[i] := Z[i] · Z[i]
}

private def realInputProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  Q[i] := Z[i] · Z[i]
}

private def fuzzyZ : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "Z" ⟨[2], #[0.5, 3.0]⟩

run_cmd do
  for (nm, prog) in [("bool-declared", boolInputProg), ("undeclared-f64", realInputProg)] do
    match prog.compileToScheduled.run 0 with
    | .error e _ => Lean.logInfo s!"S5 {nm} compile failed: {repr e}"
    | .ok sched _ =>
      match InputSignature.ofDenseInputsForDecls sched.decls fuzzyZ with
      | .error e => Lean.logInfo s!"S5 {nm} signature failed: {repr e}"
      | .ok sig =>
        match prepareEvalPlan sched sig with
        | .error _ => Lean.logInfo s!"S5 {nm} prepare failed"
        | .ok prepared =>
          let dt := (prepared.plan.raw.tensorSigs.getD 0 { shape := #[], dtype := .f32 }).dtype
          match runPreparedDense prepared fuzzyZ with
          | .error f => Lean.logInfo s!"S5 {nm} REJECTED: {repr f.cause}"
          | .ok r => Lean.logInfo s!"S5 {nm}: slot0 dtype={repr dt}  Q = {expect r.env["Q"]?}"

-- SPIKE 6 — the declaration-BLIND signature producer (`ofDenseInputs`) against a program that
-- declares a predicate INPUT: does Step B catch it?
run_cmd do
  match boolInputProg.compileToScheduled.run 0 with
  | .error e _ => Lean.logInfo s!"S6 compile failed: {repr e}"
  | .ok sched _ =>
    match prepareEvalPlan sched (InputSignature.ofDenseInputs fuzzyZ) with
    | .ok _ => Lean.logInfo "S6 declaration-blind signature was ACCEPTED (!!)"
    | .error f =>
      match f.cause with
      | .inputSignature c => Lean.logInfo s!"S6 rejected, inputSignature: {repr c}"
      | _ => Lean.logInfo "S6 rejected with some other cause"

-- SPIKE 7 — the positional boundary `runDensePlan`: does it re-establish anything `pack` does not?
-- Feed a store whose Float data is arbitrary at a `bool`-signature input slot.
run_cmd do
  match boolInputProg.compileToScheduled.run 0 with
  | .ok sched _ =>
    match InputSignature.ofDenseInputsForDecls sched.decls fuzzyZ with
    | .ok sig =>
      match prepareEvalPlan sched sig with
      | .ok prepared =>
        match runDensePlan prepared.plan #[⟨[2], #[7.0, -3.0]⟩] with
        | .error e => Lean.logInfo s!"S7 runDensePlan REJECTED arbitrary floats at a bool slot: {repr e}"
        | .ok store => Lean.logInfo s!"S7 runDensePlan .ok, store = \
{repr (store.map (fun t => t.data))}"
        -- arity and shape are checked:
        Lean.logInfo s!"S7 wrong arity  : {repr (runDensePlan prepared.plan #[] |>.toOption.isSome)}"
        Lean.logInfo s!"S7 wrong shape  : \
{repr (runDensePlan prepared.plan #[⟨[3], #[1.0,2.0,3.0]⟩] |>.toOption.isSome)}"
        Lean.logInfo s!"S7 wrong storage: \
{repr (runDensePlan prepared.plan #[⟨[2], #[1.0]⟩] |>.toOption.isSome)}"
      | .error _ => Lean.logInfo "S7 prepare failed"
    | .error _ => Lean.logInfo "S7 signature failed"
  | _ => Lean.logInfo "S7 compile failed"

-- SPIKE 8 — the Executable boundary: can a validated kernel be REUSED at a `.pointwise` step index?
-- `Y[i] := relu(X[i])` lowers to `.assign → .pointwise`, so step 1 has no JAX kernel at all.
private def nonlinProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := relu(X[i])
}

private def nonlinInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[2], #[1.0, -2.0]⟩

private def stepKind : PlanStep → String
  | .assign _ => "assign" | .scan _ => "scan"
  | .pointwise _ => "pointwise" | .axiswise _ => "axiswise"

run_cmd do
  match nonlinProg.compileToScheduled.run 0 with
  | .error e _ => Lean.logInfo s!"S8 compile failed: {repr e}"
  | .ok sched _ =>
    match prepareEvalPlan sched (InputSignature.ofDenseInputs nonlinInputs) with
    | .error _ => Lean.logInfo "S8 prepare failed"
    | .ok prepared =>
      let raw := prepared.plan.raw
      Lean.logInfo s!"S8 step kinds: {repr (raw.steps.map stepKind)}"
      match (raw.steps[0]? : Option PlanStep) with
      | some (.assign a) =>
        match checkAssign raw.tensorSigs a, a.terms[0]? with
        | .ok checked, some term =>
          let opRow : Array Nat := match (term.factors[0]? : Option FactorPlan) with
            | some (.read f) => #[f.sourceSlot] ++ (Array.range f.map.coeffs.size)
            | _ => #[]
          let einsumCand : EinsumExperimentKernelCandidate :=
            { semanticAssignment := checked, destination := a.destinationSlot
            , operands := #[opRow], outputAxes := term.outputPos }
          Lean.logInfo s!"S8 einsum candidate operands={repr einsumCand.operands} \
outputAxes={repr einsumCand.outputAxes}"
          match validateAndConstructKernel raw.tensorSigs (.einsum einsumCand) with
          | .error e => Lean.logInfo s!"S8 kernel validation rejected step 0: {repr e}"
          | .ok k0 =>
            Lean.logInfo s!"S8 step-0 kernel validated, evidence={repr k0.evidence}"
            let cand : JaxExecutableCandidate :=
              { source := prepared, steps := #[k0, k0]
              , evidence := aggregateEvidenceList (#[k0, k0].map (·.evidence))
              , aggregated := rfl }
            match validateAndConstructExecutable cand with
            | .ok _ => Lean.logInfo "S8 executable ACCEPTED a kernel reused at a .pointwise step (!!)"
            | .error e => Lean.logInfo s!"S8 executable rejected: {repr e}"
        | _, _ => Lean.logInfo "S8 checkAssign/term unavailable"
      | other => Lean.logInfo s!"S8 step 0 is not an assign: {repr (other.map stepKind)}"

-- SPIKE 9 — failed-construction evidence for the two `getD`/`replicate` defaults in
-- `packChecked` / `runDensePlan`: can a `CheckedEvalPlan` carry an out-of-range `inputSlots`
-- entry, or a `tensorSigs` slot nothing produces?
private def planErrOf {α} : Except PlanStepError α → String
  | .error e => repr e |>.pretty
  | .ok _ => "ACCEPTED (!!)"

run_cmd do
  match swapProg.compileToScheduled.run 0 with
  | .ok sched _ =>
    match prepareEvalPlan sched (InputSignature.ofDenseInputs swapInputs) with
    | .ok prepared =>
      let raw := prepared.plan.raw
      Lean.logInfo s!"S9 baseline checkPlan: {planErrOf (checkPlan raw)}"
      Lean.logInfo s!"S9 inputSlots := #[99]: \
{planErrOf (checkPlan { raw with inputSlots := #[99] })}"
      Lean.logInfo s!"S9 extra unproduced tensorSig slot: \
{planErrOf (checkPlan { raw with tensorSigs := raw.tensorSigs.push { shape := #[1], dtype := .f64 } })}"
    | .error _ => Lean.logInfo "S9 prepare failed"
  | _ => Lean.logInfo "S9 compile failed"

end AxisAProbe
