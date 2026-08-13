import LeanNCD.Eval.Plan.Compile
import LeanNCD.Eval.Plan.Dense
import LeanNCD.Eval.Report

/-!
# Wave C runtime adaptation (C4)

The layer between named source-facing tensors and the positional plan worker
(`papers/wave_c_evalplan_proposal.md` §4.3, §5.4, §5.5, Appendix A.8 C4.2). `pack`/`unpack`
translate `NamedDenseEnv ↔ Array DenseTensor`; `runPreparedDense` wires `pack → runDensePlan →
unpack` together, preserving `PreparedPlan.warnings` through every outcome.
-/

namespace LeanNCD.Eval.Plan
open LeanNCD.Eval Std

/-- Source-facing tensor environment, keyed by name. The boundary type `pack`/`unpack` translate
    to/from `Array DenseTensor` (the positional worker's own vocabulary). -/
abbrev NamedDenseEnv := HashMap String DenseTensor

/-- Resolve every input slot `runDensePlan` needs, in `raw.inputSlots` order, by NAME through
    `requiredInputs` — never by array position. `requiredInputs : RequiredBindings` is already
    checked (`checkBindings`, `Compile.lean`) to be a name-unique permutation onto
    `RequiredBindings`' OWN stored `inputSlots` field — NOT, by anything the type enforces, onto
    this particular `PreparedPlan`'s `raw.inputSlots`. The two agree for every plan
    `prepareEvalPlan` produces because it is the sole real producer and builds both from the same
    `inputSlotsAcc`; that is producer discipline, not a guarantee `PlanBindings`/`PreparedPlan`'s
    public constructors close off. So `pack` builds the `slot → name` map directly from
    `requiredInputs` and trusts the invariant instead of re-deriving it — the same way
    `runDensePlan`/`runDenseAssignAt` (`Dense.lean`) trust `checkPlan`'s invariants rather than
    re-validating them — but a hand-built `PreparedPlan` pairing a validly-checked
    `RequiredBindings` against a mismatched `raw.inputSlots` would not be caught here: the
    unmatched slot would silently resolve to `pack`'s generic `.missingEnvBinding ""` rather than a
    diagnostic naming it. What's left to check here is genuinely about the caller-supplied `env`,
    not about `requiredInputs`' own shape: resolving each name against `env` and validating
    shape/storage against `raw.tensorSigs[slot]` — the same value checks `runDensePlan`'s own
    per-input validation performs, reproduced here (not literally shared, since that helper is
    private and typed to `PositionalInputError`) so a NAMED failure is diagnosable without waiting
    for the positional worker to run. -/
def pack (plan : PreparedPlan) (env : NamedDenseEnv) :
    Except InputBindingError (Array DenseTensor) := do
  let raw := plan.plan.raw
  let slotName : HashMap TensorSlot String :=
    plan.bindings.requiredInputs.bindings.foldl (fun acc b => acc.insert b.slot b.name) {}
  let mut out : Array DenseTensor := #[]
  for slot in raw.inputSlots do
    -- `slotName` has an entry for every slot in `raw.inputSlots` FOR EVERY `PreparedPlan`
    -- `prepareEvalPlan` PRODUCES: `checkBindings` established `requiredInputs.bindings` is a
    -- name-unique permutation onto `requiredInputs`'s OWN stored `inputSlots` field, and
    -- `prepareEvalPlan` (the sole real producer) builds that field from the very same
    -- `inputSlotsAcc` it uses, unchanged, as this plan's `raw.inputSlots` — so for
    -- `prepareEvalPlan`'s output the two agree and the `getD` default is never actually reached.
    -- That agreement is producer discipline, not something the type enforces: nothing here stops
    -- a hand-built `PreparedPlan` from pairing a validly-checked `requiredInputs` against a
    -- different `raw.inputSlots`, in which case `getD`'s `""` default WOULD be reached, silently.
    let name := slotName.getD slot ""
    let t ← match env[name]? with
      | some t => pure t
      | none => throw (.missingEnvBinding name)
    let tsig := raw.tensorSigs.getD slot { shape := #[], dtype := .f64 }
    unless t.shape == tsig.shape.toList do
      throw (.shapeMismatch name slot tsig.shape t.shape)
    unless t.data.size == tsig.shape.toList.foldl (· * ·) 1 do
      throw (.storageMismatch name slot t.shape t.data.size)
    out := out.push t
  return out

/-- Reconstruct the named environment from a positional result. Starts from the ORIGINAL `env`
    (preserving every entry `pack` never consulted — extra inputs the plan doesn't read), then
    inserts every `PlanBindings.materializedNames` entry IN ORDER; a name written twice by the
    schedule appears twice here too, and since `HashMap.insert` overwrites, the later insertion
    (the plan's own last write) naturally wins — no separate "most recent" bookkeeping needed. -/
def unpack (bindings : PlanBindings) (env : NamedDenseEnv) (result : Array DenseTensor) :
    NamedDenseEnv :=
  bindings.materializedNames.foldl
    (fun acc b => acc.insert b.name (result.getD b.slot ({ shape := [], data := #[] } : DenseTensor)))
    env

/-- Run a prepared plan against a named environment: `pack` into positional slots, run the
    positional worker, `unpack` the result back into the named environment, preserving `plan`'s
    preparation warnings through every outcome (success, a `pack` failure, or a `runDensePlan`
    failure). -/
def runPreparedDense (plan : PreparedPlan) (env : NamedDenseEnv) :
    Except PlanRunFailure EvalReport := do
  let packed ← match pack plan env with
    | .ok a => pure a
    | .error e => throw { cause := .binding e, warnings := plan.warnings }
  let result ← match runDensePlan plan.plan packed with
    | .ok r => pure r
    | .error e => throw { cause := .execution e, warnings := plan.warnings }
  return { env := unpack plan.bindings env result, warnings := plan.warnings }

end LeanNCD.Eval.Plan
