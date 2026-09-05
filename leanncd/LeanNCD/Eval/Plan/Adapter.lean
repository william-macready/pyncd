import LeanNCD.Eval.Plan.Compile
import LeanNCD.Eval.Plan.EvalPlan
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
    `runDensePlan` (`EvalPlan.lean`) and `runDenseAssignAt` (`Dense.lean`) trust `checkPlan`'s
    invariants rather than re-validating them. If that invariant were ever broken (a hand-built `PreparedPlan` pairing a
    validly-checked `RequiredBindings` against a mismatched `raw.inputSlots`), `pack` fails loud
    with a `.missingEnvBinding` diagnostic naming the unmatched slot, rather than resolving a bogus
    empty-string name into `env`. What's left to check here is genuinely about the caller-supplied
    `env`, not about `requiredInputs`' own shape: resolving each name against `env` and validating
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
    -- `prepareEvalPlan`'s output the two agree and `slotName` always has an entry here. That
    -- agreement is producer discipline, not something the type enforces: nothing here stops a
    -- hand-built `PreparedPlan` from pairing a validly-checked `requiredInputs` against a
    -- different `raw.inputSlots`, in which case the slot genuinely has no bound name — handled
    -- below as a loud `missingEnvBinding` failure rather than a silent `""` lookup key.
    let name ← match slotName[slot]? with
      | some nm => pure nm
      | none => throw (.missingEnvBinding s!"<no binding for slot {slot}>")
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
    (the plan's own last write) naturally wins — no separate "most recent" bookkeeping needed.

    **The store's arity is the plan's, not the caller's (whole-branch review round 4).** This takes
    the whole `PreparedPlan`, not a bare `PlanBindings`, and requires `result.size` to equal
    `plan.raw.tensorSigs.size` EXACTLY before any binding is resolved. It used to validate
    `materializedNames` against `result.size` alone, so the caller's own store decided which
    bindings were legal: a binding naming slot 3 — out of range for a checked THREE-slot plan, and
    rejected as `slotOutOfRange 3 3` against a conforming store — succeeded the moment the caller
    handed over a four-element one, publishing whatever tensor happened to sit at slot 3 under that
    binding's name. Slot validity is a fact about the CHECKED PLAN, so the checked plan is what
    supplies the table size; a store of any other length is `PositionalInputError.storeArityMismatch`
    (the constructor `runDenseScan` already raises for exactly this, `Error.lean`), reported under
    `PlanRunCause.resultStore` — before bindings are looked at, so a too-long store is rejected as a
    wrong store rather than silently licensing extra slots, and a too-short one is rejected as a
    wrong store rather than mis-diagnosed as an out-of-range binding.

    Binding resolution itself then goes through the shared `PlanBindings.materializedWith`
    (`Prepared.lean`), the same path `PreparedPlan.materializedSignatures` uses against the
    signature table, so the metadata and execution boundaries cannot disagree about which bindings a
    `PlanBindings` resolves — and now cannot disagree about the table SIZE either, since
    `result.size = raw.tensorSigs.size` is established above. A binding naming a slot outside the
    plan is therefore `PlanError.slotOutOfRange` under `PlanRunCause.materialization` — reported
    BEFORE any name is published, since `mapM` short-circuits — rather than the empty scalar tensor
    this function once substituted silently and then inserted under that binding's name. That
    default was the worst possible lie here: `materializedNames` is public and caller-constructible
    (`PlanBindings` has a public constructor and `AdapterTest` builds one by struct update), so an
    out-of-range slot is genuinely reachable, and an empty tensor published under a real output name
    is indistinguishable from a legitimately empty result.

    The return type is `PlanRunCause` (not `PlanError`) precisely so a DIRECT `unpack` call reports
    the exact value `runPreparedDense` reports for the same malformation: that function now
    propagates this cause verbatim rather than re-tagging it.

    `pack`'s sibling `raw.tensorSigs.getD` default is NOT the same situation and is deliberately left
    alone: it indexes `raw.inputSlots`, which `checkPlan` bounds against `tensorSigs.size`
    (`checkStepGraph`'s first loop) before a `CheckedEvalPlan` exists at all, so no `PreparedPlan` —
    however hand-built its bindings — can present an out-of-range input slot there. -/
def unpack (plan : PreparedPlan) (env : NamedDenseEnv) (result : Array DenseTensor) :
    Except PlanRunCause NamedDenseEnv := do
  let expected := plan.plan.raw.tensorSigs.size
  unless result.size == expected do
    throw (.resultStore (.storeArityMismatch expected result.size))
  match plan.bindings.materializedWith result with
  | .error e => throw (.materialization e)
  | .ok pairs => return pairs.foldl (fun acc (nm, t) => acc.insert nm t) env

/-- Run a prepared plan against a named environment: `pack` into positional slots, run the
    positional worker, `unpack` the result back into the named environment, preserving `plan`'s
    preparation warnings through every outcome (success, a `pack` failure, a `runDensePlan` failure,
    or an `unpack` failure — whose typed cause is carried through unchanged, so the value a caller
    sees here and the value direct `unpack` returns are the same). -/
def runPreparedDense (plan : PreparedPlan) (env : NamedDenseEnv) :
    Except PlanRunFailure EvalReport := do
  let packed ← match pack plan env with
    | .ok a => pure a
    | .error e => throw { cause := .binding e, warnings := plan.warnings }
  let result ← match runDensePlan plan.plan packed with
    | .ok r => pure r
    | .error e => throw { cause := .execution e, warnings := plan.warnings }
  let unpacked ← match unpack plan env result with
    | .ok e => pure e
    | .error c => throw { cause := c, warnings := plan.warnings }
  return { env := unpacked, warnings := plan.warnings }

end LeanNCD.Eval.Plan
