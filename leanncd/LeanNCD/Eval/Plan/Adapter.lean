import LeanNCD.Eval.Plan.Compile
import LeanNCD.Eval.Plan.EvalPlan
import LeanNCD.Eval.Report

/-!
# Wave C runtime adaptation (C4)

The layer between named source-facing tensors and the positional plan worker
(`papers/wave_c_evalplan_proposal.md` §4.3, §5.4, §5.5, Appendix A.8 C4.2). `pack`/`unpack`
translate `NamedDenseEnv ↔ Array DenseTensor`; `runPreparedDense` wires `pack → runDensePlan →
unpack` together, preserving `PreparedPlan.warnings` through every outcome.

Since the f32 slice's Task 4 this file also owns the CARRIER-POLYMORPHIC cores those three entries
are built from — `packBodyOf`, `unpackBodyOf`, `runPreparedDenseOf`. The binary32 named boundary
(`Adapter32.lean`'s `pack32`/`unpack32`/`runPreparedDense32`) is the same three cores at
`α := Float32` with its own carrier guards, not a second copy of this traversal.
-/

namespace LeanNCD.Eval.Plan
open LeanNCD.Eval Std

/-- Source-facing tensor environment over one scalar carrier `α`, keyed by name. The boundary type
    `pack`/`unpack` (and `pack32`/`unpack32`, `Adapter32.lean`) translate to/from
    `Array (DenseTensorOf α)` (the positional worker's own vocabulary). -/
abbrev NamedDenseEnvOf (α : Type) := HashMap String (DenseTensorOf α)

/-- The binary64 named environment: the original `NamedDenseEnv`, unchanged in meaning. -/
abbrev NamedDenseEnv := NamedDenseEnvOf Float

/-! ## Carrier-polymorphic adapter cores

Each of the three bodies below is the whole of what its public entry does EXCEPT the storage-kind
guard. That split is deliberate: the traversal genuinely has nothing carrier-specific in it (only
`DenseTensorOf.shape` and `.data.size` are ever read, and `α` never crosses into a result of a
different carrier), while the guard is precisely the carrier-specific part and must stay ONE
INDEPENDENTLY EDITABLE LINE PER PUBLIC ENTRY — six of them across the two files — so each entry's
guard can be shown to fire before that entry's OWN later checks rather than inheriting a sibling's.

None of these bodies can substitute one precision for another on its own: each is parametric in `α`
and maps `NamedDenseEnvOf α` to `Array (DenseTensorOf α)` and back. What they cannot do without a
guard is TELL a caller they reached for the wrong adapter, which is what the guards are for. -/

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
    for the positional worker to run.

    Carrier-polymorphic and GUARDLESS (f32 slice, Task 4): `packChecked`/`packChecked32` are this
    body behind their own storage-kind door. See the section header above for why the guard is not
    folded in here. -/
def packBodyOf {α : Type} (plan : PreparedPlan) (checked : CheckedPreparedBindings)
    (env : NamedDenseEnvOf α) : Except InputBindingError (Array (DenseTensorOf α)) := do
  let raw := plan.plan.raw
  let slotName : HashMap TensorSlot String :=
    checked.requiredInputs.bindings.foldl (fun acc b => acc.insert b.slot b.name) {}
  let mut out : Array (DenseTensorOf α) := #[]
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
    -- Only `.shape` is ever read off this default (the two checks below are shape/storage facts),
    -- so its `dtype` field is inert — `.f64` is written for continuity with `runDensePlan`'s
    -- identical idiom and carries no carrier claim; the binary32 path reaches the same `getD` with
    -- the same unreachability argument (`checkStepGraph` bounds every `raw.inputSlots` entry
    -- against `tensorSigs.size` before a `CheckedEvalPlan` exists).
    let tsig := raw.tensorSigs.getD slot { shape := #[], dtype := .f64 }
    unless t.shape == tsig.shape.toList do
      throw (.shapeMismatch name slot tsig.shape t.shape)
    unless t.data.size == tsig.shape.toList.foldl (· * ·) 1 do
      throw (.storageMismatch name slot t.shape t.data.size)
    out := out.push t
  return out

/-- `packBodyOf` behind the BINARY64 storage-kind door.

    STORAGE KIND FIRST, before any name is resolved and before any shape or storage is validated.
    `NamedDenseEnv` is `HashMap String DenseTensor` — binary64 buffers — so packing them into a
    `.float32` plan's positional store would relabel `Array Float` data as that plan's own binary32
    inputs without any numeric worker ever running. Placed on this private helper, not on `pack`
    below, so `runPreparedDense`'s own call site inherits it too. -/
private def packChecked (plan : PreparedPlan) (checked : CheckedPreparedBindings)
    (env : NamedDenseEnv) : Except InputBindingError (Array DenseTensor) := do
  unless plan.plan.storageKind == .float64 do
    throw (.storageKindMismatch .float64 plan.plan.storageKind)
  packBodyOf plan checked env

def pack (plan : PreparedPlan) (env : NamedDenseEnv) :
    Except InputBindingError (Array DenseTensor) := do
  let checked ← match checkPreparedBindings plan with
    | .ok checked => pure checked
    | .error e => throw (.invalidPreparedBindings e)
  packChecked plan checked env

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
    however hand-built its bindings — can present an out-of-range input slot there.

    Carrier-polymorphic and GUARDLESS (f32 slice, Task 4): `unpackChecked`/`unpackChecked32` are
    this body behind their own storage-kind door. -/
def unpackBodyOf {α : Type} (plan : PreparedPlan) (checked : CheckedPreparedBindings)
    (env : NamedDenseEnvOf α) (result : Array (DenseTensorOf α)) :
    Except PlanRunCause (NamedDenseEnvOf α) := do
  let expected := plan.plan.raw.tensorSigs.size
  unless result.size == expected do
    throw (.resultStore (.storeArityMismatch expected result.size))
  match checked.materializedWith result with
  | .error e => throw (.materialization e)
  | .ok pairs => return pairs.foldl (fun acc (nm, t) => acc.insert nm t) env

/-- `unpackBodyOf` behind the BINARY64 storage-kind door.

    STORAGE KIND FIRST, before the result store's arity is examined and before any name is
    published. The result environment this builds is a `NamedDenseEnv` of binary64 tensors, so
    publishing a `.float32` plan's outputs through it would hand a caller `Array Float` buffers
    under that plan's own output names. Same placement rationale as `packChecked`'s guard above. -/
private def unpackChecked (plan : PreparedPlan) (checked : CheckedPreparedBindings)
    (env : NamedDenseEnv) (result : Array DenseTensor) :
    Except PlanRunCause NamedDenseEnv := do
  unless plan.plan.storageKind == .float64 do
    throw (.storageKindMismatch .float64 plan.plan.storageKind)
  unpackBodyOf plan checked env result

def unpack (plan : PreparedPlan) (env : NamedDenseEnv) (result : Array DenseTensor) :
    Except PlanRunCause NamedDenseEnv := do
  let checked ← match checkPreparedBindings plan with
    | .ok checked => pure checked
    | .error e => throw (.invalidBindings e)
  unpackChecked plan checked env result

/-- Run a prepared plan against a named environment, over one scalar carrier: pack into positional
    slots, run the positional worker, unpack the result back into the named environment, preserving
    `plan`'s preparation warnings through every outcome (success, a pack failure, a worker failure,
    or an unpack failure — whose typed cause is carried through unchanged, so the value a caller
    sees here and the value a direct unpack returns are the same).

    `carrier`, `packer`, `unpacker`, and `worker` are supplied by each public entry
    (`runPreparedDense` below, `runPreparedDense32` in `Adapter32.lean`) rather than derived here,
    for two reasons. The composite entry's OWN storage-kind guard — the `carrier` comparison
    immediately below, first, before `checkPreparedBindings`, before the packer, and before the
    worker — is not redundant with the packer's: this is a whole named runner, and a caller must see
    the adapter-tier cause (`PlanRunCause.storageKindMismatch`) for "you handed the Float runner a
    binary32 plan", not a nested pack or worker diagnostic that names a boundary further in. Passing
    it in keeps that guard one editable line PER RUNNER instead of one shared line serving both. And
    passing the packer/unpacker in — rather than calling the guardless bodies directly — preserves
    each carrier's defence in depth exactly as it stood before this refactor. -/
def runPreparedDenseOf {α : Type} (carrier : LeanNCD.StorageKind)
    (packer : PreparedPlan → CheckedPreparedBindings → NamedDenseEnvOf α →
      Except InputBindingError (Array (DenseTensorOf α)))
    (unpacker : PreparedPlan → CheckedPreparedBindings → NamedDenseEnvOf α →
      Array (DenseTensorOf α) → Except PlanRunCause (NamedDenseEnvOf α))
    (worker : CheckedEvalPlan → Array (DenseTensorOf α) →
      Except PositionalInputError (Array (DenseTensorOf α)))
    (plan : PreparedPlan) (env : NamedDenseEnvOf α) :
    Except PlanRunFailure (EvalReportOf α) := do
  unless plan.plan.storageKind == carrier do
    throw { cause := .storageKindMismatch carrier plan.plan.storageKind
          , warnings := plan.warnings }
  let checked ← match checkPreparedBindings plan with
    | .ok checked => pure checked
    | .error e => throw { cause := .binding (.invalidPreparedBindings e), warnings := plan.warnings }
  let packed ← match packer plan checked env with
    | .ok a => pure a
    | .error e => throw { cause := .binding e, warnings := plan.warnings }
  let result ← match worker plan.plan packed with
    | .ok r => pure r
    | .error e => throw { cause := .execution e, warnings := plan.warnings }
  let unpacked ← match unpacker plan checked env result with
    | .ok e => pure e
    | .error c => throw { cause := c, warnings := plan.warnings }
  return { env := unpacked, warnings := plan.warnings }

/-- The BINARY64 named runner: `pack → runDensePlan → unpack`, with its own `.float64` guard first. -/
def runPreparedDense (plan : PreparedPlan) (env : NamedDenseEnv) :
    Except PlanRunFailure EvalReport :=
  runPreparedDenseOf .float64 packChecked unpackChecked runDensePlan plan env

end LeanNCD.Eval.Plan
