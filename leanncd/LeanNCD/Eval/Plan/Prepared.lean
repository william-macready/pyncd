import LeanNCD.Eval.Plan.EvalPlan

/-!
# Wave C prepared-plan bindings (C4)

Owns `SlotBinding`, `PlanBindings`, `PreparedPlan` — the source-name-keyed sidecar around a
`CheckedEvalPlan` (§5.4). No canonical bytes or fingerprint field (that's `Canonical.lean`, C5).

`PreparedPlan` is also the two-phase post-checked pipeline's own boundary: `CheckedEvalPlan` →
`PreparedPlan` (this file, production `LeanNCD`) → `JaxExecutableCandidate` → `JaxExecutable`
(`Executable.lean`, Thread 5, consumed only by the non-default `JaxExperiment` library under
`experiments/jax_bridge`). Thread 5's own plan named `Compile.lean` routing to the new
executable-creation entry point (`lowerCheckPlanToCandidate`) and a comment here on that account,
but that entry point lives in `JaxExperiment`, not `LeanNCD` — wiring `Compile.lean` (production)
to call into it would be a wrong-direction dependency, so neither happened; this note records that
as a deliberate scope decision, not a silent omission.
-/

namespace LeanNCD.Eval.Plan

structure SlotBinding where
  name : String
  slot : TensorSlot
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The subset of what used to be a plain `Array SlotBinding` that is checked, not merely assumed,
    to be a name-unique reordering of its OWN stored `inputSlots` field below: `bindings.map
    (·.slot)` is a `List.Perm` of `inputSlots` — deliberately NOT plain array/positional equality,
    because `Adapter.lean`'s `pack` resolves bindings by NAME, never by array position, and only a
    `Perm`-based proof lets a reordering of `bindings` (`AdapterTest.lean` Check 5) stay provably
    legal — and `bindings.map (·.name)` has no duplicates. IMPORTANT SCOPE NOTE: `aligned` proves
    the permutation against `inputSlots` as stored HERE, not against the enclosing
    `PreparedPlan.plan.raw.inputSlots` — nothing in the type ties the two together.
    They coincide for every plan `prepareEvalPlan` produces only because it is the sole real
    producer that builds a `RequiredBindings` and its enclosing `PreparedPlan` together from the
    same array; `PlanBindings`/`PreparedPlan`'s public constructors don't enforce that coupling, so
    a hand-built `PreparedPlan` could pair a validly-checked `RequiredBindings` with a mismatched
    `raw.inputSlots` — `Adapter.lean`'s `pack` still fails loud on it (a `.missingEnvBinding` naming
    the unmatched slot, see `Error.lean`'s `InputBindingError` doc comment), just not as a
    type-level guarantee the way alignment against ITS OWN `inputSlots` is. Private constructor:
    the only way to build one from outside this module is `checkBindings`, so a `RequiredBindings`
    misaligned against ITS OWN
    `inputSlots` field (duplicate/extra/missing slot, or a name bound twice) is unconstructable,
    not merely untested — that guarantee does not extend to alignment against some OTHER
    `inputSlots` array such as a differently-constructed `PreparedPlan`'s. No `BEq`/
    `DecidableEq`/`Inhabited`: same precedent as `PreparedPlan` itself (below) — compare through
    `.bindings` (a plain `Array SlotBinding`, which does derive `BEq`) rather than whole-struct
    equality. -/
structure RequiredBindings where private mk ::
  inputSlots : Array TensorSlot
  bindings   : Array SlotBinding
  aligned    : (bindings.map (·.slot)).toList.Perm inputSlots.toList
  deriving Repr

/-- First name in `names` that recurs later in the list, if any. Total and structurally recursive;
    used only to give `checkBindings`'s `.duplicateName` failure a concrete witness once
    `(bindings.map (·.name)).toList.Nodup` has already been decided false — that branch guarantees
    this returns `some`, never `none`; `checkBindings` unwraps with a self-documenting fallback
    string rather than an `Option`-shaped return type collapsing to a bare `""` sentinel that could
    be mistaken for a real (empty) name elsewhere. -/
private def firstDuplicateName : List String → Option String
  | [] => none
  | n :: rest => if rest.contains n then some n else firstDuplicateName rest

/-- The only public way to build a `RequiredBindings`. Reordering `bindings` is fine (`Perm`, not
    positional equality — see `RequiredBindings`'s doc comment for why), but the slot multiset must
    match `inputSlots` exactly and every name must be used at most once. -/
def checkBindings (inputSlots : Array TensorSlot) (bindings : Array SlotBinding) :
    Except BindingsError RequiredBindings :=
  if h : (bindings.map (·.slot)).toList.Perm inputSlots.toList then
    if (bindings.map (·.name)).toList.Nodup then
      .ok { inputSlots, bindings, aligned := h }
    else
      .error (.duplicateName
        ((firstDuplicateName (bindings.map (·.name)).toList).getD
          "<unreachable: checkBindings already confirmed a duplicate exists>"))
  else
    .error (.notAPermutation inputSlots (bindings.map (·.slot)))

/-- `materializedNames` is NOT deduplicated by name — one entry per PERSISTENT OUTPUT, in schedule
    order. That is one entry per persistent STATE for a `PlanStep.scan` (since Wave F F4 admitted
    source scans, a single coupled scan step publishes one complete history per state — see
    `Compile.lean`'s scan arm, which pushes one binding per `compiled.stateNames` entry, and
    `ScanCompileTest.lean`'s fixture B, where one scan step yields `#[G, H]`). For a top-level
    statement it is NOT simply "one entry per `PlanStep.assign`" any more (Thread 4): an `.identity`
    statement still publishes its one name off its own `.assign` step, exactly as before, but a
    `.pointwise`/`.axiswise` statement compiles to a `.assign → .pointwise`/`.axiswise` chain whose
    INTERNAL `.assign` publishes no materialized name at all — only the trailing `.pointwise`/
    `.axiswise` step publishes the statement's one name (see `Compile.lean`'s `prepareEvalPlan`
    `.plain` branch, and `NonlinCompileTest.lean` Section 3, which pins this directly: the internal
    slot is never named). Block-local scratch inside a scan is deliberately NOT here — it never
    becomes an outer slot or a materialized name. A name reassigned twice appears twice; `unpack`
    (Task 3) relies on this, inserting each in order so the LAST entry for a repeated name is the one
    that survives. -/
structure PlanBindings where
  requiredInputs    : RequiredBindings
  materializedNames : Array SlotBinding
  deriving Repr

/-- No `deriving` clause: `CheckedEvalPlan` (private constructor) has no `BEq`/`DecidableEq`/
    `Inhabited` of its own (same as `CheckedAssignPlan`'s established precedent), and
    `List EvalWarning` has no `Repr`. Tests compare through field projections (`.bindings`,
    `.plan.raw`, ...) rather than whole-struct equality — the same idiom already used elsewhere for
    private-constructor types. -/
structure PreparedPlan where
  plan     : CheckedEvalPlan
  bindings : PlanBindings
  warnings : List EvalWarning

/-- Resolve every `materializedNames` binding against ONE slot-indexed table, pairing each entry's
    name with that slot's value — the SINGLE materialized-binding validation/access path in this
    subsystem, shared by the metadata accessor (`materializedSignatures`, over `raw.tensorSigs`) and
    by execution (`Adapter.unpack`, over the positional result store). They used to be independent:
    the accessor failed loud on an out-of-range slot while `unpack` silently substituted an empty
    scalar tensor for it and published that under the binding's name, so the two boundaries could —
    and did — disagree about the same `PlanBindings`. Sharing the traversal is what stops them
    drifting again; a caller supplies the table, this function supplies the discipline.

    Order and repeats are `materializedNames`' own (see its doc comment: NOT deduplicated), so the
    result stays positionally parallel to it and `unpack`'s "later insertion wins" semantics for a
    repeated name is preserved exactly.

    Fails loud rather than defaulting: a slot outside `table` is `PlanError.slotOutOfRange` (the
    existing constructor every other slot-table lookup in this subsystem already raises —
    `Check.lean`, `Nonlin.lean`, `Block.lean`), carrying the offending slot and the table size.
    `mapM` short-circuits at the FIRST offending entry, so no prefix of a malformed binding list is
    ever handed back to a caller half-resolved. Neither fabricating a value nor filtering the entry
    out is acceptable: fabricating misdescribes the binding (a scalar `f64` signature for a Boolean
    destination, an empty tensor for a real result), and filtering silently breaks the positional
    correspondence with `materializedNames` that both consumers rely on. -/
def PlanBindings.materializedWith {α : Type} (b : PlanBindings) (table : Array α) :
    Except PlanError (Array (String × α)) :=
  b.materializedNames.mapM (fun sb =>
    match table[sb.slot]? with
    | some v => .ok (sb.name, v)
    | none   => .error (.slotOutOfRange sb.slot table.size))

/-- Ordered materialized SIGNATURES (Task 4.3): pairs each `PlanBindings.materializedNames` entry
    with its own slot's `TensorSignature`, read from the checked plan's `raw.tensorSigs` table —
    same order, including repeats, as `materializedNames` itself (its own doc comment: NOT
    deduplicated; a name reassigned twice appears twice here too, each with its own slot's
    signature). Exposes the destination dtype `prepareEvalPlan`'s Step D derives from the source
    declaration (`dtypeOfDecl`, `Signature.lean`) at the one boundary a caller can observe it without
    reaching into `plan.raw` and re-deriving the pairing by hand.

    The traversal itself is `materializedWith` above, shared with `Adapter.unpack`: this accessor is
    that path applied to the signature table, nothing more. Failure is therefore identical at both
    boundaries — `PlanError.slotOutOfRange`, carrying the offending slot and the table size.
    Out-of-range is unreachable for any plan `prepareEvalPlan` produces (it allocates every
    materialized slot in `tensorSigs` itself), but `PreparedPlan`'s constructor is public and stays
    public — `AdapterTest`'s authority-substitution checks build one by struct update — so
    "unreachable via the real producer" is a producer-discipline fact, not a type-level guarantee,
    exactly as `RequiredBindings`'s own doc comment says of its alignment against
    `plan.raw.inputSlots`. -/
def PreparedPlan.materializedSignatures (p : PreparedPlan) :
    Except PlanError (Array (String × TensorSignature)) :=
  p.bindings.materializedWith p.plan.raw.tensorSigs

end LeanNCD.Eval.Plan
