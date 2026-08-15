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

/-- `materializedNames` is NOT deduplicated by name — exactly one entry per statement in
    `RawEvalPlan.steps`, in schedule order (§5.4's literal text: "every name produced by a
    `sched.stmts` entry"). A name reassigned twice appears twice; `unpack` (Task 3) relies on this,
    inserting each in order so the LAST entry for a repeated name is the one that survives. -/
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

end LeanNCD.Eval.Plan
