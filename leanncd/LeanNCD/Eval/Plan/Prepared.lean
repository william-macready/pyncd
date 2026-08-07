import LeanNCD.Eval.Plan.Check

/-!
# Wave C prepared-plan bindings (C4)

Owns `SlotBinding`, `PlanBindings`, `PreparedPlan` — the source-name-keyed sidecar around a
`CheckedEvalPlan` (§5.4). No canonical bytes or fingerprint field (that's `Canonical.lean`, C5).
-/

namespace LeanNCD.Eval.Plan

structure SlotBinding where
  name : String
  slot : TensorSlot
  deriving DecidableEq, BEq, Repr, Inhabited

/-- `materializedNames` is NOT deduplicated by name — exactly one entry per statement in
    `RawEvalPlan.steps`, in schedule order (§5.4's literal text: "every name produced by a
    `sched.stmts` entry"). A name reassigned twice appears twice; `unpack` (Task 3) relies on this,
    inserting each in order so the LAST entry for a repeated name is the one that survives. -/
structure PlanBindings where
  requiredInputs    : Array SlotBinding
  materializedNames : Array SlotBinding
  deriving DecidableEq, BEq, Repr, Inhabited

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
