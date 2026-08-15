import LeanNCD.Eval.Plan.RawStep

/-!
# Wave C raw evaluation-plan graph (C3)

`RawEvalPlan` is the public, unchecked graph record accepted from a compiler or codec: the
positional signature table, the ordered set of input slots, an ordered sequence of local
operations, and the numeric convention. No graph scheduling logic lives here — this module owns
only the open presentation; `checkPlan` (`EvalPlan.lean`) is what turns a `RawEvalPlan` into evidence
that its wiring is sound.
-/

namespace LeanNCD.Eval.Plan

/-- One unchecked evaluation graph: a positional tensor-signature table, ordered input slots, and
    ordered local operations. `steps` are `PlanStep`s in declared order — the order a compiler or
    codec produced them, not yet validated for slot availability or production order. -/
structure RawEvalPlan where
  tensorSigs  : Array TensorSignature
  inputSlots  : Array TensorSlot
  steps       : Array PlanStep
  numericMode : NumericMode
  deriving DecidableEq, BEq, Repr, Inhabited

end LeanNCD.Eval.Plan
