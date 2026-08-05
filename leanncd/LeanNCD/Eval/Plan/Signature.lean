import LeanNCD.Eval.SizeInfer
import LeanNCD.Eval.Plan.Types

/-!
# Wave C signature-driven shape inference (C1)

`inferAxisSizesFromSignature` is `Eval.inferAxisSizesCore` sourced from a static `InputSignature`
instead of concrete `DenseTensor`s — the counterpart Wave C's future plan compiler
(`prepareEvalPlan`, a later slice) will call, in place of the Dense evaluator's
`Eval.inferAxisSizes`. `InputSignatureError` is deliberately *not* introduced here:
`Eval.evalScheduled`'s `inputs` parameter is always the raw external-input map (never the
accumulating `env`), so a signature-based shape lookup misses a name under exactly the same
circumstances the existing env-based lookup does — no new failure mode exists at this layer yet.
The real producer for `InputSignatureError` is `prepareEvalPlan`'s schedule-completeness check
(`papers/wave_c_evalplan_proposal.md` §4.2 step 2), which does not exist until C4.
-/

namespace LeanNCD.Eval.Plan
open Std LeanNCD.Eval

/-- Derive an `InputSignature` from concrete Dense inputs. Every entry gets `ScalarDType.f64`,
    Wave C's only admitted dtype — this function cannot fail, since every `DenseTensor` already
    carries a concrete `List Nat` shape. -/
def InputSignature.ofDenseInputs (inputs : HashMap String DenseTensor) : InputSignature :=
  { tensors := inputs.toList.foldl
      (fun acc (nm, t) => acc.insert nm { shape := t.shape.toArray, dtype := .f64 }) {} }

/-- Signature-driven counterpart of `Eval.inferAxisSizes`: same fixpoint, sourced from a static
    `InputSignature` instead of concrete tensors. `ScheduledProgram.explicitSizes` is passed
    unchanged as `seed` by `prepareEvalPlan` (a later slice), exactly as `Eval.inferAxisSizes`
    receives it today. -/
def inferAxisSizesFromSignature (seed : HashMap UID Nat) (sig : InputSignature)
    (stmts : List Stmt) : Except EvalFailure (HashMap UID Nat × List EvalWarning) :=
  inferAxisSizesCore seed (fun nm => (sig.tensors[nm]?).map (fun ts => ts.shape.toList)) stmts

end LeanNCD.Eval.Plan
