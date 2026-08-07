import LeanNCD.Eval.Tensor
import LeanNCD.Eval.Error

namespace LeanNCD.Eval

/-- The complete result of evaluating an already-scheduled program. `env` deliberately preserves
    the evaluator's established full-environment behavior (inputs plus every computed tensor);
    `warnings` makes non-fatal sizing diagnostics persistent data instead of trace output. Moved
    here verbatim from `Eval.lean` (C4) — a neutral leaf shared by the legacy scheduled evaluator
    and the new `Plan/Adapter.lean`, so the latter does not need to import the whole `Eval.lean`
    dependency chain just to name this type. -/
structure EvalReport where
  env : Std.HashMap String DenseTensor
  warnings : List EvalWarning

end LeanNCD.Eval
