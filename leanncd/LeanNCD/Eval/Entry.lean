import LeanNCD.Eval.Eval
import LeanNCD.DSL.Compile

namespace LeanNCD.Eval
open Std

-- This is the source-program boundary for the reference evaluator. Keeping compilation here,
-- rather than in `Eval.lean`, lets the scheduled worker remain reusable by the future EvalPlan
-- pipeline and by tests that construct `ScheduledProgram` values directly.

/-- Compile and evaluate a source `TLProgram`, preserving both the full environment and every
    non-fatal warning in either the successful `EvalReport` or failed `EvalFailure`. Compile
    failures have no inference warnings and remain nested as `EvalError.compile cause`; this
    boundary never renders or reconstructs the typed cause. -/
def TLProgram.eval (p : TLProgram) (inputs : HashMap String DenseTensor) :
    Except EvalFailure EvalReport :=
  match p.compileToScheduled |>.run 0 with
  | .ok sched _ => evalScheduled sched inputs
  | .error e _  => .error { error := .compile e, warnings := [] }

end LeanNCD.Eval
