import LeanNCD.Eval.Scan        -- (transitively brings Contract/Nonlin/Gather/Slots/Tensor)
import LeanNCD.Eval.Scatter
import LeanNCD.Eval.SizeInfer   -- `inferAxisSizes`, called directly below
import LeanNCD.Eval.Error
import LeanNCD.Eval.Report      -- `EvalReport` (C4): moved to a neutral leaf shared with `Plan/Adapter.lean`
namespace LeanNCD.Eval
open Std

/-- The declared output shape for a scatter `nm[slots] := …`, computed from the inferred source
    axis sizes (`sizes`): each affine slot's output extent is its affine map applied to the source
    sizes — `c0 + Σ cᵢ·size(aᵢ)` for an `.affine`, `c·size(a)` for a `.scale` (e.g. upsample
    `Out[2·i]` ⇒ `2·size(i)`), `size(a)+c` for a `.shift`, `n+1` for a `.const n`, `size(a)` for a
    bare axis. (`sizes[u]` defaults to 0 for an unseen UID.) -/
def scatterOutShape (sizes : HashMap UID Nat) (slots : List LHSSlot) : Except EvalError (List Nat) :=
  -- Every axis in a scatter output coordinate must have an inferred size. An unsized axis means
  -- it is unbound by any read (an upstream sizing gap), so FAIL LOUD rather than defaulting its
  -- size to 0 (which would silently produce a wrong-shaped, usually empty, output tensor).
  slots.mapM (fun sl => match sl.outExtent (fun u => sizes[u]?) with
    | some n => pure n
    | none   => throw (.shape (.unsizedScatterOutput sl)))

/-- Evaluate one `.plain` stmt → (name, tensor). -/
def evalPlain (decls : List Decl) (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (s : Stmt) : Except EvalError (String × DenseTensor) := do
  match s with
  | .assign nm slots rhs =>
      let (_, pre) ← evalAssignDtyped decls env sizes nm slots rhs    -- contract (dtype-aware)
      let axisUids := slots.filterMap (·.axisUID?)
      let rn ← resolveNonlin rhs.nonlin slots axisUids
      return (nm, applyNonlin rn axisUids pre)
  | .scatter nm slots rhs opts =>
      let outShape ← scatterOutShape sizes slots
      evalScatter env sizes nm slots rhs opts outShape
  | .recurMorphism nm _ _ => .error (.unsupportedRecurMorphism .evalPlain nm)

/-- Evaluate a `ScheduledProgram` on concrete inputs. This worker is compiler-independent: callers
    that start from a source `TLProgram` use `Entry.lean`, while future plan/backend work can invoke
    this scheduled boundary without importing the source compiler. -/
def evalScheduled (sched : ScheduledProgram) (inputs : HashMap String DenseTensor) :
    Except EvalFailure EvalReport :=
  -- gather ALL underlying stmts (plain + scan base/recur) to infer axis sizes from the inputs:
  let allStmts : List Stmt := sched.stmts.flatMap (fun
    | .plain s => [s] | .scan _ _ b r _ => b ++ r | .scanPre _ _ _ => [])
  match inferAxisSizes sched.explicitSizes inputs allStmts with
  | .error failure => .error failure
  | .ok (sizes, warnings) =>
      -- Execute under the workers' narrow `Except EvalError` type, then attach the already-known
      -- inference warnings to either outcome at this orchestration boundary.
      let execution : Except EvalError (HashMap String DenseTensor) := do
        let mut env := inputs
        for sc in sched.stmts do
          match sc with
          | .plain s =>
              let (nm, t) ← evalPlain sched.decls env sizes s
              env := env.insert nm t
          | .scan .. =>
              let outs ← evalScan sched.decls env sizes sc
              for (nm, t) in outs do env := env.insert nm t
          | .scanPre nm _ _ => throw (.unsupportedRecurMorphism .evalScheduled nm)
        return env
      match execution with
      | .ok env => .ok { env, warnings }
      | .error error => .error { error, warnings }

end LeanNCD.Eval
