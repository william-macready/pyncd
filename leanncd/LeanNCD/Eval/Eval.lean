import LeanNCD.Eval.Scan        -- (transitively brings Contract/Nonlin/Gather/Slots/Tensor)
import LeanNCD.Eval.Scatter
import LeanNCD.Eval.SizeInfer   -- `inferAxisSizes`, called directly below
import LeanNCD.Eval.Error
import LeanNCD.Eval.Report      -- `EvalReport` (C4): moved to a neutral leaf shared with `Plan/Adapter.lean`
import LeanNCD.DSL.Pipeline.Structural  -- `buildDeclEnv`: the shared declaration-authority rule
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
    this scheduled boundary without importing the source compiler.

    **Declaration validity first.** `sched.decls` is not merely carried along: `combineFor`
    (`Contract.lean`) selects a statement's whole contraction algebra by scanning it for the
    destination's declaration, taking the FIRST tensor-bearing match. On a list declaring one
    tensor-bearing name twice — `tensor Y` then `predicate Y` — that first match silently decides
    real-vs-Boolean semantics for `Y`, while a `DeclEnv` built from the same list would see the
    LAST. The source pipeline rules that list out (`resolveDecls` → `buildDeclEnv` →
    `duplicateTensorDecl`) and so does the checked backend (`prepareEvalPlan`'s Step 0), but this
    boundary accepts a hand-built `ScheduledProgram` that never passed either. `buildDeclEnv` is
    therefore re-run here, over `sched.decls` as presented, BEFORE size inference or any statement
    executes — the same shared rule, reporting the same `CompileError` in source order, nested in
    the existing `EvalError.compile` constructor (`Entry.lean` already reports source-compile
    failures that way, so no new error shape is introduced and no cause is stringified). `sched.env`
    is a cached pipeline product and stays unconsulted, exactly as in `prepareEvalPlan`.
    `.axis`/`.iter` declarations are a separate namespace and are skipped by `buildDeclEnv`, so an
    axis sharing a predicate's name is still legal here and still resolves to the predicate.

    **Read arity likewise.** A read's index count must agree with its name's declaration (`tensor
    X(i, j)` read as `X[i]`), with the other reads of the same external name, and with its
    producer's published rank. The source pipeline enforces that in `checkReadRanks`, between
    `resolveDecls` and `checkDtypes`; a hand-built schedule bypasses it, and this worker then
    evaluated the malformed read anyway — `evalAssignDtyped` resolves a short read against whatever
    the input's real rank is — while the checked backend rejected the same program. The shared
    `checkScheduledReadRanks` (`Structural.lean`) — the same rule AND the same
    `.plain`/scan-`base ++ recur` traversal as the predicate check below — therefore runs here too,
    in the source pipeline's own position: AFTER `buildDeclEnv` (a declaration is what a declared
    read's arity is checked against) and BEFORE the predicate rule, so a program violating both
    reports `rankMismatch`, exactly as `TLProgram.compile` would.

    **Predicate-output invariants likewise.** A `predicate`-declared destination carries {0,1}
    values, so its statement may carry neither a nonlinearity (`applyNonlin` would map `relu`/
    `softmax`/`normalize` over Boolean data) nor a non-`sum` aggregation (`combineFor` selects the
    Boolean `(∧, ∃)` algebra from the DECLARATION, so a `.max`/`.min` `agg` is silently ignored
    rather than honoured). The source pipeline rules both out (`checkDtypes`), and so does
    `prepareEvalPlan`'s Step 0 — but this boundary used to EXECUTE them, so the same malformed
    schedule was a typed `sourceInvariant (.predicateNonlin/.predicateAgg)` on the checked backend
    and a silently-wrong answer here. The shared `checkPredicateOutputs` (`Structural.lean`) — the
    same rule AND the same traversal both direct entries use — therefore runs here too, over
    `sched.stmts` as presented: every `.plain` statement and every `.scan` node's base and
    recurrence statements, in source order. It runs AFTER `buildDeclEnv` (a duplicate declaration
    makes "which declaration is `Y`" ambiguous, so the predicate obligation is not even
    well-defined until the env is) and BEFORE size inference and execution, exactly as in Step 0.

    **Pinned sizes likewise.** `sched.explicitSizes` is the OTHER cached pipeline product, and size
    inference seeds from it: a seeded UID is treated as already known (`inferAxisSizesCore`'s
    `let mut sizes := seed`), so a free LHS axis that no read constrains takes its extent from the
    seed unchallenged. On a hand-built schedule declaring `axis i : ℕ = 3` with a cached `i ↦ 4`,
    that silently allocates and indexes every `i`-shaped tensor at 4. The seed is therefore
    re-derived here from `sched.decls` through the shared `declaredAxisSizes`, the same rule
    `schedule` used to build the cached field and the same rule `prepareEvalPlan`'s Step 0 applies —
    which is what keeps the reference and checked backends answering identically for a schedule
    whose cache disagrees with its declarations, rather than trading one silent wrong answer for a
    silent disagreement. -/
def evalScheduled (sched : ScheduledProgram) (inputs : HashMap String DenseTensor) :
    Except EvalFailure EvalReport :=
  match buildDeclEnv sched.decls with
  | .error e => .error { error := .compile e, warnings := [] }
  | .ok declEnv =>
  match checkScheduledReadRanks declEnv sched.stmts with
  | .error e => .error { error := .compile e, warnings := [] }
  | .ok () =>
  match checkPredicateOutputs declEnv sched.stmts with
  | .error e => .error { error := .compile e, warnings := [] }
  | .ok () =>
  -- gather ALL underlying stmts (plain + scan base/recur) to infer axis sizes from the inputs:
  let allStmts : List Stmt := sched.stmts.flatMap (fun
    | .plain s => [s] | .scan _ _ b r _ => b ++ r | .scanPre _ _ _ => [])
  match inferAxisSizes (declaredAxisSizes sched.decls) inputs allStmts with
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
