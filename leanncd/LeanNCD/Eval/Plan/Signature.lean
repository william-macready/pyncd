import LeanNCD.Eval.SizeInfer
import LeanNCD.Eval.Plan.Types
import LeanNCD.DSL.Pipeline.Structural

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
    carries a concrete `List Nat` shape. Unchanged by Task 4.3: callers that already know their
    program declares no predicate-typed name keep this simpler, non-declaration-aware constructor;
    `ofDenseInputsForDecls` below is the declaration-aware counterpart. -/
def InputSignature.ofDenseInputs (inputs : HashMap String DenseTensor) : InputSignature :=
  { tensors := inputs.toList.foldl
      (fun acc (nm, t) => acc.insert nm { shape := t.shape.toArray, dtype := .f64 }) {} }

/-- The top-level destination/signature dtype a declaration commits its name to: `bool` for exactly
    a `.predicate` declaration, `f64` for every other declaration AND for no declaration at all (an
    undeclared external name). Shared by `ofDenseInputsForDecls` below (the external-signature side)
    and `Compile.lean`'s `prepareEvalPlan` (the produced/destination side, Step B and Step D) — one
    rule, not two independently-drifting copies. -/
def dtypeOfDecl : Option Decl → ScalarDType
  | some (.predicate _ _) => .bool
  | _ => .f64

/-- Declaration-aware counterpart of `ofDenseInputs` (Task 4.3): selects `bool` for exactly the
    names a `.predicate` declaration commits to, `f64` for everything else — a `.tensor`/`.linear`
    declaration or no declaration at all (an undeclared external name). Uses the shared,
    duplicate-rejecting `buildDeclEnv` (`DSL/Pipeline/Structural.lean`) — the SAME classification
    `resolveDecls` and `prepareEvalPlan`'s Step 0 apply — rather than a linear `decls` scan
    (`Eval.combineFor`'s pattern), so this cannot disagree with either about which declaration wins
    when a name is declared more than once (the pitfall `combineFor`'s own doc comment already
    names). A malformed `decls` list (a genuine `duplicateTensorDecl`) degrades to treating every
    name as undeclared (`f64`) rather than failing: every real caller passes an already
    schedule-validated `decls` list (`buildDeclEnv` already succeeded once, during `resolveDecls` or
    `prepareEvalPlan`'s own Step 0), so this fallback is unreached by anything this codebase actually
    calls, and keeping the function total matches `ofDenseInputs`'s own shape. -/
def InputSignature.ofDenseInputsForDecls (decls : List Decl) (inputs : HashMap String DenseTensor) :
    InputSignature :=
  let env : DeclEnv := (buildDeclEnv decls).toOption.getD {}
  { tensors := inputs.toList.foldl
      (fun acc (nm, t) => acc.insert nm { shape := t.shape.toArray, dtype := dtypeOfDecl env[nm]? })
      {} }

/-- Signature-driven counterpart of `Eval.inferAxisSizes`: same fixpoint, sourced from a static
    `InputSignature` instead of concrete tensors. `ScheduledProgram.explicitSizes` is passed
    unchanged as `seed` by `prepareEvalPlan` (a later slice), exactly as `Eval.inferAxisSizes`
    receives it today. -/
def inferAxisSizesFromSignature (seed : HashMap UID Nat) (sig : InputSignature)
    (stmts : List Stmt) : Except EvalFailure (HashMap UID Nat × List EvalWarning) :=
  inferAxisSizesCore seed (fun nm => (sig.tensors[nm]?).map (fun ts => ts.shape.toList)) stmts

end LeanNCD.Eval.Plan
