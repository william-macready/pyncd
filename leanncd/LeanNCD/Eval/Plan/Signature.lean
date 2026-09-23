import LeanNCD.Eval.SizeInfer
import LeanNCD.Eval.Plan.Types
import LeanNCD.Eval.Plan.Error
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

/-- The top-level destination/signature dtype a declaration commits its name to: `f32` for exactly
    an explicit `tensor f32 …` declaration, `bool` for exactly a `.predicate` declaration, `f64` for
    every other declaration AND for no declaration at all (an undeclared external name). Shared by
    `ofDenseInputsForDecls` below (the external-signature side) and `Compile.lean`'s
    `prepareEvalPlan` (the produced/destination side, Step B and Step D) — one rule, not two
    independently-drifting copies.

    `.f32` is deliberately reported as itself rather than silently degraded to `.f64`: a degraded
    answer would let an explicitly-f32 program construct a CHECKED f64 plan and execute it in the
    existing `Float` worker, which is the exact silent-precision-substitution this classification
    exists to prevent. Since the f32 slice's Task 2 that answer is genuinely consumed rather than
    merely fail-loud: a homogeneous-f32 schedule compiles through `checkAssignF32` to `.float32`
    checked evidence, and this is the rule that gives each of its names an `f32` signature and its
    destinations an `f32` algebra. The binary64 entries (`dtypeAdmitted`, `checkAssign`, and every
    Float worker/adapter door) still reject `.f32` outright.

    Exhaustive, with no wildcard arm, exactly like `storageConstraintOfDecl` (`DSL/Ast.lean`): a
    future `TensorElementType` or `Decl` constructor must fail to compile here rather than silently
    classify as `f64`. -/
def dtypeOfDecl : Option Decl → ScalarDType
  | some (.typedTensor .f32 _ _) => .f32
  | some (.predicate _ _) => .bool
  | some (.tensor _ _) => .f64
  | some (.linear _ _ _) => .f64
  | some (.axis _ _) => .f64
  | some (.iter _ _) => .f64
  | none => .f64

/-- Rebuild the declaration environment a declaration-aware constructor answers every question
    against, or fail loud with `buildDeclEnv`'s own `CompileError` wrapped in the constructor's error
    family. Uses the shared, duplicate-rejecting `buildDeclEnv` (`DSL/Ast.lean`) — the SAME
    classification `resolveDecls` and `prepareEvalPlan`'s Step 0 apply — rather than a linear `decls`
    scan (`Eval.combineFor`'s pattern), so this cannot disagree with either about which declaration
    wins when a name is declared more than once (the pitfall `combineFor`'s own doc comment already
    names). The `decls` argument is the authority and is re-validated here: a malformed list (a
    genuine `duplicateTensorDecl`) never degrades to "every name undeclared, therefore `f64`". A
    silent degradation would be exactly the silent semantic drop the fail-loud convention forbids: it
    would hand back an all-real signature for a program that declares a predicate, and the resulting
    `f64` expectation would then be enforced downstream (`prepareEvalPlan` Step B) against the very
    declaration set that is malformed. Callers cannot substitute an already-validated `DeclEnv` and
    skip this: a cached `sched.env` is a pipeline product, not the schedule's authority
    (`prepareEvalPlan`'s Step 0 says the same and rebuilds it from `sched.decls` too). -/
def declEnvOrThrow (decls : List Decl) : Except InputSignatureBuildError DeclEnv :=
  match buildDeclEnv decls with
  | .ok env => .ok env
  | .error e => .error (.declaration e)

/-- The per-name carrier-compatibility rule both declaration-aware constructors apply, over the
    names a caller actually supplied buffers for.

    One rule, stated once: a name's declaration either constrains its precision
    (`storageConstraintOfName?`, `DSL/Ast.lean` — `.typedTensor .f32` ⇒ `.float32`,
    `.tensor`/`.linear` ⇒ `.float64`, and an UNDECLARED name ⇒ `.float64`, mirroring
    `dtypeOfDecl none = .f64`) or constrains nothing at all (a `.predicate`, whose declaration names
    the tensor's ALGEBRA rather than its precision). A constrained name whose declaration disagrees
    with the constructor's own carrier is rejected BY NAME; an unconstrained one is admitted on
    either carrier, which is exactly what lets one Boolean tensor ride along in a binary32 input map
    beside its real siblings and in a binary64 one beside theirs.

    This is deliberately the SHARED per-name constraint and not `scheduleStorageKind`'s whole-graph
    projection (`DSL/Pipeline/ScheduledValidation.lean`). That function answers a different question
    — "what single precision does this SCHEDULE commit to?" — and answers it with a `.float64`
    DEFAULT for a graph no used name constrains. Asking it here would default a predicate-only input
    map to binary64 and so refuse an explicitly-chosen `ofDenseInputs32ForDecls`, even though the
    caller has already named the carrier by choosing the constructor. The schedule-wide default
    still governs what `prepareEvalPlan` derives for such a program (a bool-only graph is still a
    `.float64` plan and is still not executable through `runPreparedDense32`); it just has no
    business constraining which buffers a caller may present. -/
def checkDeclCarriers (env : DeclEnv) (carrier : LeanNCD.StorageKind) (names : List String) :
    Except InputSignatureBuildError Unit := do
  for nm in names do
    match storageConstraintOfName? env nm with
    | some k => unless k == carrier do throw (.storageKindMismatch nm carrier k)
    | none   => pure ()

/-- The shared shape/dtype traversal behind both declaration-aware constructors, carrier-agnostic in
    the `DenseTensorOf α` shell: only `shape` is read off each buffer, and every dtype comes from the
    declaration through `dtypeOfDecl`, never from the carrier. Carries NO carrier guard of its own —
    each public constructor runs `checkDeclCarriers` with its own carrier first (see
    `ofDenseInputsForDecls`/`ofDenseInputs32ForDecls`), so that guard stays one independently
    editable line per constructor rather than one shared line serving both.

    PRIVATE because it is guardless (f32 slice, final-review fix wave). Unguarded, it is itself a
    relabel: called at `α := Float` over a `tensor f32`-declared name it returns an `.f32`
    signature for `Array Float` buffers, which is exactly what `checkDeclCarriers` exists to refuse
    and what no downstream door can catch (a signature carries no buffers to re-examine). While it
    was public it was a door around both constructors' guards; now the two constructors below are
    its only callers. -/
private def signatureOfDenseInputs {α : Type} (env : DeclEnv)
    (inputs : HashMap String (DenseTensorOf α)) :
    InputSignature :=
  { tensors := inputs.toList.foldl
      (fun acc (nm, t) => acc.insert nm { shape := t.shape.toArray, dtype := dtypeOfDecl env[nm]? })
      {} }

/-- Declaration-aware counterpart of `ofDenseInputs` (Task 4.3), for the BINARY64 carrier: selects
    `bool` for exactly the names a `.predicate` declaration commits to, `f64` for everything else —
    a `.tensor`/`.linear` declaration or no declaration at all (an undeclared external name).
    `ofDenseInputs` stays total because it consults no declaration at all.

    Since the f32 slice's Task 4 it also enforces the CARRIER: a name these binary64 buffers supply
    whose declaration commits it to `.float32` is `storageKindMismatch`, naming the input. Without
    that guard an `Array Float` buffer declared `tensor f32 X` would be handed back as an `.f32`
    SIGNATURE, which `prepareEvalPlan` then accepts as binary32 evidence for a plan whose inputs are
    binary64 — the one carrier lie this whole boundary exists to prevent, and one no downstream door
    can catch, since a signature carries no buffers to re-examine. The binary32 half of the same
    program goes through `ofDenseInputs32ForDecls` below. -/
def InputSignature.ofDenseInputsForDecls (decls : List Decl) (inputs : HashMap String DenseTensor) :
    Except InputSignatureBuildError InputSignature := do
  let env : DeclEnv ← declEnvOrThrow decls
  checkDeclCarriers env .float64 (inputs.toList.map (·.1))
  return signatureOfDenseInputs env inputs

/-- The BINARY32 sibling of `ofDenseInputsForDecls` (f32 slice, Task 4): the same declaration
    authority, the same `dtypeOfDecl` classification, and the same shape traversal, over NATIVE
    `DenseTensor32` buffers. A name it supplies whose declaration commits it to `.float64` — an
    ordinary `tensor`/`linear` declaration, or no declaration at all — is `storageKindMismatch`
    naming that input, the exact mirror of its sibling's guard, rather than a silently `.f32`-marked
    signature over a buffer the program says is binary64.

    There is no non-declaration-aware binary32 counterpart of `ofDenseInputs`: that constructor can
    be total precisely because `f64` is the answer for every undeclared name, and `f32` is never the
    answer for one. An f32 program's every real external is `tensor f32`-declared (an undeclared one
    constrains the schedule to `.float64` and makes it mixed, `prepareEvalPlan` Step 0b), so a
    declaration-blind binary32 constructor would have nothing to derive `f32` from. -/
def InputSignature.ofDenseInputs32ForDecls (decls : List Decl)
    (inputs : HashMap String DenseTensor32) : Except InputSignatureBuildError InputSignature := do
  let env : DeclEnv ← declEnvOrThrow decls
  checkDeclCarriers env .float32 (inputs.toList.map (·.1))
  return signatureOfDenseInputs env inputs

/-- Signature-driven counterpart of `Eval.inferAxisSizes`: same fixpoint, sourced from a static
    `InputSignature` instead of concrete tensors. `ScheduledProgram.explicitSizes` is passed
    unchanged as `seed` by `prepareEvalPlan` (a later slice), exactly as `Eval.inferAxisSizes`
    receives it today. -/
def inferAxisSizesFromSignature (seed : HashMap UID Nat) (sig : InputSignature)
    (stmts : List Stmt) : Except EvalFailure (HashMap UID Nat × List EvalWarning) :=
  inferAxisSizesCore seed (fun nm => (sig.tensors[nm]?).map (fun ts => ts.shape.toList)) stmts

end LeanNCD.Eval.Plan
