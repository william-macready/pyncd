import LeanNCD.DSL.Ast
import LeanNCD.DSL.Pipeline.Types
import LeanNCD.Eval.Plan.Error
import LeanNCD.Eval.Plan.Prepared
import LeanNCD.Eval.Plan.EvalPlan
import LeanNCD.Eval.Plan.Signature
import LeanNCD.Eval.Contract
import LeanNCD.DSL.Pipeline.Lowering

/-!
# Wave C source compiler: capability preflight (C4)

Ports C0's already-verified classification logic (`PlanContract.classify*`,
`test/Eval/Plan/ContractTest.lean`) from test-only `Classification`-valued classifiers into a real
production entry point that throws `CapabilityError`. No `PreparedPlan`, slot allocation, or shape
inference here — this file holds only capability preflight; `prepareEvalPlan` (Step D) grows it
with per-statement assignment residualization, generalized (Wave F F4 Task 2) into
`residualizeAssignment` so a future scan compiler (Task 3) can lower base/step assignments through
the same core instead of duplicating it.
-/

namespace LeanNCD.Eval.Plan

/-- Axis declarations (`.axis`, `.iter`) are structurally accepted regardless of use — rejection for
    `freeNorm`/scan usage happens at the `LHSSlot`/`ScanStmt` check below, not at the declaring
    axis. -/
def checkDecl : Decl → Except CapabilityError Unit
  | .tensor ..    => pure ()
  | .linear ..    => pure ()
  | .predicate n _ => throw (.booleanOutput n)
  | .axis ..      => pure ()
  | .iter ..      => pure ()

def checkLHSSlot (stmtName : String) : LHSSlot → Except CapabilityError Unit
  | .free _     => pure ()
  | .freeNorm a => throw (.unsupportedLhsSlot s!"{stmtName}: freeNorm {a.name}")
  | .iterAt a _ => throw (.unsupportedLhsSlot s!"{stmtName}: iterAt {a.name}")
  | .iterNext a => throw (.unsupportedLhsSlot s!"{stmtName}: iterNext {a.name}")
  | .affine _   => throw (.scatterOrAffineLhs s!"{stmtName}: affine LHS slot")

def checkFactor (stmtName : String) : Factor → Except CapabilityError Unit
  | .read ..       => pure ()
  | .iverson _     => throw (.maskOrPredicate s!"{stmtName}: iverson factor")
  | .unaryFn _ n _ => throw (.unaryFactor s!"{stmtName}: unary function on {n}")

def checkNonlin (stmtName : String) : Nonlin → Except CapabilityError Unit
  | .identity    => pure ()
  | .pointwise _ => throw (.unsupportedNonlin s!"{stmtName}: pointwise nonlinearity")
  | .axiswise .. => throw (.unsupportedNonlin s!"{stmtName}: axiswise nonlinearity")

def checkAggOp (stmtName : String) : AggOp → Except CapabilityError Unit
  | .sum => pure ()
  | .max => throw (.unsupportedAgg s!"{stmtName}: max aggregation")
  | .min => throw (.unsupportedAgg s!"{stmtName}: min aggregation")

/-- One `Stmt`'s capability check. Sub-construct order (LHS slots, then `agg`, then `nonlin`, then
    factors) mirrors C0's `classifyStmt` (`test/Eval/Plan/ContractTest.lean`) exactly — the first
    rejected sub-construct determines the reported category. `scatter`/`recurMorphism` are rejected
    outright, without inspecting their slots/payload, matching C0's `classifyStmt` too. -/
def checkStmt : Stmt → Except CapabilityError Unit
  | .assign nm slots rhs => do
      for s in slots do checkLHSSlot nm s
      checkAggOp nm rhs.agg
      checkNonlin nm rhs.nonlin
      for t in rhs.body.terms do
        for f in t.factors do checkFactor nm f
  | .scatter nm .. => throw (.scatterOrAffineLhs nm)
  | .recurMorphism nm .. => throw (.recurrenceOrCallback nm)

def checkScanStmt : ScanStmt → Except CapabilityError Unit
  | .plain s      => checkStmt s
  | .scan nm ..   => throw (.scanNode nm)
  | .scanPre nm .. => throw (.scanNode nm)

/-- Capability preflight over a whole `ScheduledProgram`: decls in order, then stmts in order, first
    failure wins. `unsupportedDtype`/`dynamicShape` are never thrown below — see `CapabilityError`'s
    doc comment for why they are structurally unreachable from this entry point specifically. -/
def capabilityPreflight (sched : ScheduledProgram) : Except CapabilityError Unit := do
  for d in sched.decls do checkDecl d
  for s in sched.stmts do checkScanStmt s

open Std
open LeanNCD.Eval (ShapeError EvalWarning EvalError EvalFailure termAxisUIDs)

private def liftCapability (warnings : List EvalWarning) :
    Except CapabilityError α → Except PlanCompileFailure α
  | .ok a => .ok a
  | .error e => .error { cause := .capability e, warnings }

private def liftShape (warnings : List EvalWarning) :
    Except ShapeError α → Except PlanCompileFailure α
  | .ok a => .ok a
  | .error e => .error { cause := .shape e, warnings }

private def liftPlanError (warnings : List EvalWarning) :
    Except PlanStepError α → Except PlanCompileFailure α
  | .ok a => .ok a
  | .error e => .error { cause := .invalidPlan e, warnings }

private def liftBindings (warnings : List EvalWarning) :
    Except BindingsError α → Except PlanCompileFailure α
  | .ok a => .ok a
  | .error e => .error { cause := .bindings e, warnings }

/-- External names in first-seen-read order, restricted to `sched.extNames`. NOT `sched.decls`
    filtered to `extNames` (see Global Constraints — an implicitly-external, never-`Decl`ared name
    would be silently dropped), and NOT `sched.extNames.toList` (noncomputable — `Finset.toList`
    needs `Classical.choice`). Mirrors `Lowering.lean`'s own `buildExtIndex` idiom (same traversal,
    same "membership decidable, order from traversal" pattern), returning the ordered `List String`
    directly instead of a name→index `HashMap`. -/
def orderedExtNames (sched : ScheduledProgram) : List String :=
  sched.stmts.foldl (fun acc sc =>
    sc.reads.foldl (fun acc nm =>
      if decide (nm ∈ sched.extNames) && !acc.contains nm then acc ++ [nm] else acc) acc)
    ([] : List String)

/-- Unreachable post-preflight: `checkLHSSlot` (Step A) already rejects every non-`.free` slot
    (`freeNorm`/`iterAt`/`iterNext` via `unsupportedLhsSlot`, `affine` via `scatterOrAffineLhs`)
    before `prepareEvalPlan` ever calls this. Kept total for the same reason as
    `plainStmtOrFail`/`assignPartsOrFail` above. -/
private def freeUidOrFail (context : String) : LHSSlot → Except CapabilityError UID
  | .free a => pure a.uid
  | .freeNorm _ | .iterAt .. | .iterNext _ => throw (.unsupportedLhsSlot context)
  | .affine _ => throw (.scatterOrAffineLhs context)

/-- Unreachable post-preflight: `checkScanStmt` (Step A) already rejects `.scan`/`.scanPre` via
    `scanNode` before `prepareEvalPlan` ever calls this — same "Step A already rejected these"
    pattern as the `flatStmts` filter a few lines below `capabilityPreflight`. Kept total (rather
    than assuming `.plain` via a partial match) so a future `ScanStmt` constructor is a compile
    error here, not a silent fallthrough. -/
private def plainStmtOrFail (context : String) : ScanStmt → Except CapabilityError Stmt
  | .plain s => pure s
  | .scan .. | .scanPre .. => throw (.scanNode context)

/-- Unreachable post-preflight: `checkStmt` (Step A) already rejects `.scatter`/`.recurMorphism`
    outright (`scatterOrAffineLhs`/`recurrenceOrCallback`) before `prepareEvalPlan` ever calls this.
    Kept total for the same reason as `plainStmtOrFail` above. -/
private def assignPartsOrFail (context : String) : Stmt →
    Except CapabilityError (String × List LHSSlot × RHSExpr)
  | .assign nm slots rhs => pure (nm, slots, rhs)
  | .scatter .. => throw (.scatterOrAffineLhs context)
  | .recurMorphism .. => throw (.recurrenceOrCallback context)

/-- Fail loud on an unsized axis rather than defaulting to 0 — a naive `sizes[uid]?.getD 0` would
    silently produce a wrong-shaped (usually zero-extent) plan on a program the legacy evaluator
    correctly fails on. Not in the original algorithm sketch; added while verifying this task. -/
private def resolveSizeOrFail (sizes : HashMap UID Nat) (site : UnsizedAxisSite) (uid : UID) :
    Except ShapeError Nat :=
  match sizes[uid]? with
  | some n => pure n
  | none => throw (.unsizedAxis uid site)

/-- Fold every pinned axis's contribution into `row`'s bias and drop it from both the coefficient
    row and the basis, preserving the relative order of the remaining positions. `row` must be
    `idxToRow basis e` for some `e` — one coefficient per `basis` position. This is proposal
    §4.4's base-assignment pin substitution ("substitute every `iterAt` pin into every normalized
    RHS affine row; add every pinned coefficient's contribution to the bias; remove pinned UIDs
    from the residual basis"), generalized over any pin set so `residualizeAssignment` below can
    serve both an empty-pin plain caller (this task) and a future non-empty-pin base caller
    (Task 3) with the same code. -/
private def substitutePins (pins : HashMap UID Int) (basis : List UID) (row : List Int × Int) :
    List Int × Int :=
  let (coeffs, bias) := row
  let indexed := basis.zip coeffs
  let extraBias := indexed.foldl (fun acc (u, c) => acc + (pins[u]?).getD 0 * c) 0
  let residualCoeffs := indexed.filterMap (fun (u, c) => if (pins[u]?).isSome then none else some c)
  (residualCoeffs, bias + extraBias)

/-- Hand-worked sanity check (proposal §4.4's own worked example): pinning `u := 5` into
    `7 + 2u - 3v + 4u` over basis `[u, v]` leaves residual basis `[v]`, coefficient row `[-3]`
    (`2 + 4 = 6` on `u`, dropped), bias `7 + 6·5 = 37`. Checked directly here (`substitutePins` is
    `private`, so only this file can reach it) rather than deferred to Task 3, whose base-write
    caller is the first real, non-empty-pin CALLER of `residualizeAssignment` — but not the first
    correctness check of the substitution arithmetic itself. -/
private def pinCheckU : AxisSpec := { name := "u", uid := 9001, kind := .nat }
private def pinCheckV : AxisSpec := { name := "v", uid := 9002, kind := .nat }
#guard substitutePins (({} : HashMap UID Int).insert pinCheckU.uid 5) [pinCheckU.uid, pinCheckV.uid]
    (idxToRow [pinCheckU.uid, pinCheckV.uid]
      (.affine 7 [(2, pinCheckU), (-3, pinCheckV), (4, pinCheckU)]))
  == ([-3], 37)

/-- The common per-statement assignment residualization core (Wave F F4 Task 2): given a
    statement's scan context (empty outside a scan step), its output (retained) basis, validated
    pins, a source-name-to-`(slot, shape)` resolver, and an already-allocated destination
    slot/shape, lower `terms` into an `AssignPlan`. Per proposal §4.4's ordered-basis table, each
    term's basis is `context ++ output ++ reduction`, where `reduction` is THAT TERM's own
    contracted axes (`termAxisUIDs` minus context/output — per-term, not per-statement, exactly as
    `prepareEvalPlan`'s Step D always computed it) with any pinned axis substituted out via
    `substitutePins`.

    Constructs only the `AssignPlan` value. It deliberately does NOT touch the caller's name
    environment (`slotOf`/`tensorSigsAcc`/`materializedAcc`): the plain-assignment caller below and
    Task 3's future scan base/step callers publish produced names under different rules (a scan
    step's coupled-state results, for instance, must not be visible to each other mid-block), so
    publication policy stays with each caller, not this shared core.

    Precondition (caller's responsibility, not re-validated here): `pins`' keys are disjoint from
    both `contextUids` and `outputUids` — a "validated pin" is exactly one that names neither a
    scan-context nor an output axis, by construction of whoever builds the pin set. Violating this
    would desync `outputPos`/`reductionPos` (computed from `outputUids`/`reduction`'s own lengths)
    from `iterationShape` (computed from the pin-filtered residual basis). -/
private def residualizeAssignment (sizes : HashMap UID Nat) (warnings : List EvalWarning)
    (stmtName : String) (contextUids : List UID) (contextShape : Array Nat)
    (outputUids : List UID) (pins : HashMap UID Int)
    (resolveSource : String → TensorSlot × Array Nat)
    (destSlot : TensorSlot) (outputShape : Array Nat) (terms : List ProdTerm) :
    Except PlanCompileFailure AssignPlan := do
  let mut termsAcc : Array TermPlan := #[]
  for term in terms do
    let termUids := (termAxisUIDs term).eraseDups
    let contractedUids :=
      termUids.filter (fun u => !contextUids.contains u && !outputUids.contains u)
    let basisUids := contextUids ++ outputUids ++ contractedUids
    let reductionUids := contractedUids.filter (fun u => (pins[u]?).isNone)
    let residualUids := contextUids ++ outputUids ++ reductionUids
    let iterationShape ←
      liftShape warnings (residualUids.toArray.mapM (resolveSizeOrFail sizes (.assignContracted stmtName)))
    let contextPos : Array Nat := Array.range contextUids.length
    let outputPos : Array Nat := (Array.range outputUids.length).map (· + contextUids.length)
    let reductionPos : Array Nat :=
      (Array.range reductionUids.length).map (· + contextUids.length + outputUids.length)
    let mut factorsAcc : Array ReadPlan := #[]
    for factor in term.factors do
      match factor with
      | .read name idxs =>
          -- resolved against the caller's name environment as it stood BEFORE this statement's
          -- destination slot was allocated — see the caller for why `getD`/its resolver default is
          -- never actually reached.
          let (sourceSlot, sourceShape) := resolveSource name
          let rows := idxs.map (fun e => substitutePins pins basisUids (idxToRow basisUids e))
          let coeffs : Array (Array Int) := (rows.map (fun r => r.1.toArray)).toArray
          let biasArr : Array Int := (rows.map (fun r => r.2)).toArray
          factorsAcc := factorsAcc.push
            { sourceSlot, map := { coeffs, bias := biasArr }, sourceShape, oobPolicy := .zeroPad }
      | .iverson _ => liftCapability warnings (throw (.maskOrPredicate "factor"))
          -- unreachable post-preflight (checkFactor/Step A already rejected .iverson)
      | .unaryFn .. => liftCapability warnings (throw (.unaryFactor "factor"))
          -- unreachable post-preflight (checkFactor/Step A already rejected .unaryFn)
    termsAcc := termsAcc.push
      { iterationShape, contextPos, outputPos, reductionPos, factors := factorsAcc }
  return { contextShape, destinationSlot := destSlot, outputShape, terms := termsAcc
          , algebra := admittedAlgebra }

def prepareEvalPlan (sched : ScheduledProgram) (sig : InputSignature) :
    Except PlanCompileFailure PreparedPlan := do
  -- Step A: capability preflight.
  match capabilityPreflight sched with
  | .error e => throw { cause := .capability e, warnings := [] }
  | .ok () => pure ()
  -- Step B: input signature validation, in first-seen-read order.
  let extOrder := orderedExtNames sched
  for nm in extOrder do
    match sig.tensors[nm]? with
    | none => throw { cause := .inputSignature (.missingSignature nm), warnings := [] }
    | some ts =>
        unless ts.dtype == .f64 do
          throw { cause := .inputSignature (.dtypeNotAdmitted nm ts.dtype), warnings := [] }
  -- Step C: shape inference.
  let flatStmts : List Stmt := sched.stmts.flatMap (fun
    | .plain s => [s]
    | .scan .. | .scanPre .. => [])   -- unreachable post-preflight (Step A already rejected these)
  let (sizes, warnings) ← match inferAxisSizesFromSignature sched.explicitSizes sig flatStmts with
    | .ok r => pure r
    | .error f =>
        match f.error with
        | .shape cause => throw { cause := .shape cause, warnings := f.warnings }
        | _ =>
            -- Unreachable given the current implementation (every throw site in `SizeInfer.lean`/
            -- `SizeSolve.lean` is `.shape`-tagged) — narrow fallback rather than widening
            -- `PlanCompileCause.shape`'s field type, which would destroy `DecidableEq`/`BEq` on
            -- every `PlanCompileCause` arm, not just this one.
            throw { cause := .shape (.solveFailure { kind := .inconsistent, detail? := some "unreachable: non-.shape EvalError from shape inference" })
                   , warnings := f.warnings }
  -- Step D: slot allocation + per-statement/per-term compilation, interleaved.
  let mut slotOf : HashMap String TensorSlot := {}
  let mut tensorSigsAcc : Array TensorSignature := #[]
  let mut inputSlotsAcc : Array TensorSlot := #[]
  let mut requiredInputsAcc : Array SlotBinding := #[]
  for nm in extOrder do
    -- validated present + f64 in Step B; `getD` avoids needing `Inhabited TensorSignature`
    -- (mirrors `runDensePlan`'s identical idiom in `Dense.lean`).
    let ts := sig.tensors.getD nm { shape := #[], dtype := .f64 }
    let slot := tensorSigsAcc.size
    tensorSigsAcc := tensorSigsAcc.push { shape := ts.shape, dtype := .f64 }
    slotOf := slotOf.insert nm slot
    inputSlotsAcc := inputSlotsAcc.push slot
    requiredInputsAcc := requiredInputsAcc.push { name := nm, slot := slot }
  let mut stepsAcc : Array AssignPlan := #[]
  let mut materializedAcc : Array SlotBinding := #[]
  for sc in sched.stmts do
    let s ← liftCapability warnings (plainStmtOrFail "stmt" sc)
    let (nm, slots, rhs) ← liftCapability warnings (assignPartsOrFail "stmt" s)
    let retainedUids ← liftCapability warnings (slots.mapM (freeUidOrFail "lhs"))
    let outputShape ←
      liftShape warnings (retainedUids.toArray.mapM (resolveSizeOrFail sizes (.assignOutput nm)))
    -- name-environment mutation (`slotOf`/`tensorSigsAcc`/`materializedAcc`) is this plain caller's
    -- own publication policy — `residualizeAssignment` only builds the `AssignPlan` value, per its
    -- own doc comment.
    let destSlot := tensorSigsAcc.size
    let resolveSource (name : String) : TensorSlot × Array Nat :=
      -- resolved against `slotOf` as it stands BEFORE this statement's destination slot is
      -- allocated. `getD` default is never reached: every read name is either external (allocated
      -- above) or produced by an earlier statement (schedule is topological, per
      -- `ScheduledProgram.stmts`'s own doc: "producers precede consumers").
      let sourceSlot := slotOf.getD name 0
      (sourceSlot, (tensorSigsAcc.getD sourceSlot { shape := #[], dtype := .f64 }).shape)
    -- plain assignment: empty scan context, no pins — reproduces this Step D's pre-extraction
    -- behavior exactly (Task 2's whole point; see `residualizeAssignment`'s doc comment).
    let assignPlan ←
      residualizeAssignment sizes warnings nm [] #[] retainedUids ({} : HashMap UID Int)
        resolveSource destSlot outputShape rhs.body.terms
    tensorSigsAcc := tensorSigsAcc.push { shape := outputShape, dtype := .f64 }
    stepsAcc := stepsAcc.push assignPlan
    materializedAcc := materializedAcc.push { name := nm, slot := destSlot }
    slotOf := slotOf.insert nm destSlot
  -- Step E: assemble and check. This should ALWAYS succeed for a schedule that passed capability
  -- preflight — if `checkPlan` ever rejects a compiler-generated plan, that is a bug in the
  -- compiler above, not a legitimate rejection.
  let raw : RawEvalPlan :=
    { tensorSigs := tensorSigsAcc, inputSlots := inputSlotsAcc
    , steps := stepsAcc.map .assign, numericMode := .reference64SumProduct }
  let checked ← liftPlanError warnings (checkPlan raw)
  -- Step F: assemble PreparedPlan. `requiredInputsAcc`/`inputSlotsAcc` were built positionally
  -- (hence also as a permutation) in lockstep by the same Step D loop above, so `checkBindings`
  -- should never actually reject compiler-produced input — same "this should ALWAYS succeed" spirit
  -- as `checkPlan` just above, wired through the same `lift*` pattern regardless.
  let requiredInputs ← liftBindings warnings (checkBindings inputSlotsAcc requiredInputsAcc)
  return { plan := checked
         , bindings := { requiredInputs, materializedNames := materializedAcc }
         , warnings }

end LeanNCD.Eval.Plan
