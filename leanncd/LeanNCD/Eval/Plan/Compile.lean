import LeanNCD.DSL.Ast
import LeanNCD.DSL.Pipeline.Types
import LeanNCD.Eval.Plan.Error
import LeanNCD.Eval.Plan.Prepared
import LeanNCD.Eval.Plan.Signature
import LeanNCD.Eval.Contract
import LeanNCD.DSL.Pipeline.Lowering

/-!
# Wave C source compiler: capability preflight (C4)

Ports C0's already-verified classification logic (`PlanContract.classify*`,
`test/Eval/Plan/ContractTest.lean`) from test-only `Classification`-valued classifiers into a real
production entry point that throws `CapabilityError`. No `PreparedPlan`, slot allocation, or shape
inference here — this file holds only capability preflight; Task 2 grows it.
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
    Except PlanError α → Except PlanCompileFailure α
  | .ok a => .ok a
  | .error e => .error { cause := .invalidPlan e, warnings }

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
    let mut termsAcc : Array TermPlan := #[]
    for term in rhs.body.terms do
      let termUids := (termAxisUIDs term).eraseDups
      let contractedUids := termUids.filter (fun u => !retainedUids.contains u)
      let basisUids := retainedUids ++ contractedUids
      let iterationShape ←
        liftShape warnings (basisUids.toArray.mapM (resolveSizeOrFail sizes (.assignContracted nm)))
      let outputPos : Array Nat := Array.range retainedUids.length
      let reductionPos : Array Nat :=
        (Array.range basisUids.length).extract retainedUids.length basisUids.length
      let mut factorsAcc : Array ReadPlan := #[]
      for factor in term.factors do
        match factor with
        | .read name idxs =>
            -- resolved against `slotOf` as it stands BEFORE this statement's destination slot is
            -- allocated. `getD` default is never reached: every read name is either external
            -- (allocated above) or produced by an earlier statement (schedule is topological, per
            -- `ScheduledProgram.stmts`'s own doc: "producers precede consumers").
            let sourceSlot := slotOf.getD name 0
            let sourceSig := tensorSigsAcc.getD sourceSlot { shape := #[], dtype := .f64 }
            let rows := idxs.map (idxToRow basisUids)
            let coeffs : Array (Array Int) := (rows.map (fun r => r.1.toArray)).toArray
            let biasArr : Array Int := (rows.map (fun r => r.2)).toArray
            factorsAcc := factorsAcc.push
              { sourceSlot, map := { coeffs, bias := biasArr }, sourceShape := sourceSig.shape
              , oobPolicy := .zeroPad }
        | .iverson _ => liftCapability warnings (throw (.maskOrPredicate "factor"))
            -- unreachable post-preflight (checkFactor/Step A already rejected .iverson)
        | .unaryFn .. => liftCapability warnings (throw (.unaryFactor "factor"))
            -- unreachable post-preflight (checkFactor/Step A already rejected .unaryFn)
      termsAcc := termsAcc.push
        { iterationShape, outputPos, reductionPos, factors := factorsAcc }
    let destSlot := tensorSigsAcc.size
    tensorSigsAcc := tensorSigsAcc.push { shape := outputShape, dtype := .f64 }
    stepsAcc := stepsAcc.push
      { destinationSlot := destSlot, outputShape, terms := termsAcc, algebra := admittedAlgebra }
    materializedAcc := materializedAcc.push { name := nm, slot := destSlot }
    slotOf := slotOf.insert nm destSlot
  -- Step E: assemble and check. This should ALWAYS succeed for a schedule that passed capability
  -- preflight — if `checkPlan` ever rejects a compiler-generated plan, that is a bug in the
  -- compiler above, not a legitimate rejection.
  let raw : RawEvalPlan :=
    { version := admittedVersion, tensorSigs := tensorSigsAcc, inputSlots := inputSlotsAcc
    , steps := stepsAcc, numericMode := .reference64 }
  let checked ← liftPlanError warnings (checkPlan raw)
  -- Step F: assemble PreparedPlan.
  return { plan := checked
         , bindings := { requiredInputs := requiredInputsAcc, materializedNames := materializedAcc }
         , warnings }

end LeanNCD.Eval.Plan
