import LeanNCD.DSL.Ast
import LeanNCD.DSL.Pipeline.Types
import LeanNCD.Eval.Plan.Error
import LeanNCD.Eval.Plan.Prepared
import LeanNCD.Eval.Plan.EvalPlan
import LeanNCD.Eval.Plan.Signature
import LeanNCD.Eval.Contract
import LeanNCD.DSL.Pipeline.Lowering

/-!
# Source compiler: capability preflight (Wave C C4) and scan specialization (Wave F F4)

Ports C0's already-verified classification logic (`PlanContract.classify*`,
`test/Eval/Plan/ContractTest.lean`) and F0's scan classification
(`PlanContract.WaveF.classifyScan*`, `test/Eval/Plan/ScanContractTest.lean`) from test-only
`Classification`-valued classifiers into real production entry points that throw `CapabilityError`.

`prepareEvalPlan` runs the phases proposal §7.5 fixes, in this order and no other: capability
preflight (A), external signature validation (B), static shape inference over plain AND scan
base/recurrence assignments (C), source-ordered specialization (D), checked-plan validation (E),
and bindings (F). Per-statement assignment residualization is shared by all three assignment kinds
through `residualizeAssignment` (F4 Task 2); `compileScan` (F4 Task 3) adds everything a scan needs
around it — state/scratch classification, geometry, captures, write maps, and the source-facing
`ScanCompileError` validation that must precede `checkScanPlan` so a checker rejection stays what it
is meant to be: a compiler bug, reported as `invalidPlan`.
-/

namespace LeanNCD.Eval.Plan

/-- Axis declarations (`.axis`, `.iter`) are structurally accepted regardless of use — rejection for
    scan usage happens at the `ScanStmt` check below, not at the declaring axis. `.freeNorm` usage is
    likewise checked at the `LHSSlot` check below, but (Thread 4) only rejected there for a
    scan-block statement — a top-level `.freeNorm` is now admitted (`checkLHSSlot`). -/
def checkDecl : Decl → Except CapabilityError Unit
  | .tensor ..    => pure ()
  | .linear ..    => pure ()
  | .predicate n _ => throw (.booleanOutput n)
  | .axis ..      => pure ()
  | .iter ..      => pure ()

/-- `.freeNorm` is admitted structurally here (Thread 4): a plain statement's LHS may now carry a
    `·`-marked reduction axis. Whether that marker actually agrees with the statement's own
    `Nonlin` (present exactly once, only on an unmasked `.axiswise`) is NOT this checker's job — it
    needs the whole slot list against the statement's `Nonlin`, which preflight (per-slot, no
    `Nonlin` in scope) cannot see. That agreement is `resolveNonlinAxis`'s job, at compile tier. -/
def checkLHSSlot (stmtName : String) : LHSSlot → Except CapabilityError Unit
  | .free _     => pure ()
  | .freeNorm _ => pure ()
  | .iterAt a _ => throw (.unsupportedLhsSlot s!"{stmtName}: iterAt {a.name}")
  | .iterNext a => throw (.unsupportedLhsSlot s!"{stmtName}: iterNext {a.name}")
  | .affine _   => throw (.scatterOrAffineLhs s!"{stmtName}: affine LHS slot")

def checkFactor (stmtName : String) : Factor → Except CapabilityError Unit
  | .read ..       => pure ()
  | .iverson _     => throw (.maskOrPredicate s!"{stmtName}: iverson factor")
  | .unaryFn _ n _ => throw (.unaryFactor s!"{stmtName}: unary function on {n}")

/-- Top-level (`.plain`) statement admission (Thread 4): `.pointwise`/`.axiswise` are now
    structurally admitted — `prepareEvalPlan`'s `.plain` branch compiles them into a real
    `.assign → .pointwise`/`.axiswise` chain. Whether a given statement's LHS slots actually agree
    with its `Nonlin` (a `·`-marked axis present exactly once, iff `.axiswise` and unmasked) is
    NOT checked here — that needs the whole slot list, checked once by `resolveNonlinAxis` at
    compile tier, not duplicated at preflight. -/
def checkNonlinTopLevel (_stmtName : String) : Nonlin → Except CapabilityError Unit
  | .identity    => pure ()
  | .pointwise _ => pure ()
  | .axiswise .. => pure ()

/-- Scan-block (`base`/`recur`) statement admission: unchanged from Wave C — `.pointwise`/
    `.axiswise` inside a scan block stay rejected, since Thread 4's compilation (Task 3) only
    targets `prepareEvalPlan`'s `.plain` branch, not `compileScan`. -/
def checkNonlinScanBlock (stmtName : String) : Nonlin → Except CapabilityError Unit
  | .identity    => pure ()
  | .pointwise _ => throw (.unsupportedNonlin s!"{stmtName}: pointwise nonlinearity")
  | .axiswise .. => throw (.unsupportedNonlin s!"{stmtName}: axiswise nonlinearity")

def checkAggOp (stmtName : String) : AggOp → Except CapabilityError Unit
  | .sum => pure ()
  | .max => throw (.unsupportedAgg s!"{stmtName}: max aggregation")
  | .min => throw (.unsupportedAgg s!"{stmtName}: min aggregation")

/-- One `Stmt`'s capability check. Sub-construct order (LHS slots, then `agg`, then `nonlin`, then
    factors) mirrors C0's `classifyStmt` (`test/Eval/Plan/ContractTest.lean`) — the first rejected
    sub-construct determines the reported category. This is no longer an exact mirror for the
    `nonlin` sub-construct specifically: C0's frozen `classifyNonlin` still rejects
    `.pointwise`/`.axiswise` outright, while this function's own `checkNonlinTopLevel` (Thread 4)
    admits both at top level. `scatter`/`recurMorphism` are rejected outright, without inspecting
    their slots/payload, matching C0's `classifyStmt` too. -/
def checkStmt : Stmt → Except CapabilityError Unit
  | .assign nm slots rhs => do
      for s in slots do checkLHSSlot nm s
      checkAggOp nm rhs.agg
      checkNonlinTopLevel nm rhs.nonlin
      for t in rhs.body.terms do
        for f in t.factors do checkFactor nm f
  | .scatter nm .. => throw (.scatterOrAffineLhs nm)
  | .recurMorphism nm .. => throw (.recurrenceOrCallback nm)

/-- The scan-context analogue of `checkLHSSlot`: inside a `.scan` node's own `base`/`recur` lists,
    `.iterAt`/`.iterNext` are the very constructors that MAKE it a scan, so both are admitted here.
    `.affine` stays rejected exactly as for a plain statement. `.freeNorm` is now (Thread 4) treated
    DIFFERENTLY from a plain statement: `checkLHSSlot` admits a top-level `.freeNorm`, but this
    function still rejects it inside a scan block — nonlinearity compilation (Task 3) only targets
    `prepareEvalPlan`'s `.plain` branch, not `compileScan`. Ported from F0's
    verified `PlanContract.WaveF.classifyScanLHSSlot` (`test/Eval/Plan/ScanContractTest.lean`), same
    constructor order, `Classification` replaced by a real `CapabilityError`.

    Deliberately does NOT replace `checkLHSSlot`: a genuinely plain (non-scan) statement using
    `.iterAt`/`.iterNext` is still Wave C's `unsupportedLhsSlot`, since outside a scan node there is
    no recurrence context to give either slot a meaning. The two rules coexist; which one applies is
    decided by `checkScanStmt`'s constructor, not by inspecting the slot. -/
def checkScanLHSSlot (stmtName : String) : LHSSlot → Except CapabilityError Unit
  | .free _     => pure ()
  | .freeNorm a => throw (.unsupportedLhsSlot s!"{stmtName}: freeNorm {a.name}")
  | .iterAt ..  => pure ()
  | .iterNext _ => pure ()
  | .affine _   => throw (.scatterOrAffineLhs s!"{stmtName}: affine LHS slot")

/-- One base/recurrence statement's capability check: the same sub-construct order `checkStmt`
    applies to a plain assignment (LHS slots, then `agg`, then `nonlin`, then factors), with
    `checkScanLHSSlot` in place of `checkLHSSlot`. The `nonlin` sub-check itself now (Thread 4)
    differs from a plain statement's: `checkNonlinScanBlock` still rejects `.pointwise`/`.axiswise`
    inside a scan block, where `checkStmt`'s `checkNonlinTopLevel` admits both — `agg` and factor
    checking stay identical. Ported from F0's `classifyScanBlockStmt`.

    **Necessary, not sufficient** — and deliberately so. Like F0's classifier, this is applied
    uniformly to `base ++ recur`, so it does NOT check that a base statement uses `.iterAt` rather
    than `.iterNext` (or vice versa for recurrence), nor that each state has exactly one all-axis
    `.iterNext` result. Those need the scan's context-axis list and, for extents/geometry, inferred
    sizes — neither available at preflight — so they belong to `compileScan`'s `ScanCompileError`
    tier further down this file, not here. -/
def checkScanBlockStmt : Stmt → Except CapabilityError Unit
  | .assign nm slots rhs => do
      for s in slots do checkScanLHSSlot nm s
      checkAggOp nm rhs.agg
      checkNonlinScanBlock nm rhs.nonlin
      for t in rhs.body.terms do
        for f in t.factors do checkFactor nm f
  | .scatter nm .. => throw (.scatterOrAffineLhs nm)
  | .recurMorphism nm .. => throw (.recurrenceOrCallback nm)

/-- Whole-`ScanStmt` capability check. `.plain` is unchanged Wave C. A `.scan` is now admitted
    syntactically (F4) when it declares at least one advancing axis and every base/recurrence
    statement individually passes `checkScanBlockStmt` — `base ++ recur` in that order, so the first
    rejected statement in source order wins. `.scanPre` remains rejected, but as
    `recurrenceOrCallback` rather than `scanNode`: its payload is a pre-built step morphism (the
    `Stmt.recurMorphism` escape hatch), which is precisely what that existing constructor already
    names for the un-grouped form — reusing it rather than adding a second constructor for the same
    concept (proposal §5.2, plan §4.1).

    `scanNode` therefore has no producer left in this file. It is retained on `CapabilityError`
    because a `RawEvalPlan`/`PreparedPlan` consumer may still hold a serialized Wave C rejection
    carrying it, and because deleting a shipped closed-family constructor is itself a semantic
    version change (§9.2's discipline). -/
def checkScanStmt : ScanStmt → Except CapabilityError Unit
  | .plain s      => checkStmt s
  | .scan nm axes base recur _ => do
      if axes.isEmpty then throw (.noAdvancingAxis nm)
      for s in base ++ recur do checkScanBlockStmt s
  | .scanPre nm .. => throw (.recurrenceOrCallback nm)

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

private def liftNonlin (warnings : List EvalWarning) :
    Except NonlinCompileError α → Except PlanCompileFailure α
  | .ok a => .ok a
  | .error e => .error { cause := .nonlin e, warnings }

/-- The `throw`-site counterpart of the `lift*` family above, for the one phase that raises its own
    errors directly rather than adapting another checker's `Except`: `compileScan` builds a
    `ScanCompileError` at dozens of sites and has no upstream `Except` to lift, so a value
    constructor reads better there than a `lift` wrapper around `throw`. -/
private def scanErr (warnings : List EvalWarning) (e : ScanCompileError) : PlanCompileFailure :=
  { cause := .scan e, warnings }

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

/-- The retained placement axis of a plain statement's LHS slot — `.free` and, since Thread 4's
    `checkLHSSlot` relaxation, `.freeNorm` alike (a `·`-marked axis is still a real output axis;
    `resolveNonlinAxis` is what checks its marking agrees with the statement's `Nonlin`, not this
    function). `.iterAt`/`.iterNext`/`.affine` remain unreachable post-preflight **at this
    function's only call site**, `prepareEvalPlan`'s PLAIN-statement branch: `checkLHSSlot`
    (Step A) already rejects them for a plain statement (`iterAt`/`iterNext` via
    `unsupportedLhsSlot`, `affine` via `scatterOrAffineLhs`) before `prepareEvalPlan` ever calls
    this. Deliberately NOT reused by `compileScan`: inside a scan block `.iterAt`/`.iterNext` are
    admitted (`checkScanLHSSlot`) and carry real meaning, so a scan's LHS slots are destructured
    there against the scan's own context axes rather than collapsed to "free UID or fail". Kept
    total for the same reason as `assignPartsOrFail` below. -/
private def freeUidOrFail (context : String) : LHSSlot → Except CapabilityError UID
  | .free a => pure a.uid
  | .freeNorm a => pure a.uid
  | .iterAt .. | .iterNext _ => throw (.unsupportedLhsSlot context)
  | .affine _ => throw (.scatterOrAffineLhs context)

/-- Unreachable post-preflight: `checkStmt`/`checkScanBlockStmt` (Step A) already reject
    `.scatter`/`.recurMorphism` outright (`scatterOrAffineLhs`/`recurrenceOrCallback`) before
    `prepareEvalPlan` ever calls this — for a plain statement AND for every base/recurrence statement
    inside an admitted `.scan`, which is why `compileScan` reuses this same helper rather than
    repeating the destructuring. Kept total (rather than assuming `.assign` via a partial match) so a
    future `Stmt` constructor is a compile error here, not a silent fallthrough. -/
private def assignPartsOrFail (context : String) : Stmt →
    Except CapabilityError (String × List LHSSlot × RHSExpr)
  | .assign nm slots rhs => pure (nm, slots, rhs)
  | .scatter .. => throw (.scatterOrAffineLhs context)
  | .recurMorphism .. => throw (.recurrenceOrCallback context)

/-- The placement axis of one scan-block LHS slot. Unreachable `none` post-preflight
    (`checkScanLHSSlot` rejects `.affine`), so this is the scan-block analogue of
    `freeUidOrFail`'s totality guard — but it keeps the whole `AxisSpec` and the slot's own kind for
    the caller to dispatch on, which is exactly the information a scan needs and a plain statement
    does not. -/
private def scanSlotAxisOrFail (context : String) (sl : LHSSlot) :
    Except CapabilityError AxisSpec :=
  match sl.axisSpec? with
  | some a => pure a
  | none => throw (.scatterOrAffineLhs context)

/-- First UID that recurs later in the list. Mirrors `Prepared.lean`'s `firstDuplicateName` and
    `Block.lean`'s `firstDuplicateSlot` (same shape, different element type) so a duplicate-axis
    rejection can name the offending axis rather than merely reporting that one exists. -/
private def firstDuplicateUID : List UID → Option UID
  | [] => none
  | u :: rest => if rest.contains u then some u else firstDuplicateUID rest

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

/-- One compiled source scan: the raw scan node, plus the persistent states' source names and
    complete-history shapes in persistent-state order. The two arrays are returned rather than the
    outer signature/name-environment updates themselves because publication is the CALLER's policy
    (same division of labour `residualizeAssignment` already establishes): `compileScan` fixes the
    state destination slots as `outerSigs.size + i` and the caller must append exactly those
    signatures, in exactly this order, immediately after the scan step. A desync would not be silent
    — `checkPlan`/`checkScanPlan` reject it (`slotOutOfRange`, `missingProduction`, or
    `advancingSizeMismatch`) — but the coupling is stated here rather than left to be rediscovered. -/
private structure CompiledScan where
  raw         : RawScanPlan
  stateNames  : Array String
  stateShapes : Array (Array Nat)

/-- Specialize one admitted source `.scan` node into a `RawScanPlan` (proposal §8.3-§8.5).

    **Classification is name-blind and accessor-blind** (plan §4.2). `scanName` is the scheduled
    scan's representative name; it is used ONLY as a diagnostic label inside `ScanCompileError`
    values and never to decide what a state is. `ScanStmt.outputs`/`ScanStmt.writes` are likewise
    never consulted: `.outputs` keeps only names written by BOTH lists (dropping a state whose
    recurrence result was renamed) and both `eraseDups` away the multiplicity a state split across
    several base writes needs. Persistent state is derived here from `base`/`recur` directly — every
    base destination name, in source order, is a state candidate; each needs exactly one recurrence
    result whose LHS advances EVERY context axis.

    **Preflight is necessary, not sufficient**, which is why this function exists at all:
    `checkScanBlockStmt` admits `.iterAt`/`.iterNext` uniformly across `base ++ recur` without
    knowing which list a statement came from, how many context axes there are, or any extent. Base/
    recurrence slot discipline, state pairing, geometry, base-write placement, and causality are all
    settled here, at `ScanCompileError` tier, against inferred `sizes`.

    **Two size maps, deliberately.** `sizes` holds each axis's SOURCE extent; a scan context axis's
    source extent is its full history length `N`, but a step assignment iterates the `N - 1`
    transitions. Step lowering therefore runs against `stepSizes` — `sizes` with every context axis
    overridden to `stepExtents` — so each term's `iterationShape` at a context position is `N - 1`
    and `checkAssign`'s `contextProjection == contextShape` holds. Base lowering keeps plain `sizes`:
    a base block has no context, and a base write's free face over a context axis (`dp[0, c]`)
    genuinely spans the FULL history extent. Reads are unaffected either way — affine rows come from
    `idxToRow`, not from sizes — so an external read `X[l]` still gathers `X` at the current
    coordinate with its own declared `sourceShape`. -/
private def compileScan (sizes : HashMap UID Nat) (warnings : List EvalWarning)
    (scanName : String) (axes : List AxisSpec) (base recur : List Stmt)
    (outerSigs : Array TensorSignature) (slotOf : HashMap String TensorSlot) :
    Except PlanCompileFailure CompiledScan := do
  ---------------------------------------------------------------------------
  -- Phase 0: context axes and extents.
  ---------------------------------------------------------------------------
  let axesA : Array AxisSpec := axes.toArray
  let ctxUids : List UID := axes.map (·.uid)
  match firstDuplicateUID ctxUids with
  | some u =>
      throw (scanErr warnings
        (.duplicateContextAxis scanName ((ctxUids.findIdx? (· == u)).getD 0) u))
  | none => pure ()
  let historyExtents : Array Nat ←
    liftShape warnings (axesA.mapM (fun a => resolveSizeOrFail sizes (.scanIteration a.name) a.uid))
  for h : i in [0 : historyExtents.size] do
    if historyExtents[i] == 0 then
      throw (scanErr warnings (.scanAxisZeroExtent scanName i ((axesA.getD i default).uid)))
  let stepExtents : Array Nat := historyExtents.map (· - 1)
  let numAxes := axesA.size
  let stepSizes : HashMap UID Nat := (Array.range numAxes).foldl
    (fun m i => m.insert (axesA.getD i default).uid (stepExtents.getD i 0)) sizes
  -- context-axis index of a slot's placement axis, if it names one.
  let ctxIndexOf : UID → Option Nat := fun u => ctxUids.findIdx? (· == u)
  ---------------------------------------------------------------------------
  -- Phase 1: destructure, per-statement slot discipline, and state/scratch classification.
  ---------------------------------------------------------------------------
  let baseParts ← liftCapability warnings (base.toArray.mapM (assignPartsOrFail "scan base"))
  let recurParts ←
    liftCapability warnings (recur.toArray.mapM (assignPartsOrFail "scan recurrence"))
  let mut stateNames : Array String := #[]
  for h : bi in [0 : baseParts.size] do
    let (nm, _, _) := baseParts[bi]
    unless stateNames.contains nm do stateNames := stateNames.push nm
  if stateNames.isEmpty then throw (scanErr warnings (.noPersistentState scanName))
  -- base slot discipline: no `.iterNext`, every pin names a context axis, no repeated axis.
  let mut baseOf : HashMap String (Array (Nat × List LHSSlot)) := {}
  for h : bi in [0 : baseParts.size] do
    let (nm, slots, _) := baseParts[bi]
    let slotAxes ← liftCapability warnings (slots.mapM (scanSlotAxisOrFail s!"{nm}: base LHS slot"))
    match firstDuplicateUID (slotAxes.map (·.uid)) with
    | some u => throw (scanErr warnings (.duplicateAxisInLhs scanName nm true bi u))
    | none => pure ()
    for sl in slots do
      match sl with
      | .iterNext a => throw (scanErr warnings (.iterNextInBaseBlock scanName nm bi a.uid))
      | .iterAt a _ =>
          unless (ctxIndexOf a.uid).isSome do
            throw (scanErr warnings (.pinnedAxisNotContext scanName nm bi a.uid))
      | _ => pure ()
    baseOf := baseOf.insert nm ((baseOf.getD nm #[]).push (bi, slots))
  -- recurrence classification: state result (all-axis `.iterNext`) vs block-local scratch.
  let mut resultOf : HashMap String (Nat × List LHSSlot) := {}
  let mut scratchOf : HashMap String Nat := {}
  for h : ri in [0 : recurParts.size] do
    let (nm, slots, _) := recurParts[ri]
    let slotAxes ←
      liftCapability warnings (slots.mapM (scanSlotAxisOrFail s!"{nm}: recurrence LHS slot"))
    match firstDuplicateUID (slotAxes.map (·.uid)) with
    | some u => throw (scanErr warnings (.duplicateAxisInLhs scanName nm false ri u))
    | none => pure ()
    for sl in slots do
      match sl with
      | .iterAt a _ => throw (scanErr warnings (.iterAtInStepBlock scanName nm ri a.uid))
      | _ => pure ()
    let advancing : List UID :=
      slots.filterMap (fun sl => match sl with | .iterNext a => some a.uid | _ => none)
    if stateNames.contains nm then
      if advancing.isEmpty then
        throw (scanErr warnings (.stateResultNotAdvancing scanName nm ri))
      unless advancing.length == numAxes && ctxUids.all (fun u => advancing.contains u) do
        throw (scanErr warnings (.partialAdvancingResult scanName nm ri advancing.length numAxes))
      match resultOf[nm]? with
      | some (firstRi, _) =>
          throw (scanErr warnings (.duplicateStateResult scanName nm firstRi ri))
      | none => resultOf := resultOf.insert nm (ri, slots)
    else
      unless advancing.isEmpty do
        throw (scanErr warnings (.orphanAdvancingResult scanName nm ri))
      for sl in slots do
        match sl with
        | .free a =>
            if (ctxIndexOf a.uid).isSome then
              throw (scanErr warnings (.contextAxisAsFreeOutput scanName nm ri a.uid))
        | _ => pure ()
      match scratchOf[nm]? with
      | some firstRi => throw (scanErr warnings (.duplicateScratchProducer scanName nm firstRi ri))
      | none => scratchOf := scratchOf.insert nm ri
  for st in stateNames do
    unless (resultOf[st]?).isSome do throw (scanErr warnings (.orphanBaseState scanName st))
  ---------------------------------------------------------------------------
  -- Phase 2: per-state geometry — rank, UID-to-dimension mapping, complete-history shape.
  ---------------------------------------------------------------------------
  let mut stateAdvDims : Array (Array Nat) := #[]
  let mut stateShapes : Array (Array Nat) := #[]
  for h : si in [0 : stateNames.size] do
    let st := stateNames[si]
    -- every placement of this state, in source order: its base statements first (so the BASE list
    -- establishes rank/geometry and the result is checked against it), then its one result.
    let placements : Array (Bool × Nat × List LHSSlot) :=
      ((baseOf.getD st #[]).map (fun (bi, slots) => (true, bi, slots))).push
        (false, (resultOf.getD st (0, [])).1, (resultOf.getD st (0, [])).2)
    let mut rank? : Option Nat := none
    let mut advDims? : Option (Array Nat) := none
    let mut shape? : Option (Array Nat) := none
    for h2 : pi in [0 : placements.size] do
      let (isBase, sidx, slots) := placements[pi]
      match rank? with
      | none => rank? := some slots.length
      | some r =>
          unless r == slots.length do
            throw (scanErr warnings
              (.inconsistentStateRank scanName st isBase sidx r slots.length))
      let slotAxes ← liftCapability warnings (slots.mapM (scanSlotAxisOrFail s!"{st}: LHS slot"))
      let slotUids : Array UID := (slotAxes.map (·.uid)).toArray
      -- UID-to-dimension mapping: each context axis occupies exactly one LHS position (uniqueness
      -- already established by Phase 1's `duplicateAxisInLhs` guard).
      let mut dims : Array Nat := #[]
      for h3 : i in [0 : numAxes] do
        let u := (axesA.getD i default).uid
        match slotUids.findIdx? (· == u) with
        | none => throw (scanErr warnings (.advancingAxisNotInLhs scanName st isBase sidx u))
        | some p => dims := dims.push p
      match advDims? with
      | none => advDims? := some dims
      | some prev =>
          for h3 : i in [0 : numAxes] do
            unless prev.getD i 0 == dims.getD i 0 do
              throw (scanErr warnings (.inconsistentAdvancingDim scanName st
                ((axesA.getD i default).uid) (prev.getD i 0) (dims.getD i 0)))
      -- complete-history extent per dimension: a context axis contributes its FULL history extent,
      -- every other placement axis its own inferred size.
      let mut dimShape : Array Nat := #[]
      for h3 : p in [0 : slotUids.size] do
        let u := slotUids[p]
        match ctxIndexOf u with
        | some i => dimShape := dimShape.push (historyExtents.getD i 0)
        | none =>
            let n ← liftShape warnings (resolveSizeOrFail sizes (.assignOutput st) u)
            dimShape := dimShape.push n
      match shape? with
      | none => shape? := some dimShape
      | some prev =>
          for h3 : p in [0 : prev.size] do
            unless prev.getD p 0 == dimShape.getD p 0 do
              throw (scanErr warnings
                (.inconsistentStateExtent scanName st p (prev.getD p 0) (dimShape.getD p 0)))
    stateAdvDims := stateAdvDims.push (advDims?.getD #[])
    stateShapes := stateShapes.push (shape?.getD #[])
  ---------------------------------------------------------------------------
  -- Phase 3: base block — captures, assignments, and one `StateWriteMap` per base statement.
  ---------------------------------------------------------------------------
  -- Every base destination is a state candidate (§4.2 rule 2), so a base block has no scratch and
  -- therefore no block-local production to read: a base read of a state is exactly proposal §8.4's
  -- "base reads from persistent state are rejected initially", and everything else must already be
  -- an outer name.
  let mut baseCapNames : Array String := #[]
  for h : bi in [0 : baseParts.size] do
    let (_, _, rhs) := baseParts[bi]
    for (rn, _) in rhs.readFactors do
      if stateNames.contains rn then
        throw (scanErr warnings (.stateReadInBaseBlock scanName bi rn))
      match slotOf[rn]? with
      | none => throw (scanErr warnings (.blockReadNotAvailable scanName true bi rn .unknownName))
      | some _ => unless baseCapNames.contains rn do baseCapNames := baseCapNames.push rn
  let baseInputCount := baseCapNames.size
  let baseLocalOf : HashMap String TensorSlot := (Array.range baseInputCount).foldl
    (fun m i => m.insert (baseCapNames.getD i "") i) {}
  let mut baseSigs : Array TensorSignature := baseCapNames.map (fun rn =>
    outerSigs.getD (slotOf.getD rn 0) { shape := #[], dtype := .f64 })
  let mut baseAssigns : Array AssignPlan := #[]
  let mut baseWrites : Array StateWriteMap := #[]
  for h : bi in [0 : baseParts.size] do
    let (nm, slots, rhs) := baseParts[bi]
    let si := (stateNames.findIdx? (· == nm)).getD 0
    let outputUids : List UID :=
      slots.filterMap (fun sl => match sl with | .free a => some a.uid | _ => none)
    let outputShape ←
      liftShape warnings (outputUids.toArray.mapM (resolveSizeOrFail sizes (.assignOutput nm)))
    -- §4.4: the `.iterAt` literals seed RHS evaluation as pins, not just write placement.
    let pins : HashMap UID Int := slots.foldl (fun m sl => match sl with
      | .iterAt a lit => m.insert a.uid lit | _ => m) ({} : HashMap UID Int)
    let destSlot := baseInputCount + bi
    let sigsNow := baseSigs
    let resolveSource (name : String) : TensorSlot × Array Nat :=
      let s := baseLocalOf.getD name 0
      (s, (sigsNow.getD s { shape := #[], dtype := .f64 }).shape)
    let plan ← residualizeAssignment sizes warnings nm [] #[] outputUids pins resolveSource
      destSlot outputShape rhs.body.terms
    baseSigs := baseSigs.push { shape := outputShape, dtype := .f64 }
    baseAssigns := baseAssigns.push plan
    -- write placement: a pin becomes an all-zero coefficient row with the literal as bias; a free
    -- position becomes a single `1` at its own output position. Domain is the output slice alone
    -- (base writes carry no context), so every row is `outputShape.size` wide.
    let width := outputShape.size
    let mut coeffs : Array (Array Int) := #[]
    let mut biasArr : Array Int := #[]
    let mut freeSeen := 0
    for sl in slots do
      match sl with
      | .iterAt _ lit =>
          coeffs := coeffs.push (Array.replicate width 0)
          biasArr := biasArr.push lit
      | .free _ =>
          coeffs := coeffs.push ((Array.range width).map (fun p => if p == freeSeen then 1 else 0))
          biasArr := biasArr.push 0
          freeSeen := freeSeen + 1
      | .freeNorm _ | .iterNext _ | .affine _ =>
          -- unreachable: Phase 1 rejected `.iterNext` here and preflight rejected `.freeNorm`/
          -- `.affine` in any scan block.
          liftCapability warnings (throw (.unsupportedLhsSlot s!"{nm}: base LHS slot"))
    baseWrites := baseWrites.push
      { outputSlot := destSlot, stateIndex := si, map := { coeffs, bias := biasArr } }
  ---------------------------------------------------------------------------
  -- Phase 4: step block — captures, assignments in source order, one write per state.
  ---------------------------------------------------------------------------
  -- A state name resolves to its immutable pre-step capture for the WHOLE block (§4.2); a scratch
  -- name resolves only after its producer. The two name sets are disjoint by Phase 1 (a recurrence
  -- destination sharing a base name is the state's result, never scratch), so no next-state result
  -- slot can ever shadow a state capture.
  let mut stepCapNames : Array (String × CaptureSource) := #[]
  for h : ri in [0 : recurParts.size] do
    let (_, _, rhs) := recurParts[ri]
    for (rn, _) in rhs.readFactors do
      match stateNames.findIdx? (· == rn) with
      | some si =>
          unless (stepCapNames.map Prod.fst).contains rn do
            stepCapNames := stepCapNames.push (rn, .state si)
      | none =>
          match scratchOf[rn]? with
          | some producer =>
              unless producer < ri do
                throw (scanErr warnings (.blockReadNotAvailable scanName false ri rn
                  (if producer == ri then .selfRead else .forwardReference)))
          | none =>
              match slotOf[rn]? with
              | none => throw (scanErr warnings (.blockReadNotAvailable scanName false ri rn .unknownName))
              | some outerSlot =>
                  unless (stepCapNames.map Prod.fst).contains rn do
                    stepCapNames := stepCapNames.push (rn, .external outerSlot)
  let stepInputCount := stepCapNames.size
  let stepCaptureOf : HashMap String TensorSlot := (Array.range stepInputCount).foldl
    (fun m i => m.insert (stepCapNames.getD i ("", .state 0)).1 i) {}
  let mut stepSigs : Array TensorSignature := stepCapNames.map (fun (_, src) => match src with
    | .state si => { shape := stateShapes.getD si #[], dtype := .f64 }
    | .external outerSlot => outerSigs.getD outerSlot { shape := #[], dtype := .f64 })
  let mut stepAssigns : Array AssignPlan := #[]
  let mut resultSlotOf : HashMap String TensorSlot := {}
  let mut scratchSlotOf : HashMap String TensorSlot := {}
  for h : ri in [0 : recurParts.size] do
    let (nm, slots, rhs) := recurParts[ri]
    let outputUids : List UID :=
      slots.filterMap (fun sl => match sl with | .free a => some a.uid | _ => none)
    let outputShape ←
      liftShape warnings (outputUids.toArray.mapM (resolveSizeOrFail stepSizes (.assignOutput nm)))
    let destSlot := stepInputCount + ri
    let sigsNow := stepSigs
    let scratchNow := scratchSlotOf
    let resolveSource (name : String) : TensorSlot × Array Nat :=
      -- captures first: a state's capture slot can never be displaced by a later scratch binding.
      let s := match stepCaptureOf[name]? with
        | some c => c
        | none => scratchNow.getD name 0
      (s, (sigsNow.getD s { shape := #[], dtype := .f64 }).shape)
    let plan ← residualizeAssignment stepSizes warnings nm ctxUids stepExtents outputUids
      ({} : HashMap UID Int) resolveSource destSlot outputShape rhs.body.terms
    stepSigs := stepSigs.push { shape := outputShape, dtype := .f64 }
    stepAssigns := stepAssigns.push plan
    if stateNames.contains nm then resultSlotOf := resultSlotOf.insert nm destSlot
    else scratchSlotOf := scratchSlotOf.insert nm destSlot
  -- step writes, in persistent-state order: `.iterNext` on context axis `i` becomes the canonical
  -- `context[i] + 1` row (the `+1` is built HERE — `checkScanPlan` recognizes it, it does not
  -- supply it); every other dimension passes its output position through.
  let mut stepOutputs : Array TensorSlot := #[]
  let mut stepWrites : Array StateWriteMap := #[]
  for h : si in [0 : stateNames.size] do
    let st := stateNames[si]
    let (_, slots) := resultOf.getD st (0, [])
    let outSlot := resultSlotOf.getD st 0
    let outputShape := (stepSigs.getD outSlot { shape := #[], dtype := .f64 }).shape
    stepOutputs := stepOutputs.push outSlot
    let width := numAxes + outputShape.size
    let mut coeffs : Array (Array Int) := #[]
    let mut biasArr : Array Int := #[]
    let mut freeSeen := 0
    for sl in slots do
      match sl with
      | .iterNext a =>
          let i := (ctxIndexOf a.uid).getD 0
          coeffs := coeffs.push ((Array.range width).map (fun p => if p == i then 1 else 0))
          biasArr := biasArr.push 1
      | .free _ =>
          coeffs := coeffs.push ((Array.range width).map
            (fun p => if p == numAxes + freeSeen then 1 else 0))
          biasArr := biasArr.push 0
          freeSeen := freeSeen + 1
      | .freeNorm _ | .iterAt .. | .affine _ =>
          -- unreachable: Phase 1 established that a state result's slots are `.iterNext` on every
          -- context axis and `.free` elsewhere.
          liftCapability warnings (throw (.unsupportedLhsSlot s!"{st}: state-result LHS slot"))
    stepWrites := stepWrites.push
      { outputSlot := outSlot, stateIndex := si, map := { coeffs, bias := biasArr } }
  ---------------------------------------------------------------------------
  -- Phase 5: source-facing validation of base-write placement and step-read causality.
  ---------------------------------------------------------------------------
  -- Reuses F3's own recognizers (`writeRowKinds`/`writesCollide`/`stateReadCausal`) rather than
  -- restating their rules: what this pass adds is SOURCE locators. `checkScanPlan` re-checks all of
  -- it later (Step E) as the internal safety net — a rejection there is a compiler bug reported as
  -- `invalidPlan`, which is exactly why the source-facing rejection has to happen here first.
  for h : wi in [0 : baseWrites.size] do
    let w := baseWrites[wi]
    let st := stateNames.getD w.stateIndex ""
    let stateShape := stateShapes.getD w.stateIndex #[]
    let rows := writeRowKinds stateShape.size 0 w
    unless (stateAdvDims.getD w.stateIndex #[]).any (fun d => rows.getD d none == some (.pinned 0)) do
      throw (scanErr warnings (.baseWriteNotAtBoundary scanName st wi))
    for h2 : d in [0 : rows.size] do
      match rows[d] with
      | some (.pinned lit) =>
          unless 0 ≤ lit && lit.toNat < stateShape.getD d 0 do
            throw (scanErr warnings
              (.baseWritePinOutOfRange scanName st wi d lit (stateShape.getD d 0)))
      | _ => pure ()
  for h : si in [0 : stateNames.size] do
    let st := stateNames[si]
    let stateShape := stateShapes.getD si #[]
    let mine : Array (Nat × Array (Option WriteRowKind)) :=
      (Array.range baseWrites.size).filterMap (fun wi =>
        let w := baseWrites.getD wi default
        if w.stateIndex == si then some (wi, writeRowKinds stateShape.size 0 w) else none)
    for h2 : a in [0 : mine.size] do
      for h3 : b in [0 : mine.size] do
        if a < b then
          if writesCollide mine[a].2 mine[b].2 then
            throw (scanErr warnings (.baseWritesOverlap scanName st mine[a].1 mine[b].1))
  let capturedState : Array (Option Nat) := stepCapNames.map (fun (_, src) => match src with
    | .state si => some si | .external _ => none)
  for h : ri in [0 : stepAssigns.size] do
    let a := stepAssigns[ri]
    for h2 : ti in [0 : a.terms.size] do
      let t := a.terms[ti]
      for h3 : fi in [0 : t.factors.size] do
        let f := t.factors[fi]
        match (capturedState.getD f.sourceSlot none) with
        | none => pure ()
        | some si =>
            unless stateReadCausal (stateAdvDims.getD si #[]) t.contextPos f do
              throw (scanErr warnings
                (.stateReadNotCausal scanName (stateNames.getD si "") ri ti fi))
  ---------------------------------------------------------------------------
  -- Phase 6: assemble. Every closed policy is Wave F's single admitted value.
  ---------------------------------------------------------------------------
  let states : Array StateSlot := (Array.range stateNames.size).map (fun si =>
    { destSlot := outerSigs.size + si, advancingDims := stateAdvDims.getD si #[]
    , materialization := .completeHistory })
  let raw : RawScanPlan :=
    { states
    , baseBlock :=
        { contextShape := #[], tensorSigs := baseSigs, inputs := Array.range baseInputCount
        , assignments := baseAssigns
        , outputs := (Array.range baseParts.size).map (· + baseInputCount) }
    , baseCaptures := (Array.range baseInputCount).map (fun i =>
        { inputSlot := i, source := .external (slotOf.getD (baseCapNames.getD i "") 0) })
    , baseWrites
    , stepBlock :=
        { contextShape := stepExtents, tensorSigs := stepSigs
        , inputs := Array.range stepInputCount
        , assignments := stepAssigns, outputs := stepOutputs }
    , stepCaptures := (Array.range stepInputCount).map (fun i =>
        { inputSlot := i, source := (stepCapNames.getD i ("", .state 0)).2 })
    , stepWrites
    , historyExtents
    , iterationOrder := .axisZeroFastest
    , boundaryPolicy := .zeroThenBaseOverlay
    , snapshotPolicy := .immutablePreStep }
  return { raw, stateNames, stateShapes }

/-- Resolve which output-slot position (if any) is the axiswise reduction axis, checking it
    agrees with the statement's own `Nonlin`. `slots` is the statement's LHS slot list — the
    returned position indexes directly into it, and 1:1 into the `outputShape`/`retainedUids` a
    `.free`/`.freeNorm`-only slot list produces, since `freeUidOrFail` drops no slots. -/
def resolveNonlinAxis (stmtName : String) (nonlin : Nonlin) (slots : List LHSSlot) :
    Except NonlinCompileError (Option Nat) := do
  let normPositions : List Nat :=
    slots.zipIdx.filterMap (fun (sl, i) => match sl with | .freeNorm _ => some i | _ => none)
  match nonlin with
  | .axiswise _ (some _) => throw (.maskedAxiswiseNotSupported stmtName)
  | .axiswise _ none =>
      match normPositions with
      | [] => throw (.noMarkedReductionAxis stmtName)
      | [p] => pure (some p)
      | p1 :: p2 :: _ => throw (.multipleMarkedReductionAxes stmtName p1 p2)
  | .identity | .pointwise _ =>
      match normPositions with
      | [] => pure none
      | p :: _ => throw (.unmarkedReductionAxis stmtName p)

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
  -- Plain, base, and recurrence assignments in SOURCE order (plan §4.5), interleaved exactly as
  -- `sched.stmts` presents them. `inferAxisSizesCore` (`Eval/SizeInfer.lean`) derives constraints
  -- only from `Stmt.readFactors` against known input shapes — it never inspects an `.assign`'s LHS
  -- slots at all (only `.scatter`'s, via `scatterOutputShapes`) — so `.iterAt`/`.iterNext`
  -- statements flow through it correctly with no special handling: verified by reading that
  -- function directly, not assumed. `.scanPre` stays unreachable (Step A rejects it).
  let flatStmts : List Stmt := sched.stmts.flatMap (fun
    | .plain s => [s]
    | .scan _ _ base recur _ => base ++ recur
    | .scanPre .. => [])   -- unreachable post-preflight (Step A already rejected this)
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
  let mut stepsAcc : Array PlanStep := #[]
  let mut materializedAcc : Array SlotBinding := #[]
  -- Branches on `ScanStmt`'s constructors directly rather than funnelling through a
  -- `plainStmtOrFail`-style narrowing: `.scan` is no longer "unreachable post-preflight" (F4's
  -- whole point), so the two admitted kinds need genuinely different compilation, and `.scanPre`
  -- keeps the unreachable-post-preflight throw that used to cover all three.
  for sc in sched.stmts do
    match sc with
    | .plain s =>
        let (nm, slots, rhs) ← liftCapability warnings (assignPartsOrFail "stmt" s)
        let retainedUids ← liftCapability warnings (slots.mapM (freeUidOrFail "lhs"))
        let outputShape ←
          liftShape warnings (retainedUids.toArray.mapM (resolveSizeOrFail sizes (.assignOutput nm)))
        -- Thread 4: resolve the statement's `Nonlin` against its own LHS slots BEFORE allocating
        -- any slot, so a rejection (masked axiswise, no/multiple markers, a marker on a non-
        -- axiswise statement) throws before any `PlanStep`/`TensorSignature` is built at all —
        -- `some p` indexes directly into `outputShape`/`retainedUids` per `resolveNonlinAxis`'s own
        -- doc comment (`freeUidOrFail` drops no slots, so the two lists stay 1:1 with `slots`).
        let axisPos? ← liftNonlin warnings (resolveNonlinAxis nm rhs.nonlin slots)
        -- name-environment mutation (`slotOf`/`tensorSigsAcc`/`materializedAcc`) is this plain
        -- caller's own publication policy — `residualizeAssignment` only builds the `AssignPlan`
        -- value, per its own doc comment.
        let destSlot := tensorSigsAcc.size
        let sigsNow := tensorSigsAcc
        let slotsNow := slotOf
        let resolveSource (name : String) : TensorSlot × Array Nat :=
          -- resolved against `slotOf` as it stands BEFORE this statement's destination slot is
          -- allocated. `getD` default is never reached: every read name is either external
          -- (allocated above) or produced by an earlier statement (schedule is topological, per
          -- `ScheduledProgram.stmts`'s own doc: "producers precede consumers").
          let sourceSlot := slotsNow.getD name 0
          (sourceSlot, (sigsNow.getD sourceSlot { shape := #[], dtype := .f64 }).shape)
        -- plain assignment: empty scan context, no pins — reproduces this Step D's pre-extraction
        -- behavior exactly (Task 2's whole point; see `residualizeAssignment`'s doc comment).
        let assignPlan ←
          residualizeAssignment sizes warnings nm [] #[] retainedUids ({} : HashMap UID Int)
            resolveSource destSlot outputShape rhs.body.terms
        match rhs.nonlin with
        | .identity =>
            -- Byte-for-byte unchanged (Thread 4 regression gate): single `.assign`, published
            -- directly under `nm`'s own destination slot — no internal slot allocated.
            tensorSigsAcc := tensorSigsAcc.push { shape := outputShape, dtype := .f64 }
            stepsAcc := stepsAcc.push (.assign assignPlan)
            materializedAcc := materializedAcc.push { name := nm, slot := destSlot }
            slotOf := slotOf.insert nm destSlot
        | .pointwise pf =>
            -- Two-step chain (§3): `.assign` publishes into the INTERNAL slot `destSlot`, not
            -- `nm`'s eventual published slot; `.pointwise` reads it and writes `publishedSlot`,
            -- which is what `nm` resolves to for every later reader.
            tensorSigsAcc := tensorSigsAcc.push { shape := outputShape, dtype := .f64 }
            let publishedSlot := tensorSigsAcc.size
            tensorSigsAcc := tensorSigsAcc.push { shape := outputShape, dtype := .f64 }
            stepsAcc := stepsAcc.push (.assign assignPlan)
            stepsAcc := stepsAcc.push (.pointwise
              { sourceSlot := destSlot, destinationSlot := publishedSlot
              , shape := outputShape, fn := pf })
            materializedAcc := materializedAcc.push { name := nm, slot := publishedSlot }
            slotOf := slotOf.insert nm publishedSlot
        | .axiswise fn _ =>
            -- `axisPos?` is provably `some _` here: `resolveNonlinAxis`'s `.axiswise _ none` branch
            -- (the only one that can reach this arm — `.axiswise _ (some _)` already threw above,
            -- at `liftNonlin`) never returns `none`. `getD 0` is a totality formality, not a real
            -- fallback, matching this file's own `getD`-on-an-already-validated-value idiom
            -- elsewhere (e.g. Phase 3/4's `resultOf.getD`/`stepCaptureOf.getD` above).
            let axisPos := axisPos?.getD 0
            tensorSigsAcc := tensorSigsAcc.push { shape := outputShape, dtype := .f64 }
            let publishedSlot := tensorSigsAcc.size
            tensorSigsAcc := tensorSigsAcc.push { shape := outputShape, dtype := .f64 }
            stepsAcc := stepsAcc.push (.assign assignPlan)
            stepsAcc := stepsAcc.push (.axiswise
              { sourceSlot := destSlot, destinationSlot := publishedSlot
              , shape := outputShape, axisPos, fn := fn })
            materializedAcc := materializedAcc.push { name := nm, slot := publishedSlot }
            slotOf := slotOf.insert nm publishedSlot
    | .scan scanName axes base recur _ =>
        let compiled ←
          compileScan sizes warnings scanName axes base recur tensorSigsAcc slotOf
        stepsAcc := stepsAcc.push (.scan compiled.raw)
        -- All state histories publish together, AFTER the scan step (§4.6): the outer signatures
        -- must land at exactly the destination slots `compileScan` already fixed
        -- (`tensorSigsAcc.size + i`, in persistent-state order), and no state name is visible to the
        -- scan's own base/step reads.
        for h : si in [0 : compiled.stateNames.size] do
          let nm := compiled.stateNames[si]
          let destSlot := tensorSigsAcc.size
          tensorSigsAcc :=
            tensorSigsAcc.push { shape := compiled.stateShapes.getD si #[], dtype := .f64 }
          materializedAcc := materializedAcc.push { name := nm, slot := destSlot }
          slotOf := slotOf.insert nm destSlot
    | .scanPre nm .. =>
        -- unreachable post-preflight (`checkScanStmt` rejects `.scanPre` as `recurrenceOrCallback`)
        throw { cause := .capability (.recurrenceOrCallback nm), warnings }
  -- Step E: assemble and check. This should ALWAYS succeed for a schedule that passed capability
  -- preflight AND `compileScan`'s own source-facing validation — if `checkPlan` ever rejects a
  -- compiler-generated plan, that is a bug in the compiler above, not a legitimate rejection.
  -- This is also where every compiled scan meets `checkScanPlan`: `checkPlan` already dispatches
  -- `.scan` steps to it and reports a failure as `PlanStepError.scan stepIndex cause`, which
  -- `liftPlanError` tags `invalidPlan` — exactly the internal-bug channel proposal §7.5 specifies,
  -- with the step locator already attached. Calling `checkScanPlan` a second time inside
  -- `compileScan` would duplicate that check without adding a locator it does not already carry.
  let raw : RawEvalPlan :=
    { tensorSigs := tensorSigsAcc, inputSlots := inputSlotsAcc
    , steps := stepsAcc }
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
