import LeanNCD.Eval.Plan.Kernel
import LeanNCD.Eval.Error

/-!
# Wave C plan-layer diagnostics (C2)

Closed families, no `unsupported String` escape hatch — the same discipline Wave E applied to
`EvalError`. `PlanError` is structural/semantic invalidity of a raw operation, raised by the
checker before execution. `PositionalInputError` is a runtime value-boundary failure raised by a
worker: the plan was valid, the tensors supplied to it were not.
-/

namespace LeanNCD.Eval.Plan

/-- A raw `AssignPlan` violates a local invariant. Indices identify the offending term/factor so a
    failure is locatable without re-deriving it. -/
inductive PlanError
  | slotOutOfRange           (slot : TensorSlot) (tableSize : Nat)
  | dtypeNotAdmitted         (slot : TensorSlot) (dtype : ScalarDType)
  | dtypeMismatch            (destination : ScalarDType) (source : ScalarDType)
  | affineRankMismatch       (termIndex : Nat) (factorIndex : Nat) (expected : Nat) (actual : Nat)
  | affineWidthMismatch      (termIndex : Nat) (factorIndex : Nat) (expected : Nat) (actual : Nat)
  | sourceShapeMismatch      (termIndex : Nat) (factorIndex : Nat)
                             (declared : Array Nat) (signature : Array Nat)
  | positionsNotPartition    (termIndex : Nat)
  | outputProjectionMismatch (termIndex : Nat) (projected : Array Nat) (declared : Array Nat)
  | contextProjectionMismatch (termIndex : Nat) (projected : Array Nat) (declared : Array Nat)
  | constDtypeMismatch       (dtype : ScalarDType) (const : ScalarConst)
  | algebraNotAdmitted       (algebra : ContractionAlgebra)
  | policyNotAdmitted        (policy : OutOfBoundsPolicy)
  | destinationShapeMismatch (declared : Array Nat) (signature : Array Nat)
  | duplicateInputSlot       (slot : TensorSlot)
  | inputSlotsNotOrdered     (atIndex : Nat)
  | topLevelContextNotEmpty  (nodeIndex : Nat)
  | inputSlotOverwritten     (slot : TensorSlot) (nodeIndex : Nat)
  | duplicateDestination     (slot : TensorSlot) (firstNode : Nat) (secondNode : Nat)
  | missingProduction        (slot : TensorSlot)
  | invalidForwardRead       (nodeIndex termIndex factorIndex : Nat) (slot : TensorSlot)
  | nodeError                (nodeIndex : Nat) (cause : PlanError)
  /-- A `ScatterPlan`'s placement map does not carry one `outCoeffs` row and one `outBias` entry per
      DESTINATION dimension. Carries all three counts rather than conflating them the way
      `affineRankMismatch` does on the read side: `outCoeffs` and `outBias` are separate fields here,
      so a single "actual" would hide which of the two disagrees. -/
  | scatterPlacementRankMismatch  (expected coeffRows biasEntries : Nat)
  /-- One `outCoeffs` row does not span the source iteration basis (`compute.outputShape`). The read
      side's `affineWidthMismatch` locates by term/factor; a placement row has neither, so it locates
      by DESTINATION dimension. This clause has no counterpart on the existing write path, where
      placement-row widths go unchecked. -/
  | scatterPlacementWidthMismatch (dim : Nat) (expected actual : Nat)
  /-- The stored `destShape` disagrees, at this destination dimension, with the extent
      `LHSSlot.outExtent` derives from the placement row. `declared` is `destShape[dim]`, `derived`
      is `outExtent`'s answer — never a second formula's. -/
  | scatterDestExtentMismatch     (dim : Nat) (declared derived : Nat)
  /-- `LHSSlot.outExtent` returned `none` for this destination dimension (an unsized source axis).
      Unreachable for any plan whose placement widths `checkScatter` has already validated — the
      sizing lookup is `compute.outputShape` indexed by position, total once the row spans that
      basis — and carried for the same reason `predicateWidthMismatch` below is: fail loud rather
      than silently, if the derivation is ever reached another way. -/
  | scatterDestExtentUnknown      (dim : Nat)
  /-- A `ScatterPlan`'s `fill` is not the destination algebra's reduction identity. Fill and
      collision-reduce are the identity and the operation of one monoid, so an incoherent pair
      silently yields the identity's value for every unwritten cell instead of the true one
      (`reduce := .max` with `fill := 0` loses every all-negative cell's maximum). Rejected here
      rather than normalised: a checker that quietly rewrote `fill` would be indistinguishable, from
      its return value, from one that never looked. -/
  | scatterFillNotIdentity        (fill identity : ScalarConst)
  /-- A `ScatterPlan` names a collision policy no worker implements. Only `rejectCollisions` is
      admitted; the remaining four arms are matched explicitly (never a catch-all) so adding a sixth
      policy is a compile error and landing one of these is replacing this `throw` with real logic. -/
  | scatterReduceNotAdmitted      (reduce : LeanNCD.CollisionReduce)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A checked plan met a positional tensor store that does not conform to the shapes the checker
    validated. Distinct from `PlanError`: the plan is fine, the runtime values are not. -/
inductive PositionalInputError
  | missingSlot     (slot : TensorSlot) (provided : Nat)
  | shapeMismatch   (slot : TensorSlot) (expected : Array Nat) (actual : List Nat)
  | storageMismatch (slot : TensorSlot) (shape : List Nat) (dataSize : Nat)
  | arityMismatch   (expected : Nat) (actual : Nat)
  | contextShapeMismatch (expected : Array Nat) (actual : List Int)
  /-- A worker was handed a complete signature table that is not the one its checked evidence was
      validated against. Raised by `runDenseScan` (`Scan.lean`), whose `CheckedScanPlan` stores the
      table `checkScanPlan` used: the checked scan's state shapes, capture signatures, and write
      geometry are all facts about THAT table, so indexing a different one would allocate and commit
      against extents nothing checked — the shape of failure this replaces was an `Array.set!` panic
      inside `commitWrite` with an `.ok` result still returned. Carries both tables so the caller can
      see which slot disagrees. -/
  | signatureContextMismatch (expected actual : Array TensorSignature)
  /-- A worker or a store-consuming boundary was handed a positional store whose LENGTH is not the
      one its checked signature context describes. Raised by `runDenseScan` (`Scan.lean`), where the
      store is both
      read (external captures) and WRITTEN (each state's destination slot), and the destination
      slots are facts about `CheckedScanPlan.sigs` — so a store shorter than that table drove
      `Array.set!` out of range in the final destination loop: a `lean_array_set_panic` message with
      the ORIGINAL store still returned as `.ok`, i.e. a successful-looking run whose destination is
      simply absent. `expected` is `c.sigs.size` (derived from the stored evidence, never from the
      caller's arguments); equality is exact, matching `runDensePlan`'s own `arityMismatch` boundary
      and the `signatureContextMismatch` tie beside it — a store built to a different length was
      built against a different table, which is the very thing that tie exists to reject. Distinct
      from `arityMismatch` (a positional INPUT array against `inputSlots`) and from `missingSlot`
      (one slot absent, discovered during a read).

      Also raised by `Adapter.unpack` (whole-branch review round 4), whose RESULT store is the same
      kind of value against the same kind of stored evidence: a positional store that must be the
      one `unpack`'s own `PreparedPlan` was checked against, sized by `plan.raw.tensorSigs.size`.
      Carried there under `PlanRunCause.resultStore`, not `.execution`, so the boundary that
      rejected it stays distinguishable — same constructor, same meaning, different reporter. -/
  | storeArityMismatch (expected actual : Nat)
  | unaryDomain     (op : UnaryDomainOp) (valueBits : UInt64) (slot : TensorSlot)
  -- A positional Iverson predicate leaf's coefficient width disagrees with the term's iteration
  -- basis at RUNTIME. Unreachable for any plan `checkAssign` admits (its `.iverson` width check
  -- already forces every leaf width == `iterationShape.size`); carried so the Dense predicate
  -- evaluator fails loud rather than silently, if ever handed an unchecked plan.
  | predicateWidthMismatch (expected : Nat) (actual : Nat)
  /-- Two SOURCE coordinates of a scatter place a value at the same DESTINATION coordinate under
      `CollisionReduce.rejectCollisions`. Raised by `runDenseScatter` (`Dense.lean`), and a runtime
      concern rather than a `PlanError` by construction: whether a placement map is injective over a
      given source domain is not decidable from the plan's rank/width/extent clauses, which is why
      `checkScatter` admits a non-injective map (rank-0 destination, an all-zero placement row) and
      names collision detection as the worker's own case-audit cell.

      Payload mirrors the reference `EvalError.scatterCollision` (`Eval/Error.lean`) field for field
      MINUS its leading tensor name: the checked layer is positional and retains no source names, and
      the destination slot is recoverable from the plan the caller already holds. Both conflicting
      source coordinates are carried, not just the second: naming only the write that failed leaves
      the first writer — the other half of the conflict — undiscoverable, and the reference's own
      `writtenBy` map exists solely to report it. `first` is whichever source coordinate row-major
      enumeration reached first, matching the reference's `cartesian` order. -/
  | scatterCollision (destCoord firstSource secondSource : List Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Wave C capability rejection (proposal §3.1/§3.2): which construct in the initial scan-free `f64`
    fragment boundary a source `ScheduledProgram` falls outside of, with the source-level context
    (statement/decl name, or a short description) that failed. Ported from C0's test-only
    `PlanContract.Classification` category names (`test/Eval/Plan/ContractTest.lean`) into a real,
    closed error type a real function can throw — no `unsupported : String` escape hatch (§3.2). -/
inductive CapabilityError
  | scanNode             (context : String)  -- ScanStmt.scan / .scanPre
  | scatterOrAffineLhs   (context : String)  -- scatter statements, affine LHS slots
  | unsupportedLhsSlot   (context : String)  -- freeNorm, iterAt, iterNext
  | unsupportedNonlin    (context : String)  -- pointwise/axiswise nonlinearities
  | maskOrPredicate      (context : String)  -- masks, predicates, Iverson factors: RETAINED, no
                                             -- producer left (predicate/mask parity thread admits
                                             -- source Iverson factors, lowered via
                                             -- `lowerFactorPredicate`); kept per §9.2, like scanNode
  | unaryFactor          (context : String)
  | unsupportedAgg       (context : String)  -- max/min aggregation: RETAINED, no producer left
                                             -- (checkAggOp admits max/min since they compile to the
                                             -- tropical algebras); kept per §9.2, like scanNode
  | booleanOutput        (context : String)
  | unsupportedDtype     (context : String)  -- any dtype other than the declared f64 mode
  | dynamicShape         (context : String)  -- backend- or value-dependent shapes
  | recurrenceOrCallback (context : String)
  | noAdvancingAxis      (context : String)  -- `.scan` declaring an empty advancing-axis list
  /-- A top-level scatter's affine LHS slot whose coefficient row names MORE THAN ONE source axis
      (`Out[i+j]`), where the single-axis strided forms (`Out[2*i]`, `Out[i+2]`) are admitted.
      Its own constructor rather than a reuse of `scatterOrAffineLhs`, because "a scatter is not
      supported at all" and "this one placement form is not supported" are different facts and the
      fixture distinguishing them has to be able to see which was meant.

      Why the form is rejected rather than compiled: `LHSSlot.outExtent`'s
      `bias + Σ coeff · size` is the upsample-stride convention, designed for one strided axis. On
      a two-axis row it computes the sum of the two axes' extents (`i : 3`, `j : 4` ⇒ `7`) where the
      reachable coordinate set `i + j` spans only `0 … 5`, and with a mixed-sign row it admits
      negative reachable coordinates that the worker's out-of-range skip silently absorbs. Neither
      is unsound, but neither is verified by this feature's worked examples or its differential
      corpus either, so it is refused with a locator instead of shipped unexercised. Unreachable
      from `tl!{…}` surface syntax (`elabTLLHSSlot` parses only `n*x+m`-shaped single-axis slots);
      a hand-built `ScheduledProgram` handed to `prepareEvalPlan` is what can express it. -/
  | multiAxisScatterLhs  (context : String)
  /-- A top-level scatter's `ScatterOpts` naming a fill or a collision policy the checked layer does
      not implement: a `reduce` other than `rejectCollisions` (the only policy `checkScatter`
      admits), or a `fill` that is not the destination algebra's own reduction identity
      (`ContractionAlgebra.reduceId` — §2.5's coherence rule: fill and collision-reduce are the
      identity and the operation of one monoid). Both are rejected HERE, at capability tier with a
      source locator, rather than left to surface from `checkScatter` as `invalidPlan`, which is the
      compiler-bug channel and would misreport a legitimately out-of-fragment source program as one.

      The live case is a `maxreduce`/`minreduce` scatter: `ScatterOpts.fill` is an `Int` and cannot
      express the tropical `∓∞` its algebra's identity requires, so no admissible fill exists for
      one. `agg = .sum` with `fill = 0` is coherent and admitted. A `predicate`/`bool`-declared
      scatter destination is NOT reachable from this constructor: it is rejected upstream by
      `predicateScatterDest` (below) at the same tier, before `scatterFillOrFail` is called at all.
      (Prior claim that a predicate destination with `fill = 0` was "coherent and admitted" was
      wrong — the reference `evalScatter` (`Eval/Scatter.lean`) selects its algebra from `rhs.agg`
      only, never seeing `decls`, so a Boolean scatter destination silently diverged from the
      reference in real sum arithmetic; the fix routes the rejection through the capability tier
      instead.) -/
  | scatterOptsNotAdmitted (context : String)
  /-- A top-level scatter's DESTINATION is `predicate`/`bool`-declared. The reference evaluator
      `evalScatter` (`Eval/Scatter.lean`) is not dtype-aware: it selects its algebra from `rhs.agg`
      only (`.sum ⇒ Combine.real`, real sum-product), so a Boolean destination would run real
      sum-product in the reference while the checked backend's `algebraForDest` selects
      `admittedAlgebraBool` — a silent divergence with no diagnostic. Rejected here, at capability
      tier, with a source locator naming the destination — the same way a `maxreduce`/`minreduce`
      scatter (whose fill cannot denote `∓∞`) is refused, and for the same reason: no reference
      semantics can match it, so the honest report is "not in the fragment", not a differential
      failure downstream.
      
      Detected on both surface shapes a scatter can present at capability tier: a `Stmt.scatter`
      (post-`lowerArith`, the surface-compiled case), and a `Stmt.assign` whose LHS
      `slotsBecomeScatter` (hand-built `ScheduledProgram` bypassing the source pipeline, the same
      shape `checkScatterNoScan` (`DSL/Pipeline/Structural.lean`) also inspects — one rule, mirrored
      here so a hand-built schedule reaches the same verdict). S-A supports only real-sum-product
      and the two tropical semirings (rejected via `scatterOptsNotAdmitted`); a predicate scatter
      destination is a third algebra with no reference match, and closing it means teaching the
      reference to be dtype-aware, not admitting it in the checked backend alone. -/
  | predicateScatterDest (context : String)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Why `blockReadNotAvailable` rejected a name: it never resolves to a state, a block-local
    scratch producer, or an outer/external tensor at all (`unknownName`); it resolves to a scratch
    name whose one producing statement comes strictly LATER in source order (`forwardReference`);
    or it resolves to the very statement that is itself about to produce it (`selfRead`, the
    `producer == stmtIndex` edge of the same check). Base blocks have no block-local scratch
    (§4.2/§8.4), so every base-side `blockReadNotAvailable` is `unknownName`. -/
inductive ReadUnavailableCause
  | unknownName
  | forwardReference
  | selfRead
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Wave F source-scan rejection (proposal §5.2/§7.5): what a `.scan` node's base/recurrence lists
    say that cannot be given a checked-scan meaning, discovered AFTER capability preflight and shape
    inference, once concrete axis sizes and lowered affine maps exist. Deliberately a second closed
    family beside `CapabilityError` rather than more constructors on it: a `CapabilityError` is
    decidable from the bare AST (`capabilityPreflight` runs before shape inference and cannot see a
    size), whereas every constructor below needs either an inferred extent, a derived state
    geometry, or a lowered read row. No `unsupportedScan : String` escape hatch, for the same reason
    `CapabilityError` has none (§5.2's literal text).

    Every constructor carries source locators, never rendered strings: the enclosing scan's
    representative name (`scan` — a DIAGNOSTIC label only; state classification never reads it, see
    `compileScan`'s doc comment), the offending state or destination name, the offending statement's
    index within its own `base`/`recur` list, and the term/factor or write/dimension index where one
    applies. `isBase` distinguishes the two blocks wherever one constructor genuinely serves both. -/
inductive ScanCompileError
  -- §4.2 state/base/result pairing
  | noPersistentState        (scan : String)
  | orphanBaseState          (scan state : String)
  | orphanAdvancingResult    (scan name : String) (stmtIndex : Nat)
  | duplicateStateResult     (scan state : String) (firstStmtIndex secondStmtIndex : Nat)
  | stateResultNotAdvancing  (scan state : String) (stmtIndex : Nat)
  -- "partial" in the sense of "not exactly the declared context": `declared` is how many axes the
  -- result actually advances and `expected` the scan's context width, so this covers advancing too
  -- FEW axes (some context axis left un-advanced) and advancing an axis that is not scan context at
  -- all (too many) alike — both break the canonical all-axis `+1` step geometry the same way.
  | partialAdvancingResult   (scan state : String) (stmtIndex : Nat) (declared expected : Nat)
  | duplicateScratchProducer (scan name : String) (firstStmtIndex secondStmtIndex : Nat)
  -- block dependency order
  | blockReadNotAvailable    (scan : String) (isBase : Bool) (stmtIndex : Nat) (name : String)
                             (cause : ReadUnavailableCause)
  | stateReadInBaseBlock     (scan : String) (stmtIndex : Nat) (state : String)
  -- context axes and per-state geometry
  | duplicateContextAxis     (scan : String) (axisIndex : Nat) (uid : UID)
  | scanAxisZeroExtent       (scan : String) (axisIndex : Nat) (uid : UID)
  | iterNextInBaseBlock      (scan name : String) (stmtIndex : Nat) (uid : UID)
  | iterAtInStepBlock        (scan name : String) (stmtIndex : Nat) (uid : UID)
  | pinnedAxisNotContext     (scan name : String) (stmtIndex : Nat) (uid : UID)
  | contextAxisAsFreeOutput  (scan name : String) (stmtIndex : Nat) (uid : UID)
  | advancingAxisNotInLhs    (scan name : String) (isBase : Bool) (stmtIndex : Nat) (uid : UID)
  | duplicateAxisInLhs       (scan name : String) (isBase : Bool) (stmtIndex : Nat) (uid : UID)
  | inconsistentStateRank    (scan state : String) (isBase : Bool)
                             (stmtIndex expected actual : Nat)
  -- The two below compare one placement against the one that established the state's geometry, so
  -- their locator is the STATE plus the disagreeing axis/dimension and both values, not a single
  -- statement index: a state's placements are its own base statements plus its one result, and the
  -- pair of values names which two disagree. Adding `isBase`/`stmtIndex` here would only identify
  -- the second of the two, which is not more useful than the values themselves.
  | inconsistentAdvancingDim (scan state : String) (uid : UID) (expected actual : Nat)
  | inconsistentStateExtent  (scan state : String) (dim expected actual : Nat)
  -- base write placement (§5.1: in range, boundary-touching, pairwise disjoint)
  | baseWriteNotAtBoundary   (scan state : String) (writeIndex : Nat)
  | baseWritePinOutOfRange   (scan state : String) (writeIndex dim : Nat) (lit : Int) (extent : Nat)
  | baseWritesOverlap        (scan state : String) (firstWriteIndex secondWriteIndex : Nat)
  -- §7.4 causality, checked against the lowered step-block read rows
  | stateReadNotCausal       (scan state : String) (stmtIndex termIndex factorIndex : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Wave "Thread 4" (nonlinearity) source-compile rejection: which sub-case of §3's LHS-slot vs
    `Nonlin` agreement check a top-level statement fails. Discovered at the same compile tier as
    `ScanCompileError` (after preflight admits `.freeNorm` structurally, agreement with the
    statement's own `Nonlin` is a compile-time, not a preflight, concern) — a closed family, no
    `unsupported : String` escape hatch, same discipline as its siblings above. -/
inductive NonlinCompileError
  | noMarkedReductionAxis       (stmtName : String)
  | multipleMarkedReductionAxes (stmtName : String) (firstPos secondPos : Nat)
  | unmarkedReductionAxis       (stmtName : String) (pos : Nat)
  | maskedAxiswiseNotSupported  (stmtName : String)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A required signature is missing, malformed, or incompatible with the scheduled declarations
    (§5.5). Checked for every name in `sched.extNames` — by construction (`resolveDecls`,
    `Structural.lean`), every such name is read somewhere, so no separate "read before production"
    filter is needed here. `dtypeNotAdmitted` fires when the supplied signature names a dtype no
    worker implements at all (`f32`); `dtypeMismatch` (Task 4.3) fires when the supplied dtype IS
    admitted but disagrees with the one the source DECLARATION commits this name to (a `.predicate`
    declaration expects `bool`, everything else expects `f64`) — a genuinely different failure: the
    signature is well-formed on its own, just contradicts what the program itself says about this
    name. -/
inductive InputSignatureError
  | missingSignature (name : String)
  | dtypeNotAdmitted (name : String) (dtype : ScalarDType)
  | dtypeMismatch    (name : String) (expected actual : ScalarDType)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Failure of `Prepared.lean`'s `checkBindings`: a candidate `requiredInputs` array does not align
    with a plan's `inputSlots` the way a `RequiredBindings` requires. `notAPermutation` covers a
    duplicate slot, an extra slot, or a missing slot alike — every one of those breaks
    `(bindings.map (·.slot)).toList.Perm inputSlots.toList`, so they all surface through this one
    constructor with the two slot lists that failed to match. `duplicateName` is a genuinely
    separate malformation: two different slots bound to the same source name, which slot-`Perm`
    alone cannot catch (two distinct slots can each legitimately appear once in the permutation
    while still sharing a name). Defined here, not in `Prepared.lean`, because `PlanCompileCause`
    (relocated to `EvalPlan.lean` — see the plain comment just below) needs it and `Error.lean` sits
    upstream of `Prepared.lean` in the CURRENT import graph (`Prepared → EvalPlan → Scan → Block →
    Dense → Check → Error`) — `TensorSlot`/`String` are both already available via `Kernel.lean`, so
    no `SlotBinding`-shaped payload is needed here to make that work. -/
inductive BindingsError
  | notAPermutation (expectedSlots observedSlots : Array TensorSlot)
  | duplicateName   (name : String)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A public prepared plan's name bindings do not describe its own raw positional plan.  This is
    structural slot validation only: raw plans retain no source or publication names. -/
inductive PreparedBindingsError
  | requiredInputs    (cause : BindingsError)
  | materializedSlot  (cause : PlanError)
  | publicationSlots  (expected actual : Array TensorSlot)
  deriving DecidableEq, BEq, Repr, Inhabited

/- `PlanCompileCause`/`PlanCompileFailure` used to live here (§5.5's sketch), but `invalidPlan`'s
   payload is now `PlanStepError` (`EvalPlan.lean`), which itself depends on `ScanPlanError`
   (`Scan.lean`) — one layer downstream of where this file sits in the import graph (`Error` is
   imported by `Check`, which is upstream of `Dense → Block → Scan → EvalPlan`). So both types
   relocated to `EvalPlan.lean`, the first module downstream of everything they need to reference.
   See `EvalPlan.lean` for their current definitions. -/

/-- Everything `pack` can detect wrong with the concrete tensor `env` supplies once prepared bindings
    itself is already known-good (`PlanBindings.requiredInputs : RequiredBindings`, checked by
    `checkBindings` — a clean, name-unique bijection, but onto `RequiredBindings`' OWN stored
    `inputSlots` field, NOT — by anything the type system enforces — onto the enclosing
    `PreparedPlan`'s `plan.raw.inputSlots`; the two agree for every plan `prepareEvalPlan` produces
    only because it is the sole real-world producer that builds both together from the same array,
    a producer-discipline fact, not a type-level guarantee). If that coupling were ever broken by a
    hand-built `PreparedPlan`, `pack` still fails loud — a `.missingEnvBinding` naming the unmatched
    slot, not a silent wrong-tensor pack. The three constructors this type used to carry for that
    case, `missingRequiredBinding`/`duplicateRequiredBinding`/`extraRequiredBinding`, are gone:
    unreachable for every `RequiredBindings` `prepareEvalPlan` actually produces, since
    `checkBindings` already rejects those shapes at construction. What's left are genuine runtime
    concerns about the caller-supplied `env`: `missingEnvBinding` (a required name absent from
    `env`), `shapeMismatch`/`storageMismatch` (a name resolved, but its tensor doesn't conform to
    the plan's declared signature). -/
inductive InputBindingError
  | invalidPreparedBindings (cause : PreparedBindingsError)
  | missingEnvBinding (name : String)
  | shapeMismatch     (name : String) (slot : TensorSlot) (expected : Array Nat) (actual : List Nat)
  | storageMismatch   (name : String) (slot : TensorSlot) (shape : List Nat) (dataSize : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The runtime counterpart of `PlanCompileCause`: a `PreparedPlan` failed at the named binding
    boundary on the way IN (`pack`), inside the positional worker (`runDensePlan`), or at the
    boundary on the way OUT (`unpack`) — either because the positional RESULT STORE itself is not
    the one the checked plan describes (`resultStore`) or because a materialized binding cannot be
    resolved against it (`materialization`). All payload types derive `Repr` (verified, not assumed
    by analogy — unlike `PlanCompileCause`'s `ShapeError` sibling) so `PlanRunCause` derives `Repr`
    too.

    `materialization` carries a `PlanError` rather than a fourth bespoke type: `unpack` resolves
    `PlanBindings.materializedNames` against the positional result store through the shared
    `PlanBindings.materializedWith` (`Prepared.lean`), whose failure is the same
    `PlanError.slotOutOfRange` every other slot-table lookup in this subsystem raises — and the same
    value `PreparedPlan.materializedSignatures` reports for the identical malformation, which is the
    point of sharing the path.

    `resultStore` is the OUT-boundary sibling of `execution`, and carries the same
    `PositionalInputError` family for the same reason `materialization` reuses `PlanError`: the
    malformation (`storeArityMismatch`) is a positional-store fact with an existing constructor that
    already means exactly this. It is deliberately NOT folded into `execution`: `unpack` is
    callable directly on a store no worker produced (`AdapterTest`'s own fixtures do exactly that),
    so attributing a caller-supplied store's arity to `runDensePlan` would name a boundary that may
    never have run. Through `runPreparedDense` it is unreachable — `runDensePlan` returns a store
    built at exactly `tensorSigs.size` — which is the point: the store `unpack` accepts is now
    pinned to the checked plan rather than to whatever the caller passes. -/
inductive PlanRunCause
  | binding         (cause : InputBindingError)
  | invalidBindings (cause : PreparedBindingsError)
  | execution       (cause : PositionalInputError)
  | resultStore     (cause : PositionalInputError)
  | materialization (cause : PlanError)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Failure type of `runPreparedDense`. `warnings` is always `plan.warnings` (the preparation
    warnings `PreparedPlan` already carried) — never re-derived — so a binding or execution failure
    never silently drops an earlier shape-inference warning. NOT `Repr`: `EvalWarning` has none, so
    `List EvalWarning` blocks a derived `Repr` here exactly as it did for `PlanCompileFailure`. -/
structure PlanRunFailure where
  cause    : PlanRunCause
  warnings : List EvalWarning
  deriving DecidableEq, BEq, Inhabited

end LeanNCD.Eval.Plan
