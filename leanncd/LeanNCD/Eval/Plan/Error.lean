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
  /-- An inline unary read factor inside an assignment whose graph storage kind has no unary
      implementation. Located at the ORIGINAL all-factor index (an Iverson ahead of the read does
      not shift it down), matching every other per-factor locator in this family. RETAINED
      PRODUCER-LESS as of the f32 slice's Task 2: `checkAssignF32` (`Check.lean`) admitted binary32
      unary math end to end (native `Float32.log`/`exp`/`sqrt`/`recip`/`sin`/`cos` through
      `float32Ops.applyUnary`, `Dense.lean`), so no current carrier lacks an inline-unary
      implementation. Kept for a FUTURE carrier that genuinely has none — the same discipline every
      other producer-less constructor in this file follows (§9.2) — rather than deleted, which would
      be a semantic version change. Carries the DTYPE rather than the storage kind: it is the
      destination's own declared dtype the rejection would be about, matching `dtypeNotAdmitted`. -/
  | unaryNotAdmittedForDtype      (termIndex factorIndex : Nat) (dtype : ScalarDType)
  /-- One signature table names two different REAL storage kinds. `slot` is the FIRST signature slot
      whose real storage kind disagrees with the kind an earlier slot established; `first` is the
      establishing slot's dtype and `actual` is this slot's — both concrete `ScalarDType`s, never
      `StorageKind`s, so the diagnostic names what the table actually says. `bool` signatures are
      skipped entirely (they are an algebra tag over whichever real carrier the table selects), so a
      `[f32, bool]` or `[f64, bool]` table is homogeneous, not mixed.

      Raised by `deriveStorageKind` (`Check.lean`) through `checkPlan` (`EvalPlan.lean`, wrapped as
      `PlanStepError.assign`) and `checkPlanBlock` (`Block.lean`, wrapped as `BlockError.wiring`).
      A mixed table has no meaning to compile: no worker and no algebra in this backend expresses a
      per-tensor precision boundary, and nothing inserts a conversion. -/
  | mixedStorageKinds             (slot : TensorSlot) (first actual : ScalarDType)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Which `PlanStep` constructor an outer graph step is, as a closed diagnostic payload rather than
    a rendered string. Defined here beside the other plan-layer diagnostics; its one consumer,
    `PlanStepError.f32UnsupportedStep`, lives in `EvalPlan.lean` for the same import-order reason
    `PlanStepError` itself does (it needs `ScanPlanError`), but this vocabulary needs nothing from
    that layer.

    `.assign`, `.pointwise`, and `.axiswise` are carried for completeness of the vocabulary —
    `PlanStep.kind` is total — and are deliberately NOT producers of `f32UnsupportedStep`: those are
    exactly the step kinds an `f32` graph admits (the nonlinearity pair since F32-B). Derives the
    same four classes `PlanStepError` does so that type's own derivations keep working. -/
inductive PlanStepKind
  | assign | scatter | scan | pointwise | axiswise
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
  /-- The BINARY32 sibling of `unaryDomain`: a checked binary32 read's inline unary factor rejected
      the value it gathered. `valueBits` is a `UInt32` `Float32.toBits` payload — a binary32 fact,
      never widened — and `slot` is the read's positional source slot, matching `unaryDomain`'s own
      locator. The only producer is the `Float32` scalar kernel's unary callback (`Dense.lean`,
      f32 slice Task 2), which delegates to `UnaryOp.applyChecked32` (`Eval/Error.lean`) exactly as
      `floatOps.applyUnary` delegates to `UnaryOp.applyChecked` for this constructor's binary64
      sibling. -/
  | unaryDomain32   (op : UnaryDomainOp) (valueBits : UInt32) (slot : TensorSlot)
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
  /-- A carrier-specific worker was handed checked evidence for a DIFFERENT storage kind. `expected`
      is the worker's own carrier (`.float64` for every `Array Float`-backed entry in this slice),
      `actual` is the kind the checked evidence records.

      Raised at the deepest public Float entries — `runDenseAssignAt` (`Dense.lean`) and
      `runDensePlan` (`EvalPlan.lean`) — BEFORE context, store, arity, or any input is read, so
      binary32 evidence can never be executed as binary64. Their empty-context wrappers
      (`runDenseAssign`) inherit the guard rather than repeating it; guarding only the wrappers
      would be insufficient, since a direct caller can invoke `runDenseAssignAt`. -/
  | storageKindMismatch (expected actual : LeanNCD.StorageKind)
  /-- A carrier whose scalar runtime has NO implementation of inline unary math was asked to apply
      one. `kind` is that carrier, `op` the requested operation, `slot` the read's source slot.

      RETAINED PRODUCER-LESS as of the f32 slice's Task 2: `float32Ops.applyUnary` (`Dense.lean`)
      now delegates to `UnaryOp.applyChecked32` and applies native binary32
      `log`/`exp`/`sqrt`/`recip`/`sin`/`cos` for real, so the `Float32` carrier — this constructor's
      only prior producer — no longer refuses unconditionally. It exists because the kernel seam's
      unary member is FALLIBLE rather than total — a carrier without inline unary math at all must
      be able to say so, instead of being forced to invent an answer or to route the value through
      the binary64 helper, which would be false to that carrier's own precision — and is kept for a
      FUTURE carrier that genuinely has none, the same discipline every other producer-less
      constructor in this file follows (§9.2).

      Deliberately NOT a reuse of `unaryDomain`/`unaryDomain32`: those constructors' `valueBits` are
      the OFFENDING VALUE's own bits, and this rejection is not a domain violation at all — it is
      "this carrier does not implement the operation", which has no offending value. -/
  | unaryNotAdmittedForStorage (kind : LeanNCD.StorageKind) (op : LeanNCD.UnaryOp)
                               (slot : TensorSlot)
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
  /-- A schedule the compiler will not compile FOR ITS DERIVED STORAGE KIND. Both producers are in
      `prepareEvalPlan` (never in `capabilityPreflight`, which is per-declaration and per-statement
      and cannot see a schedule-wide derivation):

      * Step 0b — a MIXED f32/f64 schedule, context `"{name}: mixed f32/f64 storage in one
        schedule"`, naming the first USED name that disagrees with the kind an earlier used name
        established. An undeclared external is a real f64 tensor, so an f32 graph reading one is
        mixed and lands here.
      * Step 0c (`f32CapabilityCheck`) — a homogeneous-f32 schedule using a construct binary32
        execution defers to a later slice, one context per construct: `"{name}: f32 scan"`,
        `"{name}: f32 scatter"`, and `"{name}: f32 nonlinearity"`. The former fourth context,
        `"{name}: f32 unary factor {termIndex}:{factorIndex}"`, has NO PRODUCER LEFT as of the f32
        slice's Task 2: `checkF32Stmt`'s factor loop that threw it is deleted, an inline unary read
        is now structurally admitted at Step 0c, and `checkAssignF32` (`Check.lean`) admits it too
        — retained here producer-less for the same reason every other retired context/constructor
        in this file is (§9.2), not deleted.

      Task 1's temporary blanket `"f32 execution not yet admitted"` context is GONE: a homogeneous
      f32 schedule inside this slice's fragment now compiles to checked binary32 evidence. -/
  | unsupportedDtype     (context : String)
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
      
      Detected on the `Stmt.scatter` shape a source predicate scatter presents at capability tier
      (post-`lowerArith`, the surface-compiled case). The OTHER shape a scatter-shaped write can take
      at this tier — a `Stmt.assign` whose LHS `slotsBecomeScatter`, reachable only from a hand-built
      `ScheduledProgram` that bypassed `lowerArith` — is rejected one step earlier by
      `unloweredScatterAssign` (below) regardless of destination dtype, since an unlowered
      scatter-shaped assign is malformed for a reason that does not depend on the destination's
      declaration. S-A supports only real-sum-product and the two tropical semirings (rejected via
      `scatterOptsNotAdmitted`); a predicate scatter destination is a third algebra with no reference
      match, and closing it means teaching the reference to be dtype-aware, not admitting it in the
      checked backend alone. -/
  | predicateScatterDest (context : String)
  /-- A scatter-shaped LHS (`slotsBecomeScatter` — an affine `Out[2*i]` or diagonal `Out[i, i]`
      write) reached capability preflight as a `Stmt.assign` node rather than a `Stmt.scatter`. The
      source pipeline's `lowerArith` (`DSL/Pipeline/Structural.lean`) UNCONDITIONALLY reclassifies
      every such `.assign` into `Stmt.scatter` before scheduling, so no `tl!{…}` program can produce
      this shape; only a hand-built `ScheduledProgram` handed straight to `prepareEvalPlan` can. It is
      rejected — independent of the destination's dtype — because an unlowered scatter-shaped assign
      has no agreed semantics: the reference reads it as a broadcast while the checked plain-assign
      path reads its repeated/affine axis differently, so the two backends silently diverge (e.g.
      `Out[i, i] := A[i]` with `A = [1, 2]` gives the reference `[[1,2],[1,2]]` and the checked
      backend `[[1,2],[2,0]]`, and NEITHER is the intended diagonal `[[1,0],[0,2]]` the
      properly-lowered `.scatter` produces). The canonical encoding of a diagonal/affine write is
      `Stmt.scatter`; this constructor names an assign node that should have been one. Distinct from
      `predicateScatterDest`, which rejects a WELL-FORMED `.scatter` on the grounds of its destination
      algebra alone. -/
  | unloweredScatterAssign (context : String)
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
  | scanWriteRowNotAdmitted  (scan name : String) (isBase : Bool) (stmtIndex dim : Nat)
                              (coeffs : Array Int) (bias : Int)
  | scatterScratchNotAdmitted (scan name : String) (stmtIndex : Nat)
  | contextAxisAsAffineOutput (scan name : String) (isBase : Bool) (stmtIndex : Nat) (uid : UID)
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

/-- Failure of a DECLARATION-AWARE `InputSignature` CONSTRUCTOR (`Signature.lean`'s
    `ofDenseInputsForDecls` and its binary32 sibling `ofDenseInputs32ForDecls`). Distinct from
    `InputSignatureError` above, which is `prepareEvalPlan`'s verdict on an already-built signature:
    this one is about building one at all.

    Two genuinely different malformations, checked in this order:

    * `declaration` — the supplied `decls` list is itself malformed, wrapping `buildDeclEnv`'s own
      `CompileError` (in practice `duplicateTensorDecl`) unchanged rather than restating it. It is
      FIRST because the declaration environment is the authority every later question is asked of:
      a list that declares one name twice has no single answer to "what precision is this name?",
      so reporting a carrier disagreement derived from a last-wins reading of it would name a
      consequence and hide the cause.
    * `storageKindMismatch` — a named input's CONCRETE CARRIER contradicts the precision its own
      declaration commits it to. `expected` is the CONSTRUCTOR's carrier (`.float64` for
      `ofDenseInputsForDecls`, `.float32` for `ofDenseInputs32ForDecls`), `actual` the declaration's
      (`storageConstraintOfName?`, `DSL/Ast.lean`). It names the input, because "some buffer is the
      wrong precision" is not actionable in a map of them. A `.predicate` declaration constrains
      nothing (a Boolean tensor's declaration names its ALGEBRA, not its precision) and so can never
      raise this from either constructor — which is what lets one Boolean name ride along with
      either real carrier. -/
inductive InputSignatureBuildError
  | declaration         (cause : LeanNCD.CompileError)
  | storageKindMismatch (name : String) (expected actual : LeanNCD.StorageKind)
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
  /-- The named INPUT adapter's own carrier does not match the prepared plan's checked storage kind.
      `expected` is the adapter's carrier (`.float64` for `pack`, `.float32` for `pack32`), `actual`
      the plan's. Raised by `packBodyOf` (`Adapter.lean`) as its first statement, before any shape
      or storage work and before any `DenseTensorOf α` is resolved out of the environment, so —
      under ordinary `StorageCarrier` instance resolution — a plan cannot have another carrier's
      buffers packed into its positional store and relabeled as its own. -/
  | storageKindMismatch (expected actual : LeanNCD.StorageKind)
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
  /-- The result adapter's or the prepared runner's own carrier does not match the prepared plan's
      checked storage kind. `expected` is that entry's carrier (`.float64` for `unpack` and
      `runPreparedDense`, `.float32` for `unpack32` and `runPreparedDense32`), `actual` the plan's.
      Two reporters, deliberately distinguishable from each other and from `binding`'s
      `InputBindingError.storageKindMismatch`: `unpackBodyOf` raises it as its first statement,
      before the result store's arity is examined or any name published, and `runPreparedDenseOf`
      raises its own copy FIRST — before `checkPreparedBindings`, `packBodyOf`, and the worker — so
      the composite entry fails at the adapter tier rather than inheriting a nested worker or pack
      diagnostic. -/
  | storageKindMismatch (expected actual : LeanNCD.StorageKind)
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
