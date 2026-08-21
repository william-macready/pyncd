# Thread 4 — implement nonlinearity (Dense-only)

## 0. Session verification record (2026-08-20)

Everything below was re-verified directly against the repo at `main` (b5bb00e, Wave F complete),
not carried over from an earlier summary.

- `LeanNCD/DSL/Ast.lean`: `PointwiseFn | relu | sigmoid | tanh | gelu | leakyrelu` and
  `AxiswiseFn | softmax | normalize | l2normalize` each derive `DecidableEq, Repr, Lean.ToExpr,
  Inhabited` — **no `BEq`**. `Nonlin | identity | pointwise PointwiseFn | axiswise AxiswiseFn
  (Option BoolExpr)` attaches to `RHSExpr.nonlin`, carried by `Stmt.assign`/`Stmt.scatter`.
  `Stmt.recurMorphism` structurally forces `.identity` (`Stmt.nonlinOf`) — independent confirming
  evidence for the scan-block scope boundary below.
- `LHSSlot.freeNorm : AxisSpec → LHSSlot` is the **sole** surface mechanism that names an axiswise
  reduction axis (the `s.`/`m.` marker). `RHSExpr.nonlin`'s `.axiswise` case carries no axis
  reference of its own.
- `LeanNCD/Eval/Plan/RawStep.lean`: `PlanStep | assign (a : AssignPlan) | scan (s : RawScanPlan)`,
  `deriving DecidableEq, BEq, Repr, Inhabited`. Imports only `Kernel.lean`.
- `LeanNCD/Eval/Plan/EvalPlan.lean`: three exhaustive matches over `PlanStep`/
  `CheckedPlanStepEvidence` — `PlanStep.sourceSlots`, `PlanStep.destinationSlots`, and `checkPlan`'s
  three separate `match step with` blocks (context-check, destination-availability loop,
  source-availability + dispatch), plus `CheckedPlanStepEvidence`'s own 2-constructor mirror and
  `runDensePlan`'s match over it. `.assign`'s source-read check is a direct per-term/per-factor loop
  (preserves `ti`/`fi` locators); `.scan`'s uses the generic `PlanStep.sourceSlots`/
  `destinationSlots` accessors with placeholder locators `0 0`.
- `LeanNCD/Eval/Plan/Compile.lean`: `checkNonlin` (the `unsupportedNonlin` rejection) has exactly
  two call sites — `checkStmt` (plain top-level statements) and `checkScanBlockStmt` (scan
  base/recurrence statements). `checkLHSSlot` (used by `checkStmt`) unconditionally rejects
  `.freeNorm` via `unsupportedLhsSlot`; `checkScanLHSSlot` (used by `checkScanBlockStmt`) admits
  `.iterAt`/`.iterNext` but still rejects `.freeNorm` too. `freeUidOrFail` (Step D helper) throws
  `unsupportedLhsSlot` on `.freeNorm`, justified by a doc comment claiming this is unreachable
  post-preflight — true only as long as `checkLHSSlot` keeps rejecting it.
- `LeanNCD/Eval/Nonlin.lean`: `reluT`/`sigmoidT`/`tanhT`/`geluT`/`leakyReluT` are pure
  `DenseTensor → DenseTensor` maps (`⟨t.shape, t.data.map f⟩` — shape-preserving by construction,
  no coordinate arithmetic that can go out of range). `softmaxT`/`normalizeT`/`l2normalizeT` take
  `(axisPos : Nat) (axisUids : List UID) (mask? : Option BoolExpr) (t : DenseTensor)`, built on a
  shared `perRow` combinator; `axisUids`/`mask?` are used **only** inside the `mask? = some _`
  branch of `perRow` (to build `coordMap` for `evalBool`) — when `mask? = none`, `axisUids` is
  never read. `gelu` is the tanh approximation (matches JAX's default; PyTorch's default is exact
  erf and needs `approximate='tanh'`).
- `LeanNCD/Eval/Plan/Error.lean`: `CapabilityError.unsupportedNonlin (context : String)` — single
  bare string, no pointwise/axiswise distinction. `ScanCompileError` (this file, not `Scan.lean`)
  is the precedent for "a second closed error family beside `CapabilityError`, for obligations that
  need more than bare-AST decidability" — several of its own constructors (e.g.
  `noPersistentState`, `duplicateContextAxis`) are in fact syntactically decidable too, so
  "needs inferred sizes" is not literally `ScanCompileError`'s membership test; "belongs to one
  named construct's own compile-tier obligations, not general per-statement preflight" is.
  `ScanPlanError` (checker-level, for `checkScanPlan`) lives in `Scan.lean` itself, not here.
- `LeanNCD/Eval/Plan/Types.lean`: `NumericMode | reference64SumProduct`, single constructor.
  `LeanNCD/Eval/Plan/Graph.lean`: `RawEvalPlan.numericMode : NumericMode`. `EvalPlan.lean`'s
  `checkPlan` throws `PlanError.numericModeNotAdmitted` if it's not `.reference64SumProduct`
  (structurally impossible, and a `GraphCheckTest.lean` comment already calls this "structurally
  unreachable"). `Compile.lean`'s `prepareEvalPlan` sets `numericMode := .reference64SumProduct` in
  the one `RawEvalPlan` literal it builds.
- Every `numericMode`/`reference64SumProduct`/`NumericMode`/`numericModeNotAdmitted` occurrence in
  the repo, from a direct grep (paths relative to `leanncd/`):
  - Production: `LeanNCD/Eval/Plan/Types.lean` (the type), `LeanNCD/Eval/Plan/Graph.lean` (the
    field), `LeanNCD/Eval/Plan/Error.lean` (the `PlanError` constructor),
    `LeanNCD/Eval/Plan/EvalPlan.lean` (the `checkPlan` guard/throw),
    `LeanNCD/Eval/Plan/Compile.lean` (the `RawEvalPlan` literal in `prepareEvalPlan`).
  - Tests, each setting `numericMode := .reference64SumProduct` in a `RawEvalPlan` literal unless
    noted: `test/Eval/Plan/EvalPlanTest.lean` (4 occurrences), `test/Eval/Plan/GraphCheckTest.lean`
    (`chainPlan`, `diamondPlan`, plus a direct `#guard (PlanError.numericModeNotAdmitted ...)  ==
    ...` line and an adjacent comment calling it "structurally unreachable"),
    `test/Eval/Plan/GraphDenseTest.lean` (5 occurrences), `test/Eval/Plan/KernelCheckTest.lean` (1),
    `test/Eval/Plan/ExecutableTest.lean` (2). Comment-only stale references once the constructor is
    gone: `test/Eval/Plan/CompileTest.lean` ("same pattern as `checkAssign`'s single-valued-vocabulary
    unreachables (`numericModeNotAdmitted`, C2/C3)"), `test/Eval/Plan/AdapterTest.lean` ("same
    pattern as `PlanError.numericModeNotAdmitted` (C3)"), `test/Eval/Plan/ContractTest.lean`
    ("`NumericMode`: deferred to C1/C2 ... Wave C admits only `reference64SumProduct`").
  - `experiments/jax_bridge/EvalPlanCodegen.lean` also sets `numericMode := .reference64SumProduct`
    in one `RawEvalPlan` literal — **left untouched**, see the JAX scope note below.
- **`experiments/jax_bridge/EvalPlanCodegen.lean` is confirmed broken independent of this thread**,
  by directly running `lake build JaxExperiment` this session (real command, real failure, not
  assumed): it fails with `Invalid field 'plan': ... CheckedPlanStepEvidence.plan` (two call sites),
  a non-exhaustive `match` over `PlanCompileCause.scan (ScanCompileError...)` variants, `'version'
  is not a field of structure 'RawEvalPlan'`, and an `AssignPlan`/`PlanStep` type mismatch in a
  `RawEvalPlan` literal — exactly the stale-`.plan`-access / removed-`version` / `PlanStep`
  generalization breakage the architecture doc already documents as Wave F leaving this file behind,
  a later unscheduled wave's problem, not this thread's. This plan does not touch that file.
- `test/Eval/Plan/DifferentialTest.lean`'s pinned corpus split (`total=17 accepted=9
  unsupportedNonlin=4 unsupportedAgg=4`) is `scanCorpusSplit` (its `enumScanCases` sweep), not the
  separate 3,832-program `enumPrograms` sweep (which has zero nonlin/scatter/scan/predicate/agg
  constructs and is unaffected either way). **Correction to the task brief's framing**: those four
  `unsupportedNonlin` cases are `ScanGen.lean`'s `template2`, whose `.pointwise .relu` sits on the
  **recurrence statement inside the scan block** (`nonlin := .pointwise .relu` on the step-block
  assignment), not at top level. Per the ruled scope boundary (scan-block nonlin stays rejected,
  ruling 6), **this split does not change** as a mechanical consequence of this thread — it is not
  "some of those 4 may now compile." Task 6 re-runs it as a confirmatory regression check, not an
  expected-to-change count.
- `test/Eval/Portfolio/ScatterNonlinRejectTest.lean` (RSN1-4) tests **scatter** statements, rejected
  by `checkStmt`'s `.scatter nm .. => throw (.scatterOrAffineLhs nm)` **unconditionally**, before
  `checkNonlin` is ever reached — confirmed by reading `checkStmt` directly. This file needs no
  change; it is not testing the same mechanism this thread touches at all (it also exercises the
  legacy `DSL/Pipeline/Structural.lean`'s own `checkScatterNonlin`, a completely separate rejection
  path).
- Real, hand-verified-elsewhere fixture donors exist for all eight nonlin functions already, so no
  new fixture value needs deriving from scratch — see each task's Fixtures list for exact
  `test`/`#guard` names and expected tensors.
- `.claude/skills/slice-plan/check-snippet.sh` ran clean against every Lean fragment this plan
  ships (four snippets: raw types + manual `BEq` instances for `PointwiseFn`/`AxiswiseFn`; the
  full `checkPointwise`/`checkAxiswise`/`CheckedPointwisePlan`/`CheckedAxiswisePlan`/
  `runDensePointwise`/`runDenseAxiswise` block plus a `sourceSlots`/`destinationSlots` mirror match;
  `resolveNonlinAxis`/`NonlinCompileError` with five `#guard`s against real `LHSSlot`/`Nonlin`
  values; and a 4-constructor `PlanStep`-shaped sum using the **real** `RawScanPlan`/`AssignPlan`
  deriving `DecidableEq, BEq, Repr, Inhabited`) — all four compiled clean on the first pass except
  for one unused-variable lint warning in an illustrative (non-shipped) snippet.

### 0a. Extensibility/code-sharing vetting addendum (same day, follow-up pass)

Requested explicitly: before executing this plan, re-examine whether it is the best design for
future nonlinearity additions and whether more code sharing is possible. Two real gaps were found
by reading `Eval/Nonlin.lean` and the drafted checker/worker signatures side by side — an
asymmetry between `PointwiseFn`'s and `AxiswiseFn`'s dispatch, and duplicated geometry checks
between `checkPointwise`/`checkAxiswise`. Both are fixed in the task text below; the resulting
design (`AxiswiseFn.apply`, `checkNonlinIO`) and its rationale are written up in §3's two new "Why"
subsections (**"Why `AxiswiseFn.apply` exists"** and **"Why `checkPointwise`/`checkAxiswise` share
`checkNonlinIO`"**) alongside this thread's other design decisions, not repeated here. This entry
records only what was verified: both fixes were checked via `check-snippet.sh` against the real
repo (two more snippets beyond the original four, both green on the corrected pass — full tally in
§8), and one confirmed-but-out-of-scope limit was noted rather than solved: `PointwiseFn`/
`AxiswiseFn` are bare (payload-free) enum constructors, so a future *parametric* nonlinearity
(configurable-α ELU, temperature-scaled softmax) would need a constructor carrying its own
field(s) — a `DSL/Ast.lean` language-design change, outside this thread's remit and not something
either fix forecloses or complicates.

## 1. Purpose

Implement Backend Eval IR's nonlinearity thread (architecture doc §7.6 thread 4) for the **Dense**
interpreter only: two new `PlanStep` cases (`.pointwise`, `.axiswise`) mirroring `Nonlin`'s AST
shape, reachable from real surface DSL syntax at the top level (not inside a scan block), checked
and executed by reusing `Eval/Nonlin.lean`'s existing float64 math rather than reimplementing it.

**Dense's role here is to establish checked reference semantics, not to be the permanent
consumer** — JAX, not Dense, is the intended primary long-term backend for this Eval IR (per the
user's own stated intent). See §2.2's JAX bullet for why JAX support itself is out of this thread's
scope, why that's a near-term follow-up rather than an indefinite deferral, and why the checked
types this thread introduces are already backend-neutral enough for that follow-up to build on
directly.

## 2. Scope

### 2.1 In scope

- New raw types `RawPointwisePlan`/`RawAxiswisePlan`, a closed checker-level error family
  (`NonlinPlanError`), a shared geometry-check helper (`checkNonlinIO`, factoring the case×class
  rows common to both step kinds) plus the two checkers built on it (`checkPointwise`/
  `checkAxiswise`), and dense workers (`runDensePointwise`/`runDenseAxiswise`) in a new file
  `LeanNCD/Eval/Plan/Nonlin.lean`.
- A small, additive, behavior-preserving edit to `LeanNCD/Eval/Nonlin.lean`: a new
  `AxiswiseFn.apply`, symmetric with the file's existing `PointwiseFn.apply` ("owned by the enum,
  so a new [pointwise] function has exactly one place to be interpreted"), and `applyNonlin`
  refactored to delegate both cases to their enum's own method (§0a) — closes the one asymmetry
  found while vetting this design for future extensibility.
- Two new `PlanStep` constructors, wired into every exhaustive match `RawStep.lean`'s doc comment
  already warns touches (`checkPlan`, `runDensePlan`, `PlanStep.sourceSlots`/`destinationSlots`,
  `CheckedPlanStepEvidence`).
- Real top-level source compilation: `checkNonlin`'s **top-level statement** call site
  (`checkStmt`) admits `.pointwise`/`.axiswise`; `checkLHSSlot` admits `.freeNorm` (relaxed, not
  removed — consistency with `Nonlin` is deferred to compile tier, mirroring
  `checkScanLHSSlot`'s own "admit syntactically, validate later" split); `prepareEvalPlan`'s Step D
  compiles a nonlin-bearing plain statement into **two** chained `PlanStep`s (see Architecture).
  A new `NonlinCompileError` family (in `Error.lean`, alongside `ScanCompileError`) and a
  `resolveNonlinAxis` function (in `Compile.lean`) own the freeNorm-axis/`Nonlin`-kind consistency
  check this needs.
- Deleting `RawEvalPlan.numericMode`/`NumericMode`/`PlanError.numericModeNotAdmitted` and every
  reference (ruling 3 — see §0's exact file/test list).
- Correcting `papers/jax_evalplan_architecture.md` §7.6's thread 4 row and §2.2's closing sentence
  to state Dense-only landed, with PyTorch and JAX given distinct framing rather than one merged
  "deferred" clause (Task 5; rationale in §2.2's JAX bullet).
- New hand-built differential fixtures exercising top-level pointwise/axiswise end-to-end (no
  existing generator produces such a program), plus a confirmatory (not expected-to-change) re-run
  of the existing scan corpus split.

### 2.2 Explicitly out of scope (deliberate, not deferred silently)

- **Nonlinearity inside a scan base/step block stays rejected.** `checkScanBlockStmt`'s
  `checkNonlin` call site is unchanged. `Stmt.recurMorphism`'s forced `.identity` (`Stmt.nonlinOf`)
  is independent structural evidence this was never meant to be a live combination; the
  architecture doc's thread 4 text describes new *outer* `PlanStep` cases only. State this in the
  completion record as a scope boundary, not a gap.
- **Masked axiswise nonlinearities (`Nonlin.axiswise fn (some _)`) are rejected**, at the compile
  tier (`NonlinCompileError.maskedAxiswiseNotSupported`), before a `RawAxiswisePlan` can exist.
  `RawAxiswisePlan` carries **no mask field at all** — not a reserved-but-unused one. Rationale:
  Plan-level `TensorSignature` is `{ shape : Array Nat; dtype : ScalarDType }` with **no axis-UID
  information whatsoever** (compiled away by design — `Kernel.lean`'s own doc comment: "no graph
  scheduling, no source names, no axis UIDs"). `softmaxT`/`normalizeT`/`l2normalizeT`'s mask
  branch needs `axisUids : List UID` to build a `HashMap UID Int` for `evalBool`; building a
  UID-free, position-based compiled predicate IR to support this would be new IR design work with
  no precedent in this codebase (`Factor.iverson`/masks are *already* uniformly rejected
  everywhere else the Plan compiler touches them, via the same `CapabilityError.maskOrPredicate`
  this plan reuses) — clearly outside "implement nonlinearity new `PlanStep` cases." This is a
  **finding from this session's verification pass, not one of the pre-agreed rulings** — flagged
  prominently per the task brief's own instruction to report such findings plainly.
  `CapabilityError.maskOrPredicate` is reused verbatim (its doc comment already reads "masks,
  predicates, Iverson factors" — an axiswise mask is exactly that).
- **PyTorch interpreter support is deferred with no scheduled thread** — mirrors thread 5's own
  precedent phrasing verbatim ("no client has asked for it... deferred with no scheduled thread,
  not merely sequenced later"). Nothing about this thread changes that status.
- **JAX interpreter support is out of scope for this thread, but not for the reason PyTorch is.**
  Per the user's own stated intent, JAX — not Dense — is the intended **primary long-term
  consumer** of this whole Eval IR; Dense's role in this thread is to establish the checked
  reference semantics (§2.2's `reference64Transcendental` contract) a future JAX lowering must
  match, not to be a permanent parallel backend. JAX is excluded here purely because
  `experiments/jax_bridge/EvalPlanCodegen.lean` is already broken against Wave F's `PlanStep`/
  `CheckedPlanStepEvidence` generalization — confirmed by directly running `lake build
  JaxExperiment` this session (§0) — an unrelated, pre-existing repair with its own blast radius,
  not something to rush into this thread's tail end alongside new nonlinearity semantics. **This is
  a near-term follow-up priority, not an indefinitely-deferred one like PyTorch**: the natural next
  slice after this one is (a) repair `EvalPlanCodegen.lean`'s `PlanStep` breakage on its own, with
  no nonlinearity content, then (b) add `.pointwise`/`.axiswise` JAX lowering on top of the checked
  types this thread introduces (`RawPointwisePlan`/`RawAxiswisePlan`/`CheckedPointwisePlan`/
  `CheckedAxiswisePlan` are already backend-neutral — only `runDensePointwise`/`runDenseAxiswise`
  are Dense-specific, exactly the same relationship `.assign`/`.scan` already have with thread 5's
  `loweringToAffineTableCandidate`/`loweringToEinsumCandidate`). A future JAX lowering should also
  follow §0a's "owned by the enum" single-dispatch-point pattern (a `PointwiseFn.toJax`/
  `AxiswiseFn.toJax`-shaped pair, analogous to `PointwiseFn.apply`/`AxiswiseFn.apply` but lowering
  to JAX expressions instead of computing `DenseTensor`s directly) rather than inlining a fresh
  match in the lowering file. Do not conflate this bullet's framing with PyTorch's above when
  writing Task 5's doc correction or Task 7's completion record — they are deferred for different
  reasons and at different urgency, and treating them identically would misstate JAX's real
  priority to the next thread's author.
- `reference64Transcendental`'s per-function ULP bounds (architecture doc §2.2 table) are recorded
  as named Lean constants **with bit-exact pinning fixtures only for the four 0-ULP functions**
  (`relu`, `leakyrelu`, `normalize`, `l2normalize`). `sigmoid`/`tanh`/`gelu`/`softmax`'s stated ULP
  bounds (2/2/4/2-per-element) are **not empirically validated** in this thread — there is no
  second backend to differential-test against once JAX is out of scope. The architecture doc's
  thread 1 status ("Specified, not validated") is unchanged by this thread; state this explicitly
  in the completion record rather than silently dropping the distinction.

## 3. Architecture: how a nonlin statement compiles (new, not previously documented)

This is the part of the design not literally spelled out in the pre-agreed rulings; it was worked
out this session to make "checkNonlin's top-level call site becomes real compilation" concrete and
is verified against real code, not asserted.

**The problem.** `RHSExpr.nonlin` attaches to the *same* statement as the affine/contraction body
(`RHSExpr { body; nonlin; agg }`), but `PlanStep.assign`'s payload, `AssignPlan`, has no nonlin
field of its own — and per ruling 1, the new `PlanStep` cases are entirely separate node kinds.
`.axiswise`'s reduction axis is named only by a `.freeNorm`-marked LHS slot (`s.`/`m.` surface
syntax), and `checkLHSSlot` (the top-level LHS-slot preflight) currently rejects `.freeNorm`
outright — meaning **no source program using `softmax`/`normalize`/`l2normalize` can compile
through the Plan pipeline unless `checkLHSSlot` is also relaxed**; leaving it rejecting would make
`.axiswise` type- and checker-complete but permanently unreachable from surface syntax, which is
not "Dense interpreter support" as the architecture doc's thread 4 row states it.

**The design.** A nonlin-bearing plain statement compiles to **two chained `PlanStep`s**: the
existing linear `AssignPlan` (unchanged, publishing into a new *internal* slot instead of the
statement's name), followed by a `.pointwise`/`.axiswise` step reading that internal slot and
writing the slot actually published under the statement's name. `rhs.nonlin = .identity` keeps
today's single-step behavior exactly (no internal slot, the `AssignPlan` publishes directly).

```text
rhs.nonlin = .identity        : [ .assign  → publish as `nm` ]                      (unchanged)
rhs.nonlin = .pointwise pf    : [ .assign  → internal slot ] → [ .pointwise → publish as `nm` ]
rhs.nonlin = .axiswise fn none: [ .assign  → internal slot ] → [ .axiswise  → publish as `nm` ]
rhs.nonlin = .axiswise _ (some _) : rejected at compile tier (NonlinCompileError), no PlanStep built
```

`checkLHSSlot` relaxes `.freeNorm` to `pure ()` (same treatment as `.free`) — syntactically
admitted, exactly like `checkScanLHSSlot` already admits `.iterAt`/`.iterNext` while deferring
cross-construct consistency. Consistency between a statement's LHS markers and its `Nonlin` kind
is **not** re-litigated as another preflight rule (`checkStmt`'s existing sub-construct order is
unchanged) — it moves to a new, dedicated compile-tier function, `resolveNonlinAxis`, mirroring
`ScanCompileError`'s own "second closed family beside `CapabilityError`" precedent (§0):

```lean
inductive NonlinCompileError
  | noMarkedReductionAxis       (stmtName : String)
  | multipleMarkedReductionAxes (stmtName : String) (firstPos secondPos : Nat)
  | unmarkedReductionAxis       (stmtName : String) (pos : Nat)
  | maskedAxiswiseNotSupported  (stmtName : String)
  deriving DecidableEq, BEq, Repr, Inhabited

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
```

Verified via `check-snippet.sh` against real `LHSSlot`/`Nonlin`/`DSL.Ast` values, including five
`#guard`s: a valid single-freeNorm axiswise case, a missing-marker rejection, a masked-axiswise
rejection, a marker-present-but-pointwise rejection, and the unmarked-identity pass-through.

`PlanCompileCause` (`EvalPlan.lean`) gains a `.nonlin (cause : NonlinCompileError)` arm alongside
its existing `.scan (cause : ScanCompileError)`, with a matching `liftNonlin` in `Compile.lean`
beside `liftCapability`/`liftShape`/`liftPlanError`/`liftBindings`.

**Why this doesn't need a second local-operation representation.** The new `.pointwise`/
`.axiswise` steps are single-source/single-destination with no term/factor/reduction structure at
all — closer to `.scan`'s "generic path" through `PlanStep.sourceSlots`/`destinationSlots` than to
`.assign`'s per-term/per-factor loop. `checkPlan`'s three match blocks each gain a `.pointwise _ |
.axiswise _` arm sitting beside the existing `.scan _` arm (same generic-path treatment, same
placeholder `0 0` locators for `invalidForwardRead`), not a new loop shape.

**Why `sourceSlot == destinationSlot` needs no guard inside `checkPointwise`/`checkAxiswise`.**
`checkPlan`'s own wiring discipline makes this unreachable structurally, not by luck: a step's
destination must be *unavailable* immediately before the step (checked first), and (via the
generic `sourceSlots` path) its source must be *available* at that same point, read from the same
`available` table before this step's own destination is marked produced. The same table entry
cannot be both `false` (required for the destination check to pass) and `true` (required for the
source check to pass) at once, so a hand-built `RawPointwisePlan`/`RawAxiswisePlan` with
`sourceSlot == destinationSlot` is rejected by `checkPlan` (as `invalidForwardRead`) before
`checkPointwise`/`checkAxiswise` is ever called with it, for **every** destination that was not
already produced by an earlier step. (If the destination *was* already produced — e.g. reused as
an unrelated later output — `checkPlan`'s destination-availability check rejects it even earlier,
as `inputSlotOverwritten`/`duplicateDestination`.) This is a call-site precondition the checker
relies on rather than re-verifies, in the same spirit `Scan.lean` flags for `baseWriteRowsOk`'s own
preconditions (§4's case×class table) — Task 2 pins it with a regression fixture at the `checkPlan`
level specifically, not inside `checkPointwise`/`checkAxiswise`'s own tests, so the reliance is
tested rather than folklore.

**Why `AxiswiseFn.apply` exists, mirroring the already-existing `PointwiseFn.apply`.**
`Eval/Nonlin.lean` already has `PointwiseFn.apply : PointwiseFn → DenseTensor → DenseTensor`,
whose own doc comment states the design intent explicitly: "owned by the enum, so a new pointwise
function has exactly one place to be interpreted." `AxiswiseFn` never got the same treatment — the
legacy `applyNonlin`'s `.axiswise` case inlines a 3-way match over `softmax`/`normalize`/
`l2normalize` directly, and a first draft of this plan's `runDenseAxiswise` would have duplicated
that same inline match a second time, permanently losing the single-touch-point property
`PointwiseFn` already has. Adding `AxiswiseFn.apply : AxiswiseFn → Nat → List UID → Option
BoolExpr → DenseTensor → DenseTensor` to `Eval/Nonlin.lean`, symmetric with `PointwiseFn.apply`,
and refactoring `applyNonlin` to delegate both cases to the enum's own method, closes that gap —
verified compiling and **behavior-preserving** (five `#guard`s comparing the refactored
`applyNonlin` against its real pre-refactor form on identity/pointwise/all-three-axiswise cases,
all equal on `.data`; §0a). After this, a future new pointwise or axiswise function touches
exactly: its constructor in `DSL/Ast.lean`, its own `*T` implementation plus one match arm in
`PointwiseFn.apply`/`AxiswiseFn.apply` (both `Eval/Nonlin.lean`), and a new fixture — nothing in
`Eval/Plan/Nonlin.lean` changes, since the Plan-layer checker is fully function-agnostic (§4's
table: no row depends on `fn`) and the Plan-layer worker (`runDensePointwise`/`runDenseAxiswise`,
Task 2) delegates its entire per-function dispatch to the enum, exactly as pointwise already does.
One pre-existing, unavoidable cost this doesn't remove: `PointwiseFn.toBrOp`/`AxiswiseFn.toBrOp`
(`DSL/Ast.lean`, the old `Br`/categorical lowering, unrelated to `Eval/Plan/`) still gains a new
match arm per future constructor — a property of the AST's own shape, not introduced or worsened
by this thread's design. A future JAX lowering (§2.2's next-slice note) should follow this same
single-dispatch-point pattern (`PointwiseFn.toJax`/`AxiswiseFn.toJax`) rather than inlining a fresh
match of its own.

**Why `checkPointwise`/`checkAxiswise` share a `checkNonlinIO` helper instead of each checking
their own geometry inline.** §4's case×class table rows 1-7 are identical obligations for both
step kinds (slot range, dtype, shape agreement) — only row 8 (`axisPos` range) is
axiswise-specific. Writing both checks out inline in both functions would put two near-identical
~6-guard blocks in the same new file, exactly the shape a reviewer can miss precisely *because*
both are new (a diff shows no prior version to compare drift against). `checkNonlinIO (sigs)
(sourceSlot destinationSlot : TensorSlot) (shape : Array Nat) : Except NonlinPlanError
(TensorSignature × TensorSignature)` factors rows 1-7 once; `checkPointwise` calls it and returns,
`checkAxiswise` calls it then adds row 8 on top. Verified compiling with five `#guard`s (a passing
case, a `slotOutOfRange`, a `sourceShapeMismatch`, and a passing/failing `axisPositionOutOfRange`
pair through `checkAxiswise` specifically, confirming the shared helper's failures propagate
through the axiswise-specific wrapper correctly; §0a). This also lets Task 1's mutation-testing
cover rows 1-7 once (through `checkPointwise`) plus one delegation check (through `checkAxiswise`),
rather than mutating all seven rows through both functions independently.

**Why `PointwiseFn`/`AxiswiseFn` need a manual `BEq` instance, not a `deriving` clause edit.**
Both derive `DecidableEq, Repr, Lean.ToExpr, Inhabited` in `DSL/Ast.lean` — no `BEq`. `PlanStep`
derives `DecidableEq, BEq, Repr, Inhabited` today, and many existing tests compare `RawEvalPlan`/
`PlanStep` values with `==` (needs `BEq`, not just `DecidableEq`), so `PlanStep`'s new payload
types must support `BEq` too, or `PlanStep`'s own `deriving BEq` breaks. Rather than touching
`DSL/Ast.lean` (surgical-changes discipline — this thread does not otherwise touch that file), add

```lean
instance : BEq LeanNCD.PointwiseFn := ⟨fun a b => decide (a = b)⟩
instance : BEq LeanNCD.AxiswiseFn := ⟨fun a b => decide (a = b)⟩
```

in the new `Nonlin.lean` (built from the existing `DecidableEq` instance, standard and verified to
compile and behave correctly via two `#guard`s). `AggOp`/`BoolExpr` have the identical
missing-`BEq` shape and are not touched — nothing downstream of them needs to derive `BEq` today.

## 4. Case × class table — `checkPointwise`/`checkAxiswise` geometry obligations

Required per the slice-plan skill: a new geometry-checking predicate family gets this table as an
explicit deliverable even though it is not an *instance* of the write-geometry defect family found
four times in F3/F4 (free-extent, pinned-literal, write-map-rank, `stepWriteRowsOk`) — verified
below, not assumed, since every `(c)` cell is a candidate instance *N+1* regardless of ancestry.

| # | Case | Pointwise | Axiswise | Class |
|---|---|---|---|---|
| 1 | `sourceSlot` in range | checked (`slotOutOfRange`) | checked | **Required** |
| 2 | `destinationSlot` in range | checked | checked | **Required** |
| 3 | source dtype `== .f64` | checked (`dtypeNotAdmitted`) | checked | **Required** |
| 4 | destination dtype `== .f64` | checked | checked | **Required** |
| 5 | source dtype `==` destination dtype | checked (`dtypeMismatch`) | checked | **Required**, vacuous today — only `.f64` exists (same single-valued-vocabulary shape as `checkAssign`'s own `dtypeMismatch`) |
| 6 | source signature shape `==` declared `shape` | checked (`sourceShapeMismatch`) | checked | **Required** |
| 7 | destination signature shape `==` declared `shape` | checked (`destinationShapeMismatch`) | checked | **Required** |
| 8 | `axisPos < shape.size` | n/a | checked (`axisPositionOutOfRange`) | **Required** (axiswise only) |
| 9 | rank-0 (scalar) `shape` | admitted | rejected as a corollary of #8 (`0 < 0` is false) | Silently admitted (pointwise, harmless — elementwise map over a 1-element array); not a separate case for axiswise |
| 10 | mask present (`Nonlin.axiswise fn (some _)`) | n/a | **Forbidden**, but at the compile tier (`NonlinCompileError.maskedAxiswiseNotSupported`) before a `RawAxiswisePlan` can exist — the raw type carries no mask field at all | Forbidden by type absence, not by a runtime-checked predicate |
| 11 | negative `axisPos` | n/a | Forbidden by type (`axisPos : Nat`) | Forbidden by type |
| 12 | `sourceSlot == destinationSlot` (self-aliasing) | not checked locally | not checked locally | Silently ignored *here*, but proven unreachable by `checkPlan`'s own availability discipline (§3) — pinned by a Task 2 regression fixture at the `checkPlan` level, not treated as folklore |
| 13 | two steps writing the same `destinationSlot` | not checked | not checked | Silently ignored by design — owned by `checkPlan`'s outer wiring loop (`duplicateDestination`/`inputSlotOverwritten`), identical division of labor to `checkAssign` |
| 14 | `sourceSlot` read before produced/available | not checked | not checked | Silently ignored by design — owned by `checkPlan`'s outer wiring loop (`invalidForwardRead` via the generic `sourceSlots` path), identical to `.scan`'s own treatment |
| 15 | worker-side out-of-bounds write | n/a | n/a | **Not a write-path predicate at all** — verified by reading every reused function: `reluT`/`sigmoidT`/`tanhT`/`geluT`/`leakyReluT` are `⟨t.shape, t.data.map f⟩` (shape- and length-preserving by construction); `softmaxT`/`normalizeT`/`l2normalizeT`'s `perRow` writes back only to coordinates it read from the same tensor. There is no second "target" tensor addressed via an independently-boundable affine map the way `commitWrite` (`Scan.lean`) has — this is the structural reason this family is not a 5th instance of the free-extent/pinned-literal/write-rank/`stepWriteRowsOk` defect shape, not merely an unexamined absence |

## 5. Task graph and review weight

```text
Task 1: raw types + checker ──┐
                               ├─> Task 3: source compiler ─┐
Task 2: dense worker + wiring ┘                             ├─> Task 6: differential/corpus ─> Task 7: closure
Task 4: numericMode removal ────────────────────────────────┤
Task 5: doc corrections ─────────────────────────────────────┘
```

Tasks 1 and 2 both touch the closed `PlanStep`/`CheckedPlanStepEvidence` sums that every backend
depends on — soundness-relevant, per the task brief's own instruction. Task 3 is the thread's
architectural centerpiece (§3). Tasks 4 and 5 are independent of 1-3 and of each other. Task 6
depends on Task 3 (needs real compiled nonlin steps to differential-test) and on Task 4 (fixture
literals must already have `numericMode` gone). Task 7 is the mandatory whole-branch close.

| Task | Outcome | Independent review reason | Risk / process weight |
|---|---|---|---|
| 1 | `RawPointwisePlan`/`RawAxiswisePlan`, `NonlinPlanError`, `checkPointwise`/`checkAxiswise` | New checker over a soundness-relevant closed family; the case×class table is itself a review artifact | **Moderate.** ~6 fixtures (one per §4 required-row failure, mutation-tested) plus the manual `BEq` instances — small production surface, but wrong here means silently-wrong nonlin results everywhere. |
| 2 | `runDensePointwise`/`runDenseAxiswise`, `PlanStep` extended to 4 constructors, all four exhaustive matches updated | Touches the closed sum every backend and every existing `.assign`/`.scan` test depends on — a regression here is invisible in a diff that only shows added match arms | **High.** Two independent final reviewers for this task specifically (not just the whole-branch review) — this is the "touches a soundness-relevant closed sum" case the task brief calls out by name. ~4-5 fixtures (one hand-built hybrid graph per new constructor, plus the sourceSlot==destinationSlot regression from §3/§4 row 12). |
| 3 | `checkLHSSlot` relaxed, `checkNonlin` real at top level, `resolveNonlinAxis`/`NonlinCompileError`, `prepareEvalPlan` two-step chaining | Main production feature; new classification logic with no precedent to copy (§3) | **High.** No fixture count discount — this is genuinely new compiler logic. Expect at least one fix round; do not compress its review because Tasks 1/2 land clean. |
| 4 | `numericMode`/`NumericMode`/`numericModeNotAdmitted` deleted everywhere (§0's exact list) | Touches every `RawEvalPlan` literal in the test suite — a reviewer needs the exact file list to confirm nothing was missed, not just skim a diff | **Low-moderate.** Mechanical but wide (5 production files, 9 test files by exact count in §0). One review round. |
| 5 | Architecture doc §7.6 row + §2.2 sentence corrected | Normative-doc content edit with a real gate (old text gone, new text present, style matches thread 5's precedent) | **Low.** Doc-only; still gets its own gate (grep-verified), not folded silently into Task 7's closure. |
| 6 | New end-to-end pointwise/axiswise differential fixtures; confirmatory (not expected-to-change) re-run of the scan corpus split; `ScatterNonlinRejectTest.lean` confirmed out of scope | No existing generator exercises the new reachable fragment — this task's fixtures are the only evidence the Dense path is *actually* correct end-to-end, not just checker-clean | **Moderate-high.** 8 new fixtures (one per nonlin function, donors named in Task 6), each compared against `evalScheduled` bit-for-bit. |
| 7 | Completion record, `AGENTS.md`/`LeanNCD.lean` discoverability, whole-branch review | Every prior slice's most valuable finding came from the whole-branch tier, never a per-task diff (skill §4) | **High.** Two independent final reviewers (soundness-relevant closed sum, per the task brief) — schedule both, do not compress to one because Tasks 1-6 passed clean. |

## Task 1: raw types, closed error family, geometry checkers

### Outcome

`LeanNCD/Eval/Plan/Nonlin.lean` exists with `RawPointwisePlan`/`RawAxiswisePlan`,
`NonlinPlanError`, `CheckedPointwisePlan`/`CheckedAxiswisePlan`, a shared `checkNonlinIO` helper,
and `checkPointwise`/`checkAxiswise` built on it, each satisfying every "Required" row of §4's
table.

### Files

- `LeanNCD/Eval/Plan/Nonlin.lean` (new)
- `test/Eval/Plan/NonlinCheckTest.lean` (new)

### Implementation

1. `import LeanNCD.Eval.Plan.Kernel` and `import LeanNCD.Eval.Nonlin` (gives `TensorSlot`/
   `TensorSignature`/`ScalarDType` and `LeanNCD.PointwiseFn`/`AxiswiseFn`/the dense math
   transitively via `DSL.Ast`/`Eval.Tensor`). Add the manual `BEq` instances from §3.
2. Add `RawPointwisePlan { sourceSlot destinationSlot : TensorSlot; shape : Array Nat; fn :
   LeanNCD.PointwiseFn }` and `RawAxiswisePlan { sourceSlot destinationSlot : TensorSlot; shape :
   Array Nat; axisPos : Nat; fn : LeanNCD.AxiswiseFn }`, both `deriving DecidableEq, BEq, Repr,
   Inhabited` — verified via `check-snippet.sh` (§0).
3. Add `NonlinPlanError` exactly as drafted in §4's row list (`slotOutOfRange`, `dtypeNotAdmitted`,
   `dtypeMismatch`, `sourceShapeMismatch`, `destinationShapeMismatch`, `axisPositionOutOfRange`),
   `deriving DecidableEq, BEq, Repr, Inhabited`.
4. Add `CheckedPointwisePlan`/`CheckedAxiswisePlan` with `private mk ::` (not bare `structure ...
   where private` — the F2/Wave-C-documented trap), each wrapping a `raw` field, `deriving Repr`.
5. Implement `checkNonlinIO (sigs) (sourceSlot destinationSlot : TensorSlot) (shape : Array Nat) :
   Except NonlinPlanError (TensorSignature × TensorSignature)` exactly as verified in §0a, covering
   §4's rows 1-7 (the obligations common to both step kinds) in the same order `checkAssign` uses
   (destination lookup, source lookup, dtype checks, shape checks). `checkPointwise` calls it and
   returns; `checkAxiswise` calls it then adds row 8's `axisPos < shape.size` check on top — neither
   function repeats rows 1-7's checks itself.

### Fixtures (donors named, per skill discipline)

All in `test/Eval/Plan/NonlinCheckTest.lean`, mirroring `GraphDenseTest.lean`'s `oneNodeSigs`-style
hand-built signature tables (not cloned from an existing Plan-layer fixture — no prior
pointwise/axiswise Plan fixture exists to clone from; each is a minimal 2-slot table, `shape :=
#[2]`, built directly per §4's row):

- One passing `RawPointwisePlan`/`RawAxiswisePlan` each (baseline — clone this table for every
  mutation below, changing exactly the one field named).
- Row 1/2: `sourceSlot`/`destinationSlot` set past `sigs.size` → `slotOutOfRange`.
- Row 3/4: a signature with `dtype := .bool` at the source/destination slot → `dtypeNotAdmitted`.
- Row 6/7: `shape := #[3]` on the raw plan against a `#[2]`-shaped signature → `sourceShapeMismatch`/
  `destinationShapeMismatch`.
- Row 8 (axiswise only): `axisPos := 2` against `shape := #[2]` (rank 2, valid positions 0-1) →
  `axisPositionOutOfRange`.
- Row 9: `shape := #[]` (rank 0) pointwise passes; rank-0 axiswise with `axisPos := 0` is rejected
  by row 8's own guard (`0 < 0` false) — one fixture confirming this, not a separate check.

### Mutation checks

- Remove each `unless` guard in `checkNonlinIO` independently; confirm the corresponding fixture
  through `checkPointwise` starts passing when it should fail (i.e. the guard was load-bearing),
  **then confirm the same guard's removal is also visible through `checkAxiswise`** with one
  fixture (not all seven) — this confirms delegation rather than re-mutating rows 1-7 a second
  time. Remove row 8's `axisPos` guard independently (axiswise-only, no pointwise analogue).
- Restore; confirm all fixtures pass again.

### Gate

```bash
cd leanncd
lake build Eval.Plan.NonlinCheckTest
lake build LeanNCD
```

Independent task review before Task 3 (Task 2 can run in parallel with this review since it only
needs Task 1's *types*, not its passing review, to start drafting — but must not merge ahead of
Task 1's review completing).

## Task 2: dense workers and `PlanStep` wiring

### Outcome

`PlanStep` has four constructors; `checkPlan`/`runDensePlan`/`PlanStep.sourceSlots`/
`destinationSlots`/`CheckedPlanStepEvidence` all handle `.pointwise`/`.axiswise` via the generic
(non-`.assign`) path; a hand-built `RawEvalPlan` chaining `.assign → .pointwise` and `.assign →
.axiswise` end-to-end passes `checkPlan` + `runDensePlan` and produces the expected tensor.

### Files

- `LeanNCD/Eval/Plan/Nonlin.lean` (adds `runDensePointwise`/`runDenseAxiswise`)
- `LeanNCD/Eval/Nonlin.lean` (adds `AxiswiseFn.apply`; refactors `applyNonlin` to delegate to
  `PointwiseFn.apply`/`AxiswiseFn.apply` — small, additive, behavior-preserving, §0a)
- `LeanNCD/Eval/Plan/RawStep.lean` (adds `import LeanNCD.Eval.Plan.Nonlin`; `PlanStep` gains
  `.pointwise (p : RawPointwisePlan)` / `.axiswise (a : RawAxiswisePlan)`)
- `LeanNCD/Eval/Plan/EvalPlan.lean` (`CheckedPlanStepEvidence`, `PlanStep.sourceSlots`,
  `PlanStep.destinationSlots`, `checkPlan`'s three match blocks, `runDensePlan`'s dispatch)
- `test/Eval/Plan/NonlinDenseTest.lean` (new)
- `test/Eval/Plan/GraphCheckTest.lean` (one new regression fixture, §3's `sourceSlot ==
  destinationSlot` unreachability claim)

### Implementation

1. In `LeanNCD/Eval/Nonlin.lean`: add `AxiswiseFn.apply (fn : AxiswiseFn) (axisPos : Nat)
   (axisUids : List UID) (mask? : Option BoolExpr) (t : DenseTensor) : DenseTensor`, matching
   `fn` to call `softmaxT`/`normalizeT`/`l2normalizeT` — symmetric with the file's existing
   `PointwiseFn.apply`, verified compiling in §0a. Refactor `applyNonlin`'s `.pointwise`/
   `.axiswise` cases to `pf.apply t` / `fn.apply p axisUids m t` respectively — verified
   **behavior-preserving** via five `#guard`s against the real (pre-refactor) `applyNonlin` in §0a;
   re-run `test/Eval/NonlinTest.lean` unchanged afterward as the production regression check (it
   already exercises `resolveNonlin`/`applyNonlin` directly and must stay green with zero edits).
2. `runDensePointwise (c : CheckedPointwisePlan) (src : DenseTensor) : DenseTensor :=
   c.raw.fn.apply src` (reuses `PointwiseFn.apply` — no new math).
3. `runDenseAxiswise (c : CheckedAxiswisePlan) (src : DenseTensor) : DenseTensor :=
   c.raw.fn.apply c.raw.axisPos [] none src` (reuses the new `AxiswiseFn.apply` from item 1 — no
   new math, no new match). `[]`/`none` because a checked `RawAxiswisePlan` can never carry a mask
   or axis-UID (§3 — Plan-layer `TensorSignature` is UID-free by design); verified via
   `check-snippet.sh` that this compiles against the real functions.
4. `RawStep.lean`: add the import, extend `PlanStep`'s `deriving` list unchanged (`DecidableEq,
   BEq, Repr, Inhabited` — already verified compiling with the two new constructors, §0).
5. `EvalPlan.lean`:
   - `CheckedPlanStepEvidence` gains `| pointwise (c : CheckedPointwisePlan) | axiswise (c :
     CheckedAxiswisePlan)`.
   - `PlanStep.sourceSlots`/`destinationSlots` gain `| .pointwise p => #[p.sourceSlot]` / `#
     [p.destinationSlot]` and the `.axiswise` analogues.
   - `checkPlan`'s context-check match: `.scan _ => pure ()` becomes `.scan _ | .pointwise _ |
     .axiswise _ => pure ()` (no top-level context obligation for any of the three).
   - `checkPlan`'s source-check match: the `.scan _ => (generic sourceSlots loop)` arm becomes `|
     .scan _ | .pointwise _ | .axiswise _ => (same loop)`.
   - `checkPlan`'s dispatch match gains `| .pointwise p => match checkPointwise raw.tensorSigs p
     with .error e => throw (.assign (.nodeError ni e)) | .ok c => checkedNodes := ...push (.pointwise
     c)` — **note the error wrapping is `.assign (.nodeError ...)`, matching the existing doc
     comment's own framing** ("`.assign`/`.scan` name the ERROR'S OWN SHAPE, not the failing step's
     kind") — `NonlinPlanError` needs its own `PlanStepError` treatment: since `PlanStepError`
     today is `| assign (cause : PlanError) | scan (stepIndex : Nat) (cause : ScanPlanError)`, and
     `NonlinPlanError` is neither, add a third constructor `| nonlin (stepIndex : Nat) (cause :
     NonlinPlanError)` (mirroring `.scan`'s shape exactly, not wrapped through `.assign`) — verify
     this against `checkPlan`'s call sites before writing the throw expressions above; a
     `PlanStepError.nonlin ni e` throw, not `.assign (.nodeError ni e)`, since `NonlinPlanError`
     is not a `PlanError`. The `.axiswise` arm is the same shape with `checkAxiswise`.
   - `runDensePlan`'s dispatch gains `| .pointwise c => store := store.set! c.raw.destinationSlot
     (runDensePointwise c (store.getD c.raw.sourceSlot placeholder))` and the `.axiswise` analogue.
6. `PlanStepError` gains the `.nonlin` constructor from item 5; re-derive
   `DecidableEq, BEq, Repr, Inhabited` (already required fields all support it).

### Fixtures (donors named)

`test/Eval/Plan/NonlinDenseTest.lean`, cloning `GraphDenseTest.lean`'s `idRead`/`idNode`/
`oneNodeSigs`/`oneNodePlan` shape directly (same donor style: hand-computed expected tensor, not
read back from the interpreter):

- **Pointwise chain**: clone `oneNodePlan`, change `steps` to `#[.assign (idNode 1 0), .pointwise {
  sourceSlot := 1, destinationSlot := 2, shape := #[2], fn := .relu }]` over input `#[-1.0, 2.0]` —
  expect `#[0.0, 2.0]` (donor value: `NonlinTest.lean`'s `reluT (t1 [-1, 2, -3, 4]) == t1 [0, 2, 0,
  4]`, same function, smaller vector).
- **Axiswise chain**: clone the pointwise fixture, change the second step to `.axiswise {
  sourceSlot := 1, destinationSlot := 2, shape := #[2,2], axisPos := 1, fn := .normalize }` over a
  `#[1,3,2,2]`-shaped source (donor: `NormTest.lean`'s NM1, `A=[[1,3],[2,2]] ⇒ [[0.25,0.75],
  [0.5,0.5]]`).
- **`sourceSlot == destinationSlot` regression** (§3/§4 row 12), in `GraphCheckTest.lean`: clone
  `oneNodePlan`, add a `.pointwise { sourceSlot := 1, destinationSlot := 1, shape := #[2], fn :=
  .relu }` step reusing slot 1 as both source and destination without an intervening producer for
  slot 1 as an input — confirm `checkPlan` rejects it as `invalidForwardRead` (via the generic
  `sourceSlots` path), pinning the §3 unreachability claim as a real test rather than an assertion.

### Mutation checks

- Remove the new `.pointwise`/`.axiswise` arms from `runDensePlan`'s dispatch one at a time; the
  corresponding dense fixture must fail to compile (exhaustiveness) or panic, not silently produce
  a wrong tensor.
- Revert the `sourceSlot == destinationSlot` regression fixture's guard reasoning by constructing
  the same plan with an *actually* already-produced slot 1 (e.g. also an input slot) reused as a
  destination; confirm it fails via `inputSlotOverwritten`/`duplicateDestination` instead —
  demonstrating both of §3's stated rejection paths, not just one.
- Confirm the `applyNonlin` refactor (item 1) is behavior-preserving in the real tree, not just in
  the §0a scratch snippet: `lake build Eval.NonlinTest` must stay green with **zero edits** to that
  file. If it doesn't, the refactor changed behavior and must be fixed before proceeding — do not
  edit `NonlinTest.lean` to make it pass.

### Gate

```bash
cd leanncd
lake build Eval.Plan.NonlinDenseTest
lake build Eval.Plan.GraphCheckTest
lake build Eval.NonlinTest
lake build LeanNCD
```

**Two independent final reviewers for this task specifically**, per the task brief's instruction
that this touches a soundness-relevant closed sum — do not fold this into Task 7's single
whole-branch pass only; get an early, task-scoped second opinion here too, since Task 3 builds on
top of this wiring and a defect found only at Task 7 would be far more expensive to unwind.

## Task 3: source compiler — real top-level compilation

### Outcome

A surface program like `Y[i] := relu(W[i,j]·x[j])` or `Y[i, s.] := softmax(A[i,s])` compiles
through `prepareEvalPlan` into a real two-step `PlanStep` chain and executes correctly; a masked
axiswise statement, an unmarked axiswise statement, and a marked-but-non-axiswise statement are all
rejected with the exact `NonlinCompileError` constructor from §3.

### Files

- `LeanNCD/Eval/Plan/Error.lean` (`NonlinCompileError`, alongside `ScanCompileError`)
- `LeanNCD/Eval/Plan/EvalPlan.lean` (`PlanCompileCause` gains `.nonlin (cause : NonlinCompileError)`)
- `LeanNCD/Eval/Plan/Compile.lean` (`checkLHSSlot`, `checkNonlin`'s top-level admission,
  `resolveNonlinAxis`, `liftNonlin`, `prepareEvalPlan`'s `.plain` branch)
- `test/Eval/Plan/CompileTest.lean` (capability-preflight-level fixtures)
- `test/Eval/Plan/NonlinCompileTest.lean` (new — compile-tier fixtures)

### Implementation

1. `Error.lean`: add `NonlinCompileError` exactly as drafted in §3, `deriving DecidableEq, BEq,
   Repr, Inhabited`. No new imports needed (`String`/`Nat` payloads only).
2. `EvalPlan.lean`: `PlanCompileCause` gains `| nonlin (cause : NonlinCompileError)`.
3. `Compile.lean`:
   - `checkLHSSlot`: change `| .freeNorm a => throw (.unsupportedLhsSlot ...)` to `| .freeNorm _ =>
     pure ()`.
   - `checkNonlin` (the function itself, both call sites currently share it): the **call site
     inside `checkStmt`** now admits — but since `checkNonlin` is shared code, either split it into
     two functions (`checkNonlinTopLevel`/`checkNonlinScanBlock`, the latter unchanged) or keep one
     function parameterized by an `admitNonlin : Bool` flag threaded from each caller. Prefer the
     split — matches this file's existing `checkLHSSlot`/`checkScanLHSSlot` naming precedent more
     directly than a boolean flag would.
   - Add `liftNonlin` beside `liftCapability`/`liftShape`/`liftPlanError`/`liftBindings`.
   - Add `resolveNonlinAxis` exactly as drafted and verified in §3.
   - `prepareEvalPlan`'s `.plain` branch: after computing `retainedUids`/`outputShape` exactly as
     today, call `resolveNonlinAxis nm rhs.nonlin slots` (lifted via `liftNonlin`). Build the
     existing `AssignPlan` targeting an **internal** slot (not `nm`'s eventual published slot) when
     `rhs.nonlin ≠ .identity`; when `.identity`, behavior is byte-for-byte unchanged (single
     `.assign`, published directly) — this is the regression-sensitive branch Task 2's parity
     fixture (F4's own precedent — Compile.lean's Task 2 established `residualizeAssignment` with
     scan-free parity as its explicit gate) must also re-confirm here.
   - For `.pointwise pf`: push a `.pointwise { sourceSlot := internalSlot, destinationSlot :=
     publishedSlot, shape := outputShape, fn := pf }` step; publish `nm` at `publishedSlot`.
   - For `.axiswise fn none` with `resolveNonlinAxis` returning `some p`: push the `.axiswise`
     analogue with `axisPos := p`.
   - `freeUidOrFail` must accept `.freeNorm a => pure a.uid` (currently throws) — update its doc
     comment too (it currently claims "unreachable post-preflight," which becomes false for
     `.freeNorm` once `checkLHSSlot` admits it).

### Fixtures (donors named)

- **Capability preflight** (`CompileTest.lean`, clone existing accepted/rejected fixture pattern
  from that file): confirm `.pointwise`/`.axiswise` (mask `none`) now pass `capabilityPreflight`
  at the top level; confirm scan-block `.pointwise`/`.axiswise` **still** reject via
  `unsupportedNonlin` (clone `ScanContractTest.lean`/`CompileTest.lean`'s existing
  scan-block-rejection fixture, change nothing but confirm the constructor is unchanged).
- **`resolveNonlinAxis` compile-tier fixtures** (`NonlinCompileTest.lean`): the five cases already
  verified via `check-snippet.sh` in §3 (valid single-marker, no-marker, masked, marker-without-
  axiswise, unmarked-identity), each re-run through the real `prepareEvalPlan` end-to-end rather
  than the standalone function, confirming the exact `NonlinCompileError` surfaces as
  `PlanCompileCause.nonlin`.
- **End-to-end compiled examples**, donors named precisely (reused again by Task 6's differential
  fixtures — do not duplicate the tensors, cite the same donor):
  - `relu`: clone `FeedforwardTest.lean` FF2 (`W=[[1,-1],[-2,1]]`, `x=[1,1]` → `H=[0,0]`).
  - `sigmoid`/`tanh`/`gelu`/`leakyrelu`: clone FF5/FF6/FF7/FF8 (`W=I₂`, `x=[-2,2]`, exact expected
    tensors already given in §0).
  - `normalize`/`softmax`: clone `NormTest.lean` NM1/NM2 (`A=[[1,3],[2,2]]`/`A=[[0,0],[0,ln3]]`).
  - `l2normalize`: clone `GenerativeTest.lean` CL3 (`Z1=[[3,4]] → [0.6,0.8]`) and CL3b (all-zero
    row → all-zero, the degenerate-norm edge case).

### Mutation checks

- Revert `checkLHSSlot`'s relaxation; confirm every axiswise end-to-end fixture starts failing at
  preflight instead of compiling (proves the relaxation, not something else, is what makes them
  reachable).
- Revert `resolveNonlinAxis`'s masked-rejection branch (make it fall through to `some p`); confirm
  the masked-axiswise fixture stops being rejected and instead silently builds a `RawAxiswisePlan`
  — restore, confirm rejection returns.
- Swap the `.identity` branch's slot allocation to also always allocate an internal slot (even when
  unused); confirm this changes `tensorSigs.size`/slot numbering versus today's baseline and would
  therefore have been a silent regression — restore the branch, confirm parity.

### Gate

```bash
cd leanncd
lake build Eval.Plan.CompileTest
lake build Eval.Plan.NonlinCompileTest
lake build LeanNCD
```

Independent task review — this is the architectural centerpiece (§5's task table). Expect at least
one fix round.

## Task 4: delete `numericMode`/`NumericMode`/`numericModeNotAdmitted`

### Outcome

`RawEvalPlan` has no `numericMode` field; `NumericMode` and `PlanError.numericModeNotAdmitted` no
longer exist; every occurrence listed in §0 is gone or updated.

### Files

Production: `LeanNCD/Eval/Plan/Types.lean`, `LeanNCD/Eval/Plan/Graph.lean`,
`LeanNCD/Eval/Plan/Error.lean`, `LeanNCD/Eval/Plan/EvalPlan.lean`, `LeanNCD/Eval/Plan/Compile.lean`.
Tests: `test/Eval/Plan/EvalPlanTest.lean`, `test/Eval/Plan/GraphCheckTest.lean`,
`test/Eval/Plan/GraphDenseTest.lean`, `test/Eval/Plan/KernelCheckTest.lean`,
`test/Eval/Plan/ExecutableTest.lean`, `test/Eval/Plan/CompileTest.lean`,
`test/Eval/Plan/AdapterTest.lean`, `test/Eval/Plan/ContractTest.lean`.
**Not touched**: `experiments/jax_bridge/EvalPlanCodegen.lean` (§0 — already broken, out of scope).

### Implementation

1. `Types.lean`: delete `NumericMode`.
2. `Graph.lean`: delete `RawEvalPlan.numericMode`.
3. `Error.lean`: delete `PlanError.numericModeNotAdmitted`.
4. `EvalPlan.lean`: delete `checkPlan`'s `unless raw.numericMode == .reference64SumProduct do throw
   (.assign (.numericModeNotAdmitted raw.numericMode))` guard.
5. `Compile.lean`: delete `numericMode := .reference64SumProduct` from `prepareEvalPlan`'s
   `RawEvalPlan` literal.
6. Every test-site `RawEvalPlan` literal in the file list above: delete the
   `numericMode := .reference64SumProduct` field.
7. `GraphCheckTest.lean`: delete the direct `#guard (PlanError.numericModeNotAdmitted ...) ==
   PlanError.numericModeNotAdmitted ...` line and its preceding "structurally unreachable" comment
   (the constructor no longer exists — this is not exercising anything after deletion).
8. `CompileTest.lean`, `AdapterTest.lean`, `ContractTest.lean`: update the three stale comment
   references identified in §0 (each cites `numericModeNotAdmitted`/`NumericMode` as a "same
   pattern" precedent for something else) so they don't cite a deleted constructor — reword to the
   remaining precedent only (`CompileTest.lean`/`AdapterTest.lean` each still have their own
   *other* single-valued-vocabulary unreachable to point to independent of this one:
   `unsupportedDtype`/`dynamicShape` for `CompileTest.lean`, nothing else for `AdapterTest.lean` —
   if no independent precedent remains for a given comment, drop the "same pattern as" clause
   entirely rather than leave a dangling reference).

### Mutation checks

Not applicable in the usual sense (this task deletes, it doesn't add a guard to break/restore) —
the verification is that `lake build LeanNCD` and the full test suite are green with the field
gone, confirming no other production or test site depends on it beyond the exact list in §0.

### Gate

```bash
cd leanncd
lake build LeanNCD
lake build Eval.Plan.EvalPlanTest Eval.Plan.GraphCheckTest Eval.Plan.GraphDenseTest \
  Eval.Plan.KernelCheckTest Eval.Plan.ExecutableTest Eval.Plan.CompileTest \
  Eval.Plan.AdapterTest Eval.Plan.ContractTest
grep -rn "numericMode\|NumericMode\|reference64SumProduct" LeanNCD/ test/  # must return nothing
  # under LeanNCD/Eval/Plan and test/Eval/Plan except inside experiments/jax_bridge, which is
  # explicitly excluded from this grep's scope (or confirm it only matches that one file)
```

Independent task review. Can run fully in parallel with Tasks 1-3 and 5.

## Task 5: architecture doc corrections

### Outcome

`papers/jax_evalplan_architecture.md` §7.6's thread 4 row and §2.2's closing sentence both state
Dense-only support landed, with **PyTorch and JAX given distinct framing, not identical deferral
text** — per this plan's own §2.2 ruling (read it before writing this task's edit; do not
re-derive the JAX/PyTorch distinction independently here).

### Files

- `papers/jax_evalplan_architecture.md`

### Implementation

1. §7.6's thread 4 table row: change `Open — the only thread still open` to reflect Dense-only
   completion, and its "Why" cell to state: `PlanStep` now has `.pointwise`/`.axiswise` (thread 4),
   checked and executed by Dense, reachable from top-level source syntax, serving as the reference
   semantics a future JAX lowering must match; scan-block nonlinearity stays rejected (deliberate
   scope boundary, §2.2 above). Then, as two visibly distinct clauses, not one merged
   "JAX/PyTorch deferred" clause, using §2.2's exact PyTorch/JAX distinction: **PyTorch** —
   deferred with no scheduled thread, quoting thread 5's own sentence structure verbatim as the
   template. **JAX** — blocked solely by `EvalPlanCodegen.lean`'s pre-existing `PlanStep` breakage,
   with repairing that file and adding `.pointwise`/`.axiswise` lowering named as the natural next
   slice, not indefinitely deferred.
2. §2.2's sentence "Once Dense, JAX, and PyTorch gain checked nonlinear support, re-measure against
   real output..." — change to name Dense's real support as landed by this thread (the reference
   semantics JAX will eventually be diffed against), apply the same PyTorch/JAX distinction as
   item 1, and state that the four transcendental-call functions' ULP bounds specifically remain
   unvalidated even for Dense (no second backend to differential against yet) per this plan's §2.2.
3. Do not touch any other section of the architecture doc (§4.3, §5.4, Appendix D) — those describe
   JAX/PyTorch executable architecture in the abstract and are unaffected by a Dense-only thread.

### Gate

```bash
grep -n "thread 4" papers/jax_evalplan_architecture.md   # confirm the row reads as updated
grep -n "Once Dense, JAX, and PyTorch" papers/jax_evalplan_architecture.md  # must return nothing
  # (the sentence should no longer read as a single still-open compound condition)
```

Independent task review (doc-only, but still gated — skill §3's "doc-sweep-vs-reactive-catch"
guidance: this is planned content work with a real claim to verify, not a drive-by rename).

## Task 6: differential/corpus re-verification

### Outcome

Eight new hand-built differential fixtures (one per nonlin function) prove the compiled Dense path
agrees bit-for-bit with `evalScheduled` for real top-level nonlin programs — the first such
evidence, since no existing generator produces one. The scan corpus split is re-run and confirmed
**unchanged** (17/9/4/4), correcting the task brief's own assumption (§0).

### Files

- `test/Eval/Plan/DifferentialTest.lean`

### Implementation

1. Add eight `checkEntry`-style comparisons (or a small dedicated loop, matching this file's
   existing `checkEntry`/`envEq` helpers) for the end-to-end fixtures named in Task 3, each
   comparing `prepareEvalPlan` + `runPreparedDense` against `evalScheduled` on the identical
   program and input, asserting `envEq` and warnings equality exactly as `checkEntry` already does
   for `enumPrograms`.
2. Re-run `scanCorpusSplit` unchanged (no code edit expected) and confirm the pinned
   `total == 17 && accepted == 9 && nonlin == 4 && agg == 4` guard still passes — this is a
   **confirmation**, not a re-baseline. If it ever disagrees, that is a real Task 3 defect to
   report (per DifferentialTest.lean's own stop-condition precedent for this exact guard), not a
   number to update in this task.
3. No change to `test/Eval/Portfolio/ScatterNonlinRejectTest.lean` — confirmed out of scope in §0
   (tests scatter, an unconditional rejection unrelated to `checkNonlin`).

### Fixtures

The eight from Task 3's "end-to-end compiled examples" list, reused verbatim (same donor tensors,
same expected values) rather than re-derived — this task's own value is running them through the
*differential* comparison (`runPreparedDense` vs. `evalScheduled`), which Task 3's own tests do not
do (Task 3 only confirms the compiled plan itself produces the right tensor, not that it agrees
with the independent legacy evaluator on the identical source program).

### Mutation checks

- Temporarily break one new differential fixture's expected value (off by a small delta); confirm
  the new comparison loop fails loudly rather than silently passing via a `DenseTensor.approxEq`-
  style tolerance mismatch with the legacy evaluator's own convention — restore.
- Confirm `scanCorpusSplit`'s guard fails loudly (not silently re-baselines) if temporarily changed
  to expect e.g. `nonlin == 0`, then restore the real pinned values.

### Gate

```bash
cd leanncd
lake build Eval.Plan.DifferentialTest
```

Independent task review.

## Task 7: closure — discoverability, completion record, whole-branch review

### Outcome

`LeanNCD.lean` imports the new file; `Eval/AGENTS.md`'s `Plan/` table and entry-points list mention
it; a completion record states exactly what shipped, what was deliberately deferred and why —
applying §2.2's PyTorch/JAX distinction rather than lumping both under one "deferred" label — plus
scan-block nonlin, masked axiswise, and the four unvalidated ULP bounds, and the corrected corpus/
differential numbers from Task 6. Two independent whole-branch reviewers have signed off.

### Files

- `LeanNCD.lean` (add `import LeanNCD.Eval.Plan.Nonlin`, placed with the other Wave F direct
  imports per the existing convention noted in `Eval/AGENTS.md`'s `Plan/` subtree section)
- `LeanNCD/Eval/AGENTS.md` (the `Plan/` file table gains a `Nonlin.lean` row; the "Add a new
  nonlinearity" entry-point row gets a second line for the Plan-layer path, distinct from the
  existing legacy-`Nonlin.lean` entry; the file-count-16 note in the "Find It Fast" table becomes
  17)
- A completion record — follow this directory's own convention of appending to the relevant design
  doc rather than a new file; since this thread has no `papers/wave_*_proposal.md` of its own,
  append the record directly to this plan file's own closing section (matching how earlier
  standalone-thread plans in this directory, e.g. `2026-08-13-thread-5-jax-executable-kernels.md`,
  close themselves) rather than inventing a new doc

### Implementation

1. Add the `LeanNCD.lean` import.
2. Update `Eval/AGENTS.md`'s `Plan/` table row list and file count.
3. Write the completion record: what shipped (two `PlanStep` cases, real top-level compilation, the
   `numericMode` deletion, the doc correction), what was deliberately deferred and why (§2.2 of
   this plan, verbatim reasons — scan-block nonlin, masked axiswise, unvalidated transcendental ULP
   bounds, and the PyTorch/JAX distinction stated separately per §2.2, not merged into one
   "backends deferred" line), and the real Task 6 numbers (scan corpus split confirmed unchanged;
   the eight new differential fixtures, named).
4. **Verify every claim in the completion record against the actual code/output before writing it**
   — per the skill's own rule 1, a completion record is exactly the kind of templated prose that
   must be checked, not asserted from design intent. In particular: do not write "no second
   local-operation representation was added" without diffing `Nonlin.lean` against `Kernel.lean`'s
   `AssignPlan` to confirm it, and do not write the Task 6 corpus numbers without pasting the real
   `lake build` output.

### Gate

```bash
cd leanncd
lake build LeanNCD
lake build   # full suite
```

**Two independent final whole-branch reviewers**, per the task brief's explicit instruction (this
touches a soundness-relevant closed sum) and this repo's own standing lesson (skill §4: the
whole-branch tier is where every prior slice's most valuable finding came from, never a per-task
diff). Do not compress this because Tasks 1-6 land clean — F3's and F4's own final reviews each
found something no per-task review caught.

## 6. Definition of done

- [ ] `LeanNCD/Eval/Plan/Nonlin.lean` exists with `RawPointwisePlan`/`RawAxiswisePlan`,
      `NonlinPlanError`, a shared `checkNonlinIO` helper, `checkPointwise`/`checkAxiswise` built on
      it, and `runDensePointwise`/`runDenseAxiswise`.
- [ ] `LeanNCD/Eval/Nonlin.lean` has a new `AxiswiseFn.apply`, symmetric with `PointwiseFn.apply`;
      `applyNonlin` delegates to both; `test/Eval/NonlinTest.lean` is unchanged and still green
      (§0a — confirms the refactor is behavior-preserving, not just independently verified).
- [ ] `PlanStep` has four constructors; `checkPlan`/`runDensePlan`/`sourceSlots`/`destinationSlots`/
      `CheckedPlanStepEvidence` all handle all four.
- [ ] `checkLHSSlot` admits `.freeNorm`; the top-level `checkNonlin` call site admits
      `.pointwise`/`.axiswise`; the scan-block call site is unchanged (still rejects both).
- [ ] `NonlinCompileError`/`resolveNonlinAxis` exist and reject masked axiswise, unmarked axiswise,
      and marker-without-axiswise, each with the exact named constructor.
- [ ] `prepareEvalPlan` compiles a nonlin-bearing plain statement into the two-step chain from §3;
      `.identity` statements are byte-for-byte unchanged.
- [ ] `numericMode`/`NumericMode`/`numericModeNotAdmitted` are gone from every site in §0's list;
      `experiments/jax_bridge/EvalPlanCodegen.lean` is untouched.
- [ ] Architecture doc §7.6 thread 4 row and §2.2's closing sentence corrected, giving PyTorch and
      JAX distinct framing (§2.2's ruling) rather than one merged deferral clause.
- [ ] Eight new end-to-end differential fixtures pass; the scan corpus split (17/9/4/4) is
      confirmed unchanged by a real re-run, not assumed.
- [ ] `LeanNCD.lean`/`Eval/AGENTS.md` updated for discoverability.
- [ ] Completion record written and verified against real code/output, not asserted.
- [ ] `lake build` (full suite) green.
- [ ] Two independent reviewers signed off on Task 2 (closed-sum wiring) and two independent
      reviewers signed off on the final whole-branch review (Task 7).

## 7. Risks and stop conditions

### 7.1 Expected high-effort areas

- Task 3's two-step chaining touches `prepareEvalPlan`'s Step D, the one existing production
  compiler path — any regression there silently breaks every Wave C/F fixture, not just new nonlin
  ones. Task 3's own gate must re-run the FULL `Eval.Plan.*` test suite, not just its own new file.
- Task 2's exhaustive-match wiring is exactly the shape of defect F3/F4 review found expensive to
  catch late (a diff showing only *added* arms cannot show whether an *existing* arm's behavior
  silently changed) — hence the two-independent-reviewer requirement on that task specifically.

### 7.2 Stop rather than broaden scope

- If implementing `resolveNonlinAxis`/the two-step chain reveals that `.freeNorm`'s relaxation has
  a THIRD consumer beyond `checkLHSSlot`/`freeUidOrFail` this plan didn't find (e.g. a scatter-path
  or `Structural.lean` check that also assumes `.freeNorm` is globally unreachable) — stop and
  report; do not silently widen this plan's Compile.lean edits to cover it without re-scoping.
- If Task 6's differential fixtures disagree with `evalScheduled` for any function — this is a
  genuine Task 3 compiler defect (per §0's scan-corpus stop-condition precedent), not a fixture to
  adjust. Stop and report to the plan owner rather than "fixing" the fixture's expected value.
- Do not attempt to relax the mask-rejection scope boundary (§2.2) mid-implementation even if it
  looks small once `resolveNonlinAxis` exists — it requires new UID-free predicate IR design with
  no precedent in this codebase, which is out of this plan's sizing entirely.

## 8. Plan-authoring verification record

- Every Lean code block in this plan (§3's `NonlinCompileError`/`resolveNonlinAxis`, the raw types
  and manual `BEq` instances, `checkPointwise`/`checkAxiswise`/`runDensePointwise`/
  `runDenseAxiswise`, and a 4-constructor `PlanStep`-shaped sum built from the **real**
  `RawScanPlan`/`AssignPlan`) was compiled via `check-snippet.sh` against the real repo this
  session (four separate snippet files, all green — one harmless unused-variable lint warning in
  an illustrative, non-shipped snippet).
- §0a's follow-up extensibility/code-sharing vetting pass added two more verified snippets: the new
  `AxiswiseFn.apply` plus refactored `applyNonlin`, checked both for compilation and for
  **behavior equivalence** to the real (pre-refactor) `applyNonlin` via five `#guard`s comparing
  `.data` output on identity/pointwise/all-three-axiswise cases (all equal, first pass after fixing
  `DenseTensor.shape`'s real type being `List Nat` not `Array Nat`); and the shared `checkNonlinIO`
  helper plus `checkPointwise`/`checkAxiswise` built on it, checked with five `#guard`s covering a
  passing case, `slotOutOfRange`, `sourceShapeMismatch`, and a passing/failing `axisPositionOutOfRange`
  pair through `checkAxiswise` specifically (first pass caught one authoring error — `shape :=
  #[2]` has `.size == 1`, not `2`, corrected before the snippet was accepted). Six snippets total,
  all green in their final form.
- Every prose claim of the "X reuses Y" / "no second Z" shape was checked against real code before
  being written: `PointwiseFn.apply`'s existing dispatch (confirmed identical to what
  `runDensePointwise` needs), `checkPlan`'s exact three-match-block structure and its `.scan`
  generic-path precedent (confirmed by reading `EvalPlan.lean` directly, not summarized from
  memory), `checkStmt`'s scatter-rejection ordering relative to `checkNonlin` (confirmed
  `ScatterNonlinRejectTest.lean` needs no change), and the scan corpus split's real composition
  (confirmed `template2`'s nonlin sits inside the recurrence block, correcting the task brief's own
  framing).
- Every file path this plan names was verified with `ls`/`grep`/`Read` this session, including
  finding `papers/jax_evalplan_architecture.md` at the pyncd repo root (not under `leanncd/`,
  where an initial search for it failed) and confirming `.claude/skills/slice-plan/` lives at the
  pyncd repo root too, not inside `leanncd/`.
- No `File.lean:NNN` line numbers appear in any task's Implementation/Files/Gate text above, or in
  the completion-record instructions Task 7 is handed — every locator is by function/constructor
  name.
- `experiments/jax_bridge/EvalPlanCodegen.lean`'s pre-existing breakage was confirmed by directly
  running `lake build JaxExperiment` this session, not assumed from the task brief's description —
  the real failure output matches the description (stale `.plan` field access, non-exhaustive
  `PlanCompileCause.scan` match, removed `RawEvalPlan.version`, an `AssignPlan`/`PlanStep`
  mismatch), independently confirming ruling 4 rather than merely repeating it.
