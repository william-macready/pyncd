# Design: nonlinearity inside scan blocks

**Status:** Brainstormed and approved by the user (2026-08-21). Not yet an implementation plan —
that is a separate step (`slice-plan`/`writing-plans`), deliberately not done here.

**Context:** Thread 4 (merged to `main` at `549adb6`, 2026-08-21) added `.pointwise`/`.axiswise`
`PlanStep` support for top-level (`.plain`) statements only. Scan-block statements (base/step)
still hit `checkNonlinScanBlock` (`LeanNCD/Eval/Plan/Compile.lean:72-75`), which unconditionally
rejects any non-`.identity` `Nonlin` — a deliberate scope boundary Thread 4's own plan documented,
not an oversight. This design lifts that boundary.

## Decisions made during brainstorming (don't re-litigate; re-derive only if this doc is stale)

1. **Support nonlinearity in both the base block and the step/recurrence block.**
2. **A persistent scan state may itself be the direct output of a nonlinearity** (e.g. a running
   softmax carried as state) — not restricted to per-step scratch/intermediate values.
3. **`.axiswise` reduction is restricted to the block's own local free axes** — no reduction across
   the scan's context/advancing axis (no cross-time-step softmax). This requires no special
   handling: `resolveNonlinAxis` only ever inspects `.freeNorm` positions among a statement's own
   LHS slots, and never inspects `.iterAt`/`.iterNext`, so it already behaves correctly for this
   restriction with zero changes.
4. **Masked `.axiswise` (`Nonlin.axiswise fn (some predicate)`) stays deferred**, in scan blocks
   exactly as it already is at the top level. Supporting it would require a new compiled, UID-free
   boolean-predicate IR — real, bounded, and precedented in *kind* (this compiler already erases
   UIDs into position-based `AffineMap`s via `idxToRow`/basis-densification for `IdxExpr`s), but a
   genuinely separate piece of work from this design, and it would *also* unblock the
   separately-tracked `.iverson` factor rejection (`checkFactor`'s `maskOrPredicate` case) — a
   real side-benefit but real scope-creep risk. Out of scope here.
5. **The design must pay down the wiring-loop duplication this repo's own history has twice
   flagged and deferred**: `checkPlanBlock`/`runDenseBlock` (`Block.lean`) are near-copies of
   `checkPlan`/`runDensePlan` (`EvalPlan.lean`)'s outer wiring loops. Adding a new node-kind
   dispatch to both independently would be the third such copy — this design generalizes instead.
6. **Approach chosen: a new `BlockStep` closed sum, structurally `PlanStep` minus `.scan`** — not
   literal reuse of `PlanStep` itself inside blocks (which would make `RawScanPlan` mutually
   recursive with itself via `RawPlanBlock → Array PlanStep → PlanStep.scan → RawScanPlan`, a real
   well-founded-recursion cost for no requested benefit — nested scans were never asked for, and
   this codebase consistently prefers making invalid states unrepresentable by the type rather than
   rejected at runtime).

## Architecture

Two structurally parallel levels, sharing everything below "which node kinds exist":

- **Outer** (unchanged): `PlanStep | assign | scan | pointwise | axiswise`, checked/run by
  `checkPlan`/`runDensePlan` (`EvalPlan.lean`).
- **Block** (new): `BlockStep | assign | pointwise | axiswise`, checked/run by
  `checkPlanBlock`/`runDenseBlock` (`Block.lean`).

`BlockStep` lives in `RawStep.lean`, alongside `RawPlanBlock` — following the existing convention
that raw types needed early (to avoid a circular import) live there, while checkers/workers live
where they're used (`Block.lean`).

### Data structures (new/changed)

```lean
-- RawStep.lean, alongside RawPlanBlock
inductive BlockStep
  | assign    (a : AssignPlan)
  | pointwise (p : RawPointwisePlan)
  | axiswise  (a : RawAxiswisePlan)
  deriving DecidableEq, BEq, Repr, Inhabited

-- RawPlanBlock.assignments : Array BlockStep   (was Array AssignPlan)
```

```lean
-- Block.lean, mirroring CheckedPlanStepEvidence
inductive CheckedBlockStepEvidence
  | assign    (c : CheckedAssignPlan)
  | pointwise (c : CheckedPointwisePlan)
  | axiswise  (c : CheckedAxiswisePlan)

-- CheckedPlanBlock.checkedNodes : Array CheckedBlockStepEvidence  (was Array CheckedAssignPlan)
```

Two new thin error-wrapper constructors, each wrapping an *already-existing* payload type
verbatim (no new error taxonomy):

```lean
-- BlockError gains, mirroring PlanStepError.nonlin exactly:
| nonlin (nodeIndex : Nat) (cause : NonlinPlanError)

-- ScanCompileError gains, mirroring PlanCompileCause.nonlin exactly:
| nonlin (stmtName : String) (cause : NonlinCompileError)
```

### The code-sharing accounting (why this is high-leverage, not just "another arm")

**Reused 100% verbatim, zero changes:** `checkNonlinIO`/`checkPointwise`/`checkAxiswise`/
`runDensePointwise`/`runDenseAxiswise` (`Nonlin.lean` — already slot-table-agnostic, confirmed by
reading every signature: they take a bare `Array TensorSignature` plus positional `TensorSlot`s,
never an outer-plan-specific concept); `resolveNonlinAxis`/`NonlinCompileError` (already
statement-shape-agnostic — scan-block statements use the identical `Stmt.assign`/`List LHSSlot`
shape as top-level ones); `RawPointwisePlan`/`RawAxiswisePlan`/`NonlinPlanError`/
`CheckedPointwisePlan`/`CheckedAxiswisePlan`; `PointwiseFn.apply`/`AxiswiseFn.apply`.

**Newly shared via generalization (written once, called from both paths):**
1. **The wiring loop.** Today `checkPlan`/`checkPlanBlock` and `runDensePlan`/`runDenseBlock` are
   separate hand-written copies of the same shape (availability/`producedBy` tracking, forward-read
   and duplicate-destination checks, missing-production sweep). De-risking finding: the two loops'
   *error vocabulary* is **already unified** — `BlockError.wiring (cause : PlanError)` already
   wraps the exact same `PlanError` type the outer loop's `PlanStepError.assign (cause : PlanError)`
   uses. So generalizing mainly means writing ONE Lean function parameterized over the node type
   (via an explicit small record of `sourceSlots`/`destinationSlots`/per-node-dispatch functions,
   Lean's idiomatic shape for this rather than a typeclass, since each call site's dispatch
   function is genuinely a one-off, not a reusable instance), used by both `checkPlan` (4 arms) and
   `checkPlanBlock` (3 arms) — and symmetrically for `runDensePlan`/`runDenseBlock`'s
   store-management loop.
2. **The two-step nonlin chaining logic.** Today this exists exactly once, inline in
   `prepareEvalPlan`'s `.plain` branch (`Compile.lean:888-924`): resolve the axis position via
   `resolveNonlinAxis`, allocate an internal slot if `nonlin ≠ .identity`, build the linear
   `AssignPlan` targeting that slot, then build the `.pointwise`/`.axiswise` step from it to the
   published slot. Extracted into one helper parameterized over (a) three small injector functions
   wrapping `AssignPlan`/`RawPointwisePlan`/`RawAxiswisePlan` into "the target step type"
   (`PlanStep` at the outer level, `BlockStep` inside a block), and (b) a slot-allocation callback
   against "the target's own local `tensorSigs` table" (the outer plan's accumulator, or a block's
   own). Called from both `prepareEvalPlan`'s `.plain` branch (refactored to use it) and
   `compileScan`'s base/step phases (Phase 3/4).
3. **Bonus find:** once scan blocks admit unmasked `.pointwise`/`.axiswise`,
   `checkNonlinTopLevel`/`checkNonlinScanBlock` (`Compile.lean:64-75`, split apart by Thread 4's
   Task 3 specifically to encode their *difference*) become **literally identical function
   bodies**. They should re-merge back into one `checkNonlin`, undoing that split — the split's
   entire reason for existing goes away.

**Necessarily separate, and why that's not a sharing failure:** `compileScan`'s own Phase 0/1/2/5/6
(context axes, state-result-vs-scratch classification, per-state geometry, causality, write-map
construction) — genuinely scan-specific, nothing analogous exists or should exist for plain
statements. The two thin error-wrapper constructors — different labels required because each
belongs to a different layer's closed error family, but wrapping the identical payload type, so
this is "different suitcase tag," not duplicated logic.

**Net effect:** essentially zero new *nonlinearity-specific* code gets written for the scan case.
The only new code is `BlockStep`/`CheckedBlockStepEvidence` (small, structurally copy-paste of
`PlanStep`/`CheckedPlanStepEvidence` minus one arm), the two generalizations (one-time cost, and
the wiring-loop one pays off independent of this feature), two error-wrapper constructors, and
relaxing two preflight checks (`checkScanLHSSlot` for `.freeNorm`, mirroring what Task 3 did to
`checkLHSSlot`; `checkNonlinScanBlock`/the merged `checkNonlin` to admit unmasked
`.pointwise`/`.axiswise`).

## Risk profile (for whoever writes the implementation plan)

The wiring-loop generalization is the highest-risk piece by far — it refactors already-shipped,
heavily-tested production code (`checkPlan`/`runDensePlan`/`checkPlanBlock`/`runDenseBlock`), not
just additive new arms. The regression bar: **every existing `.assign`/`.scan` fixture across the
whole test suite must come out byte-identical after the refactor.** This is exactly the class of
change Thread 4's own plan flagged as needing two independent reviewers for a much smaller diff
(extending `PlanStep` from 2 to 4 constructors, additive only) — a *refactor* of the same closed
sums' consuming code deserves at least that level of scrutiny, arguably more since it's harder to
review from a diff alone (a diff of a generalized function doesn't visibly show "this existing
case's behavior is preserved" the way an added-arms diff does — the reviewer has to hand-verify the
generic function specializes back to each original behavior for every case).

Suggested (not committed) task shape for the eventual plan, mirroring Thread 4's own structure:
1. `BlockStep`/`CheckedBlockStepEvidence` types + the wiring-loop generalization + regression
   suite (highest risk, do first, get it fully proven before building anything on top).
2. Wire `checkPlanBlock`/`runDenseBlock` onto the generalized loop with `BlockStep`'s 3 arms.
3. Extract the shared nonlin-chaining helper from `prepareEvalPlan`'s `.plain` branch; refactor
   `prepareEvalPlan` to use it (parity fixture: `.identity` still byte-for-byte unchanged).
4. Wire `compileScan`'s Phase 3/4 to call the same helper for base/step statements; relax
   `checkScanLHSSlot`/merge `checkNonlin`.
5. Differential fixtures: one pointwise + one (unmasked) axiswise, for each of {base block, step
   block scratch, step block state result} — 6 minimum, reusing Thread 4's own donor tensors where
   the shapes match.
6. Closure: architecture doc, discoverability, completion record, whole-branch review (two
   independent reviewers, per the same soundness-relevant-closed-sum rule Thread 4 applied).

## Open items for the implementation plan to resolve (not decided here)

- Exact Lean signature for the wiring-loop generalization's parameter record (typeclass vs.
  explicit record of functions) — a real Lean-idiom judgment call, not resolved by this
  brainstorm; needs `check-snippet.sh` verification against the real types before the plan ships.
- Whether `checkNonlinTopLevel`/`checkNonlinScanBlock`'s merge-back should happen in the same task
  as the scan-block relaxation, or as a small separate cleanup task.
- Exact new test file naming/placement for the scan-block nonlin fixtures (mirror
  `NonlinCheckTest.lean`/`NonlinCompileTest.lean`/`NonlinDenseTest.lean`'s naming, or fold into
  existing `ScanCompileTest.lean`-family files — a convention call for the plan author).
