# Design: nonlinearity inside scan blocks

**Status:** Brainstormed, externally reviewed (`papers/copilot_unification_critique.md`), revised
in response, then given a further self-review pass that found one more concrete finding (§1)
(all 2026-08-21). Not yet an implementation plan — that is a separate step
(`slice-plan`/`writing-plans`), deliberately not done here.

**Context:** Thread 4 (merged to `main` at `549adb6`, 2026-08-21) added `.pointwise`/`.axiswise`
`PlanStep` support for top-level (`.plain`) statements only. Scan-block statements (base/step)
still hit `checkNonlinScanBlock` (`LeanNCD/Eval/Plan/Compile.lean:72-75`), which unconditionally
rejects any non-`.identity` `Nonlin` — a deliberate scope boundary Thread 4's own plan documented,
not an oversight. This design lifts that boundary.

**Revision note:** the first draft of this doc was reviewed by an external critique
(`papers/copilot_unification_critique.md`) that found two real architectural gaps (§1, §2 below)
plus a genuine error in the proposed error-handling (an "own" scan-nonlin error wrapper that
would have duplicated a locator already present) and two overclaims in the original
forward-compatibility section. Every claim in the critique was independently re-verified against
the real code before being folded in here — some of the critique's own diagnoses were corrected
in the process (see §1). What follows is the revised design; the original code-sharing accounting
from the first draft is preserved below (§3/§4) and still holds.

## 1. Pipeline-boundary question: scan statements arrive pre-split, and this design must not
   assume otherwise

**The gap.** `TLProgram.compileToScheduled`'s pipeline (`DSL/Compile.lean:36-38`) runs
`splitNonlins` on the *entire* program, including scan bodies: `splitScan`
(`DSL/Pipeline/Lowering.lean:84-91`) applies `splitStmt` to every statement in a scan's `base` and
`recur` lists, exactly as it does to top-level statements. `splitStmt` (`Lowering.lean:38,69-77`)
turns any statement with `rhs.nonlin ≠ .identity` into two statements — a `%nl...`-named linear
one (`linSlots` only degrades `.freeNorm→.free`; every other slot kind, including `.iterAt`/
`.iterNext`, passes through unchanged) and a trivial-body nonlin one reading from it. So by the
time a scan-block statement could reach a relaxed `compileScan`, it has *already* been split into
two separate statements — one of which carries a real advancing (`.iterNext`) slot under a
synthetic `%nl...` name that is not a registered persistent state.

This is exactly the redundant-double-split reality Thread 4's own Task 3 already discovered and
documented for the *top-level* path (a real compiled nonlin statement produces 3 steps, not 2,
because `splitNonlins` splits once at the DSL level and the Plan-layer chaining splits the
already-trivial nonlin statement again). The gap this design missed: a naive port of the
top-level chaining helper into `compileScan` would hit the *scan-specific* consequence of the
same pre-split fact — `compileScan`'s Phase 1 classifier (`Compile.lean:454-490`) would see the
split-off `%nl...` linear statement as either an unregistered advancing result
(`orphanAdvancingResult`, `Compile.lean:479-481`, in the recurrence case) or a spurious new base
destination (in the base case), *before* any nonlin-aware compilation logic runs at all. (In the
current, unmodified codebase this never actually surfaces, because `checkNonlinScanBlock` rejects
the whole statement at preflight first — but that rejection is exactly what this design proposes
lifting, so the classifier-level failure is what would happen next, not a hypothetical.)

**Revised finding (this pass): `splitScan`'s output has a second real consumer, which changes
the tradeoff between the two candidate fixes.** `TLProgram.compile` (`DSL/Compile.lean:19-31`) is
*not* an independent pipeline — it is the literal same phase sequence as `compileToScheduled`,
plus one more step: `route g` (line 31), applied to the identical post-`schedule`
`ScheduledProgram` value both functions share. `compileToScheduled`'s own doc comment
(`Compile.lean:33-35`) confirms directly: "the routed `ThreadedComposed` collapses scan bodies and
can't be evaluated" — i.e. `route` is the "routed path" the external critique flagged, and it
consumes `splitNonlins`' output *directly*, not independently of it. So changing `splitScan`'s
behavior (option A below) changes what `route` sees too — this is now a confirmed shared-consumer
relationship, not a hypothesis to check later. Whether `route`'s own scan-collapsing logic
actually *depends on* statements arriving pre-split (as opposed to just processing whatever
statements are there, split or not) is still not established — that requires reading `route`'s
own implementation (likely in `Lowering.lean`/`RouteSpec.lean`, not yet done in this pass) — but
the fact that it shares the exact input value is now certain, not inferred.

Two candidate fixes, both still open pending that investigation:

- **Option A — change `splitScan`'s `.scan` branch to not call `splitStmt`** (the original
  proposal): scan statements stay unsplit all the way into `compileScan`, which applies the shared
  chaining helper (§4) directly to each one. Clean, and avoids scan-block compilation inheriting
  the top-level path's redundant identity-copy inefficiency (2 steps, not 3) — a real efficiency
  byproduct, not something to reconcile away. Risk: touches a function shared with `route`,
  a consumer this design doesn't otherwise touch at all.
- **Option B — leave `splitScan`/`splitNonlins` untouched; teach `compileScan`'s Phase 1
  classifier to recognize and recombine a split pair itself** (detect the `%nl...`-prefixed
  linear statement immediately followed by a same-named statement whose body is a trivial read of
  it, treat the pair as one logical nonlin-producing statement for classification purposes).
  Contained entirely inside `Eval/Plan/Compile.lean`, a file this design already extends — leaves
  `route`/the legacy Br lowering completely untouched. Cost: more implementation complexity
  (detecting and undoing a transformation, rather than simply not performing it), and it would
  *not* remove the redundant-copy inefficiency Option A avoids as a side effect.

**Decision deferred to the implementation plan's own §0**, specifically pending: (1) whether
`route`'s scan-collapsing logic actually depends on the pre-split shape (if it doesn't, Option A's
risk evaporates and it's the clear choice); (2) whether the differential/oracle testing machinery
(`ScanUnroll.lean`/`ScanOracle.lean`, not yet investigated by this design either) has the same
dependency. Both must be resolved with real evidence before `splitScan` is touched, not assumed
either way here.

**Also worth confirming, lower stakes:** whether the legacy evaluator (`evalScheduled`) produces
identical results on an unsplit nonlin-bearing scan statement as it does today on the split pair —
expected to hold under Option A (splitting is a semantics-preserving transformation by
construction: compute the contraction, then apply nonlin, whether as one statement or two), but
must be confirmed with a real differential fixture, not assumed. And: `finalizeScans` (which
classifies `Stmt.nonlinOf` for its `isAffine`/Prop 8.7 check, `Structural.lean:1025`) runs *before*
`splitNonlins` regardless (`lowerArith >=> finalizeScans >=> splitNonlins >=> schedule`), so it
already sees pre-split-status-independent, original statements either way — unaffected by either
option, and its classification of a genuinely nonlinear scan as "not affine" remains correct under
either option (a nonlinear scan step was never going to be affine regardless of split shape).

## 2. Retained-local-axis mapping for `resolveNonlinAxis`

**The gap.** `resolveNonlinAxis` (`Compile.lean:780-798`) returns an index into the statement's
*full* LHS slot list (`slots`), at the position of the sole `.freeNorm`-marked slot. At the top
level this is provably correct as-is: `checkLHSSlot`/`freeUidOrFail` (`Compile.lean:46-51,
227-231`) reject `.iterAt`/`.iterNext`/`.affine` before `resolveNonlinAxis` ever runs, so
`slots`/`retainedUids`/`outputShape` are all the same length and 1:1 by construction — the raw
list position IS the correct `RawAxiswisePlan.axisPos` (confirmed directly at the one call site,
`Compile.lean:909-922`, no remapping step exists or is needed there).

Inside a scan, this 1:1 correspondence does not hold. `compileScan`'s own step-block output shape
(`Compile.lean:652-657`) is built by filtering to `.free` *only* (`.iterNext`/`.iterAt` excluded
by construction), so for a statement like `G[l + 1, j.] := softmax(...)` the full-slot-list
position of the `.freeNorm`-marked `j` (position 1, since `.iterNext l` is position 0) does not
match its position in the block's own local output shape (position 0, since the local shape
excludes the `l` axis entirely). Using the raw position directly, as the top-level code does,
would build an out-of-range or simply wrong `axisPos`.

**Resolution.** `resolveNonlinAxis` itself is unchanged — its marker-*finding* logic is already
correct at both levels (it never inspects `.iterAt`/`.iterNext`, by design, per the original
"restrict to local free axes" decision below). What's added is a small, shared post-processing
step, used identically by both callers: given the full-list position `p` `resolveNonlinAxis`
returns and the statement's own `slots`, count how many `.free`/`.freeNorm` slots occur at
positions `≤ p` — that count, minus one, is the position among *retained local output slots*,
which is what `RawAxiswisePlan.axisPos` actually needs. At the top level this remap is
provably a no-op (every slot is `.free`/`.freeNorm`, so the count-so-far always equals `p`), so
the top-level call site's existing correct behavior doesn't change; it just becomes one
application of the shared remap rather than an implicit identity. This is a small, easily unit-
tested function on its own (feed it slot lists with interleaved `.iterAt`/`.iterNext`/`.freeNorm`
in different orders, confirm the returned position matches hand-computed expectations) — the
critique's suggested test cases (marker before/after an iteration slot, marker first/middle/last,
non-trailing advancing dimensions) are exactly the right fixture set for it.

## 3. Normative semantics for nonlinear scan-block values

Stated explicitly as semantic laws, not left implicit in the compilation mechanism — added per
the external critique's #7, which correctly identified this as more important than the
code-sharing accounting below:

- The contraction (linear/assign step) always produces the **preactivation** slice, into an
  internal, unpublished slot.
- The nonlinearity executes over that preactivation slice, producing the **result** slice.
- Only the result slice — never the preactivation — is published under the statement's own name,
  used by `StateWriteMap.outputSlot`, listed in `RawPlanBlock.outputs`, inserted into whatever
  scratch/result slot-name table later statements consult, or associated with the statement for
  diagnostics. The preactivation slot is produced but never named or externally visible.
- A later statement (in the same block) reading a nonlinear scratch name observes the **result**
  slot, transparently — no different from reading any other scratch value.
- A later statement reading a **persistent state** name still observes the immutable pre-step
  capture (the snapshot taken before the current step began, per the existing `oldStates`
  discipline in `runDenseScan`) — this is unchanged by nonlinearity and not a new rule, but is
  worth stating so it isn't mistakenly re-derived as scan-nonlin-specific.
- For a base-block nonlinear state: the nonlinearity is applied before the (base) write commits
  the slice into the state's history — the base case follows the identical preactivation-then-
  result-then-publish rule as the step case, not a separate rule.
- Axiswise reduction is computed independently at each scan context coordinate (a direct
  consequence of restricting the reduction axis to the block's own local free axes, decision
  below, but worth stating as its own law: nothing about a per-step softmax accumulates or
  threads state across steps).

## 4. Decisions from the original brainstorm (unchanged, still hold)

1. **Support nonlinearity in both the base block and the step/recurrence block.**
2. **A persistent scan state may itself be the direct output of a nonlinearity** (e.g. a running
   softmax carried as state) — not restricted to per-step scratch/intermediate values.
3. **`.axiswise` reduction is restricted to the block's own local free axes** — no reduction
   across the scan's context/advancing axis (no cross-time-step softmax).
4. **Masked `.axiswise` (`Nonlin.axiswise fn (some predicate)`) stays deferred**, in scan blocks
   exactly as it already is at the top level. It would need a new compiled, UID-free boolean-
   predicate IR — real, bounded, and precedented in *kind* (this compiler already erases UIDs
   into position-based `AffineMap`s via `idxToRow` for `IdxExpr`s) but a separate piece of work.
   **Correction from the original draft**: this IR would be a *shared prerequisite* for also
   unblocking `.iverson` factors, not something that "would unblock both" outright — the two
   integrate at different call sites (axiswise masks at the reduction-coordinate evaluation
   point; Iverson factors inside a term's own factor product, with its own contracted-axis
   concerns) and each would still need its own separate lowering/checking/worker integration.
5. **The design must pay down the wiring-loop duplication** this repo's own history has twice
   flagged and deferred (`checkPlanBlock`/`runDenseBlock` are near-copies of `checkPlan`/
   `runDensePlan`'s outer wiring loops).
6. **Approach: a new `BlockStep` closed sum, structurally `PlanStep` minus `.scan`** — not literal
   reuse of `PlanStep` inside blocks (which would make `RawScanPlan` mutually recursive with
   itself, a real well-founded-recursion cost for no requested benefit).

## 5. Architecture

Two structurally parallel levels, sharing everything below "which node kinds exist":

- **Outer** (unchanged): `PlanStep | assign | scan | pointwise | axiswise`, checked/run by
  `checkPlan`/`runDensePlan` (`EvalPlan.lean`).
- **Block** (new): `BlockStep | assign | pointwise | axiswise`, checked/run by
  `checkPlanBlock`/`runDenseBlock` (`Block.lean`).

`BlockStep` lives in `RawStep.lean`, alongside `RawPlanBlock`.

### Data structures (new/changed)

```lean
-- RawStep.lean, alongside RawPlanBlock
inductive BlockStep
  | assign    (a : AssignPlan)
  | pointwise (p : RawPointwisePlan)
  | axiswise  (a : RawAxiswisePlan)
  deriving DecidableEq, BEq, Repr, Inhabited

-- RawPlanBlock.steps : Array BlockStep   (renamed from `assignments`, per critique #8 — once
-- the field holds pointwise/axiswise operations too, "assignments" misdescribes it, and this is
-- the least expensive time to fix the name, before any wire format is frozen)
```

```lean
-- Block.lean, mirroring CheckedPlanStepEvidence
inductive CheckedBlockStepEvidence
  | assign    (c : CheckedAssignPlan)
  | pointwise (c : CheckedPointwisePlan)
  | axiswise  (c : CheckedAxiswisePlan)

-- CheckedPlanBlock.checkedNodes : Array CheckedBlockStepEvidence  (was Array CheckedAssignPlan)
```

Two new thin error-wrapper constructors — **corrected from the original draft**, see below:

```lean
-- BlockError gains, mirroring PlanStepError.nonlin exactly (genuinely justified: NonlinPlanError's
-- constructors carry no locator of their own, so nodeIndex is real new information):
| nonlin (nodeIndex : Nat) (cause : NonlinPlanError)
```

**No new `ScanCompileError` constructor.** The original draft proposed
`ScanCompileError.nonlin (stmtName : String) (cause : NonlinCompileError)` — checked against the
real code and this is wrong: `PlanCompileCause` already has a `.nonlin (cause : NonlinCompileError)`
arm, `liftNonlin` (`Compile.lean:192-195`) already turns a `NonlinCompileError` into it, and every
`NonlinCompileError` constructor already carries `stmtName : String` as its own field
(`Error.lean:146-151`). The proposed wrapper would have duplicated the statement-name locator for
zero informational gain. **Default choice: reuse `PlanCompileCause.nonlin`/`liftNonlin` directly**
for scan-local statements' axis-resolution failures too, exactly as the top-level path already
does — no new error type needed. If the implementation plan finds that scan-specific context
(scan name, base-vs-step, statement index within the block) is genuinely needed for diagnostics,
the fallback is a wrapper that actually carries that context, not one that only repeats
`stmtName`.

## 6. The shared chaining helper: publication contract

The helper (extracted from Task 3's `prepareEvalPlan`'s `.plain`-branch logic, `Compile.lean:
888-924`) must guarantee, for both call sites (top-level and scan-block):

- **`.identity`**: one slot, one `.assign`, that slot is the published/result slot — byte-for-byte
  what the top-level path already does today.
- **non-`.identity`**: two slots (internal preactivation, result), an `.assign` into the internal
  slot, then a `.pointwise`/`.axiswise` from it into the result slot — the result slot is the
  *only* one published/used downstream (§3's law).
- Allocation and publication happen only *after* the axis-resolution step (§2's remap, or the
  masked-rejection check) succeeds — a rejected statement allocates nothing.
- The originating statement's own identity (name, locators) stays associated with the underlying
  `.assign`/`.pointwise`/`.axiswise` steps it produces, for causality diagnostics and error
  locators — the helper must not lose which source statement a given pair of steps came from.

(The original draft sketched this contract too loosely — noting only "an allocation callback" —
which the external critique correctly flagged as risking "writing the preactivation rather than
the nonlinear result into persistent state." The exact Lean shape of the helper's result value is
left to the implementation plan, not fixed here.)

## 7. Checker/runner sharing: what generalizes and what must not

**Corrected from the original draft.** `checkPlan`'s own doc comment (`EvalPlan.lean:32-44`)
already states, and the real code (`EvalPlan.lean:147-162`) confirms, that the `.assign` arm's
forward-read check deliberately does *not* go through the generic `PlanStep.sourceSlots`
accessor — it uses a direct per-term/per-factor loop specifically to preserve the `ti`/`fi`
locators `invalidForwardRead` needs. `.scan`/`.pointwise`/`.axiswise`, by contrast, already do use
`sourceSlots` directly, because they have no finer-grained internal structure to preserve.

So the generalization must not flatten every node kind through one "give me your source slots as
an array" interface for the *source-check* — destination bookkeeping (`step.destinationSlots`,
already uniform across every arm today, `EvalPlan.lean:138`) generalizes cleanly as-is. The
source-check side needs each node kind to supply its own check function (able to use whatever
locator precision it needs internally — `.assign`'s own rich `ti`/`fi` loop, or the generic
`sourceSlots`-based loop for everything else), with the *outer* availability/`producedBy`
bookkeeping shared. `BlockStep`'s three arms follow the identical split: `.assign` keeps its own
rich diagnostic loop verbatim; `.pointwise`/`.axiswise` use the generic path, exactly mirroring
`PlanStep`'s existing arms.

The generalized loop must also preserve exactly, not just approximately: validation order, error
precedence, the block-context-check vs. top-level-empty-context-check distinction, and the
missing-production sweep's current behavior. Given this, the wiring-loop generalization should be
its own task with its own regression review, *before* `BlockStep`'s new node kinds are added on
top of it — not bundled into one task with the new raw types, checked evidence, and new node
kinds (the original draft's suggested task 1 was too large for its own risk level).

## 8. `.freeNorm` impact inventory

`checkScanLHSSlot`'s preflight relaxation (mirroring Task 3's top-level `checkLHSSlot` change) is
necessary but not sufficient. Directly confirmed: `compileScan`'s step-block output-shape
construction (`Compile.lean:652-657`) filters LHS slots via `.free a => some a.uid | _ => none` —
a `.freeNorm`-marked slot falls into the `_ => none` branch today and would be **silently dropped**
from the output shape if the preflight rejection were lifted without also fixing this site. This
confirms the general pattern is real, not hypothetical.

Full inventory (adopted from the external critique; the step-outputUids site above is the one
directly confirmed in this pass — the rest follow the same pattern and need direct confirmation
in the implementation plan's own verification pass, not re-derivation from this list):
- base-block `outputUids` construction (the base-phase analogue of the step-block site above).
- step-block `outputUids` construction (confirmed above).
- base write-map construction (must treat `.freeNorm` identically to `.free` for identity-row
  placement).
- step state-write construction (same).
- scratch context-axis validation (must accept `.freeNorm` in non-advancing dimensions, same as
  `.free`).
- any "unreachable"-commented branch or totality guard that currently assumes `.freeNorm` cannot
  appear inside a scan block — every such comment needs updating alongside the code it describes,
  the same discipline Task 3 already applied at the top level.

The rule throughout: `.freeNorm` contributes the *same* local UID, extent, and identity-placement
row as `.free` everywhere except the one place that inspects it specifically to find the axiswise
reduction marker (`resolveNonlinAxis`, §2).

## 9. Code-sharing accounting (unchanged from the original draft — still holds)

**Reused 100% verbatim, zero changes:** `checkNonlinIO`/`checkPointwise`/`checkAxiswise`/
`runDensePointwise`/`runDenseAxiswise` (`Nonlin.lean` — already slot-table-agnostic, confirmed by
reading every signature); `RawPointwisePlan`/`RawAxiswisePlan`/`NonlinPlanError`/
`CheckedPointwisePlan`/`CheckedAxiswisePlan`; `PointwiseFn.apply`/`AxiswiseFn.apply`.
`resolveNonlinAxis` is reused verbatim for its marker-*finding* logic (§2 adds a remap on its
*output*, not a change to the function itself).

**Additional confirmed sharing, found this pass:** `residualizeAssignment` (`Compile.lean:321`,
the function that builds an `AssignPlan` from a statement's contraction body) is *already* the
shared core between the two paths, predating this design entirely — it's called from
`prepareEvalPlan`'s `.plain` branch (`Compile.lean:886`) and from `compileScan`'s base/step
phases (`Compile.lean:590,667`) today. This narrows the shared chaining helper's actual job: it
never needs to touch how the contraction itself gets built (already shared, zero changes), only
whether/how to wrap that already-built `AssignPlan` with a nonlin step afterward.

**Newly shared via generalization (written once, called from both paths):**
1. **The wiring loop's outer bookkeeping** (§7) — shared; per-node source-check diagnostics are
   not flattened away.
2. **The two-step nonlin chaining logic** (§6), called from `prepareEvalPlan`'s `.plain` branch
   (unchanged behavior) and `compileScan`'s base/step phases — on statements in whichever shape
   §1's still-open decision lands on (unsplit, under Option A, or recombined, under Option B).
3. **Bonus find, unchanged from the original draft:** once scan blocks admit unmasked
   `.pointwise`/`.axiswise`, `checkNonlinTopLevel`/`checkNonlinScanBlock` (`Compile.lean:64-75`)
   become literally identical function bodies and should re-merge into one `checkNonlin`.

**Necessarily separate:** `compileScan`'s own scan-specific phases (context axes, state-result-
vs-scratch classification, per-state geometry, causality, write-map construction) — genuinely
scan-specific. `BlockError.nonlin`/the reused `PlanCompileCause.nonlin` (§5) — different labels
where genuinely needed, not duplicated logic.

## 10. Forward-compatibility check: does this help gather/scatter/boolean dtypes/Iverson
    predicates?

Verified against real code; **the scatter claim below is corrected from the original draft**:

- **Affine gather: not a gap this design touches, already solved and already shared.**
  `ReadPlan`/`AffineMap`-based reads already exist inside `AssignPlan.terms[*].factors`
  (`Kernel.lean:26-31`), and `RawPlanBlock.steps`' `.assign` arm carries the same `AssignPlan`
  type the outer plan uses — already shared, unrelated to `BlockStep`.
- **Scatter: this design's wiring-loop generalization helps, but not for the reason originally
  claimed.** The original draft said the wiring loop "only needs one source slot and one
  destination slot" for a scatter node — checked, and this conflates the write side with the read
  side. A scatter's *destination* genuinely would be one slot with an affine placement map,
  mirroring `StateWriteMap` (`RawStep.lean:54-58`) — that part holds. But a scatter's RHS, like
  any `AssignPlan`, may read from arbitrarily many source slots via ordinary terms/factors — "one
  source slot" is wrong. The accurate and, notably, *stronger* claim: the wiring loop already
  returns `Array TensorSlot` (not a single slot) for every existing node kind's source slots,
  including `.assign` today, which already has many-source reads. The wiring loop's actual
  requirement is just "a statically-known array of source/destination slots" — a future scatter
  node fits that regardless of how many terms it reads or how its own write-collision policy
  works, neither of which this design designs.
- **Boolean dtypes: orthogonal, not helped by this design.** `.bool`/`.f32` already exist as
  reserved-but-unused `ScalarDType`/`ScalarConst` tags; every dtype check hard-codes `== .f64`
  (not a set-membership test); `DenseTensor.data : Array Float` is unconditional storage. None of
  this is touched by `BlockStep` or the wiring-loop generalization.
- **Iverson/predicate factors: orthogonal to `BlockStep`, already free-riding on something
  older.** An Iverson `Factor` lives inside `AssignPlan.terms`, two levels below the step-dispatch
  level this design operates at (`Compile.lean:55`). It's already scan-block-shared for the same
  reason gather is (same `AssignPlan`/`TermPlan` type in both contexts), not because of anything
  `BlockStep` contributes.

Net: this design's real leverage among the four is on **scatter's outer bookkeeping** — and even
there, only the wiring-loop's slot-array generality, not a specific payload shape (which remains
undesigned).

## 11. Risk profile and suggested task shape

The wiring-loop generalization (§7) is the highest-risk piece — a refactor of already-shipped,
heavily-tested production code, not additive new arms. "Preservation" should be defined via
observable artifacts, not "byte-identical" (many `Checked*` evidence types derive `Repr` only, not
`BEq` — direct `==` comparison isn't even available for them): raw plan exact equality (the `Raw*`
types do derive `DecidableEq`/`BEq`), materialized-bindings exact equality, warning-list exact
equality, exact error constructor and priority, `Dense` output shape and `Float.toBits` data
equality, and existing corpus counts unchanged. For the wiring-loop refactor specifically: capture
a pre-refactor mutation/error matrix (the exact set of guard-removal-triggered failures the
current `checkPlan`/`checkPlanBlock` produce) and confirm the identical set reproduces after the
generalized version replaces them — a concrete regression technique, not just "run the suite."

Suggested (not committed) task shape, revised from the original draft to split the
over-large first task (per critique #5) and add the pipeline-boundary work (§1):

0. **Investigate first, before any of the below is scheduled as a task**: read `route`'s actual
   implementation to determine whether it depends on scan statements arriving pre-split, and
   check `ScanUnroll.lean`/`ScanOracle.lean` for the same dependency. This resolves §1's Option
   A/B choice with evidence rather than either being assumed — the two options lead to
   meaningfully different Task 1s below, so this gates the plan's own shape, not just its content.
1. Pipeline-boundary change, per whichever option §0 supports: (Option A) `splitScan` stops
   splitting inside `.scan` nodes, with a real differential fixture proving `evalScheduled` agrees
   on the now-unsplit scan statement; or (Option B) `compileScan`'s Phase 1 classifier gains
   split-pair recognition, entirely contained in `Eval/Plan/Compile.lean`. Either way: confirm
   `finalizeScans`/`schedule` are unaffected (already argued in §1, re-confirm directly).
2. Wiring-loop generalization alone (no new node kinds yet) — its own task, its own review,
   verified via the mutation/error-matrix technique above against the *existing* `.assign`/`.scan`
   behavior only.
3. `BlockStep`/`CheckedBlockStepEvidence` types + wiring `checkPlanBlock`/`runDenseBlock` onto the
   now-generalized loop with the 3 new arms.
4. The shared chaining helper (§6), with its publication contract as an explicit fixture set;
   refactor `prepareEvalPlan`'s `.plain` branch to use it (parity fixture: `.identity` still
   byte-for-byte unchanged).
5. Wire `compileScan`'s Phase 3/4 to call the same helper (on unsplit statements under Option A,
   or recombined pairs under Option B, §1); the retained-local-axis remap (§2) as its own tested
   unit; the `.freeNorm` inventory (§8); relax `checkScanLHSSlot`; merge `checkNonlin`.
6. Test matrix (§12) and closure: architecture doc, discoverability, completion record,
   whole-branch review (two independent reviewers, per the same soundness-relevant-closed-sum rule
   Thread 4 applied).

## 12. Test matrix

Expanded from the original draft's six-fixture sketch, which covered only smoke tests:

- **Positional correctness** (targets §2's bug directly): axiswise state with an iteration slot
  before the marked local axis; iteration slots interleaved between multiple local axes; marked
  axis first/middle/last; multi-axis scan with non-trailing advancing dimensions.
- **Publication correctness** (targets §3/§6): nonlinear scratch consumed by a later scratch;
  consumed by a state result; a direct nonlinear state consumed downstream outside the scan; a
  coupled scan with one nonlinear and one linear state; explicit verification that the committed
  state is the *result*, not the preactivation.
- **Base-block correctness**: nonlinear base state; multiple base writes to one state; a pinned
  override plus a free-face base write; verification that every `StateWriteMap.outputSlot` names
  the final (result) slot, never the preactivation.
- **Negative source tests**: masked axiswise in base and step (still rejected); missing reduction
  marker; multiple markers; marker on a pointwise/identity statement; `.freeNorm` naming a context
  axis; a malformed local axis position caught by §2's remap.
- **Direct block-checker tests** (hand-built `BlockStep`s): forward read; duplicate destination;
  input overwrite; slot out of range; source/destination shape mismatch; non-`f64` signature;
  axis position out of range; missing production; exact error constructor and node index.
- **Semantic differential tests**: compiled checked plan vs. legacy `evalScheduled` vs. independent
  scan unrolling where available — including a fixture specifically constructed so that its result
  would differ if axiswise reduction were accidentally computed across the scan's history rather
  than independently at each context coordinate (§3's last law) — a fixture that fails loudly on
  exactly the mistake this design's own scoping decision (§4.3) is meant to prevent.

## Open items for the implementation plan to resolve (not decided here)

- **The highest-priority open item**: whether `route` (`TLProgram.compile`'s final phase,
  `DSL/Compile.lean:31` — confirmed to share `splitNonlins`' exact output with the Eval/Plan
  pipeline, §1) or the differential/oracle machinery (`ScanUnroll.lean`/`ScanOracle.lean`, not
  yet investigated) actually *depends on* scan statements arriving pre-split, as opposed to
  merely being fed them today. This determines the choice between §1's Option A (change
  `splitScan`, simpler, but touches a function `route` also consumes) and Option B (leave
  `splitScan` untouched, recombine split pairs inside `compileScan` instead, more contained but
  more complex) — resolve with evidence before scheduling Task 1, not by assumption either way.
- Exact Lean signature for the wiring-loop generalization's per-node source-check callback (§7) —
  a real Lean-idiom judgment call, needs `check-snippet.sh` verification against the real types.
- The exact shape of the shared chaining helper's result value (§6) — illustrative only here, not
  fixed.
- Whether `checkNonlinTopLevel`/`checkNonlinScanBlock`'s merge-back (§9) happens in the same task
  as the scan-block relaxation, or as a small separate cleanup task.
- Whether scan-specific error context (scan name, base-vs-step, statement index) turns out to be
  needed for `PlanCompileCause.nonlin`'s reuse (§5) — default is no new wrapper; revisit only if a
  real diagnostic need surfaces.
- Independent confirmation of the remaining `.freeNorm` inventory sites beyond the one directly
  confirmed in this pass (§8).
- Exact new test file naming/placement for the scan-block nonlin fixtures.
