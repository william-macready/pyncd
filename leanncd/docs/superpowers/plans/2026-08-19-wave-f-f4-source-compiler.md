# F4 — source compiler, adapter boundary, and differential gate

## 0. Session verification record (2026-08-19)

This plan supersedes `papers/f4_plan_thoughts.md`, a draft committed directly to `main` (`c59a1e1`,
co-authored with Copilot) that memory `jax-evalplan-doc-rework` flagged as **not yet reviewed by any
session or verified against `slice-plan`'s own discipline**. This session read every claim in that
draft against the real code (not against the draft's own prose) before adopting it. What was checked
directly, this session, in this worktree:

- **Full build.** `lake build` (default targets) — **green, 8,651 jobs**, on `main` at `c59a1e1`
  (matches the draft's claim; the three doc-only commits since F3's merge don't touch `LeanNCD`).
- **Generated corpus split (17 / 9 / 4 / 4).** Read `test/Eval/PropertyOracle/ScanGen.lean` directly
  and hand-classified all six templates against the real, existing `checkNonlin`/`checkAggOp`
  (`Compile.lean:43-51`): template 1 (4 cases, identity/no-agg) accepted, template 2 (4 cases,
  `.pointwise .relu`) → `unsupportedNonlin`, template 3 (2 cases, identity/no-agg, coupled) accepted,
  template 4 (2 cases, identity/no-agg, external read) accepted, template 5 (4 cases, `.max`/`.min`)
  → `unsupportedAgg`, template 6 (1 case, identity/no-agg, 2-D) accepted. `9 = 4+2+2+1` accepted,
  `4` `unsupportedNonlin`, `4` `unsupportedAgg`, total `17` — the draft's claimed split is correct,
  independently re-derived rather than trusted.
- **Both Task 1 defects, confirmed by reading the shipped F3 code, not by trusting the draft or
  memory's account of them:**
  1. **Write-map rank gap** (the item F3's own completion record left as a deliberate, unfixed
     follow-up — see `papers/wave_f_scanplan_proposal.md` §13's F3 record). Confirmed still present:
     `writeRowKinds` (`Scan.lean:30-32`) reads `w.map.coeffs.getD d #[]` and `w.map.bias.getD d 0` —
     a short `coeffs`/`bias` array silently pads with defaults rather than failing, and `checkWrites`
     never compares `w.map.coeffs.size`/`w.map.bias.size` against the state's own rank before calling
     `writeRowKinds`. `freeExtentsAgree`/`pinnedLiteralsInRange` (the two gaps F3's final review
     already closed) are confirmed present in the shipped code (`Scan.lean:65-83`) — only the rank
     gap remains.
  2. **Capture-order-vs-`block.inputs`-order mismatch** — not previously named in any memory, found
     independently this session by reading `runDenseScan` against `runDenseBlock`. `runDenseBlock`
     (`Block.lean:109-129`) binds `inputs[i]` positionally to `raw.inputs[i]`, and `checkPlanBlock`
     requires `block.inputs` to be strictly sorted (`Block.lean:60-63`). But `runDenseScan`
     (`Scan.lean:421-423`, `432-434`) builds the input-value array via
     `raw.baseCaptures.mapM (...)`/`raw.stepCaptures.mapM (...)` — i.e. in **capture-array** order.
     `checkCaptures` (`Scan.lean:185-213`) only verifies a bijection between captures and
     `block.inputs`; it does not require the capture array to be declared in sorted-input order. A
     capture array built in a different order than `block.inputs` (exactly what a source compiler
     that appends captures in first-encountered-name order, as F4's compiler naturally would, will
     produce) binds the wrong tensor to the wrong block input, silently. This is real and reachable
     by any compiler that doesn't happen to emit captures pre-sorted by `inputSlot` — confirmed a
     defect independent of the draft's own account, which the draft plan happens to already fix as
     part of the same Task 1 (items 3-4 below).
- **Task 2's extraction target.** Confirmed against `Compile.lean`'s Step D loop (`Compile.lean:196-239`):
  the per-statement residualization (`retainedUids`/`contractedUids`/`basisUids`/`outputPos`/
  `reductionPos`/factor-row lowering via `idxToRow`) is exactly the logic the draft describes
  extracting, and it currently has no context/pin parameters — it hardcodes `contextShape := #[]`
  and no pin substitution, matching the draft's description of what has to change.
- **Task 3's structural claims.** Confirmed against `LeanNCD/DSL/Pipeline/Types.lean` (`ScanStmt.scan`
  really is `name → axes → base : List Stmt → recur : List Stmt → isAffine`, so the compiler can
  traverse `base`/`recur` directly) and `LeanNCD/DSL/Pipeline/Lowering.lean` (`ScanStmt.outputs`
  really does filter to names written by **both** base and recur, dropping single-sided
  intermediates — confirming §4.2's warning against using it or the scan's representative name for
  state classification is grounded, not speculative). Confirmed `PlanCompileCause`
  (`EvalPlan.lean:189-195`) has no `.scan` constructor yet, and `CapabilityError.scanNode` already
  exists and currently rejects every `.scan`/`.scanPre` node unconditionally
  (`Compile.lean:67-70`) — this is the exact point Task 3 must change from "reject" to "specialize."
- **Terminology correction to the draft.** The draft (§4.7, §9) refers to "`outerInputBindings`" as
  something the compiler must produce. No such identifier exists. The real type is
  `PlanBindings.requiredInputs : RequiredBindings` (built via `checkBindings`, consumed by `pack` in
  `Adapter.lean`). Every occurrence below uses the real name.
- **Not independently re-verified this session** (adopted from the draft on the strength of its own
  "Plan-authoring verification record," §13, since re-running every probe would cost more than the
  risk it retires): the exact base-pin arithmetic worked example (hand-checked by arithmetic only:
  `7 + 2·5 + 4·5 = 37`, remaining coefficient `-3` — arithmetic, not a compiled probe), the padded-read
  warning-parity probe, and the named-adapter `dp = [0,1,1,1]` probe. If Task 3/4's implementer
  reaches a contradiction with any of these during implementation, treat the implementer's own
  compiled result as authoritative over this document, per this repo's own `verify-before-claiming-
  code-state` discipline.

No Lean code blocks appear in this plan requiring `check-snippet.sh` compilation (prose and tables
only, matching the draft's own convention).

## 1. Purpose

Extend `LeanNCD.Eval.Plan.prepareEvalPlan` from the Wave C scan-free fragment to the Wave F
source-scan fragment defined in `papers/wave_f_scanplan_proposal.md` §5 and §7-11.

F4 must:

1. repair the two F3 soundness defects reproduced above;
2. specialize every admitted `.scan` into a checked `PlanStep.scan`;
3. preserve the four-layer error boundary;
4. execute scans through the existing named adapter boundary;
5. prove parity against both `evalScheduled` and an independent scan-free unrolling; and
6. finish with a clean full build and whole-branch review.

No supported scan may fall back to `Eval.evalScan`.

## 2. Scope

### 2.1 In scope

- F3 checker/worker prerequisite repairs (both defects in §0 above).
- Scan-aware capability preflight and source diagnostics.
- Static shape inference across plain, base, and recurrence assignments.
- Source scan classification and residualization into `RawScanPlan`.
- Checked outer-plan integration and materialization of complete state histories.
- Named-boundary, legacy differential, and independent-oracle tests.
- Directly related documentation and the F4 completion record.

### 2.2 Explicitly out of scope

- JAX scan lowering or repair of `runJaxPlan`'s current scan limitation.
- General affine/scatter LHS support.
- Overlapping base-write resolution.
- Multiple unrestricted boundary faces for one state.
- General non-rectangular or non-uniform scan traversal.
- F5's capability manifest and whole-wave audit.
- Optimizations based on `isAffine`.

## 3. Verified starting point

| Area | Status | Evidence |
|---|---|---|
| Repository | Ready | Clean worktree at local `main` commit `c59a1e1` (verified this session, `.lake` synced from the primary checkout's 8101-olean donor). |
| Full build | Ready | `lake build` passed, **8,651 jobs** (re-run this session, not just cited from memory). |
| F0 | Ready | Exhaustive scan classifier and legacy fixtures build. |
| F1 | Ready | Contextual assignment IR, checker, Dense worker, and tests build. |
| F2 | Ready | Checked plan blocks, opaque construction, execution, and tests build. |
| F3 structure | Ready | Raw scan IR, checker, Dense worker, outer step integration, and tests build (`Scan.lean`, `EvalPlan.lean`, `RawStep.lean` read directly this session). |
| F3 soundness | Blocked | Two reproduced defects (write-map rank gap; capture-order mismatch) must be fixed in Task 1 — both confirmed present in the current code, not merely cited from a prior record. |
| Generated corpus | Measured | 17 total: 9 accepted, 4 `unsupportedNonlin`, 4 `unsupportedAgg` — independently re-derived from `ScanGen.lean`'s six templates this session, not just cited. |
| Lean cache | Ready | `.lake` synced fresh into this worktree; no further Mathlib olean rsync is planned. |

F0-F3 are structurally present. F3 becomes a valid compiler target only after Task 1.

## 4. Contract fixed by preliminary probes

This section records decisions the implementation must follow. The task descriptions refer back to
these contracts rather than restating them.

### 4.1 Compiler phase order and error ownership

Preserve this exact order:

1. whole-program capability preflight in source order;
2. external signature validation;
3. static shape inference over plain, base, and recurrence assignments;
4. source-ordered scan specialization;
5. F3 `checkScanPlan`, followed by outer `checkPlan`;
6. runtime named-input packing and Dense execution.

Error ownership:

| Phase | Error family | Required use |
|---|---|---|
| Preflight | `CapabilityError` | Syntactically visible unsupported source. |
| Source specialization | `ScanCompileError` (new) | Pairing, dependency, geometry, or causality failures requiring shapes or affine maps. |
| Checked-plan validation | `PlanError.scanError` / `invalidPlan` | Malformed raw scan data; compiler-produced rejection is internal. |
| Runtime binding | `PositionalInputError` | Missing, malformed, or wrong-shaped external tensors. |

Specific requirements:

- Add `CapabilityError.noAdvancingAxis`.
- Reject `.scanPre` with `recurrenceOrCallback` (the constructor already exists — `Error.lean:69` —
  and is already used for `Stmt.recurMorphism`; reuse it, do not add a second one).
- Define closed `ScanCompileError` in `Eval/Plan/Error.lean`.
- Add `PlanCompileCause.scan` (confirmed absent from `EvalPlan.lean`'s current five-constructor
  `PlanCompileCause` this session).
- Preserve warnings already produced before a later compile failure.
- Never relabel a compiler-produced `ScanPlanError` as a source capability error.
- Source errors must carry source locators: scan index/name, state name, local statement index, and
  term/factor index where applicable.

`ScanCompileError` must distinguish at least:

- state/base/result pairing;
- advancing-axis mapping and write geometry;
- base range, boundary contact, and overlap;
- duplicate or forward block dependencies;
- state reads in a base block;
- step causality; and
- zero extent discovered after shape inference.

### 4.2 Persistent-state and scratch classification

Neither the scheduled scan's representative name nor `ScanStmt.outputs` defines persistent state —
confirmed this session by reading `ScanStmt.outputs`'s real definition (`Lowering.lean:96-99`): it
filters to names written by **both** the base list and the recur list, dropping intermediates that
appear on only one side. That is a reasonable summary for topological scheduling, but it is not the
same classification F4 needs, for two independent reasons that hold regardless of what `.outputs`
happens to return for any one example:

- a scratch-heavy scan can produce a recurrence-list destination named identically to something in
  the base list by accident of naming, without it being persistent state;
- a state's boundary may be split across **several** base statements sharing its name (§5.1), and
  `.outputs`/`.writes` (`List.eraseDups`-based) collapse that into one name, discarding the
  multiplicity the compiler needs to build one `StateWriteMap` per base statement.

Use the following deterministic rule instead, traversing `ScanStmt.scan`'s own `base`/`recur` fields
directly rather than the derived `.outputs`/`.writes` accessors:

1. Traverse base assignments in source order.
2. Form the ordered unique list of base destination names.
3. Treat each name as a persistent-state candidate with one or more base writes.
4. Require exactly one recurrence result with an all-axis `iterNext` LHS for each candidate.
5. Treat a recurrence result with advancing LHS syntax but no base candidate as an orphan result,
   not scratch.
6. Treat all other recurrence destinations as block-local scratch with one producer.
7. Reject orphan bases, orphan or partial advancing results, duplicate state results, duplicate
   scratch producers, and forward scratch reads.

Persistent state names resolve to immutable state-capture slots for the entire step block. Compiling
one state's next value must not shadow that capture before a later coupled result is lowered.
Scratch names become readable only after their producer.

Therefore, the common assignment lowerer (Task 2) constructs an assignment but does not mutate the
caller's name environment. Each caller owns publication policy.

### 4.3 Axis identity and state geometry

- Axis identity is by `UID`, never source name or raw list position.
- Context order is `ScanStmt.axes`.
- For each state, match each context-axis UID to its unique LHS position.
- Require the same mapping across every base and step write for that state.

Illustrative (not measured) coupled-state mapping showing why raw context order cannot be reused as
state-dimension order:

- context order: `[r, c]`;
- `G.advancingDims = #[0, 2]`;
- `H.advancingDims = #[2, 1]`.

### 4.4 Assignment residualization

Use these ordered bases:

| Assignment kind | Basis |
|---|---|
| Plain | `output ++ reduction` |
| Base | `free output ++ reduction`, after substituting validated pins |
| Step | `full scan context ++ output ++ reduction` |

For base assignments:

- substitute every `iterAt` pin into every normalized RHS affine row;
- add every pinned coefficient contribution to the bias;
- remove pinned UIDs from the residual basis.

Hand-checked (arithmetic, not a compiled probe) expected duplicate-pin behavior:

- initial bias: `7`;
- coefficients: `2u - 3v + 4u`;
- pin: `u = 5`;
- remaining basis: `[v]`;
- result: coefficient row `[-3]`, bias `7 + 2·5 + 4·5 = 37`.

For step assignments, include the full context even if a term does not mention every context axis.

### 4.5 Shape inference and external ordering

- Flatten plain, base, and recurrence assignments in source order for
  `inferAxisSizesFromSignature`.
- Preserve `orderedExtNames` first-seen external-input order (the real Wave C helper,
  `Compile.lean:108-112`, confirmed present and reusable for the scan fragment).
- Static-signature and concrete-input size maps must agree.

### 4.6 Base, step, and publication semantics

- Scan extents are statically known and at least one.
- Extent one performs base initialization and zero step iterations.
- Base writes are ordered in the raw plan but must be pairwise disjoint for F4 source admission.
- The admitted multi-write form is one free-axis face plus disjoint fully-pinned points (see the
  proposal's §5.1 for why two free-axis faces for one state can never be disjoint — a structural
  fact already enforced by `writesCollide`, confirmed above in `Scan.lean:91-95`).
- Two unrestricted boundary faces remain rejected even if their RHS values agree.
- Step writes use canonical rectangular all-axis `+1` geometry.
- State allocation and outer publication are atomic.
- Complete histories are materialized in persistent-state order.
- Scratch slots remain local and are never outer slots or materialized names.
- More than one admitted scan may appear in an outer schedule.
- Preserve source factor and reduction order.

### 4.7 Adapter boundary

`pack`/`unpack`/`runPreparedDense` (`Adapter.lean`, read directly this session) are already generic
over `PreparedPlan`/`CheckedEvalPlan` and require no scan-specific logic: `pack` resolves inputs by
name through `PlanBindings.requiredInputs : RequiredBindings` (not "`outerInputBindings`" — that
identifier does not exist in the codebase); `unpack` inserts every `PlanBindings.materializedNames`
entry into the named environment, preserving unrelated original inputs exactly. The compiler
therefore does not need adapter changes — only:

- a correct `requiredInputs : RequiredBindings` (built by `checkBindings`, exactly as Wave C already
  does in `Compile.lean`'s Step F); and
- one `materializedNames` entry per persistent state.

Do not make speculative adapter production changes. Change adapter production code only if a
source-compiler fixture demonstrates a real boundary defect.

### 4.8 Independent oracle

The current oracle (`test/Eval/PropertyOracle/ScanUnroll.lean`) is insufficient:

- the one-axis unroller always selects the immediate predecessor;
- same-step scratch renaming is incomplete;
- comparison assumes trailing scan dimensions;
- the two-axis unroller supports one fixed 2×2 template.

The replacement must remain independent from:

- `runDenseScan`;
- `evalScan`;
- `writeRowKinds`;
- `applyAffine`;
- compiler residualization helpers; and
- worker write helpers during history reconstruction.

It may evaluate the mechanically generated scan-free `TLProgram`.

## 5. Task graph, review boundaries, and per-task process weight

```text
Task 1: F3 soundness ─────┐
                          ├─> Task 3: source compiler ─> Task 4: named/legacy gate ─> Task 5: oracle/final
Task 2: lowering parity ──┘
```

| Task | Outcome | Independent review reason | Risk / process weight |
|---|---|---|---|
| 1 | Sound checked scan target | Existing kernel boundary; valid even if compiler work is rejected. | **Low-moderate.** Two localized, well-characterized bug fixes with known repro shapes (§0). Full implementer+reviewer dispatch is still warranted (production checker code, not doc/rename), but do not escalate model tier or add extra review rounds beyond one — this is the closest thing in F4 to F3's own "Task 2, small, clean" case. |
| 2 | Reusable lowering with scan-free parity | Changes existing compiler behavior and has its own regression blast radius. | **Moderate.** A refactor-only extraction (§0's Task 2 verification), but it touches `Compile.lean`'s one existing production compiler path — a regression here silently breaks Wave C. Full dispatch, one review round; the parity fixtures are the load-bearing gate, not novel design judgment. |
| 3 | Complete source scan specialization | Main production feature and natural rollback unit. | **High.** This is F4's architectural centerpiece — new classification, geometry, and causality logic with no precedent to copy from (F3 built the checked target, not the compiler). Give this task's review the same weight F3 gave Task 4 (its own centerpiece): expect at least one fix round, and do not compress its review just because Tasks 1/2 landed clean. |
| 4 | Public boundary and legacy parity | Proves API behavior rather than raw-plan structure. | **Moderate-high.** Large fixture surface (execution matrix × all Task 3 acceptance fixtures + boundary cases), but the boundary code itself (`pack`/`unpack`) is not expected to change (§4.7) — most of the risk is in exercising Task 3's compiler correctly, not in this task's own new code. |
| 5 | Independent oracle and final closure | Independent implementation plus whole-branch evidence. | **High.** A second from-scratch implementation (the generalized unroller) plus the mandatory whole-branch review. Per this repo's own standing lesson (`feedback-scale-process-to-task-risk`), do not compress the final whole-branch review regardless of how clean Tasks 1-4 land — F3's own final review found a Critical soundness gap after every per-task review had already passed. |

Tasks 1 and 2 must pass their own reviews before Task 3. Task 4 depends on Task 3. Task 5 depends on
the completed production and named-boundary paths.

**Applying `feedback-scale-process-to-task-risk` at dispatch time:** Tasks 1 and 2 are the closest
this plan has to "mechanical," but neither is pure doc/rename work — both touch checker or compiler
production code with real failure modes, so both still warrant full implementer+reviewer SDD dispatch
(this differs from F3's own Task 2, which really was a single small insertion). What should scale
down is *review round count and model tier for fix waves* on Tasks 1/2 specifically if their first
review passes clean — don't manufacture a second round there to match Task 3/5's expected depth.

## 6. Task 1 — close F3 checker/worker soundness gaps

### Outcome

F3 rejects malformed write-map ranks and binds captures solely by explicit `inputSlot`, resolved
into `RawPlanBlock.inputs` order.

### Files

- `LeanNCD/Eval/Plan/Scan.lean`
- `test/Eval/Plan/ScanTest.lean`

### Implementation

1. Add separate, locatable `ScanPlanError` constructors for:
   - coefficient-row-count mismatch (`w.map.coeffs.size` vs. state rank);
   - bias-count mismatch (`w.map.bias.size` vs. state rank).
2. In `checkWrites`, check both counts against `stateShape.size` **before** calling `writeRowKinds`
   (which currently pads short arrays via `getD` — confirmed this session, `Scan.lean:30-32` — rather
   than failing).
3. For base and step blocks, resolve the unique capture for each declared block input: build a
   lookup from `inputSlot` to its capture (already established as a bijection by `checkCaptures`),
   then map over `block.inputs` (sorted, per `checkPlanBlock`) to construct the input-value array —
   not by mapping over `raw.baseCaptures`/`raw.stepCaptures` in their own stored order, which is what
   `runDenseScan` does today (confirmed this session, `Scan.lean:421-423`, `432-434`) and is not
   guaranteed to match `block.inputs`' sorted order.
4. Apply the same fix to both `baseExternalInputs` and `stepInputs` in `runDenseScan`.
5. Retain order-insensitive capture validation in `checkCaptures` — this fix is entirely in how
   `runDenseScan` consumes an already-validated capture array, not in what `checkCaptures` accepts.

### Tests

- Coefficient rows shorter and longer than state rank.
- Bias rows shorter and longer than state rank.
- Base-capture reordering with same-shaped inputs (a capture array deliberately NOT in
  sorted-`inputSlot` order, to exercise the fix from item 3-4 directly).
- Coupled-state step-capture reordering.
- Exact error payloads.
- Exact observed histories after the capture-order fix.

### Mutation checks

- Remove each rank equality independently; the matching short/long fixture must fail.
- Restore capture-array-order binding (i.e. revert to mapping over `baseCaptures`/`stepCaptures`
  directly); the reordering fixture must reproduce the wrong bound tensor.
- Restore the fix; all fixtures must pass.

### Gate

```bash
cd leanncd
lake build Eval.Plan.ScanTest
lake build LeanNCD
```

Complete an independent task review before Task 3.

## 7. Task 2 — extract common assignment lowering with scan-free parity

### Outcome

Plain assignment compilation uses a reusable residualization helper without changing existing
behavior.

### Files

- `LeanNCD/Eval/Plan/Compile.lean`
- `test/Eval/Plan/CompileTest.lean`
- `test/Eval/Plan/DifferentialTest.lean`

### Implementation

1. Extract `Compile.lean`'s Step D per-statement loop (`Compile.lean:196-239`, confirmed this session
   as the exact target: `retainedUids`/`contractedUids`/`basisUids`/`outputPos`/`reductionPos`/
   factor-row lowering) into a private helper.
2. Make the caller supply:
   - context axes and shape;
   - output and reduction bases;
   - validated pinned UID values;
   - a source-name-to-slot resolver;
   - destination slot and signature.
3. Have the helper construct only `RawAssignPlan` (via `TermPlan`/`ReadPlan` as today).
4. Keep name-environment mutation in the caller.
5. Route plain assignments through the helper with empty context and no pins — this must reproduce
   `Compile.lean`'s current behavior exactly (`contextShape := #[]`, no pin substitution).
6. Continue rejecting scans in this task (`checkScanStmt` unchanged).

### Tests

Keep all existing expectations unchanged and add structural parity for:

- a contraction;
- multiple factors and ordered reductions;
- repeated outer assignment names;
- affine padding and warning behavior.

### Mutation checks

- Perturb the plain caller's basis order; a structural/differential fixture must fail.
- Omit the plain caller's name publication; the repeated-name fixture must fail.
- Restore both changes; all fixtures must pass.

### Gate

```bash
cd leanncd
lake build Eval.Plan.CompileTest Eval.Plan.DifferentialTest
lake build LeanNCD
```

Complete an independent parity review before Task 3.

## 8. Task 3 — implement source scan admission and residualization

### Outcome

`prepareEvalPlan` compiles the complete admitted Wave F source fragment into checked scan steps with
typed source diagnostics.

### Files

- `LeanNCD/Eval/Plan/Error.lean`
- `LeanNCD/Eval/Plan/EvalPlan.lean`
- `LeanNCD/Eval/Plan/Compile.lean`
- new `test/Eval/Plan/ScanCompileTest.lean`
- `lakefile.toml`

Keep raw F3 fixtures in `ScanTest.lean`; register source compiler fixtures separately.

### Implementation A — error and preflight boundary

1. Add closed `ScanCompileError`.
2. Add `PlanCompileCause.scan`.
3. Port F0's `.scan` classification into production.
4. Reject empty axes with `noAdvancingAxis`.
5. Reject `.scanPre` with `recurrenceOrCallback` (existing constructor, confirmed reused not
   duplicated — see §4.1).
6. Apply scan-specific admitted LHS rules recursively to all base and recurrence assignments —
   `checkLHSSlot` (`Compile.lean:31-36`) currently rejects `.iterAt`/`.iterNext` unconditionally via
   `unsupportedLhsSlot`, because it is Wave C's plain-statement preflight; a scan's base/recurrence
   statements need a distinct admission rule for these two constructors specifically (`.iterAt` in
   base statements, `.iterNext` in recurrence statements), while still rejecting `.freeNorm`/`.affine`
   there and still rejecting `.iterAt`/`.iterNext` for genuinely plain (non-scan) statements.
7. Preserve whole-program capability precedence.
8. Feed source-ordered plain, base, and recurrence assignments to static shape inference.

### Implementation B — source specialization

For each source scan:

1. Classify persistent states and scratch using §4.2 — traversing `ScanStmt.scan`'s `base`/`recur`
   fields directly, not `.outputs`/`.writes`.
2. Derive context axes and extents from `ScanStmt.axes` and static sizes.
3. Derive each state's full signature and UID-based `advancingDims`.
4. Validate consistent state geometry across all base and step writes.
5. Precollect deterministic captures:
   - base block: available outer tensors;
   - step block: immutable state histories and available outer tensors;
   - one local input slot per captured source name;
   - explicit source-slot to input-slot capture records.
6. Allocate assignment destinations in source order.
7. Publish scratch only after its producer.
8. Never shadow persistent state captures with next-state result slots.
9. Lower base assignments with empty context and pin substitution, via Task 2's helper.
10. Lower recurrence assignments with full `stepExtents` context, via Task 2's helper.
11. Build one base `StateWriteMap` per base assignment.
12. Build exactly one step write per persistent state.
13. Validate source-facing:
    - state/base/result pairing;
    - dependency order;
    - base range, boundary contact, and disjointness;
    - canonical step geometry;
    - conservative state-read causality.
14. Build `RawScanPlan`.
15. Call `checkScanPlan`; report unexpected compiler-output rejection as `invalidPlan`.
16. Allocate one outer destination and materialization binding per state.
17. Publish all state histories atomically after the scan step.
18. Run final outer `checkPlan`.

### Acceptance fixtures

- One-axis self recurrence.
- Coupled states with different advancing-dimension positions/orders.
- Scratch produced and consumed before a state result.
- External current-coordinate reads.
- Contractions.
- Constant deep history with zero padding.
- Extent one.
- Arbitrary state-axis positions.
- Duplicate pinned-UID bias substitution.
- One state with multiple disjoint base writes.
- More than one scan in an outer schedule.
- A later plain statement consuming a scan history.

### Typed rejection fixtures

- Empty axes and `.scanPre`.
- Every unsupported assignment-syntax category inside base and recurrence blocks.
- Zero inferred extent.
- Orphan base.
- Orphan, duplicate, or partial advancing result.
- Duplicate scratch destination.
- Forward scratch read.
- State read from a base block.
- Missing or inconsistent state advancing dimensions.
- Interior-only, out-of-range, or overlapping base writes.
- Non-canonical step write geometry.
- Look-ahead, scaled, cross-axis, or slice-dependent state-history reads.

### Precedence fixtures

- Unsupported nested syntax plus missing input signature reports capability.
- Valid syntax plus shape failure plus source-pairing failure reports shape.

### Structural assertions

Assert directly:

- outer tensor signatures;
- persistent-state order;
- context axes and shapes;
- `advancingDims`;
- capture source and input slots;
- local block inputs and outputs;
- base and step write maps;
- affine coefficients and biases;
- `requiredInputs : RequiredBindings` (not "outer input bindings" — see §0's terminology note);
- `materializedNames`.

Execution-only tests are insufficient for residualization.

### Mutation checks

Break each independently and observe a named fixture failure:

- state classification;
- UID-to-dimension mapping;
- pinned-bias accumulation;
- state-capture versus result-slot resolution;
- capture `inputSlot`;
- scratch privacy;
- base overlap detection;
- step write bias;
- one causality row.

Restore each mutation and rerun the targeted suite.

### Gate

```bash
cd leanncd
lake build Eval.Plan.ScanCompileTest Eval.Plan.CompileTest
lake build LeanNCD
```

Complete an independent compiler review before Task 4.

## 9. Task 4 — prove named-boundary and legacy parity

### Outcome

Compiled scans behave correctly through the public named API and match `evalScheduled`.

### Files

- `test/Eval/Plan/AdapterTest.lean`
- `test/Eval/Plan/DifferentialTest.lean`
- adapter production files (`Adapter.lean`) only if a fixture exposes a real defect

### Execution matrix

For every admitted hand-written fixture:

1. compile with `prepareEvalPlan`;
2. execute with `runPreparedDense`;
3. execute the same scheduled source with `evalScheduled`;
4. compare every materialized persistent state exactly;
5. verify unrelated named inputs remain unchanged;
6. verify scratch and compiler-local names remain private;
7. compare warning order and payload.

Cover all Task 3 acceptance fixtures plus:

- warnings on successful execution;
- warnings preserved on binding failure;
- warnings preserved on execution failure;
- missing input at a scan capture;
- input shape mismatch;
- input storage mismatch;
- alpha-renaming of scan, state, scratch, and external names with identical UIDs and values;
- same axis name with different UIDs.

### Generated-corpus gate

Pin the independently re-derived 17-case split (§0):

- 9 accepted;
- 4 `unsupportedNonlin`;
- 4 `unsupportedAgg`.

All nine accepted cases must match `evalScheduled`. Rejected cases must not reach `runDensePlan`.

### Mutation checks

- Publish scratch; privacy must fail.
- Drop one state materialization; completeness must fail.
- Alter one outer input binding; named execution must fail.
- Reverse warning concatenation; warning parity must fail.
- Change an expected generated-case count; the corpus gate must fail.

Restore every mutation and rerun the suite.

### Gate

```bash
cd leanncd
lake build Eval.Plan.AdapterTest Eval.Plan.DifferentialTest
lake build LeanNCD
```

Complete an independent public-boundary review before Task 5.

## 10. Task 5 — generalize the independent oracle and close F4

### Outcome

Every admitted case passes a three-way differential gate, directly related documentation is
accurate, and the full branch is reviewed and green.

### Files

- `test/Eval/PropertyOracle/ScanUnroll.lean`
- `test/Eval/PropertyOracle/ScanOracle.lean`
- `LeanNCD/Eval/Plan/Prepared.lean`
- `LeanNCD/Eval/AGENTS.md`
- `docs/design/eval_ir.md`
- `papers/wave_f_scanplan_proposal.md`

### Independent unroller

Replace immediate-predecessor and trailing-axis assumptions with a bounded mechanical rewrite for
the admitted rectangular all-axis `+1` fragment:

1. Independently determine persistent states and each state's advancing dimensions.
2. Create zero-valued scan-free leaves for every bounded state coordinate.
3. Enumerate validated base regions into state leaves.
4. Preserve declared base order, although production admission requires disjoint regions.
5. Enumerate recurrence context tuples lexicographically.
6. Give every scratch producer a tuple-qualified name.
7. Redirect later same-step scratch reads to that tuple-qualified result.
8. Evaluate each state read's scan-axis affine indices at the current tuple.
9. Redirect in-range state reads to prior state leaves.
10. Redirect out-of-range state reads to zero leaves.
11. Preserve non-scan index expressions.
12. Replace scan-axis expressions in external reads with literals.
13. Emit tuple-qualified next-state leaves.
14. Evaluate the resulting scan-free `TLProgram`.

The unroller must not call any implementation listed in §4.8.

### Independent history reconstruction

Generalize `ScanOracle.lean` to reconstruct complete histories with `DenseTensor.ofFn` from
per-coordinate leaves:

- do not assume advancing dimensions trail the state shape;
- do not use scan-worker write helpers;
- support one or multiple scan axes;
- support arbitrary advancing-dimension positions and order.

### Required oracle coverage

- Deep constant look-back and zero padding.
- Coupled states.
- Scratch-heavy blocks.
- External reads.
- Contractions.
- Extent one.
- Multiple scan axes.
- Multiple disjoint base writes.

The oracle need not support source syntax rejected by production preflight.

### Three-way differential gate

Compare:

1. `prepareEvalPlan -> runPreparedDense`;
2. `evalScheduled`;
3. independent scan-free unrolling.

Run this comparison for:

- every admitted hand-written case; and
- all nine accepted generated cases.

Keep exact corpus counts and ensure every required feature family has an accepted fixture. Corpus
count alone is not sufficient coverage.

### Oracle mutation checks

- Break history-coordinate selection; deep-history parity must fail.
- Break scratch renaming; scratch-heavy parity must fail.
- Break state-dimension placement; non-trailing-axis parity must fail.
- Break base leaf placement; multi-base parity must fail.
- Break one compiled capture or write map; both independent paths must disagree with the plan.

Record every fail-before/pass-after observation in the F4 completion record.

### Documentation and discoverability

Update only directly related documentation:

- `Prepared.lean`: materializations are per persistent output, not per scheduled statement.
- `Eval/AGENTS.md`: describe admitted scan compilation, error ownership, and the independent oracle.
- `eval_ir.md`: update the prepared-plan boundary and current scan status.
- `wave_f_scanplan_proposal.md`: append the F4 completion record with exact tests, corpus counts,
  mutation observations, and remaining F5 work.

No new top-level production import is expected. Verify plain `import LeanNCD` reaches the completed
compiler API after all edits.

### Gate

```bash
cd leanncd
lake build Eval.PropertyOracle.ScanUnroll Eval.PropertyOracle.ScanOracle
lake build Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
lake build Eval.Plan.CompileTest Eval.Plan.AdapterTest Eval.Plan.DifferentialTest
lake build
```

Then:

1. run the final whole-branch review against the F4 contract — per `feedback-scale-process-to-task-
   risk`, do not compress this pass regardless of how clean Tasks 1-4 landed;
2. grep the ENTIRE `papers/jax_evalplan_architecture.md` and `papers/wave_f_scanplan_proposal.md` for
   every identifier this branch introduces or changes, not just the sections that name F4 — this
   repo has hit "the spec describes shipped work as unbuilt" three separate times;
3. adjudicate every finding;
4. rerun the affected targeted suite after each correction;
5. rerun the full `lake build`.

## 11. Definition of done

F4 is complete only when:

- both F3 prerequisite regressions are fixed and mutation-tested;
- scan-free compiler parity remains intact;
- every admitted source scan compiles to checked plan IR;
- every unsupported source fails in the correct typed phase;
- compiler-produced raw plans pass F3 checking;
- complete state histories cross the named boundary;
- scratch remains private;
- all admitted hand-written fixtures pass plan-versus-legacy parity;
- the generated corpus remains exactly 9 accepted and 8 typed capability rejections;
- every admitted case passes the independent three-way differential;
- all test-the-tester mutations have recorded fail-before/pass-after evidence;
- directly related documentation is accurate;
- plain `import LeanNCD` exposes the completed compiler API;
- targeted builds and the full `lake build` pass;
- final whole-branch review findings are resolved.

## 12. Risks and stop conditions

### 12.1 Expected high-effort areas

1. Independent unrolling is the largest test-side effort because it must resolve base regions,
   arbitrary state dimensions, affine history coordinates, zero padding, and scratch without
   borrowing either implementation under comparison.
2. Error precedence is easy to blur if F3 checker failures are relabeled; simultaneous-defect tests
   are mandatory.
3. Coupled-state snapshot resolution is subtle; a shared mutable `name -> latest slot` environment
   is incorrect for persistent states.
4. Task 3's scan-specific LHS admission (§8, Implementation A item 6) must not weaken Wave C's
   existing plain-statement preflight — `.iterAt`/`.iterNext` must remain rejected for genuinely
   plain statements; the admission rule applies only inside a `.scan` node's own base/recur lists.

### 12.2 Stop rather than broaden scope

- If one of the nine F0-accepted generated cases violates the normative F4 fragment, treat it as an
  F0 contract defect. Do not weaken F4 merely to preserve the count.
- If scheduling has discarded information required for typed specialization, report the missing
  invariant. Do not infer semantics from the scan's representative name.
- If an admitted source cannot agree under snapshot semantics, `evalScheduled`, and independent
  unrolling, stop and identify the semantic conflict. Do not fall back to the legacy worker.
- If F3 rejects compiler output after source validation, fix the compiler or a demonstrated F3
  defect. Do not convert the failure to a source capability error.
- Do not repair the JAX executor in F4.
- Do not copy the Mathlib olean tree unless the current cache is actually missing or corrupt.

## 13. Plan-authoring verification record

See §0 for the full session verification record. Summary:

- No Lean code blocks in this plan require snippet elaboration.
- The generated corpus split (17 total: 9/4/4) was independently re-derived from `ScanGen.lean`'s
  source this session, not merely cited.
- The full `lake build` (8,651 jobs) was re-run this session on the current `main` (`c59a1e1`).
- Both Task 1 defects were confirmed by direct code reading this session: the write-map rank gap
  (inherited from F3's own recorded, deliberately-deferred follow-up) and the capture-order-vs-
  `block.inputs`-order mismatch (found independently this session, not previously named in any
  memory or prior document).
- Task 2's extraction target and Task 3's `ScanStmt`/`LHSSlot`/`PlanCompileCause` structural claims
  were confirmed against the real files (`Compile.lean`, `Pipeline/Types.lean`, `Pipeline/
  Lowering.lean`, `EvalPlan.lean`).
- One terminology error in the source draft (`papers/f4_plan_thoughts.md`) was found and corrected
  throughout this plan: "`outerInputBindings`" does not exist; the real type is
  `PlanBindings.requiredInputs : RequiredBindings`.
- The base-pin substitution arithmetic example, the padded-read warning-parity claim, and the named-
  adapter `dp = [0,1,1,1]` claim were adopted from the source draft's own recorded verification
  without independent re-derivation this session (see §0's explicit note on this).
