# Slice: generalize the Plan-layer wiring loop

## 0. Session verification record (2026-08-21)

Extracted from the nonlinearity-in-scans plan (`2026-08-21-nonlinearity-in-scans.md`)'s own Task 1,
split out into its own slice per a design-review decision: Task 1 there was identified as fully
independent of `BlockStep`'s existence (it generalizes `checkPlanBlock`'s wiring loop while that
function still dispatches only one node kind, `AssignPlan` — exactly as it does today), and as the
plan's single highest-risk task (a refactor of already-shipped, heavily-tested checker code for a
soundness-relevant closed sum, needing two independent reviewers) with zero semantic dependency on
nonlinearity. Splitting it into its own slice, landed before the nonlinearity-in-scans plan starts,
lets it be reviewed purely on "is this refactor behavior-preserving" — a narrower, more mechanical
question than reviewing it alongside new capability — and removes the nonlinearity-in-scans plan's
costliest task from that slice's own critical path. All facts below were independently verified
against `main` at `14b9917` (2026-08-21, pushed) during that plan's own authoring session; re-stated
here, not re-derived, since nothing about this slice's own scope has changed since that verification.

**`checkPlanBlock`/`runDenseBlock`'s current bodies** (`LeanNCD/Eval/Plan/Block.lean`) — confirmed by
reading both in full. `checkPlanBlock`'s wiring loop (input validation, then per-assignment:
block-context check → destination-availability → source-availability via a direct per-term/factor
loop → `checkAssign` → mark produced) is structurally IDENTICAL to `checkPlan`'s own loop
(`EvalPlan.lean`), differing only in: (a) the context obligation (`blockContextMismatch` against
`block.contextShape`, vs. `checkPlan`'s `topLevelContextNotEmpty` against an implicit empty context),
(b) the error wrapper (`BlockError.wiring` vs. `PlanStepError.assign`), and (c) an extra
`outputs`-range/uniqueness check `checkPlan` has no analogue for (there is no "declared outputs"
concept at the outer-graph level — every outer slot must simply be produced). Every `PlanError`-shaped
failure at BOTH call sites (`slotOutOfRange`, `duplicateInputSlot`, `inputSlotsNotOrdered`,
`inputSlotOverwritten`, `duplicateDestination`, `invalidForwardRead`, `missingProduction`, all via
`nodeError` where per-node) is embedded through exactly one wrapper function per call site
(`.assign`/`.wiring`) — confirmed by reading every throw site in both functions side by side.

**`checkPlan`'s current body, especially the `.assign`-vs-generic asymmetry** — confirmed: `checkPlan`'s
three match blocks (context-check, destination loop, source-check) each have a `.assign` arm using a
direct per-term/per-factor loop (preserving `ti`/`fi` locators for `invalidForwardRead`) and a
`.scan _ | .pointwise _ | .axiswise _` arm using the generic `PlanStep.sourceSlots`/`destinationSlots`
accessors with placeholder locators `0 0`. `runDensePlan`'s dispatch match already has all four
`PlanStep` arms (Thread 4 added `.pointwise`/`.axiswise`) — this task does not touch `runDensePlan`/
`runDenseBlock` at all; only the CHECKERS (`checkPlan`/`checkPlanBlock`) are refactored. The runners'
own dispatch loops are separate code, already correct, and out of this slice's scope.

**`.claude/skills/slice-plan/check-snippet.sh` ran clean against `WiringNode`/`checkStepGraph`,
instantiated TWICE independently**: once with `E := BlockError`, `C := CheckedAssignPlan` against the
real `checkAssign` (confirming it serves `checkPlanBlock` as it exists TODAY — one node kind, not the
future 3-arm `BlockStep` shape a later slice adds), and once with `E := PlanStepError`,
`C := CheckedPlanStepEvidence` against the real `checkPointwise`/`RawPointwisePlan` (confirming the
SAME generic shape also serves `checkPlan`'s already-existing 4-arm dispatch, including a
`.assign → .pointwise` chain accepted correctly and a shape-mismatched `.pointwise` rejected with
`.nonlin 1 _`, never mis-wrapped through `.assign`). Both fixtures also independently confirmed the
`sourceSlot == destinationSlot` self-aliasing argument transfers: a never-produced self-aliasing
destination is rejected via `invalidForwardRead` (source-check runs against the SAME `available`
snapshot the destination-check just examined, before this node's own destination is marked produced).

**Existing fixture inventory for the mutation/error-matrix technique** (the acceptance criterion —
see Task 1's own Mutation/error-matrix section): `test/Eval/Plan/BlockTest.lean` (7 fixtures: accept,
`duplicateOutputSlot`, `blockContextMismatch`, `invalidForwardRead`, `arityMismatch`,
`missingProduction`, the `CheckedPlanBlock` privacy check), plus the analogous outer-level fixtures in
`test/Eval/Plan/GraphCheckTest.lean`/`GraphDenseTest.lean`/`EvalPlanTest.lean`.

## 1. Purpose

Pay down a duplication this repo's own history has flagged twice as deferred (Wave F F2's own
completion record: "F3 will be tempted to add a third copy of one or both loops for the scan graph —
this is the moment to consider factoring `Check.lean`/`Dense.lean` into shared parameterized helpers
instead"): `checkPlanBlock`'s wiring loop is a near-copy of `checkPlan`'s own loop, not a shared
function. Generalize both onto one shared implementation, `checkStepGraph`, with **zero behavior
change to either** — this slice adds no new capability, no new node kind, and no new test fixture; it
is a pure refactor whose entire acceptance criterion is "every existing fixture asserts the identical
outcome before and after."

This slice exists specifically so a later slice (nonlinearity-in-scans, already planned at
`2026-08-21-nonlinearity-in-scans.md`, currently blocked on this one landing first) can extend
`checkPlanBlock`'s dispatch to a new 3-arm `BlockStep` sum by adding cases to an already-generalized
loop, rather than by hand-writing a third near-copy or by co-reviewing "is the refactor safe" and "does
the new capability work" in the same branch.

## 2. Scope

### 2.1 In scope

- `LeanNCD/Eval/Plan/Block.lean` gains `WiringNode`/`checkStepGraph` (§3 below).
- `checkPlanBlock` (`Block.lean`) is rewritten to build `WiringNode`s per `AssignPlan` (still the
  only node kind `RawPlanBlock.assignments` holds — this slice does not rename the field or touch
  its element type) and delegate the wiring loop to `checkStepGraph`.
- `checkPlan` (`EvalPlan.lean`) is rewritten the same way, over its existing 4 `PlanStep` arms.

### 2.2 Explicitly out of scope

- **`BlockStep`, the rename of `RawPlanBlock.assignments`, and any new node kind** — the next slice's
  job entirely. `checkPlanBlock` still dispatches exactly one node kind after this slice lands.
- **`runDensePlan`/`runDenseBlock`** — their own dispatch loops are separate from the checker's wiring
  loop and are not touched by this slice.
- **Any new test fixture** — the existing fixtures ARE the acceptance test, via the mutation/
  error-matrix technique. Adding new ones would test capability this slice doesn't add.
- **Anything about nonlinearity, scans-as-a-feature, or `compileScan`** — entirely the next slice's
  concern; this slice's diff touches only `Block.lean` and `EvalPlan.lean`.

### Global constraints (exact values)

- Every fixture in `test/Eval/Plan/BlockTest.lean`, `GraphCheckTest.lean`, `GraphDenseTest.lean`, and
  `EvalPlanTest.lean` must assert the IDENTICAL pass/fail outcome and, for rejections, the IDENTICAL
  error constructor, before and after this slice's refactor. Any difference is this slice's own bug,
  not a fixture to update.
- `runDensePlan`/`runDenseBlock`: zero changes.
- `RawPlanBlock`/`CheckedPlanBlock`/`PlanStep`/`CheckedPlanStepEvidence`: zero changes to their own
  type definitions — only the checker FUNCTIONS that consume them are refactored.

## 3. Architecture: `WiringNode`/`checkStepGraph`

`checkPlan`'s and `checkPlanBlock`'s wiring loops differ only in: which `PlanError`-shaped failures
get wrapped by which final constructor (`.assign`/`.wiring`), the context obligation (empty vs.
`block.contextShape`), and whether a per-node source-check needs `.assign`'s own rich per-term/
per-factor loop or the generic `sourceSlots`-based one. Every genuinely shared `PlanError` value (slot
range, input ordering, overwrite, duplicate destination, missing production) is embedded through
exactly ONE caller-supplied function, `liftWiring : PlanError → E`.

```lean
structure WiringNode (E C : Type) where
  contextCheck     : Except E Unit
  destinationSlots : Array TensorSlot
  sourceCheck      : Array Bool → Except E Unit
  localCheck       : Except E C

def checkStepGraph {E C : Type} (n : Nat) (inputs : Array TensorSlot) (liftWiring : PlanError → E)
    (nodes : Array (WiringNode E C)) : Except E (Array C) := do
  for h : i in [0 : inputs.size] do
    let s := inputs[i]
    unless s < n do throw (liftWiring (.slotOutOfRange s n))
    if h2 : i + 1 < inputs.size then
      let s2 := inputs[i + 1]
      if s == s2 then throw (liftWiring (.duplicateInputSlot s))
      else if s2 < s then throw (liftWiring (.inputSlotsNotOrdered i))
  let mut available : Array Bool := Array.replicate n false
  let mut producedBy : Array (Option Nat) := Array.replicate n none
  for s in inputs do available := available.set! s true
  let mut checkedNodes : Array C := #[]
  for h : ni in [0 : nodes.size] do
    let node := nodes[ni]
    node.contextCheck
    for dest in node.destinationSlots do
      match available[dest]? with
      | none => throw (liftWiring (.nodeError ni (.slotOutOfRange dest n)))
      | some isAvail =>
          if isAvail then
            match producedBy[dest]?.join with
            | none => throw (liftWiring (.inputSlotOverwritten dest ni))
            | some firstNode => throw (liftWiring (.duplicateDestination dest firstNode ni))
    node.sourceCheck available
    let c ← node.localCheck
    checkedNodes := checkedNodes.push c
    for dest in node.destinationSlots do
      available := available.set! dest true
      producedBy := producedBy.set! dest (some ni)
  for h : i in [0 : n] do
    unless available[i]! do throw (liftWiring (.missingProduction i))
  return checkedNodes
```

`WiringNode`'s four fields are genuine functions/values built by the caller per node, called by the
loop at the exact point in the per-node sequence (context → destination → source → local-check)
`checkPlan`/`checkPlanBlock` already use today — this preserves validation order and error precedence
by construction, not by re-deriving it, and (since Lean's `Except` values carry no side effects) a
node past the first failure is simply never reached by the `for` loop, exactly matching today's
short-circuiting.

**Why this is the right signature, not merely a plausible one**: verified via `check-snippet.sh`
TWICE, independently — once instantiated with `E := BlockError`, `C := CheckedAssignPlan` against the
real `checkAssign` (confirming it serves `checkPlanBlock` as it exists today), and once with
`E := PlanStepError`, `C := CheckedPlanStepEvidence` against the real `checkPointwise`/
`RawPointwisePlan` (confirming the SAME generic shape also serves `checkPlan`'s full 4-arm dispatch).
Both fixtures also independently confirmed the `sourceSlot == destinationSlot` self-aliasing argument
transfers: a never-produced self-aliasing destination is rejected via `invalidForwardRead` (source-
check runs against the SAME `available` snapshot the destination-check just examined, before this
node's own destination is marked produced).

`checkStepGraph`/`WiringNode` live in `Block.lean` (visible to `EvalPlan.lean` transitively via
`Scan.lean`'s own import of `Block.lean` — confirmed by re-reading the import chain:
`EvalPlan.lean → Scan.lean → Block.lean`; no new import needed anywhere).

## 4. Task graph and review weight

One task. The reviewer test doesn't support splitting it: `checkPlan` and `checkPlanBlock` share the
one `WiringNode`/`checkStepGraph` definition, so a reviewer needs both call sites in view at once to
confirm the shared function is genuinely correct for both, not just one — splitting them would force
either an incomplete first review or a second review that re-derives the same context.

| Task | Outcome | Independent review reason | Risk / process weight |
|---|---|---|---|
| 1 | `WiringNode`/`checkStepGraph` in `Block.lean`; `checkPlan`/`checkPlanBlock` refactored onto it, behavior UNCHANGED | Refactor of already-shipped, heavily-tested checker code for a soundness-relevant closed sum — a diff showing only the refactor cannot show whether an existing behavior silently changed | **High, two independent reviewers.** Zero new fixtures — the mutation/error-matrix technique is the entire acceptance criterion. |

## Task 1: generalize the wiring loop

### Outcome

`Block.lean` gains `WiringNode`/`checkStepGraph`; `checkPlanBlock` (`Block.lean`) and `checkPlan`
(`EvalPlan.lean`) are both refactored to build `WiringNode`s and delegate to it. Every existing
`.assign`/`.scan` behavior is byte-for-byte unchanged — no new node kind exists, and `RawPlanBlock`
still holds `assignments : Array AssignPlan` exactly as before this task.

### Files

- `LeanNCD/Eval/Plan/Block.lean` (`WiringNode`, `checkStepGraph`; `checkPlanBlock` rewritten)
- `LeanNCD/Eval/Plan/EvalPlan.lean` (`checkPlan` rewritten)

### Implementation

1. Add `WiringNode`/`checkStepGraph` to `Block.lean` exactly as verified in §3.
2. Rewrite `checkPlanBlock`'s per-assignment loop: build one `WiringNode BlockError CheckedAssignPlan`
   per `AssignPlan` in `block.assignments`, with `contextCheck := unless step.contextShape ==
   block.contextShape do throw (.blockContextMismatch ni block.contextShape step.contextShape)`,
   `destinationSlots := #[step.destinationSlot]`, `sourceCheck` the existing rich per-term/per-factor
   loop (unchanged, just wrapped as a closure), `localCheck := match checkAssign block.tensorSigs step
   with .error e => throw (.wiring (.nodeError ni e)) | .ok c => pure c`. Call `checkStepGraph
   block.tensorSigs.size block.inputs BlockError.wiring nodes`, keeping the pre-existing
   `outputs`-range/duplicate check as a separate step before/after the loop call, unchanged.
3. Rewrite `checkPlan`'s three match blocks the same way, building one `WiringNode PlanStepError
   CheckedPlanStepEvidence` per `PlanStep`, with the SAME `.assign`-rich/`.scan`-generic source-check
   split it already has, and `localCheck` matching each of the 4 existing arms' existing dispatch to
   `checkAssign`/`checkScanPlan`/`checkPointwise`/`checkAxiswise`. Call `checkStepGraph
   raw.tensorSigs.size raw.inputSlots PlanStepError.assign nodes`.
4. `runDensePlan`/`runDenseBlock` are UNCHANGED by this task (their own dispatch loops are separate
   from the checker's wiring loop and untouched here).

### Mutation/error-matrix technique

Before the refactor, run `lake build Eval.Plan.BlockTest Eval.Plan.GraphCheckTest
Eval.Plan.GraphDenseTest Eval.Plan.EvalPlanTest` and record the pass/fail outcome and, for each
rejection fixture, the EXACT error constructor observed (already pinned by each fixture's own
`#guard`/`run_cmd` assertion — no new capture needed beyond re-reading each file's existing
assertions). After the refactor, re-run the identical command and confirm every fixture still asserts
the SAME constructor. Do not add new fixtures for this task; the existing ones are the matrix.

### Gate

```bash
cd leanncd
lake build Eval.Plan.BlockTest Eval.Plan.GraphCheckTest Eval.Plan.GraphDenseTest \
  Eval.Plan.EvalPlanTest Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
lake build Tests
lake build LeanNCD
```

**Two independent reviewers** — refactor of a soundness-relevant closed sum's checker, per this
repo's own standing rule; a diff showing only the new `WiringNode`-building code cannot show whether
an existing arm's behavior silently changed.

## 5. Definition of done

- [ ] `WiringNode`/`checkStepGraph` exist in `Block.lean`, exactly as verified in §3.
- [ ] `checkPlanBlock` and `checkPlan` both delegate to `checkStepGraph` — no hand-written wiring loop
      remains in either.
- [ ] `runDensePlan`/`runDenseBlock` are byte-for-byte unchanged.
- [ ] Every fixture in `BlockTest.lean`/`GraphCheckTest.lean`/`GraphDenseTest.lean`/`EvalPlanTest.lean`
      asserts the identical outcome (and, for rejections, the identical error constructor) before and
      after — confirmed via the mutation/error-matrix technique, not assumed.
- [ ] `lake build` (full suite) green.
- [ ] Two independent reviewers signed off, per this repo's own standing rule for a refactor of a
      soundness-relevant closed sum.
- [ ] Completion record states plainly that this slice adds no new capability and exists solely to
      unblock the nonlinearity-in-scans slice's own Task 1 (formerly its Task 2) with a lower-risk
      starting point.

## 6. Risks and stop conditions

### 6.1 Expected high-effort area

The entire task IS the high-effort area — there is only one task, and its risk is inherent to any
refactor of a soundness-relevant closed sum's checker: a diff that only shows the new generic loop
cannot itself prove an existing arm's behavior is preserved. This is why the acceptance criterion is
empirical (the mutation/error-matrix technique) rather than structural (a diff read).

### 6.2 Stop rather than broaden scope

- If refactoring `checkPlanBlock`/`checkPlan` reveals a THIRD near-copy of this wiring-loop shape
  elsewhere in the codebase not identified in this plan's §0 — stop and report; do not fold a third
  call site into this slice without re-scoping, since this slice's own review weight was sized for
  exactly two call sites.
- If any existing fixture's outcome changes as a result of this refactor — that is a genuine defect
  in this slice's own implementation, not a fixture to update. Do not "fix" a fixture to match new
  behavior; fix the refactor to match the old behavior.

## 7. Plan-authoring verification record

- `WiringNode`/`checkStepGraph` was compiled via `check-snippet.sh` twice, independently, against the
  real `BlockError`/`CheckedAssignPlan`/`checkAssign` types and the real `PlanStepError`/
  `CheckedPlanStepEvidence`/`checkPointwise`/`RawPointwisePlan` types — both green, confirming one
  signature genuinely serves both call sites as they exist today, not a plausible-looking guess.
- Every file path this plan names was verified present in the repo during the nonlinearity-in-scans
  plan's own authoring session (2026-08-21, against `main` at `14b9917`); re-verify at execution time
  if this slice is not executed immediately, since it depends on nothing else moving in the meantime
  (this slice touches no file any other in-flight work is also touching).
- No `File.lean:NNN` line numbers appear in any task's Implementation/Files/Gate text above, or in the
  completion-record instruction in §5 — every locator is by function/constructor name.
