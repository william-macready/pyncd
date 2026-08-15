# Wave F, F3: Checked Scan Graph Vertical Slice

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `RawScanPlan`, `PlanStep` (the closed `assign | scan` sum), private checked scan
evidence (`CheckedScanPlan`, `checkScanPlan`), the causality certificate, the four-phase Dense scan
worker (`runDenseScan`), and outer-graph integration (`RawEvalPlan.steps : Array PlanStep`,
`checkPlan`/`runDensePlan` handling both step kinds) as one executable vertical slice
(`papers/wave_f_scanplan_proposal.md` §13's F3 entry). This is F3 in the Wave F sequence — F0
(executable scan contract), F1 (contextual local kernel), and F2 (checked plan-block) are landed;
see Status below. **Do not** teach the source compiler to admit `.scan` — that is F4. The source
compiler still rejects every scan at the end of this slice; F3 proves the language and worker via
hand-built checked plans only.

**Status.** F0 (2026-08-08), F1 (2026-08-08), and F2 (2026-08-14, `Eval.Plan.Block`:
`RawPlanBlock`/`BlockError`/`CheckedPlanBlock`/`checkPlanBlock`/`runDenseBlock`) are landed —
verified by re-reading `LeanNCD/Eval/Plan/{Types,Kernel,Check,Graph,Dense,Block,Error,
Coordinates}.lean` directly before drafting this plan, not assumed from the proposal's prose.
`papers/jax_evalplan_architecture.md` §7.6 (thread 3) names "F2-F4: checked block and scan layers"
as the in-progress work this slice continues.

## Architecture — the discovered constraint and its resolution

**The naive approach does not compile.** The proposal describes `RawEvalPlan.steps` becoming
`Array PlanStep` where `PlanStep.scan : RawScanPlan → PlanStep` and `RawScanPlan` embeds
`RawPlanBlock` (F2's block type). But `RawPlanBlock` today lives in `Block.lean`, which imports
`Dense.lean → Check.lean → {Graph.lean, Error.lean}` — and `Graph.lean` is where `RawEvalPlan` is
defined. Making `Graph.lean` reference `RawScanPlan` (which needs `RawPlanBlock`, from `Block.lean`,
which transitively imports `Graph.lean` already) is a direct circular import. This is not a naming
or style problem; Lean's module system rejects it outright.

The same shape of conflict recurs one layer up: `checkPlan` (the outer-graph checker, defined in
`Check.lean` today) must dispatch `.scan` steps to `checkScanPlan` to build one `CheckedEvalPlan`.
But `checkScanPlan` needs `checkPlanBlock` (`Block.lean`, needs `checkAssign` from `Check.lean`) —
so `Check.lean` cannot import whatever module defines `checkScanPlan` without a second cycle.
`runDensePlan` (`Dense.lean`) has the identical problem with `runDenseScan`.

**Resolution, verified against the real environment (not asserted):** the raw *types*
(`RawPlanBlock`, `RawScanPlan`, `StateSlot`, `BlockCapture`, `StateWriteMap`, `PlanStep`, and the
four closed scan policy tags) need nothing beyond `Kernel.lean` (`AssignPlan`, `TensorSlot`,
`TensorSignature`) — they do not need `checkAssign`, `runDenseAssignAt`, `PlanError`, or anything
else downstream. Only the *checkers and workers* (`checkPlanBlock`, `runDenseBlock`, `checkScanPlan`,
`runDenseScan`, `checkPlan`, `runDensePlan`) need those. Confirmed by compiling a standalone file
containing exactly these type definitions against `import LeanNCD.Eval.Plan.Kernel` alone — no
`Block`, `Check`, `Dense`, `Error`, or `Graph` import — via `check-snippet.sh`; it compiled clean.

This gives the new import order (unchanged files not listed):

```text
Types.lean → Kernel.lean → RawStep.lean (NEW: types only) → Coordinates.lean
  → Error.lean (MODIFIED: PlanError.versionNotAdmitted removed; Task 1 also adds one temporary
      `scanStepNotYetSupported` constructor per its own ledger ruling, deleted again in Task 4)
  → Graph.lean (MODIFIED: imports RawStep, not Kernel directly;
      RawEvalPlan.steps : Array PlanStep; version field removed)
  → Check.lean (MODIFIED: loses checkPlan/CheckedEvalPlan/admittedVersion/versionNotAdmitted —
      keeps only checkAssign/CheckedAssignPlan, the C2 local-kernel layer)
  → Dense.lean (MODIFIED: loses runDensePlan — keeps runDenseAssignAt/runDenseAssign)
  → Block.lean (MODIFIED: RawPlanBlock struct removed — now inherited from RawStep —
      BlockError/CheckedPlanBlock/checkPlanBlock/runDenseBlock unchanged)
  → Scan.lean (NEW: ScanPlanError, CheckedScanPlan, checkScanPlan, CausalityCertificate,
      runDenseScan, and the write-geometry/causality/rank-unrank helpers)
  → EvalPlan.lean (NEW: the RELOCATED checkPlan, CheckedEvalPlan, runDensePlan — now the only
      module able to see both checkAssign/runDenseAssignAt AND checkScanPlan/runDenseScan)
```

`Prepared.lean`, `Compile.lean`, `Adapter.lean`, and `Executable.lean` — every existing consumer of
`checkPlan`/`CheckedEvalPlan`/`runDensePlan` — update their imports from `Check`/`Dense` to
`EvalPlan` accordingly. This is a real, non-additive restructuring; F2's "additive only" constraint
does not carry over to F3 (F2's own plan said as much: "F3 is what gives it a caller").

**Why this is not overreach:** every one of these moves is required by the acyclic-import
constraint above, not chosen for taste. `checkAssign`/`CheckedAssignPlan`'s own module doc already
frames `checkPlan` as a separate concern bolted onto the same file ("Graph availability and
production order are deliberately NOT checked here... `checkPlan` (C3) adds them") — splitting them
apart now is a natural consequence of that documented separation, not an arbitrary reshuffle.

**`CheckedEvalPlan.checkedNodes`'s element type changes** from `Array CheckedAssignPlan` to
`Array CheckedPlanStepEvidence` (a new two-case sum: `.assign (c : CheckedAssignPlan) | .scan
(c : CheckedScanPlan)`, defined in `EvalPlan.lean` alongside the relocated `checkPlan`). Every
production consumer of `checkedNodes` was re-checked before writing this plan:
`Executable.lean` (JAX kernel-lowering scaffolding) only reads `raw.steps.size` (a `Nat`) — verified
by grep, not assumed — so it is unaffected. **`experiments/jax_bridge/{EvalPlanCodegen,
EvalPlanAffineSmoke,EvalPlanAffineCorpus}.lean` (the `JaxExperiment` lake target) directly iterate
`checkedNodes` assuming every element is a bare `CheckedAssignPlan`** (`cn.plan`,
`plan.plan.checkedNodes.flatMap`, etc.) and **will fail to compile once this slice lands.**
`JaxExperiment` is explicitly excluded from `lakefile.toml`'s `defaultTargets = ["LeanNCD",
"Tests"]` (confirmed by reading `lakefile.toml`), so this does not fail `lake build` or gate this
slice — Wave F's own architecture doc treats JAX/scan lowering as a separate, unscheduled thread
(thread 5 vs. thread 3 in `papers/jax_evalplan_architecture.md` §7.6). Record this as a known,
deliberate consequence in the F3 completion record (Task 5); do not fix it in this slice.

## Global Constraints

- **No source compiler changes.** `prepareEvalPlan`'s scan-specialization phase, capability
  preflight, and `evalScheduled` are untouched. Every checked plan in this slice's fixtures is
  hand-built `RawScanPlan`/`RawPlanBlock` data, not compiled from a `.scan` source node. F4 owns
  source admission.
- **Reuse the F2 block layer unchanged.** `checkScanPlan` composes `checkPlanBlock` (Law 2: compose
  the layer below, don't duplicate it); `runDenseScan` composes `runDenseBlock`. Neither
  reimplements local wiring or local execution.
- **Private constructor pattern.** `CheckedScanPlan` follows `CheckedAssignPlan`/`CheckedPlanBlock`'s
  `private mk ::` discipline exactly.
- **Closed error families, indices carry locators.** `ScanPlanError` has one constructor per checker
  branch (proposal §7.5); no `unsupported : String` escape hatch. Every write/capture/state failure
  carries the index needed to locate it without re-deriving it.
- **Fixture values are observed, not hand-derived.** Every hand-computed worker fixture in Task 3
  reuses a value this plan already obtained by running the real evaluator (F0's `evalScan` fixtures
  in `test/Eval/ScanTest.lean`, or a fresh `evalScan` run performed while drafting this plan and
  shown inline below) — none are asserted from arithmetic alone.
- **Every Lean block in this plan has been compiled** against the real `leanncd` environment via
  `.claude/skills/slice-plan/check-snippet.sh` before being written here, including the full
  `checkScanPlan` structural checker (accept + 2 reject mutations), the causality-integrated checker
  (accept + Jacobi-style reject), and the complete `runDenseScan` worker (verified to reproduce the
  legacy evaluator's exact `[1, 11, 31]` linear-scan output). The one exception, disclosed rather
  than silently assumed: Task 4's multi-file import restructuring cannot be simulated by
  `check-snippet.sh` (which compiles one file against the *existing* built environment, not a
  hypothetical restructured one) — its core claim (raw scan/step types need only `Kernel.lean`) *is*
  independently verified this way; the remaining cross-file wiring is specified precisely but must
  be confirmed with a real `lake build` during Task 4's own execution, per that task's own review
  gate.
- **Re-verify after assembly.** Any reformatting of the snippets below during transcription into
  real files needs `check-snippet.sh` re-run on the post-edit form, per the `slice-plan` skill's own
  rule — a purely cosmetic edit to a `do`-block can silently break parsing.

---

## File Structure

**Create:**
- `leanncd/LeanNCD/Eval/Plan/RawStep.lean` — the four scan policy tags, `StateSlot`,
  `CaptureSource`, `BlockCapture`, `StateWriteMap`, `RawPlanBlock` (relocated from `Block.lean`),
  `RawScanPlan`, `PlanStep`
- `leanncd/LeanNCD/Eval/Plan/Scan.lean` — `WriteRowKind` and its classifier/validators,
  `ScanPlanError`, `CheckedScanPlan`, `checkCaptures`, `checkWrites`, `checkScanPlan`,
  `CausalityCertificate`, `causalAdvancingRow`, `stateReadCausal`, `mixedRadixRank`/`Unrank`/
  `DomainSize`, `runDenseScan`
- `leanncd/LeanNCD/Eval/Plan/EvalPlan.lean` — relocated `checkPlan`, `CheckedEvalPlan`,
  `CheckedPlanStepEvidence`, `runDensePlan` (all previously in `Check.lean`/`Dense.lean`)
- `leanncd/test/Eval/Plan/ScanTest.lean` — scan checker and worker fixtures/mutations
  (named to avoid colliding with the legacy `test/Eval/ScanTest.lean`)
- `leanncd/test/Eval/Plan/EvalPlanTest.lean` — outer-graph multi-output fixtures/mutations for the
  relocated `checkPlan`/`runDensePlan`

**Modify:**
- `leanncd/LeanNCD/Eval/Plan/Graph.lean` — import `RawStep` instead of `Kernel`; `steps : Array
  PlanStep`; remove `version`/rename nothing else
- `leanncd/LeanNCD/Eval/Plan/Check.lean` — remove `checkPlan`, `CheckedEvalPlan`, `admittedVersion`
- `leanncd/LeanNCD/Eval/Plan/Dense.lean` — remove `runDensePlan`
- `leanncd/LeanNCD/Eval/Plan/Block.lean` — remove the `RawPlanBlock` structure definition (now
  inherited); everything else unchanged
- `leanncd/LeanNCD/Eval/Plan/Error.lean` — remove `PlanError.versionNotAdmitted`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean` — **the `steps :=`/`version :=` part of this edit landed
  in Task 1** (ledger ruling: a 2-token, zero-logic-change fix pulled forward to keep `lake build`
  green through Tasks 1-3 — `steps := stepsAcc` → `steps := stepsAcc.map .assign`, `version :=
  admittedVersion,` deleted). Task 4 only needs its `checkPlan` call site (and whatever
  `liftPlanError`/error-mapping helper wraps it) to resolve via the new `EvalPlan` import and the
  `PlanStepError` type instead of bare `PlanError` — check `liftPlanError`'s current shape directly
  before editing it, this plan does not assume it sight-unseen.
- `leanncd/LeanNCD/Eval/Plan/Prepared.lean`, `Adapter.lean` — import `EvalPlan` wherever they
  currently rely on `Check`/`Dense` for `checkPlan`/`CheckedEvalPlan`/`runDensePlan`
- `leanncd/test/Eval/Plan/{GraphCheckTest,GraphDenseTest,ExecutableTest,KernelCheckTest}.lean` — the
  21 `RawEvalPlan` literal-construction sites (`version := admittedVersion, ..., steps := #[...]`)
  drop `version :=` and wrap each step in `.assign`
- `leanncd/lakefile.toml` — add `"Eval.Plan.ScanTest"`, `"Eval.Plan.EvalPlanTest"` to `Tests`' globs
- `leanncd/LeanNCD.lean` — add `import LeanNCD.Eval.Plan.RawStep`, `.Scan`, `.EvalPlan`
  (discoverability: these are core Wave F production code, like `Block.lean`, not experiments)
- `leanncd/LeanNCD/Eval/AGENTS.md` — update the `Plan/` file table and count
- `papers/wave_f_scanplan_proposal.md` — append an "F3 completion record" under §13

---

## Task 1: `RawStep.lean` types, write-geometry recognizer, and `checkScanPlan`'s structural half

Add the relocated/new raw types, the write-geometry classifier and disjointness recognizer
(compiled and numerically verified below against F0's own observed fixtures), and `checkScanPlan`
covering every §7.3 structural/geometry/capture obligation *except* causality (Task 2).

### `RawStep.lean`

```lean
-- leanncd/LeanNCD/Eval/Plan/RawStep.lean
import LeanNCD.Eval.Plan.Kernel

namespace LeanNCD.Eval.Plan

/-- Which values a scan actually returns. Wave F admits exactly one policy. -/
inductive MaterializationPolicy
  | completeHistory
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Coordinate enumeration order over a scan's recurrence domain. Wave F admits exactly one. -/
inductive ScanIterationOrder
  | axisZeroFastest
  deriving DecidableEq, BEq, Repr, Inhabited

/-- How complete state histories are initialized before base writes apply. Wave F admits exactly
    one. -/
inductive ScanBoundaryPolicy
  | zeroThenBaseOverlay
  deriving DecidableEq, BEq, Repr, Inhabited

/-- What a step block's state captures observe. Wave F admits exactly one. -/
inductive ScanSnapshotPolicy
  | immutablePreStep
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One persistent scan state: the outer graph slot that receives its complete history, which of
    its own tensor dimensions are advancing (in scan-context order, so `advancingDims[i]` is the
    state dimension driven by context position `i`), and how it materializes. -/
structure StateSlot where
  destSlot        : TensorSlot
  advancingDims   : Array Nat
  materialization : MaterializationPolicy
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Where a block input's value comes from: an already-available outer graph slot, or a snapshot
    of one persistent state (by index into `RawScanPlan.states`). -/
inductive CaptureSource
  | external (outerSlot : TensorSlot)
  | state    (stateIndex : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One block-input binding. -/
structure BlockCapture where
  inputSlot : TensorSlot
  source    : CaptureSource
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One state write: a block output slot's value, placed into complete state `stateIndex` through
    `map`. `map`'s domain is `context ++ outputSlice` (empty context for a base write); its
    codomain is the complete state's own rank, one row per state dimension. Reuses `AffineMap`
    unchanged rather than inventing a second placement-map type. -/
structure StateWriteMap where
  outputSlot : TensorSlot
  stateIndex : Nat
  map        : AffineMap
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A local, acyclic, context-parameterized dataflow graph — the base block or the step block of a
    scan (proposal §6.2). Relocated from `Block.lean` (F2): this type only ever needed
    `Kernel.lean` (`AssignPlan`, `TensorSlot`, `TensorSignature`) — `checkPlanBlock`/`runDenseBlock`
    are what need `checkAssign`/`runDenseAssignAt`, not this definition. Moving it here (instead of
    leaving it in `Block.lean`) is what lets `RawEvalPlan` (`Graph.lean`) reference `RawScanPlan`
    without a circular import — see this plan's Architecture section for the full argument. -/
structure RawPlanBlock where
  contextShape : Array Nat
  tensorSigs   : Array TensorSignature
  inputs       : Array TensorSlot
  assignments  : Array AssignPlan
  outputs      : Array TensorSlot
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One unchecked scan node: explicit states, base/step blocks, their captures and write maps, and
    the closed policies every checked scan admits in this version. -/
structure RawScanPlan where
  states         : Array StateSlot
  baseBlock      : RawPlanBlock
  baseCaptures   : Array BlockCapture
  baseWrites     : Array StateWriteMap
  stepBlock      : RawPlanBlock
  stepCaptures   : Array BlockCapture
  stepWrites     : Array StateWriteMap
  historyExtents : Array Nat
  iterationOrder : ScanIterationOrder
  boundaryPolicy : ScanBoundaryPolicy
  snapshotPolicy : ScanSnapshotPolicy
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One outer graph node: an ordinary local assignment, or a scan. `RawEvalPlan.steps` becomes
    `Array PlanStep` in F3 (was `Array AssignPlan`). -/
inductive PlanStep
  | assign (a : AssignPlan)
  | scan   (s : RawScanPlan)
  deriving DecidableEq, BEq, Repr, Inhabited

end LeanNCD.Eval.Plan
```

**Verified:** compiled standalone against `import LeanNCD.Eval.Plan.Kernel` only (no `Block`,
`Check`, `Dense`, `Error`, `Graph`) via `check-snippet.sh` — confirms the acyclic-import resolution
above actually holds, not just on paper.

**`Block.lean` change:** delete the `RawPlanBlock` structure (lines 24-30 of the current file) and
its doc comment; everything else (`BlockError`, `firstDuplicateSlot`, `CheckedPlanBlock`,
`checkPlanBlock`, `runDenseBlock`) is unchanged — they already only used `RawPlanBlock`'s fields,
never redefined it.

### Write-geometry recognizer (`Scan.lean`, part 1)

```lean
-- leanncd/LeanNCD/Eval/Plan/Scan.lean (part 1 of several in this plan)
import LeanNCD.Eval.Plan.Block

namespace LeanNCD.Eval.Plan

/-- One recognized shape for a write-map row: pinned to a literal, an order-preserving projection
    of the block's own output slice, or bound to `context[p] + 1` (step writes only). Anything else
    is an unrecognized affine geometry and must be rejected. -/
inductive WriteRowKind
  | pinned    (lit : Int)
  | free      (outputPos : Nat)
  | advancing (contextPos : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Classify one complete-state dimension's write row. `contextWidth` is `0` for a base write and
    `advancingDims.size` for a step write — the same `AffineMap` shape serves both, distinguished
    only by how many leading domain positions are scan-context rather than output-slice. -/
def classifyWriteRow (contextWidth : Nat) (coeffRow : Array Int) (bias : Int) : Option WriteRowKind :=
  let nz := coeffRow.toList.zipIdx.filter (fun (c, _) => c != 0)
  match nz with
  | [] => some (.pinned bias)
  | [(c, p)] =>
      if c == 1 && p < contextWidth && bias == 1 then some (.advancing p)
      else if c == 1 && p ≥ contextWidth && bias == 0 then some (.free (p - contextWidth))
      else none
  | _ => none

/-- Row classifications for one write against one state, given the complete state's rank and the
    write's declared context width (`0` for base, `advancingDims.size` for step). -/
def writeRowKinds (stateRank contextWidth : Nat) (w : StateWriteMap) : Array (Option WriteRowKind) :=
  (Array.range stateRank).map (fun d =>
    classifyWriteRow contextWidth (w.map.coeffs.getD d #[]) (w.map.bias.getD d 0))

/-- A base write's rows must all be recognized, its free positions must cover `0 .. outputShape)`
    in increasing order (order-preserving onto the block's own output axes), and at least one
    advancing dimension must be pinned to literal `0` (touches the lower boundary). -/
def baseWriteRowsOk (advancingDims : Array Nat) (outputShapeSize : Nat)
    (rows : Array (Option WriteRowKind)) : Bool :=
  rows.all Option.isSome &&
  ((rows.toList.filterMap (fun r => match r with | some (.free p) => some p | _ => none))
    == List.range outputShapeSize) &&
  advancingDims.any (fun d => rows.getD d none == some (.pinned 0))

/-- A step write's rows: every advancing dimension must be `.advancing` at its own context position
    (dimension `advancingDims[i]` at context position `i`), every other dimension must be `.free`
    in increasing order onto the block's own output axes, and no row may be unrecognized. -/
def stepWriteRowsOk (advancingDims : Array Nat) (outputShapeSize : Nat)
    (rows : Array (Option WriteRowKind)) : Bool :=
  rows.all Option.isSome &&
  (advancingDims.toList.zipIdx.all (fun (d, i) => rows.getD d none == some (.advancing i))) &&
  ((rows.toList.zipIdx.filterMap (fun (r, d) =>
      if advancingDims.contains d then none else match r with
        | some (.free p) => some p | _ => none))
    == List.range outputShapeSize)

/-- Two writes' declared regions collide iff no dimension forces them apart. Since every row is
    `.pinned`/`.free`/`.advancing`, a dimension forces the regions apart only when BOTH writes pin
    it to DIFFERENT literals; `.free`/`.advancing` always range over their full domain and can never
    exclude the other write. This single rule is what makes "two full free-axis faces never
    disjoint" (proposal §5.1) a structural consequence rather than an asserted claim — verified
    below against F0's own worked fixture. -/
def writesCollide (rowsA rowsB : Array (Option WriteRowKind)) : Bool :=
  ¬ (List.range rowsA.size).any (fun d =>
      match rowsA.getD d none, rowsB.getD d none with
      | some (.pinned a), some (.pinned b) => a != b
      | _, _ => false)

end LeanNCD.Eval.Plan
```

**Verified against F0's own fixture** (`test/Eval/ScanTest.lean`'s face-plus-point-override case,
`dp = [[0,1],[1,1]]`): building `dp`'s exact base writes (`dp[0,j] = ROWFACE[j]`: `coeffs = #[#[0],
#[1]], bias = #[0,0]`; `dp[1,0] = ONE`: `coeffs = #[#[],#[]], bias = #[1,0]`) and its step write
(`dp[r+1,c+1] := dp[r,c]+T[r,c]`: `coeffs = #[#[1,0],#[0,1]], bias = #[1,1]`), then confirming via
`check-snippet.sh`:

| Check | Result |
|---|---|
| `baseWriteRowsOk` on face write alone | `true` |
| `baseWriteRowsOk` on point-override write alone | `true` |
| `stepWriteRowsOk` on the step write | `true` |
| `writesCollide` face vs. disjoint point override | `false` (accepted) |
| `writesCollide` face vs. a shrunk point override now sharing `(0,0)` | `true` (rejected) |
| `writesCollide` face vs. a second free-axis face (row-0 vs. column-0) | `true` (rejected — both
individually pass `baseWriteRowsOk`, confirming the doc's claim that two free-axis faces can each be
individually well-formed yet never disjoint) |

### `ScanPlanError`, `checkCaptures`, `checkWrites`, `checkScanPlan` (`Scan.lean`, part 2)

```lean
/-- A raw `RawScanPlan` violates a scan-level invariant. Indices identify the offending
    state/write/capture so a failure is locatable without re-deriving it (proposal §7.5). -/
inductive ScanPlanError
  | noStates
  | noAdvancingAxes
  | zeroExtent                    (axisIndex : Nat)
  | stateDestSlotOutOfRange       (stateIndex : Nat) (slot : TensorSlot) (tableSize : Nat)
  | duplicateStateDestSlot        (stateIndex firstStateIndex : Nat) (slot : TensorSlot)
  | advancingDimOutOfRange        (stateIndex dim rank : Nat)
  | duplicateAdvancingDim         (stateIndex dim : Nat)
  | advancingDimCountMismatch     (stateIndex expected actual : Nat)
  | advancingSizeMismatch         (stateIndex axisIndex expected actual : Nat)
  | baseBlockContextNotEmpty      (actual : Array Nat)
  | stepBlockContextMismatch      (expected actual : Array Nat)
  | baseBlockError                (cause : BlockError)
  | stepBlockError                (cause : BlockError)
  | captureInputSlotOutOfRange    (isBase : Bool) (captureIndex : Nat) (slot : TensorSlot)
  | duplicateCaptureInput         (isBase : Bool) (slot : TensorSlot)
  | captureTargetsNonInput        (isBase : Bool) (slot : TensorSlot)
  | blockInputNotCaptured         (isBase : Bool) (slot : TensorSlot)
  | stateCaptureInBaseBlock       (captureIndex : Nat)
  | captureStateIndexOutOfRange   (isBase : Bool) (captureIndex stateIndex numStates : Nat)
  | captureExternalSlotOutOfRange (isBase : Bool) (captureIndex : Nat) (slot tableSize : Nat)
  | captureSignatureMismatch      (isBase : Bool) (captureIndex : Nat)
                                  (expected actual : TensorSignature)
  | noBaseWriteForState           (stateIndex : Nat)
  | noStepWriteForState           (stateIndex : Nat)
  | multipleStepWritesForState    (stateIndex firstWriteIndex secondWriteIndex : Nat)
  | writeStateIndexOutOfRange     (isBase : Bool) (writeIndex stateIndex numStates : Nat)
  | writeSourceNotBlockOutput     (isBase : Bool) (writeIndex : Nat) (slot : TensorSlot)
  | blockOutputNotWritten         (isBase : Bool) (outputSlot : TensorSlot)
  | duplicateWriteForOutput       (isBase : Bool) (outputSlot : TensorSlot)
                                  (firstWriteIndex secondWriteIndex : Nat)
  | writeGeometryNotAdmitted      (isBase : Bool) (writeIndex : Nat)
  | baseWritesOverlap             (stateIndex firstWriteIndex secondWriteIndex : Nat)
  | iterationOrderNotAdmitted     (order : ScanIterationOrder)
  | boundaryPolicyNotAdmitted     (policy : ScanBoundaryPolicy)
  | snapshotPolicyNotAdmitted     (policy : ScanSnapshotPolicy)
  | materializationPolicyNotAdmitted (stateIndex : Nat) (policy : MaterializationPolicy)
  | causalityFailure              (stateIndex termIndex factorIndex : Nat)  -- Task 2
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Evidence that one `RawScanPlan` is a sound checked scan: both blocks are checked, every
    capture/write obligation in proposal §7.3 holds, and (Task 2) causality holds for every state
    read. `stepExtents` is retained rather than recomputed by every consumer. -/
structure CheckedScanPlan where private mk ::
  raw         : RawScanPlan
  checkedBase : CheckedPlanBlock
  checkedStep : CheckedPlanBlock
  stepExtents : Array Nat
  deriving Repr

/-- Validate a block's captures against its own declared `inputs`: every capture's `inputSlot` is
    one of the block's inputs, every input has exactly one capture, and (for the base block) no
    capture may be a state capture. `numStates`/`states`/`isBase` parameterize the two call sites
    identically rather than duplicating this function. -/
private def checkCaptures (sigs : Array TensorSignature) (block : RawPlanBlock)
    (captures : Array BlockCapture) (numStates : Nat) (states : Array StateSlot) (isBase : Bool) :
    Except ScanPlanError Unit := do
  let mut boundInputs : Array Bool := Array.replicate block.tensorSigs.size false
  for h : i in [0 : captures.size] do
    let c := captures[i]
    unless c.inputSlot < block.tensorSigs.size do
      throw (.captureInputSlotOutOfRange isBase i c.inputSlot)
    unless block.inputs.contains c.inputSlot do
      throw (.captureTargetsNonInput isBase c.inputSlot)
    if boundInputs.getD c.inputSlot false then throw (.duplicateCaptureInput isBase c.inputSlot)
    boundInputs := boundInputs.set! c.inputSlot true
    match c.source with
    | .external outerSlot =>
        unless outerSlot < sigs.size do
          throw (.captureExternalSlotOutOfRange isBase i outerSlot sigs.size)
        let expected := sigs.getD outerSlot { shape := #[], dtype := .f64 }
        let actual := block.tensorSigs.getD c.inputSlot { shape := #[], dtype := .f64 }
        unless expected == actual do throw (.captureSignatureMismatch isBase i expected actual)
    | .state stateIndex =>
        if isBase then throw (.stateCaptureInBaseBlock i)
        unless stateIndex < numStates do
          throw (.captureStateIndexOutOfRange isBase i stateIndex numStates)
        let st := states.getD stateIndex default
        let expected := sigs.getD st.destSlot { shape := #[], dtype := .f64 }
        let actual := block.tensorSigs.getD c.inputSlot { shape := #[], dtype := .f64 }
        unless expected == actual do throw (.captureSignatureMismatch isBase i expected actual)
  for inputSlot in block.inputs do
    unless boundInputs.getD inputSlot false do throw (.blockInputNotCaptured isBase inputSlot)

/-- Validate one block's writes against its own declared `outputs` and against `states`: every
    write's `stateIndex` is in range, every write's `outputSlot` is a declared block output, every
    declared output is written by exactly one write, base-write geometry is admitted and pairwise
    disjoint across each state's FULL write list, and step-write geometry is admitted. Returns, per
    state, the accepted row classifications so the caller can additionally require exactly one step
    write and at least one base write. -/
private def checkWrites (sigs : Array TensorSignature) (block : RawPlanBlock)
    (writes : Array StateWriteMap) (states : Array StateSlot) (isBase : Bool) :
    Except ScanPlanError (Array (Array (Array (Option WriteRowKind)))) := do
  let mut writtenOutputs : Array (Option Nat) := Array.replicate block.tensorSigs.size none
  let mut rowsByState : Array (Array (Array (Option WriteRowKind))) :=
    Array.replicate states.size #[]
  for h : wi in [0 : writes.size] do
    let w := writes[wi]
    unless w.stateIndex < states.size do
      throw (.writeStateIndexOutOfRange isBase wi w.stateIndex states.size)
    unless block.outputs.contains w.outputSlot do
      throw (.writeSourceNotBlockOutput isBase wi w.outputSlot)
    match writtenOutputs.getD w.outputSlot none with
    | some firstWi => throw (.duplicateWriteForOutput isBase w.outputSlot firstWi wi)
    | none => writtenOutputs := writtenOutputs.set! w.outputSlot (some wi)
    let st := states.getD w.stateIndex default
    let stateRank := (sigs.getD st.destSlot { shape := #[], dtype := .f64 }).shape.size
    let contextWidth := if isBase then 0 else st.advancingDims.size
    let rows := writeRowKinds stateRank contextWidth w
    let outputShapeSize := (block.tensorSigs.getD w.outputSlot { shape := #[], dtype := .f64 }).shape.size
    let admitted := if isBase then baseWriteRowsOk st.advancingDims outputShapeSize rows
                    else stepWriteRowsOk st.advancingDims outputShapeSize rows
    unless admitted do throw (.writeGeometryNotAdmitted isBase wi)
    rowsByState := rowsByState.set! w.stateIndex (rowsByState.getD w.stateIndex #[] |>.push rows)
  for outputSlot in block.outputs do
    unless writtenOutputs.getD outputSlot none |>.isSome do
      throw (.blockOutputNotWritten isBase outputSlot)
  -- pairwise disjointness across each state's FULL base-write list (proposal §7.3: not just
  -- checked between an arbitrarily chosen pair; index into each state's own accumulated write
  -- list, not the raw `writes` array — the implementer may thread through global write indices
  -- instead if a reviewer prefers that error shape, a call-site detail with no semantic effect).
  if isBase then
    for h : si in [0 : rowsByState.size] do
      let stateRows := rowsByState[si]
      for h2 : a in [0 : stateRows.size] do
        for h3 : b in [0 : stateRows.size] do
          if a < b then
            if writesCollide stateRows[a] stateRows[b] then throw (.baseWritesOverlap si a b)
  return rowsByState

/-- Validate an unchecked scan node (proposal §7.3). This version omits causality — Task 2 adds the
    `stateReadCausal` pass before the final `return`. -/
def checkScanPlan (sigs : Array TensorSignature) (raw : RawScanPlan) :
    Except ScanPlanError CheckedScanPlan := do
  if raw.states.isEmpty then throw .noStates else pure ()
  if raw.historyExtents.isEmpty then throw .noAdvancingAxes else pure ()
  for h : i in [0 : raw.historyExtents.size] do
    if raw.historyExtents[i] == 0 then throw (.zeroExtent i) else pure ()
  let stepExtents : Array Nat := raw.historyExtents.map (· - 1)
  let numAxes := raw.historyExtents.size
  let mut destSeen : Array (Option Nat) := Array.replicate sigs.size none
  for h : si in [0 : raw.states.size] do
    let st := raw.states[si]
    unless st.destSlot < sigs.size do
      throw (.stateDestSlotOutOfRange si st.destSlot sigs.size)
    match destSeen.getD st.destSlot none with
    | some firstSi => throw (.duplicateStateDestSlot si firstSi st.destSlot)
    | none => destSeen := destSeen.set! st.destSlot (some si)
    unless st.advancingDims.size == numAxes do
      throw (.advancingDimCountMismatch si numAxes st.advancingDims.size)
    let stateSig := sigs.getD st.destSlot { shape := #[], dtype := .f64 }
    let mut dimSeen : Array Bool := Array.replicate stateSig.shape.size false
    for h2 : i in [0 : st.advancingDims.size] do
      let d := st.advancingDims[i]
      unless d < stateSig.shape.size do throw (.advancingDimOutOfRange si d stateSig.shape.size)
      if dimSeen.getD d false then throw (.duplicateAdvancingDim si d)
      dimSeen := dimSeen.set! d true
      unless stateSig.shape.getD d 0 == raw.historyExtents.getD i 0 do
        throw (.advancingSizeMismatch si i (raw.historyExtents.getD i 0) (stateSig.shape.getD d 0))
    unless st.materialization == .completeHistory do
      throw (.materializationPolicyNotAdmitted si st.materialization)
  unless raw.iterationOrder == .axisZeroFastest do
    throw (.iterationOrderNotAdmitted raw.iterationOrder)
  unless raw.boundaryPolicy == .zeroThenBaseOverlay do
    throw (.boundaryPolicyNotAdmitted raw.boundaryPolicy)
  unless raw.snapshotPolicy == .immutablePreStep do
    throw (.snapshotPolicyNotAdmitted raw.snapshotPolicy)
  unless raw.baseBlock.contextShape == #[] do throw (.baseBlockContextNotEmpty raw.baseBlock.contextShape)
  unless raw.stepBlock.contextShape == stepExtents do
    throw (.stepBlockContextMismatch stepExtents raw.stepBlock.contextShape)
  let checkedBase ← (checkPlanBlock raw.baseBlock).mapError .baseBlockError
  let checkedStep ← (checkPlanBlock raw.stepBlock).mapError .stepBlockError
  checkCaptures sigs raw.baseBlock raw.baseCaptures raw.states.size raw.states true
  checkCaptures sigs raw.stepBlock raw.stepCaptures raw.states.size raw.states false
  let baseRowsByState ← checkWrites sigs raw.baseBlock raw.baseWrites raw.states true
  let stepRowsByState ← checkWrites sigs raw.stepBlock raw.stepWrites raw.states false
  for h : si in [0 : raw.states.size] do
    if (baseRowsByState.getD si #[]).size == 0 then throw (.noBaseWriteForState si) else pure ()
    match (stepRowsByState.getD si #[]).size with
    | 0 => throw (.noStepWriteForState si)
    | 1 => pure ()
    | _ => throw (.multipleStepWritesForState si 0 1)
  -- Task 2 inserts the causality pass here, before the return below.
  return CheckedScanPlan.mk raw checkedBase checkedStep stepExtents

end LeanNCD.Eval.Plan
```

**Verified end-to-end** via `check-snippet.sh` against a hand-built linear self-recurrence
`RawScanPlan` (outer slots `0=S0` scalar, `1=X` shape `[3]`, `2=S` shape `[3]`; base `S[iterAt l
0]:=S0`; step `S[iterNext l]:=S[l]+X[l]`; `historyExtents=#[3]`):

- `checkScanPlan outerSigs linearScan` → `.ok` (both blocks check, captures/writes bijections hold,
  geometry admitted: base row `.pinned 0`, step row `.advancing 0`).
- Mutating `historyExtents` to `#[0]` → `.error (.zeroExtent 0)`.
- Mutating the step write's bias from `1` to `2` (a look-ahead-shaped write) → `.error
  (.writeGeometryNotAdmitted false 0)`.

### Task 1 steps

- [ ] Create `RawStep.lean` with the relocated/new raw types (verified above).
- [ ] Modify `Block.lean`: delete the `RawPlanBlock` struct definition; confirm the file still
      compiles unchanged otherwise.
- [ ] Modify `Graph.lean`: `import LeanNCD.Eval.Plan.RawStep` in place of `.Kernel`; `steps : Array
      PlanStep`; remove the `version : Nat` field.
- [ ] Modify `Error.lean`: remove `PlanError.versionNotAdmitted`.
- [ ] Modify `Check.lean`: remove `admittedVersion`. (`checkPlan`/`CheckedEvalPlan` removal is Task 4,
      since Task 1 doesn't yet need them touched — leave a `-- TODO(F3 Task 4)` marker only if the
      file would otherwise fail to compile standalone; if it still compiles with `admittedVersion`
      merely unused elsewhere, defer the `checkPlan` extraction entirely to Task 4 to avoid two
      partial edits to the same function.)
- [ ] Create `Scan.lean` with `WriteRowKind`/classifier/validators, `ScanPlanError`,
      `CheckedScanPlan`, `checkCaptures`, `checkWrites`, `checkScanPlan` (verified above).
- [ ] Create `test/Eval/Plan/ScanTest.lean` with: the write-geometry worked examples (face/point/
      collision/two-free-faces, verified above), the linear-scan accept/zero-extent/bad-geometry
      cases (verified above), plus one mutation per remaining reachable `ScanPlanError` branch not
      already covered (`noStates`, `stateDestSlotOutOfRange`, `duplicateStateDestSlot`,
      `advancingDimOutOfRange`, `duplicateAdvancingDim`, `advancingDimCountMismatch`,
      `advancingSizeMismatch`, `baseBlockContextNotEmpty`, `stepBlockContextMismatch`,
      `baseBlockError`/`stepBlockError` propagation, every `checkCaptures`/`checkWrites` branch,
      `baseWritesOverlap`, `noBaseWriteForState`, `noStepWriteForState`,
      `multipleStepWritesForState`) — required by this slice's own gate ("one mutation per
      reachable scan... error branch").
- [ ] Add `"Eval.Plan.ScanTest"` to `lakefile.toml`'s `Tests` globs; add `import
      LeanNCD.Eval.Plan.RawStep` and `.Scan` to `LeanNCD.lean`.

**Gate:** `checkScanPlan` rejects every malformed structural/geometry/capture shape with the correct
`ScanPlanError` branch; every accepted case's `CheckedScanPlan` carries the exact checked blocks
`checkPlanBlock` would independently produce; `lake build` green.

---

## Task 2: Causality certificate

Add the causality recognizer (verified below, including against the exact Jacobi/Gauss-Seidel
snapshot-safety fixture F0 pinned to show the *legacy* evaluator is unsafe) and wire it into
`checkScanPlan`.

```lean
-- Scan.lean, appended after writesCollide, before ScanPlanError:

/-- Opaque evidence that every persistent-state read in a scan's step block is causal. Only
    `checkScanPlan` constructs values whose presence certifies this (the certificate itself carries
    no data beyond marking that the pass ran — `CheckedScanPlan`'s existence, not a separate field,
    is the evidence a worker relies on; see the note after `stateReadCausal` below for why no
    separate stored field is needed). -/

/-- Whether one read row (for state dimension `d`, whose scan-context position is `ctxPos`) is
    causal: exactly one nonzero coefficient, equal to `1`, at `ctxPos`, and non-positive bias. This
    single row-shape rule captures all three cases of proposal §7.4's causality obligation
    uniformly — out-of-bounds zero-padding, initialized-boundary reads, and a strictly-earlier
    recurrence producer are not case-split here: a canonical `q + 1` successor write makes every row
    satisfying this shape resolve to one of those three automatically, regardless of the concrete
    bias value or declared extents (the checker "tests this implication directly over the canonical
    geometry," per §7.4, rather than leaving it as worker folklore). -/
def causalAdvancingRow (row : Array Int) (bias : Int) (ctxPos : Nat) : Bool :=
  let nz := row.toList.zipIdx.filter (fun (c, _) => c != 0)
  match nz with
  | [(c, p)] => c == 1 && p == ctxPos && bias ≤ 0
  | _ => false

/-- Every advancing dimension of a captured state's read must be causal at its own scan-context
    position; non-advancing dimensions are ordinary reads and carry no causality obligation. -/
def stateReadCausal (advancingDims : Array Nat) (contextPos : Array Nat) (f : ReadPlan) : Bool :=
  advancingDims.size == contextPos.size &&
  (Array.range advancingDims.size).all (fun i =>
    causalAdvancingRow (f.map.coeffs.getD (advancingDims.getD i 0) #[])
      (f.map.bias.getD (advancingDims.getD i 0) 0) (contextPos.getD i 0))
```

**Verified** (standalone, then integrated) against four worked reads:

| Read | Row shape | `stateReadCausal` |
|---|---|---|
| `G[l-2]` (F0's deep-history fixture) | `coeffs=#[1], bias=#[-2]` | `true` |
| `G[l+1]` (hypothetical look-ahead) | `coeffs=#[1], bias=#[1]` | `false` |
| `A[.const 1]` (F0's Jacobi discriminator's unsafe read) | `coeffs=#[0], bias=#[1]` | `false` |
| `G[l]` (ordinary predecessor) | `coeffs=#[1], bias=#[0]` | `true` |

**Integration point** — insert immediately before `checkScanPlan`'s final `return`:

```lean
  let stateCaptureFor : TensorSlot → Option Nat := fun inputSlot =>
    (raw.stepCaptures.find? (fun c => c.inputSlot == inputSlot)).bind (fun c => match c.source with
      | .state si => some si | .external _ => none)
  for h : ai in [0 : raw.stepBlock.assignments.size] do
    let a := raw.stepBlock.assignments[ai]
    for h2 : ti in [0 : a.terms.size] do
      let t := a.terms[ti]
      for h3 : fi in [0 : t.factors.size] do
        let f := t.factors[fi]
        match stateCaptureFor f.sourceSlot with
        | none => pure ()
        | some si =>
            let st := raw.states.getD si default
            unless stateReadCausal st.advancingDims t.contextPos f do
              throw (.causalityFailure si ti fi)
  return CheckedScanPlan.mk raw checkedBase checkedStep stepExtents
```

**Verified end-to-end** against a hand-built deep-history `RawScanPlan` (`G[l+1]:=G[l-2]`, axis size
5, matching F0's own observed `evalScan` result `[5,0,0,5,0]`): `checkScanPlan` accepts it. A
mutation replacing that read with a constant read (`coeffs=#[0], bias=#[1]`, mirroring the Jacobi
discriminator's `A[.const 1]`) is rejected with `.causalityFailure 0 0 0`.

### Task 2 steps

- [ ] Add `causalAdvancingRow`/`stateReadCausal` to `Scan.lean` (verified above).
- [ ] Insert the causality loop into `checkScanPlan` (verified above).
- [ ] Add fixtures to `ScanTest.lean`: the deep-history accept case, the constant-read
      `causalityFailure` rejection, a look-ahead-bias rejection, and one mutation confirming
      `stateReadCausal` genuinely gates a *non-advancing* read differently (a non-advancing "j"-axis
      read must NOT be causality-checked — confirm a plain non-advancing read with an arbitrary
      affine map still passes, so the certificate is not over-restrictive).

**Gate:** every persistent-state read failing proposal §7.4's rule is rejected with
`.causalityFailure`; every causal read (including non-positive deep history) is admitted; `lake
build` green.

---

## Task 3: Rank/unrank and the four-phase Dense scan worker

```lean
-- Scan.lean, appended:

/-- `rank_D(q) = sum_i q[i] * product_{j<i} D[j]` (proposal §6.6): axis `0` varies fastest. -/
def mixedRadixRank (D : Array Nat) (q : Array Nat) : Nat :=
  (Array.range D.size).foldl (fun acc i =>
    acc + q.getD i 0 * (Array.range i).foldl (fun p j => p * D.getD j 1) 1) 0

/-- Inverse of `mixedRadixRank`: axis `0` decoded first (fastest-varying), matching
    `ScanIterationOrder.axisZeroFastest`. Deliberately independent from `Coordinates.lean`'s
    `allCoords` (last-index-fastest, the local-kernel's own row-major convention) — proposal §9.3:
    "Rank/unrank belongs to the scan worker and is intentionally independent from the local
    assignment kernel's coordinate enumerator." -/
def mixedRadixUnrank (D : Array Nat) (r : Nat) : Array Nat := Id.run do
  let mut rem := r
  let mut q : Array Nat := #[]
  for d in D do
    q := q.push (rem % d)
    rem := rem / d
  return q

def mixedRadixDomainSize (D : Array Nat) : Nat := D.foldl (· * ·) 1

/-- Place one write's value(s) into a complete-state tensor. `ctx` is the write's context portion
    (empty for base, the current recurrence coordinate for step); the write's full domain is
    `ctx ++ outputCoord` for every coordinate `outputCoord` of the block's own output tensor at
    `w.outputSlot` (proposal §6.5) — a write with a genuinely FREE position (e.g. a face write like
    `dp[0, j] := ROWFACE[j]`) has a non-scalar output and must place every one of its elements, not
    just element `0`. Reduces to the scalar case cleanly: `allCoords [] = [[]]` (one iteration),
    `flatIndex [] [] = 0`, so a fully-pinned/advancing write (no free positions, scalar output)
    behaves exactly as a single-coordinate commit. **Corrected during Task 3** (ledger ruling): an
    earlier draft of this function took only `blockStore...data.getD 0 0.0` and one fixed `iter`,
    which is correct ONLY for scalar (no-free-position) writes — it silently dropped every element
    past the first for any write with a genuine free output position, a real, load-bearing gap the
    plan's own required fixtures (multi-base-write face-plus-point-override, asymmetric rectangular)
    would otherwise not have caught, since the linear-scan fixture this function was originally
    verified against has no free-position writes at all. Verified against both the scalar case
    (`[42.0,0,0]` unaffected) and a worked 2-element face write (`dp[0,j] := ROWFACE[j]`, `ROWFACE =
    [10,20]`, correctly placing `[10,20,0,0]` into a `2×2` target) via `check-snippet.sh`. -/
private def commitWrite (target : DenseTensor) (w : StateWriteMap) (blockStore : Array DenseTensor)
    (ctx : List Int) : DenseTensor := Id.run do
  let out := blockStore.getD w.outputSlot { shape := [], data := #[] }
  let mut target := target
  for oc in allCoords out.shape do
    let iter := ctx ++ oc
    let coord := (applyAffine w.map iter).map Int.toNat
    let v := out.data.getD (flatIndex out.shape (oc.map Int.toNat)) 0.0
    target := { target with data := target.data.set! (flatIndex target.shape coord) v }
  return target

/-- The general Dense scan worker (proposal §9): allocate, apply every checked base write, then for
    each recurrence coordinate in increasing mixed-radix rank, bind an immutable pre-step snapshot,
    run the checked step block, and commit every designated next-state slice simultaneously.
    Independent of `Eval.evalScan`/`evalScheduled` by construction — imports neither, builds no
    `HashMap UID Int`, knows no source names (proposal §9.1). `sigs` supplies each state's declared
    complete shape for allocation. -/
def runDenseScan (sigs : Array TensorSignature) (c : CheckedScanPlan) (outerStore : Array DenseTensor) :
    Except PositionalInputError (Array DenseTensor) := do
  let raw := c.raw
  let mut states : Array DenseTensor := raw.states.map (fun st =>
    let sig := sigs.getD st.destSlot { shape := #[], dtype := .f64 }
    { shape := sig.shape.toList, data := Array.replicate (sig.shape.toList.foldl (· * ·) 1) 0.0 })
  let baseExternalInputs ← raw.baseCaptures.mapM (fun cap => match cap.source with
    | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
    | .state _ => throw (PositionalInputError.arityMismatch 0 0))  -- unreachable: checked
  let baseStore ← runDenseBlock c.checkedBase [] baseExternalInputs
  for w in raw.baseWrites do
    let target := states.getD w.stateIndex { shape := [], data := #[] }
    states := states.set! w.stateIndex (commitWrite target w baseStore [])
  let domainSize := mixedRadixDomainSize c.stepExtents
  for r in [0 : domainSize] do
    let q := mixedRadixUnrank c.stepExtents r
    let oldStates := states
    let stepInputs ← raw.stepCaptures.mapM (fun cap => match cap.source with
      | .external slot => pure (outerStore.getD slot { shape := [], data := #[] })
      | .state si => pure (oldStates.getD si { shape := [], data := #[] }))
    let ctx : List Int := q.toList.map Int.ofNat
    let stepStore ← runDenseBlock c.checkedStep ctx stepInputs
    let mut nextStates := states
    for w in raw.stepWrites do
      let target := nextStates.getD w.stateIndex { shape := [], data := #[] }
      nextStates := nextStates.set! w.stateIndex (commitWrite target w stepStore ctx)
    states := nextStates
  let mut result := outerStore
  for h : si in [0 : raw.states.size] do
    result := result.set! raw.states[si].destSlot (states.getD si { shape := [], data := #[] })
  return result
```

**Verified**, both pieces independently and composed:

1. **Rank/unrank round-trip and ordering**, `D = #[2, 3]`: `mixedRadixUnrank` for ranks `0..5`
   produces exactly `[(0,0),(1,0),(0,1),(1,1),(0,2),(1,2)]` (axis `0` visibly fastest-varying), and
   `mixedRadixRank D (mixedRadixUnrank D r) == r` for every `r` in that range.
2. **Full worker**, run against the linear self-recurrence fixture (`S0=1, X=[10,20,30]`): produces
   `data == #[1, 11, 31]` — bit-for-bit the value `test/Eval/ScanTest.lean`'s own linear-scan fixture
   observes from the real `evalScan` for this recurrence shape.

### Additional hand-computed fixtures required for `ScanTest.lean` (values already observed)

| Fixture | Source of the observed value | Expected |
|---|---|---|
| Self-recurrence (linear scan) | `test/Eval/ScanTest.lean`'s own linear fixture, adapted to a single state | `[1, 11, 31]` — verified above |
| Deep history (`k=2` look-back) | F0's fixture, `test/Eval/ScanTest.lean` | `[5, 0, 0, 5, 0]` |
| Extent one (base-only) | F0's fixture | `[7]` |
| Coupled (Fibonacci-shaped `G`/`H`) | `test/Eval/ScanTest.lean`'s own coupled fixture | `G=[1,2,3,5]`, `H=[1,1,2,3]` |
| Face-plus-point-override multi-base-write | F0's fixture, `test/Eval/ScanTest.lean` | `dp = [0,1,1,1]` (row-major `[2,2]`) |
| Asymmetric rectangular all-axis `+1` (`2×3`) | Freshly run against the real `evalScan` while drafting this plan (not in any existing test file) — `iter r=2,c=3; G[r,0]:=Z[r]; G[r+1,c+1]:=G[r,c]+A[r,c]`, `Z=[2,5]`, `A=`ones`(2,3)` | `[2,0,0, 5,3,1]` (row-major `[2,3]`) — confirmed via `check-snippet.sh` running the actual legacy evaluator, output `#[2.0,0.0,0.0,5.0,3.0,1.0]` |

Each of these needs its own hand-built `RawScanPlan`/`RawPlanBlock` (following the linear-scan
fixture's shape above) and a `runDenseScan` assertion against the table's value. The coupled and
asymmetric cases additionally exercise geometry/causality this plan's other fixtures don't: coupled
states reading each other's captures, and a state with different per-axis history extents.

### Task 3 steps

- [ ] Add `mixedRadixRank`/`Unrank`/`DomainSize`, `commitWrite`, `runDenseScan` to `Scan.lean`
      (verified above).
- [ ] Add the six hand-computed fixtures above to `ScanTest.lean`, each built as a `RawScanPlan` and
      asserted via `runDenseScan` (not `checkScanPlan` alone — these exercise execution, not just
      checking).
- [ ] Mutation coverage per §11.4: reverse the mixed-radix rank order and confirm a coupled or
      deep-history fixture's result changes (demonstrating traversal order is actually observed, not
      incidentally correct); change one step-write `+1` bias and confirm the result changes; bind a
      state capture from a stale/wrong array in `stepInputs`' construction and confirm the affected
      fixture's result changes (demonstrating the snapshot-vs-mutable distinction is load-bearing,
      not vacuous — proposal §11.4's "bind a state capture from a deliberately different
      accumulator" mutation). Record both the mutated (fails) and restored (passes) observations for
      each, per the `slice-plan` skill's mutation discipline.

**Gate:** every hand-computed fixture's `runDenseScan` result matches its table value exactly; every
required mutation demonstrably changes the result; the worker imports no DSL, `Plan.Compile`, or
legacy `Eval` execution module (`Eval.Scan`, `Eval.Gather`, `Eval.Contract`, etc. — confirm via
import list, matching proposal §9.1); `lake build` green.

---

## Task 4: Outer graph integration — `EvalPlan.lean`, multi-output `checkPlan`/`runDensePlan`, and migration

Relocate `checkPlan`/`CheckedEvalPlan`/`runDensePlan` into a new `EvalPlan.lean` (the only module
that can see both the local-kernel checker/worker and the scan checker/worker without a cycle — see
this plan's Architecture section), generalize them to handle `PlanStep.scan`, and migrate every
existing `RawEvalPlan` construction site to the new `steps : Array PlanStep` shape.

### `CheckedPlanStepEvidence`, relocated `CheckedEvalPlan`/`checkPlan`, relocated `runDensePlan`

```lean
-- leanncd/LeanNCD/Eval/Plan/EvalPlan.lean
import LeanNCD.Eval.Plan.Scan

namespace LeanNCD.Eval.Plan

/-- One outer step's checked meaning: either a local assignment or a scan. Replaces
    `CheckedEvalPlan.checkedNodes`'s previous element type, `CheckedAssignPlan`, now that outer
    nodes are no longer uniformly assignments. -/
inductive CheckedPlanStepEvidence
  | assign (c : CheckedAssignPlan)
  | scan   (c : CheckedScanPlan)
  deriving Repr

/-- A `PlanStep`'s outer-graph-visible source/destination slots — derived, not stored (proposal
    §6.6: "These are derived functions, not stored fields"). An assignment has one destination; a
    scan has one per state, plus every base/step external capture as a source alongside its own
    factor sources are already covered by the block's own checking. -/
def PlanStep.sourceSlots : PlanStep → Array TensorSlot
  | .assign a => a.terms.flatMap (·.factors.map (·.sourceSlot))
  | .scan s => (s.baseCaptures ++ s.stepCaptures).filterMap (fun c => match c.source with
      | .external slot => some slot | .state _ => none)

def PlanStep.destinationSlots : PlanStep → Array TensorSlot
  | .assign a => #[a.destinationSlot]
  | .scan s => s.states.map (·.destSlot)

/-- Evidence that a `RawEvalPlan`'s wiring is sound, generalized to `PlanStep`: every step is
    locally checked (via `checkAssign` or `checkScanPlan`), input slots are in-range/unique/ordered,
    no step's destination overwrites an existing slot, every read is from an input or an earlier
    destination, and every non-input slot is produced exactly once. A scan step's MULTIPLE
    destination slots are all marked produced together, atomically with respect to this outer-graph
    tracking — matching the scan's own atomic commit semantics one level up. -/
structure CheckedEvalPlan where private mk ::
  raw          : RawEvalPlan
  checkedNodes : Array CheckedPlanStepEvidence
  deriving Repr

/-- Validate an open evaluation graph. Generalizes Wave C's `checkPlan` (previously in `Check.lean`)
    to `PlanStep`: an ordinary node still uses `checkAssign` verbatim and requires empty context
    exactly as before; a scan node uses `checkScanPlan` and requires ALL of its declared destination
    slots to be currently unavailable (so none can already be produced) before checking, then marks
    all of them available together afterward. -/
def checkPlan (raw : RawEvalPlan) : Except PlanError CheckedEvalPlan := do
  unless raw.numericMode == .reference64SumProduct do throw (.numericModeNotAdmitted raw.numericMode)
  let n := raw.tensorSigs.size
  for h : i in [0 : raw.inputSlots.size] do
    let s := raw.inputSlots[i]
    unless s < n do throw (.slotOutOfRange s n)
    if h2 : i + 1 < raw.inputSlots.size then
      let s2 := raw.inputSlots[i + 1]
      if s == s2 then throw (.duplicateInputSlot s)
      else if s2 < s then throw (.inputSlotsNotOrdered i)
  let mut available : Array Bool := Array.replicate n false
  let mut producedBy : Array (Option Nat) := Array.replicate n none
  for s in raw.inputSlots do
    available := available.set! s true
  let mut checkedNodes : Array CheckedPlanStepEvidence := #[]
  for h : ni in [0 : raw.steps.size] do
    let step := raw.steps[ni]
    for src in step.sourceSlots do
      match available[src]? with
      | none => throw (.nodeError ni (.slotOutOfRange src n))
      | some true => pure ()
      | some false => throw (.invalidForwardRead ni 0 0 src)
    let dests := step.destinationSlots
    for dest in dests do
      match available[dest]? with
      | none => throw (.nodeError ni (.slotOutOfRange dest n))
      | some isAvail =>
          if isAvail then
            match producedBy[dest]?.join with
            | none => throw (.inputSlotOverwritten dest ni)
            | some firstNode => throw (.duplicateDestination dest firstNode ni)
    match step with
    | .assign a =>
        unless a.contextShape == #[] do throw (.topLevelContextNotEmpty ni)
        match checkAssign raw.tensorSigs a with
        | .error e => throw (.nodeError ni e)
        | .ok c => checkedNodes := checkedNodes.push (.assign c)
    | .scan s =>
        match checkScanPlan raw.tensorSigs s with
        | .error e => throw (.nodeError ni (.scanError e))  -- see note below
        | .ok c => checkedNodes := checkedNodes.push (.scan c)
    for dest in dests do
      available := available.set! dest true
      producedBy := producedBy.set! dest (some ni)
  for h : i in [0 : n] do
    unless available[i]! do throw (.missingProduction i)
  return CheckedEvalPlan.mk raw checkedNodes

/-- Execute a checked graph over positional Dense inputs. Generalizes `runDensePlan` (previously in
    `Dense.lean`): a `.assign` node uses `runDenseAssign` exactly as before; a `.scan` node uses
    `runDenseScan` and writes every one of its state destinations into the store. -/
def runDensePlan (c : CheckedEvalPlan) (inputs : Array DenseTensor) :
    Except PositionalInputError (Array DenseTensor) := do
  let raw := c.raw
  unless inputs.size == raw.inputSlots.size do
    throw (.arityMismatch raw.inputSlots.size inputs.size)
  let n := raw.tensorSigs.size
  let placeholder : DenseTensor := { shape := [], data := #[] }
  let mut store : Array DenseTensor := Array.replicate n placeholder
  for h : i in [0 : raw.inputSlots.size] do
    let slot := raw.inputSlots[i]
    let t := inputs[i]!
    let sig := raw.tensorSigs.getD slot { shape := #[], dtype := .f64 }
    unless t.shape == sig.shape.toList do throw (.shapeMismatch slot sig.shape t.shape)
    unless t.data.size == sig.shape.toList.foldl (· * ·) 1 do
      throw (.storageMismatch slot t.shape t.data.size)
    store := store.set! slot t
  for node in c.checkedNodes do
    match node with
    | .assign c => store := store.set! c.plan.destinationSlot (← runDenseAssign c store)
    | .scan c => store ← runDenseScan raw.tensorSigs c store
  return store

end LeanNCD.Eval.Plan
```

**Open item flagged for the implementer, not silently resolved:** `.nodeError ni (.scanError e)`
above assumes a new `PlanError.scanError (cause : ScanPlanError)` constructor — but `PlanError`
(`Error.lean`) is upstream of `Scan.lean` and cannot reference `ScanPlanError` (the same acyclic-
import constraint as `RawPlanBlock`/`Graph.lean`, this time one layer up). **Do not add
`PlanError.scanError`.** Instead, introduce the wrapping at `EvalPlan.lean`'s own level, downstream
of everything: change `checkPlan`'s return type from `Except PlanError CheckedEvalPlan` to `Except
PlanStepError CheckedEvalPlan`, where

```lean
/-- `checkPlan`'s error type, generalized from bare `PlanError` now that an outer step can fail
    either as a malformed assignment (unchanged `PlanError`, including its existing `nodeError`
    wrapper) or a malformed scan (`ScanPlanError`, not representable inside `PlanError` itself — see
    this plan's Architecture section for why). -/
inductive PlanStepError
  | assign (cause : PlanError)
  | scan   (stepIndex : Nat) (cause : ScanPlanError)
  deriving Repr
```

lives in `EvalPlan.lean` too, and every existing `PlanError`-shaped failure from the loop above
(`slotOutOfRange`, `duplicateInputSlot`, ..., `checkAssign`'s own errors via `nodeError`) is wrapped
as `.assign (...)` at the point `checkPlan` throws, while a `checkScanPlan` failure becomes `.scan ni
e` directly (no double-wrapping through `nodeError`, since `ScanPlanError` already carries its own
internal locators). This is a real, deliberate divergence from the proposal's §7.5 sketch
(`PlanError.scanError(stepIndex, ScanPlanError)`), recorded here rather than discovered mid-
implementation, because the sketch is not achievable given the actual file layout. Consumers
downstream of `checkPlan`'s result type change accordingly:

- `PlanCompileCause.invalidPlan (cause : PlanError)` → `(cause : PlanStepError)` (`Error.lean`).
- `Compile.lean:245`'s `liftPlanError warnings (checkPlan raw)` and its error-mapping helper update
  their own type to match — check `liftPlanError`'s current signature directly before editing (this
  plan does not assume its exact shape sight-unseen).
- `test/Eval/Plan/{AdapterTest,CompileTest}.lean`'s `.invalidPlan c => s!"invalidPlan: {repr c}"`
  arms need no logic change (generic `repr`), only re-verification that they still compile against
  the new payload type.

### Migration inventory (verified by direct `grep`, not estimated)

`RawEvalPlan` literal-construction sites needing `version :=` removed and every `steps := #[...]`
entry wrapped in `.assign`:

| File | Literal sites |
|---|---|
| `test/Eval/Plan/GraphCheckTest.lean` | 4 |
| `test/Eval/Plan/GraphDenseTest.lean` | 11 |
| `test/Eval/Plan/ExecutableTest.lean` | 4 |
| `test/Eval/Plan/KernelCheckTest.lean` | 2 |
| `test/Eval/Plan/CompileTest.lean` | field access, not construction — see below |

`test/Eval/Plan/GraphCheckTest.lean:80`'s `errOf (checkPlan { diamondPlan with version := 2 }) ==
some (.versionNotAdmitted 2)` fixture is deleted outright (the field and error it tests no longer
exist) — this is expected loss of a Wave-C-only regression test, not a gap, per proposal §2.3's own
argument for removing the version tag.

**`Compile.lean`'s own `RawEvalPlan` construction site already landed in Task 1** (ledger ruling —
a 2-token, zero-logic-change fix pulled forward to keep `lake build` green through Tasks 1-3):
`steps := stepsAcc` → `steps := stepsAcc.map .assign`, `version := admittedVersion,` deleted.
**`CompileTest.lean` surfaced as a 5th affected test file only once that fix let `Compile.lean`
itself compile** (Lean can't attempt a file whose imports don't build) — a different fix shape from
the other four: it's not a `RawEvalPlan` literal construction site, it's direct field access on an
already-`PlanStep`-typed value (`p.plan.raw.steps[0]!.terms`, `.contextShape`, confirmed by running
`lake env lean test/Eval/Plan/CompileTest.lean` directly — `PlanStep` has no `.terms` field, only
`.assign`/`.scan` do). Fix each site as `match p.plan.raw.steps[0]! with | .assign a => a.terms | .scan
_ => <fail the assertion — every one of these fixtures is scan-free by construction, so this arm
should never actually be hit; make that explicit rather than silently defaulting>`, not by chasing a
literal-construction pattern that doesn't apply here.

**`JaxExperiment` breakage (deliberately not fixed here):** `experiments/jax_bridge/
{EvalPlanCodegen,EvalPlanAffineSmoke,EvalPlanAffineCorpus}.lean` iterate `checkedNodes` assuming a
bare `CheckedAssignPlan` element (`cn.plan`, `plan.plan.checkedNodes.flatMap ...`) and will fail
under `lake build JaxExperiment` once `checkedNodes`'s element type becomes
`CheckedPlanStepEvidence`. `JaxExperiment` is excluded from `defaultTargets`, so this does not fail
`lake build` or gate this slice. Record it in the Task 5 completion record as a known, deliberate
consequence for whichever later thread revisits the JAX bridge (`papers/jax_evalplan_architecture.md`
§7.6 thread 5, explicitly unscheduled).

### Task 4 steps

- [ ] Remove `checkPlan`/`CheckedEvalPlan` from `Check.lean` (`admittedVersion` was already removed
      in Task 1); remove `runDensePlan` from `Dense.lean`. Also remove `Error.lean`'s
      `PlanError.scanStepNotYetSupported` — Task 1's temporary interim placeholder (ledger ruling),
      now dead once `checkPlan`'s real scan dispatch lands here.
- [ ] Create `EvalPlan.lean` with `CheckedPlanStepEvidence`, `PlanStepError`, `PlanStep.sourceSlots`/
      `destinationSlots`, the relocated/generalized `checkPlan`, and the relocated/generalized
      `runDensePlan` (drafted above; verify via a real `lake build` — this cross-file wiring is the
      one piece this plan could not pre-verify with `check-snippet.sh`, per Global Constraints).
- [ ] Update `Error.lean`: `PlanCompileCause.invalidPlan`'s payload type to `PlanStepError`.
- [ ] Update `Compile.lean`: import `EvalPlan` instead of relying on `Check`/`Dense` for `checkPlan`
      (the `steps :=`/`version :=` part of this already landed in Task 1, ledger ruling — do not
      redo it); update `liftPlanError` (or whatever it's actually named/shaped — check first) for
      the new `PlanStepError` type.
- [ ] Update `Prepared.lean`, `Adapter.lean`: import `EvalPlan` wherever `Check`/`Dense` were relied
      on transitively for `checkPlan`/`CheckedEvalPlan`/`runDensePlan`.
- [ ] Migrate the 21 test-literal sites (table above) in `GraphCheckTest.lean`, `GraphDenseTest.lean`,
      `ExecutableTest.lean`, `KernelCheckTest.lean`: drop `version :=`, wrap each `steps` entry in
      `.assign`, delete the now-inapplicable `versionNotAdmitted` mutation fixture.
- [ ] Fix `CompileTest.lean`'s direct-field-access sites (a different shape from the four above — see
      Migration inventory note): pattern-match each `p.plan.raw.steps[0]!` access on `.assign`/`.scan`
      rather than projecting `.terms`/`.contextShape` straight off a `PlanStep`.
- [ ] Create `test/Eval/Plan/EvalPlanTest.lean`: a scan-containing outer graph (reuse Task 3's
      linear-scan fixture as one `PlanStep.scan` node, composed with a plain `PlanStep.assign` node
      reading the scan's output) proving multi-output outer-graph wiring — accept case, plus
      mutations for: a plain step reading a scan's state destination before the scan step runs
      (`invalidForwardRead`), two steps (any mix of `.assign`/`.scan`) both targeting the same outer
      slot (`duplicateDestination`), and a scan step's `checkScanPlan` failure surfacing correctly as
      `PlanStepError.scan`.
- [ ] Add `"Eval.Plan.EvalPlanTest"` to `lakefile.toml`; add `import LeanNCD.Eval.Plan.EvalPlan` to
      `LeanNCD.lean`.
- [ ] Confirm (do not assume) that `Executable.lean` still compiles unchanged — its only touchpoint
      with the migrated types is `candidate.source.plan.raw.steps.size` (a `Nat`), verified by grep
      before this plan was written; re-verify after the migration lands.

**Gate:** every existing Wave C plan/graph test passes under the new `PlanStep`-shaped construction
(scan-free plans retain Wave C behavior exactly); a scan-containing outer graph checks and executes
correctly end-to-end through `checkPlan`/`runDensePlan`; malformed multi-output wiring is rejected;
`lake build` green (`Tests` target); `lake build JaxExperiment` is allowed to fail, and that failure
is recorded, not silently left for someone to discover.

---

## Task 5: Discoverability, whole-branch review, and completion record

- [ ] Confirm `RawStep.lean`, `Scan.lean`, `EvalPlan.lean` are all reachable from `import LeanNCD`
      (added in Task 1/3/4 above; re-verify here as a single pass across all three).
- [ ] Update `LeanNCD/Eval/AGENTS.md`'s `Plan/` file table and count to include the three new files.
- [ ] Full-build job count: run `lake build` clean and record the exact job count (matching F0/F1/F2's
      own completion-record convention).
- [ ] Whole-branch review per `superpowers:subagent-driven-development`'s own guidance: this is the
      tier that caught F2's wiring-loop duplication claim and Wave C's capability-matrix
      contradiction — do not skip it even though every per-task review above already ran. Specific
      things to check that no single task's own review would catch: (a) does `EvalPlan.lean`'s
      `checkPlan` genuinely compose `checkAssign`/`checkScanPlan` without re-deriving either's
      obligations, the way F2's own record required verifying for `checkPlanBlock`/`checkPlan`; (b)
      does the causality certificate's absence of a stored field (Task 2's design note) actually
      hold up — is there any path where a `CheckedScanPlan` could exist without the causality loop
      having run against ITS OWN `raw`, not some other plan's; (c) diff every "X reuses Y" and "no
      second Z" claim in this plan's own Architecture section against the actual landed code, per
      the `slice-plan` skill's own rule.
- [ ] Append an "F3 completion record" under `papers/wave_f_scanplan_proposal.md` §13, following the
      F0/F1/F2 convention: what actually landed, the exact file list, the `lake build` job count, and
      explicitly recording the `JaxExperiment` breakage (Task 4) as a known, deliberate, unfixed
      consequence for a later thread.
- [ ] Update `papers/jax_evalplan_architecture.md`'s Wave F reference if its wording (currently:
      "the checked block and scan layers (F2-F4) have not [landed]") needs updating now that F2+F3
      have.

**Gate:** Laws 1 (N/A — no source compiler yet), 2, and 6 hold for every hand-built checked scan in
this slice's own test suite; Law 4's boundary claim is out of scope until F4 introduces named scan
bindings. `import LeanNCD` reaches every new file. F4 can build source-scan compilation directly on
top of `checkScanPlan`/`runDenseScan` without importing anything from this slice's test files.

---

## Definition of Done

- [ ] All five tasks' gates pass.
- [ ] `lake build` (default targets `LeanNCD`, `Tests`) is green.
- [ ] The source compiler still rejects every `.scan`/`.scanPre` exactly as before this slice (no
      accidental admission).
- [ ] Every scan-free existing plan/graph/block/kernel test still passes unchanged in observable
      behavior (only its `RawEvalPlan` construction syntax changes, per the migration table).
- [ ] The F3 completion record is appended, including the `JaxExperiment` disclosure.
