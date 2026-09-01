# Slice 5 — predicate factors and axiswise masks in the checked `EvalPlan` backend

> **For agentic workers:** REQUIRED SUB-SKILL: use
> `superpowers:subagent-driven-development`. Author-side verification of every
> Lean block, path, and fixture value in this plan followed
> `.claude/skills/slice-plan`. Run implementers and reviewers at high effort with
> long context. This is a real implementation slice (not a disposable spike): all
> code lands and stays.

**Goal:** Close item 5 of
[`backend_missing_functionality.md`](../../../papers/backend_missing_functionality.md)
— admit Iverson predicate factors and axiswise `where=` masks in the checked
`EvalPlan` backend, to bit-parity with the reference interpreter. Item 4
(Boolean/predicate tensors) is a **separate later slice** and is out of scope
here.

This plan operationalizes §6 (Tasks 5.0–5.4) of the design proposal
[`predicate_boolean_backend_parity.md`](../../../papers/predicate_boolean_backend_parity.md),
whose coordinate policies were validated by the disposable
[`predicate coordinate-parity spike`](../../../papers/predicate_coordinate_parity_spike_results.md).
Read the design proposal first; this plan does not restate its rationale, only
the executable steps, verified against the tree at authoring time.

## Provenance of this plan's claims

Every factual claim below was **measured against the tree at `6feb958`** during
authoring (not inherited from the proposal's prose). Re-measure anything a task
depends on before restating it.

| Claim | How verified this session |
|---|---|
| All named production/test paths exist | `test -e` over every path in every task's Files list |
| Core new types compile | `check-snippet.sh` on the §"Verified core types" block below — COMPILES |
| `JaxExperiment` is currently red | `lake build JaxExperiment` → 8 errors + 1 `sorry` cascade (see Task 5.0) |
| `TermPlan.factors` consumers | `grep -n '\.factors'` over `leanncd/LeanNCD/Eval/Plan/*.lean` (see §Migration blast radius) |
| Rejection producers | `grep` for `maskOrPredicate` / `maskedAxiswiseNotSupported` in `LeanNCD/` (see Task 5.2/5.3) |
| Locator surfaces coincide today | read of each factor loop: every one indexes `t.factors` and accesses `.sourceSlot`; all factors are reads today, so all-factor index == filtered-read index |
| Last measured full build | 8659 jobs at `cd497c6` (docs-only commits since do not touch Lean) — re-measure at worktree prep |

## Global constraints

- **Behavior for existing programs is byte-for-byte preserved.** Every currently
  green fixture stays green with identical values. New capability is additive.
- **One private lowering core, two public entry points.** A private recursive
  `BoolExpr → PosBoolExpr` core takes an ordered basis and pin map. Compiler call
  sites reach it only through `lowerFactorPredicate` (factor policy:
  `context ++ output ++ per-term reduction`, real pins) and `lowerMaskPredicate`
  (mask policy: local non-seeded output basis, empty pins). No call site reaches a
  generic basis-and-pins entry point directly.
- **No new field on `ScheduledProgram` or persistent checked-plan IR** for
  coordinate context. Extract a private compiler-local helper/structure only if
  completed wiring shows identical derivation at ≥2 sites, and record the
  duplicated expressions it replaces.
- **Positional predicate IR is UID-free.** `PosPredArith`/`PosBoolExpr` contain no
  `AxisSpec`, UID, axis name/kind, tensor name/slot, or source `IdxExpr`/`PredArith`/`BoolExpr`.
- **`TermPlan.factors` becomes one ordered `Array FactorPlan`** (`read | iverson`),
  never two parallel arrays. Every filtered traversal keeps the **original
  all-factor index**, never a reindexed filtered-read index.
- **Capability constructors kept producer-less.** After their last producer is
  removed, `CapabilityError.maskOrPredicate` and
  `NonlinCompileError.maskedAxiswiseNotSupported` remain as compatibility
  constructors (same discipline as `scanNode`, `numericModeNotAdmitted`).
- **No source `BoolExpr` retained in checked IR; no predicate truth tables; no
  `RawAxiswisePlan` mask broadening to scan context; no `ieq`-approximation
  change; no JAX predicate/mask execution; no Boolean-tensor work.**
- **Verification gate (every task):** `cd leanncd && "$HOME/.elan/bin/lake" build`
  succeeds; stay `sorry`-free; add no `maxHeartbeats`/`native_decide`. Last
  measured baseline: 8659 jobs (re-measure at worktree prep and record it).
- **Commit trailer:** end every commit body with
  `Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>`. Do not
  push or PR unless asked. Re-grep before editing; cite identifiers, never
  `File.lean:NNN`, in any shipped text (completion records, AGENTS rows, design-doc edits).

## Verified core types (compiles as one block via `check-snippet.sh`)

These land in `Eval/Plan/Kernel.lean` (types) and `Eval/Plan/Dense.lean`
(evaluator). Reuse the exact shapes below — they compiled verbatim this session
(and are the spike's proven forms with the "temporary" comments dropped). Any
reformatting during assembly must be re-checked with `check-snippet.sh`.

```lean
-- in Eval/Plan/Kernel.lean (namespace LeanNCD.Eval.Plan; RelOp is LeanNCD.RelOp)
/-- One affine predicate leaf over a positional iteration coordinate. -/
structure PosAffine where
  coeffs : Array Int
  bias : Int
  deriving DecidableEq, BEq, Repr, Inhabited

/-- UID-free predicate arithmetic. -/
inductive PosPredArith
  | affine : PosAffine → PosPredArith
  | mul : PosPredArith → PosPredArith → PosPredArith
  | iabs : PosPredArith → PosPredArith
  deriving DecidableEq, BEq, Repr, Inhabited

/-- UID-free Boolean predicate. -/
inductive PosBoolExpr
  | rel : RelOp → PosPredArith → PosPredArith → PosBoolExpr
  | and : PosBoolExpr → PosBoolExpr → PosBoolExpr
  | or : PosBoolExpr → PosBoolExpr → PosBoolExpr
  | not : PosBoolExpr → PosBoolExpr
  | ieq : PosPredArith → PosPredArith → PosBoolExpr
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Ordered factor: a tensor read or a positional Iverson predicate, in source order. -/
inductive FactorPlan
  | read : ReadPlan → FactorPlan
  | iverson : PosBoolExpr → FactorPlan
  deriving DecidableEq, BEq, Repr, Inhabited
```

`TermPlan.factors` changes from `Array ReadPlan` to `Array FactorPlan`; every
other `TermPlan` field is unchanged. The positional evaluator (`evalPosAffine`
rejects unequal widths with `PosPredicateError.affineWidthMismatch`,
`evalPosPredArith`, `evalPosBool`) is the spike's verified form; it imports
neither `Eval.Gather` nor the source `evalPred`/`evalBool`. `PosPredicateError`
is the **Dense runtime** evaluator's error only. The **checker** does not use it:
the `.iverson` width check in `checkAssign` reuses the existing
`PlanError.affineWidthMismatch termIndex factorIndex expected actual` (already
thrown for read affine rows), so predicate and read width failures carry the same
`(ti, fi)` locator.

## Migration blast radius (verified `.factors` consumers)

Task 5.1 must update every one of these and nothing else silently. `fi`/`ni`/`ti`
denote factor/node/term indices in the diagnostics each throws.

| Site (identifier) | Current shape | Required change | Locator risk |
|---|---|---|---|
| `Check.checkAssign` factor loop | `for fi in t.factors`; dtype/shape/rank/width on `f.sourceSlot`, errors carry `(ti, fi)` | match `.read` → existing checks; add `.iverson` arm checking each leaf width == `iterationShape.size`; keep `fi` = all-factor index | **yes** |
| `Block.checkPlanBlock` sourceCheck | `for fi in t.factors`; `invalidForwardRead ni ti fi f.sourceSlot` | skip `.iverson` (no slot), keep `fi` | **yes** |
| `EvalPlan` top-level sourceCheck | `for fi in t.factors`; `invalidForwardRead ni ti fi` | skip `.iverson`, keep `fi` | **yes** |
| `Compile` source scan causality (`checkScanPlan`) | `for fi in t.factors`; `stateReadNotCausal … ri ti fi` on `f.sourceSlot`; `ri` iterates `stepAssignPlans` (already assignment-filtered) | skip `.iverson`, keep `fi` | **yes** (`fi` only; admitted in 5.2) |
| `Scan.checkScanPlan` checked scan causality | `for fi in t.factors` over an **unfiltered** `stepBlock.steps` loop (`ai`); `causalityFailure si ai ti fi` on `f.sourceSlot` | skip `.iverson`, keep `fi`; `ai` already counts all block steps | **yes** (`fi`; `ai` already correct) |
| `Dense.runDenseAssignAt` factor fold | `for f in t.factors` / `factors.toList.mapM gatherFactor` | `.read` → gather; `.iverson` → evaluate `PosBoolExpr` to `1.0`/`0.0` against the built iteration coordinate | value |
| `EvalPlan` source-slot collect (`.factors.map (·.sourceSlot)`) | flat-maps every factor's slot | `filterMap` read factors only | wiring |
| `RawStep` source-slot collect (`.factors.map (·.sourceSlot)`) | flat-maps every factor's slot | `filterMap` read factors only | wiring |
| `Executable` affine-table / einsum candidate | `tables.size == term.factors.size`; `term.factors.zip tables/operands` | candidate valid only when every factor is `.read`; otherwise not an affine/einsum candidate | value |
| `Compile.residualizeAssignment` build loop | pushes `ReadPlan` into `factorsAcc : Array ReadPlan` | push `FactorPlan.read`; the `.iverson` arm stays rejected until 5.2 | build |

**The locator trap (why fixtures must force `fi` apart):** today every factor is
a read, so the all-factor index and any filtered-read index are equal in every
existing fixture; a migration that reindexes filtered reads passes the entire
current suite and regresses silently. Each **yes** row above therefore needs a
fixture whose term places a non-read factor *before* the failing read, so the two
readings diverge (correct reports the larger all-factor index).

## Task map and sizing

| Task | Deliverable | New fixtures | Mutation cycles | Depends on | Rollback unit |
|---|---|---:|---:|---|---|
| 5.0 | Restore `JaxExperiment` baseline | 4 | 2 | — | yes |
| 5.1 | `FactorPlan` migration + checker + Dense + direct fixtures + JAX Iverson rejection | 8 | 5 | 5.0 | yes |
| 5.2 | Admit source Iverson via `lowerFactorPredicate` | 8 | 6 | 5.1 | yes |
| 5.3 | Axiswise masks + shared nonlinear callback via `lowerMaskPredicate` + JAX mask rejection | 14 | 8 | 5.1 | yes |
| 5.4 | Independent oracle, predicate corpus, JAX gates | 12 curated | 6 | 5.2, 5.3 | yes |

Each task touches existing production code with dependents and is a natural
rollback unit that a reviewer could reject while approving its neighbor, so none
merge. 5.2 and 5.3 both branch from 5.1 and both edit `Compile.lean`; land them
**serially** (5.2 then 5.3) — never two concurrent branches over
`residualizeAssignment`/nonlinear construction. Begin **Task 5.4's scan-free
oracle design and curated scan-free cases in parallel** with 5.2/5.3 (per the
"sequence expensive independent verification early" discipline), integrating its
scan Iverson/mask cases as 5.2/5.3 land.

The costly tasks are 5.3 (14 fixtures × mutation cycles) and 5.4 (a from-scratch
oracle leg); size their dispatches to fixture/mutation count, not diff size.

---

## Task 5.0 — Restore the optional `JaxExperiment` baseline

**Why (measured at `6feb958`):** `lake build JaxExperiment` fails with, in order:
`CheckedPlanStepEvidence.plan` projected but absent (two sites); a non-exhaustive
match (`Missing cases`); an application type mismatch; `RawEvalPlan.version` and
`RawEvalPlan.numericMode` no longer fields (two sites); and a `sorry`/error
cascade through `JaxBridge.idRaw`. This is pre-existing rot, not caused by this
slice; repair it first so later tasks can gate on a green optional target.

**Files:** `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`.

**Deliverable:** pattern-match every `CheckedPlanStepEvidence` case; route
assignment steps through the existing affine/einsum path; reject pointwise,
axiswise, and scan steps with one located unsupported-step error; make
compile-cause rendering exhaustive; drop obsolete `RawEvalPlan` fields and wrap
fixture assignments in `PlanStep.assign`. No predicate/Boolean support here.

**Fixtures (4) / mutation cycles (2):** each rejection fixture puts a **valid
assignment at step index 0** and the unsupported step at **index 1**, so the
required location `1` is not tautological, and builds a proper payload (a
`.pointwise`/`.axiswise`/`.scan` step cannot be a repackaged `AssignPlan` — their
constructors take `RawPointwisePlan`/`RawAxiswisePlan`/`RawScanPlan`).

| Fixture | Donor / construction | Distinguishes |
|---|---|---|
| Identity assignment still emits | existing `idRaw` fixture, repaired to `PlanStep.assign` | assignment path intact |
| Pointwise step rejected, located | `[assign@0, pointwise@1]` with a minimal `RawPointwisePlan` | unsupported-step location = 1, not 0 |
| Axiswise step rejected, located | `[assign@0, axiswise@1]` with a minimal `RawAxiswisePlan` | unsupported-step location = 1 |
| Scan step rejected, located | `[assign@0, scan@1]` with a minimal valid `RawScanPlan` | unsupported-step location = 1 |

Mutation cycles: (1) replace the located unsupported-step error with a catch-all
that hardcodes location 0 → the three rejection fixtures (each at index 1) must
fail; (2) route a pointwise step through the assignment path → the pointwise
fixture must fail. Record failing and restored-passing observations.

**Gate:** `cd leanncd && "$HOME/.elan/bin/lake" build JaxExperiment` green before
Task 5.1. Record its job count.

---

## Task 5.1 — Introduce the ordered positional factor IR

**Deliverable:** add `PosAffine`/`PosPredArith`/`PosBoolExpr`/`FactorPlan` and the
positional evaluator (the verified core-types block above); migrate `TermPlan.factors`
to `Array FactorPlan`; update every consumer in the blast-radius table; add an
`.iverson` width check in `checkAssign` that reuses the existing
`PlanError.affineWidthMismatch ti fi expected actual` (each `PosBoolExpr` leaf
width == `iterationShape.size`);
add direct checked-plan fixtures; wrap existing direct `ReadPlan` factor literals;
establish the located experimental-JAX rejection for `FactorPlan.iverson` and make
affine-corpus feature extraction inspect read factors explicitly. **Source Iverson
stays rejected** (that admission is Task 5.2) — but hand-built direct `AssignPlan`
values carrying `FactorPlan.iverson` are how this task's checker/Dense fixtures are
built.

**Production files (all verified to exist):** `Eval/Plan/Kernel.lean`,
`Eval/Plan/Error.lean`, `Eval/Plan/Check.lean`, `Eval/Plan/Dense.lean`,
`Eval/Plan/RawStep.lean`, `Eval/Plan/Block.lean`, `Eval/Plan/EvalPlan.lean`,
`Eval/Plan/Scan.lean`, `Eval/Plan/Compile.lean`, `Eval/Plan/Executable.lean`,
`experiments/jax_bridge/EvalPlanCodegen.lean`,
`experiments/jax_bridge/EvalPlanAffineCorpus.lean`.

`Compile.lean` changes here are mechanical: `residualizeAssignment` pushes
`FactorPlan.read`; its `.iverson` arm still throws `maskOrPredicate` (removed in
5.2). No `lowerFactorPredicate` yet.

**Mechanical fixture migration:** wrap direct `ReadPlan` factor literals in
`FactorPlan.read`. The current direct-plan set (verify by type-directed search;
do not treat as closed) includes `BlockTest`, `CheckedPrivacyTest`, `CompileTest`,
`EvalPlanTest`, `ExecutableTest`, `GraphCheckTest`, `GraphDenseTest`,
`KernelCheckTest`, `KernelDenseTest`, `NonlinCompileTest`, `NonlinDenseTest`,
`ScanCompileTest`, `ScanTest`. Re-grep after migration.

**Required review artifact — the factor-kind × consumer table.** Produce it from
the implemented code and classify every cell **required / forbidden / silently-ignored**.
Pre-filled below from this session's reads; the implementer confirms each cell and
turns every *silently-ignored* cell into either a distinguishing fixture or a
justified no-op. Every silently-ignored cell is a candidate locator bug.

| Consumer | Plain read | Unary read | Iverson |
|---|---|---|---|
| Source-slot discovery (`EvalPlan`, `RawStep` `.map (·.sourceSlot)`) | required | required | forbidden — `filterMap` skips |
| Runtime store validation (`Dense.gatherFactor`) | required | required | forbidden — evaluate predicate, no store read |
| Source dtype/shape (`Check.checkAssign`) | required | required | forbidden — skip, keep `fi` |
| Predicate width (`Check`, new arm) | n/a | n/a | required — leaf width == `iterationShape.size`, report `(ti, fi)` |
| Outer forward-read (`EvalPlan`) | required | required | forbidden — skip, keep `fi` |
| Block forward-read (`Block`) | required | required | forbidden — skip, keep `fi` |
| Scan capture discovery | required | required | forbidden — no slot |
| Source scan causality (`Compile.checkScanPlan`) | required | required | forbidden — skip, keep `fi` (exercised in 5.2) |
| Checked scan causality (`Scan`) | required | required | forbidden — skip, keep `fi` |
| Affine-table candidate (`Executable`) | required | required | forbidden — any Iverson ⇒ not a candidate |
| Einsum/JAX lowering (`Executable`, `EvalPlanCodegen`) | required | required or located reject | forbidden — located reject |
| Corpus feature extraction (`EvalPlanAffineCorpus`) | required | required | forbidden — inspect reads explicitly |

**New fixtures (8) / mutation cycles (5):** all direct checked-plan fixtures
(hand-built `AssignPlan`/blocks), since source Iverson is still rejected. Each
locator fixture places a non-read factor *before* the failing read so the
all-factor index diverges from a filtered-read index.

| Fixture | Donor + one-field change | Distinguishes |
|---|---|---|
| Accepted positional Iverson | `KernelCheckTest.goodPlan`; insert a correctly-sized `FactorPlan.iverson` between its two reads | predicate checker path accepts |
| Predicate-width locator | same donor; the inserted predicate has a leaf of width ≠ `iterationShape.size`, placed at all-factor index 1 | `affineWidthMismatch ti fi` reports `fi=1`, **not** a filtered-predicate index 0 |
| Read-after-predicate locator | `KernelCheckTest.goodPlan`; make the term `[iverson, read(bad shape)]` | `sourceShapeMismatch ti fi` reports `fi=1` (all-factor), **not** filtered-read 0 |
| True predicate execution | accepted fixture (`KernelDenseTest`); predicate true at the coordinate | contributes `1.0` |
| False predicate execution | same; predicate false | annihilates the term (`0.0`) |
| Outer forward-read locator | `EvalPlanTest.termLocatorPlan` (already pins `invalidForwardRead 0 1 0 1`); make its failing term `[iverson, read(forward)]` | `invalidForwardRead ni ti fi` reports `fi=1`, not filtered-read 0 |
| Block forward-read locator | `BlockTest.forwardReadBlock`; failing term `[iverson, read(forward)]` | block `invalidForwardRead ni ti fi` reports `fi=1`, not 0 |
| Checked-scan causality double locator | `ScanTest.stepBlockNonlinBetweenAssignsG` (already pins `blockStepIndex`); make the noncausal assignment's term `[iverson, read(noncausal state)]` | `causalityFailure si ai ti fi` reports the all-block-step `ai` **and** all-factor `fi=1` — both diverge from filtered indexings at once |

Locator note: `Compile.checkScanPlan`'s `ri` is already a `stepAssignPlans`
(assignment-filtered) index and non-assignment steps never enter it, so its
`stmtIndex` is unambiguous *there* (exercised in 5.2 for `fi` only). The block
`ni` (`Block`/`EvalPlan`) and the checked-scan `ai` (`Scan`) already count all
steps correctly; the new hazard everywhere is `fi`, and the checked-scan fixture
above forces `ai` and `fi` apart simultaneously (the §9.3 "both at once" case).

Mutation cycles (5): (1) reindex filtered reads in the `Check` loop →
"Read-after-predicate locator" fails; (2) reindex filtered reads in the block
forward-read loop → "Block forward-read locator" fails; (3) reindex filtered reads
in `Scan.checkScanPlan` → "Checked-scan causality double locator" fails; (4) drop
the predicate-width check → "Predicate-width locator" loses its rejection; (5) make
`Dense` treat a false predicate as `1.0` → "False predicate execution" fails. Each:
show the diff, observe the failure, restore, observe pass.

**Validation:**
```bash
cd leanncd && "$HOME/.elan/bin/lake" build      # full suite; must stay green + JaxExperiment
cd leanncd && "$HOME/.elan/bin/lake" build JaxExperiment
```

---

## Task 5.2 — Admit and residualize source Iverson predicates

**Deliverable:** remove the two `.iverson` rejection producers —
`checkFactor`'s preflight `maskOrPredicate` and the defensive
`residualizeAssignment` `.iverson` arm — and translate the existing UID-bearing
`BoolExpr` into `PosBoolExpr` through a new **`lowerFactorPredicate`** entry point.
It receives `contextUids`, `outputUids`, the pin map, the term, and the predicate;
derives that term's first-encountered reductions via `termAxisUIDs`; builds the
basis `context ++ output ++ reduction`; and invokes the **private** recursive core,
which lowers each embedded `IdxExpr` with `idxToRow` then `substitutePins`. Keep
`substitutePins` private; do not duplicate it. Keep `CapabilityError.maskOrPredicate`
producer-less.

**Files (verified):** `Eval/Plan/Compile.lean`, `test/Eval/Plan/CompileTest.lean`,
`test/Eval/Plan/ScanCompileTest.lean`, `test/Eval/Plan/DifferentialTest.lean`,
`test/Eval/Plan/AdapterTest.lean`.

**New fixtures (8) / mutation cycles (6):** these are source→checked differential
parity fixtures; the source value is observable now (spike-measured where noted)
and the checked side must match it.

| Fixture | Donor + change | Source value (observed) | Distinguishes |
|---|---|---|---|
| Pure Iverson | `RelationalTest` RL1, unchanged | identity `[1,0,0,0,1,0,0,0,1]` | predicate-only axes, output basis |
| Retained/reduction order | `RecurrenceTest` RC3, unchanged | `[1,3,6]` | output before reduction in `[i,j]` |
| Multiple reductions | `CompileTest.multiReductionSched`; append `[j < k]` | (differential) | first-seen reduction order `j` then `k` |
| UID not name | `DifferentialTest.sameAxisNameSched`; add a predicate comparing the two same-named `l` axes (distinct UIDs) | (differential) | identity by UID, not name |
| Scan base Iverson | convert base-side `ScanCompileTest.badIverson` (currently a rejection) to an accept | (differential) | base-block admission + pins |
| Scan recurrence Iverson | convert recurrence-side `badIverson` to an accept | (differential) | recurrence admission + live context to the factor |
| Pin + context residualization | base leg from the second base assignment of `ScanCompileTest.multiBaseSched` (pin `r:=1`); recurrence leg from a `badIverson … nextL`-shaped accept; predicate uses nested `mul`/`iabs` over the base pin and a recurrence context axis | (differential) | pins folded into leaf bias; context kept |
| Source causality factor locator | clone `ScanCompileTest`'s term-1/factor-1 `stateReadNotCausal` fixture (the `… "S" 0 1 1` case); insert an Iverson **immediately before** the noncausal state read | error stays `stateReadNotCausal … ti=1 fi=2` | all-factor `fi=2`, **not** filtered-read `fi=1` |

The last fixture is the load-bearing locator for this task: without the inserted
Iverson, factor index and read index coincide (they do in the donor); with it,
the noncausal read moves to all-factor index 2 while a filtered-read indexing
would report 1. Verify the donor's payload is `(scan, "S", stmtIndex, termIndex=1,
factorIndex)` and that the accepted-then-broken construction still fires
`stateReadNotCausal`.

Mutation cycles (6): (1) resolve predicate axes by name → "UID not name" fails;
(2) swap output/reduction basis order → "Retained/reduction order" fails; (3)
reverse the two reductions → "Multiple reductions" fails; (4) omit `substitutePins`
in predicate leaves → "Pin + context residualization" fails; (5) drop Iverson
factors entirely in Dense → "Pure Iverson" fails; (6) reindex filtered reads in
`checkScanPlan` → "Source causality factor locator" fails. Record each.

**Validation:** full `lake build`; the `DifferentialTest` sweep and scan corpus
counts must be unchanged except for the intended new accepts.

---

## Task 5.3 — Axiswise masks and the shared nonlinear callback

**Deliverable:** add `mask : Option PosBoolExpr := none` to `RawAxiswisePlan`; add
its checker (each mask leaf width == `shape.size`) and Dense adapter; lower source
masks through a new **`lowerMaskPredicate`** entry point (local non-seeded output
basis, **empty** pins supplied internally so a caller cannot pass factor context or
base pins) at all three compiler construction sites; remove the
`resolveNonlinAxis` masked-axiswise rejection; refactor the private row worker in
`Eval/Nonlin.lean` around a **full-coordinate → included?** callback shared by the
source wrapper (evaluates `BoolExpr`) and the checked adapter (evaluates
`PosBoolExpr`), keeping one implementation each of softmax/normalize/L2; and add the
complete-step JAX support check routing the checked axiswise case to the generic
unsupported-step error. Keep `NonlinCompileError.maskedAxiswiseNotSupported`
producer-less. Do **not** add a `RawAxiswisePlan` mask-axis-UID field; the local
`shape` gives the positional width.

**Files (verified):** `Eval/Nonlin.lean`, `Eval/Plan/Nonlin.lean`,
`Eval/Plan/Compile.lean`, `experiments/jax_bridge/EvalPlanCodegen.lean`,
`test/Eval/Plan/NonlinCheckTest.lean`, `test/Eval/Plan/NonlinDenseTest.lean`,
`test/Eval/Plan/NonlinCompileTest.lean`, `test/Eval/Plan/ScanCompileTest.lean`.

**New fixtures (14) / mutation cycles (8).** Source→checked differential unless a
literal is given; observed values are spike-measured where noted.

| Fixture | Donor + change | Value / distinguishes |
|---|---|---|
| Top-level masked normalize | `NormTest` NM4, unchanged | `[0,.4,.6,0,.5,.5]` (observed); inclusion polarity + local basis |
| Non-last mask basis | `NormTest` NM5; add asymmetric `where s < q` | swapping `s`/`q` positions changes the result (locator for basis order) |
| Masked softmax | NM4; change only the function | differential |
| Masked L2 normalize | NM4; change only the function | differential |
| Three all-masked rows | NM4; `where s < 0`, once per axiswise fn | all-masked row → zeros, not uniform |
| Masked extreme | NM4→softmax; place `1000` in the already-excluded `s=0` entry | excluded value never enters the row maximum (spike-measured `[0,.269,.731,…]`) |
| Masked scan base | convert `ScanCompileTest.maskedAxiswiseBase` (rejection→accept) | base-block mask, non-seeded output basis |
| Masked recurrence | convert `ScanCompileTest.maskedAxiswiseRecur` (rejection→accept) | recurrence mask, non-seeded output basis |
| Seeded-axis-zero parity | recurrence donor; `where l = 0` | seeded `l` absent from the mask basis ⇒ evaluates as zero at every step (spike-measured `[1,3,.25,.75,.25,.75]`) |
| Eliminated free scan coordinate | derive from `ScanGen.template6`; retain a separate `.freeNorm i`; base mask `where r ≠ 0` over the eliminated non-seeded `.free r` | `r` gets its actual coordinate; zeroing it would all-mask the `r=1` face |
| Eliminated `.freeNorm` scan coordinate | exact source `iter r = 2, c = 2; tensor Z(r); G[r.,0] := normalize(where r ≠ 0)(Z[r]); G[r+1,c+1] := G[r,c]`, `Z=[1,3]` | source == checked == hand-expected `[2,2]`/`[0,0,1,0]` (spike-measured) |
| Masked axiswise JAX rejection | compile the top-level masked donor | generic located unsupported-step error before Python emission |
| Unmasked nonlinear unchanged | existing FF/AT/NM unmasked fixtures | the callback refactor changes no unmasked value |
| Mask width locator | a checked axiswise plan with a mask leaf of width ≠ `shape.size` | mask width check reports the mask, not a factor |

The **Eliminated `.freeNorm` scan coordinate** fixture is source-reachable
(occurrence-local axis kinds share one UID: `r` is `.real`/`.freeNorm` in the base
occurrence and `.nat`/`.iterNext` in the recurrence). It is pinned in **this task**
by direct source/checked/hand-expected agreement plus its mutation below — it is
**not** covered by the independent oracle (see Task 5.4).

Mutation cycles (8): (1) invert callback inclusion polarity → "Top-level masked
normalize"; (2) include masked values in the softmax maximum → "Masked extreme";
(3) return a uniform row for an all-masked softmax → "Three all-masked rows"; (4)
substitute live scan context into a recurrence mask → "Seeded-axis-zero parity";
(5) substitute zero for the eliminated `.free r` coordinate → "Eliminated free
scan coordinate"; (6) substitute zero for the eliminated `.freeNorm` coordinate
during lowering → "Eliminated `.freeNorm` scan coordinate"; (7) swap the two mask
positions → "Non-last mask basis"; (8) let the checked axiswise step through JAX →
"Masked axiswise JAX rejection". Record each failing/restored pair.

**Validation:** full `lake build` (all unmasked nonlinear fixtures byte-for-byte
unchanged) and `lake build JaxExperiment`.

---

## Task 5.4 — Independent oracle, predicate corpus, and JAX rejection gates

**Deliverable:** teach the independent scan unroller to rewrite predicate
arithmetic and masks **without importing the implementations it checks**; add a
compact curated predicate parity corpus separate from `enumPrograms`; and exercise
the JAX rejections established by 5.1/5.3.

`ScanUnroll` must recursively substitute `IdxExpr` inside both `PredArith` and
`BoolExpr` occurrences (its `rewriteFactor` currently rejects `.iverson`) using its
own `substIdx`, preserving factor order, with: Iverson factors taking the actual
`sigma` scan coordinate; masks taking zero for every source seed and the actual
enumerated coordinate for an eliminated non-seeded `.free`/`.freeNorm` output
slot; retained output UIDs staying expressions. It must **explicitly reject** an
axiswise operation whose normalization axis is an *eliminated scan coordinate*,
with a named fragment error `ScanUnroll.fragment.eliminatedNormalizationAxis`
(the per-coordinate leaf unroller cannot group those leaves; that case is pinned
directly in Task 5.3, not here). The oracle names only scan-free `evalScheduled`;
it must not call checked predicate lowering, positional evaluation, or checked
scan-worker helpers — audit imports/calls and record the result.

**Files (verified):** `test/Eval/PropertyOracle/Gen.lean`,
`test/Eval/PropertyOracle/ScanGen.lean`, `test/Eval/PropertyOracle/ScanUnroll.lean`,
`test/Eval/PropertyOracle/ScanOracle.lean`, `test/Eval/Plan/DifferentialTest.lean`,
`test/Eval/Plan/ExecutableTest.lean`,
`experiments/jax_bridge/EvalPlanCodegen.lean`,
`experiments/jax_bridge/EvalPlanAffineCorpus.lean`.

Do **not** append predicate/mask cases to `enumPrograms`: the affine JAX corpus
consumes that list wholesale and treats every affine-reference rejection as fatal,
while Iverson/masked programs must now be JAX-rejected. Export a separate compact
`predicatePrograms` list (or an equivalent dedicated list in `DifferentialTest`)
and run the reference/checked differential over it separately; keep the existing
affine corpus's source list and positional indices stable.

**Curated cases (12) / mutation cycles (6):**
- scan-free: RL1, RL6, RL7, RL8, NM4, AT12 (design/build these in parallel with 5.2/5.3);
- scan: recurrence Iverson, masked recurrence, seeded-axis-zero, one base Iverson,
  and the `ScanGen.template6`-derived non-seeded `.free` scan-axis mask;
- JAX: an Iverson inserted at factor index 1 in the `idRaw` family.

Mutation cycles (6): omit Iverson substitution in `ScanUnroll` → three-way scan
oracle disagrees; omit mask substitution → seeded-axis-zero structural check
fails even when values agree; substitute live context into a mask → masked
recurrence disagrees; filter the JAX predicate reject → located JAX rejection
fixture; reindex a predicate corpus case's factors → factor-locator oracle case;
accept the eliminated-normalization-axis shape in `ScanUnroll` → its fragment
rejection fixture. Record each.

---

## Required sibling audits (deliverables, not optional)

- **Factor-kind × consumer table** (Task 5.1): every cell classified
  required/forbidden/silently-ignored, produced from code; every silently-ignored
  cell resolved to a fixture or a justified no-op.
- **Locator preservation** (Tasks 5.1, 5.2): the plan names, and the task must
  ship, a fixture that forces `fi` (all-factor vs filtered-read) apart for each
  **yes** row of the blast-radius table, plus one fixture forcing block-step `ni`
  and factor `fi` apart simultaneously.
- **Unchanged source walkers** (Task 5.2): re-read and record why `Factor.read?`,
  `Stmt.readFactors`/`readNames`, predicate/mask axis traversals, UID relabeling,
  `termAxisUIDs`, `readAxisUIDs`, and size inference remain correct.
- **Executable candidate audit** (Task 5.1): confirm an affine-table/einsum
  candidate is rejected (not silently mis-sized) when any factor is an Iverson,
  and ship direct assertions that both source-slot accessors
  (`PlanStep.sourceSlots` and `BlockStep.sourceSlots`) omit Iverson factors and
  that the affine-table and einsum candidate validators reject any Iverson-bearing
  term. These accessors/validators are unchanged code a diff cannot show, so the
  assertions are the only regression guard.

## Review plan

Per-task reviews for the mechanical/localized tasks (5.0, and the fixture-wrapping
half of 5.1). Then **two independent final whole-branch reviews** with different
lenses (design §12):

1. source/positional semantic parity and oracle independence;
2. checker, scan write/capture/causality, locator, and unchanged-consumer correctness.

The final tier is where this slice's soundness findings will surface (the locator
family is invisible in any single task diff); do not trim it. Fix or adjudicate
every finding.

## Completion record (per task; identifiers only, no line numbers)

Commit SHA; exact commands + exit statuses + job counts; observed fixture values;
before/after `DifferentialTest`/scan-corpus counts; every mutation's failing and
restored-passing observation; the completed factor-consumer and locator tables;
a repo-wide value-grep for any capability-boundary numbers this slice moves; and
the two final-review outcomes. Before declaring the documentation sweep complete,
value-grep the whole repo for any moved capability counts (not just edited files).
