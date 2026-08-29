# Slice T4 — admit nonlinear Plan scans (compiler lowering, oracle agreement, publication)

**Scope:** Task 4 only of
[`papers/nonlinearity_split_pair_direct_lowering.md`](../../../../papers/nonlinearity_split_pair_direct_lowering.md)
(that document's §3.6, "admit nonlinear Plan scans"; its design contract is §2.7 and §2.8). That
document remains the canonical design record; this is the executable plan for its fourth slice.
Read §3.6's opening blockquote (the resolved oracle-value history) and §2.7/§2.8 before executing.

**Deliberately NOT in this slice** (each is a later slice or an already-landed prerequisite, per
CLAUDE.md Rule 13):

| Master-plan task | Deliverable | Owned by |
|---|---|---|
| Task 5 | differential documentation for the new shapes beyond the corpus rebaseline, stale-document sweep, whole-branch closure | a later slice |
| Task 3 (done) | the general `BlockStep` vertical slice this task builds on | merged (`65e27ce` … `bc6cdf5`); its execution record is [`2026-08-27-nonlinearity-t3-blockstep-migration.md`](./2026-08-27-nonlinearity-t3-blockstep-migration.md) §6 |
| Step 10 (done) | the independent unroller's `.freeNorm` preservation (`buildGeom`/`baseFreeSlots`) | merged (`5fab993`); §0.5 re-verifies it, this slice does **not** re-implement it |

This slice changes production `Compile.lean` (`checkNonlinScanBlock`, `checkScanLHSSlot`,
`checkScanBlockStmt`, and `compileScan`) and adds fixtures to the checked-Plan, independent-oracle,
and differential test files. It does **not** touch `DSL/*`, the `RouteFragments`/route layer, or the
`BlockStep`/`checkStepGraph` types Task 3 already generalized — a nonlinear scan statement reaches a
`.pointwise`/`.axiswise` **block step** through Task 3's machinery, which is why that machinery must
already exist before this slice runs.

---

## §0 Verified baseline

Executed in this worktree against `main` at `5fab993` on 2026-08-28. Re-run this section before
editing; a failure here is base drift, not an implementation defect. `lake` is invoked as
`"$HOME/.elan/bin/lake"` from `leanncd/` throughout (it is not on `PATH`).

### 0.1 The four production gates reproduce their job counts exactly

```bash
cd leanncd
"$HOME/.elan/bin/lake" build Eval.Plan.CompileTest Eval.Plan.ScanCompileTest Eval.Plan.ScanTest Eval.Plan.DifferentialTest
"$HOME/.elan/bin/lake" build Eval.PropertyOracle.ScanOracle Eval.PropertyOracleScanTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

| Command | Result | Jobs |
|---|---|---:|
| `CompileTest ScanCompileTest ScanTest DifferentialTest` | pass | 8,525 |
| `Eval.PropertyOracle.ScanOracle Eval.PropertyOracleScanTest` | pass | 8,505 |
| `Tests` | pass | 8,657 |
| `LeanNCD` | pass (one pre-existing unrelated `Agreement.lean` linter warning) | 8,543 |

Do not compare counts across rows — the module sets differ and a cross-row mismatch is not drift.

### 0.2 The 17-case scan corpus is at 9 / 4 / 4, the split this slice moves

`DifferentialTest.lean`'s gate prints, and asserts, the curated corpus split:

```
DifferentialTest scan corpus: total=17 accepted=9 unsupportedNonlin=4 unsupportedAgg=4
```

The assertion pinning it is `scanCorpusSplit`'s `run_cmd`, currently
`unless total == 17 && accepted == 9 && nonlin == 4 && agg == 4`. The four `unsupportedNonlin`
cases are `ScanGen.lean`'s `template2` (the ReLU-scan template); admitting nonlinear scan sources
moves them to `accepted`, giving **13 / 0 / 4**. This is the only corpus count this slice changes,
and only after observing the exact new split (Task 1).

### 0.3 The capability is genuinely absent today — the reject sites this slice opens

The three preflight sites, read directly (not inferred), all currently reject nonlinear scan
sources — so a fixture asserting acceptance fails today and will only pass once Task 1 lands:

- `checkNonlinScanBlock` (`Compile.lean`): `.pointwise _` and `.axiswise ..` both
  `throw (.unsupportedNonlin …)`. Contrast `checkNonlinTopLevel` in the same file, which already
  admits both — Task 1 makes the scan-block checker match it.
- `checkScanLHSSlot` (`Compile.lean`): `.freeNorm a => throw (.unsupportedLhsSlot …)`. Contrast
  `checkLHSSlot`, which already admits a top-level `.freeNorm`.
- `compileScan` (`Compile.lean`): assembles `baseAssigns.map .assign` and `stepAssigns.map .assign`
  — every block step is `.assign`, and the `.freeNorm` LHS arms in its base-write and step-write
  loops are marked `unreachable` because preflight rejected `.freeNorm` upstream.

The live `unsupportedNonlin=4` corpus count in §0.2 independently confirms the reject path is real.

### 0.4 The six oracle-group programs reproduce their recorded legacy values

```bash
cd leanncd
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/OracleFixtureSeed.lean
```

Observed, byte-identical to §3.6's fixture list and the seed README's "Oracle fixture authoring":

```
FIXTURE 1: S shape [2, 3] = #[-1.000000, 2.000000, 0.000000, 2.000000, 6.000000, 18.000000]
FIXTURE 2: S shape [3, 2, 3] = #[1, 0, 0, 3, 0, 0, 0, 0.25, 0, 0, 0.75, 0, 0, 0, 0.25, 0, 0, 0.75]
FIXTURE 3 ADOPTED: SOURCE ASSERTIONS PASSED (test/Eval/ScanTest.lean; ReLU-scan asserts S = [1, 0])
FIXTURE 4: S shape [2, 3] = #[0, 0, 0, 3, -3, 3]
FIXTURE 5: S shape [3] = #[1, 6, 0]
FIXTURE 6 ADOPTED: SOURCE ASSERTIONS PASSED (EvalExamplesTest example 5; asserts G=[1,3,6], H=[2,3,6])
```

These are the values every checked-Plan and independent-oracle assertion in this slice must
reproduce. They are **legacy-observed outputs, never targets** — the differential guarantee is that
three independent implementations agree, not that any matches a historical float. Do not
reverse-engineer a program to hit any of them (§1.3.1 donor boundary).

### 0.5 Step 10 (independent-oracle `.freeNorm` preservation) is already merged — verify, don't rebuild

`test/Eval/PropertyOracle/ScanUnroll.lean` already carries the two `.freeNorm`-preserving arms
(one in `buildGeom`, one in `baseFreeSlots`), each `| some (LHSSlot.freeNorm a) => pure (LHSSlot.freeNorm a)`:

```bash
cd leanncd
grep -n "LHSSlot.freeNorm a) => pure (LHSSlot.freeNorm a)" test/Eval/PropertyOracle/ScanUnroll.lean
```

Expect exactly two hits. The unroller **preserves** the marker rather than downgrading to `.free`
(the one subtly-wrong version). Its import surface is exactly `Compare` and `ScanGen` — no
`Eval.Plan`, `DSL.Pipeline`, or route import (the differential is circular if the oracle reaches the
Plan path). Task 3 of this slice adds `.freeNorm` **fixtures** through this unroller; it does not
re-touch `ScanUnroll.lean`'s two arms.

### 0.6 Every named donor and Files-list path exists

`ls`/`grep` verified on this tree:

| Files-list module | Present |
|---|---|
| `LeanNCD/Eval/Plan/Compile.lean`, `test/Eval/Plan/{CompileTest,ScanCompileTest,ScanTest,DifferentialTest}.lean` | yes |
| `test/Eval/PropertyOracle/{ScanUnroll,ScanOracle}.lean`, `test/Eval/PropertyOracleScanTest.lean` | yes |

| Donor | Location | Use |
|---|---|---|
| `reluScan` | `test/DSL/Pipeline/ScanAffineTest.lean` (**private**) | clone its source construction; do not import |
| `coupledSched` / `coupledInputs` | `test/Eval/Plan/ScanCompileTest.lean` (public) | coupled-states geometry |
| `scratchSched` / `scratchInputs` | `test/Eval/Plan/ScanCompileTest.lean` (public) | scratch mechanics (donor is *linear*; make the producer nonlinear) |
| `multiBaseSched` / `multiBaseInputs` | `test/Eval/Plan/ScanCompileTest.lean` (public) | base geometry |
| `sampleMask` | `test/Eval/Plan/NonlinCompileTest.lean` (`BoolExpr`) | the mask for masked-axiswise **rejection** fixtures |
| `axiswisePlan` | `test/Eval/Plan/NonlinDenseTest.lean` (`RawEvalPlan`) | axiswise Dense-execution reference |
| `nonlinearBaseProgram`, `multiAxisProgram` | `test/DSL/Pipeline/RouteFragmentCorpusTest.lean` | nonlinear-base / interleaved geometry precedent |
| `freeNormAxiswiseProg` | `test/DSL/Pipeline/RouteWeaveTest.lean` (public) | Task-1 named axiswise source construction |
| `retainedAxisPos` | rehearsed in [`…/nonlinear_scan_admission/NonlinearScanAdmissionSeed.lean`](../../../../papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/NonlinearScanAdmissionSeed.lean) with `#guard`s over leading/interleaved/trailing positions | copy the helper; it is the one part of that seed that is a donor |
| `template2` | `test/Eval/PropertyOracle/ScanGen.lean` (**private**) | do **not** cite as a reusable donor (§3.6); shape precedent only |

The six oracle-group **programs** are in
[`…/nonlinear_scan_admission/OracleFixtureSeed.lean`](../../../../papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/OracleFixtureSeed.lean),
verbatim, with their inputs — the direct donor for this slice's fixtures. It lives under `papers/`
and **must not be imported**; re-home the programs into the test files.

### 0.7 There is no pre-verified production donor for `compileScan` — stated so it is not assumed

Unlike Task 3, which transplanted a byte-for-byte compiler-verified donor seed, **this slice has no
production donor for the `compileScan` change.** The rehearsal seed
`NonlinearScanAdmissionSeed.lean` is explicitly *not a transplant donor*: it contains no unroller,
no lowering, no allocation/publication logic, only the `retainedAxisPos` helper and a stop report.
The `OracleFixtureSeed.lean` programs run **only** the legacy path — no checked-Plan admission, no
oracle agreement, no publication/write safety. So the leverage this plan gives the implementer is
(a) the normative contract in master §2.7/§2.8, (b) the verified fixture programs and values in
§0.4, and (c) the mutation matrix in §2. The `compileScan` body is written against the contract and
gated by the fixtures and mutations, not copied. Size Task 1 accordingly (§2).

---

## §1 Global constraints

Exact values, and what is deliberately excluded. These refine master §3.1's global list and §2.7's
publication contract to this slice.

- **Only unmasked pointwise/axiswise `f64` is admitted — no new backend capability.** Masks,
  Iverson predicates, programmatic max/min, scatter-nonlinear, `scanPre`, and non-`f64` dtypes stay
  rejected. A masked axiswise is rejected **downstream at `resolveNonlinAxis`**
  (`.axiswise _ (some _) => throw (.maskedAxiswiseNotSupported …)`), exactly as the top-level path
  does — *not* re-added as a preflight reject in `checkNonlinScanBlock`. `checkNonlinScanBlock`
  becomes identical to `checkNonlinTopLevel` (admit `.pointwise`/`.axiswise`); the mask distinction
  is a resolution-tier concern that needs the whole slot list.
- **Every admitted nonlinear scan statement emits exactly two block steps** — a preactivation
  `.assign` destination followed by one `.pointwise`/`.axiswise` step consuming it. An identity
  statement emits exactly one. This is the Task-3 provenance invariant's precondition: a nonlinear
  block step's source is always a *preceding local `.assign` destination*, never a capture or
  another nonlinearity.
- **Publication is exactly master §2.7's table.** Preactivations are never materialized, published,
  or state-written. Only result slots consumed by a base or state write are published as block
  outputs; a recurrence scratch result enters `scratchSlotOf` but never `RawPlanBlock.outputs`.
  Construct `baseBlock.outputs`/`stepBlock.outputs` **explicitly** from the written result slots —
  never from `Array.range` or a statement count.
- **Every physical destination is allocated from the current signature count** (`baseSigs.size` /
  `stepSigs.size` at the point of emission), never from a logical statement ordinal — because a
  nonlinear statement contributes two signatures, so logical-ordinal arithmetic desyncs.
- **`retainedAxisPos` counts preceding `.free | .freeNorm` slots only**; iteration slots
  (`.iterAt`/`.iterNext`) do not count toward the local tensor's nonlinearity axis. Leading,
  interleaved, and trailing marker positions must all map correctly (rehearsed, §0.5/§0.6).
- **Captures are derived before allocation, not after.** The step block's capture set
  (`stepCapNames`) is fixed by scanning read factors before any result/scratch slot is allocated, so
  a next-state result slot can never shadow a state's pre-step capture.
- **Task 3's four-guard causality-completeness argument must survive.** Assignment-only scan
  causality stays sound only because a nonlinear block source is provenance-checked to a preceding
  local `.assign`; the four guards are `nonlinearSourceNotLocalAssignment` ∧ `checkStepGraph`'s
  `inputSlotOverwritten` ∧ `checkCaptures`' `captureTargetsNonInput` ∧ `duplicateDestination`. This
  slice relaxes provenance almost by definition (it is the first slice whose *compiler* emits
  nonlinear block steps), so re-derive the argument against the compiled output; do not assume it.
- **`commitWrite`'s write-region bounds depend on every `PointwiseFn`/`AxiswiseFn` arm being
  shape-preserving**, because a block output may now be a nonlinear step's destination. Admit no
  reducing axiswise constructor; doing so silently reintroduces the F3/F4 write-region bug class.
- **The independent oracle must not import Plan or route helpers** (§0.5). Oracle fixtures reach the
  unroller through `ScanGen`/`Compare` only.
- **Diagnostic order is normative** (master §2.7): block outputs → node context → destination
  range/availability → source range/availability → nonlinear assignment-provenance → nonlinear local
  check → scan causality.
- **`ScanPlanError.causalityFailure.stmtIndex` denotes the block-step index** (Task 3's carry-
  forward), not a filtered-assignment ordinal. Any new causality fixture must pin that meaning.
- **No `sorry`, `admit`, or `axiom`.** Full `Tests` and `LeanNCD` builds gate every task.
- **Every mutation cycle is a production mutation** (or independent-oracle mutation where stated):
  toggle the real logic, observe the named fixture fail, restore, observe it pass. Predicting a
  failure or mutating the assertion does not count.

**Discoverability.** Nothing here adds a module. `Compile.lean` is already reachable from
`import LeanNCD`; the test files are already in the `Tests` target graph. This slice generalizes
existing declarations in place and appends fixtures to existing files.

---

## §2 Task breakdown

Three tasks. Boundaries chosen by the reviewer test (*a reviewer could meaningfully reject one while
approving its neighbour*).

**Fixture accounting.** Master §3.2 budgets **"19 cross-layer fixtures *including* 6 oracle
groups"** — the 19 and the 6 are not additive. This slice builds **19** distinct fixtures total
(positional 1–5, publication 6–10, base 11–13, negative 14–19). The six oracle groups are **not new
programs**: they are six of those nineteen (fixtures 4, 5, 6, 8, 9, 11 — see the Task 3 mapping) run
through a *third* assertion path, the independent unroller. Task 3 therefore adds **zero new
fixtures**; its deliverable is the extra assertion path plus its four oracle mutations. An
implementer must not author the six programs twice.

| Task | Deliverable | New fixtures | Mutation cycles | Risk driver |
|---|---|---:|---:|---|
| 1 | `compileScan` admits/lowers nonlinear sources; the three preflight sites open; accept-path fixtures assert compiled values; 17-case corpus rebaselined to 13/0/4 | 8 (positional 1–5, base 11–13) | 3 | **highest** — the architectural centerpiece, written against a contract with no production donor (§0.7): allocation, two-step emission, `retainedAxisPos`, publication policy |
| 2 | Soundness matrix — publication/dependency and negative/write-safety fixtures — plus the six production mutation cycles that prove the reject-path and dependency guards are real | 11 (publication 6–10, negative 14–19) | 6 | the entire soundness claim: a publication leak or a provenance/causality gap is the failure mode Task 4 exists to prevent |
| 3 | Six **already-built** fixtures (4, 5, 6, 8, 9, 11) routed through the independent unroller for legacy-vs-checked-vs-unroller agreement, plus three oracle mutation cycles | 0 (third assertion path over existing fixtures) | 3 | oracle independence and the differential's teeth — a circular or toothless oracle reports agreement it does not verify |

Nine production mutation cycles total (3 in Task 1, 6 in Task 2) plus three oracle mutation cycles in
Task 3 — twelve. (The master plan's §4.4 estimate of thirteen assumed four oracle cycles; the unroller
applies the nonlinearity inline, with no preactivation/result slot to confuse, so its distinct
surfaces are three, not four — see Task 3.)

**Why three, not two or four.** Task 1 and Task 2 split on the same axis Task 3's own plan used:
Task 1 makes the accept path exist, produces correct *values*, and **carries its own three mutation
cycles** — the ones that exercise `compileScan`'s own invariants (preactivation-vs-result,
`retainedAxisPos` remapping, explicit-vs-`Array.range` publication), so Task 1 cannot be approved
without evidence its fixtures have teeth. There is no behaviour-unchanged safety net here — no
existing scan test exercises a nonlinear source — so the accept fixtures and their teeth ship *with*
the compiler change. Task 2 proves the *reject* path and the dependency/publication invariants that
have no accept-path fixture of their own. A reviewer can approve Task 1
(accepts, computes right, its three guards fail when broken) while rejecting Task 2 (a negative
fixture does not actually exercise rejection, or a mutation does not fail). Task 3 is separate because
its failure mode is orthogonal to both: the oracle's import boundary and the differential's
missing-result detection are neither exercised nor endangered by the checked-Plan fixtures. The
corpus rebaseline folds into Task 1 (it is the direct, observed consequence of admission and shares
Task 1's `DifferentialTest` build) rather than being its own dispatch — merging a tiny consequential
edit into its cause, per the sizing rule.

Every mutation cycle below names the fixture that must fail under it, and where a locator/publication
requirement is at stake, the fixture's construction is chosen so the two readings do **not** coincide
(the trap the skill warns about). Those pairings are called out inline.

---

### Task 1 — admit and lower nonlinear scan sources in `compileScan`

**Outcome.** Logical pointwise and axiswise base/recurrence statements compile and execute through
checked block steps. Only result slots are bound, published, or state-written; preactivations never
are. Every existing `ScanCompileTest`/`ScanTest` fixture keeps its byte-identical observed value
(this task adds a capability; it must not perturb the linear path). The 17-case corpus reads 13/0/4.

**Files**

- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`
- `leanncd/test/Eval/Plan/ScanTest.lean`
- `leanncd/test/Eval/Plan/DifferentialTest.lean` (corpus assertion only)

**Implementation** (against master §2.7 — read it; the steps below are the executable ordering, not
a re-derivation of the contract):

1. **Open the three preflight sites.** In `checkNonlinScanBlock`, admit `.pointwise _` and
   `.axiswise ..` (make it identical to `checkNonlinTopLevel`); the masked distinction is deferred
   to `resolveNonlinAxis`. In `checkScanLHSSlot`, admit `.freeNorm a => pure ()`. Leave
   `checkScanBlockStmt`'s structure otherwise unchanged — its `.affine`/scatter/`recurMorphism`
   rejects stay.
2. **Destructure nonlinear statements.** `compileScan`'s Phase-1 `assignPartsOrFail` currently
   accepts only identity `.assign`; generalize the base/recurrence destructuring to carry each
   statement's `Nonlin`, so a nonlinear statement is split into a preactivation `.assign` term plus a
   `.pointwise`/`.axiswise` step over its result. Reuse the top-level nonlinearity signature/chain
   helpers (`resolveNonlinAxis` and the residualization path), not a scan-specific reimplementation.
3. **`retainedAxisPos`.** Copy the rehearsed helper from `NonlinearScanAdmissionSeed.lean` (§0.6):
   `(slots.take p).countP` over `.free`/`.freeNorm` slots. Use it to map the `.freeNorm` slot position
   `resolveNonlinAxis` returns (an index over *all* LHS slots) to the local tensor's axis position,
   excluding iteration slots.
4. **Shapes and writes.** Update output-shape computation, base writes, recurrence writes, and
   scratch context-axis checks to handle a `.freeNorm` slot (the previously-`unreachable` arms in the
   base-write and step-write loops become real: a `.freeNorm` position passes through like a `.free`
   for write placement, since it is still a real output axis).
5. **Allocate from the current signature count** for every physical destination
   (preactivation and result), never from a logical ordinal (§1).
6. **Emit one block step for identity, two for nonlinear** — the preactivation `.assign` then the
   nonlinear step — replacing the unconditional `baseAssigns.map .assign` / `stepAssigns.map .assign`
   assembly. Bind a recurrence scratch's result to its slot in `scratchSlotOf` while keeping it out of
   `outputs`.
7. **Publish explicitly** (§1, master §2.7 table): build `baseBlock.outputs`/`stepBlock.outputs` from
   the result slots that a base or state write consumes; drop the `Array.range` derivation.
8. **Keep masked axiswise rejected at `resolveNonlinAxis`** (step 1 deferred it there).
9. **Rebaseline the corpus to 13/0/4 in `DifferentialTest.lean` — only after observing that exact
   split.** Change `scanCorpusSplit`'s `run_cmd` assertion from `accepted == 9 && nonlin == 4` to
   `accepted == 13 && nonlin == 0` (agg stays 4, total stays 17), and update the adjacent explanatory
   comment (the four `template2` cases are now admitted). If the observed split is anything other than
   13/0/4, **stop and report** — an accepted case that stops matching `evalScheduled` is an admission
   defect, not a number to force.

**Accept-path fixtures** (checked-Plan; assert compiled output equals the §0.4 legacy value). Each
names its donor as `clone <donor>, change <one field>`:

| # | Shape | Donor | Asserted value (from §0.4) |
|---|---|---|---|
| 1 | `G[l+1,j.] := softmax(...)`; local axis position 0 | clone `reluScan` source, swap ReLU→softmax, marker first | (structural; assert acceptance + shape) |
| 2 | interleaved iteration/local axes, marker in the middle | clone `OracleFixtureSeed.fixture2` (marker `.freeNorm` at slot index 1, strictly between iteration slots) | `[3,2,3]`, diagonal `[1,3]/[.25,.75]/[.25,.75]` |
| 3 | marker last among several local axes | clone fixture 2, move the `.freeNorm` slot to the trailing position | (structural; assert acceptance + shape) |
| 4 | leading-axis pointwise exact history | clone `OracleFixtureSeed.fixture1` (leading pointwise scratch) | `[2,3] = [-1,2,0,2,6,18]` |
| 5 | interleaved axiswise exact history | `OracleFixtureSeed.fixture2` (adopt directly) | `[3,2,3]` as fixture 2 |
| 11 | pointwise nonlinear **base**, differing preactivation/result | `OracleFixtureSeed.fixture4` (nonlinear base, `.pointwise .relu`; recurrence `.identity`) | `[2,3] = [0,0,0,3,-3,3]` |
| 12 | nonlinear free-face plus point override | clone fixture 4, add an `.iterAt` point override to the base LHS | (structural; assert acceptance + shape) |
| 13 | successful axiswise nonlinear base | clone fixture 4, swap `.pointwise .relu`→`.axiswise .normalize none` on a marked base axis | (assert acceptance + shape) |

Fixtures 2, 3, and 5 are the **retained-axis-mapping locators**: their `.freeNorm` marker sits at a
non-zero position among the local axes, so a fixture whose marker were at position 0 would leave
`retainedAxisPos = 0` and could not tell a correct remap from a removed one. Fixture 11's
preactivation (`relu(X)`) and result differ in value on the negative input, making it the
**preactivation-vs-result locator** (mutation cycle 1 below names it).

**Mutation cycles** (three; production mutation in `compileScan` → named fixture fails → restore →
passes). These exercise Task 1's *own* invariants, so they ship with it — Task 1 is not reviewable
without them:

| # | Mutation in `compileScan` | Fixture that must fail | Why it distinguishes |
|---|---|---|---|
| 1 | publish/state-write the preactivation slot instead of the result | 11 | preactivation (`relu(X)`) ≠ result in value on the negative input |
| 2 | remove the `retainedAxisPos` remapping (use the raw slot index) | 2, 3, 5 | each marker sits at a non-zero local position, so raw index ≠ remapped |
| 3 | reintroduce `Array.range` block outputs | 19 (built in Task 2) — until then, assert against fixture 4's `outputs` shape | a scratch/preactivation would leak into `outputs` |

Mutation 3's ideal witness (fixture 19, a mixed identity/nonlinear-output state) is built in Task 2;
in Task 1, run it against fixture 4 whose block emits a preactivation the `Array.range` derivation
would wrongly publish, and re-confirm it against fixture 19 in Task 2's cycle set. (Cycles for the
**dependency and negative** invariants — capture ordering, the four `.freeNorm` reverts, allocation-
by-statement-count — live in Task 2 because their witnessing fixtures do.)

**Gate.** Beyond the four builds in §0.1, Task 1's own safety net — the only one it has, given no
donor (§0.7) — is that **`Eval.Plan.ScanCompileTest` and `Eval.Plan.ScanTest` build with every
pre-existing fixture's observed value unchanged.** State this in the completion record with the two
targeted build results, not just the aggregate `Tests` count: an aggregate count can stay constant
while a scan value silently shifts.

**Risk / cost.** Highest in the slice. 8 fixtures + 3 mutation cycles, but the cost is in the
`compileScan` body written against a contract with no donor (§0.7) plus keeping every existing linear
fixture byte-identical. Budget for iteration on allocation/publication, not for the fixture count
alone.

---

### Task 2 — soundness matrix and its six production mutation cycles

**Outcome.** The publication policy and the provenance/causality guards are proven real by fixtures
that fail when the guard is removed. Preactivations are demonstrably never published or state-written;
a nonlinear source that is not a preceding local assignment is rejected; masked axiswise is rejected;
`.freeNorm` in a disallowed position is rejected.

**Files**

- `leanncd/LeanNCD/Eval/Plan/Compile.lean` — one production line: the scratch context-axis guard
  now covers `.freeNorm` as well as `.free` (a Task 1 gap surfaced by fixture 17; see the execution
  record). This was not in the plan's original Task 2 footprint.
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`
- `leanncd/test/Eval/Plan/ScanTest.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean` (negative/diagnostic cases)

**Publication / dependency fixtures**

| # | Shape | Donor | Asserts |
|---|---|---|---|
| 6 | nonlinear scratch consumed by a later scratch | `OracleFixtureSeed.fixture5` (scratch→scratch→state), `[3]=[1,6,0]` | scratch results are internal; not in `outputs` |
| 7 | nonlinear scratch consumed by a state | clone fixture 5, drop the second scratch | scratch result feeds the state write, not published directly |
| 8 | persistent state's own nonlinear recurrence | `OracleFixtureSeed.fixture3` (adopted `reluScan`, `S=[1,0]`) | base+recurrence writes; result-only publication |
| 9 | coupled linear/nonlinear states | `OracleFixtureSeed.fixture6` (adopted EvalExamplesTest ex 5), `G=[1,3,6]`, `H=[2,3,6]` | two states, exact per-state values |
| 10 | exact capture order after a nonlinear logical statement | clone fixture 5, add an external read after the nonlinear step | capture set/order unchanged by the intervening nonlinearity |

**Negative / write-safety fixtures**

| # | Shape | Donor | Expected rejection |
|---|---|---|---|
| 14 | masked axiswise **base** | clone fixture 13, attach `sampleMask` | `maskedAxiswiseNotSupported` at `resolveNonlinAxis` |
| 15 | masked axiswise **recurrence** | clone fixture 5's state recurrence, make it a masked axiswise | `maskedAxiswiseNotSupported` |
| 16 | `.freeNorm` with **pointwise** ReLU | clone fixture 1, keep the `.freeNorm` marker but set `.pointwise .relu` | rejection (a marker with a non-axiswise nonlinearity is inconsistent) |
| 17 | `.freeNorm` on a **context axis** scratch | clone fixture 2, mark an iteration axis `.freeNorm` | `contextAxisAsFreeOutput`/norm-axis rejection |
| 18 | state write pointed at **preactivation** while outputs retain result | hand-built: a state whose write map targets the preactivation slot | rejection — preactivation is never a write source |
| 19 | mixed identity/nonlinear outputs contain **results only** | clone fixture 9, add an identity state alongside the nonlinear one | `outputs` holds result slots for both, no preactivation |

Fixture 18 is the **publication locator**: its preactivation and result occupy distinct slots with
distinct values, so publishing/writing the preactivation is observable. Fixtures 16/17 are the
`.freeNorm`-validation locators for the four `.freeNorm` revert cycles below.

**Mutation cycles** (six; production mutation → named fixture fails → restore → passes). Task 1
already carries the three that exercise its own invariants (preactivation-vs-result,
`retainedAxisPos`, `Array.range` outputs); these six are the reject-path, dependency, and
`.freeNorm`-validation guards whose witnessing fixtures are built here:

| # | Mutation in `compileScan` | Fixture that must fail | Why it distinguishes |
|---|---|---|---|
| 1 | advance allocation by logical-statement count | 5 / 6 | nonlinear statement emits two destinations |
| 2 | revert `.freeNorm` in **output-shape** computation | 5 / 13 | marker participates in the shape |
| 3 | revert `.freeNorm` in the **base-write** loop | 13 | nonlinear base carries the marker |
| 4 | revert `.freeNorm` in the **recurrence-write** loop | 5 | nonlinear recurrence carries the marker |
| 5 | revert `.freeNorm` in **scratch context-axis validation** | 17 | rejection depends on the marker check |
| 6 | derive captures **after** allocation | 10 | capture order is observable only post-nonlinearity |

The `Array.range`-outputs revert (Task 1's cycle 3) is re-confirmed here against fixture 19, its
sharper witness, once that fixture exists.

**Risk / cost.** 11 fixtures × 6 mutation cycles — the largest fixture count in the slice, and the
cost is the trial-and-error of building each negative fixture so its rejection is the *named*
constructor, not an incidental earlier reject. Each negative fixture's donor is a one-field mutation
of an accept-path fixture (above), which is what keeps that cost bounded.

---

### Task 3 — route six existing fixtures through the independent oracle, and its oracle mutations

**Outcome.** Six of the nineteen fixtures Tasks 1–2 already built — the oracle groups — gain a
**third assertion path**: in addition to legacy `evalScheduled` and the checked Plan, each is run
through the independent unroller, and all three agree on the §0.4 values. **No new program is
authored here** (that is the fixture-accounting point in §2): these are fixtures 4, 5, 6, 8, 9, 11,
re-asserted under the unroller. The unroller's teeth are proven by the oracle mutations below. Step 10
(the unroller's `.freeNorm` arms) is already merged (§0.5) and is not re-implemented.

**Files**

- `leanncd/test/Eval/Plan/DifferentialTest.lean` — the three-way parity list (`nonlinearScanFixtures`
  through `scanParityCheck`). This is the genuine three-way integration point per master §2.8: it
  already imports both the compiler (`Adapter`, `ScanCompileTest`) and the unroller (`ScanUnroll`),
  which `ScanOracle.lean`/`PropertyOracleScanTest.lean` (the plan's original guess) deliberately
  cannot, since the oracle must not import the Plan compiler.
- `leanncd/test/Eval/Plan/ScanCompileTest.lean` — the §3.6 structural-fact guards for the four
  freshly-authored groups (co-located with the programs).

**Implementation**

1. Reference the six programs Tasks 1–2 built (see the mapping below), not fresh copies — they are
   public `ScheduledProgram` defs in `ScanCompileTest`, in scope in `DifferentialTest` via its
   existing `import Eval.Plan.ScanCompileTest`. Route each through `scanParityCheck`, which runs the
   compiled Plan (`runPreparedDense`), legacy `evalScheduled`, and `PropertyOracle.independentRun` and
   asserts all three agree on every materialized state plus scratch privacy on all three legs.
2. Groups 1, 2, 4, 5 are freshly authored and their values exist nowhere else, so each also asserts
   the structural facts §3.6 records (group 1's scratch local axis at slot index 0 and its single
   writing statement; group 2's `.freeNorm` slot strictly between iteration slots; group 4's pointwise
   base and identity recurrence; group 5's three destinations in dependency order) — a value with no
   independent record pins a number without pinning the shape it came from.

**Oracle-group → fixture mapping** (all six built by Tasks 1–2; none new):

| Oracle group | Shape | Fixture (Task) |
|---|---|---|
| 1 | leading pointwise scratch (`fixture1`) | 4 (Task 1) |
| 2 | interleaved axiswise (`fixture2`) | 5 (Task 1) |
| 3 | leading persistent nonlinear (adopted `reluScan`) | 8 (Task 2) |
| 4 | nonlinear base (`fixture4`) | 11 (Task 1) |
| 5 | scratch→scratch→state (`fixture5`) | 6 (Task 2) |
| 6 | coupled states (adopted example 5) | 9 (Task 2) |

**Mutation cycles** (three; mutate the **independent oracle** (`ScanUnroll`), not production — this is
the one place the skill sanctions oracle mutation, because the oracle is the thing under test). The
plan originally listed four, but this unroller applies the nonlinearity **inline** on each leaf — it
has no preactivation/result slot to confuse — so the plan's "skip nonlinear leaf evaluation" and
"publish preactivation" are the *same* mutation here (not applying the nonlinearity IS publishing the
preactivation). The three surfaces the oracle genuinely has are split so each names a distinct group:

| # | Mutation in the unroller (`ScanUnroll`) | Group that must fail | Why it distinguishes |
|---|---|---|---|
| 1 | `buildGeom` drops the `.freeNorm` marker (retained-axis mapping) | 2 | only group 2 carries an axiswise marker |
| 2 | the STEP (recurrence) leaf rewrite drops the nonlinearity | 1 (also 3, 5, 6) | recurrence nonlinearity is load-bearing |
| 3 | the BASE leaf rewrite drops the nonlinearity | 4 | only group 4's nonlinearity is on the base |

Together the three break every one of the six groups (2; 1/3/5/6; 4), so the oracle is proven to
actually apply each group's nonlinearity rather than agree vacuously.

**Risk / cost.** **Zero new fixtures** — this task adds a third assertion path plus its own file
scaffolding over six fixtures Tasks 1–2 already built, so it is the cheapest of the three despite
being a separate dispatch (its failure mode — a circular or toothless oracle — is orthogonal to the
other two, which is why it is not folded in). The four oracle mutations are test-only. The
import-boundary check (§0.5) must be re-run after any edit: the oracle must still import only
`Compare`/`ScanGen`, never a `Eval.Plan`/`DSL.Pipeline`/route module.

---

## §3 Stop conditions

Stop and revise rather than improvise if (these specialize master §4.3):

- the 17-case corpus does not produce exactly 13/0/4 after admission;
- preactivation and result cannot be distinguished in a base or state write;
- a checked nonlinear block node can consume a capture or another nonlinearity directly (Task 3's
  provenance guard would be defeated, not merely relaxed);
- assignment-only Plan-block causality changes behaviour on any existing linear fixture;
- a scratch result must become a block output to be consumed locally;
- the independent oracle must import a Plan or route module to reproduce a value;
- a differential comparison can pass with a logical result missing;
- admitting the capability requires a reducing axiswise constructor (would break `commitWrite`'s
  shape-preserving assumption, §1);
- any existing `ScanCompileTest`/`ScanTest` fixture's observed value changes.

A masked or otherwise out-of-capability shape that *seems* required is a signal to stop, not to widen
admission.

---

## §4 Definition of done

- `checkNonlinScanBlock`/`checkScanLHSSlot` admit unmasked pointwise/axiswise and `.freeNorm`; masked
  axiswise is rejected at `resolveNonlinAxis`.
- `compileScan` emits exactly two block steps per nonlinear statement and one per identity;
  allocates every destination from the current signature count; maps retained axes correctly for
  leading, interleaved, and trailing positions.
- Preactivations are never materialized, published, or state-written; `outputs` are built explicitly
  from written result slots, never `Array.range`.
- Legacy Eval, checked Plan, and the independent oracle agree on all six oracle-group values and on
  every accept-path fixture, at the §0.4 numbers.
- All 12 mutation cycles (3 production in Task 1, 6 production in Task 2, 3 oracle in Task 3) show
  fail-on-mutation and pass-on-restore in their **named** fixtures, recorded observed-not-predicted.
- The 17-case scan corpus reads 13/0/4; **`Eval.Plan.ScanCompileTest` and `Eval.Plan.ScanTest` build
  with every pre-existing fixture's observed value unchanged**, recorded as two targeted build
  results in Task 1's record — not inferred from the aggregate `Tests` count, which can hold constant
  while a scan value shifts.
- `Tests` and `LeanNCD` build green at counts consistent with §0.1 plus the new fixtures; no `sorry`.
- Two whole-branch reviews (per master §3.6): one for compiler allocation / axis mapping /
  diagnostics, one for publication / oracle independence / Dense semantics — findings green or
  adjudicated.

---

## §5 Execution record

*(To be appended on execution — commits, gate job counts, the observed 13/0/4 split, Task 1's two
targeted `ScanCompileTest`/`ScanTest` build results confirming unchanged pre-existing values, each
new fixture's observed value, all 13 mutation cycles observed-not-predicted, the oracle
import-boundary re-check, and both whole-branch review adjudications. Cite identifiers, never
`File.lean:NNN` line numbers.)*

### Task 1 — executed 2026-08-28

**Production change** (`LeanNCD/Eval/Plan/Compile.lean`): `checkNonlinScanBlock` and
`checkScanLHSSlot` now admit `.pointwise`/`.axiswise`/`.freeNorm` (identical to the top-level
`checkNonlinTopLevel`/`checkLHSSlot`); `resolveNonlinAxis` moved above `compileScan` and a new
`retainedAxisPos` helper added beside it; `compileScan`'s base and step phases generalized to resolve
each statement's `Nonlin`, allocate every destination from the current signature count, emit one
`.assign` block step for identity and a preactivation `.assign` + one `.pointwise`/`.axiswise` step
for a nonlinear statement, bind a scratch/state name to its post-nonlinearity **result** slot, and
publish block outputs explicitly (`baseResultSlots` / `stepOutputs`) — the `Array.range` base-output
derivation is gone. Phase-5 causality iterates the preactivation assigns (`stepAssignPlans`).

**Test changes.** `CompileTest.lean`: two scan-block preflight fixtures flipped from
`errOf … == unsupportedNonlin` to `isOk` (the shapes are now admitted). `ScanCompileTest.lean`:
the three now-admitted shapes (`.freeNorm`, `.pointwise`, `.axiswise`) removed from the section-2.2
preflight-rejection enumeration and their orphaned `badFreeNorm`/`badNonlin` helpers deleted; the
precedence fixture reworded to a still-rejected shape (`badAffineLhs`); a new Part 4 adds the eight
accept-path fixtures. `DifferentialTest.lean`: corpus assertion rebaselined 9/4/0/4 → 13/0/4.

**Corpus.** Observed `total=17 accepted=13 unsupportedNonlin=0 unsupportedAgg=4`. Because the sweep
short-circuits on the first parity disagreement, `accepted=13` also asserts the four newly-admitted
`template2` ReLU-scan cases match `evalScheduled` byte-for-byte.

**Accept-path fixture values** (compiled checked-Plan output via `runPreparedDense`, all observed):

| Fixture | Program | Observed |
|---|---|---|
| 4 | leading pointwise scratch | `S` `[2,3]` = `[-1,2,0,2,6,18]` |
| 2/5 | interleaved axiswise | `S` `[3,2,3]` = `[1,0,0,3,0,0,0,.25,0,0,.75,0,0,0,.25,0,0,.75]` |
| 11 | pointwise nonlinear base | `S` `[2,3]` = `[0,0,0,3,-3,3]` |
| 1 | softmax marker-first | accepted; `S` shape `[3,2]` |
| 3 | normalize marker-last | accepted; `S` shape `[3,2,2]` |
| 12 | nonlinear base 2-D face | accepted; `S` shape `[2,2,3]` |
| 13 | axiswise nonlinear base | accepted; `S` shape `[2,3]` |

Fixtures 4, 2/5, 11 match `OracleFixtureSeed`'s legacy values exactly.

**Mutation cycles** (production mutation → observed fail in the named fixture → restore → observed
pass; all observed, not predicted):

| # | Mutation | Observed failure |
|---|---|---|
| 1 | base `.pointwise` publishes `preSlot` not the result slot | only `T4.11` fails: `got [-2,-4,-8,3,-3,3]` vs `[0,0,0,3,-3,3]` (raw `X` propagated, not `relu(X)`) |
| 2 | drop `retainedAxisPos` (use raw all-slots index) | `T4.2/5`, `T4.1`, `T4.3` fail `invalidPlan/scan` (axisPos out of range); `T4.13` correctly unaffected (its marker is genuinely at position 0) |
| 3 | step outputs from statement count (`Array.range`) | `T4.4` fails `writeSourceNotBlockOutput`; also breaks the pre-existing `C/scratch` fixture, confirming the invariant is broadly load-bearing |

Restore after each cycle verified byte-clean against the pre-mutation copy.

**Gates** (all green): targeted `CompileTest ScanCompileTest ScanTest DifferentialTest` 8,525;
`Eval.PropertyOracle.ScanOracle Eval.PropertyOracleScanTest` 8,505; `Tests` 8,657; `LeanNCD` 8,543.
The `Tests` and oracle counts are unchanged from §0.1, and `ScanCompileTest`/`ScanTest` build with
every pre-existing fixture value unchanged — Task 1's donor-free safety net.

### Task 2 — executed 2026-08-29

**Production change** (one line, `Compile.lean`): the scratch context-axis guard in `compileScan`'s
Phase 1 now matches `.free a | .freeNorm a`, not `.free a` alone — a `.freeNorm` marking a scan
context axis on a scratch was the one silently-ignored cell of the retained-vs-context audit. Sibling
cells are covered elsewhere and were left unchanged: a state result's `.freeNorm` on a context axis
duplicates that axis's mandatory `.iterNext` and is caught by `firstDuplicateUID`/`partialAdvancingResult`;
a base's stray free/freeNorm context axis is rejected downstream by `checkScanPlan`'s base-write
geometry check (a base must pin each advancing dim). This gap was invisible to Task 1's diff review —
the guard it needed to change was unchanged code — and surfaced exactly as the skill predicts, via
fixture 17.

**Test changes** (`ScanCompileTest.lean` Part 5): eleven fixtures. Publication/dependency 6–10 assert
compiled values and structure via `runPreparedDense`/`scanAt`; negatives 14–19 assert the named
rejection. All observed:

| # | Shape | Observed |
|---|---|---|
| 6 | scratch→scratch→state | `S` `[3]` = `[1,6,0]`; `T`/`U` not materialized, 1 step output |
| 7 | scratch→state | `S` `[3]` = `[1,2,0]` |
| 8 | persistent nonlinear recurrence | `S` `[1,2]` = `[1,0]` |
| 9 | coupled states | `G` `[1,3]` = `[1,3,6]`, `H` `[1,3]` = `[2,3,6]` |
| 10 | capture order | `stepCaptures` sources `[state 0, external 1, external 2]` |
| 14 | masked axiswise base | `nonlin (maskedAxiswiseNotSupported "S")` |
| 15 | masked axiswise recurrence | `nonlin (maskedAxiswiseNotSupported "S")` |
| 16 | `.freeNorm` + pointwise | `nonlin (unmarkedReductionAxis "S" 1)` |
| 17 | `.freeNorm` on context-axis scratch | `scan (contextAxisAsFreeOutput "S" "T" 0 …)` |
| 18 | state write → preactivation slot | `scan (writeSourceNotBlockOutput false 0 preSlot)` (compiled then repointed) |
| 19 | mixed identity/nonlinear outputs | 2 step outputs, materialized `[G, H]`, no preactivation |

**Mutation cycles** (six production mutations → observed fail in the named fixture → restore → pass;
all observed):

| # | Mutation | Observed failure |
|---|---|---|
| 1 | step allocation by statement ordinal (`stepInputCount + ri`) | `T4.6` (+4/7/9/10) fail `invalidPlan/scan` (slot desync) |
| 2 | drop `.freeNorm` from `outputUids` (base+step) | `T4.2/5`, `T4.13` (+1/3) fail `invalidPlan/scan` |
| 3 | drop `.freeNorm` from the base-write loop | only `T4.13` fails `unsupportedLhsSlot "S: base LHS slot"` |
| 4 | drop `.freeNorm` from the step-write loop | `T4.2/5` (+1/3) fail `unsupportedLhsSlot "S: state-result LHS slot"` |
| 5 | drop `.freeNorm` from the scratch context-axis guard | only `T4.17` `#guard` fails (no longer rejects) |
| 6 | reorder captures (`stepCapNames.reverse`) | `T4.10` fails `[external 2, external 1, …]` vs `[state 0, external 1, external 2]`; also breaks pre-existing A/B/C capture fixtures |

Mutation 6 is a realizable **proxy** for the plan's "derive captures after allocation": the literal
restructuring is not a one-line toggle, so the cycle reverses the derived capture order instead,
which exercises the same invariant fixture 10 pins (capture order is source-determined and stable).
Restore after each cycle verified byte-clean.

**Gates** (all green, unchanged from §0.1 except the intended corpus flip): targeted 8,525; oracle
8,505; `Tests` 8,657; `LeanNCD` 8,543 (the one-line production guard added no regression).

### Task 3 — executed 2026-08-29

**No production change.** The six oracle-group programs (built in Tasks 1–2, referenced not
re-authored) are routed through `DifferentialTest.lean`'s `scanParityCheck` as `nonlinearScanFixtures`
— the genuine three-way gate (compiled `runPreparedDense`, legacy `evalScheduled`, independent
`PropertyOracle.independentRun`), which also asserts scratch privacy on all three legs. All six pass:
groups 1/5 with scratch sets `["T"]`/`["T","U"]`, the rest none. Master §2.8 places this three-way
gate in `DifferentialTest` (which imports both the compiler and the unroller); the plan's original
Task 3 Files guess (`ScanOracle`/`PropertyOracleScanTest`) was wrong because those files must not
import the compiler. Four §3.6 structural-fact guards for the freshly-authored groups (1, 2, 4, 5)
were added to `ScanCompileTest.lean`, co-located with the programs.

**Import independence re-checked:** `ScanUnroll.lean` imports exactly `Eval.PropertyOracle.Compare`
and `Eval.PropertyOracle.ScanGen` — no `Eval.Plan`/`DSL.Pipeline`/`Adapter`/`Compile` import (the two
`grep` hits for those strings are docstring prose, not imports). An oracle that reached into the Plan
path would make the differential circular.

**Oracle mutation cycles** (three; mutate `ScanUnroll`'s `independentRun`, observe a three-way
disagreement in the named group, restore, observe pass — all observed):

| # | Mutation | Observed failure |
|---|---|---|
| 1 | `buildGeom` maps `.freeNorm a` to `.free a` (drops the marker) | `group2/interleavedAxiswise` fails: "applies normalize but no output axis is marked" |
| 2 | STEP (recurrence) leaf rewrite forces `nonlin := .identity` | `group1/leadingPointwiseScratch` fails THREE-WAY (also corpus case 4, a `template2` ReLU scan) |
| 3 | BASE leaf rewrite forces `nonlin := .identity` | only `group4/nonlinearBase` fails THREE-WAY (recurrence-nonlinear groups untouched) |

The three break every group (2; 1/3/5/6; 4), proving the oracle applies each group's nonlinearity
rather than agreeing vacuously. Only three cycles, not the plan's four: the unroller applies the
nonlinearity inline (no preactivation/result slot), so "skip nonlinear leaf eval" and "publish
preactivation" coincide — splitting the nonlinearity drop into the recurrence and base paths gives
groups 1 and 4 distinct witnesses, which is finer coverage than the plan's original grouping.
Restore after each cycle verified byte-clean.

**Gates** (all green): targeted 8,525; oracle 8,505; `Tests` 8,657; `LeanNCD` 8,543 — all unchanged
from §0.1 except the corpus flip. Total slice mutation cycles: 3 + 6 + 3 = **12**.
