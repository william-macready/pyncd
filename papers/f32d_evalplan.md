# F32-D: native binary32 top-level scatter — implementation plan

**Status:** authored 2026-09-25 on branch `plan/f32d` from `main` at `6303e9f`. Not executed.
**Companions:** `papers/f32d_record.md` (what was measured while authoring, how, and what was not
verified); `papers/f32d_mutations.json` (the mutation cycles, run by
`leanncd/scripts/mutation-manifest.sh`); `papers/f32d_files/` (the two new test files, compiled and
run while authoring, to be copied, not retyped). You do not need to read the record.

**How to read code in this repo during execution.** Every task lists the symbols it touches as
`identifier @ file`. Run `rg -n <identifier> <file>` and read a ~40-60 line window. **Never read a
file over ~20k characters whole** (`Compile.lean` 120k, `CompileTest.lean` 130k, `Adapter32Test.lean`
47k, `Error.lean` 43k, `Dense.lean` 26k, `Check.lean` 28k, `EvalPlan.lean` 24k, `GraphCheckTest.lean`
24k). Do not read `papers/f32_evalplan.md` or `papers/f32b_evalplan.md` whole either; the steps that
edit them give the exact `rg` to find their lines.

---

## 1. Scope

### 1.1 Admitted by this slice

A top-level `.scatter` step in a `.float32` graph, executed natively in binary32, end to end: from
`tlprog!` source (`prepareEvalPlan`) through `checkPlan` (`checkScatterF32`), `runDensePlan32`
(`runDenseScatter32`), and the named boundary `runPreparedDense32`. This includes a scatter whose
RHS carries an inline unary read factor (F32-B §1.3 assigned that case here), a Boolean-tagged
source read (it rides the binary32 carrier exactly as for assignments; fixture 1.8), and a
binary32 scatter that reads a preceding binary32 assignment's or nonlinearity's result.

### 1.2 Still refused, unchanged (owner in brackets)

| Construct | Where it is refused | Owner |
|---|---|---|
| every scan form, including scan-local scatter | Step 0c `"{nm}: f32 scan"`; `checkPlan` `f32UnsupportedStep i .scan`; `runDensePlan32` `.scan` arm | F32-C |
| a scatter nonlinearity (`relu`, `softmax`, …) on ANY dtype | Step A `unsupportedNonlin "{nm}: scatter nonlinearity"` | policy — not a gap |
| a collision policy other than `.rejectCollisions`, either carrier | Step A `scatterOptsNotAdmitted`; `checkScatter`/`checkScatterF32` `scatterReduceNotAdmitted` | policy |
| a source `fill` ≠ the algebra's identity, or one that rounds to `±∞` in binary32 | `scatterFillOrFail`: the `.f32` arm also requires `(Float32.ofInt fill).isFinite` (15(c) refusals) | policy |
| a binary64 source `fill` that rounds to `-∞` (e.g. `-(2^1024)` on `maxreduce`) | NOT refused: `Float.ofInt` overflows to the `-∞` bits `admittedAlgebraMax.reduceId` holds, so the `.f64` arm admits it (pre-existing; binary64 is preserved bit for bit, so unchanged here) | **none yet** — a binary64 gap |
| any f32 plan on JAX | plan-level `.float64` gate at every JAX door | F32-JAX |
| any f32 program on the legacy evaluator | `EvalError.unsupportedDtype` | permanent |
| mixed f32/f64 in one graph | Step 0b; `mixedStorageKinds` | F32-E (contingent) |

F32-B §1.3 said F32-D would include a scatter "whose RHS carries … a nonlinearity". It does not: a
scatter nonlinearity is rejected at Step A for binary64 too (`checkNonlinScatter`), so there is no
binary32 gap there. Task 3 records this in F32-B's §1.3.

### 1.3 Carry-forward for F32-C (re-derived for this plan, not inherited)

`papers/f32_evalplan.md` §1.4 said "scan-local scatter probably reuses F32-D's fill and placement
write path. This is unverified." **It does not.** `LeanNCD/Eval/Plan/Scan.lean` and `Block.lean`
contain zero references to `ScatterPlan`, `checkScatter`, `runDenseScatter`, `scatterFillOrFail`,
or `scatterPlacementOrFail`. The scan compiler lowers placement into its own state-write rows
(`scanPlacementRows @ Compile.lean`), checks fill with its own integer test (`opts.fill != 0`), and
shares only the carrier-free extent function `scatterDestExtent @ Check.lean`. F32-C must build a
binary32 state-write path in `runDenseScan @ Scan.lean` itself. The (c) cells `runDenseBlock` and
`runDenseScan` (Float-only, safe only behind the `.scan` refusals) are unchanged by this slice.

---

## 2. Global constraints (exact values)

- **Guard first, at every scatter door.** `runDenseScatter` checks `c.storageKind == .float64` and
  `runDenseScatter32` checks `c.storageKind == .float32` as their FIRST statement, before
  `validateContext`/`validateStore`. A mismatch is `PositionalInputError.storageKindMismatch
  <door's kind> <evidence's kind>`, never a conversion.
- **`CheckedScatterPlan` records `storageKind : LeanNCD.StorageKind`**, set only by
  `checkScatter` (`.float64`) and `checkScatterF32` (`.float32`), both thin applications of ONE
  private `checkScatterCore kind`, which calls the existing private `checkAssignCore kind`. No
  public raw-plan-plus-ops scatter entry is added.
- **One formula, two carriers.** `runDenseScatter`/`runDenseScatter32` both run ONE private
  `runDenseScatterWith ops`; the binary32 path never widens to `Float` (the pattern forbidden by
  Plan/AGENTS.md: "never derive them by narrowing binary64 results").
- **Binary64 behaviour is preserved bit for bit.** Gate G64 (§5, Task 1 step 1) must be green before
  and after Task 1 with NO edits to `ScatterCheckTest.lean`'s guards, `ScatterDenseTest.lean`,
  `ScatterCompileTest.lean`, `GraphDenseTest.lean`, or `DifferentialTest.lean`.
- **Values are exact bit patterns** compared through `Float32.toBits`/`Float.toBits`, never
  `BEq Float32`. Every value in this plan was observed on a prototype (§3.4); if the real code
  produces a different value, STOP (§8), do not edit the expectation.
- **No `File.lean:NNN` line numbers** in anything you ship (docstrings, AGENTS.md, papers,
  completion notes). Cite identifiers.
- **Retained, not deleted:** `PlanStepKind.scatter` (still a `PlanStep` kind; it just stops being an
  `f32UnsupportedStep` payload), `CapabilityError.unsupportedDtype` (still live: mixed storage, f32
  scan), the `"{nm}: f32 scatter"` context's doc entry in `Error.lean` (re-worded as producer-less).
- **Throw-site counts after the slice** (re-count in Task 3 step 10): `.unsupportedDtype s!` in
  `Compile.lean` 4 → **3**; `f32UnsupportedStep ni` in `EvalPlan.lean` 2 → **1**;
  `throw (.storageKindMismatch .float32 .float64)` in `Dense32.lean` 2 → **1**.
- **Build:** `bash leanncd/scripts/lake-build.sh <leanncd-dir>` ends `Build completed successfully`
  (baseline **8670 jobs** at `6303e9f`; the two new test modules should add 2, record the actual).
- **New test modules must be registered** in `leanncd/lakefile.toml`'s `Tests` `globs`, beside
  `"Eval.Plan.ScatterDenseTest"` and `"Eval.Plan.Adapter32Test"` respectively, or they never build.

---

## 3. Design

### 3.1 Checker

`checkScatter`'s body becomes `private checkScatterCore (kind)`; its first line calls
`checkAssignCore kind sigs s.compute (some s.destShape)` instead of `checkAssign …`; every other
clause (fill coherence `s.fill == s.compute.algebra.reduceId`, the `.rejectCollisions`-only reduce
match, placement rank/width/extent through `scatterDestExtent`) is unchanged and therefore shared.
Under `.float32`, `checkAssignCore` already enforces f32/bool dtypes and `admittedAlgebrasForF32`,
so a coherent fill is necessarily an `.f32`/`.bool` constant.

### 3.2 Worker

`runDenseScatter`'s body becomes `private runDenseScatterWith ops`: `floatOps.decodeConst` →
`ops.decodeConst`, `denseValueAt a [] store sc` → `denseValueAtWith ops a [] store sc`, and the
three unreachable arithmetic reduce arms go through `ops.binOp` (`.add`/`.max`/`.min`) instead of
Float `+`/`Max.max`/`Min.min` — so admitting a policy later remains a checker change alone, for both
carriers. Every other line — `validateContext a []`, `validateStore`, the placement `AffineMap`,
`inBoundsPerDim` before `flatIndex`, the `writtenBy` collision record — is moved VERBATIM (the
manifest's G1/G2 cycles mutate two of those lines and must still pass after the move).

### 3.3 Graph and compiler

- `checkPlan @ EvalPlan.lean`: the `.float32` capability loop's `.scatter _` arm becomes `pure ()`;
  the `.scatter s` `localCheck` arm selects `checkScatter`/`checkScatterF32` by the graph's
  `storageKind`, exactly as the `.assign` arm does.
- `runDensePlan32 @ Dense32.lean`: the `.scatter` arm runs `runDenseScatter32` and writes
  `c.plan.compute.destinationSlot`, mirroring `runDensePlan`'s arm.
- `Compile.lean`: `checkF32Stmt` is deleted (after the change every arm would be `pure ()`), and
  `f32CapabilityCheck`'s `.plain` arm becomes `.plain _ => pure ()`. `scatterFillOrFail`'s
  `.f32 _ => false` becomes `.f32 bits => (Float32.ofInt fill).isFinite && bits == …toBits` (native,
  bits; finiteness refuses an integer that overflows to the `-∞`/`+∞` identity of a tropical algebra).
  Step D's scatter branch needs NO change: it already selects `destDtype` and
  `algebraForDest destDtype rhs.agg` from the destination's declaration.

### 3.4 How the values in this plan were obtained

The production edits of all three tasks were applied to namespace-renamed copies of `Check.lean`,
`Dense.lean`, `EvalPlan.lean`, `Dense32.lean`, `Prepared.lean`, `Compile.lean`, `Adapter.lean`, and
`Adapter32.lean` in gitignored `leanncd/spikes/` (namespace `LeanNCD.Eval.Plan.P`), compiled, and
every fixture below was run against them. The blocks below ARE that text. Details:
`f32d_record.md` §2.

### 3.5 The independent binary32 oracle (Task 3)

Required by `papers/f32_evalplan.md` §1.3 item 3. The legacy evaluator cannot serve (it refuses
f32). **Design:** under `.rejectCollisions`, placement copies values with no arithmetic, so a
binary32 scatter's result must equal (a) its RHS evaluated as an ordinary binary32 ASSIGNMENT — a
`twin` program with a free LHS over the same source axes, run through the F32-A path (Step D's
plain branch, `checkAssignF32`, `runDenseAssign32`), which touches no scatter code — placed by (b) a
test-local function written from the SOURCE LHS text (`fun c => c.map (2 * ·)` for `Out[2*i]`),
with its own row-major helpers (not `outCoeffs`/`outBias`, not `applyAffine`/`flatIndex`), into a
`destShape` taken from the reference-measured binary64 extents, `+0` elsewhere.

**Independent enough, because** the two legs share no code with anything this slice adds or
enables: Step 0c's scatter admission, Step D's scatter branch (`scatterPlacementOrFail`,
`scatterFillOrFail`), `checkScatterF32`, the `checkPlan`/`runDensePlan32` scatter arms, and
`runDenseScatterWith` are all bypassed by the twin, and the placement is re-derived from source.
Measured on the prototype: dropping the compiler's placement bias (manifest C1/C1b) makes the oracle
DISAGREE on O2, not merely fail a pinned literal.

**What it cannot catch:** (1) a defect in the traversal both legs share — `denseValueAtWith`,
`float32Ops`, `residualizeAssignment` (pinned separately by F32-A/B bit fixtures and Task 1's 1.4);
(2) the destination-extent convention (the oracle takes `destShape` as given); (3) collisions and
out-of-range placement (every case is in range and collision-free — all surface syntax can
express); (4) any non-zero or tropical `fill` (binary32 source admits only fill `0` on sum-product: `fill := 1`
and the overflowing `-(2^128)` are refused, 15(c) refusals; Task 1's 1.5 pins `-∞` programmatically). It is also only as broad as its five programs.

**Scheduling.** It is Task 3 phase 1's FIRST step, written before the compiler edit and observed
failing (`BINARY32 SCATTER ORACLE FAILED: O1 strided, unary, carrier-discriminating: prepare
failed`, observed on today's tree). That is the earliest point it can run at all: it needs Step 0c
lifted, and Step 0c is the last door.

---

## 4. Sibling audit (skill §2): every door after this slice

Classes: **required**, **forbidden**, **(c)** = silently correct only because an upstream refusal
holds. Fixture ids refer to §5.

**Table A — case × door**

| Case | Source (Step 0c / A) | `checkPlan` / direct checkers | Float workers | binary32 workers | Named adapters | JAX | Legacy |
|---|---|---|---|---|---|---|---|
| f32 top-level scatter (sum-product, fill 0) | **required** (3.1 15(c) flip; oracle O1–O5) | **required** `checkScatterF32` (2.1, 1.1); `checkScatter` on an f32 table `dtypeNotAdmitted 1 .f32` (ScatterCheckTest fixture 9, unchanged) | **forbidden** — `runDenseScatter` guard first (1.7); `runDensePlan` guard first (2.3) | **required** `runDenseScatter32` (1.1–1.6), `runDensePlan32` arm (2.1, 2.2) | **required**, unchanged cores at `Float32` (oracle) | **forbidden**, plan-level gate first (ExecutableTest fixtures 23/24, unchanged) | **forbidden**, permanently |
| f32 scatter with inline unary factor | **required** (O1) | **required** (1.4) | **forbidden** (1.7) | **required** `float32Ops.applyUnary` via the shared traversal (1.4, O1) | **required** (O1) | **forbidden** | **forbidden** |
| scatter nonlinearity, any dtype | **forbidden** Step A (3.3) | never compiled | — | — | — | — | — |
| non-default collision policy, either carrier | **forbidden** Step A (existing) | **forbidden** `scatterReduceNotAdmitted` in the shared core (ScatterCheckTest binary64; 1.3 binary32) | **(c)** `.overwrite/.sum/.max/.min` arms of `runDenseScatterWith`: unreachable behind that clause; now via `ops.binOp` | same **(c)** | — | — | — |
| tropical / non-zero / overflowing fill, f32 | **forbidden** from source (`scatterFillOrFail`; 15(c) refusals, P3-3, P3-4) | **required**, programmatic: fill must equal `reduceId` (1.3) | — | **required** `ops.decodeConst` (1.5) | — | — | — |
| out-of-range placement (programmatic only) | unreachable | admitted by design (reference parity) | **required** silent skip (ScatterDenseTest pins) | **(c)** same shared `inBoundsPerDim` skip, no binary32 fixture; carrier-free integer code | — | — | — |
| f64 scatter (preservation) | unchanged | **required** `checkScatter` records `.float64` (1.2) | **required** (G64 gate, G1/G2) | **forbidden** `runDenseScatter32` guard first (1.7) | unchanged | scatter refused categorically, unchanged | unchanged |
| f32 scan-local scatter | **forbidden** `"{nm}: f32 scan"` (15(d), 3.2) | **forbidden** `f32UnsupportedStep i .scan` (2.x, S2) | **(c)** `runDenseScan` Float-only — F32-C | none | none | **forbidden** | **forbidden** |

**Table B — a binary64 literal at an arm binary32 now reaches**

| Site | Reached by f32 after this slice? | Class | Pin |
|---|---|---|---|
| `floatOps.decodeConst s.fill` @ `runDenseScatter` | yes | **fixed** → `ops.decodeConst` | 1.5, P1-4 |
| `denseValueAt a [] store sc` (Float traversal) @ `runDenseScatter` | yes | **fixed** → `denseValueAtWith ops` | 1.4 |
| `prev + val`, `Max.max`, `Min.min` reduce arms | no | **(c)** → `ops.binOp` | — (unreachable) |
| `checkAssign` call @ `checkScatter` | yes | **fixed** → `checkAssignCore kind` | 1.2, 1.3 |
| `.f32 _ => false` @ `scatterFillOrFail` | yes | **fixed** → native `Float32.ofInt` bits, finite only | 15(c), P3-1, P3-3, P3-4 |
| `destDtype`/`algebraForDest` @ Step D scatter branch | yes | **required**, already correct | 3.1 second guard, oracle |
| scatter-branch `resolveSource`'s `getD … dtype := .f64` | yes | **(c)** totality formality: contributes `.shape` only, and every key is validated by the `slotOf.contains` loop above it | — |

**Doors to open during the audit even though they are absent from a diff:** `runDenseScatter`,
`runDenseScatter32`, `runDensePlan`, `runDensePlan32`, `runDenseBlock`, `runDenseScan` (workers);
`checkPlan`, `checkPlanBlock`, `checkScanPlan`, `checkScatter`, `checkScatterF32` (checkers);
`packBodyOf`, `unpackBodyOf`, `runPreparedDenseOf` (adapter cores, unchanged, carrier-generic);
`requireFloat64Plan`/`validateAndConstructExecutable` (JAX, unchanged); `evalScheduled` (legacy).
Task 3's completion note re-derives both tables against the merged tree, cell by cell.

---

## 5. Tasks

| Task | Deliverable | Fixtures | Mutation cycles | Expected turns | Dispatch |
|---|---|---|---|---|---|
| 1 | carrier-parametric scatter checker + worker (`Check.lean`, `Dense.lean`) | 8 (16 `#guard`s, one new file) | G1, G2 (each run before AND after the edit) + P1-1..P1-4 = 8 runs | ~45–60 | one |
| 2 | graph admission (`EvalPlan.lean`, `Dense32.lean`) | 3 re-points + 3 new (`GraphCheckTest`, `EvalPlan32Test`) | S2 + predicted P2-1..P2-3 = 4 | ~35–45 | one |
| 3 | source admission (`Compile.lean`), the oracle, CompileTest re-points, docs | 4 re-point groups + 5 oracle cases | S1, S3, C1, C1b + predicted P3-1, P3-2 = 6 | ~80–100 | **two** (phase 1 production + fixtures green; phase 2 cycles + docs), `split-handoff-template.md` |

"Predicted" cycles: their old-strings are code that does not exist yet, so they cannot be in the
manifest. Each was run against the prototype and broke exactly the fixture named (record §4). After
your production commit, append each as a manifest entry (`task`, `file`, `old`, `new`, `targets`,
and `expect` COPIED from your own observed build log), run it, and keep it. In those tables `\|` is a
Markdown escape; the source has a plain `|`.

---

### Task 1 — carrier-parametric checked scatter

**Files:** `leanncd/LeanNCD/Eval/Plan/Check.lean`, `leanncd/LeanNCD/Eval/Plan/Dense.lean`,
new `leanncd/test/Eval/Plan/ScatterDense32Test.lean`, `leanncd/test/Eval/Plan/ScatterCheckTest.lean`
(prose only), `leanncd/lakefile.toml`.

**Symbols (`rg -n`, window-read):** `CheckedScatterPlan @ Check.lean`, `checkScatter @ Check.lean`,
`checkAssignCore @ Check.lean`, `checkAssignF32 @ Check.lean` (docstring only),
`runDenseScatter @ Dense.lean`, `denseValueAt @ Dense.lean` (docstring only),
`denseValueAtWith @ Dense.lean`, `floatOps`/`float32Ops @ Dense.lean`,
`ScatterDenseTest.srcCompute`/`srcRead`/`placed`/`sigsFor`/`collisionSigs`/`collisionCompute`/`collisionScatter @ test/Eval/Plan/ScatterDenseTest.lean`,
`t32 @ test/Eval/Plan/KernelDense32Test.lean`, "fixture 9" section @ `ScatterCheckTest.lean`.

**Step 1 — gate G64, on the UNMODIFIED tree.**

```bash
bash leanncd/scripts/lake-build.sh leanncd Eval.Plan.ScatterCheckTest Eval.Plan.ScatterDenseTest \
  Eval.Plan.ScatterCompileTest Eval.Plan.GraphDenseTest Eval.Plan.DifferentialTest
bash leanncd/scripts/mutation-manifest.sh leanncd papers/f32d_mutations.json G1 G2
```

Both must succeed (G1, G2 PASS). They prove the binary64 fixtures bite on the two lines of
`runDenseScatter` you are about to move.

**Step 2 — `Check.lean`.** Replace the `CheckedScatterPlan` structure (and its docstring) with:

<!-- block:t1-checked -->
```lean
/-- Evidence that one `ScatterPlan` satisfies every local invariant, TOGETHER WITH the storage kind
    it was validated for. Same `private mk ::` boundary as `CheckedAssignPlan`: `checkScatter`
    (`.float64`) and `checkScatterF32` (`.float32`) are the only ways to obtain one, and each scatter
    worker door (`runDenseScatter`, `runDenseScatter32`) refuses the other carrier's evidence as its
    first statement.

    Deliberately stores ONLY the raw plan and its kind — not the `CheckedAssignPlan` the core
    returned for the compute half. A scatter's worker is source-driven and must not be able to hand
    that evidence to `runDenseAssign`: doing so publishes the SOURCE-shaped compute result under the
    destination's name, which is the exact silent-wrong-answer failure the rejected "widen
    `AssignPlan`" design was measured to produce. -/
structure CheckedScatterPlan where private mk ::
  raw : ScatterPlan
  storageKind : LeanNCD.StorageKind
  deriving Repr
```

Replace the first three lines of `def checkScatter` (signature through the `checkAssign` call) with:

<!-- block:t1-core-head -->
```lean
private def checkScatterCore (kind : LeanNCD.StorageKind) (sigs : Array TensorSignature)
    (s : ScatterPlan) : Except PlanError CheckedScatterPlan := do
  let _ ← checkAssignCore kind sigs s.compute (some s.destShape)
```

and its last line `return CheckedScatterPlan.mk s` with:

<!-- block:t1-core-tail -->
```lean
  return CheckedScatterPlan.mk s kind

/-- The FLOAT64 scatter checker: the S-A policy, unchanged in every clause, now naming its storage
    kind on the evidence it returns. Still rejects `f32` at the destination and at every read. -/
def checkScatter (sigs : Array TensorSignature) (s : ScatterPlan) :
    Except PlanError CheckedScatterPlan :=
  checkScatterCore .float64 sigs s

/-- The FLOAT32 scatter checker, through the same private core: identical fill, collision-policy,
    and placement clauses, with the compute half checked by `checkAssignCore .float32` (f32/bool
    dtypes, `admittedAlgebrasForF32`). A sibling of `checkScatter`, never a relaxation of it. -/
def checkScatterF32 (sigs : Array TensorSignature) (s : ScatterPlan) :
    Except PlanError CheckedScatterPlan :=
  checkScatterCore .float32 sigs s
```

Docstring edits, same file (the long docstring now sits on `checkScatterCore`): "the compute half
through the shared `checkAssign` core" → "…through `checkAssignCore kind`"; replace the sentence
"`ScalarConst.f32` is unreachable in a checked plan for the same reason." with "Under `.float32` the
same argument runs over `admittedAlgebrasForF32`, so a coherent fill is an `.f32` or `.bool`
constant." In `checkAssignF32`'s docstring, replace "since a binary32 scatter — the one construct
that needs it — is deferred to slice F32-D" with "a binary32 scatter reaches the core through
`checkScatterF32`, which passes `some s.destShape` to `checkAssignCore` directly".

**Step 3 — `Dense.lean`.** Replace `def runDenseScatter` (from its signature line through
`return { shape := destShape, data := data }`) with the block below. The long docstring above it
stays, now on `runDenseScatterWith`; in it replace "through the shared `denseValueAt`" with
"through the shared `denseValueAtWith ops`". In `denseValueAt`'s docstring replace "and the only one
`runDenseScatter` uses" with "used by `runDenseAssignAt`".

<!-- block:t1-dense -->
```lean
private def runDenseScatterWith {α : Type} (ops : ScalarKernelOps α) (s : ScatterPlan)
    (store : Array (DenseTensorOf α)) : Except PositionalInputError (DenseTensorOf α) := do
  let a := s.compute
  -- A scatter is admitted only as a top-level step, so its compute half runs at the empty context —
  -- the same coordinate `runDenseAssign` supplies. Validated rather than assumed: `checkScatter`
  -- deliberately does not check `compute.contextShape` (`checkPlan`'s `contextCheck` owns that), so
  -- a non-empty one must fail loud here instead of silently binding no context position.
  validateContext a []
  validateStore a store
  let destShape := s.destShape.toList
  -- The placement map's fields already ARE `AffineMap`'s, row per destination dimension and width per
  -- source position, so `applyAffine` applies as-is — no second affine evaluator.
  let placement : AffineMap := { coeffs := s.outCoeffs, bias := s.outBias }
  let fill ← ops.decodeConst s.fill
  let mut data : Array α := Array.replicate (destShape.foldl (· * ·) 1) fill
  let mut writtenBy : Std.HashMap Nat (List Nat) := {}
  for sc in allCoords a.outputShape.toList do
    let val ← denseValueAtWith ops a [] store sc
    let dc := applyAffine placement sc
    if inBoundsPerDim destShape dc then
      let oc := dc.map Int.toNat
      let fi := flatIndex destShape oc
      let prev := data.getD fi fill
      match s.reduce with
      | .rejectCollisions =>
          match writtenBy[fi]? with
          | some firstSrc => throw (.scatterCollision oc firstSrc (sc.map Int.toNat))
          | none =>
              writtenBy := writtenBy.insert fi (sc.map Int.toNat)
              data := data.set! fi val
      | .overwrite => data := data.set! fi val
      | .sum => data := data.set! fi ((← ops.binOp .add) prev val)
      | .max => data := data.set! fi ((← ops.binOp .max) prev val)
      | .min => data := data.set! fi ((← ops.binOp .min) prev val)
  return { shape := destShape, data := data }

/-- Execute one checked BINARY64 scatter. **The storage-kind guard is first**, before the context
    and store checks: binary32 evidence executed here would answer a binary32 question in binary64
    with no diagnostic anywhere. -/
def runDenseScatter (c : CheckedScatterPlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  unless c.storageKind == .float64 do
    throw (.storageKindMismatch .float64 c.storageKind)
  runDenseScatterWith floatOps c.plan store

/-- Execute one checked BINARY32 scatter, natively: `fill` decoded by `float32Ops`, every compute
    value from the shared traversal over `float32Ops`, nothing widened. **The storage-kind guard is
    first**, the mirror of `runDenseScatter`'s. -/
def runDenseScatter32 (c : CheckedScatterPlan) (store : Array DenseTensor32) :
    Except PositionalInputError DenseTensor32 := do
  unless c.storageKind == .float32 do
    throw (.storageKindMismatch .float32 c.storageKind)
  runDenseScatterWith float32Ops c.plan store
```

**Step 4 — G64 again** (same two commands as step 1): green, and G1/G2 PASS, now against
`runDenseScatterWith`.

**Step 5 — fixtures.** Add `"Eval.Plan.ScatterDense32Test"` to `lakefile.toml`'s globs after
`"Eval.Plan.ScatterDenseTest"`, and create the test file by copying it:

```bash
cp papers/f32d_files/ScatterDense32Test.lean leanncd/test/Eval/Plan/ScatterDense32Test.lean
```

Do not retype it; it is the file that was compiled and run (record §3). What it pins:

| Fixture | Donor (`ScatterDenseTest` unless noted) | Pins |
|---|---|---|
| 1.1 | fixture 1 `placed #[6] #[#[2]] #[0]`, algebra → `admittedAlgebraF32` | native placement + `+0` fill: `[1065353216, 0, 1073741824, 0, 1077936128, 0]` |
| 1.2 | same | `checkScatterF32` stamps `.float32`, `checkScatter` `.float64`; `checkScatterF32` on an f64 table → `dtypeNotAdmitted 1 .f64` |
| 1.3 | same, `fill := admittedAlgebra.reduceId`; `reduce := .sum` | fill and collision clauses run under `.float32`: `scatterFillNotIdentity (.f64 0) (.f32 0)`, `scatterReduceNotAdmitted .sum` |
| 1.4 | `srcRead`/`srcCompute`, three terms, `unary := some .sqrt` on the first | native rounding with a unary factor: `[0, 0, 1080033280, 0, 1082654720, 0]`; binary64 lane 0 is `1.0`, narrowing to `1065353216` ≠ `0` |
| 1.5 | `maxScatter` (algebra → `admittedAlgebraF32Max`) | `-∞` fill decoded by `float32Ops`: `4286578688` in the odd cells |
| 1.6 | `collisionScatter` retagged | `scatterCollision [0] [0, 0] [0, 1]` |
| 1.7 | `srcCompute` with `contextShape := #[1]` | each door's guard precedes `validateContext`/`validateStore` (wrong carrier → `storageKindMismatch`; right carrier → `contextShapeMismatch #[1] []`) |
| 1.8 | `KernelDense32Test` fixture 16 `boolSourceSigs32`, as a scatter | a `.bool`-tagged source is gathered unchanged: `[1048576000, 0, 1056964608, 0, 1065353216, 0]` |

**Step 6 — `ScatterCheckTest.lean` fixture 9, prose only** (`rg -n "fixture 9" …`). Its guards stay
and stay true (`checkScatter` is still the binary64 checker). Replace the rationale "top-level binary32
scatter is slice F32-D, so there is no f32 scatter worker, and the whole point of keeping the
scatter checker Float-backed is that direct construction cannot acquire evidence for an operation
with no binary32 worker" with: "`checkScatter` is the binary64 checker; binary32 evidence comes only
from its sibling `checkScatterF32` (`ScatterDense32Test`), and each worker door refuses the other
carrier's evidence." Also replace "`checkScatter` calls ORDINARY `checkAssign`, never
`checkAssignF32`" with "`checkScatter` runs the shared core at `.float64`".

**Step 7 — cycles.** `bash leanncd/scripts/mutation-manifest.sh --task 1 leanncd papers/f32d_mutations.json`
(G1, G2: both PASS). Then append and run the four predicted cycles, all on `Dense.lean`/`Check.lean`,
target `Eval.Plan.ScatterDense32Test`:

| Label | old → new | Prototype: fixture that broke |
|---|---|---|
| P1-1 | delete the `unless c.storageKind == .float64 do` guard (2 lines) in `runDenseScatter` | 1.7, first guard (got `contextShapeMismatch`) |
| P1-2 | delete the `.float32` guard (2 lines) in `runDenseScatter32` | 1.7, third guard |
| P1-3 | `return CheckedScatterPlan.mk s kind` → `… s .float64` | 1.1, 1.2 first guard, 1.4 (binary32 guard), 1.5, 1.6, 1.7 first two guards |
| P1-4 | `let fill ← ops.decodeConst s.fill` → `let fill := ops.zero` | 1.5 only |

**Commit:** `feat(leanncd): carrier-parametric checked scatter (F32-D Task 1)`.

---

### Task 2 — graph-level admission

**Files:** `leanncd/LeanNCD/Eval/Plan/EvalPlan.lean`, `leanncd/LeanNCD/Eval/Plan/Dense32.lean`,
`leanncd/test/Eval/Plan/GraphCheckTest.lean`, `leanncd/test/Eval/Plan/EvalPlan32Test.lean`.

**Symbols:** `checkPlan @ EvalPlan.lean` (capability loop, `localCheck`'s `.scatter s` arm, the
docstring and the "CAPABILITY SECOND" comment), `PlanStepError.f32UnsupportedStep @ EvalPlan.lean`
(docstring), `runDensePlan32 @ Dense32.lean` (arm + docstring), module docstring @ `Dense32.lean`;
`f32UnsupportedStepOrder`, `stepOrderScatter`, `f32ScatterPlan`, `f32Scan`, `f32ScanPlan`,
`isF32Unsupported`, `storageOf`, `idNode` @ `GraphCheckTest.lean`; `runGraph32`, `bitsAt` @
`EvalPlan32Test.lean`; `t32 @ KernelDense32Test.lean`.

**Step 1 — `EvalPlan.lean`.** In the `.float32` capability loop replace
`| .scatter _   => throw (.f32UnsupportedStep ni .scatter)` with:

<!-- block:t2-cap -->
```lean
      | .scatter _   => pure ()
```

and replace the `localCheck` `.scatter s` arm's `match checkScatter raw.tensorSigs s with` line so the
arm reads:

<!-- block:t2-local -->
```lean
          | .scatter s =>
              match (match storageKind with
                     | .float64 => checkScatter raw.tensorSigs s
                     | .float32 => checkScatterF32 raw.tensorSigs s) with
              | .error e => throw (.assign (.nodeError ni e))
```

Prose: the "CAPABILITY SECOND" comment → "binary32 admits assignments, the two nonlinearity
operations (F32-B), and top-level scatter (F32-D); scan (F32-C) is refused"; the scatter
`localCheck` comment → say the graph's storage kind selects `checkScatter`/`checkScatterF32`;
`f32UnsupportedStep`'s docstring → drop "scatter is slice F32-D".

**Step 2 — `Dense32.lean`.** Replace `| .scatter _ => throw (.storageKindMismatch .float32 .float64)`
with the block below. In `runDensePlan32`'s docstring and the module docstring, "scatter and scan
evidence is refused" becomes "scan evidence is refused"; scatter now runs `runDenseScatter32`, which
re-checks its evidence's kind first.

<!-- block:t2-dense32 -->
```lean
    | .scatter s =>
        store := store.set! s.plan.compute.destinationSlot (← runDenseScatter32 s store)
```

**Step 3 — `GraphCheckTest.lean` re-points** (all three observed on the prototype):

(a) Fixture 14 second half: replace
`#guard errOf (checkPlan f32UnsupportedStepOrder) == some (.f32UnsupportedStep 2 .scatter)` with
the line below, and re-word the section prose (the graph is now accepted; its index claim moves to
the new witness in (c)).

<!-- block:t2-g14 -->
```lean
#guard storageOf (checkPlan f32UnsupportedStepOrder) == some LeanNCD.StorageKind.float32
```

(b) Fixture 16 scatter: replace `#guard errOf (checkPlan f32ScatterPlan) == some (.f32UnsupportedStep 0 .scatter)`
with the line below, and DELETE the `#guard !(isF32Unsupported 0 .scatter …)` control after it (it
discriminated a binary32-specific refusal that no longer exists). Re-word "The scatter and scan cases
are rejections" → "The scan case is a rejection; the scatter case is an acceptance since F32-D".

<!-- block:t2-g16 -->
```lean
#guard storageOf (checkPlan f32ScatterPlan) == some LeanNCD.StorageKind.float32
```

(c) The index witness, re-pointed: insert immediately before the `-- Axiswise.` comment (after the
scan case's binary64 control). Correct reports `3 .scan`; a loop keeping the LAST rejection would
report `4`, a filtered sublist of refused kinds `0`, and a loop that still refused scatter `2 .scatter`.
Its binary64 twin reports `duplicateDestination 2 1 3`, not a capability error.

<!-- block:t2-g14c -->
```lean
/-- Fixture 14's index witness, re-pointed by F32-D: `f32UnsupportedStepOrder` (now accepted) with
    `f32Scan` appended TWICE, at outer indices 3 and 4, so first-rejection-wins (3) and
    last-rejection-wins (4) disagree. -/
def f32StepOrderWithScan : RawEvalPlan :=
  { f32UnsupportedStepOrder with
    steps := f32UnsupportedStepOrder.steps ++ #[.scan f32Scan, .scan f32Scan] }

#guard errOf (checkPlan f32StepOrderWithScan) == some (.f32UnsupportedStep 3 .scan)

#guard !(isF32Unsupported 3 .scan (checkPlan
  { f32StepOrderWithScan with
    tensorSigs := f32StepOrderWithScan.tensorSigs.map (fun s => { s with dtype := .f64 })
    steps := #[ .assign (idNode 1 0)
              , .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[2], fn := .relu }
              , .scatter (stepOrderScatter admittedAlgebra), .scan f32Scan, .scan f32Scan ] }))
```

**Step 4 — `EvalPlan32Test.lean`.** Add `import Eval.Plan.GraphCheckTest` and, after the existing
`open`, `open LeanNCD.Eval.Plan.GraphCheckTest (f32ScatterPlan f32UnsupportedStepOrder)`. Append
before `end`:

<!-- block:t2-evalplan32 -->
```lean
/-! ## F32-D fixtures 2.1–2.3: binary32 scatter through the graph worker

Donors: `GraphCheckTest.f32ScatterPlan` (fixture 16, `Out[2*i] := X[i]`) and
`GraphCheckTest.f32UnsupportedStepOrder` (`[assign, pointwise relu, scatter]`). -/

-- 2.1: `X = [1, 2, 3]` lands at 0, 2, 4 of slot 1; the odd cells keep `fill = +0`.
#guard bitsAt (runGraph32 f32ScatterPlan #[ t32 [3] #[0x3f800000, 0x40000000, 0x40400000] ]) 1
  == some #[1065353216, 0, 1073741824, 0, 1077936128, 0]

-- 2.2: the scatter reads the preceding pointwise result. `X = [1.5, 2.5]` land at 0 and 2 of slot 3;
-- `X = [1.5, -2.5]` shows relu ran before the scatter read (lane 1 becomes `+0`).
#guard bitsAt (runGraph32 f32UnsupportedStepOrder #[ t32 [2] #[0x3fc00000, 0x40200000] ]) 3
  == some #[1069547520, 0, 1075838976, 0]
#guard bitsAt (runGraph32 f32UnsupportedStepOrder #[ t32 [2] #[0x3fc00000, 0xc0200000] ]) 3
  == some #[1069547520, 0, 0, 0]

-- 2.3: the binary64 graph worker refuses the binary32 scatter graph FIRST (before arity: no inputs).
#guard (match checkPlan f32ScatterPlan with
  | .ok c => match runDensePlan c #[] with | .error e => some e | .ok _ => none
  | .error _ => none) == some (.storageKindMismatch .float64 .float32)
```

**Step 5 — cycles.** `mutation-manifest.sh --task 2 …` (S2: PASS). Append and run the predicted
cycles (targets `Eval.Plan.GraphCheckTest Eval.Plan.EvalPlan32Test`):

| Label | old → new | Prototype: fixtures that broke |
|---|---|---|
| P2-1 | capability arm `\| .scatter _   => pure ()` → `\| .scatter _   => throw (.f32UnsupportedStep ni .scatter)` | (a), (b), (c) first guard, 2.1, 2.2 (both), 2.3 |
| P2-2 | `\| .float32 => checkScatterF32 raw.tensorSigs s) with` → `\| .float32 => checkScatter raw.tensorSigs s) with` | (a), (b), 2.1, 2.2 (both), 2.3 |
| P2-3 | the two-line `runDensePlan32` `.scatter s =>` arm → `\| .scatter _ => pure ()` | 2.1, 2.2 (both) |

**Commit:** `feat(leanncd): admit binary32 scatter in checkPlan and runDensePlan32 (F32-D Task 2)`.

---

### Task 3 — source admission, the oracle, and documentation (two dispatches)

**Files:** `leanncd/LeanNCD/Eval/Plan/Compile.lean`, `leanncd/LeanNCD/Eval/Plan/Error.lean` (doc
only), new `leanncd/test/Eval/Plan/Scatter32OracleTest.lean`, `leanncd/test/Eval/Plan/CompileTest.lean`,
`leanncd/lakefile.toml`, `leanncd/LeanNCD/Eval/Plan/AGENTS.md`, the papers in step 9.

**Symbols:** `checkF32Stmt`, `f32CapabilityCheck`, `scatterFillOrFail`, `prepareEvalPlan` (the Step 0c
comment), the f32 section docstring above `checkF32Stmt` @ `Compile.lean`; `CapabilityError.unsupportedDtype`
docstring @ `Error.lean`; `f32ScatterProg`, `f32ScatterThenScanProg`, `f32ScanThenScatterProg`,
`f32ScatterReluProg`, `f32MixedScatterReluProg`, `f32ScanProg`, `f32ScanSig`, `f32ScanAxL`,
`f32IdentitySig`, `causeOf`, `errOf`, "Fixture 2.9", "Fixture FW2" @ `CompileTest.lean`.

#### Phase 1 (production + fixtures, one commit, green)

**Step 1 — oracle first.** Create `test/Eval/Plan/Scatter32OracleTest.lean` (command below),
register `"Eval.Plan.Scatter32OracleTest"` in `lakefile.toml` after `"Eval.Plan.Adapter32Test"`, and
build it: it must FAIL with `BINARY32 SCATTER ORACLE FAILED: O1 strided, unary,
carrier-discriminating: prepare failed` (observed on today's tree). If it fails any other way, STOP.
(The twin tensor is `Src`, not `T`: `T(` and `C(` are DSL tokens inside `tlprog!`.)

```bash
cp papers/f32d_files/Scatter32OracleTest.lean leanncd/test/Eval/Plan/Scatter32OracleTest.lean
```

Do not retype it. Its module docstring states the design and its limits (§3.5). Cases, each
`scatter` vs `twin` + `place` into `destShape`:

| Case | Scatter LHS / RHS | `place`, `destShape` | Observed bits | Also pins |
|---|---|---|---|---|
| O1 | `Out[2*i] := sqrt(A[i]) + B[i] + Z[i]` | `2i`, `[6]` | `[0, 0, 1080033280, 0, 1082654720, 0]` | unary factor; carrier contrast (binary64 lane 0 = 1) |
| O2 | `Out[2*i + 1] := A[i] · B[i]` | `2i+1`, `[6]` | `[0, 1266683904, 0, 1050253722, 0, 1050253722]` | placement bias (C1b) |
| O3 | `Y[i, i] := A[i] + B[i]` | `(i, i)`, `[3, 3]` | `[1266679808, 0, 0, 0, 1050253722, 0, 0, 0, 1077936128]` | diagonal (no `.affine` slot) |
| O4 | `Out[2*i, 2*j] := X[i, j]` | `(2i, 2j)`, `[4, 6]` | 24 lanes (in the file) | two extents; swapped rows would differ |
| O5 | `W[i] := A[i]·A[i]` then `Out[2*i] := W[i] + B[i] + Z[i]` | `2i`, `[6]` | `[0, 0, 1093140480, 0, 1069547520, 0]` | the scatter's OWN rounding: lane 0 is `0` natively, `1065353216` with the scatter half in binary64 over native `W` (the file's contrast), `1073741824` whole-program binary64 |

O2/O3/O4 are not carrier discriminators (one rounding each, so binary64-then-narrow agrees); they
pin placement.

**Step 2 — `Compile.lean`.** Delete `checkF32Stmt` and its docstring. Replace `f32CapabilityCheck`
(docstring and body) with:

<!-- block:t3-cap -->
```lean
/-- The whole-schedule binary32 capability pass: top-level scheduled statements in SOURCE order,
    first rejection wins. Every top-level statement kind is admitted (assignments since F32-A, their
    nonlinearities and inline unary factors since F32-B, top-level scatter since F32-D; a
    `.recurMorphism` is refused dtype-blind by `capabilityPreflight`). A `.scan`/`.scanPre` node is
    refused as an unsupported OUTER step kind without descending into its blocks — this makes no
    precedence claim against an independently invalid scan body, and a scan's own statements are
    not top-level statements. -/
def f32CapabilityCheck (stmts : List ScanStmt) : Except CapabilityError Unit := do
  for sc in stmts do
    match sc with
    | .plain _ => pure ()
    | .scan nm .. => throw (.unsupportedDtype s!"{nm}: f32 scan")
    | .scanPre nm .. => throw (.unsupportedDtype s!"{nm}: f32 scan")
```

In `scatterFillOrFail` replace the two-line "unreachable" comment and `| .f32 _    => false` with the
line below; in its docstring's "Admitted:" sentence add "and a binary32 sum-product scatter with
`fill = 0` (binary32 `+0`, bits `0`, compared as native `Float32.ofInt` bits)"; and in the clause
"which an `Int` fill cannot denote at all" (anchor `rg -n "fill cannot denote at"`) insert after
"all": " (binary32 additionally requires the converted value to be finite, since
`Float32.ofInt (-(2^128))` IS `-∞`; the binary64 arm has the same overflow at `2^1024` and does not
refuse it — a pre-existing gap)".

<!-- block:t3-fill -->
```lean
    | .f32 bits => (Float32.ofInt fill).isFinite && bits == (Float32.ofInt fill).toBits
```

Prose in `Compile.lean`: the f32 section docstring's "each names the DEFERRED SLICE that will admit
it (F32-C scan, F32-D scatter)" → "(F32-C scan)"; Step 0c's comment in `prepareEvalPlan` drop
"top-level scatter"; the header comment that says Step 0c `f32CapabilityCheck` refuses constructs —
keep, it is still true for scans. `Error.lean`'s `unsupportedDtype` docstring: move
`"{name}: f32 scatter"` into the "NO PRODUCER LEFT" sentence ("as of F32-D").

**Step 3 — `CompileTest.lean` re-points** (all observed on the prototype):

(a) Fixture 15(c): replace its one `#guard causeOf … "Y: f32 scatter"` with the two guards below
(re-word its comment: "(c) top-level scatter: ACCEPTED since F32-D").

<!-- block:t3-15c -->
```lean
#guard ((prepareEvalPlan f32ScatterProg f32IdentitySig).toOption.map (·.plan.storageKind))
  == some LeanNCD.StorageKind.float32

#guard ((prepareEvalPlan f32ScatterProg f32IdentitySig).toOption.map (fun p =>
    match p.plan.raw.steps with
    | #[.scatter s] => s.fill == .f32 0 && s.compute.algebra == admittedAlgebraF32
        && s.destShape == #[6] && p.plan.raw.tensorSigs[s.compute.destinationSlot]?.map (·.dtype) == some .f32
    | _ => false))
  == some true
```

Then append the two refusals the new `.f32` arm must make (cycles P3-3, P3-4 fail without them):

<!-- block:t3-15c-refuse -->
```lean
-- 15(c) refusals. A fill the algebra's identity does not equal (`1` on sum-product) is refused...
def f32ScatterFill1Prog : ScheduledProgram :=
  { f32ScatterProg with
    stmts := [.plain (.scatter "Y" [.affine (.scale 2 axI1)]
      { body := { terms := [{ factors := [.read "X" [.axis axI1]] }] }, nonlin := .identity }
      { fill := 1, reduce := .rejectCollisions })] }

#guard causeOf (prepareEvalPlan f32ScatterFill1Prog f32IdentitySig) ==
  some { cause := .capability (.scatterOptsNotAdmitted "Y: fill"), warnings := [] }

-- ...and so is an integer past binary32's range: `Float32.ofInt (-(2^128))` rounds to `-∞`, which IS
-- `admittedAlgebraF32Max.reduceId` bit for bit (4286578688), so only the finiteness test refuses it.
def f32ScatterOverflowFillProg : ScheduledProgram :=
  { f32ScatterProg with
    stmts := [.plain (.scatter "Y" [.affine (.scale 2 axI1)]
      { body := { terms := [{ factors := [.read "X" [.axis axI1]] }] }, nonlin := .identity
      , agg := .max }
      { fill := -(2^128), reduce := .rejectCollisions })] }

#guard causeOf (prepareEvalPlan f32ScatterOverflowFillProg f32IdentitySig) ==
  some { cause := .capability (.scatterOptsNotAdmitted "Y: fill"), warnings := [] }
```

(b) Fixture 2.9: in the forward-order guard change `"Y: f32 scatter"` to `"S: f32 scan"` (the
scatter is admitted and the traversal continues); the reversed guard is unchanged. Source order is
now pinned between two scans — append after the reversed guard:

<!-- block:t3-29 -->
```lean
-- Since F32-D the scatter above is admitted, so source order is pinned between two SCANS instead:
-- `f32ScanProg`'s node and a renamed clone (`T`, `T0`, `Xt`, axis `m`).
def f32ScanAxM : AxisSpec := ⟨"m", 7, .nat⟩

def f32TwoScanProg : ScheduledProgram :=
  { decls := f32ScanProg.decls ++
      [ .iter f32ScanAxM 3, .typedTensor .f32 "T0" [], .typedTensor .f32 "Xt" [f32ScanAxM]
      , .typedTensor .f32 "T" [f32ScanAxM] ]
  , stmts := [ f32ScanProg.stmts[0]!
             , .scan "T" [f32ScanAxM]
                 [ .assign "T" [.iterAt f32ScanAxM 0]
                     { body := { terms := [{ factors := [.read "T0" []] }] }, nonlin := .identity } ]
                 [ .assign "T" [.iterNext f32ScanAxM]
                     { body := { terms := [ { factors := [.read "T" [.axis f32ScanAxM]] }
                                          , { factors := [.read "Xt" [.axis f32ScanAxM]] } ] }
                     , nonlin := .identity } ]
                 false ]
  , env := {}
  , extNames := insert "S0" (insert "X" (insert "T0" (insert "Xt" (∅ : Finset String))))
  , explicitSizes := f32ScanProg.explicitSizes.insert f32ScanAxM.uid 3 }

#guard causeOf (prepareEvalPlan f32TwoScanProg f32ScanSig) ==
  some { cause := .capability (.unsupportedDtype "S: f32 scan"), warnings := [] }
#guard causeOf (prepareEvalPlan { f32TwoScanProg with stmts := f32TwoScanProg.stmts.reverse } f32ScanSig) ==
  some { cause := .capability (.unsupportedDtype "T: f32 scan"), warnings := [] }
```

(c) Fixture FW2: `f32ScatterReluProg` alone is no longer a Step 0c rejection, so the order witness
needs a statement Step 0c still refuses. Keep `f32ScatterReluProg`, its `capabilityPreflight` guard,
and FW2b unchanged. Replace the FW2a `run_cmd` with the block below (re-word the section prose: the
witness is now "the relu scatter followed by 2.9's scan"; Step A's competing answer is the scatter
nonlinearity, Step 0c's is the scan).

<!-- block:t3-fw2 -->
```lean
-- Since F32-D Step 0c admits the scatter itself, so on its own this program reaches Step A.
#guard causeOf (prepareEvalPlan f32ScatterReluProg f32IdentitySig) ==
  some { cause := .capability (.unsupportedNonlin "Y: scatter nonlinearity"), warnings := [] }

-- The witness: the relu scatter, then fixture 2.9's f32 scan. Step A alone reports the scatter.
def f32ScatterReluThenScanProg : ScheduledProgram :=
  { f32ScatterThenScanProg with
    stmts := [f32ScatterReluProg.stmts[0]!, f32ScatterThenScanProg.stmts[1]!] }

#guard errOf (capabilityPreflight f32ScatterReluThenScanProg)
  == some (.unsupportedNonlin "Y: scatter nonlinearity")

-- FW2a: through `prepareEvalPlan` Step 0c's scan payload arrives instead.
run_cmd do
  match prepareEvalPlan f32ScatterReluThenScanProg f32IdentitySig with
  | .error { cause := .capability (.unsupportedDtype "S: f32 scan"), warnings := [] } => pure ()
  | .error { cause := .capability c, .. } =>
      throwError s!"fixture FW2a: Step 0c did not precede Step A — got capability {repr c}"
  | .error _ => throwError "fixture FW2a: rejected, but not at the capability tier"
  | .ok _ => throwError "fixture FW2a: accepted an f32 scan"
```

**Step 4 — build** the whole tree (§2 build command): green, including the oracle (all five cases
agree). Commit: `feat(leanncd): admit binary32 top-level scatter from source (F32-D Task 3)`.
Hand phase 2 the SHA via `split-handoff-template.md` with this task's symbol list above.

#### Phase 2 (cycles + documentation, one commit)

**Step 5 — cycles.** `mutation-manifest.sh --task 3 --out <scratch>/t3.md leanncd papers/f32d_mutations.json`
(S1, S3, C1, C1b: all PASS; C1b's `expect` was observed on the prototype — if it does not match
your log exactly, STOP). Then append and run (targets `Eval.Plan.CompileTest Eval.Plan.Scatter32OracleTest`):

| Label | old → new | Prototype: what broke |
|---|---|---|
| P3-1 | the `.f32 bits => …` arm → `\| .f32 _ => false` | 15(c) both guards; oracle `O1 … prepare failed` |
| P3-2 | `\| .plain _ => pure ()` → `\| .plain (.scatter nm ..) => throw (.unsupportedDtype s!"{nm}: f32 scatter")` then `\| .plain _ => pure ()` | 15(c) both, 2.9 forward, FW2 relu-alone, FW2a (`got capability … "Y: f32 scatter"`), oracle O1 |
| P3-3 | the `.f32 bits => …` arm → `\| .f32 bits => true` | both 15(c) refusals |
| P3-4 | drop the `isFinite &&` conjunct | the overflow refusal only |

**Step 6 — full manifest.** Run every entry (no `--task`), `--out` to a scratch table; 8/8 plus
your appended 9 predicted cycles must PASS. Paste the table into your report.

**Step 7 — `Plan/AGENTS.md`** (injected sections are 692 chars; keep them under 3k). Code Map:
`Check.lean` row → "`checkScatter`/`checkScatterF32` over one private `checkScatterCore kind` →
`CheckedScatterPlan` (records `storageKind`)"; `Dense.lean` row → replace the "`runDenseScatter` is
**Float-only** …" sentence with "Scatter doors: `runDenseScatter` (guarded `.float64`) and
`runDenseScatter32` (guarded `.float32`) over one private `runDenseScatterWith ops`"; `Dense32.lean`
row → "`.assign`/`.pointwise`/`.axiswise`/`.scatter` natively; `.scan` refused as
`storageKindMismatch .float32 .float64`". Contracts, "Current binary32 boundary": add `.scatter`
(top-level) to admitted; refused becomes `.scan` only (`"{nm}: f32 scan"`, `f32UnsupportedStep i
.scan`, `runDensePlan32`); "`runDenseBlock`/`runDenseScan` are Float-only and are safe only because
of those refusals — F32-C inherits them"; add "Binary32 scatter's independent oracle:
`Scatter32OracleTest`". Pitfalls "A (c) cell…": drop `runDenseScatter` from the list. Entry Points
"An oracle that is neither evaluator": add the binary32 scatter oracle.

**Step 8 — value-grep, every document** (the stale values, not the vocabulary):

```bash
rg -n "f32 scatter" leanncd/LeanNCD leanncd/test papers --glob '!papers/f32d_*'
rg -n "F32-D" leanncd papers --glob '!papers/f32d_*'
rg -n "f32UnsupportedStep [0-9a-z]+ \.scatter|scatter[^\n]*storageKindMismatch \.float32 \.float64" leanncd papers --glob '!papers/f32d_*'
rg -n "runDenseScatter[^3W]*(Float-only|Float-backed)|Float-backed[^\n]*checkScatter|checkScatter[^\n]*Float-backed" leanncd papers --glob '!papers/f32d_*'
rg -n "mixed storage, f32 scan, and f32 scatter|mixed storage, f32 scan, f32" papers --glob '!papers/f32d_*'
```

Allowed to remain: the legacy evaluator's own docs (`Eval/Eval.lean`, `Eval/Scan.lean`,
`test/Eval/ScanTest.lean` fixtures 11/12, `Eval/AGENTS.md`) — the legacy evaluator refuses f32
permanently; historical close-out sections of `f32_evalplan.md`/`f32b_evalplan.md` (append a dated
note, never rewrite history); the new `"{name}: f32 scatter"` producer-less mention in `Error.lean`.
Every other hit gets fixed.

**Step 9 — papers** (find each with the `rg` shown; edit only those lines):
- `papers/f32_evalplan.md`: `rg -n "F32-D — top-level scatter|F32-D second|probably reuses F32-D" papers/f32_evalplan.md`
  — §1.3 item 3 and §1.4 item 2: append "**Landed by `f32d_evalplan.md`.**"; §1.4 item 3's
  "unverified" bullet → state §1.3 of this plan's finding (no shared path; only `scatterDestExtent`).
- `papers/f32b_evalplan.md`: `rg -n "F32-D" papers/f32b_evalplan.md` — §1.3's F32-D bullet: append
  "Landed by `f32d_evalplan.md`, except the nonlinearity, which is refused for every dtype
  (policy)"; the two §3.5 table rows marked **F32-D**: append "closed by F32-D (see
  `f32d_evalplan.md` §4)"; do not re-classify the historical cells.
- `papers/backend_missing_functionality.md`: `rg -n "F32-D|f32 scatter" papers/backend_missing_functionality.md`
  — the "Binary32 beyond the assignment fragment" row and item 4: remove top-level scatter (F32-D)
  from what remains; the two "(mixed storage, f32 scan, f32 scatter)" lists → "(mixed storage, f32
  scan)"; the 10/16/6 split is UNCHANGED (say so).
- `papers/wave_f_capability_manifest.md`: `rg -n "F32-D" papers/wave_f_capability_manifest.md` —
  "and top-level scatter likewise (F32-D)" → "top-level scatter is admitted natively since F32-D".
- `papers/scatter_affine_lhs_writes.md`: `rg -n "binary32 scatter|f32 scatter" papers/scatter_affine_lhs_writes.md`
  — append a dated note that binary32 top-level scatter landed in F32-D.
- `papers/eval_ir.md`: `rg -n "float32. graph" papers/eval_ir.md` — `.scatter` is now reachable for a
  `.float32` graph; only `.scan` is rejected.

**Step 10 — counts** (must match §2): 

```bash
rg -c '\.unsupportedDtype s!' leanncd/LeanNCD/Eval/Plan/Compile.lean          # 3
rg -c 'f32UnsupportedStep ni' leanncd/LeanNCD/Eval/Plan/EvalPlan.lean          # 1
rg -c 'throw \(\.storageKindMismatch \.float32 \.float64\)' leanncd/LeanNCD/Eval/Plan/Dense32.lean  # 1
```

**Step 11 — completion note.** Append to `papers/f32d_record.md` §7: the three counts, the full
manifest table, the build job count, and both §4 tables re-derived cell by cell against the merged
tree (diff each claim yourself — skill §1; no line numbers). Then run step 8's greps once more.
Commit: `docs(leanncd): close out F32-D (binary32 top-level scatter)`.

---

## 6. Risks

Each task's dominant risk and its pin: the move into `runDenseScatterWith` (G64 + G1/G2 before and
after); a guard placed after validation (1.7, P1-1/P1-2); the real compiler emitting a different f32
plan than the prototype (15(c)'s second guard, the oracle's pinned bits, §8); a re-pointed order
fixture that stops pinning order (each re-point names the wrong answers it rejects; S2, S3, P2-1,
P3-2); an oracle sharing code with its subject (§3.5; C1b); a stale document nobody opened (Task 3
step 8's value-greps).

## 7. Definition of done

1. `bash leanncd/scripts/lake-build.sh leanncd` → `Build completed successfully` (8670 + new modules
   jobs; record the number). No `sorry`, no edited binary64 scatter guards (§2).
2. `mutation-manifest.sh` over the whole manifest (8 authored + 9 appended) → all PASS, table in
   the record.
3. Step 10 counts are 3 / 1 / 1; step 8 greps return only the allowed hits.
4. Both §4 tables re-derived against the merged tree in the record's completion note.
5. The final whole-branch review (two lenses: soundness of the guard/evidence boundary; oracle
   independence and docs truthfulness) is clean or adjudicated. Merge to local `main` per Rule 13;
   do not push.

## 8. Stop conditions

- Any observed value (bits, error payload, message) differs from this plan's. Do not edit the
  expectation; the plan's values came from a prototype, so a difference means the real code
  differs from it. Report both values.
- G64 is red after Task 1 step 3, or a binary64 test file other than those §5 names needs an edit.
- The oracle's red failure (Task 3 step 1) is anything but the quoted message, or any oracle case
  disagrees after step 2.
- A manifest entry fails with "expected text not in mutated build log".
- A (c) cell in §4 turns out to be reachable.

## 9. Decisions (none needs the user)

1. **Storage kind on the evidence, kind parameter on a private core** — the F32-A/B shape
   (Plan/AGENTS.md "a new carrier follows the f32 shape"). Alternative, a second
   `CheckedScatterPlan32` type: rejected, it would duplicate every consumer arm.
2. **`runDenseScatter` keeps its name and signature**, gaining only the guard; `runDenseScatter32`
   is new. No caller changes (`runDensePlan` still calls `runDenseScatter`).
3. **Unreachable reduce arms go through `ops.binOp`**, not deleted and not Float-typed: keeps S-A's
   "admitting one later is a checker change alone", now for both carriers, without an `[Add α]`
   instance bound the seam deliberately avoids.
4. **`checkF32Stmt` is deleted** rather than left with three `pure ()` arms: it would be dead code
   this change made dead. `f32CapabilityCheck` keeps arm-by-arm matching over `ScanStmt`.
5. **`scatterFillOrFail`'s f32 arm uses native `Float32.ofInt`, compares bits, and requires a finite
   value**: `(Float.ofInt fill).toFloat32` would be binary64-then-narrow, and without finiteness
   `-(2^128)` would silently read as `-∞` (controller's decision). The `.f64` arm's same overflow is
   pre-existing and left alone (§1.2).
6. **Oracle = twin assignment + source-derived placement**, scheduled as Task 3's first step
   (§3.5). A from-scratch evaluator was not built: placement under `.rejectCollisions` has no
   arithmetic, and the arithmetic half is exactly the F32-A path with its own bit fixtures.
7. **FW2's witness becomes `[relu scatter, f32 scan]`**, not an f32 scan alone: Step A must have a
   competing answer or the order is unpinned. **2.9's source-order pin moves to two scans**; the
   scatter-then-scan pair stays as the "scatter admitted, traversal continues" witness.
8. **No new JAX fixture.** An f32 scatter plan is refused by the same plan-level gate as every f32
   plan, before any per-step check; `ExecutableTest` fixtures 23/24 already pin that order on the
   shape (zero steps) where a wrong gate would be invisible elsewhere.
9. **No `DifferentialTest` change**: there is no binary32 legacy leg to compare against.
10. **The oracle has its own `compile32`/`run32`** rather than un-privatizing `Adapter32Test`'s
    `prepare32`: it keeps the oracle file self-contained and avoids importing that test's chain.
11. **The third task is split into two dispatches** (skill §5): its fixtures are fully specified here,
    so phase 2 needs no production reasoning, only the cycles and the scripted docs.
