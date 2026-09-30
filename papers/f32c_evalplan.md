# F32-C: native binary32 scans — implementation plan

**Status:** authored 2026-09-30 on branch `worktree-f32c-scans-plan` from `main` at `49c1ed6`. Not
executed.

**Companions:** `papers/f32c_prototype_notes.md` (the authoring-time record — every value below was
observed on a real build of the prototype branch `f32c-proto`, real-split, real namespace; §11 also
records this planning dispatch's own token cost); `papers/f32c_mutations_post.json` (18 cycles Q1–Q18,
mutating code this slice ADDS, all PASS per `papers/f32c_files/mutation_results.md`);
`papers/f32c_mutations.json` (2 cycles G1–G2, mutating code that already EXISTS on `main` — the
binary64 preservation gate the prototype notes flagged as missing; built and run by this authoring
dispatch directly against the unmodified tree, both PASS — see Task 1 step 1); both run by
`leanncd/scripts/mutation-manifest.sh`;
`papers/f32c_files/task{1,2,3}.patch` (every CODE change below — production and the one new test file
— generated mechanically from the prototype branch by a scratch script and independently re-verified
by this dispatch: `git apply` of all three in order onto today's `main` tip applies with **zero
conflicts** and touches exactly `Block.lean`, `Scan.lean`, `lakefile.toml`, `Dense32.lean`,
`EvalPlan.lean`, `GraphCheckTest.lean`, `Compile.lean`, `CompileTest.lean`, and the new
`test/Eval/Plan/ScanDense32Test.lean`; apply, do not retype). **This plan holds rationale, the §2
sibling audit, fixtures, decisions, and every prose/docstring edit the patches do NOT carry (they
carry code only) — not transcribed Lean.** A fresh `papers/f32c_record.md` starts at Task 1's first
commit and holds execution-time measurements (manifest tables, the re-derived §4 audit, final job
counts); this plan's own authoring-time measurements stay in `papers/f32c_prototype_notes.md`.

**How to read code in this repo during execution.** Every task lists the symbols it touches as
`identifier @ file`. Run `rg -n <identifier> <file>` and read a ~40–60 line window. **Never read a
file over ~20k characters whole**: `Compile.lean` 119k, `CompileTest.lean` 134k, `Error.lean` 43k,
`Scan.lean` 51k, `Check.lean` 30k, `EvalPlan.lean` 25k, `GraphCheckTest.lean` 25k. `Block.lean` (19k),
`Dense32.lean` (4.5k), `Types.lean` (5.4k) are small enough to read whole if truly needed, but prefer
a window regardless.

---

## 1. Scope

### 1.1 Admitted by this slice

Every scan form — plan level (`checkScanPlan`/`runDenseScan`), graph level (`checkPlan`/
`runDensePlan32`), and source level (`prepareEvalPlan`) — executed natively in binary32, including: a
scan with a nonlinear base or step body (pointwise or axiswise, either block); scan-local scatter
inside an f32 scan (its own state-write path, not F32-D's); and a predicate-only scan (bool-only block
tables) inside an f32 program. This closes the only remaining gap in
`papers/backend_missing_functionality.md`'s "Binary32 beyond the assignment fragment" row.

### 1.2 Still refused, unchanged (owner in brackets)

| Construct | Where it is refused | Owner |
|---|---|---|
| a scatter nonlinearity, non-`.rejectCollisions` policy, a non-identity fill outside the algebra's identity | Step A / `checkScatter`/`checkScatterF32` (unchanged by this slice) | policy (F32-D) |
| any f32 plan on JAX | plan-level `.float64` gate at every JAX door | F32-JAX |
| any f32 program on the legacy evaluator | `EvalError.unsupportedDtype` | permanent |
| mixed f32/f64 in one graph | Step 0b; `mixedStorageKinds` | F32-E (contingent) |

After this slice, **every top-level statement kind a `.float32` schedule can name is admitted**; the
only remaining refusals are policy (scatter options), a different backend (JAX), a different
evaluator (legacy), or a different invariant (mixed precision).

### 1.3 Carry-forward from the master plan and F32-D (re-derived, not inherited)

`papers/f32_evalplan.md` §1.4 said F32-C "builds on both" F32-B and F32-D and predicted a two-slice
split "as binary64 scatter did." **Re-derived here: one slice, three tasks** (§1.5). The binary64
scatter precedent does not apply — S-A/S-B had to invent the placement semantics; scan and
scan-local scatter reuse every existing carrier-free geometry, causality, snapshot, and placement
rule (`Scan.lean` §2.2 below), so no new semantics is created, only a second carrier for existing
code.

`papers/f32d_evalplan.md` §1.3 flagged one open question for this slice to settle: whether
`independentRun`'s scan-unroll oracle, run through the checked binary32 path, covers every
scan-local scatter placement the scan compiler admits ("fragment coverage against `evalScheduled`'s
wider placement admission is unverified"). **Settled, moot:** every scan-local scatter placement the
checked SCAN compiler admits unrolls to a top-level scatter the checked binary32 compiler also
admits (verified on all 5 `scanScatterOracleCases` plus 5 adversarial probes: prototype notes §5).
The oracle's real, unrelated gap is that `unrollScanNode` emits no dtype declarations for its
unrolled leaves (§3.5 below), not a placement-coverage gap.

Also settled: F32-D §1.3 proposed lifting its `compile32`/`run32`/`env32` harness into a shared test
module "when F32-C adds that second caller." **The lift trigger did not fire.** F32-D's harness takes
a `TLProgram`; F32-C's oracle needs to run an already-*unrolled* `ScheduledProgram` (the unroll's own
output), a different shape at a different pipeline stage. The oracle's `run32 (p : ScheduledProgram)`
(§3.5, Task 3) duplicates the middle of F32-D's `compile32` rather than reusing it. No shared module
is introduced; record this as the lift trigger not firing, not as a gap.

### 1.4 Known gaps in this slice's fixture coverage (no owner yet, non-blocking)

Not part of this slice's Definition of Done; each is cheap to add later if a real model needs it:

- No binary32 fixture with **two states** or a **cross-state read** — the immutable pre-step snapshot
  (`oldStates`) is exercised only by binary64 `ScanTest` fixtures. The code is shared verbatim and
  carrier-generic, so nothing binary32-specific is untested at the TYPE level, but no binary32 pin
  distinguishes a Jacobi snapshot from Gauss–Seidel numerically.
- No f32 **two-advancing-axis** scan and no f32 **mask predicate** (`softmax where …`) inside a scan.
- No generated-corpus f32 leg (`ScanGen`/`ScanOracle`) — optional, unknown cost, the natural
  "if it grows" item.
- The oracle (§3.5) covers 3 of its own programs (Part D) plus the 5 `scanScatterOracleCases` used
  only manually in §5.1's placement argument, not wired as oracle guards. Wiring all 5 in as f32
  oracle guards is cheap and NOT yet run — a good Task 3 stretch item if turns allow, but not
  required (§7).

### 1.5 One slice, three tasks — adopted from the prototype's own recommendation

| Task | Deliverable | Production diff (measured, `git apply --stat`) | Fixtures | Mutation cycles |
|---|---|---|---|---|
| 1 | carrier-parametric block + scan checker/worker | `Block.lean` +73/−(part), `Scan.lean` +84/−(part) (`+215/−36` combined with the new test file and lakefile) | Part A: 17 `#guard`s (new file, counted `rg -c '^\+#guard'` against the patch) | Q1–Q12 (12) + G1–G2 (2, `papers/f32c_mutations.json`) |
| 2 | graph admission (`checkPlan` loop deleted, arm selection by kind; `runDensePlan32` `.scan` arm) | `+20/−17` combined | Part B: 3 new guards; `GraphCheckTest`: 2 fixtures re-pointed (3 guard lines net, one fixture splits into two guards) | Q13–Q14 (2) |
| 3 | source admission (Step 0c deleted, 4 `destDtype` sites), the oracle, `CompileTest` re-points, doc sweep | `+181/−40` combined | Parts C+D: 12 new guards; `CompileTest`: 5 fixture groups re-pointed (2 new guard lines, 3 value-only re-points) | Q15–Q18 (4) |

Totals: ~150 production lines, 37 new/re-pointed guard lines, 20 cycles (18 in
`f32c_mutations_post.json` + 2 in `f32c_mutations.json`) — the same order as F32-D (3 tasks, ~19
cycle runs), which fit one plan.

---

## 2. Global constraints (exact values)

- **Guard first, at every scan/block door.** `runDenseScan`/`runDenseScan32` and
  `runDenseBlock`/`runDenseBlock32` check `c.storageKind` as their FIRST statement, before the
  signature tie (scan) or the arity check (block). A mismatch is
  `PositionalInputError.storageKindMismatch <door's kind> <evidence's kind>`, never a conversion.
- **`CheckedScanPlan` and `CheckedPlanBlock` each record `storageKind : LeanNCD.StorageKind`**, set
  only by their `.float64`/`.float32` checker pair, both thin applications of ONE private
  `…Core kind`. No public raw-plan-plus-ops scan or block entry is added.
- **One formula, two carriers**, both levels: `runDenseBlockWith`/`runDenseScanWith` are `{α}`-generic
  private workers; the binary32 path never widens to `Float` (the pattern forbidden by
  `Plan/AGENTS.md`: "never derive them by narrowing binary64 results").
- **Bool-only block tables are admitted under either kind** (§8.1 decision below): `checkPlanBlockCore`'s
  gate is `unless k == kind || block.tensorSigs.all (·.dtype == .bool) do throw …`, not a plain
  `k == kind`. A table with no real (non-`bool`) slot constrains no carrier.
- **Binary64 behaviour is preserved bit for bit.** No edit to `ScanTest.lean`, `ScanCompileTest.lean`,
  `BlockTest.lean`, `ScanContractTest.lean`, `DifferentialTest.lean`,
  `test/Eval/PropertyOracle/*`, or `test/Eval/ScanTest.lean`. All build green, unedited, on the
  prototype (prototype notes §4.2 — the complete non-progress build output diffs empty against base).
  Gate G1/G2 (`papers/f32c_mutations.json`, Task 1 steps 1 and 6) proves two of the moved lines'
  binary64 fixtures actually bite, both before and after the move — this authoring dispatch built
  and ran both against `main` at `49c1ed6` directly (not merely asserted from the prototype).
- **Values are exact bit patterns**, compared through `Float32.toBits`/`Float.toBits`, never
  `BEq Float32`. Every value in §4/§6 was observed on the prototype (prototype notes §3, §7); if the
  real code produces a different value, STOP (§8), do not edit the expectation.
- **No `File.lean:NNN`** in anything you ship. Cite identifiers.
- **Vacuous refusal machinery is deleted, not kept as an inert extension point** (§8.2 decision):
  `f32CapabilityCheck` (Step 0c) and `checkPlan`'s `.float32` capability loop are both removed — every
  arm was `pure ()` after this slice, the F32-D precedent for `checkF32Stmt`.
- **Retained, not deleted:** `PlanStepError.f32UnsupportedStep` and `PlanStepKind` (both producer-less
  after this slice — the closed-family discipline F32-D already applied to `PlanStepKind.scatter`);
  the `"{name}: f32 scan"` context's doc entry in `Error.lean` (re-worded as producer-less).
- **Build:** `bash leanncd/scripts/lake-build.sh <leanncd-dir>` ends `Build completed successfully`
  (baseline **8672 jobs** at `49c1ed6`; the one new test module adds 1 — record the actual, prototype
  observed 8673).
- **New test module must be registered** in `leanncd/lakefile.toml`'s `Tests` `globs`, after
  `"Eval.Plan.Scatter32OracleTest"` (task1.patch already does this — verify it landed).

---

## 3. Design (as prototyped and code-verified; the patches carry the code)

Mirrors F32-D §3: one private core per checker, two thin public wrappers, one private `…With` worker,
two thin public workers each guarding the storage kind first. Full code: `papers/f32c_files/task{1,2,3}.patch`.

### 3.1 Block (`Block.lean`, Task 1)

`CheckedPlanBlock` gains `storageKind` (last field). `checkPlanBlock`'s body becomes
`private checkPlanBlockCore (kind)`; its `localCheck` selects `checkAssign`/`checkAssignF32`,
`checkPointwise`/`checkPointwiseF32`, `checkAxiswise`/`checkAxiswiseF32` by `kind`. Public wrappers:
`checkPlanBlock := checkPlanBlockCore .float64`, `checkPlanBlockF32 := checkPlanBlockCore .float32`.
`runDenseBlock`'s body moves verbatim into `private runDenseBlockWith {α} (assignAt) (pointwise)
(axiswise) c ctx inputs` (the three per-kind workers are parameters — no `ScalarKernelOps` record
here, since it is `private` to `Dense.lean`). `runDenseBlock`/`runDenseBlock32` each guard first, then
call `runDenseBlockWith` with the matching three workers.

### 3.2 Scan (`Scan.lean`, Task 1)

`CheckedScanPlan` gains `storageKind`. New `private scanDtypeAdmitted kind : ScalarDType → Bool`
(dispatches to `dtypeAdmitted`/`dtypeAdmittedF32`). `checkCaptures` takes `kind` first and applies
`scanDtypeAdmitted kind` — **stays producer-less under both kinds** (Table A row "f32 capture dtype"
below; the block-level storage gate always fires first, exactly as it already does at `.float64`, per
the existing docstring's own argument — see the Check.lean/Scan.lean prose edit in Task 1 step 4 above).
`checkScanPlan`'s body becomes `private checkScanCore (kind)`: the state loop uses
`scanDtypeAdmitted kind`, blocks are checked by `checkPlanBlock`/`checkPlanBlockF32` selected by
`kind`, captures by `checkCaptures kind`. **Carrier-free and shared unchanged (≈85% of the file):**
`WriteRowKind`, `classifyWriteRow`, `writeRowKinds`, `outputPosOfRow`, `baseWriteTouchesBoundary`,
`baseWriteRowsOk`, `stepWriteRowsOk`, `outputRowExtentsAgree`, `pinnedLiteralsInRange`,
`writesCollide`, `causalAdvancingRow`, `stateReadCausal`, `checkWrites`, the causality loop, and
`mixedRadix*`. `commitWrite` becomes `{α} (zero : α)` (only carrier use: the `getD … zero` default,
unreachable since output shapes are checked). `runDenseScan`'s body moves verbatim into
`private runDenseScanWith {α} (zero) (runBlock) sigs c outerStore` — the only changes from the
original are `0.0 → zero` (state allocation) and `runDenseBlock → runBlock` (×2) and
`commitWrite target … → commitWrite zero target …` (×2); the signature tie, store arity, capture-order
lookup, snapshot (`oldStates`), simultaneous commit and publication are byte-identical.
`runDenseScan`/`runDenseScan32` each guard first (`0.0`/`(0.0 : Float32)` zero, `runDenseBlock`/
`runDenseBlock32`).

**Docstring placement (settled, no further action):** the long pre-existing docstrings above
`runDenseBlock`/`runDenseScan` stay in place above the now-private `…With` workers (the mechanical
move left them there); only the new binary32 public wrappers get their own short docstrings. This
mirrors F32-D's own `checkScatter`/`checkScatterF32` asymmetry (only the F32 sibling got new prose).

### 3.3 Graph (`EvalPlan.lean`, `Dense32.lean`, Task 2)

`checkPlan`: the whole `if storageKind == .float32 then … | .scan _ => throw (.f32UnsupportedStep ni
.scan)` capability loop is DELETED (every arm was `pure ()`). The `.scan s` `localCheck` arm selects
`checkScanPlan`/`checkScanPlanF32` by `storageKind`, exactly as the nonlinearity arms already do.
`runDensePlan32`: `.scan c => store ← runDenseScan32 raw.tensorSigs c store`, mirroring
`runDensePlan`'s arm.

### 3.4 Source (`Compile.lean`, Task 3)

`f32CapabilityCheck` (Step 0c) is DELETED along with `prepareEvalPlan`'s Step 0c call block.
`compileScan`: in the 4 nonlinear result-slot pushes (base/step × pointwise/axiswise),
`{ shape := outputShape, dtype := .f64 }` becomes `dtype := destDtype` — `destDtype` is already in
scope at each site (the F32-B Task 4 pattern). Scan-local scatter source path: **no change** —
`checkScanScatterOpts`'s integer fill check is carrier-free and placement stays in
`scanPlacementRows`.

### 3.5 The independent binary32 scan oracle (Task 3)

Required by `papers/f32_evalplan.md` §1.3 item 2 and the master plan's general independent-oracle
rule; settles F32-D §1.3's open question (§1.3 above). The legacy scan oracle,
`independentRun @ test/Eval/PropertyOracle/ScanUnroll.lean`, unrolls a scan into a scan-free program
and runs it through the LEGACY `evalScheduled`, which refuses f32 permanently — no use here.

**Design (`oracle32`, `test/Eval/Plan/ScanDense32Test.lean` Part D, in `task3.patch`):**
1. Size inference and `unrollScanNode`, exactly as `independentRun` does them.
2. For every unrolled leaf not already in `un.decls`: declare `.typedTensor .f32 leaf axes` (the
   assignment's free LHS axes, or the state's `sliceAxes` for a scatter leaf). This is the oracle
   gap: `unrollScanNode` emits `.predicate` leaf decls only, never `.typedTensor .f32` — declaring
   leaves with `[]` axes instead fails `sourceInvariant (rankMismatch … 0 1)`, so decl rank matters.
3. `prepareEvalPlan` → `runPreparedDense32` on the scan-free program (through THIS slice's Step D —
   the unroll can run natively in binary32 only because Task 3's `destDtype` fix and F32-D's
   top-level scatter both already admit it).
4. Widen the leaf env to `Float` exactly (`Float32.toFloat`), call the existing
   `reconstructHistory` (pure placement, no arithmetic), narrow back (exact for widened values), and
   compare bits against the scan worker's own `runPreparedDense32` result.

**Independent enough, because** the oracle leg never touches `runDenseScan32`, `runDenseBlock32`,
`commitWrite`, `checkScanPlanF32`, `checkPlanBlockF32`, or `compileScan`. It shares
`runDenseAssign32`, `runDenseScatter32`, and the nonlinearity workers, each already pinned by
F32-A/B/D. **What it cannot catch:** a defect in traversal code both legs share; the
destination-extent convention; collisions/out-of-range placement; a non-identity fill (none of these
are new — F32-D's oracle has the same list). **Limitations specific to this design:** the leaf-decl
scatter-leaf state match is a name heuristic correct for single-state scans only; it handles one scan
per program; it does not reuse F32-D's `compile32`/`run32` (§1.3).

---

## 4. Sibling audit (skill §2): every scan-execution door after this slice

Carried forward from `papers/f32c_prototype_notes.md` §9, observed on the prototype. **Task 3 phase 1
step 4 re-derives both tables against the real tree, cell by cell, and appends the result to
`papers/f32c_record.md`** — this table is the authoring-time snapshot, not a substitute for that
re-derivation. Classes: **required**, **forbidden**, **(c)** = correct only because an upstream check
holds, **SI** = silently ignored/unpinned (candidate next instance — §1.4 lists the two SI cells
below as known, non-blocking gaps).

**Table A — case × door**

| Case | Source (`compileScan`) | `checkPlan`/`checkScanPlan*`/`checkPlanBlock*` | Float workers | binary32 workers | Adapter | JAX | Legacy |
|---|---|---|---|---|---|---|---|
| f32 scan, identity bodies | **required** (C1) | **required** `checkScanPlanF32` (B1, A1; Q13) | **forbidden**, guard first (A3, B1; Q2, Q4) | **required** (A1, B1; Q1, Q3, Q14) | **required**, carrier-generic (C1) | forbidden, plan-level `.float64` gate, unchanged | forbidden permanently (fixture 13) |
| f32 scan, nonlinear body | **required**, `destDtype` ×4 (C2, C5–C7; Q15–Q18) | **required** `checkPointwiseF32`/`checkAxiswiseF32` (Q10, Q11) | forbidden | **required** (via `runDenseBlockWith`) | required | forbidden | forbidden |
| f32 scan-local scatter | **required**, no source change (C3) | **required**, carrier-free geometry | forbidden | **required**, state `+0` init pinned (C3; Q12) | required | forbidden | forbidden |
| predicate-only scan (bool-only blocks) in f32 program | **required** (C4) | **required**, bool-only exemption (A6, C4; Q8) | forbidden | **required** | required | forbidden | forbidden |
| f64 state/block in an f32 scan (programmatic) | unreachable from source | **forbidden**: `stateDtypeNotAdmitted` (A4), `baseBlockError (storageKindNotAdmitted .float64)` (A4b; Q7) | — | — | — | — | — |
| f32 capture dtype | — | **(c)**, producer-less under both kinds: the block gate always runs first | — | — | — | — | — |
| binary64 scans (preservation) | unchanged | **required**, stamps `.float64` (A2) | **required**, all binary64 suites unedited/green | **forbidden** (A3; Q1, Q3) | unchanged | unchanged | unchanged |
| snapshot / cross-state read | carrier-free | carrier-free | pinned by binary64 `ScanTest` | **SI**: shared generic code, no binary32 multi-state pin (§1.4) | — | — | — |

**Table B — a binary64 literal at a site binary32 now reaches**

| Site | Reached by f32? | Class | Pin |
|---|---|---|---|
| `0.0` state init @ `runDenseScan` | yes | **fixed** → `zero` param | C3, Q12 |
| `0.0` `getD` default @ `commitWrite` | yes (unreachable arm) | **fixed** → `zero`; (c) | — |
| `runDenseBlock` calls ×2 @ `runDenseScan` | yes | **fixed** → `runBlock` param | A1, Q3 |
| `checkAssign`/`checkPointwise`/`checkAxiswise` @ `checkPlanBlock` | yes | **fixed** → select by kind | Q9–Q11 |
| `.ok .float64 => pure ()` gate @ `checkPlanBlock` | yes | **fixed** → `k == kind` or all-`bool` | A5, A6, C4, Q8 |
| `dtypeAdmitted` @ `checkScanPlan` state loop / `checkCaptures` | yes | **fixed** → `scanDtypeAdmitted kind` | A1, A4, Q6 |
| `checkPlanBlock` calls @ `checkScanPlan` | yes | **fixed** → by kind | A4b, Q7 |
| 4 × `dtype := .f64` nonlinear result slots @ `compileScan` | yes | **fixed** → `destDtype` | C2, C5–C7; Q15–Q18 |
| `getD … { dtype := .f64 }` totality defaults (shape-only) | yes | **(c)** | — |
| `opts.fill != 0` @ `checkScanScatterOpts` | yes | **required**, carrier-free (`+0` both) | C3 |

**Doors to open during the audit even though no diff shows them:** `runDensePlan` (unchanged scan
arm), `checkWrites`, `commitWrite`'s caller sites, `rawPublicationSlots @ Prepared.lean`'s `.scan` arm
(carrier-free), `packBodyOf`/`unpackBodyOf`/`runPreparedDenseOf` (carrier-generic),
`requireFloat64Plan`/the plan-level gate in `Executable.lean` (JAX, unchanged), `evalScheduled`
(legacy, unchanged), `experiments/jax_bridge/EvalPlanCodegen.lean` (prose-only mentions).

---

## 5. Tasks

### Task 1 — carrier-parametric checked block and scan

**Dispatch:** Opus 5.5, high effort. Highest-risk task: two files' checker/worker cores rewritten
together, and the bool-only exemption is a real bug class (§8.1) the prototype hit once already.

**Files:** `leanncd/LeanNCD/Eval/Plan/Block.lean`, `leanncd/LeanNCD/Eval/Plan/Scan.lean`,
`leanncd/LeanNCD/Eval/Plan/Check.lean` (docstring only), `leanncd/lakefile.toml`, new
`leanncd/test/Eval/Plan/ScanDense32Test.lean`.

**Symbols (`rg -n`, window-read):** `CheckedPlanBlock`/`checkPlanBlock`/`runDenseBlock` @
`Block.lean`; `CheckedScanPlan`/`checkScanPlan`/`checkCaptures`/`commitWrite`/`runDenseScan` @
`Scan.lean`; `dtypeAdmitted @ Check.lean` (docstring, `rg -n "checkScanPlan.*shares this predicate"`); `ScanTest.linearScan`/
`linearScanF32`/`baseBlock`/`stepBlock`/`stepBlockF32`/`outerSigs`/`outerSigsF32` @
`test/Eval/Plan/ScanTest.lean` (donors — do not edit).

**Step 1 — gate G1/G2, on the UNMODIFIED tree, before touching anything.**
```bash
bash leanncd/scripts/mutation-manifest.sh leanncd papers/f32c_mutations.json
```
Both PASS (already verified by this authoring dispatch against `main` at `49c1ed6` — rerun to confirm
against your own tree state). They prove the binary64 fixtures `ScanTest` review fixtures 12/17 and
`BlockTest`'s arity-mismatch fixture bite on the exact lines of `runDenseScan`/`runDenseBlock` you are
about to move (the signature tie and the block arity check respectively).

**Step 2 — apply the patch.** `git apply papers/f32c_files/task1.patch`. This creates
`test/Eval/Plan/ScanDense32Test.lean` (Part A, 17 `#guard`s) and registers it in `lakefile.toml`. Do
not retype any of it.

**Step 3 — build.**
```bash
bash leanncd/scripts/lake-build.sh leanncd Eval.Plan.ScanDense32Test Eval.Plan.ScanTest \
  Eval.Plan.BlockTest Eval.Plan.ScanCompileTest Eval.Plan.GraphCheckTest Eval.Plan.CompileTest \
  Eval.Plan.EvalPlan32Test
```
Expect `Build completed successfully`. The prototype observed `8533 jobs` for exactly this target set
after task 1 — record your own number, do not assume it matches.

**Step 4 — the one prose edit the patch does NOT carry.** `Check.lean`'s `dtypeAdmitted` docstring
(`rg -n "checkScanPlan.*Scan.lean.*shares this predicate"`) says: "`checkScanPlan`
(`Scan.lean`) shares this predicate and stays Float-backed for the same reason (scan is F32-C, still
unadmitted)." Replace with: "`checkScanPlan` (`Scan.lean`) shares this predicate for its
`.float64` door; its `.float32` sibling `checkScanPlanF32` shares `dtypeAdmittedF32` instead, through
the shared dispatcher `scanDtypeAdmitted`." `Scan.lean`'s `checkCaptures` docstring
(`CURRENTLY PRODUCER-LESS…`) needs NO edit — re-verified here (not merely re-asserted): its argument
("the block-level storage gate is strictly stronger and runs first, so this clause's own throw is
unreachable") is unaffected by adding a `kind` parameter, since `checkPlanBlock`/`checkPlanBlockF32`
still both run before `checkCaptures` at their respective kind, and each still refuses every off-kind
slot at the WHOLE-TABLE level before any capture is examined. Table A row "f32 capture dtype" above
pins this as **(c)**, still true.

**Step 5 — the bool-only decision (§8.1), recorded not re-litigated.** `deriveStorageKind` defaults an
all-`bool` (no real-dtype slot) table to `.float64`. A literal `unless k == kind` gate therefore
refuses every predicate-only block inside an f32 scan — reachable from source (fixture C4, Task 3) and
was first caught as a compiler-bug-channel `invalidPlan`. **Decision: exempt bool-only tables in the
gate** (`|| block.tensorSigs.all (·.dtype == .bool)`), already in the patch. The alternative
(parameterize `deriveStorageKind`'s default) would touch `Check.lean` and the top-level `checkPlan`
too, for no behavioral difference — the top-level graph checker has no analogue of this bug because a
top-level bool-only graph legitimately IS `.float64` (nothing else could make it f32). Do not change
this decision without a fixture showing the exemption is wrong.

**Step 6 — G1/G2 again**, now against the moved code (`runDenseScanWith`/`runDenseBlockWith`):
```bash
bash leanncd/scripts/mutation-manifest.sh leanncd papers/f32c_mutations.json
```
Both PASS — same fixtures, same literal lines, now inside the private `…With` workers instead of the
old public `runDenseScan`/`runDenseBlock`. Confirms the move changed nothing binary64 observes.

**Step 7 — the new-code mutation cycles.**
```bash
bash leanncd/scripts/mutation-manifest.sh --task 1 leanncd papers/f32c_mutations_post.json  # Q1-Q12
```
All 12 PASS (`papers/f32c_files/mutation_results.md` records this from the prototype; rerun here
against the real tree). A FAIL with "expected text not in mutated build log" is a STOP (§8), not a
fixture edit.

**Commit:** `feat(leanncd): carrier-parametric checked block and scan (F32-C Task 1)`.

---

### Task 2 — graph-level admission

**Dispatch:** Sonnet 5, medium effort. Small, mechanical, a direct mirror of F32-D Task 2's own
`checkPlan`/`runDensePlan32` pattern — no new design decision.

**Files:** `leanncd/LeanNCD/Eval/Plan/EvalPlan.lean`, `leanncd/LeanNCD/Eval/Plan/Dense32.lean`,
`leanncd/test/Eval/Plan/GraphCheckTest.lean`, `leanncd/test/Eval/Plan/ScanDense32Test.lean`.

**Symbols:** `checkPlan @ EvalPlan.lean` (capability loop, `localCheck`'s `.scan s` arm),
`PlanStepError.f32UnsupportedStep`'s docstring @ `EvalPlan.lean` (`rg -n "f32UnsupportedStep"`),
`PlanStep.kind`'s docstring @ `EvalPlan.lean` (`rg -n "PlanStep.kind"`), `runDensePlan32 @
Dense32.lean` (arm + its long docstring, `rg -n "scan evidence is refused"`); `f32ScanPlan`,
`f32StepOrderWithScan`, `f32UnsupportedStepOrder`, `storageOf`, `isF32Unsupported` @
`GraphCheckTest.lean`.

**Step 1 — apply the patch.** `git apply papers/f32c_files/task2.patch`. This deletes `checkPlan`'s
whole `.float32` capability loop (and its "CAPABILITY SECOND" comment along with it — nothing to
reword there, it is simply gone), re-points `GraphCheckTest` fixture 16 (`f32ScanPlan`: was
`f32UnsupportedStep 0 .scan`, now accepted, `storageOf … == some .float32`) and
`f32StepOrderWithScan` (was `f32UnsupportedStep 3 .scan`; with no capability refusal left, the two
appended scans' shared destination slot 2 fires instead: `.assign (.duplicateDestination 2 1 3)` —
this is a genuinely different failure, not a re-labelling, so it exercises `checkStepGraph`'s wiring
check where it previously never reached that far), and appends Part B (3 new guards) to
`ScanDense32Test.lean`.

**Step 2 — prose edits the patch does NOT carry (both in `EvalPlan.lean`).**
`PlanStepError.f32UnsupportedStep`'s docstring says "Binary32 admits assignments, the two
nonlinearity operations (F32-B), and top-level scatter (F32-D); scan (and scan-local scatter) is
F32-C." Replace with: "Since F32-C, every top-level statement kind a `.float32` schedule can name is
admitted; this constructor is retained producer-less (closed-family discipline, `PlanStepKind.scatter`'s
F32-D precedent)." `PlanStep.kind`'s docstring says the `.assign`/`.pointwise`/`.axiswise`/`.scatter`
answers "are never actually reported by that error, since those are exactly the kinds a binary32 graph
admits" — append: "since F32-C, `.scan` joins them: `f32UnsupportedStep` has no live producer at all."

**Step 3 — the `Dense32.lean` docstring (Task 2 file, not in the patch).** `runDensePlan32`'s long
docstring (`rg -n "scan evidence is refused"`) reads: "**Assignments, the two nonlinearity operations,
and top-level scatter run natively; scan evidence is refused as binary64 evidence.**" through "…is a
deliberate edit at its own arm." Replace the whole paragraph with: "**Every step kind runs natively,
since F32-C.** `.assign` runs `runDenseAssign32`, `.pointwise`/`.axiswise` run
`runDensePointwise32`/`runDenseAxiswise32` (F32-B), `.scatter` runs `runDenseScatter32` (F32-D), and
`.scan` runs `runDenseScan32` (F32-C), each of which re-checks its own evidence's storage kind as its
first statement. Matched arm by arm rather than through a catch-all, so a future admission remains a
deliberate edit at its own arm." (The two sentences after it, about `checkPlan` rejecting `.scan`
outright and `storageKindMismatch` "stating the literal truth," are now false in their entirety —
delete them; there is no longer a case where `.scan` evidence reaching here is anything but real
binary32 evidence, exactly like every other arm.)

**Step 4 — mutation cycles.**
```bash
bash leanncd/scripts/mutation-manifest.sh --task 2 leanncd papers/f32c_mutations_post.json  # Q13-Q14
```
Both PASS.

**Commit:** `feat(leanncd): admit binary32 scan in checkPlan and runDensePlan32 (F32-C Task 2)`.

---

### Task 3 — source admission, the oracle, and documentation (two dispatches)

**Files:** `leanncd/LeanNCD/Eval/Plan/Compile.lean`, `leanncd/LeanNCD/Eval/Plan/Error.lean` (doc
only), `leanncd/LeanNCD/Eval/Plan/Types.lean` (checked, no edit — Task 3 phase 1 step 4 below),
`leanncd/test/Eval/Plan/CompileTest.lean`, `leanncd/test/Eval/Plan/ScanDense32Test.lean`,
`leanncd/LeanNCD/Eval/Plan/AGENTS.md`, the papers in phase 2 step 4.

**Symbols:** `f32CapabilityCheck`, `compileScan` (the 4 nonlinear result-slot pushes),
`prepareEvalPlan` (Step 0c call block) @ `Compile.lean`; `CapabilityError.unsupportedDtype`'s
docstring @ `Error.lean` (`rg -n '"\{name\}: f32 scan"'`, the Step 0c bullet); `f32ScanProg`,
`f32ScanSig`, `f32ScatterThenScanProg`, `f32ScanThenScatterProg`, `f32TwoScanProg`,
`f32ScatterReluThenScanProg`, `causeOf` @ `CompileTest.lean`.

#### Phase 1 (production + oracle + fixtures, one commit, green)

**Dispatch:** Opus 5.5, high effort. The independent-oracle design and the four correctness-critical
re-points (2.9, the two-scan pair, FW2a) are the plan's highest-value correctness surface after
Task 1.

**Step 1 — apply the patch.** `git apply papers/f32c_files/task3.patch`. This deletes
`f32CapabilityCheck` and Step 0c's call block; fixes the 4 `destDtype` sites; re-points `CompileTest`
fixture 2.9 (forward: `"S: f32 scan"` → `.inputSignature (.missingSignature "S0")`, since Step 0c no
longer exists to hide the missing signature — Step B now answers instead), the two-scan pair (both
orders now report `.inputSignature (.missingSignature "T0")` rather than a source-order-sensitive
capability rejection — this pair **no longer pins source order**, note this drop honestly, do not
claim it still does), and FW2a (was a `run_cmd` catching "Step 0c precedes Step A"; now a plain
`#guard` since Step 0c is gone and Step A alone answers: `.unsupportedNonlin "Y: scatter
nonlinearity"`). It appends Parts C (9 guards) and D (3 guards) to `ScanDense32Test.lean`, including
`oracle32` and `run32` (§3.5).

**Step 2 — build the whole tree** (§2's command): green, oracle Part D's 3 `agrees` guards pass.

**Step 3 — the prose edit the patch does NOT carry (`Error.lean`).**
`CapabilityError.unsupportedDtype`'s docstring (`rg -n '"\{name\}: f32 scan"'`) currently reads
"Step 0c (`f32CapabilityCheck`) — a homogeneous-f32 schedule using a construct binary32 execution
defers to a later slice, one context per construct: `"{name}: f32 scan"`." followed by three
sentences about the SECOND/THIRD/FOURTH contexts having no producer left "as of F32-D and F32-B."
Replace the whole Step 0c bullet with: "* Step 0c (`f32CapabilityCheck`, DELETED by F32-C) —
formerly a homogeneous-f32 schedule using a deferred construct, one context per construct. All FOUR
contexts this bullet ever produced — `"{name}: f32 scan"`, `"{name}: f32 scatter"`, `"{name}: f32
nonlinearity"`, `"{name}: f32 unary factor {termIndex}:{factorIndex}"` — have NO PRODUCER LEFT as of
F32-C, F32-D, and F32-B Tasks 4 and 2 respectively: every top-level statement kind a `.float32`
schedule can name is structurally admitted at Step 0c's former position, with `prepareEvalPlan`'s
later steps emitting each kind's real dtype/algebra. Retained here producer-less for the same reason
every other retired context/constructor in this file is (§9.2), not deleted."

**Step 4 — verify `Types.lean` needs no edit (re-check, do not just re-assert).** Its `ScalarDType`
docstring (`rg -n "rejected by every BINARY64 entry"`) lists `checkScanPlan`/`checkPlanBlock` among
the binary64-only checkers that still reject an `.f32` signature. **This remains literally true**:
`checkScanPlan`/`checkPlanBlock` are still the `.float64` doors after this slice, exactly as
`checkAssign`/`checkPointwise`/`checkAxiswise` already were before this slice with their own F32
siblings — the sentence never claimed f32 has no admission path at all, only that these specific
BINARY64 entries reject it. No edit needed; record this as a checked-and-confirmed-accurate finding
in `papers/f32c_record.md`, not a silent skip.

**Step 5 — re-derive §4's Tables A and B against the tree, cell by cell** (`rg`/read each door the
cell names; no line numbers). Append the result to `papers/f32c_record.md`. Phase 2 does no
production reasoning.

**Step 6 — cycles.**
```bash
bash leanncd/scripts/mutation-manifest.sh --task 3 leanncd papers/f32c_mutations_post.json  # Q15-Q18
```
All PASS.

**Commit:** `feat(leanncd): admit binary32 scan from source (F32-C Task 3)`. Hand phase 2 the SHA via
`.claude/skills/slice-plan/split-handoff-template.md` with this task's symbol list above.

#### Phase 2 (documentation sweep, one commit)

**Dispatch:** Sonnet 5, low/medium effort. Purely mechanical — every edit below is a value-grep and a
line replacement, no design judgment.

**Step 1 — full manifest run, no `--task`, `--out` to a scratch table, both manifests:**
`papers/f32c_mutations.json` (G1/G2, final confirmation the binary64 gate still holds after Tasks 2–3)
and `papers/f32c_mutations_post.json` (Q1–Q18). 20/20 PASS. Paste both tables into your report.

**Step 2 — `Plan/AGENTS.md`** (injected Pitfalls section is 655 chars; Code Map/Contracts are small
too — no trim needed, confirmed). Code Map: `Block.lean` row → append "`checkPlanBlock`/
`checkPlanBlockF32` over one private `checkPlanBlockCore kind`; `runDenseBlock`/`runDenseBlock32` over
one private `runDenseBlockWith`"; `Scan.lean` row → append "`checkScanPlan`/`checkScanPlanF32` over
one private `checkScanCore kind`; `runDenseScan`/`runDenseScan32` over one private
`runDenseScanWith`". Contracts, "Current binary32 boundary" (`rg -n "Current binary32 boundary"`):
replace "Refused: `.scan`, at compile time (Step 0c: …), at `checkPlan` (…), and at
`runDensePlan32`. `runDenseBlock`/`runDenseScan` are Float-only and are safe only because of those
refusals — F32-C inherits them." with "Since F32-C, every step kind is admitted; nothing is refused
by capability any more (§ "Still refused" in `f32c_evalplan.md` §1.2 for what remains refused by
policy or by a different backend). Binary32 scan's independent oracle: `ScanDense32Test` Part D
(`oracle32`)." Pitfalls "A (c) cell…" (`rg -n "A \(c\) cell is a guard dependency"`): the sentence
"`runDenseBlock` and `runDenseScan` compute through Float-only helpers and are correct only because
f32 scan never reaches them" is now false for THIS pair specifically (they are carrier-parametric
since Task 1) — reword to name a still-true example instead, or drop the sentence if none remains in
this file (check before deciding; do not leave a stale (c) claim).

**Step 3 — value-grep, every document** (the stale values, not the vocabulary):
```bash
rg -n "F32-C" leanncd papers --glob '!papers/f32c_*' --glob '!papers/f32d_*' --glob '!papers/f32b_*'
rg -n "f32 scan" leanncd/LeanNCD leanncd/test papers --glob '!papers/f32c_*'
rg -n "f32UnsupportedStep [0-9a-z]+ \.scan|scan[^\n]*storageKindMismatch \.float32 \.float64" leanncd papers --glob '!papers/f32c_*'
rg -n "checkScanPlan[^\n]*Float-backed|Float-backed[^\n]*checkScanPlan|runDenseScan[^3W][^\n]*Float-only|runDenseBlock[^3W][^\n]*Float-only" leanncd papers --glob '!papers/f32c_*'
rg -n "f32CapabilityCheck" leanncd papers --glob '!papers/f32c_*'
rg -n "scan is F32-C|scan.*still unadmitted|scan evidence is refused" leanncd/LeanNCD leanncd/test
```
The last six greps hit the stale sentences enumerated in phase 1's steps above, plus any sibling this
plan's authoring did not enumerate — treat an unexpected hit as real, not noise. Allowed to remain:
the legacy evaluator's own docs (`Eval/Eval.lean`, `Eval/Scan.lean`, `Eval/AGENTS.md`,
`test/Eval/ScanTest.lean` fixture 13 — the legacy evaluator refuses f32 permanently); historical
close-out sections of `f32_evalplan.md`/`f32b_evalplan.md`/`f32d_evalplan.md` (append a dated note,
never rewrite history); the new `"{name}: f32 scan"` producer-less mention in `Error.lean`.

**Step 4 — papers** (find each with the `rg` shown; edit only those lines):
- `papers/f32_evalplan.md`: `rg -n "F32-C" papers/f32_evalplan.md` — §1.3 item 2, §1.4 item 3: append
  "**Landed by `f32c_evalplan.md`.**"; §1.4's "It is also the largest risk surface … expect it to
  split into two slices" sentence: append "It did not need to — one slice, three tasks (see
  `f32c_evalplan.md` §1.5)."
- `papers/f32d_evalplan.md`: `rg -n "F32-C" papers/f32d_evalplan.md` — §1.3's "Where the two slices DO
  connect" paragraph and its "Unverified, for F32-C to settle first" sentence: append "**Settled by
  `f32c_evalplan.md` §1.3: moot** (every scan-local scatter placement the checked scan compiler admits
  unrolls to a top-level scatter the checked binary32 compiler also admits)."; the harness-lift
  sentence: append "The lift did not happen — see `f32c_evalplan.md` §1.3."
- `papers/backend_missing_functionality.md`: `rg -n "F32-C|f32 scan" papers/backend_missing_functionality.md`
  (lines 101, 121, 163, 353, 355 at `49c1ed6`) — the "Binary32 beyond the assignment fragment" row and
  item 4: remove "every scan form (including scan-local scatter, F32-C)" from what remains — this
  slice closes the LAST bounded-per-construct row, so also update the summary line above the table if
  it counts remaining rows; the "mixed storage, f32 scan" / "(F32-C)" mentions → drop the F32-C
  qualifier, note landed; the 10/16/6 split count: re-derive it (do not assume it changes to a
  round number) and say so explicitly.
- `papers/wave_f_capability_manifest.md`: `rg -n "F32-C" papers/wave_f_capability_manifest.md` (three
  hits at `49c1ed6`) — "still refused outright … (F32-C, still deferred)" → "admitted natively since
  F32-C"; the Binary32 row's "Nothing on THIS page (the scan kernel) is binary32 … (F32-C)" sentence →
  rewrite to state scan is now admitted, citing this plan; the "Only binary32 scan …, F32-C" clause
  near the end → drop scan from the still-open list.
- `papers/eval_ir.md`: `rg -n "f32CapabilityCheck" papers/eval_ir.md` (one hit at `49c1ed6`) — update
  the Step 0c description to note it is deleted since F32-C.

**Step 5 — counts** (before this slice):
```bash
rg -c 'unsupportedDtype s!"\{nm\}: f32 scan"' leanncd/LeanNCD/Eval/Plan/Compile.lean   # 2 (both deleted)
rg -c 'f32UnsupportedStep' leanncd/LeanNCD/Eval/Plan/EvalPlan.lean                      # 3 (throw site removed → 2)
rg -c '\.scan _ => throw \(\.storageKindMismatch \.float32 \.float64\)' \
  leanncd/LeanNCD/Eval/Plan/Dense32.lean                                                 # 1 (→ 0)
```
Record the after-slice numbers alongside these before-slice baselines (re-measured on today's tree,
not assumed from this plan) in `papers/f32c_record.md`.

**Step 6 — completion note.** Append to `papers/f32c_record.md`: the three counts (before/after), both
manifest tables (20 cycles total), and the final build job count. Then run Step 3's greps once more —
expect the allowed hits only.

Commit: `docs(leanncd): close out F32-C (native binary32 scans)`.

---

## 6. Risks and decisions

Rationale for each, not instruction — cross-referenced to where it is pinned:

1. **Bool-only block exemption (§8.1 / Task 1 step 4).** Chosen over parameterizing
   `deriveStorageKind`'s default because it is a narrower change (one gate, two files touched instead
   of three) with an identical observable result, and the top-level graph checker has no analogous
   bug to fix in parallel. Pinned by A6, C4, Q8.
2. **Delete Step 0c and the capability loop rather than keep them as an inert extension point
   (§8.2 / Task 3 phase 1).** F32-D's precedent for `checkF32Stmt`. The alternative (keep as dead
   code) has no fixture that could ever exercise it, which this repo's conventions treat as a smell,
   not a safety margin. Consequence, owned here rather than hidden: fixture 2.9's pair and the
   two-scan pair lose the SOURCE-ORDER property they used to pin (§5 Task 3 phase 1 step 1) — the
   plan states this loss explicitly rather than silently re-pointing to a coincidentally-similar
   guard.
3. **Known fixture gaps (§1.4) are left unowned, not silently dropped.** Multi-state snapshot,
   two-advancing-axis, mask-predicate-in-scan, and the generated-corpus leg are all carrier-free code
   paths already exercised by binary64 fixtures; nothing here is a binary32-SPECIFIC risk, only an
   absence of a binary32-specific bit pin. Explicitly not required for §7.
4. **The independent oracle's coverage is 3 programs (Part D), not all 5 `scanScatterOracleCases`
   in f32 (§1.4).** Wiring the other 5 in as oracle guards is cheap; not required, because the
   moot-placement argument (§1.3, §3.5) does not depend on running them — it depends on the STRUCTURAL
   argument about `residualPlacement`/`contextAxisAsAffineOutput`, which the 5+5-probe check already
   verified once (prototype notes §5.1–§5.2). Re-verifying that structural argument, not re-running
   more numeric cases, is what would change this decision.

## 7. Definition of done

1. `bash leanncd/scripts/lake-build.sh leanncd` → `Build completed successfully` (8672 + 1 new module
   — record the number). No `sorry`, no edited binary64 scan/block guards (§2).
2. `mutation-manifest.sh` over both manifests (`f32c_mutations.json`, 2 entries; `f32c_mutations_post.json`,
   18 entries) → all 20 PASS, tables in the record.
3. Step 5 (Task 3 phase 2) counts move exactly as predicted (2→0 scan-context throws in
   `Compile.lean`, 3→2 `f32UnsupportedStep` occurrences, 1→0 `storageKindMismatch .float32 .float64`
   scan arm in `Dense32.lean`); Task 3 phase 2 Step 3 greps return only the allowed hits.
4. Both §4 tables re-derived against the tree in the record (Task 3 phase 1 step 5).
5. The final whole-branch review — **two lenses**: (a) soundness of the storage-kind guard/evidence
   boundary across `Block.lean`/`Scan.lean`/`EvalPlan.lean`/`Dense32.lean`/`Compile.lean`; (b)
   independence of the binary32 scan oracle and truthfulness of every doc edit against the tree — is
   clean or adjudicated. Per-task review at Sonnet 5 medium effort for Tasks 1–2 (routine diffs once
   the two lenses' concerns are known); the final two-lens review runs at Opus 5.5 high effort.
6. Merge to local `main` per CLAUDE.md Rule 13; do not push.

## 8. Stop conditions

- Any observed value (bits, error payload, message) differs from this plan's. Do not edit the
  expectation; every value here came from the prototype, so a difference means the real code differs
  from it. Report both values.
- A binary64 test file other than those §2 names needs an edit.
- The oracle's Part D `agrees` guards disagree on any case after Task 3 phase 1's build.
- A manifest entry fails with "expected text not in mutated build log."
- A (c) cell in §4 turns out to be reachable.
- Task 3 phase 1 exceeds ~60 turns before the commit — split further per `slice-plan` §5 rather than
  pushing through; the prototype's own authoring dispatch (§11 of the prototype notes) already
  overran its budget once on this slice's surface, so treat a repeat as a real signal, not noise.
