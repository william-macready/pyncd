# F32-C execution record

Companion to `papers/f32c_evalplan.md`: execution-time measurements (manifest tables, the re-derived
§4 audit, job counts). Authoring-time measurements stay in `papers/f32c_prototype_notes.md`.

The plan says this file "starts at Task 1's first commit"; Tasks 1 and 2 did not create it (their
measurements live in the SDD ledger, `.superpowers/sdd/f32c_evalplan/task-{1,2}-report.md`). It is
first created here, by Task 3 phase 1.

## Task 3 phase 1 — source admission and the independent oracle

Tree: `worktree-f32c-scans-plan`, base `77f111a` + `papers/f32c_files/task3.patch` + the prose
edits below. Build: `bash leanncd/scripts/lake-build.sh leanncd` → `Build completed successfully
(8673 jobs)` (plan: 8672 + 1 new module; observed 8673).

### Observed values (all equal the plan's)

- `CompileTest` fixture 15(d) (`f32ScanProg`): `causeOf … == none` (admitted).
- Fixture 2.9, both orders (`f32ScatterThenScanProg`, `f32ScanThenScatterProg`, `f32IdentitySig`):
  `.inputSignature (.missingSignature "S0")`.
- Two-scan pair, both orders (`f32TwoScanProg`, `f32ScanSig`): `.inputSignature (.missingSignature
  "T0")`.
- FW2a (`f32ScatterReluThenScanProg`): `.capability (.unsupportedNonlin "Y: scatter nonlinearity")`.
- `ScanDense32Test` Part C: 9 guards green (C1 identity, C3 scan-local scatter, C4 predicate-only,
  C2 identity/relu pair, C5 base relu/identity pair, C6 step softmax, C7 base softmax).
- `ScanDense32Test` Part D: 3 `agrees` guards green. Both legs were also printed (`#eval`, scratch
  file, not shipped) to confirm neither is vacuous — both `.ok`, bit-equal:
  - `linProg .identity`: oracle `("S", [0x4B800000 ×3])`, scan worker `[0x4B800000 ×3]`.
  - `linProg (.pointwise .relu)` / `reluIn`: both `[0x4B800000, 0x4B800000, 0]`.
  - `scatProg`: both `[0x4B800000, 0x4B800000, 0, 0, 0x41B00000, 0x41B00000, 0, 0, 0x42040000,
    0x42040000, 0, 0]`.

### Fixture re-points: what they no longer pin (owned, not hidden)

Fixture 2.9's pair and the two-scan pair (`f32TwoScanProg`) **no longer pin source order**. Both
used to observe `f32CapabilityCheck`'s first-rejection-wins traversal; with Step 0c deleted and scan
admitted, every statement in either program passes Steps 0b and A, and Step B (first-seen-read
signature validation) answers with the same payload in both orders. No binary32 source-order
capability traversal remains to pin. FW2a no longer witnesses a 0c-before-A order; it now witnesses
Step A answering ahead of Step B (the program also lacks `S0` in `f32IdentitySig`). FW2b still pins
Step 0b ahead of Step A. The `CompileTest` prose around these fixtures (Fixture 15's heading, the
2.9 docstring and heading, the two-scan comment, the FW2 docstring and FW2a/FW2b comments) was
rewritten to say this; the patch's own comments still claimed `f32TwoScanProg` pins source order.

### Prose edits beyond the patch (all in files this task touches)

- `CapabilityError.unsupportedDtype` docstring (`Error.lean`): the Step 0c bullet replaced with the
  plan's text (Step 0c DELETED by F32-C, all four contexts producer-less); the lead-in "Both
  producers are in `prepareEvalPlan`" corrected to one producer (Step 0b).
- `Compile.lean`: the `## Binary32 source capability` module-doc section that described the deleted
  `f32CapabilityCheck` removed with it; `checkDecl`'s `.typedTensor` comment no longer cites Step 0c;
  `compileScan`'s base-branch comment "their OWN result-slot pushes stay literal `.f64`" (made false
  by the `destDtype` fix) rewritten.

### `Types.lean` — checked, no edit needed (Task 3 phase 1 step 4)

`ScalarDType`'s docstring says `f32` "remains rejected by every BINARY64 entry — `dtypeAdmitted`,
`checkAssign`, `checkScanPlan`, `checkPointwise`/`checkAxiswise`, `checkPlanBlock`, and each Float
worker/adapter door." Re-checked against the tree, true for each scan/block name:
`checkScanPlan := checkScanCore .float64`, whose state loop applies `scanDtypeAdmitted .float64 =
dtypeAdmitted` (`.f32 => false`) — pinned by `ScanTest` f32 fixture 10 (`stateDtypeNotAdmitted 0 2
.f32`, unedited); `checkPlanBlock := checkPlanBlockCore .float64`, whose gate `unless k == kind ||
all-bool` refuses a real-f32 table as `storageKindNotAdmitted .float32` (`BlockTest`, `ScanTest`
unedited pins). The sentence never claimed f32 has no admission path — only that these binary64
entries reject it, which remains literally true. **Accurate; not edited.**

### §4 re-derivation against the post-Task-3-phase-1 tree

Every door the tables name was located with `rg` and read. Doors opened: `compileScan`'s four
nonlinear result-slot pushes (`destDtype`, base/step × pointwise/axiswise) and its preactivation
push (`destDtype`, unchanged); `prepareEvalPlan` (no Step 0c; Step 0b → Step A → Step B …);
`checkScanScatterOpts` (`opts.fill != 0` integer check, carrier-free); `checkPlan`'s `.scan`
`localCheck` arm (selects `checkScanPlan`/`checkScanPlanF32` by `storageKind`; no capability loop);
`checkScanCore` (state loop `scanDtypeAdmitted kind`; `checkPlanBlock`/`checkPlanBlockF32` by kind;
BOTH blocks checked before EITHER `checkCaptures kind` call); `checkPlanBlockCore` (gate `k == kind ||
all-bool`, then `localCheck` selecting `checkAssign`/`checkAssignF32`, `checkPointwise`/
`checkPointwiseF32`, `checkAxiswise`/`checkAxiswiseF32` by kind; stamps `kind`); `runDenseScan`/
`runDenseScan32` and `runDenseBlock`/`runDenseBlock32` (each guards `storageKind` as its first
statement, then calls the private `…With` worker with `0.0`/`(0.0 : Float32)` and the matching block
worker / the three matching per-kind workers); `runDenseScanWith` (state allocation `Array.replicate
… zero`; `sig` default `getD … dtype := .f64` used for `.shape` only; two `commitWrite zero …` calls);
`commitWrite` (`getD … zero`); `runDensePlan`'s `.scan` arm (`runDenseScan`, unchanged) and
`runDensePlan32`'s `.scan` arm (`runDenseScan32`); `rawPublicationSlots`' `.scan` arm (state
`destSlot`s, carrier-free); `runPreparedDense32 := runPreparedDenseOf runDensePlan32` and
`packBodyOf`/`unpackBodyOf`/`runPreparedDenseOf` (`{α} [StorageCarrier α]`); the JAX plan-level gate
in `Executable.lean` (`candidate.source.plan.storageKind == .float64`, unchanged); the legacy
evaluator's `rejectUnsupportedStorage` entry guards (`Eval/Scan.lean`) and `test/Eval/ScanTest.lean`
fixtures 11–13 (unchanged).

**Result: no cell disagrees with the plan's §4.** Two precision notes, neither changing a class:

1. Table B's "`getD … { dtype := .f64 }` totality defaults (shape-only)" row: not every such default
   is shape-only. In `compileScan`, `baseSigs`' initial `outerSigs.getD (slotOf.getD rn 0) { …
   .f64 }` flows its DTYPE into the block table, and in `Scan.lean` `checkCaptures`/`checkWrites`
   compare the defaulted dtype. Each default is unreachable — `slotOf[rn]?` is proven `some` just
   above in `compileScan`; each `Scan.lean` index is range-checked before its `getD`, directly or via
   membership in the block's outputs, which `checkPlanBlockCore` already range-checked — so the
   class stays **(c)**, but the row's "(shape-only)" qualifier is only exact for `resolveSource` and
   `runDenseScanWith`'s `sig`.
2. Table A's "f32 capture dtype" **(c)** cell: confirmed producer-less under `.float32`.
   `captureDtypeNotAdmitted` fires under `.float32` only for an `.f64` capture slot; any block table
   containing one either derives `.float64` or is mixed, and `checkPlanBlockCore`'s gate (or
   `deriveStorageKind`'s mixed error) rejects that block first, because `checkScanCore` checks both
   blocks before either capture check.

**Table A — case × door (re-derived; unchanged from the plan)**

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

**Table B — a binary64 literal at a site binary32 now reaches (re-derived; unchanged from the plan,
see precision note 1)**

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

No (c) cell turned out reachable (plan §8).

### Mutation cycles Q15–Q18 (`mutation-manifest.sh --task 3`)

Run directly on `papers/f32c_mutations_post.json` (no scratch-manifest workaround needed: `--check`
validated all 18 entries, every old-string unique, now that the patch's final text exists).

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| Q15 (base pointwise result slot back to .f64) | yes | yes | yes | PASS |
| Q16 (base axiswise result slot back to .f64) | yes | yes | yes | PASS |
| Q17 (step pointwise result slot back to .f64) | yes | yes | yes | PASS |
| Q18 (step axiswise result slot back to .f64) | yes | yes | yes | PASS |

4/4 cycles passed. Mutated-build failures (`ScanDense32Test` guards): Q15 → C5's base-relu guard,
Q16 → C7 (base softmax), Q17 → C2's relu guard AND Part D's `agrees (linProg (.pointwise .relu))
reluIn` (the independent oracle catches this mutation on its own), Q18 → C6 (step softmax). The earlier deferred cycles (Q5, Q8,
Q10–Q14) and G1/G2 are Task 3 phase 2's full re-run, not run here.
