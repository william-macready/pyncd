# F32-D authoring verification record

Companion to `papers/f32d_evalplan.md`. The live plan does not depend on this file; reviewers and
the next slice's drafter do. Authored 2026-09-25 on `plan/f32d`, base `main` = `6303e9f`, Lean
`leanprover/lean4:v4.30.0`.

## 1. Provenance of every claim

| Claim class | How measured | Where the evidence is |
|---|---|---|
| Plan code compiles | the plan's `<!-- block:… -->` blocks were extracted FROM THE PLAN TEXT, applied to namespace-renamed copies of the real sources, compiled, and every test block compiled with `check-snippet.sh` | §3; `papers/f32d_files/f32d_verify.py` |
| Fixture values | observed from `#eval`/`#guard` runs against that prototype; binary64 contrasts against the real tree | §3 |
| Real-tree mutation cycles | `mutation-manifest.sh` against the real tree, 7/7 PASS | §4.1 |
| New-code mutation cycles | applied to the prototype, rebuilt, test re-run, restored | §4.2 (marked prototype-observed) |
| Code-structure prose ("X shares no code with Y") | `rg` over the named files | §5 |

## 2. The prototype (method)

The real modules cannot be edited on this branch, and the private helpers the new code needs
(`checkAssignCore`, `ScalarKernelOps`, `floatOps`/`float32Ops`, `denseValueAtWith`,
`validateContext`, `validateStore`) cannot be reached from another module. So the text of each
module between `namespace LeanNCD.Eval.Plan` and its `end` was copied into gitignored
`leanncd/spikes/` under `namespace LeanNCD.Eval.Plan.P` (innermost-namespace resolution makes every
unqualified name inside resolve to the copy), the plan's blocks applied, and the copies compiled to
`.olean`s on a private `LEAN_PATH`:

- `F32DProto` = `Check.lean` + `Dense.lean` (Task 1 blocks);
- `F32DProto2` = `EvalPlan.lean` + `Dense32.lean` (Task 2 blocks), importing the real `EvalPlan`
  too, so dot-notation on `PlanStep` resolves;
- `F32DProto3` = `Prepared.lean` + `Compile.lean` + `Adapter.lean` + `Adapter32.lean` (Task 3
  blocks), so a `tlprog!` source program runs through `P.prepareEvalPlan` → `P.checkPlan` →
  `P.runPreparedDense32`.

Test files were compiled with their namespace changed to `LeanNCD.Eval.Plan.P.<Name>` and their
first import changed to the prototype; nothing else differs (diffed). `check-snippet.sh` sees the
prototype because `lake env` preserves a caller's `LEAN_PATH` (checked: it compiled a file importing
`F32DProto`). The final run of `f32d_verify.py` printed, verbatim:

```
proto F32DProto: exit 0
proto F32DProto2: exit 0
proto F32DProto3: exit 0
--- check-snippet t1 (exit 0)
Compiling snippet as leanncd/spikes/SnippetCheck_27549_6735.lean ...


COMPILES. Safe to write into the plan.
--- check-snippet t2 (exit 0)
Compiling snippet as leanncd/spikes/SnippetCheck_27614_27519.lean ...


COMPILES. Safe to write into the plan.
--- check-snippet t3oracle (exit 0)
Compiling snippet as leanncd/spikes/SnippetCheck_27681_22873.lean ...


COMPILES. Safe to write into the plan.
--- check-snippet t3compile (exit 0)
Compiling snippet as leanncd/spikes/SnippetCheck_27717_13558.lean ...


COMPILES. Safe to write into the plan.
--- oracle on the real tree (must be red):
  spikes/f32d_red.lean:231:0: error: BINARY32 SCATTER ORACLE FAILED: O1 strided, unary, carrier-discriminating: prepare failed
ALL OK
```

`#guard`s that pass print nothing, so "COMPILES" on a test file means every guard in it held.

## 3. Observed values

**Local (Task 1), prototype `runDenseScatter32`:**

| Case | Result |
|---|---|
| `Out[2*i] := X[i]`, `X = [1,2,3]` | `[6] [1065353216, 0, 1073741824, 0, 1077936128, 0]` |
| evidence kind, `checkScatterF32` / `checkScatter` | `.float32` / `.float64` |
| `checkScatterF32` on binary64 sigs; `checkScatter` on binary32 sigs | `dtypeNotAdmitted 1 .f64`; `dtypeNotAdmitted 1 .f32` |
| f32 sigs with the f64 algebra | `algebraNotAdmitted {… .f64 …}` (not used as a fixture) |
| f32 plan with f64 fill; with `reduce := .sum` | `scatterFillNotIdentity (.f64 0) (.f32 0)`; `scatterReduceNotAdmitted .sum` |
| `sqrt(X)+Y+Z`, `X=[2^48,4,9]`, `Y=[1,1,1]`, `Z=[-2^24,0.5,0.25]` | f32 `[0, 0, 1080033280, 0, 1082654720, 0]`; f64 `[1.0, 0, 3.5, 0, 4.25, 0]` = bits `[4607182418800017408, 0, 4615063718147915776, 0, 4616471093031469056, 0]`; narrowed lane 0 `1065353216` |
| same with the `sqrt` removed (a worker ignoring `unary`) | lane 0 `1468006399` ≠ `0` — so 1.4 also detects a dropped unary |
| max-product fill | `[1065353216, 4286578688, 1073741824, 4286578688, 1077936128, 4286578688]` |
| collision, `Y = [10, 100]` | `scatterCollision [0] [0, 0] [0, 1]` |
| context-shape `#[1]` plan, empty store | wrong carrier → `storageKindMismatch` (both directions); right carrier → `contextShapeMismatch #[1] []` |

Input bit patterns (from `Float32.toBits`): `2^48 = 1468006400`, `4 = 1082130432`,
`9 = 1091567616`, `1 = 1065353216`, `-2^24 = 3414163456`, `0.5 = 1056964608`, `0.25 = 1048576000`.

**Graph (Task 2), prototype `checkPlan`/`runDensePlan32`:** `f32ScatterPlan` accepted `.float32`,
slot 1 `[1065353216, 0, 1073741824, 0, 1077936128, 0]`; `f32UnsupportedStepOrder` accepted, slot 3
`[1069547520, 0, 1075838976, 0]` for `X=[1.5, 2.5]` and `[1069547520, 0, 0, 0]` for `X=[1.5,-2.5]`;
with `f32Scan` appended → `f32UnsupportedStep 3 .scan` (the real checker today reports
`f32UnsupportedStep 2 .scatter` for that graph); its binary64 twin reports
`duplicateDestination 2 1 3`, not a capability error. `runDensePlan` on the f32 scatter graph →
`storageKindMismatch .float64 .float32`. Not used as fixtures: an f32 graph with an f64 fill →
`nodeError 0 (scatterFillNotIdentity …)`; an f64 table with the f32 algebra → `algebraNotAdmitted`.

**Source (Task 3):** oracle cases O1–O5 all agree with their twins on the prototype; values in the
plan's table. Carrier contrasts, real binary64 runner: O1 binary64 `[1.0, 0, 3.5, 0, 4.25, 0]`
(narrowed lane 0 `1065353216`); O5 binary64 `[16785410, 0, 10, 0, 1.25, 0]` (narrowed lane 0
`1266683905` vs native `1266683904`). O2 and O3 do NOT discriminate (narrowed equals native): a
single rounding of exact binary32 operands is correctly rounded either way, which is why the plan
does not call them discriminators. Re-point observations: `capabilityPreflight` on
`[relu scatter, f32 scan]` → `unsupportedNonlin "Y: scatter nonlinearity"`; the two-scan program
reports `"S: f32 scan"` forward and `"T: f32 scan"` reversed on the REAL tree today (no scatter
involved); the prototype compiles `f32ScatterProg` to one `.scatter` step with `fill = .f32 0`,
`admittedAlgebraF32`, `destShape #[6]`, destination dtype `.f32`. `Float32.ofInt 0` bits `0`,
`Float32.ofInt 1` bits `1065353216`.

The oracle's red state on today's tree: `BINARY32 SCATTER ORACLE FAILED: O1 strided, unary,
carrier-discriminating: prepare failed`. The oracle's `compile32` discards the
`PlanCompileFailure`, so the CAUSE (expected: Step 0c's `"Out: f32 scatter"`) was not observed; only
that preparation fails.

DSL tokens found the hard way: `C(` and `T(` inside `tlprog!` do not parse as tensor declarations,
and a spike importing `LeanNCD.Eval.Entry` cannot use `bias :=` or `iter` as field syntax; that is
why the prototype modules import only what the real modules import, and why the twin is `Src`.

## 4. Mutation cycles

### 4.1 Real tree, through `mutation-manifest.sh` (7/7)

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| G1 (binary64 gate: collision arm overwrites instead of throwing) | yes | yes | yes | PASS |
| G2 (binary64 gate: placement bias dropped) | yes | yes | yes | PASS |
| K1 (shared checker core: f32 destination uses the f64 algebra table) | yes | yes | yes | PASS |
| S2 (checkPlan capability loop admits an f32 scan) | yes | yes | yes | PASS |
| S1 (Step 0c admits an f32 scan) | yes | yes | yes | PASS |
| S3 (Step 0c skipped: Step A answers first) | yes | yes | yes | PASS |
| C1 (compiler placement bias dropped; binary64 witness) | yes | yes | yes | PASS |

7/7 cycles passed. Every `old` string survives the slice's edits unchanged (checked against the
plan blocks), and every `expect` string names a fixture the slice does not edit (G1/G2:
`ScatterDenseTest`; K1: `KernelCheckTest`, built as a dependency of `KernelDense32Test`; S2:
`GraphCheckTest` fixture 16's scan guard; S1/S3: `CompileTest` 15(d), and S3's FW2a message, whose
prefix is unchanged by the FW2 re-point), so the seven should still PASS after execution. That is a
prediction until Task 3 step 6 runs them. `mutation-manifest.sh --check` on the final manifest:

```
manifest OK: 8 entries, 8 selected, every old-string unique
```

### 4.2 Prototype (code that does not exist yet)

Run with a small harness (mutate the prototype copy, rebuild the dependent prototype `.olean`s,
re-run the test spike, restore, rebuild, re-run — the restored run was clean each time). The table
is the SECOND run, on the prototype rebuilt from the final plan text by `f32d_verify.py`; a first
run on the hand-edited prototype agreed but its failure lists were truncated by a `head` in the
harness, which is why a first draft of this table listed fewer fixtures. P3-1's oracle failure
(`O1 … prepare failed`) was observed in the first run against the oracle spike; the second run of
P3-1 targeted the CompileTest re-points only.

| Cycle | Fixtures that failed |
|---|---|
| P1-1 `runDenseScatter` guard deleted | 1.7 first guard (`contextShapeMismatch` instead of `storageKindMismatch`) |
| P1-2 `runDenseScatter32` guard deleted | 1.7 third guard |
| P1-3 core stamps `.float64` | 1.1, 1.2 first guard, 1.4 (binary32 guard), 1.5, 1.6, 1.7 first two guards |
| P1-4 `fill := ops.zero` | 1.5 only (every other fixture's fill is `+0`) |
| P2-1 capability arm refuses scatter again | 14(a), 16(b), 14(c) first guard, 2.1, 2.2 (both), 2.3 |
| P2-2 `.float32` arm calls `checkScatter` | 14(a), 16(b), 2.1, 2.2 (both), 2.3 |
| P2-3 `runDensePlan32` scatter arm a no-op | 2.1, 2.2 (both guards) |
| P3-1 `scatterFillOrFail` `.f32 _ => false` | 15(c) both guards; oracle `O1 … prepare failed` |
| P3-2 Step 0c refuses scatter again | 15(c) both, 2.9 forward, FW2 relu-alone, FW2a (`got capability … "Y: f32 scatter"`), oracle O1 |
| C1b compiler placement bias dropped | oracle: `O2 shifted stride (placement bias): scatter [6]/#[1266683904, 0, 1050253722, 0, 1050253722, 0] ≠ oracle [6]/#[0, 1266683904, 0, 1050253722, 0, 1050253722]` — a DISAGREEMENT, which is the independence claim |

## 5. Re-derived facts (the controller's list, and siblings it did not name)

- `ScatterPlan @ Kernel.lean` fields: `compute`, `destShape`, `outCoeffs`, `outBias`, `fill`,
  `reduce` — read. `CheckedScatterPlan` has only `raw` — read. `checkScatter` calls
  `checkAssign … (some s.destShape)` then fill, reduce, placement — read.
- `runDenseScatter` has no storage-kind guard and uses `floatOps.decodeConst` and the Float
  `denseValueAt` — read. Its `.overwrite/.sum/.max/.min` arms use Float `+`/`Max.max`/`Min.min`.
- `runDensePlan32`'s `.scatter _ => throw (.storageKindMismatch .float32 .float64)` — read.
- Step 0c / `checkF32Stmt` / `scatterFillOrFail` `.f32 _ => false` / Step D scatter branch — read;
  Step D uses `algebraForDest destDtype rhs.agg`, and `algebraForDest .f32 = algebraForAggF32` — read.
- `rg -c "ScatterPlan|checkScatter|runDenseScatter|scatterFill|scatterPlacement"` over `Scan.lean`
  and `Block.lean` prints nothing (zero matches). The scan compiler's own helpers
  (`scanPlacementRows`, `scanOutputRowExtent`) call only `scatterDestExtent`; its fill check is
  `if opts.fill != 0`.
- Refusal-pinning siblings: the controller named CompileTest 15(c), FW2/FW2a, GraphCheckTest
  `f32UnsupportedStepOrder`, and F32-B's (c) cells. **Also found:** CompileTest fixture 2.9's forward
  guard (`"Y: f32 scatter"`), GraphCheckTest fixture 16's `f32ScatterPlan` refusal and its binary64
  control, and ScatterCheckTest fixture 9's rationale prose. No other test pins f32-scatter refusal
  (`rg` for `f32 scatter`, `f32UnsupportedStep`, `.scatter` over `test/`; `ScanTest` 11/12 are
  legacy and stay).
- JAX: `validateAndConstructExecutable` checks `storageKind == .float64` first; `EvalPlanCodegen`'s
  doors call `requireFloat64Plan` first; `ExecutableTest` fixtures 23/24 pin that order — read.
- Import-cycle check for Task 2's new `import Eval.Plan.GraphCheckTest` in `EvalPlan32Test`:
  `GraphCheckTest` imports only `LeanNCD.Eval.Plan.EvalPlan`; only `NonlinDense32Test` imports
  `EvalPlan32Test`.
- Baseline: `lake-build.sh leanncd` → `Build completed successfully (8670 jobs).`
- Injected AGENTS.md sections: `Eval/Plan` 692, `Eval` 1420, `leanncd` 0 characters (all < 3k).
- Counts today: `.unsupportedDtype s!` in `Compile.lean` 4 (scatter, scan, scanPre, mixed);
  `f32UnsupportedStep ni` in `EvalPlan.lean` 2; `throw (.storageKindMismatch .float32 .float64)` in
  `Dense32.lean` 2.
- `backend_missing_functionality.md`'s 10/16/6 `CapabilityError` split: `unsupportedDtype` keeps
  live producers (mixed, f32 scan), so the split does not move.

## 6. Not verified

- **The real modules were never compiled with the edits.** Everything rests on the prototype being
  the same text in the same import context. The two things that could differ: (a) a name the copy
  resolved to its own `P.` version where the real module would see a different one (none known —
  every copied definition is textually the real one); (b) instance or `private` visibility effects
  across the real `import` graph. The plan's STOP-on-mismatch rule covers both.
- C1b's `expect` string and the P-cycles' failures were observed on the prototype only.
- That G1/G2/K1/S1/S2/S3/C1 still PASS after the slice (predicted, §4.1).
- The post-slice build job count (predicted 8672).
- The documentation edits (Task 3 steps 7–9) are specified, not performed; the sweep commands were
  written against today's tree but not run as a "before" baseline beyond the grep in §5.
- Turn estimates in the plan's task table are judgement, not measurement.

## 7. Completion note (appended by Task 3 step 11)

_(empty until executed)_
