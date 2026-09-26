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

## 5b. Adversarial-review fixes (2026-09-25), measured on real-split copies

Method: the reviewer's `rv_build.py` applies every plan edit to FULL copies of the real modules
(real namespace and module split, `leanncd/spikes/F32DRV_*.lean`) and compiles them in dependency
order (must end `ALL COMPILED`); a companion runner applies one manifest mutation at a time to those
copies, compiles the mutated module and its dependents into a private `.olean` dir shadowing the
clean ones, and records the log (`spikes/mut_<label>.log`). Both scripts are preserved as
`papers/f32d_files/rv_build.py` and `papers/f32d_files/mut_run.py` (authoring-time tools; execution
uses the real `lake-build.sh`/`mutation-manifest.sh`).

**Group 1 — fill.** `Float32.ofInt (-(2^128))` → bits `4286578688`, `isFinite = false`;
`admittedAlgebraF32Max.reduceId = .f32 4286578688`. `Float.ofInt (-(2^1024))` → bits
`18442240474082181120`, not finite, and a hand-built binary64 `maxreduce` scatter with that fill IS
admitted by `prepareEvalPlan` today (`fill = .f64 18442240474082181120`, `admittedAlgebraMax`,
`.float64`): a pre-existing binary64 gap, left unchanged (plan §1.2). Before the finiteness
conjunct, the binary32 analogue (`-(2^128)`) was likewise admitted with `fill = .f32 4286578688`.
With the plan's arm: `fill := 1` → `scatterOptsNotAdmitted "Y: fill"`; `-(2^128)` on `agg := .max`
→ `scatterOptsNotAdmitted "Y: fill"`. Cycles: P3-3 (`.f32 bits => true`) fails both refusal guards;
P3-4 (finiteness dropped) fails the overflow guard only; P3-1 fails 15(c)'s two guards and the oracle
(`O1 … prepare failed`); P3-2 fails 15(c) ×2, both refusals, 2.9 forward, FW2 relu-alone, FW2a
(`got capability … "Y: f32 scatter"`), oracle O1.

**Group 2 — evidence strength.** (a) O5 redesigned (supersedes §3's O5 values): the old
`Out[2*i] := W[i] + B[i]` could not tell carriers apart in the scatter itself — native lane 0 and
"scatter half in binary64, then narrow" were both `1266683904`; only whole-program binary64 gave
`1266683905`, all from the F32-A assignment `W`. New RHS `W[i] + B[i] + Z[i]`, `Z = [-16785408, 0.5,
0.25]`: native `[0, 0, 1093140480, 0, 1069547520, 0]`; scatter half alone in binary64 over the native
`W = [1266683904, 1091567616, 1048576000]` (observed from the F32-A assignment) → `[1.0, 0, 10.5, 0,
1.5, 0]`, narrowed lane 0 `1065353216`; whole program in binary64 → `[2.0, …]`, lane 0 `1073741824`.
The file's O5 contrast is now the scatter-half reading. (b) `f32StepOrderWithScan` with two scans
(outer 3, 4) → `f32UnsupportedStep 3 .scan`; binary64 twin → `duplicateDestination 2 1 3`. (c)
Fixture 1.8 (Boolean-tagged source, `checkScatterF32` + `runDenseScatter32`) → `[1048576000, 0,
1056964608, 0, 1065353216, 0]`. (d) K1 DROPPED: under its mutation `KernelCheckTest`,
`KernelDenseTest` and `KernelDense32Test` fail, and `ScatterDense32Test` is never built (it imports
`KernelDense32Test` for `t32`), so K1 cannot guard any fixture this slice adds; the manifest is now
7 entries. (e) `ScatterDense32Test.lean` has 16 `#guard`s (`grep -c '^#guard'`), 8 fixtures.

**Group 3 — manifests.** `papers/f32d_mutations_post.json` (11 entries) was written from the
observed failures of the companion runner on the real-split copies; every `expect` string was
re-checked present in its mutated log (11/11). Observed shape differences from the prototype table
in §4.2, which the post manifest encodes: P1-4 breaks the BINARY64 `ScatterDenseTest` max-fill guard
first (shared worker), so `ScatterDense32Test` (which imports it) is not built and 1.5 cannot report
— target is `Eval.Plan.ScatterDenseTest`; under P2-1/P2-2 `GraphCheckTest` fails first, so
`EvalPlan32Test` (2.1–2.3) is not built — expects name `GraphCheckTest` guards only; P1-3 now also
fails fixture 1.8. Uniqueness: a scratch tree mirroring `LeanNCD/Eval/Plan/<File>.lean` and
`test/Eval/Plan/…` with the post-edit texts →

```
manifest OK: 11 entries, 11 selected, every old-string unique
```

(and `--task 1/2/3`: 4, 3, 4 selected, all unique; the P1-1/P1-2 anchors include the
`def runDenseScatter…`/`def runDenseScatter32…` signature lines because the guard text alone also
occurs at the assignment doors). The pre-slice manifest's old-strings are unique in the post-edit
texts too (`manifest OK: 7 entries, 7 selected, every old-string unique`), and G1, G2, S2, S1, S3,
C1b each fail with every `expect` present on the post-edit copies (C1 not run there: its target
`ScatterCompileTest` is not among the copied modules).

**Group 4 — docs sweep.** `rg -n checkF32Stmt` (excluding `papers/f32d_*`) today: the three
`Compile.lean` code/comment sites the slice deletes, `Error.lean` (retired-contexts history),
`Plan/AGENTS.md` `Compile.lean` row, `CompileTest.lean` `f32BadOrderProg` prose,
`backend_missing_functionality.md` retired-contexts sentence, and history in
`f32_evalplan.md`/`f32b_evalplan.md` — each now assigned an edit or an allow-list entry. The
multi-line `rg -U` in step 8 hits exactly nine wrapped stale sentences today (Dense32 ×3 incl.
`F32-C/D`, Check ×4, Error ×1, Dense ×1); after the prose edits it should print nothing (predicted —
the prose edits are specified, not performed). `rawPublicationSlots @ Prepared.lean` and
`assignPlans @ experiments/jax_bridge/EvalPlanAffineCorpus.lean` read: both carrier-free. Found in
passing, NOT fixed: `runDenseScatter`'s docstring says the reference "cannot express `±∞` at all",
false for the same `Float.ofInt` overflow as the binary64 fill gap (plan §1.2). Plan trimmed to 852
lines by moving §6 Risks, §9 Decisions and the oracle-scheduling note here (§6b).

## 6. Not verified

- ~~The real modules were never compiled with the edits.~~ Superseded 2026-09-25 (§5b): every plan
  edit was applied to full real-split copies (real namespace and module split) and compiled, with
  every test module in the chain. Still not done: `lake build` of the actual tree with the edits,
  and C1 on the post-edit copies (its target `ScatterCompileTest` was not copied).
- The P-cycles and C1b were re-observed on the real-split copies (§5b) with a runner that mirrors,
  but is not, `mutation-manifest.sh`/`lake build`; the restore-and-rebuild half was not run by it.
- That C1 still PASSes after the slice (G1/G2/S1/S2/S3/C1b re-observed on post-edit copies, §5b;
  K1 dropped).
- The post-slice build job count (predicted 8672).
- The documentation edits (Task 3 steps 7–9) are specified, not performed; the sweep commands were
  written against today's tree but not run as a "before" baseline beyond the grep in §5.
- Turn estimates in the plan's task table are judgement, not measurement.

## 6b. Decisions and risks (moved from the plan, 2026-09-25; none needs the user)

### Risks

Each task's dominant risk and its pin: the move into `runDenseScatterWith` (G64 + G1/G2 before and
after); a guard placed after validation (1.7, P1-1/P1-2); the real compiler emitting a different f32
plan than the prototype (15(c)'s second guard, the oracle's pinned bits, §8); a re-pointed order
fixture that stops pinning order (each re-point names the wrong answers it rejects; S2, S3, P2-1,
P3-2); an oracle sharing code with its subject (§3.5; C1b); a stale document nobody opened (Task 3
step 8's value-greps).

### Oracle scheduling

**Scheduling.** It is Task 3 phase 1's FIRST step, written before the compiler edit and observed
failing (`BINARY32 SCATTER ORACLE FAILED: O1 strided, unary, carrier-discriminating: prepare
failed`, observed on today's tree). That is the earliest point it can run at all: it needs Step 0c
lifted, and Step 0c is the last door.

### Decisions

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

## 7. Completion note (appended by Task 3 steps 4 and 11)

_(empty until executed)_
