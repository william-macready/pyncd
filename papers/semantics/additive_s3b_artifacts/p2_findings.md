# S3b P2 findings (T2: padding, Iverson and constants come from the algebra, both backends, f64 and f32)

Branch `proto-s3b-p2` (worktree left checked out on it), from `proto-s3b-p1` tip c9c8f537.
Commits: `e81e8919` T2-01 production (9 files, +58/-46), `398d197b` T2-02 tests (7 files, +356/-20).
Patches in this directory: `T2-01-production.patch` (c9c8f537..e81e8919), `T2-02-tests.patch` (e81e8919..398d197b).
Replay proof: `git apply --check -R` of each patch at tip 398d197b exits 0 (no output).

## (e) Audit / design corrections (read first)

1. The `approxEq` fix is PRODUCTION source (`LeanNCD/Eval/Tensor.lean`), not a test helper, so it lands in T2-01. `evalEqB` (Harness.lean) needs no change: it calls `DenseTensor.approxEq` and compares shapes, nothing else blocks infinities.
2. `ScalarKernelOps.one` becomes dead once the Iverson arm decodes `factorId`/`reduceId`. T2-01 deletes it; `zero` stays (the real 0 used for the unary pad only). A plan author who keeps `one` leaves an unused field. Doc on `zero` rewritten.
3. The `store[f.sourceSlot]? = none` branch in `gatherFactorWith` is UNREACHABLE through every public door: `validateStore` (Dense.lean:171, called at 270/309/377) returns `PositionalInputError.missingSlot` first. Decision: it pads like an in-bounds miss/OOB (`padV`). No fixture can observe it; the doc says so. (Not a behaviour change.)
4. The pad has TWO values inside one function: a bare read pads with the decoded `reduceId`, a unary read with `ops.zero`. Implemented as `padV := match f.unary with | none => pad | some _ => ops.zero`, with `pad` = `reduceId` passed by the sole caller `denseValueAtWith`. The in-bounds-miss `getD` also uses `padV`.
5. `gatherRead` (reference) gained a `pad` parameter; its only callers are inside `gather` (no test or scan path calls it). `gather` has exactly two production callers (Contract.lean evalAssignSeeded, Scatter.lean evalScatter) and one test caller (test/Eval/GatherTest.lean, 4 calls, migrated to `(0.0, 1.0)`). No scan path calls `gather`.
6. Almost no existing expectation changed: only `oobMaxPlan` and its f32 twin (fixture 9). No RC-series, ConvPool, Portfolio, ExecutableTest, DifferentialTest, ScanTest, MaxReduceTest row changed (none pads or uses a false Iverson under a tropical statement, or they agree either way). Budget T8 migration for T2 accordingly: zero extra files.
7. The existing f32 fixture-9 comment already said "if the pad were `-inf` this would return [-1,-3]": the old fixtures documented the intended value.
8. Under the OLD Iverson constants a false tropical Iverson contributed `0.0` = the SAME as a true one, so a false mask was invisible (`falsePredPlan` under max-plus gave the unmasked `A+3`). That is why the fixtures use a coordinate-dependent mask `[i <= j]` and a row with no kept j.
9. Toolchain actually used by `lake-build.sh` here: Lean 4.30.0 (p1_findings said 4.35); irrelevant to behaviour.
10. Python/ConvPool surface works as expected: `maxreduce(exp(X[2 * i + p]))` parses (unary under a tropical statement is expressible at source level), `axis i : ℕ = 2, p : ℕ = 3` with `X : [4]` yields an OOB read at i=1,p=2, and `predicate E(j), B(i)` + `B[i] := E[2*i+p]` gives a bool statement with an OOB read.

## (a) Observed old -> new (migrated expectations)

| File | Label | Old | New | Why |
|---|---|---|---|---|
| test/Eval/Plan/KernelDenseTest.lean | oobMaxPlan (A=[[-1,-2],[-3,-4]], j in 0..2) | [0, 0] | [-1, -3] | bare OOB pad is -inf, max over valid cells |
| test/Eval/Plan/KernelDense32Test.lean | fixture 9 (f32 oob) | bits [0, 0] | bits [3212836864, 3225419776] = [-1, -3] | same |
| test/Eval/GatherTest.lean | 4 existing `gather` calls | `gather env ...` | `gather 0.0 1.0 env ...` | new signature; values unchanged |

Everything else is unchanged and green.

## (b) Red-target classification (full `Tests`, run twice: after test edits and after mutation restore)

| Target | Class |
|---|---|
| Eval.Portfolio.GnnScatterTest (GN4: false vs true) | (ii) deferred to T5 (bool -> max-plus cast); same as T1 |
| Semantics.SourceSortedDifferentialTest (same 11 `#guard_msgs` sites as T1) | (ii) deferred to T7 |
UNEXPECTED: none. No T2-owned red remained.

## (c) Job count
Full `Tests`: 8823 jobs (both runs). LeanNCD library alone 8614.

## (d) Fixtures, donors, mutation runs (each witnessed red on the intended rows, then reverted; `git diff` of LeanNCD empty after each)

| Fixture | Donor | Mutation witnessed |
|---|---|---|
| KernelDenseTest oobMaxPlan (migrated), oobMinPlan twin (store negated, [1,3]), oobRealPlan (real, [-3,-7]), oobBoolPlan (bool, [0,1]); f32 fixture 9 + min twin + real + bool neighbours (bits) | oobMaxPlan | `gatherFactorWith` bare pad -> `ops.zero`: KD lines 125,132; KD32 361,364 red; real/bool/unary rows green |
| KD `unaryPlan .exp 1` under max/min (233,235); KD32 fixture 2.3b (602,604) | unaryPlan / f32PadStore | unary pad -> `pad`: exactly those 2+2 rows red |
| KD maxTrue/maxFalse/minTrue/minFalse (donors truePredPlan/falsePredPlan), lePredPlan `[i<=j]` max + min twin + real neighbour; KD32 same in bits (fixture 10b) | truePredPlan, falsePredPlan, contractPlan | Iverson false -> `ops.zero`: KD 872,875,891,898; KD32 413,417,430,432 red. Iverson true -> decoded real one (old `ops.one`): KD 871,874,891,898; KD32 411,415,430,432 red. Real rows green in both |
| KD/KD32 tropical empty product (efpPlan), empty sum (etaPlan), zero-extent (zerdPlan), both sorts | efpPlan/etaPlan/zerdPlan | regression pins: already true after T1. Reference-side mutation below shows they bite |
| GatherTest: bare pad max/min, in-range, unary pad max/min (exp), Iverson true/false max/min, real/bool rows (lines 40-55) | existing GatherTest block | ref gather bare pad -> 0.0: rows 40,41 red; unary pad -> zero: rows 47,48 red; Iverson -> old `1.0/0.0`: rows 50-53 red |
| ConvPoolTest CV5o/CV5od (pad), CV5r (real neighbour), CV5b (bool neighbour), CV5u/CV5ud (unary under exp, f64 reference e2e) | CV5 maxpool | same two ref mutations: CV5o, CV5od red (bare); CV5u, CV5ud red (unary); CV5r, CV5b green |
| TropicalTest TR10/TR10d (Iverson mask max/min), TR10e/TR10ed (all-false row = -inf/+inf) | RC3 prefix-sum mask | Iverson -> old constants: all four red |
| ContractTest (reference) empty product/sum/zero-extent x max/min/real (lines 262-270) | existing evalAssign usage + Combine | `Combine.tropical` (unit0,unit1) -> (0.0, 1.0): 262,265,266,268,269 red; 263 (min empty product) masked by that same mutation (min(0,1)=0); real rows 264,267,270 green |
| TensorTest approxEq inf/-inf/NaN guards | existing approxEq guards | scratch `spikes/s3b_t2_approx_probe.lean` (gitignored): old body returns false for equal infinities, new true; TR10e also depends on it |

No new helper beyond two tiny private defs in GatherTest (`okIs`, `negInf`/`posInf`) and `refRows` in ContractTest (3 uses each).

## (f) Turns and context
About 90 tool calls (over the ~60 budget: nine mutation cycles, two full-`Tests` runs, ~12 read/compare calls). Peak context roughly 150k; no whole build log was Read (only `rg` and one 16-line window). Breach surfaced: mutation cycles are the cost; a plan should give them their own dispatch or fold min/max twins into one mutation each, as done here.
Helpers in this directory's parent scratchpad: `mut.sh <target> <test files>` (build then `lean-file.sh` per test file, prints failing line numbers; usable for f32 despite KD red because it bypasses lake's import blocking) and `mut2.sh <lake targets>`.

## (g) Facts for the T3 author (top-level tropical scatter)
- `Scatter.lean` after T2: `evalScatter` already calls `gather c.unit0 c.unit1 env coord f` with `c := combineFor decls nm rhs.agg`, so scatter source values already get the right pad/Iverson. UNCHANGED by T2 and still T3's: `let boolDest := isPredicateDest decls nm`; `out := DenseTensor.ofFn outShape (fun _ => 0.0)` (init must become `c.unit0`); fold `out.set! oc (if boolDest then Max.max prev val else prev + val)` (must become `c.combine prev val`, boolDest special case disappears; note `Max.max` there is NOT the NaN-propagating one).
- Guards that still refuse tropical top-level scatter (T3 deletes): `checkScatterAgg` (Eval/Eval.lean:32, called :57, raises `EvalError.scatterFillNotIdentity`); `scatterAggOrFail` (Plan/Compile.lean:545, called :1595, raises `CapabilityError.scatterOptsNotAdmitted`); the sorted-source refusal in Semantics/Source/Adapter.lean:33 and Admission.lean:905 (T7 territory, plus `tropicalScatterFill` in NumericalProfile/SortedDifferential/Differential).
- The plan scatter fill is already `reduceId` (Dense.lean ~382 `runDenseScatterWith`), and its compute half goes through `denseValueAtWith`, so after T2 the checked backend's scatter values (pad, Iverson) already follow the algebra. Only the guard stands between a tropical scatter and the checked backend; the Dense.lean doc at ~358 already states the `∓∞` fill.
- Tests that mention these guards and will flip: tests pinning `scatterFillNotIdentity`/`scatterOptsNotAdmitted` (rg them), `SourceSortedDifferentialTest` tropical-scatter rows (T7), GN4 is bool-cast (T5, not scatter).
- Reference scatter OOB write is already an error (B6), unaffected.
