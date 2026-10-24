# P8 findings (T8: negation-duality property, scan oracle on tropical states, fixture twins, one parked pin)

Branch `proto-s3b-p8` (from proto-s3b-p7 7473023d). TESTS ONLY: no file under LeanNCD/ was edited.
Mutations: `p8_mutations.json` (6 entries, `--check` OK, expect strings empty, none run).

## (a) Production bugs / corrections to audit and design (read first)
1. **No production bug found.** Duality holds exactly on the reference, the checked plan f64 and the checked plan f32 for every program the generators emit.
2. **TEST-SIDE ORACLE BUG, now fixed (audit section 8f.4 confirmed).** `ScanUnroll.lean` built the zero leaf (`terms := []`) and the base-contribution merge with the DEFAULT `agg := .sum`, so on a tropical state with an
   UNWRITTEN cell the independent unrolling filled it with the real 0. Minimal case (new `ScanGen.templateTropGrid`, RC10-shaped): `G[r,0] := Z[r]; G[r+1,c+1] := maxreduce(G[r,c]·W[r,c,k])`, cell `G[0,1]` is written by nothing.
   Before the fix the oracle reported `SCAN-UNROLL law violated: state G differs — left (legacy evaluator) = [2,-inf,5,5], right (unrolling) = [2,0,5,5]` and for min `left = [-2,inf,-5,-5]`, `right = [-2,0,-5,-5]`. Production was right (T6), the oracle wrong.
   Fix (test-side, `ScanUnroll.localStateAgg`): zero leaf and merge take the state's own aggregation.
3. **Rule 14 / brief deviation, surfaced:** the property's enumPrograms leg tropicalises the sweep (every `agg := .sum` -> `.max`/`.min`) because the sweep itself has no max aggregation at all (Gen.lean: all `agg := .sum`); there is no "max sweep" to twin.
4. Syntax trap found while adding the scatter cases: in the tlprog! source language `Out[i + 1] := ...` is a SCAN advance (`scanAxisNotIter`), not an affine scatter; use `Out[2 * i + 1]`.
5. Budget breach (Rule 6): about 75 tool calls against the ~60 brief (context stayed well under 250k). Reason: the property module needed three iterations to pin counts (the distinguished measure, the grid, the scatter syntax) plus the oracle probe.

## (b) The duality property
- **Location:** new module `test/Eval/Plan/DualityTest.lean`, registered in `lakefile.toml` `Tests` globs after `Eval.Plan.DifferentialTest`.
- **Statement:** for each program P, `P` = every statement tagged `agg := .max`, `P'` = every statement `.min`, inputs of `P'` negated: `result(P', -x)` equals `-result(P, x)` cell for cell (IEEE `==`: `+0 = -0`, equal infinities equal, NaN fails), same key set and shapes; refusal must be symmetric.
- **Backends:** reference (`evalScheduled`, f64 only), checked plan f64 (`prepareEvalPlan` + `runPreparedDense`), checked plan f32 (`runPreparedDense32`, inputs declared `f32`, outputs default f32; the reference is f64-only so there is no f32 reference leg).
- **Coverage (pinned by one `#guard`, all three backends identical):**
  - `enumPrograms`: 3832 programs, 3832 dual / 0 refused / 0 skipped per backend; 3754 of them differ from the all-`sum` run (non-vacuity; the other 78 are programs whose max result coincides with the real result, e.g. a single read).
  - `enumScanCases` (17): 13 checked per backend (13 dual / 0 refused), 4 SKIPPED explicitly (template 2: `relu` nonlinearity, outside the property); 13 distinguished from the real run.
  - `tropicalUnwrittenScanCases` (2, new): 2 dual per backend, 2 distinguished.
  - top-level scatters (2: `Out[2i]`, `Out[2i+1]`): 2 dual per backend, 2 distinguished.
  - Skips: 0 in the sweep, 4 in the scan corpus (predicate destinations: none occur in either corpus).
- **Non-vacuity:** a sum-only program is its own negation dual under the REAL algebra, so agreement alone proves nothing; `distinguished` (max result differs from the all-`sum` result) is pinned. Also the tester is tested: `dualEqOf` guards (equal-not-negated fails, -inf/+inf and signed zero pass, NaN fails).
- **Circularity:** the property compares production with itself under a symmetry; it uses no production state init, no fibre fold, no expected value. A mirror-asymmetric bug fails it; a bug that is mirror-SYMMETRIC and negation-fixed (a wrong constant 0.0 in both sorts) cannot be caught by it, by construction (see mutations M3).
- **Cannot express:** predicate/bool programs (bool is not tropical), nonlinear programs (tropical + nonlin refused), the Source differential rows (`SourceSortedDifferentialTest` helpers are agg-parametric and every T7 row already has its min twin).

## (c) Fixture-gap table (`rg -n "maxreduce|minreduce|AggOp.max|AggOp.min"` per file)
| file | fixture | twin exists | disposition |
|---|---|---|---|
| Portfolio/ConvPoolTest | max-pool L44/L57, exp-pool L98 | yes (min L66, L108) | none needed |
| Portfolio/GnnScatterTest | GN4 `maxreduce(edge·X)` (bool cast) | no | ADDED `GN4m` (edge moved so the masked row would win under a wrong cast; GN4 itself does not discriminate a cast of 0.0, noted) |
| Portfolio/ClassicalMLTest | CM3 `Vn[s] := maxreduce(Q[s,a])` | no | intentionally none: a Bellman-max, no min analogue; construct (single-read contraction) covered by the property |
| EvalExamplesTest | `Peak[] := maxreduce(X[i])` multi-output | no | ADDED `Trough[] := minreduce(X[i])` (rank-0 output is not in the property) |
| DSL/MaxReduceTest | parse `maxreduce` agg=.max; evalAssignWith max-times parameter tests | no | ADDED parse twin (`minreduce` -> `.min`); the `evalAssignWith (·*·) floatMax ..` rows are a legacy harness with explicit algebra parameters, so a min twin would test the parameters not the product: intentionally none |
| Plan/Adapter32Test | fixture 9 max/min | yes | none needed |
| Plan/ScatterDenseTest | F4 (L314-324), TropCollide | yes (min rows present) | none needed |
| Plan/ScatterDense32Test | (no tropical fixture at all) | n/a | PARKED: no f32 tropical scatter fixture in either sort; the property now covers f32 scatter for two shapes (plan32 leg) |
| DSL/Pipeline/CollectTest | C6, C6b, C6c max multi-writer refusals | no | ADDED c6min, c6bm, c6cm |
| Eval/CollectEvalTest | J4 | no | ADDED J4m |
| PropertyOracle/ScanGen | template 5 | yes (`useMax` false) | none; NEW template 7 (grid, both sorts) |
| Plan/DifferentialTest | 7 hits; sweep; S3b scatter at L2082 | yes | none needed |

## (d) ScanGen unwritten-cell result
New `templateTropGrid (useMax)` + `tropicalUnwrittenScanCases` in ScanGen (kept OUT of `enumScanCases`, whose length 17 is pinned in five places). The oracle DISAGREED before the fix (see (a)2) and agrees after.
Circularity avoided: `localStateAgg` derives the state's aggregation from the statements' annotations in the test (a non-neutral statement's `agg`; the neutral-writer classification is restated test-side as `localNeutral`), and calls none of `scanStateAlgebra`, `scanStateSorts`, `stateAgg`, `StateSlot.initValue`. The independent unrolling's zero leaf is then the empty `agg` fold = the sort's `0_K` computed by the ordinary assignment evaluator, not by any scan init code.
Guards: `ScanOracle` `#guard (tropicalUnwrittenScanCases.findSome? checkScanLaw).isNone` plus a value guard on the legacy evaluator (`[2,-inf,5,5]` / `[-2,inf,-5,-5]`); `DualityTest` pins both values on the reference AND the checked plan, and the dual property runs on the grid.
Not done: the grid cases are not registered in `DifferentialTest`'s three-way (compiled plan, legacy, independent) leg (cost: one more list there); ref-vs-plan agreement is covered by the DualityTest value pins.

## (e) The parked pin
`DualityTest.lean`, `parkedAllNeutralScanState` (comment block starts `PARKED (S3b):`). `M[j,0] := maxreduce(X0[j+1])`, `M[j,l+1] := maxreduce(M[j,l])`, X0 = [3,4], L = 2: both statements are sort-neutral, so the state is real and the out-of-range read pads with the real 0.
Current behaviour pinned on the reference AND the checked plan: `M = [[4,4],[0,0]]`. The alternative (a neutral annotation votes for the sort when nothing else does) would give `[[4,4],[-inf,-inf]]`. No S3b task changes it; it is a design-note decision. Mutation T8-M5 flips it.

## (f) Full `Tests`
Final tip `43e86c5d`: **green, 8825 jobs (p7: 8824 + the new `Eval.Plan.DualityTest`), ZERO red targets.** An intermediate full build had exactly one red target (`DualityTest`, the scatter-syntax pin), fixed before the final build.
Commits: `2103edb7` T8-01 (scan oracle: ScanGen/ScanUnroll/ScanOracle, 3 files +74/-2), `43e86c5d` T8-02 (DualityTest + lakefile + 5 twin files, 7 files +331/-1).
Patches (`apply --check -R` OK at the tip): `T8-01-scan-oracle.patch` (7473023d..2103edb7), `T8-02-duality-property.patch` (2103edb7..43e86c5d).
Correction to (b): the "78 programs where max coincides with the real result" is a count (3832-3754), the reason is not investigated.

## (g) Calls and context
About 75 tool calls (over the ~60 budget, see (a)5); peak context roughly 150k. No hand mutation cycles.
