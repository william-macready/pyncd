# P6 findings (T6: scan state init at the state's 0_K; neutral base adopts the state's sort)

Branch `proto-s3b-p6` (from proto-s3b-p5 6b0cb23b). Commits: `83102c7b` T6-01 production (6 files, +106/-25), `3476f129` T6-02 tests (3 files).
Patches (apply --check -R verified at the tip): `T6-01-production.patch` (6b0cb23b..83102c7b), `T6-02-tests.patch` (83102c7b..3476f129).
Mutations: `p6_mutations.json` (12 entries, `--check` OK, expect strings empty, none run).

## (a) Corrections to audit / design (read first)
1. **Neither backend needs the `algebras` map.** Reused the T4 agreement logic over the scan's own statements: `Stmt.ownAlgebra?` moved
   from `ScheduledValidation.lean` to `DSL/Ast.lean` (so `Eval/Scan.lean` can reach it; no import cycle), plus `scanStateSorts`
   (the per-name list `scheduleAlgebras` checks for agreement, now shared), `scanStateAlgebra` (headD real), `SortAlgebra.stateAgg`,
   `Stmt.withAgg`, `scanStateStmts env base recur`. `evalScan`/`compileScan` signatures are unchanged.
2. **The one mechanism is annotation rewriting, not a new parameter.** `scanStateStmts` rewrites every sort-neutral statement's `agg` to
   the state's `stateAgg` (maxPlus -> max, minPlus -> min, real/bool -> sum). Both backends already take pad (`reduceId` / `Combine.unit0`)
   and the T5 bool-cast key from `rhs.agg`, so "neutral base adopts the state's sort" and "change `boolReadCast` and the `tropical` flag
   together" both fall out with ZERO edits to `boolReadCast` / `residualizeAssignment` / `algebraForDest`. Consequence for mutations: the cast key
   cannot be mutated separately from the pad; T6-M5/M6 (drop the rewrite per backend) and M7 (force `.sum`) cover it.
3. **The rewrite applies to every neutral statement of the scan, scratch included** (the audit said "base statement"). Reason: `scheduleAlgebras`
   gives an all-neutral name the sort `real`, so a neutral scratch annotated `max` is now evaluated real (pad 0, not -inf), consistent with
   `algebraOf`. Observable only for an annotated NEUTRAL scratch/recurrence statement with an OOB bare read; no existing test does that
   (full `Tests` green). Flag for the plan: keep (consistent with the map) or restrict to base+state names.
4. **Raw plan carries a SORT, not a constant.** New `inductive StateInit (zero | negInf | posInf)` in `Plan/RawStep.lean`, new field
   `StateSlot.initValue : StateInit := .zero`. Carrier-independent, so the default is valid for f32 and f64: **no raw-plan literal in any test needed
   an edit** (`StateSlot` literals in ScanTest/GraphCheckTest/ScanCompileTest compile unchanged). The worker `runDenseScanWith` takes `zero negInf posInf`
   (f64 `-1.0/0.0`, `1.0/0.0`; f32 `Float32.ofBits 0xff800000 / 0x7f800000`). `commitWrite`'s `zero` default is untouched (never observable:
   `out.data.getD ... zero` is in-range).
5. **New Check rule** (in `checkScanCore`, `ScanPlanError`, NOT `PlanError`; scan-plan errors live in `Plan/Scan.lean`):
   `stateInitNotAdmitted (stateIndex) (init) (dtype)`: a `negInf`/`posInf` init on a `.bool` state signature. No `match` on `ScanPlanError` is exhaustive
   anywhere (derived instances only), so adding the constructor needed no other edit. `constMatchesDtype` is not involved (no constant in the plan).
6. **Scratch cannot be written in the surface.** `M[r] := maxreduce(...)` inside a scan gives `CompileError.scanProjectionUnsupported "M"`; scratch fixtures
   must be raw `ScheduledProgram`s (donor `scratchPredicateSched`). Fixture (e) is raw, in `ScanCompileTest`.
7. Prediction check: every value fixture (a, b, c, d, f) passed the first time in all three backends; only the surface scratch fixture failed (item 6).
8. `buildDeclEnv` is now called twice per `evalScan` (`rejectUnsupportedStorage` already does once); it throws `.compile` on failure exactly as that guard does.

## (b) Tests flipped (old -> new)
- RC10 (`RecurrenceTest`): `G[0,1]` 0 -> -inf, expected `[2,0,5,5]` -> `[2,-inf,5,5]`. Why: the state is max-plus (recurrence `maxreduce`) and the cell is never written.
- Nothing else flipped: ScanTest, ScanDense*, ScanUnroll/ScanOracle property oracle, ExecutableTest, DifferentialTest sweep counts all stayed green
  (the property oracle did NOT go red: its scans have real state or no unwritten tropical cell).

## (c) Red targets (full `Tests`, 8824 jobs)
- (ii) deferred, inherited: `Semantics.SourceSortedDifferentialTest`, still exactly 19 error sites. (i) T6-owned: none red. (iii) UNEXPECTED: none.
- Library `LeanNCD`: 8614 jobs green (before tests).

## (d) Fixtures (donors; all in three-way `assertAgree` unless noted: reference, plan f64, plan f32)
BoolCastTest.lean (section "S3b T6"; donors RC10 + `scanMax` + the T5 harness):
- a1/a2 `stateMax`/`stateMin` (RC10 shape, `[2,-inf,5,5]` / `[-2,+inf,-5,-5]`); b `stateSum` keeps 0 (`[2,0,5,8]`);
- c1/c2 neutral base with OOB `X0[j+1]` (`axis j : ℕ = 3`): `[-2,-2,-3,-3,-inf,-inf]` / `[2,2,3,3,+inf,+inf]` (old code: 0 in the last row);
- d1/d2 neutral base bare-reading `predicate P`: `[0,0,-inf,-inf,0,0]` / `[0,0,+inf,+inf,0,0]` (old code: raw 1/0 in the base);
- f1-f3 compiled-plan probe `scanInits`: max-plus `#[.negInf]`, min-plus `#[.posInf]`, sum `#[.zero]`.
ScanCompileTest.lean: (e) raw schedule `scratchMaxSched` (max-plus scratch `T`, state `S` stays real: `initValue = #[.zero]`, scratch algebra `admittedAlgebraMax`, `checkerAgrees`);
(g) raw-plan guards for `stateInitNotAdmitted`: accept `zero/negInf/posInf` on an f64 state, reject `negInf`/`posInf` on a bool state sig, neighbours `zero`+bool and `negInf`+f64 not rejected by this rule.
RecurrenceTest.lean: RC10 flipped; new RC10m (min-plus twin, `[-2,+inf,-5,-5]`).

## (e) Budget
About 62 tool calls, context peak roughly 150-170k (two avoidable costs: a wide `rg` over the 2.8M test log dumped 19 huge `info:` lines; each Edit echoed the intent-layer hook text).
No hand mutation runs.

## (f) For the T7 author (SourceSortedDifferentialTest, 19 red sites)
Cause for all: since T1-T5 production's tropical multi-factor `⊗` is `+`, scatter empty fibers are `0_K`, and the empty product is `1_K = 0`, so the oracle/production
"known contract differences" (`tropicalMultiFactor`, `tropicalScatterFill`, the zero-factor `1.0` vs `0` discrepancy) no longer exist. Actual outputs read from the p5 `Tests` log;
T6 did not change them (still 19 sites, same set).
Site (line of the command) | asserts today | after production (= oracle)
- 104 `classOf (product .max)`, 106 `(product .min)` | `knownContractDifference (tropicalMultiFactor ..decl 6)` | `fourLegParity`
- 108 `classOf (strided .max)` | `knownContractDifference (tropicalScatterFill ..)` | today `nativeFailure` (binding issue, see below); with the extent fixed: `fourLegParity`
- 188 `known (strided .min)` | `"scatterFill (some 6)"` | today `"not known: nativeFailure ..shape Y [7] vs [8]"`; with extent fixed `"not known: ..fourLegParity"`
- 191 `[bareY,multiV]`, 193 `[multiY,bareV]`, 196 `[multiY,multiV]` | `multiFactor (some 7|6|6)` | `"not known: ..fourLegParity"` (same string row 198 already asserts)
- 201 `[stridedY,bareV]`, 204 `[bareY,stridedV]`, 206 `[stridedY,stridedV]`, 209 `[stridedY,multiV]` | `scatterFill (some 6|7|6|6)` | today `nativeFailure` binding issues on Y and/or V (`shape [7] vs [8]`); with extent fixed `fourLegParity`
- 227 `#guard fills nY 6`, 228 `#guard fills nV 7` | the confirmer accepts the native legs | false: `nativeOf` is `none` (binding failure) and, once extent fixed, the legs agree so `confirmsSorted .. tropicalScatterFill` is false. Dead condition: delete or rewrite as a negative pin.
- 242 `#guard multi 7` | `confirmsSorted .. tropicalMultiFactor` accepts | false (legs agree): same, dead condition.
- 262 `tagOf [bareY, zeroV]` | `"nativeDiscrepancy at 7, bits 4607182418800017408"` (1.0 vs oracle 0) | `"parity"` (production empty product now 0)
- 264 `[multiY,bareV]`, 269 `[multiV,multiY]` | `"multiFactor (some 6)"` | `"parity"`
- 266 `#guard (tagOf [multiY, zeroV]).startsWith "nativeDiscrepancy"` | unexplained divergence beside a known one stays reported | false (`"parity"`): the `zeroV` probe can no longer produce a real divergence; to keep the intent (`unexplainedAgree`/"known condition must not hide an unexplained mismatch") a new genuinely divergent probe is needed, or retire it (292-294 `unexplained` rows are green and still pin `unexplainedAgree`, they operate on oracle cells).
- 272 `#guard !(match .. checked with | .mismatch c => confirmsSorted .. | _ => true)` | negative guard (mismatch by +1 bits is not confirmed) | the `| _ => true` arm now fires (checked leg agrees), so `!true` fails: rewrite or drop with the dead condition.
Also affected but NOT red today and will flip if extent 7 -> 8: `yCore (strided .max/.min)` rows (89/91, 7 cells) gain a trailing `±inf` cell.
Also unaffected: Q6 selection rows, Q5 single/product values, extent-0 rows, accept-neighbour 198, 229-232 (trivially true on `none`).

**The `BindingIssue.shape [7] vs [8]` site (108/188/201/204/206/209).** It is production's derived extent versus the snapshot's declared extent: `strided` declares `Y` over axis `k` with `extent = 7`
(`snap`'s `extent` function: uid 9 -> 7; the oracle writes `Y[2a]`, a < 4, so the highest cell is 6), while production derives the scatter destination extent as `c0 + sum coef*extent` = `2*4 = 8`
(`derivedShape` in `Semantics/Source/Differential.lean:191`, "`2*a` over 4 gives 8"). The native output binding compares the declared spec `[7]` with production's `[8]` and fails BEFORE any value comparison.
That is exactly the `scatterExtentOverridesDeclared` condition (`detectConditions`: nonBare write, single writer, `declared != derived`), which the plain differential suppresses value comparison for and the
SORTED classification has no arm for: before T3 production refused/mis-valued the strided tropical write, so the extent mismatch was never reached. Fix options for T7: (1) preferred: declare `k` extent 8 in the sorted snapshots
(`extent`: uid 9 -> 8; the oracle then has a trailing empty fiber `-inf`, matching production's `0_K` fill); (2) give the sorted classification a `scatterExtentOverridesDeclared` arm like the plain one.
