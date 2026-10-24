# S3b record: production tropical sorts become max-plus and min-plus

Status: EXECUTED 2026-10-24. The measured results are in section 9 (written by the controller); the per-section `TBD` cells below were not individually filled and are superseded by section 9.
Plan: `papers/semantics/additive_s3b_plan.md`. Design: `additive_s3b_design.md` (§9 is the landed shape). Prototype evidence: `additive_s3b_artifacts/` (`p1..p8_findings.md`, `manifest_report.md`).
Line numbers are never written in this file (identifiers only).

## 1. Changes (one row per task; fill after each commit)

| Task | Commit | Patches applied | Targets | Jobs (`Tests`) | Red list observed (must equal the plan's known-red set) | Turns | Context peak | Breach? |
|---|---|---|---|---|---|---|---|---|
| T1 | TBD | T1-01, T1-02 | `Tests` | TBD (expect 8823) | TBD (expect GN4 + SSDT 11 sites) | TBD | TBD | TBD |
| T2 | TBD | T2-01, T2-02 | `Tests` | TBD (8823) | TBD (GN4 + SSDT 11) | TBD | TBD | TBD |
| T3 | TBD | T3-01, T3-02 | `Tests` | TBD (8823) | TBD (GN4 + SSDT 19) | TBD | TBD | TBD |
| T4 | TBD | T4-01, T4-02 | `Tests` | TBD (8823) | TBD (GN4 + SSDT 19) | TBD | TBD | TBD |
| T5 | TBD | T5-01, T5-02 | `Tests` | TBD (8824) | TBD (SSDT 19) | TBD | TBD | TBD |
| T6 | TBD | T6-01, T6-02 | `Tests` | TBD (8824) | TBD (SSDT 19) | TBD | TBD | TBD |
| T7 | TBD | T7-01, T7-02 | `Tests` | TBD (8824) | TBD (none) | TBD | TBD | TBD |
| T8 | TBD | T8-01, T8-02 | `Tests` | TBD (8825) | TBD (none) | TBD | TBD | TBD |
| T9 (A) comments-only Lean, 7 files | TBD | none (commands) | `Tests` (full; builds the library and the touched test modules), then `JaxExperiment` | TBD (expect 8825) | TBD (expect none) | TBD | TBD | TBD |
| T9 (B) docs, 12 docs | TBD | none (commands) | none (markdown only) | n/a | n/a | TBD | TBD | TBD |

Prototype tips (scratch, unmerged): `proto-s3b-p1` `c9c8f537`, `p2` `398d197b`, `p3` `281a1719`, `p4` `ccf9f745`, `p5` `6b0cb23b`, `p6` `3476f129`, `p7` `7473023d`, `p8` `43e86c5d`. After T8 the slice tree should equal `proto-s3b-p8` outside `papers/` and the T9 docs:
`/usr/bin/git -C <wt> diff --stat proto-s3b-p8 -- leanncd/LeanNCD leanncd/test leanncd/lakefile.toml` must be empty before T9 (TBD: result).

## 2. Old -> new expectations (every migrated or flipped expectation; observed, from p1..p8 (a)/(b))

| Task | File | Fixture | Old | New | Reason |
|---|---|---|---|---|---|
| T1 | `test/Eval/Portfolio/TropicalTest.lean` | TR3 (`maxreduce` P*P best path) | `[0.72,0,0,0.72]` | `[1.7,0.9,0.8,1.7]` | tropical ⊗ is `+` |
| T1 | same | TR7 (`minreduce` A*B) | `[4,2]` | `[5,3]` | ⊗ is `+` |
| T1 | same | TR5 min-plus shortest path | documented gap (inexpressible) | `[0,1,3, 5,0,2, 3,4,0]` (new value test) | after the flip `minreduce(D[i,j] * D[j,k])` IS min-plus, same surface |
| T1 | `test/Eval/Portfolio/RecurrenceTest.lean` | RC5 | `[2,6,18]` | `[2,5,8]` | `M_{l+1} = M_l + 3` |
| T1 | same | RC7 | `[2,4,8]` | `[2,4,6]` | `M_{l+1} = M_l + 2` |
| T1 | same | RC10 | `[2,0,5,6]` | `[2,0,5,5]` (interim, T1) | `G[1,1] = max(2+1, 2+3)`; unwritten cell `G[0,1]` still 0 until T6 |
| T1 | `test/Eval/Plan/KernelDenseTest.lean` | `maxContractPlan` (A*B, B=[1,2,3]) | `[30,300,3000,30000]` | `[13,103,1003,10003]` | A + 3 |
| T1 | same | `minContractPlan` | `[10,100,1000,10000]` | `[11,101,1001,10001]` | A + 1 |
| T1 | same | `maxContractPlan`, B=[-1,-2,-3] | `[-10,-100,-1000,-10000]` | `[9,99,999,9999]` | A - 1 |
| T1 | `test/Eval/Plan/KernelDense32Test.lean` | fixtures 7, 8 (f32 bits) | `3240099840..` / `1092616192..` | `1095761920,1120796672,1148895232,1176259584` (13..) / `1093664768,1120534528,1148862464,1176257536` (11..) | A + 3 / A + 1 |
| T1 | `test/Eval/Portfolio/GnnScatterTest.lean` | GN4 (`maxreduce(edge * X)`) | `[3,4,3,4]` | OBSERVED `[4,5,4,5]` (RED T1-T4, expectation left unchanged) | the bool cast is T5 |
| T2 | `test/Eval/Plan/KernelDenseTest.lean` | `oobMaxPlan` (A=[[-1,-2],[-3,-4]], j in 0..2) | `[0,0]` | `[-1,-3]` | bare OOB pad is -inf, max over valid cells |
| T2 | `test/Eval/Plan/KernelDense32Test.lean` | fixture 9 (f32 OOB) | bits `[0,0]` | bits `[3212836864, 3225419776]` = `[-1,-3]` | same |
| T2 | `test/Eval/GatherTest.lean` | the 4 existing `gather` calls | `gather env ...` | `gather 0.0 1.0 env ...` | new signature, values unchanged |
| T3 | `test/Eval/ScanTest.lean` | shape 1 max (`Out[2*i] := maxreduce(X[i])`, X=[-1,-2,-3]) | `scatterFillNotIdentity "Out" .max` (rejection) | `[-1,-inf,-2,-inf,-3,-inf]` | top-level tropical scatter accepted, 0_K fill |
| T3 | same | shape 1 min twin (X=[1,2,3]) | `scatterFillNotIdentity "Out" .min` | `[1,+inf,2,+inf,3,+inf]` | same |
| T3 | same | shape 1 joined (A+B, `.max`) | `scatterFillNotIdentity` | `[10,5,2]` (min twin on negated data `[-10,-5,-2]`) | same |
| T3 | `test/Eval/Plan/CompileTest.lean` | f32 `Out[2*i]` `.max` / `.min` | `scatterOptsNotAdmitted "Y: fill"` (rejection) | accepted: scatter step algebra == `admittedAlgebraF32Max` / `Min`, `destShape #[6]` | guard deleted |
| T3 | `test/Eval/ScatterTest.lean` | 4g regression (`.max`, `[10,5,2]`) | `[10,5,2]` | unchanged value; comment fixed, min twin `[-10,-5,-2]` added | stale comment ("hardcodes real sum") |
| T3 | `test/Eval/Plan/ScatterDenseTest.lean`, `ScatterDense32Test.lean` | raw tropical plans (`maxScatter`, 1.5) | values | UNCHANGED (checked worker was already algebra-generic); `ScatterDenseTest`: a comment claiming the divergence was "adjudicated, permanent, deliberate" rewritten; `ScatterDense32Test`: fixture 1.6c (max AND min collision, bits) added | |
| T3 | `test/Eval/Plan/ScatterCheckTest.lean` | raw tropical plan (`maxScatter`) | value | UNTOUCHED: no patch edits this file (an earlier draft of this record said a comment was rewritten in T3; plan review F9). Its stale "max-product" wording is fixed in T9 (comments-only commit) | |
| T3 | `test/Eval/Plan/DifferentialTest.lean` | classifier arm for `scatterOptsNotAdmitted` | reachable | comment only (arm must stay while the constructor exists); arm removed in T7 | exhaustive match |
| T5 | `test/Eval/Portfolio/GnnScatterTest.lean` | GN4 | red (`[4,5,4,5]`) | green with the ORIGINAL expectation `[[3,4],[3,4]]` | bool -> max-plus cast (audit claim that the value is preserved holds exactly) |
| T6 | `test/Eval/Portfolio/RecurrenceTest.lean` | RC10 | `[2,0,5,5]` | `[2,-inf,5,5]` (new twin `RC10m` `[-2,+inf,-5,-5]`) | state is max-plus; unwritten cell `G[0,1]` is 0_K |
| T7 | `test/Semantics/SourceSortedDifferentialTest.lean` | `carrierOf (scatter max)` | `refused ..scatterPolicy` | `"maxPlus"` | oracle admits tropical scatter |
| T7 | same | `yCore (strided .max/.min)` | 7 cells | 8 cells (trailing `-inf`/`+inf`) | snapshot declares `k` extent 8 (production's derived extent; fixes `BindingIssue.shape [7] vs [8]`) |
| T7 | same | `classOf (product .max/.min)` | `knownContractDifference (tropicalMultiFactor ..)` | `fourLegParity` | production now agrees with the oracle |
| T7 | same | `classOf (strided .max)` | `knownContractDifference (tropicalScatterFill ..)` | `fourLegParity` | same |
| T7 | same | `(strided .min)`; `[bareY,multiV]`, `[multiY,bareV]`, `[multiY,multiV]`; strided pairs | `scatterFill (some n)` / `multiFactor (some d)` | `"parity"` (helper `tagOf`) | same |
| T7 | same | `[bareY, zeroV]` | `nativeDiscrepancy at 7, bits 4607182418800017408` (1.0 vs 0) | `"parity"` | production empty product is now 0 |
| T7 | same | `[multiY, bareV]`, `[multiV, multiY]`, `[multiY, zeroV]` | `multiFactor (some 6)` / `startsWith "nativeDiscrepancy"` | `"parity"` | same |
| T7 | same | `fills`, `multi` confirmer guards, same-first-mismatch guard, `unexplained` guards | accepting/negative guards | REMOVED (dead conditions; their programs kept as parity rows) | `confirmsSorted`/`unexplainedAgree` no longer exist |
| T7 | same | NEW parity rows | n/a | `collide max/min` `[-3,-inf,7,-inf,17,-inf,27,-inf]` / `[-5,+inf,5,+inf,15,+inf,25,+inf]`; `contract` `[97,107,117,127]` / `[-4,6,16,26]`; `zeroY` `[0,0,0,0]`; `product [-1..-4]` `[99,98,97,96]` / `[0,-1,-2,-3]` | max-times would give other values |
| T7 | `test/Semantics/SourceAdmissionAffineTest.lean` | scatter max refusal (two sites) | `.unsupported .scatterPolicy` refusal | admission view `scaleView` / `bareView` | refusal gone |
| T7 | `test/Semantics/SourceSortedAuditTest.lean` | row 7 (admission precedes selection) | `scatterPolicy` | `writeOutOfRange` (its program writes `Y[2a]` over `a`), plus a new in-range twin over `k` refused `sortSelection (mixedSorts ..)` | |
| T7 | same | row 9 | refusal | `selected (bareScatter .max/.min) == "maxPlus"/"minPlus"` | |
| T8 | `test/Eval/PropertyOracle/ScanUnroll.lean` | independent unrolling zero leaf / base merge | real 0 on an unwritten tropical cell (legacy `[2,-inf,5,5]` vs unrolling `[2,0,5,5]`) | state's own `0_K` (`localStateAgg`) | TEST-SIDE oracle bug, production was right |
| none | `test/DSL/MaxReduceTest.lean` evaluation blocks | | | UNCHANGED (they pass their own `mul` to `evalAssignWith`; audit §8f.1 / decision note A10 correction) | |
| none | `LoweringTest` AGG1/AGG2, `RouteFragmentCorpusTest` `aggregate`, `Adapter32Test`, `DifferentialTest` single-factor rows, `ScanGen` template 5 | | | UNCHANGED, green | route semantics-free; single factor |

Not flipped although the audit predicted it (audit §8c): `CompileTest` pointwise `.relu`+`.max`, `StructuralTest`, `SourceRawCorrespondenceTest` (p4 (b): none of the three flipped; reason UNVERIFIED, see §5).

## 3. The author's calls (not user decisions; mark and correct)

| # | Call | Why / where decided |
|---|---|---|
| 1 | "S3b" = the semiring flip for single-writer programs; tropical multi-writer collection and A4 agreement are S3b-ii, planned after | design §6; `multiWriterAlgebra` stays the refusal |
| 2 | One plan per slice | Rule 13 |
| 3 | `approxEq` fixed in PRODUCTION source (`Eval/Tensor.lean`), not a test helper | p2 (e)1; needed for RC10's -inf cell |
| 4 | tropicalNonlin and scan-state agreement rejections in scope; route untouched | design §6 and §3 |
| 5 | Audit §8c "become rejections" not trusted until observed | design §6 (wrong for 2 of 5; p4 observed none flipped) |
| 6 | `scatterFillNotIdentity`, `scatterOptsNotAdmitted` deleted with their consumers (T7); conflicts with the `Eval/Plan/AGENTS.md` pitfall, resolved by scoping it (T9) | p7 (a)7 |
| 7 | Prototype-first authoring in EIGHT dispatches (design §6 said five), patches per task | ledger |
| 8 | Type named `SortAlgebra` (`Algebra` is a class; fails only at the `LeanNCD` aggregate) | p4 (a)1 |
| 9 | No `algebras` map in either backend; casts use local facts (`isPredicateDest`, slot signature dtype, `agg != .sum`); cast field `ReadPlan.boolToTropical` (not `ReadPlan.cast`) | design §9; p5 (a)1 |
| 10 | The cast check skips a destination with no map entry (multi-writer name) | p4 (a)2 |
| 11 | Neutral writers decided by SHAPE only; a neutral statement's annotation is ignored; an all-neutral annotated scan state evaluates REAL (parked, pinned) | p4 (a)3, p6, p8 (e) |
| 12 | Scan state sort and neutral writers use ONE mechanism: `scanStateStmts` rewrites each neutral statement's `agg`; applies to every neutral statement of the scan, scratch included (consistent with `algebraOf`; unpinned) | p6 (a)2-3 |
| 13 | Raw plans carry a sort (`StateInit`), not a constant; default `.zero` keeps every raw literal compiling | p6 (a)4 |
| 14 | Truth convention "stored != 0"; `ScalarKernelOps.one` deleted, `zero` kept; the store-slot-missing branch of `gatherFactorWith` pads like OOB (unreachable) | p5, p2 (e)2-3 |
| 15 | `Combine.bool` uses the NaN-propagating `minNaN`/`maxNaN` (differs from `min`/`max` only on non-binary NaN) | design §2.2; p3 (f)1 |
| 16 | T7-01 carries deletion-forced test edits (3 files) so the task builds; `SourceSortedDifferentialTest` is T7-02 | p7 (a)1 |
| 17 | Extent fix = declare `k` extent 8 in the sorted snapshots (not a classification arm) | p6 (f), p7 (a)6 |
| 18 | `SortedClassification.knownContractDifference` deleted (no producer); the REAL harness keeps its own | p7 (a)5 |
| 19 | Duality property tropicalises `enumPrograms` (the sweep has no max aggregation); grid cases kept OUT of `enumScanCases` (length pinned in five places) | p8 (a)3, (d) |
| 20 | `T4-M7` (check order swap) is an equivalent mutant; replaced by `T4-M7b`; `T5-M5b` equivalent; `T4-M4` not stateable for both tips | p4 (a)4, p5 (a)2, manifest_report (a) |
| 21 | Manifest pruned from 53 observed cycles to 48 entries (dropped: T1-M7, T4-M4b, T6-M5, T7-M4, T7-M6, plus unrun twins) | manifest_report (b)/(c) |
| 22 | Per-task full `Tests` build (the prototypes' known-red sets and job counts are full-target measurements); filtered manifest per task | plan §1 |

## 4. Verification (fill)

| Check | Result | Source |
|---|---|---|
| Authoring: in-order replay of 16 patches onto the slice tip equals `proto-s3b-p8` | done by the authoring dispatch (design §9); `T1-01` `apply --check --index` re-verified on the plan tip | design §9; plan dispatch |
| Authoring: full `Tests` at `proto-s3b-p8` | green, 8825 jobs, zero red | p8 (f) |
| Base: full `Tests` on main `8cf5052a` | 8823 jobs green | `additive_b6_record.md` |
| Execution: full `Tests` on the slice tip (controller) | TBD jobs (expect 8825), TBD red | controller |
| `Semantics.AxiomAudit` | TBD (standard axioms only; constant count TBD) | controller |
| Sweep counts unchanged (DifferentialTest 3832/3832/0, scan corpus 17/17) | TBD | controller |
| DualityTest pins (3832 / 17 (13 checked, 4 skipped) / 2 / 2) | TBD | controller |
| Deleted-name grep over `leanncd/LeanNCD` `*.lean` empty (plan T7 checklist) | TBD | controller |
| `git diff --stat main -- leanncd/test` lists no weakened test | TBD | final review (b) |

**Mutation manifest, authoring-time observation (manifest_report; `additive_s3b_mutations_post.json`, 48 entries; `--check` OK, every `old` unique at each task's tip and at the final tip).**
Run 1: 53 cycles (106 builds) on tip `43e86c5d`, empty `expect`: 53/53 PASS (every mutation broke the build, every file restored byte-identical, every restored rebuild green); about 2.5-3 hours. Five of those 53 cycles are not manifest entries
(T1-M7, T4-M4b, T6-M5, T7-M4, T7-M6: duplicates of kept entries). Run 2: five entries re-run with `expect` enforced (T3-M3 new text, T4-M3c, T6-M8, T7-M1, T8-M1): 5/5 PASS, about 15 minutes. The other 43 entries' `expect` strings were verified by string match against run-1
output (`verify_expect.py`, 0 missing) and for existence at each task tip (`tipexpect.py`), NOT by an enforced run: the per-task `--task` run is their first enforced run. Surviving mutants: none. Equivalent mutants: T4-M7, T5-M5b (not run). Bad text found and fixed: T3-M3 (first version replaced the combine for every `agg` and was killed by sum rows, not the NaN fixtures).
Per-task entries: T1 6, T2 6, T3 6, T4 7, T5 9, T6 7, T7 2, T8 5.

Execution (controller fills after each task's commit). Rules (plan §1): the run happens with an otherwise idle worktree; after the run `git status --short` must be EMPTY before the next task starts (record "status empty: yes/no"); every cycle NOT run is listed
in the `Skipped` column BY LABEL with the reason (a deferral per the plan's deferral order, or other), never omitted (Rule 12); "Skipped: none" is written explicitly when nothing was skipped.

| Task | `--task` entries | Run | PASS | Skipped (labels, reason) | Failing `expect` / finding | Status empty after | Wall time |
|---|---|---|---|---|---|---|---|
| T1 | 6 | TBD | TBD | TBD | TBD | TBD | TBD |
| T2 | 6 | TBD | TBD | TBD | TBD | TBD | TBD |
| T3 | 6 | TBD | TBD | TBD | TBD | TBD | TBD |
| T4 | 7 | TBD | TBD | TBD | TBD | TBD | TBD |
| T5 | 9 | TBD | TBD | TBD | TBD | TBD | TBD |
| T6 | 7 | TBD | TBD | TBD | TBD | TBD | TBD |
| T7 | 2 | TBD | TBD | TBD | TBD | TBD | TBD |
| T8 | 5 | TBD | TBD | TBD | TBD | TBD | TBD |

Known-red line sets (plan §1 step 3): per task the SSDT failing-line set observed is recorded here and compared with the findings' sets, TBD (T1-T2: 11 lines; T3-T6: 19 lines).

## 5. Findings and disposition

Authoring-time findings (already resolved or parked):

| # | Finding | Disposition |
|---|---|---|
| A1 | `Algebra` name clash (a class in `LeanNCD/Algebra/Algebra.lean`); fails only at the aggregate build | RESOLVED: `SortAlgebra` |
| A2 | `ScanUnroll` (test oracle) gave the real 0 for an unwritten tropical cell (audit §8f.4) | RESOLVED test-side in T8-01; production was right |
| A3 | Audit §8c list of "become rejections" not borne out (LoweringTest, RouteFragmentCorpusTest by design; CompileTest/StructuralTest/SourceRawCorrespondenceTest: p4 saw none flip, reason UNVERIFIED) | recorded; no action |
| A4 | The KernelDenseTest all-negative-B row no longer separates the -inf seed | RESOLVED: `storeNegA_NegB` added (f64 and f32) |
| A5 | Under the OLD Iverson constants a false tropical Iverson was invisible | RESOLVED: coordinate-dependent masks in the fixtures |
| A6 | T3-M3 first text killed by sum rows, not the NaN fixtures | RESOLVED in the manifest |
| A7 | `Eval/Plan/AGENTS.md` pitfall "Don't delete producer-less constructors" conflicts with T7 | RESOLVED in T9 (scope the pitfall) |
| A8 | 78 of 3832 sweep programs have a max result equal to the real result; reason not investigated | parked (curiosity, no correctness claim rests on it) |
| A9 | Single-factor tropical statements normalise `-0.0` to `+0.0` | accepted |
| A10 | An interim `completed` notice arrived while P7's final build ran | process lesson (plan §1) |
| A11 | Silently-ignored cells not pinned: C23 (bool state read), neutral scratch, contracted-axis neutral condition, the cast under a contracted axis; C21 (multi-writer source read by a bool statement) is NOT in this list any more: it is unreachable for plain writer sets (collection refuses every multi-writer set with a tropical writer: `multiWriterScatter`/`multiWriterAlgebra`/`multiWriterScan`), only the order of refusals is unpinned (plan review F6) | parked (plan §2/§3) |
| A12 | p8 (c) said `ScatterDense32Test` has no tropical fixture and parked it; `git grep` at `proto-s3b-p8` shows a max row and fixture 1.6c (max and min) | recorded: the parking was dropped from the plan |
| A13 | Plan review (Opus, 2026-10-23, `additive_s3b_review_plan.md`): 13 findings, no Critical; the plan's rejection table wrongly said `compileToScheduled` accepts `tropicalNonlin` (it runs `checkDtypes` and rejects); T9 omitted `DSL/AGENTS.md` and the stale Lean docstrings; mutation cycles needed serialization and a schedule | FIXED in plan §1, §3(iii), T9, and this record (commit "S3b plan: review fixes") |

Execution findings (fill; one row each, with the fix commit or the parking reason):

| # | Finding | Source (task, review, cycle) | Disposition |
|---|---|---|---|
| E1 | TBD | | |

## 6. Parked by scope (copied from the plan §2; update status at close-out)

| Item | Owner / disposition |
|---|---|
| Tropical multi-writer collection and writer agreement (A4); `multiWriterAlgebra` stays the only refusal | S3b-ii: its own slice, planned after this lands (Rule 13) |
| Multi-writer scatter B5 | parked; own slice |
| F3: scan-local scatter overwrite on collision | parked |
| `real -> bool` rejection | parked; pinned as accepted (T4-M3d) |
| `OutOfBoundsPolicy.zeroPad` rename | parked; doc only |
| Oracle per-tensor sorts; oracle coverage of casts, Iverson values, padding | later follow-up |
| JAX/Python tropical execution | unowned (`Executable` gate stays) |
| All-neutral tropical-annotated scan state evaluates REAL | design-note decision; pinned by `parkedAllNeutralScanState`; T8-M5 flips it |
| Annotated neutral scratch statement evaluated in the state's sort, no fixture | parked; ~1 Direct fixture |
| Contracted-axis condition of the neutral-writer definition has no dedicated fixture | parked; ~1 Direct fixture |
| Bool STATE read by a tropical scan step is cast, no fixture | parked; ~1 Direct fixture |
| Multi-writer SOURCE name read by a bool statement (cast check sees the declaration): unreachable for plain writer sets, collection refuses first; only the order of refusals is unpinned | parked; fold into S3b-ii |
| `T5-M8`/`T5-M10` (scan-step and plain caller cycles of `residualizeAssignment`'s cast flag) pruned, never run: the step-caller flag has no killing observation | parked; ~1 Direct item (one cycle) |
| Cast under a contracted axis has no fixture of its own | parked; ~1 Direct fixture |
| Grid scan cases not in `DifferentialTest`'s three-way leg | parked; one list entry |
| Stale S2a/S2b manifests | not edited; records |

## 7. Cost and process notes

- Authoring cost (measured with `token-report.py` on the authoring session, 2026-10-23): **159.3M cumulative input tokens against the ~50M target, a 3.2x overrun** (S1 82M, S2a 110M, S2b about 2x were the earlier overruns).
  Controller 21.2M (96 turns, peak 336k). Dispatches 138.1M: audit 12.7M (75 turns, peak 280k); builder check 0.6M; P1 12.2M (79 turns); P2 15.0M (86 turns, peak 259k); P3 8.0M (58); P4 6.9M (53);
  P5 8.0M (53); P6 12.2M (72 turns, peak 246k); P7 9.1M (69); P8 9.9M (73); manifest dispatch 8.0M (64 turns); plan write-up 7.5M (43 turns, peak 281k); Opus plan review 18.6M (103 turns); review-fix dispatch 9.4M (50 turns, peak 252k).
  Rule 6 breaches (dispatch cap: peak <= ~250k and <= ~60 turns): audit, P1, P2, P6, P7, P8, the manifest dispatch, the plan write-up (peak), the review (103 turns) and the fix dispatch (peak). Causes: hand mutation cycles in P1 and P2 (the manifest dispatch later reran them), Edit-hook echoes,
  harness refusals, whole-log reads, and a review given three lenses in one dispatch. What would have cut it: prototyping T1+T2 without hand mutations from the start (P3 onward did, and stayed near 53-69 turns), and one reviewer lens per dispatch.
  Execution budget is a separate line (Rule 6: <= ~175M) and is not yet spent.
- Prototype tool-use counts (harness counts from the ledger; reported-by-agent counts in parentheses): P1 101 (75), P2 149 (90), P3 104 (68), P4 96 (55), P5 106 (52), P6 127 (62), P7 99 (60), P8 126 (75). Every prototype exceeded the ~60-call cap by the harness count; the cost drivers were hand mutations (P1, P2), harness refusals and builds.
- Authoring-time process findings: interim `completed` notices arrive while a build still runs (check `ps` and `git log`); the full manifest is hours (measured: about 3 minutes per cycle averaged over 53 cycles, plan-root mutations included; expected serial total about 6-7 hours, plan §1): run `--task` filtered, serialized with every other use of the worktree; never Read a build log (use `rg`).
- Execution cost (controller fills): TBD total input tokens (target <= ~175M, Rule 6), per-task turns and context peaks in §1, review cost, fix dispatch cost.

## 8. Merge

TBD: merge hash, date, `git diff --stat main worktree-additive-s3b-tropical-flip` empty before removal, `main` ahead of `origin/main` (not pushed), worktree and branch removed, scratch `proto-s3b-p1..p8` deleted only with the user's OK noted here (TBD: date and who), post-merge docs commit hash with the merge hash filled in the decision note and path doc.

## 9. Execution results (controller, 2026-10-24)

Executed by one scripted driver (apply `--check` then `--index` per patch, full `Tests` build, exact comparison of red targets, job count and the SSDT failing-line set with the plan's table, one commit, filtered `--task` mutation run, clean-tree check). It stopped on deviation; the only stops were two bugs in the driver's own comparison (GN4 line count, empty red set), not deviations in the results.

| Task | Commit | `Tests` jobs | Red targets | SSDT lines | Cycles |
|---|---|---|---|---|---|
| T1 | 66e65eb9 | 8823 | GN4 site + SSDT | = plan (11) | 6/6 |
| T2 | 5da4acc1 | 8823 | same | = plan (11) | 6/6 |
| T3 | b147da55 | 8823 | same | = plan (19) | 6/6 |
| T4 | 403a55e7 | 8823 | same | = plan (19) | 7/7 |
| T5 | d245fb2e | 8824 | SSDT only | = plan (19) | 9/9 |
| T6 | fc0ad016 | 8824 | SSDT only | = plan (19) | 7/7 |
| T7 | 2ddebea3 | 8824 | none | n/a | 2/2 |
| T8 | d520883a | 8825 | none | n/a | 5/5 |
| T9 (A) comments-only Lean | 6c8de978 | 8825 | none | n/a | none |
| T9 (B) docs | be4d888d | n/a | n/a | n/a | none |
| review fix F1/M1 | 38c468f5 | 8825 | none | n/a | T4-M7b, T6-M7, T6-M8, T8-M5, T9-M1: 5/5 PASS |

All 48 manifest entries plus the new `T9-M1` passed with their `expect` strings enforced (no stale string, no surviving mutant). Final full `Tests`: Build completed successfully (8825 jobs), no `sorryAx`, every `depends on axioms` line a subset of propext / Classical.choice / Quot.sound (641 lines). `JaxExperiment`: 8515 jobs, green. The deviations from the plan: per-task mid-tier reviews were NOT run (the two final Opus reviews covered the whole diff); the `T9 (A)` build was the final build (as planned); the fix commit 38c468f5 re-ran the full `Tests` (8825, green) and only the five entries whose file it touched.

### Final reviews (Opus, read-only; files `additive_s3b_review_final_semantics.md`, `additive_s3b_review_final_rejections.md`)
0 Critical. Major: **M1 = F1** (one defect found by both lenses): `Stmt.isSortNeutral` ignored `rhs.nonlin`, so a scan base such as `relu(P[j])` was rewritten to the state's tropical sort after `tropicalNonlin` had passed. FIXED in 38c468f5 (a statement with a nonlinearity is never neutral; 5 fixtures, mutation `T9-M1`). **F2** (decision, NOT changed: plan decision 6 stands): the max-plus <-> min-plus and tropical -> bool cast rejections are bypassed by one real copy (`R[i] := M[i]` between them is accepted, bit-identical result), and minimax `Z := minreduce(maxreduce ...)` that was accepted before S3b is now refused; decision note A7 is PROPOSED. DECIDED 2026-10-24 by the user: option A, keep and document (decision note A7); revisit B (identity) or C (sorts tracked through copies) when S3b-ii plans writer agreement.
Minor, PARKED (own scope, ~1 Direct item each): bool -> tropical cast reads a stored NaN as true (the NaN disappears); under a unary function an OOB read contributes `f(0)` and can win a tropical reduction (plan rule, but same shape as the bare-read bug T2 fixed); raw scan checker does not tie a state's `initValue` to its step algebra (compiled plans are consistent); neutrality treats `Out[i+j] := maxreduce(X[i,j])` as non-combining though its writes collide (live only with S3b-ii or F3); the property-oracle unroller's `localNeutral` copies production's neutrality rule (so a neutrality bug is invisible to the duality property: this is how M1 slipped through; the duality property also skips the relu scan template). Doc nits fixed in 38c468f5 (`algebraOf` is read only by validation and tests; backend_missing_functionality refusal list).

### Cost
Execution total 27.1M cumulative input tokens (`token-report.py`): controller 8.7M, docs dispatch 4.7M, two reviews 11.2M, fix dispatch 2.5M; target <= ~175M (Rule 6). Rule 6 per-dispatch breaches: the false-rejections review peaked at 214k context (within 250k) with 48 turns; no dispatch exceeded 60 turns. Authoring was 159.3M (section 7).
