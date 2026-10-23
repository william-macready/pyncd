# P7 findings (T7: production agrees with the S2b oracle on tropical programs; the known-difference apparatus is gone)

Branch `proto-s3b-p7` (from proto-s3b-p6 3476f129). Commits: `250c3445` T7-01 production (11 files, +33/-157), `7473023d` T7-02 tests (1 file, +109/-125).
Patches (apply --check -R verified at the tip): `T7-01-production.patch` (3476f129..250c3445), `T7-02-tests.patch` (250c3445..7473023d).
Mutations: `p7_mutations.json` (6 entries, `--check` OK, expect strings empty, none run).

## (a) Corrections to audit / design (read first)
1. **T7-01 contains test edits (deletion-forced).** Deleting `scatterPolicy` and `scatterOptsNotAdmitted` breaks compilation of three test files that are not
   the 19-site file: `SourceAdmissionAffineTest` (L127, L221: refusal -> `view == scaleView` / `bareView`; `isPolicy` deleted; (d)/(h) prose updated),
   `SourceSortedAuditTest` (rows 7 and 9), `DifferentialTest` L115 (classifier arm). These are in T7-01 so it builds; `SourceSortedDifferentialTest` is in T7-02
   (it was already red at the base and references deleted names, so at T7-01 alone it fails to compile instead of failing assertions).
2. **Audit row 7 (`SourceSortedAuditTest`) did not become a `mixedSorts` refusal.** Its program writes `Y[2a]` into `Y` over `a` (extent 4), so with the policy refusal gone
   the statement's own cause is `writeOutOfRange` (observed), still "admission precedes selection". Kept as that, plus a new in-range twin over `k` that IS refused
   `sortSelection (mixedSorts ..)`. Row 9 flipped to `selected (bareScatter .max/.min) == "maxPlus"/"minPlus"`.
3. **One arm for `.assign` and `.scatter`** in `admitAffineStatement` (`| .assign name slots rhs | .scatter name slots rhs =>`): the sorted flag erases the agg for both.
   Unsorted behaviour unchanged (a non-sum scatter still refuses `nonSum` at `admitStatement`/`admitAffineWrite`; pinned by the existing unsorted rows).
4. **Oracle/Core legs needed no change** for a non-sum carrier: `termFiber`/`contribution` are `Semiring K`-generic (`total : K := 0` = carrier zero), the sorted
   rows below reach `fourLegParity` with published agreement.
5. **`SortedClassification.knownContractDifference` deleted** (trivial: no producer once `confirmed` went; only the 19-site test named it). The REAL harness keeps
   `Differential.Classification.knownContractDifference` and `multiWriterScatter`/`scatterExtentOverridesDeclared`/`usedDType` (untouched except the deleted `tropical*` arm in `confirms`).
6. **Extent fix = declare 8** (p6 (f) option 1): `snap`/`snap2` `extent` uid 9 -> 8 and `.axis k (some 8)`. No classification arm added. The `yCore (strided ..)` rows gain a trailing `±inf`.
7. **Rule conflict (flag for T9):** `Eval/Plan/AGENTS.md` Pitfalls says "Don't delete producer-less constructors ... retained on purpose". The brief (and both constructors' own
   docstrings, "deleted with ... (T7)") ordered deleting `scatterFillNotIdentity`/`scatterOptsNotAdmitted`; I followed the brief. T9 should scope that pitfall to the
   named constructors (`dtypeMismatch`, `unaryNotAdmittedForStorage`, ...).
8. Historical comments still naming the deleted constructors (left, they are history, not claims): `test/Eval/ScanTest.lean:1069`, `test/Eval/Plan/DifferentialTest.lean:2083`,
   `test/Eval/Plan/CompileTest.lean:1289`, and the new T7 prose in `SourceSortedDifferentialTest` (L79, L161). No Lean source outside tests names them.
9. Prediction check: every new/flipped `SourceSortedDifferentialTest` value passed on the first build (all predicted by hand); only audit row 7 needed an observation probe.

## (b) Sites old -> new (SourceSortedDifferentialTest; line numbers of the BASE file)
- 79/80 `carrierOf (scatter max)`: `refused ..scatterPolicy` -> `"maxPlus"`.
- 89/91 `yCore (strided .max/.min)`: 7 cells -> 8 cells (trailing `-inf`/`+inf`, the empty fiber at 7).
- 104/106 `classOf (product .max/.min)`: `knownContractDifference (tropicalMultiFactor ..)` -> `fourLegParity`.
- 108 `classOf (strided .max)`: `knownContractDifference (tropicalScatterFill ..)` -> `fourLegParity`.
- 188 `(strided .min)`; 191/193/196 `[bareY,multiV]`,`[multiY,bareV]`,`[multiY,multiV]`; 201/204/206/209 strided pairs: `scatterFill`/`multiFactor (some d)` -> `"parity"` (helper `tagOf`; `known` deleted). 198 `[bareY,bareV]` stays parity.
- 262 `[bareY, zeroV]`: `nativeDiscrepancy at 7, bits 4607182418800017408` -> `"parity"`; 264/269 -> `"parity"`; 266 `[multiY, zeroV]` `startsWith "nativeDiscrepancy"` -> `"parity"`.
- REMOVED (dead conditions, their programs kept as parity rows above): 211-232 `fills` confirmer (`nativeOf`, `originOf`, `nY`/`nV`, 6 guards); 234-244 `multi` confirmer (3 guards);
  271-277 same-first-mismatch guard; 279-294 `unexplained` (3 guards). Reason: `confirmsSorted`/`unexplainedAgree` no longer exist; with no masking, any divergence is a real
  `nativeDiscrepancy`/`nativeFailure` (the intent of 266/272/292-294 is now structural: nothing can hide a mismatch).
- Doc fixes: header `k (8)`, `±inf` pin comment (strided rows now compare infinite cells with production), extent-0 comment.
Other files: SourceAdmissionAffineTest L127/L221 refusal -> admission view; SourceSortedAuditTest rows 7/9 (see (a)2).

## (c) Red targets / full `Tests`
Full `Tests` at the T7 tip (7473023d): **green, 8824 jobs, ZERO red targets** (first fully green tip since T1). Library `LeanNCD` green before tests.
Sweep counts unchanged: DifferentialTest sweep total=3832 accepted=3832 rejected=0; scan corpus 17/17. `SourceOracleCarrierTest`, `SourceSortedAuditTest`,
`SourceDifferentialCorpusTest`, `ScanUnroll`, `ScanGen`, enumPrograms sweeps all built green (their assertions are `#guard`/`#guard_msgs`, so green = unchanged values).

## (d) Fixtures (donors), all in `SourceSortedDifferentialTest` section "S3b T7 parity rows", each `yCore` value + `classOf == fourLegParity`
- (a) `collide max/min`: `.scatter "Y" [2a] := agg Z[a,b]` over `k` (8): `[-3,-inf,7,-inf,17,-inf,27,-inf]` / `[-5,+inf,5,+inf,15,+inf,25,+inf]` (b-collisions into cell 2a, unwritten odd cells). Donor: ScatterCompileTest S11, old `tropicalScatterFill` rows. Fails against old fill 0.
- (b) `contract max/min`: `Y[a] := agg Z[a,b] W[b]`: `[97,107,117,127]` / `[-4,6,16,26]` (max-times would be `-5,50,1500,2500`). Donor: `product` rows, TR3/TR7 shape.
- (c) `zeroY max/min`: `Y[a] := agg ()`: `[0,0,0,0]` both. Donor: `zeroV`.
- (d) `product max/min [-1,-2,-3,-4]`: `[99,98,97,96]` / `[0,-1,-2,-3]` (max-times `-1..-4`, min-times `-100..-400`). Donor: `product` row with `xValues`.

## (e) Budget
About 60 tool calls; context peak roughly 110-130k. No hand mutation runs.

## (f) For the T8 author
- `Eval.PropertyOracle.ScanUnroll` and `ScanGen` rebuilt green, unchanged, in the targeted build after T7-01 (T7 touches no scan code).
- Tropical fixture counts per test file (`rg -c "maxreduce|minreduce|AggOp.max|AggOp.min" leanncd/test`): BoolCastTest 24, TropicalTest 18, RecurrenceTest 12, ScatterCompileTest 11,
  DifferentialTest 7, ConvPoolTest 6, MaxReduceTest 5, CollectTest 5, Adapter32Test 4, SourceSortedDifferentialTest 2 (helpers are agg-parametric; every T7 row has a min twin),
  CollectEvalTest/CompileTest/ScatterTest/ScanTest/LoweringTest 2 each, and 1 each in SourceAdmissionAcceptanceTest, ClassicalMLTest, ScatterDenseTest, EvalExamplesTest,
  GnnScatterTest, RouteFragmentCorpusTest, ScanGen, KnownGapTest, RouteFragmentDiagnosticTest, RejectTest, StructuralTest.
  Single-count files (ConvPool max-pool, GnnScatter, ScanGen, ScatterDense, EvalExamples, ClassicalML) are the likely duality-twin gaps; not audited max-vs-min individually here (budget).
- Tropical scan shapes: RC10 has RC10m (T6); BoolCastTest a1/a2, c1/c2, d1/d2 are twinned. ScanGen's tropical generator (1 hit) is the place to check for a min-plus scan shape.

## (g) Markdown/doc files still stating the old divergence (for T9)
`rg -ln "tropicalMultiFactor|tropicalScatterFill|Production multiplies|scatterPolicy|scatterFillNotIdentity|max-times|max-product|min-product" WT --glob '*.md'`:
leanncd/LeanNCD/Semantics/AGENTS.md, leanncd/docs/test_portfolio.md, papers/f32d_evalplan.md, papers/einsum_tensor_logic.md, papers/backend_missing_functionality.md,
papers/max_min_aggregation.md, papers/scatter_affine_lhs_writes.md, papers/f32d_record.md, papers/copilot_code_analysis.md, papers/semantics/{additive_s2a_review_T4AB,
additive_s3a_record, additive_b6_record, additive_s3b_design, additive_s2b_plan, additive_s2b_review_final_soundness, additive_s2b_ledger, additive_s2a_artifacts/p2a_findings,
lean_executable_semantics_path_part_4, additive_s2a_plan, additive_s2a_ledger, additive_s2a_record, oracle_extension_s2_design, additive_s2a_review_T2, additive_s2b_review_T4B,
additive_s2b_artifacts/p2_findings, additive_s2b_record, additive_s2b_review_final_regression, additive_s3b_audit, additive_s2b_review_T2}.md.
Live (non-record) ones T9 must fix: Semantics/AGENTS.md, Eval/Plan/AGENTS.md (pitfall in (a)7), docs/test_portfolio.md, papers/max_min_aggregation.md, papers/backend_missing_functionality.md.
