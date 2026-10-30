# B5c final whole-branch review B — oracle independence

- Base: `806d35abb86e743c0c9c9f9dfe08d9f0c32db5f1`
- Committed snapshot: `d634d84c` on `b5c-exec`.
- Scope: independent whole-branch review, emphasizing source-restated sort
  oracles, retired-condition safety, and the SHAPED fixture/mutation evidence.
- Method: immutable `git show`/`git diff` evidence; no builds, source changes,
  fixture changes, external systems, delegation, or consultation of review A.
- Status: complete — **APPROVE** (static review; controller owns execution gates).

## Evidence log

1. Initial committed diff inventory: 17 files, 298 insertions, 40 deletions.
   Production changes are in collection, scheduled validation, and source
   differential labeling; the remaining changes cover tests and documentation.
2. Read the authority plan §§2,5,6,7, the authoring record
   `additive_b5c_plan_record.md`, and the approved single-writer design. The
   authoring record explicitly corrects affine `.assign` prediction to account
   for lowering, and discloses the three S-cell limitations rather than claiming
   exhaustive coverage.
3. After the controller announced mutation activity, cached source/test evidence
   exclusively from `git show d634d84c:<path>` and the complete pinned branch
   diff in a disposable untracked evidence directory. All source references
   below concern those immutable blobs, not live files.
4. Initial independence check: `OracleSortRules.singleBoxed` (lines 301–317)
   uses declaration syntax, its own coefficient normalization/boundedness rules,
   and raw slot UIDs. It does not call `boxedSingleGroups` or
   `declaredAxisSizes`. `pinnedBox` (287–294) independently recognizes both
   pinned `.axis` and `.iter` declarations. This was the initial checkpoint;
   the completed semantics/observation cross-checks are recorded in entries 5–10.
5. SHAPED observations are not predictor self-comparisons:
   `OracleSortRulesTest.lean:413–436` independently builds sizes/signatures, then
   calls `productionShapedVerdict`; `OracleSortRules.lean:348–365` runs
   `compileToScheduled`, `validateScheduled` (via `productionVerdict`), and real
   `prepareEvalPlan`. The staged list at test lines 469–491 has 17 rows;
   lines 493–502 require agreement for every row and exactly 11 predicted
   accepts (hence six refusals). The four additions cover axis/iter boxes,
   an undersized iter box, and the D5 idiom; these use affine `.assign`
   statements, so they also guard the lowering-sensitive predictor correction.
6. Retired-condition safety: `Differential.lean:293–327` still requires completed
   reference execution, successful oracle/profile/comparisons, and *both*
   native comparisons for parity. With no condition, native failures remain
   `nativeFailure` and observed mismatches remain `nativeDiscrepancy`; deleting
   a condition cannot itself manufacture parity.
7. `fR` is explicitly retained as a real native failure:
   `SourceDifferentialScatterTest.lean:328–336` pins oracle shape `[6]` and
   `[0,0,0,0,0,10]`, both failures on scratch `Y#1` at coordinate 5 outside
   extent 5, and zero conditions. This is the documented M4 derived-scratch
   limitation, not parity and not an allowed difference. `fH9` at lines
   114,142–144,336 requires actual parity with zero conditions; the
   classification path compares full metadata/shape and every output cell
   (`Differential.lean:111–159`), not just an error label.
8. Cross-checked the distinct representations rather than requiring identical
   branches. Production `Collect.lean:142–162` sees scheduled statements;
   predictor `singleBoxed` sees pre-lowering statements. In
   `Structural.lean:1121–1137`, affine/repeated-slot `.assign` becomes
   `.scatter`, so the predictor's bounded-slot rule for both forms is correct.
   Independent coefficient summation in `OracleSortRules.lean:138–153`
   agrees with the admitted geometry, including zero/canceled coefficients;
   D5 deliberately uses raw source UIDs, not only surviving coefficients.
9. `declaredShapeWins` at `Differential.lean:205–213` uses only admitted
   destination/form data. Its lack of explicit predicate/scalar/pinning
   branches is not a hidden expansion: `Source/Adapter.lean:273–287`
   rejects unpinned and iter declarations, and lines 411–421 reject predicates;
   rank-zero writes cannot pass the caller's `nonBareWrite` guard at
   `Differential.lean:223`. Undeclared destinations are refused by
   `Source/Admission.lean:885–887`. Explicit constant forms have empty
   coefficient lists and fail its bounded test; multiple surviving source
   coefficients fail it as well. D5 uses admitted raw form UIDs
   (`Admission.lean:795–803` preserves affine coefficients).
10. Production plumbing preserves the intended boundary:
    `ScheduledValidation.lean:243–260` reconstructs the source environment and
    passes declaration pins to both collection and retained shape obligations.
    `Collect.lean:100–104,174–184,241–291` uses B5 for singleton groups,
    preserves the original writers' geometry, and emits one `T#1` plus collector.
    `Eval/CollectorShape.lean:10–41` still enforces derived-extent fit and
    uses the existing boxed scratch sizing view. `Pipeline/Lowering.lean:594–601`
    and `Bridge/Agreement.lean:30–50` still call the default unpinned desugar:
    route/proof scope is not silently widened.

## Findings

**No defects found.** No blocking, medium-priority, or nonblocking correctness
findings, and no proposed code/fixture/manifest adjudications. The limitations
below are explicitly approved coverage boundaries, not reasons to weaken tests.

## Whole-branch coverage

All 17 changed files in the pinned base-to-snapshot diff were reviewed:

| Area | Files / assessment |
| --- | --- |
| Production | `leanncd/LeanNCD/DSL/Pipeline/Collect.lean`, `ScheduledValidation.lean`; `leanncd/LeanNCD/Semantics/Source/Differential.lean`: collection/plumbing and condition retirement aligned with the approved exclusions. |
| Native fixtures | `leanncd/test/Eval/Plan/B5cSingleBoxTest.lean`, `DefaultF32Test.lean`: padding/fit, D5, scalar, identity, predicate and D2 probes, three native legs, declared-axis reader, tropical hole bits; default-f32 migration preserves its declared/undeclared **plan** comparison rather than disguising shape parity. |
| Independent predictor and differential fixtures | `leanncd/test/Semantics/OracleSortRules.lean`, `OracleSortRulesTest.lean`, `SourceDifferentialScatterTest.lean`: independent prediction, actual checked preparation, fH9 parity and fR failure retained. |
| Registration | `leanncd/lakefile.toml:53`: the new native fixture is in the existing test glob. |
| Live subsystem documentation | `leanncd/AGENTS.md`, `leanncd/LeanNCD/DSL/AGENTS.md`, `leanncd/LeanNCD/Eval/AGENTS.md`, `leanncd/LeanNCD/Semantics/AGENTS.md`: B5c boundary and updated 17/11/6 counts; historical/asymmetric rule distinguished from the current rule. |
| Papers | `papers/backend_missing_functionality.md`, `papers/semantics/additive_b5b_containing_box_design.md`, `additive_production_decision_note.md`, `additive_single_writer_box_design.md`: scope/status changes agree with the plan and D5/rank-zero refinement. |

Unchanged immediate dependencies were checked at the same snapshot: DSL affine
classification/lowering and route, the bridge agreement statement, source
admission/adapter/native legs, collector shape checking and native test helpers.
No production helper was substituted for an independent expected result.

## Explicit production-independence assessment

**PASS.** `singleBoxed` independently recognizes declaration pins (including
iter), nonempty declared destination axes, predicate exclusion, bounded slots,
and D5 from declarations and statements. Its broader treatment of a source
`.assign` is intentional: lowerArith changes affine/repeated slots into a
scatter before production collection. Identity and transposed declared-axis
writes are excluded by D5; scalar destinations by nonempty declared axes.

`declaredShapeWins` independently sums admitted form coefficients, rejects
explicit constants/multi-axis forms, and checks raw source/destination UID
overlap. The admitted model omits pin provenance, but its current source
adapter already demands pinned axis declarations and rejects predicate/iter
declarations. Thus this review does **not** claim it tests inferred-axis
provenance or iter admission. Actual axis/iter box observations are provided by
the SHAPED path; the unpinned native neighbour is `B5cSingleBoxTest.oneInferred`
(lines 16,103).

Production imports inside `OracleSortRules.lean` serve the **observation** side.
The predicted side does not call `boxedSingleGroups`, `declaredAxisSizes`,
`LHSSlot.outExtent`, or production's affine classifier. Native `groupsOf` probes
(`B5cSingleBoxTest.lean:79–82,138–141`) intentionally test the production
classifier directly; these are exclusion/selection probes, not evidence of
oracle independence.

SHAPED accepts mean real preparation acceptance, not independent value
execution. Value/shape padding evidence comes separately from the native
fixtures and fH9's full differential. `agreesShaped`'s existing sizeConflict
allowance applies only to predicted `writerExtentMismatch`, not the new
undersized-box `writerExtentExceedsBox` case.

## Fixture and mutation evidence

- `B5cSingleBoxTest.lean:93–146` has hard expected values/shapes and typed fit
  diagnostics: larger/equal/smaller boxes, bare assigns, unpinned neighbour, D5
  scatter/transpose, scalar/identity, tropical `-inf`, reader and exclusions.
  `B5NativeTest.agree` (158–166) compares actual f64/f32 bits on all three
  native legs; `B5bBoxTest.shapesOf` (102–105) observes their actual shapes.
- Independently counted the 17 staged rows: the original three donors give one
  accept/two refusals; larger axis/iter boxes give three accepts/one refusal;
  the four singleton rows give three accepts/one refusal; equal-extent twins
  give two accepts; matrix twins give two accepts/two refusals. Total:
  **11 accepts, six refusals**. The all-row assertion and count guards connect
  these predictions to actual production preparation.
- Inspected all eleven entries of
  `papers/semantics/additive_b5c_mutations_post.json`. A read-only count against
  the pinned blobs found each `old` substitution exactly once. N01–N08 perturb
  pinning/D5/D1/D2/singleton B5/plumbing/rank-zero; N09 restores the retired
  condition and is observed by fH9; N10 removes singleton prediction and is
  observed by the undersized single iter box; N11 drops predictor D5 and is
  observed by the idiom row. Their targets and expected failing modules/messages
  correspond to the asserted fixtures.
- The authoring record's Verification section reports **11/11 PASS**, byte-
  identical restoration and green restored builds, after correcting equivalent
  identity mutants and adding the transposed/scalar coverage. This is reported
  authoring evidence, not a mutation run performed by this reviewer.
  Controller replay/gates remain separate; no current mutation result is assumed.
- Eight cached changed source/test blob IDs were independently recomputed and
  match the plan §7 hashes. The pinned whole-branch `git diff --check` was clean.
  No builds or tests were run in this review, as requested.

## fR adjudication

**Keep the committed expectations unchanged.** It remains `nativeFailure`,
condition count **0**, and both failures name **`Y#1`**. The box is six cells,
but the scratch's derived extent is five and coordinate five is out of range.
This intentionally unresolved M4/B6 interaction is a real refusal, not a
known-contract-difference escape or successful padding. fH9 is different:
both native outputs actually match the oracle's nine-cell declared shape and
values before classification can return parity.

## Known limits / parked side issues

| Limit | Evidence and adjudication |
| --- | --- |
| Route sees no singleton boxes — S cell | `B5cSingleBoxTest.lean:144` checks successful routing only, not the absence of singleton desugaring. Source inspection of route/default pins supports the intended boundary, but there is no isolating fixture. Leave unchanged. |
| Differential D5 clause — S cell | `SourceDifferentialScatterTest.lean:337–341`: the intended idiom is refused by the oracle first as `writeOutOfRange`. SHAPED and native rows observe D5, not this particular differential clause. Leave unchanged. |
| Predicate checked execution — S cell | `B5cSingleBoxTest.lean:132–134`: reference-only shape observation; checked real-input-to-predicate refusal prevents that execution observation. The direct group-selection probe does not remove this limitation. Leave unchanged. |
| General scope | No actual-write-image fit fix (M4), inferred-size boxes, route/JAX shape agreement, scan-local widening, F3, or generalized signature/capability/range predictor. No backend-refinement theorem is claimed. |

Side issues: isolating the three disclosed S cells; required for this goal? **no**;
rough cost **one focused dispatch per cell**, with admission/capability work
potentially exceeding that estimate; parked, no work undertaken.

## Final verdict and budget

**APPROVE. No defects found.** Approval is of the immutable committed snapshot
and its oracle-independence/evidence claims, not certification of controller
gates still running.

Review stayed below the 45-turn limit (fewer than 30 assistant/tool-call rounds).
Exact token/peak-context telemetry was not measured; no context-budget breach
was observed. No delegation, external system access, builds, commits, or
production/test/manifest changes were performed. This report is the only
tracked-file edit; disposable immutable evidence copies are removed at close.
