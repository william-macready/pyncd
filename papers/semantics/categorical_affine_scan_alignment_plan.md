# Certified affine-scan alignment: implementation plan

**Process: Full — new affine admission, constructed-component and whole-history soundness capabilities.**

**State:** executed. All nine tasks were replayed and the final controller gates passed; see the execution section of the [record](categorical_affine_scan_alignment_record.md) for results, deviations and the post-review fix.
Execute this one slice continuously, reporting milestones rather than presenting approval menus.

## 1. Frozen inputs and command discipline

Goal authority: [handoff](categorical_affine_scan_alignment_handoff.md).
Current evidence authority: [authoring evidence](categorical_affine_scan_alignment_artifacts/authoring-evidence.json).
Implementation authority: [package](categorical_affine_scan_alignment_artifacts/package.json),
its nine ordered patches and nineteen exact final-file SHA-256 values.
Controls: [canonical manifest](categorical_affine_scan_alignment_mutations.json).
History, measurements and pending-gate receipts belong in the separate [record](categorical_affine_scan_alignment_record.md).
Older BLOCKED/only-shift-closed receipts are superseded by current evidence.

- Frozen code base: `13ee25a38366b2069c970754fa371f06d3f15ff9`, including incoming JAX changes.
- Order: admission, component, access, history, interpretation, compiler, mixed, acceptance, documentation.
- Sixteen new Lean modules, `leanncd/lakefile.toml`, and two documentation files account for the nineteen hashes.
- Recorded ordered private-index replay: PASS. Each new module registration occupies its own line;
  incremental patches preserve the original globs prefix. This is a real artifact dependency.
- The manifest belongs to the authoring package, **not** `documentation.patch`; never apply it twice.
- `package.py` reuses the existing operational-associativity generator. It writes patches/receipts:
  do not run it as a supposedly read-only verifier or regenerate the frozen package during replay.
- No Lean snippets are transcribed here. Apply the exact compiled patches; no invented declarations.

Every execution brief opens with this shell-harness discipline:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <absolute-worktree>`.
> Build only with `bash <absolute-worktree>/leanncd/scripts/lake-build.sh <absolute-worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Read approximately 40–60-line windows.
> Stage explicit file paths; never stage `.claude/settings.json`. No nested agents.

The recipes below reserve
`/Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution`
as the **bound** owned clean replay worktree, not an already prepared directory.
The controller verified that both this path and its execution branch are unused before freeze.
No recipe is permission to overwrite an existing checkout.
The current prototype worktree is preserved, including the separately contributed mixed proof.

## 2. Bounded capability and theorem contract

| Surface | Certified scope |
|---|---|
| State/clock | One persistent history `H[i,t]`, spatial extent `d`, recurrence count `n`, history `[d,n+1]`, step context `[n]` |
| Base | Actual external `Z`, one identity assignment, complete canonical writes `H[i,0]=Z[i]` |
| Successors | One real sum/product assignment, complete canonical writes `H[i,t+1]`; initialized boundary policy and immutable-pre-step captures |
| State reads | Arbitrary integer-affine spatial rows, including clock dependence and noninjectivity; temporal row exactly own-clock `t-k`, `k≥0` |
| External reads | Actual integer-affine tables, source shapes, external capture slots and signature association |
| Basis | Certified `contextPos`/`outputPos`, not a guessed matrix-column convention; no reduction positions |
| Arithmetic | Real sum/product structure with f64/float64 storage metadata; supplied exact rational semantic inputs, not Float conversion |
| Boundaries | Zero recurrence, zero spatial extent and both zero, with inhabited actual compiler certificates and retained ports |

`Profile` retains an actual `CheckedScanPlan`, existential checker origin and direct field certificates.
`certifyProfile` distinguishes checker rejection from unsupported checked structure.
It does not change `checkScanPlan` or the general source-admission acceptance set.

The data path must remain visible through the reviews:
actual preparation result → returned `RawScanPlan`/signatures → checker-origin `Profile` →
actual `AffineMap`/`ReadPlan` basis and slot interpretation → admitted reads and ordered bodies →
finite `program`, graph, `close_ok`, `sourceMatch`, `rankCertificate`, `component` →
same-table recurrence/model/unique full store → actual default semantic runners and categorical comparison.
The matching, closure, rank, existence, uniqueness and agreement results are proved, not additional caller premises.
Fresh semantic identities are assigned consistently from actual slots/signatures; original source UIDs are not reconstructed.

Admission proves raw-coordinate equality, rank/width and per-dimension bounds before flattening,
exact in-bounds address, constant-zero padding and ordered footprints with repeated occurrences.
Padding removes only the nonexistent dependency. It is not an unavailable in-bounds read.
Total rational sum/product evaluation supplies existence; rank alone does not exclude strict failure.

Excluded: multiple clocks or persistent states; scattered/partial writes; scratch chains;
contractions/reductions; masks/casts; nonlinear/unary/partial primitives; arbitrary temporal
reindexing, resampling, scan naturality or prefix laws; finite padded-gather fusion;
new administrative `Domain` wires; a general St/Br functor; universal parser/compiler correctness;
Float `runDenseScan`, JAX/backend refinement and physical-storage correctness.
Observed Float fixture rows are observations only, never the rational theorem.
Any side issue outside these goals is parked with its relevance and rough dispatch cost, not implemented.

## 3. Controller preflight and per-task transaction

1. Verify this plan/record against the frozen inputs; freeze the authoring package separately.
   The authoring-only commit includes the plan, record, canonical manifest and artifact package,
   not prototype implementation files or `.claude/settings.json`.
2. Preserve the prototype source and other actor's mixed proof in their existing owned checkout
   or a non-destructive owned snapshot/commit; verify the nineteen final hashes before moving on.
   Do not reset, discard, force-checkout, or `git clean` the prototype.
3. Create a clean owned execution branch/worktree from the frozen base plus the authoring-only package.
   Verify that the implementation files are absent there before applying patches.
   Pin a local authoring-package ref for `prepare-worktree.sh --base`; do not let its default
   moving `main` silently alter the frozen replay base. Preserve concurrent main changes for integration.
4. Follow `new-slice`: prepare the worktree/cache with the prescribed helper, verify ≥95% warm
   Mathlib, then refresh project-owned `LeanNCD` through `lake-build.sh`.
   Stop a genuine cold-Mathlib rebuild and repair cache preparation rather than waiting hours.
   The measured 807-second first `CompilerCertificates` build was cold **project** work over warm Mathlib.
5. Before each task, read its named symbols/imports in 40–60-line windows and check prerequisites.
   Prefer roughly three work items per dispatch. User waived turn/dispatch stop limits:
   do not pause execution merely because a round count is reached; retain context discipline and report overruns.

For **every** task, including documentation:

- Recompute its patch SHA-256 against `package.json`; check the expected prior replay state.
- Run separate `/usr/bin/git -C <execution-root> apply --check <absolute-patch>` and
  `/usr/bin/git -C <execution-root> apply <absolute-patch>` commands, in the fixed order.
  Never replace patch application with hand-transcribed source or broaden a failed hunk.
- Build the smallest target(s) in §4 through the absolute execution-worktree wrapper.
  Documentation has no test of its own.
- Hash each newly introduced module against `package.json`. For `lakefile.toml`, compare
  the cumulative replayed patch state, not the final nineteen-file hash prematurely.
  Its package final hash, and the documentation hashes, become mandatory after task 9.
- Where a manifest task exists, run its exact task selection with `mutation-manifest.sh`,
  retaining the generated table, intended anchors, byte-identical restoration and restored-green result.
  A filtered run is a task checkpoint, never the final unfiltered gate.
- Review the applied diff against the task's contract/fixtures, including its whole theorem statement
  and unchanged siblings in §6. Record findings incrementally in the record/session evidence.
  Fixes that alter frozen source require explicit controller revalidation of patches, hashes and affected controls.
- Stage only that task's explicit files listed below, with absolute path arguments;
  inspect staged names/diff and exclude `.claude/settings.json`. Commit after the spec review is satisfied.
  Include `Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>` as the final trailer.
- Report completed task, target, hash/control results and next task; continue without an approval menu.
  A real load-bearing, unfixable artifact/profile defect is a blocker, not permission to improvise.

Mutation commands use the canonical manifest already present from the authoring commit:

```text
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/leanncd/scripts/mutation-manifest.sh --task admission /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/papers/semantics/categorical_affine_scan_alignment_mutations.json
```

For later task checkpoints replace only the literal task argument with the exact ID below.
Do not pass `--task mixed` or `--task documentation`: those selections have no entries and are errors.

## 4. Nine replay tasks

All module filenames below are exact paths relative to
`leanncd/experiments/indexed_execution/`; explicitly stage those paths, not the directory.
Tasks 1–8 also each change **only their incremental** `leanncd/lakefile.toml` registration.
All patches live in `papers/semantics/categorical_affine_scan_alignment_artifacts/`.
Code prerequisites below describe imports; every task after 1 additionally depends on its predecessor
for **patch replay**, even where no mathematical/import dependency exists.

### Task 1 — `admission.patch` / manifest ID `admission`

- Files: `IndexedAffineScanRead.lean`, `IndexedAffineScanProfile.lean`,
  `IndexedAffineScanPrototypeTest.lean`, plus `leanncd/lakefile.toml`.
- Code prerequisites: existing coordinate/semantic APIs and `Eval.Plan.ScanCompileTest`; no new module prerequisite.
- Symbols: `ReadTable`, `decodeRaw`, `ReadTable.admitted` @ `IndexedAffineScanRead.lean`;
  `profileOk`, `Profile`, `certifyProfile` @ `IndexedAffineScanProfile.lean`;
  `spatialSched`, `boundaryCheck` @ `IndexedAffineScanPrototypeTest.lean`.
- Contract: actual checked tables, structural/external-slot/basis/arithmetic/write certificates,
  explicit unsupported/checker errors, canonical identity base and `[d,n+1]` history.
- Validate: target `IndexedAffineScanPrototypeTest`; four boundary rows `(2,2)`, `(2,0)`, `(0,2)`, `(0,0)`.
  The two manifest controls corrupt base placement and the base-inclusive history extent.
- Review/hash/commit: apply §3; pin acceptance of legal zero neighbors, not merely rejection of bad geometry.
  Suggested subject: `feat(semantics): certify bounded affine scan tables`.

### Task 2 — `component.patch` / manifest ID `component`

- Files: `IndexedAffineScanConstruction.lean`, `IndexedAffineScanMatch.lean`,
  `IndexedAffineScanRank.lean`, plus `leanncd/lakefile.toml`.
- Code prerequisite: task 1.
- Symbols: `externalSlots`, `outerSlot`, `declarations`, `termBasis`, `actualAccess`,
  `orderedProduct`, `orderedSum`, `program`, `captured_state_earlier` @ `IndexedAffineScanConstruction.lean`;
  `closureFacts`, `close_ok`, `schedule`, `sourceMatch` @ `IndexedAffineScanMatch.lean`;
  `factor_rank`, `body_rank`, `rankCertificate`, `component` @ `IndexedAffineScanRank.lean`.
- Contract: constructed finite program, all actual body dependencies, closure/priority/source match,
  time-decreasing rank, external input ports and one full-history output port.
  A spatially transformed read is not replaced by an output-zero representative.
- Validate: target `IndexedAffineScanRank`; three implementation live-proof controls:
  first-only dependencies, spatial-column-as-clock, and future captured clock.
- Review/hash/commit: apply §3; inspect the full generic constructions rather than count closed examples.
  Suggested subject: `feat(semantics): construct matched ranked affine scan components`.

### Task 3 — `access.patch` / manifest ID `access`

- Files: `IndexedAffineScanAccessAgreement.lean`, plus `leanncd/lakefile.toml`.
- Code prerequisites: task 1 and task 2 construction.
- Symbols: `decodeRaw_bounds`, `table_raw_list`, `actualAccess_eq_admitted`,
  `factorBody_read_footprint`, `actual_orderedProduct_footprint`,
  `FiniteControls.aliasTable`, `FiniteControls.shiftExpr`, `FiniteControls.ordered_multiplicity`
  @ `IndexedAffineScanAccessAgreement.lean`.
- Contract: actual raw coordinates/per-dimension admission/padding and exact ordered occurrence footprint.
  Rank/width assumptions must remain explicit; flat-offset range is insufficient.
- Validate: target `IndexedAffineScanAccessAgreement`; three executable assertion groups
  (alias, finite shift/inverse, ordered multiplicity), plus kernel controls.
  Six manifest cycles: five runtime observations, one rank-length live-proof oracle.
- Review/hash/commit: apply §3; preserve the valid interior/nearest-coordinate neighbors and negative fusion result.
  Suggested subject: `feat(semantics): prove actual affine access and footprint agreement`.

### Task 4 — `history.patch` / manifest ID `history`

- Files: `IndexedAffineScanHistory.lean`, plus `leanncd/lakefile.toml`.
- Code prerequisites: task 2 rank, task 3 access, existing ranked witness bridge.
- Symbols: `History.tableRead`, `tableProduct`, `tableSum`, `tableCell`,
  `cell_interpret`, `padding_does_not_cancel_missing`, `Recurrence`, `models_iff_recurrence`,
  `wholeStore_model`, `exists_unique_whole_history`, `actual_base_value`,
  `wholeStore_base`, `wholeStore_successor` @ `IndexedAffineScanHistory.lean`.
- Contract: recurrence from the same actual tables, every materialized coordinate,
  input preservation, generic model equivalence, total well-founded existence/uniqueness,
  actual identity base and successor clock/write geometry.
- Validate: target `IndexedAffineScanHistory`; four cycles: three implementation live-proof
  controls (base spatial offset, successor clock, nonzero semantic padding) and one strictness oracle.
- Review/hash/commit: apply §3; do not introduce execution agreement or a model as a caller premise.
  Suggested subject: `feat(semantics): characterize complete affine scan histories`.

### Task 5 — `interpretation.patch` / manifest ID `interpretation`

- Files: `IndexedAffineScanInterpretation.lean`, `IndexedAffineScanHistoryTest.lean`,
  `IndexedAffineScanSemantics.lean`, plus `leanncd/lakefile.toml`.
- Code prerequisites: task 4; public entry point also imports task 3.
- Symbols: `Interpretation.default_full_history`, `recurrence_iff_actual_full`,
  `history_port_metadata`, `witness_total`, `categorical_comparison`,
  `categorical_whole_history`, `operational_history_full` @ `IndexedAffineScanInterpretation.lean`;
  `HistoryTest.rationalHistory`, `referenceHistory`, `actual_executor_agreement`
  @ `IndexedAffineScanHistoryTest.lean`.
- Contract: actual default checked/reference completion, relations and **full stores**;
  complete witness/categorical image and all history slices, including empty-port metadata.
  `IndexedAffineScanSemantics` is the discoverable nondefault public entry point,
  without importing compiler-example certificate work into that entry point.
- Validate together: targets `IndexedAffineScanSemantics IndexedAffineScanHistoryTest`.
  Three cycles: final-only observation and empty-witness-image implementation controls;
  zero-spatial port-erasure live-proof oracle.
- Review/hash/commit: apply §3; exact semantic runners are not the Float scan backend.
  Suggested subject: `feat(semantics): interpret affine histories operationally and categorically`.

### Task 6 — `compiler.patch` / manifest ID `compiler`

- Files: `IndexedAffineScanCompilerExamples.lean`, `IndexedAffineScanCompilerCertificates.lean`,
  plus `leanncd/lakefile.toml`.
- Code prerequisites: task 1 prototype/profile and task 2 construction.
  History/interpretation are **not** mathematical prerequisites; task 5 precedes this solely for replay wiring.
- Symbols: `CompilerExamples.recurrenceSched`, `CompiledExample`, `compileExample`,
  `checkLinks`, `checkSpatialFamily`, `checkMixedFamily`, `checkDeepFamily`,
  `wrongBasisExample`, `wrongMapExample`, `wrongOrderExample`, `wrongMultiplicityExample`
  @ `IndexedAffineScanCompilerExamples.lean`;
  `shift_success`, `spatialDonor_success`, `spatialDonorCompiled`
  @ `IndexedAffineScanCompilerCertificates.lean`.
- Contract: actual `prepareEvalPlan`/`scanAt`/certification origins, actual compiler maps,
  roles and slots; closed shift, stride, reversal, deep and four boundary donors.
  The mixed runtime donor is present; its closed compiler certificate is task 7.
- Validate: target `IndexedAffineScanCompilerCertificates`; three executable family groups,
  eight manifest runtime controls. First project compilation measured 807 seconds over warm Mathlib;
  give the wrapper sufficient time rather than confusing this with a cache failure.
- Review/hash/commit: apply §3; retain lawful native `String.hash` enumeration handling,
  not an assumed native hash order or a hard-coded reordered signature.
  Suggested subject: `test(semantics): certify actual affine scan compiler donors`.

### Task 7 — `mixed.patch` / no manifest selection

- Files: `IndexedAffineScanMixedCompilerCertificate.lean`, plus `leanncd/lakefile.toml`.
- Code prerequisite: task 6.
- Symbols: `CompilerExamples.mixed_signature_cases`, `mixed_inferred`, `mixed_success`,
  `mixedCompiled`, `mixedCompiled_origin`, `mixedCertifiedProfile`
  @ `IndexedAffineScanMixedCompilerCertificate.lean`.
- Contract: close the ninth actual compiler donor without fixing one accidental external-input
  hash enumeration. Keep its actual preparation, scan and certification associations.
  Preserve the separately user-assigned Claude Code contribution; root already independently validated it.
- Validate: target `IndexedAffineScanMixedCompilerCertificate`; one additional closed donor,
  no new manifest controls. Its discriminating runtime controls are in task 6 and final acceptance.
- Review/hash/commit: apply §3; do not replace the proof with a proposition about a hand-built profile.
  Suggested subject: `test(semantics): close mixed affine compiler certification`.

### Task 8 — `acceptance.patch` / manifest ID `acceptance`

- Files: `IndexedAffineScanHistoryCompilerTest.lean`, `IndexedAffineScanNamespaceAudit.lean`,
  plus `leanncd/lakefile.toml`.
- Code prerequisites: task 5 history interpretation, task 7 mixed (transitively task 6);
  audit also imports the public entry point and task 1 prototype.
- Symbols: `CompilerHistoryTest.certifiedExamples`, `certified_examples_full_meaning`,
  `observeAll`, `checkNegativeControls` @ `IndexedAffineScanHistoryCompilerTest.lean`;
  whole `IndexedExecutionExperiment.AffineScan` namespace @ `IndexedAffineScanNamespaceAudit.lean`.
- Contract: all nine closed donors retain unique model/full-store default execution/category meaning.
  Eight exact rational history rows independently check expectations, whole coordinate count and ports.
  Wrong basis/map/multiplicity, equal-valued wrong order, strict missing demand and all-padded success remain live.
- Validate: target `IndexedAffineScanNamespaceAudit`; eight runtime controls and namespace axiom audit.
  Prototype observation: 861 new namespace constants use only `propext`, `Classical.choice`, `Quot.sound`.
- Review/hash/commit: apply §3; numeric rows do not substitute for generic live theorem consumers.
  Suggested subject: `test(semantics): pin compiler histories and audit the affine namespace`.

### Task 9 — `documentation.patch` / no manifest selection

- Files only: `leanncd/AGENTS.md`, `papers/semantics/categorical_tensor_logic_semantics.md`.
- Code prerequisites: public API/results from tasks 1–8; replay prerequisite task 8.
- Contract: discoverable nondefault entry point, actual certificate/whole-history capability,
  compiler-certificate separation, empty metadata and explicit numerical/transformation nonclaims.
- Apply §3, run the documentation sweeps in §8, then verify **all nineteen** final hashes.
  No documentation-specific build; the final controller full build remains required.
  Suggested subject: `docs(semantics): document certified affine scan alignment`.

## 5. Frozen fixtures: donors, deltas and discrimination

These are already compiled/observed artifacts, not instructions to design replacement fixtures.
Names below locate the exact implementation in task files; keep the package's assertions verbatim.

| Fixture/donor | Actual delta and observed discrimination |
|---|---|
| `Prototype.spatialSched` from `axisPosSched` | Concrete `d,n+1` extents; `boundaryCheck` accepts all four `(2,2),(2,0),(0,2),(0,0)` cases with actual checker/profile metadata |
| `shiftSched` from `recurrenceSched` | Spatial `i-1`: at clock zero raw `[-1,0]` pads with no dependency; other addresses yield diagnostic values `100,110,120` |
| `strideSched` from the same donor | Spatial `2i`: addresses `[0,0],[2,0],[4,0],[6,0]`; values `100,120,0,0`, last two footprints empty |
| `reversalSched` from the same donor | Spatial `3-i`: diagnostic values `130,120,110,100`; distinguishes sign and offset without assuming injectivity generally |
| `mixedSched` from the same donor | State `i+t`, external `1+2i+t` with extent 9 versus state extent 4; actual basis context 0/output 1; factors `[S,X,S]+[X,S]` |
| `wrongBasisExample` from returned mixed tables | Swap unequal external columns only: at `i=1,t=2`, external address `5→6`, value `19399380→19416936` |
| `wrongMapExample` from returned mixed tables | Drop state spatial column only: state address `[3,2]→[2,2]`, value `19399380→16581630` |
| `wrongMultiplicityExample` from returned mixed tables | Drop repeated first-term factor: five occurrences become four, value `19399380→291720` |
| `wrongOrderExample` from returned mixed tables | Reorder factors; diagnostic value stays `19399380`, but ordered footprint changes. Value parity cannot certify order |
| `deepSched`, spatial lift of `deepHistorySched` | Actual temporal bias `-2`; at clocks `0,1,2`, deep coordinates `[1,-2],[1,-1],[1,0]`, values `110,111,222` including the immediate term |
| Legal temporal neighbors | Bias `-1` at `i=1,t=2` reads `[1,1]`, value `111`; bias `0` is also accepted. Future `+1`, scaled clock `2t`, wrong spatial-clock column are rejected by unchanged source/checker |
| `FiniteControls.aliasTable` | Shape `[2,3]`, raw `[0,3]`, flat offset `3` aliases `[1,0]` yet per-dimension bounds reject; nearest valid neighbor `[0,2]` discriminates |
| `FiniteControls.rank_hypothesis_is_essential` | Rank-short `[0]` passes zip bounds for `[2,0]` but typed decoding fails; one explicit live-proof oracle, not a runtime-core mutation |
| `FiniteControls.shiftExpr` | Staged `+1` then `-1` versus raw identity: `[some 0,some 6,some 7]` versus `[some 5,some 6,some 7]`; legal interior retained |
| `FiniteControls.readOrder` | Padded occurrence disappears; ordered footprint remains `[[0],[0],[1]]`. Control both removes a repeated zero read and moves distinct address one first |
| Mixed strictness/boundaries | At `i=2,t=2`, state factors pad, external address 7 remains demanded twice: total value zero but missing-store result `none`; at `i=3,t=2`, all pad, footprint empty and result `some 0` |
| Actual empty compiler donors | `(2,0)` retains full base `[1/2,1]`; `(0,2)` and `(0,0)` return `[]` while retaining input `[[0]]` and output `[[0,n+1]]`; kernel certificates, not vacuous support |

The eight history rows are `observeAll`'s shift, stride, reversal, mixed, deep, zero recurrence,
empty spatial, and empty spatial+zero recurrence rows @ `IndexedAffineScanHistoryCompilerTest.lean`.
Exact full expected lists remain in the compiled patch. For example, the observed mixed row starts
`[1/2,1/2,88/9,14523712/27]`; these rational semantic inputs are intentionally not the Float diagnostic inputs.
Each row has its own manifest control; the last two controls pin metadata, not a nonexistent numeric coordinate.
The ordinary `(2,2)` boundary is the ninth certified donor, not an invented ninth rational-history row.

## 6. Required/forbidden/ignored sibling audit

Review unchanged contracts alongside changed code; a diff alone cannot establish their agreement.
Names without file prefixes here are in `leanncd/LeanNCD/Eval/Plan/`.

| Case/class | Required / forbidden | Siblings and treatment |
|---|---|---|
| Rank/coordinates | Require rank/width and per-dimension bounds; forbid flat-alias admission | `applyAffine`, `inBoundsPerDim`, `flatIndex` @ `Coordinates.lean`; semantic `decodeRaw` and access lemmas; zip rank-short caveat explicitly protected |
| State time | Require own `contextPos` coefficient one, nonpositive bias; forbid future/scaled/wrong-clock rows | `causalAdvancingRow`, `stateReadCausal` @ `Scan.lean`; `stateRowsOk`, `state_time`, `captured_state_earlier`; legal `0,-1,-2` and three bad neighbors pinned |
| Full placement | Require identity base, canonical full successors and `n+1` history; forbid scatter/overlap/partial writes | `baseWriteRowsOk`, `stepWriteRowsOk`, `writeRowKinds` @ `Scan.lean`; `profileOk`, `actual_write_coordinates`, base/successor theorems |
| Arithmetic/read effects | Require real sum/product and plain reads; forbid reductions/masks/casts/unary/partial ops | `readFactorsIndexed` @ `Kernel.lean`, `checkAssignCore` @ `Check.lean`, `plainRead`/`termSupported`; unsupported is explicit, never silently dropped |
| Capture/signature roles | Require actual base+step externals and separate state role; forbid phantom ports or UID reconstruction | `allCaptures`, `externalSlots`, `readTensor`, `outerSlot`, `CompiledExample` origins; unequal mixed external shape and zero metadata protected |
| Order/demand | Require every repeated address in factor/term order; padding only omits nonexistent address | `gatherFactorWith` @ `Dense.lean` is contract context, not a Float correctness target; `orderedProduct`, footprints and strict missing-read controls |
| Scope boundaries | General source scan/affine admission and administrative wires unchanged | `readIndices`, `outputIndices` @ `leanncd/LeanNCD/Semantics/Source/Admission.lean`; existing ranked/witness frame restrictions retained |

No ignored-cell acceptance is claimed: unsupported syntax/fields are explicitly rejected at the
profile door or remain outside this bridge. Irrelevant source names/UID reconstruction and arbitrary
Float payload interpretation are nonclaims, not silently trusted inputs. If review finds a field
silently ignored where this table requires it, record a load-bearing finding rather than widening the profile.

## 7. Measured risk and mutation accounting

Fixture counts below count actual named assertion groups/rows or closed donors, not every proposition.
Zero standalone numeric fixtures does not mean zero proof obligations.
R = runtime-observation, I = live-proof-implementation, O = live-proof-oracle.

| Task | Frozen fixture/proof workload | Manifest cycles R/I/O | Expected anchors | Risk |
|---|---|---|---|---|
| admission | 4 boundary rows | 2/0/0 | 2 | Base-inclusive extent and legal empty neighbors |
| component | Generic construction/match/rank; no standalone numeric rows | 0/3/0 | 9 | All dependencies and actual own clock |
| access | 3 executable assertion groups plus kernel controls | 5/0/1 | 7 | Rank-short caveat, flat alias, order, finite padding |
| history | Generic recurrence/model/existence/uniqueness; no standalone numeric rows | 0/3/1 | 11 | Base/clock alignment, totality versus rank, strict demand |
| interpretation | Generic full-store/category/metadata consumers; no standalone numeric rows | 0/2/1 | 8 | Final-only observation, empty witness image/port |
| compiler | 3 family assertion groups; 8 closed nonmixed donors | 8/0/0 | 8 | Actual maps/slots, native hashing; 807-second first project build |
| mixed | 1 additional closed donor, reusing mixed observations | 0/0/0 | 0 | Preserve external contribution and lawful signature-order cases |
| acceptance | 8 rational-history rows; full-meaning consumers for all 9 donors | 8/0/0 | 8 | Independent expected values, empty metadata, standard-only audit |
| documentation | 2 existing documents | 0/0/0 | 0 | Discoverability and nonclaims; no separate test |
| **Total** | Shared donors/groups are not additive fixture counts | **23/8/3 = 34** | **53** | Controller replay remains pending |

All 34 final candidates were observed to fail their mutated build, restore byte-identically and
build green after restoration during authoring. `expect` strings are copied from those failures.
These are **not 34 runtime-core defect kills**: eight protect live implementations through proofs,
three reverse logical oracles, and twenty-three protect runtime observations.
Some live-proof diagnostics include type/proof failures plus namespace `sorryAx` rejection;
report them as such, never as runtime assertions or setup refusals.

There were 35 exploratory cycles. The retired source-factor-order proxy changed capture numbering
and failed earlier metadata checks; it does not count in the final 34. Its replacement reverses
semantic `orderedProduct` traversal with unchanged capture tables and commutative rational values.
The non-palindromic second mixed term makes ordered footprints discriminate the true semantic reversal.
Canonical unfiltered `--check` passed in authoring; per-cycle observations do **not** complete the
release gate requiring the controller's unfiltered intended-diagnostic replay.

## 8. Final controller gates, reviews and local integration

After task 9, controller independently:

1. Recompute all nine patch hashes, all nineteen final-file hashes and manifest SHA-256
   `8bb0ab94b611e39eb444690ddddce4e516ea28d42e28a215ec47361af99d9f25`.
   Check exact base/order/schema, 34 unique labels/replacement sites and 53 expected anchors.
2. Run unfiltered schema check **and** unfiltered canonical replay below; retain the complete results
   table in the record. Require all intended anchors, actual mutated failures, byte-identical restored
   sources and restored-green builds. Recheck all nineteen source hashes afterward.

```text
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/papers/semantics/categorical_affine_scan_alignment_mutations.json
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/papers/semantics/categorical_affine_scan_alignment_artifacts/controller-mutation-results.md /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/papers/semantics/categorical_affine_scan_alignment_mutations.json
```

The wrapper's `--out` result is a generated table: **do not overwrite the authored record**.
The recipe writes a separate project-local result, not a new frozen package input. Append its table
to the record, then remove the intermediate only after preserving the evidence.
Keep those operations separate; no shell pipelines into git.
Run this exact final hash check before and after the replay:

```text
python3 -c 'import pathlib,json,hashlib; r=pathlib.Path("/Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution"); d=r/"papers/semantics/categorical_affine_scan_alignment_artifacts"; p=json.loads((d/"package.json").read_text()); assert len(p["patches"])==9 and len(p["sources"])==19; assert all(hashlib.sha256((d/x["path"]).read_bytes()).hexdigest()==x["sha256"] for x in p["patches"]); assert all(hashlib.sha256((r/f).read_bytes()).hexdigest()==h for f,h in p["sources"].items()); assert hashlib.sha256((r/"papers/semantics/categorical_affine_scan_alignment_mutations.json").read_bytes()).hexdigest()=="8bb0ab94b611e39eb444690ddddce4e516ea28d42e28a215ec47361af99d9f25"; print("PASS: 9 patch hashes, 19 final source hashes, canonical manifest hash")'
```

3. Audit **all sixteen** `IndexedAffineScan*.lean` sources for axiom/constant declarations,
   `sorry`, `admit`, `native_decide`, `ofReduceBool`, hard-coded user paths and diagnostic file writes.
   Repeat the all-namespace target `IndexedAffineScanNamespaceAudit`; do not audit only headline lemmas.
   Require standard-only axioms and compare the recorded 861-constant coverage; explain any discrepancy.
4. Run documentation sweeps as commands, adjudicating historical handoff/record matches rather than
   rewriting history. No acceptance-set count changed in the existing scan checker.

```text
rg -n --glob '*.md' 'IndexedAffineScan|AffineScan.Profile|whole.history|runDenseScan|padded.gather' /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/leanncd/AGENTS.md /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/papers/semantics
rg -n --glob '*.md' 'only.shift|shift.only|34.{0,30}runtime|807|8980|861|174,907,950|425,440' /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution
rg -n --glob 'IndexedAffineScan*.lean' '(^|[[:space:]])(axiom|constant|sorry|admit|native_decide|ofReduceBool)([[:space:]]|$)|/Users/|IO\.FS\.(writeFile|appendFile)' /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/leanncd/experiments/indexed_execution
```

The source sweep should have no matches; inspect any match, including comments, before adjudication.
Documentation-only sweeps are controller work, not a heavyweight new implementation dispatch.

5. Obtain **two final whole-branch review lenses**, not just task reviews:
   - Soundness: affine admission/raw bounds/padding/ordered footprints, every dependency's rank,
     constructed closure/priority/source match, same-table whole-model existence/uniqueness,
     actual default full stores and categorical comparison; no assumed conclusion.
   - Applicability/boundaries: actual checked/compiler origins and slot/signature data, base/successor
     geometry, own-clock policies, factor order/multiplicity, strict zero-times-missing,
     zero/empty inhabitance and metadata, exact-rational versus Float boundary and explicit nonclaims.
   Review complete branch diff plus named unchanged siblings. Keep incremental findings;
   adjudicate/fix them and repeat affected validation. No nested agents in this authoring dispatch.
6. Controller runs the full required build, not merely accepts the prototype receipt:

```text
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution/leanncd LeanNCD Tests IndexedExecutionExperiment
```

7. Record measured execution-only usage separately from authoring, review outcomes, full-build result,
   all hashes and mutation table; state the covered profile and remaining nonclaims precisely.
   Execution accounting starts separately against the 175M budget; existing cumulative authoring
   totals cannot certify it. Use `token-report.py` when available and disclose missing telemetry.
8. Inspect current local `main` and worktree status. Preserve concurrent main changes, including JAX;
   reconcile on the owned execution branch without rewriting/discarding anyone else's history.
   If integration changes the reviewed tree, repeat affected reviews/hash adjudication/mutations and
   controller full build on the final combined tree. Frozen replay hashes remain the original receipt;
   record any necessary integration adaptation separately instead of silently regenerating them.
9. With gates green and findings adjudicated, merge to **local main**, verify the resulting tree,
   delete only owned task branches and remove only owned worktrees after inspecting their status.
   Do not delete the preserved prototype/other-actor work until its safe persistence and ownership
   are confirmed. No destructive reset/checkout/clean, no force cleanup of unidentified files.
   Do not push. Report local integration and any local-main lead over origin truthfully.

Milestones: authoring frozen → clean replay tasks 1–3 → history/interpretation tasks 4–5 →
compiler/acceptance tasks 6–8 → documentation/final hashes → controller replay/audits/two reviews/full build →
local integration/owned cleanup. None is a menu or automatic approval pause.
