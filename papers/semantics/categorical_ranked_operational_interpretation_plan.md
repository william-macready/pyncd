# Provenance-aware ranked operational interpretation — implementation plan

**Process: Full** — new operational categories/functor and a soundness surface; explicitly approved provenance-aware source refinement, required for this goal.
One slice, eight mechanical task patches. Authoring (b) used frozen artifacts only.
**Execution and controller release complete; local integration pending.** All eight tasks were cleanly replayed and committed, all eleven controller cycles passed, and the full build passed 8,953 jobs. P1 `SEM-ADMIN-INTERPRETATION` is CLOSED by focused semantic source review; the integration lens is clean. The plan below preserves the verified execution contract; actual receipts are in the record.
Evidence, historical limitations and release receipts belong in the [separate record](categorical_ranked_operational_interpretation_record.md).

## 1. Frozen contract and shell discipline

- Worktree: `/Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff`.
- Frozen base: `921cca7e4c28066ae1912c398b27c351930fc18c`.
- Package: [artifacts/package.json](categorical_ranked_operational_interpretation_artifacts/package.json); eight ordered patch hashes and fourteen final file hashes are authoritative. The old seven-patch/thirteen-file receipt is historical only.
- Canonical [mutations manifest](categorical_ranked_operational_interpretation_mutations.json) belongs to the **authoring package**, not `documentation.patch`; eleven measured cycles, no post-manifest needed.
- Latest controller report: primary checkout is clean; local main advanced through four unrelated JAX documentation/test commits to `aa343773`, with Lean/semantics scope untouched. The frozen replay base remains `921cca7e`; integrate latest local main before final release validation.
- Plain, separate shell commands; no chained directory changes, shell-variable expansion, pipelines into git, temporary directories, resets, checkouts, cleans or code rewriting.
- Use absolute paths and `/usr/bin/git -C <worktree>`. Build only through the absolute `leanncd/scripts/lake-build.sh` wrapper with the absolute `leanncd` directory.
- Stage explicit task paths only; never `.claude/settings.json`. Preserve unrelated source/doc changes and concurrent main work. No push.
- In the task lists below, module files are `leanncd/experiments/indexed_execution/<module>.lean`; each task also owns its exact incremental `leanncd/lakefile.toml` hunk, except Task 8.
- Read only 40–60-line windows around the listed `identifier @ file`; do not rediscover or transcribe the compiled implementation. Exact code is in the patches.
- This is an existing isolated worktree; do not create another or cold-build Mathlib. Stop on a load-bearing blocker, hash mismatch or overlap, rather than weakening a theorem.

## 2. Chosen semantics and hard exclusions

**Arrows.** `Normal X Y` is either `admin w` for a complete certified whole-interface wire, with no core program, or `compute A rank origin before after`.
Its four-case composition composes administrative wires, changes only exterior wires in mixed cases, and uses the existing actual `compose`, `connectingBoundary` and `compositeRankCertificate` for two computations.
`Origin` distinguishes opaque leaves from joined compiled origins containing both child origins and the actual supplied boundary.
Administrative `History.done` preserves the supplied full state; `AvailableView.reindex` changes the interface view without adding events or changing inherited availability/ordered ledgers.
**Connected realization.** `Realizes` is indexed by the existing `Normal`, ambient scope, inherited state, input environment and output-carrying history; admin uses actual `runWire`, compute uses the lifted actual `actualHistory`.
`Frame` supplies certified injective domain/address and identity placements, inherited outside availability and an ordered ledger prefix disjoint from local identities.
`FreshInput` explicitly requires the entire owned initial availability, including private cells, to match the actual local initial state; it does not permit arbitrary prepopulated owned computation storage.
`successfulView` derives whole output availability from actual successful completion; failure absorbs the continuation without an output premise. Mixed pre/post-wire realization and `actual_join_identity` connect actual histories, not just normalized units.
`source_history`, `target_history`, `semantics_history` retain full observation agreement and derive ambient history equality under structural `Coherent` address/identity/inherited-frame squares, not assumed execution equality.

**Independent target.** Administrative agreement is equality of entire Wire records; admin/compute agreement is false.
`ComputeAgrees` chooses one metadata transport and one structurally certified `ProvenanceIso` **before** quantifying over every whole external environment.
It requires full raw/admitted input/output exterior equations and actual `CompleteObservation.Agrees` for every validated input.
Whole ports, roles, Option-valued input, every private snapshot, ordered ledger/events and terminal failures remain observable; failure requires no successful output.
`composition_congruence` is proved from local observations via scope/history naturality and full raw exterior gluing, not assumed for composites.
Only then does `Arrow.comp` descend `Normal.comp`, with units/associativity, to the actual Mathlib category on the distinct `Target` wrapper.

**Generated source, not a selected-representative quotient.** A separate `Object`, ranked/origin-carrying `Term`, and generated `Rel` give the source category.
The exact retained generators are reflexivity/symmetry/transitivity, sequential congruence, category left/right units and associativity, wire identity/composition/both inverses, decorated assembly, and left/right inherited full-Wire boundary squares.
The boundary squares are administrative and rank-free; leaves and decorated computational assembly carry actual ranks.
Assembly relates the explicitly joined compiled origin to its ranked children, never an arbitrary opaque compiled leaf.
`sound` checks all generators; `semantics` is a genuine Mathlib functor into the independent target.
`left_eq_triple` and `right_eq_triple` derive `bracket_rel` and `bracket_sound` from assembly, squares and category laws; bracket is not a new assumed primitive.
Alternative valid rank certificates preserve actual full histories/observations and the functor image for a fixed origin; they do not erase provenance.

**Conservative bridge.** `actualHistory_spec` proves admissibility, actual default `runChecked` equality and the correct initial state.
`actual_binary` reuses actual binary history composition; native nested metadata and `nestedAdapterEquiv_originals` retain the original `(ab, bc)` with arbitrary child origins.
`actualReferenceObservation` uses actual default `Program.Executor.run`; `actual_reference_states` retains normalized `referenceSnapshots`, `LedgerInvariant` and the full existing `Relation`, including pending occurrences/accumulators.
`rightUnitReference` preserves the same metadata, reference start/result and correspondence.
This is **not** a generic arbitrary-program reference-state transport theorem.

Do not change runner/scheduler/default fuel, core operators or completed witness source.
Do not add a phantom identity/copy, substitute input for output, collapse vacuous computations into admin arrows, reorder events, quotient stuttering, forget metadata/provenance, or claim execution on arbitrary prepopulated frames.
Malformed raw-input and arbitrary debug-fuel equivalence, unranked operational equations, backend refinement and generic categorical machinery are excluded.
No new scope slice or side issue is authorized.

## 3. Clean reexecution protocol

The current working tree contains the repaired verified prototype under final module names. **Do not apply patches on top of it.**
Use only the regenerated eight-patch/fourteen-file package; the historical thirteen-file package is superseded.
The controller first verifies all eight patch hashes and all fourteen current file hashes against `package.json`.
Inspect status and preserve every nonowned change. Hash equality is mandatory before deleting any prototype-owned file.
Reverse only these patches, checking each immediately before applying it, in this order:
`documentation`, `acceptance`, `interpretation`, `source`, `category`, `scope`, `core`, `units`.
For example, the first pair is:

```sh
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff apply --reverse --check /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/papers/semantics/categorical_ranked_operational_interpretation_artifacts/documentation.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff apply --reverse /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/papers/semantics/categorical_ranked_operational_interpretation_artifacts/documentation.patch
```

Expand this same separate-command pair for each remaining explicit patch path in the stated reverse order; no loop or broad restore.
Verify implementation-owned existing files equal their frozen-base blobs and the eleven new module paths are absent.
The authoring package, canonical manifest, this plan and record remain untouched; unrelated files must remain unchanged.
Commit the authoring package/manifest/plan/record **first**, staging their individual files explicitly, not a directory wildcard.
Authoring inventory: the eight named patches, `package.py`, `package.json`, `snippets.json`, `authoring-mutations.md`, canonical manifest, plan and record.
Raw snippet logs are gitignored evidence, not promised committed deliverables; `package.py --snippets` reproduces them and receipts, but do not regenerate frozen inputs during deterministic replay.
No implementation source belongs in that first commit.

Then apply Tasks 1–8 **in order**, each with `git apply --check` followed by `git apply`, targeted build, per-task review and explicit-path commit.
For Task 1 the command pair is:

```sh
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff apply --check /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/papers/semantics/categorical_ranked_operational_interpretation_artifacts/units.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff apply /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/papers/semantics/categorical_ranked_operational_interpretation_artifacts/units.patch
```

Use the corresponding explicit absolute patch path for each later task. Do not regenerate the frozen package or hand-edit Lean.
Append execution findings/results to the record, not this live plan. Commit messages follow repository style and include the required Copilot coauthor trailer.
A reviewer may reject any task independently of its neighbor. Review is a bounded checklist, not a heavyweight documentation dispatch.

### Risk/work inventory

Counts are mechanically observed patch contents: anonymous `example` assertion sites, named donor instantiations and `#eval` rows, **not counts of independent runtime defects**.
General quantified theorems are not counted as concrete fixtures. Cycles are assigned once; downstream proof coverage is shared.

| Task | Patch | Actual import prerequisites among tasks | Fixture/assertion and eval count | Assigned final cycles |
|---|---|---|---|---|
| 1 | `units.patch` | none | 19 anonymous assertions; 4 eval rows | 4: U1–U4 |
| 2 | `core.patch` | none; ordered after 1 for lakefile patch context | 0 concrete assertions/evals; quantified bridge/coherence proofs | 0; checked downstream by S1/S3 |
| 3 | `scope.patch` | 2 | 0 concrete assertions/evals; quantified naturality proofs | 1: S3 |
| 4 | `category.patch` | 2, 3 | 0 concrete assertions/evals; equivalence, 4 composition cases, 8 association cases | 1: S2 |
| 5 | `source.patch` | 1, 2, 4; 3 transitively | 0 concrete assertions/evals; generated soundness/reference proofs | 1: S1 |
| 6 | `interpretation.patch` | 1, 5; aggregator also imports 2–4 | 0 concrete assertions/evals; connected realization/frame/actual-history proofs | 2: M1/M2 |
| 7 | `acceptance.patch` | 1–6 transitively | 24 anonymous assertions + 2 named empty/axis instances; 3 eval rows | 2: W1/W2 |
| 8 | `documentation.patch` | no Lean imports; truthful documentation requires 1–7 | 0 | 0 |

The complete manifest runs after Task 7, without filters; targeted builds do not replace it.
No additional fixture discovery, fresh implementation dispatch or production/fixtures split is expected for mechanical replay.
If any task approaches 60 turns or 250k peak context, stop and split the bounded work; do not silently overrun.

## 4. Task briefs and per-task review

### Task 1 — administrative history units and scoped wires

Files: `IndexedOperationalUnits.lean`, `IndexedOperationalWireFrame.lean`, incremental lakefile.
Symbols: `History.returning`, `done_bind`, `bind_done`, `done_splice`, `splice_returning`, `failure_bind`, `returning_map`, `splice_normalization`, `actual_leaf_right_unit` @ `IndexedOperationalUnits.lean`;
`Scope`, `AvailableView.reindex`, `Scope.reindex`, `runWire_identity`, `runWire_composition`, `runWire_inverse` @ `IndexedOperationalWireFrame.lean`.
Donors: clone `Fixtures.first`/`second`, insert return before/after; clone `privateFailure`, insert return or `second`; clone `ledgerLeft`, `ledgerRight`, `privateAvailable`, preserve nonempty prefix/private 42; clone `emptyMetadata` and `MetadataLawFixtures.absentEmptyMetadata`, keep equal event-free histories but unequal whole input presence; clone `swapping` to check transport.
Review: no copied core identity, duplicate shared snapshot, failure fall-through, ledger reset/reversal or private erasure; actual-leaf proof obtains its history/start from `ranked_default_exists`.
Build `IndexedOperationalUnits IndexedOperationalWireFrame`; commit those two modules and only this lakefile increment.

### Task 2 — ranked normal closure and exact provenance coherence

Files: `IndexedRankedOperationalCore.lean`, incremental lakefile.
Symbols: `connectingBoundary`, `boundaryEquiv`, `wireReindex`, `boundaryReindex`, `left_square_full`, `right_square_full`, `Normal.comp`, `Origin`, `actualHistory_spec`, `actual_binary`, `actualHistory_rank_independent`, `actualObservation_rank_independent`, `nestedAdapterEquiv_originals`, `nestedOrigin_metadata` @ `IndexedRankedOperationalCore.lean`.
Review: all four constructor combinations type correctly; only computational/computational composition creates joined provenance; every Domain includes raw-axis/admitted coherence.
Inspect siblings `leftBoundaryEquiv_recover`/`rightBoundaryEquiv_recover`, both wire inverses and administrative slide/cancellation, not only the patched equation.
`observation_shape_does_not_assert_start` is the quantified wrong-start countercontrol, not an actual-run fixture; `no_unit_boundary_equiv` rejects invented opaque provenance.
Build `IndexedRankedOperationalCore`; commit module/lakefile increment.

### Task 3 — full-state scope/history naturality

Files: `IndexedOperationalScopeNaturality.lean`, incremental lakefile.
Symbols: `ScopeChange`, `combinedIdentity`, `combinedTransport`, `upstream_state`, `downstream_state`, `upstream_history`, `downstream_history`, `boundary_inputs`, `combined_metadata`, `binary_transport`, `runner_congruence` @ `IndexedOperationalScopeNaturality.lean`.
Review upstream/downstream siblings across availability, ordered ledger, events, failures, full-store witnesses, input validation and shared cuts.
The parity-conjugated identity map retains upstream/downstream lanes; `BoundaryCoordinates` is a derived admitted-coordinate helper, not a replacement for full raw-wire gluing.
No theorem asks the runner to execute arbitrary inherited frames. S3 swaps the lane equivalences and must break the live proof.
Build `IndexedOperationalScopeNaturality`; commit module/lakefile increment.

### Task 4 — full observation congruence and independent target category

Files: `IndexedRankedOperationalCategory.lean`, incremental lakefile.
Symbols: `ComputeAgrees`, `ProvenanceIso`, `Agrees`, `exterior_gluing`, `compute_comp_congruence`, `compute_precompose`, `compute_postcompose`, `composition_congruence`, `composition_associativity`, `Arrow.comp`, `targetCategory` @ `IndexedRankedOperationalCategory.lean`.
Review fixed-before-input transports; full input/output exterior squares; exact `boundaryReindex` image; original child provenance; admin/compute exclusion and `opaque_not_joined`.
Check both mixed whiskerings and computational composition, all eight association cases, and descent respectfulness before accepting the category.
No composite execution equality is assumed. S2 is the live-proof guard against event-free computational/admin collapse.
Build `IndexedRankedOperationalCategory`; commit module/lakefile increment.

### Task 5 — generated source, actual functor and full reference bridge

Files: `IndexedRankedOperationalSource.lean`, `IndexedRankedOperationalReference.lean`, incremental lakefile.
Symbols: `Term`, `Rel`, `assembled`, `pair`, `Term.normalize`, `sound`, `semantics`, `bracket_rel`, `bracket_sound`, `semantics_leaf_rank_independent` @ `IndexedRankedOperationalSource.lean`;
`actualReferenceObservation`, `actual_reference_states`, `rightUnitReference` @ `IndexedRankedOperationalReference.lean`.
Review every generator listed in Section 2; assembly's origin must be joined, the squares rank-free, and bracket derived.
Source equality is generated syntax, not target equality by definition; both Mathlib categories and the functor are genuine and distinct from the existing witness category.
Check actual default reference execution/full `Relation` and pending/accumulator data, not only final values. No generic reference-state transport claim.
S1 replaces joined assembly origin with opaque origin and must break source proof soundness.
Build `IndexedRankedOperationalSource IndexedRankedOperationalReference`; commit two modules/lakefile increment.

### Task 6 — connected administrative and mixed actual-history interpretation

Files: `IndexedRankedOperationalInterpretation.lean`, `IndexedRankedOperationalSemantics.lean`, incremental lakefile.
Symbols: `Frame`, `Frame.FreshInput`, `Realizes`, `successfulView`, `computeHistory`, `compute_failure`, `realizes_pre_wire`, `realizes_post_wire`, `actual_join_identity`, `Coherent`, `source_history`, `target_history`, `semantics_history` @ `IndexedRankedOperationalInterpretation.lean`; imports @ `IndexedRankedOperationalSemantics.lean`.
Review P1 closure: `Realizes.admin` actually uses `runWire`; compute lifts actual default histories with explicit whole-owned freshness, preserves outside cells and ordered prefix, and derives successful views rather than assuming success or using fallback values.
Check both mixed wire sides, strict failure, exact native-history projection and actual binary cut insertion without duplicate snapshots.
Check coherence contains only structural placement/inherited-state squares, not history equality; source/target/functor descent must reach ambient histories.
M1 drops the inherited prefix; M2 erases outside private values. Both are live-proof controls, not runtime kills.
Build `IndexedRankedOperationalInterpretation IndexedRankedOperationalSemantics`; commit two modules/lakefile increment.

### Task 7 — discriminating donors and namespace/proof acceptance

Files: `IndexedRankedOperationalTest.lean`, `IndexedRankedOperationalAudit.lean`, incremental lakefile.
Symbols: `rotateDomain`, `wireObservation`, `wireControls`, `privateReassociation`, `privateInteriorUnit`, `populatedFrame`, `populatedFrame_fresh`, `pairFrame`, `pairFrame_coherent`, `private_failure_no_output`, `emptyReassociation`, `axisReassociation` @ `IndexedRankedOperationalTest.lean`; namespace audits @ `IndexedRankedOperationalAudit.lean`.
Donors/deltas and observed values are the table below. Retain all current assertions; do not weaken failure branches or substitute output-only agreement.
Build `IndexedRankedOperationalTest IndexedRankedOperationalAudit`; run all eleven final cycles through the controller, then rebuild these targets.
Per-task review checks nine live-proof controls versus two type-valid numeric donor controls honestly, connected source realization, and nine namespace-audit outputs.
Require inhabited `pairFrame`/`FreshInput`/`Coherent` instances in the actual composite `framedDeclarations` space, including explicit `compute_history_congruence` specialization; a universal comparison in an impossible two-tensor frame is insufficient.
Commit only the two modules/lakefile increment. Canonical mutation files were committed as authoring inputs, not recreated here.

### Task 8 — discoverability and bounded capability claims

Files: `leanncd/AGENTS.md`, `papers/semantics/categorical_tensor_logic_semantics.md`, **only**.
Apply `documentation.patch` unchanged. The actual entry point is `import IndexedRankedOperationalSemantics` under the nondefault `IndexedExecutionExperiment`, not production `LeanNCD`.
Review synthesis Section 6.13 and its updated summaries/tables/appendix links, including explicit `Realizes`/fresh-frame connections; preserve old witness/associativity scope and explicit exclusions.
Run the documentation sweeps in Section 7; adjudicate stale matches without widening this slice. No heavyweight docs dispatch.
Commit explicit two paths; no Lean build required solely for prose, but the final full wrapper build is mandatory.

## 5. Donor and mutation ledger

| Donor / surgical delta | Why discriminating; observed authoring evidence | Controls |
|---|---|---|
| `Fixtures.first`, `second`, `privateFailure`; insert administrative return | Success events/states `([10], [0,1])`; failure `([10,11,99], [0,1,2], Except.error (2,7))`; shared snapshot not duplicated, failure absorbs later work | General unit/failure/transport proofs; U1 is a wire live-proof control, not a separate failure-fixture runtime kill |
| `ledgerLeft`, `ledgerRight`, `privateAvailable`; retain supplied frame | `([(101,1),(102,-1)], some 42)`; reversal/reset/private erasure differ | U2/U3/U4 live proofs |
| `emptyMetadata`, `absentEmptyMetadata`; change presence only | Same full history, unequal `Agrees`; `(0,0,1,0)` event/input-port counts | Kernel presence proof, not an independently measured runtime mutation kill |
| `IndexedComponentTransportTest` coordinate-domain donor; use 3 extent-two axes, cyclic wire, public/private cube and populated prefix | `(0,1,[(101,1),(102,-1)],some 1011,some 101)`; identity/inverse/double/cancel `(some 11,some 110,some 110,some 11)`; all variants type-valid; full `raw` Domain supplied | W1 changes forward 101 to inverse 110; W2 dropping second wire changes third control 110 to 101 |
| `consumerComponent`, `consumerRank`, `privateBoundary`, `privateCounts`; clone actual private success/failure triple | Success `(4,4,4)` has 12 events/13 states; failures A `(0,4,4)`: 3/3, B `(4,0,4)`: 7/7, C `(4,4,0)`: 11/11 | Four full-`Agrees` source instances plus existing actual-run counts; shared S1/S2/S3 proof controls, not four new runtime kills |
| Same private pair; insert identity between boundary and second leaf | `privateInteriorUnit` preserves the whole normalized operational observation for `(4,4)` | Generated unit/soundness proofs |
| Existing `view`/`rotate`; realize source identity/nonidentity wire and their composition/inverse | Actual inherited-state `runWire` witnesses, not only normalization equality | Connected administrative realization proofs |
| `consumerComponent`/`privateInput`; embed local declarations beside existing public/private cube via `framedDeclarations` | Inhabited `populatedFrame`, explicit `FreshInput`, ledger prefix `[(101,1),(102,-1)]`, outside value `1011`, exact lifted native history and actual failure without output premise | M1/M2 live-proof controls; generic realized leaf/failure checks |
| `privateComposite 4 0`; use composite-sized `pairFrame` and same-frame structural coherence | Explicit inhabited frame/freshness/coherence plus `compute_history_congruence` specialization; repairs the reviewed vacuous two-tensor donor | Parent-adjudicated additive acceptance repair; not an extra runtime kill |
| Actual private binary join; insert administrative identity at supplied boundary | `actual_join_identity` derives actual failure/success split, output view and shared cut | Connected actual-history proof, not normalized-unit parity alone |
| Empty producer/consumer, `emptyBoundary`/`emptyTailBoundary`; instantiate bracket | Full `emptyReassociation`, not address-enumeration equality | Shared source/metadata proofs |
| Axis producer/consumer, `axisBoundary`/`axisTailBoundary`, then `consumerComponent 4`; instantiate bracket | Full `axisReassociation` retains certified boundary/domain maps | Shared source/raw-map proofs |
| `hiddenUpstream`/`hidden_no_rank`, with ranked private neighbor | Negative rank certificate assertion; old unrestricted assembly not imported as operational truth | Kernel rank rejection; not a runtime/type-mismatch mutation |
| Existing `reorderedTripleRun`/`strongerThanFinalOutput`; no clone or modification | Existing order-sensitive oracle remains built; final equality cannot replace history observation | Unchanged donor, not counted as a new fixture or kill |

Exactly eleven measured cycles: W1/W2 are type-valid donor-observation controls; U1–U4/S1–S3/M1/M2 are nine live-proof controls.
Expected strings come from the canonical manifest's observed diagnostics; type mismatch/setup refusal is never counted as runtime evidence.
Every cycle must show intended diagnostics, restored-green build and byte-identical restoration. Shared proof controls are not claimed as separate mutation runs for each donor instance.

## 6. Recurring-defect sibling audit

Each per-task review records this matrix in the execution record, including whether any newly found cell was silently ignored. None may remain silently ignored in the admitted profile.

| Case × sibling functions | Required | Forbidden / explicitly outside claim |
|---|---|---|
| `returning`, `bind_done`, `failure_bind`, `splice_normalization` × success/failure | Same ordered events/states/payload; exactly one shared cut | Extra work, duplicate snapshot, failure fall-through |
| `runWire_identity/composition/inverse`, `Scope.reindex` × empty/populated/private frame | Entire inherited state and full domain maps, explicit whole presence | Reset/reversal/private erasure; identifying wires by cardinality |
| `Normal.comp` × admin/admin, admin/compute, compute/admin, compute/compute | Typed closure, mixed neutrality, exact connecting boundary | Invented computation/provenance on administrative insertion |
| `upstream_*`/`downstream_*`, `combined_metadata`, `binary_transport` × success and reached failures | Ordered prefixes, lane identity, full state/history and input square | Swapped identities, weakened failure; arbitrary-frame runner execution is explicitly outside claim |
| `inputExterior`/`outputExterior`, both boundary squares/recoveries × raw/admitted/empty | Complete certified maps and exact boundary image | Coordinate-only/raw-erasing comparisons, ignored empty tensors |
| `assembled`/`pair`, `leftNested`/`rightNested`, `ProvenanceIso.joined` × opaque/joined | Original boundaries/children; only decorated assembly | Opaque-to-joined admission, arbitrary adapter renaming |
| `actualHistory_spec`/`actual_reference_states`/`rightUnitReference` × success/A/B/C failures | Actual defaults, strict terminal failure, all full reference relations | Admissibility mistaken for execution; final-store projection |
| `Realizes.admin/compute`, mixed pre/post wires, `actual_join_identity` × success/failure | Actual admin/native histories, derived whole successful view, one shared cut | Unconnected normalized-unit claims, invented success, input substituted for output |
| `Frame.owned/outside/ledger`, `FreshInput`, `Coherent.state/event/history` × leaf/composite frames | Entire owned initial availability, outside values, prefix and inhabited structural comparison | Erased outside state/prefix, arbitrary prepopulated owned execution, contradictory/vacuous frame donor |

## 7. Controller verification and release gates

Run these commands separately with the absolute paths shown; no delegated green report substitutes for the controller's final checks.
First verify the latest local-main delta still leaves package-owned/Lean/semantics scope untouched, and safely integrate it while preserving concurrent work.
Do this **before** the final mutation/audit/full-build command block, not after declaring a frozen-base build the release build.
Use the manifest's unfiltered run; `--check` alone is not a mutation release gate.

```sh
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/papers/semantics/categorical_ranked_operational_interpretation_mutations.json
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/leanncd/scripts/mutation-manifest.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/papers/semantics/categorical_ranked_operational_interpretation_mutations.json
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/leanncd IndexedRankedOperationalInterpretation IndexedRankedOperationalSemantics IndexedRankedOperationalTest IndexedRankedOperationalAudit
rg -n 'Prototype|\bsorry\b|\badmit\b|sorryAx|^axiom |^unsafe ' --glob 'IndexedRankedOperational*.lean' --glob 'IndexedOperationalUnits.lean' --glob 'IndexedOperationalWireFrame.lean' --glob 'IndexedOperationalScopeNaturality.lean' /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/leanncd/experiments/indexed_execution
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff diff 921cca7e4c28066ae1912c398b27c351930fc18c HEAD -- leanncd/LeanNCD leanncd/experiments/indexed_execution/IndexedSourceSyntax.lean
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff diff --name-only 921cca7e4c28066ae1912c398b27c351930fc18c HEAD -- leanncd
rg -n 'process units|Process units|no .*process category|operational functor|6\.13|IndexedRankedOperationalSemantics' /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/leanncd/AGENTS.md /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/papers/semantics/categorical_tensor_logic_semantics.md
rg -n 'units remain|Units remain|Process units.*remain|no event.*process category' --glob '*.md' /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff/leanncd LeanNCD Tests IndexedExecutionExperiment
```

The audit target runs nine namespace-wide standard-axiom audits, including Interpretation, and prints category/source/reference and connected realization/join/descent proof dependencies.
Record exact results; source scans supplement, not replace, kernel audits. An empty `rg` result exits 1 and is not a build failure.
Inspect protected-path differences and the complete Lean changed-path list against package ownership: no slice-owned runner/core/witness edits are permitted; unrelated main changes must be preserved, not rolled back.
Documentation search matches in historical handoffs/records are not current capability claims. No numerical accepted-count boundary changes; grep any newly introduced count by value if found.

Before reverse cleanup and again after all eight tasks, run this read-only hash comparison:

```sh
python3 - <<'PY'
import hashlib, json
from pathlib import Path
root = Path('/Users/williammacready/code/python/pyncd.worktrees/categorical-ranked-interpretation-handoff')
art = root / 'papers/semantics/categorical_ranked_operational_interpretation_artifacts'
manifest = json.loads((art / 'package.json').read_text())
for entry in manifest['patches']:
    assert hashlib.sha256((art / entry['path']).read_bytes()).hexdigest() == entry['sha256'], entry['path']
for path, digest in manifest['sources'].items():
    assert hashlib.sha256((root / path).read_bytes()).hexdigest() == digest, path
print(len(manifest['patches']), 'patches;', len(manifest['sources']), 'byte-identical files')
PY
```

Record whole-execution equality before integration. If latest local main overlaps any package-owned file, stop and adjudicate without rewriting the frozen bytes silently.
Recheck package equality after integration; the command block above validates the integrated final candidate.
Two independent whole-branch lenses and focused follow-ups are clean: semantics/provenance/soundness closes P1 on exact reviewed bridge bytes; conservative runner/reference/acceptance is clean.
The original unchanged proof files retain their old verdicts; changed files do **not** inherit old hash approval. Interpretation proof bytes match focused review; parent adjudicated the later additive inhabited-frame test and explicit documentation clarification.
Carry those bounded verdicts through deterministic replay only for the corresponding reviewed/adjudicated bytes, verified against all fourteen current package-owned hashes. Inspect final plan/record/integration delta; any further source change requires review.
Reviewers use bounded windows, append findings incrementally to the record and adjudicate every finding; no open load-bearing issue may be called complete.
When the controller's eleven unfiltered cycles, full build and both reviews/delta are green/adjudicated, merge to local `main` without a menu.
Delete only this branch and its worktree after successful integration; do not push. Record integration hashes, preserved concurrent changes and main's remote divergence.
Disclose missing telemetry/breaches: approximately 250k peak/60 turns per dispatch, 50M authoring target and 175M execution ceiling are not measured passes without data.
