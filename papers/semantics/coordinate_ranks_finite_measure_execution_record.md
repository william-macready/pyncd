# Coordinate ranks and finite measure: execution record

## Status and scope

Executed the [verified plan](coordinate_ranks_finite_measure_plan.md) on
2026-10-08, using the **Full** path for a new proof/soundness capability.
All three implementation tasks, controller validation gates and both final
whole-branch reviews passed. The implementation is merged to local main, and
the integrated main's full build is green.
No remote push is authorized or performed.

This is the implementation record, not the
[authoring record](coordinate_ranks_finite_measure_authoring_record.md).
Prototype commits remain provenance only: implementation was replayed from
published patches onto then-current **local main**.

| Item | Actual value |
| --- | --- |
| Execution base / prepared local main | `b45603cd00846a3e69dee60d5de1f7143cff673c` |
| Execution branch | `agents/implement-execution-ready-plan` |
| Execution worktree | `/Users/williammacready/code/python/pyncd.worktrees/implement-execution-ready-plan` |
| Task 01 | `cae5040` |
| Task 02 | `35510a1` |
| Task 03 / implementation validation HEAD | `d0b0820e40ced0b4cbe7a2c2320be3c2a25e6ce4` |
| Controller session | `27187f36-757a-4226-8395-a2c5d1f50c50` |
| Session evidence directory | `/Users/williammacready/.copilot/session-state/27187f36-757a-4226-8395-a2c5d1f50c50/files` |

Only the eight plan-authorized implementation paths changed in those three
commits. The newer main's unrelated f32 changes and all planning artifacts were
preserved. This additional record is the plan-required close-out deliverable.
No protected source, settings, prototype emitter, or mutation manifest was edited.

## Preparation and independent replay checks

The existing isolated session worktree was clean but stale at `e13fd6f`.
`prepare-worktree.sh` fast-forwarded it to local main and synced the primary
checkout's warm cache: 8,101 Mathlib oleans / 8,094 sources, plus 220 project
oleans. `lake-build.sh` then refreshed `LeanNCD` using the pinned toolchain.
There was no cold Mathlib build.

Preparation unnecessarily included `--plan`; the already tracked plan was
copied byte-identically. The generated setup ledger was inspected and moved
to session storage as `coordinate-ranks-setup-ledger.md`. The subsequent gate
required empty status including untracked paths and checked protected hashes
and absence of new outputs, including dangling symlinks.

The controller's deterministic `coordinate-ranks-audit.py` independently
checked:

- All 31 evidence-protected inputs matched their SHA-256 values, before the
  first build and after all mutations.
- All four published patch/manifest hashes matched exactly.
- A disposable temporary index at original base `a2be7b9` sequentially
  checked/applied all patches and reproduced every recorded task tree and
  final candidate tree.
- A separate temporary-index replay at captured execution base `b45603c`
  supplied the descendant-specific expected blobs/modes. All eight actual
  implementation paths matched that replay; descendant whole-tree equality
  with the prototype was neither required nor claimed.
- Each real `git apply --check` ran immediately before its task's apply,
  with preceding tasks present. All three succeeded without conflicts.
- The four new modules matched the required blob IDs below, before and after
  mutation validation. No transcription or prototype cherry-pick was used.

| Artifact | Observed SHA-256 |
| --- | --- |
| Patch 01 | `b3e5ee2c527bbfa2b61e878af91d8ef531e42bd13893a04f7ea3faf7637b1e8e` |
| Patch 02 | `1c8a2151cd839ae72a1eb48784e5f7b71dcc5f1413b7371e34e6691bb815d74f` |
| Patch 03 | `e7b84cb0029430df7f83aa02c49d95d5c993daf43ea7293ae51de726757cada0` |
| Post manifest | `82fa84a0f02c453fda0aec66a8896e4da7f5fc522d7201eea4c393531794f2a1` |

| New module | Observed Git blob |
| --- | --- |
| `Ranks.lean` | `e1e401893352b100f82d8874bc20f99ca71c1f9c` |
| `Measure.lean` | `72da5e2c126f15629dd09a91e5932461e69f52f4` |
| `Progress.lean` | `eebe0604f5524dfbd727714caecc4c152c31cc32` |
| `RankedMachineTest.lean` | `3df423a85b7b6281481dd83771c57e25ff1ab266` |

Current covering guidance was measured before replay: parent injected named
sections contain 2,981 content characters (3,014 including headings); semantic
guidance has no matching injected section headings. This remains near the
approximately 3k threshold. No unrelated guidance was trimmed.

Evidence: `coordinate-ranks-preflight.json` and
`coordinate-ranks-post-audit.json` in controller session storage.

## Tasks and per-task review dispositions

The controller directly replayed and reviewed each bounded patch; no
implementation redesign or nested implementer dispatch was necessary.

| Task | Verification and per-task disposition |
| --- | --- |
| 01 | `LeanNCD.Semantics.Measure` build passed. Coordinate destination fibers, guard-admitted occurrences, unchanged strict footprints, input exclusion, all defined addresses, exact consume/publication decreases and failure trace bounds reviewed: **approved**. CR1-CR4 deliberately delayed until fixture integration. |
| 02 | `LeanNCD.Semantics.Progress` build passed. No model premise in ranked progress; reached terminal maximality; rank-independent extension; ranked dichotomy; full-store uniqueness; existing denotation reuse; schedule agreement without diagnostic independence reviewed: **approved**. CR5 delayed until integration. |
| 03 | `Semantics.RankedMachineTest LeanNCD.Semantics` build passed. Donors/discriminators, all 16 families, semantic import/default Tests wiring, bounded docs, declaration counts and proof inventories reviewed: **approved**. All six cycles subsequently executed. |

Every commit stages explicit plan paths and carries the required Copilot
co-author trailer. Targeted build logs are `coordinate-ranks-task01-build.log`,
`coordinate-ranks-task02-build.log`, and `coordinate-ranks-task03-build.log`.

### Required sibling case x class review

Reviewed unchanged `Step.contribute`, `Step.publication`, `Step.undefined`,
`consume`, `publish`, and every `footprint` constructor against new dependencies,
measure and progress. R = required, F = forbidden, I = silently ignored.

| Step | pending tag | ready some | ready none | unavailable read | unpublished cell | empty fiber | zero value | output flag | certificate | model |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| contribute | R | R | F | F | I | I | R: erase at zero | I | I | I |
| publication | F in destination fiber | I | I | I | R | R | R: publish zero | I | I | I |
| undefined | R | F | R | F | I | I | I | I | I | I |

For reachable contribution/failure, the published invariant makes the pending
tag's destination unpublished; that tag makes its fiber nonempty. Publication
evaluates no body. Every defined cell counts regardless of output status.
Rank/model are not Step or termination premises. Undefined has no value and
retains its pending tag/configuration. These justify every ignored Step cell.

| Footprint case | own edge | strict children | all binder coordinates | selected-coordinate-only | rejected valuations |
| --- | --- | --- | --- | --- | --- |
| lit | F | I: no children | I: no binder | I | F |
| iverson | F | I: value-free predicate | I: no binder | I | F |
| resolved read-at | R: source coordinate | I: no children | I: no binder | I | F |
| resolved read-const | F | I: no children | I: no binder | I | F |
| rejected read | F: no admitted witness | I | I | I | F |
| binary | F: child edges only | R: both, including zero multiplication | I: no binder | F | F |
| reduce | F: child edges only | R | R: every finite coordinate | F | F |
| tab | F: child edges only | R | R: every layout coordinate | F | F |
| at | F: child edges only | R: entire array | R: inherited tab demand | F | F |
| prim | F: child edges only | R: every typed argument | R: inherited array demand | F | F |

Leaf/no-binder/absent-constructor ignored cells have no applicable child,
binder or admitted read; selected-coordinate-only is inapplicable to these
leaves. Dependencies require an admitted occurrence in the exact destination
fiber; other fibers and rejected valuations are forbidden. Repeated source
addresses have set multiplicity ignored, not read demand erased; occurrence
tags retain multiplicity in measure. Input destinations have no edges, while
input sources remain dependencies and are initially available. No unjustified
ignored cell or required sibling correction was found.

## Fixtures, discovery, and proof observations

The actual fixture source has **49 named declarations**: 25 theorems and
24 definitions/abbreviations. All witnesses from the **16-family** coverage
table are present. The eight program construction definitions are `maskedSelf`,
`selectedP`, `boundaryP`, `reductionP`, `primitiveP`, `singletonP`, `emptyP`,
and `twoBad`; the true/false guard instances of `maskedSelf` give nine instances.

Successful Lean elaboration independently proves duplicate initial measure
5 and post-consume measure 4; scalar singleton initial measure 1 and rank 0;
zero-extent initial measure 0; and exact one-unit decreases for zero-valued
consumption, empty-fiber publication and nonoutput publication. These are
proof observations, not evaluation of a noncomputable runtime measure.

Plain `import LeanNCD.Semantics` exposes certificate, measure, well-founded
termination, both trace bounds, progress, dichotomy, singleton correspondence
and schedule-agreement symbols, verified with `lean-file.sh` after dependency
builds. Its temporary source was removed. The default full build includes
`Semantics.RankedMachineTest` without a target selector.

The actual logs verify all **31 named axiom inventories** from published
evidence: seven existing Soundness inventories, eight Measure inventories,
nine Progress inventories, and seven fixture inventories. Only `propext`,
`Classical.choice`, and `Quot.sound` occur, exactly as expected. The four
new code files contain no `sorry`, `axiom`, or `native_decide`.

Documentation/import sweeps confirm current discovery and the new boundary.
Numeric "five semantic" sweep hits were historical/unrelated descriptions
and the plan's own command, not stale current fixture counts; nothing was
widened or rewritten. Evidence: `coordinate-ranks-fixture-audit.json`,
`coordinate-ranks-validation-summary.json`, and
`coordinate-ranks-public-import.log` in session storage.

## Controller mutation and full-build validation

The controller ran the real post manifest, not merely `--check`, after all
three task commits:

```bash
bash leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/implement-execution-ready-plan/leanncd papers/semantics/coordinate_ranks_finite_measure_mutations_post.json
bash leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/.copilot/session-state/27187f36-757a-4226-8395-a2c5d1f50c50/files/coordinate_ranks_mutation_results.md /Users/williammacready/code/python/pyncd.worktrees/implement-execution-ready-plan/leanncd papers/semantics/coordinate_ranks_finite_measure_mutations_post.json
bash leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/implement-execution-ready-plan/leanncd
```

| Selected mutation | Expected proof-rejection surface matched | Cycle | Byte-identical restore | Restored build | Result |
| --- | --- | --- | --- | --- | --- |
| CR1 dependency omission | Progress argument type mismatch | yes | yes | green | PASS |
| CR2 nonstrict rank | Cannot apply certificate decrease | yes | yes | green | PASS |
| CR3 defined-address count omission | Measure unsolved goals | yes | yes | green | PASS |
| CR4 pending erasure omission | Measure simplification type mismatch | yes | yes | green | PASS |
| CR5 stopped-prefix maximality | Progress function expected | yes | yes | green | PASS |
| CR6 strict right-read omission | Readiness argument type mismatch | yes | yes | green | PASS |

**6/6 selected; 6/6 passed; none skipped.** Every populated manifest expectation
matched. Existing protected Machine/Interpret sources temporarily mutated by
CR4/CR6 were restored exactly; all 31 protected hashes were rechecked.
Committed source comparison was clean.

These are generic **kernel-proof rejections**, potentially upstream of the
fixture module, not isolated fixture or runtime-oracle kills. No claim that all
16 families were independently mutation-tested is made.

The controller's default full build passed: **8,699 jobs**.
It reported **17 warnings**, including **three new unused-simp warnings** in
`boundary_no_edge` (two) and `distinct_first_failures` (one). Targeted fixture
build reported six warnings. The other 14 full-build warnings are inherited
section-variable/simp/class-attribute warnings and existing unrelated sorry
warnings. Exact replay retains the disclosed fixture warnings; the build is
green, not warning-free.

Evidence: `coordinate_ranks_mutation_results.md`,
`coordinate-ranks-mutation-run.log`, and `coordinate-ranks-full-build.log`
in controller session storage. Raw/transient validation logs are not committed.

## Final reviews, budgets, limitations, and integration

Two final whole-branch reviewers were dispatched with distinct lenses:

| Lens | Agent | Disposition |
| --- | --- | --- |
| Semantic/proof contracts | `001212a8-6dbc-40dd-9d9d-25f2f95e60a1` | APPROVE: all eight paths; no actionable high-confidence defects |
| Replay/fixture/process safety | `fc55fed1-741d-432a-a138-eabc7e4615d2` | APPROVE: all eight paths; no actionable replay/fixture/discovery/process defects |

Incremental reports live in session storage as
`coordinate-ranks-proof-review.txt` and `coordinate-ranks-replay-review.txt`.
Both reviewers approved implementation HEAD `d0b0820`. Neither changed sources,
reran controller gates, or dispatched nested agents. Disclosed fixture warnings
were non-blocking; no finding required adjudication or a source fix. The
execution record itself was finalized by the controller after their review.

The repository token reporter was invoked for the Copilot session and returned
`no transcript for session 27187f36-757a-4226-8395-a2c5d1f50c50`. Cumulative
input tokens, context peak and complete execution-turn telemetry are
**unavailable**; compliance with the approximate 175M execution budget is not
certified. Review briefs cap dispatches at approximately 60 turns / 250k
peak, target 30 turns, and require reporting any observed breach. The proof
reviewer reported 13 assistant turns and all read windows at most 60 lines.
The replay reviewer reported 14 tool-call rounds and one accidental 62-line
read, a two-line reading-window breach, with no observed turn-budget breach.
Neither had exact peak-token telemetry. These reports do not certify cumulative
execution-token compliance.

Retained limitations: relations/proofs are noncomputable, with no executable
scheduler, source/rank checker, rank synthesis or graph-acyclicity equivalence.
Unranked blocking and schedule-dependent first failures remain intentional.
There is representative array-primitive demand coverage, not a separate
fixture for every heterogeneous operand position. Strict typed footprint is
unchanged. No backend/source/float refactor, runtime oracle, new proof escape,
or unrelated cleanup was introduced.

Local integration completed without conflicts:
`fefd8628066265e29d9ffddc10cd48a051a1c69e` merges the implementation branch into
local main. Main was clean, the branch was a merged ancestor, and the merge and
topic trees were identical before this integration-result documentation update.
The controller also ran the full build in the primary checkout after merging:
**8,699 jobs passed**, recorded in `coordinate-ranks-integrated-main-build.log`.

Final cleanup is limited to this execution branch/worktree. Its pre-removal
status was clean; the only ignored path was the preparation/build-owned
`leanncd/.lake/` cache. The final cleanup/clean-main result is retained in
controller session storage as `coordinate-ranks-integration.json`.
No unrelated branch or worktree is selected for removal. No remote push.
