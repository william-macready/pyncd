# Ranked operational → complete-witness comparison: implementation plan

**Process: Full** — new categorical capability and quotient soundness surface.
**Execution: PENDING.** Compiled authoring prototypes are present, not executed
task commits or completed final review. Controller owns those gates next.
Base: `37500cab85a2989a1422da2ef21256cb5648e8da`.

## 1. Contract and frozen package

Implement the existing handoff's directed comparison, not another source-only
interpretation or output relation:

- Existing operational TARGET quotient → existing full witness-span category:
  actual functor, well-defined on all agreement cases, identity/binary
  composition, graph/inverse/composed wires, original boundaries and exteriors.
- Derive completion iff model, failure iff no model, ranked at-most-one and
  injective left leg. No supplied success, existence, uniqueness or execution
  agreement premise. Rank permits strict failure; it is not totality.
- Preserve every component-owned complete private store and both span legs.
  Input rebasing uses the inverse exterior, output rebasing the forward map.
- Explicit erasure between DISTINCT source categories, every ranked generating
  relation checked, actual functor-equality diagram; no quotient identification.
- Actual default checked/reference completion, full `Relation`, availability at
  every address, exact reference final store, domain/failure complements and
  conditional exact span values. Wires need no fictional core execution.
- Retain metadata and empty whole-input presence; no cardinality/name matching.
  Rank/origin independence is only of the witness image, not operational arrows.

Hypotheses: `σ : Declarations Unit`, `Fintype σ.Tensor`,
`DecidableEq σ.Tensor`, `A : MatchedComponent σ`, its program rank certificate,
and validated `A.program.Input` for per-input claims. The supplied match is
`A.matched`. `model_of_available` does not need rank. Actual execution uses the
existing default schedules/budgets, unchanged.

Information intentionally lost: event order, intermediate histories/stores and
ledger prefixes, failure tags/diagnostics and assembly provenance. Failed
fibers are empty, not zero-success. Witnesses contain owned stores, not an
inherited outside frame. Existing `Realizes`, `FreshInput`, structural
`Coherent` frames and reference transports are unchanged.

Excluded: frontend/backend or numerical refinement; bialgebraic pilot;
St/Br/monoidal/PROP or broader interfaces; solver/model search; new runner/core
operators, observation quotients or scheduler laws; arbitrary prepopulated
private-store execution; generic cross-program reference-state transport;
unranked extension, totality, faithfulness, inverse/equivalence or history
reconstruction; re-proving existing category/gluing laws. No `reorderedTripleRun`
comparison instance: that graph-only donor lacks a component match.

Package paths (relative to repository root):

- `papers/semantics/categorical_operational_witness_comparison_artifacts/`
  (patches 01–03, `evidence.json`, generator and logs).
- `papers/semantics/categorical_operational_witness_comparison_stage2_artifacts/`
  (04–06, `evidence.json`, generator and logs).
- `papers/semantics/categorical_operational_witness_comparison_acceptance_artifacts/`
  (07–09, `evidence.json`, generator and logs).
- `papers/semantics/categorical_operational_witness_comparison_post_artifacts/`
  (10–11, `package-evidence.json`, measured controls/audits, replay helper).
- `papers/semantics/categorical_operational_witness_comparison_mutations_post.json`
  (all 12 measured controls; no pre-code mutations).
- `papers/semantics/categorical_operational_witness_comparison_record.md`
  (authoring evidence and pending execution ledger; keep this plan live/short).

`replay-manifest.json` in the post directory is the exact hash/ownership index:
base and final SHA256 for all 17 owned files, each patch SHA256 and per-step
before/after hashes, exact patch paths, targets and ordered dependencies, plus
historical evidence/script/log hashes. `ordered-replay-evidence.json` records
actual git check/apply, reverse and forward in its disposable project-local
tree and byte equality to the compiled sources/docs. Do not regenerate 01–10
with their historical generators against this later tree.

## 2. Controller/implementer preamble and task schedule

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn/context budget and
> disclose any breach.

Use the prepared warm worktree, preserving unrelated work. Read only 40–60
lines around the identifier locators below; do not whole-file-read proofs.
Apply frozen patches, do not transcribe Lean blocks from prose. This plan has
no Lean code snippets. Keep compiled code unchanged unless a real finding
requires an explicitly verified replacement package.

File aliases below are exact prefix expansions, not omitted ownership:
`E = leanncd/experiments/indexed_execution/`,
`L = leanncd/lakefile.toml`, `A = leanncd/AGENTS.md`,
`M = papers/semantics/categorical_operational_witness_comparison_mutations_post.json`,
`D = papers/semantics/categorical_tensor_logic_semantics.md`.
Module targets are exact filenames without `.lean`.

Each task depends on **every preceding patch**, transitively through task N−1:
shared lakefile hunks require this serial replay even where theorem work is
independent. Review at these boundaries; group dispatches 01–03, 04–06,
07–09, then 10 (three work items: controls, audits, packaging).
11 is a documentation sweep, not a heavyweight dispatch.

| Task / exact patch basename | Exact Files (expanded via aliases) | Target(s) / acceptance |
| --- | --- | --- |
| 01 `01-IndexedRankedWitnessBridge.patch` | E`IndexedRankedWitnessBridge.lean`, L | `IndexedRankedWitnessBridge`; derived model/domain/uniqueness |
| 02 `02-IndexedRankedWitnessDescent.patch` | E`IndexedRankedWitnessDescent.lean`, L | `IndexedRankedWitnessDescent`; all-input full-store bijection and both legs |
| 03 `03-IndexedRankedWitnessAudit.patch` | E`IndexedRankedWitnessAudit.lean` | `IndexedRankedWitnessBridge IndexedRankedWitnessDescent`; single-file audit below, 15 signatures / 11 named queries |
| 04 `04-IndexedRankedWitnessComparison.patch` | E`IndexedRankedWitnessComparison.lean`, L | `IndexedRankedWitnessComparison`; genuine target functor and actual composition |
| 05 `05-IndexedRankedWitnessSource.patch` | E`IndexedRankedWitnessSource.lean`, L | `IndexedRankedWitnessSource`; erasure, every relation, actual functor equality |
| 06 `06-IndexedRankedWitnessOutcomes.patch` | E`IndexedRankedWitnessOutcomes.lean`, E`IndexedRankedWitnessStage2Audit.lean`, L | `IndexedRankedWitnessOutcomes`; actual runners/full model, stage audit 18 signatures / 14 named queries |
| 07 `07-IndexedRankedWitnessOutcomeTest.patch` | E`IndexedRankedWitnessOutcomeTest.lean`, L | `IndexedRankedWitnessOutcomeTest`; acceptance families 1–2 |
| 08 `08-IndexedRankedWitnessCategoryTest.patch` | E`IndexedRankedWitnessCategoryTest.lean`, L | `IndexedRankedWitnessCategoryTest`; families 3–5 |
| 09 `09-IndexedRankedWitnessBoundaryTest.patch` | E`IndexedRankedWitnessBoundaryTest.lean`, E`IndexedRankedWitnessSemantics.lean`, L | `IndexedRankedWitnessBoundaryTest IndexedRankedWitnessSemantics`; families 6–7, public API import (no tests) |
| 10 `10-controls-and-namespace-audit.patch` | E`IndexedRankedWitnessControlTest.lean`, E`IndexedRankedWitnessNamespaceAudit.lean`, L, A, M | `IndexedRankedWitnessControlTest IndexedRankedWitnessNamespaceAudit`; all 12 cycles, 9 namespaces / 124 constants, discoverability |
| 11 `11-synthesis.patch` | D | Documentation consistency/value sweep; no Lean target or new control |

Do not refactor A: patch10 already updates its discoverability entry.
Registrations remain only in nondefault `IndexedExecutionExperiment`;
default imports/production source/category/equality definitions stay unchanged.
API entry point: E`IndexedRankedWitnessSemantics.lean`. Keep tiny signature
audits with their proof tasks, not separate implementer dispatches.

### Identifier @ path brief locators

All filenames in this list expand with E; these are locators, not source
proofs reproduced by the author.

- 01: `complete_iff_model`, `failed_iff_no_model`, `ranked_atMostOne`,
  `complete_iff_admInput`, `model_available`, `model_of_available`,
  `component_left_injective` @ `IndexedRankedWitnessBridge.lean`.
  Donors: `Correspondence.completed_model`, `Correspondence.failed_has_no_model`
  @ `IndexedCompositionValidated.lean`;
  `ranked_default_terminal` @ `IndexedComponentExecutionRuns.lean`.
- 02: `observation_model_transport`, `witnessMap_store`, `witnessMap_left`,
  `compute_iso`, `agrees_iso`, `source_denote`, `arrowHom_mk`
  @ `IndexedRankedWitnessDescent.lean`.
  Neighbors: `ComputeAgrees`, `Agrees` @ `IndexedRankedOperationalCategory.lean`;
  `SpanIso.rebaseGraphs` @ `IndexedWitnessComposition.lean`.
- 04: `source_comp`, `comparison`, `comparison_admin`,
  `comparison_wire_inverse`, `comparison_rank_origin_independent`
  @ `IndexedRankedWitnessComparison.lean`;
  `composition_hom`, `compositeWiredIso` @ `IndexedWitnessComposition.lean`.
- 05: `eraseTerm`, `erase_rel`, `erase`, `normalize_denote`, `diagram`
  @ `IndexedRankedWitnessSource.lean`;
  `Rel` @ `IndexedRankedOperationalSource.lean` and `IndexedSourceSyntax.lean`.
- 06: `actual_correspondence`, `model_iff_actual_full`, `domain_iff_checked`,
  `domain_iff_reference`, `checked_failed_iff_no_domain`,
  `reference_failed_iff_no_domain`, `checked_success_value`,
  `reference_success_value` @ `IndexedRankedWitnessOutcomes.lean`.
- 07: `strict_private_no_witness`, `private_success_full`,
  `private_reference_value`, `pair_success_full`, `failure_A`, `failure_B`,
  `failure_C`, `leafRow` @ `IndexedRankedWitnessOutcomeTest.lean`.
- 08: `wireImageRow`, `binary_exterior`, `binary_composition`, `interior_unit`,
  `left_nested_exterior`, `right_nested_exterior`, `route_diagram`, `rank_image`,
  `operational_origins_distinct`, `origins_same_full_image`
  @ `IndexedRankedWitnessCategoryTest.lean`.
- 09: `empty_metadata_distinct`, `empty_input_present`, `empty_diagram`,
  `hidden_full_not_outputs`, `no_hidden_ranked_extension`, `emptyPresenceRow`,
  `hiddenStoreRow` @ `IndexedRankedWitnessBoundaryTest.lean`.
- 10: `strictFailureRow`, `exterior_legs`
  @ `IndexedRankedWitnessControlTest.lean`;
  `IndexedRankedWitnessNamespaceAudit.lean` is the all-nine namespace audit
  driver (not a tenth theorem namespace).

## 3. Acceptance, donors/deltas and sibling audit

Counts below are **goal families**, not invented counts of independent
evaluators or theorem assertions. Concrete observed rows and diagnostics are
in the receipts, logs and manifest; triple final-store/reference-cut rows
were observations, not independently pinned assertions.

| Family / task | Donor → delta and nearest legal neighbor | Measured controls |
| --- | --- | --- |
| 1 strict failure / 07 | Clone `consumerComponent 4` with `privateInput`, change private primitive profile to 0; visible output remains before private failure. Clone total `(4,4,4)` actual leftBracket, change exactly A/B/C to 0: `(0,4,4)/(4,0,4)/(4,4,0)`. Neighbor: all 4 with legal `consumerRank`. | P01 executable donor substitution; P02 live-proof failed-domain polarity |
| 2 full private store / 07 | Reuse total `privateRows`/`privateReferenceCuts` leaf and actual pair; instantiate complete-store/value APIs at every address and both rebased legs. Neighbor: same total donor with every private cell retained, not output reconstruction. | P03 live-proof boundary-retaining/private-zeroing claim; P05 independent input leg |
| 3 wires / 08 | Clone identity graph, substitute certified `rotate`, inverse and twice on nonconstant coordinates. Neighbor: identity; observed `(11,101,110,110)` separates directions. | P04 decidable forward/inverse row; P05 live-proof input reversal holding output correct |
| 4 composition / 08 | Reuse actual `privateLeft`, `privateRight`, `privateReassociation`, `privateInteriorUnit`; instantiate binary/nested image equations and original exterior chains. Neighbor: same components with interior identity, or distinct identity/rotate factors rather than repeated equal factors. | P05 exterior law; P06 actual source diagram/composition live-proof control |
| 5 information loss / 08 | Clone `consumerRank 4`, shift it pointwise (still legal, differs at consumerPre); reuse `privateComposite 4 4`, switch opaque/joined origin only. Neighbor: same witness image; operational origins still unequal by `opaque_not_joined`. | P07 image independence; P08 forbid reflected provenance equality; both live-proof |
| 6 empty metadata / 09 | Reuse empty producer/component/source donors; change `some empty tensor` to missing input, and compare distinct singleton-environment metadata objects. Neighbor: present empty input succeeds; both carriers singleton without identifying objects. | P09 decidable presence row; P10 metadata and P06 diagram live-proof |
| 7 hidden multiplicity / 09 | Reuse `hiddenZero`/`hiddenOne`, change only private hidden value 0→1 with output still 0; retain `hidden_no_rank`. Neighbor: legal consumer/shifted ranks, never an illegal hidden operational arrow. | P11 distinct full witnesses; P12 forbid rank extension; both live-proof |

Case × class audit of siblings invisible to a task diff:

| Case / siblings | Required | Forbidden | Silently ignored? |
| --- | --- | --- | --- |
| `Agrees` admin/admin; mixed; compute/compute | wire equality; mixed false; exact existing `ComputeAgrees` with fixed all-input transport/raw squares | weakening operational equality or choosing input-specific transport | No agreement constructor omitted (`agrees_iso`) |
| `Normal.source`; comparison graph/compute | retain wires/component; whole-store rebasing | output-only apex or dropped private addresses | rank/origin intentionally forgotten only in image |
| ranked source `Rel` siblings | refl/symm/trans, seq congruence, units, assoc, wire identity/composition/inverses, assembly, both nested exterior squares | identifying distinct source quotients or asserting converse | old unrestricted bracket relation not required in erasure direction |
| checked/reference domain/failure/value APIs | both actual defaults, every-address equality/full relation | success premise in unconditional domain iff; failed zero witness | outside frame/history diagnostics intentionally absent from witness target |
| empty/hidden neighbors | presence/metadata, distinct private witnesses, no hidden rank | carrier-cardinality identification/unranked generalization | no manufactured operational representative |

No locator/index/check-order or diagnostic-priority feature is added.
Orientation and payload distinctions are pinned by the nonconstant wire row,
full-store conjunctions and independent P05 input reversal, not coinciding
identity exteriors. `expect` strings are copied from actual mutated failures.
P01's initial stuck kernel reduction is NOT a certified runtime kill.

### Risk and cycle budget

| Tasks | Fixture-family count | New cycles at task | Risk / execution budget |
| --- | --- | --- | --- |
| 01–03 | 0 concrete acceptance families | 0 | high: derived uniqueness/descent, full-store inverses and legs; audit with proofs |
| 04–06 | 0 concrete acceptance families | 0 | high: real composition, distinct-source diagram, actual reference outcomes |
| 07 | 2 donor families | 0 (3 controls at 10) | strict versus total/private data; no new interpreter |
| 08 | 3 donor families | 0 (5 controls at 10) | coordinate direction, nested exteriors and intentional nonfaithfulness |
| 09 | 2 donor families | 0 (4 controls at 10) | empty metadata/presence and negative unranked boundary |
| 10 | reuses all 7; 0 new concrete instances | 12 | 3 executable/decidable observations + 9 live-proof controls; 2 new universal law controls and 1 executable assertion |
| 11 | 0 | 0 | docs only; no housekeeping bundled with mathematical claims |

Manifest legacy `"task": "1"/"2"/"3"` means outcome/category/boundary control
groups, NOT plan tasks 01/02/03. Run it unfiltered after 10.
Each dispatch ≤~60 turns / ≤~250k peak context; ~3 work items maximum.
If a finding requires more, split production from fixtures/cycles using
`.claude/skills/slice-plan/split-handoff-template.md`; do not grow the dispatch.
Execution total ≤~175M cumulative input; authoring target ~50M. Telemetry was
unavailable; stage2 may have slightly exceeded its 55-turn cap. See record.

## 4. Exact controller commands and remaining gates

Run each line separately from this worktree. `reverse` validates final hashes,
preflights the entire scratch replay, then reverses ONLY owned patches 11→01.
It preserves plans, package, logs and unrelated files; no reset/checkout/clean.
Stop on drift rather than overwrite another edit. Stage explicit task paths
from the ownership table/manifest; never stage `.claude/settings.json`.

```text
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py audit
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py replay
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py reverse
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py forward 1
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py forward 2
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py forward 3
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py forward 4
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py forward 5
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py forward 6
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py forward 7
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py forward 8
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py forward 9
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py forward 10
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py forward 11
```

Between forwards, use the task's exact targets with the build wrapper; run
the two unregistered signature audits with the single-file wrapper:

```text
bash /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd/scripts/lean-file.sh /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd experiments/indexed_execution/IndexedRankedWitnessAudit.lean
bash /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd/scripts/lean-file.sh /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd experiments/indexed_execution/IndexedRankedWitnessStage2Audit.lean
bash /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/controller-mutations.md /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_mutations_post.json
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py audit
bash /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd IndexedRankedWitnessControlTest IndexedRankedWitnessNamespaceAudit
python3 /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_operational_witness_comparison_post_artifacts/package_replay.py source-audit
bash /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/leanncd LeanNCD Tests IndexedExecutionExperiment
rg -n 'Connect the denotational|next main milestone|alongside the comparison|all four directions|all three directions|6\.14|comparison|ranked_atMostOne' /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness/papers/semantics/categorical_tensor_logic_semantics.md
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/follow-directions-categorical-witness diff --check
```

Require 12/12 intended-diagnostic cycles, byte-identical restored sources and
green restored builds, not merely `--check`. In namespace build output require
all nine named namespaces from `package-evidence.json`, descendants included,
124 constants using only `propext`, `Classical.choice`, `Quot.sound` (subsets
allowed); reject `sorryAx`. `source-audit` scans all 13 sources and verifies no
default imports/config changed. Re-run full build and audits after any fix.

Two DISTINCT final whole-branch review lenses, after task reviews:

1. **Mathematical/quotient soundness:** arbitrary representatives, full witness
   bijections and inverse laws, both exterior legs, actual composition,
   distinct-source erasure/diagram and exact domain/uniqueness hypotheses.
2. **Operational/integration and adversarial acceptance:** actual graph/reference
   defaults, strict private failure, full private store, metadata/presence,
   nonconstant wire orientation, provenance loss without reflected equality,
   negative unranked boundary, and honest executable versus live-proof controls.

Reviewers use the locators/windows above, append findings incrementally to the
record, check headroom before starting; one bounded fix group per finding group.
No final review was performed in authoring. Controller records actual gates,
adjudication and measured budget (or unavailable telemetry), then integrates
locally only when green/reviewed. Preserve concurrent main work, delete only
the owned branch/worktree, do not push. Stop for a load-bearing blocker; never
substitute output-only meaning or silently weaken operational equality.
