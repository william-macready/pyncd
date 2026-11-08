# Witness-preserving categorical semantics: verified execution plan

**Process: Full — new denotational capability and soundness surface.**
This is the second, artifact-only authoring phase. Execute the seven frozen
patches, not a transcription of their Lean code. Prototype verification is
complete; controller replay, direct reviews and local integration are pending.
Historical receipts and accounting live in
`categorical_witness_semantics_plan_record.md`.

## 1. Frozen inputs and release contract

- Controller: `/Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup`.
- Owned detached prototype: `/Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-prototype`.
- Primary checkout: `/Users/williammacready/code/python/pyncd`.
- Base: `a9c9a647a04e260e21c8e5c624a0bac3fa13ef20`.
- Compiled source HEAD: `0e49e37020b848d9a88da1daa7b95b5eef8260a7`.
- Compiled source tree: `ac03d2b330b355cc4632a2f3371e11f2081d81fd`.
- Authoritative package: `categorical_witness_semantics_artifacts/package.json`;
  patch paths below are relative to that artifact directory.
- Package records patch SHA-256, every changed file's intermediate SHA-256,
  source commits and exact build targets. Do not regenerate or edit the package,
  patches, copied bodies, scripts or populated mutation manifest during replay.
- Controller reports latest local-main alignment after non-overlapping scan
  changes. The replay guard, not an assumption about branch names, decides
  whether this checkout is eligible. Stop on a guard failure; do not bypass it.

Plain separate shell commands only, absolute paths, no shell-variable
expansion, no pipelines into git. Shell git commands use `/usr/bin/git -C`.
Build only through `bash <checkout>/leanncd/scripts/lake-build.sh
<checkout>/leanncd [targets]`. Never run Lake from the repository root.
Stage explicit paths only; never stage or commit `.claude/settings.json`.
Protect every other worktree and all pre-existing edits. The primary
`papers/semantics/README.md` protected SHA-256 is
`467f94f6890675822e3972fc72d8d79ebdf3f661d48cdb7f5449606f4f568f25`.
Record hashes of other protected edits before integration; compare afterward.

No repetitive implementer dispatches: the package applies already compiled
bytes. The controller directly reviews each task's actual code and tests,
using `rg -n` and Read/view windows of roughly 40–60 lines at named symbols.
Never substitute `source_hashes: pass` or the script's
`controller_review: exact frozen bytes` label for a substantive review.

## 2. Exact semantic scope and invariants

Objects are `WholeInterface : Type 1`: port-only tensor identity, injective
UID, sort/full axes and exhaustive duplicate-free whole-port roster.
Empty tensors remain ports. Equal environment cardinality, names or extents
do not identify objects. `Env`, complete stores and concrete apexes are
`Type 0`; quantification over arbitrary `Type 0` apexes puts quotient homs
in `Type 1`. The checked ordinary instance is `Category.{1}`, not a
same-universe locally-small claim or enumeration of rational models.

Arrows are spans `Env X ← W → Env Y` modulo `SpanIso`: an apex equivalence
commuting with **both** legs. Pullback composition retains compatible witness
pairs. Identity has apex `Env X` and both legs identity. Setoid, pullback
congruence, left/right units and associativity descend to quotient homs.
Raw nested dependent pairs need not be equal.

`componentSpan` ranges over **all** validated inputs η and every whole store
ρ satisfying the authoritative `Program.Models RationalReference.ops η ρ`.
Proof terms do not create multiplicity; distinct complete private stores do.
The left leg uses `inputEquiv`; the right uses `outputEquiv` and
`outputProjection`. Retain body-definedness and complete equations, not just
outputs, successful runs, reachable stores, or an existential output relation.

`boundaryEnvEquiv` explicitly sends upstream output to downstream input,
using `Boundary.matched` and certified coordinate maps in their stated
direction. Graph spans are administrative semantic wires. Exterior
`compositeInputEquiv`/`compositeOutputEquiv` rebase endpoints; tagged composite
interfaces are not definitionally their original interfaces.
`allInputWiredEquiv` lifts `witnessesEquiv` over η.
`compositeWiredIso` proves both outer-leg commutations, not just a bijection.

For actual nested source composites, derive both typed nested boundaries.
Both bracket spans pass through the **same** `CompatibleTriple`, retaining
all three complete stores and both AB/BC equations. Prove adapter squares and
both outer legs. Fresh private IDs may differ; preserve provenance rather
than requiring raw program or UID equality.

`component_injective_iff` is `AtMostOneModels ↔ injective left leg`.
No existence follows. Restricted partial maps use existential witness domain,
unique value on that domain, and `none` for absence. Identity, graphs and
pullbacks preserve injectivity; quotient invariance and domain/value laws
connect to `admInput_restrictions_iff` and `denotation_successive` under
**both** component hypotheses. Downstream selection forbids unrestricted
unique-model extraction from arbitrary spans.

No source `Category`/functor or event-exact identity is delivered.
Core `output_defined` forbids input aliases; a copy adds work/events.
Source equations and denotational isomorphisms are not runtime/event laws.
Excluded: rank stitching, runtime phase/trace projection, event-sensitive
process-category laws, numerical/backend refinement, general St/Br/PROP
interpretations, wider interfaces, automatic leaf matching, old coverage or
accounting repairs, core-language/runners/registry changes.

## 3. Task risk and evidence map

Counts are scenario families, not theorem counts or invented scalar runs.
Generic controls quantify universally; their numeric fixture count is zero.
All ten executable cycles belong to task 6 and **new** `_post` code.
No fabricated empty pre-code mutation manifest is needed.

| Task | Numeric/scenario fixture count and exact donor delta | Mutation cycles | Risk/direct review |
| --- | --- | --- | --- |
| 1 | 2 donor scenarios: `emptyProducerComponent` → tensor-level empty input presence; `hiddenUpstream` → two complete stores with equal projected output. 0 numeric fixtures for generic category laws. | 0 here | Metadata, universe, quotient congruence, both units and associativity. |
| 2 | 0 new numeric fixtures; universally quantified boundary inverse, graph identity/composition, all-input inverse and both `compositeWiredIso` legs. | 0 here | Direction, dependent η inverse and exterior transports. |
| 3 | 0 numeric fixtures; universal nested boundary squares, `leftTripleIso`, `rightTripleIso`, `bracketSpanIso`, `bracket_hom`. Concrete triple deferred to task 5. | 0 here | Same compatible full-model triple, not unrelated apex bijections. |
| 4 | 3 donor scenarios: `strict_no_model`/`strict_no_composite` → empty span domain and `none`; `total_composite_model` → populated domain; cyclic zero/one and `cycle_composite_unique` → selection counterexample. | 0 here | At-most-one without existence; restricted quotient/domain/value laws. |
| 5 | 6 scenarios in 3 workitems: strict, total, hidden, empty, axis, triple. Promote existing models to all-input witnesses; extend shaped copy donor twice by +10/+20 for the triple. | 0 here | Nonconstant boundaries, input cells, actual bracket iso and private stores. |
| 6 | 5 donor families `Hidden/Audit/Empty/Axis/Triple`, plus 1 positive singleton extraction control; 7 universal exact-body `rfl` parities (0 numeric fixtures). | 10: 6 copied-map + 4 donor controls | Independent observations, valid typed mutations, isolation from Parity. |
| 7 | 0 numeric fixtures; aggregate/import, nondefault globs and documentation scope checks. | 0 new; final rerun covers all 10 | Discoverability without default-production promotion or process overclaim. |

No existing recurring core defect is being repaired: the sibling audit is the
following new-surface contract, not a rationale to widen scope.

| Surface / sibling checks | Required | Forbidden | Silently ignored |
| --- | --- | --- | --- |
| `roleInterface`, `envInput`, `inputEquiv`, `outputEquiv` | Whole ports, identity/sort/axes, empty binding presence | Object equality inferred from Env size | None permitted |
| `componentSpan`, `toWired`, `allInputWiredEquiv` | All η, complete Models, private stores | Success-only/output-only witness filter | Proof identity only, intentionally irrelevant |
| `boundaryEnvEquiv`, exterior adapters, nested squares | Certified direction, both legs | Flattening by cardinality; numerical-ID coincidence | None permitted |
| `SpanIso.pullback`, units, assoc; both triple isos | Compatibility, congruence, common triple | Raw nested-pair equality as category law | Equality-proof identity only |
| Restricted extraction and `component_*`/`wired_*` laws | Injectivity, occupied domain, both hypotheses | Zero/default witness; arbitrary-span unique extraction | None permitted |

## 4. Seven executable patch groups

Files are repository-relative and exactly the package's per-task file lists.
Symbols are identifiers at those files; namespace for semantic declarations
is `IndexedWitness`. Review existing prerequisites named in the handoff only
where a changed proof depends on them, not an unrelated source survey.

### Task 1 — metadata, span category and controls

Patch `patches/task-1.patch`; source commit
`3fc437a28834d614ca730caaa78c1026c658efd0`.
Files:
- `leanncd/experiments/indexed_execution/IndexedWitnessInterface.lean`
- `leanncd/experiments/indexed_execution/IndexedWitnessSpan.lean`
- `leanncd/experiments/indexed_execution/IndexedWitnessTest.lean`
- `leanncd/lakefile.toml`

Read `WholeInterface`, `roleInterface`, `envInput`, `inputEquiv`, `outputEquiv`
at Interface; `Span`, `SpanIso`, `spanSetoid`, `WitnessHom`, `Span.pullback`,
`SpanIso.pullback/leftUnit/rightUnit/assoc`, `homComp`, `componentSpan` at Span;
category/empty/multiplicity checks at Test. Confirm exact universe and
complete witness apex. Targets: `IndexedWitnessInterface IndexedWitnessSpan
IndexedWitnessTest`.

### Task 2 — explicit boundary and all-input comparison

Patch `patches/task-2.patch`; source commit
`c71ee3d31cd44a139c8541cd1f2e710634e21fea`.
Files:
- `leanncd/experiments/indexed_execution/IndexedWitnessComposition.lean`
- `leanncd/experiments/indexed_execution/IndexedWitnessTest.lean`
- `leanncd/lakefile.toml`

Read `boundaryEnvEquiv`, `boundaryEnv_apply`, `Span.graph`, `graphHom_identity`,
`graphHom_comp`, `Span.rebase`, `compositeInputEquiv`, `compositeOutputEquiv`,
`toWired`, `fromWired`, both inverse proofs, `allInputWiredEquiv`,
`compositeWiredIso`, `composition_hom` at Composition. Confirm the dependent
inverse uses the actual indexed complete-model equivalence and compatibility;
both exterior legs commute for arbitrary η. Targets:
`IndexedWitnessComposition IndexedWitnessTest`.

### Task 3 — actual nested source bracket spans

Patch `patches/task-3.patch`; source commit
`451a5bb56c5eb0d158fcdd33def74f48478bea58`.
Files:
- `leanncd/experiments/indexed_execution/IndexedWitnessCoherence.lean`
- `leanncd/experiments/indexed_execution/IndexedWitnessCoherenceTest.lean`
- `leanncd/lakefile.toml`

Read `leftNestedBoundary`, `rightNestedBoundary`, both boundary squares,
`leftBracketSpan`, `rightBracketSpan`, `CompatibleTriple`, `tripleSpan`,
`leftTripleEquiv`, `rightTripleEquiv`, both triple isos, `bracketSpanIso`,
`bracket_hom` at Coherence; generic leg/audit checks at CoherenceTest.
Require one common triple with the original certified AB/BC maps.
Targets: `IndexedWitnessCoherence IndexedWitnessCoherenceTest`.

### Task 4 — restricted partial maps and authoritative connection

Patch `patches/task-4.patch`; source commit
`0a3b8e97854dbf7c46daa9b08378eb1d2cbf635b`.
Files:
- `leanncd/experiments/indexed_execution/IndexedWitnessPartial.lean`
- `leanncd/experiments/indexed_execution/IndexedWitnessPartialTest.lean`

Read `Span.Domain/value/partialOption`, `RestrictedSpan`,
`RestrictedHom.partialOption`, `SpanIso.injective_left_iff/domain_iff/value_eq`,
`Span.pullback_injective/pullback_domain_iff/pullback_value`,
`component_injective_iff/domain_iff/value`, `wired_domain_iff/value`,
`component_composite_domain/value` at Partial. Read
`strict_consumer_undefined`, `downstream_selection_not_unrestricted` at
PartialTest. Targets: `IndexedWitnessPartial IndexedWitnessPartialTest`.

### Task 5 — six discriminating actual scenarios

Patch `patches/task-5.patch`; source commit
`2cbf39e97386e3c57d627e869ae922c46e7edb00`.
File: `leanncd/experiments/indexed_execution/IndexedWitnessCompositionTest.lean`.
Read namespaces `Audit`, `Hidden`, `Empty`, `Axis`, `Triple` at that file.
Exact donors and construction deltas are in task 5's record; observations:

- Strict: no complete span/pullback witness at any input. Total donor:
  actual private audit `1/2`, final output `0`.
- Hidden: actual upstream private cells `0/1`; final cells both `1`;
  whole final environments equal, wired witnesses distinct.
- Empty: required composite output port present, UID `3`, axes `[⟨51,0⟩]`;
  singleton Env does not identify producer metadata (UID `0`).
- Axis: `axisProducer/axisConsumer/axisBoundary`, geometry models and
  `swapDomain` donor. Forward cells at p/q `5/2`, flattening `3/4`,
  well-typed reverse-style control `4/3`; final `14` alone masks the error.
  Its original input is empty, so do not use it as a nonconstant input test.
- Triple: clone shaped producer/read-match patterns into
  `copyComponent false/true`: A UIDs `40/41`, shape `2×3`, +10;
  B UIDs `70/71`, shape `3×2`, +20; unchanged `axisConsumer` is C.
  AB uses typed inverse `reverseDomain`, BC `swapDomain`.
  Inputs `5/2`; AB `15/12` vs wrong `14/13`;
  BC `35/32` vs wrong `33/34`; final `134`.
  Nested squares observe `35` and `15`. Actually applied bracket iso
  returns the right witness and then the complete original triple.
  Private values `15/35/134`; left UIDs `164/286/3`, right `82/285/7`.

These are kernel-checked propositions, not invented printed evaluations.
Target: `IndexedWitnessCompositionTest`.

### Task 6 — isolated copies, independent parity and ten cycles

Patch `patches/task-6.patch`; final packaged source commit
`1348a295bc833a9083b85cecaf8479f20649415c`.
Files:
- `leanncd/experiments/indexed_execution/IndexedWitnessObservationParity.lean`
- `leanncd/experiments/indexed_execution/IndexedWitnessObservationProbe.lean`
- `leanncd/experiments/indexed_execution/IndexedWitnessObservationProbeTest.lean`
- `leanncd/lakefile.toml`

Probe copies only declaration names for `roleInterface`, `envInput`,
`componentSpan`, `boundaryEnvEquiv`, `compositeInputEquiv`,
`compositeOutputEquiv`, `toWired`; internal production references remain.
Read these `*Copy` declarations at Probe, all seven `*_parity` theorems at
Parity, and `Hidden.good_option_cell`, `Empty.metadata`,
`Axis.boundary_cells/external_copy_cells`, `Triple.input_copy_cells`,
`Triple.private_stores` at ProbeTest. Positive singleton extraction is
`some 1`, not an injectivity claim about the unrestricted hidden component.
Build baseline `IndexedWitnessObservationProbeTest` and
`IndexedWitnessObservationParity` separately. **During mutations build only
ProbeTest; it never imports/references Parity.**

Use only `categorical_witness_semantics_mutations_post.json`.
First six preserve types, complete-model apexes and valid equivalences:
coordinate reversal; zero projection; injectivity-preserving UID +1;
present input functions zeroed without removing `Some`; external input
reversal; involutive output negation. Last four are donor controls:
hidden one→zero; private audit→output locator; right store→zero store;
total substituted into strict absence theorem (**not numeric**).
Every populated `expect` has two actual strings: numeric controls require
the decide-tactic diagnostic plus their named ProbeTest axiom-audit failure;
strict donor requires `Type mismatch` plus `Audit.strict_empty` audit failure.
See the JSON for exact spelling, not a reconstructed diagnostic.
No direct production generic-law mutation or independent `toWiredCopy`
embedded-proof mutation is claimed.

### Task 7 — nondefault discovery and accurate ledger

Patch `patches/task-7.patch`; source commit equals frozen source HEAD.
Files:
- `leanncd/AGENTS.md`
- `leanncd/experiments/indexed_execution/IndexedWitnessSemantics.lean`
- `leanncd/lakefile.toml`
- `papers/semantics/categorical_tensor_logic_component_interfaces.md`
- `papers/semantics/categorical_tensor_logic_semantics.md`

Read aggregate imports, experiment globs, interface Sections 6–7,
synthesis Sections 9.2–9.3/10 and progress ledger.
Target: `IndexedWitnessSemantics`. Preserve the nondefault experiment:
do not insert witness imports into default `LeanNCD`.
Measured relevant AGENTS hooks total 2,951 characters; no trim is needed.
Docs must say denotational target/unit/coherence results are proved while
source-category/functor and process/rank targets remain open.

## 5. Controller replay and real checkpoints

First review each frozen task's actual compiled code/patch directly against
Sections 2–4; persist per-task invariants/findings in the plan record.
Resolve findings before running replay. Keep protected edits outside staging.
The controller explicitly stages/commits the plan/artifact package and
updated records before replay, so its tracked worktree and index are clean.
The author does not commit. Do not use `add .` or stage incidental settings.

`package.py --replay` first runs its private-index exact-tree check, then
applies each actual patch, builds the listed targets, hashes each changed
file, checks **every changed .lean in POST-edit form** with the project's
`check-snippet.sh`, and runs copied-source checks at groups 6 and 7.
It stages only that task's explicit file keys, checks staged whitespace,
commits with the Copilot trailer and writes `execution_replay.json` after
each successful task. No document contains a Lean block to paste/compile.

Its private-index workspace must remain project-local, not system `/tmp`.
Create the support directory and explicitly bind Python's workspace root:

```sh
/bin/mkdir -p /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_witness_semantics_artifacts/index_support
/usr/bin/env TMPDIR=/Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_witness_semantics_artifacts/index_support python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_witness_semantics_artifacts/package.py --replay --checkout /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup
```

Do not invoke `--emit`, `probes.py --emit`, or `--emit-manifest`: they
regenerate frozen artifacts/proposals and could erase observed expectations.
After replay, inspect the actual seven committed task diffs and receipt;
append substantive task reviews, including both commutations, full triple,
no existence inference, donor discrimination and parity isolation.
Receipts are build/hash/snippet checkpoints, not independent review verdicts.
On any failure stop and record the exact task/state; do not blindly restart
`--replay`, whose clean-tree/base guards are not a resume mechanism.

## 6. Final release gates and integration

Run these controller checks unfiltered after task 7:

```sh
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_witness_semantics_artifacts/probes.py --check --prototype /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/leanncd IndexedWitnessObservationParity
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_witness_semantics_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/leanncd/scripts/mutation-manifest.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_witness_semantics_mutations_post.json
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_witness_semantics_artifacts/probes.py --check --prototype /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/leanncd LeanNCD Tests IndexedExecutionExperiment
rg -n 'sorry|admit|native_decide|^axiom ' /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/leanncd/experiments/indexed_execution/IndexedWitness*.lean
rg -n 'ObservationParity' /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/leanncd/experiments/indexed_execution/IndexedWitnessObservationProbeTest.lean
rg -n '\.lean:[0-9]+|Proposed packaging|not yet a complete categorical semantics|interpretation still needs|packaging and coherence laws remain' /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_witness_semantics*record.md /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_tensor_logic_semantics.md /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_tensor_logic_component_interfaces.md
```

`rg` no-match exits 1 are expected for forbidden tokens/references.
Review namespace `#audit_axioms`/`#print axioms` outputs from actual test
builds: only standard `propext`, `Classical.choice`, `Quot.sound` as applicable.
Do not treat expected temporary mutation `sorryAx` failures as baseline axioms.
The mutation receipt must show all 10 selected, both expected strings,
byte-identical restoration and restored green; persist its actual table.
Historical proposed/open wording in historical records is not a current gap.

Two independent whole-branch review lenses follow: (1) categorical/model
soundness — sizes, quotient, all-input/both-leg comparison, same triple and
restricted hypotheses; (2) integration/observations — actual imports/targets,
exact-copy/source/namespace audit, discriminating controls and honest docs.
Reviewer briefs use named symbols and 40–60-line windows, aim for 40 turns
and stop/report before 60 turns or ~250k context; do not infer measured token
compliance without a transcript. Reviewers retain findings incrementally
in the record; the controller fixes
or explicitly adjudicates each finding and reruns affected gates.
No pause/menu between approved tasks. No new work outside the exclusions.

Only after both reviews and the full three-target build are green, record
actual commit/review/build/mutation receipts and accounting limitations.
Recheck protected-edit hashes, then merge to **local main**, without pushing.
Use the actual owned branch name discovered by `/usr/bin/git -C <controller>
branch --show-current`, not an invented branch. Remove only this task's owned
controller/prototype worktrees and topic branch after recording results and
ensuring no owned uncommitted deliverables remain. Never delete others'
worktrees, force-push, or clean a shared checkout. Report local integration
and any ahead-of-origin state only when actually observed.
