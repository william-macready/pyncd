# Part V slice 4: buffer reuse execution record

Status: implementation validated. Both controller full builds and the axiom
audit are green, all 64 mutation verdicts pass, both whole-branch reviews are
clean or adjudicated, and exact ordered patch replay is verified.
Local integration completed with merge `c44f8a21`; no remote push was performed.

## Approved scope

Base: local `main` at `4ffdc342`.
Design: `docs/superpowers/specs/2026-10-11-buffer-reuse-aliasing-design.md`.
The owner approved D1-D6 individually and then approved the design document.
The preceding retirement design remains unchanged as a historical record.

Full path: physical buffers, static typed placement, boundary-local layout
injectivity, and an unmapped-slot invariant replace the globally injective
tensor-slot profile. Scan programs, relocation, input retirement and in-place
kernels remain out of scope.

## Setup and baseline observations

- Existing isolated worktree: `implement-buffer-reuse-aliasing-plan`.
- `prepare-worktree.sh` fast-forwarded `42102087` to local `main` at `4ffdc342`.
- Cache verification: 8101 Mathlib oleans / 8094 source files; 318 project oleans.
- Refresh build of `LeanNCD` succeeded. This is a library refresh, not the final
  full build or test-suite gate.
- Baseline `Plan*Test.lean` fixtures: 281, comprising 149 `#eval check` rows and
  132 top-level `example`/`theorem` items.
- Inherited manifests: 20 slice-1, 15 slice-2, 9 D7 and 10 slice-3 cycles,
  totaling 54. They have not yet been run against the new interfaces.

## Prototype checkpoints

### Physical storage and kernels

Commit `b6f05490` contains the approved design and foundation prototype.

- `Allocation` contains a computationally decidable, explicitly enumerated
  finite buffer type, per-buffer sort and capacity, and sort-certified bounded
  placement for defined addresses.
- `Plan.allocation` has a canonical per-tensor default; expansion preserves it.
- Physical slots distinguish supplied-input storage from reusable buffers.
- Memory, reads, writes, decoding and outcomes are allocation-indexed.
- `R.dead` now states that every unmapped physical slot contains `none`.
- The foundation agent compiled `Syntax` and `Memory`, including general
  `R_start`, but stopped with a proof-transport error in `execAnn_prefix`.
- A separate narrow fix split the normalized accumulation matches and compiled
  `LeanNCD.Semantics.Plan.Step`, including `stepCommand_single`.
- At this checkpoint simulation, validity, wrappers and fixtures remained to be
  migrated; the later checkpoints below supersede that status.

### Alias-safe step simulation

Commit `41cb1829` compiled `LeanNCD.Semantics.Plan.Simulation`.

- `LayoutOK` is injectivity on the current `SlotView` domain, not on all
  logical addresses.
- `step_init` requires the successor-boundary layout; `step_acc` and
  `step_retire` require the current-boundary layout.
- `step_R` carries both boundary premises. `AnnOK` is unchanged.
- Publication and failure matching need no additional layout premises.
- Mapped-value agreement, retention, `retPub` and unmapped-slot emptiness are
  preserved for arbitrary allocations satisfying those local premises.
- The dispatch reported 32 turns, within its cap. Its compiled axiom reports
  contain only `propext`, `Classical.choice` and `Quot.sound`.
- At this checkpoint exact checking and downstream migration were in progress.

### Exact layout checker and singleton correctness

Commit `c615fb9b` compiled `LeanNCD.Semantics.Plan.Correctness`.

- `Valid.layout` requires `LayoutOK` at every boundary up to and including
  `commands.length`; `layout_boundary` supplies pre/post premises for a step.
- `checkLayouts` checks represented resource pairs at every position in
  `range (commands.length + 1)`, including input resources and unpublished
  materialized accumulators.
- Soundness, completeness and checker redundancy results are preserved.
- Singleton run preservation, progress and correctness use the boundary
  premises rather than globally injective placement.
- The dispatch reported 26 turns and 25 standard-axiom theorem audits.
- Wrapper and canonical fixture migration subsequently completed.

### Fused/fault wrappers and canonical preservation

- `832ad70d` compiled fused and fault-wrapper migration. `R_transport`,
  `execAnn_prefix` and `decode_prefix_congr` carry allocation equality and casts;
  expanded layout premises reach all folds. No-fault parity, error-state `R`
  and the existing correctness/model theorems remain.
- Wrapper dispatch: 23 turns. Canonical migration `763e5403` stayed within its
  50-turn cap. All baseline 281 assertions remain: 149 `#eval check` rows and
  132 top-level `example`/`theorem` items, with only required API/proof changes.
- The 13 original `Plan*Test` modules remain registered; three new test modules
  were added in `deb4fecd`, giving 16. The additional shared `PlanFixtures`
  module makes 14 original Plan test/shared modules and 17 total.

### Actual physical-reuse fixtures

`deb4fecd` compiled all three new modules. Measured total:
**354 = 174 `#eval check` rows + 180 top-level `example`/`theorem` items**.
The increase is 73: `PlanReuseTest` 26, `PlanReuseStorageTest` 22,
`PlanReuseWrapperTest` 25. `PlanFixtures` is not included in that test count.

- Core (`rtInitAfter` donor): point 2 takes retired point 0's slot; accepted,
  `done 7`, raw row `[4,3,4]`, empty output decode `[]`.
  Shared-slot pc 4–7 values are `[none,0,4,4]`; retired read `none`,
  ghost 0, new read 4. R holds at 0–7; unused capacity and buffer stay `none`.
- Nearest bad allocation routes point 2 into live point 1: checker false,
  unchecked `done 7`, corrupted row `[none,1,1]`; point 1 reads 1 vs ghost 3.
- Component fixtures separate pub/pub, pub/acc, acc/acc collisions from legal
  separate-buffer neighbors; the final-boundary discriminator is pinned.
- Storage: internal tensor 2 and output tensor 1 share workspace index 0.
  Checker true, `done 7`, output decode 2 matches canonical donors; retired
  read `none`, ghost 3. Retained-output conflicts reject.
- Typed custom buffers: Bool sorts with ℤ/ℚ carriers; `done 3`, decode
  `(11,7/8)` equals canonical. Empty output `done 0`, zero capacity, successful
  decode; unused physical capacity stays `none`.
- Fused good retire-then-init: accepted `done 6`, R at 0–6, same allocation and
  expansion as the singleton donor. Reversed order has all 7 outer layouts
  true but 8 expanded layouts false only at index 4; checker false,
  unchecked `stuck 4`, row `[none,3,none]`.
- Fault after the reused-slot write: error pc 5, row `[4,3,4]`, error-state R;
  physical value 4, old read `none`, ghost 0. No-fault parity is proved.

### Controller verification and fresh authoring

- Controller full build passed 8796 jobs before mutation cycles.
- `Semantics.AxiomAudit` actually built and audited 5992 constants; dependencies
  are standard axioms only. The four pre-existing sorry warnings in Base/St,
  Base/Br, Core/Weave and Instances/StBr are unchanged.
- Six mechanical git-format-patch artifacts exist in
  `plan_layer_slice4_patches/`, covering the six checkpoints above. The controller
  verified exact ordered replay from `4ffdc342` to `deb4fecd` with an isolated
  index; the final git diff exited 0. No destructive revert/reapplication is
  required.
- Deviation: the compiled prototype doubles as implementation. Fresh authoring
  writes the execution plan from compiled artifacts rather than pretending the
  implementation has not happened. Immutable `deb4fecd` snapshot windows were
  used while controller cycles could temporarily mutate production.
- Inherited manifests: 20 + 15 + 9 + 10 = 54; the new manifest has 10 entries,
  seven library-proof controls and three fixture controls. Old strings were
  unique under final unfiltered `--check`. All five actual manifests pass:
  **20/20 + 15/15 + 9/9 + 10/10 + 10/10 = 64/64**. Every cycle broke its
  build, observed its expected failure, restored the file byte-identically and
  passed the restored build. Results are in `plan_layer_slice4_mutation_results/`.
  Seven new controls die at library proofs; three die at named fixture checks
  without changing production. No per-fixture kill claim is made for storage.
- New live plan: `plan_layer_slice4_plan.md`; production/fixture tasks marked as
  executed checkpoints, with donors, symbol windows, patch scopes and risks.
  Manifest gates, documentation verification, both fresh whole-branch reviews,
  the final controller build and local integration are complete.

### Final controller validation and review disposition

- The initial new-manifest run killed/restored all ten controls, but two
  expected diagnostic strings had incorrect capitalization. The controller
  copied the observed `Application type mismatch` diagnostic and reran the
  complete ten-entry manifest successfully.
- The first inherited slice-1 rerun killed/restored all twenty controls, but
  five expected diagnostics no longer matched the migrated proof structure.
  The initial repair reduced all 45 slice-1/2/3 expectation lists to file-level
  substrings, losing 64 historical failure-site strings (29 + 15 + 20) and
  merging multi-site checks. The resulting PASS verdicts were weaker than
  required, not a faithful location repair. The post-merge follow-up below
  restores exact sites and diagnostics from fresh failures.
- The inherited N5/N6 controls retain their equivalence labels. Their library
  proof failures are not claimed as semantic counterexamples.
- Fresh soundness review found no high-confidence bugs. Fresh spec-to-Lean
  fidelity review found no blocking defects and three documentation issues:
  the `RetOK` safety classification, completed replay still marked pending,
  and test-module counts double-counting `PlanFixtures`. All three are fixed.
- Reviews used the immutable compiled snapshot while mutation cycles ran.
  After review, only documentation and observed diagnostic anchors changed;
  no executable behavior or theorem premise changed.
- Final post-cycle controller full build passed **8796 jobs**. Its actual
  `Semantics.AxiomAudit` build audited **5992 constants** with standard axioms
  only. The four pre-existing sorry warnings outside Plan remain unchanged.
- Controller assertions found no prohibited proof shortcuts in the eleven
  Plan modules and verified all 64 persisted mutation table verdicts are PASS.
- Final inventory: **16 test modules + shared `PlanFixtures` = 17 Plan modules**;
  **354 assertions = 174 evaluated rows + 180 proof items**. All 281 baseline
  assertions and their expected values remain preserved.

### Documentation value sweep

Commands used: `rg -n -l --glob '*.md'` over the repository with
`281|149|132|dense injective|never.?reused|no Lean.{0,30}reuse`, followed by
targeted `rg -n --no-filename` in the current specification, path and AGENTS nodes.
Current Part V profile/count claims are updated to typed static same-sort reuse,
boundary-local `LayoutOK`, unmapped-slot `R.dead` and 354 fixtures.
The current retirement clause's no-second-retire role is now safety, not merely
diagnostic: `step_retire` uses `RetOK` to obtain the retiring resource's
pre-boundary `SlotView`, preventing clearing a reused slot's new occupant.
General mathematical contract prose is unchanged: only formalization paragraphs,
proof-status rows and profile labels change. Historical slices 1–3 plans,
records, retirement design and the pre-approval reuse brief remain historical;
unrelated numeric/index hits are not capability claims. The approved reuse design
only receives status and measured-prototype clarifications.

Authoring checks: the live plan was 244 lines at authoring time, named module/test paths exist,
new immutable fixture counts are 10+16 core, 6+16 storage and 9+16 wrapper.
Current stale-value hits are historical baseline counts or unrelated section
numbers; no current "reuse absent" profile remains in the four swept current
documents. `Plan/AGENTS.md` Pitfalls are below 3k characters. Whitespace checks
passed. No Lean snippets, builds, commits, nested dispatches or production/test/
manifest/patch edits were performed by this documentation author.

## Budget and measurement limitations

The foundation dispatch reported exceeding its 55-turn cap and stopped. The
controller surfaced the breach and split the remaining work into fresh bounded
dispatches. The prefix-fix dispatch reported 10 turns without a breach.

`python3 .claude/skills/slice-plan/token-report.py
faaa5884-f669-4d5f-808f-1790f4b3e9db` reports no Claude transcript for this
Copilot SDK session. The session-usage query also returned no accounting rows.
Therefore cumulative tokens and context peaks are unavailable at this point,
not measured as zero. No claim of compliance with the cumulative token budget
can be made without an actual usage source.

Other dispatch reports: simulation 32 turns, checker 26, wrappers 23;
core fixtures 31; storage approximately 36, **breaching its 35-turn cap/reserve**;
wrapper fixtures within 35. Both foundation and storage breaches are surfaced,
not silently treated as compliant. Fresh authoring stayed below its 35-turn cap;
no additional known budget breach occurred. Exact cumulative usage and measured
context peaks remain unavailable, not zero, so the 250k context and cumulative
token budgets have no accounting certificate.

## Local integration

- Merged the validated topic branch into local `main` with `--no-ff` as
  `c44f8a21`.
- Confirmed the topic branch is an ancestor of `main` and the merged trees
  have no content difference before this documentation close-out.
- The primary checkout was clean at integration. No remote push was performed.
- Cleanup is limited to this task's topic branch/worktree and temporary
  immutable snapshot; no other checkout or branch is in scope.

## Post-merge review follow-up

Direct path, isolated branch `worktree-reuse-review-fixes`, based on `84b1cc1c`.
The three Important findings and confirmed Minor findings were checked against
the landed code and the external review reports, not treated as new capabilities.

- All 45 inherited slice-1/2/3 expectation lists now retain separate exact
  file/line/column/diagnostic strings. Every observed failure site is pinned,
  including both `checkRet_sound` and `checkRet_complete` for S3-M3/M4/M5/M10.
  D7's nine entries now have observed diagnostic anchors rather than `n/a`;
  reuse controls also have exact sites. There are 167 anchored expectations
  across the five manifests; no bare `File.lean:` expectation remains.
- The N5 A2-e equivalence control now fails at `execAnn_prefix` in `Step`,
  not at the former Simulation sites. It remains a local proof-shape control,
  not evidence of a semantic counterexample or a transactional simulation kill.
- S4-M6 retains the weakened `R.dead` mutant but targets the test consumers.
  The physical-slot branch of `R_start` and the cleared-slot branch of
  `step_retire` now use simplification rather than syntax-sensitive producers.
  The mutant therefore builds the library and fails at
  `retired_slot_free_of_injective` in `PlanRetireTest`, which needs actual
  emptiness. `PlanReuseTest` is also a target but imports that failing module,
  so this is not claimed as an independent kill of its unused-capacity theorem.
  The ten reuse controls are now six library-proof controls, one test-level
  invariant consumer and three computed fixture controls.
- `storage-live-output-claim` computes output 1 before internal tensor 2.
  The old step rules pass, layout rejects the shared allocation, and the same
  commands pass with canonical allocation. Both unchecked runs finish at 7;
  the shared run clears the output and cannot decode, while the canonical run
  decodes 2. The trace pins output reads `[2,0,3,none]`. The older output-retire
  and overwrite fixtures are explicitly labelled inherited-rule checks.
- `reuse-retire-again-after-reuse` retires point 0 after point 2 has written 4
  into its old slot. The checker rejects it; the unchecked run clears 4 and
  is `stuck` at the later publication. Its canonical twin is also rejected
  but finishes `done`, because the new occupant has separate storage.
- Empty decode is documented and tested as a vacuous control: both good and
  bad aliases return `some []`. Nonempty output correctness is pinned by the
  storage fixtures. `storage-custom-zero-capacity` uses an explicitly supplied
  independent `Fin 1` buffer, capacity 0, and successful empty-domain decoding.
- `layoutOK_of_canonical` and `checkPlan_of_canonical` are library theorems;
  the test-only copy is removed. Direct axiom reports cover both bridges,
  `place_sort`, `cast_option_none`, `start_read`, `expand_allocation`,
  `execAnn_prefix` and `stepCommand_single`. Their reports use standard axioms.
- The canonical fused `PlanOutcome.Agree` example is independent computation
  again: pointwise `fin_cases`/`rfl`, not `runPlan_agree`.
- All five live pending-status documents are refreshed, including the path
  heading/TOC and roadmap; the top-level Lean index says slices 1-4.
  The repeated-retire pitfall is scoped to canonical versus reused storage,
  `R`'s profile docstring is current, and the plan-length observation above
  is explicitly historical. No mathematical contract or runtime kernel changed.

### Observed validation

- Targeted reuse/storage/wrapper/fused correctness builds passed.
- Hand mutation probes: switching `outputFirst` to canonical allocation fails
  both new output rows; removing the second retirement fails both new retire
  rows; increasing custom capacity to 1 fails the capacity row and its emptiness
  proof. Each wrapper verified byte-identical restoration and a restored build.
- Fixture inventory: **360 = 179 evaluated rows + 181 proof items**, split
  28 core reuse, 26 storage and 25 wrappers. All 149 inherited evaluated rows
  outside the new reuse modules are byte-identical to the landed baseline;
  the canonical example's statement is unchanged.
- All six historical patches independently replayed in order in an isolated
  index from `4ffdc342`; the complete `leanncd` tree equals `deb4fecd`.
  No worktree source files or real Git index were used for replay.
- Final anchored reruns: **20/20 + 15/15 + 9/9 + 10/10 + 10/10 = 64/64**.
  Every expected site appears in its own mutated log, every file is restored
  byte-identically, and every restored build passes. Preliminary S4-M6 variants
  that stopped at producer/prefix proofs were rejected, not counted as consumer
  evidence; only the final consumer-killing control is shipped.
- Controller full build passed **8796 jobs**. The actual rebuilt axiom audit
  checked **5994 constants**, all with standard axioms. Four pre-existing
  `sorry` warnings outside Plan remain; no proof shortcut was added.
- Direct whole-branch review covered code, fixtures, live documents, all five
  manifests and persisted results: no outstanding findings. Structural checks
  confirm all mutation bodies are unchanged; only S4-M6's target/label changes
  besides expectations. Whitespace and the live stale-status sweep are clean.
- Token reporting found no transcript for this Copilot session. Cumulative
  usage is unavailable, not measured as zero; no subagents were dispatched.

## Retirement/reuse fixture-probe closure

The subsequent `worktree-buffer-fixture-probes` pass closes slice-3 O3 without
changing any runtime kernel, theorem or production mutation entry. Full
reconciliation, per-mutant observations and reproduction command are in
`plan_layer_slice3_record.md`, section "O3 reconciled and closed".

`buffer-fixture-probes.py` source-extracts the exact current definitions and
committed row expressions, proves clean copy parity, and measures ten retirement
and six reuse computed component kills. It additionally checks the unused-capacity/buffer
consumer under the exact weakened `R.dead` field, independently of
`PlanRetireTest`'s earlier proof barrier. All seventeen probes pass with clean
controls before and after, production hashes unchanged and no admissions.
These supplemental component/consumer probes do not expand the 64 production
manifest entries or claim whole mutated executor runs.

Seven appended rows raise the current count to **367 = 186 evaluated rows +
181 proof items** (360 immediately after the review fixes). All previous fixture
lines remain unchanged, so existing mutation anchors do not move. Retirement
fixtures total 72; reuse fixtures split 31 core, 26 storage and 25 wrappers.
The original three reuse fixture controls already have computed kills, so all
twenty buffer controls now have evidence beyond library proofs. This remains
separate from complete mutated executor coverage or a mutation per fixture.

Final validation: supplemental probes **17/17**, both production buffer
manifests **20/20**, full build **8796 jobs**, actual axiom audit **5994 constants**,
and direct whole-branch review clean after the diagnostic-handling fix.
All old fixture lines and production Lean definitions/proofs remain unchanged;
the historical 64-entry manifests are neither weakened nor expanded.
