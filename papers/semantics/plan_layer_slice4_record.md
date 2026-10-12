# Part V slice 4: buffer reuse execution record

Status: production and fixtures compiled; controller pre-cycle full build and
axiom audit green. Mutation kills, ordered replay, fresh whole-branch reviews,
final post-cycle build and local integration are **PENDING**.

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
- The 14 existing Plan test targets remain registered; three new targets were
  added in `deb4fecd`.

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
  is checking ordered replay from `4ffdc342` with an isolated index; result
  pending. No destructive revert/reapplication is required.
- Deviation: the compiled prototype doubles as implementation. Fresh authoring
  writes the execution plan from compiled artifacts rather than pretending the
  implementation has not happened. Immutable `deb4fecd` snapshot windows were
  used while controller cycles could temporarily mutate production.
- Inherited manifests: 20 + 15 + 9 + 10 = 54; the new manifest has 10 entries,
  seven library-proof controls and three fixture controls. Old strings were
  unique under unfiltered `--check`. **Actual slice-4 kills are PENDING**:
  manifest `expect` strings are not observed failures. Results will be under
  `plan_layer_slice4_mutation_results/`; proof kills and fixture discrimination
  must be reported separately. No per-fixture kill claim is made for storage.
- New live plan: `plan_layer_slice4_plan.md`; production/fixture tasks marked as
  executed checkpoints, with donors, symbol windows, patch scopes and risks.
  Remaining tasks are manifest/replay gates, documentation verification, two
  fresh whole-branch reviews, final controller build and local integration.

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

Authoring checks: the live plan is 244 lines, named module/test paths exist,
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

## Outstanding completion gates

- Measured mutation results for all inherited and new cycles.
- Controller result for isolated ordered patch replay.
- Controller verification of authored plan and current documentation sweep.
- Both fresh whole-branch soundness/fidelity review lenses.
- Final post-cycle controller full build and axiom audit.
- Local integration; no remote push.
