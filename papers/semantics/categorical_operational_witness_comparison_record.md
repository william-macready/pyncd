# Operational-to-witness comparison: evidence and execution record

Base: `37500cab85a2989a1422da2ef21256cb5648e8da`.
Live instructions: [implementation plan](categorical_operational_witness_comparison_plan.md).
**Controller execution, task commits, final whole-branch reviews and integration:
PENDING.** Compiled authoring prototypes are not a completed release.

## Authoring inputs and provenance

Fresh second-context write-up used the goal handoff, the four receipts below,
their compiled artifact/evidence packages, and targeted synthesis windows.
No source proofs were researched, read or reimplemented; no new Lean snippets
were authored. Lean source reads by deterministic tooling were limited to
hashing, replay byte comparisons and placeholder/namespace scans.

Receipt directory:
`/Users/williammacready/.copilot/session-state/4fce84db-8293-4039-9357-f23acfd3ecc1/files/`

- `categorical-operational-witness-prototype-receipt.md`
- `categorical-operational-witness-stage2-receipt.md`
- `categorical-operational-witness-acceptance-receipt.md`
- `categorical-operational-witness-controls-receipt.md`

These are historical authoring receipts, left unchanged. Their durable
repository counterparts are the evidence JSON/logs and mechanically extracted
patches in the four artifact directories indexed by the live plan.

### Measured stages, not controller release gates

| Stage | Frozen deliverables | Observed authoring evidence |
| --- | --- | --- |
| Prototype | patches 01–03; bridge/descent/signature audit | targeted build exit 0; 15 public signatures, 11 named axiom queries; four replayed files byte-equal |
| Stage2 | 04–06; actual comparison/source erasure/outcomes and tiny stage audit | targeted build/audit exit 0; 18 public signatures, 14 named queries; patches 01–06 replayed, eight files byte-equal |
| Acceptance | 07–09; seven goal families and public import | targeted/full build exit 0, 8962 jobs; 19 named queries; three patches checked/applied, 12 source hashes |
| Controls | 10; controls, namespace driver, manifest, nondefault registrations and Lean discoverability | unfiltered 12/12 cycles, intended diagnostics and byte restoration; full build exit 0, 8964 jobs; 9 namespaces / 124 constants; 13 new-source files scanned |
| Fresh write-up | 11 synthesis; plan/record; combined replay helper/manifest | ordered 01–11 check/apply, reverse and forward in own disposable tree; 17 files byte-equal; unfiltered manifest `--check` exit 0 |

Allowed axiom audit results are subsets of `propext`, `Classical.choice`,
`Quot.sound`, with no `sorryAx`. Existing dependency warnings are not presented
as new-module warnings. No final independent proof review is inferred from
axiom audits or successful compilation.

## Mathematical result documented by the receipts

`IndexedRankedWitnessBridge` derives model existence iff actual completion,
no model iff actual failure, at-most-one models and component-span left
injectivity for the matched ranked profile. Rank does not imply success.
The authoritative ingredients are actual default terminality, conditional
completed-model uniqueness and failed-run exclusion; no new existence,
uniqueness, execution-agreement or completion premise is added.

`IndexedRankedWitnessDescent.compute_iso` uses the fixed all-input
`ComputeAgrees` transport to map every complete store, including all private
addresses, with both exterior legs commuting. The reverse uses inverse
transport and symmetric observation agreement; ranked left injectivity
supplies inverse laws. Raw input-square/provenance information remains in
the unchanged hypothesis even though actual all-input agreement suffices for
the store transport argument. All `Agrees` constructor pairs are covered.

`IndexedRankedWitnessComparison.comparison` is an actual target-quotient
functor, with identity/composition proofs. `source_comp` reuses
`composition_hom`/`compositeWiredIso`, original boundary environment and both
exterior wires. The image is independent of rank and origin on the same
component/exteriors, without weakening operational provenance.

`IndexedRankedWitnessSource.erase` is an actual functor between distinct
source categories. `erase_rel` covers every ranked relation constructor.
The old source's extra bracket relation needs no converse preservation.
`diagram` is actual functor equality, not merely equal output observations.

`IndexedRankedWitnessOutcomes` connects actual default checked/reference
runners via the existing accepted correspondence. Its model characterization
retains full `Relation`, every-address availability and exact reference
`finalStore`. Both domain/failure complements are unconditional per validated
input; exact success-value theorems are conditional on displayed success.

Common scope is finite decidable tensors over `Declarations Unit`, matched
ranked components and validated inputs, with existing rational operations,
budgets and schedules. Witnesses retain complete owned stores and both legs,
not inherited outside frames. No new arbitrary-private-store execution,
generic cross-program reference transport, scheduler theorem, unranked
extension, totality, faithfulness, inverse/equivalence or history recovery.
Event order, intermediate histories/ledger prefixes, failure diagnostics and
assembly provenance are intentionally lost in witness meaning. Empty fibers
do not become successful zero values. Existing frame/`Realizes` results remain.

## Concrete observations and control classification

Copied from compiled acceptance evidence, not calculated during write-up:

- Strict leaf: `("failed", some 30,
  some ([some 3, some 9, none], [(201,9)]))`.
- Total leaf: `("complete", none,
  some ([some 3, some 9, some (7/2)], [(201,9),(301,7/2)]))`.
- Total pair: `[some 3, some 9, some (7/2), some 81, some (19/2)]`.
- Total triple: `[some 3, some 9, some (7/2), some 81, some (19/2),
  some 6561, some (163/2)]`.
- Nonconstant wire `(input, forward, inverse, twice) = (11,101,110,110)`.
- Empty presence `(true,false,"complete","invalidInput")`.
- Hidden private/output row `(0,1,0,0)`.

Leaf/pair/failure-reference/wire/empty/hidden rows have decidable assertions.
Triple availability and intermediate reference-cut rows are observations,
not independently pinned assertions. Generic categorical/model equations
are live-proof donors, not independent runtime evaluator observations.

The final manifest contains 12 measured controls:
P01/P04/P09 are type-valid executable/decidable fixture observations;
P02/P03/P05/P06/P07/P08/P10/P11/P12 are live-proof policy controls.
P03 retains boundary values while changing private values; P05 reverses only
input orientation, holding output correct; P04 independently distinguishes
output direction. P06 uses actual functors/diagram, not a copied interpreter.
P07/P08 separate image forgetting from operational provenance distinction.
P09–P12 protect presence, metadata, full unranked witnesses and rank exclusion.
All seven acceptance rows have meaningful nearest legal neighbors.

No setup/type error is counted as a runtime-core defect kill. The retained
`initial-P01-reduction-stuck.log` is an unsuccessful exploratory attempt,
superseded by P01's observed explicit executable assertion diagnostic.
Historical `initial-*` logs are not final certification. Final diagnostics,
source hashes and classifications are in the manifest and post evidence.
Zero new concrete fixture instances were added in controls: existing donors
were reused, with two universal law controls and one executable assertion.

## Combined durable package

Directory:
`papers/semantics/categorical_operational_witness_comparison_post_artifacts/`

- `package_replay.py`: deterministic packaging/hash audit, scratch replay,
  owned-only reverse and numbered forward; no staging, commits, reset,
  checkout, git clean or implementation edits during authoring.
- `11-synthesis.patch`: mechanically extracted documentation-only delta from
  the exact base; Lean AGENTS changes remain solely in frozen patch10.
- `replay-manifest.json`: exact base/final, patch, evidence/script/log and
  per-step file hashes, ownership, targets and serialized replay prerequisites.
- `ordered-replay-evidence.json`: actual command/exit ledger for forward,
  reverse, forward in `ordered-replay-tree`, with final byte equality and
  baseline restoration; that explicitly owned tree was removed.

The helper refuses an existing replay tree or owned-file drift. `reverse`
preflights a disposable replay, then checks each real reverse operation and
reverses only patch-owned changes. `forward N` checks the entire expected
owned state at N−1 before applying N. Package/plan/record remain in place.
No other files are deleted. Authoring did not reverse the live prototype.
Controller commands for actual reverse/per-task forward, unfiltered mutations,
full build, all-nine namespace audit, source/default-import scan and synthesis
value sweep are in the plan.

### Fresh author verification

- Combined packaging succeeded: 11 patches, 17 exact owned files; actual
  ordered `git apply --check`/apply in scratch, reverse to base, forward to
  compiled/doc bytes. All historical patches stayed unchanged.
- Canonical `mutation-manifest.sh --check` with no filters:
  `manifest OK: 12 entries, 12 selected, every old-string unique`.
- `git diff --check` passed.
- Independent helper invocations `audit`, `replay` and `source-audit` passed:
  frozen evidence/file hashes, 66 successful git check/apply operations
  (11 forward, 11 reverse, 11 forward), 13-file source scan, nine namespaces
  and unchanged default imports/config. The owned replay tree is absent.
- Helper Python syntax parsed successfully; an out-of-order `forward 2`
  request on the final prototype was refused for owned-file drift without
  edits. All 19 experiment filenames named in plan briefs exist; the live
  plan is 280 lines, below the requested ~400-line target.
- No new implementation build or mutation run was claimed: frozen Lean source
  is hash-equal to prior compiled/fully built evidence. Documentation has no
  Lean blocks requiring snippet compilation.
- No source proof exploration, agents, staging, commits, final review,
  execution or integration performed.

## Budget disclosure

Authoring was bounded/split: prototype, stage2, acceptance, controls, then this
fresh write-up context. Prior receipts report approximately 33–35 prototype
turns, approximately 55 stage2 tool rounds, within-bound acceptance and about
40 controls action turns. Stage2 explicitly warns host counting including
commentary/final turns may slightly exceed its 55-turn cap; preserve that
possible breach, not an unmeasured pass.

`token-report.py 4fce84db-8293-4039-9357-f23acfd3ecc1` again returned
`no transcript for session ...` (exit 0). Cumulative/peak token telemetry is
unavailable; neither the ~50M authoring target nor a measured peak pass can
be certified. This fresh context remains visibly below 250k and below 55
turns; no fresh-context breach observed. Execution's ≤~175M total and each
dispatch's ≤~250k/~60-turn caps still apply and must be recorded honestly.

## Controller completion ledger — all PENDING

- [ ] Own-only reverse and actual per-task forward/build/review/commits 01–11.
- [ ] Direct unfiltered 12/12 intended-diagnostic cycles, restored-green builds
  and final source/hash audit (authoring replay is not this controller gate).
- [ ] All-nine namespace/descendant audit, placeholder/new-axiom source scan,
  unchanged default imports and nondefault-only configuration.
- [ ] Direct full `LeanNCD Tests IndexedExecutionExperiment` wrapper build.
- [ ] Whole-branch review lens 1: quotient/comparison/domain/diagram soundness.
- [ ] Whole-branch review lens 2: operational/reference/acceptance/information loss.
- [ ] Findings adjudicated/fixed with refreshed gates; budget close-out.
- [ ] Local main integration green; only owned branch/worktree removed; no push.

Append execution results/findings here; do not rewrite historical receipts or
promote authoring measurements into controller completion.
