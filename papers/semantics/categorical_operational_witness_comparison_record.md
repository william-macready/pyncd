# Operational-to-witness comparison: evidence and execution record

Base: `37500cab85a2989a1422da2ef21256cb5648e8da`.
Live instructions: [implementation plan](categorical_operational_witness_comparison_plan.md).
**Controller execution and release: COMPLETE.** Task commits, both independent
whole-source review lenses, direct mutation replay and full build pass.
Local main integration is recorded separately below.

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

## Controller completion ledger

- [x] Own-only reverse and actual per-task forward/build/review/commits 01–11.
- [x] Direct unfiltered 12/12 intended-diagnostic cycles, restored-green builds
  and final source/hash audit (authoring replay is not this controller gate).
- [x] All-nine namespace/descendant audit, placeholder/new-axiom source scan,
  unchanged default imports and nondefault-only configuration.
- [x] Direct full `LeanNCD Tests IndexedExecutionExperiment` wrapper build.
- [x] Whole-branch review lens 1: quotient/comparison/domain/diagram soundness.
- [x] Whole-branch review lens 2: operational/reference/acceptance/information loss.
- [x] Findings adjudicated/fixed with refreshed gates; budget close-out.
- [ ] Local main integration green; only owned branch/worktree removed; no push.

Append execution results/findings here; do not rewrite historical receipts or
promote authoring measurements into controller completion.

## Controller execution and release

The controller reversed only the eleven hash-verified owned patches, confirmed
base source state, then applied them individually in order. Each task had a
successful targeted wrapper build (documentation needs no build), exact
reviewed-source hash checkpoint, explicit-path staging and separate commit.
The two unregistered signature audits ran after tasks 03 and 06.

| Task | Commit | Result |
| --- | --- | --- |
| 01 bridge | `07a022a8` | PASS |
| 02 descent | `208740e4` | PASS |
| 03 signatures | `35b1085f` | PASS |
| 04 comparison | `9b10c637` | PASS |
| 05 source diagram | `694d18e5` | PASS |
| 06 actual outcomes | `4ec224cb` | PASS |
| 07 private outcomes | `1784372b` | PASS |
| 08 categorical acceptance | `07a2d1d2` | PASS |
| 09 metadata/multiplicity | `18800b64` | PASS |
| 10 controls/audits | `5491f4c6` | PASS |
| 11 synthesis | `e5b03424` | PASS |

Two independent whole-package reviewers examined the frozen proof/test/doc
source before replay, with distinct mathematical and operational/adversarial
lenses. Both returned no significant findings. The operational reviewer also
reported all eleven task checkpoints clean and independently built all 8964
jobs. The controller's final committed-delta check confirms all seventeen
owned files exactly match those reviewed bytes; no implementation changed
during replay or release. Review conclusions therefore apply to the final
whole branch, not merely an earlier draft. No finding was waived.

The controller directly ran the canonical mutation manifest **unfiltered**:
**12/12 PASS**, every intended diagnostic observed, every restored build
green, and every mutated file byte-identical afterward. The committed
[controller mutation receipt](categorical_operational_witness_comparison_post_artifacts/controller-mutations.md)
retains each result. Classification remains three executable/decidable donor
observations and nine live-proof controls, not twelve runtime-core defect kills.

After restoration, the controller's full wrapper build of
`LeanNCD Tests IndexedExecutionExperiment` passed **8964 jobs**. Its namespace
audit reported all nine namespaces and **124 constants**, using only standard
axioms. The frozen source audit passed for thirteen new Lean files, no proof
placeholders/new axioms, exact source hashes and unchanged default imports
and configuration. Existing runners, operational equality and witness source
were not modified. The comparison remains additive and nondefault.

Execution logs and the per-task JSON ledger are in the session receipt
directory above (`comparison-execution-*.log`, `comparison-execution.json`,
`comparison-controller-mutations.log`, `comparison-controller-full-build.log`).
The initial staged whitespace check rejected legitimate blank context lines
inside patch artifacts. The controller excluded patch-file contents from that
check rather than altering frozen patches; source/document whitespace checks
passed. No validation or task was skipped.

The close-out token-report invocation again returned no transcript. Cumulative
input, peak context and token-budget totals remain unavailable rather than
claimed compliant; the possible stage2 turn-cap breach remains disclosed.
No new mathematical boundary, faithfulness or unranked claim is inferred from
the release checks. No remote push has been performed.
