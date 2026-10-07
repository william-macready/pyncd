# Expression/readiness authoring record

## Status and ownership

Fresh-context authoring dispatch B writes the
[live execution plan](expression_readiness_plan.md) from verified artifacts only.
This is not implementation release, a final code review, or a publication record.
Final review status: **PENDING**, controlled by the parent.
Controller final artifact verification is **DONE**, as confirmed in the follow-up
handoff; this does not mark either final review lens complete.
No implementation files are released on this plan branch by this dispatch.
No code patches applied, builds started, commits, pushes, merges, or nested agents.
Only the live plan and this record are created.

Process choice: Full, because typed expression interpretation and independent proofs
introduce a new semantic soundness surface. Scope is one expression/readiness
semantic-validation slice, not redesign or optimization of a production backend.

## Provenance and source-of-truth hierarchy

- Plan branch: `agents/expression-readiness-plan`.
- Verified rehearsal baseline: `44296ad56e11b3b296c265119466b91aef8200e0`;
  not an exact execution-HEAD requirement.
- Authoring checkout:
  `/Users/williammacready/code/python/pyncd.worktrees/tensor-logic-boundary-policy-review`.
- Verified prototype:
  `/Users/williammacready/code/python/pyncd.worktrees/expression-readiness-authoring`.
- Independent physical rehearsal:
  `/Users/williammacready/code/python/pyncd.worktrees/expression-readiness-plan-rehearsal`.
- Namespace of new production-shaped modules: `LeanNCD.Semantics`.
  Prior spike namespace remains `LeanNCD.TensorLogicSemanticCoreSpike`.

Inputs:

1. [evidence.json](expression_readiness_artifacts/evidence.json): measured
   representation, symbols, fixtures, hypotheses, reuse, task suggestions,
   final replay, and controller budget observations.
2. [mutation_results.md](expression_readiness_artifacts/mutation_results.md):
   final 27/27 manifest cycles, intended failures, green restore, and byte equality.
3. [expression_readiness_mutations_post.json](expression_readiness_mutations_post.json):
   actual observed `expect` strings and unique replacement anchors.
4. Ordered [00 preflight](expression_readiness_patches/00-context-preflight.patch),
   [01 types/expressions](expression_readiness_patches/01-types-expr.patch),
   [02 interpretation/readiness](expression_readiness_patches/02-interpretation-readiness.patch),
   [03 fixtures/integration](expression_readiness_patches/03-fixtures-integration.patch).
   These mechanical exports, not hand-transcribed Lean, are execution code.

The evidence is additive and contains superseded early-stage statements:
`patch_application` says rehearsal pending; early build/scope entries say mutation
cycles were not run or outcomes not claimed. Those described earlier authoring stages.
The later `mutation_protocol`, `final_patch_replay`, supplemental proof evidence,
final mutation table, and the parent's verified handoff supersede them.
Do not repeat the obsolete statements as final verification gaps.
Artifacts themselves were not modified by dispatch B.

## Verified implementation inventory

| Patch | Files |
| --- | --- |
| 00, controller only before T1 | [leanncd/AGENTS.md](../../leanncd/AGENTS.md), `leanncd/AGENTS_REFERENCE.md` |
| 01, T1 | `leanncd/LeanNCD/Semantics/Types.lean`, `leanncd/LeanNCD/Semantics/Expr.lean` |
| 02, T2 | `leanncd/LeanNCD/Semantics/Interpret.lean`, `leanncd/LeanNCD/Semantics/Readiness.lean`, `leanncd/LeanNCD/Semantics/Completeness.lean`, `leanncd/LeanNCD/Semantics.lean` |
| 03, T3 fixtures | `leanncd/test/Semantics/ExpressionTest.lean`, `leanncd/test/Semantics/NativeTest.lean`, `leanncd/test/Semantics/ContractTest.lean` |
| 03, T3 integration | [LeanNCD.lean](../../leanncd/LeanNCD.lean), [lakefile.toml](../../leanncd/lakefile.toml), [leanncd/AGENTS.md](../../leanncd/AGENTS.md), [Semantics/AGENTS.md](../../leanncd/LeanNCD/Semantics/AGENTS.md), [prior spike record](tensor_logic_semantic_core_spike_record.md) |

Monospaced paths name planned files not yet created in this plan-only tree;
the corresponding ordered patch links above provide their verified code.
Existing current-repository file/guidance links remain links.
Patch inventories and prototype paths were checked during write-up.
All four patch SHA-256 values matched the evidence during dispatch B:

| Patch | SHA-256 |
| --- | --- |
| 00 | `41829db84334b1dfad07b895698a79cb8565fb3aed53eb9e2e2eaf5c089133cd` |
| 01 | `8d8187f579558757dfdb36d889a1aa9af262b035727c4cf8d9209cca2c363fce` |
| 02 | `beccb485d85221cfeb072feffcd3f45d2c95587a6edd1338effc44f3a3457111` |
| 03 | `d65394550f86a8eb29e668783b7f8bf6ce42f68548d44494f76dd535f5e0aebe` |

Final ordered replay tree: `2bca1c43db13dc6078aaa45a43ff4e489fe2de2e`.
Evidence records clean application of 00+01+02+03 at the pinned baseline,
all output files matching the compiled staged snapshot, and all Lean/config bytes
matching the independently applied successful physical rehearsal.
The parent verified those comparisons; dispatch B checked the artifact hashes
and inventories, not a second patch application.
Preflight reduces root hook sections 6,957 -> 2,882 characters and preserves
full Patterns verbatim in the reference.

### Final review correction: execution base (Medium)

The exact old-baseline execution gate conflicted with normal new-slice preparation
fast-forwarding to published local `main`, which also delivers the plan/patches/manifest.
Corrected Section 4 and T1's prerequisite: execution may use published local main or
an artifact-only descendant after clean-status, baseline-ancestor, and unchanged
protected-source/specification guards, all before 00. The ordered patch checks remain
mandatory. Meaningful protected-path changes or conflicts stop for controller
adjudication, with no passive port/rebase. Execution commands use inherited artifacts;
no copy from the old pin or ephemeral authoring checkout is required.

**Medium correction PENDING reviewer confirmation.** Parent will actually replay
the guards against the artifact-only commit before publication. Dispatch B has
validated only the document changes, not run those guards or claimed their success.
All existing pinned replay/build/mutation results remain rehearsal provenance.

## Verification results inherited from verified execution

| Check | Observed result | Attribution |
| --- | --- | --- |
| T1 `LeanNCD.Semantics.Expr` | Passed, 2,944 jobs | Parent's pinned ordered rehearsal handoff. |
| T2 `LeanNCD.Semantics` | Passed, 2,948 jobs | Parent's pinned ordered rehearsal handoff. |
| T3 full default | Passed, 8,686 jobs | Verified prototype/rehearsal and final handoff. |
| Supplemental clause proof target | `Semantics.ContractTest` passed; full default also passed | Supplemental evidence, includes exact reduction instantiations. |
| Ordered final patches | Clean apply at `44296ad`; staged/rehearsal byte comparisons pass | Final replay evidence and parent verification. |
| Final manifest, actual execution | 27/27 pass; intended failure seen; restored build green; file byte-identical | Independent rehearsal final mutation results, not merely `--check`. |
| Axiom audit | Standard `propext`, `Quot.sound`, `Classical.choice` only; no `sorryAx` confirmed | Verified proof output and parent handoff. |
| Exported interfaces | All correctly compiled exported interfaces rechecked with `check-snippet.sh` from `import LeanNCD` | Parent's final verification handoff; no new Lean block authored here. |

The early umbrella count of 2,947 jobs predates `Completeness` and final fixtures.
It is not substituted for the final T2 result. The old spike's historical 8,676-job
build is likewise historical, not the current full default result.
Existing dependency warnings remain flagged; green build is not a warning-free claim.
Dispatch B performs documentation validation, not another Lean build.

### Exact fixture accounting

Counts were extracted from the verified test files, read in bounded code windows,
and confirmed by declaration/command counts. Do not infer exhaustive coverage.

| Module | Guards | Theorem fixtures | `#eval` observations | Axiom prints |
| --- | --- | --- | --- | --- |
| `Semantics.ExpressionTest` | 23 | 0 | 2 | 0 |
| `Semantics.ContractTest` | 8 | 10 | 0 | 4 |
| `Semantics.NativeTest` | 5 | 1 | 1 | 1 |
| Total | 36 | 11 | 3 | 5 |

Thus T3 has 47 concrete assertion units, not 47 independently mutation-tested
semantic laws. Five theorems are elaboration-negative tests with `fail_if_success`.
The other six are axis-order inequality, two exact reduction clauses, independent
nonselected-lane impossibility, the actual signed-coordinate seam, and exact Complex.
The evidence's 13 fixture categories are a grouping, not a judgment count.
Both exact-reduction fixtures are already included in these counts.
Updated evidence also records 5 named core theorems in `Readiness` and 14 in
`Completeness`: 19 generic theorems, separate from the 11 theorem fixtures.

Observed values and discriminators are retained in the live plan: constants/remaps
9 versus 7; missing resolved coordinate waiting rather than zero; strict undefined
operands; empty zero/empty complete array versus outer domain rejection; binder
42 versus 28; Cartesian value 14 and six reads; selected/array-primitive values 6/8;
nullary 13 and heterogeneous 14; signed -1/rejection guards; native bit patterns;
and exact noncomputable I*I=-1. None were hand-derived for this write-up.

### Mutation accounting and strengthened controls

The final manifest has 27 entries, every verification `task` is `3`, and every
`expect` list matches its observed evidence entry. `owner_task` is source ownership,
not a license to run cycles before fixtures/config integration.

- 11 implementation/proof mutations.
- 5 type-admission contrast controls: legal neighbors substituted inside negative tests.
- 11 fixture/registry/metadata contract perturbations.

They are not all implementation regressions. Some failures arise from generic
kernel proofs before concrete guards. No claim of isolated mutation coverage for
every one of the 47 assertion units is made.
Weak proposed controls were strengthened before the final verified run:
constant footprint is well typed with a positive layout-count guard;
raw/resolved distinction uses toNat-before-mod at negative raw input;
unavailable fallback targets actual `evalReady`; strict primitive-argument bypass
targets source sequencing. Expected strings came from observed logs, without
diagnostic line numbers. Only the post manifest is needed for new candidate code.

## Semantic fidelity and provisional choices

- The presentation is of structurally ADMITTED semantic forms. Gamma is a typed
  valuation space; callbacks are semantic maps/predicates; products extend binders.
  This is not a named affine syntax checker or proof of every Section 14 judgment.
- Open scalar sorts and carriers admit heterogeneous signatures. Exact sum theorems
  require only the selected sort's `AddCommMonoid`, zero/add agreement, and successful
  body values. Aggregate equality gives no reverse summand inference.
- `tab_complete`, `reduce_defined_iff`, `reduce_empty`, `at_some_iff`, and
  `prim_some_iff` independently characterize clauses, not just wrapper agreement.
- Footprint stability and readiness consistency preserve values AND undefinedness.
  `ready_complete_extension` uses zero only to construct a mathematical witness.
  Low-level `evalWith none` needs readiness/complete-store scope to be interpreted;
  public classification uses `interpret` or `evalReady`.
- Arrays are complete coordinate functions with a checked layout equivalence.
  Alternative storage formats need their own representation proof, not a list cast.
- Metadata retains axis UID/order but does not prove global source-signature
  consistency. Declaration refs and bounded coordinates are expression-level;
  complete input binding, including empty required inputs, remains program-level.
- Reuse is concrete: existing UID, `finProdFinEquiv`, checked native unary APIs,
  and the old spike's actual realized `StMat` coordinate witness. The signed seam
  is raw-coordinate equality only, not a D-graded functor or full categorical backend.
- New API is reachable from `import LeanNCD`; default `Tests` registers three modules.
  `ContractTest` imports the old spike, so default tests now check it INDIRECTLY.
  Root `LeanNCD` does not import the spike. Patch 03 qualifies local guidance and
  the historical spike record rather than retaining a non-default-only claim.
- No writes, occurrences, collection, models, publication, ranked scheduler, JAX,
  categorical algebra, native complex64, or production acceptance changes.

These choices delimit this slice; broader semantics are not certified bug-free.
Parked questions require separately agreed scope: source judgment/DSL correspondence
and syntactic context laws; program input/model/demanded-task obligations; backend
storage/refinement and full categorical interpretation. Each is separate substantial
follow-on work with dispatch counts not yet sized, not an authorized task here.

## Budget observations and limits

- Dispatch B hard limit: 30 tool-bearing turns; approximately 250k peak context.
  Initial write-up used 14 tool-bearing turns including document validation.
  The controller handoff brought the count to 17; navigation correction to 20;
  the bounded Medium execution-base correction brings the cumulative count to 23,
  within the turn cap. Peak and aggregate token
  telemetry are not reliably measured by the supplied transcript tool.
- Every execution dispatch is budgeted at about 60 turns / 250k peak.
  Execution ceiling approximately 175M cumulative input tokens; authoring target
  approximately 50M. These are planned limits, not measured compliance results.
- Evidence records a historical SDK controller prompt snapshot of **453,827**
  tokens at `2026-10-06T19:15:24.548Z`, above the approximately 250k target.
  This observed context overrun was surfaced, not hidden.
- That snapshot is controller-only, not an isolated dispatch-B peak or an aggregate
  authoring cost. Reliable cumulative authoring totals and per-agent peaks are unmeasured.
- The prescribed `token-report.py` found no transcript for the supplied SDK session
  ID `b7b54e50-2051-42c5-be3e-9a26cfe9ee84`. Do not invent totals or compliance.
  Dispatch B reran that meter and confirmed the same unavailable-transcript result.
- Mitigation: prototype/verification and fresh write-up separated; bounded windows;
  source patches instead of copied Lean; live execution plan separate from this record;
  T3 can split integration and validation into fresh contexts within the SAME task.

## Authoring checklist and pending gates

- [x] Two-stage authoring: verified prototype, then fresh-context write-up.
- [x] Mechanical ordered patches identified; hashes/inventories checked in dispatch B.
- [x] Parent verified clean pinned replay and staged/pristine Lean/config byte identity.
- [x] Exact scalar/array/binder/readiness scope mapped to requested specification sections.
- [x] Fixture values inherited from observed runs, not invented.
- [x] Concrete fixture counts inspected; mutation classes kept distinct.
- [x] Actual final manifest execution, intended failures, and byte-identical restoration recorded.
- [x] Strong index/binder/array distinctions retained; no weak/no-op control substituted.
- [x] Donors named; new specification fixtures explicitly have no old-source donor.
- [x] Independent clause theorems and selected-sort sum hypotheses specified.
- [x] Public discovery and indirect default spike coverage stated accurately.
- [x] Controller preflight and root-hook budget preparation scheduled before T1.
- [x] No authored Lean code fences/transcription; no new snippet compilation needed here.
- [x] Parent confirms all exported interfaces rechecked via `check-snippet.sh` from `import LeanNCD`.
- [x] Live task citations use identifiers, not `File.lean:NNN`.
- [x] Documentation sweeps are commands, not a new heavyweight dispatch.
- [x] Initial write-up validation incorrectly accepted prototype-only link targets.
  Corrected during final review: 20 future-file links (10 per document) replaced
  with exact monospaced planned paths, retaining corresponding real patch links.
  All 32 surviving links resolve in the current repository; no ephemeral prototype links.
  ASCII only; no Lean fences or numeric Lean line citations.
- [x] Historical context breach and missing telemetry surfaced.
- [ ] Medium execution-base correction: reviewer confirmation and parent guard replay
  against the artifact-only commit before publication.
- [ ] Parent final review lens 1: semantic/proof fidelity, findings and adjudication.
- [ ] Parent final review lens 2: types/backend/categorical/reuse, findings and adjudication.
- [ ] Controller accepts authoring documents and controls any publication.
- [ ] At execution: controller runs all 27 cycles and full default build on the execution branch.
- [ ] At execution close-out: measured costs where available, breaches/limits, all review outcomes.

**Review status remains PENDING.** Verified rehearsal is not execution-branch
completion and not a substitute for either whole-branch review.
