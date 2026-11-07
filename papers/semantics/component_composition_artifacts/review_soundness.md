# Whole-branch soundness review

## Scope and frozen evidence

Review complete. Lens: high-confidence mathematical, design and public-API
defects in static sealed whole-tensor composition. Fixed source range:
`16721af5..06d4e470a0c30f00ab5347e13f7c358e55593c17`.
Only this receipt is written; no source changes, nested agents, commits,
build reruns or mutation reruns.

Authority: `component_composition_handoff.md`, relevant sections of
`categorical_tensor_logic_component_interfaces.md`, and the exact goal in the
review request. Rank/phase results, model gluing, categorical laws and general
adapters are expressly outside the implemented goal.

Controller-reported full build and restored mutation cycles are separate gates,
not independently reproduced evidence from this review. Task approvals below
will concern the frozen bytes of the eight manifest patches, not newly made
edits; subsequent controller exact replay is a separate checkpoint.

## Findings

**Clean: no high-confidence scoped mathematical, design or public-API defect
found.** No severity-rated finding or within-static-goal repair is required.
This verdict is for the fixed source range, not an assertion that the excluded
future theorems have been proved or that all controller release gates have
already completed.

## Task review evidence

Manifest SHA-256 values verified for all eight exact patches. All 27 listed
files equal their fixed source-HEAD blobs; every changed `leanncd/` file is
covered. The historical patch/prototype copies are not independent review
targets.
Each of the eight patch files also equals the exact `git diff --binary` for
its manifest file list over the reviewed fixed range. Approvals therefore
identify the actual frozen task bytes, not merely their filenames.

| Task / exact patch | SHA-256 | Soundness review status |
| --- | --- | --- |
| 1 `task_01_scope.patch` | `ca7e3b372803ed1ff9c0232c3092fb8fefa684ccbb4c398cad6d354c68a8c74b` | Approved: exact local ports, bijective certified boundary, disjoint retained universe and IDs; experiment-only target registration. |
| 2 `task_02_source-schedule.patch` | `c411eff37c5a090d0cec31349a93ffa0553017fcefa4efb73b5a63826c2c0716` | Approved: complete guarded programs, occurrence/key equivalences, ordered tensor/key append. |
| 3 `task_03_closure.patch` | `32e962c224a480f55f335970631119236c02b0344c5f37b24cf7b31b613aa485` | Approved: closure facts extracted and sufficient, concrete scope derived, canonical closure proved. |
| 4 `task_04_match.patch` | `f7c77859b11adf757534b595973a2502f7b3c39d349e037e3fab35b3db117410` | Approved: positional occurrence bijection, dependent destinations, arbitrary partial-store agreement, complete priority and all nine fields. |
| 5 `task_05_port-fixtures.patch` | `319969c023e9dd607fcc01141301f236e9fd72a4715453f5e92e4b73a3bdfa60` | Approved: genuinely local scalar source/graph, strict failure/private completion, zero collectors, exact empty ports and input-presence/order discrimination. |
| 6 `task_06_advanced-fixtures.patch` | `80a872a87dc50bec115f37d2dd620ec1904e3a643cb080b9a021584b0cf29611` | Approved: guarded equal-valued positional multiplicity, private collisions, unsorted collector/capability orders and nonpalindromic axis read sequence. |
| 7 `task_07_correspondence-controls.patch` | `962fb591c453426f6b6619be1e08df8583a25e43b75aeec6c4057432c658ca20` | Approved: existing correspondence applied after construction, typed negatives with positive neighbors, graph-only counterexamples and honest mutation classes. |
| 8 `task_08_discovery.patch` | `9fc913130f00a619e53d1bbf792c8d4960298ea1049bab9186b185a6a21301e9` | Approved: discovery points to the public experiment API; implemented static facts, historical checkpoints, mutation limits and unproved future work remain distinguished. |

Core checkpoint: no high-confidence scoped defect discovered. `closureScope`
is proved from roles, output-definedness, the explicit boundary and component
closure, not a premise of `compose_match`. Only readable membership is
deduplicated; writer footprints and collector/capability sequences are not.

Fixture/correspondence checkpoint: no scoped defect discovered. Scalar checks
retain four writers plus three publications: failure at event six after output
publication for `other = 0`, completion at seven with private `Audit = 1/2`
for `other = 4`. The zero pair retains an empty-capability collector and five
events. Empty tensors retain whole ports and `[20, 0, 3]` validation order,
distinguishing present empty input from absence and simultaneous faults.
Collision checks retain valuations 2 then 0, two equal `+1` writers, distinct
private values and both nonsorted orders. Axis checks retain the full
`p/q/p/q` footprint mapped to `(2,0)/(0,1)/(2,0)/(0,1)` and output 14.
These are reviewed executable assertions, not independently rerun tests.

The 16 post-code controls comprise seven live-proof controls, two typed
controls, three fixture-source/binding controls and four graph-counterexample
controls. They are not 16 live executor mutations or complete per-assertion
kill coverage. No altered graph counterexample supplies a forged match.

## Whole-branch coverage and conclusion

All 18 added experimental Lean modules were read in bounded windows:
`IndexedComponentCompositionScope`, `Program`, `Schedule`, `Closure`,
`Assemble`, `AssemblyAudit`, `Match`, `Priority`, the public
`IndexedComponentComposition`, `LocalFixtures`, `PortFixtures`, `Test`,
`CollisionFixtures`, `AxisFixtures`, `InterfaceTest`, `CounterexampleTest`,
`CorrespondenceTest`, and `IndexedComponentClosureFacts`. The abbreviated
module names in this list carry the `IndexedComponentComposition` prefix
except the explicitly named closure-facts module.
The changed `leanncd/lakefile.toml` and `leanncd/AGENTS.md`, task-seven audit
and mutation manifest, and all task-eight discovery/evidence documents were
also reviewed. Immediate unchanged match, program, transport, fixture-check
and canonical-close definitions were checked as dependencies.

The review specifically checked complete noninput collector coverage,
including zero-writer fibers; injective images and sealed downstream
destinations; statement/valuation/guard preservation; source occurrences
bijection to writer **positions**, not values; dependent destination casts;
ordered full footprints; agreement for every partial store; full mapped
priority; checked tensor/tag/capability freshening; and exact empty-port
metadata/input presence. The public constructor has no additional composite
closure, match, execution, action/state/fiber or rank premise.
No runner, primitive, partiality or production-import change occurs in the
reviewed source diff.

All eight task patches are approved under this whole-branch soundness lens.
The controller's subsequent exact-replay checkpoints may reference these
frozen-byte approvals as task-review evidence. This receipt does not claim
those later replays were performed by the reviewer. It is not the separate
whole-branch instruction-compliance lens or a release/integration receipt.

## Budget and reviewer actions

23 action/tool turns, counting each parallel batch as one turn; cap 50.
Retained context is estimated below 100k tokens, below the 250k cap; peak
context is not independently instrumented. No budget breach observed.
Every source read window was at most 60 lines. Only this requested receipt
was written, incrementally. No nested agent, source edit, commit, build or
mutation execution was performed.
