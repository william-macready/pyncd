# Reference-machine soundness execution record

## Scope and disposition

Executed the three task groups in the
[published plan](reference_machine_plan.md) on 2026-10-07.
The implementation is relation-only semantic validation, not a production
executor or an executable scheduler.

| Task | Commit | Controller task review |
| --- | --- | --- |
| Tagged reference machine | `4aac11f` | PASS: initialization, three rules, dependent tags, unchanged failure snapshot, terminality, whole-store completion |
| Conservation and reached-run soundness | `77d1b74` | PASS: proof-only history, retained tagged sums, read stability, witness-free successful model, whole-store uniqueness, reached-failure exclusion |
| Fixtures, discovery, scoped guidance | `c08dc3f` | PASS: donors/discriminators, 12 constructions, 33 named theorem declarations, both imports and default test discovery |

Per-task reviews were performed directly by the controller. Two separate
whole-branch reviewers subsequently reviewed `582b28c..c08dc3f`:

- Proof-semantic lens: **CLEAN**, no actionable findings.
- Transition/type/fixture/discovery lens: **CLEAN**, no actionable findings.

Both reports concern committed sources and the stable disposable replay,
not transiently mutated working-tree files. Their reported budget estimates
were approximately 14 and 16 tool-bearing turns, respectively. They did not
rerun controller builds or mutations; the controller owns the receipts below.
The controller accepted both clean dispositions.

## Preparation and exact replay

Execution worktree:
`/Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan`.
Execution branch: `agents/implement-soundness-plan`.
Prepared execution/rehearsal base:
`582b28c2de4db9a00f3a432acb07f9f43854efa2`.

The preparation script advanced the initially stale checkout from `2e850b1`
to local main. It copied a donor cache without building in or modifying the
donor: 8101 Mathlib oleans / 8094 sources, and 216 project oleans.
Preparation omitted `--plan`; no disposable ledger was created.

Preflight independently verified clean status, original-base ancestry,
all 16 protected source SHA-256 values, all three exact patch SHA-256 values,
and absence of all four new outputs, including symlink checks. The covering
AGENTS files had zero characters in the named hook sections
Pitfalls/Checks/Patterns/Context, before and after integration.

The original patches applied sequentially with `git apply --check`, followed
by `git apply`, and each task's target build passed. No patches or protected
sources were rewritten. The four new Git blobs match the published artifacts:

| New module | Git blob |
| --- | --- |
| [Machine](../../leanncd/LeanNCD/Semantics/Machine.lean) | `9685fa7cb8e64dea41676e5f7e05f3a65e37cde3` |
| [Invariants](../../leanncd/LeanNCD/Semantics/Invariants.lean) | `b52289195c0efac9f926b6257c6f6e57cbde4fff` |
| [Soundness](../../leanncd/LeanNCD/Semantics/Soundness.lean) | `a8882d25f6626bd7e655b5631547967b7748b7fb` |
| [ReferenceMachineTest](../../leanncd/test/Semantics/ReferenceMachineTest.lean) | `9204a011f7ad5fc4966ffb3c4775678be550b4e8` |

The four existing integration-file hunks were inspected against the prepared
base. Unrelated binary32-default additions in the lakefile and top-level
Lean guidance were preserved; those existing files need not equal old
prototype blobs.

The controller also created a detached disposable replay at
`/Users/williammacready/.copilot/session-state/bedd56f8-068c-4ee3-acb6-e9edfec95195/files/reference-machine-replay`,
pinned to the prepared base. It independently refreshed LeanNCD, checked and
applied each original patch in order, built each task target, checked both
manifests, executed both actual suites, and built the full default targets.
All eight replay deliverables matched the execution sources byte-for-byte
after restoration. The replay contained only four known new files and four
known integration edits.

Two controller verification-script assumptions failed and were corrected:
the initial cross-check read an execution file during an intentional mutation
and was repeated against immutable committed blobs; a cleanup assertion
initially required no untracked replay files instead of the four expected
new patch outputs. Neither failure was a patch, proof, build, mutation-suite,
or restoration failure. The corrected checks passed.

## Actual validation and restoration

| Checkout / gate | Production proof/type cycles | Fixture contrasts | Restoration and expected diagnostics |
| --- | --- | --- | --- |
| Execution, task gates | 12/12 PASS | 12/12 PASS | Every expected failure seen; every file byte-identical; every restored target green |
| Execution, final repeat | 12/12 PASS | 12/12 PASS | Every expected failure seen; every file byte-identical; every restored target green |
| Independent disposable replay | 12/12 PASS | 12/12 PASS | Every expected failure seen; every file byte-identical; every restored target green |

No entries were filtered or skipped. There are **12 production controls** and
**12 fixture contrasts**, repeated for verification, not 24 independent
implementation regressions. Production runtime oracle kills: **zero**.
The production mutations are proof/type rejections, including changed-premise
application failures. The fixture controls may also fail during elaboration.

Fixture control mapping:

| Control | Construction |
| --- | --- |
| F01 | duplicate |
| F02 | collision |
| F03 | noStatements |
| F04 | zP |
| F05 | badP |
| F06 | excludedP |
| F07 | dependentP |
| F08 | waitingBad |
| F09 | cycleP |
| F10 | roleProgram |
| F11 | valuationP |
| F12 | scalarRole |

The target build independently observed:

- 33 top-level named theorem declarations, including helper and reachability
  declarations, across 12 constructions.
- Donor collection values: `[4, 9, 0, 0, 9, 5, 14, 3 / 4]`.
- New readiness labels: `["notReady", "notReady", "undefined"]`.
- Donor readiness labels: `["undefined", "notReady"]`.
- Public import reachability through LeanNCD and LeanNCD.Semantics, and
  inclusion of Semantics.ReferenceMachineTest in the default Tests glob.

The execution discovery build, final full/default build, disposable replay
full build, and replay post-mutation full build passed with **8695 jobs**.
This is an observed count for this revision, not a permanent requirement.
Final execution tracked-source diff and status were empty, and all 16
protected inputs and all three patch digests remained unchanged.

### Axioms and warnings

The controller independently parsed the actual build inventories for
reachable_invariant, successful_model, candidate_preserved, successful_unique,
successful_admInput, successful_denotation, failed_no_model,
duplicate_model_without_witness, failure_excludes_models, and cycle_blocked.
Every inventory contains only `propext`, `Classical.choice`, and `Quot.sound`.
No new sorry, sorryAx, axioms, native_decide, or algebra instances were added.

The known replay warnings remain: unused section variables in
finalStore_published and publish_extends, and unused simp argument ops in the
cyclic-model fixture. Full builds also replay unrelated pre-existing sorry
and linter warnings. This is not a warning-free repository build, and these
unrelated issues were not repaired or used by the new results.

## Commands and retained evidence

Controller session artifacts are retained at:
`/Users/williammacready/.copilot/session-state/bedd56f8-068c-4ee3-acb6-e9edfec95195/files`.
They include task and final build logs; task, final, and disposable replay
mutation tables/logs; controller axiom/mapping audit; replay audit; both JSON
review reports; and documentation sweep/classification files.

The following commands were run from the execution worktree. The Python
controller gates invoked the same wrappers with resolved absolute script
and manifest paths for the final and disposable suites.

```bash
bash .claude/skills/new-slice/prepare-worktree.sh
bash leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd LeanNCD
git apply --check papers/semantics/reference_machine_patches/01-machine.patch
git apply papers/semantics/reference_machine_patches/01-machine.patch
bash leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd LeanNCD.Semantics.Machine
git apply --check papers/semantics/reference_machine_patches/02-invariants-soundness.patch
git apply papers/semantics/reference_machine_patches/02-invariants-soundness.patch
bash leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd LeanNCD.Semantics.Soundness
bash leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd papers/semantics/reference_machine_mutations_post.json
bash leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/.copilot/session-state/bedd56f8-068c-4ee3-acb6-e9edfec95195/files/reference_machine_task02_mutation_results.md /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd papers/semantics/reference_machine_mutations_post.json
git apply --check papers/semantics/reference_machine_patches/03-fixtures-integration.patch
git apply papers/semantics/reference_machine_patches/03-fixtures-integration.patch
bash leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd Semantics.CollectionModelTest Semantics.ReferenceMachineTest
bash leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd papers/semantics/reference_machine_fixture_mutations_post.json
bash leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/.copilot/session-state/bedd56f8-068c-4ee3-acb6-e9edfec95195/files/reference_machine_task03_fixture_contrast_results.md /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd papers/semantics/reference_machine_fixture_mutations_post.json
bash leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd LeanNCD Tests
python3 .claude/skills/slice-plan/token-report.py bedd56f8-068c-4ee3-acb6-e9edfec95195
```

Exact final actual-suite commands:

```bash
bash /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/.copilot/session-state/bedd56f8-068c-4ee3-acb6-e9edfec95195/files/reference_machine_final_mutation_results.md /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/papers/semantics/reference_machine_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/.copilot/session-state/bedd56f8-068c-4ee3-acb6-e9edfec95195/files/reference_machine_final_fixture_contrast_results.md /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/papers/semantics/reference_machine_fixture_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/implement-soundness-plan/leanncd
```

## Documentation, budget, and remaining boundaries

The scoped documentation sweep classified 1727 hits across 116 files:
21 current-guidance hits, 528 historical audit/plan/prototype hits,
62 authority hits, 26 prospective boundary-policy hits, and 1090 other
subsystem/backend/conceptual hits. The whole papers/leanncd value sweep
classified 97 hits across 42 files. Historical counts and earlier capability
gaps remain historical; the current semantic guidance now includes the
reference machine and preserves its exclusions. No additional documentation
correction or side issue was required.

The token-report helper reported no transcript for this Copilot session.
Cumulative tokens, peak context, and measured controller turn count are
unavailable; budget compliance is not certified. Reviewer estimates are
not telemetry. The prototype's conflicting 76-tool-call versus 48-turn
estimates remain unresolved historical evidence, not proof of compliance.

No scheduler, progress/maximal-run completeness, rank, finite termination
measure, cyclic solver, general model-existence theorem, source elaboration,
production/backend replacement, precision refinement, or full categorical
interpretation was added. Premise-eligibility fixtures are not advertised as
separate transition-absence theorems. The cyclic blocked fixture is not
advertised as separately reachable.

Local integration is authorized after these completed gates. Pre-integration
main is `146366a94d96cae6e936af930c75ec98ac65b789`; its two concurrent
binary32/binary64 documentation commits do not touch any deliverable or
protected prerequisite and must be preserved. Integration and cleanup receipts
are retained in controller session artifacts. No remote push is authorized.
