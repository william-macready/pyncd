# Coordinate ranks, finite measure, and maximal-run correspondence

## 1. Authority, authorization, and artifact boundary

**Full path:** a new proof/soundness capability, replayed as three independently
rejectable task patches. This is AUTHORING PHASE B, **PLAN ONLY**. No prototype
is a release or merge target. Independent controller verification and both final
review lenses passed; this plan is **verified and execution-ready**, as recorded
in the separate [authoring record](coordinate_ranks_finite_measure_authoring_record.md).
The record is not an execution completion record.

Authority, as identified by the supplied artifacts and controller brief:
[tensor_logic_semantics.md](tensor_logic_semantics.md) Sections 23.4 and 26.4,
and [lean_executable_semantics_path.md](lean_executable_semantics_path.md)
Section 5.1. The [reference-machine plan](reference_machine_plan.md) and
[reference-machine authoring record](reference_machine_authoring_record.md)
are style/guard precedents ONLY; none of their verification assertions transfers.

Implementation source is the mechanically emitted, prototype-compiled patches:
[01 ranks/measure](coordinate_ranks_finite_measure_patches/01-ranks-measure.patch),
[02 progress/correspondence](coordinate_ranks_finite_measure_patches/02-progress-correspondence.patch),
[03 fixtures/integration](coordinate_ranks_finite_measure_patches/03-fixtures-integration.patch).
There are no Lean code blocks: replay exact bytes, do not transcribe or redesign.
The [evidence](coordinate_ranks_finite_measure_artifacts/evidence.json) contains
the prototype's sequential temporary-index replay assertion; there is NO separate
coordinate-ranks `replay-audit.json`.
The [emitter](coordinate_ranks_finite_measure_artifacts/emit-patches.py)
WRITES patches and evidence and requires prototype commits/logs. Do not run it
as an execution prerequisite or call it read-only.

| Provenance only, never required implementation HEAD | Value |
| --- | --- |
| Prototype base | `a2be7b9048ccfc70ab9d74cb19c5e5ee79861357` |
| Task 01 commit | `2de6c4d2a2d37043d22fed1cf5d608497450a517` |
| Task 02 commit | `08297501d4e1f8310b4f5901861b2683fc79e600` |
| Task 03 candidate | `426fe581c65e3478b9894de9ee414bba4a272e0d` |
| Candidate tree | `0ce025c588da2687a519bde099cb5eadd8e2295a` |

Execution starts from later **LOCAL main**, or a controller-selected compatible
descendant. At authoring, planning HEAD and local main both resolve to
`e13fd6f30303c3caec8ad470652b59907d3bbf2b`. The controller reports an unrelated
f32 merge touching seven non-semantic files. Preserve those changes; compatibility
is a gate, not an inference from ancestry. Controller rehearsal on that newer
main passed; see [controller verification](coordinate_ranks_finite_measure_artifacts/controller-verification.json).
Parent reports the prerequisite full build green, 8,695 jobs, at the prototype
base; that is attributed controller evidence, not this author's build.

Only the controller publishes/commits this plan package here. Later implementation
integration is conditional on all execution gates; never merge the prototype.
No remote push. Do not modify or build in unrelated branches/worktrees.

## 2. Exact semantic contract

All production identifiers below are in namespace `LeanNCD.Semantics.Program`.
Fixture identifiers are in `LeanNCD.Semantics.RankedMachineFixtures`.
Linked new modules are **FUTURE/generated**, absent in the planning tree.

### Coordinate dependencies and explicit certificate

- `dependencies @` [Ranks.lean](../../leanncd/LeanNCD/Semantics/Ranks.lean)
  uses the existing `footprint @`
  [Interpret.lean](../../leanncd/LeanNCD/Semantics/Interpret.lean).
  A dependency witnesses a guard-admitted tagged occurrence in the exact
  destination address's fiber. Occurrences targeting other coordinates and
  guard-rejected valuations do not contribute edges. Tags retain multiplicity
  for measure even though dependencies are a set.
- Input addresses have no outgoing dependencies. Input sources remain genuine
  footprint dependencies and are initially available.
- Strict masked operands, all reduction coordinates, whole tabulations under
  selection, and all heterogeneous typed primitive operands retain their
  existing strict footprint. Resolved constant boundaries contribute no edge.
  Rank construction does not change interpretation or boundary resolution.
- `RankCertificate @` [Ranks.lean](../../leanncd/LeanNCD/Semantics/Ranks.lean)
  supplies `Address σ -> Nat` explicitly, with STRICT decrease along every
  dependency. It ranks coordinates, not tensor identifiers; is input-value
  independent; and certifies no primitive definedness.
- No scheduler, source checker, rank synthesis, graph-acyclicity equivalence
  proof/checker, backend changes, or source/float refactor is included.

### Rank-independent finite measure

`DefinedAddress @` [Ranks.lean](../../leanncd/LeanNCD/Semantics/Ranks.lean)
is a defined tensor together with its coordinate. Inputs are not counted.
Zero-extent tensors have no coordinates; rank-zero scalar coordinates are
`Unit`, hence one address, not zero.

`measure @` [Measure.lean](../../leanncd/LeanNCD/Semantics/Measure.lean)
is total pending tagged occurrences PLUS unpublished DEFINED address count.
It includes nonoutputs and empty destination fibers. Initially:

`mu0 = occurrenceCount + card DefinedAddress`.

`consume_measure` and `publish_measure @`
[Measure.lean](../../leanncd/LeanNCD/Semantics/Measure.lean) each establish
exactly one less running measure, including zero-valued contributions and
zero-valued empty-fiber/nonoutput publications. Undefined evaluation is a
terminal failure, not consumption/publication: it may add ONE total transition
beyond `mu0`. `stateMeasure` is running `mu + 1`, failed `0`; every step strictly
decreases it. No rank or supplied model is needed for termination.

`Trace`, `trace_bound`, `running_trace_bound`, `failed_trace_bound`,
`step_wellFounded`, and `no_infinite_chain @`
[Measure.lean](../../leanncd/LeanNCD/Semantics/Measure.lean) pin these boundaries.
Running-to-running traces have at most initial running measure transitions;
running-to-failed traces have at most that measure plus one. Do not state
an exact one-unit `stateMeasure` drop for the undefined step.

### Ranked progress and correspondence

`ranked_progress @`
[Progress.lean](../../leanncd/LeanNCD/Semantics/Progress.lean) requires the
explicit certificate, a well-formed input, reachability from initialization,
and incompleteness; NOT a supplied model witness. Reachable invariants make
inputs available. A least-ranked unpublished defined address either publishes
an exhausted fiber or has a ready contributor, yielding contribution OR
undefined failure. Ranks exclude blocking, not failure.

`Terminal` means no outgoing step; `Maximal @`
[Progress.lean](../../leanncd/LeanNCD/Semantics/Progress.lean) means a reached
terminal endpoint. Arbitrary finite stopped prefixes are not maximal.
`terminal_extension` is rank-independent for any state, and
`maximal_extension` gives every reached prefix a reached terminal extension.
Unranked terminal blocking can still occur; do not turn extension into success
without the ranked hypotheses.

For ranked reachable maximal endpoints:

- `maximal_dichotomy`: successful complete running state OR explicit failed
  state excluding every model.
- `model_maximal_success`: model existence forces success, with the UNIQUE
  FULL store equal to that model, not merely equal output projection.
- `no_model_maximal_failure`: no model forces failure.
- `initialization_iff_singleton`: initialization reaches a successful full
  store exactly when the model set is that singleton.
- `successful_schedules_agree`: any two successful schedules have the same
  full store; this theorem itself does not require a rank certificate.

These identifiers are all `@`
[Progress.lean](../../leanncd/LeanNCD/Semantics/Progress.lean).
Denotation reuses `successful_denotation @`
[Soundness.lean](../../leanncd/LeanNCD/Semantics/Soundness.lean);
there is no separate duplicate ranked-denotation theorem in the patch.
First-failure tags/diagnostics are NOT schedule-independent.
The second-success fixture proves an extension from a different first step,
not a computed scheduler trace.

## 3. FUTURE preparation and replay gates -- controller owns these

Every command below is a **FUTURE execution template**, not an authoring action.
Replace placeholders with literal absolute paths or literal branch/commit names
before use. `<execution-worktree>` is a NEW isolated implementation checkout;
`<controller-session-artifacts>` is a controller-selected existing storage
directory. Result files under it are FUTURE/generated. Never use shell variables,
compound commands, or pipelines into git. Each displayed line is separate.

Use the repository new-slice procedure to create the execution checkout from
then-current local main, not origin/main or prototype HEAD. Preparation must
not overwrite published planning artifacts; omit `--plan`. The current author
did not run preparation because this planning worktree is already isolated.

```bash
bash <execution-worktree>/.claude/skills/new-slice/prepare-worktree.sh --base main
/usr/bin/git -C <execution-worktree> status --porcelain=v1 --untracked-files=all
/usr/bin/git -C <execution-worktree> rev-parse HEAD main
/usr/bin/git -C <execution-worktree> merge-base --is-ancestor a2be7b9048ccfc70ab9d74cb19c5e5ee79861357 HEAD
```

Require empty status, including untracked files/symlinks. If preparation leaves
a ledger, inspect and move only its identified path to session storage; never
delete unrelated work to obtain cleanliness. Capture prepared HEAD as
`<execution-base-commit>`. An ancestor-compatible main is allowed only with ALL
31 evidence-protected inputs unchanged, including scripts, existing fixtures,
authority/roadmap and reference-machine artifacts. `.claude/settings.json`
is a protected input, NEVER a staging target. A mismatch is STOP/adjudication,
not permission to ignore an evidence field.

The following read-only gate checks those exact protected hashes, and absence
of all four new outputs INCLUDING dangling symlinks. It uses evidence, not the
writing emitter. A printed FAIL/nonzero exit stops execution.

```bash
python3 -c 'import json,pathlib,hashlib; r=pathlib.Path("<execution-worktree>"); e=json.loads((r/"papers/semantics/coordinate_ranks_finite_measure_artifacts/evidence.json").read_text()); bad=[p for p,h in e["protected_input_sha256"].items() if not (r/p).is_file() or hashlib.sha256((r/p).read_bytes()).hexdigest()!=h]; new=["leanncd/LeanNCD/Semantics/Ranks.lean","leanncd/LeanNCD/Semantics/Measure.lean","leanncd/LeanNCD/Semantics/Progress.lean","leanncd/test/Semantics/RankedMachineTest.lean"]; occupied=[p for p in new if (r/p).exists() or (r/p).is_symlink()]; print("protected mismatches:",bad,"occupied outputs:",occupied); raise SystemExit(1 if bad or occupied or len(e["protected_input_sha256"])!=31 else 0)'
shasum -a 256 <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_patches/01-ranks-measure.patch <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_patches/02-progress-correspondence.patch <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_patches/03-fixtures-integration.patch <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_mutations_post.json
```

| Artifact | Required SHA-256 |
| --- | --- |
| Patch 01 | `b3e5ee2c527bbfa2b61e878af91d8ef531e42bd13893a04f7ea3faf7637b1e8e` |
| Patch 02 | `1c8a2151cd839ae72a1eb48784e5f7b71dcc5f1413b7371e34e6691bb815d74f` |
| Patch 03 | `e7b84cb0029430df7f83aa02c49d95d5c993daf43ea7293ae51de726757cada0` |
| Post manifest | `82fa84a0f02c453fda0aec66a8896e4da7f5fc522d7201eea4c393531794f2a1` |

Repeat clean/protected/absence gates after preparation, before the first build.
Confirm compatible Mathlib cache preparation; stop on a cold-build indication.
Refresh project-owned oleans ONLY with:

```bash
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD
```

No root-level lake invocation. Recheck covering guidance budgets: prototype
evidence reports parent Patterns 456 / Global Pitfalls 2,525 characters
(2,981 combined), semantic guidance no matching injected headings. This is
prototype measurement, not a future hook-budget guarantee. Controller checks
then-current injected Pitfalls/Checks/Patterns/Context near the ~3k threshold.
Do not trim unrelated guidance or change exact patches silently.

Controller independently checks provenance using a DISPOSABLE temporary index
at the ORIGINAL base: sequential cached `apply --check`/apply must reproduce
each recorded task tree and final candidate tree. This is not a required
execution checkout HEAD and does not authorize emitter writes here.
Whole-tree equality applies ONLY to that baseline temporary-index replay.

On compatible descendants compare new module blobs and all eight authorized
code/integration paths against a temporary-index replay of the CAPTURED prepared
HEAD; preserve unrelated changes outside patch hunks. Do not require descendant
whole-tree equality with the prototype. Compile actual descendant sources.
Each actual `git apply --check` must run sequentially, immediately before that
task's apply; earlier-task code must already be present. A conflict is STOP.

After all patches, expected NEW blob IDs, in this command's order:
`e1e401893352b100f82d8874bc20f99ca71c1f9c`,
`72da5e2c126f15629dd09a91e5932461e69f52f4`,
`eebe0604f5524dfbd727714caecc4c152c31cc32`,
`3df423a85b7b6281481dd83771c57e25ff1ab266`.
Modified integration files need not equal prototype blobs.

```bash
/usr/bin/git -C <execution-worktree> hash-object <execution-worktree>/leanncd/LeanNCD/Semantics/Ranks.lean <execution-worktree>/leanncd/LeanNCD/Semantics/Measure.lean <execution-worktree>/leanncd/LeanNCD/Semantics/Progress.lean <execution-worktree>/leanncd/test/Semantics/RankedMachineTest.lean
```

## 4. Briefs, bounded dispatches, and independently rejectable tasks

Every FUTURE implementer/reviewer/handoff brief opens VERBATIM:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Locate exact identifiers with `rg -n`; read 40-60-line windows. No whole large
files, fresh implementation design, or nested agents. A replay implementer
applies/builds/reports exact patches; controller owns independent verification,
actual cycles, whole-branch reviews, readiness and integration.

| Task | Replay workitems (at most three) | New fixture families/declarations here | Deferred coverage | Mutation ownership, all run after 03 |
| --- | --- | ---: | --- | --- |
| 01 | coordinate ranks; finite measure | 0 / 0 | Families 1-10, not added yet | CR1-CR4, four |
| 02 | ranked progress; terminal extension; correspondence | 0 / 0 | Families 11-16, not added yet | CR5, one |
| 03 | exact fixture-module replay; import/default discovery; bounded docs | 16 / 49 | All families integrate here | CR6, one |

Deferred coverage is NOT additional fixtures: the slice total is 16 families,
49 named declarations (25 theorem, 24 definition/abbreviation), eight program
construction definitions / nine instances, six cycles. These are prototype
counts, subject to independent controller validation; not 49 regressions.
Task 01 may be rejected for counting/edge defects while Task 02's correspondence
design is otherwise acceptable; Task 03 may be rejected for coverage/discovery
without redesigning either production group. Each requires per-task review.

Target replay dispatches <=40 turns; hard approximate limits <=60 turns /
250k peak. Authoring Phase B has the narrower <=40 turns / ~200k peak cap.
Execution cumulative cap ~175M input tokens; authoring target ~50M. Measure if
supported; unavailable Copilot token-report telemetry must be stated, never
treated as certified compliance. Report any breach immediately and at close-out.
Use attached long-build completion notifications, not repeated polling.

If Task 03 fixture verification is expected to exceed 60 turns, split exact
patch application/build/production handoff from verification-only dispatches.
Use [split-handoff-template.md](../../.claude/skills/slice-plan/split-handoff-template.md).
Keep each fixture brief to <=3 families: groups 1-3, 4-6, 7-9, 10-12, 13-15,
and 16; copy their witnesses/donors from Section 8, all `@`
[RankedMachineTest.lean](../../leanncd/test/Semantics/RankedMachineTest.lean).
These are bounded verification windows, not six redesign tasks or extra patches.
Do not bundle all 16 fixture constructions plus six cycles into an implementer.

## 5. Task 01 -- exact ranks and measure replay

Deliver ONLY FUTURE/generated
[Ranks.lean](../../leanncd/LeanNCD/Semantics/Ranks.lean) and
[Measure.lean](../../leanncd/LeanNCD/Semantics/Measure.lean).
Patch 01 windows: 1-60, 61-120, 121-180, 181-217.

Brief symbols:

- `DefinedAddress`, `definedAddress`, `definedAddress_injective`, `dependencies`,
  `input_dependencies_empty`, `RankCertificate`, `definedFintype`,
  `definedAddressFintype @` [Ranks.lean](../../leanncd/LeanNCD/Semantics/Ranks.lean).
- `pendingCount`, `unpublishedCount`, `measure`, `occurrenceCount`,
  `initial_measure`, `consume_measure`, `publish_measure`, `running_step_measure`,
  `stateMeasure`, `step_decreases`, `step_wellFounded`, `Trace`, `trace_reaches`,
  `trace_bound`, `running_trace_bound`, `failed_trace_bound`, `no_infinite_chain @`
  [Measure.lean](../../leanncd/LeanNCD/Semantics/Measure.lean).
- Existing siblings to examine only as needed: `Occurrence`, `destination @`
  [Program.lean](../../leanncd/LeanNCD/Semantics/Program.lean);
  `footprint @` [Interpret.lean](../../leanncd/LeanNCD/Semantics/Interpret.lean);
  `consume`, `publish`, `Step`, `initial @`
  [Machine.lean](../../leanncd/LeanNCD/Semantics/Machine.lean).

Reject input counting, tensor-level ranking, nonstrict decrease, output-only
publication counts, demand omission, or a rank/model premise on termination.
Section 8's case x class table is a required review deliverable, including
justifications for SILENTLY IGNORED cells; compare unchanged sibling rules.

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_patches/01-ranks-measure.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_patches/01-ranks-measure.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD.Semantics.Measure
/usr/bin/git -C <execution-worktree> add -- leanncd/LeanNCD/Semantics/Ranks.lean leanncd/LeanNCD/Semantics/Measure.lean
```

Review/adjudicate, then commit exact paths under repository conventions and the
required co-author trailer. Four assigned mutation entries are NOT runnable
yet against their named target; do not promise an early mutation build.

## 6. Task 02 -- exact progress and correspondence replay

Deliver ONLY FUTURE/generated
[Progress.lean](../../leanncd/LeanNCD/Semantics/Progress.lean).
Patch 02 windows: 1-60, 61-120, 121-180, 181-198.

Brief symbols: `invariant_input_available`, `unpublished_of_noncomplete`,
`ranked_progress`, `ranked_not_blocked`, `complete_terminal`, `Terminal`,
`Maximal`, `reaches_trans`, `terminal_extension`, `maximal_extension`,
`maximal_running_success`, `maximal_dichotomy`, `model_maximal_success`,
`no_model_maximal_failure`, `initialization_iff_singleton`,
`successful_schedules_agree @`
[Progress.lean](../../leanncd/LeanNCD/Semantics/Progress.lean).
Immediate existing proof dependencies: `reachable_invariant @`
[Invariants.lean](../../leanncd/LeanNCD/Semantics/Invariants.lean);
`successful_model`, `successful_unique`, `failed_no_model`,
`successful_denotation @`
[Soundness.lean](../../leanncd/LeanNCD/Semantics/Soundness.lean).

Reject a hidden model premise for progress, stopped-prefix maximality,
rank-independent success, output-only uniqueness, or failure-diagnostic
schedule independence. Verify denotation reuse, not a nonexistent extra theorem.

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_patches/02-progress-correspondence.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_patches/02-progress-correspondence.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD.Semantics.Progress
/usr/bin/git -C <execution-worktree> add -- leanncd/LeanNCD/Semantics/Progress.lean
```

Per-task review/adjudication precedes commit. CR5 is assigned here but its
fixture target is still absent: delay actual cycles until Task 03.

## 7. Task 03 -- exact fixtures, discovery, and documentation replay

Deliver FUTURE/generated
[RankedMachineTest.lean](../../leanncd/test/Semantics/RankedMachineTest.lean),
plus existing [Semantics.lean](../../leanncd/LeanNCD/Semantics.lean),
[lakefile.toml](../../leanncd/lakefile.toml),
[semantic AGENTS.md](../../leanncd/LeanNCD/Semantics/AGENTS.md),
and [parent AGENTS.md](../../leanncd/AGENTS.md).
Patch 03 windows: 1-60, 61-120, 121-180, 181-240, 241-300, 301-360, 361-364.

Brief symbols: every witness in Section 8 `@`
[RankedMachineTest.lean](../../leanncd/test/Semantics/RankedMachineTest.lean);
`Progress` import `@` [Semantics.lean](../../leanncd/LeanNCD/Semantics.lean);
`Tests` glob `@` [lakefile.toml](../../leanncd/lakefile.toml);
semantic exploration/discovery descriptions `@`
[semantic AGENTS.md](../../leanncd/LeanNCD/Semantics/AGENTS.md) and
[parent AGENTS.md](../../leanncd/AGENTS.md).

Fixture donors live in existing
[ReferenceMachineTest.lean](../../leanncd/test/Semantics/ReferenceMachineTest.lean),
[ExpressionTest.lean](../../leanncd/test/Semantics/ExpressionTest.lean), and
[CollectionModelTest.lean](../../leanncd/test/Semantics/CollectionModelTest.lean).
Use their namespaces as listed below; do not reconstruct donors by intuition.

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_patches/03-fixtures-integration.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_patches/03-fixtures-integration.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd Semantics.RankedMachineTest LeanNCD.Semantics
/usr/bin/git -C <execution-worktree> add -- leanncd/test/Semantics/RankedMachineTest.lean leanncd/LeanNCD/Semantics.lean leanncd/lakefile.toml leanncd/LeanNCD/Semantics/AGENTS.md leanncd/AGENTS.md
```

Per-task review must verify fixture discrimination, all tables below, plain
top-level semantic umbrella `import LeanNCD.Semantics`, and default `Tests`
discoverability. Do not claim a new root `LeanNCD` import modification: patch
03 changes the semantic umbrella. Default full build must include the fixture
target without an explicit target selector.

Documentation sweep is commands/reporting, NOT a heavyweight new dispatch:

```bash
rg -n 'Semantics.RankedMachineTest|LeanNCD.Semantics.Progress' <execution-worktree>/leanncd/lakefile.toml <execution-worktree>/leanncd/LeanNCD/Semantics.lean <execution-worktree>/leanncd/LeanNCD/Semantics/AGENTS.md
rg -n 'progress, measures, and termination are not supplied|cyclic solving|rank|scheduler' <execution-worktree>/leanncd/LeanNCD/Semantics/AGENTS.md <execution-worktree>/leanncd/AGENTS.md
rg -n 'five semantic|5 semantic|five.*semantic.*test|5.*semantic.*test' <execution-worktree>
rg -n '\b(sorry|axiom|native_decide)\b' <execution-worktree>/leanncd/LeanNCD/Semantics/Ranks.lean <execution-worktree>/leanncd/LeanNCD/Semantics/Measure.lean <execution-worktree>/leanncd/LeanNCD/Semantics/Progress.lean <execution-worktree>/leanncd/test/Semantics/RankedMachineTest.lean
```

The last search expects NO matches (rg exit 1 is the expected absence result).
Any new proof escape is STOP. Numeric/vocabulary hits require classification:
do not alter historical records or widen scope to unrelated cleanup. An actual
current discoverability contradiction requires controller adjudication.

## 8. Fixture donors, sibling audit, and proof-pinning limits

Source of these tables is the supplied
[coverage audit](coordinate_ranks_finite_measure_artifacts/coverage-audit.json).
All witnesses are identifiers `@` FUTURE/generated
[RankedMachineTest.lean](../../leanncd/test/Semantics/RankedMachineTest.lean).
Donor prefixes: `RM = ReferenceMachineFixtures`, `F = Fixtures`,
`CM = CollectionModelFixtures`, in the three existing donor files from Section 7.

| # | Family / donor and exact retained or changed discriminator | Witnesses |
| --- | --- | --- |
| 1 | Retain `RM.dependentP` / `F.direct`: same tensor, DIFFERENT coordinates | `historyCertificate`, `history_unstuck` |
| 2 | Clone `RM.cycleP` with `F.zeroStrict`: strict zero self-read; change guard to reject valuation for accept neighbor | `maskedSelf`, `masked_self_edge`, `masked_self_no_certificate`, `excludedSelfCertificate` |
| 3 | Clone `F.selected` / `F.tabulated`: select coordinate 1 while coordinate 2 is also read | `selectedP`, `off_selected_edge` |
| 4 | Clone `F.constRead` / `F.constantPolicy`: retain resolved constant boundary in admitted Unit context | `boundaryP`, `boundaryCertificate`, `boundary_no_edge` |
| 5 | Clone `F.nested` / `F.arrayPrimitive`: retain strict reduction and whole-array primitive operand, off-selected demand | `reductionP`, `primitiveP`, `reduction_edge`, `primitive_off_selected_edge` |
| 6 | Retain `RM.scalarRole` input address | `input_has_no_dependencies` |
| 7 | Clone `RM.scalarRole`: remove input and extra tensor IDs, rank-zero scalar nonoutput | `singletonDeclarations`, `singletonP`, `singletonInput`, `singletonCertificate`, `singleton_rank_zero`, `singleton_initial_count` |
| 8 | Clone `singletonP` with `F.emptyShape`: change extent to zero | `emptyDeclarations`, `emptyP`, `emptyInputP`, `emptyCertificate`, `zero_extent_no_addresses`, `zero_extent_initial_complete`, `empty_initial_count` |
| 9 | Retain `RM.d0` / `RM.d1` / `RM.dtag`: distinct duplicate tags survive initial count, exact consume drop | `duplicateCertificate`, `duplicate_initial_count`, `duplicate_consume_count` |
| 10 | Retain `RM.z0/z1`, `RM.n0/n1`, `RM.r1/r2`: zero consumption, empty fiber, nonoutput publication | `zero_consumption_decreases`, `empty_fiber_decreases`, `nonoutput_decreases` |
| 11 | Retain `RM.badP`, `RM.located_failure`, `RM.failure_excludes_models` | `failureCertificate`, `ready_failure_maximal`, `ready_failure_no_model` |
| 12 | Retain `RM.cycle_model` / `RM.cycle_blocked`: model plus unranked blocking, not a ranked counterexample | `cycle_model_and_blocked` |
| 13 | Retain `RM.d0` / `RM.duplicate_success`: available step refutes stopped-prefix maximality | `stopped_prefix_not_maximal` |
| 14 | Clone `RM.duplicate_success` / `RM.duplicate_model_without_witness`: first consume tag 1 instead of tag 0; prove terminal extension and identical full store | `second_schedule` |
| 15 | Clone `CM.duplicate` with `F.bad`: two distinct independently ready undefined tags | `twoBad`, `twoBadTarget`, `twoBadTag`, `twoBadInput`, `twoBadInitial`, `distinct_first_failures` |
| 16 | Retain `singletonP`; instantiate `Program.initialization_iff_singleton` | `ranked_singleton_correspondence` |

Generic helper `footprintFreeCertificate` clones literal/empty-footprint
`CM.expressionProgram` witnesses, assigning constant zero address ranks.
Cardinality proofs use `Types.canonicalLayout` / `F.point` and explicit
equivalences, not executable evaluation of the noncomputable measure.
Prototype proof observations: duplicate initial 5, after consume 4; singleton
initial 1 and certificate rank 0; zero-extent initial 0; each zero/empty/nonoutput
running decrease 1. Controller must independently observe elaboration.

These are proof-based pins, not 16 independently mutation-tested families.
The six mutations below are generic kernel-proof rejections; failures can arise
upstream before fixtures elaborate. No isolated fixture oracle was performed,
and no production runtime oracle kill is claimed. Family 5 has an array-primitive
example, not an isolated fixture for every heterogeneous operand position;
general strict demand is retained by unchanged typed footprint and proof use.

### Step case x class -- R required, F forbidden, I SILENTLY IGNORED

Unchanged siblings: `Step.contribute`, `Step.publication`, `Step.undefined`,
`consume`, `publish @` [Machine.lean](../../leanncd/LeanNCD/Semantics/Machine.lean).
Review call-site/reachability premises, not only constructor text.

| Case | pending tag | ready some | ready none | unavailable read | unpublished cell | empty fiber | zero value | output flag | certificate | model witness |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| contribute | R | R | F | F | I | I | R: erase even zero | I | I | I |
| publication | F in destination fiber | I | I | I | R | R | R: publish even zero | I | I | I |
| undefined | R | F | R | F | I | I | I | I | I | I |

I is deliberate, not missing coverage: pending destination is unpublished by
reachable published invariant; a pending tag makes that fiber nonempty.
Publication evaluates no expression. Every defined address, including nonoutputs,
counts. Step/finite bounds ignore rank/model; certificate enters ranked progress
only. Undefined has no value and retains the pending tag/configuration.
An ignored cell with no such justification is a candidate sibling defect: STOP.

### Footprint case x class

Sibling `footprint` branches `@`
[Interpret.lean](../../leanncd/LeanNCD/Semantics/Interpret.lean);
consumer `dependencies @`
[Ranks.lean](../../leanncd/LeanNCD/Semantics/Ranks.lean).

| Case | own edge | strict child reads | all binder coordinates | selected-coordinate-only | rejected valuations |
| --- | --- | --- | --- | --- | --- |
| lit | F | I: no children | I: no binder | I | F |
| iverson | F | I: value-free predicate | I: no binder | I | F |
| resolved read-at | R: source coordinate | I: no children | I: no binder | I | F |
| resolved read-const | F | I: no children | I: no binder | I | F |
| rejected read | F: no admitted constructor witness | I | I | I | F |
| binary | F: only child edges | R: both, even zero multiplication | I: no binder | F | F |
| reduce | F: only child edges | R | R: every finite coordinate | F | F |
| tab | F: only child edges | R | R: every layout coordinate | F | F |
| at | F: only child edges | R: entire array expression | R: inherited tab demand | F | F |
| prim | F: only child edges | R: every typed argument, whole arrays included | R: inherited array demand | F | F |

Contributor class audit: admitted occurrence in destination fiber R; other
destination fiber F; guard-rejected valuation F; duplicate read address I as
SET multiplicity only, not erased demand; input destination F (empty dependencies);
input source R when in footprint (initially available). Required/forbidden/I
classification is a task review artifact, not permission to modify protected code.

## 9. Post-state mutations -- controller, after all three patches

Use the existing [post manifest](coordinate_ranks_finite_measure_mutations_post.json).
No unnecessary before-manifest: production replay adds modules and integration,
not edits to existing semantic definitions. CR4/CR6 intentionally mutate
protected existing files ONLY in disposable validation, restore exactly, and
never ship those modifications.

| Entry | Assigned task | Mutation target / change | Target build | Expected rejection surface |
| --- | --- | --- | --- | --- |
| CR1 | 01 | `dependencies @` [Ranks.lean](../../leanncd/LeanNCD/Semantics/Ranks.lean): empty read list | `Semantics.RankedMachineTest` | Progress, argument type mismatch |
| CR2 | 01 | `RankCertificate @` [Ranks.lean](../../leanncd/LeanNCD/Semantics/Ranks.lean): `<` becomes `<=` | same | cannot apply certificate decrease |
| CR3 | 01 | `measure @` [Measure.lean](../../leanncd/LeanNCD/Semantics/Measure.lean): omit unpublished count | same | Measure unsolved goals |
| CR4 | 01 | `consume @` [Machine.lean](../../leanncd/LeanNCD/Semantics/Machine.lean): retain pending tag | same | Measure simplification type mismatch |
| CR5 | 02 | `Maximal @` [Progress.lean](../../leanncd/LeanNCD/Semantics/Progress.lean): terminal conjunct becomes True | same | Progress function expected |
| CR6 | 03 | `footprint @` [Interpret.lean](../../leanncd/LeanNCD/Semantics/Interpret.lean): omit binary right read | same | Readiness argument type mismatch |

File identifiers in this table refer to the linked exact modules above.
Populated `expect` strings are in the manifest, copied from prototype rejection
segments by the emitter. Evidence attributes six PASS cycles/restored builds;
controller must execute all six independently, not just validate their syntax.

`--check` cannot run on base: new mutation modules are absent. Selecting entries
01/02 later still builds `Semantics.RankedMachineTest`, absent until Task 03.
Therefore all actual cycles are delayed until fixture integration; assignment
to a task does not authorize an impossible early selected build.

```bash
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --check <execution-worktree>/leanncd <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_mutations_post.json
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --out <controller-session-artifacts>/coordinate_ranks_mutation_results.md <execution-worktree>/leanncd <execution-worktree>/papers/semantics/coordinate_ranks_finite_measure_mutations_post.json
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd
/usr/bin/git -C <execution-worktree> diff --exit-code HEAD -- leanncd
/usr/bin/git -C <execution-worktree> status --porcelain=v1 --untracked-files=all
```

Run after task commits for the clean restoration comparison. Require six
selected/PASS entries, every populated expectation matched, byte-identical
restore, restored green builds, no skipped entries, and final default full build
green. Repeat all 31 protected hashes after cycles (without the preflight
generated-output absence test). Preserve result table/log references in controller
session storage; do not commit raw prototype logs or transient validation files.

Controller independently verifies 31 printed inventories named in evidence;
permitted axioms are only `propext`, `Classical.choice`, `Quot.sound`.
Do not confuse 31 printed inventories with every declaration separately printed.
Scan new code for no new sorry/axiom/native_decide and inspect actual inventory
output. Baseline unrelated sorry/linter warnings persist; the prototype also has
THREE NEW unused-simp warnings in `boundary_no_edge` and
`distinct_first_failures @`
[RankedMachineTest.lean](../../leanncd/test/Semantics/RankedMachineTest.lean).
Full prototype logs report 17 warnings, targeted logs six. Not warning-free and
not "only pre-existing warnings"; controller records actual descendant warnings.

## 10. Independent reviews, readiness, and later local integration

Controller rehearses on compatible current main and records exact base, patch
hashes, sequential checks, authorized-scope replay equality, actual six-cycle
table, protected restorations, full build, discovery, counts and inventories.
Only after these checks and adjudicated reviews may the authoring record say
execution-ready. Current authoring cannot predeclare that status.

Per-task reviews are required; final whole-branch reviews use TWO distinct lenses:

1. **Semantic/proof contracts:** Section 2 and ranks/measure/progress symbols.
   Reject tensor-not-coordinate rank, footprint weakening, input-value-dependent
   certificates, definedness assumptions, output-only counts, wrong +1 failure
   bound, model-dependent progress, stopped-prefix maximality, weakened full-store
   correspondence, or diagnostic-independence overclaim.
2. **Replay/fixture/process safety:** Sections 3, 7-9 and all fixture witnesses.
   Reject stale remote/prototype base, writing-emitter prerequisites, descendant
   whole-tree comparison to prototype, dirty/symlink inputs, patch transcription,
   impossible pre-03 cycles, missing restoration/discovery, fixture-independence
   claims unsupported by generic proof rejection, or hidden warning/budget gaps.

Give each reviewer the preamble, identifiers and <=60-line windows; preserve
findings incrementally in controller session storage. Fix only adjudicated
groups. Stop on a load-bearing unfixable finding or invalidating plan defect;
do not weaken contracts or invent a port. No authoring agents/builds/mutations
are authorized here.

Future execution close-out goes in FUTURE
`papers/semantics/coordinate_ranks_finite_measure_execution_record.md`, created
ONLY during execution, not now. Its template requirements are:

- Actual selected local-main base/HEAD, exact commands, three task commits,
  per-task review dispositions, patch/new-blob checks and preserved unrelated edits.
- Six-row mutation table: selected/result, expectation, proof-rejection
  classification, restore and restored-build outcomes; zero runtime-oracle claim.
- Full default build, semantic umbrella/default Tests discovery, 16-family/
  49-declaration count validation, proof-observed values and 31 inventories.
- Protected hashes after restore, no new proof escapes, warnings including new
  simp warnings, two distinct final review dispositions and adjudications.
- Measured turns/peak/cumulative tokens when available; explicit telemetry
  unavailability otherwise; every breach and all parked limitations.
- Local integration result, retained planning/prototype boundary, no remote push.

Later execution controller reruns actual manifest and full build on final
implementation sources, confirms both final lenses clean/adjudicated, then merges
IMPLEMENTATION to local main and removes only its own branch/worktree under the
new-slice finish procedure. If main moved, repeat compatibility/replay/build gates.
Do not remove unrelated work, commit `.claude/settings.json`, or push remotely.
This future integration does not authorize merge/commit actions in Phase B.
