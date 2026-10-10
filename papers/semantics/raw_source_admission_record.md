# Raw-source/admission: authoring verification record

Date: 2026-10-09. **Authoring record, not an execution closeout.**
Latest status: **EXECUTION-READY, NOT LANDED**. Earlier sections retain their historical
partial-prototype status; the final dated controller receipt supersedes those gates.
Companion: [one-slice plan](raw_source_admission_plan.md).
Base: `3d721f9631de8642163446f98b4efc8fe1d078d5`.
Worktree: `/Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4`.

## Historical partial-seed receipt (preserved, superseded by readiness section below)

The sections through "Write-up verification and budget status" describe the earlier partial seed
and its restored checkout, not the subsequently completed installed prototype. Their open A/B/C
gates and pending-family estimates are historical. They are retained without rewriting receipts.

## Evidence and provenance

Write-up uses the supplied prototype artifacts and controller-verified path/donor facts:
[evidence.json](raw_source_admission_artifacts/evidence.json),
[builds.log](raw_source_admission_artifacts/builds.log),
[fixtures.log](raw_source_admission_artifacts/fixtures.log),
[axioms.log](raw_source_admission_artifacts/axioms.log),
[mutations-existing.md](raw_source_admission_artifacts/mutations-existing.md),
[mutations-post.md](raw_source_admission_artifacts/mutations-post.md),
[task-1.patch](raw_source_admission_patches/task-1.patch),
[task-2.patch](raw_source_admission_patches/task-2.patch),
[task-3.patch](raw_source_admission_patches/task-3.patch),
[existing-code manifest](raw_source_admission_mutations.json), and
[post manifest](raw_source_admission_mutations_post.json).

The writing dispatch used bounded artifact windows, with no source edits, new proof runs, or artifact
changes. Subsequent direct controller verification checked existing dependency locators and paths.
Initial `/usr/bin/git -C` status showed only those untracked artifacts/manifests/
patches. Evidence records source restored to base by reverse-applying patches; source-path status
and all-leanncd diff were empty. The source currently does **not** implement prototype additions.

The seed's new [RawCorrespondence.lean](../../leanncd/LeanNCD/Semantics/Source/RawCorrespondence.lean)
and [SourceRawCorrespondenceTest.lean](../../leanncd/test/Semantics/SourceRawCorrespondenceTest.lean)
are **planned/generated paths**, created by patch 3, not existing files at base.
No implementation was landed, committed, merged, or pushed. Authoring used separate prototype and
write-up dispatches, then direct controller verification; no implementation whole-branch review.

## Recorded prototype build receipts

The following commands and results are copied **verbatim** from builds.log; these are prototype
receipts, not builds of the restored current source or new A–C proofs:

```text
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd LeanNCD.Semantics.Source.Admission
exit=0: Build completed successfully (8507 jobs).
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd Semantics.SourceAdmissionTest LeanNCD
exit=0: Build completed successfully (8595 jobs).
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd
exit=0: Build completed successfully (8765 jobs).
```

Thus a full default prototype build was green. This does not make the patch series complete.

## Six seed fixture entrypoints and coverage

Identifiers below are in the patch-generated test, not current source declarations.

| Fixture | Donor / observed fact | Recorded mutation coverage |
|---|---|---|
| AsymmetricOrder | snapshot donor; first write B,A,B then A then empty product. Reads declaration IDs 4,3,4; slots [1],[1,2],[1]; origins term0 factors0,1,2, then term1 factor0. | M1; M4 fixture-contrast |
| ParsedMetadata | independent actual `tlprog!` copy of ParsedRawNatCopy; raw UID0 → resolved UID1, declaration nat vs real use-site kind retained, names retained; evaluated true. | M1 |
| ParsedRead | parsed donor; output Y declaration2 [1], read X declaration1 [1], statement0/term0/factor0. | M1 |
| EmptyAndDiagonal | asymmetric snapshot donor; Diagonal declaration7 output [1,1] with empty product; repeated Y declaration5 with empty sum; evaluated true. | M1 |
| ZeroExtent | resolved context UIDs [1,2,3]; declaration IDs 3/4/5/6/7 with shapes [2,3]/[2]/[2]/[0]/[2,2]; evaluated true. | M1 |
| ErrorOrder | snapshot-based donor violates nonSum, nonIdentity, undeclared output simultaneously. Expects nonSum, statement stage, output side, statement0, other origin fields absent; evaluated true. | **None: mutation pin pending** |

Verified donor facts supplied separately: snapshot has i(uid7,extent2), k(uid3,extent3),
e(uid11,extent0), A[2,3] inputs [1..6], B[2] inputs [10,20], Empty[0] inputs [],
Y/Diagonal writable declarations. ParsedRawNatCopy inputs are 3,5.
RealLinearSumProduct supplies typed/untyped tensor/linear, f32/f64, bias/nonbias, reads X*X + X,
and rational inputs 1/3,5/7. Its matrix is an execution preservation requirement; no new matrix
count or new correspondence-fixture result is asserted here.

## Four final mutation receipts

| Cycle | What was changed | Observed failure / meaning | Restoration |
|---|---|---|---|
| M1 | Original axis-name mint loop iterates an empty list. | Test build error containing `Expression`; hits five fixtures above. Implementation mutation, not global freshness proof. | Bytes restored; restored build green. |
| M2 | Read declaration origin becomes tensor-table position. | Admission proof error: `` `simp` made no progress ``. **Proof kill**, not a runtime fixture or A invariant proof. | Bytes restored; restored build green. |
| M3 | Certified checked read order is reversed in the theorem contract. | Admission proof error: `Application type mismatch`. **Proof kill**, not runtime reordering coverage. | Bytes restored; restored build green. |
| M4 | Expected asymmetric tensor order swaps distinct B/A entries. | Test build error containing `Expression`. **Fixture-contrast kill**, not an implementation-runtime kill. | Bytes restored; restored build green. |

Both mutation receipt files report `2/2 cycles passed`. Evidence records:
existing-code manifest `PASS: 2 entries, every old-string unique`;
prototype-added manifest `PASS: 2 entries, every old-string unique`.
Checks were on the final installed prototype, **before restoration**. Post manifest paths/targets
depend on prototype-generated files. These checks are not asserted to pass on restored base.
The controller checked runner argument order against the existing wrapper and added future
invocations to the plan. No additional controller mutation cycles are claimed.

M1–M4 do not pin ErrorOrder or the missing declaration/raw/semantic obligations.
Future manifests need newly observed `expect` strings and replacement targets for strengthened
proofs. Do not report all fixture mutation coverage.

## Generic theorem axiom audit

axioms.log records **15** generic `#print axioms` audits:
`assignUIDs_mapUID`, `resolveSource_mapUID`, `mapM_success_forall2`, `admitRead_fields`,
`admitTerm_reads`, `TensorTable.find_name`, `astRead_fields`, `admitOutput_fields`,
`admitStatement_fields`, `adaptSource_statements`, `admitSource_fields`,
`mapUID_axis_metadata`, `admitRawSource_fields`, `TermFields.factor_count`,
`StatementFields.term_count`.

Only `propext`, `Classical.choice`, `Quot.sound`, or no axioms appear.
`mapUID_axis_metadata` has no axioms. No `sorryAx` or native-proof dependency appears;
evidence reports no sorry/admit/new axiom/native_decide generic proofs.
This audit covers the seed only, not A–C or future extraction-equality theorems.

## Mechanical patch and replay receipts

Evidence records ordered cached apply checked, exact compiled-byte replay, and isolated temporary
git index with explicit source paths; real index untouched. Patch hashes recorded there:

| Patch | SHA-256 |
|---|---|
| task-1.patch | `d839237bafc6b7c2879bc198fff6e18e8955b97fd3f6cb7d614f26c387d10e81` |
| task-2.patch | `d49d9d9598de95837270144a853e51724726c8a6427bc8af0a35990a4939c4fc` |
| task-3.patch | `78ebb326f2884d5de0468bd61900d74db4c223fbc2c119657e4e3feaf4c54e4f` |

Eight compiled-file hashes are retained in evidence.json, including the two generated paths.
These are recorded receipts, not hashes recomputed during write-up.
The patches reuse compiled partial work; none may be blindly applied and called a completed slice.
Patch 1 lacks a generic FreshM extraction behavior-equality proof. Patch 2 proves resolved ordered
fields, not raw declaration certification. Patch 3 packages a partial raw endpoint and registrations.

## Open gates and explicit non-claims

**A:** No generic success invariant connects private checkTable's decls.zipIdx scan and mutable
entries/shape to original declaration lookup. Required: every tensor-bearing form, name/element
type, ordered successful sourceAxis, specs role/shape, intervening axis declarations. Direct proof
or behavior-equal helper extraction plus refusal fixtures is required. Controller review also
requires `checkAxes` context/domain preservation and actual memo coverage for occurring names;
the seed does not prove those. Memo coverage is not global UID freshness/injectivity.

**B:** Whole-program mapUID equalities are not expanded into pointwise bare raw output/read slots
and raw indexed AST relations. Exact nested Forall₂, metadata and sentinel distinction are required.

**C:** No composition with certified raw projection/body/fiber/collect/models/reached-success
results. No independent raw denotation theorem. The controller verified the exact existing
dependency locators; proving their composition with the strengthened certificate remains open.

Additional limits: no first-match/minimal-position theorem for table.find beyond returned-name
equality; not required unless endpoint proof needs it. No parser-string correctness, global UID
freshness/injectivity, scans/affine/guards/nonlinear/marked arrays, arbitrary substitution,
re-admitting source permutations, rank synthesis, oracle equality, floats/backend refinement,
or fix to production cross-statement additive divergence.
No whole-branch review, all-fixture mutation verification, execution closeout, or proof-closed claim.
Historical 39 controls are not this slice's receipts.

## Write-up verification and budget status

Authored exactly the requested plan and this record with apply_patch, with no Lean snippets to
compile. Verified claims were taken from artifact windows, including build text, fixtures,
mutations, axiom reports, and mechanical patch contracts. No source rebuild is needed for these
documentation-only changes. New theorem and fixture names are explicitly proposed, not observed.
Ten pending fixture families and per-task cycle counts in the plan are **estimates**.
Context-node injection measurement/trimming, replacement patch compilation,
per-stage fixture/import/target staging, new mutation observations, and independent reviews remain
future gates. Seed prefix builds cannot exercise M1/M2 without patch 3's generated targets.

Controller verification independently replayed all three seed patches into an isolated temporary
git index at the stated base. All three patch hashes and eight resulting source hashes matched
evidence.json. The real index was untouched; `git diff --exit-code HEAD -- leanncd` passed.
Existing source/documentation paths and semantic dependency locators were checked. No source build
was rerun after restoration: the new deliverables are documentation and retained prototype evidence.
No Lean blocks are embedded in the plan.

Write-up uses a small bounded set of turns below the requested 30-turn cap.
Prototype evidence says proof work stopped near its requested approximately 60-turn cap.
Exact prototype telemetry unavailable: token-report.py found no Claude transcript for Copilot SDK.
No exact SDK context peak or cumulative usage is available here either; **do not infer measured
compliance or breach**. No measured budget conclusion is available.
Targets retained: authoring approximately 50M cumulative input, execution approximately 175M,
dispatch peak approximately 250k / approximately 60 turns; this write-up peak cap 250k.
Any future measured overrun must be surfaced, not silently omitted.

## 2026-10-09 — completed-proof packaging readiness, controller checks pending

This is a fresh write-up/packaging dispatch, **not implementation execution or landing**.
The installed prototype now contains compiled A/B/C. This section supersedes the earlier partial
status and open-proof inventory; the original seed evidence and task-1/2/3 patches remain history.
No source proof behavior was rediscovered: contracts, observations and scope were read from the
authoritative artifacts; only mechanical capture inspected source bytes.

### Authoritative completed-proof evidence

- [declaration_invariants.json](raw_source_admission_artifacts/declaration_invariants.json):
  actual successful checkAxes/checkTable/adaptSource ordered pins and every original declaration,
  declared slots, spec lookup/role/shape. Original declaration IDs are not tensor-table positions.
- [resolver_binding.json](raw_source_admission_artifacts/resolver_binding.json):
  actual occurring-name memo coverage, same-name UID binding and full `assignUIDs_eq_inline`
  FreshM equality (values, errors and final state). Reusable list/mapUID helpers live in Traverse.
- [raw_bridge.json](raw_source_admission_artifacts/raw_bridge.json):
  `admitRawSource_fields` supplies full original-raw declaration/indexed AST/slot correspondence
  solely from actual admission success, with an actual covering resolver memo.
- [semantic_connection.json](raw_source_admission_artifacts/semantic_connection.json):
  RawSemanticConnection gives usable certified raw-coordinate witnesses, existing body/fiber/
  collection/model applicability, and explicit rational reached-result corollaries.
- [structural_fixtures.json](raw_source_admission_artifacts/structural_fixtures.json) and
  [endpoint_fixtures.json](raw_source_admission_artifacts/endpoint_fixtures.json): ten observed
  true contract families. The endpoint target receipt includes the acceptance target replay,
  not a final default full build or new acceptance count.
- [soundness_review.json](raw_source_admission_artifacts/soundness_review.json) and
  [fidelity_review.json](raw_source_admission_artifacts/fidelity_review.json): independent,
  source-only clean scoped reports. Neither reviews final plan staging/docs or authorizes landing.

All original runtime bodies are unchanged except the generically behavior-equal assignUIDs
memo/relabel extraction; collector visibility and added proof definitions are not runtime rewrites.
No independent raw denotation, global mint injectivity, unconditional successful run, input-buffer
certificate, native refinement or oracle-equality claim is added.
Reached equations and uniqueness use **result.input**, not automatically source-stored buffers.
Canonical parsed/asymmetric donors use `sourceInput` through their actual source runs, observed
complete with4/12 events respectively; their named kernel theorems still require actual complete-
outcome equalities. Existing denotation is output-restricted; generic body/collection uses total
stores and semirings. The original proof scope and outside-fragment limits remain.

### Mechanical package receipt

New tool: [emit_ready_patches.py](raw_source_admission_artifacts/emit_ready_patches.py).
New metadata: [readiness.json](raw_source_admission_artifacts/readiness.json).
Four final patches, mechanically emitted from the exact installed compiled text:
[01-certified-binding.patch](raw_source_admission_patches/01-certified-binding.patch),
[02-resolved-occurrences.patch](raw_source_admission_patches/02-resolved-occurrences.patch),
[03-raw-correspondence.patch](raw_source_admission_patches/03-raw-correspondence.patch),
[04-semantic-fixtures.patch](raw_source_admission_patches/04-semantic-fixtures.patch).
Hashes and exact ten-file mapping are in readiness.json, not copied manually here.
Temporary-index capture and ordered cached application passed; every resulting source SHA256
matches captured compiled bytes. Source files and the real git index were unchanged by capture.
Temporary indices were cleaned automatically. No real-index staging/commit/merge/restoration/spawn.

Task order is1→2→3→4. Stage1 builds Adapter (Traverse/Structural available), stage2 Admission,
stage3 RawCorrespondence directly, stage4 RawSemanticConnection/tests/LeanNCD.
All ten runtime/donor fixture families arrive in stage4, not stages1/2. Early stages validate
production proof contracts and prefix-available mutation pins. Runtime docs are deferred task4
edits; the compiled patch does not pretend to contain them.
The live [plan](raw_source_admission_plan.md) is now an apply/build/review recipe, not a list of
proofs for an implementer to discover.

### Mutation consolidation and observed receipts

[controller-existing.md](raw_source_admission_artifacts/controller-existing.md),
[controller-post.md](raw_source_admission_artifacts/controller-post.md),
[controller-structural.md](raw_source_admission_artifacts/controller-structural.md) and
[controller-endpoint.md](raw_source_admission_artifacts/controller-endpoint.md), with their logs,
record17 pre-consolidation cycles: each broke, restored byte-identically, and rebuilt green.
Exactly15 proof-protected rejections,2 fixture contrasts (M4/E5),0 runtime kills.
M1 now fails Structural proofs; E1/E2/E3 fail Admission proofs before fixtures; E4 fails semantic
coordinate linkage. The two contrasts mutate fixture oracle/donor rather than production runtime.
The current [existing](raw_source_admission_mutations.json) / [post](raw_source_admission_mutations_post.json)
manifests consolidate all17 controls into11 base-text /6 post-text entries, preserving exact
replacement text and stable M/S/E prefixes. Final task tags and targets are prefix-available.
Each `expect` uses the file error prefix plus an actually observed message, never a line number.
Historical candidate manifests are retained unchanged and are no longer pending execution authority.
**These final manifests have not had their cycles rerun by this dispatch.**
Historical17/17 success does not imply final-target17/17 success.

### Controller readiness append template — leave pending until observed

| Gate | Current status | Controller receipt to append |
|---|---|---|
| four ordered cached applies, ten compiled-byte hashes | passed packaging | readiness.json mechanical validation |
| ordered stage1/2/3/4 wrapper builds on patch prefixes | pending | commands, exit codes, logs; no future test dependency |
| final module/test/LeanNCD targets and full default build | pending | exact wrapper commands, exit codes and logs |
| both consolidated manifest `--check` runs | passed packaging:11/6 unique entries | controller repeats on final installed source |
| both consolidated actual manifests, all17 cycles | pending | final output tables/logs,15+2 classifications |
| final cycle restores byte-identical and restored green | pending | hashes/runner summaries |
| mark package execution-ready | blocked on preceding pending gates | date, base, unchanged hashes, scoped verdict |
| runtime docs + two final whole-branch reviews | future execution | sweep adjudication and review findings/disposition |

Use stage application/build commands and task-filtered commands from the live plan.
Final controller commands (new receipt paths preserve the existing historical tables):

```sh
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd LeanNCD.Semantics.Source.RawCorrespondence LeanNCD.Semantics.Source.RawSemanticConnection Semantics.SourceRawCorrespondenceTest Semantics.SourceAdmissionTest Semantics.SourceAdmissionAcceptanceTest LeanNCD
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/mutation-manifest.sh --cd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd --out /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/controller-final-existing.md /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_mutations.json
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/mutation-manifest.sh --cd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd --out /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/controller-final-post.md /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_mutations_post.json
```

Controller marks ready only after actual observations; controller restoration comes afterward.
Source-only authoring reviews do not substitute for the execution whole-branch reviews after docs.
This authoring phase must not land or push.

### Named-section context metric and budget

Controller measurements include named Pitfalls/Checks/Patterns/Context and Global headings:
leanncd AGENTS2984 chars, DSL AGENTS1790, Semantics AGENTS0 (no matching named sections).
No trim is needed by this metric; **not all injected text was measured**.
Separate prototype dispatches reported bounded35–60 rounds. Exact SDK transcript/turn totals,
context peaks and cumulative tokens are unavailable; no measured approximately50M compliance
or exact combined turn count is claimed. Current write-up cap is approximately45 turns/250k;
future dispatch caps approximately60 turns/250k, authoring target approximately50M, execution
approximately175M. Report a known breach; unavailable telemetry remains explicit, not "passed".

Packaging validation observed: both consolidated wrapper `--check` commands exit0 (11/6 entries,
all unique); standalone emitted-package verification passes ordered cached replay and ten hashes.
Python syntax, four-stage/ten-file shape,17 unique stable IDs, stage counts7/7/0/3, two contrasts,
resolved recipe links, no Lean line locators/snippets, and live-plan preferred line budget passed.
No stage build, full default build or actual mutation cycle was run in this write-up.

Packaging found and fixed a runner/recipe mismatch: mutation-manifest.sh validates all entries
before applying `--task`, and refuses zero selected. The emitter now generates hashed exact
task projections (stage1 existing/post, stage2 existing/post, stage4 post). Early stages run
those projections; the two consolidated manifests remain the sole authority and final-cycle
inputs. Task4 has no existing-text entries and no empty-selection invocation.
This fixes staging without editing the runner or claiming a staged build has already passed.

Final packaging validation: live plan365 lines (preferred limit400). All five projection wrapper
`--check` runs exit0 with5/2/6/1/3 selected entries. Temporary-index replay additionally verifies
each projected old string is unique at its own patch prefix. Final package/projection re-emission
is byte-identical; tool syntax and recipe links pass. An in-memory incorrect patch hash was
explicitly rejected in the packaging test. No source restoration or final cycles occurred here.

## 2026-10-09 — final controller readiness verification complete

This section supersedes the earlier pending controller template. All authoring readiness gates
passed on base `3d721f9631de8642163446f98b4efc8fe1d078d5`.
The live [plan](raw_source_admission_plan.md) is released as **execution-ready, not landed**.

Authoritative machine-readable receipt:
[controller-readiness.json](raw_source_admission_artifacts/controller-readiness.json).
The [verification harness](raw_source_admission_artifacts/verify_ready_package.py) checked exact
installed compiled hashes, reverse-applied only the four scoped prototype patches, replayed them in
task order and built each prefix. It did not touch the real index or unrelated paths.

| Controller gate | Observed result |
|---|---|
| stage 1: Adapter, including Structural and Traverse | green, 8,505 jobs |
| stage 2: Admission | green, 8,507 jobs |
| stage 3: RawCorrespondence, without future tests/imports | green, 8,516 jobs |
| stage 4: RawSemanticConnection, raw/admission tests, LeanNCD | green, 8,597 jobs |
| all five task projections schema/unique-text checks at their actual prefixes | pass |
| authoritative existing-text manifest schema and actual cycles | 11/11 pass |
| authoritative post-text manifest schema and actual cycles | 6/6 pass |
| full default prototype build after final cycles | green, 8,766 jobs |
| every mutated file restored byte-identically; restored builds green | pass |
| final source restoration and original source-path status | equals base, no implementation changes |
| restored base LeanNCD build | green, 8,584 jobs |
| final cached package replay after source restoration | all ten compiled-byte hashes match |

Actual consolidated cycle tables are [existing-text](raw_source_admission_artifacts/final-manifest-existing.md)
and [post-text](raw_source_admission_artifacts/final-manifest-post.md), with retained matching logs.
All 17 controls were rerun with final labels and prefix-safe targets. The first-failure
classification remains **15 proof-protected rejections, 2 fixture contrasts, 0 runtime kills**.
Every expected diagnostic substring appeared. Prior candidate manifests and partial seed receipts
remain historical; they do not supply this final readiness verdict.

The two source review lenses were clean within their stated boundaries, and direct controller
package validation covered final task staging and replay. Runtime documentation edits and the
implementation's final whole-branch reviews remain execution obligations. No independently
specified raw denotation, unconditional kernel completion, input-buffer certification, numerical
refinement or production contract change is claimed.

Prototype implementation files are now restored to base. Persistent deliverables are the plan,
records, four final patches, manifests, reproducible tools and evidence. No implementation commit,
merge or remote push occurred. Exact SDK cumulative tokens and context peaks remain unavailable;
the configured token-report tool found no transcript, so measured budget compliance is not claimed.

## 2026-10-09 — implementation execution

Execution worktree: `raw-source-admission-correspondence`.
Branch: `agents/raw-source-admission-correspondence`.
Authoring base: `3d721f9631de8642163446f98b4efc8fe1d078d5`.
Execution base: `9f333b91` (local `main` after worktree preparation).
The only intervening change is the pointwise matrix-addition documentation
example; the ten patch input paths compare identically to the authoring base.
The package CLI correctly refused execution-base verification because it pins
HEAD. Its unmodified `--verify` passed in the recipe checkout at the recorded
base; installed hashes were independently verified in this execution worktree.
No guard was removed and no package was recaptured or silently rebased.
Mathlib preparation verified 8,101 built oleans / 8,094 sources and 229 project
oleans. Controller `LeanNCD` refresh passed with 8,584 jobs.

All four final patch hashes and ten compiled source hashes are preserved in
[readiness.json](raw_source_admission_artifacts/readiness.json). Only patches
01 through 04 were applied, in order. Historical partial seeds, candidate
manifests and authoring observations were preserved, not counted as execution.
Each stage's installed bytes matched its recorded SHA256; all ten final
installed source hashes also matched after the task-filtered controls.

| Stage | Controller build (exit 0) | New cycles, all restored green | Per-task proof/fidelity review |
|---|---|---|---|
| 1 | Adapter, 8,505 jobs | 5 existing + 2 post | clean |
| 2 | Admission, 8,507 jobs | 6 existing + 1 post | clean |
| 3 | RawCorrespondence directly, 8,516 jobs | 0 new | clean |
| 4 | RawCorrespondence, RawSemanticConnection, raw/admission/acceptance tests, LeanNCD, 8,597 jobs | 3 post | clean |

Build receipts: [stage 1](raw_source_admission_artifacts/execution-stage1-build.log),
[stage 2](raw_source_admission_artifacts/execution-stage2-build.log),
[stage 3](raw_source_admission_artifacts/execution-stage3-build.log),
[stage 4](raw_source_admission_artifacts/execution-stage4-build.log).
Projected cycle tables:
[task 1 existing](raw_source_admission_artifacts/execution-task1-existing.md),
[task 1 post](raw_source_admission_artifacts/execution-task1-post.md),
[task 2 existing](raw_source_admission_artifacts/execution-task2-existing.md),
[task 2 post](raw_source_admission_artifacts/execution-task2-post.md),
[task 4 post](raw_source_admission_artifacts/execution-task4-post.md),
with matching `.log` receipts. All 17 cycles saw their expected diagnostic,
restored byte-identically and rebuilt green: **15 proof-protected rejections,
2 fixture contrasts, 0 runtime kills**. Prefix tests were not falsely attributed
to stages 1-3; all ten runtime families ran at stage 4.

Raw and semantic generic endpoint axiom receipts contain only `propext`,
`Classical.choice`, `Quot.sound`, subsets thereof, or no axioms.
`admitRawSource_fields`, `admitRawSource_certified`, `admitRawSource_reached`,
and `admitRawSource_reached_denotation` use exactly those three standard axioms,
never `sorryAx`. The source/Structural/Traverse proof-token sweep had no matches.
Parsed donor: complete, four events, X/Y `[3,5]`. Asymmetric donor: complete,
12 events, Y `[607,6016]`, Diagonal `[1,0,0,1]`, and an empty buffer.
These are actual `sourceInput` runs; the named kernel theorems still require
their complete-outcome equality. The result.input/output-restricted denotation
boundary and all non-claims in the recipe remain unchanged.

Runtime documentation updated the roadmap's bounded raw link, Proposition 19.1
status, source-record follow-up and DSL/Semantics/root discoverability.
The value sweep retained unrelated ports, line locators, unrelated slice counts,
and historical 39/18/79/six-patch source receipts; this follow-up does not change
the original differential counts. Remaining "by construction" statements concern
Naperian coordinates or existing output-domain checks, not an unproved raw link.
See [value sweep](raw_source_admission_artifacts/execution-value-sweep.log).
`git diff --check` passed.

The configured [token reporter](../../.claude/skills/slice-plan/token-report.py)
found no transcript for this Copilot SDK execution session:
[receipt](raw_source_admission_artifacts/execution-token-report.txt).
Exact cumulative input, context peaks and measured 175M execution compliance
are unavailable, not zero or "passed". Per-task reviews reported staying within
their bounded briefs; no known execution budget breach is asserted.

### Final controller validation

Both unfiltered authoritative manifests passed schema/unique-text checks and
actual cycles: [existing-text](raw_source_admission_artifacts/execution-final-existing.md)
**11/11** and [post-text](raw_source_admission_artifacts/execution-final-post.md)
**6/6**, with matching retained logs and exact expected diagnostics. Every
mutation restored byte-identically and rebuilt green. Classification remains
15 proof-protected rejections, two fixture contrasts, zero runtime kills.
The final installed ten-source SHA256 check passed after these cycles.

The controller full default build passed, exit 0, **8,766 jobs**:
[receipt](raw_source_admission_artifacts/execution-full-build.log).
This is not warning-free: existing project warnings and sorries remain, and
the added Adapter/Admission proofs emit non-fatal Lean linter warnings (unused
simp arguments, an unnecessary tactic sequence and a local variable naming
warning). No new theorem depends on `sorryAx`.

### Whole-branch review gate

Two independent whole-branch reviews of execution base `9f333b91` through
immutable tip `270b517d` are **clean within their stated scopes**:
[soundness](raw_source_admission_artifacts/execution-whole-branch-soundness.md)
and [runtime/fidelity](raw_source_admission_artifacts/execution-whole-branch-fidelity.md).
The soundness review followed the complete actual-success premise chain and
immediate semantic dependencies. The fidelity review independently reconstructed
four patches in memory, verified all ten hashes and the exact stage projections,
and checked every execution-final cycle's expected error/restoration evidence.
Neither review reran builds or mutations or claimed independent runtime evidence.
Both reported no known dispatch-budget breach; exact SDK telemetry is unavailable.

The soundness review records an important evidence limit: the asymmetric donor
has an unused zero-extent source axis, so its full-source UIDVal read/output
specializations are vacuous. They alone do not prove non-vacuous coordinate
evaluation. The generic `RawReadSlots.coordinate` / `RawOutputSlots.coordinate`
APIs can instead use localized term or output Slots without the unused axis;
that applicability was read, not independently instantiated in a scratch proof.
This is not a load-bearing theorem defect and no broader claim is made here.

After review, the controller confirmed the reviewed implementation and runtime
documentation unchanged, then reran the full default build: exit 0, 8,766 jobs.
Only review receipts and this close-out have been added since the immutable tip.
All source/build/mutation/review gates are satisfied. Local integration is next;
no remote push is authorized or performed.
