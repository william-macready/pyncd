# Computable reference executor: authoring and execution validation record

Sections 1-7 preserve the historical authoring receipts and their then-pending
implementation gates. Section 8 records actual execution on current local main;
authoring verification is not substituted for any execution gate.

## 1. Status and limits of this record

Authoring Phase B, 2026-10-08, fresh context from verified package artifacts and
the controller's supplied facts. The [live plan](computable_reference_executor_plan.md)
is the execution brief; this record keeps provenance and receipts separate.
**Verified and execution-ready.** Controller replay/build/control gates and both
final whole-package review lenses passed. This is not a production execution record.

The planning worktree HEAD was observed as
`4a30ae09c87ef11d778f175a639b71225868170b`.
Its initial status contained only the new executor package artifacts.
No plan task was executed in Phase B. No Lean source, patch, manifest, evidence,
roadmap marker, prototype, replay, or main checkout was changed by this author.
There was no build, staging, commit, merge, or push in this phase.

Authority windows read: [roadmap](lean_executable_semantics_path.md) Sections
1, 3, 5.1/5.2, and 6. The [specification](tensor_logic_semantics.md) Sections
21/27 were located by headings only; this phase did not reread or redesign the
full semantic sources. No previous slice's receipts were transferred.
New module definitions were inspected as patch windows, not integrated sources.
All new modules/test paths were checked absent in the planning tree.

## 2. Artifact identity and precedence

Primary receipt: [evidence.json](computable_reference_executor_artifacts/evidence.json).
It has four tasks, four replay-tree entries, 22 fixture rows, the 28-cell audit,
theorem/assumption inventories, and A/A2 history.
At Phase B read time the [patch manifest](computable_reference_executor_patches/manifest.json)
was the older three-task core manifest, with candidate `175c3d0`.
The controller subsequently regenerated it mechanically from the four-task
evidence ledger. The current manifest and evidence agree on all four tasks and
candidate `be51d96`; no patch bytes were amended.

### 2.1 Exact patch lineage

Base: `4a30ae09c87ef11d778f175a639b71225868170b`.

| Task | Parent | Prototype commit | Reconstructed tree |
| --- | --- | --- | --- |
| 1 | 4a30ae0 | b1ffa7029d1c3e6a7748a938211ff658461c4c15 | 0a8abb37d8892a93b32794fd3249b5025841b6d6 |
| 2 | b1ffa70 | d0bb9a7f275a57c3e321e1ddb5a6c144cef891d5 | ea92a8622e0d2864c0f15f3a126e2534cf6729f3 |
| 3 | d0bb9a7 | 175c3d07f96196bdecfbc77bd2bfb7c968337c6c | ae0431c8d1519dcef0aacc92afc8a4d7268367ff |
| 4 | 175c3d0 | be51d96c66c5f823754fd493b39e669237f30258 | 2eed13a7d4b1b354ad150ab489b3746279070180 |

Evidence marks all four replay trees matching. Phase B independently recomputed
all four patch SHA256 values and observed equality with the evidence:

| Patch | SHA256 |
| --- | --- |
| [01.patch](computable_reference_executor_patches/01.patch) | cbba6b0697eafe7a10a77d78e973f85888624090d2cf9d7e5e3e112f05f44a41 |
| [02.patch](computable_reference_executor_patches/02.patch) | 56d85f03707a169e8ee713a7868082f6bc9dd60a204efa1feec67a82d7fece0d |
| [03.patch](computable_reference_executor_patches/03.patch) | 60c969e5fbb2bc701dbd419be77d4e30d4ea78169688744783d6415839243ed6 |
| [04.patch](computable_reference_executor_patches/04.patch) | 153a7339587108557ebda519a9ac400fcd9cf7fe2a4fd7f0fba89e4a523db548 |

Other observed package digests:

| Artifact | SHA256 |
| --- | --- |
| [evidence.json](computable_reference_executor_artifacts/evidence.json) | 3de3a9cdf0d84efb27bc08a4d72bd0e804c5c24874b0148bce2a6d754f7ddfbc |
| [manifest.json](computable_reference_executor_patches/manifest.json), after controller reconciliation | 94e51519f1021fe3c1a51c58bef6679cd22d635016e0f8e92e47e65c804409e7 |
| [16-control manifest](computable_reference_executor_mutations_post.json) | aed82925958f13d22ea59f522312689dff7c7584d514ecb0399aab7c8610af04 |
| [3-smoke manifest](computable_reference_executor_smoke_mutations_post.json) | 8dc9b5ab67cd54bcbdb0666f4d97ca53843283d45e1b7c903eeb423b86163fa7 |

Except for the explicitly reconciled manifest, these are Phase B read-time
identities, not a claim that future compatible-main execution has those tree hashes.
The controller must freeze/cross-check its reviewed package before execution.

### 2.2 Allowed future path set and discovery

Task 1 creates [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean).
Task 2 creates [ExecutableSelection.lean](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean).
Task 3 creates [ReferenceExecutor.lean](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean),
[RationalReference.lean](../../leanncd/LeanNCD/Semantics/RationalReference.lean), and
[ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean);
it edits [Semantics.lean](../../leanncd/LeanNCD/Semantics.lean),
[lakefile.toml](../../leanncd/lakefile.toml), [leanncd AGENTS](../../leanncd/AGENTS.md),
and [semantic AGENTS](../../leanncd/LeanNCD/Semantics/AGENTS.md).
Task 4 edits only that future test file.

Patch 3's inspected hunks add the rational entry import, the default `Tests`
glob entry, and both AGENTS discoverability updates.
The existing public [LeanNCD.lean](../../leanncd/LeanNCD.lean) is not a patch output.
This is intended transitive public discovery, subject to later target validation.
No production evaluator is in the mutation or implementation path set.

Planning hook-window measurement: Patterns body 456 characters plus Global
Pitfalls body 2,525 characters in [leanncd AGENTS](../../leanncd/AGENTS.md):
2,981 combined, near the approximately 3k guideline. The semantic node has no
headings named Pitfalls/Checks/Patterns/Context. These are bounded-section
measurements, not a claim that entire AGENTS files are under 3k.

## 3. Validation receipts: attribution matters

### 3.1 Controller facts supplied to Phase B

- Isolated planning checkout prepared and fast-forwarded from `e13fd6f` to
  `4a30ae0`, then kept as the planning baseline.
- Donor counts: 8,101 Mathlib oleans, 8,094 Mathlib sources, 224 project artifacts.
- Baseline **LeanNCD target** passed with 8,561 jobs; this is not a full Tests
  baseline receipt.
- Prototype full default build passed with 8,704 jobs.
- Independent materialized replay was detached at `4a30ae0`. Patches 1/2/3 were
  checked/applied sequentially and their targets green. Patch 4 was subsequently
  checked/applied; all 22 outputs were observed and both manifests' `--check`
  passed (16 + 3 entries).
- The controller's first patch-4 invocation used a relative patch path under
  `git -C replay` and could not locate the file. Corrected absolute invocation
  succeeded. This was not patch-content or Lean-build failure.
- Controller smoke discovery ran/restored 3/3 controls successfully. Repetition
  with copied `expect` substrings and the 16-control suite was still a pending
  final gate in the authoring brief.

These facts were supplied by the controller, not rerun by Phase B.

### 3.2 Prototype/A2 receipts inspected

[Evidence](computable_reference_executor_artifacts/evidence.json) reports passing
state/selection targets, smoke/full builds, and A2 fixture/full builds.
It also retains an earlier failed driver-build entry. Later passing entries
must not be flattened into a claim that every exploratory build passed.
The final verified bytes, not earlier attempts, are the implementation package.

[a2-mutations.md](computable_reference_executor_artifacts/a2-mutations.md)
records 16/16 PASS: intended failure, byte-identical restoration, and restored
green builds. [controller-smoke-mutations.md](computable_reference_executor_artifacts/controller-smoke-mutations.md)
was present and inspected: 3/3 PASS with expected-failure column `n/a`.
It supports discovery/restoration only, **not** completion of the later
expect-enforced controller repetition.
No absent controller receipt was read or inferred.

The supplied A2 harness temporarily routed builds through the absolute build
wrapper and restored its scripts. That adjustment is not needed for execution:
the controller used the repository's documented mutation wrappers unchanged,
and verified their base bytes after all cycles.

### 3.3 Independent controller verification

[controller-verification.json](computable_reference_executor_artifacts/controller-verification.json)
records the materialized replay and its log identities. The controller:

- Reconstructed every intermediate tree from the base and exact four patches
  in a disposable Git index; all patch SHA256 values matched.
- Independently checked/applied all four patches to the prepared replay,
  built each task target, and observed all 22 executable rows.
- Ran the actual 16-control suite and the supplemental 3-smoke suite with every
  copied expected failure enforced: **19/19 PASS**.
- Verified byte-identical restoration for each cycle and equality of all nine
  final deliverables with the exact patch-reconstructed candidate.
- Verified the three mutation scripts equal their original base bytes;
  no temporary harness edit was required.
- Ran the full default replay build: **PASS, 8,704 jobs**.

The controller receipts are
[controller-mutations.md](computable_reference_executor_artifacts/controller-mutations.md)
and [controller-smoke-mutations.md](computable_reference_executor_artifacts/controller-smoke-mutations.md).
The latter now records `yes` for expected-failure enforcement, superseding the
earlier discovery receipt's `n/a` without retroactively changing that observation.
No controls were filtered or skipped. These are authoring/replay receipts,
not production execution or integration receipts.

### 3.4 Final reviews and planning-branch build

Two independent reviewers read the whole planning package and the stable
controller-verified replay, accepting controller test receipts rather than
rerunning mutations:

| Lens | Verdict | Manual dispatch count |
| --- | --- | ---: |
| [Semantic/soundness review](computable_reference_executor_artifacts/semantic-review.json) | CLEAN, no must-fix findings | 20 turns |
| [Computability/fidelity/replay review](computable_reference_executor_artifacts/fidelity-review.json) | CLEAN, no must-fix findings | 19 tool-bearing rounds |

The controller accepted both dispositions. The fidelity reviewer records one
62-line read window, two lines over the requested maximum; this did not conceal
a finding or change the validation scope. Actual token/peak measurements remain
unavailable, not measured compliance.

The controller also ran the full default build on the planning branch's
unchanged production baseline: **PASS, 8,699 jobs**. Its log identity is in
[controller-verification.json](computable_reference_executor_artifacts/controller-verification.json).
The different 8,704-job replay includes future executor modules and tests.
Neither count is a permanent requirement. No production Lean source was changed
or prototype implementation merged during plan publication.

Publication whitespace checking excludes the exact `.patch` artifacts: their
blank context lines contain the required unified-diff space prefix, which a
diff of the patch file itself reports as trailing whitespace. Non-patch package
files pass `git diff --cached --check`; patch bytes retain their verified digests.

## 4. Fixture and mutation accounting

22 rows: Group 1 has 10, Group 2 has 6, Group 3 has 6.
Task 3 contains three smoke rows; Task 4 adds the other 19.
The live plan maps every row to its verified donor and discriminating result;
exact complete observed tuples remain in the evidence.

The A2 fixture ledger's empty smoke mutation mappings are a real bookkeeping
boundary. They do not invalidate the later smoke discovery, but they must not be
silently described as original A2 coverage. The smoke manifest supplies:

| Retained smoke row | Observed baseline | Controller contrast |
| --- | --- | --- |
| duplicate | `("complete", 5, [some 4,some 0,some 0], 0)` | S1 expects 2 at the colliding cell instead of 4 |
| ready-failure | `("failed", 1, [none,none,none], 1)` | S2 expects success/zero instead of ready failure |
| blocked | `("blocked", 2, [none,some 0,some 0], 1)` | S3 expects failure instead of blocking |

All non-smoke rows have A2 control mappings.
The full inventory is **19 controls**, classified as follows:

| Class | Labels | Count | What the receipt establishes |
| --- | --- | ---: | --- |
| Production runtime oracle kills | R1-reciprocal, R2-square | 2 | changed registry meanings fail actual executor assertions |
| Fixture contrasts | F1-F10, S1-S3 | 13 | changed fixture inputs/projections/expectations are discriminated |
| Proof/type rejections | P1-P4 | 4 | illegal selector/effect changes fail proof/type obligations |

Do not call these 19 runtime oracle kills.
R1/R2 need the broadened test rows from patch 4 even though owned by Task 3.
Task 2's proof controls can be classified by ownership but all combined controller
cycles are scheduled after all four patches.

Discarded scalar mutation: an initial F4 body rewrite failed in scalar schedule
coverage proofs, not runtime. It was replaced by an expected-record contrast.
Only the corrected observed contrast is counted, not the discarded proof failure
as a production runtime oracle kill.

## 5. Proof, categorical, and scope judgments

Patch inspection supports the four organizing layers:

- Finite Naperian domains and supplied ordered presentations refine representation;
  they do not synthesize orders by classical selection or change read domains.
- Tagged statement/valuation coproducts feed covariant additive collection;
  duplicate bodies and valuations retain distinct identities.
- Strict `Option` partial interpretation precedes collection. Unavailability,
  ready undefinedness, and zero contribution remain different cases.
  Arbitrary primitive maps are not additive; nonlinear placement is protected.
- Published-store extension and selected transition paths refine the existing
  machine relation. The trace-forgetting theorem reuses reachability; no abstract
  Cat/Functor/Kan interpreter or backend correspondence is claimed.

The supplied schedule, coordinate rank, and exact profile are explicit inputs,
not hidden synthesis/checking features. Success results use whole-store soundness;
failure/no-model results require reached initialization.
Arbitrary-state debug outcomes have no unconditional ranked/no-model promise.
Events trace selected transitions; observations inspect current readiness;
there is no full scan log, public scalar/string renderer, CLI, or dense storage.

The evidence's 28-cell case-by-sibling matrix is carried into the plan, including
every intentionally ignored cell and its owning API. No prototype correctness
defect was identified by that audit. This is not proof that every broader
production subsystem was audited.

Observed core theorem axiom lists: `propext`, `Classical.choice`, `Quot.sound`
for selector completeness, default nonexhaustion, ranked dichotomy, model/failure
results. A2 reports the same list for `chainCertificate`, no new axioms, no
`sorry`, and no `native_decide`. Existing classical dependencies are erased proof
content, not runtime enumeration. Final branch audit remains pending.
Prototype linter warnings include unusedSectionVars and unnecessarySeqFocus;
do not claim warning-free or that all warnings were inherited.

## 6. Goals excluded and remaining gates

Excluded: source-production correspondence, named syntax/rank checker, source
elaboration, automatic schedule/rank synthesis, storage/backend refinement,
general cyclic solver, native floats, exact-real transcendentals, custom boundary
policy changes, and full category interpreter.
Heterogeneous non-additive-input runtime coverage remains **parked** as one small
future fixture dispatch; it is not required by this milestone's closed profile.
No new scope was added to close that gap during authoring.

Later implementation actions, not completed by plan authoring:

1. Own fresh execution preflight against current local main, exact sequential
   patch checks, per-task target tests/reviews, and full default green build.
2. Repeat all 19 expectation-enforced controls in the actual execution checkout.
3. Own final whole-branch soundness/fidelity reviews, proof audit, authoritative
   docs sweep, and integration. No roadmap marker moves until later verification.

Independent materialized replay and prototype receipts provide strong package
evidence, not production integration or completion of future implementation gates.

## 7. Authoring discipline and budget

The prototype/fixture authoring and this fresh artifact-only authoring are
separate contexts, satisfying the two-dispatch discipline; the fixture expansion
was a separate A2 continuation. No plan execution happened.

A/A2 claimed at most 60 manually counted turns per dispatch; A2's artifact
upper bound is 50 tool-bearing turns. Those are claims, not telemetry-derived
cumulative token measurements.
Phase B target is at most 45 turns and approximately 250k peak context;
authoring aggregate target is approximately 50M cumulative input tokens.
The Claude-only [token-report.py](../../.claude/skills/slice-plan/token-report.py)
cannot find Copilot session `835c8ec7-4595-4ed3-a54a-048a0d651b33`.
Actual peak/cumulative token metrics are **unavailable**, not zero and not
measured compliance. No known turn/context breach at drafting; report any
subsequently observed breach rather than silently claiming compliance.
Phase B's manually counted upper bound through close-out is 16 tool-bearing
turns, below the 45-turn target; this is not a token-telemetry measurement.

Phase B validation is read-only package digest/schema/count/path validation plus
document checks. No Lean blocks were transcribed, so snippet compilation is not
applicable. Lean builds/mutation execution belong to the controller's receipts
and pending gates, not this authoring phase.

### 7.1 Phase B document validation

- Live plan: 571 lines, within the requested 450-600 aim and approximately
  800-line ceiling; no Lean code blocks.
- All Markdown path links resolve to present files/directories or explicitly
  identified future patch outputs; no unexplained broken links.
- JSON-derived control counts agree with the draft: 19 entries, classified
  4 proof/type, 2 production runtime, 13 fixture contrasts.
- All 22 fixture rows map to at least one control when the original evidence
  and the separate smoke manifest are joined; no unmapped row remains.
- All four patch digests still match the original evidence after document creation.
- Tracked worktree diff remains empty; status adds only the two requested
  documents to the pre-existing untracked package artifacts.
- No build was run or skipped under a claim of passing: this was documentation
  authoring, with controller build/mutation/review gates explicitly pending.

## 8. Implementation execution, 2026-10-08

### 8.1 Preflight and exact replay

The existing isolated execution worktree was clean before setup. Preparation
advanced its stale `e13fd6f` base to current local main, ultimately `c01cb33`;
the intervening main change updated the semantic specification, not protected
implementation paths. Mathlib was verified warm: 8,101 oleans for 8,094 sources,
and 224 project oleans. `LeanNCD` was refreshed before patch execution.

All four patch SHA256 values, evidence entries, commit/tree/parent links, and
allowed header paths matched the manifest. All five new output paths were
absent; protected existing paths had no staged or unstaged changes.
The actual hook-injected Patterns and Global Pitfalls bodies remained 2,981
characters, so no unrelated instruction trimming was needed.

The controller applied the exact patches sequentially, with `git apply --check`
before each application. These are implementation receipts, not claims of
reproducing the historical prototype's whole-tree hashes on a newer baseline:

| Task | Execution commit | Target build | Independent task review |
| --- | --- | --- | --- |
| 1: computable state | `e4b31cd` | `LeanNCD.Semantics.ExecutableState`, 2,956 jobs | No significant issues |
| 2: exact selector | `8a31ceb` | `LeanNCD.Semantics.ExecutableSelection`, 2,957 jobs | No significant issues |
| 3: validated driver/profile/discovery | `16a34b9` | `LeanNCD` and `+Semantics.ExecutableReferenceTest`, 8,566 jobs | No significant issues |
| 4: broader fixtures | `6026f0b` | `+Semantics.ExecutableReferenceTest`, 2,960 jobs | No significant issues |

After all mutations, all nine distinct implementation/wiring paths still
matched the final prototype bytes. Existing semantic definitions, production
DSL/evaluators, and build/mutation scripts were unchanged.

### 8.2 Observed computation and control gates

All 22 distinct named `#eval` assertions ran and passed in the actual execution
checkout. They retain the three smoke rows and add the 19 rows documented in
the [plan's fixture table](computable_reference_executor_plan.md#8-fixture-intent-donors-and-discriminating-observations).
The assertions check full values, traces, payloads, input-error priority, empty
tensor presence, whole-store/nonoutput completion, strict blocking locators,
retained failure state, and exact fuel boundaries, not merely row counts.

Both manifests passed `--check`. The controller then ran the actual manifests,
not only schema checks, with the unmodified repository harness:

| Control | Class | Expected failure seen | Source byte-identical | Restored target green |
| --- | --- | --- | --- | --- |
| P1-pending | Proof/type rejection | yes | yes | yes |
| P2-barrier | Proof/type rejection | yes | yes | yes |
| P3-undefined | Proof/type rejection | yes | yes | yes |
| P4-effect | Proof/type rejection | yes | yes | yes |
| R1-reciprocal | Production runtime oracle kill | yes | yes | yes |
| R2-square | Production runtime oracle kill | yes | yes | yes |
| F1-tagged-body | Fixture contrast | yes | yes | yes |
| F2-tag-projection | Fixture contrast | yes | yes | yes |
| F3-zero-empty-excluded | Fixture contrast | yes | yes | yes |
| F4-scalar-nonoutput | Fixture contrast | yes | yes | yes |
| F5-input-order | Fixture contrast | yes | yes | yes |
| F6-empty-presence | Fixture contrast | yes | yes | yes |
| F7-fuel-terminal | Fixture contrast | yes | yes | yes |
| F8-blocked-locator | Fixture contrast | yes | yes | yes |
| F9-failure-snapshot | Fixture contrast | yes | yes | yes |
| F10-coordinate-chain | Fixture contrast | yes | yes | yes |
| S1-duplicate-smoke | Fixture contrast | yes | yes | yes |
| S2-ready-failure-smoke | Fixture contrast | yes | yes | yes |
| S3-blocked-smoke | Fixture contrast | yes | yes | yes |

The combined result is 19/19: 4 proof/type rejections, 2 production runtime
oracle kills, and 13 fixture contrasts. Every mutated build broke for its
manifest's expected reason; every restore and restored build passed.
The full default build passed with 8,704 jobs. No test or control was skipped.
Detailed build and cycle logs are retained in the controller session artifacts.

### 8.3 Proof audit, scope, and remaining close-out gates

The added modules and test certificate contain no `sorry`, `native_decide`, or
new axiom declarations. The six printed audits (`select_none_iff`,
`run_not_exhausted`, `run_ranked_dichotomy`, `result_model`, `result_failure`,
`chainCertificate`) report only `propext`, `Classical.choice`, and `Quot.sound`.
These are existing erased proof dependencies, not runtime classical enumeration.
New unusedSectionVars and unnecessarySeqFocus warnings remain; the build is
green, not warning-free.

The admitted exact-rational profile retains function-valued stores, supplied
complete ordered schedules, and supplied coordinate-rank certificates. Success
and reached failure refine the existing whole-store soundness results. Debug
blocking/exhaustion carry no unconditional no-model claim. Source correspondence,
schedule/rank synthesis or checking, dense/backend refinement, native floats,
exact-real transcendentals, cyclic solving, and full categorical interpretation
remain excluded. The heterogeneous non-additive-input runtime fixture remains
parked at an estimated one small fixture dispatch, not silently completed.

Both final whole-branch code reviews are clean:

| Lens | Reviewed baseline / implementation | Result |
| --- | --- | --- |
| Semantic soundness | `c01cb33` / `6026f0b`, all nine changed paths | No high-confidence load-bearing findings |
| Executable fidelity/integration | `c01cb33` / `6026f0b`, all nine changed paths | No significant fidelity/integration defects |

Neither reviewer reran controller builds or mutations. Each persisted evidence
in controller session artifacts and stayed within the 35-turn review budget;
exact token telemetry was unavailable. The controller's post-mutation full
default build also passed (8,704 jobs).

The authoritative roadmap and specification now describe the verified admitted
rational executor, while retaining source/backend gaps and categorical
separation. Value/status sweeps distinguished historical authoring and earlier
relation-only receipts from current capability claims. The soundness documentation
follow-up was clean. The fidelity follow-up found one factual attribution:
the exact pre-failure snapshot belongs to the failed outcome, not the undefined
event. The roadmap now distinguishes these correctly; fix verification and
the fidelity review are adjudicated clean. Local integration remains pending
at this checkpoint.
No remote push is authorized.

The repository token reporter was invoked for Copilot session
`996f3537-2167-4d8e-b408-13fc5ff025ee` and reported no transcript. Cumulative input
tokens and peak context are unavailable, not zero or measured budget compliance.
The final fidelity fix-verification follow-up reported four turns against its
three-turn local cap, an overrun of one turn. Both initial code reviews and
documentation follow-ups reported staying within their stated caps. Exact
context usage and aggregate token-budget compliance remain unmeasured.

### 8.4 Local integration receipt

Local main was clean and an ancestor of the reviewed implementation before
integration. Merge `6a27bb2` incorporated the completed branch with `--no-ff`;
the controller confirmed identical main/topic trees and merge ancestry.
The integrated-main full default build passed with 8,704 jobs, and all 22
fixture assertions were observed there again. No test or control was skipped.

The merged topic branch was deleted. The execution ledger was archived to
controller session artifacts and its temporary repository directory removed.
The active VS Code worktree is retained clean at detached HEAD rather than
deleting the workspace while this session uses it. This is the only parked
worktree-cleanup step; no other user's branches or worktrees were touched.
Local main remains ahead of origin; no remote push occurred.

The pending integration wording in Section 8.3 describes the earlier checkpoint.
All implementation, validation, review, documentation, and local integration
gates are now complete, with the scope and budget limitations above retained.
