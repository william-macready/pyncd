# B5c execution record

Authority: [the execution plan](additive_b5c_plan.md), with
[authoring evidence](additive_b5c_plan_record.md) and
[approved design](additive_single_writer_box_design.md).

## Snapshot and setup

- Branch: `b5c-exec`, isolated worktree `.claude/worktrees/b5c-exec`.
- Base: `806d35abb86e743c0c9c9f9dfe08d9f0c32db5f1` (local `main`).
- Final implementation/documentation snapshot:
  `d634d84ce96b55891d36817302b51b8ebebb2e20`.
  This is the committed snapshot supplied independently to both reviewers.
  The close-out commit adds the two review reports, this record, and the
  adjudicated one-word A1 documentation correction; no production/test code
  changes follow the tested and reviewed snapshot. Its hash is obtainable with
  `git log -1 --format=%H -- papers/semantics/additive_b5c_record.md`;
  the final local merge hash is reported separately by the controller.
- Preparation: primary checkout donor, 8101 built Mathlib oleans / 8094 sources,
  reported **100%**; 364 project oleans. No cold Mathlib build.
- Baseline `LeanNCD` refresh: exit 0,
  `Build completed successfully (8615 jobs)`.

## Patch fidelity and per-task results

Every patch passed `git apply --check` before unmodified replay.

| Task | Commit | Gate observed |
| --- | --- | --- |
| T1 | `cc87adafed734e879e4376563e1a9831116c27ed` | All eight specified targets, exit 0, 8531 jobs |
| T2 | `800d66e5733202b09c7981e0f31e6d07e457ec10` | All three specified targets, exit 0, 8568 jobs |
| T3 | `d634d84ce96b55891d36817302b51b8ebebb2e20` | Required sweeps, paper link existence, and `git diff --check` passed; design status changed to implemented |

`SourceDifferentialScatterTest` was not built until T2, as required.
All nine `git hash-object` results exactly matched plan section 7:

| File (relative to repository root) | Observed Git blob | Result |
| --- | --- | --- |
| `leanncd/LeanNCD/DSL/Pipeline/Collect.lean` | `37bc3daedbe192e677fd19b659045627eabaf9e8` | MATCH |
| `leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean` | `ff9b226cab484a3d38c07e209aa0ffe8a0406d71` | MATCH |
| `leanncd/lakefile.toml` | `daf11e8f1dd8f02050a98cbd70f413d5bb03fadc` | MATCH |
| `leanncd/test/Eval/Plan/B5cSingleBoxTest.lean` | `9e91221b91d5e5dafe61f475c6da93d0b9c565aa` | MATCH |
| `leanncd/test/Eval/Plan/DefaultF32Test.lean` | `f08770bf37dc1e173fec0c81f0a22c62958eca12` | MATCH |
| `leanncd/LeanNCD/Semantics/Source/Differential.lean` | `39f30eae9ca080eb245dc494ba68736e57e8bcb4` | MATCH |
| `leanncd/test/Semantics/OracleSortRules.lean` | `831a6fd18c08a9e17215dc3c153eedb1639914fa` | MATCH |
| `leanncd/test/Semantics/OracleSortRulesTest.lean` | `39856ef09fcc552b295cd7f3d209827dbbe8267f` | MATCH |
| `leanncd/test/Semantics/SourceDifferentialScatterTest.lean` | `96d55ce8fc622f0efd02eb0a8c58411684bbc261` | MATCH |

### Documentation sweep

The exact plan patterns and exclusions produced **158 matching lines in 75 files**:
45 lines for `scatterExtentOverridesDeclared`, 7 for `derived shape`, 1 for
`derives the destination extent`, 19 for `writerExtentMismatch`, and 91 for
`single-writer` (patterns overlap). There were 20 live code/node hits,
35 test hits, and 103 paper/history hits. Historical slice plans, reviews,
patches, and S1 acceptance statements remain historical; the route/default
unpinned entry retains single-writer identity. Live native shape documentation
states the B5c exception, while the extent condition survives for non-boxed writes.
The row-count sweep produced one hit: **seventeen hand rows, eleven accepts,
six shape refusals**. All 16 distinct file-link destinations in the edited
papers existed. Both whitespace checks passed.

## Values re-observed on the executed tree

A temporary `B5cExecutionProbe.lean` imported the new fixture and ran through
`lean-file.sh` after T1's dependency build; it exited 0 and was removed.
The following are actual printed observations, not authoring results.
Reference f64, checked f64, and checked f32 agreed in every row below.

| Program | Shapes / values observed |
| --- | --- |
| Single `S[2*i]`, declared `k = 8` | `[8]`; `[-5, 0, -2, 0, 0, 0, 0, 0]` |
| Same, declared `k = 4` | `[4]`; `[-5, 0, -2, 0]` |
| Same, declared `k = 3` | All three report writer 1, dimension 0: extent 4 exceeds box 3; the fixture pins constructor `writerExtentExceedsBox "S" 1 0 3 4` |
| Same, unpinned `k` | `[4]`; `[-5, 0, -2, 0]` |
| Single bare `S[i]`, declared `k = 4` | `[4]`; `[-5, -2, 0, 0]` |
| Two interleaved writers, declared `k = 8` | `[8]`; `[-5, -7, -2, -3, 0, 0, 0, 0]` |
| Single writer followed by `R[k] := S[k]` | Both `S` and `R` shape `[8]`; `R = [-5, 0, -2, 0, 0, 0, 0, 0]` |
| Tropical single writer, `k = 8` | `[8]`; `[-5, -inf, -2, -inf, -inf, -inf, -inf, -inf]` |

The printed group-membership table for `one`, `oneEqual`, `oneInferred`,
`bareOne`, `idiom`, `identityOne`, `tropOne`, `predOne`, `multiAxisOne`,
`constOne`, `concat`, `transposeOne`, `scalarOne` was
`[[S], [S], [], [S], [], [], [S], [], [], [], [], [], []]`.
T2's successful compilation additionally evaluated the actual guards for
`fH9` parity with zero conditions, `fR` native failure with zero conditions
and scratch `Y#1`, and all 17 staged SHAPED rows / 11 predicted accepts.
The old baseline values in plan section 3 were not re-measured before replay;
only the post-patch values above are claimed as this execution's observations.

## Final controller gates

- Full `Tests JaxExperiment` build: exit 0,
  **`Build completed successfully (8841 jobs)`**.
- Unfiltered mutation preflight: exit 0,
  `manifest OK: 11 entries, 11 selected, every old-string unique`.
- Real mutation run: controller-invoked in the background after the full build,
  exit 0, **11/11 cycles passed**. Builds and mutations did not overlap.
  Every mutated build failed for its expected reason, every file was restored
  byte-identically, and every restored target build passed:

| Mutation | Expected failure seen | Byte-identical restore | Restored build | Verdict |
| --- | --- | --- | --- | --- |
| N01 pinned test dropped | yes | yes | green | PASS |
| N02 D5 dropped for scatters | yes | yes | green | PASS |
| N03 D5 dropped for assigns | yes | yes | green | PASS |
| N04 predicate destinations boxed | yes | yes | green | PASS |
| N05 constant/multi-axis slots collected | yes | yes | green | PASS |
| N06 one-writer group skips B5 | yes | yes | green | PASS |
| N07 no pinned sizes supplied | yes | yes | green | PASS |
| N08 rank-0 destination boxed | yes | yes | green | PASS |
| N09 oracle always predicts override | yes | yes | green | PASS |
| N10 predictor ignores single boxes | yes | yes | green | PASS |
| N11 predictor drops D5 | yes | yes | green | PASS |

All eleven summaries reported `mutation_exit=1 restore_hash_exit=0
restored_build_exit=0`. A final `git hash-object` recheck of all nine pinned
paths matched the original table exactly. Only the execution/review records
remained untracked; there were no production changes after restoration.

## Independent reviews and adjudication

Two fresh contexts were dispatched independently against the committed
snapshot above, each instructed to append findings to its own file as it went.

- A, acceptance/shape: `b13a2ad1-a7b2-4399-b328-33e630bbc168`;
  [review file](additive_b5c_review_acceptance.md);
  **APPROVE WITH NONBLOCKING FINDINGS**.
- B, oracle independence: `f1050926-e254-44b7-b98d-e42713173114`;
  [review file](additive_b5c_review_oracle.md); **APPROVE**, no defects found.

Every reported finding is adjudicated:

| Review / finding | Adjudication |
| --- | --- |
| A1, low: live semantics node says two iter-pinned SHAPED rows, but there are four | Accepted and fixed in this close-out: `two rows` -> `four rows`. This is directly related evidence documentation within T3's scope; row totals 17/11/6 and all code/fixtures remain unchanged. Documentation-only correction, checked with `git diff --check`; no extra build required. |
| B, no findings | Accepted. Independent `singleBoxed` / `declaredShapeWins` restatements verified; SHAPED reaches production; `fH9` is actual parity and `fR` remains an explicit native failure, not a hidden divergence. |

Review A checked the unchanged group/route path and Bridge/Agreement's
statements, including the distinction between B5 multiwriter refusal and
legacy all-bare routing. Both reviewers read the entire 17-file committed diff.
Each wrote its report early and appended evidence during its own investigation.
Neither read the other's report, ran gates, or changed source/tests/manifests.
Their temporary snapshot extracts were removed.

## Scope, skips, budget, and integration

No patch, fixture, or manifest entry was edited to obtain a pass.
M4 actual-image fit, inferred-size boxes, route/JAX shape changes, D1/D2
extensions, and F3 remain outside scope. The three known S cells in plan
section 5 are retained, not silently counted as coverage.

Side issues / limits, parked without work:

- Route singleton-desugar isolation; needed for this goal? no (known S);
  rough cost one focused dispatch.
- Differential D5 isolating fixture; needed? no (known S, admission refuses
  the intended idiom first); rough cost one dispatch, possibly more if admission widens.
- Checked predicate single-writer observation; needed? no (known S);
  rough cost one dispatch, possibly more for capability work.
- Stronger D2 scheduling/end-to-end assertions; needed? no (no current
  failure found); rough cost one dispatch.
- Dedicated undeclared-single/min-plus-hole/f32-reader-value fixture widening;
  needed? no (not claimed as new coverage); rough cost one dispatch.
- SHAPED compares preparation outcomes, not published values/shapes, and retains
  the existing exact-shape `sizeConflict` allowance; stronger oracle? not needed;
  rough cost one dispatch.

Token measurement was attempted with
`python3 .claude/skills/slice-plan/token-report.py 5af39e59-0d5c-4bf5-875c-82d71ec2b2e6`.
It reported `no transcript for session ...` because this execution uses Copilot,
not a Claude transcript. Actual Copilot `session.usage_record` telemetry was
then measured at the completed-review close-out checkpoint. Deduplication used
`accounting.sourceSessionId` and `accounting.sequence`. Every record's
`inputTokens` equaled input + cache-read + cache-write token details, so cached
tokens are included exactly once, not added a second time.

| Context source session | API calls at checkpoint | Cumulative input | Peak input |
| --- | --- | --- | --- |
| Controller `5af39e59-0d5c-4bf5-875c-82d71ec2b2e6` | 55 | 4,179,818 | 108,541 |
| Independent review context `bcd8c029-40b1-497d-9e1b-dd34d0b77c59` | 26 | 1,809,275 | 116,708 |
| Independent review context `6402fe75-026e-4eb6-9617-cb3c972df642` | 24 | 1,390,578 | 90,997 |
| **Total through review receipt** | **105** | **7,379,671** | **116,708 maximum** |

The measurement excludes subsequent documentation finalization and local
integration calls, not builds or review work. Both review dispatches remained
below 45 rounds and 200k peak; none breached the plan's 60-turn/250k dispatch
limits. Measured execution cost is below the approximately 30M target and
175M slice limit; no measured token-budget breach. Final controller overhead
and any controller-only round-limit overrun are reported in the session.

All required patch, hash, targeted-build, sweep/link/whitespace, full-build,
mutation, and independent-review steps ran. No required gate or mutant was
skipped; no FAIL verdict occurred. The three disclosed S cells and the
pre-replay historical values are not claimed as freshly tested coverage.
The only post-review change is the adjudicated one-word documentation fix.

Integration policy: merge locally from the primary checkout using `--no-ff`,
verify `git diff --stat main b5c-exec` is empty, remove the clean execution
worktree, then delete `b5c-exec`. The controller reports the actual merge hash
and cleanup outcome after those commands. No remote push is authorized or
performed; local `main` is to remain ahead of `origin/main`.

## Post-landing review (2026-10-30)

Landed `main` `e33ee410` was reviewed independently: the nine code hashes match plan section 7; the
docs differ from the T3 patch only in the adjudicated `two rows` to `four rows` fix (an error in the
patch text); a full `Tests JaxExperiment` build on the landed tree is `Build completed successfully
(8841 jobs)`.

**Finding (low, parked, not fixed here): the experimental JAX codegen newly refuses a class of programs.**
`generateForward` on the prepared f64 plan (`bareOne`: a single bare `S[i] := A[i]` into a pinned
`S(k = 4)`) is `labelExtentMismatch 1 0 0 0 0 2 (some 4)`, while the same program with `k` unpinned,
and an identity writer generate (probed; scalar destinations were not). B5c collects the boxed single bare assign, and
the collector's padded read of the shorter scratch is not expressible in the JAX lowering. The refusal
is typed and loud, the path is experimental (`JaxExperiment`, not imported by `LeanNCD`), and no test
covers it, so the plan's "JAX unchanged" was inaccurate for this subset; the plan, design note and
`DSL/AGENTS.md` now say so. Cost to close: teach the JAX lowering a padded bare read, or refuse it
earlier with a source-level diagnostic; roughly one focused dispatch.
