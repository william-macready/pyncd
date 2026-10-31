# Scatter geometry slice A: execution record

## Scope and baseline

Executed [the slice A plan](additive_scatter_geometry_a_plan.md) using its six
verified patches, without hand-repairing patches or changing fixtures.
Process: Full, light. Scope remains checked f64/f32 top-level multi-axis and
constant-slot scatter, shared exact-reach extents, and four-leg tropical tests.
Groups, boxed writers of these forms, and surface syntax remain slice B.

- Execution base: `d48691daa8d08d45bf8645b21b3b6bc85def18f3`, local `main`.
- Working branch: `agents/implement-additive-scatter-geometry`, in an isolated
  linked worktree.
- Preparation fast-forwarded the stale starting branch from `87cfb2fb`.
- Mathlib cache: 8101 built / 8094 sources, reported 100%; project cache:
  365 oleans. No Mathlib cold build.
- Initial `LeanNCD` refresh: successful, 8615 jobs.
- No implementation path changed between the plan's base `6715e128` and the
  execution base; only the plan package changed.
- No remote push is authorized or performed.

## Patch replay and builds

All six supplied patches passed `git apply --check`, were applied in order
without manual repairs, and were committed separately after the prescribed
build passed. Commit subjects were shortened to the repository's conventional
style; the patch order and content are unchanged.

| Task | Commit | Patch check | Build result |
| --- | --- | --- | --- |
| T1 | `49228361986cc47a31b51ba40478f6a361ce75e3` | PASS | successful, 8843 jobs |
| T2 | `c377171a70e9afebc8432dc74613d2179f08dad6` | PASS | successful, 8569 jobs |
| T3a | `7ce8759687ae41de60967a385a7c564be0df5873` | PASS | successful, 8843 jobs |
| T3b | `d6f2476f8cb8a0df3225bc6a39821f3f18150057` | PASS | successful, 8494 jobs |
| T4 | `694ce1db973fb969c719c0576d2125a8a6daa32f` | PASS | successful, 8557 jobs |
| T5 | `ba1c783d7d1c971c05e5651f73a14b3284a09538` | PASS | successful, 8843 jobs |

T1, T3a, and T5 built `LeanNCD Tests JaxExperiment`; T2 built
`Eval.Plan.CompileTest Eval.Plan.ScatterGeometryTest
Semantics.SourceDifferentialScatterTest`; T3b built
`DSL.Pipeline.StructuralTest`; T4 built
`Semantics.SourceSortedDifferentialTest`.

The six implementation commits touch exactly 20 paths, with 834 insertions
and 137 deletions. The final implementation head is
`ba1c783d7d1c971c05e5651f73a14b3284a09538`.
Reports and this record are separate close-out artifacts, not changes to
the supplied implementation blobs.

## Verification and observations

All 20 plan blob checkpoints matched at their owning task and again after
all patches. After stopping mutations, all 20 matched once more; there was
no remaining production-source diff and no manual restoration was necessary.

| Path | Expected and observed blob | Result |
| --- | --- | --- |
| `leanncd/LeanNCD/Eval/Plan/Check.lean` | `ad4b61ebef7757f74cc7a7e0ec84374d9454b89b` | PASS |
| `leanncd/LeanNCD/Semantics/Source/Differential.lean` | `66a88a8d0831c8d43037ec948b9f07d53f4d97c0` | PASS |
| `leanncd/lakefile.toml` | `235b03c2e9e0016f413cc7598a223af664fd30c3` | PASS |
| `leanncd/test/Eval/Plan/ScatterCheckTest.lean` | `4697dc7211d4cfb74594d193e788c4533c6d8572` | PASS |
| `leanncd/LeanNCD/DSL/Ast.lean` | `e804a5b3ed927b93a1f4923f6a28002711364e16` | PASS |
| `leanncd/LeanNCD/Eval/Plan/Compile.lean` | `fc821872cd2ae77163327f7a98572d2ea64edb02` | PASS |
| `leanncd/test/Eval/Plan/CompileTest.lean` | `222b2ce10f58f289bc4f40289439984cd4c9acbd` | PASS |
| `leanncd/test/Eval/Plan/ScatterGeometryTest.lean` | `920f35a4714e171c0134ee92519664281ccc64c1` | PASS |
| `leanncd/test/Semantics/SourceDifferentialScatterTest.lean` | `42a3c0d9ae5b4ce6bed27f7e1eafb00310148569` | PASS |
| `leanncd/LeanNCD/DSL/Pipeline/Structural.lean` | `769135b75a17a9a417f31236c8d7acca203e1d27` | PASS |
| `leanncd/LeanNCD/Exec/Uid.lean` | `637fbafd007c00a6270ebf954ba22349a842d7a7` | PASS |
| `leanncd/test/DSL/Pipeline/StructuralTest.lean` | `1e419a9e34b755cfb836feadef78b76871222b43` | PASS |
| `leanncd/test/Semantics/SourceSortedDifferentialTest.lean` | `1fcc04a76b7f01e927c91f7a9bd89dd828de7f70` | PASS |
| `leanncd/LeanNCD/DSL/AGENTS.md` | `077d2170e8a4f38ad9a9c5924102f51e9efbfd01` | PASS |
| `leanncd/LeanNCD/Eval/AGENTS.md` | `5636792eb0aef0a4a38a01e80a8ef4f3ce9241e4` | PASS |
| `leanncd/LeanNCD/Eval/Plan/AGENTS.md` | `91affebe90de89f1343e3603da0cd2c514246a7d` | PASS |
| `leanncd/LeanNCD/Eval/Plan/Error.lean` | `0701c926a9c7784bbbd092870bc270c0578bac32` | PASS |
| `leanncd/LeanNCD/Semantics/AGENTS.md` | `d9c750e5c85e24e63ca6e0fc772e981fa20761ba` | PASS |
| `papers/backend_missing_functionality.md` | `1bfd3c037e98d9baeed7ff25f594cbb6c899da76` | PASS |
| `papers/scatter_affine_lhs_writes.md` | `c6a13747e5136c6572cbdaa270644be3087e10f9` | PASS |

### Fixture observations

Successful builds evaluated the existing `#guard`, `#guard_msgs`, and
`run_cmd` assertions, rather than merely typechecking expected-output
comments. They confirm the supplied fixtures, but not arbitrary programs;
the additional counterexamples below demonstrate the missing coverage.

- T1's extent controls, empty named-axis guards, direct B6 corner diagnostics,
  and the differential declared/derived twin passed. `a+b` has extent 6,
  `a+4b` has extent 12, and `2a+3b` has extent 13. Single-axis `2*i`
  over 4 remains extent 8.
- T2's reference/f64/f32 polynomial product is
  `[1,12,123,234,340,400]`; wide placement is
  `[1,2,3,4,10,20,30,40,100,200,300,400]`; the legal mixed-sign
  cross-correlation is `[100,210,321,432,43,4]`.
- T3's constant placement has shape `[4]`, cells `[0,0,0,10]`, and
  placement fields `(#[#[1,0]], #[3], #[4], #[1,4])`. Both assignment
  and scatter arms, two-constant placement, max reduction, raw bypass
  refusal, genuine constant group refusals, and derived boxed shapes passed.
  `StructuralTest` confirmed the retained scan-constant error and its
  nearest legal scan.
- Native f32 convolution bits are
  `[1022739088,1046562735,1047233823,1061830000,1050253722,1059145646]`;
  the independent non-scatter twin matches. Constant f32 reduction gives
  `[0,0,0,1266679808]`, while f64-then-narrow gives
  `[0,0,0,1266679810]`, preserving the precision discriminator.
- T4 evaluated eight max/min geometry cases and reported four-leg parity:

| Geometry | Max-plus cells | Min-plus cells |
| --- | --- | --- |
| `a+b` | `[2,11,101,102,103,104]` | `[2,3,4,5,14,104]` |
| `2a+3b` | `[2,-inf,3,11,4,12,101,13,102,14,103,-inf,104]` | `[2,+inf,3,11,4,12,5,13,102,14,103,+inf,104]` |
| constant, scatter arm | `[-inf,-inf,-inf,4]` | `[+inf,+inf,+inf,1]` |
| constant, assign arm | `[-inf,-inf,-inf,4]` | `[+inf,+inf,+inf,1]` |

The historical P0 runs and authoring/replay performance in plan section 4
were not independently rerun; removed historical worktrees and old
pre-change behavior are not claimed as current measurements.

### Mutation execution

Unfiltered `mutation-manifest.sh --check` passed: 31 entries, every
old-string unique. The controller began serial task runs with the original
manifest unchanged, then stopped after the acceptance review exposed A1/A2.
Seven complete cycles passed their intended diagnostic checks, byte-identical
restoration checks, and restored builds. No mutation verdict failed.
The remaining 24 entries were not run; their targets below are prescribed
targets, not claimed observed killers. A task-level results table was not
completed because the run was interrupted.

| Entry | Observed killer / prescribed targets | Result |
| --- | --- | --- |
| SGA-T1-01 | Eval.Plan.ScatterCheckTest | PASS; exact restore; restored build green |
| SGA-T1-02 | Eval.Plan.ScatterCheckTest | PASS; exact restore; restored build green |
| SGA-T1-03 | Eval.Plan.ScatterCheckTest | PASS; exact restore; restored build green |
| SGA-T1-04 | Eval.Plan.ScatterCheckTest | PASS; exact restore; restored build green |
| SGA-T1-05 | Eval.Plan.ScatterCheckTest | PASS; exact restore; restored build green |
| SGA-T1-06 | Eval.Plan.ScatterCheckTest | PASS; exact restore; restored build green |
| SGA-T1-07 | Eval.Plan.ScatterCheckTest | PASS; exact restore; restored build green |
| SGA-T1-08 | Eval.Plan.ScatterCheckTest | NOT RUN: A1/A2 |
| SGA-T1-09 | Semantics.SourceDifferentialScatterTest | NOT RUN: A1/A2 |
| SGA-T2-01 | Eval.Plan.CompileTest, Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T2-02 | Eval.Plan.CompileTest | NOT RUN: A1/A2 |
| SGA-T2-03 | Eval.Plan.CompileTest, Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T2-04 | Eval.Plan.B5BoundaryTest, Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T2-05 | Eval.Plan.B5cSingleBoxTest, Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T2-06 | Eval.Plan.B5NativeTest, Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T2-07 | Semantics.SourceDifferentialScatterTest | NOT RUN: A1/A2 |
| SGA-T3-01 | Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T3-02 | Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T3-03 | Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T3-04 | Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T3-05 | Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T3-06 | Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T3-07 | Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T3-08 | Eval.Plan.ScatterGeometryTest | NOT RUN: A1/A2 |
| SGA-T3-09 | DSL.Pipeline.StructuralTest | NOT RUN: A1/A2 |
| SGA-T3b-01 | DSL.Pipeline.StructuralTest | NOT RUN: A1/A2 |
| SGA-T3b-02 | DSL.Pipeline.StructuralTest | NOT RUN: A1/A2 |
| SGA-T3b-03 | DSL.Pipeline.StructuralTest | NOT RUN: A1/A2 |
| SGA-T4-01 | Semantics.SourceSortedDifferentialTest | NOT RUN: A1/A2 |
| SGA-T4-02 | Semantics.SourceSortedDifferentialTest | NOT RUN: A1/A2 |
| SGA-T4-03 | Semantics.SourceSortedDifferentialTest | NOT RUN: A1/A2 |

After diagnostic verification and removal of the temporary diagnostic file,
the controller ran `LeanNCD Tests JaxExperiment` again: **successful, 8843
jobs**. A green default build does not adjudicate away the reproduced bugs.

### Documentation gates

Exact value-grep commands from section 8 produced:

| Pattern | Hit count | Adjudication |
| --- | --- | --- |
| `multiAxisScatterLhs\|scatterOrAffineLhs` | 19 | Real code producers and historical/scan refusals remain valid; the predicate example in `capabilityPreflight` is stale (D1). |
| `overlappingScatter` | 6 | Exactly one throw producer remains; other hits document the scan-only guard. |
| `legacy linear\|collapses` | 7 | Correct fallback description and unrelated English uses; the excluded `ScatterCompileTest` comment is outside this command's test search scope. |
| `derives 7\|derives 16\|extent 7\|extent 16` | 3 | Correct three-axis extent, distinct MIN-corner fixture, and unrelated sorted-audit axis; no stale `derives 7`/`derives 16` hit. |

All 13 relative links in the two edited papers resolve.
`DSL/AGENTS.md`'s Pitfalls section is 2200 characters, below 3000.
`git diff --check` passed. All six patches' added lines have no
Lean line-number locators. Review D1 identified additional directly related
live-doc repairs, so the semantic documentation gate is not declared clean.

## Reviews and adjudication

Both separate-context whole-branch reviews completed:

- [Acceptance/correctness report](additive_scatter_geometry_a_review_acceptance.md):
  **findings**, two load-bearing defects.
- [Oracle-independence report](additive_scatter_geometry_a_review_oracle.md):
  **PASS** for the value/fixture wiring and the explicitly agreed shared-extent
  predictor tradeoff; one non-blocking audit wording correction.

The controller stopped mutations, verified exact restored source hashes,
refreshed the test dependencies, and ran a temporary diagnostic module with
`lean-file.sh`. The first diagnostic omitted required `nonlin` fields;
adding `.identity` corrected the diagnostic compile. No production or
existing test was changed. The corrected diagnostic compiled successfully:

| Finding | Observed result | Verdict |
| --- | --- | --- |
| A1: unrelated empty RHS axis, `S[a+b] := A[a]*B[b]*C[c]`, extents 4, 3, 0 | reference `[6]`; checked f64/f32 `[7]`; sparse/dense helpers return 6/7 | BLOCKED: needs consistent sparse/dense empty-domain policy, not a fixture relaxation |
| A2: ordinary `#constUser` axis size 2, destination box size 8 | `boundedScatter == false`; all three legs publish `[2]`; duplicated group gives no successful result | BLOCKED: name prefix is not proof of generated provenance; prior boxed `[8]` is the review's baseline code trace, not a separately run baseline |
| D1: stale predicate example, affine-extent docstring, and ambiguous boxed-writer docs | directly related documentation findings | Park with repair, about 0.1 dispatch |
| O1: section 6's `s6ZeroBase` wording | slot preflight admits; the whole scan is refused | Accept correction in this record; no runtime change owed |
| MIN-corner and historical scan-refusal candidate comments | different valid fixture / explicitly scan-local history | Reject as findings; no edit |

A1/A2 are defects in the supplied plan's exact representation/extent policy,
not mismatched patches. A provenance-safe replacement for the marker, or an
explicitly accepted restriction of previously valid programmatic axis names,
and the empty-domain policy require plan repair. Per the BLOCKED contract,
the controller does not improvise a new representation or hand-repair the
patches. **The branch is not approved for integration despite green builds.**

## Parked scope

The plan's exclusions remain explicit:

- Groups and boxed multi-axis/constant writers, including ignored pinned
  declarations: slice B, approximately one dispatch.
- `declaredShapeWins` mirrors the boxed-writer rule; shared-predicate cleanup
  is optional slice B work, approximately 0.5 dispatch.
- Scan-local multi-axis and hand-built constant scatter overwrite versus
  accumulation: F3, approximately one dispatch.
- Independent mutation isolation for new-module pins shadowed by older B5
  fixtures: parked, approximately 0.3 dispatch.
- Diagonal scatter inside scans and zero-coefficient boxed writers lack
  separate pins: parked, approximately 0.3 dispatch each.
- Stale `LHSSlot.collapses` comment in `ScatterCompileTest`: parked,
  approximately 0.1 dispatch; not needed for this slice.
- No changes to route, JAX admission, predicate/bool destinations, or surface
  negative coefficients/biases; no f32 tropical four-leg harness claim.

## Usage and completion

Copilot SDK runtime `session.usage_record` telemetry was measured directly
from this execution's event ledger, including propagated child-review records,
deduplicated by accounting `sourceSessionId`/`usageId`. `inputTokens` already
includes cache tokens, so cache reads/writes are not added again.
The cross-session usage database had no row for this live session.

Snapshot after the initial close-out evidence commit
`f892862fc5ba8ae0c22708ca4eeeeed7c0a76e1b`:

| Execution context | API calls | Cumulative input tokens | Output tokens | Peak input context |
| --- | --- | --- | --- | --- |
| Controller | 46 | 3959035 | 30675 | 130009 |
| Review context 1 | 32 | 2539558 | 17368 | 132317 |
| Review context 2 | 23 | 1386124 | 16323 | 96522 |
| Total | 101 | **7884717** | **64366** | 132317 maximum |

Combined input/output total is 7949083 at this snapshot. It excludes the
small subsequent close-out/commit/final-response tail; it is not presented
as complete lifetime accounting. No measured context exceeds 250k, each
dispatch is below 60 API turns, and cumulative input is well below both
the 35M slice estimate and the 175M ceiling. The Claude Code token-report
script is not an applicable measurement method for this executor.

**Skipped/deferred:** mutation entries 8-31 (24 entries), clean-review
approval, integration to local `main`, branch deletion, and worktree removal.
The historical P0 and prior authoring runs were not rerun. No remote push
was performed. No step is silently treated as passed.

**Final status: BLOCKED.** Preserve the six implementation commits, this
record, and both reviews on the isolated branch for repair. Local `main`
remains at the execution base. Do not merge or delete the worktree while
the load-bearing findings remain unresolved. Local `main` remains eight
commits ahead of `origin/main`; none of this execution's commits were
merged or pushed.
