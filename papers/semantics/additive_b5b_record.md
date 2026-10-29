# B5b declared containing box: execution record

## Authority and snapshot

- Authority: [execution plan](additive_b5b_plan.md), with the
  [authoring record](additive_b5b_plan_record.md) and approved design sections 3-4.
- Execution date: 2026-10-28.
- Branch: `b5b-exec`; isolated worktree:
  `/Users/williammacready/code/python/pyncd/.claude/worktrees/b5b-exec`.
- Base: `f0dd2d78e1f62ad715c55807fc0952339d1f3931`
  (local `main`; ancestry check passed).
- Final implementation/review snapshot:
  `411c2a11b432ff87ba4ac28ab9c23e1601bf68fb`.
  The later evidence commit contains this record and the two reviews, not code changes.
- No patch, production fixture, or mutation-manifest entry was edited.

## Setup and task gates

The preparation script ran from inside the new worktree. Donor: primary checkout;
Mathlib **8101 built / 8094 sources (100%)**, project **363 oleans**.
No Mathlib compilation was observed.

| Step | Observed result | Commit |
| --- | --- | --- |
| Refresh `LeanNCD` | Build completed successfully (8615 jobs) | base |
| T1 check/apply | `git apply --check` and `git apply` exit 0; ten hashes match | `080fc39c` |
| T1 six targets | Build completed successfully (8529 jobs), no `error:` | `080fc39c` |
| T2 check/apply | Both exit 0; three hashes match | `d0f0d8f0` |
| T2 two targets | Build completed successfully (8563 jobs), no `error:` | `d0f0d8f0` |
| T3 check/apply | Both exit 0; `git diff --check` clean | `411c2a11` |

T1 targets: `Eval.Plan.B5NativeTest`, `Eval.Plan.B5BoundaryTest`,
`Eval.Plan.B5bBoxTest`, `DSL.Pipeline.CollectTest`, `Eval.CollectEvalTest`,
`Eval.Plan.CollectPlanTest`. T2 targets: `Semantics.OracleSortRulesTest`,
`Semantics.OracleMixedRefusalTest`.

### Fidelity table

All 13 results match plan section 7, first immediately after the applicable patch,
then together after T3 and again after all mutation restorations. The plan as executed called these "sha256" (corrected afterwards to Git blob IDs), but its specified command
`git hash-object` and its 40-hex expected values are Git SHA-1 blob IDs; the exact
specified values were checked, not substituted with a different hash algorithm.

| File under `leanncd/` | Observed Git blob ID |
| --- | --- |
| `LeanNCD/DSL/Pipeline/Collect.lean` | `50b81b773377d138599314c31d68ade776927bab` |
| `LeanNCD/DSL/Pipeline/ScheduledValidation.lean` | `cc8efc1849dfab11f5583e61ffccdb990cd7b1dc` |
| `LeanNCD/Eval/CollectorShape.lean` | `5ba6422c18943e1a25cb3cc9eed6b5f59d8472ed` |
| `LeanNCD/Eval/Error.lean` | `73460910d2d10301d2606cc6468a29db5108b6af` |
| `LeanNCD/Eval/Eval.lean` | `4a3589dda9fba385fc60f1ad6a1f1568ac00b272` |
| `LeanNCD/Eval/Plan/Compile.lean` | `5684743c98864986562b69a0aab123dfc27f5923` |
| `lakefile.toml` | `d6ccd66db9f46538666a2cea31fe26904c78eba8` |
| `test/Eval/Plan/B5BoundaryTest.lean` | `fd1ac0e229d24dac97e12eae07c33f2a62a6e8ea` |
| `test/Eval/Plan/B5NativeTest.lean` | `2d1261ef3d1519ee0f2eb55d6ff5b10bd0c658c6` |
| `test/Eval/Plan/B5bBoxTest.lean` | `39cc162f95a86c3d14157965ea0402d2011b0319` |
| `test/Semantics/OracleMixedRefusalTest.lean` | `3912d02a7ac668b9bd667d89d66ecea619572a9e` |
| `test/Semantics/OracleSortRules.lean` | `0d5d497926f29ca457a23c118f6979d2a7657520` |
| `test/Semantics/OracleSortRulesTest.lean` | `f17b78c744d22ecce3f1bc6410bb1d0c5308ce4f` |

### T3 sweep

The two commands in plan T3 were run verbatim from the worktree, with output
redirected to controller-session logs:

- Rule/value sweep: **74 matching lines in 25 files**.
- `81|nine hand|five accepts` sweep: **5 matching lines in 2 files**:
  one live Semantics node line and four historical B5 record lines.
- The live node explicitly says eleven hand rows, seven accepts, four refusals,
  and 81 `writerExtentExceedsBox` refusals.
- Hits cover the box rule and exact twins, historical B5 plans/patches/evidence,
  and unaffected generic size-conflict or scan extent checks. The command's
  `!additive_b5_patches/**` glob does not exclude nested historical patch paths
  in this invocation; its **19 historical patch hits** are included, not hidden.
- Relative Markdown links in the four edited papers: **19 checked, zero missing**.
- No master plan naming B5b was found in the plan/documentation searches, so no
  Task-N completion blockquote was added.

## Values re-observed on the executed tree

These are executed Lean fixture guards from the fresh targeted builds and a
temporary, subsequently removed observation file run through `lean-file.sh` after
the mutations restored production. They are not hand-derived values or merely
copied authoring observations.

- Assign scratch of extent 2 read over extent 4: `[5, 7, 0, 0]` on reference,
  checked f64, and checked f32; the three-leg agreement guard passed.
- Bare read of scatter scratch `S1[2*j]`, `j = 1`, over `k = 4`:
  `sizeConflict` UID 2, `4 vs 2`, on all three native paths.
- Shifted read `S1[k + w]`, `w = 1`: `[5, 0, 0, 0]` on all three paths;
  the three-leg agreement guard passed.
- `concat` and reversed writer order: reference, checked f64, and checked f32
  all yield `[-5, -2, -7, -3]` (inputs `[-5, -2]`, `[-7, -3]`).
  The observation file also printed this result on all three paths.
- Short bare writer in a pinned box: `[5, 20, 28, 0]`; larger scatter box:
  `[-5, -7, -2, -3, 0]`. Tropical holes retain `-inf`/`+inf`, including f32 bits.
- Exact twins retain the pinned mismatch payloads; exceeding writers retain
  the box/writer/dimension payloads; negative writer still reaches B6.
- The oracle guards execute the 81-refusal histogram and eleven-row/seven-accept
  counts, and genuine four-leg box overlap values:
  real `[8,0,20,0,51,0,118,0,0,0]`,
  max-plus `[20,-inf,7,-inf,17,-inf,40,-inf,-inf,-inf]`,
  min-plus `[-5,inf,2,inf,3,inf,25,inf,inf,inf]`.
- Thus the scratch observations from plan section 3 were re-observed on the
  executed tree, where these single-writer programs remain unchanged; the old
  pre-B5b rejection of `concat` is historical, not claimed for the modified tree.

## Controller final gates

- Full `Tests JaxExperiment`: **Build completed successfully (8840 jobs)**, exit 0.
- Unfiltered mutation preflight: `manifest OK: 13 entries, 13 selected, every old-string unique`.
- Real mutation-manifest run: **13/13 cycles passed**, exit 0.
  Every mutation failed for its expected reason, restored byte-identically, and
  rebuilt green. Controller log verification found thirteen summaries with
  `mutation_exit=1 restore_hash_exit=0 restored_build_exit=0`, thirteen manifest
  PASS verdicts and no FAIL verdict. The full generated table is
  [preserved separately](additive_b5b_mutation_results.md).

| Mutation | Result | Expected failure seen | Byte-identical restore | Restored build |
| --- | --- | --- | --- | --- |
| M01 fit becomes strict less-than | PASS | yes | yes | green |
| M02 boxed groups keep equality | PASS | yes | yes | green |
| M03 fit check dropped | PASS | yes | yes | green |
| M04 any declaration is a box | PASS | yes | yes | green |
| M05 partially pinned declaration is a box | PASS | yes | yes | green |
| M06 no scratch exemption | PASS | yes | yes | green |
| M07 exemption applies to exact groups | PASS | yes | yes | green |
| M08 reference sizing ignores exemption | PASS | yes | yes | green |
| M09 checked sizing ignores exemption | PASS | yes | yes | green |
| M10 no pinned sizes reach obligations | PASS | yes | yes | green |
| M11 predictor ignores boxes | PASS | yes | yes | green |
| M12 predictor fit direction reversed | PASS | yes | yes | green |
| M13 observation maps box error to mismatch | PASS | yes | yes | green |

## Independent reviews and adjudication

Both reviewers were launched in separate fresh contexts against committed
snapshot `411c2a11b432ff87ba4ac28ab9c23e1601bf68fb`, without nested delegation.
Each owns a separate findings file and was instructed to append evidence as it goes:

- A, acceptance/shape: [review](additive_b5b_review_acceptance.md), **complete,
  zero correctness findings**. Every section 5 case and the named unchanged
  siblings were inspected.
- B, oracle independence: [review](additive_b5b_review_oracle.md), **complete,
  zero correctness findings**. Independent declaration/extent prediction and
  actual four-leg execution were traced, without borrowing production helpers.

All observations were adjudicated; no code fix was required:

| Observation | Adjudication |
| --- | --- |
| A: additional f32 later-dimension and bare-exact pins | Optional coverage, not an observed divergence; shared paths inspected. Not required for the goal; parked, roughly one direct test dispatch. |
| A: direct output-shape assertions beyond data-bit checks | Optional coverage; unchanged collector basis still determines shape. Not required for the goal; parked, roughly one direct test dispatch. |
| B: staged-row comment says "bool" for the max-plus donor | Confirmed comment-only typo inside the supplied patch. No effect on counts, values or admission; leave exact patch bytes unchanged. Not required for the goal; parked, roughly one direct documentation dispatch. |
| B: no iter-pinned staged row | Coverage limitation, not a bug in the independently inspected declaration rule. Not required for the goal; parked, roughly one direct test dispatch. |
| B: late-dimensional/B6 precision coverage | Report initially conflated the paths. Same reviewer corrected its report and appended adjudication: late-dimensional is reference/f64 checked; negative-writer B6 is reference/f32 preparation. Optional complementary precision coverage remains parked, roughly one direct test dispatch. |

Reviewers did not run builds or mutations; all required build/mutation evidence
above was run by the controller. Reviews finished before mutations began.

## Budget, exclusions, and integration

The repository token reporter was actually invoked for Copilot session
`0c538145-1985-4bdf-ac5e-ec49e2e655d3`; it reports **no transcript for session**.
That reporter cannot measure this SDK session. The SDK's own numeric
`session.usage_record` events do provide a real measurement, deduplicated by usage
ID and grouped by source session. Cumulative context is the sum of disjoint
input/cache-read/cache-write token details, avoiding double counting SDK
`inputTokens` (which already includes cached input).

At the post-mutation/pre-integration checkpoint:

| Context | Recorded calls/turns | Cumulative input including cache | Peak input |
| --- | --- | --- | --- |
| Controller `0c538145-1985-4bdf-ac5e-ec49e2e655d3` | 51 | 2,956,979 | 94,990 |
| Reviewer session `41eb75fa-f979-47e4-84bb-b4f57b728960` | 21 | 1,154,052 | 94,046 |
| Reviewer session `9f14e77b-8c7b-4e98-8f6c-17d34f0e7f06` | 25 | 1,614,950 | 95,629 |

Measured cumulative total: **5,725,981 input tokens (5.726M)**, below the
approximately 25M execution target. This is a checkpoint, not a claim that later
close-out calls consume zero tokens. No 60-turn or 250k peak-context breach was
observed at this checkpoint; neither reviewer reported a breach.

Scope exclusions remain unchanged: single-writer declaration asymmetry, M4
actual-write-image fit, inferred-size boxes, route/JAX widening,
predicate/multi-axis/constant scatter, and F3.

No required task, gate, mutation, review, or section 3 observation was skipped.
The conditional master-plan blockquote was inapplicable (no B5b master-plan
entry found). Optional review suggestions were deliberately parked as above.
The temporary observation file was removed without changing any shipped fixture.

This evidence is committed after the final implementation snapshot; only the
record, the two review reports and the mutation results are added. Local
integration follows this evidence commit using `merge --no-ff`, an empty
`git diff --stat main b5b-exec` check, worktree removal and branch deletion.
The controller reports the resulting merge hash; embedding this evidence
commit's own hash in itself is not attempted. **No push is authorized or performed.**

## Post-landing coverage widening (2026-10-28)

Follow-up to the review's parked optional gaps, test-only (no production change), `B5bBoxTest` and
`OracleSortRulesTest`:

- checked-f32 guards for the later-dimension cases (`lateExact`, `lateExceeds`, `lateMismatch` bits)
  and for `bareExact`;
- direct output-shape assertions on all three native legs for `concat` (`[4]`), `bareMismatch`
  (`[4]`), `declaredMismatch` (`[5]`), `tropBox` (`[5]`), `lateMismatch` (`[4, 3]`);
- `iter`-pinned boxes: native `iterBox` (accepted, `[-5, -2, -7, -3]`, shape `[4]`) and
  `iterExceeds` (`writerExtentExceedsBox "S" 2 0 3 4` on all three legs), plus two oracle staged rows
  (iter box 12 accepted, iter box 4 refused). `sizesOf` in the oracle test now reads `.iter` pins;
  staged rows are 13, eight predicted accepts.

The f32 and f64 checked entries share `checkCollectorShapes`, so the f32 guards pin the f32 entry's
wiring rather than additional logic, and no mutant isolates them. No isolating mutant was built for
the shape assertions either; they were observed passing, not shown able to fail on their own.
