# Scatter geometry slice B: execution record

## Scope and commit identity

Executed the binding [plan](additive_scatter_geometry_b_plan.md) and
[brief](additive_scatter_geometry_b_execution_brief.md) without retyping or repairing patches.
Process: Full, six patch commits, real mutations and two independent review contexts.

- Base: `fd922285d4e779210f76c26d0e64ed7c92df8e52` (the execution brief on local `main`).
- Code-complete head: `f7c731f4146c6fab1e481e79dfe0273c2770748a`.
- Final implementation commit: `f7c731f4146c6fab1e481e79dfe0273c2770748a`.
  The subsequent documentation-only close-out is the second parent of the local integration merge;
  its exact hash and the merge hash are reported at integration rather than made self-referential here.
- Execution worktree: `.claude/worktrees/scatter-geometry-b-exec`, branch `scatter-geometry-b-exec`.
- Preparation: Mathlib 8101 built / 8094 sources (100%); 365 project oleans copied.
  Project refresh passed, 8615 jobs. No Mathlib cold compilation was observed.
- The protected prototype worktree and branch were not modified.

| Task | Commit | Apply check | Patch blob | Owned hash rows | Builds |
| --- | --- | --- | --- | --- | --- |
| T1 | `0193930acb8d501c27ae5e039ca1a743ea3ef34f` | PASS | PASS | 10/10 | Full: 8843 jobs |
| T2 | `02de6e7576c2c9e0a97586f2e8f9e5fcc6a9ae43` | PASS | PASS | No stage rows | Targeted: 8567; full: 8843 |
| T3 | `a83086ca268d196f01bdf9cec2e2ccb9a138df1e` | PASS | PASS | 1/1 | Targeted: 8481 |
| T4 | `192e364049f83387a01de1d40cc5fe9b63894696` | PASS | PASS | 8/8 | Targeted: 8523; full: 8844 |
| T5 | `75406c648ae7670c70dab8594eb2e1113fd7c843` | PASS | PASS | 13/13 | Full: 8844 |
| T6 | `f7c731f4146c6fab1e481e79dfe0273c2770748a` | PASS | PASS | 4/4 | Full: 8844 |

Each apply check ran before its apply, each patch was committed separately with explicit-path staging,
and hashes were checked after the owning task. All six patch blobs and all 36 stage rows matched the
plan exactly. The six commits change 26 distinct paths under `leanncd`, as required.
Targeted and full targets are exactly those specified by each task. No failed gate was repaired or retried.

## Real mutation results

Unfiltered validation reported:
`manifest OK: 18 entries, 18 selected, every old-string unique`.
Real runs followed in order T1, T3, T6, each with a separate output table and log.
The tree was clean after each task. Every cycle broke the intended build, restored the file
byte-identically, passed its restored build and matched every configured expected failure string.

Killer paths below are relative to `leanncd/test`; identifiers, not volatile line pins, identify the
fixtures. Exact failure locations were retained in the execution logs.

| Mutation | Killer module / file | Expected failure | Byte-identical / restore build | Verdict |
| --- | --- | --- | --- | --- |
| SGB-T1-01 | `Eval.Plan.B5BoundaryTest` / `Eval/Plan/B5BoundaryTest.lean` | seen | yes / green | PASS |
| SGB-T1-02 | `Eval.Plan.B5BoundaryTest` / `Eval/Plan/B5BoundaryTest.lean` | seen | yes / green | PASS |
| SGB-T1-03 | `Eval.Plan.B5cSingleBoxTest` / `Eval/Plan/B5cSingleBoxTest.lean` | seen | yes / green | PASS |
| SGB-T1-04 | `Semantics.SourceDifferentialScatterTest` / `Semantics/SourceDifferentialScatterTest.lean` | seen | yes / green | PASS |
| SGB-T1-05 | `Semantics.SourceDifferentialScatterTest` / `Semantics/SourceDifferentialScatterTest.lean` | seen | yes / green | PASS |
| SGB-T1-06 | `Eval.Plan.B5cSingleBoxTest` / `Eval/Plan/B5cSingleBoxTest.lean` | seen | yes / green | PASS |
| SGB-T1-07 | `Eval.Plan.ScatterGeometryTest` / `Eval/Plan/ScatterGeometryTest.lean` (`rawInGroup`, F8) | seen | yes / green | PASS |
| SGB-T1-08 | `Eval.Plan.B5bBoxTest` / `Eval/Plan/B5bBoxTest.lean` | seen | yes / green | PASS |
| SGB-T1-09 | `Eval.Plan.B5NativeTest` / `Eval/Plan/B5NativeTest.lean` | seen | yes / green | PASS |
| SGB-T3-01 | `DSL.ParseProgramTest` / `DSL/ParseProgramTest.lean`; `Eval.Plan.ScatterSurfaceTest` / `Eval/Plan/ScatterSurfaceTest.lean` | seen | yes / green | PASS |
| SGB-T3-02 | `DSL.ParseProgramTest` / `DSL/ParseProgramTest.lean` only | seen | yes / green | PASS |
| SGB-T3-03 | `DSL.ParseProgramTest` / `DSL/ParseProgramTest.lean`; `Eval.Plan.ScatterSurfaceTest` / `Eval/Plan/ScatterSurfaceTest.lean` | seen | yes / green | PASS |
| SGB-T3-04 | `DSL.ParseProgramTest` / `DSL/ParseProgramTest.lean`; `Eval.Plan.ScatterSurfaceTest` / `Eval/Plan/ScatterSurfaceTest.lean` | seen | yes / green | PASS |
| SGB-T3-05 | `DSL.ParseProgramTest` / `DSL/ParseProgramTest.lean`; `Eval.Plan.ScatterSurfaceTest` / `Eval/Plan/ScatterSurfaceTest.lean` | seen | yes / green | PASS |
| SGB-T3-06 | `DSL.ParseProgramTest` / `DSL/ParseProgramTest.lean` only | seen | yes / green | PASS |
| SGB-T3-07 | `DSL.ParseProgramTest` / `DSL/ParseProgramTest.lean` only | seen | yes / green | PASS |
| SGB-T3-08 | `DSL.ParseProgramTest` / `DSL/ParseProgramTest.lean` only | seen | yes / green | PASS |
| SGB-T6-01 | `Eval.Plan.ScatterSurfaceTest` / `Eval/Plan/ScatterSurfaceTest.lean` (`r1Surf`) | seen | yes / green | PASS |

Totals: T1 **9/9**, T3 **8/8**, T6 **1/1**, overall **18/18**.
Only SGB-T1-07 is killed by the new T2 fixtures; the other engine kills are by upstream
pre-existing/re-pinned guards or `SourceDifferentialScatterTest`. F1-F6 independent kill power remains
unmeasured. T3 expected strings identify files, not individual guards, and term order is value-invariant:
its reversal is detected by parser structure only. T6 separately targets the new `r1Surf` identity-slot pin.

## Re-observed section 3 values

The replayed source blobs are exact, and the task builds executed their guards on this checkout.
These are guard-confirmed values, not newly invented arithmetic or an independent fixture-kill claim.

| Fixture / surface | Re-observed result |
| --- | --- |
| F1 boxed constant pair plus bare writer | `[8]`; `[1,2,3,24,0,0,0,0]` |
| F2 mixed multi-axis/constant/bare | `[2,14,126,248,340,400,0,0]` |
| F3 tropical | `[2,11,101,102,103,104,4,-inf]` |
| F4 constant / multi-axis boxed singles | `[0,0,0,10,0,0,0,0]` / `[1,12,123,234,340,400,0,0]`; both overshoots refused |
| F5 D5 multi-axis single | Derived `[6]`, no collector group |
| F6 unpinned | Extent mismatch `6` versus `4`; matching pair `[2,24,246,468,680,800]` |
| F7 `#constUser` | Ordinary axis; both compile chains accept; `[1,2,0,0,0,0,0,0]` |
| F8 raw constant schedule | `multiWriterScatter "S"` |
| C1 corpus | 505 programs; classes `[281,186,38]`; 99 concrete shape-stage programs |
| Differential re-pins | `fI1`, `fI2`, `fMask`, `fFbig` parity; `conditionCount fI2 == 0`, `conditionCount fFbig == 0` |
| `convSurf` | `[6]`; `[1,12,123,234,340,400]`; equal to hand-built convolution |
| `biasSurf` | `[10]`; `[0,1,10,102,20,203,30,304,40,400]` |
| `f1Surf` / `constPinSurf` | `[1,2,3,24,0,0,0,0]` / `[0,0,0,0,0,10,0,0]` |
| Lone numeral | Still `.iterAt`; `constLoneSurf` refuses with `noAdvancingAxis "S"` |
| `a + a` / `0*a + b` | `[8]`, `[111,0,222,0,333,0,444,0]` / `[3]`, `[10,100,1000]` |
| Empty source axis with empty input | `[4]`, all zeros |
| Scan-local constant / multi-axis | `overlappingScatter "G"` / `multiAxisScatterLhs "G: affine LHS slot"` |
| `r1Surf` / `r2Surf` | `[4,3]`, row 3 `[1,10,100]` / `[8,3]`, rows 3 and 5 `[1,10,100]`; remaining cells zero |

The numeric fixtures using `agree` confirm reference, checked f64 and native checked f32 bit equality.
Parser guards confirm term order, coefficients and bias; both `=3` and `= 3` produce `.const 3`.
Old single-axis constructors remain pinned (`free`, `freeNorm`, `shift`, `scale`, one-term affine).
No claim is made to have repeated the authoring-only unpinned empty-input error probe or arithmetic
counterfactual overwrite calculations. The rank-0 and zero-coefficient-group authoring probes were not
repeated; the plan explicitly permits this. No timing estimate of hours was substituted for a result.

## Reviews, documentation sweeps and final build

The controller's post-mutation full build passed: **8844 jobs** (`LeanNCD Tests JaxExperiment`).
Reports:
[siblings](additive_scatter_geometry_b_exec_review_siblings.md) and
[surface/document truth](additive_scatter_geometry_b_exec_review_surface.md).
Both lenses completed all three assigned work items. Neither found a production blocker or a
load-bearing design question. Lens 2 also ran the combined parser/surface target: 8524 jobs, green.

| Finding | Adjudication |
| --- | --- |
| L1-K1: test-side multi-axis extent predictor still uses legacy sum | Park, already explicitly excluded by plan section 2; about 0.3 dispatch |
| L1-N1: acceptance re-pins using `sourceError == none` can pass after failed scheduling | Park, about 0.1 dispatch, Direct: add explicit scheduling-success guards. This is a real low test blind spot, not current compilation failure; shape/value fixtures and manifest checks passed. Do not silently improve the supplied fixture patches under this executor-only contract |
| S-1: suspected old-constructor ambiguity | Reject: disjoint grammar and exact old-constructor guards |
| S-2: degenerate forms | Park under existing validation scope, about 1 dispatch (group pin about 0.2); no new semantics decision |
| S-3: semantic documentation's boxed-shape summary omits D5 | Park, about 0.1 dispatch, wording only. The omission is real; detailed production/oracle comments and the approved plan already state D5, and `r1Surf`/`r2Surf` pin it. Preserve the supplied T5 blob, carry the correction explicitly, and state the exception in these completion notes |
| S-4: suspected missing advertised surface pins | Reject: all advertised slot, scan-refusal and D5 guards exist and passed |

These are final controller verdicts; the reviewers' proposed fix-now labels were recommendations,
not work silently performed. Both new low findings are reported, not described as fixed or clean.

T5 sweeps, with commands and complete outputs in the surface report:

| Pattern / search root | Output |
| --- | --- |
| `boundedScatter\|isConstUnit\|constUnitPrefix\|checkReservedAxisNames\|reservedAxisName` in `leanncd`, Lean/Markdown globs and prescribed exclusion | 3 hits, 1 file; all deleted/reversed historical comments |
| `slice B\|Slice B` in `leanncd/LeanNCD` | 10 hits, 8 files; implemented/current descriptions |
| `multiWriterScatter\|multiAxisScatterLhs\|scatterOrAffineLhs` in production Markdown | 6 hits, 3 files; capability claims correct, with S-3's separate shape-summary omission |
| Added `.lean` line citations in patch files and the reviewed branch diff | 0 hits |

Review reports normalize volatile source line numbers before shipping; original reviewer transcripts
are retained in session evidence. This preserves commands, hit text and counts without shipping
unstable source-location citations. The final close-out documentation receives the same citation check.

The master scatter design now has an A/B execution-status table and marks its admission table as
historical; the slice B design has a completion note, and the slice B plan links this record.
Other narrative snapshots excluded by T5 remain historical, not silently refreshed.

## Carried-forward parked scope

Estimates are dispatch costs, not measurements; none was started.

| Item | Owner / estimated cost |
| --- | --- |
| Scan-local constant/multi-axis semantics | F3 / about 1 |
| Predicate groups; negative surface coefficients/biases; route/JAX scatter | Unowned / not estimated |
| Degenerate repeated/zero coefficients, including no placing term and zero-coefficient D5 | About 1, Direct; re-pin U5 as needed |
| Shared production/oracle/test boxed predicate | About 0.5 |
| Test `predictedExtent` legacy multi-axis sum rule | About 0.3 |
| Narrow D5 to non-identity positions | Owner chose keep D5 / about 1 Direct |
| Zero-coefficient group value pin | About 0.2; group/boxed coverage family about 0.3 |
| Single-writer error says "multi-writer ... writer 1" | About 0.1 |
| Independent F1-F6 kill power | About 1 |
| T3 manifest guard-line expectations | About 0.3 |
| `#const...` axis group/scan coverage | About 0.2 |
| Diagonal-in-scan coverage | About 0.3, inherited |
| Historical narrative wording in semantic path part 4 / gap audit | About 0.2 |
| Other slice A parked nits | Inherited from slice A record; not re-derived |
| Live backend inventory still describes the pre-B group/surface boundary | Not needed for patch replay; about 0.2 wording-only |
| L1-N1 acceptance-guard scheduling-success blind spot | About 0.1, Direct |
| S-3 semantic shape-summary D5 omission | About 0.1, wording-only |

Rank-0 boxed-vacuity disagreement remains closed as unreachable in the authoring audit, not a new
execution measurement. Repeated-axis group coverage belongs to the degenerate-slot row.

## Usage, skipped work and integration

Telemetry snapshot at `2026-11-01T23:40:17.544388Z`:

| Context | Recorded calls | Cumulative input | Output | Peak input |
| --- | --- | --- | --- | --- |
| Controller | 50 | 4,166,105 | 23,388 | 125,498 |
| Sibling reviewer | 26 | 1,836,706 | 13,845 | 119,870 |
| Surface reviewer | 20 | 1,220,518 | 17,958 | 105,814 |
| Total | 96 | **7,223,329** | **55,191** | maximum 125,498 |

Method: sum deduplicated `session.usage_record` events by accounting usage ID (fallback API call ID),
grouped by accounting source-session ID, including reviewer contexts, reporting input and output
separately. Cache tokens are a breakdown of input, not added a second time. Input plus output is
7,278,520 tokens at this snapshot; cumulative input is well below the approximately 175M execution cap.
All contexts are below 60 recorded calls and 250k peak input at this snapshot. Each reviewer handled
three work items; mechanical replay was split into T1-T3 and T4-T6 batches. This measurement excludes
the remaining documentation/commit/integration/final-response calls; it is not mislabelled a
post-response total. Reviewers' unsuccessful Claude-only utility attempts are not the telemetry source.
The approximately 35M authoring estimate in the design is not an execution requirement.

No patch, stage hash, prescribed task build or real manifest entry was skipped.
Optional authoring probes, negative parse runtime probes, isolated F1-F6 mutation liveness and the
two parked review repairs were not run/performed; their limits are stated above.
One early exploratory file-window request overshot a short design file and two requests overshot the
mutation wrapper; the successful bounded reads supplied the required content. No validation gate was
red, skipped, or repaired around.

Integration is authorized only as `merge --no-ff` into local `main`, after this record is committed,
with an empty main/topic diff, clean status, and removal of this execution worktree/branch only.
The host session's original worktree is not the execution worktree and is not removed.
No push is authorized or attempted. Before close-out, the implementation topic was 12 commits ahead of
`origin/main`; this documentation commit and the no-ff merge add two. The final response reports the
observed integration hash and ahead count.
