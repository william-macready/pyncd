# B5b independent acceptance/shape review

- Base: `f0dd2d78`
- Review snapshot: `411c2a11b432ff87ba4ac28ab9c23e1601bf68fb`
- Lens: acceptance/shape; executed patch replay against the B5b plan, not redesign.
- Status: complete — clean acceptance/shape review; no high-confidence correctness findings.
- Constraints: read-only review except this report; no builds, source mutations, commits, nested agents, or consultation of the other review.

## Review log

- Review initialized before reading the authority and branch diff.
- Read plan sections 2, 5, 6, 7 and design sections 3–4 first. Authority requires a fully pinned declaration, per-dimension derived-extent fit, unchanged exact behavior and unchanged downstream scatter shapes/range checks.
- Initial evidence: `CollectorShape.lean:10–28` branches only the extent obligation on `g.boxed`; `:31–40` limits inference rewriting to named boxed scatter scratches. `B5bBoxTest.lean` contains accepted concatenation/reversal, exact and exceeding twins, tropical holes, later-dimension cases, and a negative-writer B6 assertion. These observations are provisional pending sibling/call-site tracing.
- Worktree status shows no tracked modifications; only controller/reviewer untracked reports exist. The other review report was not read.
- Traced both inference consumers: `Eval.lean:147–156` and `Plan/Compile.lean:1511–1520` apply `sizingView` only to top-level plain statements, retain the pre-existing scan-local conversion, and execute/compile the original collected schedule afterward. Shape obligations run before execution (`Eval.lean:161`) or slot allocation (`Plan/Compile.lean:1531`).
- Checked unchanged shape siblings: `SizeInfer.lean:64–71,126–146` derives only actual `.scatter` outputs and checks bare read conflicts; `Eval.lean:16–22,43–45` still allocates original derived scratch extents; `Plan/Compile.lean:525–540,1607–1613` still derives and records those extents in scatter placement and tensor signatures. No box-sized scratch allocation, truncation, or B6 bypass was introduced.
- `Collect.lean:97–140,144–175` keeps the B5 eligibility boundary and rank checks. Fully pinned classification uses declarations and the same declared axes as `writerGroupBasis`; undeclared fallback remains first ordinary bare assignment, and all-bare groups do not acquire B5b shape obligations.
- Re-derived pin authority: `ScheduledValidation.lean:241–256` rebuilds `sourceEnv`, gathers obligations from the source before renaming, and supplies `declaredAxisSizes sched.decls`, not the caller's cached map. `Structural.lean:742–746` includes pinned `.axis` and `.iter` declarations. The same explicit sizes seed both inference paths.
- Verified unchanged RHS sizing: `Ast.lean:518–520` gives assignments and scatters identical `readFactors`; the sizing-only constructor substitution therefore removes only scratch-output sources, not writer RHS constraints.
- Order check: pin classification depends on declarations, not writer order; generated scratch ordinals and obligations both use the same source writer list. `B5bBoxTest.lean:53–54` pins concatenation reversal on all three native legs; existing `B5NativeTest.lean:171–172,193–198` covers declared and undeclared mixed-writer reversal. This is acceptance/order stability, not a new floating-point reassociation promise.
- Route remains gated before physicalization in `Lowering.lean:594–601`, using unchanged `needsB5`; `B5NativeTest.lean:206` asserts a valid pinned interleave still reports `routeUnsupportedMultiWriter`.
- B6 remains independent of fit: `Scatter.lean:72–75` checks every actual reference write against the scratch extent; `Plan/Check.lean:460–483` validates derived extents and then image bounds. The negative writer and zero-scale guards deliberately reach these checks after fitting their declared box.
- Read the whole committed diff, including the native guard replacements, oracle changes at shallow scope, registration of `B5bBoxTest` in `lakefile.toml`, and all changed live/paper documentation. No production change outside the planned metadata, obligation, sizing-view and diagnostic surface was found.
- Confirmed `HEAD` is exactly the requested snapshot. Read unchanged scan-local fixtures (`ScanCompileTest.lean:1943–1995`, base stride, step stride and interleave; `ScanTest.lean:665–692`) and all-bare UID/identity fixtures (`CollectTest.lean:85–96,147–176`). The scan flattening arms are byte-unchanged in the committed diff.

## Section 5 case × class checklist

Paths below are relative to `leanncd/test/`; `Native` = `Eval/Plan/B5NativeTest.lean`, `Box` = `Eval/Plan/B5bBoxTest.lean`. “Checked” means source/fixture inspection, not a build executed by this reviewer.

| Required case | Checked evidence and outcome |
| --- | --- |
| Boxed short bare assign | `Native:177`, `bareMismatch`: all three native bitwise value guards include a real-zero hole. Only scatter scratches change their inference view. |
| Boxed wider bare assign | `Box:65–67`, `bareExceeds`: reference, checked f64 and checked f32 assert writer 2, dimension 0, box 4, actual 5. |
| Boxed short scatter | `Box:53–55`, `concat`: all three native paths must succeed; the boxed-only inference view prevents the collector's bare read conflict. |
| Boxed wider scatter | `Box:61–63`, `concatExceeds`: all three paths assert writer 2, dimension 0, box 3, actual 4. Fit runs before scratch execution/plan allocation. |
| Inferred-size exact short bare | `Native:179–183`, `bareExact`: reference and checked f64 retain `writerExtentMismatch "S" 2 0 4 3`. No boxed scratch names are produced. |
| Exact short scatter | `Box:57–59`, `concatExact`: all three paths retain `writerExtentMismatch "S" 1 0 4 2`, rather than becoming accepted or unsized. |
| Partially pinned multi-dimensional | `Box:37,78–79`, `lateExact`: an unpinned later axis makes the entire group exact; reference and checked f64 retain writer 3, dimension 1, expected 3, actual 2. |
| Boxed later dimension fits | `Box:74–77`, `lateMismatch`: reference and checked f64 assert the full 12-cell result. Later-dimension exceeds neighbor at `Box:80–81` asserts box 3, actual 4. |
| Tropical max/min holes | `Box:69–71`, `tropBox`/`tropMinBox`: reference f64 and both checked storage kinds compare bits including the trailing `-inf`/`+inf` hole. |
| Writer reversal | `Box:53–54` and `Native:171–172,193–198`; classification is declaration-only, collector basis is unchanged, and scratch ordinals match retained obligations. |
| Negative writer fitting a box reaches B6 | `Box:84–89`: reference range error names private `S#2`; checked f32 reports the expected invalid-plan range error. Zero coefficient remains covered by `Native:250–268`; empty source remains accepted at `Native:174`. |
| Undeclared fallback / all-bare / single writer / scan-local | `Collect.lean:109–120,144–175,198–199` preserves basis selection, UID agreement and single-writer early return. Existing `Native` undeclared mixed reversal and `inferredBasis:330`, `CollectTest` identity/UID guards, and scan-local fixtures were inspected. Both scan-local inference arms are unchanged. |
| Non-boxed or non-plain inference identity | `CollectorShape.lean:31–40` returns no scratch names for exact groups and returns every non-scatter `Stmt` unchanged. The two orchestration sites invoke it only in `.plain`; scans retain their own pre-existing conversion. Exact twins would detect a broadened exemption. M07's static manifest replacement matches this boundary; its execution was not rerun here. |
| Boxed non-scatter scratch | `bareMismatch` remains an ordinary assignment in the sizing view; `sizingView` cannot rewrite it. |
| Route valid boxed group | `Native:206`, `interleave`: unchanged route gate refuses every `needsB5` group with `routeUnsupportedMultiWriter`. |
| Actual-image-only fit (M4) | Owner-accepted exclusion, not a defect: all fit and scratch shape calculations still use `LHSSlot.outExtent`; no actual-image widening was attempted. |

## Findings and adjudication

**Correctness findings: 0.** No within-plan fix or adjudication is required by this lens.

### Optional coverage gaps — not findings or merge blockers

- The later-dimension acceptance/exact/exceeds checks are reference/checked f64 only; the old checked-f32 mismatch guard was removed without an equivalent f32 later-dimension assertion. `bareExact` likewise has no direct checked-f32 guard, although the scatter exact twin does. Optional within-plan strengthening would add matching f32 assertions using the existing helpers; shared production paths were inspected and no divergence was found.
- `agree` compares result data bits, not `DenseTensor.shape`. Direct box-shape assertions, especially `[4, 3]` on `lateMismatch`, would strengthen shape-focused regression coverage. The inspected compiler/evaluator construct output shape from the unchanged collector basis, so this is not evidence of wrong output shape.

### Accepted exclusions / scope

Single-writer declaration asymmetry, M4 actual-image fit, inferred-size boxes, route/JAX widening, predicate/multi-axis/constant scatter and F3 were not reopened. No unrelated issue requiring a parked dispatch was identified.

## Limitations and completion

- This was a static whole-committed-diff review with immediate call-chain, sibling and fixture inspection. No builds, mutation tests, dependency changes or source changes were run; the controller owns the concurrent full-build/verification results. Fixture presence is not asserted here as an independently observed green build.
- Oracle changes were read for whole-branch scope, but oracle independence was intentionally left to the separate fresh reviewer. The other review file and controller conclusions were not consulted.
- The only file written by this reviewer is this report; no commits or nested agents.
- Budget: completed below 60 review turns, with no known context-budget breach (250k ceiling); peak token usage was not separately instrumented.
- **Final verdict: clean. Findings count: 0. All section 5 cases and named unchanged siblings checked, with the optional precision/shape coverage limitations above.**
