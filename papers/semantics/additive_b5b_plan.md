# B5b declared containing box: implementation plan

**Status: execution-ready package; execution not yet started.** Owner approval of the design
([additive_b5b_containing_box_design.md](additive_b5b_containing_box_design.md)) was given on
2026-10-28: M1 (a pinned declared box only), leave the single-writer declaration asymmetry alone,
accept the M4 slack. Execution is a separate step; this file does not start it. The patches were
generated against `2ce6365c` (`leanncd/` identical to the pushed `342106e4`) and apply to any
descendant of it that has not touched the 13 files in section 7; the commit that adds this package
changes only `papers/semantics/`.
**Process: Full, light.** New accepted programs and a restated independent predictor, but no new
carrier, kernel, backend or plan IR. One slice, three tasks, all code authored and verified in a
prototype worktree and shipped as patches; the executor replays and verifies, it does not design.
Authoring evidence is in section 9. Execution record goes to `additive_b5b_record.md` (created by
the executor, section 8).

**Goal:** a destination declared with every axis pinned by `axis … = n` accepts multi-writer
groups whose writers each fit inside it (concatenation, shorter bare writers, holes), under real,
max-plus and min-plus, on the reference and both checked native paths; every other group keeps
B5's exact equality.

**Architecture:** relax `checkCollectorShapes` from equality to fit for boxed groups only; present a
boxed group's scatter scratches to size inference as assignments (the scan-local precedent) so the
collector's padded read of a short scratch cannot raise the scatter-output `sizeConflict`;
restate the rule independently in the oracle predictor. No change to `ScatterPlan`,
`checkScatterCore`, dense kernels, algebra tables, `route`, JAX or B6.

**Tech stack:** Lean 4 (`leanncd/`), shell scripts in `leanncd/scripts/`.

**Spec:** the design note above (sections 3-4 are the rule; section 5 the risks).

## 1. Execution contract

Open every implementation, review and fix brief with this preamble (resolve `<worktree>` first):

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use a file viewer for windows and `rg -n` for search.
> Stage files by explicit path; never commit `.claude/settings.json`. Stay within the stated turn
> and context budget and say so in the report if you breach it.

- **Worktree.** Create a new linked worktree from local `main` (for example
  `git worktree add <repo>/.claude/worktrees/b5b-exec -b b5b-exec main`), then run
  `bash <worktree>/.claude/skills/new-slice/prepare-worktree.sh` from inside it. It fast-forwards to
  local `main` and syncs the Mathlib cache; it must report Mathlib at 100% (a cold Mathlib build
  takes hours; stop if it starts one). Then build `LeanNCD` once to refresh project oleans.
- **Do not push.** Local `main` stays ahead of `origin/main`; say so in the final report.
- **Patches are the code.** Apply `additive_b5b_patches/T1-box-rule.patch`, `T2-oracle.patch`,
  `T3-docs.patch` in order, each after `git apply --check`. Do not retype Lean from this document;
  this plan has no Lean code fences on purpose. If a patch does not apply, or a post-apply hash
  (section 7) differs, stop and report BLOCKED with the output. Do not repair a patch by hand.
- **Budget.** At most three substantive work items per dispatch, 60 turns, 250k peak context. Run
  builds in the background and wait for the completion notice; do not poll them. Report measured
  usage and any breach. No nested delegation.
- **No relaxing to get green.** A fixture that fails is a finding, not something to loosen.

## 2. Fixed semantics and exclusions

1. **Box.** A bounded B5 group is *boxed* iff its destination has a tensor declaration
   (`Decl.tensorAxes?`) and every declared axis UID is in `declaredAxisSizes sched.decls` (pinned by
   `axis … = n`, or `iter … = n`). Anything else (declared with an inferred size, partially pinned,
   undeclared) is *exact*.
2. **Fit.** In a boxed group, for writer `k` (1-based) and dimension `d` (0-based), the realized
   extent (`LHSSlot.outExtent` over inferred sizes: assign = slot sizes, scatter = derived extent)
   must be `<=` the basis extent. Failure: `ShapeError.writerExtentExceedsBox T k d box actual`,
   rendered `multi-writer T: writer k, dimension d: extent actual exceeds declared box extent box`.
3. **Exact.** Every non-boxed group keeps B5's rule and constructor unchanged
   (`writerExtentMismatch T k d expected actual`).
4. **Collector and results.** Unchanged. Short scratches pad with the agreed sort's `0_K` through the
   collector's out-of-range read; the published `T` has the box shape.
5. **Inference exemption.** For a boxed group, scatter scratches `T#1 .. T#n` are presented to size
   inference as assignments (`sizingView`), in both `evalScheduled` and `prepareEvalPlan` Step C.
   Their right-hand reads still size axes.
6. **Unchanged**: eligibility (`checkWriterGroup`, `needsB5`), basis selection, B6 range errors,
   votes and casts, scan conflicts, all-bare UID agreement, single-writer programs (including
   `scatterExtentOverridesDeclared`: a lone scatter's derived extent still beats its declaration),
   `route` (`routeUnsupportedMultiWriter`), JAX, predicate/constant/multi-axis scatter.
7. **Not done here** (owner decisions, each a later slice): reconciling the single-writer
   declaration asymmetry; fit by actual write image (M4: `S[2*i+2]`, `i = 2`, into `S(5)` is still
   refused because its derived extent is 6); boxes whose size is inferred; route/JAX execution.

## 3. Facts measured at authoring (do not restate without re-measuring)

Probes on `342106e4` (design note section 2) and the prototype results (section 9) establish:
smaller assign scratches already collect bit-identically on all three native legs; smaller scatter
scratches fail only through the B3 bare-read `sizeConflict`; after the change the concat program
`S[i] := A[i]; S[1*i + 2] := B[i]` into pinned `S(4)` gives `[-5, -2, -7, -3]` on the reference,
checked f64 and checked f32 (inputs `A = [-5, -2]`, `B = [-7, -3]`).

## 4. Tasks

### T1: box rule, sizing view, native fixtures (atomic production + fixtures)

**Files** (all created/changed by `T1-box-rule.patch`):
`leanncd/LeanNCD/DSL/Pipeline/Collect.lean`, `.../ScheduledValidation.lean`,
`leanncd/LeanNCD/Eval/CollectorShape.lean`, `.../Error.lean`, `.../Eval.lean`,
`leanncd/LeanNCD/Eval/Plan/Compile.lean`, `leanncd/lakefile.toml` (one glob entry),
`leanncd/test/Eval/Plan/B5NativeTest.lean`, `.../B5BoundaryTest.lean`, new `.../B5bBoxTest.lean`.

**Symbols** (use `rg -n`, window 40-60 lines): `CollectorShapeObligation` (new field `boxed`),
`collectorShapeObligations` (new `pinned` argument) @ `Collect.lean`; `validateScheduled` @
`ScheduledValidation.lean` (passes `declaredAxisSizes sched.decls`); `checkCollectorShapes`,
`boxedScratchNames`, `sizingView` @ `CollectorShape.lean`; `ShapeError.writerExtentExceedsBox` and its
render arm @ `Error.lean`; `evalScheduled` @ `Eval.lean` and `prepareEvalPlan` Step C @ `Compile.lean`
(the `padded` binding and `sizingView padded s` in the statement flattening).

- [ ] **Step 1:** `git apply --check` then `git apply` `T1-box-rule.patch`.
- [ ] **Step 2:** confirm the hashes of the ten T1 files (section 7).
- [ ] **Step 3:** build in the background:
  `lake-build.sh <worktree>/leanncd Eval.Plan.B5NativeTest Eval.Plan.B5BoundaryTest Eval.Plan.B5bBoxTest DSL.Pipeline.CollectTest Eval.CollectEvalTest Eval.Plan.CollectPlanTest`.
  Expected: `Build completed successfully` and no `error:` line.
- [ ] **Step 4:** stage the ten paths explicitly and commit
  `feat(eval): B5b declared containing box for multi-writer scatter`.

**Flipped pins (expected, all inside the patch).** Each is a program the old equality rule refused
and the box accepts, with its old payload kept as an exact twin:
`bareMismatch` (pinned `k = 4`, bare writer over `j = 3`: values `[5, 20, 28, 0]`; twin `bareExact`
keeps `writerExtentMismatch "S" 2 0 4 3`), `declaredMismatch` (pinned `k = 5`, scatter extent 4:
`[-5, -7, -2, -3, 0]`), `lateMismatch` (writer 3 dimension 1: 2 fits 3; twin `lateExact`),
`negativeWriter` (now reaches B6 instead of a shape error).

**Fixtures (donor in parentheses) and mutation cost.** `B5bBoxTest` holds 22 guards over these families:
`concat` (donor `interleave`), `concatExact`, `concatExceeds`, reversed writers, `tropBox` /
`tropMinBox` (donors `tropical` / `tropMin`), `bareExceeds` (donor `bareMismatch`), `lateExact`,
`lateExceeds` (donor `lateMismatch`), the `negativeWriter` B6 pins (reference and plan). Ten mutants
(M01-M10) cover T1; `B5NativeTest` (33 guards after the patch) carries the flipped pins and the exact twin `bareExact`.

### T2: independent predictor and oracle rows

**Files** (`T2-oracle.patch`): `leanncd/test/Semantics/OracleSortRules.lean`,
`.../OracleSortRulesTest.lean`, `.../OracleMixedRefusalTest.lean`.

**Symbols**: `pinnedBox` (new, private), `predictShaped`, `productionShapedVerdict`, `agreesShaped`
@ `OracleSortRules.lean`; `box12Decls`, `stagedRows`, the C1 histogram guard @ `OracleSortRulesTest.lean`;
`mkBox`, `overlapBox`, `valueParity` @ `OracleMixedRefusalTest.lean`.

`pinnedBox` must restate "declared and every axis pinned" **from the declarations**, not call
production's `declaredAxisSizes`/`collectorShapeObligations`; keep it that way in review.

- [ ] **Step 1:** apply `T2-oracle.patch` (check first). **Step 2:** confirm hashes (section 7).
- [ ] **Step 3:** build `Semantics.OracleSortRulesTest Semantics.OracleMixedRefusalTest` (background).
- [ ] **Step 4:** commit `test(oracle): independent B5b box prediction and four-leg box rows`.

Observed values the patch pins: C1 histogram `[("writerExtentExceedsBox", 81)]` (C1 declares extent 4
against realized 8, so no corpus row becomes accepted; the 81 only change their refusal name);
eleven staged hand rows, seven predicted accepts (`stagedRows.length == 11`); box-extent-10 overlap
rows have actual `fourLegParity` with values `[8,0,20,0,51,0,118,0,0,0]` (real),
`[20,-inf,7,-inf,17,-inf,40,-inf,-inf,-inf]` (max), `[-5,inf,2,inf,3,inf,25,inf,inf,inf]` (min).
Three mutants (M11-M13) cover T2.

### T3: documentation (value-grep sweep, commands not prose)

**Files** (`T3-docs.patch`): the five `AGENTS.md` nodes (`leanncd/AGENTS.md`, `DSL/`, `Eval/`,
`Eval/Plan/`, `Semantics/`), `papers/backend_missing_functionality.md`,
`papers/semantics/additive_b5_record.md` (supersession banner),
`papers/semantics/additive_production_decision_note.md`,
`papers/semantics/additive_b5b_containing_box_design.md` (status line).

- [ ] **Step 1:** apply the patch (check first), then run the sweep and record counts in the record:
  `rg -n "writerExtentMismatch|exact extent equality|extent equality|containing box|sizeConflict" leanncd papers/backend_missing_functionality.md papers/semantics --glob '!additive_b5b_*' --glob '!*.json' --glob '!additive_b5_patches/**'`
  Every hit must be either history (B5 plan/record/design text carrying the supersession banner) or
  already describing the box rule. Value-grep the numbers that moved: `rg -n "81|nine hand|five accepts" leanncd/LeanNCD/Semantics/AGENTS.md papers/semantics/additive_b5_record.md`
  (the B5 record keeps its historical 81/nine/five as history; the live `Semantics/AGENTS.md` must say
  eleven hand rows, seven accepts, four refusals, 81 `writerExtentExceedsBox`).
- [ ] **Step 2:** `git diff --check`; every relative link in the edited papers resolves (`ls` them).
- [ ] **Step 3:** commit `docs(semantics): B5b box rule in the live nodes and supersession banners`.

## 5. Recurring-defect audit (case x class)

The defect family: a shape or admission predicate stated in one place and silently ignored in a
sibling. Siblings a diff cannot show: `scatterOutputShapes` / `inferAxisSizesCore` (B3 positions),
`scatterOutShape` and `evalPlain`'s scatter arm (reference output shape), `scatterPlacementOrFail`
and plan scatter signatures (checked output shape), `writerGroupBasis`, the route gate, the oracle
`predictShaped`. None is changed except the two Step-C call sites and the obligation check.
`R` required, `F` forbidden, `S` silently ignored (each `S` is a candidate defect; the fixture closes it).

| Case | Required behaviour | Fixture | Class |
| --- | --- | --- | --- |
| boxed, bare assign short | accepted, hole `0_K` | `bareMismatch` | R |
| boxed, bare assign wider | `writerExtentExceedsBox` | `bareExceeds` | R |
| boxed, scatter short | accepted, no `sizeConflict` | `concat` | R |
| boxed, scatter wider | `writerExtentExceedsBox` | `concatExceeds` | R |
| exact (size inferred), bare short | old mismatch payload | `bareExact` | R |
| exact, scatter short | old mismatch payload (not an unsized error) | `concatExact` | R |
| partially pinned multi-dim | exact, not boxed | `lateExact` | R |
| boxed multi-dim, later dimension fits | accepted | `lateMismatch` | R |
| tropical max/min with holes | `-inf` / `+inf`, f32 bits | `tropBox`, `tropMinBox` | R |
| writer order reversed | same result | `reverseWriters concat` | R |
| negative-coefficient writer in a box | fits by derived extent, then B6 | `negativeWriter` | R |
| undeclared fallback basis, all-bare, single-writer, scan-local scatter | unchanged | existing B5/Collect tests, full `Tests` build | R |
| `sizingView` on a non-plain or non-boxed statement | identity | M07 (exact twin) | R |
| boxed, scratch of a writer that is not a scatter | no view change needed | `bareMismatch` | R |
| route on a valid boxed group | `routeUnsupportedMultiWriter` | existing `routeError interleave` | R |
| fit by actual write image | not offered (M4) | none, documented | S by decision |

The only `S` cell is the owner-accepted M4 slack; it must stay documented, not widened.

## 6. Review focus (inputs the spec implies and no task wanted to forget)

1. A box *larger* than every writer (holes) under max/min: pad identities, native f32 bits (`tropBox`).
2. A box size left to inference silently accepted: must stay the exact diagnostic (`concatExact`, `bareExact`, `lateExact`).
3. A short *scatter* scratch accepted only in boxed groups (M06, M07 separate "off" and "everywhere").
4. A writer past the box refused before any execution, with box, writer and dimension in the payload.
5. A negative or zero-coefficient writer that fits the box by derived extent still hits B6, not a quiet drop.

## 7. Verification gates and exact values

- Hashes after each patch (sha256 of the final file):
  `git hash-object <file>` of each file after the three patches (T1 files after T1, T2 after T2):

  | File | blob |
  | --- | --- |
  | `leanncd/LeanNCD/DSL/Pipeline/Collect.lean` | `50b81b773377d138599314c31d68ade776927bab` |
  | `leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean` | `cc8efc1849dfab11f5583e61ffccdb990cd7b1dc` |
  | `leanncd/LeanNCD/Eval/CollectorShape.lean` | `5ba6422c18943e1a25cb3cc9eed6b5f59d8472ed` |
  | `leanncd/LeanNCD/Eval/Error.lean` | `73460910d2d10301d2606cc6468a29db5108b6af` |
  | `leanncd/LeanNCD/Eval/Eval.lean` | `4a3589dda9fba385fc60f1ad6a1f1568ac00b272` |
  | `leanncd/LeanNCD/Eval/Plan/Compile.lean` | `5684743c98864986562b69a0aab123dfc27f5923` |
  | `leanncd/lakefile.toml` | `d6ccd66db9f46538666a2cea31fe26904c78eba8` |
  | `leanncd/test/Eval/Plan/B5BoundaryTest.lean` | `fd1ac0e229d24dac97e12eae07c33f2a62a6e8ea` |
  | `leanncd/test/Eval/Plan/B5NativeTest.lean` | `2d1261ef3d1519ee0f2eb55d6ff5b10bd0c658c6` |
  | `leanncd/test/Eval/Plan/B5bBoxTest.lean` | `39cc162f95a86c3d14157965ea0402d2011b0319` |
  | `leanncd/test/Semantics/OracleMixedRefusalTest.lean` | `3912d02a7ac668b9bd667d89d66ecea619572a9e` |
  | `leanncd/test/Semantics/OracleSortRules.lean` | `0d5d497926f29ca457a23c118f6979d2a7657520` |
  | `leanncd/test/Semantics/OracleSortRulesTest.lean` | `f17b78c744d22ecce3f1bc6410bb1d0c5308ce4f` |
- Targeted builds per task as above; then the controller's full build:
  `lake-build.sh <worktree>/leanncd Tests JaxExperiment` expects `Build completed successfully (8840 jobs)`
  (B5's was 8839; the one extra job is `B5bBoxTest`).
- Mutation manifest `papers/semantics/additive_b5b_mutations_post.json` (13 entries, M01-M13): run
  `mutation-manifest.sh --check <worktree>/leanncd <manifest>` first (expects `13 entries, 13
  selected, every old-string unique`), then the real run with `--out`; all 13 must PASS and the
  mutated file must be restored byte-identically each time. The manifest is a *post* manifest: it
  needs the patches applied. Expected `expect` strings are in the manifest and were observed.
  Observed at authoring (prototype, two runs: M02, M03, M05, M11-M13 in the first run, M01, M04,
  M06-M10 in a second after correcting their `expect` strings): 13 of 13 PASS, every mutated file
  restored byte-identically, every restored build green. Because `B5bBoxTest` imports
  `B5BoundaryTest`, which imports `B5NativeTest`, a mutant that breaks `B5NativeTest` hides
  `B5bBoxTest`; the manifest `expect` therefore names the module that fails first:

  | Mutant | Intended reason | First failing module |
  | --- | --- | --- |
  | M01 fit `<=` becomes `<` | writer exactly filling the box is refused | `B5NativeTest` |
  | M02 boxed groups keep equality | short writers in a box refused | `B5NativeTest` |
  | M03 fit check dropped | wider writers accepted | `B5bBoxTest` |
  | M04 any declaration is a box | inferred-size twins accepted | `B5NativeTest` |
  | M05 partially pinned counts as boxed | `lateExact` accepted | `B5bBoxTest` |
  | M06 no scratch exemption | short scatter scratch raises `sizeConflict` | `B5NativeTest` |
  | M07 exemption applies to exact groups | exact twin changes payload | `B5NativeTest` |
  | M08 reference ignores the exemption | reference leg conflicts | `B5NativeTest` |
  | M09 checked path ignores the exemption | checked legs conflict | `B5NativeTest` |
  | M10 no pinned sizes reach obligations | every group exact | `B5NativeTest` |
  | M11 predictor ignores boxes | hand SHAPED rows disagree | `OracleSortRulesTest` |
  | M12 predictor fit direction reversed | hand SHAPED rows disagree | `OracleSortRulesTest` |
  | M13 observation maps the box error to mismatch | hand SHAPED rows disagree | `OracleSortRulesTest` |

  If a mutant's verdict is FAIL (the build did not break, or broke elsewhere), do not edit the
  manifest: report it, since it means a patch or hash differs from the prototype.
- Two final review lenses, as separate contexts reading a committed snapshot, findings appended to
  a file as they go: (A) acceptance/shape: the section 5 table, the unchanged siblings, order
  independence, exact twins; (B) oracle independence: `pinnedBox` and the fit rule restated without
  production helpers, four-leg rows actually `fourLegParity`, no doctored predictor.
- Then merge locally per the `new-slice` finish sequence (`git merge --no-ff`, confirm
  `git diff --stat main <branch>` empty, remove the worktree, delete the branch). Do not push.

## 8. Close-out record (executor writes `papers/semantics/additive_b5b_record.md`)

Required fields, each from a real run: base and final commit hashes; per-task build results; the
sha256 table result; full build job count; mutation table (13 PASS lines and restore results);
review findings and adjudication; the section 3 values re-observed on the executed tree; measured
token usage (`python3 .claude/skills/slice-plan/token-report.py <session-id>` where available,
otherwise say it was not measured) against the target of about 25M for execution; every skipped
step, if any. Add the Task-N completion blockquote to the master plan docs only if a master plan
names B5b (grep first).

## 9. Authoring evidence

Prototype worktree `worktree-b5b-proto` on `2ce6365c`: T1, T2 and T3 committed; a full
`Tests JaxExperiment` build on the final committed tree is `Build completed successfully (8840
jobs)`, and the 13 mutants PASS (two runs, section 7). Values and the corrections made along the way
are in `additive_b5b_plan_record.md`. The patches were not replayed on a second clean checkout with a
build; the executor's apply check and hash table are that gate. Authoring token cost was not
measured. Decisions the author made without the owner (check them): the new constructor name
`writerExtentExceedsBox` (design left it to the builder); `sizingView` as the exemption mechanism
(precedent: scan-local scatters are shown to inference as assignments); a `boxed` flag on the
obligation, computed in `collectorShapeObligations` from a pinned-size map that `validateScheduled`
passes in (import-order reason: `declaredAxisSizes` lives in `Structural.lean`, which `Collect.lean`
does not import).
