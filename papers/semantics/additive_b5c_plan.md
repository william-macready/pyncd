# B5c: a pinned declaration decides the shape for every writer count: implementation plan

**Status: execution-ready package; execution not yet started.** Owner approval of the design
([additive_single_writer_box_design.md](additive_single_writer_box_design.md)) was given on
2026-10-29: the rule (a pinned declaration decides the published shape for every writer count),
D1-D3 as recommended, the go decision (D4) and the D5 refinement. The patches were generated
against `329a1e4a` and apply to any descendant of it that has not touched the 9 files in section 7;
the commits that add this package change only `papers/semantics/`.
**Process: Full, light.** Changed shapes for accepted programs, a retired differential condition and a
restated independent predictor, but no new carrier, kernel, backend or plan IR. One slice, three
tasks, all code authored and verified in a prototype worktree and shipped as patches; the executor
replays and verifies, it does not design. Authoring evidence is in section 9. The execution record
goes to `additive_b5c_record.md` (created by the executor, section 8).

**Goal:** a destination declared with every axis pinned by `axis … = n` publishes exactly that shape
whether it has one writer or several: writers must fit, and unwritten cells hold the sort's `0_K`.

**Architecture:** B5b already makes a boxed multi-writer group publish its declared shape through a
scratch-and-collector desugar. B5c feeds a boxed single non-identity writer into the same machinery
(`boxedSingleGroups`, reachable from `collectDefinitions` only), so the fit check, the padded read, the
sizing view and the diagnostics are reused unchanged. The oracle's single-writer
`scatterExtentOverridesDeclared` condition is retired for boxed writes, and the independent predictor
restates the rule.

**Tech stack:** Lean 4 (`leanncd/`), shell scripts in `leanncd/scripts/`.

**Spec:** the design note above (sections 2-5 are the rule, the mechanism and the measured blast radius).

## 1. Execution contract

Open every implementation, review and fix brief with this preamble (resolve `<worktree>` first):

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use a file viewer for windows and `rg -n` for search.
> Stage files by explicit path; never commit `.claude/settings.json`. Stay within the stated turn
> and context budget and say so in the report if you breach it.

- **Worktree.** Create a new linked worktree from local `main` (for example
  `git worktree add <repo>/.claude/worktrees/b5c-exec -b b5c-exec main`), then run
  `bash <worktree>/.claude/skills/new-slice/prepare-worktree.sh` from inside it. It must report
  Mathlib at 100% (a cold Mathlib build takes hours; stop if it starts one). Then build `LeanNCD` once
  to refresh project oleans.
- **Do not push.** Local `main` stays ahead of `origin/main`; say so in the final report.
- **Patches are the code.** Apply `additive_b5c_patches/T1-single-box.patch`, `T2-oracle.patch`,
  `T3-docs.patch` in order, each after `git apply --check`. Do not retype Lean from this document; this
  plan has no Lean code fences on purpose. If a patch does not apply, or a post-apply hash (section 7)
  differs, stop and report BLOCKED with the output. Do not repair a patch by hand.
- **Budget.** At most three substantive work items per dispatch, 60 turns, 250k peak context. Run
  builds in the background and wait for the completion notice; do not poll them. Report measured
  usage and any breach. No nested delegation.
- **No relaxing to get green.** A fixture that fails is a finding, not something to loosen.

## 2. Fixed semantics and exclusions

1. **Boxed.** A destination is boxed iff it has a tensor declaration whose every axis UID is in
   `declaredAxisSizes sched.decls` (pinned by `axis … = n` or `iter … = n`) and it is not a `predicate`
   (D1). Unpinned or undeclared destinations are not boxed and keep the derived shape.
2. **One-writer groups.** `boxedSingleGroups env pinned stmts` yields a name with exactly one plain
   writer when its destination is boxed and the writer is collected: an explicit scatter whose slots
   are all `LHSSlot.boundedScatter` (no constant or multi-axis slot, D2); or an assign whose slots are
   distinct free axes. **D5:** a writer is excluded if any declared axis UID occurs in its slot
   expressions (the `tensor Out(i)` + `Out[2*i]` idiom, where the declaration names the source axis).
   D5 also excludes the identity writer (`tensor S(i)` with `S[i]`) and a transposed write over the
   declared axes, so the design note's D3 (identity criterion) needs no clause of its own. **A rank-0
   (scalar) destination is never boxed**: it has nothing to pad, and the D5 test is vacuous for it
   (an earlier prototype that dropped the identity clauses as redundant collected scalar programs,
   which `DefaultF32Test` caught).
3. **Reuse.** A collected single writer takes the B5 path: `needsB5` is true for a one-writer group;
   the group's basis is the declared axes; the shape obligation carries `boxed`; fit failure is
   `writerExtentExceedsBox T 1 d box actual`; the scratch is `T#1`, read by the collector with a padded
   read. Nothing in `ScatterPlan`, `checkScatterCore`, the dense kernels or B6 changes.
4. **Entry points.** Only `collectDefinitions` (via `validateScheduled`) passes `pinned`, so `route` and
   the `Bridge/Agreement` proof are untouched: a single boxed writer still routes, and `route` still
   refuses groups of two or more writers.
5. **Oracle.** `declaredShapeWins` (Differential.lean) retires `scatterExtentOverridesDeclared` for a
   boxed single write; the predictor's `singleBoxed` restates the rule independently of production.
6. **Unchanged**: multi-writer behaviour, scan-local writers (top-level plain statements only),
   votes and casts, B6, unpinned destinations, all-bare UID agreement. (JAX codegen is not edited, but
   it is affected: see item 7.)
7. **JAX consequence (found in post-landing review, not in the original plan):** the experimental JAX
   codegen (`generateForward`) refuses a boxed single bare assign over a different axis, because its
   collector's padded read is not expressible (`labelExtentMismatch`), where it accepted the same
   program before B5c; it refuses loudly. Identity writers and unpinned destinations still
   generate (probed). Parked, see the record.
8. **Not done here**: fit by actual write image (M4: `Y[0*a + 5]` into a declared 6 is still refused
   because the scratch `Y#1` has derived extent 5), inferred-size boxes, route/JAX shapes, predicate
   (D1) and multi-axis/constant-slot (D2) single writers, F3.

## 3. Facts measured at authoring (do not restate without re-measuring)

Before any change (`b45deb9b`), three native legs agree: a single `S[2*i]` (`i = 2`, `A = [-5, -2]`)
publishes `[4]` for `S` declared with `k` = 8, 4, 3 or unpinned; a single bare `S[i]` into a pinned
`S(k = 4)` publishes `[2]`; a reader `R[k] := S[k]` over pinned `k = 8` after a single writer is
refused with `sizeConflict 8 vs 4`; two writers publish the declared shape. After the patches: the
same single writer into `k = 8` gives `[-5, 0, -2, 0, 0, 0, 0, 0]`, shape `[8]`; the reader gives
`R` shape `[8]`. The throwaway spike that sized the blast radius is in the design note section 5.

## 4. Tasks

### T1: boxed single writers and native fixtures (atomic)

**Files** (all changed by `T1-single-box.patch`): `leanncd/LeanNCD/DSL/Pipeline/Collect.lean`,
`.../ScheduledValidation.lean`, `leanncd/lakefile.toml` (one glob entry), new
`leanncd/test/Eval/Plan/B5cSingleBoxTest.lean`, `leanncd/test/Eval/Plan/DefaultF32Test.lean`.

**Symbols** (use `rg -n`, window 40-60 lines): `boxedSingleGroups` (new), `WriterGroup.needsB5`,
`collectorShapeObligations`, `desugarMultiWriters` (new `pinned` argument, default none) @
`Collect.lean`; `collectDefinitions` (new `pinned` argument) and `validateScheduled` (passes
`declaredAxisSizes sched.decls`) @ `ScheduledValidation.lean`.

- [ ] **Step 1:** `git apply --check` then `git apply` `T1-single-box.patch`.
- [ ] **Step 2:** confirm the five T1 hashes (section 7).
- [ ] **Step 3:** build in the background:
  `lake-build.sh <worktree>/leanncd Eval.Plan.B5cSingleBoxTest Eval.Plan.DefaultF32Test Eval.Plan.B5NativeTest Eval.Plan.B5BoundaryTest Eval.Plan.B5bBoxTest DSL.Pipeline.CollectTest Eval.CollectEvalTest Eval.Plan.CollectPlanTest`.
  Expected: `Build completed successfully` and no `error:` line. (`Semantics.SourceDifferentialScatterTest`
  fails until T2; do not build it yet.)
- [ ] **Step 4:** stage the five paths explicitly and commit `feat(dsl): B5c boxed single writers`.

**Migrated pin.** `DefaultF32Test`'s `scatter` corpus row compares a program with undeclared tensors
against the same program declared `f32`. It declared `Out(o)` with `axis o = 6` pinned, which is now a
box and so compiles differently from the undeclared variant. The patch changes the row to the D5 idiom
(`tensor f32 X(i), Out(i)`), which keeps the derived shape and the equivalence.

**Fixtures** in `B5cSingleBoxTest` (donors in parentheses): `one` (donor `B5bBoxTest.concat`, one
scatter writer, `k = 8`), `oneEqual`, `oneExceeds` (`k = 3`, the M4 slack refused), `oneInferred`,
`bareOne` / `bareOneTight` / `bareOneExceeds`, `idiom` (D5), `transposeOne` (D5 for assigns), `scalarOne` (rank 0), `identityOne`, `tropOne` (donor
`B5NativeTest.tropical`), `oneReader`, `predOne` (D1, reference leg), `multiAxisOne` / `constOne` (D2,
group-membership table only) and the `groupsOf` exclusion table over all of them plus `concat`.
Eight mutants (N01-N08) cover T1.

### T2: oracle: retired condition and independent single-writer prediction

**Files** (`T2-oracle.patch`): `leanncd/LeanNCD/Semantics/Source/Differential.lean`,
`leanncd/test/Semantics/OracleSortRules.lean`, `.../OracleSortRulesTest.lean`,
`.../SourceDifferentialScatterTest.lean`.

**Symbols**: `declaredShapeWins` (new, private) and `detectConditions` @ `Differential.lean`;
`singleBoxed` (new, private), `predictShaped` @ `OracleSortRules.lean`; `stagedRows`, the row-count
guards @ `OracleSortRulesTest.lean`; `fH9`, `fR` and their guards @ `SourceDifferentialScatterTest.lean`.

`singleBoxed` must restate "declared, pinned, not predicate, bounded slots, not identity, no declared
axis among the source axes" **from the declarations and the statement**, not call production's
`boxedSingleGroups` or `declaredAxisSizes`; keep it that way in review. The oracle cannot see whether an
axis was pinned (declared extents are taken as pinned); the SHAPED rows, which run production, are
where pinned-ness is observed.

- [ ] **Step 1:** apply `T2-oracle.patch` (check first). **Step 2:** confirm the four hashes (section 7).
- [ ] **Step 3:** build `Semantics.OracleSortRulesTest Semantics.SourceDifferentialScatterTest
  Semantics.OracleMixedRefusalTest` (background). **Step 4:** commit
  `test(oracle): B5c single-writer boxes in the predictor and the differential`.

Values the patch pins: `fH9` (`Y[2a]` declared 9, derived 8) is now `parity` with `conditionCount 0`
(published shape `[9]` on the oracle and both native legs); `fR` (`Y[0*a + 5]`, declared 6) stays
`nativeFailure` with `conditionCount 0`, now naming the scratch `Y#1`; staged SHAPED rows are 17, eleven
predicted accepts (`stagedRows.length == 17`), including four single-writer rows (iter box 12 accepted,
iter box 4 refused with `writerExtentExceedsBox`, box 12 accepted, the D5 idiom accepted). Three
mutants (N09-N11) cover T2.

### T3: documentation (value-grep sweep, commands not prose)

**Files** (`T3-docs.patch`): the four `AGENTS.md` nodes (`leanncd/AGENTS.md`, `DSL/`, `Eval/`,
`Semantics/`), `papers/backend_missing_functionality.md`,
`papers/semantics/additive_production_decision_note.md`,
`papers/semantics/additive_b5b_containing_box_design.md` (update banner).

- [ ] **Step 1:** apply (check first), then run the sweep and record counts in the record:
  `rg -n "scatterExtentOverridesDeclared|derived shape|derives the destination extent|writerExtentMismatch|single-writer" leanncd papers/backend_missing_functionality.md papers/semantics --glob '!additive_b5*' --glob '!*.json' --glob '!additive_single_writer_box_design.md'`
  Every hit must be history or already describe the B5c rule (the single-writer condition survives only
  for non-boxed writes). Value-grep the numbers that moved:
  `rg -n "thirteen hand rows|eight accepts|five shape refusals|seventeen hand rows" leanncd/LeanNCD/Semantics/AGENTS.md`
  (the live node must say seventeen, eleven, six).
- [ ] **Step 2:** `git diff --check`; every relative link in the edited papers resolves (`ls` them).
- [ ] **Step 3:** edit `papers/semantics/additive_single_writer_box_design.md` status line to "implemented,
  record `additive_b5c_record.md`" (this file is not in the patch because the patch base predates its
  later edits). Commit `docs(semantics): B5c box rule in the live nodes`.

## 5. Recurring-defect audit (case x class)

The defect family: a shape rule stated in one place and silently ignored in a sibling. Siblings a diff
cannot show: `writerGroups` (multi-writer groups), `checkWriterGroup` and the group-level geometry
refusals, `collectorShapeObligations`, the `route` gate (`writerGroups logical.stmts`, multi only),
`Bridge/Agreement`'s statement of `desugarMultiWriters`, the oracle's `pinnedBox` and `predictShaped`, and
the DefaultF32 corpus. `R` required, `F` forbidden, `S` silently ignored.

| Case | Required behaviour | Fixture | Class |
| --- | --- | --- | --- |
| single scatter, declared larger | published shape = declared, `0_K` holes, three legs | `one` | R |
| single scatter, declared equal | unchanged values | `oneEqual` | R |
| single scatter, declared smaller (writes would fit) | `writerExtentExceedsBox "S" 1 0 3 4` | `oneExceeds` | R |
| single scatter, unpinned declaration | derived shape | `oneInferred` | R |
| single bare assign over a different axis | padded / tight / refused by fit | `bareOne*` | R |
| D5 idiom (`Out(i)` + `Out[2*i]`) | derived shape, not collected | `idiom`, staged idiom row | R |
| D5 for a bare assign (transposed write over the declared axes) | derived shape `[3, 2]`, not collected | `transposeOne` | R |
| identity writer | not collected | `identityOne` | R |
| scalar (rank-0) destination | not collected, shape `[]` | `scalarOne`, the DefaultF32 scalar rows | R |
| tropical single writer | `-inf` holes, f32 bits | `tropOne` | R |
| reader of the declared axis | box-shaped `R` (was `sizeConflict`) | `oneReader` | R |
| predicate destination (D1) | derived shape (reference leg) | `predOne` | R |
| constant / multi-axis slot (D2) | not collected | `multiAxisOne`, `constOne` | R |
| two writers | stays in `writerGroups`, not collected twice | `groupsOf concat` | R |
| `route` of a single boxed writer | still routes | `routeError one` | R, weak (see below) |
| oracle `fH9` | parity, no condition | `fH9` | R |
| oracle `fR` | `nativeFailure`, scratch `Y#1` named | `fR` | R |
| SHAPED single-writer rows | predicted = observed | staged rows | R |
| route sees no singles | `desugarMultiWriters` default `pinned := {}` | none isolating | **S** |
| oracle D5 clause in `declaredShapeWins` | mirrors production | none isolating | **S** |
| predicate single writer on the checked legs | not exercised (the checked legs refuse a real input into a predicate for unrelated reasons) | reference leg only | **S** |

The three `S` cells are known limits, not new instances: the route guard (`routeError one == none`)
does not distinguish "route ignores singles" from "route accepts a collected single", the oracle's
D5 clause is unreachable through the differential (the oracle refuses the idiom first as
`writeOutOfRange`), and D1's checked-leg behaviour is unobserved. Do not widen any of them here.

## 6. Review focus

1. A pinned destination declared larger than the writer's derived extent (holes), including tropical (`one`, `tropOne`).
2. The upsample idiom keeps working: `Out(i)` with `Out[2*i]` must not be refused (`idiom`, the DefaultF32 row, the staged idiom row).
3. A declared extent smaller than the derived one is refused even when the writes would fit (`oneExceeds`, M4).
4. An unpinned or undeclared destination is untouched (`oneInferred`, the groups table).
5. `route` and the `Bridge/Agreement` proof are untouched (the builds, `routeError`).

## 7. Verification gates and exact values

- Hashes after each patch (Git blob IDs of the final file, as `git hash-object` prints them):

  | File | blob |
  | --- | --- |
  | `leanncd/LeanNCD/DSL/Pipeline/Collect.lean` | `37bc3daedbe192e677fd19b659045627eabaf9e8` |
  | `leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean` | `ff9b226cab484a3d38c07e209aa0ffe8a0406d71` |
  | `leanncd/lakefile.toml` | `daf11e8f1dd8f02050a98cbd70f413d5bb03fadc` |
  | `leanncd/test/Eval/Plan/B5cSingleBoxTest.lean` | `9e91221b91d5e5dafe61f475c6da93d0b9c565aa` |
  | `leanncd/test/Eval/Plan/DefaultF32Test.lean` | `f08770bf37dc1e173fec0c81f0a22c62958eca12` |
  | `leanncd/LeanNCD/Semantics/Source/Differential.lean` | `39f30eae9ca080eb245dc494ba68736e57e8bcb4` |
  | `leanncd/test/Semantics/OracleSortRules.lean` | `831a6fd18c08a9e17215dc3c153eedb1639914fa` |
  | `leanncd/test/Semantics/OracleSortRulesTest.lean` | `39856ef09fcc552b295cd7f3d209827dbbe8267f` |
  | `leanncd/test/Semantics/SourceDifferentialScatterTest.lean` | `96d55ce8fc622f0efd02eb0a8c58411684bbc261` |

- Targeted builds per task as above; then the controller's full build:
  `lake-build.sh <worktree>/leanncd Tests JaxExperiment` expects
  `Build completed successfully (8841 jobs)` (B5b's was 8840; the extra job is `B5cSingleBoxTest`).
- Mutation manifest `papers/semantics/additive_b5c_mutations_post.json` (11 entries, N01-N11): run
  `mutation-manifest.sh --check <worktree>/leanncd <manifest>` first (expects `11 entries, 11 selected,
  every old-string unique`), then the real run with `--out`; all 11 must PASS and the mutated file must be
  restored byte-identically each time. It is a *post* manifest: it needs the patches applied.
  Observed at authoring (prototype, final committed tree): **11 of 11 PASS**, every mutated file
  restored byte-identically, every restored build green. Every T1 mutant fails first in
  `B5cSingleBoxTest` (the `expect` string is that module's `error:` line); the T2 mutants fail in
  `SourceDifferentialScatterTest` and `OracleSortRulesTest` ("hand SHAPED disagreements"):

  | Mutant | Intended reason | First failing module |
  | --- | --- | --- |
  | N01 pinned test dropped | an unpinned destination is boxed | `B5cSingleBoxTest` |
  | N02 D5 dropped for scatters | the `Out(i)` idiom is collected | `B5cSingleBoxTest` |
  | N03 D5 dropped for assigns | the transposed write is collected | `B5cSingleBoxTest` |
  | N04 predicate destinations boxed | D1 broken | `B5cSingleBoxTest` |
  | N05 constant / multi-axis slots collected | D2 broken | `B5cSingleBoxTest` |
  | N06 one-writer group skips the B5 path | no fit check for a bare single writer | `B5cSingleBoxTest` |
  | N07 `collectDefinitions` gets no pinned sizes | no single writer is ever collected | `B5cSingleBoxTest` |
  | N08 rank-0 destination boxed | scalar programs collected | `B5cSingleBoxTest` |
  | N09 oracle always predicts the override condition | `fH9` back to `known:extent` | `SourceDifferentialScatterTest` |
  | N10 predictor ignores single-writer boxes | SHAPED single-writer rows disagree | `OracleSortRulesTest` |
  | N11 predictor drops D5 | the idiom row disagrees | `OracleSortRulesTest` |

  If a mutant's verdict is FAIL (the build did not break, or broke elsewhere), do not edit the
  manifest: report it, since it means a patch or hash differs from the prototype. Two prototype
  rounds are why the manifest has 11 entries: a first run left three mutants alive (two were
  identity-clause mutants that D5 made equivalent for non-empty axes, one a real fixture gap, the
  transposed assign); removing the identity clauses then failed `DefaultF32Test` on scalar programs
  (rank 0), which is why N08 and `scalarOne` exist.
- Two final review lenses, as separate contexts reading a committed snapshot, findings appended to a
  file as they go: (A) acceptance/shape: the section 5 table, the unchanged siblings (route, the group
  path, `Bridge/Agreement`'s statement), the D5/D1/D2 exclusions; (B) oracle independence: `singleBoxed`
  and `declaredShapeWins` restated without production helpers, the retired condition not hiding a real
  divergence (`fR`), the staged single-writer rows actually exercising production.
- Then merge locally per the `new-slice` finish sequence (`git merge --no-ff`, confirm
  `git diff --stat main <branch>` empty, remove the worktree, delete the branch). Do not push.

## 8. Close-out record (executor writes `papers/semantics/additive_b5c_record.md`)

Required fields, each from a real run: base and final commit hashes; per-task build results; the hash
table result; full build job count; mutation table (11 PASS lines and restore results); review findings
and adjudication; the section 3 values re-observed on the executed tree; measured token usage
(`python3 .claude/skills/slice-plan/token-report.py <session-id>` where available, otherwise say it was
not measured) against a target of about 30M for execution; every skipped step, if any.

## 9. Authoring evidence

Prototype worktree on `329a1e4a`: T1, T2 and T3 committed; a full `Tests JaxExperiment` build on the
committed tree is `Build completed successfully (8841 jobs)`, and the 11 mutants were run (section 7).
Two earlier spike builds (design note section 5) sized the blast radius before the rule was refined.
Values and corrections are in `additive_b5c_plan_record.md`. The patches were not replayed on a second
clean checkout with a build; the executor's apply check and hash table are that gate. Authoring token
cost was not measured. Decisions the author made without the owner (check them): the function name
`boxedSingleGroups`; `collectDefinitions` taking `pinned` with a default so `route` and the
`Bridge/Agreement` proof stay unchanged; the DefaultF32 corpus row migrated to the D5 idiom; the oracle's
`declaredShapeWins` treating declared extents as pinned.
