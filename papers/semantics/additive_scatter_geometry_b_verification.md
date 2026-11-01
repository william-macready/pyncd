# Scatter geometry slice B: authoring verification

Every check run by the plan-write dispatch, with its result. Prototype worktree
`/Users/williammacready/code/python/pyncd/.claude/worktrees/proto-scatter-geometry-b`, branch
`worktree-proto-scatter-geometry-b`. Base `759bbf56a9be779b26dfc675405cb62794b17ad7`. T1-T4 tip `08ff6ba5`.
T5 is two commits on top: `37ea96fa` (docs) and `2ad72b7c` (one added comment line so the guard line numbers
named by manifest `expect` strings do not move; `git commit --amend` is blocked by a session guard, so it is a
second commit; the T5 patch is `git diff 08ff6ba5 2ad72b7c`).

## T5 build

After the docs edits, `bash lake-build.sh <proto>/leanncd LeanNCD Tests JaxExperiment`:
`Build completed successfully (8844 jobs)` (run twice: once at `37ea96fa`, once at `2ad72b7c`).

## Replay onto the base

Method: in the proto worktree `git checkout --detach 759bbf56`, for each of T1..T5 in order
`git apply --check <patch>` then `git apply <patch>` (all ten commands printed nothing, exit 0), then
`git hash-object` over the 26 paths changed by the five patches against `git ls-tree 37ea96fa` (the first T5
version). Result: all 26 blobs EQUAL. Because T5 was then regenerated for `2ad72b7c`, the T5 patch was replayed
again on `08ff6ba5` (`git checkout --detach 08ff6ba5`, `git apply --check`, `git apply`), and `git hash-object`
of its 13 paths against `2ad72b7c` was EQUAL for all 13 (including `SourceDifferentialScatterTest.lean`
`6d6468dfeef3216809ba2e714e1985480b0cd10c`), and `git diff 2ad72b7c --stat -- leanncd` was empty.
`ScatterSurfaceTest.lean` is a new file (untracked after `git apply`); it was verified by `hash-object`
(`d08659f6bd237928789b8292bb4693dfb9649147`), as `git diff` does not show untracked files. After each replay
`git checkout -f worktree-proto-scatter-geometry-b` and `git status --short` printed nothing (clean). T1+T2 and
T3 alone were not rebuilt separately: their intermediate states were not hash-checked individually, only the
cumulative post-T4 and post-T5 states (the plan's hash table says so).

Patch blobs on `main` (`git hash-object`): `T1-engine.patch` `0264270c1065d3469d0ad036c07e62419a4d5362`,
`T2-engine-fixtures.patch` `9f1a2da8292977950f7cd78eea389c943473162f`, `T3-surface.patch`
`260faaa6adabd0cb84accb82ac8ecf115015a6f3`, `T4-surface-fixtures.patch`
`60747c3fd9dfd34f92ec5216bab070b5635e3048`, `T5-docs.patch` `5a5c3b4174f671632667e6731f296999878798dc`
(the final export, `git diff 08ff6ba5 2ad72b7c`).

## Manifest

`bash <proto>/leanncd/scripts/mutation-manifest.sh --check <proto>/leanncd
papers/semantics/additive_scatter_geometry_b_mutations_post.json` (run in the proto tree at the tip, after
T5's first commit and again at the final tip `2ad72b7c`): `manifest OK: 17 entries, 17 selected, every
old-string unique`. The manifest was NOT
modified: the T3 labels already carry the final surface task id, and the engine labels `SGB-T1-*` are shared by
T1 and T2 by design. The REAL run (not `--check`) was done by the prototype dispatches (17/17 PASS on the T4
tip, tree clean afterwards) and was NOT repeated by this dispatch. Not re-run: T5 changes only comments and
docs, and its one line-count-sensitive file is kept line-stable by construction. Verified: the lines the
manifest's `SGB-T1-04` and `-05` expects name (`conditionCount fI2` and `conditionCount fFbig` guards in
`SourceDifferentialScatterTest.lean`) are still at lines 185 and 181 after T5.

## Greps (counts)

Run in the proto worktree at the T5 tip:

- `rg -n "boundedScatter|isConstUnit|constUnitPrefix|checkReservedAxisNames|reservedAxisName" leanncd --glob "*.lean" --glob "*.md" --glob "!docs/superpowers/**" --glob "!.lake"`:
  3 hits, all comments in `leanncd/test/Eval/Plan/ScatterGeometryTest.lean` saying the names are deleted or
  reversed. Before T5 the live-claim hits were in `DSL/AGENTS.md` (2) and `Semantics`/`Plan` rows.
- `rg -n "slice B|Slice B" leanncd/LeanNCD`: 10 hits in 8 files, all past tense after T5 (before T5:
  `Eval/Plan/Error.lean`, `Eval/Plan/AGENTS.md` x2, `Semantics/AGENTS.md`, `DSL/AGENTS.md` carried future
  tense; the test hits are the slice's own comments).
- `rg -n "multiWriterScatter|multiAxisScatterLhs|scatterOrAffineLhs"` over `leanncd` non-test: the remaining
  prose hits (`Eval/Plan/AGENTS.md`, `Semantics/AGENTS.md`, `Error.lean`, `Compile.lean`, `Uid.lean`,
  `Lowering.lean`) were each read; `Uid.lean` and the `DSL/AGENTS.md` Collect row were the stale ones.
- `rg -n "222|195/88"` over `leanncd` `*.md`: one stale hit (`Semantics/AGENTS.md`), fixed by T5 to
  `281/186/38` and the adjacent `81` to `99`. `rg -n "seventeen|== 17|== 11"` confirmed the hand-row counts
  (17 rows, 11 accepts) are unchanged in `OracleSortRulesTest.lean`.
- `rg -n "EC9|KG-reshape"` over `leanncd`: 8 hits in `docs/test_portfolio.md`, `EdgeCaseTest.lean`,
  `KnownGapTest.lean` said a multi-axis slot does not parse; fixed by T5.
- `papers/semantics/*.md` excluding records, reviews, plans and designs of landed slices: value-grep of
  `multiWriterScatter|multiAxisScatterLhs|boundedScatter|isConstUnit|reservedAxisName|slice B`: 21 files hit
  (mostly dated artifacts and ledgers); the three narrative notes with a present-tense rejection claim are
  parked (plan record), not edited.
- `rg -n "^\+.*[A-Za-z]+\.lean:[0-9]+" papers/semantics/additive_scatter_geometry_b_patches`: no matches (exit 1).
  The same pattern over the plan and the record: no matches.
- Code fences in the plan: none (`rg -c "\x60\x60\x60"` exit 1), so there is no Lean block to compile.
- Callers re-grepped for the section 5 audit: `collectable` (Ast definition; `Collect.lean` x2, doc comments),
  `scatterAffineClass` (Ast definition, `Eval/Plan/Compile.lean`), `slotsBecomeScatter` (Ast, `Structural.lean`,
  `RouteFragments.lean`, `Eval/Plan/Compile.lean`, `Collect.lean` x3, doc comments), `checkScanScatterLHSSlot`
  (`Eval/Plan/Compile.lean`), `declaredShapeWins`, `derivedShape`, `nonBareWrite`, `detectConditions`
  (`Differential.lean`; `nonBareWrite` also in `Observation.lean`), `outExtent` (`CollectorShape.lean` calls it at
  two sites), test `bounded`, `singleBoxed`, `predictedExtent`. Read in place: `collectable`, `boxedSingleGroups`,
  `checkWriterGroup`, `declaredShapeWins`, `bounded`, `singleBoxed`, `predictedExtent` (confirmed: multi-axis falls to
  the `legacy` sum rule), `checkScatterAffineExpr`, `checkScanScatterLHSSlot`.
- Fixture/identifier existence (`rg -o "def X"` in `leanncd/test`): `twoAxes`, `explicitConstant`, `predicateDest`,
  `multiAxisOne`, `constOne`, `convTwo`, `convBoxed`, `rawInGroup`, `convProg`, `convSurf`, `biasSurf`, `f1Surf`,
  `constPinSurf`, `constLoneSurf`, `diagonal`, `zeroScale`, `identityOne`, `transposeOne`: all found. `ls`/`git ls-files`
  of the scripts and files the plan names (`prepare-worktree.sh`, `lake-build.sh`, `mutation-manifest.sh`,
  `CollectorShape.lean`, `CompileTest.lean`, `ScatterCompileTest.lean`, slice A record, ledger): all exist.
- The `AGENTS.md` injected Pitfalls section of `DSL/AGENTS.md` is 2562 characters after T5 (was 2472), under 3k.
  `Eval/Plan/AGENTS.md` Pitfalls untouched.

## Not run, and why

- A real mutation-manifest run (17 entries, hours of builds) on the T5 tip: not repeated; see above.
- A build of the T1+T2 and T3-only intermediate states: only the cumulative post-T4 and post-T5 states were
  built and hash-checked in this dispatch; the prototype dispatches built T1 (8843) and T1+T2 (8843) and T4 (8844).
- The rank-0 destination and zero-coefficient group probes: not attempted (Rule 14; they are parked and assigned
  to review lens 1).
- `token-report.py`: not run (the session id is the controller's).

## Authoring checklist (`.claude/skills/slice-plan/SKILL.md`)

| Item | Result |
| --- | --- |
| Every Lean block compiled via `check-snippet.sh` | N/A: the plan has no Lean code fences (identifiers only; the patches carry the code, which was built in full) |
| Blocks edited after verification re-verified | N/A, same reason; the T5 `.lean` edits (comments) were rebuilt in full twice (8844 jobs) |
| Every asserted fixture value observed from a real run | Met via the ledger (values written from arithmetic, then confirmed by the real run, none adjusted); plan section 3 restates only ledger values; no value was newly asserted here |
| Every regression/parity fixture mutation-tested, both observations recorded | Partly: 17 mutants, 17/17 killed (ledger), but only `SGB-T1-07` is killed by the new T2 fixtures; F1-F6 independent kill power is UNMEASURED and says so (plan section 7(a), section 2) |
| Index/locator/order/payload requirements: fixture distinguishes the readings | Met for the extent payloads (F1 `24` distinguishes sum from overwrite readings 4 and 10; F4 payloads name `writerExtentExceedsBox "S" 1 0 3 4` and `... 5 6`); there are no new check-order claims |
| Prose claims about code checked against the code, not asserted | Done: each claim in sections 2-5 was grepped or read (see Greps); two ledger claims were corrected (`zeroScale` is a group fixture; `#constUser` is a boxed single, not a group) |
| Every file path named verified with `ls` | Done (see Greps) |
| Inherited gap lists re-derived | Partly: the ledger's parked items were re-grepped for the ones this plan restates (predictedExtent, rank-0, docs); "other slice A parked nits" is explicitly NOT restated or re-derived |
| Capability boundary moved: value-grep for numbers that moved | Done: `222/195/88`, `81`, `known:extent`, "does not parse" rows; found 8 stale statements the ledger list missed (record, deviation 9) |
| No `File.lean:NNN` in shipped text | Met: patches, plan, record, this file (greps above) |
| Recurring-defect family: siblings named, case x class table is a deliverable, every S cell owned | Met in plan section 5; S cells are owned in section 2 or parked in section 5 with costs; two lens-1 observations are requested |
| Every required fixture names its donor | Partly: T2 donors named in plan T2 and in the test file; T4 donors (`convOf sumSlot`, F1) named; ParseProgramTest pins have no donor beyond the pre-change arms (U2) |
| Task boundaries pass the reviewer test, tiny additions merged | Met: six tasks (T6 added after review), each with its own risk row; T4 is the smallest (one new file) and is separate because it is the surface evidence |
| Risk entry states fixture and mutation-cycle count | Met (plan section 4 table) |
| Global Constraints exact values; "does NOT do" with owners | Met (plan section 2, section 7); job counts 8843 / 8844 are observed; T3-alone job count stated as not built |
| New subsystem discoverable | Met: `ScatterSurfaceTest` is in the `Tests` glob (lakefile row) and described in two `AGENTS.md` rows; no new subsystem otherwise |
| Briefs list symbols as `identifier @ file` with window-read instruction | Met (plan section 4, preamble in section 1) |
| `AGENTS.md` injected sections at most about 3k characters | Met for `DSL/AGENTS.md` (2562); the other two nodes' injected sections were not edited |
| Mutation cycles in `papers/<plan>_mutations*.json`, expects from observed failures, `--check` passes | Met: `manifest OK: 18 entries` (re-run by the controller against the T6 tip after adding `SGB-T6-01`); T3 expects are file prefixes (weak, stated) |
| Close-out and authoring records in `_record.md`, live plan at most about 800 lines | Met: plan 517 lines after the review fixes (was 468) |
| Documentation-sweep steps written as commands | Met (T5 section) |
| Task expected over about 60 turns marked for a two-dispatch split | N/A as a patch: T1 is applied, not authored; the prototype breach is recorded |
| Authoring ran as two dispatches, code ships as patches that apply in order | Met: prototype (two dispatches) plus this write-up; replay verified |
| Reviewer and fixer briefs give window sizes; reviewers append findings; one fix dispatch per group | Met in plan section 6 and section 1 (reviewers write to named files); the fix-per-group rule is stated by the skill, not repeated |

## Review-time and T6 checks (2026-11-01, controller unless noted)

| Check | Result |
| --- | --- |
| Authoring-time review, two lenses | `additive_scatter_geometry_b_review_siblings.md` (0 P1, 1 P2, 2 P3) and `additive_scatter_geometry_b_review_surface.md` (0 P1, 0 P2, 5 P3); adjudication in the record |
| Lens 2 recomputed the plan's 32 blob rows at the T4 and T5 tips | all matched (lens report; the controller did not repeat it) |
| T6 tip identity | proto branch tip `8b8eaabe4ea8080cb4679748b1931cac726cbcbe`, worktree clean (controller `git status`) |
| T6 post-state blobs, controller `git rev-parse 8b8eaabe:<path>` | the four hashes in plan section 7 match the fixer's list exactly |
| T6 patch file | 108 lines, `diff --git` headers for exactly the four paths; blob `bbfd3509b118a5b537263dff29e76f30f5ea8d93` (`git hash-object`) |
| T6 replay onto `2ad72b7c` | done by the fixer (detached checkout, `git apply`, four blob matches, branch restored, clean); NOT repeated by the controller, and T1-T6 were not replayed in one run from the base after T6 was added (T1-T5 were, by the write-up dispatch; T1-T4 by the controller) |
| Full build `LeanNCD Tests JaxExperiment` | controller: 8844 jobs green at `2ad72b7c` and again at `8b8eaabe` |
| Manifest `--check` with `SGB-T6-01` added | controller: `manifest OK: 18 entries, 18 selected, every old-string unique` against the T6 tip |
| `SGB-T6-01` real run | fixer only (one-entry manifest): PASS, killed by `Eval.Plan.ScatterSurfaceTest` with only the four `r1Surf` guards failing; the controller did not repeat it |
| 17-entry real run after T5 and T6 | NOT repeated (observed 17/17 on the T4 tip by the prototype agents) |
| `r1Surf`/`r2Surf` exercise only native legs | confirmed by grep: no oracle or `conditionCount` use; the oracle's D5 agreement for the identity-slot row is therefore not pinned (stated in plan section 5) |
| plan has no code fences and no `File.lean:NNN` after the edits | controller grep: no hit (checked after the last edit) |
