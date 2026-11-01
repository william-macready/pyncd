# Scatter geometry, slice B: groups, boxed writers and surface syntax for multi-axis and constant scatters: implementation plan

**Status: T1-T6 executed; verification and integration evidence is in
[the execution record](additive_scatter_geometry_b_record.md).** The design note
([additive_scatter_geometry_b_design.md](additive_scatter_geometry_b_design.md)) is BINDING: scope approved
2026-10-30, constant spelling `S[=3]` approved 2026-10-31. Its section 4 task list became T1-T5 below, and T6 (the pre-execution review fixes, section 9) was added on top. The
patches were generated against `759bbf56a9be779b26dfc675405cb62794b17ad7` (the design-note commit; local
`main` was `5cee18a3` when this package was authored, which only adds papers); the executor does not trust that sha: it re-checks `git apply --check` on whatever
local `main` is, and any descendant that has not touched the 26 paths of section 7 applies.

**Process: Full.** A new capability (two surface slot forms) on a soundness surface (what the collector admits
and which shape is published), six tasks, all code authored and replayed in a prototype worktree and shipped
as patches; the executor replays and verifies, it does not design.

**Goal.** A top-level scatter whose slot names two or more axes (`S[a + b] := ...`) or is a constant
(`S[=3] := ...`) can be written in `tl!{...}` surface syntax, can be one writer of a multi-writer group
(summed by the group's agreed sort), and a single such writer into a destination with every axis pinned
publishes the DECLARED shape, on the reference evaluator, the checked f64 and checked f32 backends and the
oracle alike.

**Anti-goals (non-negotiable, from the design note).** (1) No name-based or otherwise forgeable marker:
nothing may read an axis NAME (the slice A defect A2). (2) A lone numeral keeps meaning the scan base case
(`.iterAt`); never reinterpret it. (3) No second extent formula: every extent is `LHSSlot.outExtent`. Also
from the design note: no constant or multi-axis write silently skipped or clamped; the single-axis
stride-aligned extent is unchanged.

**Tech stack:** Lean 4 (`leanncd/`), shell scripts in `leanncd/scripts/`.

## 1. Execution contract

Open every implementation, review and fix brief with this preamble (resolve `<worktree>` first):

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use a file viewer for windows (40-60 lines, never a whole
> file over about 20k characters) and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and say so in the report
> if you breach it.

- **Worktree.** Create a new linked worktree from LOCAL `main` (not `origin/main`, which is stale):
  `git worktree add <repo>/.claude/worktrees/scatter-geometry-b-exec -b scatter-geometry-b-exec main`. Then run
  `bash .claude/skills/new-slice/prepare-worktree.sh` from inside it (a repo script; it syncs the built
  `.lake`). It must report Mathlib at 100%; if a build starts compiling Mathlib, stop (a cold build takes
  hours). Then build `LeanNCD` once to refresh project oleans.
- **Do not push.** Local `main` stays ahead of `origin/main`; say so in the final report.
- **Patches are the code.** Directory `papers/semantics/additive_scatter_geometry_b_patches/`: apply
  `T1-engine.patch`, `T2-engine-fixtures.patch`, `T3-surface.patch`, `T4-surface-fixtures.patch`,
  `T5-docs.patch`, `T6-review-fixes.patch` in that order, each after `git apply --check <absolute patch path>`
  run in the worktree root. One commit per patch: six commits. Stage by explicit path. Do not retype Lean from
  this document; it has no Lean code fences on purpose. **T1 must be applied as one patch, never reconstructed
  by hand:** the engine change forces 15 logically re-pinned guards (25 `#guard` lines changed in the patch;
  the prototype ledger counts the 15) across 7 test modules (section 3), and the prototype's first
  attempt to hand-edit them took about 152 tool calls.
- **BLOCKED rule.** A patch that does not apply, or a blob hash (section 7) that differs after the owning
  task, is BLOCKED: stop and report with the command output. Never repair a patch by hand and never loosen a
  fixture to get green; a failing fixture is a finding.
- **Builds.** Only `bash leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD Tests JaxExperiment` (or a
  module list a task names); run long builds in the background and wait for the completion notice. An
  `Ast.lean` edit (T1) recompiles about 8800 jobs, so T1 ends with the full build. After T1 alone the Lake
  graph SKIPS dependents of a failing module: a red `B5BoundaryTest` hides `ScatterGeometryTest`, so read the
  first error, not the last.
- **Mutation manifest.** `bash leanncd/scripts/mutation-manifest.sh --check <worktree>/leanncd
  <worktree>/papers/semantics/additive_scatter_geometry_b_mutations_post.json` unfiltered first (expect
  `manifest OK: 18 entries`), then, only after all six patches are applied, the REAL run (not only
  `--check`): `--task T1` (9 entries), `--task T3` (8 entries) and `--task T6` (1 entry), one at a time, each in the background with
  `--out <scratch file>`. Run `git status` after each; the tree must be clean.
- **Budget.** At most three substantive work items per dispatch, 60 turns, 250k peak context per dispatch;
  report measured usage and any breach. No nested delegation.
- **Tokens.** This executor is not Claude Code, so `.claude/skills/slice-plan/token-report.py` does not
  apply: record the total from the executor's own usage telemetry and name the method (section 8).
- **Review and merge.** After the two review lenses (section 6) and their adjudication, merge to local
  `main` per the `new-slice` finish sequence (`git merge --no-ff`, confirm `git diff --stat main <branch>`
  is empty, remove the worktree, delete the branch). Rule 13 of the repo `CLAUDE.md` authorizes this: no
  merge/PR menu. Do not push.

## 2. Fixed semantics and exclusions

Decisions, all BINDING (design note section 2):

- **B-D1 Admission.** Top-level groups and boxed single writers accept multi-axis and lowered-constant slots.
  The predicate is `LHSSlot.collectable` (`DSL/Ast.lean`, renamed from `boundedScatter`): `.free`/`.freeNorm`
  true; `.affine (.const _)` false BY CONSTRUCTOR; any other `.affine _` true; scan slots false. A RAW
  `.affine (.const _)` is only reachable through a hand-built schedule that skipped `lowerArith` (pinned by
  fixture F8 on `validateScheduled`).
- **B-D2 Marker deleted.** `constUnitPrefix`, `IdxExpr.isConstUnit` (`DSL/Ast.lean`),
  `checkReservedAxisNames` (`DSL/Pipeline/Structural.lean`, and its two uses in `DSL/Compile.lean`) and
  `CompileError.reservedAxisName` (`Exec/Uid.lean`) are gone. `lowerConstSlots` still spells the synthetic
  axis `"#const" ++ toString u`, for display only. A user axis spelled `#constUser` is now an ordinary axis
  (fixture F7 pins both compile chains).
- **B-D3 Shape change, intended.** A single constant or multi-axis writer into a destination declared with
  every axis pinned now publishes the DECLARED shape, PROVIDED no declared axis occurs among the writer's own
  source axes; a writer reaching past the box fails with `writerExtentExceedsBox`. The D5 idiom exclusion (a
  declared axis that is also one of the writer's source axes keeps the derived shape) is unchanged, and it
  fires for an IDENTITY slot too. Consequence, decided by the owner on 2026-11-01 (review finding L1-1: keep
  D5, document and pin): with `tensor S(k, b)`, `axis k = 8`, `axis b = 3`, ONE writer `S[=3, b] := B[b]`
  publishes `[4, 3]` (the `b` slot is an identity over declared `b`, so the derived shape stays), while TWO
  such writers (`S[=3, b]`, `S[=5, b]`) publish the declared `[8, 3]`. So for a writer with an identity slot
  over a declared axis the published shape depends on the writer count; this already held for single-axis
  writers (`S[2*a + 1, b]`) since B5c and is pinned by `r1Surf`/`r2Surf` in `ScatterSurfaceTest` (T6).
  Narrowing D5 to non-identity positions is parked (about 1 dispatch, Direct path, would re-pin corpus
  programs). Observed programs whose published shape moved (all other
  accepted programs unchanged; the full build is green with only the re-pins of section 3):
  `convBoxed` (`S[a+b]`, declared `k = 8`) `[6]` to `[8]`; `S3` pinned 8 (`S[3]`, both `.scatter` and
  `.assign` spellings) `[4]` to `[8]`; `SourceDifferentialScatterTest` `fI1`, `fI2`, `fMask`, `fFbig` derived
  shape to declared shape, class `known:extent` to `parity`. Programs now ACCEPTED that were refused: every
  group containing a multi-axis or constant writer (`twoAxes`, `explicitConstant`, `convTwo`, the `S3`
  pairs) and 59 more programs of the C1 oracle corpus (class counts `[222,195,88]` to `[281,186,38]` over the
  same 505 programs; shape-stage concrete C1 programs 81 to 99).
- **B-D4 Surface.** `a + b`, `n*a + m*b`, any number (at least two) of axis terms, each `ident` or
  `num * ident`, optional trailing numeral bias, elaborated to `.affine (.affine bias [(c, axis), ...])`;
  `S[=3]` elaborated to `.affine (.const 3)` (`S[= 3]` also parses). Existing single-axis arms keep their
  constructors byte-unchanged. Coefficients and biases are non-negative numerals. `S[a + b +1]` is a PARSE
  ERROR (`+1` is one token); the spaced `S[a + b + 1]` is the bias spelling. No parse ambiguity was observed
  (section 3).
- **B-D5 Scan-local stays refused.** A surface constant slot inside a scan statement fails with
  `compile CompileError.overlappingScatter "G"`; a surface multi-axis slot fails with
  `preflight CapabilityError.multiAxisScatterLhs "G: affine LHS slot"` (pinned in `ScatterSurfaceTest`; the
  hand-built `checkScanScatterLHSSlot` constant refusal stays pinned in `CompileTest`).
- **B-D6 Oracle.** `declaredShapeWins` (`Semantics/Source/Differential.lean`) is now exactly
  `!sourceUIDs.any destUIDs.contains` (the `bounded` filter deleted). A shared predicate with
  `boxedSingleGroups` did not fall out cheaply and is parked.

**Does NOT do** (each with its owner and estimated cost in dispatches; estimates, not measurements):

| Not done | Owner | Cost |
| --- | --- | --- |
| scan-local multi-axis or constant slots (reference and legacy overwrite there; checked refuses) | F3, a later slice | about 1 |
| predicate/bool destination groups (still `multiWriterScatter`) | unowned | not estimated |
| negative coefficients or biases in surface syntax | unowned | not estimated |
| `route` / JAX scatter capability for these forms (`routeUnsupportedMultiWriter` unchanged) | unowned | not estimated |
| validation of degenerate slots `a + a` (acts as `2*a`) and `0*a + b` (accepted, `a` becomes a collision axis) | parked | about 1 (Direct path, plus re-pin of the two U5 pins) |
| shared predicate between `boxedSingleGroups` and the oracle (`declaredShapeWins`, test-side `bounded`, `singleBoxed`) | parked | about 0.5 |
| test-side `OracleSortRules.predictedExtent` uses the legacy sum rule for a multi-axis slot (a+b over 4,3 gives 7, production gives 6); now reachable, unexercised by any corpus program | parked | about 0.3 |
| `declaredShapeWins` does not test `!declaredAxes.isEmpty` like production's `boxed`. OBSERVED by review lens 1 (2026-11-01): UNREACHABLE for a non-empty write, because a rank-0 destination with a scatter writer is refused at `compileToScheduled` (`rankMismatch "S" 0 1`) and by the source oracle's admission; so the vacuous-truth cell cannot disagree with production | closed as unreachable (no work) | 0 |
| narrow the D5 exclusion to declared axes used in a NON-identity position (review L1-1; changes B5c semantics, mirrored in `declaredShapeWins` and test-side `singleBoxed`) | owner chose "keep D5" on 2026-11-01; parked | about 1 (Direct path, may re-pin corpus programs) |
| `S[0*a + 0*b + 3]` (a slot with NO placing term) has extent 3 and every leg fails with a range error, while `S[=3]` has extent 4; in `tensor S(a)` the writer `S[0*a + b]` fires D5 through the zero-coefficient declared axis `a` (review L1-3, L2-3); documented in `DSL/AGENTS.md` by T6, not validated | parked (same row as degenerate-slot validation) | included in the 1 above |
| zero-coefficient multi-axis writers in a GROUP: OBSERVED by lens 1, two `S[0*a + b]` writers give `[20, 200, 2000]` unboxed and `[20, 200, 2000, 0, 0, 0, 0, 0]` boxed, reference and both checked legs bit-equal; no fixture pins it | parked | about 0.2 (one fixture) |
| `writerExtentExceedsBox` reports "multi-writer ... writer 1" for a single boxed writer (wording of the pre-existing message, review L2-4) | parked | about 0.1 |
| independent kill power of fixtures F1-F6 (the manifest cannot show it, section 7) | parked | about 1 |
| tighten the T3 manifest `expect` strings to line pins | parked | about 0.3 |
| the other slice A parked nits (record `additive_scatter_geometry_a_record.md`, "Parked scope") | slice A record | not restated here, not re-derived |

## 3. Facts measured at authoring (do not restate without re-measuring)

Source: prototype ledger `additive_scatter_geometry_b_files/proto_notes.md` (engine dispatch and surface
dispatch), prototype worktree branch `worktree-proto-scatter-geometry-b`, tip of T1-T4 `08ff6ba5`, T5 tip
`2ad72b7c`. Every fixture value below was first written from arithmetic and then CONFIRMED by a real run (the
guards pass; none was adjusted to fit).

- **Re-pinned guards (T1, P1 of the ledger), before to after.** Failing modules in dependency order:
  `StructuralTest` synthetic-axis name test removed (`u == u'` only); `B5BoundaryTest` `twoAxes`,
  `explicitConstant` refused `multiWriterScatter` to admitted; `SourceDifferentialScatterTest` `fI1`, `fI2`,
  `fMask [5,6]`, `tag fFbig` `known:extent` to `parity`, `conditionCount fFbig` 1 to 0;
  `OracleSortRulesTest` C1 class counts, `concreteC1.length` 81 to 99 and its histogram, the supplemental
  "explicit constant scatter groups" row now admitted (`.ok []`, `runs := [real, real]`), `multiWriterScatter`
  dropped from `strictC1Tags` (with a negative guard); `OracleMixedRefusalTest` rows whose `multiAxis` or
  `constant` group was the `multiWriterScatter` control are now accept neighbours (the false-`nativeFailure`
  rows deleted; the split-leg pair uses `castDirect` against `r16a`); `ScatterGeometryTest` `convTwo`,
  `convBoxed`, `S3`, the three `multiWriterScatter` group pins, plan-field decl list, and the A2
  reserved-name pins reversed (`#constUser` compiles); `B5cSingleBoxTest` `groupsOf` for `multiAxisOne` and
  `constOne` `[]` to `["S"]`. The only surviving source of `multiWriterScatter` is a predicate destination,
  which the source oracle refuses first (`UnsupportedSource.predicate`).
- **T2 fixtures (all in `ScatterGeometryTest`; all pass on the reference evaluator, checked f64 and checked
  f32 through `agree`, bit equal).** F1 `S(k)` k=8: `S[3]` twice plus `S[a]`: shape `[8]`,
  `[1,2,3,24,0,0,0,0]` (24 = 10+10+4; overwrite readings give 4 or 10). F2 `S[a+b]:=A*B`, `S[3]:=A[a]`,
  `S[a]:=A[a]`: `[2,14,126,248,340,400,0,0]`. F3 tropical max-plus `S[a+b]` with `S[6]:=maxA`:
  `[2,11,101,102,103,104,4,-inf]`. F4 boxed single constant `[0,0,0,10,0,0,0,0]` and boxed multi-axis
  `[1,12,123,234,340,400,0,0]`; past the box: `writerExtentExceedsBox "S" 1 0 3 4` (constant, box 3) and
  `... 1 0 5 6` (`a+b`, box 5). F5 `S(a)` plus `S[a+b]` (D5 with a multi-axis writer): derived shape `[6]`,
  `groupsOf == []`. F6 unpinned `conv` plus bare `S[a]`: `writerExtentMismatch "S" 2 0 6 4`; two `conv`
  writers accepted `[2,24,246,468,680,800]`. F7 `#constUser`: `[1,2,0,0,0,0,0,0]` in all legs. F8 raw
  `.affine (.const 3)` writers in a hand-built schedule: `validateScheduled` gives `multiWriterScatter "S"`.
  F9 (scan-local constant) is already pinned (`StructuralTest` and the preflight pin), none added.
- **Raw `.affine (.const _)` reachability.** Not reachable through `compile` or `compileToScheduled`:
  `lowerArith` lowers every raw constant of a plain `.assign`/`.scatter`; the only statements that keep a raw
  constant carry a scan slot, and `plainAt?` (the collector's view) does not see scan bodies.
- **Surface parse results** (verbatim `#eval`): `S[a + b]` gives `.affine (.affine 0 [(1,a),(1,b)])`;
  `S[2*a + b]` `[(2,a),(1,b)]`; `S[a + 2*b + 3]` bias 3; `S[a + b + 3*c + 5]` bias 5 with three terms;
  `S[=3]` and `S[= 3]` both `.affine (.const 3)`; `S[3]` `.iterAt` with the placeholder axis (name `""`);
  existing forms: `x` `.free`, `x .` `.freeNorm`, `x +1` `.affine (.shift x 1)` (scan lowering reclassifies it
  to `.iterNext` for a scan axis), `x + 2` `.affine (.shift x 2)`, `2*x` `.affine (.scale 2 x)`, `2*x + 3`
  `.affine (.affine 3 [(2,x)])`. `S[a + a]` is two unmerged terms; `S[0*a + b]` keeps `(0,a)`.
- **Ambiguity.** None observed: the new rule needs at least two axis terms and a lone numeral is not an axis
  term, so `x + n` and `n*x + m` never match it; the `atomic("+" tl_axis_term)` is needed or the many1 loop
  commits to `+` and dies on the bias numeral. The name `bias` is a reserved token (from `linear ... bias`),
  so a Lean local called `bias` in the elaborator arm fails to parse (the arm uses `c0`); an axis NAMED `bias`
  cannot appear in a slot (pre-existing).
- **Surface fixture values.** `convSurf` (`S[a+b] := A[a] . B[b]`, a=4, b=3, A=[1,2,3,4], B=[1,10,100]):
  shape `[6]`, `[1,12,123,234,340,400]` in reference, checked f64, checked f32, bit-equal to the hand-built
  `convProg`. `biasSurf` (`S[2*a + b + 1]`): shape `[10]`, `[0,1,10,102,20,203,30,304,40,400]`. `f1Surf`
  (F1 in surface form) `[1,2,3,24,0,0,0,0]`, `compErr == none`. `constPinSurf` (`S[=5] := A[a]`, k=8)
  `[0,0,0,0,0,10,0,0]`. `constLoneSurf` (`S[3] := A[a]`): `preflight CapabilityError.noAdvancingAxis "S"`.
  `a + a`: ACCEPTED, shape `[8]`, `[111,0,222,0,333,0,444,0]`. `0*a + b`: ACCEPTED, shape `[3]`, `[10,100,1000]`.
  Empty axis `b = 0` with `B = []`: shape `[4]`, all zeros, all legs. An empty axis with a NON-empty input
  makes all three legs return `none` (not pinned).
- **Scan bodies (U6, linear bodies only; with `relu` the nonlinear-scatter refusal
  `unsupportedNonlinScatter "G"` fires first and masks).** Baseline `G[j,0]; G[j,l +1]` accepted.
  `G[=2, l +1]` and base `G[=1, 0]`: `compile CompileError.overlappingScatter "G"`; `G[j + k, l +1]`:
  `preflight CapabilityError.multiAxisScatterLhs "G: affine LHS slot"`.
- **Job counts (full build `LeanNCD Tests JaxExperiment`).** T1 only (first engine commit): 8843. T1+T2:
  8843. T1-T4, T1-T5 and T1-T6: 8844 (the `+1` is `ScatterSurfaceTest`; T6 adds no module). T3 alone was not
  built separately.

## 4. Tasks

| Task | Patch | Fixtures / pins | Mutation cycles | Risk |
| --- | --- | --- | --- | --- |
| T1 engine | `T1-engine.patch` (14 files) | 15 logically re-pinned guards (25 `#guard` lines changed) in 7 modules; 0 new fixtures | 9 (`SGB-T1-01..09`, shared with T2) | high: `Ast.lean` rebuild, many re-pins |
| T2 engine fixtures | `T2-engine-fixtures.patch` (2 files) | F1-F8 in `ScatterGeometryTest` (8 families) plus `conditionCount fI2 == 0` in `SourceDifferentialScatterTest`: 20 added `#guard` lines in all | (the same 9) | medium |
| T3 surface syntax | `T3-surface.patch` (3 files) | pins U1, U2, U3, U5 (elaboration half) in `ParseProgramTest` (14 added guard lines) | 8 (`SGB-T3-01..08`) | medium |
| T4 surface fixtures | `T4-surface-fixtures.patch` (2 files) | `ScatterSurfaceTest`: convSurf, biasSurf, f1Surf, constPinSurf, constLoneSurf, U5 value pins, U6 scan refusals (21 added guard lines) | (the T3 8) | low |
| T5 docs | `T5-docs.patch` (13 files) | none | none | low, but rebuilds downstream (comments in `.lean` files) |
| T6 review fixes | `T6-review-fixes.patch` (4 files: `ScatterSurfaceTest.lean`, `Collect.lean`, `Differential.lean`, `DSL/AGENTS.md`) | `r1Surf`, `r2Surf` (10 added `#guard` lines): the D5 identity-slot pair of B-D3; docstring wording in `boxedSingleGroups` and `declaredShapeWins`; `DSL/AGENTS.md` notes (parse spellings, zero-coefficient slots, `route` ignores the box) | 1 (`SGB-T6-01`: D5 exclusion removed, killed by `ScatterSurfaceTest` alone, kill site `r1Surf`) | low, but rebuilds downstream (docstrings) |

Total: 18 manifest entries; 6 commits; one full build (8844 jobs) at the end of T1 and again at the end.
Task boundaries: T1 and T2 are separate because a reviewer could reject the production change and re-pins
while approving the new fixtures, or the reverse; T3 and T4 for the same reason on the surface. T1's expected
turn count was above 60 in the prototype; as a patch it is one `git apply` plus one full build.

### T1: engine admission, marker deletion, oracle mirror (`T1-engine.patch`)

Files (each `identifier @ file`; window-read, never whole-file-read):

- `LHSSlot.collectable` (renamed from `LHSSlot.boundedScatter`), deleted `constUnitPrefix`,
  `IdxExpr.isConstUnit` @ `leanncd/LeanNCD/DSL/Ast.lean`.
- `boxedSingleGroups` (scatter arm; its docstring), `checkWriterGroup` @ `leanncd/LeanNCD/DSL/Pipeline/Collect.lean`.
- deleted `checkReservedAxisNames`; `lowerConstSlots` (axis spelled as a bare literal, display only)
  @ `leanncd/LeanNCD/DSL/Pipeline/Structural.lean`.
- the two uses of `checkReservedAxisNames` in `TLProgram.compile` and `compileToScheduled`
  @ `leanncd/LeanNCD/DSL/Compile.lean`.
- deleted `CompileError.reservedAxisName` @ `leanncd/LeanNCD/Exec/Uid.lean` (no match arms existed).
- `declaredShapeWins` @ `leanncd/LeanNCD/Semantics/Source/Differential.lean`.
- test-side `bounded` @ `leanncd/test/Semantics/OracleSortRules.lean`.
- re-pins @ `leanncd/test/DSL/Pipeline/StructuralTest.lean`, `test/Eval/Plan/B5BoundaryTest.lean`,
  `test/Eval/Plan/B5cSingleBoxTest.lean`, `test/Eval/Plan/ScatterGeometryTest.lean`,
  `test/Semantics/OracleMixedRefusalTest.lean`, `test/Semantics/OracleSortRulesTest.lean`,
  `test/Semantics/SourceDifferentialScatterTest.lean`.

`checkCollectorShapes` / `CollectorShape.lean` need no new arithmetic: they call `LHSSlot.outExtent` per slot
(re-grepped at authoring: `outExtent` at the two call sites in `leanncd/LeanNCD/Eval/CollectorShape.lean`).
Check: apply, `git apply --check` first, full build green (8843 jobs), hash table rows marked T1.

### T2: engine fixtures (`T2-engine-fixtures.patch`)

`ScatterGeometryTest` F1-F8 (section 3 values; donors named in the file: `cstProg`/`pinAll` to `grpN`,
`convOf`'s slot to `sumSlot`, `cst`, `facA`/`facAB`, `shapesOf`, `refShape`/`planShape` from `B5NativeTest`)
and `#guard conditionCount fI2 == 0` @ `leanncd/test/Semantics/SourceDifferentialScatterTest.lean`. That guard
exists because mutant `SGB-T1-04` (the oracle excludes constant writers again) SURVIVED every `tag` guard: the
native legs now publish the declared shape and never `confirm` a predicted condition, so only a condition
count sees the predictor. Check: targeted build `Eval.Plan.ScatterGeometryTest` and
`Semantics.SourceDifferentialScatterTest` green, full build 8843 jobs.

### T3: surface syntax (`T3-surface.patch`)

- `declare_syntax_cat tl_axis_term`; `syntax:max ident : tl_axis_term`; `syntax num "*" ident : tl_axis_term`;
  `syntax:55 tl_axis_term (atomic("+" tl_axis_term))+ ("+" num)? : tl_lhs_slot`;
  `syntax:max "=" num : tl_lhs_slot` @ `leanncd/LeanNCD/DSL/Syntax.lean` (just above the old `tl_lhs_slot`
  rules).
- `elabTLAxisTerm` (new) and two new FIRST arms of `elabTLLHSSlot` (multi-axis, constant)
  @ `leanncd/LeanNCD/DSL/Elab.lean`. Every pre-existing arm is byte-unchanged (verified by the diff touching
  only added lines in that function).
- pins U1, U2, U3, U5 (elaboration half) @ `leanncd/test/DSL/ParseProgramTest.lean` (helper `slotsOf`).
No guard re-pin is forced (the full build was green with no existing test edited). Check: targeted build of
`LeanNCD.DSL.Elab` and `DSL.ParseProgramTest`, hash rows marked T3.

### T4: surface fixtures (`T4-surface-fixtures.patch`)

`leanncd/test/Eval/Plan/ScatterSurfaceTest.lean` (new; imports only `Eval.Plan.B5NativeTest`), registered in
`leanncd/lakefile.toml` after `Eval.Plan.ScatterGeometryTest`. Donors: `ScatterGeometryTest.convOf sumSlot`
(`convProg`) for U4, F1 for `f1Surf`. Check: targeted build of `Eval.Plan.ScatterSurfaceTest`, full build
8844 jobs. The new module is reachable by the `Tests` glob (the lakefile row), so it is part of the standard
test build; no `AGENTS.md` change is needed for discoverability beyond T5's rows in
`DSL/AGENTS.md` and `Eval/Plan/AGENTS.md`.

### T5: documentation (`T5-docs.patch`)

Edits only text that now lies; no code. Applied on top of T4. Files and identifiers:

- `elabTLLHSSlot` docstring @ `Elab.lean` (lists every slot form; fixes the pre-existing wrong
  `x +1 -> .iterNext` line, which is `.affine (.shift x 1)`, reclassified by scan lowering).
- header comment of the multi-axis rule @ `Syntax.lean` (said the old rules were "above", they are below;
  documents the `S[a + b +1]` parse error).
- `CapabilityError.multiAxisScatterLhs` docstring @ `Eval/Plan/Error.lean` (said unreachable from surface
  syntax; it is now reachable for a scan statement `G[j + k, l +1]`).
- header of `DSL/Pipeline/Collect.lean`, comment on `CompileError.multiWriterScatter` @ `Exec/Uid.lean`.
- header of `test/Eval/Plan/ScatterGeometryTest.lean`, the `fI1`/`fI2`/`fMask` comment block in
  `SourceDifferentialScatterTest.lean`. The T5 patch keeps that file's guard line numbers unchanged (a
  comment line was added back), because the manifest `expect` strings for `SGB-T1-04` and `SGB-T1-05` name
  line numbers in it.
- `leanncd/LeanNCD/DSL/AGENTS.md` (Collect row; the constant-slot Pitfall rewritten without the marker or
  the reservation; one new Pitfall for `S[a + b +1]`; one new Contracts bullet with the `tl_lhs_slot` grammar;
  injected Pitfalls section stays about 2.5k characters), `Eval/Plan/AGENTS.md` (two rows),
  `Semantics/AGENTS.md` (C1 counts `281/186/38` and `99`, the `known:extent` paragraph).
- `leanncd/docs/test_portfolio.md` rows KG-reshape (two) and EC9, and the comments in
  `test/Eval/Portfolio/EdgeCaseTest.lean` and `KnownGapTest.lean`: these said a multi-axis LHS slot does not
  parse. Text now says it parses and where it is pinned, and does NOT claim reshape/flatten/Kronecker/im2col
  programs are covered.

Not edited (history): every `*_record.md`, `*_review*.md`, slice plans, `docs/superpowers/**`, and the
`papers/semantics` narrative notes that mention `multiWriterScatter` as it was when written
(`additive_production_decision_note.md`, `lean_executable_semantics_path_part_4.md`,
`tensor_logic_semantic_gap_audit.md`). The last two state "scatter multi-writer sets are rejected" as of their
landing date; they are stale in that sense and are PARKED (about 0.2 dispatch, wording only).

Docs sweep as commands, run in the worktree root after T5 (record counts in the close-out):

- `rg -n "boundedScatter|isConstUnit|constUnitPrefix|checkReservedAxisNames|reservedAxisName" leanncd --glob "*.lean" --glob "*.md" --glob "!docs/superpowers/**"`:
  the expected result (observed at authoring on the T5 tip) is exactly three hits, all comments in
  `leanncd/test/Eval/Plan/ScatterGeometryTest.lean` that say these names are DELETED or reversed; any other
  hit, or one that presents a name as live, is a finding.
- `rg -n "slice B|Slice B" leanncd/LeanNCD`: every hit must describe slice B in the past tense (observed at
  authoring: 10 hits in 8 files, all past tense; `leanncd/test` hits are the slice's own fixture comments).
- `rg -n "multiWriterScatter|multiAxisScatterLhs|scatterOrAffineLhs" leanncd/LeanNCD --glob "*.md"`: each
  remaining hit must be correct under section 2.
- `rg -n "^\+.*[A-Za-z]+\.lean:[0-9]+" papers/semantics/additive_scatter_geometry_b_patches` must report nothing.

### T6: pre-execution review fixes (`T6-review-fixes.patch`)

Added after the authoring-time review (section 9), on top of T5. Four files: `r1Surf` and `r2Surf` appended at
the end of `ScatterSurfaceTest.lean` (no earlier line moves; the T3 manifest entries are file-prefix matches,
so they are unaffected); the D5 paragraph of the `boxedSingleGroups` docstring in `Collect.lean` and the
`declaredShapeWins` docstring in `Differential.lean` (comment text only, no code); and `DSL/AGENTS.md` notes:
`a + b +1` and `a+b+1` are both parse errors (the `+1` token) and the bias spelling is `a + b + 1`; `0*a + b`
is accepted with `a` a summed collision axis whereas `Out[0*i]` is rejected, and a slot with no placing term
compiles but fails at run time; `route` / `TLProgram.compile` never applies a declared box (it calls
`desugarMultiWriters` without the pinned map), so a boxed single writer whose reach exceeds the box compiles
through `route` but is refused natively with `writerExtentExceedsBox`, now also for constant and multi-axis
writers. Check: `git apply --check`, the four hash rows marked T6, full build 8844 jobs, `--task T6` PASS.
Observed at authoring: `r1Surf` shape `[4, 3]` and cells nine zeros then `1, 10, 100`; `r2Surf` shape `[8, 3]`
with rows 3 and 5 each `1, 10, 100`, all other cells 0; reference, checked f64 and checked f32 agree.

## 5. Recurring-defect audit (case x class)

The defect family (slice A defects A1 and A2 both shipped because a diff reader could not see them): a slot
rule stated in one place and silently ignored or restated in a sibling. Siblings a diff cannot show, each
re-grepped at authoring for callers:

- `LHSSlot.collectable` @ `DSL/Ast.lean`: callers are exactly `boxedSingleGroups` (scatter arm) and
  `checkWriterGroup` (`DSL/Pipeline/Collect.lean`), and the doc comments; it no longer calls
  `scatterAffineClass`, whose only remaining consumer is `checkScatterAffineExpr` (`Eval/Plan/Compile.lean`).
- `slotsBecomeScatter` @ `DSL/Ast.lean` (any `.affine` slot, or a repeated free axis): callers in
  `Structural.lean` (`lowerArith`, the read-rank guard), `RouteFragments.lean` (`fragmentClass`,
  `physicalizeOne`), `Eval/Plan/Compile.lean` (`unloweredScatterAssign`), `Collect.lean` (`checkWriterGroup`
  `.assign` arm and two group predicates). T1 does not change it, so a multi-axis or constant `.assign` is
  still reclassified to a scatter before collection.
- `checkScanScatterLHSSlot` / `checkScatterAffineExpr` @ `Eval/Plan/Compile.lean`: unchanged; scan-local
  constant and multi-axis stay refused.
- `boxedSingleGroups` D5 test (`sourceUIDs` against `declUIDs`) @ `Collect.lean`: unchanged; it now also sees
  multi-axis and lowered-constant writers.
- the oracle predictors: `declaredShapeWins`, `derivedShape`, `nonBareWrite`, `detectConditions` @
  `Semantics/Source/Differential.lean`; `bounded`, `singleBoxed`, `pinnedBox`, `predictedExtent`, `predict`
  @ `test/Semantics/OracleSortRules.lean` (TEST code).

Cell = what the code does after this slice; class R = required and pinned by a named fixture, F = forbidden
and pinned, **S** = silently ignored (no pin).

| slot class | top-level single | multi-writer group | boxed single (pinned decl) | scan-local |
| --- | --- | --- | --- | --- |
| single-axis strided (`2*i`, `i+2`) | R (CompileTest, ScatterCompileTest S9) | R (B5 tests) | collected unless D5: R (B5c) | admitted by `checkScanScatterLHSSlot`: R |
| multi-axis (`a+b`) | R (`conv`, `convSurf`) | admitted since T1: R (`convTwo`, `twoAxes`, F2, F6) | collected, declared shape wins: R (F4, `convBoxed`, `multiAxisOne`, `fFbig`); D5 with multi-axis: R (F5) | refused `multiAxisScatterLhs` at preflight: F (U6); reference/legacy overwrite there (F3): **S**, owner F3 |
| constant, lowered (`S[=3]`, hand-built `.affine (.const n)`) | R (`constPinSurf`, `fI1`..) | admitted: R (`explicitConstant`, F1, F2, `f1Surf`) | collected, declared shape wins: R (F4, `constOne`, `fI1`, `fI2`, `fMask`) | `overlappingScatter` at compile: F (U6, `StructuralTest`) |
| constant, RAW (hand-built schedule that skipped `lowerArith`) | refused by preflight (`scatterOrAffineLhs`, `CompileTest`): R | `multiWriterScatter`: F (F8, fixture `rawInGroup`) | not collected: F (by constructor; F8) | refused: R |
| zero coefficient (`0*a + b`, `0*i`) | multi-axis surface form accepted: R as observed (U5); single-axis `Out[0*i]` rejected out of range: R; a slot with no placing term (`0*a + 0*b + k`) compiles and fails at run time with a range error in every leg: observed by lens 2, documented (T6), not pinned: **S** | single-axis `0*i` group admitted: R (`zeroScale` @ `B5NativeTest`); multi-axis `0*a + b` in a group: observed bit-equal across reference and both checked legs by lens 1, not pinned: **S**, parked 0.2 | collected: **S** (not separately pinned); a zero-coefficient declared axis fires D5: observed, documented (T6) | slot admitted, scan refused: R |
| constant or multi-axis slot beside an IDENTITY slot over a declared axis (`S[=3, b]`, `tensor S(k, b)` pinned) | R (`r1Surf`) | two writers publish the declared shape: R (`r2Surf`) | D5 fires, derived shape `[4, 3]`: R as the documented consequence of the exclusion (`r1Surf`; owner decision 2026-11-01) | refused as for a plain constant: F (U6) |
| repeated axis (`a + a`) | accepted, behaves as `2*a`: R as observed (U5) | **S** | **S** | **S** |
| diagonal (`Y[i,i]`) | R (`diagonal`) | R | D5 excludes the repeated free slot: R | **S** (no pin, slice A parked) |
| axis spelled `#const...` | ordinary axis: R (F7, both compile chains) | **S** | collected into the declared box: R (F7) | **S** |
| predicate destination | refused at capability tier: R | `multiWriterScatter`: F (`B5BoundaryTest` `predicateDest`) | not boxed: R | n/a |
| rank-0 destination (no declared axes) | a non-empty scatter write is refused at `compileToScheduled` (`rankMismatch "S" 0 1`) and by the source oracle's admission: unreachable (observed by lens 1) | same refusal | not boxed in production (`boxed` needs `!ax.isEmpty`); `declaredShapeWins` is vacuously true but the cell is unreachable | n/a |

Oracle and predictor cells:

| predictor | production rule it restates | agreement pinned by | status |
| --- | --- | --- | --- |
| `declaredShapeWins` | `boxedSingleGroups` boxed and D5 | `conditionCount fI2 == 0` (T2), `fFbig`, `fI1`, `fI2`, `fMask` `parity`; mutants `SGB-T1-04`, `-05`; D5 identity-slot row `r1Surf` (T6, mutant `SGB-T6-01` mutates production, not the oracle: the oracle's own D5 agreement for that row is not pinned) | R; rank-0 cell unreachable (above) |
| `derivedShape` | `LHSSlot.outExtent` (calls it) | `fF`, `fD` (M1) | R (calls the single home, not a restatement) |
| `nonBareWrite` | classifies forms | `fA`..`fN` | R |
| test `bounded` / `singleBoxed` | `LHSSlot.collectable` on source slots | `OracleSortRulesTest` C1 counts, `strictC1Tags` guards, hand rows (17 rows, 11 accepts) | R; `bounded` accepts a raw `.affine (.const _)` that production refuses, unreachable from source: **S**, harmless |
| test `predictedExtent` | extent per slot | single-axis guards only | multi-axis uses the legacy SUM rule: **S**, parked 0.3 |

Every **S** cell has an owner in section 2 (parked with an estimated cost) or is the F3 slice, EXCEPT the
following, which this plan parks here: zero-coefficient writer in a group or boxed destination (about 0.3,
Direct path, one fixture each; the group value was observed by lens 1, section 2), repeated axis in a group
(covered by the degenerate-slot validation row of section 2), `#const...` axis in a group or scan context
(about 0.2), diagonal scatter in a scan (about 0.3, inherited from slice A). The authoring-time review
(section 9) probed the rank-0 cell (unreachable) and the zero-coefficient group cell (observed); the executor's
lenses (section 6) need not repeat those two probes.

## 6. Review focus

Two lenses, separate contexts, each given `git diff <base>..<branch head>` plus sections 3 and 5 of this plan,
each appending findings to its own file as it goes (not at the end). Window reads only.

- **Lens 1: what a diff cannot show**, file `papers/semantics/additive_scatter_geometry_b_review_siblings.md`.
  For each sibling named in section 5, re-grep callers and read the unchanged code around them. Does any
  consumer of a slot still special-case a constant by SHAPE of its axis or by position (forgeable marker
  survivors)? Does the oracle ever disagree with production for a program class this slice newly accepts:
  rank-0 destination, zero-coefficient writer, multi-axis writer reaching `predictedExtent`? Are the
  re-pinned guards in section 3 still capable of failing (the re-pinned intent, not just the new value)?
- **Lens 2: surface grammar and doc truth**, file `papers/semantics/additive_scatter_geometry_b_review_surface.md`.
  Parse ambiguity beside `x +1`, `x + n`, `n*x + m`, `x .`, `n`; degenerate forms (`a + a`, `0*a + b`,
  `S[a + b +1]`, an axis called `bias`); does the docs sweep of T5 leave any stale statement (run the commands
  of T5 and read each hit)? Are all docs claims about "pinned in `ScatterSurfaceTest`" true?

Each finding gets a verdict (fix now, park with cost, reject with reason) in the record.

## 7. Verification gates and exact values

- **Blob hashes** (Git blob IDs as `git hash-object` prints them). A path changed by several tasks is only
  checkable after its last owning task; the T5-touched paths are given after T4 and after T5. Tree hashes are
  not used (the executor's base also carries this plan).

  | Path | blob | check after |
  | --- | --- | --- |
  | `leanncd/LeanNCD/DSL/Ast.lean` | `68bfb6275fb1ffd7918733538f049ddf95b794f4` | T1 |
  | `leanncd/LeanNCD/DSL/Compile.lean` | `ad9e73cd1d0280d7440b1dfb9c06813c8b52ff53` | T1 |
  | `leanncd/LeanNCD/DSL/Pipeline/Structural.lean` | `1354a2058b15b3a6153ca71c4d55b1f240bd97fd` | T1 |
  | `leanncd/LeanNCD/Semantics/Source/Differential.lean` | `29dd768cd4d237923eb7230ca13f8063af031ea0` | T1 |
  | `leanncd/test/DSL/Pipeline/StructuralTest.lean` | `3869378a7f2f878b37cb1794addc2d76389b7014` | T1 |
  | `leanncd/test/Eval/Plan/B5BoundaryTest.lean` | `32430358acacbc48808570b9f1d2149371a47923` | T1 |
  | `leanncd/test/Eval/Plan/B5cSingleBoxTest.lean` | `4dfba98e65dd354430f8dead9915bf68ba1559eb` | T1 |
  | `leanncd/test/Semantics/OracleMixedRefusalTest.lean` | `c7bb3f3f70e078476e506182171d35783d8827dc` | T1 |
  | `leanncd/test/Semantics/OracleSortRules.lean` | `d95b9fe5729159b2634b12e168e58e44b8543560` | T1 |
  | `leanncd/test/Semantics/OracleSortRulesTest.lean` | `1ffd58cae16b7c4bd61f6e9dc47fddc3a1807c5c` | T1 |
  | `leanncd/test/DSL/ParseProgramTest.lean` | `eff4e64177c95a27f166f469f6698b4a721968a4` | T3 |
  | `leanncd/lakefile.toml` | `dc7de3f4719d84786b1f28cacb8f4acb9aa40210` | T4 |
  | `leanncd/test/Eval/Plan/ScatterSurfaceTest.lean` | `d08659f6bd237928789b8292bb4693dfb9649147` | T4 |
  | `leanncd/LeanNCD/DSL/Elab.lean` | `c3a9f84b1c42b0732da728c753902f1856ec9d94` | T4 |
  | `leanncd/LeanNCD/DSL/Pipeline/Collect.lean` | `d455e05faf6a146045b49308f22cf9a5c633b666` | T4 |
  | `leanncd/LeanNCD/DSL/Syntax.lean` | `e538eaddffde4d26d5c24449d9a533e2fc6092e8` | T4 |
  | `leanncd/LeanNCD/Exec/Uid.lean` | `637fbafd007c00a6270ebf954ba22349a842d7a7` | T4 |
  | `leanncd/test/Eval/Plan/ScatterGeometryTest.lean` | `0f8fa16d97f683409d18464deec333ee6c64831c` | T4 |
  | `leanncd/test/Semantics/SourceDifferentialScatterTest.lean` | `9cc0309575918c8b20f3f1b4fe041d4ac3e720aa` | T4 |
  | `leanncd/LeanNCD/DSL/Elab.lean` | `f1847ec910ce6cf5159e36364a9ba8c27281958c` | T5 |
  | `leanncd/LeanNCD/DSL/Pipeline/Collect.lean` | `9044fc2cc9e6fae8a025bb1a5603820416baf361` | T5 |
  | `leanncd/LeanNCD/DSL/Syntax.lean` | `64f206258ac30c41d3b03445fb8fb48cd737e529` | T5 |
  | `leanncd/LeanNCD/Exec/Uid.lean` | `91f716af652cb32b581d3c02de989e0fd15049b4` | T5 |
  | `leanncd/test/Eval/Plan/ScatterGeometryTest.lean` | `fc10a46fab7690fe22bb2ab4101a3775d8dcd5ec` | T5 |
  | `leanncd/test/Semantics/SourceDifferentialScatterTest.lean` | `6d6468dfeef3216809ba2e714e1985480b0cd10c` | T5 |
  | `leanncd/LeanNCD/DSL/AGENTS.md` | `b913fd3223a3a91c2261e7f5445518812a3c46ec` | T5 |
  | `leanncd/LeanNCD/Eval/Plan/AGENTS.md` | `6c182ec3068c97df8dc3f79f658fb73f7d21ae7a` | T5 |
  | `leanncd/LeanNCD/Eval/Plan/Error.lean` | `fd4cf80711c7f28b3f1dcec1dd17b9c34691bd15` | T5 |
  | `leanncd/LeanNCD/Semantics/AGENTS.md` | `6fa30b471e9a4c8bc9a85e9c8b3d5403341d7aba` | T5 |
  | `leanncd/docs/test_portfolio.md` | `9d8b50d8100437be5c87a10853b7709a2fe09b01` | T5 |
  | `leanncd/test/Eval/Portfolio/EdgeCaseTest.lean` | `20141972bd7a4ab6ce1fd5208d19245531c64e63` | T5 |
  | `leanncd/test/Eval/Portfolio/KnownGapTest.lean` | `61c34ece35a12c196c005e2f6c02dfb6809a4910` | T5 |
  | `leanncd/test/Eval/Plan/ScatterSurfaceTest.lean` | `dc44f29bee5713223b75736cdc65ca3127e4dbad` | T6 |
  | `leanncd/LeanNCD/DSL/Pipeline/Collect.lean` | `380cba607b4b6fee37d86edaae4ed01f3c942a4e` | T6 |
  | `leanncd/LeanNCD/Semantics/Source/Differential.lean` | `3f6f0360cb7fd0c7bb9900bef806d3bd8ea83c4b` | T6 |
  | `leanncd/LeanNCD/DSL/AGENTS.md` | `81ce262de3c0a00bed5942a56b87c2dce543971b` | T6 |

  Patch file blobs (to detect a corrupted copy of the package): `T1-engine.patch`
  `0264270c1065d3469d0ad036c07e62419a4d5362`, `T2-engine-fixtures.patch`
  `9f1a2da8292977950f7cd78eea389c943473162f`, `T3-surface.patch` `260faaa6adabd0cb84accb82ac8ecf115015a6f3`,
  `T4-surface-fixtures.patch` `60747c3fd9dfd34f92ec5216bab070b5635e3048`, `T5-docs.patch`
  `5a5c3b4174f671632667e6731f296999878798dc`, `T6-review-fixes.patch`
  `bbfd3509b118a5b537263dff29e76f30f5ea8d93`. The T1 row of `Differential.lean` and the T4/T5 rows of
  `Collect.lean`, `ScatterSurfaceTest.lean` and `DSL/AGENTS.md` are checked at their own stage and are
  superseded by the T6 rows once T6 is applied.

- **Final build.** `lake-build.sh <worktree>/leanncd LeanNCD Tests JaxExperiment` expects
  `Build completed successfully (8844 jobs)` after T4, T5 and T6 (8843 after T1 and after T2; T6 observed
  at authoring by the fixer and again by the controller). The count
  can drift by a few if main moved; any failure is BLOCKED.
- **Manifest.** `--check` unfiltered expects `manifest OK: 18 entries, 18 selected, every old-string unique`.
  The real run after all six patches: `--task T1` 9/9, `--task T3` 8/8 and `--task T6` 1/1, every verdict PASS,
  each mutated file restored byte-identically and each restore build green (`git status` clean after each).
  Observed at authoring: 17/17 on the T4 tip (prototype agents) and `SGB-T6-01` PASS on the T6 tip (fixer, one
  entry); the controller ran `--check` on all 18 against the T6 tip, not a real run of all 18. T6-01's `expect`
  strings are line pins on the second and fifth `#guard` lines of `r1Surf` (read them in the manifest), so
  they go stale if lines are inserted above `r1Surf`. If a verdict is FAIL do not edit the manifest: a patch or hash
  differs from the prototype. **What the manifest does NOT establish** (do not claim it in the record):
  (a) `ScatterGeometryTest` imports `B5cSingleBoxTest`, which imports `B5bBoxTest`, `B5BoundaryTest`,
  `B5NativeTest`; when a mutant breaks an upstream module Lake never builds `ScatterGeometryTest`, so only
  mutant `SGB-T1-07` is killed BY the new T2 fixtures (kill site `ScatterGeometryTest`, F8); for `-01..03`,
  `-06`, `-08`, `-09` the kill is by an upstream re-pinned or pre-existing guard (kill sites in
  `B5BoundaryTest`, `B5cSingleBoxTest`, `B5bBoxTest`, `B5NativeTest`), and `-04`, `-05` by
  `SourceDifferentialScatterTest`. The independent kill power of F1-F6 is UNMEASURED (parked, about 1
  dispatch). (b) The `SGB-T3` `expect` strings are file prefixes (`error: test/DSL/ParseProgramTest.lean:`,
  `error: test/Eval/Plan/ScatterSurfaceTest.lean:`), not guard lines, so they accept any failing guard in that
  file. (c) `SGB-T3-02` (term order reversed) is killed by `ParseProgramTest` ONLY: the affine function is
  order-invariant, so the surface cells cannot see it. (d) `SGB-T3-06..08` are killed by `ParseProgramTest`
  only. (e) a mutant breaking single-axis `Out[0*i]` behaviour is covered by `CompileTest` and
  `ScatterCompileTest` S9 in the full build only, not by any manifest entry.
- **Diff size.** `git diff --stat <base>..HEAD -- leanncd` over the six commits touches 26 distinct paths
  (T6 adds no new path); the table above is the list (36 rows: six paths are checked after T4 and again
  after T5, and four paths get one more row after T6). A different count is a finding.
- **No line numbers shipped.** `rg -n "^\+.*[A-Za-z]+\.lean:[0-9]+" papers/semantics/additive_scatter_geometry_b_patches`
  reports nothing (checked at authoring), and the same pattern over the executed documentation diff
  (`git diff <base>..HEAD -- "*.md"`) must be empty.

## 8. Close-out record (executor writes `papers/semantics/additive_scatter_geometry_b_record.md`)

Required fields, each from a real run: base and final commit hashes and the six commit hashes; per-task
`git apply --check` results; the section 7 hash table result; per-task build results and the final job count;
the mutation table (18 lines, killer module and file, restore results) with a line stating which kills are
by new fixtures versus upstream guards (section 7 caveat a); the section 3 values re-observed on the executed
tree; review findings and adjudication; the T5 sweep command outputs; the observation for the rank-0 and
zero-coefficient cells if attempted; **measured token total from the executor's own usage telemetry, naming
the method** (this is not Claude Code), against the Rule 6 slice-execution ceiling of about 175M and the
design note's guess of about 35M authoring; every skipped step; parked items carried forward with cost
(section 2 and 5 lists plus new review findings). Also add the task-completion note to the design note and
the Slice B row to the master plan documents the repo keeps (value-grep `scatter geometry` in
`papers/semantics/*.md` for the list).

## 9. Authoring evidence

Record: `additive_scatter_geometry_b_plan_record.md` (deviations, decisions, call counts, parked list, review
adjudication). Verification: `additive_scatter_geometry_b_verification.md` (replay, greps, manifest check,
checklist, T6 checks). Prototype ledger: `additive_scatter_geometry_b_files/proto_notes.md`.

Authoring-time review (2026-11-01, two lenses over the package at the T5 tip `2ad72b7c`): lens 1 (what a diff
cannot show) `additive_scatter_geometry_b_review_siblings.md`, 0 P1, 1 P2 (L1-1), 2 P3; lens 2 (grammar,
degenerate forms, package truth) `additive_scatter_geometry_b_review_surface.md`, 0 P1, 0 P2, 5 P3. T6
(`T6-review-fixes.patch`) is the fix batch for L1-1 (owner chose "keep D5, document and pin"), L1-2, L1-3,
L2-1 and L2-3; the other findings are plan-text corrections or parked rows (record). The executor's own two
lenses (section 6) still run on the executed tree.
