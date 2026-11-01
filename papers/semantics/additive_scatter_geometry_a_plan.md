# Scatter geometry, slice A: multi-axis and constant-slot scatters on the checked backend: implementation plan

**Status: execution-ready package; execution not yet started.** The owner approved the design
([additive_scatter_geometry_design.md](additive_scatter_geometry_design.md)) on 2026-10-30: decisions
D1-D6 as recommended, plus two owner decisions the same day: keep the scan-local `overlappingScatter`
guard (narrowed, section 2 item 6), and four-leg tropical fixtures are in slice A (not a later add-on).
The patches were generated against local `main` `6715e1280961b87423b3daa85942ce26113f7507` (the shas in
the verification record). The executor does not trust that sha: it re-checks `git apply --check` on
whatever local `main` is, and any descendant of it that has not touched the 20 paths in section 8 applies.
**Process: Full, light.** Changed published shapes for hand-built accepted programs and a new compile
rewrite, but no new carrier, kernel, plan IR or backend. One slice, five tasks, all code authored and
replayed in prototype and replay worktrees and shipped as patches; the executor replays and verifies, it
does not design. Authoring evidence is section 10; the execution record goes to
`additive_scatter_geometry_a_record.md` (created by the executor, section 9).

**Goal:** the checked f64/f32 backend runs a top-level scatter whose slot names two or more axes
(`S[a+b] := A[a]*B[b]`, the anti-diagonal sum) or is a constant coordinate (`S[3] := W[j]`, a total
reduction placed at coordinate 3), with the same shape and values as the reference evaluator, the legacy
evaluator and the oracle.

**Behaviour change in one paragraph.** (1) `LHSSlot.outExtent` for two or more distinct nonzero-coefficient
axes becomes the exact reach `max image + 1`, from one shared corner formula `affineImageBounds`
(`a+b` over (4,3) was 7, now 6); the oracle's `derivedShape` stops restating the formula and calls
`outExtent`. (2) The checked preflight admits multi-axis at top level (scan-local keeps refusing). (3) A
constant slot is rewritten by `lowerArith` (`lowerConstSlots`) into a placement over a synthetic size-1
axis named `#const<uid>`, so the plan IR needs no change; the marker `IdxExpr.isConstUnit` keeps groups
and boxed single writers treating it as before; the stale unconditional `.assign` guard is deleted for
ordinary constants and kept for a constant inside a scan statement. (4) Four-leg tropical rows on the
sorted differential vouch for the new geometries. (5) Live docs are updated.
**Slice B owns:** groups and boxed single writers of these forms (`LHSSlot.boundedScatter` stops gating),
and the surface syntax for both forms.

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

- **Worktree.** Create a new linked worktree from LOCAL `main`, not `origin/main` (stale), for example
  `git worktree add <repo>/.claude/worktrees/scatter-geometry-a-exec -b scatter-geometry-a-exec main`.
  Then run `bash .claude/skills/new-slice/prepare-worktree.sh` from inside it. It must report Mathlib at
  100%; if a build starts compiling Mathlib, stop (a cold build takes hours). Then build `LeanNCD` once
  to refresh project oleans.
- **Do not push.** Local `main` stays ahead of `origin/main`; say so in the final report.
- **Patches are the code.** Directory `papers/semantics/additive_scatter_geometry_a_patches/`: apply
  `T1-extent.patch`, `T2-multi-axis.patch`, `T3a-constant.patch`, `T3b-scan-const.patch`,
  `T4-tropical-fixtures.patch`, `T5-docs.patch` in that order, each after
  `git apply --check <patch>` (run from the worktree root, giving the absolute patch path). One commit per
  patch: six commits (Task 3 is two commits). Stage by explicit path. Do not retype Lean from this
  document; it has no Lean code fences on purpose.
- **BLOCKED rule.** A patch that does not apply, or a blob hash (section 8) that differs after the
  owning task, is BLOCKED: stop and report with the command output. Never repair a patch by hand and never
  loosen a fixture to get green; a failing fixture is a finding.
- **Builds.** Only `bash leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD Tests JaxExperiment`
  (or the module list a task names); long runs in the background, wait for the completion notice, do not
  poll. An `Ast.lean` edit (Tasks 1 and 3) recompiles about 8800 jobs, so those tasks end with the full
  build; the other tasks use the targeted build they name and the full build is the section 8 gate.
- **Mutation manifest.** `bash leanncd/scripts/mutation-manifest.sh --check <worktree>/leanncd
  papers/semantics/additive_scatter_geometry_a_mutations_post.json` unfiltered first, then
  `--task T1`, `--task T2`, `--task T3`, `--task T4` one at a time with `--out <scratch file>`, each in the
  background. It is a post manifest: run it only after all six patches are applied (section 8); the
  per-task commands below say which entries belong to which task.
- **Budget.** At most three substantive work items per dispatch, 60 turns, 250k peak context per dispatch.
  Report measured usage and any breach. No nested delegation. The prototype and replay dispatches
  exceeded this (section 4); that is why the work is shipped as patches, and the plan is not budgeted by
  them.
- **Tokens.** This executor is not Claude Code, so `.claude/skills/slice-plan/token-report.py` does not
  apply: record the total from the executor's own usage telemetry and name the method (section 9).
- **Review and merge.** After the two review lenses (section 7) and their adjudication, merge to local
  `main` per the `new-slice` finish sequence (`git merge --no-ff`, confirm `git diff --stat main <branch>`
  is empty, remove the worktree, delete the branch). Rule 13 of the repo `CLAUDE.md` authorizes this: no
  merge/PR menu. Do not push.

## 2. Fixed semantics and exclusions

1. **D1 scope.** Checked f64/f32, legacy evaluator and oracle only. `route`, JAX and scan-local are
   unchanged (same cut B5 and B5b made). `route` carries no extents and already accepted every form; the
   JAX codegen refuses every `.scatter` step categorically, so geometry cannot change that.
2. **D2 constant representation: C1, a unit axis.** A constant slot `n` becomes the placement `n + 1*u` over
   a fresh synthetic axis `u` pinned to size 1, as a `lowerArith` rewrite (`lowerConstSlots`). The existing
   `.affine` arm then derives extent `n+1` and image `n`; `ScatterPlan`, `checkScatterCore`, the range check
   and the kernels are not edited. (C2 masked assign and C3 plan marker were rejected: C2 needs a pinned
   declaration, C3 touches every consumer of the plan structure.)
3. **D3 multi-axis extent: M1, exact reach** from the same corner formula as the B6 range check.
   Exact values: `a+b` over (4,3) is 6; `a+4b` is 12; `2a+3b` is 13; the constant `3` is 4. The
   single-axis stride-aligned rule is unchanged: `2*i` over 4 is 8. M1 also WIDENS acceptance for
   mixed-sign rows whose minimum is already non-negative (`a-b+2` over (4,3): legacy extent 3, reach 6,
   was a B6 error, now in range); hand-built only, since the surface cannot spell a negative coefficient.
4. **D4 surface.** Multi-axis `x + y` slots and an explicit constant marker are slice B; the lone-numeral
   slot keeps meaning the scan base case (`.iterAt`), never a constant write.
5. **D5 guard.** The unconditional `overlappingScatter` throw on the `.assign` arm of `lowerArith` is
   deleted for ordinary constants (stale since S3a, which sums collisions).
6. **Owner decision, scan-local guard kept.** A statement carrying an `iterAt`/`iterNext` slot AND a raw
   constant slot still throws `CompileError.overlappingScatter` at `lowerArith` (`LHSSlot.isScanSlot`,
   `LHSSlot.isRawConst`). Deleting it outright made such a program compile and then overwrite in the
   reference and legacy evaluators (F3) while the checked preflight refuses it: a fail-loud regression.
   `overlappingScatter` therefore keeps exactly one producer.
7. **Plan-time refinements.** The top-level `.constant` arm of the checked preflight STAYS, narrowed to
   a hand-built schedule that bypasses `lowerArith` (it reports `scatterOrAffineLhs`; without it the program
   fails later with a confusing `scatterImageOutOfRange`). `checkScanScatterLHSSlot` keeps both refusals,
   so `scatterAffineClass` stays. The constant-writer-under-a-boxed-declaration fixture is slice B.
8. **D6 slicing.** A then B. Slice B's plan is written after A lands.

**Not in this slice** (owner and rough cost in dispatches):

- Groups and boxed single writers of these forms, and surface syntax for both: slice B (`boundedScatter`
  stops gating; about 1 dispatch of B's own work for the pinned-declaration-ignored cell).
- Scan-local multi-axis and constant scatters: F3 (overwrite versus sum), a dedicated slice, about 1 dispatch.
- `route` and JAX: unchanged refusals, no work owed.
- Predicate and bool destinations (B5 D1); negative coefficients or biases in surface syntax; M4 actual-image
  box fit; f32 tropical comparison on the four-leg harness.
- Mutation-checking the new-module pins independently of the older B5 pins: parked, about 0.3 dispatch
  (the ledger's reason: `ScatterGeometryTest` imports a chain that fails first, section 5 Task 2).
- Further parked items from the ledger, each with cost: a hand-built scan-local constant `.scatter` is still
  accepted by reference/legacy and overwrites (F3, 1 dispatch); no pin for a diagonal scatter inside a
  scan, none for a zero-coefficient writer under a boxed declaration (0.3 dispatch each); the oracle's
  `declaredShapeWins` mirrors `boxedSingleGroups` by hand and the `isConstUnit` marker must be unmarked
  together with it when slice B boxes constants (a shared predicate in `Ast.lean` would remove the copy,
  about 0.5 dispatch); a stale comment in `leanncd/test/Eval/Plan/ScatterCompileTest.lean` still names the
  deleted `LHSSlot.collapses` (0.1 dispatch, found at authoring, not covered by any patch).

**Anti-goals** (a failure even if every test passes): changing the stride-aligned single-axis extent;
reinterpreting a lone numeral slot; a silently skipped or clamped out-of-range write (a constant or
multi-axis write outside its extents is an error in both backends); a second extent formula (the extent
stays computed in one place, `affineImageBounds`).

## 3. Reuse and invariants

- One corner formula: `affineImageBounds` (`DSL/Ast.lean`) is called by `LHSSlot.outExtent` (the extent) and
  by `scatterImageBounds` (`Eval/Plan/Check.lean`, the B6 range rule); `scatterImageBounds` kept its name
  and signature so B6 callers are untouched.
- The oracle's `derivedShape` calls `LHSSlot.outExtent`; it no longer owns an extent formula.
- Invariants each fixture below encodes: every program accepted before publishes the same shape and values
  except hand-built multi-axis scatters (M1 shrinks their extent); single-axis extents do not move;
  reference, legacy, checked f64 and checked f32 agree on every new fixture; out-of-range is an error.

## 4. Facts measured at authoring (do not restate without re-measuring)

- **P0 probe** (throwaway worktree on `6c4a737e`, since removed). With the two checked refusals lifted and
  no M1, `Y[a+b]` and `Y[a+4b]` matched the reference in value and shape (`[7]`, `[16]`), so the kernel and
  range check are multi-axis-ready. A constant slot failed in `prepareEvalPlan` with
  `scatterImageOutOfRange "Y" 0 3 3 3` while the reference published `[4]`. Source-level, an extent-1 axis
  read by no tensor (`Y[u+3] := X[a]`) gave `[4]`, `[0,0,0,10]` in both backends, which is why C1 is a
  rewrite. `route` returned OK for every case. Mixed-sign `a-b` is an error in both backends.
- **M1 blast radius** (two full builds): M1 alone moved 2 test modules and 7 guards
  (`ScatterCheckTest`, `SourceDifferentialScatterTest`); M1 plus the top-level lift moved 3 modules
  (`CompileTest` added). Every failing guard pinned the legacy extent or a refusal slice A removes.
- **Second extent formula (found in prototype dispatch 1).** The oracle's `derivedShape`
  (`Semantics/Source/Differential.lean`) restated `c0 + sum c*n`; under M1 alone no guard failed
  (`conditionCount fF == 1` still passed, predicting 7 against production's 6), so the stale copy is
  invisible until the checked refusal is lifted. Task 1 therefore edits it. It also removes a latent
  `2a+3` divergence (stride-aligned 10 against the predictor's 11) that no fixture covered.
- **Phase order.** `assignUIDs, resolveDecls, reclassifyIterSlots, checkReadRanks, checkDtypes,
  checkScatterNonlin, lowerArith, finalizeScans, schedule`; collection (`collectDefinitions`,
  `writerGroups`, `boxedSingleGroups`, `checkWriterGroup`) runs on the scheduled program, AFTER
  `lowerArith`. A plain rewrite would therefore make `boundedScatter` see a bounded single-axis slot and
  admit constant writers to groups; the marker `IdxExpr.isConstUnit` (axis-name prefix
  `constUnitPrefix`) inside `LHSSlot.boundedScatter` is the one gate both collector sites use.
- **Replay** of the patches onto base `6715e128` in a fresh worktree: all six apply with
  `git apply --check` and `git apply`; 20 paths are blob-equal to the prototype head `e5bb6b3c`;
  `lake-build.sh ... LeanNCD Tests JaxExperiment` reports `Build completed successfully (8843 jobs)`;
  manifest `--check` OK (31 entries), then 31 of 31 killed (T1 9/9, T2 7/7, T3 12/12, T4 3/3), every
  production file restored byte-identically. Applying all six in order in a scratch worktree reproduced the
  replay tree for `leanncd/` and the two papers docs.
- **NOT done.** No review lens has read the diff. Authoring tokens were not measured by the controller.
  Per-task builds were not measured on the replay (only the final tree). The prototype dispatches exceeded the
  60-call guidance; harness-reported tool-use counts: dispatch 1 = 138, dispatch 2 = 118, dispatch 3 = 53
  then resumed to a cumulative 83, dispatch 4 = 29, replay = 38. The plan itself is not budgeted by them.

## 5. Tasks

Paths are relative to `<worktree>`; patch directory `papers/semantics/additive_scatter_geometry_a_patches/`.
Hash check command (one per path, no pipeline): `/usr/bin/git -C <worktree> hash-object <path>`; expected
values are the section 8 table.

### Task 1: exact-reach extent (`T1-extent.patch`)

**Files (7):** `leanncd/LeanNCD/DSL/Ast.lean`, `leanncd/LeanNCD/Eval/Plan/Check.lean`,
`leanncd/LeanNCD/Semantics/Source/Differential.lean`, `leanncd/lakefile.toml` (one `Tests` glob entry),
`leanncd/test/Eval/Plan/ScatterCheckTest.lean`, new `leanncd/test/Eval/Plan/ScatterGeometryTest.lean`,
`leanncd/test/Semantics/SourceDifferentialScatterTest.lean`.

**Behaviour.** `affineImageBounds` (new, `DSL/Ast.lean`, directly above `LHSSlot.outExtent`) is the single
corner formula; `LHSSlot.outExtent` gains an arm for two or more distinct nonzero-coefficient axes giving
the exact reach (clamped at 0; a zero-size named axis keeps the legacy value); the single-axis stride arm,
the zero/no-coefficient fall-through, the `.const` arm and the `none`-if-unsized rule are unchanged.
`scatterImageBounds` (`Check.lean`) becomes a call to `affineImageBounds`. The oracle's `derivedShape`
calls `outExtent`. `Eval.Plan.ScatterGeometryTest` is added to the `Tests` globs.

- [ ] **Step 1:** `git apply --check` then `git apply` `T1-extent.patch`.
- [ ] **Step 2:** hash check the four T1-final paths (section 8 table, column "after Task 1").
- [ ] **Step 3:** full build in the background: `lake-build.sh <worktree>/leanncd LeanNCD Tests JaxExperiment`.
  Expected: `Build completed successfully` and no `error:` line (prototype saw 8841 jobs on the
  `LeanNCD Tests` targets; the section 8 count is for the final tree).
- [ ] **Step 4:** stage the seven paths and commit `feat(dsl): scatter geometry A, exact-reach extent for multi-axis slots`.

**Re-pinned guards** (each keeps its intent): `ScatterCheckTest`: `(affine 1 [(2,I),(1,J)]).outExtent`
11 becomes 9 (reach `1+2*2+1*3 = 8`); `scatterDestExtent #[3,2] #[2,-1] 1` 5 becomes 6; the B6 max-corner
off-by-one is no longer buildable through `checkScatter` (its extent clause forces the derived value), so
it is re-pinned directly at `scatterRangeViolation #[3,2] #[#[2,-1]] #[1] #[5] == some (0,0,5,5)`,
`#[6] == none`, and a min-corner `#[0] #[6] == some (0,-1,4,6)`. `SourceDifferentialScatterTest`: donors
`fD` snap 7 becomes 6 (cells `[1,12,123,234,340,400]`), `fN` snap 16 becomes 12; `conditionCount fF` 1
becomes 0 with a new twin `fFbig` (snap 7, declared too big, keeps `== 1`).

**Observed values** (`ScatterCheckTest` direct `outExtent`, sizes `i:3 j:4 k:2`): `i+j` 6; `i+j+3` 9;
`4i+j` 12; `i+j+k` 7; `i+j+i` 8 (densified `2i+j`); `2i-j+3` 8 (legacy 5); `i-j` 3; `-i-j` 1; zero-size `i`:
`i+j` 4 and `-i+j` 4 (legacy kept; the second kills a missing guard, since a corner of an empty box adds a
spurious `+1`); unsized gives `none`. Controls unchanged: `2i` 6, `2i+3` 8, `0i+j` 4, `3+0i+0j` 3,
`.const 3` 4. `scatterImageBounds #[3,4] #[1,1] 0 == (0,5)`, `scatterDestExtent #[3,4] #[1,1] 0 == 6`,
`#[4,1]` gives 12. `ScatterGeometryTest` (hand-built `conv` = `S[a+b] := A[a]*B[b]` and `convWide` =
`a+4b`, `|a|=4`, `|b|=3`, `S` unpinned) pins reference shapes `[6]` and `[12]` and values
`[1,12,123,234,340,400]`, and, at this point only, that the checked leg STILL refuses with
`multiAxisScatterLhs` (Task 2 flips it).

**Manifest:** task `T1`, 9 entries (SGA-T1-01 to 09; 01-08 killed by `Eval.Plan.ScatterCheckTest`, 09 by
`Semantics.SourceDifferentialScatterTest`): `mutation-manifest.sh --task T1 --out <scratch>/t1.md
<worktree>/leanncd papers/semantics/additive_scatter_geometry_a_mutations_post.json`. Accept-neighbours:
the controls above. Note SGA-T1-04 is killed only by the `-i+j` empty-axis guard.
**Build effect:** re-pins `ScatterCheckTest` and `SourceDifferentialScatterTest`; adds
`ScatterGeometryTest`; the `Ast.lean` edit rebuilds nearly everything.
**STOP:** any guard failing outside those two modules and the new one means the blast radius differs from
P0: BLOCKED, report the failing guard list.

### Task 2: multi-axis admitted at top level (`T2-multi-axis.patch`)

**Files (4):** `leanncd/LeanNCD/Eval/Plan/Compile.lean`, `leanncd/test/Eval/Plan/CompileTest.lean`,
`leanncd/test/Eval/Plan/ScatterGeometryTest.lean`, `leanncd/test/Semantics/SourceDifferentialScatterTest.lean`.

**Behaviour.** The private `checkScatterAffineExpr` (`Compile.lean`) takes a first parameter
`multiAxisAdmitted : Bool`: the `.constant` arm still throws `scatterOrAffineLhs`; `.multiAxis` throws
`multiAxisScatterLhs` only when the flag is false. `checkScatterLHSSlot` (top level) passes `true`,
`checkScanScatterLHSSlot` passes `false`, so scan-local keeps both refusals. Doc comments updated; nothing else
in production changes (no `lowerArith`, `Collect`, kernel or plan edit).

- [ ] **Step 1:** check then apply `T2-multi-axis.patch`. **Step 2:** no final-blob checkpoint (all four paths
  change again in Task 3); instead confirm `rg -n "multiAxisAdmitted" leanncd/LeanNCD/Eval/Plan/Compile.lean` hits.
- [ ] **Step 3:** targeted build in the background:
  `lake-build.sh <worktree>/leanncd Eval.Plan.CompileTest Eval.Plan.ScatterGeometryTest Semantics.SourceDifferentialScatterTest`.
  **Step 4:** commit `feat(plan): scatter geometry A, checked backend admits multi-axis scatter at top level`.

**Observed values.** Differential tags: `fD` (scatter `a+b`, `|k|=6`), `fF` (assign `a+b`, 6), `fF'` (`a+4b`,
12), `fN` (scatter `a+4b`, 12) all `parity`; `fD'` (constant slot) and `fOriginC` still `nativeFailure`
(Task 3 flips them); `fFbig` (declared 7, reach 6) is `known:extent` (both native legs publish `[6]`
against the oracle `[7]`), by design: production does not box a multi-axis single writer and
`declaredShapeWins` excludes it. `fSign` (`a-b`, `|k|=4`) is `refused:writeOutOfRange`; `fSignOk` (`a-b+2`,
6) is `parity`, cells `[100,210,321,432,43,4]`. Checked cells for `fF`: shape `[6]`,
`[1,12,123,234,340,400]`; for `fF'`: shape `[12]`, `[1,2,3,4,10,20,30,40,100,200,300,400]`.
`ScatterGeometryTest` (inputs `A=[1,2,3,4]`, `B=[1,10,100]`): plan fields
`(outCoeffs, outBias, destShape, compute.outputShape)` = `(#[#[1,1]], #[0], #[6], #[4,3])` for `conv`
and `(#[#[1,4]], #[0], #[12], #[4,3])` for `convWide`; `agree` (reference == checked f64 == checked f32
bit for bit) for `conv` `[1,12,123,234,340,400]`, `convWide` `[1,2,3,4,10,20,30,40,100,200,300,400]`,
cross-correlation `a-b+2` `[100,210,321,432,43,4]`, max-plus `agg max` `[2,11,101,102,103,104]`. B6,
mixed-sign `a-b` (reach -2..3, extent 4): reference error `scatterWriteOutOfRange "S" [-1] [0,1]`, checked
`.shape (.scatterImageOutOfRange "S" 0 (-2) 3 4)`. f32 (`A=[0.1,0.7,0.3,0.9]`, `B=[0.3,0.1,0.7]`): native
bits `#[1022739088, 1046562735, 1047233823, 1061830000, 1050253722, 1059145646]`, equal to the independent
binary32 twin; the narrowed binary64 answer differs in lanes 0, 1, 3 and is pinned as a carrier
discriminator. Constant slot still refused at this point (`prepCause` is `scatterOrAffineLhs "S: constant affine LHS slot"`).
Multi-writer with a multi-axis writer: `sourceError convTwo == some (.multiWriterScatter "S")`. Boxed single
multi-axis writer (`k` pinned 8) keeps the derived shape on all three legs, `(some [6], some [6], some [6])`,
and `B5cSingleBoxTest.groupsOf convBoxed == []`. `routeError conv == none`. In `CompileTest` the multi-axis
preflight pin flips to `isOk`, and the predicate-declaration donor "fixture 11" is re-donored from the two-axis
slot to a constant-slot scatter `Out[3]` (still `scatterOrAffineLhs "Out: constant affine LHS slot"`).

**Manifest:** task `T2`, 7 entries (SGA-T2-01 to 07): `--task T2 --out <scratch>/t2.md ...`. Killers:
01-03 `Eval.Plan.CompileTest`, 04 `Eval.Plan.B5BoundaryTest`, 05 `Eval.Plan.B5cSingleBoxTest`, 06
`Eval.Plan.B5NativeTest`, 07 `Semantics.SourceDifferentialScatterTest`. Accept-neighbours: the scan-local
pins in `CompileTest` and the existing `B5BoundaryTest.twoAxes`.
**Caveat (parked, section 2):** `ScatterGeometryTest` imports `B5cSingleBoxTest`, which imports
`B5BoundaryTest` and `B5NativeTest`; for 04-06 the older pin fails first and Lake never builds the new
module, so the manifest `expect` strings name the older module and the new `convTwo`, `convBoxed` and B6
pins are not independently shown live.
**Build effect:** re-pins `CompileTest` and `SourceDifferentialScatterTest`, extends `ScatterGeometryTest`.
**STOP:** a failing module other than these three is BLOCKED (scan, route, B5 and JAX experimental must not move).

### Task 3: constant slot as a unit-axis placement (`T3a-constant.patch`, then `T3b-scan-const.patch`)

One task, two commits, in this order.

**Task 3a files (8):** `leanncd/LeanNCD/DSL/Ast.lean`, `leanncd/LeanNCD/DSL/Pipeline/Structural.lean`,
`leanncd/LeanNCD/Eval/Plan/Compile.lean`, `leanncd/LeanNCD/Exec/Uid.lean`,
`leanncd/test/DSL/Pipeline/StructuralTest.lean`, `leanncd/test/Eval/Plan/CompileTest.lean`,
`leanncd/test/Eval/Plan/ScatterGeometryTest.lean`, `leanncd/test/Semantics/SourceDifferentialScatterTest.lean`.

**Behaviour (3a).** `lowerConstSlots` (new, `Structural.lean`) rewrites every `.affine (.const n)` slot of a
scatter-shaped `.assign` and of a hand-built `.scatter` into `.affine (.affine n [(1, u)])` over a fresh
axis `u` (UID from `freshNonZero`, name `constUnitPrefix ++ toString uid`, i.e. `#const<uid>`) and appends
`Decl.axis u (some 1)` to the returned decls. A statement carrying an `iterAt`/`iterNext` slot is left
untouched. The `.assign` arm's unconditional `overlappingScatter` throw is deleted and `LHSSlot.collapses`
(its only user) is deleted. `constUnitPrefix`, `IdxExpr.isConstUnit` and `LHSSlot.boundedScatter`
(`Ast.lean`): `boundedScatter` answers false for the rewritten constant, which keeps groups
(`multiWriterScatter`) and boxed single writers (derived shape wins, `groupsOf == []`) exactly as before.
`scatterAffineClass` and the checked preflight are untouched: the rewritten slot is single-axis bounded, so
the top level admits it, and the raw `.constant` arm remains for hand-built bypass and the scan arm.
`CompileError.overlappingScatter` (`Exec/Uid.lean`) is kept. Marker choice: a name prefix, not a new
`IdxExpr` constructor (it would touch every exhaustive match) and not a `Decl` lookup (`boundedScatter` has no env).

- [ ] **3a Step 1:** check then apply `T3a-constant.patch`. **Step 2:** hash check the five paths in
  section 8 column "after Task 3a" (`Ast`, `Compile`, `CompileTest`, `ScatterGeometryTest`,
  `SourceDifferentialScatterTest`); `Structural`, `Uid`, `StructuralTest` are checked after 3b.
- [ ] **3a Step 3:** full build in the background (`Ast.lean` changed). **Step 4:** commit
  `feat(dsl): scatter geometry A, constant slot lowered to a unit-axis placement`.

**Observed values (3a).** `S[3] := A[a]` on the `.scatter` and the `.assign` arm: reference == checked f64
== checked f32, shape `[4]`, cells `[0,0,0,10]`; plan fields `(#[#[1,0]], #[3], #[4], #[1,4])` (columns `[u, a]`);
`scheduled.decls` gains exactly one entry, `.axis "#const4" (some 1)`. `S[a,3] := A[a]` (dst `[a,k]`): `[4,4]`,
column 3 equals `A`. `S[3,4] := A[a]`: `[4,5]`, one nonzero cell (index 19) = 10, plan
`(#[#[1,0,0],#[0,1,0]], #[3,4], #[4,5], #[1,1,4])`. `S[3] := A[a]*B[b]`: `[0,0,0,1110]`. `S[0]`: `[1]`, `[10]`;
`S[0]` with `agg max`: `[4]`; `S[3]` with `agg max`: `[-inf,-inf,-inf,4]` on all three legs. f32
(`A=[2^24,1,1,1]`): native bits `[0,0,0,1266679808]` equal to the independent twin; narrowed binary64
`[0,0,0,1266679810]`. Boxed single (`k` pinned 8), both arms: `(some [4], some [4], some [4])`,
`groupsOf == []`. Multi-writer: `multiWriterScatter "S"` on all three legs (pairs of `.scatter`, pairs of
`.assign`, constant plus `conv`, both orders). `routeError` none on both arms. `EvalWarning` count 0. Bypass:
a raw constant handed straight to `prepareEvalPlan` is refused with `scatterOrAffineLhs "S: constant affine
LHS slot"`. Differential: `tag fD'` `parity` (cells `[0,0,0,10]`); `fI1`, `fI2`, `fMask` (declared larger than
`n+1`) now `known:extent`, the same class as `fFbig` and the residual slice B closes (before 3a they were
`nativeFailure` via `overlappingScatter`); `fOriginC` `parity`, no `scatterOrAffineLhs` in its report.
`StructuralTest`: the collapsing-constant pin is re-pinned to the lowering, plus a scan-slot-untouched pin.

**Task 3b files (3):** `leanncd/LeanNCD/DSL/Pipeline/Structural.lean`, `leanncd/LeanNCD/Exec/Uid.lean`,
`leanncd/test/DSL/Pipeline/StructuralTest.lean`.

**Behaviour (3b), the fail-loud repair.** In `lowerArith`'s `.assign` arm, inside the scatter-shaped
branch, a statement with a scan slot (`LHSSlot.isScanSlot`) AND a raw constant slot (`LHSSlot.isRawConst`)
throws `CompileError.overlappingScatter nm`, exactly the pre-slice result for those programs. The hand-built
`.scatter` arm is unchanged (checked refuses; reference/legacy accept, F3 parked). `lowerConstSlots` now uses
`isScanSlot`. The `Uid.lean` comment says `overlappingScatter` has one producer again. The throw sits in
`lowerArith`, not in `lowerConstSlots`, because that function is shared with the `.scatter` arm.

- [ ] **3b Step 1:** check then apply `T3b-scan-const.patch`. **Step 2:** hash check `Structural`, `Uid`,
  `StructuralTest` (section 8 column "after Task 3b"). **Step 3:** targeted build in the background:
  `lake-build.sh <worktree>/leanncd DSL.Pipeline.StructuralTest`. **Step 4:** commit
  `fix(dsl): scatter geometry A, keep the constant-slot guard for scan statements`.

**Observed values (3b).** `StructuralTest`: the scan-slot pin now uses a non-constant slot (`.scale 2 j` next
to `.iterAt l 0`), asserting slots and decls untouched; `lowerArith` of `.assign "S" [.iterAt l 0, .affine
(.const 3)]` gives `.error (.overlappingScatter "S")`; whole-pipeline `scanSurfaceConst` (the surface scan
program `iter l = 3`, `S[i, 0] := X[i]`, `S[i, l + 1] := S[i, l]`, with the base statement's free slot replaced
by `.affine (.const 3)`) gives `compileToScheduled` = `overlappingScatter "S"`; the accept-neighbour
`scanSurface` (unmodified) compiles to a `ScanStmt.scan`; a hand-built `.scatter "S" [.iterAt l 0, .affine
(.const 3)]` keeps its raw constant with no synthetic decl (this pin exists because after 3b the `.assign`
arm throws first, so without it SGA-T3-09 would survive).

**Manifest:** task `T3`, 12 entries: SGA-T3-01 to 09 (killed by `Eval.Plan.ScatterGeometryTest` for 01-05 and
08; `Eval.Plan.B5BoundaryTest` for 06-07; `DSL.Pipeline.StructuralTest` for 09) and SGA-T3b-01 to 03 (all
`DSL.Pipeline.StructuralTest`): `--task T3 --out <scratch>/t3.md ...`. Accept-neighbours: `scanSurface`, the
non-scan constant pin that still lowers, `multiWriterScatter` pairs unchanged.
**Build effect:** 3a re-pins `StructuralTest`, `CompileTest` (comment only), `SourceDifferentialScatterTest`,
extends `ScatterGeometryTest`; 3b re-pins `StructuralTest` only.
**STOP:** if `multiWriterScatter "S"` changes for any pair, or a boxed single constant stops reporting
`groupsOf == []`, the marker is broken: BLOCKED. If a scan-local constant program compiles, 3b is missing.

### Task 4: four-leg tropical fixtures (`T4-tropical-fixtures.patch`)

Shipped as a patch (the earlier executor brief
[additive_scatter_geometry_tropical_fixture_brief.md](additive_scatter_geometry_tropical_fixture_brief.md)
is SUPERSEDED: do not follow it, in particular not its three-commit work-item structure or its by-hand mutation
checks; its precondition about where the `overlappingScatter` throw sits is stale, see the record).

**Files (1):** `leanncd/test/Semantics/SourceSortedDifferentialTest.lean`. No production change.

**Behaviour.** New axes `o6`, `o13`, `o4` (uids 10, 11, 12), `snapG` (a copy of `snap` with a destination axis
of declared extent `n`; `snap` untouched), rows `conv` (`Y[a+b]`, extent 6), `conv23` (`Y[2a+3b]`, extent 13),
`constSc` and `constAs` (`Y[3]` as `.scatter` and as `.assign`, extent 4), each for `.max` and `.min`,
asserting `yCore` (the Core leg's `Y` cells) and `classOf` with `#guard_msgs`. No existing row is edited. Do not
use `compareSource` (it refuses `max`/`min` as `nonSum`).

- [ ] **Step 1:** check then apply. **Step 2:** hash check `SourceSortedDifferentialTest` (section 8).
- [ ] **Step 3:** targeted build in the background: `lake-build.sh <worktree>/leanncd
  Semantics.SourceSortedDifferentialTest`. **Step 4:** commit
  `test(oracle): scatter geometry A, four-leg tropical rows for multi-axis and constant slots`.

**Observed values** (all four legs report `fourLegParity`; equal the brief's hand cross-checks): `conv` max
`[2, 11, 101, 102, 103, 104]`, min `[2, 3, 4, 5, 14, 104]` (inputs `X=[1,2,3,4]`, `W=[1,10,100]`); `conv23` max
`[2, -inf, 3, 11, 4, 12, 101, 13, 102, 14, 103, -inf, 104]`, min `[2, +inf, 3, 11, 4, 12, 5, 13, 102, 14, 103,
+inf, 104]` (empty fibres at cells 1 and 11); `constSc` and `constAs` identical: max `[-inf, -inf, -inf, 4]`,
min `[+inf, +inf, +inf, 1]`. Whether these rows are non-tautological (max-plus against max-times at cell 1) is
review lens (b)'s question; the ledger recorded only the max-plus values above.

**Manifest:** task `T4`, 3 entries (SGA-T4-01 outExtent multi-axis arm back to the legacy sum; 02 top-level
`checkScatterLHSSlot` refuses multi-axis again; 03 constant placement bias `n + 1`), all killed by
`Semantics.SourceSortedDifferentialTest` via the `classOf` rows (the `yCore` rows read the Core leg, which
these production changes do not touch); expect strings `error: test/Semantics/SourceSortedDifferentialTest.lean:`
plus ``Docstring on `#guard_msgs` does not match generated message:``, no line numbers: `--task T4 --out
<scratch>/t4.md ...`. Accept-neighbours: the existing `collide` and `strided` rows, untouched.
**Build effect:** only `Semantics.SourceSortedDifferentialTest` changes.
**STOP:** an observed value differing from the lists above is BLOCKED (report both, edit neither).

### Task 5: live docs (`T5-docs.patch`)

**Files (7):** `leanncd/LeanNCD/DSL/AGENTS.md` (new Pitfall), `leanncd/LeanNCD/Eval/AGENTS.md`,
`leanncd/LeanNCD/Eval/Plan/AGENTS.md`, `leanncd/LeanNCD/Eval/Plan/Error.lean` (doc comment of
`multiAxisScatterLhs` only), `leanncd/LeanNCD/Semantics/AGENTS.md`, `papers/backend_missing_functionality.md`,
`papers/scatter_affine_lhs_writes.md`. Live docs and doc comments only; no behaviour.

- [ ] **Step 1:** check then apply; hash check the seven paths. **Step 2:** `git diff --check`; every relative
  link in the two edited papers resolves (`ls` them).
- [ ] **Step 3:** run the section 8 value-grep gates as commands and record each result in the record.
- [ ] **Step 4:** full build in the background (`Error.lean` doc comment changed); commit
  `docs(leanncd): scatter geometry A, live nodes and papers describe the exact-reach extent and constant lowering`.

**Ledger facts.** Stale claims before the edit: 6 (`Eval/Plan/AGENTS.md`, `Eval/AGENTS.md`, `Semantics/AGENTS.md`,
the `Error.lean` doc, and the two papers); after: 0. The `DSL/AGENTS.md` Pitfalls section stays under 3000
characters. Not edited because already current: `Ast.lean`, `Structural.lean`, `Compile.lean`, `Uid.lean`.
**Build effect:** none beyond rebuilding `Error.lean` dependents.

## 6. Recurring-defect audit (case x class)

The defect family: a geometry rule stated in one place and silently ignored in a sibling. Siblings a diff
cannot show: `scatterAffineClass`, `LHSSlot.boundedScatter`, `checkScatterAffineExpr`, `checkScatterLHSSlot`,
`checkScanScatterLHSSlot`, `slotsBecomeScatter`, the oracle's `derivedShape` and `declaredShapeWins`,
`boxedSingleGroups`, `checkWriterGroup`. Cell = what the code does after this slice, then class: R required
and pinned, F forbidden and pinned, **S** silently ignored (no pin or no diagnostic).

| slot class | top-level single | multi-writer group | boxed single (pinned decl) | scan-local |
| --- | --- | --- | --- | --- |
| single-axis strided (`2*i`, `i+2`) | scatter, stride-aligned extent: R | admitted: R (B5 tests) | collected unless D5: R (B5c) | admitted by `checkScanScatterLHSSlot`: R |
| multi-axis (`a+b`) | admitted since Task 2, exact reach: R (`ScatterGeometryTest`, tropical rows) | `multiWriterScatter`: F (`B5BoundaryTest.twoAxes`, `convTwo`) | not collected, derived shape wins: R as pinned (`convBoxed`, `multiAxisOne`); **S** as a diagnostic (oracle shows `known:extent`) | `multiAxisScatterLhs` for checked: F; **S**: reference/legacy accept and overwrite (F3) |
| constant (`Y[3]`, hand-built `.affine (.const n)`) | lowered to a unit-axis placement, extent `n+1`: R (both arms) | `multiWriterScatter` via `isConstUnit`: F (all pairs) | not collected, derived `n+1` wins, pinned on three legs: R; **S** as a diagnostic (`known:extent` for `fI1`, `fI2`, `fMask`) | `.assign` with scan slot: `overlappingScatter`: F (`StructuralTest`); hand-built `.scatter`: checked refuses, reference/legacy overwrite: **S** (F3) |
| zero-coefficient (`0*i`, `0*i+5`) | bounded, every write out of range: B6 error on both backends: R | admitted: R (`zeroScale`) | collected: **S** (not separately pinned) | slot admitted, whole scan refused: R (`s6ZeroBase`, `scanWriteRowNotAdmitted`) |
| diagonal (`Y[i,i]`) | scatter, no `.affine` slot consulted: R (`diagonal`) | admitted: R | D5 excludes the repeated free slot: R (`identityOne`, `transposeOne`) | **S**: no pin for a diagonal scatter inside a scan |
| free (`Y[i]`) | plain assign: R | bare groups: R | one-writer group: R | plain: R |

Every **S** cell has an owner:

| Silently ignored cell | Owner | Cost |
| --- | --- | --- |
| pinned declaration ignored for a boxed single multi-axis or constant writer (derived shape, no diagnostic) | slice B (`boundedScatter` stops gating) | inside B, about 1 dispatch |
| scan-local multi-axis, and hand-built scan-local constant `.scatter`: reference/legacy overwrite | F3 | about 1 dispatch |
| diagonal scatter inside a scan, no pin | parked | 0.3 dispatch |
| zero-coefficient writer under a boxed declaration, no pin | parked | 0.3 dispatch |
| `declaredShapeWins` hand-mirrors `boxedSingleGroups`; `isConstUnit` unmarks with it | slice B (shared predicate optional) | about 0.5 dispatch |
| new-module pins not independently mutation-checked | parked | 0.3 dispatch |
| stale `LHSSlot.collapses` comment in `ScatterCompileTest` | parked | 0.1 dispatch |

## 7. Review focus

Two lenses, separate contexts, each given `git diff <base>..<branch head>` plus sections 3 and 6 of this plan,
each appending findings to its own file as it goes (not at the end):

- **(a) Acceptance and correctness**, file `papers/semantics/additive_scatter_geometry_a_review_acceptance.md`.
  Does any accepted program change shape or value except hand-built multi-axis scatters under M1? Does any
  previously refused program now run wrongly (the widened mixed-sign case, a constant in a scan, a constant
  in a group)? Scan-local refusals intact (`overlappingScatter`, `multiAxisScatterLhs`, `scatterOrAffineLhs`)?
  Does the `isConstUnit` marker keep groups and boxed single writers unchanged? Is `lowerConstSlots` skipped
  for exactly the scan statements?
- **(b) Oracle independence**, file `papers/semantics/additive_scatter_geometry_a_review_oracle.md`. Do
  `derivedShape` and `declaredShapeWins` agree with production, now that `derivedShape` calls `outExtent`
  (is that independence loss acceptable, and does `fFbig` still catch a divergence)? Are the four-leg tropical rows
  non-tautological (max-plus differs from max-times at cell 1 of `conv`)? Is each silently-ignored cell in
  section 6 real and correctly owned?

Each finding gets a verdict (fix now, park with cost, reject with reason) in the record.

## 8. Verification gates and exact values

- **Blob hashes** (Git blob IDs as `git hash-object` prints them). A path changed by several tasks is only
  checkable after its last owning task. Task 2 has no checkpoint. Tree hashes are not used: the executor's
  base also carries this plan, so trees differ.

  | Path | blob | check after |
  | --- | --- | --- |
  | `leanncd/LeanNCD/Eval/Plan/Check.lean` | `ad4b61ebef7757f74cc7a7e0ec84374d9454b89b` | Task 1 |
  | `leanncd/LeanNCD/Semantics/Source/Differential.lean` | `66a88a8d0831c8d43037ec948b9f07d53f4d97c0` | Task 1 |
  | `leanncd/lakefile.toml` | `235b03c2e9e0016f413cc7598a223af664fd30c3` | Task 1 |
  | `leanncd/test/Eval/Plan/ScatterCheckTest.lean` | `4697dc7211d4cfb74594d193e788c4533c6d8572` | Task 1 |
  | `leanncd/LeanNCD/DSL/Ast.lean` | `e804a5b3ed927b93a1f4923f6a28002711364e16` | Task 3a |
  | `leanncd/LeanNCD/Eval/Plan/Compile.lean` | `fc821872cd2ae77163327f7a98572d2ea64edb02` | Task 3a |
  | `leanncd/test/Eval/Plan/CompileTest.lean` | `222b2ce10f58f289bc4f40289439984cd4c9acbd` | Task 3a |
  | `leanncd/test/Eval/Plan/ScatterGeometryTest.lean` | `920f35a4714e171c0134ee92519664281ccc64c1` | Task 3a |
  | `leanncd/test/Semantics/SourceDifferentialScatterTest.lean` | `42a3c0d9ae5b4ce6bed27f7e1eafb00310148569` | Task 3a |
  | `leanncd/LeanNCD/DSL/Pipeline/Structural.lean` | `769135b75a17a9a417f31236c8d7acca203e1d27` | Task 3b |
  | `leanncd/LeanNCD/Exec/Uid.lean` | `637fbafd007c00a6270ebf954ba22349a842d7a7` | Task 3b |
  | `leanncd/test/DSL/Pipeline/StructuralTest.lean` | `1e419a9e34b755cfb836feadef78b76871222b43` | Task 3b |
  | `leanncd/test/Semantics/SourceSortedDifferentialTest.lean` | `1fcc04a76b7f01e927c91f7a9bd89dd828de7f70` | Task 4 |
  | `leanncd/LeanNCD/DSL/AGENTS.md` | `077d2170e8a4f38ad9a9c5924102f51e9efbfd01` | Task 5 |
  | `leanncd/LeanNCD/Eval/AGENTS.md` | `5636792eb0aef0a4a38a01e80a8ef4f3ce9241e4` | Task 5 |
  | `leanncd/LeanNCD/Eval/Plan/AGENTS.md` | `91affebe90de89f1343e3603da0cd2c514246a7d` | Task 5 |
  | `leanncd/LeanNCD/Eval/Plan/Error.lean` | `0701c926a9c7784bbbd092870bc270c0578bac32` | Task 5 |
  | `leanncd/LeanNCD/Semantics/AGENTS.md` | `d9c750e5c85e24e63ca6e0fc772e981fa20761ba` | Task 5 |
  | `papers/backend_missing_functionality.md` | `1bfd3c037e98d9baeed7ff25f594cbb6c899da76` | Task 5 |
  | `papers/scatter_affine_lhs_writes.md` | `c6a13747e5136c6572cbdaa270644be3087e10f9` | Task 5 |

- **Final build.** `lake-build.sh <worktree>/leanncd LeanNCD Tests JaxExperiment` expects
  `Build completed successfully (8843 jobs)`. The count can drift by a few if main moved; any failure is BLOCKED.
- **Manifest.** `--check` unfiltered expects 31 entries, every old-string unique; then
  `--task T1` 9/9, `--task T2` 7/7, `--task T3` 12/12, `--task T4` 3/3, all killed, each mutated file restored
  byte-identically and each restored build green (run `git status` after each task run). Observed at replay:
  31 of 31. If a verdict is FAIL do not edit the manifest: it means a patch or hash differs from the
  prototype. Where an entry's `expect` names an older module (T2-04 to 06, T3-06 and 07), that is correct
  (section 5 Task 2 caveat).
- **Diff size.** `git diff --stat <base>..HEAD` over the six commits touches 20 paths (6 test files,
  7 `.lean` files under `leanncd/LeanNCD`, 4 `AGENTS.md` nodes, `lakefile.toml`, 2 papers; the table above is
  the list). A different count is a finding.
- **Value-grep gates** (run in the worktree root, record counts):
  `rg -n "multiAxisScatterLhs|scatterOrAffineLhs" leanncd/LeanNCD papers/backend_missing_functionality.md papers/scatter_affine_lhs_writes.md`,
  `rg -n "overlappingScatter" leanncd/LeanNCD papers/backend_missing_functionality.md papers/scatter_affine_lhs_writes.md`,
  `rg -n "legacy linear|collapses" leanncd/LeanNCD papers/backend_missing_functionality.md papers/scatter_affine_lhs_writes.md`,
  `rg -n "derives 7|derives 16|extent 7|extent 16" leanncd/LeanNCD leanncd/test papers/backend_missing_functionality.md papers/scatter_affine_lhs_writes.md`.
  Rule: every remaining hit in live docs must be correct under the new rules or marked history.
  Known correct at authoring: `legacy linear` in the `Ast.lean` doc of the fall-through (every other affine form
  keeps the legacy boundary) and one `B5NativeTest` comment; `collapses` hits that are unrelated English
  (`DSL/Compile.lean`, `Compile.lean`, test files) except the parked `ScatterCompileTest` comment naming
  `LHSSlot.collapses`; `extent 7` in `ScatterCheckTest` (`i+j+k`, correct under M1) and `SourceSortedAuditTest`
  (unrelated `k`). Any new `derives 7` or `derives 16` is a stale claim.
- **No line numbers shipped.** `rg -n "^\+.*[A-Za-z]+\.lean:[0-9]+" papers/semantics/additive_scatter_geometry_a_patches`
  must report nothing (the added lines of all six patches; checked at authoring), and the same pattern over this
  slice's added documentation lines in the executed diff (`git diff <base>..HEAD -- '*.md'`) must be empty.

## 9. Close-out record (executor writes `papers/semantics/additive_scatter_geometry_a_record.md`)

Required fields, each from a real run: base and final commit hashes and the six commit hashes; per-task
`git apply --check` results; the section 8 hash table result; per-task build results and the final job count;
mutation table (31 lines with killer module, restore results); the section 4 and 5 values re-observed on the
executed tree; review findings and adjudication; the value-grep gate outputs; **measured token total from the
executor's own usage telemetry, naming the method** (this is not Claude Code), against the Rule 6 slice-execution
ceiling of about 175M and the design note's per-slice guess of about 35M, with any overrun explained; every
skipped step; parked items carried forward with cost (section 2 and 6 lists plus new review findings).

## 10. Authoring evidence

Patches, manifest, verification record and ledger live under `papers/semantics/`:
`additive_scatter_geometry_a_patches/` (six patches), `additive_scatter_geometry_a_mutations_post.json` (31
entries, tasks T1-T4), `additive_scatter_geometry_a_verification.md` (base sha, commit and tree table, blob
table, mutation table), `additive_scatter_geometry_a_files/proto_notes.md` (prototype ledger copy: observed
values, case x class tables, decisions, parked items). Base `6715e1280961b87423b3daa85942ce26113f7507`; replay
code head `ef48df69ad258640d3caefde5e8808b2f9648ebd` (replay branch tip `ef02e256`, which adds the verification
artifacts); prototype head `e5bb6b3c`. Verified by the replay controller: apply, 20-path blob equality, the
8843-job build, 31/31 manifest. Verified at authoring (this plan's author): every cited identifier and path
exists in the replay tree (record lists the checks). Not verified: any review lens, per-task builds on the
replay, authoring token cost. Decisions made without the owner (check them): the Task 3 split into two commits
with the scan pin folded into 3b; the module `ScatterGeometryTest` shipping in Task 1 (the patch that adds its
lakefile glob) rather than Task 2; building the Task 2, 3b and 4 steps with targeted builds and the others with the
full build.
