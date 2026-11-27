# Step-Aware `where` Masks (Lean side) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. The plan is executed by Claude agents; each task names its model. Process path: FULL (new capability, changes the plan IR, a soundness-adjacent guard), executed patch-first because the code was prototyped and verified.

**Goal:** Inside a scan, a `where` mask in a recurrence body (a state step statement or a per-step intermediate) sees the LIVE scan coordinate(s), on the source guard, the reference evaluator, the checked plan, the dense workers (binary64 and binary32) and the unrolled differential; the JAX renderer refuses such plans loudly until the next slice.

**Architecture:** One new `RawAxiswisePlan` field `maskContextRank : Nat := 0` (mask leaf width `shape.size + maskContextRank`, context coordinates appended after the tensor coordinates in block-context order), set only when a step mask mentions an iteration axis of its own scan. `runDenseBlockWith` already receives `ctx`; the axiswise worker now takes it. The reference evaluator already holds the live coordinates in `seed`; its mask environment now includes them for STEP statements only. Verified code ships as two patches generated from the prototype branch `proto-step-mask`: `0001` production, `0002` tests.

**Tech Stack:** Lean 4 (`leanncd`), lake targets `LeanNCD`, `Tests`, `JaxExperiment`, `IndexedExecutionExperiment`; `mutation-manifest.sh`.

**Spec:** `papers/semantics/jax_step_mask_scope.md` (sites, policy conflicts, owner decisions) and the prototype record `papers/step_mask_files/proto_report.md`, `proto_report2.md` (observed facts), `patches/`, `expected_step_mask.py` (independent expected values). Read the two reports before executing; they say what was observed and what was not.

## Global Constraints

- Owner decisions (2026-11-26): (1) step masks only, the `Kh[k, s]` causality proof is out of scope; (2) the Slice 5.3 policy "a mask over a seeded scan axis reads coordinate 0" is REVERSED for step statements and per-step intermediates; (3) a mask over a BASE statement's pinned scan axis stays REFUSED at the source (`maskBaseAtZero`, `maskBaseAtOne`); contracted and unbound mask axes stay refused (`maskContractedAxis`, `maskUnboundAxis`); post-scan statements and an EARLIER scan's axis as a free state axis behave exactly as today; (4) IR = explicit field `maskContextRank : Nat := 0`.
- Exact names: `RawAxiswisePlan.maskContextRank`, `NonlinPlanError.maskContextRankMismatch (contextRank actual : Nat)`, `JaxCodegenError.axiswiseContextMask (nodeIndex maskContextRank : Nat)`, workers `runDenseAxiswiseAt` / `runDenseAxiswiseAt32` (the old `runDenseAxiswise` / `runDenseAxiswise32` stay as wrappers passing no context).
- Exact counts: `lake-build.sh <wt>/leanncd Tests JaxExperiment` = **8846 jobs**, no new Lean module; library `LeanNCD` = 8615 jobs; `JaxExperiment` = 8526 jobs.
- Existing JAX output is UNCHANGED: the generated `generated_evalplan_nonlin_smoke64.py` and `...32.py` are byte-identical before and after (the gate of T3), and the nonlin runner stays 65 binary64 / 56 binary32 (confirmation only).
- Not done here, owned by the NEXT slice (JAX, plan written after this one lands): stacked step-major include tables in `buildAxiswiseInclude` and the Python runtime, lifting `axiswiseContextMask`, the `kv_cache` natural-spelling and sliding-window FIXTURES on JAX, and the `checkJaxScanSupport` gate check (the support gate in `Executable.lean` currently ADMITS a step-aware axiswise node and only the renderer refuses it: loud, not wrong, parked).
- Not done at all: step masks in base blocks; causality proof for `Kh[k, s]`; the independent unroller on the per-step-intermediate program (see Parked).
- Execution budget (CLAUDE.md Rule 6): each dispatch at most about 60 harness-counted tool calls and 250k context; the harness count, not the agent's own count, is what is reported. Breaches are said, not hidden.
- Commits: end with `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`; never commit `.claude/settings*.json`; do not push; merge only at T3 by the controller (Rule 13).

## Build-Time Budget (the owner's constraint: builds have made recent slices very slow)

Measured on the prototype (wall seconds, `scripts/lake-build.sh`): targeted deepest module `LeanNCD.Eval.Plan.Nonlin` 29; library `LeanNCD` after the `Nonlin.lean` batch 348 (42 modules); `JaxExperiment` 44; ONE test module 33; targeted mutant builds 80-190 each; full cold `Tests` about 837 (it stops at failing modules and skips every importer of a failed one, so a green run costs at least that). Every lake call also costs 25-30 s before compiling anything.

Rules, applied in every task:
1. NO full `Tests` build until the end of T2b. Intermediate checks are targeted module builds, several modules per `lake-build.sh` call, in import order.
2. ALL edits to a `.lean` file, comments included, happen BEFORE the build that must cover that file. A comment edit after a build costs a rebuild of everything downstream (production files: the whole test suite). So prose-only edits (markdown, AGENTS.md) go to T3; Lean comment edits go inside T1 and T2 before their builds.
3. Long builds run with `run_in_background` and output to a file; wait for the notification or an `until grep` loop on the log; never poll turn by turn.
4. Mutants run once, from the manifest, each against the ONE test module that should kill it (never `Tests`).
5. The final replay runs three independent jobs in three worktrees in parallel (T3).
6. Never two lake invocations in the same worktree at once.

Expected total build wall time for the whole slice, [judgment from the measured numbers]: T1 about 7 min, T2 about 4 min, T2b about 3 min, one cold `Tests` about 14 min, manifest about 20 min (mutate+build+restore+rebuild per entry), parallel replay overlapping it. Roughly 45-60 minutes, against repeated 8846-job rebuilds per task in earlier slices.

## Model Assignment

| Work | Model | Why |
|---|---|---|
| T0 setup, T3 replay and merge | controller (this session) | worktrees, background builds, merge are controller duties |
| T1 apply patch 0001, comment edits, builds, commit | Sonnet 5.5 (high) | mechanical and verified; the risk is not applying it exactly |
| T1 production review | **Opus 5.5 (high)**, read-only | IR/guard/semantics: the only place a design flaw can hide; reads diff + case x class table |
| T2 apply patch 0002, comment edits, targeted builds, commit | Sonnet 5.5 (high) | mechanical and verified |
| T2b two NEW pins (multi-axis context order; earlier-scan axis) | **Opus 5.5 (high)** | not prototyped; needs semantic reasoning and independent values |
| T3 docs sweep | Sonnet 5.5 (high) | commands and value-grep |
| Final whole-branch review | **two Opus 5.5 (high) reviewers**, different lenses | soundness-adjacent: (a) wrongly accepts or misreads a mask, (b) breaks an existing program or fixture |

## Review Focus

Failure modes the spec implies that the prototype's tests do not exercise, most likely first; each is owned by a task below.
1. **Multi-axis scans.** The context order is block-context order `[r, c]`; every prototype pin uses ONE scan axis, so a swapped order is undetected today. Pin: T2b-A.
2. **A mask over an EARLIER scan's axis in a later scan's step** (`maskOtherScanAxisFree`) is a free state axis, must stay rank 0 and read its real coordinate; only the source guard is pinned today. Pin: T2b-B.
3. **A step mask that mentions only output axes** must stay rank 0 and produce byte-identical plans (stage 1 found its first version broke `ScanAffineEmitTest` here). Pin: the existing JAX fixtures plus the byte-identical gate of T3.
4. **The JAX support gate admits what the renderer refuses.** Pinned at the renderer (`axiswiseContextMask`, T2); the gate is the next slice's.
5. **Hand-built plans with a wrong rank** (block rank neither 0 nor `contextShape.size`; top-level rank > 0) must refuse with `maskContextRankMismatch`. Pinned in T2 at `checkPlanBlock` and `checkAxiswise` (top level through `prepareEvalPlan` is unreachable from source).

## File Structure

Production (patch 0001): `leanncd/LeanNCD/Eval/Plan/Nonlin.lean` (field, error, check, `axiswiseIncluded`, workers), `.../Plan/Block.lean`, `.../Plan/Compile.lean` (`lowerMaskPredicate` extra basis, scan-step arm), `leanncd/LeanNCD/DSL/Pipeline/Structural.lean` (`finalizeScans` guard), `leanncd/LeanNCD/Eval/Nonlin.lean` and `.../Eval/Scan.lean` (reference mask environment), `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean` (`axiswiseContextMask`). Plus comment-only edits listed in T1 (`.../Exec/Uid.lean` too).
Tests (patch 0002): `leanncd/test/DSL/Pipeline/StructuralTest.lean`, `.../Eval/Plan/ScanCompileTest.lean`, `.../Eval/Plan/NonlinCompileTest.lean`, `.../Eval/PropertyOracle/ScanUnroll.lean`, `.../Eval/Plan/DifferentialTest.lean`, `leanncd/experiments/jax_bridge/ScanAffineEmitTest.lean` (the JAX refusal pin lives there because only `JaxExperiment` imports the renderer).
Plan package (already committed with this plan): `papers/step_mask_files/` (reports, patches, `expected_step_mask.py`), `papers/step_mask_mutations_post.json` (5 mutants, `--check` validated against the patched tree).
Close-out (T3): `papers/step_mask_record.md`, docs listed in T3.

---

### Task 0: Worktree (controller)

- [ ] **Step 1:** `EnterWorktree` (name `step-mask`), then `bash .claude/skills/new-slice/prepare-worktree.sh`. The result must say "Worktree ready". Record `<wt>` and the base SHA (`git -C <wt> log --oneline -1`); it must contain the plan-package commit (`ls <wt>/papers/step_mask_files/patches` shows two patches).
- [ ] **Step 2:** `git -C <wt> apply --check <wt>/papers/step_mask_files/patches/0001-feat-plan-step-aware-axiswise-masks-Lean-side.patch` and the same for `0002-...` (both check against the clean tree; 0002 touches no file 0001 touches). Expected: no output.
- [ ] **Step 3:** Python env symlink only if the optional runner confirmation of T3 is wanted: `ln -s /Users/williammacready/code/python/pyncd.worktrees/task4-boolean-output/leanncd/experiments/jax_bridge/.cache/python <wt>/leanncd/experiments/jax_bridge/.cache/python` (create `.cache` first; never commit it).

### Task 1: Production batch (Sonnet 5.5 high, then Opus 5.5 high review)

**Files:** apply patch 0001; comment-only edits in `LeanNCD/Eval/Plan/Compile.lean`, `LeanNCD/Exec/Uid.lean`, `experiments/jax_bridge/EvalPlanCodegen.lean`.
**Interfaces:** Produces the names of Global Constraints; consumed by T2 (tests) and by the JAX slice.

- [ ] **Step 1:** `git -C <wt> apply <wt>/papers/step_mask_files/patches/0001-...patch` (worktree root; do not `git am`, do not edit the patch, do not "improve" it). Expected: `git diff --stat` shows 7 files, +134/-60 (production only, nothing under `test/`).
- [ ] **Step 2 (comment-only, BEFORE any build; identifiers, not line numbers):** (a) `lowerMaskPredicate` docstring neighbourhood in `Compile.lean`: it says "local non-seeded output basis, empty pins": add that the scan-step site appends the enclosing scan's iteration-axis uids (`contextUids`) after the output uids; (b) the `compileScan` STEP `.axiswise` arm comment ("Mask policy: local non-seeded output basis ...") in `Compile.lean`: now `outputUids ++ ctxUids`, rank set only when the mask mentions an iteration axis of this scan; the base-block and top-level comments stay (check wording only); (c) `CompileError.maskAxisNotOutput` comment in `LeanNCD/Exec/Uid.lean`: add "except the statement's own enclosing-scan axes in a recurrence body"; (d) the Slice 5.3 masked-axiswise note in `EvalPlanCodegen.lean`: add that rank > 0 is refused with `axiswiseContextMask`. No code change.
- [ ] **Step 3 (ONE library build, then ONE JaxExperiment build, each in the background):** `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd LeanNCD` then `... JaxExperiment`. Expected: `Build completed successfully (8615 jobs)` (about 6 min) and `(8526 jobs)` (about 1 min). A failure here is a STOP: report the first error, do not repair around it.
- [ ] **Step 4: Commit** `feat(plan): step-aware axiswise masks (Lean side)` (explicit paths, trailer line). `git -C <wt> status --short` empty.
- [ ] **Step 5 (Opus 5.5 high, read-only review, ~25 calls, writes findings to `<wt>/papers/step_mask_files/review_t1.md` as it goes):** open only the diff (`git -C <wt> show --stat HEAD`, then the six production files in 40-60 line windows) and `papers/step_mask_files/proto_report.md` sections (b), (c), (d). Verify, reporting VERIFIED or SUSPECTED per item: (i) the rank rule: a step mask gets `maskContextRank > 0` ONLY when it mentions an iteration axis of ITS OWN scan (not another scan's axis, not an output axis); (ii) the context coordinates are appended in the same order everywhere (`ctxUids` in `compileScan`, `ctx` passed by `runDenseScanWith`, `seed` order in the reference): read each site; (iii) every "silently ignored" cell of the case x class table is truly harmless for this slice (`checkScanCore` raw-step arms, `Executable.lean` arm); (iv) the guard in `finalizeScans`: which axes become visible for a state recurrence versus a per-step intermediate, and that base statements and post-scan statements are unchanged; (v) rank-0 behaviour is byte-identical in `axiswiseIncluded`/`axiswiseIncludedPredicate`. Severity per finding; do not fix anything. The controller adjudicates before T2.

### Task 2: Test batch (Sonnet 5.5 high)

**Files:** apply patch 0002; comment-only edits in `test/Eval/Plan/ScanCompileTest.lean`, `test/Eval/Plan/NonlinCompileTest.lean`, `test/DSL/Pipeline/StructuralTest.lean`.
**Interfaces:** Consumes T1's names. Produces the pins whose first failing messages are the manifest `expect` strings.

- [ ] **Step 1:** `git -C <wt> apply <wt>/papers/step_mask_files/patches/0002-...patch`. Expected: 6 files, +273/-46 (the 7th file of the prototype commit is `expected_step_mask.py`, already in `papers/step_mask_files/`), nothing under `LeanNCD/`.
- [ ] **Step 2 (comment-only, BEFORE any build):** the "local NON-SEEDED output basis, empty pins" headers of the Fixture 14-15 block in `ScanCompileTest.lean` and of the 1-D admission comment in `NonlinCompileTest.lean`: add the step-aware exception; the contracted/unbound comment in `StructuralTest.lean`: mark the coordinate-0 sentence as former behaviour. No code change.
- [ ] **Step 3 (targeted builds, two calls, import order):** `lake-build.sh <wt>/leanncd Eval.Plan.ScanCompileTest DSL.Pipeline.StructuralTest Eval.Plan.NonlinCompileTest Eval.PropertyOracle.ScanUnroll` (expected green, about 35-50 s), then `... Eval.Plan.DifferentialTest ScanAffineEmitTest` (expected green, about 40-55 s). The wall times go in the record.
- [ ] **Step 4: Verify the pins' observed values against the independent script:** `python3 <wt>/papers/step_mask_files/expected_step_mask.py` prints the tensors that `stepMaskInter`, `stepMaskStep`, `kvMaskCausal`, `kvMaskWindow` and the block pins assert; `seededAxisZero` is `[1,3,0.25,0.75,0,0]`; the block run is `[1,0,0]` at ctx 0 and `[0.2689414213699951, 0.7310585786300049, 0]` at ctx 1. A mismatch is a STOP.
- [ ] **Step 5: Commit** `test: step-aware mask pins and unrolled-differential flip`. Do NOT run the full `Tests` build here (T2b ends with it).

### Task 2b: Two new pins (Opus 5.5 high; NOT prototyped)

**Files:** Modify `test/Eval/Plan/ScanCompileTest.lean` (or `NonlinCompileTest.lean`, whichever holds the donor), extend `papers/step_mask_files/expected_step_mask.py`, extend `papers/step_mask_mutations_post.json` with M6.
**Rule:** if the source pipeline, the plan, the reference or the independent script REFUSES either program for a reason unrelated to the mask, STOP and report the exact error; do not change production code and do not shrink the pin to fit.

- [ ] **Step 1 (pin A, multi-axis context order):** donor: the two-axis scan machinery in `ScanCompileTest.lean` (`axR`, `axC`, `okBase2`/`okRecur2`, the `rej2` playground) or a source `tlprog!` with two `iter` axes of DIFFERENT extents. A step statement masked over BOTH scan axes asymmetrically (for example `where r <= c`, with extents chosen so that a swapped `(c, r)` order gives a different tensor). Expected values from a plain-Python simulation added to `expected_step_mask.py`; assert plan == reference == script through `diffEqB`; the pin must DIFFER under a swapped context order (state the swapped value in a comment).
- [ ] **Step 2 (pin B, earlier scan's axis):** donor: `maskOtherScanAxisFree` in `StructuralTest.lean`. Make it a runnable `diffEqB` program (small `H0`, `A`), expected from the script; it asserts that a mask over the EARLIER scan's axis `t` inside the later `l` scan reads the real `t` coordinate of that free state axis (and the plan carries rank 0 for that mask: check `maskContextRank` of the compiled axiswise step directly, or by the fact the JAX renderer still renders the program).
- [ ] **Step 3:** targeted build of the touched test module(s) only (one call, about 35-60 s); read the observed values; confirm against the script.
- [ ] **Step 4 (one extra mutant):** author manifest entry **M6** (`task` `T3`, file `LeanNCD/Eval/Plan/Compile.lean`, the multi-axis order: reverse the context uids INSIDE the step-site basis, targets = the module holding pin A, `expect` = the first failing message you OBSERVE by running it once with `mutation-manifest.sh <wt>/leanncd papers/step_mask_mutations_post.json "M6"`), then `mutation-manifest.sh --check` on the whole file (no filters) must pass.
- [ ] **Step 5: Commit** `test: multi-axis and earlier-scan-axis step mask pins`; then the controller starts the ONE cold full build in the background: `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests JaxExperiment` (expected `Build completed successfully (8846 jobs)`, about 14 min). Red or a changed job count is a STOP.

### Task 3: Docs, final replay, record, merge (controller; Sonnet 5.5 for the docs sweep)

- [ ] **Step 1 (docs sweep, no Lean file touched, so no rebuild):** edit exactly the prose items of `proto_report2.md` section (g) that are markdown: `LeanNCD/Eval/Plan/AGENTS.md` (`Nonlin.lean` row: `maskContextRank`, `maskContextRankMismatch`), `LeanNCD/DSL/AGENTS.md` (`finalizeScans` guard: step-scan-axes visibility), `papers/backend_missing_functionality.md` (mask lowering line), `papers/semantics/jax_scan_record.md` (the exclusions line, section 26's silent-wrong-answer and fix text get a dated correction pointer, the later "still fails `maskAxisNotOutput`" claim re-checked against the program it names), `papers/semantics/jax_step_mask_scope.md` (mark decisions taken and the Lean slice landed). The three historical session briefs (`jax_layers_time_session_brief.md`, `jax_kv_window_session_brief.md`, `jax_skew_fixtures_session_brief.md`) get ONE dated annotation line each, not a rewrite. Check AGENTS.md hook-injected sections stay under about 3k characters per edit.
- [ ] **Step 2 (verify the sweep with values, not vocabulary):** `rg -n "coordinate 0|reads 0|non-seeded output basis|Slice 5.3|maskOverScanAxis|seeded scan axis" leanncd papers` ; every remaining hit must be history already annotated or a sentence that is still true (base and top-level masks); list the survivors in the record.
- [ ] **Step 3 (final replay, three parallel jobs in three worktrees; each job runs one lake invocation at a time):** (A) in `<wt>`: `check-lean-drivers.sh` (expect "all eight drivers ran clean"), then the mutation manifest `bash <wt>/leanncd/scripts/mutation-manifest.sh <wt>/leanncd <wt>/papers/step_mask_mutations_post.json` (6 entries, about 20 min; every entry PASS; `git diff --stat` empty afterwards); (B) a second prepared worktree at the same tip: `lake-build.sh <wtB>/leanncd IndexedExecutionExperiment` (expect 8729 jobs, standard axioms only; it contains `IndexedAffineScanProfile`, which keeps the strict predicate; about 12 min); (C) the byte-identical gate: in the PRIMARY checkout (built at the base) and in `<wt>` run `/Users/williammacready/.elan/bin/lake +leanprover/lean4:v4.30.0 -d <leanncd> env lean --run <leanncd>/experiments/jax_bridge/EvalPlanNonlinSmoke.lean <out>/g64.py <out>/g32.py`, then `cmp` the two `g64.py` and the two `g32.py`; if they differ, first run the BASE generator twice and compare to rule out nondeterminism before concluding anything. Optional confirmation if the Python env is linked: `env -u PYTHON bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh` (expect 65 / 56 "fixtures within" lines).
- [ ] **Step 4 (final whole-branch review: two Opus 5.5 high reviewers in parallel, read-only, findings appended to `papers/step_mask_files/review_final_a.md` / `_b.md` as they go):** (a) WRONGLY ACCEPTS / MISREADS: the guard visibility rule, rank gating, context order, reference-vs-plan agreement, base statements; (b) BREAKS EXISTING: every pin and fixture that changed, byte-identical JAX output, the strict `stateReadCausal` untouched, the unrolled differential's other fixtures. Both receive the diff and `papers/step_mask_files/proto_report*.md`, not this plan's conclusions. Adjudicate findings; one fix dispatch per finding group, each given only its section.
- [ ] **Step 5 (record):** write `papers/step_mask_record.md`: measured wall time of every build and of each manifest entry, observed values, the counts, the review dispositions, harness-counted tool calls per dispatch, parked items. Then merge (Rule 13): `/usr/bin/git -C <primary> merge --no-ff <branch>`, re-run `lake-build.sh <primary>/leanncd Tests JaxExperiment` on the merged tree (expect 8846), confirm `git diff --stat main <branch>` is empty, remove the worktrees and branches, archive any executor logs. Do NOT push.

## Parked (with rough cost, not started)

| Item | Cost [judgment] |
|---|---|
| JAX slice: stacked step-major include tables (codegen + `_run_axiswise_node`/scan `stacked`), lift `axiswiseContextMask`, JAX fixtures: `kv_cache` natural spelling and sliding window, gate check in `checkJaxScanSupport` | its own Full plan, about 4-6 dispatches |
| `checkJaxScanSupport` admits a step-aware axiswise node (gate/renderer disagree) | one line + a pin, folded into the JAX slice |
| `Kh[k, s]` free-axis causality proof (mask-implies-causal), needs a second predicate at the two causality call sites and the `.axiswise` step in `checkScanCore`'s walk | 2-3 dispatches after this lands |
| The independent unroller fails on the per-step-intermediate program `Pa[j.] := softmax(where j <= l)(S[j, l])` (`output axis has no inferable size`); that program is pinned plan-vs-reference only; not checked whether it failed before the flip | about 1 dispatch audit |
| Base-block step-aware masks (base literal reads) | not wanted (owner decision 3) |
| Top-level rank > 0 pinned at `checkAxiswise`, not through `prepareEvalPlan` (unreachable from source) | none |

## Authoring Verification Record (what was observed, what was not)

Observed on the prototype branch `proto-step-mask` (2026-11-26): patch 0001 builds green at library and `JaxExperiment`; patch 0002 and 0001 together give a green `Tests JaxExperiment` (8846 jobs; warm run 61 s because targeted builds had compiled almost everything: the cold time is the 837 s measured in stage 1 for the failing run); both patches `git apply --check` clean on current `main`; the five mutants of the manifest each fail in their killer module with the quoted message and restore to an empty diff; `mutation-manifest.sh --check` passes on the patched tree; every pin value matches `expected_step_mask.py` except where a pin is Lean-only (see report 2 (b)). NOT observed: the two T2b pins and M6; multi-axis behaviour of any kind; the byte-identical gate; `IndexedExecutionExperiment` on this change; the Python runner on this change; a cold full `Tests` run after patch 0002; the context-token use of the prototype dispatches (stage 1: 86 harness tool calls, stage 2: about 69, both over the 60 cap). M1 is a narrow stand-in (the guard has no separate contracted-axis branch); M5 is killed by `ScanUnroll`'s own new guards, upstream of `DifferentialTest`.
