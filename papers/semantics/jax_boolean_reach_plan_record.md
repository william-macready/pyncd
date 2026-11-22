# JAX Boolean reachability plan: authoring record

> **Update 2026-11-22 (main `40b7af4a`).** The five stale entries J4, J5, J13, J14, J15 of
> `papers/f32_jax_mutations_post.json` were re-anchored (`a4552839`), and every other stale `expect`
> pin in that manifest and in `jax_scatter_mutations_post.json` was refreshed (`40b7af4a`). Both
> manifests now run unfiltered with exit 0 (f32 15/15, scatter 6/6), so the "stale entries" and the
> unfiltered `--check` exit-125 exception described below were true of the baseline this document
> was written against and no longer apply. The text below is otherwise unedited.

**Status.** Planning record for [`jax_boolean_reach_plan.md`](jax_boolean_reach_plan.md). The plan is
execution-ready and implementation has not started. This record explains how the plan was produced
and what evidence supports each part of it. It is not an execution record. The executor writes
`papers/semantics/jax_boolean_reach_record.md` separately.

Labels used below:

- **ARTIFACT**: reported by a prototype dispatch, as recorded in `authoring_evidence.md` or
  `preflight/REPORT.md`.
- **CONTROLLER**: re-checked by the authoring controller, as marked in the evidence.
- **AUTHOR**: observed by the plan author (this document's writer) from the patch text or a scratch
  replay.
- **UNVERIFIED**: stated but not observed by anyone in the authoring chain.

## Scope and process

**Process weight: Full path.** The slice adds a backend capability on a soundness surface: a render
profile, a runtime algebra and a Lean-decided Iverson lowering. If the gate and the emitted metadata
disagree, a Boolean node silently miscompiles.

How the package was produced (ARTIFACT, from the evidence headers):

1. **Preflight audit**, 2026-11-19, on `main` `b305b363`. Lean probe drivers are under
   `jax_boolean_reach_files/preflight/`: `ReachPlanDump.lean`, `ReachEdgeValues.lean`,
   `StepIversonProbe.lean`, `MinMaxTies.lean`. It produced the decisions D1-D7, which the user accepted.
2. **Five task prototypes** on branch `proto-boolean-reach`:

   | Task | Commits | Tip |
   |---|---|---|
   | T1 | one commit | `15b40b9b` |
   | T2 | `69f9d5be`, `4f56270f`, `30f66a7c` | `30f66a7c` |
   | T3 | `05e0444e`, `2c4fac2f` | `2c4fac2f` |
   | T4 | `7b031673`, `c785fe7d` | `c785fe7d` |
   | T5 | `7bf46907`, `4af683c7` (T5b), `b46cef9d` (T5c) | `b46cef9d` |

3. **Packaging.** The patches are the `git diff` between consecutive task tips. Per-task cumulative
   hash snapshots are `task1.json`..`task5.json`, with 7, 11, 15, 15 and 19 file entries (T5 touches 7
   files: the T5c follow-up added `EvalPlanCodegen.lean` and `papers/f32_jax_mutations_post.json`). The replay
   verifier is `verify_package.py`. Both new mutation manifests ship inside the patches, because their
   `old` strings exist only after their task's code.
4. **This plan.** A fresh prose author wrote it from the artifacts only, without reading current
   production source.

Dispatch incidents (ARTIFACT):

- T1 was stopped by mistake and resumed.
- T3 Phase B ran across resumes, with one API outage.
- T2 was red at `69f9d5be` ("JAX unexpectedly admitted a Boolean scan"). This was repaired by T2c
  (`30f66a7c`), which is folded into patch 02.

No dispatch is reported as failed outright.

## Evidence read by the plan author

- `papers/semantics/jax_boolean_reach_files/package.json`, `task5.json` (file list and the
  new-file markers), `verify_package.py`.
- `papers/semantics/jax_boolean_reach_files/authoring_evidence.md` (all of it).
- `papers/semantics/jax_boolean_reach_files/preflight/REPORT.md` (all of it). The raw dumps
  `plan_dump.txt`, `edge_values.txt`, `step_iverson.txt` and `minmax_ties.txt` were NOT read.
- `papers/semantics/jax_boolean_reach_patches/01..05.patch`: file/hunk headers in full. Bounded hunks:
  - 01: `Executable.lean` gate; the new pins in `ExecutableTest.lean` and `ScanJaxGateTest.lean`; all
    manifest hunks.
  - 02: the Lean manifest additions and re-anchors; the `checkStructure` and `gateMatrix` hunks; the
    `ScanAffineEmitTest.lean` and `EvalPlanCodegen.lean` pin blocks.
  - 03: the runtime hunks; the `booleanRaw` driver hunk; the verifier's Boolean assertions and
    refusal list; the Python manifest labels plus four entries in full.
  - 04: all of it.
  - 05: headers only.
- Layout donors (structure only): `papers/semantics/jax_maxplus_plan.md` (header, sections 1, 9, 10)
  and the heading list of `jax_maxplus_plan_record.md`.
- Rules: the project `CLAUDE.md` (Rules 6, 9, 12, 13, 14) and `.claude/skills/slice-plan/SKILL.md`
  sections 0-6 and the authoring checklist.
- Script headers only, for exact command shapes: `leanncd/scripts/mutation-manifest.sh`,
  `leanncd/scripts/lake-build.sh`, `leanncd/experiments/jax_bridge/check-lean-drivers.sh`,
  `run-evalplan-maxplus.py`, `mutation_python_manifest.py`, `setup-python.sh`, the `PYTHON` lines of
  the five shell runners, the `JaxExperiment` globs in `leanncd/lakefile.toml`, and
  `.claude/skills/new-slice/prepare-worktree.sh` (usage lines).

## Observations supplied by the prototype stages

| Boundary | Observed | Label |
|---|---|---|
| baseline | max-plus runner 28 checked / 26 refusals / 28 source / 5 / 20 / 20 per precision; 8 drivers in `check-lean-drivers.sh` | ARTIFACT (counts implied by the "was" values in the T3/T4 reports) |
| T1 `15b40b9b` | +306/-12, 7 files; accept/refuse verdicts as in plan section 6; accept pins went red against a `.realOnly`-like stub; 3 mutants killed | ARTIFACT |
| T2 `69f9d5be` | `check-lean-drivers.sh` red: "JAX unexpectedly admitted a Boolean scan" | ARTIFACT |
| T2 `30f66a7c` | `check-lean-drivers.sh` all eight PASS; max-plus runner 28 checked / 26 refusals per precision | CONTROLLER |
| T2 | 6 mutants killed; 12 table pins agree with an independent Python enumeration; record contract as in plan section 3 | ARTIFACT |
| T3 after Phase A (`05e0444e`) | runner 62 checked / 62 refusals / 28 source / 5 / 20 / 20; 17 raw fixtures bitwise in f64/f32, eager/jit; 18 refusal cases; real-path runners (affine, affine32, nonlin, scatter, logic) and drivers 8/8 green. Phase B (`2c4fac2f`) added mutation manifests only and changed no code | ARTIFACT |
| T3 Phase B (`2c4fac2f`) | Boolean Python manifest 30 entries killed in both precisions, sha-clean, confirmation run twice; max-plus Python 18/18; grad 8/8 | ARTIFACT |
| T4 `c785fe7d` | +64/-10, 3 files; runner 62 / 58 / 52 / 5 / 20 / 20; drivers exit 0 (8); `run-evalplan-logic.sh` exit 0 (13 fixtures); `Closed` 19 true pairs; chain `Reach[0,5,:]` = `[0,0,0,0,0,1,1]`; 3 controls (one survived until `positional_ran` was added) | ARTIFACT |
| T4 | affine/affine32/nonlin/scatter runners NOT rerun (shared runtime and emitter untouched) | ARTIFACT |
| T5b `4af683c7` | +111/-40, 5 files; `LeanNCD` and `JaxExperiment` rebuilt green (8620 jobs); doc counts copied from the evidence, not recounted | ARTIFACT |
| T5c `b46cef9d` | 7 files in patch 05 in all. `J3` cycle run on the tip: KILLED, `expect` refreshed (it was stale before this slice); re-run PASS, restored byte-identically. `JS-L-g1` cycled PASS unchanged. README limitation and runtime paragraphs corrected; patch 02's whitespace change to `preparedOf` reverted | ARTIFACT, reported by the controller (see "Post-review fixes") |

## Replay observation

- **CONTROLLER** (from the evidence). Patches 01..05 apply in order onto `b305b363` with
  `git apply --check` and then `git apply`. After 01..04 the tree equals
  `8bd705dee6675cf692015c9e68204ddcc8ef4afc` (the prototype tip `c785fe7d`). After 05 (now three
  prototype commits, T5b and T5c included) it equals `64ece7de674cac511d8ea6bad616f08355e625f8` (tip
  `b46cef9d`). This replaces the earlier `efa0c1cb53c333ddd69d654e33539c5e51c40f6c` (tip `4af683c7`),
  which was the tree before the T5c fixes. `verify_package.py --task 0` passes.
- **AUTHOR.** I extracted `leanncd/`, `papers/` and the two root files from `b305b363` into a scratch
  directory outside the worktree and applied 01..05 there in order with `patch -p1`. All five applied
  cleanly. All 19 files in `task5.json` then matched their `sha256`.
- **AUTHOR**, counted by `task` key on the scratch result:
  - `jax_boolean_reach_mutations_post.json`: 9 entries (`T1` 3, `T2` 6).
  - `jax_boolean_reach_mutations_python.json`: 33 entries (`T3` 30, `T4` 3).

  This agrees with the evidence.
- **AUTHOR.** I ran the stale-claim token grep (plan section 11) on that scratch tree; the
  dispositions table in the plan comes from it. The package files did not exist at `b305b363`, so the
  scratch tree has none of them. In the executor's tree they will exist, and the grep excludes them.
- **AUTHOR.** I did not run `verify_package.py` myself. Git operations against a non-worktree path
  were refused in my session.

## Deviations from the original design direction

1. **Helper location.** Preflight proposed one shared helper "next to `evalPosBool`, also called by
   Dense's Iverson arm". The prototype put `iversonIncludeTable` in
   `experiments/jax_bridge/EvalPlanCodegen.lean` beside `buildFactorTable`, with no core library
   change. `evalPosBool`/`allCoords` were already public, and Dense keeps its own arm. So the include
   table and Dense agree by construction of the same `allCoords` order, not by sharing code. The pins
   cross-check the tables against an independent enumeration and against the plan's own geometry.
2. **Step-dependent predicates admitted** (D4). Preflight listed refusal as an option; the user chose
   admission. It is pinned by the step toy (`brStep`), `bool_scan_step_iverson` and the shrinking dual
   `bool_scan_step_iverson_ge`. The dual was added because the monotone toy cannot distinguish a
   stepped include table from an unstepped one.
3. **T2c fold-in.** The `checkStructure` flip was planned for T2. It landed as a separate prototype
   commit after the T2 boundary went red, and is part of patch 02, so the executor commits it with T2.
4. **`gateMatrix` row change.** Preflight said the Boolean row "flips". The actual change swaps the
   row's signatures to all-Boolean (`idSigs.map` instead of `idSigs.modify 1`) and expects acceptance.
   The old row (Boolean destination over an f64 source) was still refused after T2, so it would have
   passed unchanged and pinned nothing new. `mixedBoolDest` keeps the mixed case.
5. **Refusal cases deleted in T4.** `boolean_output` and `iverson` were removed from the max-plus
   refusal list. After T3 they refuse with the same messages and properties as
   `bool_max_plus_semantics` and `iverson_in_max_plus_node`. Preflight had flagged that they "would be
   refused only by accident".
6. **`include` key on a read refused** in any algebra. The implementer added this; nobody requested
   it. It is pinned by `bool_read_with_include` and mutant `BR-T3-include_on_read_guard_dropped-*`.
   Recorded as a scope addition, small and fail-closed.
7. **Unary read in a Boolean statement admitted.** No refusal was added. Two raw fixtures pin the
   pad-then-apply order.
8. **No execution record in patch 05.** Preflight's T5 row listed a "new record"; patch 05 creates none.
   The plan therefore asks the executor to write `jax_boolean_reach_record.md` at closeout.

## Contradictions and naming observations between artifacts

- **Python mutant label vs killing fixture.** `BR-T3-iverson_admitted_in_maxplus-*` is named for
  max-plus, but its `expect` names the first admitted case, `iverson_in_real_node`. The dropped guard
  (`if not boolean`) covers both non-Boolean algebras, and the verifier stops at the first failure.
  The evidence describes this mutant as "iverson-in-non-Boolean (`iverson_in_real_node`)", which agrees
  with the `expect`. Not a defect; the label is narrower than the guard.
- **Semantics refusals.** The evidence words them as "wrong/unknown/missing/max-plus semantics". The
  patch has three semantics cases (`bool_unknown_semantics`, `bool_missing_semantics`,
  `bool_max_plus_semantics`) plus `semantics_without_algebra`. The total of 18 cases agrees.
- **T1 re-anchors.** The evidence names only `MAX-L-DEFAULT`. The patch shows the other two lines are
  `JS-L-g1` (`jax_scan_mutations_post.json`) and `J3` (`papers/f32_jax_mutations_post.json`). The plan
  uses the patch names.
- **"Step-block table sizes 216 (term 0) and 1296 (term 1)".** The evidence states this for
  `reachProg`, but the `brReach` pin asserts exactly one `include` in the render, the base `[i = j]`.
  The sizes therefore cannot be include tables; they read as the step block's factor index tables. The
  plan does not repeat the 216/1296 figures.
- **`EvalPlanNonlinSmoke.lean` prose.** Preflight listed this as a doc door. Neither T5 nor the
  evidence's sweep addresses it. The `Zc` comment ("The bridge has no lowering for predicate factors
  (`JaxCodegenError.iversonFactor`)") is still accurate for that real-algebra fixture but is now too
  general. Parked in the plan as "report, do not edit".

## Not verified by the plan author

- No Lean build, runner, verifier or mutation cycle was run. Every count in the plan is ARTIFACT or
  CONTROLLER, apart from the AUTHOR manifest-entry counts and the `#guard`-line counts. Those I counted
  from patch text: 56 + 8 in T1; 14 + 8, plus one rewritten `run_cmd` message, in T2.
- The expected Lean driver line `generated 14 checked edge cases, 17 Boolean raw fixtures` is derived
  from the patched `main` text and the counts. It is not quoted in the evidence.
- The runner summary format (`PASS max-plus<precision>: ... checked views, ... refusals, ... source
  views, ... gradient input points, ... point-forward views, ... gradient views`) was read from the
  post-T5 scratch copy of `evalplan_maxplus_smoke.py`, not from a run. Whether `<precision>` prints as
  `64` or `float64` was not checked.
- The re-anchored existing mutation entries are not reported as cycled by the prototype:
  - `MAX-L-SCAN`, `MAX-L-DEFAULT`
  - `JS-L-g2`, `JS-L-e3`, `JS-L-e4`, `JS-L-e5`, `JS-L-c1`

  The plan schedules them in final verification as first observations. `JS-L-g1` and `J3` WERE cycled
  at T5c (both PASS; `J3` after an `expect` refresh): see "Post-review fixes".
- Driver and real-path runner results at the T1 boundary, and real-path runner results at T2, were not
  reported. The plan expects green and asks the executor to record them.
- The full `LeanNCD Tests JaxExperiment` job count at the final tip was not recorded (the 8620-job
  build was observed at `4af683c7`, before T5c).
- J4, J5, J14 and J15 were not individually confirmed stale at `b305b363`; only J13 was (ARTIFACT).
- The JAX environment setup (`setup-python.sh`, the fixed interpreter path used by
  `mutation_python_manifest.py`) comes from script headers. The evidence does not record it.
- The raw preflight dumps were not read.

## Budget disclosure (CLAUDE.md Rule 6)

- **Prototype dispatches** (ARTIFACT). The ~60-turn budgets were exceeded: T2 Phase B ~85 turns,
  T3 Phase A ~58, T3 Phase B ~71+ across resumes, T4 139 tool calls in one dispatch. The authoring
  token total has not been measured yet; measure it with
  `python3 .claude/skills/slice-plan/token-report.py <session-id>`.
- **This plan-writing dispatch.** About 55 turns, with context estimated under 200k. Both are
  estimates, not harness measurements.
- **Authoring target.** ≤ ~50M cumulative input tokens (CLAUDE.md Rule 6). Whether it was met is
  unknown until measured.

## Post-review fixes

Two read-only reviews of the draft plan (`5705a364`) were adjudicated by the controller.

- **Review A (executability): fix first.** 1 Critical, 3 Important, 8 Minor. The Critical: the `expect`
  strings of `J3` in `papers/f32_jax_mutations_post.json` named a blank line, so the cycle the plan
  schedules would have stopped the executor.
- **Review B (semantics): accept after text edits.** 10 Minor, no Critical or Important. Its findings
  file could not be written by its harness; its message was the only copy, and the controller
  adjudicated from that message.

What the controller did:

1. **Patch work (T5c, `b46cef9d`, folded into patch 05).**
   - P1: the `J3` cycle was run on the prototype tip. The mutant is killed; its `expect` was refreshed
     from the observed failure lines (`ExecutableTest.lean:587:0: Expression` and `:1929:0:
     Expression`; manifest `expect` strings may carry line numbers); the re-run passed and the file was
     restored byte-identically. `JS-L-g1` was cycled and passed unchanged. J4, J5, J13, J14, J15 are
     untouched and stay stale at the baseline.
   - P2: the README "Known limitation" now names the concrete `Edge` false = `-0` route through
     `Closed` (not run by any fixture; inferred from the documented pitfall).
   - P3: the README runtime paragraph no longer claims the runtime fails loud on missing Boolean
     metadata (total loss with no Iverson factor runs silently as sum-product; the emitter guards it).
   - P4: patch 02's whitespace-only change to `preparedOf` is reverted in patch 05.
   - Result: patch 05 covers three prototype commits (`7bf46907`, `4af683c7`, `b46cef9d`), touches 7
     files, and the tree after patches 01..05 is `64ece7de674cac511d8ea6bad616f08355e625f8` (replay
     observed by the controller; identical to the prototype tip). After 01..04 the tree is still
     `8bd705dee6675cf692015c9e68204ddcc8ef4afc`.
2. **Plan text (W1-W14, applied to the plan, this record and the evidence file).** JAX environment
   setup and `<jax-python>` (W1); the three `BR-T4-*` controls run at the T4 boundary from a filtered
   manifest copy (W2); parallel mutation worktrees, merge preconditions and cleanup (W3); runner
   `PYTHON` defaults (W4); the documented exceptions to "build only with `lake-build.sh`" (W5); the
   non-zero-exit stop rule with the f32 `--check` exit 125 exception (W6); `verify_package.py --task N`
   scope (W7); T3-era figures "carried from T3" (W8); `mkdir -p` before the `TMPDIR` fallback (W9); the
   `JS-L-g2` shift and its refresh in patch 02 (W10); the T3 attribution corrected to "after Phase A
   (`05e0444e`), Phase B added manifests only" (W11); the audit row for a bool source under a Boolean
   algebra (W12); the evidence path of `ScanAffineEmitTest.lean` (it lives in
   `leanncd/experiments/jax_bridge/`) and the T5/J3 updates (W13, W14, P5).
3. **Parked (K1-K6),** listed with cost in plan section 12 and as silently-ignored cells in the audit:
   zero-extent Iverson include; the weak empty-range accept neighbour; D6 pinned at node level only;
   Iverson with a unary or several reads; the unpinned `jit` `-0` route through `Closed`; and the
   earlier parked list (including `papers/f32_jax_prototype_notes.md`, which still cites the old `J3`
   line).

Unchanged and disclosed: the authoring token total remains unmeasured (the controller will measure it at
closeout). A verification round aimed only at these fixes follows; this record does not claim its result.
