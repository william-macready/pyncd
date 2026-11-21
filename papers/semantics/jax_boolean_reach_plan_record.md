# JAX Boolean reachability plan: authoring record

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
   | T5 | `7bf46907`, `4af683c7` | `4af683c7` |

3. **Packaging.** The patches are the `git diff` between consecutive task tips. Per-task cumulative
   hash snapshots are `task1.json`..`task5.json`, with 7, 11, 15, 15 and 19 file entries. The replay
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
| T3 `2c4fac2f` | runner 62 checked / 62 refusals / 28 source / 5 / 20 / 20; 17 raw fixtures bitwise in f64/f32, eager/jit; 18 refusal cases; Boolean Python manifest 30 entries killed in both precisions, sha-clean, confirmation run twice; max-plus Python 18/18; grad 8/8; real-path runners (affine, affine32, nonlin, scatter, logic) and drivers 8/8 green | ARTIFACT |
| T4 `c785fe7d` | +64/-10, 3 files; runner 62 / 58 / 52 / 5 / 20 / 20; drivers exit 0 (8); `run-evalplan-logic.sh` exit 0 (13 fixtures); `Closed` 19 true pairs; chain `Reach[0,5,:]` = `[0,0,0,0,0,1,1]`; 3 controls (one survived until `positional_ran` was added) | ARTIFACT |
| T4 | affine/affine32/nonlin/scatter runners NOT rerun (shared runtime and emitter untouched) | ARTIFACT |
| T5 `4af683c7` | +111/-40, 5 files; `LeanNCD` and `JaxExperiment` rebuilt green (8620 jobs); doc counts copied from the evidence, not recounted | ARTIFACT |

## Replay observation

- **CONTROLLER** (from the evidence). Patches 01..05 apply in order onto `b305b363` with
  `git apply --check` and then `git apply`. After 01..04 the tree equals
  `8bd705dee6675cf692015c9e68204ddcc8ef4afc` (the prototype tip `c785fe7d`). After 05 it equals
  `efa0c1cb53c333ddd69d654e33539c5e51c40f6c` (tip `4af683c7`). `verify_package.py --task 0` passes.
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
  - `JS-L-g1`, `JS-L-g2`, `JS-L-e3`, `JS-L-e4`, `JS-L-e5`, `JS-L-c1`
  - `J3`

  The plan schedules them in final verification as first observations.
- Driver and real-path runner results at the T1 boundary, and real-path runner results at T2, were not
  reported. The plan expects green and asks the executor to record them.
- The full `LeanNCD Tests JaxExperiment` job count at the final tip was not recorded.
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
