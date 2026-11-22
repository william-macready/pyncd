# JAX Boolean reachability: execution record

**READY FOR WHOLE-BRANCH REVIEW.** All five patches and every required verification
completed successfully. No implementation, fixture, manifest or expect string was
hand-edited. Review and integration are the owner's next steps; nothing was merged
or pushed.

## Provenance and environment

- Execution base: `72c5a8e71dae87659902bf4714fa6f1b7c054a51` (local `main`).
- Source baseline: `b305b363942e440845ae19e57fec0629b7c1af04`.
- Branch: `jax-boolean-reach-exec`.
- Implementation tip before this record: `2d4a5ba970b6417908188d4970c0ed9b8e7f7184`.
- Primary: `/Users/williammacready/code/python/pyncd`.
- Worktree: `/Users/williammacready/code/python/pyncd/.claude/worktrees/boolean-reach-exec`.
- JAX interpreter: `/Users/williammacready/code/python/pyncd/.claude/worktrees/boolean-reach-exec/leanncd/experiments/jax_bridge/.cache/python/bin/python`.
- Setup reported JAX 0.10.0 and `[CpuDevice(id=0)]`; prescribed dependencies installed.
- Preparation selected the primary as donor, copied 8101 Mathlib oleans and reported
  `8101 built / 8094 sources (100%)`, plus 490 project oleans. No Mathlib cold-build
  was observed. The prototype was neither used as donor nor otherwise touched.
- Host UTC timestamp at the report checkpoint: `2026-11-22T14:48:00Z`.
  Elapsed execution time was not measured.
- No extra mutation worktree was created: all builds, runners, verifiers and
  mutations ran serially in the execution worktree.
- Long commands ran attached in the background, with logs under the worktree's
  `.cache/`; completion was awaited. No detached service was started.

Pre-flight ancestry exited 0; the baseline-to-main diff contained only added
`jax_boolean_reach_*` package files under `papers/semantics/`. The primary was clean
on `main`; the reserved execution branch and directory did not exist.
`prepare-worktree.sh` ran with the execution worktree as its working directory
(a Python `os.chdir`/`os.execv` launch supplied that directory). Its executed child
was the prescribed `bash <worktree>/.claude/skills/new-slice/prepare-worktree.sh`.
Preparation, Python setup and initial package verification all exited 0.
No `PYTHON` probe was made in this corrected execution. Every shell runner,
including `check-lean-drivers.sh`, was prefixed with `env -u PYTHON`.

Local `main` still equals the execution base. The final read-only
`rev-list --left-right --count origin/main...main` returned `0 35`: local `main`
is 35 commits ahead of the existing `origin/main` reference. No fetch or push ran.

## Commits and patch protocol

| Task | Commit | Subject |
|---|---|---|
| T1 | `0e881eab96f1996a99730de461765a3bddec353e` | `feat(jax): admit the .booleanReach render profile in the JAX gate` |
| T2 | `2f78de866943f843d3a1aa5c3c11cc6cf03e5014` | `feat(jax): emit Boolean nodes and Lean-decided Iverson include tables` |
| T3 | `f4a6309e301a174be324dfb0c40a6f01a4f7a113` | `feat(jax): execute ordered_boolean_v1 nodes and pin raw Boolean fixtures` |
| T4 | `6c06af0ac31a5318fad7e257ffd7de3248036527` | `test(jax): run the six reachability fixtures on JAX against the BFS oracle` |
| T5 | `2d4a5ba970b6417908188d4970c0ed9b8e7f7184` | `docs(jax): document Boolean reachability on JAX` |

T5's body is exactly: `Refresh the J3 mutation expect strings; revert an unrelated
whitespace change to preparedOf.` Each commit also has the required Copilot
co-author trailer. This record is committed separately with
`docs(jax): record Boolean-reachability execution`; its hash and the resulting
branch tip are in the final owner message, not embedded self-referentially here.

For every task, these were separate commands in this order, with literal absolute
paths substituted for `<worktree>` and the actual patch number for `0N`:

```text
python3 <worktree>/papers/semantics/jax_boolean_reach_files/verify_package.py --task <N-1>
/usr/bin/git -C <worktree> apply --check <worktree>/papers/semantics/jax_boolean_reach_patches/0N.patch
/usr/bin/git -C <worktree> apply <worktree>/papers/semantics/jax_boolean_reach_patches/0N.patch
python3 <worktree>/papers/semantics/jax_boolean_reach_files/verify_package.py --task <N>
```

Then the prescribed task checks ran, exactly the task's named `touched_files`
were staged, `status --short` was checked, and one commit was made. No three-way
application, rejects, observation/rewrite mode or patch modification was used.

| Task | Prior boundary | `apply --check` | `apply` | New boundary | Staged files |
|---|---|---|---|---|---|
| T1 | task 0, exit 0 | silent, exit 0 | silent, exit 0 | task 1, exit 0 | exactly 7 |
| T2 | task 1, exit 0 | silent, exit 0 | silent, exit 0 | task 2, exit 0 | exactly 7 |
| T3 | task 2, exit 0 | silent, exit 0 | silent, exit 0 | task 3, exit 0 | exactly 5 |
| T4 | task 3, exit 0 | silent, exit 0 | silent, exit 0 | task 4, exit 0 | exactly 3 |
| T5 | task 4, exit 0 | silent, exit 0 | silent, exit 0 | task 5, exit 0 | exactly 7 |

Exact package outputs, with each number observed at the corresponding boundary:

```text
Package OK: 5 ordered patches, task 0 boundary; index unchanged.
Package OK: 5 ordered patches, task 1 boundary; index unchanged.
Package OK: 5 ordered patches, task 2 boundary; index unchanged.
Package OK: 5 ordered patches, task 3 boundary; index unchanged.
Package OK: 5 ordered patches, task 4 boundary; index unchanged.
Package OK: 5 ordered patches, task 5 boundary; index unchanged.
```

Task 0 passed during setup and again before T1. Task 5 also passed before final
verification and again after all final mutation cycles. The working tree was
clean after final restoration and before creating this record.

## Per-task checks and suite boundaries

All commands listed in plan sections 6-10 ran with exit 0. Script and interpreter
paths were the worktree paths above; builds used `leanncd/scripts/lake-build.sh`.
The max-plus command was always
`python3 <worktree>/leanncd/experiments/jax_bridge/run-evalplan-maxplus.py --python <jax-python>`.
Python mutation commands always used `mutation_python_manifest.py` without
`--observe`. Lean commands used `mutation-manifest.sh` with the plan's task or
label selections.

| Task | Build / principal checks | Mutations | Boundary suites |
|---|---|---|---|
| T1 | `Eval.Plan.ExecutableTest Eval.Plan.ScanJaxGateTest JaxExperiment`: exit 0, **8531 jobs**; Boolean and both re-anchored manifest checks passed | T1 Lean 3/3 | eight drivers and all five real-path runners, all exit 0 |
| T2 | `JaxExperiment`: exit 0, **8526 jobs**; Boolean and both re-anchored manifest checks passed | T2 Lean 6/6 | eight drivers, max-plus both precisions, all five real-path runners, all exit 0 |
| T3 | max-plus runner first: exit 0; `14 checked edge cases, 17 Boolean raw fixtures` observed | Boolean Python 30/30, max-plus Python 18/18, grad 8/8 | eight drivers and all five real-path runners, all exit 0 |
| T4 | eight drivers, max-plus both precisions, logic runner, all exit 0 | filtered-copy command printed **3**; three controls 3/3 | no affine/affine32/nonlin/scatter rerun, as prescribed |
| T5 | `LeanNCD JaxExperiment`: exit 0, **8620 jobs**; pre-staging `diff --check` empty, exit 0; value grep exit 0 | no mutation cycle required at this boundary | no full boundary suite required |

At T4, only the three specified files were staged. Neither
`evalplan_affine_runtime.py` nor `EvalPlanCodegen.lean` was touched by that patch.
The filtered copy was created by the plan's exact JSON-selection command and
was not committed.

Max-plus counts are per precision, identical in binary64 and binary32:

| Boundary | Checked views | Refusals | Source views | Gradient input points | Point-forward views | Gradient views |
|---|---:|---:|---:|---:|---:|---:|
| T1 | not run / not observed | not observed | not observed | not observed | not observed | not observed |
| T2 | 28 | 26 | 28 | 5 | 20 | 20 |
| T3 | 62 | 62 | 28 | 5 | 20 | 20 |
| T4 | 62 | 58 | 52 | 5 | 20 | 20 |
| final | 62 | 58 | 52 | 5 | 20 | 20 |

Each T1, T2, T3 and final real-path suite had these observed counts, independently
checked against each log: affine **20** (9 named + 10 assignment + 1 positional);
affine32 **56 fixtures / 160 checks**; nonlin **55 f64 / 47 f32**; scatter
**10 f64 / 5 f32**; logic **13**. No required suite was skipped.
T1/T2 suite results are fresh observations, not substituted prototype claims.

Each driver-check last line, at T1, T2, T3, T4 and final, was:

```text
all eight drivers ran clean (Lean side only; the Python/JAX verifiers were not run)
```

The Python/JAX runners subsequently ran separately as recorded above.
The affine32 known divergence was reproduced, not skipped:
`f32Identity positions [1, 2]`.

Logs: [T1 mutations](../../.cache/t1-mutations.log),
[T2 mutations](../../.cache/t2-mutations.log),
[T3 Boolean Python](../../.cache/t3-boolean-python.log),
[T3 max-plus Python](../../.cache/t3-maxplus-python.log),
[T3 grad](../../.cache/t3-grad-python.log),
[T4 controls](../../.cache/t4-controls.log).
Build and suite logs use `.cache/tN-{build,drivers,maxplus,affine,affine32,nonlin,scatter,logic}.log`
where that command ran.

Note (2026-11-22, added after the whole-branch review): the `../../.cache/...` log links in this
record point into the gitignored `.cache` of the execution worktree, which was removed after the merge,
so they are not durable. The quoted command outputs and tables in this record are the durable evidence.

## Final verification

The exact plan section 11 sequence ran serially: task-5 package verification;
`lake-build.sh` with `LeanNCD Tests JaxExperiment`; driver check; max-plus runner;
affine, affine32, nonlin, scatter and logic runners; `git diff --check main`;
Group L; Group P; value grep. All exited 0. Final restoration was additionally
checked with package verification and a clean `status --short`.

The full build result was:

```text
Build completed successfully (8847 jobs).
```

This target set's job count is a fresh observation; the prototype did not record
it. T5's narrower build matched its recorded 8620-job observation.

Exact final max-plus report lines:

```text
PASS max-plus64: 62 checked views, 58 refusals, 52 source views, 5 gradient input points, 20 point-forward views, 20 gradient views
PASS max-plus32: 62 checked views, 58 refusals, 52 source views, 5 gradient input points, 20 point-forward views, 20 gradient views
```

The independent oracle reported 13 exact logic fixtures and 19 true reachability
pairs. The wiring controls below passed in both their T4 run and the full final
manifest. No gradients through Boolean nodes were run or claimed.

| Final runner | Exit | Last line |
|---|---:|---|
| affine | 0 | `Lean checked plan -> affine lookup tables -> ordered JAX reference -> Dense agreement passed` |
| affine32 | 0 | `56 binary32 fixtures, 160 eager/jit output checks: bit-identical to the Lean binary32 reference except the pinned KNOWN_DIVERGENT positions (x64 disabled)` |
| nonlin | 0 | `jit(grad) finite and non-trivial for gelu, softmax and causal softmax` |
| scatter | 0 | `fast mode: unknown scatter_mode and out-of-range placement rejected` |
| logic | 0 | `PASS: 13 fixtures x reference/checked64/checked32; every export and history cell exact; no skipped checks` |

Nonlin tolerances remained the runner's existing f64 `rtol 1e-12 / atol 1e-14`
and f32 `rtol 1e-05 / atol 1e-06`; no tolerance was added for Boolean reachability.
Scatter's existing fast-mode colliding tolerances remained unchanged.

Logs: [full build](../../.cache/final-build.log),
[drivers](../../.cache/final-drivers.log),
[max-plus](../../.cache/final-maxplus.log),
[affine](../../.cache/final-affine.log),
[affine32](../../.cache/final-affine32.log),
[nonlin](../../.cache/final-nonlin.log),
[scatter](../../.cache/final-scatter.log),
[logic](../../.cache/final-logic.log).

## Mutation checks and every final cycle

Per-task `--check` output:

| Boundary / manifest | Exact output |
|---|---|
| T1 Boolean Lean | `manifest OK: 3 entries, 3 selected, every old-string unique` |
| T1 and T2 max-plus Lean | `manifest OK: 2 entries, 2 selected, every old-string unique` |
| T1 and T2 scan Lean | `manifest OK: 11 entries, 11 selected, every old-string unique` |
| T2 Boolean Lean | `manifest OK: 9 entries, 9 selected, every old-string unique` |

Final `--check` output, each from a separate successful command before its cycle:

| Manifest / selection | Exact output |
|---|---|
| Boolean Lean, all | `manifest OK: 9 entries, 9 selected, every old-string unique` |
| max-plus Lean, all | `manifest OK: 2 entries, 2 selected, every old-string unique` |
| scan Lean, `JS-L-g1 JS-L-g2 JS-L-e3 JS-L-e4 JS-L-e5 JS-L-c1` | `manifest OK: 11 entries, 6 selected; 5 outside the selection not validated; every selected old-string unique` |
| f32 Lean, `"J3 "` | `manifest OK: 15 entries, 1 selected; 14 outside the selection not validated; every selected old-string unique` |

Python's runner has no `--check` mode; its prescribed execution checks baseline
green, old-string uniqueness, expected failure text, SHA restoration and restored
baseline green. No Python `--check` result is invented here.

Each Lean row below had mutation exit 1, restoration hash exit 0, restored build
exit 0, and `MANIFEST VERDICT: PASS`. The tuple **1 / 0 / 0** denotes those three
observed exits, not an inferred kill.

| Manifest | Label | Killed / SHA-restored / restored build | Verdict |
|---|---|---|---|
| Boolean Lean | `BR-T1-REAL-SRC-IN-BOOLEAN` | 1 / 0 / 0 | PASS |
| Boolean Lean | `BR-T1-BOOL-SRC-LEAKS-REALONLY` | 1 / 0 / 0 | PASS |
| Boolean Lean | `BR-T1-MAXPLUS-ADMITS-BOOLEAN` | 1 / 0 / 0 | PASS |
| Boolean Lean | `BR-T2-INCLUDE-ORDER` | 1 / 0 / 0 | PASS |
| Boolean Lean | `BR-T2-NO-CONTEXT-COORDS` | 1 / 0 / 0 | PASS |
| Boolean Lean | `BR-T2-ERROR-AS-INCLUDED` | 1 / 0 / 0 | PASS |
| Boolean Lean | `BR-T2-NO-BOOLEAN-NODE-META` | 1 / 0 / 0 | PASS |
| Boolean Lean | `BR-T2-NO-BOOLEAN-READ-TAG` | 1 / 0 / 0 | PASS |
| Boolean Lean | `BR-T2-IVERSON-ADMITTED-EVERYWHERE` | 1 / 0 / 0 | PASS |
| max-plus Lean | `MAX-L-SCAN` | 1 / 0 / 0 | PASS |
| max-plus Lean | `MAX-L-DEFAULT` | 1 / 0 / 0 | PASS |
| selected scan | `JS-L-g1` | 1 / 0 / 0 | PASS |
| selected scan | `JS-L-g2` | 1 / 0 / 0 | PASS |
| selected scan | `JS-L-e3` | 1 / 0 / 0 | PASS |
| selected scan | `JS-L-e4` | 1 / 0 / 0 | PASS |
| selected scan | `JS-L-e5` | 1 / 0 / 0 | PASS |
| selected scan | `JS-L-c1` | 1 / 0 / 0 | PASS |
| selected f32 | `J3` | 1 / 0 / 0 | PASS |

Final Boolean Python: **33/33 PASS**, all killed and SHA-restored with restored
baseline green. This is the first full 33-entry observation in this execution.
For the table below, the literal labels are `BR-T3-<name>-64` and
`BR-T3-<name>-32`; **K/R** means the observed line was `PASS ... | killed | restored`.
All 30 also passed at T3.

| Name | `-64` | `-32` |
|---|---|---|
| `ordered_min_is_jnp_minimum` | K/R | K/R |
| `ordered_min_tie_swapped` | K/R | K/R |
| `factor_fold_min_to_product` | K/R | K/R |
| `reduction_fold_max_to_sum` | K/R | K/R |
| `term_fold_max_to_sum` | K/R | K/R |
| `iverson_ignores_include` | K/R | K/R |
| `include_table_not_stepped` | K/R | K/R |
| `factor_seed_one_to_zero` | K/R | K/R |
| `reduce_id_zero_to_neg_inf` | K/R | K/R |
| `iverson_admitted_in_maxplus` | K/R | K/R |
| `real_to_bool_guard_dropped` | K/R | K/R |
| `include_range_guard_dropped` | K/R | K/R |
| `include_length_guard_dropped` | K/R | K/R |
| `include_on_read_guard_dropped` | K/R | K/R |
| `bool_to_tropical_key_guard_dropped` | K/R | K/R |

The remaining three entries each run both precisions:

| Full label | T4 filtered run | Final full manifest |
|---|---|---|
| `BR-T4-stale_baseline_reachability_inputs` | PASS, killed, restored | PASS, killed, restored |
| `BR-T4-closed_taken_from_hop_4` | PASS, killed, restored | PASS, killed, restored |
| `BR-T4-positional_skipped_for_reachability` | PASS, killed, restored | PASS, killed, restored |

Max-plus Python: **18/18 PASS**, all killed and restored at T3 and final.
Labels are `MAX-P-<name>-64` and `MAX-P-<name>-32`.

| Name | `-64` | `-32` |
|---|---|---|
| `factor_order_cancellation` | K/R | K/R |
| `first_state_init` | K/R | K/R |
| `unary_final_oob_mask` | K/R | K/R |
| `omit_cast` | K/R | K/R |
| `zero_init` | K/R | K/R |
| `freeze_time` | K/R | K/R |
| `zero_pad` | K/R | K/R |
| `native_max_zero_tie` | K/R | K/R |
| `remove_custom_jvp` | K/R | K/R |

Gradient Python: **8/8 PASS**, all killed and restored at T3 and final.
Labels are `MAX-AD-<name>-64` and `MAX-AD-<name>-32`.

| Name | `-64` | `-32` |
|---|---|---|
| `stale_baseline_parameters` | K/R | K/R |
| `permutation_transport` | K/R | K/R |
| `approximate_max` | K/R | K/R |
| `approximate_max_left` | K/R | K/R |

There were no survivors, missing-expect verdicts, failed restorations or failed
restored builds. The weak include-length kills still rely on the manifest's
documented `TypeError`, not the intended ValueError; that weakness is not fixed.
The first executed cycles of the re-anchored `MAX-L-*`, `JS-L-g2`,
`JS-L-e3/e4/e5/c1` all passed; no refreshed expect string was improvised.

Logs: [Boolean Lean](../../.cache/final-boolean-lean.log),
[max-plus Lean](../../.cache/final-maxplus-lean.log),
[selected scan](../../.cache/final-scan-lean.log),
[J3](../../.cache/final-j3-lean.log),
[Boolean Python](../../.cache/final-boolean-python.log),
[max-plus Python](../../.cache/final-maxplus-python.log),
[grad](../../.cache/final-grad-python.log).
An additional deterministic log check verified each exact cycle count and every
restoration status above; it exited 0.

## Stale-value grep: all 24 hits classified

The exact section-11 value grep ran after T5 and again after final mutations,
each with exit 0. Package files were excluded by `--glob '!jax_boolean_reach_*'`.
The final result had **24 source lines**: **4 live/correct**, **1 unrelated-sense**,
**3 dated snapshots**, and **16 frozen-history** hits. No unlisted live stale
claim was found, and no text outside the patches was edited.

| Source (repository-relative) | Token(s) | Hits | Classification |
|---|---|---:|---|
| `leanncd/AGENTS.md` | Iverson lowering | 1 | live, correct Boolean-only boundary |
| `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`, Boolean Iverson error comment | Iverson lowering | 1 | live, correct Boolean-only boundary |
| `leanncd/experiments/jax_bridge/README.md`, out-of-scope paragraph | Iverson lowering | 1 | live, correctly excludes non-Boolean lowering |
| `leanncd/experiments/jax_bridge/README.md`, runner-count paragraph | 62 checked views | 1 | live, verified |
| `papers/boolean_predicate_output_evalplan.md` | Iverson lowering | 1 | unrelated source-side design sense |
| `papers/wave_f_capability_manifest.md` | no JAX Boolean execution | 1 | dated snapshot, intentionally unchanged |
| `papers/wave_f_scanplan_proposal.md` | no JAX Boolean execution | 1 | dated snapshot, intentionally unchanged |
| `papers/jax_evalplan_architecture.md` | no JAX Boolean execution | 1 | dated snapshot, intentionally unchanged |
| `papers/semantics/jax_gqa_session_brief.md` | Lean-side only | 1 | frozen history |
| `papers/semantics/jax_rnn_session_brief.md` | Lean-side only | 1 | frozen history |
| `papers/semantics/jax_conv_session_brief.md` | Lean-side only | 1 | frozen history |
| `papers/semantics/jax_cross_attention_session_brief.md` | Lean-side only | 1 | frozen history |
| `papers/semantics/jax_maxplus_plan.md` | Iverson lowering; 28 checked / 26 refusals | 2 | frozen history |
| `papers/semantics/jax_maxplus_patches/04.patch` | Iverson lowering; Lean-side only | 4 | frozen patch history |
| `papers/semantics/jax_maxplus_files/authoring_evidence.json` | Iverson lowering | 1 | frozen evidence |
| `papers/semantics/jax_maxplus_patches/03.patch` | Boolean reachability remains | 1 | frozen patch history |
| `papers/semantics/jax_maxplus_record.md` | Boolean reachability remains; seven drivers | 2 | frozen history |
| `papers/semantics/jax_scan_record.md` | Lean-side only | 1 | frozen history |
| `papers/semantics/jax_maxplus_plan_record.md` | Iverson lowering | 1 | frozen history |

Raw outputs: [T5 grep](../../.cache/t5-value-grep.log),
[final grep](../../.cache/final-value-grep.log).

## Parked items and exclusions

These are carried from plan section 12, not new fixes or measurements:

| Item | Disposition | Estimated cost |
|---|---|---|
| K1: zero-extent Iverson include pin | not implemented | about 1 small dispatch |
| K2: weak empty-range scan accept neighbour | not tightened | small; dispatch count not estimated |
| K3: non-0/1 input values at named/positional entry points | **Resolved 2026-11-22**: fixture `reachability_weighted` (Edge 0.5/0.25/0.75/2/0.125) through both entry points, both precisions, eager and jit; runner now 64 / 58 / 56 | done |
| K4: Iverson with unary/multiple reads, or listed first | no new fixture | unestimated |
| K5: jit signed-zero route through `Closed` | known limitation, no new fixture or repair | unestimated |
| K6: earlier parked list | unchanged | unestimated |
| J4/J5/J13/J14/J15 | outside selected J3 cycle; no repair or individual recheck at the time. **Resolved 2026-11-22** (`a4552839`; the manifest's other stale pins `40b7af4a`): re-anchored, 5/5 cycles pass, manifest 15/15 unfiltered | done |
| weak include-length reason pin | TypeError kill retained, not tightened | unestimated |
| equivalent mutants and dated snapshot docs | no new cycle or prose rewrite | unestimated |
| too-general `EvalPlanNonlinSmoke.lean` predicate-lowering prose | carried parked note; outside these value-grep tokens | unestimated |
| historical f32 prototype note citing old J3 location | frozen history, not edited | unestimated |

Iverson in real/max-plus nodes, realToBool, min-plus, traceback, nested scans,
Boolean gradients, large-shape experiments and the XLA signed-zero limitation
were not added or repaired. Existing max-plus gradient checks did run.

## Stops, skipped work, and measured budget

- The earlier attempt against `6bd548975dee9c9bb7a71edbc7490b6ef59bc6d7`
  stopped when `printenv PYTHON` produced no output and exited 1, under the old
  brief. It created no execution branch or worktree and applied no patch.
- The corrected run restarted from `72c5a8e7`. After T1 it paused at the clean
  committed boundary because the session had reached 61 measured assistant
  turns. The owner then explicitly requested continuation ignoring turn limits.
- No required verification was skipped in the completed execution, and no
  build, runner, fixture, mutation or package command needed repair or retry.
- A `read_bash` wait request of 1200 seconds was rejected by the tool; subsequent
  waits used its allowed maximum of 600 seconds. This did not rerun a command.
- SQL usage-telemetry attempts were unavailable; measurements instead used
  this session's own persisted usage records.
- The optional unfiltered f32 manifest check was not run; the documented
  five-stale-entry exit 125 is not presented as a new observation.
- Extra-worktree parallelization was not used. Preparation's optional plan-copy
  and SDD-ledger steps were skipped because no `--plan` was supplied, as prescribed.
- The owner-only whole-branch review, merge and cleanup steps have not run.
  This is readiness for review, not a claim that review already passed.

Measured pre-record telemetry checkpoint: **22,909,593 cumulative input tokens**,
**34,263 output tokens**, **144,419 peak input tokens**, **216 usage records /
assistant turns started**. Method: read this session's `events.jsonl`, sum
`session.usage_record.data.usage.inputTokens` and `outputTokens`, take the maximum
`inputTokens`, and count `assistant.turn_start`. Input totals already include
cached input; cache counters were not added again. No subagents ran.
The snapshot includes the earlier stopped attempt and precedes this record's
authoring/commit. The final owner message reports a later measured snapshot.
The measured input total is below 175M, and peak context is below 250k.
Turn-limit enforcement after the T1 pause was explicitly waived by the owner.

Only this record is added after the five patches. Its commit is last. The branch
and worktree remain for owner review; local `main` is unchanged and remains ahead
of `origin/main`. Nothing was pushed, merged, amended or deleted from anyone
else's branch or worktree.
