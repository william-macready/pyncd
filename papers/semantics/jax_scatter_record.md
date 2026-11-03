# JAX scatter slice: execution record

**Status: READY FOR WHOLE-BRANCH REVIEW.** All seven immutable patches were
replayed, committed and verified. The required post-T6 corpus was measured.
No whole-branch review, merge or push was performed by the executor.

Binding package: [plan](jax_scatter_plan.md),
[execution brief](jax_scatter_execution_brief.md), and
[prototype observations](jax_scatter_files/FINDINGS.md).

## 1. Base, verified code tip and commits

- Base local `main`: `8beaaef5b1ff7561ad9ec7454b85fc6348b87c0a`.
- Patch base: `2cf922091cbd4550dfa141793d407ce1559f6b14`.
- Verified seven-patch code tip:
  `87683625d762b5a242b9867f94e8da59a89f2592`.
- Execution branch: `jax-scatter-exec`.
- Execution worktree:
  `/Users/williammacready/code/python/pyncd/.claude/worktrees/jax-scatter-exec`.
- This record is committed afterward with subject
  `docs: JAX scatter slice record`; its commit is the review-handoff branch tip,
  reported separately rather than attempting to embed this file's own commit hash.
- Every patch commit has the required Copilot co-author trailer.

| Task | Commit | Exact subject |
| --- | --- | --- |
| T1 | `f197472102bbd47570b8c360d2c05c3df6ea7d98` | `feat(jax): render scatter steps in affineReference (ordered placement table)` |
| T2 | `2a4d302eb3a32af0bfcc3357668d2d29ce3ef331` | `feat(jax): ordered scatter runtime and Lean-vs-JAX scatter differential` |
| T3 | `11451aacc526857220128fd17fd0f6a9cfb3a8d0` | `test(jax): end-to-end compute-half gate guard for scatter rendering` |
| T4 | `abdedcfe65ec7b43a72662080d14c3bd34bebf08` | `test(jax): Python mutation runner for the JAX scatter runtime` |
| T5 | `54032b3c3e0ef70cdbc693219c0455eacbdd66ff` | `docs(jax): scatter rendering is admitted in affineReference (ordered mode)` |
| T6 | `54441d1296ec270da5a215bb8105f009706231e3` | `feat(jax): fast vectorised scatter fold (opt-in, tolerance-compared)` |
| T7 | `87683625d762b5a242b9867f94e8da59a89f2592` | `docs(jax): Plan AGENTS B5 bullet and JAX run table reflect scatter rendering` |

Observed `/usr/bin/git -C <worktree> log --oneline 2cf92209..HEAD`
before the record commit:

```text
87683625 docs(jax): Plan AGENTS B5 bullet and JAX run table reflect scatter rendering
54441d12 feat(jax): fast vectorised scatter fold (opt-in, tolerance-compared)
54032b3c docs(jax): scatter rendering is admitted in affineReference (ordered mode)
abdedcfe test(jax): Python mutation runner for the JAX scatter runtime
11451aac test(jax): end-to-end compute-half gate guard for scatter rendering
2a4d302e feat(jax): ordered scatter runtime and Lean-vs-JAX scatter differential
f1974721 feat(jax): render scatter steps in affineReference (ordered placement table)
8beaaef5 docs: JAX scatter slice execution brief for GPT
7cd0540e docs: JAX scatter slice package
```

## 2. Pre-flight and environment

Pre-flight A passed. `main` was a descendant of the patch base, and
`diff --name-only 2cf92209 main` listed only these package paths:

```text
papers/semantics/jax_scatter_execution_brief.md
papers/semantics/jax_scatter_files/FINDINGS.md
papers/semantics/jax_scatter_mutations_post.json
papers/semantics/jax_scatter_mutations_python.json
papers/semantics/jax_scatter_patches/T1-lean-render-and-gate.patch
papers/semantics/jax_scatter_patches/T2-ordered-runtime-and-differential.patch
papers/semantics/jax_scatter_patches/T3-end-to-end-gate-guard.patch
papers/semantics/jax_scatter_patches/T4-python-mutation-runner.patch
papers/semantics/jax_scatter_patches/T5-docs.patch
papers/semantics/jax_scatter_patches/T6-fast-mode.patch
papers/semantics/jax_scatter_patches/T7-agents-stale-bullet.patch
papers/semantics/jax_scatter_plan.md
papers/semantics/jax_scatter_plan_record.md
```

Primary status was clean, and the package commit
`7cd0540e docs: JAX scatter slice package` was on `main`.
The prescribed worktree was created from local `main`, not `origin/main`.

`prepare-worktree.sh` ran with its working directory set to the new worktree
using a literal Python `subprocess.run(..., cwd=..., check=True)` invocation.
It passed: donor was the primary checkout, 8,101 Mathlib oleans / 8,094 sources
(100%), and 367 project oleans. No Mathlib cold compilation was observed.
No `--plan` was supplied, as in the brief's command; the optional plan-copy and
ledger-scaffold steps explicitly reported that they were skipped.

Pre-flight B passed: all seven patches and both manifests existed and execution
status was empty. A warm `LeanNCD` refresh passed before driver execution.
Its exact final summary was not observed because harness output was truncated;
8,615 was the observed progress denominator, not a substituted full-build count.

`setup-python.sh` ran exactly once and exited 0:

```text
Installed JAX 0.10.0; devices: [CpuDevice(id=0)]
```

The originally attached worktree lacked the brief, so it was read from the
primary checkout. The owner subsequently confirmed that the authoring prototype
path was reference only. That prototype was not accessed, copied, changed,
merged or deleted.

## 3. Per-task apply, blob and verification results

Each patch had a separate successful `git apply --check`, then `git apply`,
explicit-path staging, and its exact-subject commit. All exited 0.
No patch, code, manifest, tolerance, count or expectation was hand-edited.
Task hashes were checked after the owning commit, before its verification.

| Task | Apply-check | Owning blob rows | Verification |
| --- | --- | --- | --- |
| T1 | exit 0 | 3/3 exact | `LeanNCD Eval.Plan.ExecutableTest JaxExperiment`, exit 0; final summary truncated, progress denominator 8,619 observed |
| T2 | exit 0 | 5/5 exact | scatter differential and Lean drivers, both exit 0 |
| T3 | exit 0 | 1/1 exact | `JaxExperiment`, exit 0: `Build completed successfully (8516 jobs).`; Lean manifest check and 6/6 cycles passed afterward |
| T4 | exit 0 | 1/1 exact | prescribed isolated Python AST syntax check, exit 0, no output |
| T5 | exit 0 | 2/2 exact | `git diff --check`, exit 0, no output; Markdown only, no build |
| T6 | exit 0 | 4/4 exact | scatter differential including fast mode, exit 0; Python manifest executed in the final sequence after T7 |
| T7 | exit 0 | 1/1 exact | stale-refusal grep zero matches; run-script grep exactly one match at line 59; Markdown only, no build |

The superseded task rows also matched, not merely the final tip:

| File under `leanncd/` | Task | Intermediate exact blob |
| --- | --- | --- |
| `experiments/jax_bridge/EvalPlanCodegen.lean` | T1 | `b7df0edda8bb1a65c2a20f3d6a7a2d795a31c9fd` |
| `experiments/jax_bridge/evalplan_affine_runtime.py` | T2 | `6c2cbab9a89096c196aa83b125260843416996e8` |
| `experiments/jax_bridge/evalplan_scatter_smoke.py` | T2 | `db216aebbdacc3e950519390f4b9ff42b679ca2f` |
| `LeanNCD/Eval/Plan/AGENTS.md` | T5 | `968fa0eb8227fcc5ebf94ae0a0cacbbea2eec5dc` |
| `experiments/jax_bridge/README.md` | T5 | `748a46b7d437308b0a1a594ea07513fc45c44305` |
| `LeanNCD/Eval/Plan/AGENTS.md` | T6 | `3826c2d9b86c93426421c1681eda72524c066a84` |

The section 6 consolidated table matched after T7 and again after all mutations,
older verifiers, corpus and the last full build. Final status before this record
was empty. A programmatic extraction of the binding table asserted exactly
11 rows, ran `/usr/bin/git -C <worktree> hash-object` for those explicit paths,
and compared every full hash:

| File under `leanncd/` | Final exact blob |
| --- | --- |
| `LeanNCD/Eval/Plan/Executable.lean` | `205decd661a61e83245df0f9fa5da225ac1556a1` |
| `experiments/jax_bridge/EvalPlanCodegen.lean` | `7eea46991b62b38ddea13a7d37fe7e26055096f4` |
| `test/Eval/Plan/ExecutableTest.lean` | `d3c9434264762d496e05152995fdb2b9f8534b70` |
| `experiments/jax_bridge/EvalPlanScatterSmoke.lean` | `3934eb727ca32a555e96c91d7d331bd4ae4bed4b` |
| `experiments/jax_bridge/check-lean-drivers.sh` | `fe35d10e28d70c5005a63afec11f4fa44ac9e593` |
| `experiments/jax_bridge/run-evalplan-scatter.sh` | `354367d8667dfc279db46b350074249784bf74be` |
| `experiments/jax_bridge/mutation_python_manifest.py` | `dec4b4ea170e95a3f684be44921f8f1065e0ef52` |
| `experiments/jax_bridge/evalplan_affine_runtime.py` | `954dc5aa6c9685949091b191da73a34829fb1780` |
| `experiments/jax_bridge/evalplan_scatter_smoke.py` | `059d1b670e7af73fdc0e48abb972b90dc73b55ef` |
| `experiments/jax_bridge/README.md` | `b3ddbd137db7c2f120fce87d633fbf14033066f6` |
| `LeanNCD/Eval/Plan/AGENTS.md` | `ffe68114c7b540c81ed679a7e05700b8d95c3fc0` |

```text
11/11 final blobs match section 6 after all mutations and verifiers
```

## 4. Full builds and final verification order

Both full `LeanNCD Tests JaxExperiment` builds exited 0 and printed exactly:

```text
Build completed successfully (8844 jobs).
```

The count equals the binding plan's 8,844; there is no discrepancy. The earlier
8,843 count in FINDINGS was not used as the acceptance criterion.

The final sequence was strictly serial:

1. Full build: 8,844 jobs.
2. Lean-side drivers.
3. Scatter differential.
4. Python mutation manifest.
5. Lean mutation manifest: `--check`, then real run, without `--out`.
6. Older affine verifier.
7. Older affine32 verifier.
8. Timed post-T6 corpus.
9. Final full build: 8,844 jobs.
10. Empty status, then 11/11 final hash comparison.

No two builds, manifests, verifiers or corpus processes ran concurrently.

## 5. Scatter differential: quoted output

T2 ordered mode passed 10 binary64 and 5 binary32 fixtures, eager and jit.
T6 and the final scatter run passed the same ordered lines and every fast-mode
line below:

```text
10 float64 scatter fixtures bit-identical to Lean (eager + jit)
collision order pinned: multi cell 2 = np.float64(1e+16) (the reversed fold differs)
signed-zero and gradient pins ok
fast mode: 8 collision-free fixtures bit-identical to Lean, 2 colliding within rtol 1e-12 (eager + jit); default/ordered traced without scatter-add, fast with it
fast colliding fixtures also bit-identical to Lean on this backend (observation, not a guarantee): {'multi': True, 'contract': True}
fast mode: random well-conditioned collisions within rtol 1e-12 of ordered
fast mode: unknown scatter_mode and out-of-range placement rejected
fast-mode gradient (jit(grad)) and signed-zero pins ok
5 float32 scatter fixtures bit-identical to Lean (eager + jit)
collision order pinned: multi32 cell 2 = np.float32(1.6777216e+07) (the reversed fold differs)
fast mode: 3 collision-free fixtures bit-identical to Lean, 2 colliding within rtol 1e-05 (eager + jit); default/ordered traced without scatter-add, fast with it
fast colliding fixtures also bit-identical to Lean on this backend (observation, not a guarantee): {'multi32': True, 'contract32': True}
fast mode: random well-conditioned collisions within rtol 1e-05 of ordered
fast mode: unknown scatter_mode and out-of-range placement rejected
```

The CPU collision equality is an observation, not a guarantee for other hardware.
No GPU or other XLA backend was measured.

## 6. Mutation tables

The Lean manifest ran after T3 and again in the final sequence. Both checks
printed exactly:

```text
manifest OK: 6 entries, 6 selected, every old-string unique
```

Both real runs exited 0 and reported:

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
| --- | --- | --- | --- | --- |
| JS-T1-01 (placement table off by one) | yes | yes | yes | PASS |
| JS-T1-02 (placement table in reversed source order) | yes | yes | yes | PASS |
| JS-T1-03 (out-of-range placement backstop dropped) | yes | yes | yes | PASS |
| JS-T1-04 (affineReference refuses scatter again) | yes | yes | yes | PASS |
| JS-T1-05 (scatter support gate not applied) | yes | yes | yes | PASS |
| JS-T1-06 (checkJaxScatterSupport skips the compute-half policy) | yes | yes | yes | PASS |

```text
6/6 cycles passed.
```

The final Python manifest exited 0 and printed all 16 lines:

```text
PASS JS-T2-01 (ordered fold reversed) | killed | restored
PASS JS-T2-02 (reduceId init wrong: ones, not the real sum-product identity 0) | killed | restored
PASS JS-T2-03 (collision overwrites instead of summing) | killed | restored
PASS JS-T2-04 (copy-on-first-write: signed zero kept instead of reduceId + v) | killed | restored
PASS JS-T2-05 (node-kind dispatch drops scatter) | killed | restored
PASS JS-T2-06 (float32 destination inside a float64 run: precision path mixed) | killed | restored
PASS JS-T2-07 (runtime placement index shifted by one) | killed | restored
PASS JS-T6-01 (fast fold overwrites with .set instead of .add) | killed | restored
PASS JS-T6-02 (fast fold index shifted by one) | killed | restored
PASS JS-T6-03 (default mode leaks: run_named defaults to fast) | killed | restored
PASS JS-T6-04 (fast fold used even when mode is ordered) | killed | restored
PASS JS-T6-05 (fast requested but ordered fold silently used) | killed | restored
PASS JS-T6-06 (unknown scatter_mode not rejected) | killed | restored
PASS JS-T6-07 (tolerance vacuous: RTOL huge) | killed | restored
PASS JS-T6-08 (tolerance check compares fast against itself) | killed | restored
PASS JS-T6-09 (fast range check dropped) | killed | restored
```

Summary: 16 PASS, 0 FAIL; every mutant killed and restored.
The runner does not print a separate numeric summary line.

Recorded caveats, unchanged: Python expectations name generic assertion source
lines rather than killing fixtures. JS-T6-03/04/05 are distinguished by the
jaxpr scatter-add check on this CPU, not by differing numerical results.
JS-T6-01 is killed first by that check; its value checks were not isolated.
The constructible mixed-precision pin is JS-T2-06, not an f64 destination inside
an x64-disabled f32 run. Admitted algebras have zero reduceId; signed zero pins
init-versus-first-write, and the ones-init mutant is killed by shift.

## 7. Older verifiers and measured corpus

All three exited 0. Their last verifier lines were:

```text
Lean checked plan -> affine lookup tables -> ordered JAX reference -> Dense agreement passed
56 binary32 fixtures, 160 eager/jit output checks: bit-identical to the Lean binary32 reference except the pinned KNOWN_DIVERGENT positions (x64 disabled)
full Wave C affine corpus -> ordered JAX reference -> Dense agreement passed
```

The affine32 run explicitly reproduced the existing XLA CPU divergence at
`f32Identity` positions `[1, 2]`. This is the verifier's pinned, expected
exception, not a skipped test or a new all-bit-identical claim.

The corpus was run after T6, not inferred from the prototype's T5 observation.
Exact corpus output:

```text
corpus: source_cases=3832 eager_mismatches=0 feature_masks=45 jit_cases=65 (corpus_representatives=45, curated=20)
artifact_bytes=3424195 generation_seconds=21.121 eager_seconds=623.751 jit_seconds=6.711
full Wave C affine corpus -> ordered JAX reference -> Dense agreement passed
real 657.61
user 755.69
sys 115.21
```

Wall duration was measured with `/usr/bin/time -p`: 657.61 seconds
(10 minutes 57.61 seconds). All 3,832 source cases ran eagerly. Jit coverage
was the existing 45 corpus representatives plus 20 curated cases, not all
3,832 cases under jit.

## 8. Lean-side drivers

The T2 and final driver checks exited 0. Exact final line:

```text
all five drivers ran clean (Lean side only; the Python/JAX verifiers were not run)
```

The separate scatter and older Python/JAX verifiers were run as recorded above.

## 9. Value-grep and documentation classification

The exact section 9 grep was run from the execution root, excluding the JAX
scatter package and `.lake`, then filtered for scatter. Both grep commands
exited 0. Observed count: **184 hit lines**, matching the plan's finished-tree
reference count.

All hits were read. For statements claiming JAX refuses or lacks scatter:

- **(a) History:** previous slice plans, handoffs, records, reviews and prototype
  notes, including the additive scatter geometry family, B5 plan/plan record/
  mutation results, S3a record, F32-B/F32-D planning and records, historical
  baseline rows in F32 plans, and the dated scan-scatter plan under
  `leanncd/docs/superpowers/plans/`. The copied old Plan AGENTS bullet in
  `additive_scatter_geometry_b_exec_review_surface.md:108` is historical evidence,
  not the live node.
- **(b) Already updated or still accurate with its stated boundary:** the live
  Plan AGENTS B5/JAX bullets and run row, and the JAX bridge README. Einsum-only,
  evidence-path, tropical/Boolean/contextful/unary scatter refusals remain
  intentional. The DSL AGENTS boxed-single-bare-assign `labelExtentMismatch`
  sentence is a narrower existing refusal, not a claim that all scatter is
  refused. Earlier audit statements about assignment-only executable evidence
  remain accurate for that evidence path.
- **(c) Stale-live statements:** the following list, reported without edits.

| Document / identifier | Stale-live claim |
| --- | --- |
| `papers/backend_missing_functionality.md:326` and `:327` | categorical scatter rejection and no JAX scatter execution |
| `papers/f32_jax_evalplan.md:59` | blanket no JAX scan/scatter/nonlinearity implementation; the evidence-path refusal part remains true |
| `papers/semantics/additive_production_decision_note.md:209` | JAX refuses actual prepared scatter nodes before emission |
| `papers/semantics/additive_b5_design.md:163` | renderAffineNodesArray rejects scatter; Python runtime has no scatter placement |
| `papers/f32_evalplan.md:293` | no JAX scan/scatter/nonlinearity/predicate/f32 implementation |
| `papers/f32_evalplan.md:609`, JAX column | categorical JAX scatter refusal regardless of dtype; the surrounding historical F32 baseline and no-candidate evidence remain historical/intentional respectively |

The five documents were already named by the plan. The additional explicit
identifier `papers/f32_evalplan.md:609` is reported beyond its named `:293`
sentence; no new stale-live document was found.
The live Plan AGENTS stale "refuse before emission" wording is absent after T7.
No stale paper sentence was edited. Cost of the parked paper sweep remains
about 0.5 dispatch.

## 10. Token and turn budgets

Method: local `events.jsonl` `session.usage_record` entries, deduplicated by
`(accounting.sourceSessionId, accounting.usageId)`. Sum `usage.inputTokens`,
which includes cached context; do not add cacheReadTokens/cacheWriteTokens
again. Peak is the largest reported inputTokens for one call. Recorded turns
below count unique usage records, one per recorded model turn.

Measured snapshot at the verification/close-out boundary, before writing and
committing this record:

| Dispatch | Cumulative input tokens | Recorded turns | Peak input tokens |
| --- | --- | --- | --- |
| Controller `dc9a778c-630e-4993-b3f1-b889e6fe7250` | 2,842,313 | 42 | 95,312 |
| T1-T3 `195ef3f1-06fa-4041-b3f4-738655228fa7` | 1,695,061 | 42 | 53,900 |
| T4-T7 `d3abf4fa-26cd-4cab-853e-412abc4c3931` | 1,381,302 | 39 | 47,785 |
| Total | **5,918,676** | | |

No measured dispatch breached 60 turns or 250k peak. The measured cumulative
input total is below 175M. This is a cutoff snapshot, not an invented final
total: later record/commit/handoff turns are excluded and their complete final
usage is not measured in this file. The controller reports a later snapshot
in the final handoff if available.

Dispatch 1 originally reported a pre-final-response snapshot of 1,641,161 input
tokens, 41 turns and 52,431 peak; the table above uses the later deduplicated
completed-dispatch telemetry instead. Dispatch 2's self-report said telemetry
was not measured; its retained usage records permitted the controller's actual
measurement above. Claude-only token-report.py was not used.

## 11. Skips, STOPs, deviations and retained evidence

- No gate failed, no mutant survived, no restore failed, and no BLOCKED/STOP
  fired. No failing code was repaired or fixture loosened.
- Worktree preparation was moved to the background by the user and awaited.
  Optional plan-copy/ledger steps skipped explicitly because no --plan was
  supplied; the committed package was already present.
- Dispatches used blocking completion reads rather than exclusively push
  notifications for some successful builds. Long controller mutation runs,
  corpus and the last build ran in the background and were read only after
  completion notices. No repeated status polling was used.
- Baseline and T1 exact final build summaries were truncated/not observed.
  Successful exits and progress denominators are distinguished above.
- Dispatch 1 reran the already-successful precision verifier entrypoints to
  recover truncated T2 output; these were successful output-recovery reruns,
  not retries of failed gates. T3 stdout was summary-filtered.
- Driver scratch in the delegated runs used literal TMPDIR under the session
  files directory and the existing cleanup traps. No new worktree log files
  were created. Generated ignored Python/JAX caches are intentional verifier
  artifacts, not source changes.
- T6's Python mutation run was deferred to the required final sequence after
  T7. The Lean manifest was run both after T3 and again in that final sequence.
- Expected zero-match grep/check-ignore probes return exit 1 by convention:
  the stale-refusal grep had no match, and the new record was not gitignored.
  Neither was a failed acceptance gate.
- No implementation step, required final verifier or corpus was skipped.
  Markdown-only T5/T7 intentionally had no separate build.
- Not performed, as required: whole-branch review, merge, push, prototype
  access, out-of-scope implementation or stale-paper edits.
- At the measured pre-record checkpoint, `origin/main...main` was `0 34`:
  local main was 34 commits ahead with none behind. Execution did not merge
  into main or push it.

Complete retained run evidence is in this session's files directory:
`/Users/williammacready/.copilot/session-state/dc9a778c-630e-4993-b3f1-b889e6fe7250/files/`.
Logs: `lean-mutations-t3.log`, `jax-scatter-exec-T6-scatter.log`,
`jax-scatter-exec-final-build.log`, `jax-scatter-exec-final-drivers.log`,
`jax-scatter-exec-final-scatter.log`, `python-mutations-final.log`,
`lean-mutations-final.log`, `affine-final.log`, `affine32-final.log`,
`corpus-final.log`, `full-build-after-mutations.log`, and
`jax-scatter-valuegrep.log`. The parent event transcript retains task reports
and apply/hash/commit telemetry. Timing not explicitly listed is not measured.

## 12. Parked items (plan section 4 unchanged; owner: none)

| Not done | Consequence / cost line |
| --- | --- |
| **`route` and diagram rendering: the Python diagram stack, `Bridge/`, the diagram viewer, `tsncd`.** Untouched. `route` keeps refusing B5 groups with `routeUnsupportedMultiWriter`. | **No owner and no estimate.** The user does not need it. |
| Tropical, Boolean, predicate, contextful and unary-read scatter on JAX | Still refused by the compute-half gate (`checkJaxScatterSupport`), guarded end to end by the T3 guard. FINDINGS gives no cost line; not estimated. |
| Scan, pointwise and axiswise steps on JAX | Still `unsupportedStep` in `renderAffineNodesArray`. Not estimated. |
| `einsumOnly` mode for a scatter | Stays refused, pinned `unsupportedStep 0` for both `generateNamed .einsumOnly` and `lowerCheckPlanToCandidate`. Not estimated. |
| Scatter evidence: the `JaxKernelCandidate` arm, `stepTiedToPreparedStep`, an `ExecutableTest.lean` rewrite | The evidence path is unchanged, so a scatter plan runs through JAX but exposes no `ExecutionEvidence`. About 3 dispatches; touches core `Executable.lean`. |
| Wiring `scatter_mode` through any driver | Not done; the verifier calls the Python runners directly. No cost line in FINDINGS. |
| Exercising fast mode's tolerance path on hardware where it differs from ordered (GPU, other XLA backend) | On this CPU fast is bit-identical even for ill-conditioned collisions, so the tolerance path is exercised only synthetically (the 1e-3 perturbation self-test). About 0.5 dispatch, needs a GPU or another XLA backend. |
| Factor the driver helpers duplicated from the other smoke drivers (`pyTensorEntry32` and the named-fixture helpers) into `EvalPlanCodegen` | About 1 dispatch. |
| Assert in `EvalPlanAffineCorpus.lean` that the corpus generator emits no scatter (`assignPlans` silently drops `.scatter`, benign today) | About 0.5 dispatch. |
| Edit the stale `papers/` sentences listed in section 9 | About 0.5 dispatch. |

The execution branch and worktree remain in place for the owner's controller
session to review. **READY FOR WHOLE-BRANCH REVIEW.**
