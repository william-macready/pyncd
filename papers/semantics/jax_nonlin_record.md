# JAX pointwise/axiswise slice: execution record

**Status: READY FOR WHOLE-BRANCH REVIEW.** All package gates passed. No merge or push.
Executed the supplied six patches without code, patch, fixture, tolerance, manifest or
`expect` edits. The owner's controller owns whole-branch review and integration.

## Identity and pre-flight

- Branch: `jax-pointwise-exec`.
- Worktree: `/Users/williammacready/code/python/pyncd/.claude/worktrees/jax-pointwise-exec`.
- Package patch base: `f2616f54fd3a6eccc18a9d09d2870ced37ced5fa`.
- Actual starting local `main`: `3952cbbd645adb63376f41fa495f5a0a97c57394`.
- Final implementation commit: `408822546c69ec1166f9642384603af2c17faa0b`.
- The record commit is the commit containing this file, subject
  `docs: JAX pointwise slice record`; its hash is reported at execution close-out
  rather than embedded self-referentially here.
- Local `main` was unchanged and remained 46 commits ahead of `origin/main`.

Pre-flight A: `/usr/bin/git -C /Users/williammacready/code/python/pyncd merge-base --is-ancestor f2616f54 main`
exited 0. The primary checkout was clean; the plan's package commit was `af0ade83`.
The execution branch and directory were absent before creation. The exact
`diff --name-status f2616f54 main` output was:

```text
A	papers/semantics/jax_nonlin_execution_brief.md
A	papers/semantics/jax_nonlin_files/FINDINGS.md
A	papers/semantics/jax_nonlin_mutations_post.json
A	papers/semantics/jax_nonlin_mutations_python.json
A	papers/semantics/jax_nonlin_patches/T1-lean-render.patch
A	papers/semantics/jax_nonlin_patches/T2-runtime-and-differential.patch
A	papers/semantics/jax_nonlin_patches/T3-transformer-fixture.patch
A	papers/semantics/jax_nonlin_patches/T4-python-mutation-runner.patch
A	papers/semantics/jax_nonlin_patches/T5-survivor-fixtures.patch
A	papers/semantics/jax_nonlin_patches/T6-docs.patch
A	papers/semantics/jax_nonlin_plan.md
A	papers/semantics/jax_nonlin_plan_record.md
```

Created the prescribed worktree from local `main`. Ran `prepare-worktree.sh` once
using the plan's `python3 -I -c` / `subprocess.run(..., cwd=..., check=True)` form.
It reported `already at main (3952cbbd)`, donor 8101 Mathlib oleans, 8101 synced,
`8101 built / 8094 sources (100%)`, and 367 project oleans. Post-prepare HEAD was
exactly the actual starting `main` above. No cold Mathlib build was observed.
No `--plan` was supplied, so preparation explicitly skipped plan-copy/ledger steps.

Pre-flight B: all six patches and all three required manifests existed, and status
was empty. The baseline `LeanNCD` build exited 0; its oversized tool output hid the
final summary, so its job count was **not observed**, not inferred. Python setup ran
once and exited 0:

```text
Installed JAX 0.10.0; devices: [CpuDevice(id=0)]
```

## Six patch commits and per-task gates

Each task used separate plain `apply --check`, `apply`, owning-path `hash-object`,
explicit-path `add` and exact-subject `commit` commands. Every apply/check exited 0
without output. Every owning blob matched its full plan hash. Each commit includes
`Applies <patch file name>` and the required Copilot coauthor trailer.

| Task | Full commit | Exact subject | Verification |
| --- | --- | --- | --- |
| T1 | `64e26a9be834e7cb29a403afd667c7f87956d3a7` | `feat(jax): render pointwise and axiswise steps in affineReference` | 2/2 owning hashes; build `8619 jobs`; seven new guards compiled; Lean manifest 8/8; clean status and both hashes rechecked after restore |
| T2 | `3d1eefae246bd0b90038f98bde27e63ee9f38c44` | `feat(jax): pointwise and axiswise runtime and Lean-vs-JAX differential` | 5/5 owning hashes; runner exited 0, 11 fixtures per precision |
| T3 | `f365108a9c88b9cd7e2fff342d2b601a5fe82b64` | `test(jax): single-layer transformer through Lean and JAX` | 2/2 owning hashes; runner exited 0, 12 fixtures per precision; transformer shape assertion passed |
| T4 | `9e729357cfa295b56003d2a9569460621d6496e9` | `test(jax): Python mutation runner accepts a per-entry verifier` | 1/1 owning hash; specified `ast.parse` syntax check exited 0, no output |
| T5 | `3499b437f54a3c931cdee02b4e811b03a378c546` | `test(jax): fixtures that pin softmax row max, relu NaN and the compare path` | 2/2 owning hashes; runner exited 0, 15 fixtures and every required pin line per precision |
| T6 | `408822546c69ec1166f9642384603af2c17faa0b` | `docs(jax): pointwise and axiswise steps render in affineReference (tolerance-compared)` | 6/6 owning hashes; `diff --check` and `bash -n` exited 0 without output |

T6's `all five drivers` grep exited 1 without output, the required absence.
The `all six drivers ran clean` grep exited 0 with exactly:

```text
65:echo 'all six drivers ran clean (Lean side only; the Python/JAX verifiers were not run)'
```

T1's exact build summary was `Build completed successfully (8619 jobs).`
T2 and T3 runner internal builds reported 8615 and 8516 jobs. Their observed counts
were 11 + 11 and 12 + 12, respectively, as expected, with eager and jit comparisons.
The transformer assertion checked 14 steps: 10 assign, 1 pointwise and 3 axiswise.

The required `log --oneline f2616f54..HEAD`, before adding this record:

```text
40882254 docs(jax): pointwise and axiswise steps render in affineReference (tolerance-compared)
3499b437 test(jax): fixtures that pin softmax row max, relu NaN and the compare path
9e729357 test(jax): Python mutation runner accepts a per-entry verifier
f365108a test(jax): single-layer transformer through Lean and JAX
3d1eefae feat(jax): pointwise and axiswise runtime and Lean-vs-JAX differential
64e26a9b feat(jax): render pointwise and axiswise steps in affineReference
3952cbbd docs: JAX pointwise slice execution brief for GPT
af0ade83 docs: JAX pointwise/axiswise slice package
```

## Lean mutation manifest, once immediately after T1

The specified `mutation-manifest.sh --check` exited 0:

```text
manifest OK: 8 entries, 8 selected, every old-string unique
```

The real run immediately afterward used no `--out`, exited 0, and produced:

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| JN-T1-01 (include table in reversed row-major order) | yes | yes | yes | PASS |
| JN-T1-02 (include table inverted: masked coordinates included) | yes | yes | yes | PASS |
| JN-T1-03 (axiswise function names swapped: softmax <-> normalize) | yes | yes | yes | PASS |
| JN-T1-04 (the include key dropped: a masked step renders as unmasked) | yes | yes | yes | PASS |
| JN-T1-05 (pointwise function names swapped: relu <-> sigmoid) | yes | yes | yes | PASS |
| JN-T1-06 (affineReference refuses pointwise and axiswise steps again) | yes | yes | yes | PASS |
| JN-T1-07 (axis_pos always rendered as 0) | yes | yes | yes | PASS |
| JN-T1-08 (a mask the worker refuses fails open: rendered unmasked) | yes | yes | yes | PASS |

```text
8/8 cycles passed.
```

Every cycle reported `mutation_exit=1 restore_hash_exit=0 restored_build_exit=0`;
restored builds reported 8516 jobs. Both T1 blob hashes and clean status were
rechecked. This manifest was not rerun later, as prescribed.

## Final-order verification, strictly serial

All twelve steps completed in the prescribed order, with no overlapping builds,
mutation runs, drivers, verifiers or corpus runs.

| Step | Check | Observed result |
| --- | --- | --- |
| 1 | Full `LeanNCD Tests JaxExperiment` build | exit 0; `Build completed successfully (8844 jobs).` |
| 2 | `check-lean-drivers.sh` | exit 0; exact final line below |
| 3 | `run-evalplan-nonlin.sh` | exit 0; 15 binary64 + 15 binary32, all required pins below |
| 4 | Python nonlin manifest | exit 0; 17 PASS, all killed/restored, run once |
| 5 | `run-evalplan-scatter.sh` | exit 0; 10 binary64 + 5 binary32 bit-identical fixtures |
| 6 | Scatter Python manifest | exit 0; 16 PASS, all killed/restored, run once |
| 7 | `run-evalplan-affine.sh` | exit 0; exact final line below |
| 8 | `run-evalplan-affine32.sh` | exit 0; exact final line below |
| 9 | `run-evalplan-affine-corpus.sh` | exit 0; 3832 cases, zero eager mismatches, 666.03 seconds wall time |
| 10 | Final full `LeanNCD Tests JaxExperiment` rebuild | exit 0; `Build completed successfully (8844 jobs).` |
| 11 | `git status --short` | exit 0, empty |
| 12 | Twelve section-6 `hash-object` checks | all exact matches, table below |

Both full-build job counts equal the plan's 8844. The corpus's own build also
reported 8844. No package gate failed and no required verifier was skipped or rerun.

Exact driver final line (observed after T6, not inherited from the prototype):

```text
all six drivers ran clean (Lean side only; the Python/JAX verifiers were not run)
```

### Nonlinearity differential: exact final pin lines

The following were observed in both T5 verification and final-order step 3.
The binary64 block:

```text
15 float64 nonlinearity fixtures within rtol 1e-12 / atol 1e-14 of Lean (eager + jit)
tolerance self-test: 1e-3 relative perturbation and a zeroed output are rejected
require_close canary: a 1e-3 perturbed output is rejected end to end
pins: relu(NaN) = +0, large-negative and huge-masked softmax rows are real distributions
relu signed zero: assign copy turns -0.0 into +0.0 in Lean; relu bit-exact in eager JAX
pinned: all-masked row = zeros (not uniform), zero-sum normalize = zeros, all-zero l2 = zeros, large logits [1000, 1001, ...] finite and sum to 1 (max subtraction)
reduction order pinned: forward sum np.float64(1.0), reversed np.float64(0.0), tree np.float64(0.0); Lean row = x / forward sum, JAX matches it within tolerance (a reordered sum would give all zeros)
jit(grad) finite and non-trivial for gelu, softmax and causal softmax
```

The binary32 block:

```text
15 float32 nonlinearity fixtures within rtol 1e-05 / atol 1e-06 of Lean (eager + jit)
tolerance self-test: 1e-3 relative perturbation and a zeroed output are rejected
require_close canary: a 1e-3 perturbed output is rejected end to end
pins: relu(NaN) = +0, large-negative and huge-masked softmax rows are real distributions
relu signed zero: assign copy turns -0.0 into +0.0 in Lean; relu bit-exact in eager JAX
pinned: all-masked row = zeros (not uniform), zero-sum normalize = zeros, all-zero l2 = zeros, large logits [1000, 1001, ...] finite and sum to 1 (max subtraction)
reduction order pinned: forward sum np.float32(1.0), reversed np.float32(0.0), tree np.float32(0.0); Lean row = x / forward sum, JAX matches it within tolerance (a reordered sum would give all zeros)
jit(grad) finite and non-trivial for gelu, softmax and causal softmax
```

### Python nonlin manifest: exact 17-row output

```text
PASS JN-P-01 (relu via jnp.maximum) | killed | restored
PASS JN-P-02 (softmax row max folded over ALL entries, masked included) | killed | restored
PASS JN-P-03 (softmax row max via plain jnp.maximum from 0) | killed | restored
PASS JN-P-04 (softmax masked entries still summed) | killed | restored
PASS JN-P-05 (normalize masked entries still summed) | killed | restored
PASS JN-P-06 (row fold reversed, right to left) | killed | restored
PASS JN-P-07 (all-masked softmax row uniform instead of zeros) | killed | restored
PASS JN-P-08 (normalize zero-sum guard dropped) | killed | restored
PASS JN-P-09 (l2normalize without the sqrt) | killed | restored
PASS JN-P-10 (sigmoid sign flipped) | killed | restored
PASS JN-P-11 (leakyrelu slope 0.1, binary64) | killed | restored
PASS JN-P-12 (gelu cubic coefficient perturbed, binary64) | killed | restored
PASS JN-P-13 (axis_pos ignored: always the last axis) | killed | restored
PASS JN-P-14 (include table ignored: treated as all-true) | killed | restored
PASS JN-P-15 (f32 gelu_scale bit pattern perturbed in a mantissa bit) | killed | restored
PASS JN-P-16 (verifier tolerance made huge) | killed | restored
PASS JN-P-17 (verifier compares the JAX output against itself) | killed | restored
```

Summary: 17 PASS; no survivor or failed restore.

### Scatter regression manifest: exact 16-row output

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

Summary: 16 PASS; no survivor or failed restore.

### Older verifier endings and first corpus measurement

Scatter fixture summaries and literal final line:

```text
10 float64 scatter fixtures bit-identical to Lean (eager + jit)
5 float32 scatter fixtures bit-identical to Lean (eager + jit)
fast mode: unknown scatter_mode and out-of-range placement rejected
```

Affine final line:

```text
Lean checked plan -> affine lookup tables -> ordered JAX reference -> Dense agreement passed
```

Affine32 final line:

```text
56 binary32 fixtures, 160 eager/jit output checks: bit-identical to the Lean binary32 reference except the pinned KNOWN_DIVERGENT positions (x64 disabled)
```

The corpus ran alone among builds/verifiers/mutations, in the background, timed
with `/usr/bin/time -p`. This is the executor's first post-slice measurement:

```text
JAX 0.10.0 on cpu: [CpuDevice(id=0)]
corpus: source_cases=3832 eager_mismatches=0 feature_masks=45 jit_cases=65 (corpus_representatives=45, curated=20)
artifact_bytes=3424195 generation_seconds=21.441 eager_seconds=631.732 jit_seconds=6.742
generated feature coverage: nonzero_bias, nonunit_or_multiaxis_coeff, multiple_factors, multiple_terms, reduction_domain, multiple_graph_nodes, internal_read
curated-only feature coverage: negative_invalid, zero_coeff_row, zero_extents, empty_factors, empty_terms
full Wave C affine corpus -> ordered JAX reference -> Dense agreement passed
real 666.03
user 764.48
sys 114.94
```

### Final twelve-file blob check

All twelve matched both immediately after T6 and again after the final full build
and clean-status check. This includes the Lean manifest's restored codegen file.

| File | Final blob |
| --- | --- |
| `leanncd/LeanNCD/Eval/Plan/Nonlin.lean` | `ae3536f1d078e456bc66fbb2b256d6741e891ab3` |
| `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean` | `3d54ef44ea4b136e95748f62856988c26a263358` |
| `leanncd/experiments/jax_bridge/EvalPlanNonlinSmoke.lean` | `3ca00cd9fd582b1e030eb17d83bef70aa4c993c6` |
| `leanncd/experiments/jax_bridge/check-lean-drivers.sh` | `2388fcfc2d474e2c4d4c4c7fef00a1b3df13cfe4` |
| `leanncd/experiments/jax_bridge/evalplan_affine_runtime.py` | `14885bd688440249809e9220c572d3e1754efe5a` |
| `leanncd/experiments/jax_bridge/evalplan_nonlin_smoke.py` | `ee512bedf8e27ac115cb0d0fba0ca7dcd0ee5771` |
| `leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh` | `e530c72793c0779bfc90ad8d766512a2eb679262` |
| `leanncd/experiments/jax_bridge/mutation_python_manifest.py` | `2ff09da131a8c728afa5b252cda42afda24e8c29` |
| `leanncd/LeanNCD/Eval/Plan/AGENTS.md` | `4ba20583a496519cf6896bfda150ee5f63f663b2` |
| `leanncd/experiments/jax_bridge/README.md` | `4288ceee620f16f1a9c4d0971f54294f505a1aaa` |
| `papers/f32_jax_evalplan.md` | `1c0549867857c14f1154cb97401d8735c059c8e7` |
| `papers/predicate_boolean_backend_parity.md` | `6137c6980c00cf122896f6e15814c5b11ab8f3d3` |

## Report-only documentation sweep

Ran both section-9 commands literally with absolute search roots, after final
verification and before creating this record:

- Line-based command: **100 hit lines in 47 files**, not the reported 74/41.
  The literal `!papers/semantics/jax_nonlin_*` and `jax_scatter_*` exclusions did
  not exclude those paths under absolute roots in this invocation. Of the 100,
  26 lines were in those package/scatter historical paths. A deterministic
  report-only filter removing them leaves **74 lines in 41 files**, matching
  the plan's comparison set. No source, command pattern or expected count was edited.
- Multiline command: **3 output lines**, comprising the known architecture
  sentence's two lines and its quotation in the package plan. Again the literal
  relative-root exclusion did not exclude that package quotation.
- All capability-refusal hits outside those historical package quotations were
  already represented by section 9's classification. No new live JAX capability
  finding was discovered.
- Stale-live (c): [jax_evalplan_architecture.md](../jax_evalplan_architecture.md),
  the wrapped sentence claiming no pointwise/axiswise lowering.
- Borderline: [f32_evalplan.md](../f32_evalplan.md), whose historical-baseline
  note names F32-JAX and scatter but not pointwise/axiswise.
- The predicate-parity row carries T6's superseding note; its separate evidence-door
  rejection guard remains applicable. The Boolean-predicate plan's old instruction,
  pre-scatter audit and older nonlinearity plans are historical, not new live claims.
- The smoke driver's "All five pointwise functions" is an unrelated function count.
  No live driver-count text says five; the exact driver command says six.

Neither stale/borderline document was edited. Controller follow-up after landing:
about 0.5 dispatch, as estimated by the plan, not measured here.

## Process, STOPs, deviations and measurement limitations

- Two bounded implementation dispatches, no nested delegation. Dispatch 1 completed
  setup and T1-T3. Dispatch 2 completed T4-T6 and final-order steps 1-6. The controller
  completed steps 7-12, documentation classification and this record.
- Every required package gate is green. No patch/code/build/verifier/manifest command
  was repaired or retried. The Lean manifest ran once after T1; each Python manifest
  ran once in its prescribed final-order position.
- **Dispatch-2 STOP, not a package failure:** an extra report-only assertion wrongly
  guessed scatter mutation IDs as `JS-P-`, despite the successful manifest's actual
  `JS-T2-` / `JS-T6-` IDs. It exited 1 with `AssertionError`, and the dispatch stopped
  after final-order step 6 rather than running its assigned steps 7-8. The controller
  read the successful actual 16-row output, recorded the error, and resumed at step 7.
  No fixture, manifest, count or assertion in the package was changed.
- Exact failed extra command:

```text
python3 -I -c "from pathlib import Path; s=Path('/Users/williammacready/.copilot/session-state/0e33eed6-070d-4e43-9334-d2348c3cb12c/files/jax-nonlin-final-06-scatter-mutations.log').read_text(); lines=s.splitlines(); assert len(lines)==16 and all(x.startswith('PASS JS-P-') and x.endswith('| killed | restored') for x in lines); print(s,end='')"
```

Its output was a Python traceback ending `AssertionError` (exit 1).

- Background completion was awaited with long blocking `read_bash` calls rather
  than automatic notices. Some commands required more than one long wait; no
  verifier/mutation was relaunched and there was no rapid polling. The controller's
  initial 1200-second read request was refused by the tool (`Invalid delay: 1200.
  Please supply a valid delay between 0 and 600 seconds.`), after which two
  600-second waits completed the corpus; the corpus command itself was not retried.
- Some report-only reads exceeded display limits and were narrowed. The baseline
  build's exact final summary remains unobserved, although exit 0 was observed.
  The initial requested brief was absent in the session's stale worktree; the
  committed copy in the primary checkout was located and read before execution.
- Token use, cumulative input tokens, context peaks and exact telemetry turn counts:
  **not measured** for either dispatch or controller. No own deduplicated
  `session.usage_record` telemetry was exposed; Claude's `token-report.py` was not
  used. Dispatch 2 manually reported about 54 tool-response turns; dispatch 1's
  exact turn count was not measured.
- **Conservative budget disclosure:** the controller exceeded 60 individual tool
  calls, including parallel window reads and per-path hash commands. Treat that
  as a breach under the prototype's tool-call accounting convention; an exact
  telemetry turn count is unavailable. Neither the 250k peak nor the approximately
  175M cumulative-input ceiling can be verified without telemetry. No token total
  or timing other than the corpus measurement is guessed.
- No required execution step was skipped. Per-task documentation-only T6 did not
  require a build; the final sequence supplied the full builds. Prototype-only
  per-function/per-output tables were not rederived, as prescribed.
- Whole-branch review, merge and push are intentionally not performed. The record
  commit and branch/worktree remain for the owner's controller.
- Inherited caveats remain: generic Python `expect` strings do not distinguish a
  different first assertion; unpinned audit cells (scan render/einsum, hand-built
  evidence candidate, non-real nonlinear storage, unknown function) are not newly
  tested. No owner decision was invented; controller adjudication remains open.

## Parked scope (plan section 4 copied unchanged; owner: none)

The owner does not need the following. They are not owed by this plan, and each is listed so a
reviewer does not mistake silence for omission. Cost lines are the controller's estimate in dispatches
(one dispatch is the Rule 6 unit), not measurements.

| Not done | Consequence / cost line |
| --- | --- |
| ~~**Unary reads on JAX**~~ (`sqrt`, `exp`, `log`, `sin`, `cos`, reciprocal; LayerNorm with `eps`) | **Done 2026-11-04** in the follow-on slice (last section of this record): `affineReference` renders them; `einsumOnly`, the evidence path and scatter's compute half still refuse (`unaryFactor`, about 3 dispatches with the evidence path). |
| ~~**Scan on JAX**~~ | **Done 2026-11-05** in the scan slice (`jax_scan_record.md`): `affineReference` lowers single-axis real scans through `lax.scan` (the nonlin differential is now 32 binary64 and 24 binary32 fixtures); `einsumOnly`, the candidate conversions and the evidence path still throw `unsupportedStep`. The remaining scan parked items are in that record. |
| **The evidence path** for scatter, pointwise and axiswise (`JaxKernelCandidate` arm, `stepTiedToPreparedStep`, `ExecutableTest.lean` rewrite) | A scatter, pointwise or axiswise plan runs through JAX with no `ExecutionEvidence`. About 3 dispatches, do all three together; touches core `Executable.lean`; needs a fast-mode-versus-label style decision (scatter's `scatter_mode`). |
| Tropical and Boolean pointwise/axiswise steps | Not rendered; the plan-level storage gate of `affineReference` is inherited (section 8 notes it was not measured for these steps). Not estimated. |
| A raw-plan fixture that feeds a signed zero DIRECTLY into relu | Every surface program emits an assignment copy first (`+0 + -0 = +0`), so the eager bit-exactness of relu is exercised only through that copy. About 1 dispatch. |
| Factor the driver helpers duplicated across the smoke drivers (`pyTensorEntry32`, the named-fixture helpers) into `EvalPlanCodegen` | About 0.5 dispatch. |
| Measure the tolerance on a GPU or another XLA backend | Tolerances were measured on this CPU, not derived; other backends may differ more. Needs a GPU or another backend; not estimated. |
| `route` and diagram rendering (Python diagram stack, `Bridge/`, `tsncd`) | No owner and no estimate. |
| Lean-side gaps that stop other models (embedding gather, RoPE, ALiBi, data-driven masks) | Catalogued in `leanncd/test/Eval/Portfolio/KnownGapTest.lean`. Not part of this slice. |
| Edit the stale `papers/` sentences found by the section 9 value-grep | Reported, not edited (Rule 14). About 0.5 dispatch. |

Additional parked observation: the package's absolute-root value-grep exclusions
do not remove their intended historical paths in this invocation. Fixing those
future instructions is not required for this slice; estimated 0.25 dispatch, not
started. The literal results and filtered comparison are reported above instead.

## Follow-on: unary reads on JAX (2026-11-04, Direct path)

Not part of the slice above; recorded here because it closes the first parked row. Process: Direct
path (no plan document), two implementer dispatches on branch `worktree-jax-unary-reads`, commits
`d19580e6` (gate opt-in and rendering), `9609aed6` (runtime), `7366b736`, `cb218347`, `694ae628`
(fixtures and pins), `797764bf` (empty commit; five mutation results in its body, the sixth, unary
applied before the pad, in the body of `7366b736`), then the controller's review fixes below.

- **Decision (user, 2026-11-04): B1, an unchecked precondition.** JAX lowers to plain `jnp` ops and
  agrees with Lean within tolerance only where Lean returns ok. Rejected: a NaN promise (Lean's
  `relu(NaN)` is `+0`, and `exp(log 0) = exp(-inf) = 0` is finite, so it cannot be kept), a
  canonicalised NaN, and a checked variant (`checkify` or a validity-flag output; changes the
  generated signature, its own slice).
- **Gate.** `jaxAssignSupported` takes `allowUnary : Bool := false`, threaded through
  `checkJaxAssignSupport` and `requireJaxSupport`; only `renderAffineNode` passes `true`.
  `einsumOnly`, both candidate conversions, the evidence path and scatter's compute half keep the
  `unaryFactor` refusal (fixture 4 in `EvalPlanCodegen.lean` pins both halves).
- **Runtime.** `_apply_unary` runs after the zero-pad `where`, and in the empty-source shortcut
  (Dense pads with 0, then applies the function: an out-of-bounds `exp` read is 1).
- **Fixtures** (21 per precision, up from 15): `unary_exp_oob`, `unary_ops` (log, sqrt, sin, cos,
  reciprocal), `unary_mix` (unary times plain factor), `unary_red` (unary read under a reduced
  axis), `unary_ln` (LayerNorm with `eps = 1e-5`, compiled from source), `unary_empty` (zero-extent
  source). Every input is Lean-ok. `domainPins` in `EvalPlanNonlinSmoke.lean` observes that `log(0.0)`,
  `log(-1.0)`, `sqrt(-4.0)` and `recip(0.0)` are typed unary-domain errors in Dense, binary64 and
  binary32: those inputs are out of contract and excluded from the comparison.
- **Hand mutations** (each failed its fixture, restored): sin/cos swapped, log/sqrt swapped,
  reciprocal as `x`, empty-source shortcut dropping the unary, `unaryOpName` sin/cos crosswise,
  and the unary applied before the pad.
- **Whole-branch review** (one reviewer, one lens, read-only): no behavioural defect. Findings and
  disposition: (1) scatter's compute half refused a unary read only by omission, no fixture pinned
  it; fixed with a guard in `ExecutableTest.lean` (clone `idScatter`, compute half `unaryAssign`,
  expect `unaryFactor 0 0 0`), hand-mutation-checked below. (2) `unary_mix` was described as pinning
  the factor product order but cannot (a reordering differs by about 1e-16, inside tolerance); the
  comment now says it pins that the unary attaches to its own factor. (3) Four stale live comments
  and one inventory doc (`backend_missing_functionality.md`) still said JAX refuses a unary read;
  fixed. (4) The hand mutations live only in commit bodies and are not manifest entries (Direct
  path, no new manifest entries); this record's earlier wording put all six in one commit body.
- **Parked, new:** the six unary hand mutations plus the scatter-gate default are not manifest
  entries (about 1 dispatch to add them to `jax_nonlin_mutations_python.json` and
  `jax_nonlin_mutations_post.json` with observed `expect` strings).
- **Parked, unchanged:** unary reads in the evidence path, `einsumOnly` and scatter's compute half
  (about 3 dispatches with the evidence path), f32 domain-boundary values such as signed zero
  (about 1 dispatch; plan-level pins exist in `KernelDense32Test`), the relu/NaN and `-inf`
  swallowing interaction (documented in the jax_bridge README, not changed).
- **Controller verification** (run by the controller, not read from the implementers' reports): full
  `Tests` build 8841 jobs; `run-evalplan-nonlin.sh` 21 + 21 fixtures with the domain pins;
  `check-lean-drivers.sh` all six drivers clean; corpus 3832 cases, 0 eager mismatches, 45 feature
  masks, 65 JIT cases; Python manifests 17/17 (nonlin) and 16/16 (scatter); Lean manifest 8/8.
- **Manifest line pins.** `jax_nonlin_mutations_post.json` pins `EvalPlanCodegen.lean:N:0` guard
  lines in its `expect` strings, so adding 32 lines above them made the first manifest run report
  0/8 although every mutation was still killed by the same guards. The ten line numbers were
  shifted by +32 after checking each entry's observed failing lines against its expected lines plus
  32 (7 of 8 entries matched exactly; JN-T1-06 observed four extra pre-existing guards failing, which
  the manifest does not require). Any later slice that edits `EvalPlanCodegen.lean` above line 2300
  must re-run this manifest and shift the pins.
- **Budget (Rule 6).** Both implementer dispatches breached the 60-turn cap: 80 and 87 tool calls
  (the harness count; each report under-stated its own), context peaks about 150k. Waiting on
  5-minute runner builds drove most of it. Authoring tokens were not measured with `token-report.py`.

## Follow-on: the one-layer transformer with a real RMSNorm (2026-11-05, Direct path)

Step 1 of the transformer goal (structure at small scale; the user scoped realistic sizes out). The
existing `transformer` fixture used `normalize` (sum normalisation) as a stand-in for the paper's
RMSNorm. Unary reads on JAX made the real norm expressible, so this adds, beside it and without
changing it, `transformer_rms` and `transformer_rms32` (sizes SEQ=3, m=4, h=2, k=2, d=4, the same
non-identity weights; two extra input tensors, `Inv` = 1/4 per lane and `Eps` = 1e-5 per row).
Commits `6ae2ab24` (fixtures) and `54bd32ac` (verifier; mutation results in its body).

- **Program.** Each norm is five statements: `Z[q,m] := a + b`, `Ss[q] := Z·Z·Inv`, `Ve[q] := Ss + Eps`,
  `Sd[q] := sqrt(Ve)`, `Out[q,m] := Z / Sd[q]`. The surface language accepted all of it with no
  production change. The driver enforces the plan counts (`exact (18, 1, 1)`: 18 assignments, 1 axiswise
  softmax, 1 pointwise relu; 4 unary factors, two `sqrt` and two reciprocal).
- **Value-independent pin.** Lean/JAX agreement says only that both compute the same function, so the
  verifier also pins that the norm is what it claims: every row of `A` and `H` has mean square within
  1e-3 of 1, while the pre-norm `Z1` and `Z2` do not (some row more than 0.05 from 1), so the pin cannot
  pass with the norm acting as the identity. Mutation (reported by the implementer): `Inv` set to 1.0
  (a sum of squares) leaves the differential green and fails this pin.
- **Verifier change.** The `startswith("transformer")` test and the per-output statistics, keyed by
  output name only, would have mixed the two fixtures; they are now an explicit `TRANSFORMER_FIXTURES`
  set and statistics keyed by (fixture, output). The original `transformer` table is identical, line
  for line, before and after, in both precisions (controller compared the two run logs).
- **Controller verification** (run by the controller): `run-evalplan-nonlin.sh` 22 + 22 fixtures, the
  `transformer_rms` summary line present in both precisions; nonlin Python manifest 17/17; Lean manifest
  8/8; `Tests`, `JaxExperiment` and the drivers built by the runner. Not re-run: the 3832-case corpus and
  the scatter manifest, because no runtime, gate or production file changed.
- **Not done at the time (since done: the scan slice, `jax_scan_record.md`, added the unrolled and
  scan-over-layers forms):** several layers written as unrolled flat equations; the paper's
  scan-over-layers form needs scan on JAX. The unary precondition (README) applies here: `Ve` is at least
  `Eps` by construction, so the `sqrt` and reciprocal inputs are always in domain.
- **Budget (Rule 6).** The implementer reported about 62 tool calls; the harness counted 71, over the
  cap of 60 again (cause given: a dropped space in a Lean edit, self-matching `pgrep` waits, one
  unfiltered build log). Context peak about 150-170k.
