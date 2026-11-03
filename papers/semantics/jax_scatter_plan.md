# JAX scatter steps (ordered and fast lowering): implementation plan

**Status: execution-ready package; execution not yet started.** Every line of code is already
written, verified and committed in a prototype worktree and shipped as seven per-task patches in
[`jax_scatter_patches/`](jax_scatter_patches/); the executor replays, verifies and records, it does
not design. The patches were generated against local `main` at `2cf92209` and apply to any
descendant of it that has not touched the 11 files in section 6 (the commits that add this package
change only `papers/semantics/`). **Process: Full, light**: experimental JAX bridge only (one core
Lean file gains one additive public function), no new carrier, kernel or plan IR. Prototype
observations are in [`jax_scatter_files/FINDINGS.md`](jax_scatter_files/FINDINGS.md); how this plan
was authored, and what is unverified, is in [`jax_scatter_plan_record.md`](jax_scatter_plan_record.md).
The execution record goes to `papers/semantics/jax_scatter_record.md` (created by the executor,
section 10).

**Goal.** A prepared plan containing `.scatter` steps (including the B5 groups that
`prepareEvalPlan` produces: writer scatters into private slots plus a collector assign) renders in
`EvalPlanCodegen`'s `affineReference` mode and runs through JAX in binary64 and binary32:
(a) **ordered** mode (default, bit-identical to the Lean dense worker, eager and jit), and
(b) **fast** mode (opt-in, `scatter_mode="fast"` on the Python runners; one `.at[].add` fold over
the same static placement table; compared to Lean with a tolerance, exact only when no two source
coordinates share a destination cell or every partial sum is exactly representable).

**Scope in one paragraph.** Lean: `checkJaxScatterSupport` (public, additive, `Executable.lean`),
`renderScatterNode` and the `scatterPlacementOutOfRange` codegen error (`EvalPlanCodegen.lean`),
guards, two `ExecutableTest.lean` guards, a new Lean driver. Python: node-kind dispatch and the
ordered fold in `evalplan_affine_runtime.py`, `scatter_mode`, a new verifier, a stdlib mutation
runner. Docs: `README.md` section and one `AGENTS.md` bullet. Nothing else.

## 1. Execution contract

Open every brief with this preamble (resolve `<worktree>` first):

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command, no pipelines into git.
> Use absolute paths and `git -C <worktree>`. Build Lean only with
> `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target...]`; never run `lake`
> from the worktree root. Stage files by explicit path. Stay within the stated turn and context
> budget and say so in the report if you breach it.

- **Worktree.** Run Pre-flight A (section 7) first. Create a linked worktree from local `main` (for example
  `git -C <repo> worktree add <repo>/.claude/worktrees/jax-scatter-exec -b jax-scatter-exec main`), then run
  `bash <worktree>/.claude/skills/new-slice/prepare-worktree.sh` from inside it. It must report
  Mathlib at or above 95% built; if it starts a cold Mathlib build (hours), STOP. Then build
  `LeanNCD` once to refresh project oleans.
- **Do not push.** Local `main` stays ahead of `origin/main`; say so in the final report.
- **Patches are the code.** Apply the seven patches in section 5 strictly in order T1, T2, T3, T4, T5,
  T6, T7, each after `git apply --check`. Do not retype code from this document (it has none). If a patch
  does not apply, or a post-apply blob differs from the section 5 table, STOP and report BLOCKED with
  the command output. **Do not repair a patch by hand, do not re-generate it, do not use
  `git apply --3way` or `--reject`.**
- **No relaxing to get green.** A fixture, guard or mutation that fails is a finding to report, not
  something to loosen. Do not edit a manifest, a tolerance, a count or an `expect` string.
- **Budget (Rule 6).** One dispatch is at most about 60 turns and 250k peak context. Suggested split:
  dispatch 1 = pre-flight, T1, T2, T3 and the Lean mutation manifest; dispatch 2 = T4, T5, T6, T7, then
  every verifier and the record. A dispatch that nears 60 turns stops at a task boundary (after the
  commit), reports, and the next one resumes from `git -C <worktree> log --oneline -8` (the commit
  subjects in section 5 say which tasks are done). Run builds and the corpus in the background and wait
  for the completion notice; do not poll. No nested delegation. Report your own measured token use and
  turn count (from your own telemetry; if you have none, say "not measured"). Prototype reference
  points: section 11.
- **Serial only.** Both mutation runners edit tracked files in place; the corpus verifier imports
  `evalplan_affine_runtime.py`. Never run two of {mutation manifest, corpus, any verifier, a Lake
  build} at the same time.

## 2. Global constraints (exact values)

| Item | Value |
| --- | --- |
| Base commit | local `main` at `2cf92209` (full `2cf922091cbd4550dfa141793d407ce1559f6b14`) |
| Patches | 7, in `papers/semantics/jax_scatter_patches/` (section 5) |
| Files touched in total | 11, all under `leanncd/` (section 6) |
| Full build `LeanNCD Tests JaxExperiment` | `Build completed successfully (8844 jobs)`; no new library module is added (the new driver is a `lake env lean --run` script outside every Lake target), so this is the base's own count (see Discrepancies in the record) |
| Scatter differential fixtures | 10 binary64 + 5 binary32, all bit-identical to Lean, eager and jit |
| Lean mutation manifest | `papers/semantics/jax_scatter_mutations_post.json`: 6 entries (`JS-T1-01..06`), expect `manifest OK: 6 entries` then `6/6 cycles passed` |
| Python mutation manifest | `papers/semantics/jax_scatter_mutations_python.json`: 16 entries = 7 (`JS-T2-01..07`) + 9 (`JS-T6-01..09`), expect 16 `PASS` lines |
| Fast-mode tolerance | `RTOL = {"float64": 1e-12, "float32": 1e-5}` in `evalplan_scatter_smoke.py`; check `abs(fast - lean) <= RTOL * max(abs(lean))` |
| Python / JAX | `setup-python.sh`: JAX 0.10.0, CPU only (`CpuDevice`) |
| Scatter modes | `("ordered", "fast")`; default `"ordered"`; any other value raises `ValueError` at entry |
| Corpus verifier | 3,832 cases (`run-evalplan-affine-corpus.sh`), 10+ minutes |

## 3. Fixed semantics (what the patches implement)

1. **Placement table.** A scatter node renders as the compute half's affine tables plus `dest_shape`
   and a static `dest_flat_index` table: for each source coordinate in the dense worker's `allCoords`
   order, the flat index of its destination cell. A source coordinate whose destination is outside
   the destination box is a codegen error `JaxCodegenError.scatterPlacementOutOfRange` (a backstop;
   the checked plan already refuses it).
2. **Ordered fold.** The destination starts as the algebra's `reduceId` (zeros for the admitted
   real algebras); each source value is folded in table order with `acc[c] + source[k]` (not
   copy-on-first-write: `-0.0` folded into `+0.0` is `+0.0`, pinned by `negZero`).
3. **Fast fold.** `zeros.at[idx].add(source, mode="promise_in_bounds")` after a trace-time Python
   range check of the static table (`ValueError` naming "index outside" for `-1` and `10**6`), so
   JAX's silent drop of out-of-range indices is never relied on. Only the placement fold differs;
   the compute half stays the ordered reference. No Lean change.
4. **Gate.** The compute half is graded by the same policy as an assignment
   (`jaxAssignSupported`, via the new `checkJaxScatterSupport`): tropical, Boolean, contextful and
   unary-read scatters are refused. `checkJaxAssignSupport` cannot be reused because it re-runs
   `checkAssign`, which rejects a scatter's compute half (its output shape is the source shape).
5. **Unchanged on purpose.** `stepTiedToPreparedStep` (evidence path) still refuses a scatter, so a
   scatter plan runs through JAX but exposes no `ExecutionEvidence`. `einsumOnly` mode still refuses
   a scatter (`unsupportedStep 0`; a scatter is source-driven, `jnp.einsum` is a gather).

## 4. Deliberately NOT done (no owner, none started)

The user does not need the following. They are not owed by this plan, and each is listed so a
reviewer does not mistake silence for omission. Cost lines are the prototype's own, from FINDINGS
"Parked", where it gave one.

| Not done | Consequence / cost line |
| --- | --- |
| **`route` and diagram rendering: the Python diagram stack, `Bridge/`, the diagram viewer, `tsncd`.** Untouched. `route` keeps refusing B5 groups with `routeUnsupportedMultiWriter`. | **No owner and no estimate.** The user does not need it. |
| Tropical, Boolean, predicate, contextful and unary-read scatter on JAX | Still refused by the compute-half gate (`checkJaxScatterSupport`), guarded end to end by the T3 guard. FINDINGS gives no cost line; not estimated. |
| Scan, pointwise and axiswise steps on JAX | Still `unsupportedStep` in `renderAffineNodesArray`. Not estimated. |
| `einsumOnly` mode for a scatter | Stays refused, pinned `unsupportedStep 0` for both `generateNamed .einsumOnly` and `lowerCheckPlanToCandidate`. Not estimated. |
| Scatter evidence: the `JaxKernelCandidate` arm, `stepTiedToPreparedStep`, an `ExecutableTest.lean` rewrite | The evidence path is unchanged, so a scatter plan runs through JAX with no `ExecutionEvidence`. About 3 dispatches; touches core `Executable.lean`. |
| Wiring `scatter_mode` through any driver | Not done; the verifier calls the Python runners directly. No cost line in FINDINGS. |
| Exercising fast mode's tolerance path on hardware where it differs from ordered (GPU, other XLA backend) | On this CPU fast is bit-identical even for ill-conditioned collisions, so the tolerance path is exercised only synthetically (the 1e-3 perturbation self-test). About 0.5 dispatch, needs a GPU or another XLA backend. |
| Factor the driver helpers duplicated from the other smoke drivers (`pyTensorEntry32` and the named-fixture helpers) into `EvalPlanCodegen` | About 1 dispatch. |
| Assert in `EvalPlanAffineCorpus.lean` that the corpus generator emits no scatter (`assignPlans` silently drops `.scatter`, benign today) | About 0.5 dispatch. |
| Edit the stale `papers/` sentences listed in section 9 | About 0.5 dispatch. |

## 5. Tasks

Apply each patch from the worktree root. Patch files are named `T<n>-*.patch` under
`papers/semantics/jax_scatter_patches/`. After each apply, check the blob table with
`git -C <worktree> hash-object <path>`; the value must equal the **full** hash in the task table.
Commit with the exact subject given (a body line saying which patch was applied is enough; add the
attribution trailer your environment requires). Stage only the files in that task's table.

### T1: Lean codegen for scatter steps, the support gate, Lean guards

**Patch** `T1-lean-render-and-gate.patch` (3 files, +187 -34). **Commit subject:**
`feat(jax): render scatter steps in affineReference (ordered placement table)`.

**What it does.** `Executable.lean` gains the public `checkJaxScatterSupport` (the scatter compute
half graded by `jaxAssignSupported`, the scatter checker re-run; purely additive).
`EvalPlanCodegen.lean`: `renderAffineNodesArray`'s `.scatter` arm calls `renderScatterNode`
(compute-half tables, `dest_shape`, `dest_flat_index`), gated by `requireJaxScatterSupport`; new
`JaxCodegenError.scatterPlacementOutOfRange`; `.scan`, `.pointwise`, `.axiswise` still throw
`unsupportedStep`; the existing `b5ScatterRejectedBeforeEmission` guard stays true (it asserts the
einsum refusal) and gains a clarifying comment; new `#guard`s: donor scatter 0 table `#[0,2]`,
scatter 1 table `#[1,3]`, destination shape `#[4]`, the backstop (`scatterPlacementOutOfRange 0 [10] [0]`),
and `unsupportedStep 0` for einsumOnly and for `lowerCheckPlanToCandidate`. `ExecutableTest.lean`:
the stale header prose ("NO JAX rendering at all") is rewritten and two guards for
`checkJaxScatterSupport` are added; the existing "S-A Task 2" evidence-path guards are unchanged.

| File (under `leanncd/`) | Full blob after T1 | Prefix |
| --- | --- | --- |
| `LeanNCD/Eval/Plan/Executable.lean` | `205decd661a61e83245df0f9fa5da225ac1556a1` | `205decd6` |
| `experiments/jax_bridge/EvalPlanCodegen.lean` | `b7df0edda8bb1a65c2a20f3d6a7a2d795a31c9fd` | `b7df0edd` |
| `test/Eval/Plan/ExecutableTest.lean` | `d3c9434264762d496e05152995fdb2b9f8534b70` | `d3c94342` |

**Verify.** `lake-build.sh <worktree>/leanncd LeanNCD Eval.Plan.ExecutableTest JaxExperiment`
(background). Expect `Build completed successfully` and no `error:` line; the `#guard`s are
compile-time, so a green `JaxExperiment` build is the guard run. Counts: 0 new fixtures run here,
6 Lean mutants (`JS-T1-01..06`) are owned by this task and are run in section 7 after T3.
**Sibling-audit rows owned** (section 8): rows 1-5 and 12-13 (render arms, einsum arms, evidence path
unchanged, gate). **STOP:** `git apply --check` failure, blob mismatch, or any `error:` in the build.

### T2: ordered Python runtime, new Lean driver, differential verifier

**Patch** `T2-ordered-runtime-and-differential.patch` (5 files, +447 -4; three are new files).
**Commit subject:** `feat(jax): ordered scatter runtime and Lean-vs-JAX scatter differential`.

**What it does.** `evalplan_affine_runtime.py`: node-kind dispatch (`_exec_node`; a node without a
`kind` field is an assign; `"scatter"` goes to `_run_scatter_node`; an unknown kind raises
`ValueError`), the ordered fold, used by `run_plan_positional` and `run_named`. New
`EvalPlanScatterSmoke.lean` (a `lake env lean --run` driver: it runs the Lean dense worker on each fixture
in both precisions and emits the generated Python modules that the verifier loads). New `evalplan_scatter_smoke.py` (the verifier: reconstructs the
Lean bits and compares eager and jit). New `run-evalplan-scatter.sh`. `check-lean-drivers.sh`
registers the new driver (it now reports `all five drivers ran clean`).

**Fixtures** (donors in parentheses; all from `EvalPlanScatterSmoke.lean`):
f64 (10): `shift` (`Y[2*i+1]`, Scatter32OracleTest O2 placement: unwritten cells keep the 0 init),
`stride` (`Y[2*i]`, O1), `multi` (`Y[a+b]`, ParseProgramTest `S[a+b]`: a cell receives `[1e16, 1, 1]`;
forward fold `1e16`, reversed `1.0000000000000002e16`), `const` (`Y[i, =2]`), `contract` (`stride`
plus a contraction), `empty` (`axis i = 0`), `b5` and `b5Overlap` (donor `b5ScatterScheduled`: two
writers plus a collector; overlapping writers; after `prepareEvalPlan` a group is
`[scatter, scatter, assign]` writing private slots 2 and 3, the collector writing slot 4; only slot 4
is materialized, so `run_named` needed no change), `chain` (`stride` plus a later read of the
destination), `negZero` (`shift` with inputs `[-0.0, 0.0, 2.0]`: reduceId plus `-0.0` is `+0.0`, so a
copy-on-first-write runtime is caught). f32 (5): `stride32`, `multi32` (f32 collision order: `2^24`
forward, `2^24+2` reversed), `contract32`, `b5Overlap32`, `empty32` (clones with `tensor f32`).
Note: `Y[i+1] := ...` parses as a scan lookback (`scanAxisNotIter`), not a scatter, which is why
`shift` uses `Y[2*i+1]`. Also pinned: collision order (the reversed fold gives a different cell) and
the signed-zero and gradient (`grad` of `stride` is `[1,1,1]`) pins.

| File (under `leanncd/`) | Full blob after T2 | Prefix |
| --- | --- | --- |
| `experiments/jax_bridge/EvalPlanScatterSmoke.lean` | `3934eb727ca32a555e96c91d7d331bd4ae4bed4b` | `3934eb72` |
| `experiments/jax_bridge/check-lean-drivers.sh` | `fe35d10e28d70c5005a63afec11f4fa44ac9e593` | `fe35d10e` |
| `experiments/jax_bridge/evalplan_affine_runtime.py` | `6c2cbab9a89096c196aa83b125260843416996e8` | `6c2cbab9` (superseded by T6) |
| `experiments/jax_bridge/evalplan_scatter_smoke.py` | `db216aebbdacc3e950519390f4b9ff42b679ca2f` | `db216aeb` (superseded by T6) |
| `experiments/jax_bridge/run-evalplan-scatter.sh` | `354367d8667dfc279db46b350074249784bf74be` | `354367d8` |

**Verify** (after the first-time `bash <worktree>/leanncd/experiments/jax_bridge/setup-python.sh`,
about a minute, JAX 0.10.0 CPU): `bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-scatter.sh`
(about 51 s). Expect exit 0 and, for each precision, a line of the form
`<n> <dtype> scatter fixtures bit-identical to Lean (eager + jit)` with `n = 10` (binary64) and
`n = 5` (binary32), a `collision order pinned: ...` line in both runs, and in the binary64 run only
the line `signed-zero and gradient pins ok`. Then
`bash <worktree>/leanncd/experiments/jax_bridge/check-lean-drivers.sh` (about 29 s): last line
`all five drivers ran clean (Lean side only; the Python/JAX verifiers were not run)`.
**Sibling-audit rows owned:** 8-9 (runtime dispatch, unknown kind) and the B5-group case. 7 Python
mutants (`JS-T2-01..07`) are owned here; they run in section 7 after T6. **STOP:** a fixture that is
not bit-identical is a finding: report it with the fixture name and precision; do not touch the
verifier or the Lean driver.

### T3: end-to-end compute-half gate guard

**Patch** `T3-end-to-end-gate-guard.patch` (1 file, +17). **Commit subject:**
`test(jax): end-to-end compute-half gate guard for scatter rendering`.

**What it does.** Mutation `JS-T1-05` (removing `requireJaxScatterSupport` from `renderScatterNode`)
first SURVIVED the direct gate guard. T3 adds an end-to-end `#guard` at the end of
`EvalPlanCodegen.lean`: clone the donor's raw plan (`b5ScatterPrepared`), change only the first
scatter's compute algebra to max-plus, re-check, render; the render must be refused. It is the only
thing that kills `JS-T1-05`.

| File (under `leanncd/`) | Full blob after T3 | Prefix |
| --- | --- | --- |
| `experiments/jax_bridge/EvalPlanCodegen.lean` | `7eea46991b62b38ddea13a7d37fe7e26055096f4` | `7eea4699` (**supersedes the T1 row for this file**) |

**Verify.** `lake-build.sh <worktree>/leanncd JaxExperiment`; then run the Lean mutation manifest
(section 7: `--check`, then the full run). **The manifest's `expect` line numbers are valid only from
this commit on**: the T1 tip has fewer lines, so do not run the manifest before T3. Expect
`manifest OK: 6 entries`, then `6/6 cycles passed`; each entry restored byte-identically.
Sibling-audit row owned: 13 (tropical/Boolean/contextful/unary end to end). **STOP:** any
`JS-T1-xx` entry that FAILS (survives or breaks elsewhere) means a patch or hash differs from the
prototype: report, do not edit the manifest.

### T4: stdlib Python mutation runner

**Patch** `T4-python-mutation-runner.patch` (1 new file, +81). **Commit subject:**
`test(jax): Python mutation runner for the JAX scatter runtime`.

**What it does.** `mutation-manifest.sh` only builds Lake targets, so it cannot kill a mutation of a
Python file. `mutation_python_manifest.py` applies the same entry fields (`label`, `task`, `file`,
`old`, `new`, `expect`) with `runs` (`float64`/`float32`) in place of `targets`: it requires the
`old` string to occur exactly once, mutates `evalplan_affine_runtime.py` (or the verifier), runs the
verifier per `runs` against the pre-generated modules in `jax_bridge/.cache`, requires a non-zero
exit and every `expect` string, restores, checks the sha256, reruns green. Prints `PASS`/`FAIL`
lines.

| File (under `leanncd/`) | Full blob after T4 |
| --- | --- |
| `experiments/jax_bridge/mutation_python_manifest.py` | `dec4b4ea170e95a3f684be44921f8f1065e0ef52` |

**Verify.** Only a syntax check here:
`python3 -I -c "import ast,sys; ast.parse(open(sys.argv[1]).read())" <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py`
(exit 0). **Do not run the runner yet**: the committed manifest is the T6 (final) one, whose `old`
strings only exist after T6. **STOP:** blob mismatch or syntax error.

### T5: docs

**Patch** `T5-docs.patch` (2 files, +27 -1). **Commit subject:**
`docs(jax): scatter rendering is admitted in affineReference (ordered mode)`.

**What it does.** `LeanNCD/Eval/Plan/AGENTS.md`: the JAX-contract bullet (the one beginning "JAX is
context-free") now says a `.scatter` is rendered by `affineReference` only, einsumOnly and the
evidence path still refuse it as `unsupportedStep`, a scatter plan exposes no `ExecutionEvidence`,
and tropical/Boolean/contextful scatters stay refused by the compute-half gate.
`experiments/jax_bridge/README.md`: new section "Scatter steps (ordered mode, JAX scatter slice)" with
the refusal table and a pointer to the Python mutation manifest.

| File (under `leanncd/`) | Full blob after T5 | Prefix |
| --- | --- | --- |
| `LeanNCD/Eval/Plan/AGENTS.md` | `968fa0eb8227fcc5ebf94ae0a0cacbbea2eec5dc` | `968fa0eb` (superseded by T6) |
| `experiments/jax_bridge/README.md` | `748a46b7d437308b0a1a594ea07513fc45c44305` | `748a46b7` (superseded by T6) |

**Verify.** `git -C <worktree> diff --check` (no output). No build needed (markdown only).
**STOP:** blob mismatch.

### T6: fast mode (opt-in, tolerance-compared)

**Patch** `T6-fast-mode.patch` (4 files, +174 -11). **Commit subject:**
`feat(jax): fast vectorised scatter fold (opt-in, tolerance-compared)`.

**What it does.** `evalplan_affine_runtime.py`: `SCATTER_MODES = ("ordered", "fast")`,
`_require_scatter_mode`, `scatter_mode` on `run_plan_positional` and `run_named` (`run_assign`
unchanged), the fast fold and its trace-time range check. `evalplan_scatter_smoke.py`: `RTOL`, a
collision classifier, the fast-mode verification (collision-free tables bit-identical; colliding
tables compared within `RTOL`; random well-conditioned collision trials; a 1e-3 perturbation
self-test that caps `RTOL`; unknown mode and out-of-range rejection; the jaxpr `scatter-add`
presence check that proves which fold ran; B5 groups through `run_named` eager and jit; the
`jit(grad)` pin). Docs: `README.md` fast-mode paragraph, the same `AGENTS.md` bullet extended.
Fast-mode observations to expect: collision-free fixtures (the 8 f64 and 3 f32 whose tables never
collide: `shift`, `stride`, `const`, `empty`, `chain`, `negZero`, `b5`, `b5Overlap`, and `stride32`,
`b5Overlap32`, `empty32`) are bit-identical to Lean; `multi`, `contract` and their f32 clones collide
(`contract` collides because the contracted axis is a source coordinate, table `[0,0,0,2,2,2]`). On
CPU, XLA applies updates in order, so even the colliding fixtures are bit-identical (`multi` `1e16`,
`multi32` `16777216`; 200 random-normal trials per plan: 0 not bit-equal, worst relative difference
0.0). That proves nothing for other backends. `negZero` in fast mode: `zeros + (-0.0)` is `+0.0`,
bits 0, same as Lean. `jit(grad)` of `stride` through fast mode: `[1,1,1]`.

| File (under `leanncd/`) | Full blob after T6 | Supersedes |
| --- | --- | --- |
| `experiments/jax_bridge/evalplan_affine_runtime.py` | `954dc5aa6c9685949091b191da73a34829fb1780` (`954dc5aa`) | T2 row |
| `experiments/jax_bridge/evalplan_scatter_smoke.py` | `059d1b670e7af73fdc0e48abb972b90dc73b55ef` (`059d1b67`) | T2 row |
| `experiments/jax_bridge/README.md` | `b3ddbd137db7c2f120fce87d633fbf14033066f6` (`b3ddbd13`) | T5 row |
| `LeanNCD/Eval/Plan/AGENTS.md` | `3826c2d9b86c93426421c1681eda72524c066a84` (`3826c2d9`) | T5 row |

For these four files the T6 row replaces the earlier row; the other seven files keep the hash from
the task that last touched them (section 6 is the consolidated final table).

**Verify.** Re-run `run-evalplan-scatter.sh`: the T2 lines unchanged, plus these fast-mode lines (the
numbers in the first line are observed counts; the lines must be present and the run must exit 0):
`fast mode: <n> collision-free fixtures bit-identical to Lean, <m> colliding ...`,
`fast mode: random well-conditioned collisions within rtol <RTOL> of ordered`,
`fast mode: unknown scatter_mode and out-of-range placement rejected`,
`fast mode: ...` lines appear in both precisions; the last, `fast-mode gradient (jit(grad)) and
signed-zero pins ok`, only in the binary64 run. Then the Python mutation manifest (section 7).
Sibling-audit rows owned: 10-11 (mode validation, `run_assign` unchanged). 9 Python mutants
(`JS-T6-01..09`) owned here; `JS-T2-05` was repaired by one line in the committed manifest because the
added parameter changed the text it matches (meaning unchanged). **STOP:** a mutant that SURVIVES or
is NOT RESTORED, or any non-bit-identical collision-free fixture.

### T7: Intent Layer fix for the stale B5 bullet and the JAX run row

**Patch** `T7-agents-stale-bullet.patch` (1 file, 2 lines changed). **Commit subject:**
`docs(jax): Plan AGENTS B5 bullet and JAX run table reflect scatter rendering`.

**What it does.** In `leanncd/LeanNCD/Eval/Plan/AGENTS.md` the B5 bullet no longer says "the JAX
codegen fixture requires actual prepared scatter nodes to refuse before emission": it now says JAX
`affineReference` renders and runs a group's writer scatters while `einsumOnly` still refuses them
before emission (`b5ScatterRejectedBeforeEmission`). The "Run checked plans against JAX" entry-point
row gains `run-evalplan-scatter.sh`. This is the one live Intent Layer sentence that T5/T6 made
stale; fixing it here keeps the node true when the slice lands instead of leaving it for an audit.
Docs only; no code, build or fixture changes.

**Apply** from the worktree root: `git apply --check` then `git apply`
`papers/semantics/jax_scatter_patches/T7-agents-stale-bullet.patch`. Pre-image is T6's `AGENTS.md`
(`3826c2d9b86c93426421c1681eda72524c066a84`).

| File (under `leanncd/`) | Full blob after T7 | Supersedes |
| --- | --- | --- |
| `LeanNCD/Eval/Plan/AGENTS.md` | `ffe68114c7b540c81ed679a7e05700b8d95c3fc0` (`ffe68114`) | T6 row |

**Verify.** The blob; then `rg -n "refuse before emission" leanncd/LeanNCD/Eval/Plan/AGENTS.md` must
print nothing, and `rg -n "run-evalplan-scatter.sh" leanncd/LeanNCD/Eval/Plan/AGENTS.md` must print
one line. No build needed (Markdown only); the final verification order (section 7) covers the rest.
**STOP:** blob mismatch.

## 6. Final blob table (tip after T7; the 11 touched files)

Check once more with `git hash-object` after T7. Any mismatch is a STOP.

| File (under `leanncd/`) | Last touched by | Full blob |
| --- | --- | --- |
| `LeanNCD/Eval/Plan/Executable.lean` | T1 | `205decd661a61e83245df0f9fa5da225ac1556a1` |
| `experiments/jax_bridge/EvalPlanCodegen.lean` | T3 | `7eea46991b62b38ddea13a7d37fe7e26055096f4` |
| `test/Eval/Plan/ExecutableTest.lean` | T1 | `d3c9434264762d496e05152995fdb2b9f8534b70` |
| `experiments/jax_bridge/EvalPlanScatterSmoke.lean` | T2 | `3934eb727ca32a555e96c91d7d331bd4ae4bed4b` |
| `experiments/jax_bridge/check-lean-drivers.sh` | T2 | `fe35d10e28d70c5005a63afec11f4fa44ac9e593` |
| `experiments/jax_bridge/run-evalplan-scatter.sh` | T2 | `354367d8667dfc279db46b350074249784bf74be` |
| `experiments/jax_bridge/mutation_python_manifest.py` | T4 | `dec4b4ea170e95a3f684be44921f8f1065e0ef52` |
| `experiments/jax_bridge/evalplan_affine_runtime.py` | T6 | `954dc5aa6c9685949091b191da73a34829fb1780` |
| `experiments/jax_bridge/evalplan_scatter_smoke.py` | T6 | `059d1b670e7af73fdc0e48abb972b90dc73b55ef` |
| `experiments/jax_bridge/README.md` | T6 | `b3ddbd137db7c2f120fce87d633fbf14033066f6` |
| `LeanNCD/Eval/Plan/AGENTS.md` | T7 | `ffe68114c7b540c81ed679a7e05700b8d95c3fc0` |

## 7. Ordering, pre-flight and commands

**Ordering.** Apply T1 to T7 strictly in order (T7's `AGENTS.md` pre-image is T6's); each patch's pre-image is the previous patch's
post-image (T3's `EvalPlanCodegen.lean` pre-image is T1's blob; T6's runtime pre-image is T2's;
T6's `AGENTS.md`/`README.md` pre-images are T5's). The Lean manifest `expect` line numbers are valid
only from T3 on. The Python manifest is the final (T6) one and runs only after T6.

**Placeholders.** `<repo>` is the primary checkout, `/Users/williammacready/code/python/pyncd`.
`<worktree>`, `<wt>` and the execution worktree are one and the same path,
`<repo>/.claude/worktrees/jax-scatter-exec`.

**Pre-flight A (before creating the worktree; only `<repo>` exists).**
1. `git -C <repo> rev-parse main` must print `2cf922091cbd4550dfa141793d407ce1559f6b14`, or, once the
   package commit has landed on `main`, a descendant of it. If it prints something else, run
   `git -C <repo> diff --name-only 2cf92209 main`: if every path is under
   `papers/semantics/` (the package itself), continue; otherwise do not stop yet: after creating the
   worktree (section 1), run `git apply --check` for T1, apply it, `--check` T2, apply, and so on
   through T7, and **STOP and report on the first failure**; also record that the job count may
   differ from 8844.
2. `git -C <repo> status --short` shows nothing under `papers/semantics/jax_scatter*`, and
   `git -C <repo> log --oneline -3 -- papers/semantics/jax_scatter_plan.md` shows the package commit
   (`docs: JAX scatter slice package ...`). If it does not, the package has not landed: **STOP,
   report BLOCKED** (the owner lands it; do not merge the prototype branch `worktree-jax-scatter-plan`,
   which already contains the code the patches would add).

**Pre-flight B (after the worktree exists, `prepare-worktree.sh` has passed).**
3. `ls <worktree>/papers/semantics/jax_scatter_patches` lists `T1` to `T7`, and
   `ls <worktree>/papers/semantics/jax_scatter_mutations_post.json` and
   `ls <worktree>/papers/semantics/jax_scatter_mutations_python.json` succeed. If any is missing,
   **STOP, report BLOCKED**.
4. `git -C <worktree> status --short` is empty.
5. Environment: `setup-python.sh` runs `pip install` and needs network access. If it fails offline,
   **STOP, report BLOCKED**; do not substitute another JAX build.

**Commands** (run from outside the worktree with absolute paths, or with the working directory set to
`<worktree>`; `<wt>` = the worktree path). "Reported" is what the prototype observed.

| Purpose | Command | Reported |
| --- | --- | --- |
| Python environment, once | `bash <wt>/leanncd/experiments/jax_bridge/setup-python.sh` | JAX 0.10.0, `CpuDevice`, about 1 min |
| Full Lean build | `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd LeanNCD Tests JaxExperiment` | `Build completed successfully (8844 jobs)` |
| Scatter differential | `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-scatter.sh` | 10 f64 + 5 f32 bit-identical, about 51 s, plus the fast-mode lines of T6 |
| Lean-side drivers | `bash <wt>/leanncd/experiments/jax_bridge/check-lean-drivers.sh` | `all five drivers ran clean ...`, about 29 s |
| Lean mutations, check | `bash <wt>/leanncd/scripts/mutation-manifest.sh --check <wt>/leanncd <wt>/papers/semantics/jax_scatter_mutations_post.json` | `manifest OK: 6 entries` |
| Lean mutations, run | the same without `--check` (do not pass `--out`: a results file inside the worktree would leave it dirty; paste the table into the record instead) | `6/6 cycles passed` |
| Python mutations | `python3 <wt>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <wt>/papers/semantics/jax_scatter_mutations_python.json` (needs `run-evalplan-scatter.sh` run first, to create the generated modules in `jax_bridge/.cache`) | 16 `PASS` lines, exit 0 |
| Older verifier 1 | `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-affine.sh` | last line `Lean checked plan -> affine lookup tables -> ordered JAX reference -> Dense agreement passed` |
| Older verifier 2 | `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-affine32.sh` | last line contains `56 binary32 fixtures, 160 eager/jit output checks` |
| Older verifier 3, **corpus (3,832 cases, 10+ min, background)** | `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-affine-corpus.sh` | `full Wave C affine corpus -> ordered JAX reference -> Dense agreement passed` |

**The corpus verifier must be run by the executor.** The prototype ran it at the T5 tip and passed,
but did NOT re-run it after T6 (T6 edits `evalplan_affine_runtime.py`; the change is additive with an
`ordered` default, which is a belief, not a measurement). If it fails after T6, report the failing
case and STOP; do not edit the runtime.

**Final verification order after T7 (T6 is the last code patch; strictly serial):** full build; `check-lean-drivers.sh`;
`run-evalplan-scatter.sh`; Python mutation manifest; Lean mutation manifest (`--check`, then run);
`run-evalplan-affine.sh`; `run-evalplan-affine32.sh`; the corpus (background, nothing else running);
final `lake-build.sh ... LeanNCD Tests JaxExperiment` again (confirms the mutation restores);
`git -C <wt> status --short` empty; the section 6 hash table once more. (The Lean manifest can
equally be run right after T3; either position is fine, but only once all of T1-T3 are in.)

**Python-mutation caveats (record them, do not fix).** The `expect` strings are the verifier's generic
`AssertionError` source line; they do not name the killing fixture. `JS-T6-03/04/05` (default leaks,
fast used under ordered, ordered used under fast) are killed only by the jaxpr `scatter-add` presence
check because numeric results are identical on this CPU, inherent. `JS-T6-01` (`.set` instead of
`.add`) is killed by the jaxpr check first; the value checks were not isolated. "f32 through the f64
path" is not constructible in the float32 verifier (x64 off makes `jnp.float64` silently f32), so the
mirror case `JS-T2-06` (f32 destination inside an f64 run) is the pinned one. No admitted algebra has
a non-zero `reduceId`, so signed zero (`negZero`) is the only init-versus-first-write distinction; the
"ones" init mutant `JS-T2-02` is killed by `shift`.

## 8. Recurring-defect audit (step-kind handling: case x class)

The defect family: a step-kind rule stated in one place and silently ignored in a sibling. `R`
required, `F` forbidden (must stay refused), `S` silently ignored. Each row was observed by the
prototype; the guard or fixture that could fail is named. Owning tasks in section 5.

| # | Site | Case | Required behaviour | Pinned by | Class |
| --- | --- | --- | --- | --- | --- |
| 1 | `renderAffineNodesArray` | `.scatter` | rendered (tables, `dest_shape`, `dest_flat_index`) | T1 `#guard`s, T2 differential; mutant `JS-T1-04` | R |
| 2 | `renderAffineNodesArray` | `.scan`, `.pointwise`, `.axiswise` | `unsupportedStep` | unchanged arm; no mutant | F |
| 3 | `lowerPlan` (einsum) | `.scatter` | `unsupportedStep 0` | T1 guard (`generateNamed .einsumOnly`) | F |
| 4 | `lowerCheckPlanToCandidate` | `.scatter` | `unsupportedStep 0` | T1 guard | F |
| 5 | `stepTiedToPreparedStep` | scatter | refuses (no `ExecutionEvidence`) | existing "S-A Task 2" guards, unchanged and green | F |
| 6 | `assignPlans` in `EvalPlanAffineCorpus.lean` | the `.scatter _ \| .scan _ \| .pointwise _ \| .axiswise _ => none` arm | silently dropped | none; benign: the corpus generator emits no scatter and a comment says so | **S** |
| 7 | `b5ScatterRejectedBeforeEmission` | einsum refusal of a B5 scatter | still true | kept, with a clarifying comment | F |
| 8 | runtime `_exec_node` | node with a `kind` field | scatter handled | T2 differential; mutant `JS-T2-05` | R |
| 9 | runtime `_exec_node` | unknown `kind` | `ValueError` | T2 | F |
| 10 | runtime `run_plan_positional`/`run_named` | `scatter_mode` not in `("ordered","fast")` (`"bogus"`, `"Fast"`) | `ValueError("unsupported scatter_mode ...")` at entry | T6 verifier; mutant `JS-T6-06` | F |
| 11 | runtime `run_assign` | any `scatter_mode` | not a parameter: unchanged | by construction (no mode on the assign path) | S, benign |
| 12 | `checkJaxScatterSupport` | compute-half policy skipped | tropical/Boolean/contextful/unary refused | T1 `ExecutableTest` guards; mutant `JS-T1-06` | F |
| 13 | `renderScatterNode` | gate removed | refused end to end | T3 guard; mutant `JS-T1-05` | F |
| 14 | placement table | off by one / reversed order / out of range | wrong bits / error | mutants `JS-T1-01`, `-02`, `-03`; runtime `JS-T2-07`, `JS-T6-02`, `JS-T6-09` | R |

Rows 6 and 11 are known, benign silently-ignored cells; do not widen them (section 4).

## 9. Documentation and Intent Layer

The two documents that already carry the capability boundary ship inside T5/T6/T7:
`leanncd/LeanNCD/Eval/Plan/AGENTS.md` (the JAX-contract bullet) and
`leanncd/experiments/jax_bridge/README.md` (the scatter section). `experiments/jax_bridge/` has no
`AGENTS.md` node of its own.

**Deliberately NOT edited** (outside the slice's edit set; Rule 14; each is a stale sentence the
prototype named):

| Document | Stale sentence |
| --- | --- |
| `papers/backend_missing_functionality.md` | "rejects a `.scatter` step categorically ... no JAX scatter execution" |
| `papers/f32_jax_evalplan.md` | the "scan, scatter, pointwise/axiswise steps on JAX" refusal row (still true for the evidence path; "no JAX scatter ... exists" is stale) |
| Historical slice records | `additive_scatter_geometry_a_*`, `additive_s3a_record.md`, `additive_b5_mutation_results.md`, `f32_evalplan*.md`: history, left as written |

**Value-grep (run it; report, do not edit).**
`rg -n -i "jax" papers leanncd --glob '*.md' --glob '!papers/semantics/jax_scatter*' --glob '!leanncd/.lake/**'`
and keep the lines that also mention "scatter" (pipe the output to `rg -i scatter`). At authoring
that produced about 183 hit lines (a replay of the finished tree counted 184; do not treat a difference of a few lines as a finding), nearly all history (design/plan/record files of earlier slices and the
`scatter_affine_lhs_writes.md` family). Classify every hit that says JAX **refuses or lacks** scatter
as (a) history, (b) already updated, or (c) stale-live; list (c) in the record with file and
identifier, without editing. The authoring pass found these (c) candidates beyond the table above:
`papers/semantics/additive_production_decision_note.md` ("JAX refuses actual prepared scatter nodes
before emission"), `papers/semantics/additive_b5_design.md` (the JAX row "keep explicit
unsupported-step errors"), `papers/f32_evalplan.md` ("no JAX scan, scatter, nonlinearity ... exists"),
and, because it is a live Intent Layer node, the B5 bullet of
`leanncd/LeanNCD/Eval/Plan/AGENTS.md` ("JAX codegen fixture requires actual prepared scatter nodes to
refuse before emission": true only of the einsum refusal asserted by
`b5ScatterRejectedBeforeEmission`, no longer of `affineReference`). **That AGENTS sentence is fixed
by T7** (together with the JAX run row), so it must no longer appear in the value-grep; the three
papers above remain unedited. Any hit beyond these is reported in the record.

## 10. Close-out (executor writes `papers/semantics/jax_scatter_record.md`)

Required fields, each from a real run (no hand-derived values; a skipped step is stated as skipped):

1. Base and final commit hashes; the seven commit subjects and hashes (T1 to T7); `git -C <wt> log --oneline 2cf92209..HEAD`.
2. Pre-flight result (main equals `2cf92209` or the name-only diff, and which).
3. Per-task: apply-check result, blob table result (11 files at the end), build result.
4. Full build job count, compared with 8844 (any difference is stated and explained, not silently accepted).
5. `run-evalplan-scatter.sh`: the fixture-count lines (10 f64, 5 f32) and every fast-mode line, quoted.
6. Both mutation tables: 6 Lean and 16 Python lines (label, killed or survived, restored) and the
   `6/6` and `16 PASS` summaries, plus the `--check` line.
7. The three older verifiers' last lines, and the corpus case count and duration (the prototype never
   ran the corpus after T6).
8. `check-lean-drivers.sh` last line.
9. The section 9 value-grep: count, the (c) list, and whether any hit is new relative to the plan.
10. Measured token use and turn count per dispatch against Rule 6 (60 turns, 250k peak per dispatch;
    execution target about 175M total cumulative input tokens across dispatches). State "not
    measured" if you have no telemetry. State any breach.
11. Every skipped step, every STOP, every deviation from this plan.
12. Parked items: copy section 4 unchanged (owner: none).

**Stop point: do NOT merge.** The repository rule is that a branch merges to local `main` only after
the full build is green AND a whole-branch review is clean or its findings adjudicated; the executor
does not review its own work. So: once the full build, both manifests, the three older verifiers and
the corpus are green, commit the record (`docs: JAX scatter slice record`), leave the worktree and
branch `jax-scatter-exec` in place, and report "READY FOR WHOLE-BRANCH REVIEW" with the branch tip
hash. The owner's controller session runs the review and then performs the merge
(`git -C <repo> merge --no-ff jax-scatter-exec`, confirm `git -C <repo> diff --stat main
jax-scatter-exec` is empty, remove the worktree, delete the branch). **Never push**; `main` stays
ahead of `origin/main`. If any gate is red or a STOP fired, leave the branch and report.

## 11. Authoring evidence and reference budgets

Prototype: two dispatches (about 240k plus about 125k subagent tokens; about 100 plus about 58 tool
calls; the first breached the 60-turn cap, which is why execution is split in section 1). The
controller's independent re-verification at the T6 tip is listed in the record. Not verified at
authoring: the corpus after T6; fast mode on any backend other than this CPU; the patches replayed
here with a build (the prototype's chain replay onto a throwaway worktree matched all 11 hashes, but
the replay did not build). The executor's apply checks, hash table, builds and manifests are those
gates.
