# JAX pointwise and axiswise steps (affineReference, tolerance-compared): implementation plan

**Status: execution-ready package; execution not yet started.** Every line of code is already
written, verified and committed in a prototype worktree and shipped as six per-task patches in
[`jax_nonlin_patches/`](jax_nonlin_patches/); the executor replays, verifies and records, it does
not design. The patches were generated against local `main` at `f2616f54` and apply to any
descendant of it that has not touched the 12 files in section 6 (the commits that add this package
change only new files under `papers/semantics/`). **Process: Full path** (new capability, six
patches); GPT executes, the owner's controller session reviews and merges. Experimental JAX bridge
only: one core Lean file (`Nonlin.lean`) gains one additive public function, no new carrier, kernel
or plan IR. Prototype observations: [`jax_nonlin_files/FINDINGS.md`](jax_nonlin_files/FINDINGS.md).
How this plan was authored, and what is unverified: [`jax_nonlin_plan_record.md`](jax_nonlin_plan_record.md).
The execution record goes to `papers/semantics/jax_nonlin_record.md` (created by the executor,
section 10).

**Goal.** A prepared plan containing `.pointwise` steps (`relu`, `sigmoid`, `tanh`, `gelu`,
`leakyrelu`) or `.axiswise` steps (`softmax`, `normalize`, `l2normalize`, masked or not) renders in
`EvalPlanCodegen`'s `affineReference` mode and runs through JAX in binary64 and binary32, compared to
the Lean dense workers WITHIN A MEASURED TOLERANCE (the owner accepted tolerance; exactness is not
required). Behind it: the repo's single-layer transformer (`test/Eval/EvalExamplesTest.lean`
example 12) compiles to 14 checked nodes (10 assign, 3 axiswise, 1 pointwise); before this slice the
four nonlinear nodes were refused, so the model could not run through JAX.

**Scope in one paragraph.** Lean: `axiswiseIncludedPredicate` (one additive public wrapper in
`LeanNCD/Eval/Plan/Nonlin.lean`), `renderPointwiseNode`, `renderAxiswiseNode`, `buildAxiswiseInclude`
and the `axiswiseIncludeRefused` codegen error (`EvalPlanCodegen.lean`), seven new `#guard`s, a new
Lean driver (`EvalPlanNonlinSmoke.lean`). Python: node-kind arms and the nonlinear runtime in
`evalplan_affine_runtime.py`, a new verifier, a new runner script, a per-entry `verifier` field in
the stdlib mutation runner. Docs: the Plan `AGENTS.md` bullet, the jax_bridge `README.md`, the
runtime docstring, two `papers/` sentences. Nothing else.

## 1. Execution contract

Open every brief with this preamble (resolve `<worktree>` first):

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` or `$(...)` in a command, no heredocs,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`. Build Lean only with
> `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target...]`; never run `lake`
> from the worktree root. Stage files by explicit path. Stay within the stated turn and context
> budget and say so in the report if you breach it.

- **Worktree.** Run Pre-flight A (section 7) first. Create a linked worktree from local `main`
  (`/usr/bin/git -C <repo> worktree add <repo>/.claude/worktrees/jax-pointwise-exec -b jax-pointwise-exec main`;
  **if that branch or directory already exists, STOP and report; do not delete or reuse it**),
  then run `bash <worktree>/.claude/skills/new-slice/prepare-worktree.sh` WITH THE SHELL'S WORKING
  DIRECTORY SET TO `<worktree>` (the script refuses to run from the primary checkout, and `cd x && y`
  is forbidden: set the tool's working-directory parameter, or run
  `python3 -I -c "import subprocess; subprocess.run(['bash','<worktree>/.claude/skills/new-slice/prepare-worktree.sh'], cwd='<worktree>', check=True)"`). It must
  report Mathlib at or above 95% built, and the worktree base must be the `main` you checked in
  Pre-flight A (the stale-base trap: if the script reports a different base, STOP). If it starts a
  cold Mathlib build (hours), STOP. Then build `LeanNCD` once to refresh project oleans.
- **Do not push.** Local `main` stays ahead of `origin/main`; say so in the final report.
- **Patches are the code.** Apply the six patches in section 5 strictly in order T1 to T6, each
  after `git apply --check`. Do not retype code from this document (it has none). If a patch does not
  apply, or a post-apply blob differs from the section 5 table, STOP and report BLOCKED with the
  command output. **Do not repair a patch by hand, do not re-generate it, do not use
  `git apply --3way` or `--reject`.**
- **No relaxing to get green.** A fixture, guard, tolerance or mutation that fails is a finding to
  report, not something to loosen. Do not edit a manifest, a tolerance, a count or an `expect`
  string.
- **Prototype branch is not part of the package.** `worktree-jax-pointwise-plan` already contains the
  code the patches add: never merge it, never delete it, never copy from it, never touch its
  worktree `<repo>/.claude/worktrees/jax-pointwise-plan`.
- **Budget (Rule 6).** One dispatch is at most about 60 turns and 250k peak context. Suggested split:
  dispatch 1 = pre-flight, worktree, `LeanNCD` build, `setup-python.sh`, T1 (with its Lean mutation
  manifest, run once right after T1's build: section 5 T1), T2, T3; dispatch 2 = T4, T5, T6, the final
  verification in section 7 order, the value-grep and the record. A dispatch that nears 55 turns
  stops at a task or final-order step boundary (after the commit or the step), reports, and the next
  one resumes from
  `/usr/bin/git -C <worktree> log --oneline -8` (the commit subjects in section 5 say which tasks are
  done). Run builds, the manifests and the corpus in the background and wait for the completion
  notice; do not poll. No nested delegation. Report your own measured token use and turn count (from
  your own telemetry, `session.usage_record` deduplicated; if you have none, say "not measured").
  The prototype's reference points are in section 11.
- **Serial only.** Both mutation runners edit tracked files in place; the verifiers import
  `evalplan_affine_runtime.py`. Never run two of {a Lake build, a mutation manifest, the corpus, any
  verifier, `check-lean-drivers.sh`} at the same time.

## 2. Global constraints (exact values)

| Item | Value |
| --- | --- |
| Base commit | local `main` at `f2616f54` (full `f2616f54fd3a6eccc18a9d09d2870ced37ced5fa`) |
| Patches | 6, in `papers/semantics/jax_nonlin_patches/` (section 5) |
| Files touched in total | 12: 10 under `leanncd/`, 2 under `papers/` (section 6) |
| T1 build `LeanNCD Eval.Plan.ExecutableTest JaxExperiment` | printed `8619 jobs` at the prototype (the first build after the `Nonlin.lean` edit recompiles thousands of jobs: background) |
| Full build `LeanNCD Tests JaxExperiment` | `Build completed successfully (8844 jobs).`; the new driver is a `lake env lean --run` script outside every Lake target, so this equals `main`'s own count before the slice |
| `run-evalplan-nonlin.sh` internal builds | `lake build LeanNCD` printed `8615 jobs`, `lake build JaxExperiment` printed `8516 jobs` |
| Nonlinearity differential at the tip | 15 binary64 fixtures and 15 binary32 fixtures, eager and jit (section 5 T3 and T5 give the per-task counts) |
| Tolerance, binary64 | `rtol 1e-12`, `atol 1e-14` |
| Tolerance, binary32 | `rtol 1e-5`, `atol 1e-6` |
| Tolerance check | `abs(g - w) <= atol + rtol * abs(w)`, `g` = JAX, `w` = Lean |
| Lean mutation manifest | `papers/semantics/jax_nonlin_mutations_post.json`: 8 entries (`JN-T1-01..08`); `--check` prints `manifest OK: 8 entries, 8 selected, every old-string unique`; the real run ends `8/8 cycles passed.` |
| Python mutation manifest | `papers/semantics/jax_nonlin_mutations_python.json`: 17 entries (`JN-P-01..15` task field T2, `JN-P-16..17` task field T3), expect 17 `PASS` lines |
| Scatter Python manifest (regression) | `papers/semantics/jax_scatter_mutations_python.json`: 16 `PASS` lines with the T4 runner |
| `check-lean-drivers.sh` last line (after T6) | `all six drivers ran clean (Lean side only; the Python/JAX verifiers were not run)`; this is the FIRST observation of that exact line (the prototype only syntax-checked it after the text edit) |
| Python / JAX | `setup-python.sh`: JAX 0.10.0, CPU only (`CpuDevice`) |
| Corpus verifier | 3,832 cases (`run-evalplan-affine-corpus.sh`), about 11 minutes; NOT measured after this slice by the prototype |
| Record shape (exact observed texts, pinned by guards) | a pointwise node `{"kind": "pointwise", "source": 0, "dest": 1, "shape": [3], "fn": "relu"}`; an axiswise node adds `"axis_pos"`, `"fn"` and, only when masked, a row-major 0/1 `"include"` table |

## 3. Fixed semantics (what the patches implement)

1. **Records.** A pointwise node is `kind`, `source`, `dest`, `shape`, `fn`; an axiswise node is
   `kind`, `source`, `dest`, `shape`, `axis_pos`, `fn` and an `include` list only when the step is
   masked (an unmasked step omits the key). The record is dtype-free: the same plan retagged binary32
   renders the identical text.
2. **Mask evaluated in Lean (D3).** The runtime never sees a predicate. `buildAxiswiseInclude` builds
   the static `include` table through the dense worker's own predicate. The worker's
   `axiswiseIncluded` is private, so the one core edit is the additive public delegating wrapper
   `axiswiseIncludedPredicate` in `leanncd/LeanNCD/Eval/Plan/Nonlin.lean` (no existing body changes).
   A mask the worker refuses (unreachable for a checked plan, it is `maskWidthMismatch`) throws the
   located `JaxCodegenError.axiswiseIncludeRefused` rather than emit an unmasked table.
3. **No support gate (D4).** Unlike scatter there is no `checkJaxPointwiseSupport`. The evidence comes
   from `checkPlan`, which already ran `checkPointwise`/`checkAxiswise` (or the binary32 variants)
   under `raw.tensorSigs`, selected by the storage kind, and `renderAffineNodesArray` reads exactly
   that table. No standalone renderer takes a caller-supplied table, so a re-run could only repeat the
   check, and these steps have no compute half to grade. `Executable.lean` is untouched.
4. **Render only (D1).** `einsumOnly`, the evidence door (`lowerCheckPlanToCandidate`,
   `JaxExecutableWellFormed`), `.scan` and an inline unary read (`sqrt`, `exp`, `log`, `sin`, `cos`,
   reciprocal; refused by the assignment gate as `unaryFactor`) stay refused. The three Slice 5
   guards `testPointwiseStepRejectedLocated`, `testAxiswiseStepRejectedLocated` and
   `testMaskedAxiswiseStepRejectedLocated` call the evidence door and are unchanged.
5. **Runtime mirrors `LeanNCD.Eval.Nonlin` operation for operation.** relu is `where(0 <= x, x, 0)`
   (Lean `max 0 x`: `relu(NaN) = +0`; never `jnp.maximum`). Softmax row maximum and every row sum are
   sequential left folds (`fori_loop`) over the UNMASKED entries. Masked entries are 0; an all-masked,
   zero-sum or all-zero row is exactly 0. binary32 `gelu` and `leakyrelu` constants are the exact bit
   patterns of Lean's (`0x3F4C422A`, `0x3D372713`, `0x3C23D70A`).
6. **Comparison policy.** Within tolerance for everything (constants above). Exceptions that are
   required EXACT: relu is required bit-exact in the EAGER run only (under `jit` XLA drops the `+0`
   seed of the assignment copy, so `-0.0` survives; jit compares by value); every output value must
   be finite; the exact-zero pattern of masked, all-masked and zero-sum rows must match Lean. The
   transformer fixtures skip the "relu is bit-exact" rule and the per-function statistics, because the
   relu input already carries the upstream libm-versus-XLA difference.
7. **Observed margins (this machine's XLA CPU backend; observations, not guarantees).** binary64 worst
   absolute difference about `4.4e-16` (`atol` margin about 22 times); the binary32 gelu relative
   difference `2.458e-05` is above `rtol` but sits at an output near `3.6e-3`, so the `atol` term
   covers it (the binary32 gelu tolerance is absolute-driven, `atol` margin about 11 times). The
   per-function and per-output tables are in FINDINGS; the executor does not reproduce them.

## 4. Deliberately NOT done (no owner, none started)

The owner does not need the following. They are not owed by this plan, and each is listed so a
reviewer does not mistake silence for omission. Cost lines are the controller's estimate in dispatches
(one dispatch is the Rule 6 unit), not measurements.

| Not done | Consequence / cost line |
| --- | --- |
| **Unary reads on JAX** (`sqrt`, `exp`, `log`, `sin`, `cos`, reciprocal; LayerNorm with `eps`) | Still refused by the assignment gate (`unaryFactor`). Needs a domain-error decision first (Lean fails loud on a negative `sqrt`; `jit` cannot raise). About 1 to 2 dispatches. |
| **Scan on JAX** | `.scan` still throws `unsupportedStep` in `renderAffineNodesArray`. About 3 to 5 dispatches. |
| **The evidence path** for scatter, pointwise and axiswise (`JaxKernelCandidate` arm, `stepTiedToPreparedStep`, `ExecutableTest.lean` rewrite) | A scatter, pointwise or axiswise plan runs through JAX with no `ExecutionEvidence`. About 3 dispatches, do all three together; touches core `Executable.lean`; needs a fast-mode-versus-label style decision (scatter's `scatter_mode`). |
| Tropical and Boolean pointwise/axiswise steps | Not rendered; the plan-level storage gate of `affineReference` is inherited (section 8 notes it was not measured for these steps). Not estimated. |
| A raw-plan fixture that feeds a signed zero DIRECTLY into relu | Every surface program emits an assignment copy first (`+0 + -0 = +0`), so the eager bit-exactness of relu is exercised only through that copy. About 1 dispatch. |
| Factor the driver helpers duplicated across the smoke drivers (`pyTensorEntry32`, the named-fixture helpers) into `EvalPlanCodegen` | About 0.5 dispatch. |
| Measure the tolerance on a GPU or another XLA backend | Tolerances were measured on this CPU, not derived; other backends may differ more. Needs a GPU or another backend; not estimated. |
| `route` and diagram rendering (Python diagram stack, `Bridge/`, `tsncd`) | No owner and no estimate. |
| Lean-side gaps that stop other models (embedding gather, RoPE, ALiBi, data-driven masks) | Catalogued in `leanncd/test/Eval/Portfolio/KnownGapTest.lean`. Not part of this slice. |
| Edit the stale `papers/` sentences found by the section 9 value-grep | Reported, not edited (Rule 14). About 0.5 dispatch. |

## 5. Tasks

Patch files are named `T<n>-*.patch` under `<worktree>/papers/semantics/jax_nonlin_patches/`. The
literal procedure for every task, as separate plain commands (`<patch>` = the absolute path of that
task's patch, `<paths>` = every file in that task's blob table, written with its `leanncd/` or
`papers/` prefix):
1. `/usr/bin/git -C <worktree> apply --check <patch>` (prints nothing, exit 0, else STOP);
2. `/usr/bin/git -C <worktree> apply <patch>`;
3. `/usr/bin/git -C <worktree> hash-object <path>` for each path in the task table: the value must
   equal the **full** hash in that table (else STOP, BLOCKED);
4. `/usr/bin/git -C <worktree> add <paths>` (explicit paths only, never `-A` or `.`);
5. `/usr/bin/git -C <worktree> commit -m "<the exact subject given below>" -m "Applies <patch file name>"`
   plus the attribution trailer your environment requires as a further `-m` (no heredocs).
Then run the task's Verify step. The blob tables list paths relative to `leanncd/` unless the path
already starts with `leanncd/` or `papers/`.

### T1: Lean render of pointwise and axiswise steps, the include table, the Lean guards

**Patch** `T1-lean-render.patch` (2 files, +157 -2). **Commit subject:**
`feat(jax): render pointwise and axiswise steps in affineReference`.

**What it does.** `Nonlin.lean` gains the public wrapper `axiswiseIncludedPredicate`.
`EvalPlanCodegen.lean`: `renderAffineNodesArray`'s `.pointwise` and `.axiswise` arms call
`renderPointwiseNode` and `renderAxiswiseNode` (the latter calls `buildAxiswiseInclude`); `.scan`
still throws `unsupportedStep`; new `JaxCodegenError.axiswiseIncludeRefused`; a new section 11 at the
end of the file with seven `#guard`s: the exact record text of a pointwise relu node, of a masked
causal softmax node (`include` `[1, 0, 0, 1, 1, 0, 1, 1, 1]`) and of an unmasked `l2normalize` node;
the dtype-free check (binary32 retag renders the same text); the include table of a `s < q` clone
(`#[0, 0, 0, 1, 0, 0, 1, 1, 0]`); `einsumOnly` and `lowerCheckPlanToCandidate` still refuse all three
shapes with `unsupportedStep 0`; the fail-loud backstop (`maskWidthMismatch 2 1` from the checker,
`axiswiseIncludeRefused 7 (predicateWidthMismatch 2 1)` from the table builder).

| File (under `leanncd/`) | Full blob after T1 | Note |
| --- | --- | --- |
| `LeanNCD/Eval/Plan/Nonlin.lean` | `ae3536f1d078e456bc66fbb2b256d6741e891ab3` | final |
| `experiments/jax_bridge/EvalPlanCodegen.lean` | `3d54ef44ea4b136e95748f62856988c26a263358` | final (no later patch touches it) |

**Verify.** `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD Eval.Plan.ExecutableTest JaxExperiment`
in the background. Expect `Build completed successfully` (the prototype printed `8619 jobs`) and no
`error:` line; the `#guard`s are compile-time, so a green `JaxExperiment` is the guard run.
**Then the Lean mutation manifest, once, right here** (nothing else running; it edits
`EvalPlanCodegen.lean` in place): `bash <worktree>/leanncd/scripts/mutation-manifest.sh --check <worktree>/leanncd <worktree>/papers/semantics/jax_nonlin_mutations_post.json`
must print `manifest OK: 8 entries, 8 selected, every old-string unique`; then the same command without
`--check` (do NOT pass `--out`), in the background; expect `8/8 cycles passed.` and, afterwards,
`/usr/bin/git -C <worktree> status --short` empty and the T1 blob table still true. It is NOT repeated
in the final order: T2 to T6 never touch `EvalPlanCodegen.lean`, so the hash check at the end of
section 7 covers it. A `FAIL` or a survivor is a finding: STOP and report.
**Risk entry:** FIXTURE 0 run here (7 new `#guard`s compile); MUTATION 8 Lean mutants
(`JN-T1-01..08`) owned and run by this task. The manifest's `expect` line numbers are valid
from this commit on (no later patch changes `EvalPlanCodegen.lean`, the blob is identical at the tip).
**Sibling-audit rows owned** (section 8): 1 to 6 and 9. **STOP:** `git apply --check` failure, blob
mismatch, or any `error:` in the build.

### T2: nonlinear runtime, new Lean driver, differential verifier

**Patch** `T2-runtime-and-differential.patch` (5 files, +644; three are new files).
**Commit subject:** `feat(jax): pointwise and axiswise runtime and Lean-vs-JAX differential`.

**What it does.** `evalplan_affine_runtime.py`: the `_exec_node` arms for `"pointwise"` and
`"axiswise"`, `_run_pointwise_node`, `_run_axiswise_node` (shape, `axis_pos` and `include` length
checks that raise `ValueError`; unsupported function names raise `ValueError`). New
`EvalPlanNonlinSmoke.lean` (a `lake env lean --run` driver: it runs the Lean dense worker on each
fixture in both precisions and emits the generated Python modules the verifier loads). New
`evalplan_nonlin_smoke.py` (the verifier: reconstructs the Lean values, compares eager and jit under
the section 2 tolerance, relu bit-exact in eager, finite-value and exact-zero-pattern rules, a
tolerance self-test). New `run-evalplan-nonlin.sh`. `check-lean-drivers.sh` registers the driver
(the script then still says "five" in prose until T6 fixes it).

**Fixtures.** The driver holds the per-function fixtures (`pw`/`pw32` cover the pointwise functions
over one input that includes `0.0` and `-0.0`), plain and masked axiswise cases (inputs include a
zero-sum row, an all-zero row, large-magnitude rows, a first-axis case and a rank-3 case), and a
left-fold order probe (`order`, `order32`). The committed driver at this task holds 11 fixtures per
precision (counted by the controller from the committed driver text, `git grep -c` on the fixture call
lines at the T2 commit; the printed verifier line was only observed at the tip). Do not add, delete or
edit any.
Surface-language facts a reader may trip on: `T` is a reserved token in `tlprog!` (tanh outputs are
named `Th`); `explicitF64` (`test/Eval/ExplicitF64.lean`) is not importable here because
`run-evalplan-nonlin.sh` builds only `LeanNCD` and `JaxExperiment`, so every tensor is declared
`tensor f64 ...` by hand.

| File (under `leanncd/`) | Full blob after T2 | Note |
| --- | --- | --- |
| `experiments/jax_bridge/EvalPlanNonlinSmoke.lean` | `6bcc1472a8aba59af8162c80dbeb8db59e691b16` | superseded by T3, then T5 |
| `experiments/jax_bridge/check-lean-drivers.sh` | `2fdace3a552948c478a032fb23927a050b3b9ec8` | superseded by T6 |
| `experiments/jax_bridge/evalplan_affine_runtime.py` | `b6e15bd66b3ad3f4d865bb6f398989f872f5e3d4` | superseded by T6 |
| `experiments/jax_bridge/evalplan_nonlin_smoke.py` | `db391b7bf36def29022ce516bfcb34f421844e8a` | superseded by T3, then T5 |
| `experiments/jax_bridge/run-evalplan-nonlin.sh` | `e530c72793c0779bfc90ad8d766512a2eb679262` | final |

**Verify** (after the first-time `bash <worktree>/leanncd/experiments/jax_bridge/setup-python.sh`, about
a minute, JAX 0.10.0 CPU): `bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh`
(it builds `LeanNCD` and `JaxExperiment` itself; observed `8615` and `8516 jobs`; run it in the
background). Expect exit 0 and, per precision, a line of the form
`<n> float64 nonlinearity fixtures within rtol 1e-12 / atol 1e-14 of Lean (eager + jit)` and
`<n> float32 nonlinearity fixtures within rtol 1e-05 / atol 1e-06 of Lean (eager + jit)`. The value of
`<n>` should be 11 (the driver's fixture count at this commit; a different count with exit 0 is
recorded, not a STOP); a missing line or a non-zero exit is the STOP.
**Risk entry:** FIXTURE 11 per precision (counted from the committed driver text);
MUTATION 15 Python mutants (`JN-P-01..15`, task field T2) live in this code, run in section 7 after
T5 (the Python manifest needs T1 to T5). **Sibling-audit rows owned:** 11 to 13. **STOP:** a fixture
outside tolerance is a finding: report the fixture name, precision, and the printed difference; do
not touch the verifier, the Lean driver or the tolerance.

### T3: single-layer transformer through Lean and JAX

**Patch** `T3-transformer-fixture.patch` (2 files, +126 -9). **Commit subject:**
`test(jax): single-layer transformer through Lean and JAX`.

**What it does.** Adds the single-layer transformer (hand-chosen non-identity weights; `SEQ 3`, `D 4`,
`H 2`, `K 2`, `DFF 4`; the causal rows keep 1, 2 and 3 entries) to `EvalPlanNonlinSmoke.lean` in both
precisions, a Lean-side pin of the plan shape (14 checked steps = 10 assign, 1 pointwise, 3 axiswise),
and compares 10 materialized outputs (`Q K V S AttnOut Attn A F Y H`) in `evalplan_nonlin_smoke.py`.
The transformer's pure assignments (`Q`, `K`, `V`) are exact; everything downstream of an `exp` or a
normalize differs by about `1e-16` (binary64) or `1e-7` (binary32), inside the unchanged tolerances.

| File (under `leanncd/`) | Full blob after T3 | Note |
| --- | --- | --- |
| `experiments/jax_bridge/EvalPlanNonlinSmoke.lean` | `c33ebd773a301379cf5faa6e192d437691197a56` | **supersedes the T2 row**; superseded by T5 |
| `experiments/jax_bridge/evalplan_nonlin_smoke.py` | `ac4828cd5ace4afc2bc92036a7eb7f1c9297baa6` | **supersedes the T2 row**; superseded by T5 |

**Verify.** `run-evalplan-nonlin.sh` again (background). Expect exit 0 and the two
`nonlinearity fixtures within ... of Lean (eager + jit)` lines. The count `<n>` printed here should be
12 per precision (counted from the committed driver text at the T3 commit: the T2 11 plus the
transformer). A different count with exit 0 is recorded, not a STOP; the pinned 15 is the T5 gate.
Also expect the transformer plan-shape pin to hold (the driver asserts it; a failed assertion is the
STOP). **Risk entry:** FIXTURE 1 new per precision (the transformer), MUTATION 2 Python mutants
(`JN-P-16..17`, task field T3) live in this verifier; `JN-P-17` is killed only by a T5 canary.
**Sibling-audit row owned:** 14. **STOP:** blob mismatch, tolerance failure or shape-pin failure.

### T4: Python mutation runner accepts a per-entry verifier

**Patch** `T4-python-mutation-runner.patch` (1 file, +21 -12). **Commit subject:**
`test(jax): Python mutation runner accepts a per-entry verifier`.

**What it does.** `mutation_python_manifest.py` (introduced by the scatter slice) gains a per-entry
`verifier` field (the nonlin Python manifest sets `evalplan_nonlin_smoke` on every entry; the scatter
manifest has no such field, and the prototype re-ran it 16/16 with this runner) and runs the verifier
subprocesses with `PYTHONDONTWRITEBYTECODE=1`. The second change fixes a measured flake: a
same-size mutation restored within the same second leaves a bytecode file valid by whole-second
mtime and size, so the post-restore baseline once ran the mutant (`JN-P-12` reported
`NOT RESTORED/GREEN` once while `git status` was clean). The diagnosis is supported by the flake not
recurring in three further full runs, not proved by an isolated reproduction.

| File (under `leanncd/`) | Full blob after T4 | Note |
| --- | --- | --- |
| `experiments/jax_bridge/mutation_python_manifest.py` | `2ff09da131a8c728afa5b252cda42afda24e8c29` | final |

**Verify.** A syntax check only:
`python3 -I -c "import ast,sys; ast.parse(open(sys.argv[1]).read())" <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py`
(exit 0). **Do not run either Python manifest here**: the nonlin manifest needs T1 to T5, and the
scatter manifest needs the scatter driver's generated modules (section 7 runs it, after
`run-evalplan-scatter.sh`, in the final order; the prototype's one re-run printed 16 of 16 `PASS`).
**Risk entry:** FIXTURE 0, MUTATION 0 owned (the runner is exercised by both Python manifests in
section 7). **STOP:** blob mismatch or syntax error.

### T5: fixtures that kill the four first-run survivors

**Patch** `T5-survivor-fixtures.patch` (2 files, +51 -1). **Commit subject:**
`test(jax): fixtures that pin softmax row max, relu NaN and the compare path`.

**What it does.** Three new fixtures per precision and one verifier canary. `relu_nan`/`relu_nan32`:
a NaN input to relu alone; Lean `relu(NaN) = +0`, `jnp.maximum` would propagate NaN (kills
`JN-P-01`, "non-finite value"). `causal_big`/`causal_big32`: masked entries `1000`, `2000`, `900`, so a
row maximum taken over masked entries makes `exp(x - m)` underflow and the row collapse to zeros
(kills `JN-P-02`, "exact-zero pattern differs"). `aw_neglarge`/`aw_neglarge32`: rows all below `-999`,
so a row maximum folded from 0 collapses the row (kills `JN-P-03`, "exact-zero pattern differs"). A
canary in `main()`: `require_close` must reject a `1e-3` perturbed output end to end (kills `JN-P-17`).

| File (under `leanncd/`) | Full blob after T5 | Note |
| --- | --- | --- |
| `experiments/jax_bridge/EvalPlanNonlinSmoke.lean` | `3ca00cd9fd582b1e030eb17d83bef70aa4c993c6` | final |
| `experiments/jax_bridge/evalplan_nonlin_smoke.py` | `ee512bedf8e27ac115cb0d0fba0ca7dcd0ee5771` | final |

**Verify.** `run-evalplan-nonlin.sh` (background). Expect exit 0 and, quoted verbatim in the record:
`15 float64 nonlinearity fixtures within rtol 1e-12 / atol 1e-14 of Lean (eager + jit)`,
`15 float32 nonlinearity fixtures within rtol 1e-05 / atol 1e-06 of Lean (eager + jit)`, and, per
precision, `tolerance self-test: 1e-3 relative perturbation and a zeroed output are rejected`,
`require_close canary: a 1e-3 perturbed output is rejected end to end`,
`pins: relu(NaN) = +0, large-negative and huge-masked softmax rows are real distributions`, and the
line `relu signed zero: assign copy turns -0.0 into +0.0 in Lean; relu bit-exact in eager JAX`
(all four lines are printed unconditionally by the verifier's `main()`, so they appear once in the
`float64` run and once in the `float32` run; the executor quotes both). **Risk entry:** FIXTURE 3 new per precision (count 15 at this commit),
MUTATION 4 first-run survivors (`JN-P-01/02/03/17`) are killed by these additions. **STOP:** a count
other than 15 per precision, a missing pin line, or any tolerance failure.

### T6: docs and the driver-count text

**Patch** `T6-docs.patch` (6 files, +56 -7). **Commit subject:**
`docs(jax): pointwise and axiswise steps render in affineReference (tolerance-compared)`.

**What it does** (from the commit's file statistics and FINDINGS; the patch text was not read in
full at authoring). `LeanNCD/Eval/Plan/AGENTS.md` (4 lines changed): the live JAX-contract text
records that pointwise and axiswise steps render in `affineReference` with a tolerance comparison,
the other doors unchanged. `experiments/jax_bridge/README.md` (+43 -1, shown as 44 lines changed in the stat): documentation of this slice.
`check-lean-drivers.sh` (4 lines): the header and the final line say "six" (the new driver is the
sixth `run_driver`). `evalplan_affine_runtime.py` (+7): docstring text. `papers/f32_jax_evalplan.md`
and `papers/predicate_boolean_backend_parity.md` (2 lines each): the two stale sentences the slice
itself made untrue (the second is the "Superseded for masked axiswise" note on the JAX row of its
table).

| File | Full blob after T6 | Note |
| --- | --- | --- |
| `leanncd/LeanNCD/Eval/Plan/AGENTS.md` | `4ba20583a496519cf6896bfda150ee5f63f663b2` | final |
| `leanncd/experiments/jax_bridge/README.md` | `4288ceee620f16f1a9c4d0971f54294f505a1aaa` | final |
| `leanncd/experiments/jax_bridge/check-lean-drivers.sh` | `2388fcfc2d474e2c4d4c4c7fef00a1b3df13cfe4` | **supersedes the T2 row** |
| `leanncd/experiments/jax_bridge/evalplan_affine_runtime.py` | `14885bd688440249809e9220c572d3e1754efe5a` | **supersedes the T2 row** |
| `papers/f32_jax_evalplan.md` | `1c0549867857c14f1154cb97401d8735c059c8e7` | final |
| `papers/predicate_boolean_backend_parity.md` | `6137c6980c00cf122896f6e15814c5b11ab8f3d3` | final |

**Verify.** `/usr/bin/git -C <worktree> diff --check` (no output); `bash -n <worktree>/leanncd/experiments/jax_bridge/check-lean-drivers.sh`
(exit 0, no output); `rg -n "all five drivers" <worktree>/leanncd/experiments/jax_bridge/check-lean-drivers.sh`
prints nothing; `rg -n "all six drivers ran clean" <worktree>/leanncd/experiments/jax_bridge/check-lean-drivers.sh`
prints one line. No build is needed for this task; the section 7 final order covers the rest. The
`.py` change is a docstring edit: it must not change behaviour, and the section 7 verifiers are the
check. **Risk entry:** FIXTURE 0, MUTATION 0. **Sibling-audit row owned:** none (documentation).
**STOP:** blob mismatch, `git diff --check` output, or `bash -n` failure.

## 6. Final blob table (tip after T6; the 12 touched files)

Check once more with `/usr/bin/git -C <worktree> hash-object` after T6 and again at the very end. Any
mismatch is a STOP.

| File | Last touched by | Full blob |
| --- | --- | --- |
| `leanncd/LeanNCD/Eval/Plan/Nonlin.lean` | T1 | `ae3536f1d078e456bc66fbb2b256d6741e891ab3` |
| `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean` | T1 | `3d54ef44ea4b136e95748f62856988c26a263358` |
| `leanncd/experiments/jax_bridge/EvalPlanNonlinSmoke.lean` | T5 | `3ca00cd9fd582b1e030eb17d83bef70aa4c993c6` |
| `leanncd/experiments/jax_bridge/check-lean-drivers.sh` | T6 | `2388fcfc2d474e2c4d4c4c7fef00a1b3df13cfe4` |
| `leanncd/experiments/jax_bridge/evalplan_affine_runtime.py` | T6 | `14885bd688440249809e9220c572d3e1754efe5a` |
| `leanncd/experiments/jax_bridge/evalplan_nonlin_smoke.py` | T5 | `ee512bedf8e27ac115cb0d0fba0ca7dcd0ee5771` |
| `leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh` | T2 | `e530c72793c0779bfc90ad8d766512a2eb679262` |
| `leanncd/experiments/jax_bridge/mutation_python_manifest.py` | T4 | `2ff09da131a8c728afa5b252cda42afda24e8c29` |
| `leanncd/LeanNCD/Eval/Plan/AGENTS.md` | T6 | `4ba20583a496519cf6896bfda150ee5f63f663b2` |
| `leanncd/experiments/jax_bridge/README.md` | T6 | `4288ceee620f16f1a9c4d0971f54294f505a1aaa` |
| `papers/f32_jax_evalplan.md` | T6 | `1c0549867857c14f1154cb97401d8735c059c8e7` |
| `papers/predicate_boolean_backend_parity.md` | T6 | `6137c6980c00cf122896f6e15814c5b11ab8f3d3` |

## 7. Ordering, pre-flight and commands

**Ordering.** Apply T1 to T6 strictly in order. Pre-images chain: T3's `EvalPlanNonlinSmoke.lean` and
`evalplan_nonlin_smoke.py` pre-images are T2's blobs; T5's are T3's; T6's `check-lean-drivers.sh` and
`evalplan_affine_runtime.py` pre-images are T2's. The Lean manifest's `expect` line numbers are valid
from T1 on. The Python nonlin manifest runs only after T5 (T4 adds the runner's `verifier` field, T5
adds the fixtures that kill `JN-P-01/02/03/17`); its entries' `task` field (T2 for the runtime code,
T3 for the verifier lines `JN-P-16/17` mutate) says roughly where the mutated code lives, not when
the entry runs. The Lean manifest runs once, right after T1's build (section 5 T1); the Python
manifests run once, in the final order below.

**Placeholders.** `<repo>` is the primary checkout, `/Users/williammacready/code/python/pyncd`.
`<worktree>`, `<wt>` and the execution worktree are one and the same path,
`<repo>/.claude/worktrees/jax-pointwise-exec` (branch `jax-pointwise-exec`).

**Pre-flight A (before creating the worktree; only `<repo>` exists).**
1. `/usr/bin/git -C <repo> merge-base --is-ancestor f2616f54 main` must exit 0 (else **STOP**: `main`
   is not a descendant of the base the patches were generated against). Then run
   `/usr/bin/git -C <repo> diff --name-status f2616f54 main` and record its output in the record. After
   the package commit lands this is NEVER empty, so read it: continue only if every line starts with
   `A` (added) and names a path under `papers/semantics/` (the package) and none of the 12 files in
   section 6 appears. If any other line appears, do not stop yet: after creating the worktree, run
   the section 5 procedure (`apply --check`, apply) for T1 through T6 in order and **STOP and report
   on the first failure**; also record that the job count may differ from 8844. After
   `prepare-worktree.sh`, `/usr/bin/git -C <worktree> rev-parse HEAD` must equal
   `/usr/bin/git -C <repo> rev-parse main` (the stale-base trap: else STOP).
2. `/usr/bin/git -C <repo> status --short` shows nothing under `papers/semantics/jax_nonlin*`, and
   `/usr/bin/git -C <repo> log --oneline -3 -- papers/semantics/jax_nonlin_plan.md` shows the package
   commit. If it does not, the package has not landed: **STOP, report BLOCKED** (the owner lands it;
   do not merge the prototype branch `worktree-jax-pointwise-plan`, which already contains the code).

**Pre-flight B (after the worktree exists and `prepare-worktree.sh` has passed).**
3. `ls <worktree>/papers/semantics/jax_nonlin_patches` lists `T1-lean-render.patch`,
   `T2-runtime-and-differential.patch`, `T3-transformer-fixture.patch`,
   `T4-python-mutation-runner.patch`, `T5-survivor-fixtures.patch`, `T6-docs.patch`;
   `ls <worktree>/papers/semantics/jax_nonlin_mutations_post.json` and
   `ls <worktree>/papers/semantics/jax_nonlin_mutations_python.json` succeed, and so does
   `ls <worktree>/papers/semantics/jax_scatter_mutations_python.json`. If any is missing,
   **STOP, report BLOCKED**.
4. `/usr/bin/git -C <worktree> status --short` is empty.
5. Environment: `setup-python.sh` runs `pip install` and needs network access. If it fails offline,
   **STOP, report BLOCKED**; do not substitute another JAX build.

**Commands** (absolute paths; `<wt>` = the worktree). "Reported" is what the prototype observed.

| Purpose | Command | Reported |
| --- | --- | --- |
| Python environment, once | `bash <wt>/leanncd/experiments/jax_bridge/setup-python.sh` | JAX 0.10.0, `CpuDevice`, about 1 min |
| T1 build (background) | `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd LeanNCD Eval.Plan.ExecutableTest JaxExperiment` | `Build completed successfully`, `8619 jobs` |
| Full Lean build | `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd LeanNCD Tests JaxExperiment` | `Build completed successfully (8844 jobs).` |
| Nonlinearity differential | `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh` | 15 f64 + 15 f32 within tolerance, plus the T5 pin lines; duration not measured |
| Lean-side drivers | `bash <wt>/leanncd/experiments/jax_bridge/check-lean-drivers.sh` | last line `all six drivers ran clean (Lean side only; the Python/JAX verifiers were not run)` (first observation) |
| Python mutations, nonlin | `python3 <wt>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <wt>/papers/semantics/jax_nonlin_mutations_python.json` (needs `run-evalplan-nonlin.sh` run immediately before, for the generated modules in `jax_bridge/.cache`) | 17 `PASS` lines, exit 0 |
| Lean mutations, check (after T1's build) | `bash <wt>/leanncd/scripts/mutation-manifest.sh --check <wt>/leanncd <wt>/papers/semantics/jax_nonlin_mutations_post.json` | `manifest OK: 8 entries, 8 selected, every old-string unique` |
| Lean mutations, run (once, after T1's build) | the same without `--check` (do NOT pass `--out`: a results file inside the worktree would leave it dirty; paste the table into the record) | `8/8 cycles passed.` |
| Scatter differential | `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-scatter.sh` | `10 float64 scatter fixtures bit-identical to Lean (eager + jit)` and `5 float32 scatter fixtures bit-identical to Lean (eager + jit)` |
| Scatter Python mutations (regression) | `python3 <wt>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <wt>/papers/semantics/jax_scatter_mutations_python.json` (needs `run-evalplan-scatter.sh` run immediately before) | 16 `PASS` lines (one prior re-run: 16/16) |
| Older verifier 1 | `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-affine.sh` | last line `Lean checked plan -> affine lookup tables -> ordered JAX reference -> Dense agreement passed` |
| Older verifier 2 | `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-affine32.sh` | last line `56 binary32 fixtures, 160 eager/jit output checks: bit-identical to the Lean binary32 reference except the pinned KNOWN_DIVERGENT positions (x64 disabled)` |
| Older verifier 3, **corpus (3,832 cases, about 11 min, background)** | `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-affine-corpus.sh` | not measured after this slice |

**The corpus verifier must be run by the executor.** The slice adds node kinds the corpus never emits
(its generator drops non-assign steps, section 8 row 15), and T2 and T6 edit
`evalplan_affine_runtime.py`; that the corpus still passes is a belief, not a measurement. If it fails,
report the failing case and STOP; do not edit the runtime.

**Final verification order after T6 (strictly serial; one item at a time, each to completion):**
1. full build `LeanNCD Tests JaxExperiment` (expect 8844 jobs);
2. `check-lean-drivers.sh`;
3. `run-evalplan-nonlin.sh`;
4. the Python nonlin manifest (17 `PASS`);
5. `run-evalplan-scatter.sh`;
6. the scatter Python manifest (16 `PASS`);
7. `run-evalplan-affine.sh`;
8. `run-evalplan-affine32.sh`;
9. `run-evalplan-affine-corpus.sh` (background, nothing else running);
10. a final full build `LeanNCD Tests JaxExperiment` (confirms the mutation restores);
11. `/usr/bin/git -C <wt> status --short` empty;
12. the section 6 hash table once more (this also covers `EvalPlanCodegen.lean`, which the Lean
    manifest mutated and restored after T1).

Step 5 sits before step 6 because the scatter manifest runs against the generated modules that
`run-evalplan-scatter.sh` writes to `jax_bridge/.cache`; step 3 sits immediately before step 4 for the
same reason.

**Python-mutation caveats (record them, do not fix).** The `expect` strings are generic assertion
source lines observed from the first failing assertion, so a mutant dying for a different assertion
would not be distinguished by them (inherited from the scatter slice). The Lean manifest's `expect`
strings contain line numbers (`error: experiments/jax_bridge/EvalPlanCodegen.lean:<n>:0: Expression`)
only because they were copied from observed output; they are valid from T1 on. Observed: `JN-T1-01`
and `02` at lines 2285 and 2297; `03`, `04`, `07` at 2285; `05` at 2280; `06` at 2278; `08` at 2315.
(`06`'s 2278 looks wrong, a blank line before the first section 11 `#guard` at 2280: it is the line
number in the MUTATED file, where the three replaced arm lines became one, shifting every later line
up by two.)
`JN-P-08` was rewritten after its first version died of a `TypeError` instead of the guarded 0/0; the
committed entry is killed by "non-finite value".

## 8. Recurring-defect audit (step-kind handling: case x class)

The defect family: a step-kind rule stated in one place and silently ignored in a sibling. `R`
required, `F` forbidden (must stay refused), `S` silently ignored or unpinned. Every entry point in
`EvalPlanCodegen.lean` and `Executable.lean` that matches on a plan step kind was enumerated with
`rg -n "\.pointwise|\.axiswise|\.scatter|\.scan"` at authoring. The step-kind by door matrix first:

| Step kind | affineReference render | einsumOnly | Evidence (`lowerCheckPlanToCandidate`, `JaxExecutableWellFormed`) |
| --- | --- | --- | --- |
| pointwise | R: pinned by the record-text `#guard`, the differential, `JN-T1-05`, `JN-T1-06` | F: pinned by the T1 door `#guard` (`unsupportedStep 0`) | F: pinned by `testPointwiseStepRejectedLocated` (index 1) and the T1 door `#guard` (index 0) |
| axiswise, unmasked | R: pinned by the unmasked `l2normalize` record-text `#guard` and the differential; NO Lean mutant targets the unmasked branch (`JN-T1-03`, `JN-T1-07` die on the MASKED causal guard) | F: T1 door `#guard` | F: `testAxiswiseStepRejectedLocated`, T1 door `#guard` |
| axiswise, masked | R: pinned by the record-text and include-table `#guard`s, the differential, `JN-T1-01/02/04/08` | F: T1 door `#guard` | F: `testMaskedAxiswiseStepRejectedLocated`, T1 door `#guard` |
| scan | F: the `.scan` arm in `renderAffineNodesArray` is unchanged; **S (unpinned)**: no guard of this slice and no mutant covers it | F by the shared arm in `lowerPlan`; **S (unpinned)**: not verified that any guard exercises it | F: `testScanStepRejectedLocated` (index 1) |

The site table (owning tasks in section 5):

| # | Site | Case | Required behaviour | Pinned by | Class |
| --- | --- | --- | --- | --- | --- |
| 1 | `renderAffineNodesArray` | `.pointwise` | rendered, gate-free | T1 `#guard`s, differential; `JN-T1-05/06` | R |
| 2 | `renderAffineNodesArray` | `.axiswise` unmasked | rendered, no `include` key | T1 unmasked `l2normalize` record-text `#guard`; no Lean mutant targets this branch (`JN-T1-03/04/07` die on the masked guard) | R |
| 3 | `renderAffineNodesArray` | `.axiswise` masked | rendered with the row-major `include` | T1 `#guard`s; `JN-T1-01/02/04` | R |
| 4 | `renderAffineNodesArray` | `.scan` | `unsupportedStep` (node index) | unchanged arm; nothing fails if it is changed | F, **S (unpinned)** |
| 5 | `lowerPlan` (einsum, via `generateForward` and `generateNamed .einsumOnly`) | pointwise, axiswise | `unsupportedStep 0` | T1 door `#guard` | F |
| 6 | `lowerCheckPlanToCandidate` | pointwise, axiswise, masked, scan | located `unsupportedStep` | the four Slice 5 guards (unchanged) and the T1 door `#guard` | F |
| 7 | `stepTiedToPreparedStep` / `JaxExecutableWellFormed` (`Executable.lean`, untouched) | any non-assign step | `false` through its wildcard arm | no direct guard; reachable only by a hand-built candidate (the evidence door refuses first) | F, **S (unpinned)** |
| 8 | `renderAffinePlanPositional`, `renderAffinePlanNamed`, `generateNamed .affineReference` | storage kind (plan-level `requireModeStorage` before node iteration) | the same gate for every step kind | inherited; no pointwise/axiswise fixture under non-real storage; not measured | **S (not measured)** |
| 9 | `buildAxiswiseInclude` | a mask the worker refuses | `axiswiseIncludeRefused`, never an unmasked table | T1 backstop `#guard`; `JN-T1-08` | F |
| 10 | `renderAffineAssign`, `loweringToAffineTableCandidate`, `loweringToEinsumCandidate` | take a `CheckedAssignPlan` | no step kind to match | by type | N/A |
| 11 | runtime `_exec_node` | kind `pointwise` | handled | differential; `JN-P-01/10/11/12/15` | R |
| 12 | runtime `_exec_node` | kind `axiswise` (axis, include, folds) | handled | differential; `JN-P-02..09`, `JN-P-13/14` | R |
| 13 | runtime `_exec_node` | unknown `kind`; unknown pointwise/axiswise `fn` | `ValueError` | unknown `kind`: the scatter slice's pin (unchanged); unknown `fn`: no mutant, not verified that a fixture reaches it | F; `fn` case **S (unpinned)** |
| 14 | verifier tolerance, comparison and canary | tolerance made huge, output compared with itself | verifier fails | `JN-P-16`, `JN-P-17` (the latter killed only by the T5 canary) | R |
| 15 | `assignPlans` in `EvalPlanAffineCorpus.lean` | the non-assign arm | silently dropped | none; benign: the corpus generator emits no non-assign step (carried from the scatter plan; not re-read here) | **S, benign** |
| 16 | runtime `run_assign` | a node carrying a `kind` | not dispatched (assign-only entry) | by construction (no mode or dispatch on that path); what it does with such a node was not measured | **S, benign** |

Rows 15 and 16 are known and benign; do not widen them (section 4). Rows 4, 7, 8 and 13 (`fn` case)
are silently-ignored or unpinned cells that the slice did not create: **no guard or mutant kills a
regression in them**; they are listed so the reviewer can decide whether a later defect slice owns
them. The owner decision is recorded in the record (open decisions).

## 9. Documentation and Intent Layer

T6 ships the live documents that carry the capability boundary: the Plan `AGENTS.md` bullet, the
jax_bridge `README.md`, the runtime docstring, and one sentence in each of two papers.
`experiments/jax_bridge/` has no `AGENTS.md` node of its own. T6's first `check-lean-drivers.sh`
wording fix ("five" to "six") is the only prose that counted drivers.

**Value-grep (run it; report, do not edit).** From outside the worktree, with absolute paths:
`rg -n -i "JAX[^.]{0,80}(refus|reject|lack|no |not )[^.]{0,80}(pointwise|axiswise|nonlinear)|no JAX[^.]{0,60}nonlinear|masked axiswise[^.]{0,80}reject|(pointwise|axiswise|nonlinear)[^.]{0,80}(refus|reject)[^.]{0,60}JAX|five drivers|all five" <wt>/leanncd <wt>/papers --glob '!papers/semantics/jax_scatter_*' --glob '!papers/semantics/jax_nonlin_*' --glob '!**/jax_*_patches/**' --glob '!**/.lake/**' --glob '!**/.cache/**' --glob '!**/node_modules/**'`
and count the output lines. At authoring this printed **74 hit lines** in 41 files (a difference of a
few lines in the execution tree is not a finding). One of the 74 is the slice's OWN driver:
`leanncd/experiments/jax_bridge/EvalPlanNonlinSmoke.lean` line 142 ("All five pointwise functions over
one input") matches "all five"; it is class (a) and not a finding. The grep is line-based, so it cannot
see a sentence that wraps across lines: the executor ALSO runs
`rg -n -U -i "no\s.\.pointwise./.\.axiswise.\slowering" <wt>/papers --glob '!papers/semantics/jax_*'` and reports every hit (at authoring exactly one
sentence, printed as two output lines, 342 and 343 of the file below). Classification found at
authoring:

| Hit group | Class | Reason |
| --- | --- | --- |
| About 60 lines (74 minus the 13 lines in the rows below, an estimate) matching only "all five" or "All five" (Wave, F32, nonlinearity, plan-layer records and plans, spikes, `SORRY_INVENTORY.md`, test headers) | (a) history / unrelated (not each line read) | the matched phrase is a count of something else in the old documents; only the file names and the matched phrase were inspected, so a JAX-capability sentence hiding among them is not excluded |
| `papers/predicate_boolean_backend_parity.md` (the table row beginning "JAX \| Reject Iverson factors, masked axiswise") | (b) already updated | T6 appended a "Superseded for masked axiswise by the JAX pointwise slice" note to this row |
| `papers/predicate_boolean_backend_parity.md` ("Masked axiswise JAX rejection" row of a guard table) | (b) still accurate | it describes the located unsupported-step guard on the evidence door, which is unchanged |
| `papers/f32_evalplan.md` ("no JAX scan, scatter, nonlinearity, predicate, or f32 implementation exists") | (b) borderline | the sentence already carries a "Historical baseline" note naming F32-JAX and scatter, but the note does not mention pointwise/axiswise; owner may want the note extended |
| `papers/boolean_predicate_output_evalplan.md` ("JAX explicitly rejects Boolean, tropical, unary, contextful, Iverson, nonlinear, and scan") | (a) history | reclassified by the controller after reading the context: the line sits in a list under "Update current-state docs to say:" inside an old plan, i.e. an instruction of that plan, not a live statement; it is still true of `einsumOnly` and the evidence door |
| `papers/jax_evalplan_architecture.md` (a sentence wrapped over three lines: "the experiment simply has no `.pointwise`/`.axiswise` lowering yet and rejects those steps with a located `unsupportedStep`, so it is the natural next slice") | (c) stale-live | false for `affineReference` after this slice (still true of `einsumOnly` and the evidence door); invisible to the line-based grep, found by the independent reviewer; reported, not edited by the executor (Rule 14); the controller edits it after the slice lands |
| `papers/pre_scatter_backend_audit.md` | (a) history | a pre-scatter audit |
| masked-axiswise-reject lines in `papers/nonlinearity_split_pair_direct_lowering.md`, `papers/2026-08-20-thread-4-nonlinearity-plan-review.md`, and `leanncd/docs/superpowers/plans/` nonlinearity plans | (a) history | design and plan documents of the Lean nonlinearity thread |
| "five drivers" | none | zero hits; the only driver-count sentence, in `check-lean-drivers.sh`, says "six" after T6 |
| Plan `AGENTS.md`, `README.md` | not hits | edited by T6 and no longer match |

The executor re-runs the grep, reports the count, and lists every hit that says JAX refuses or lacks
a pointwise, axiswise or nonlinear step and is not in the table above as a NEW finding. The
stale-live list at authoring has ONE entry, `papers/jax_evalplan_architecture.md` (the wrapped
sentence above), and one borderline, `papers/f32_evalplan.md` (its historical-baseline note names
scatter but not pointwise/axiswise). The executor edits neither (Rule 14); the controller fixes both
after the slice lands (about 0.5 dispatch, no build).

## 10. Close-out (executor writes `papers/semantics/jax_nonlin_record.md`)

Required fields, each from a real run (no hand-derived values; a skipped step is stated as skipped):

1. Base and final commit hashes; the six commit subjects and hashes (T1 to T6);
   `/usr/bin/git -C <wt> log --oneline f2616f54..HEAD`.
2. Pre-flight result: the `merge-base --is-ancestor` exit code, the name-status diff `f2616f54..main`
   (quoted), and the worktree-HEAD equals `main` check.
3. Per-task: apply-check result, blob table result (12 files at the end), build or verify result
   (T1 build job count, the T1 Lean manifest `--check` line and `8/8` result, the `setup-python.sh`
   JAX line, the T4 `ast` syntax check, the T6 `git diff --check`, `bash -n` and grep results).
3b. Final-order steps 10 to 12 (the final rebuild job count, `git status --short` empty, the final
   hash-table comparison).
4. Full build job count, compared with 8844 (any difference is stated and explained).
5. The nonlinearity differential: the 15 + 15 fixture lines and every pin line quoted (tolerance
   self-test, canary, pins, relu signed zero), plus the T2 and T3 counts you observed.
6. Both mutation tables: 8 Lean and 17 Python lines (label, killed or survived, restored) with the
   `8/8` and `17 PASS` summaries and the `--check` line; also the scatter manifest's 16 `PASS`.
7. The last line of each older verifier (`run-evalplan-scatter.sh`, `run-evalplan-affine.sh`,
   `run-evalplan-affine32.sh`) plus the corpus case count and duration (first measurement after this
   slice).
8. `check-lean-drivers.sh` last line (the first observation of the "six" line).
9. The section 9 value-grep: count, the (c) list, and whether any hit is new relative to the plan.
10. Measured token use and turn count per dispatch against Rule 6 (60 turns, 250k peak per dispatch;
    execution target about 175M total cumulative input tokens across dispatches), method
    (`session.usage_record`, deduplicated; `token-report.py` is Claude-only and does not apply). State
    "not measured" if you have no telemetry. State any breach.
11. Every skipped step, every STOP, every deviation from this plan, and the confirmation that nothing
    was merged or pushed and the branch `jax-pointwise-exec` is waiting for review.
12. Parked items: copy section 4 unchanged (owner: none), plus any side issue you found, each with a
    one-line cost, not started (Rule 14).

**Stop point: do NOT merge.** The repository rule is that a branch merges to local `main` only after
the full build is green AND a whole-branch review is clean or its findings adjudicated; the executor
does not review its own work. So: once the full build, both nonlin manifests, the scatter manifest,
the older verifiers and the corpus are green, commit the record (`docs: JAX pointwise slice record`),
leave the worktree and branch `jax-pointwise-exec` in place, and report "READY FOR WHOLE-BRANCH
REVIEW" with the branch tip hash. The owner's controller session runs the review and then performs the
merge (`git -C <repo> merge --no-ff jax-pointwise-exec`, confirm `git -C <repo> diff --stat main
jax-pointwise-exec` is empty, remove the worktree, delete the branch). **Never push**; `main` stays
ahead of `origin/main`. If any gate is red or a STOP fired, leave the branch and report.

**The final message** states: the base commit and the branch tip; the six commit hashes and subjects;
per-task `git apply --check` results; the hash-table result per task and at the end (12 files);
per-task build results and the final job count; the nonlinearity differential lines; the Lean (8) and
Python (17) mutation tables with the `--check` line and the scatter 16; the last line of each older
verifier plus the corpus case count and duration; the `check-lean-drivers.sh` last line; the
value-grep count and its stale-live list; parked items with cost; measured tokens and method; every
skipped step or STOP; and the confirmation that nothing was pushed or merged.

## 11. Authoring evidence and reference budgets

Prototype: dispatch 1 (T1, T2) took 105 tool calls by the harness count against the 60-turn cap (its
own report said about 75) and about 206,818 subagent tokens; dispatch 2 (T3 and a draft of the Python
manifest) took 68 tool calls and about 130,294 tokens; the controller did the rest (T4, T5, both
manifests, T6, the patches, the replay) itself. Authoring totals are not measured as one figure. That
is why execution here is split in section 1 and why the executor, who only replays patches, should fit
each dispatch well under the cap.

Verified by the prototype controller (FINDINGS): the six patches replayed onto a throwaway tree at
`f2616f54` with `patch -p1 --fuzz=0`, all applied, and all 12 touched files hashed identically to the
prototype tip; the full build at the tip printed `8844 jobs`; the differential, the Python manifest
(17/17 after T5; the first run killed 13 and left 4 survivors) and the Lean manifest (`--check`, then
8/8) were run by the controller; the scatter slice's Python manifest re-ran 16/16 with the modified
runner; the three older verifiers were run after T2 only.

Verified by the plan author (this pass, by command): the six commits and their subjects; every full
blob in sections 5 and 6 (`rev-parse <commit>:<path>`, and the same 12 files at the tip); the Lean
manifest `--check` line; the entry counts (8 and 17) and labels; the file list of each commit; the
sibling-audit enumeration; the value-grep count. Not verified at authoring: any build, verifier or
manifest run (nothing was executed), `git apply --check` of the patch files against the base, the
per-precision fixture counts at T2 and T3, whether the corpus passes after this slice, anything on a
backend other than CPU, and the full text of the patches (only commit file statistics, the T5 fixture
diff and the guard section of `EvalPlanCodegen.lean` were read). The executor's apply checks, hash
table, builds, manifests and verifiers are those gates.
