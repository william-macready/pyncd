# Lean-JAX bridge experiments

This directory holds five isolated experiment runners, none of which changes LeanNCD's dependencies
or toolchain:

- **`run.sh`**: upstream `NetSpec` -> generated JAX. Evaluates the
  [`lean4-mlir`](https://github.com/brettkoonce/lean4-mlir) JAX bridge, an upstream code
  generator that never runs LeanNCD's own Tensor Logic pipeline.
- **`run-evalplan.sh`**: Tensor Logic -> checked LeanNCD plan -> generated `jnp.einsum` -> JAX.
  Runs a Tensor Logic fixture through LeanNCD's own `compileToScheduled` / `prepareEvalPlan` /
  `CheckedEvalPlan` pipeline (see `docs/superpowers/plans/2026-08-10-jax-evalplan-smoke.md`), then
  through a narrow experimental Lean code generator (`EvalPlanSmoke.lean`) that emits a Python
  module containing a real `jnp.einsum` call.
- **`run-evalplan-affine.sh`**: curated source, checked-kernel, and positional-graph fixtures ->
  checker-produced affine lookup tables -> the ordered JAX reference runtime.
- **`run-evalplan-affine-corpus.sh`**: all 3,832 `PropertyOracle.enumPrograms` cases through the same
  affine reference, with eager full-output comparison and JIT feature representatives.
- **`run-scaling-probe.sh`**: one mid-sized (64x64, 4,096-coordinate) contraction through the same
  affine reference, measured against native `jnp.einsum` computing the same contraction — not a
  permanent test, a one-off measurement for `papers/jax_evalplan_architecture.md` §7.6 row 2.

## `run.sh`: upstream `NetSpec` bridge

The upstream bridge is a code generator, not an in-process Lean/Python FFI:

1. [`BridgeSmoke.lean`](./BridgeSmoke.lean) defines a small `NetSpec`.
2. Upstream `JaxCodegen.generate` emits a Python module.
3. [`smoke.py`](./smoke.py) imports that module and checks eager evaluation,
   `jax.jit`, and `jax.grad`.

The runner pins upstream commit
`4f91e2a32d7eda0fc44f02a4b04c2fa0e5f59dab`. Its Lean 4.32.2 project is
cloned under the ignored `.cache/` directory, keeping it separate from
LeanNCD's Lean 4.30.0 project.

### Run

From this directory:

```bash
./setup-python.sh
./run.sh
```

`setup-python.sh` creates an isolated CPU-only Python environment and installs
JAX 0.10.0 from the fully pinned [`requirements-cpu.txt`](./requirements-cpu.txt).
It uses Python 3.11-3.13 when available, otherwise it falls back to an installed
`conda` to create Python 3.12. The macOS system Python 3.9 is too old for JAX
0.10.0.

Set `PYTHON` to use an existing JAX environment instead:

```bash
PYTHON=/path/to/python ./run.sh
```

The first run fetches the pinned upstream repository and its Lean dependencies.
Later runs reuse everything under `.cache/`.

### Scope

This spike establishes that a Lean-authored network specification can reach
JAX execution and autodiff. It does not yet translate LeanNCD's tensor-logic
IR into upstream `NetSpec`. The checked-`EvalPlan` experiment below tests a
direct LeanNCD-to-JAX path instead of adding that adapter.

## `run-evalplan.sh`: checked `EvalPlan` -> `jnp.einsum` bridge

Unlike `run.sh`, this path never leaves LeanNCD's own project or toolchain, and never touches
upstream `NetSpec`:

1. [`EvalPlanSmoke.lean`](./EvalPlanSmoke.lean) compiles a Tensor Logic affine fixture
   (`Y[i] := W[i, j] · x[j] + b[i]`) with `compileToScheduled`, prepares it with
   `prepareEvalPlan`, runs it with `runPreparedDense`, and generates a Python module from the
   resulting `PreparedPlan` — reading only checker-produced positional data and source-name
   bindings, never source syntax or axis UIDs. It also confirms an affine-shift fixture
   (`Y[i] := A[i + 1]`) is rejected by a typed codegen error before any Python is emitted for it.
2. [`evalplan_smoke.py`](./evalplan_smoke.py) enables `jax_enable_x64`, reconstructs inputs and
   the independent Dense-computed expected output from the emitted `Float.toBits` payloads,
   AST-asserts the generated module contains a real `jnp.einsum("ab,b->a", ...)` call, and checks
   eager/`jax.jit` output is bit-identical to Dense and `jax.grad(sum(Y), W) == [[5], [5]]`.

### Run

From this directory:

```bash
./setup-python.sh
./run-evalplan.sh
```

`run-evalplan.sh` reuses the same experiment Python environment as `run.sh` (`.cache/python/bin/python`,
or `PYTHON` if set) and never invokes `run.sh` or clones/builds upstream `lean4-mlir`. It builds
`LeanNCD` (through Elan, from LeanNCD's own Lean 4.30.0 project root) before `lake env lean --run`,
so the generator never runs against stale `.olean`s, then generates
`.cache/generated_evalplan_smoke.py` and runs `evalplan_smoke.py` on it.

### Scope

This spike is a feasibility check that one real, scan-free Tensor Logic program can travel
through LeanNCD's own checked-plan boundary and execute as generated JAX. It is not a production
JAX backend: it accepts only projection-only affine `einsum` contractions in `f64`/`reference64`
mode, with no context positions, scans, or nonlinearities. See
`docs/superpowers/plans/2026-08-10-jax-evalplan-smoke.md` for the full exit criteria and
non-goals.

## Ordered affine reference and full corpus

`EvalPlanCodegen.lean`'s explicit `affineReference` mode emits static safe-index/mask tables built
from the same coordinate primitives as Dense. `evalplan_affine_runtime.py` interprets those tables
with ordered factor, reduction, and term folds; it does not use `einsum` or a tree reduction.

`run-evalplan-affine.sh` checks 20 curated fixtures eagerly and under JIT. These supply semantics
outside the generated grammar: negative-coordinate invalidity, zero-coefficient rows, zero extents,
empty factors, and empty terms. `run-evalplan-affine-corpus.sh` explicitly builds `LeanNCD`, `Tests`, and the
non-default `JaxExperiment` target, then generates and checks every corpus case and every
materialized output. The generated `.cache/` artifacts remain ignored.

Measured on the JAX CPU backend, 2026-08-10 and re-measured 2026-08-12:

- 3,832 source/eager cases, zero mismatches (both runs);
- 45 distinct generated feature masks and 65 JIT checks (45 representatives + 20 curated);
- 3,424,195-byte generated module (identical size on both runs; the runner records `artifact_bytes`
  only, so this is consistent with a deterministic generator but does not prove it — no digest is kept);
- of that module, the `safe_index`/`mask` literals are 571,459 bytes (~17%) across 28,106 literals;
  the rest is per-case keys, input tensors, and expected outputs, ~894 bytes per case;
- 13.482 s / 685.535 s / 7.317 s generation, eager, JIT+curated on 2026-08-10;
- 13.214 s / 661.263 s / 7.056 s on 2026-08-12.

The 2026-08-12 re-measurement followed a driver repair. Wave F F1 added `TermPlan.contextPos` and
`AssignPlan.contextShape`, and the hand-built plan literals in `EvalPlanAffineSmoke.lean` were
positional anonymous constructors of the pre-F1 arity, so they stopped compiling. Because the drivers
belong to no Lake target (`JaxExperiment` globs only `EvalPlanCodegen`), `lake build` stayed green and
both affine runners were silently unrunnable. The literals now use named-field syntax like the
`KernelDenseTest` fixtures, which survives field additions. **Run the runners after any change to
`Eval/Plan` types — a green `lake build` does not typecheck these drivers.**

Generated cases cover nonzero bias, non-unit/multi-axis coefficient rows, multiple factors/terms,
reduction domains, multiple graph nodes, and internal reads. Curated cases uniquely supply
negative-coordinate invalidity, zero-coefficient rows, zero extents, empty factors, and empty terms.
These are empirical binary64 results for the measured CPU platform, not a proof about every XLA
platform. Scan lowering remains future work.

## Scaling probe

`run-scaling-probe.sh` measures one mid-sized contraction — `Y[i] := Σⱼ W[i,j]·x[j]`, `i,j` both
ranging over 64, a 4,096-coordinate iteration domain, 1,024× the corpus's maximum of four — against
native `jnp.einsum` computing the same contraction. Not a permanent test: this converts
`papers/jax_evalplan_architecture.md` §5.4's affine-table scaling risk from code inspection into a
measurement (§7.6 row 2).

Measured on the JAX CPU backend, 2026-08-13 (JAX/JAXlib 0.10.0):

- 177,547-byte generated artifact from this one fixture — about 5% of the entire 3,832-case corpus's
  3,424,195 bytes;
- 34 µs affine-table JIT steady-state call (median of 20) versus 7 µs for native `jnp.einsum`, about
  4.9× slower — measured with `.block_until_ready()` inside the timed region, since unblocked JAX
  dispatch understates completion time;
- 340 ms / 15 ms first-call (eager) times for the affine path and native `jnp.einsum` respectively —
  both pay real XLA compilation on first call (`jax.lax.fori_loop`/`jax.vmap` compile their bodies
  even outside an outer `jax.jit`), so this gap overstates the steady-state one.

## Verified environment and commands

The completed smoke plan was verified on 2026-08-10 with:

- Lean 4.30.0 (`d024af099ca4bf2c86f649261ebf59565dc8c622`);
- Python 3.13.5;
- JAX/JAXlib 0.10.0;
- NumPy 2.5.2; and
- the JAX CPU backend.

The final validation commands were:

```bash
cd leanncd/experiments/jax_bridge
./run-evalplan.sh
./run-evalplan-affine.sh
./run-evalplan-affine-corpus.sh
./run.sh

cd ../..
"$HOME/.elan/bin/lake" build
```

All four experiment runners passed, and the complete Lean build finished with 8,642 jobs.
