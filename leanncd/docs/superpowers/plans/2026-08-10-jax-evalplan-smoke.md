# JAX evaluator smoke test for checked Tensor Logic plans

**Status:** draft, 2026-08-10

## Goal

Prove one real, scan-free Tensor Logic program can travel through the existing Wave C boundary and
execute as generated JAX:

```text
TLProgram
  -> compileToScheduled
  -> prepareEvalPlan
  -> PreparedPlan / CheckedEvalPlan
  -> experimental Lean code generator
  -> Python module containing jnp.einsum
  -> JAX eager, jax.jit, and jax.grad
```

This is a feasibility spike, not a production JAX backend. Its exit criterion is:

1. the affine Tensor Logic fixture below evaluates to `Y = [11, 16]` through
   `runPreparedDense`;
2. the same checked plan generates a Python module whose contraction is an actual
   `jnp.einsum` call;
3. JAX eager and `jax.jit` produce bit-identical `float64` output to Dense for this fixture;
4. `jax.grad` through the generated function produces the expected finite gradient; and
5. an otherwise valid checked plan containing an affine shift is rejected by a typed codegen
   error rather than silently lowered incorrectly.

If any step requires bypassing `prepareEvalPlan`, reconstructing the source equation by hand in
Python, or translating through upstream `NetSpec`, the spike has failed its purpose.

## Fixed design decisions

- **Input is `PreparedPlan`, not source syntax or `RawEvalPlan`.** Code generation reads only the
  checker-produced plan and its source-name bindings. Raw plans cannot execute.
- **Generate Python directly.** Do not add a JSON schema or a Python plan interpreter for this
  one-fixture spike. The generated module is the cross-toolchain artifact.
- **Do not use `NetSpec`.** It is upstream `lean4-mlir`'s sequential layer-list IR and cannot
  represent LeanNCD's checked assignment graph without a separate semantic translation.
- **Use the current LeanNCD toolchain for generation.** The new smoke runner must not enter the
  pinned upstream Lean 4.32.2 project or fetch/build upstream Mathlib. It invokes LeanNCD's warm
  Lean 4.30.0 build, while the existing isolated Python environment supplies JAX.
- **`einsum` only, with explicit rejection.** This slice accepts projection-only affine maps and
  emits `jnp.einsum(..., optimize=False)`. It does not implement a generic gather/zero-padding
  fallback.
- **Reference numeric mode.** Enable `jax_enable_x64` before importing the generated module. The
  smoke fixture uses exactly representable values so bit equality is meaningful and stable.
- **F1 compatibility, not F1 dependence.** If Wave F F1 has landed before execution, top-level
  assignments must have empty `contextShape` and every term empty `contextPos`; otherwise codegen
  returns a typed unsupported-context error. No scan block or contextual invocation is lowered.
- **Experiment isolation.** Add files under `leanncd/experiments/jax_bridge/`; do not add a JAX
  dependency to `lakefile.toml`, change `LeanNCD`'s public plan types, or register the experiment in
  the default Lean build.

## Exact admitted fragment

One checked assignment term is `einsum`-eligible only when all of the following hold:

- it has at least one factor;
- every affine-map bias is zero;
- every affine-map row contains exactly one coefficient `1` and all other coefficients are zero;
- every output and reduction iteration position occurs in at least one factor subscript;
- no context position is present;
- the iteration rank fits the deterministic ASCII label table used by the generator; and
- the checked plan remains in Wave C's admitted `f64`, real sum-product, `reference64` mode.

Repeated use of one iteration label in a source subscript is allowed, since `einsum` gives it
diagonal semantics. General affine coefficients, shifts, zero-padded reads, unused reduction
positions that contribute multiplicity, output-only broadcast positions, factor-free constant
terms, and context coordinates are rejected. Each rejection condition gets a closed
`JaxCodegenError` constructor carrying node/term/factor/row location where applicable.

For each eligible term:

1. assign one deterministic letter to each iteration-basis position;
2. derive each factor's input subscript from its projection rows;
3. derive the output subscript from `outputPos`;
4. emit one `jnp.einsum` call; and
5. combine term results with `+` in the checked term-array order.

For the fixture below, the core generated assignment should be equivalent to:

```python
term0 = jnp.einsum("ab,b->a", slots[0], slots[1], optimize=False)
term1 = jnp.einsum("a->a", slots[2], optimize=False)
slots[3] = term0 + term1
```

The test must derive and inspect the generated code; this example is not permission to hard-code
the equation.

## Verified fixtures

The exact Lean fixtures are:

```lean
import LeanNCD.Eval.Plan.Adapter
import LeanNCD.DSL.Compile

namespace LeanNCD.Eval.Plan.JaxSmoke

open LeanNCD LeanNCD.Eval Std

def affineProg : TLProgram := tlprog!{
  Y[i] := W[i, j] · x[j] + b[i]
}

def affineInputs : HashMap String DenseTensor :=
  HashMap.ofList
    [ ("W", ⟨[2, 1], #[2.0, 3.0]⟩)
    , ("x", ⟨[1], #[5.0]⟩)
    , ("b", ⟨[2], #[1.0, 1.0]⟩) ]

def shiftedProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i + 1]
}

end LeanNCD.Eval.Plan.JaxSmoke
```

Pre-flight observations made while drafting this plan:

- the assembled Lean block above compiles through
  `.claude/skills/slice-plan/check-snippet.sh`;
- the existing `Eval.Portfolio.FeedforwardTest` FF4 fixture ran through the real evaluator and
  observed `[11, 16]`;
- JAX 0.10.0 with x64 enabled produced eager and JIT output `[11, 16]`, and
  `grad(sum(Y), W) = [[5], [5]]`, for the planned `einsum` expression; and
- removing the bias term produced `[10, 15]`, and the exact-output assertion failed. The parity
  fixture therefore observes ordered term combination rather than only the contraction.

## Task 1: Generate JAX from one checked plan

Add `leanncd/experiments/jax_bridge/EvalPlanSmoke.lean`.

The file owns both the narrow experimental code generator and the executable fixture driver; do
not create a production `LeanNCD.Eval.Plan.Jax` module for one consumer.

Implement:

1. a closed `JaxCodegenError` type for every unsupported matcher condition described above;
2. deterministic Python string rendering, including safe quoting of source names;
3. projection-row recognition and deterministic `einsum` subscript construction;
4. assignment-node emission in checked graph order;
5. positional slot initialization from `PreparedPlan.bindings.requiredInputs`;
6. materialized output reconstruction from `PreparedPlan.bindings.materializedNames`, preserving
   last-write-wins behavior for repeated source names;
7. generated static shape checks for external inputs before evaluation; and
8. fixture preparation, Dense execution, and generated-module writing from `main`.

The driver must:

- compile `affineProg` with `compileToScheduled`;
- prepare it with `prepareEvalPlan` and `InputSignature.ofDenseInputs affineInputs`;
- run `runPreparedDense`;
- require Dense `Y` to equal shape `[2]`, values `[11, 16]`;
- emit input shapes and `Float.toBits` payloads into the generated module;
- emit Dense output bits into the generated module as the independent expected result;
- generate `forward(inputs)`, which returns source-name-keyed materialized outputs; and
- compile and prepare `shiftedProg`, then require codegen to return the specific affine-bias
  rejection constructor.

Do not use `getD`, placeholder expressions, or a success-shaped fallback in the code generator.
Checked-plan invariants may be trusted, but every restriction added by this narrower backend must
fail explicitly.

### Task 1 verification

Run:

```bash
cd leanncd
"$HOME/.elan/bin/lake" build LeanNCD
"$HOME/.elan/bin/lake" env lean --run \
  experiments/jax_bridge/EvalPlanSmoke.lean \
  experiments/jax_bridge/.cache/generated_evalplan_smoke.py
```

Inspect the generated file and confirm:

- it contains no source-level Tensor Logic syntax or axis UIDs;
- it obtains external tensors through the emitted binding names;
- the contraction subscript is derived as `"ab,b->a"`; and
- the shifted-read fixture failed before any Python was emitted for it.

Commit the Lean generator and driver as one unit. They have one failure mode and one execution
cycle, so splitting the error type, matcher, and driver into separate tasks would add review
overhead without an independently approvable boundary.

## Task 2: Execute, differentiate, and prove the `einsum` path

Add:

- `leanncd/experiments/jax_bridge/evalplan_smoke.py`;
- `leanncd/experiments/jax_bridge/run-evalplan.sh`; and
- documentation updates in `leanncd/experiments/jax_bridge/README.md` and `leanncd/AGENTS.md`.

`run-evalplan.sh` must:

1. locate LeanNCD's root and invoke Lake there through Elan;
2. use the existing experiment Python at `.cache/python/bin/python`, or an explicit `PYTHON`;
3. tell the user to run `setup-python.sh` when JAX is absent;
4. build the required LeanNCD target before `lake env lean --run`, avoiding stale oleans;
5. generate `.cache/generated_evalplan_smoke.py`; and
6. invoke `evalplan_smoke.py` on that generated module.

It must not invoke the existing upstream-oriented `run.sh`, clone `lean4-mlir`, or run a cold
Mathlib build.

`evalplan_smoke.py` must:

1. enable JAX x64 before loading the generated module;
2. reconstruct inputs from the Lean-emitted shapes and `Float.toBits` payloads;
3. parse the generated source with Python's `ast` module and require a real
   `jnp.einsum("ab,b->a", ...)` call;
4. run eager `forward`;
5. run `jax.jit(forward)`;
6. reconstruct Dense expected outputs from emitted bits;
7. require eager and JIT outputs to be bit-identical to Dense;
8. differentiate `sum(Y)` with respect to `W` and require `[[5], [5]]`; and
9. print the generated lowering kind, outputs, and gradient on success.

The AST assertion is required in addition to numeric equality: a hand-written `@`, `matmul`, or
constant result could produce `[11, 16]` without answering whether an `einsum` expression passed
through the bridge.

### Task 2 mutation checks

Before considering the task complete:

- remove the generated bias-term addition and confirm parity fails with `[10, 15]`;
- replace the generated `jnp.einsum` call with numerically equivalent `jnp.matmul` and confirm the
  AST assertion fails while the numeric assertion still passes; and
- disable x64 setup and confirm the dtype/bit assertion fails rather than accepting float32.

Restore each mutation and rerun the smoke test after every check.

### Task 2 verification

Run:

```bash
cd leanncd/experiments/jax_bridge
./setup-python.sh
./run-evalplan.sh
```

Then run the existing upstream smoke test to prove the new runner did not disturb it:

```bash
./run.sh
```

Finally run the full Lean build:

```bash
cd leanncd
"$HOME/.elan/bin/lake" build
```

The README must distinguish the two experiments:

- `run.sh`: upstream `NetSpec` -> generated JAX; and
- `run-evalplan.sh`: Tensor Logic -> checked LeanNCD plan -> generated `jnp.einsum` -> JAX.

`leanncd/AGENTS.md` must list the experiment from an existing entry point so a reader looking for
future fast backends can find it.

## Whole-branch review gate

After both tasks:

1. review the complete branch against this plan, not only each task diff;
2. confirm every codegen branch either emits supported semantics or returns a typed error;
3. confirm generated code depends on checked positional data, not source syntax or the hard-coded
   fixture;
4. confirm the AST test would reject a numerically equivalent non-`einsum` lowering;
5. confirm no Lean/JAX dependency leaked into `lakefile.toml` or the default public API;
6. confirm both smoke runners and the full Lean build pass; and
7. record exact toolchain/JAX versions and commands in the README.

## Explicit non-goals and follow-up

This slice does not add:

- general affine gathers, shifts, strides, or zero padding;
- broadcasting or multiplicity for iteration positions absent from factor maps;
- pointwise nonlinearities, predicates, max/min, or non-`f64` dtypes;
- contextual F1 execution, plan blocks, scans, or `lax.scan`;
- parameter initialization, training loops, optimizer state, or persistence;
- a stable serialized plan format;
- a production backend API; or
- a claim that arbitrary `reference64` contractions remain bit-identical under all XLA
  reassociations.

If the spike passes, the next design decision is whether to promote this into a checked JAX
backend with two explicit lowering paths:

1. a proven-recognized `einsum` fast path for projection contractions; and
2. a generic affine-gather fallback matching `runDenseAssignAt`.

That promotion should be planned separately. Scan lowering remains downstream of Wave F's checked
block and scan semantics, not part of this experiment.
