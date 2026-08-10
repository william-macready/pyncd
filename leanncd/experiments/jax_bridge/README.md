# Lean-JAX bridge experiment

This isolated smoke test evaluates the
[`lean4-mlir`](https://github.com/brettkoonce/lean4-mlir) JAX bridge without
changing LeanNCD's dependencies or toolchain.

The upstream bridge is a code generator, not an in-process Lean/Python FFI:

1. [`BridgeSmoke.lean`](./BridgeSmoke.lean) defines a small `NetSpec`.
2. Upstream `JaxCodegen.generate` emits a Python module.
3. [`smoke.py`](./smoke.py) imports that module and checks eager evaluation,
   `jax.jit`, and `jax.grad`.

The runner pins upstream commit
`4f91e2a32d7eda0fc44f02a4b04c2fa0e5f59dab`. Its Lean 4.32.2 project is
cloned under the ignored `.cache/` directory, keeping it separate from
LeanNCD's Lean 4.30.0 project.

## Run

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

## Scope

This spike establishes that a Lean-authored network specification can reach
JAX execution and autodiff. It does not yet translate LeanNCD's tensor-logic
IR into upstream `NetSpec`; that adapter is the next integration boundary to
investigate.
