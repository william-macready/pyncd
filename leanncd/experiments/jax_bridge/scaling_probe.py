"""One-off scaling measurement for `papers/jax_evalplan_architecture.md` §7.6 row 2.

Loads the Lean-generated affine table for one mid-sized contraction
(`generated_scaling_probe.py`, from `ScalingProbe.lean` / `KernelDenseTest.scalingProbePlan` —
`Y[i] := Σⱼ W[i,j]·x[j]`, `i,j` both ranging over 64, a 4,096-coordinate iteration domain versus the
existing corpus's maximum of 4), checks it is bit-identical to Dense eagerly and under `jax.jit`, and
times both against a native `jnp.einsum` computing the same contraction — the fast path the affine
table lowering exists instead of. Not a permanent test; run once, read the printed numbers, and record
them in the doc.
"""

from __future__ import annotations

import importlib.util
import math
import sys
import time
from pathlib import Path
from types import ModuleType

import jax

jax.config.update("jax_enable_x64", True)

import jax.numpy as jnp  # noqa: E402
import numpy as np  # noqa: E402

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

import evalplan_affine_runtime as rt  # noqa: E402


def load_generated_module(path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location("generated_scaling_probe", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load generated module from {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def reconstruct(entry: dict) -> jax.Array:
    shape = tuple(entry["shape"])
    bits = entry["bits"]
    size = math.prod(shape) if shape else 1
    arr = np.array(bits, dtype=np.uint64).view(np.float64)
    if arr.shape[0] != size:
        arr = np.zeros(size, dtype=np.float64)
    return jnp.asarray(arr.reshape(shape))


def require_bit_identical(actual: jax.Array, entry: dict, label: str) -> None:
    actual_np = np.asarray(actual)
    if actual_np.dtype != np.float64:
        raise AssertionError(f"{label}: expected float64, got {actual_np.dtype}")
    expected_shape = tuple(entry["shape"])
    if actual_np.shape != expected_shape:
        raise AssertionError(f"{label}: shape {actual_np.shape} != expected {expected_shape}")
    expected_bits = np.array(entry["bits"], dtype=np.uint64)
    actual_bits = actual_np.reshape(-1).view(np.uint64)
    if not np.array_equal(actual_bits, expected_bits):
        raise AssertionError(f"{label}: not bit-identical to Dense")


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} GENERATED_MODULE")

    generated_path = Path(sys.argv[1]).resolve()
    artifact_bytes = generated_path.stat().st_size

    rt.require_x64()
    module = load_generated_module(generated_path)
    f = module.FIXTURES[0]
    node = f["assign"]
    store = [reconstruct(e) for e in f["store"]]

    # --- affine-table path: eager, then JIT (compile + first call, then a steady-state call) -----
    t0 = time.perf_counter()
    eager = rt.run_assign(node, store)
    eager_s = time.perf_counter() - t0
    require_bit_identical(eager, f["expected"], "scalingProbe eager")

    jit_fn = jax.jit(lambda s: rt.run_assign(node, s))
    t0 = time.perf_counter()
    jitted = jit_fn(store)
    jit_compile_s = time.perf_counter() - t0
    require_bit_identical(jitted, f["expected"], "scalingProbe jit (compile+run)")

    t0 = time.perf_counter()
    jit_fn(store)
    jit_steady_s = time.perf_counter() - t0

    # --- comparison context: native jnp.einsum computing the identical contraction ----------------
    w = store[0]
    x = store[1]

    def einsum_fn(w_: jax.Array, x_: jax.Array) -> jax.Array:
        return jnp.einsum("ij,j->i", w_, x_)

    t0 = time.perf_counter()
    einsum_eager = einsum_fn(w, x)
    einsum_eager_s = time.perf_counter() - t0

    einsum_jit = jax.jit(einsum_fn)
    t0 = time.perf_counter()
    einsum_jit(w, x)
    einsum_jit_compile_s = time.perf_counter() - t0
    t0 = time.perf_counter()
    einsum_jit(w, x)
    einsum_jit_steady_s = time.perf_counter() - t0

    if not np.array_equal(np.asarray(einsum_eager), np.full(64, 64.0)):
        raise AssertionError("native einsum comparison did not reproduce the expected [64.0]*64")

    print(f"JAX {jax.__version__} on {jax.default_backend()}: {jax.devices()}")
    print(f"generated artifact: {artifact_bytes} bytes")
    print(f"affine-table eager: {eager_s:.6f} s")
    print(f"affine-table jit (compile+run): {jit_compile_s:.6f} s")
    print(f"affine-table jit (steady-state call): {jit_steady_s:.6f} s")
    print(f"native jnp.einsum eager: {einsum_eager_s:.6f} s")
    print(f"native jnp.einsum jit (compile+run): {einsum_jit_compile_s:.6f} s")
    print(f"native jnp.einsum jit (steady-state call): {einsum_jit_steady_s:.6f} s")
    print("affine-table result bit-identical to Dense (eager + jit) passed")


if __name__ == "__main__":
    main()
