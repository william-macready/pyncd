"""One-off scaling measurement for `papers/jax_evalplan_architecture.md` §7.6 row 2.

Loads the Lean-generated affine table for one mid-sized contraction
(`generated_scaling_probe.py`, from `ScalingProbe.lean` / `KernelDenseTest.scalingProbePlan` —
`Y[i] := Σⱼ W[i,j]·x[j]`, `i,j` both ranging over 64, a 4,096-coordinate iteration domain versus the
existing corpus's maximum of 4), checks it is bit-identical to Dense eagerly and under `jax.jit`, and
times both against a native `jnp.einsum` computing the same contraction — the fast path the affine
table lowering exists instead of. Every timed JAX call is followed by `.block_until_ready()` inside
the timed region (JAX dispatch is asynchronous; without this a `perf_counter` delta measures dispatch
overhead, not completion) and steady-state numbers are the median of 20 repeated calls, not one
sample. Not a permanent test; run once, read the printed numbers, and record them in the doc.
"""

from __future__ import annotations

import statistics
import sys
import time
from pathlib import Path

import jax

jax.config.update("jax_enable_x64", True)

import jax.numpy as jnp  # noqa: E402
import numpy as np  # noqa: E402

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

import evalplan_affine_runtime as rt  # noqa: E402
from evalplan_affine_smoke import (  # noqa: E402
    load_generated_module,
    reconstruct,
    require_bit_identical,
)

STEADY_STATE_REPEATS = 20


def timed_call(fn) -> tuple[jax.Array, float]:
    """Run `fn()`, blocking on the result inside the timed region so async JAX dispatch doesn't
    make the measured duration understate actual completion time."""
    t0 = time.perf_counter()
    result = fn()
    result.block_until_ready()
    return result, time.perf_counter() - t0


def median_steady_state(fn) -> float:
    durations = []
    for _ in range(STEADY_STATE_REPEATS):
        _, dt = timed_call(fn)
        durations.append(dt)
    return statistics.median(durations)


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

    # --- affine-table path: first call (eager, pays any internal fori_loop/vmap compilation),
    # then JIT compile+first-run, then a median of steady-state JIT calls ------------------------
    eager, eager_s = timed_call(lambda: rt.run_assign(node, store))
    require_bit_identical(eager, f["expected"], "scalingProbe eager")

    jit_fn = jax.jit(lambda s: rt.run_assign(node, s))
    jitted, jit_compile_s = timed_call(lambda: jit_fn(store))
    require_bit_identical(jitted, f["expected"], "scalingProbe jit (compile+run)")

    jit_steady_s = median_steady_state(lambda: jit_fn(store))

    # --- comparison context: native jnp.einsum computing the identical contraction ----------------
    w = store[0]
    x = store[1]

    def einsum_fn(w_: jax.Array, x_: jax.Array) -> jax.Array:
        return jnp.einsum("ij,j->i", w_, x_)

    einsum_eager, einsum_eager_s = timed_call(lambda: einsum_fn(w, x))

    einsum_jit = jax.jit(einsum_fn)
    _, einsum_jit_compile_s = timed_call(lambda: einsum_jit(w, x))
    einsum_jit_steady_s = median_steady_state(lambda: einsum_jit(w, x))

    if not np.array_equal(np.asarray(einsum_eager), np.full(64, 64.0)):
        raise AssertionError("native einsum comparison did not reproduce the expected [64.0]*64")

    print(f"JAX {jax.__version__} on {jax.default_backend()}: {jax.devices()}")
    print(f"generated artifact: {artifact_bytes} bytes")
    print(f"affine-table first call (eager): {eager_s:.6f} s")
    print(f"affine-table jit compile+first-run: {jit_compile_s:.6f} s")
    print(f"affine-table jit steady-state (median of {STEADY_STATE_REPEATS}): {jit_steady_s:.6f} s")
    print(f"native jnp.einsum first call (eager): {einsum_eager_s:.6f} s")
    print(f"native jnp.einsum jit compile+first-run: {einsum_jit_compile_s:.6f} s")
    print(
        f"native jnp.einsum jit steady-state (median of {STEADY_STATE_REPEATS}): "
        f"{einsum_jit_steady_s:.6f} s"
    )
    print("affine-table result bit-identical to Dense (eager + jit) passed")


if __name__ == "__main__":
    main()
