"""Binary32 `affineReference` bit-exactness check (slice F32-JAX).

Loads `generated_evalplan_affine_smoke32.py` (from `EvalPlanAffineSmoke32.lean`) and runs every
fixture through the SAME committed runtime as binary64 (`evalplan_affine_runtime.py`, `dtype=
jnp.float32`), eagerly and under `jax.jit`, requiring every materialized output's `Float32.toBits`
pattern to equal the Lean checked binary32 reference (`runPreparedDense32`) exactly, except the
positions pinned in `KNOWN_DIVERGENT` (the XLA CPU subnormal/signed-zero limit of `f32Identity`).

`jax_enable_x64` is NEVER enabled in this process (asserted), so no float64 can arise anywhere: this
is genuine binary32 execution, not a narrowed binary64 run.
"""

from __future__ import annotations

import importlib.util
import math
import sys
import time
from pathlib import Path

import jax

if jax.config.read("jax_enable_x64"):
    raise AssertionError("binary32 reference check must run with jax_enable_x64 DISABLED")

import jax.numpy as jnp  # noqa: E402
import numpy as np  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
import evalplan_affine_runtime as rt  # noqa: E402


def reconstruct32(entry: dict) -> jax.Array:
    if entry.get("dtype") != "float32":
        raise AssertionError(f"expected a float32-tagged entry, got {entry.get('dtype')!r}")
    shape = tuple(entry["shape"])
    size = math.prod(shape) if shape else 1
    arr = np.array(entry["bits"], dtype=np.uint32).view(np.float32)
    if arr.shape[0] == 0 and size != 0:
        # A destination-slot placeholder (declared shape, empty data) the runtime never reads —
        # materialized as zeros so the positional store stays well-formed (as the binary64 smoke does).
        arr = np.zeros(size, dtype=np.float32)
    if arr.shape[0] != size:
        raise AssertionError(f"entry holds {arr.shape[0]} values for shape {shape}")
    return jnp.asarray(arr.reshape(shape))


# KNOWN, MEASURED XLA CPU divergences from the Lean binary32 reference (prototype notes §3), pinned
# per fixture as the exact set of flat positions allowed to differ. Every other position must still
# be bit-identical, and at least one listed position must ACTUALLY differ in some leg — if a later
# XLA stops diverging, this fails loud and the entry must be revisited, never silently kept.
#   f32Identity: input [+0, -0, least subnormal] through `Y[i] := X[i]`; Lean gives [+0, +0, 1].
#     pos 2 — XLA CPU flushes subnormal operands/results of arithmetic (f32 AND f64, eager AND jit;
#             `--xla_cpu_enable_fast_math=false` does not change it).
#     pos 1 — under jit XLA simplifies the reduction seed `+0 + x` to `x`, returning -0 where the
#             ordered left fold gives +0 (eager executes the add and agrees).
KNOWN_DIVERGENT = {"f32Identity": {1, 2}}
divergence_seen: dict[str, set] = {k: set() for k in KNOWN_DIVERGENT}


def require_bits32(actual: jax.Array, entry: dict, label: str, fixture: str = "") -> None:
    a = np.asarray(actual)
    if a.dtype != np.float32:
        raise AssertionError(f"{label}: expected float32, got {a.dtype}")
    if a.shape != tuple(entry["shape"]):
        raise AssertionError(f"{label}: shape {a.shape} != {tuple(entry['shape'])}")
    got = a.reshape(-1).view(np.uint32)
    want = np.array(entry["bits"], dtype=np.uint32)
    allowed = KNOWN_DIVERGENT.get(fixture, set())
    if allowed:
        diff = set(np.flatnonzero(got != want).tolist())
        if not diff <= allowed:
            raise AssertionError(f"{label}: unexpected divergence at {sorted(diff - allowed)}")
        divergence_seen[fixture] |= diff
        return
    if not np.array_equal(got, want):
        bad = int(np.flatnonzero(got != want)[0])
        raise AssertionError(f"{label}: not bit-identical at {bad}: {got[bad]:#010x} vs {want[bad]:#010x}")


def main() -> None:
    spec = importlib.util.spec_from_file_location("g32", Path(sys.argv[1]).resolve())
    g = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(g)
    # Optional JIT sampling for corpus cases: every non-corpus fixture is always JIT-checked; corpus
    # case k (its `corpus<k>` name) is JIT-checked iff k % jit_stride == 0. Default 1 = every case.
    jit_stride = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    fixtures = g.FIXTURES
    checks = eager_checks = jit_checks = 0
    kinds = {"named": 0, "assign": 0, "positional": 0}
    t_eager = t_jit = 0.0
    f32 = jnp.float32
    for f in fixtures:
        name, kind = f["name"], f["kind"]
        kinds[kind] += 1
        do_jit = not name.startswith("corpus") or int(name[len("corpus"):]) % jit_stride == 0
        if kind == "named":
            plan = f["plan"]
            args = {n: reconstruct32(e) for n, e in f["inputs"].items()}
            fn = lambda a, plan=plan: rt.run_named(plan, a, dtype=f32)
            pairs = lambda out: [(out[n], e, n) for n, e in f["expected"].items()]
        elif kind == "assign":
            node = f["assign"]
            args = [reconstruct32(e) for e in f["store"]]
            fn = lambda a, node=node: rt.run_assign(node, a, dtype=f32)
            pairs = lambda out: [(out, f["expected"], "result")]
        else:
            plan = f["plan"]
            args = [reconstruct32(e) for e in f["inputs"]]
            fn = lambda a, plan=plan: rt.run_plan_positional(plan, a, dtype=f32)
            pairs = lambda out: [(out[k], e, f"slot {k}") for k, e in enumerate(f["expected_store"])]
        t0 = time.perf_counter()
        for out, exp, lbl in pairs(fn(args)):
            require_bits32(out, exp, f"{name} eager {lbl}", name)
            eager_checks += 1
        t_eager += time.perf_counter() - t0
        if do_jit:
            t0 = time.perf_counter()
            for out, exp, lbl in pairs(jax.jit(fn)(args)):
                require_bits32(out, exp, f"{name} jit {lbl}", name)
                jit_checks += 1
            t_jit += time.perf_counter() - t0
    checks = eager_checks + jit_checks
    for k, allowed in KNOWN_DIVERGENT.items():
        if divergence_seen[k] != allowed:
            raise AssertionError(f"{k}: known divergence {sorted(allowed)} but observed {sorted(divergence_seen[k])}")
        print(f"known XLA CPU divergence reproduced exactly: {k} positions {sorted(allowed)}")
    # The dtype is the caller's explicit choice: the binary64 default refuses binary32 inputs loudly
    # (x64 is off here, so it is the x64 gate that fires) rather than running them.
    f0 = next(f for f in fixtures if f["kind"] == "named")
    try:
        rt.run_named(f0["plan"], {n: reconstruct32(e) for n, e in f0["inputs"].items()})
    except RuntimeError as e:
        if "jax_enable_x64" not in str(e):
            raise
    else:
        raise AssertionError("default float64 dtype accepted binary32 inputs")
    # ... and an explicit float32 call refuses a tensor of any other dtype instead of casting it.
    try:
        rt.run_named(f0["plan"], {n: reconstruct32(e).astype(jnp.float16) for n, e in f0["inputs"].items()},
                     dtype=jnp.float32)
    except TypeError as e:
        if "float16" not in str(e):
            raise
    else:
        raise AssertionError("float32 dtype accepted float16 inputs")
    print(f"kinds={kinds} eager_checks={eager_checks} jit_checks={jit_checks} (jit_stride={jit_stride}) "
          f"eager_seconds={t_eager:.3f} jit_seconds={t_jit:.3f}")
    print(f"{len(fixtures)} binary32 fixtures, {checks} eager/jit output checks: bit-identical "
          "to the Lean binary32 reference except the pinned KNOWN_DIVERGENT positions (x64 disabled)")


if __name__ == "__main__":
    main()
