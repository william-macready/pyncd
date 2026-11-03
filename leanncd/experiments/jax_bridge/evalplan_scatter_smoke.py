"""Scatter differential verifier (JAX scatter slice, ordered mode).

Loads the Lean-generated module (`EvalPlanScatterSmoke.lean`): per fixture the static plan data
(`renderAffinePlanNamed`, scatter nodes included) and the Lean reference worker's own result bits
(`runPreparedDense` / `runPreparedDense32`). Runs every fixture through the committed runtime
(`evalplan_affine_runtime.py`) eagerly and under `jax.jit` and requires exact dtype/shape/bit
agreement with Lean. Fixtures were chosen so an ordered fold, a placement table, a `reduceId` init
or a node-kind dispatch that is subtly wrong cannot also agree with Lean.

Usage: evalplan_scatter_smoke.py float64|float32 GENERATED_MODULE
float64 runs with x64 enabled; float32 with x64 DISABLED (no float64 can arise at all).
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import jax

_DT = sys.argv[1] if len(sys.argv) == 3 else ""
if _DT not in ("float64", "float32"):
    raise SystemExit(f"usage: {Path(sys.argv[0]).name} float64|float32 GENERATED_MODULE")
jax.config.update("jax_enable_x64", _DT == "float64")
import jax.numpy as jnp  # noqa: E402
import numpy as np  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
import evalplan_affine_runtime as rt  # noqa: E402

JDT = jnp.float64 if _DT == "float64" else jnp.float32
NDT = np.float64 if _DT == "float64" else np.float32
UDT = np.uint64 if _DT == "float64" else np.uint32

# Fixtures whose jit result may differ from eager in the sign of zero only (XLA drops a `+0` fold
# seed under jit; see the AGENTS.md pitfall "JAX ordered-reference labels are measured").
JIT_SKIP: set[str] = set()


def reconstruct(entry: dict) -> jax.Array:
    arr = np.array(entry["bits"], dtype=UDT).view(NDT)
    return jnp.asarray(arr.reshape(tuple(entry["shape"])))


def require_bits(actual, entry: dict, label: str) -> None:
    a = np.asarray(actual)
    if a.dtype != NDT:
        raise AssertionError(f"{label}: expected {NDT.__name__}, got {a.dtype}")
    if a.shape != tuple(entry["shape"]):
        raise AssertionError(f"{label}: shape {a.shape} != {tuple(entry['shape'])}")
    got = a.reshape(-1).view(UDT)
    exp = np.array(entry["bits"], dtype=UDT)
    if not np.array_equal(got, exp):
        raise AssertionError(f"{label}: bits differ from Lean: {got.tolist()} vs {exp.tolist()}")


def run_fixture(f: dict) -> None:
    plan = f["plan"]
    kinds = [n.get("kind", "assign") for n in plan["nodes"]]
    if kinds.count("scatter") != f["n_scatter"] or f["n_scatter"] < 1:
        raise AssertionError(f"{f['name']}: plan nodes {kinds} vs n_scatter {f['n_scatter']}")
    inputs = {n: reconstruct(e) for n, e in f["inputs"].items()}
    eager = rt.run_named(plan, inputs, JDT)
    jitted = jax.jit(lambda i: rt.run_named(plan, i, JDT))(inputs)
    for name, exp in f["expected"].items():
        require_bits(eager[name], exp, f"{f['name']} eager {name}")
        if f["name"] not in JIT_SKIP:
            require_bits(jitted[name], exp, f"{f['name']} jit {name}")


def main() -> None:
    spec = importlib.util.spec_from_file_location("gen_scatter", Path(sys.argv[2]).resolve())
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    by = {f["name"]: f for f in mod.FIXTURES}
    for f in mod.FIXTURES:
        run_fixture(f)
    print(f"{len(mod.FIXTURES)} {_DT} scatter fixtures bit-identical to Lean (eager + jit)")

    # Collision ORDER: one cell receives [big, 1, 1] in row-major order; the forward left fold stays
    # at `big`, the reversed fold (1 + 1 first) lands above it. Lean's bits are the forward one.
    key = "multi" if _DT == "float64" else "multi32"
    cell2 = np.array(by[key]["expected"]["Y"]["bits"], dtype=UDT).view(NDT)[2]
    big = NDT(1e16 if _DT == "float64" else 16777216.0)
    assert cell2 == big, f"{key}: cell 2 = {cell2!r}, forward fold must give {big!r}"
    assert (NDT(1.0) + NDT(1.0)) + big != big, "fixture would not distinguish fold order"
    print(f"collision order pinned: {key} cell 2 = {cell2!r} (the reversed fold differs)")

    if _DT == "float64":
        # Signed zero: Lean computes reduceId + (-0.0) = +0.0; copy-on-first-write would keep -0.0.
        nz = np.array(by["negZero"]["expected"]["Y"]["bits"], dtype=np.uint64)
        assert nz[1] == 0, f"reduceId + (-0.0) must be +0.0, got bits {nz[1]:#x}"
        # Differentiable through the ordered fold: d sum(Y) / dA = 1 for a one-to-one placement.
        f = by["stride"]
        ins = {n: reconstruct(e) for n, e in f["inputs"].items()}
        g = np.asarray(jax.grad(lambda a: jnp.sum(rt.run_named(f["plan"], {"A": a}, JDT)["Y"]))(ins["A"]))
        assert g.tolist() == [1.0, 1.0, 1.0], g
        print("signed-zero and gradient pins ok")


if __name__ == "__main__":
    main()
