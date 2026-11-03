"""Scatter differential verifier (JAX scatter slice, ordered mode).

Loads the Lean-generated module (`EvalPlanScatterSmoke.lean`): per fixture the static plan data
(`renderAffinePlanNamed`, scatter nodes included) and the Lean reference worker's own result bits
(`runPreparedDense` / `runPreparedDense32`). Runs every fixture through the committed runtime
(`evalplan_affine_runtime.py`) eagerly and under `jax.jit` and requires exact dtype/shape/bit
agreement with Lean. Fixtures were chosen so an ordered fold, a placement table, a `reduceId` init
or a node-kind dispatch that is subtly wrong cannot also agree with Lean.

Fast mode (`scatter_mode="fast"`, one vectorised `.at[].add`) is checked after the ordered pass:
bit-exact against Lean wherever the plan has no two source coordinates on one destination cell,
within RTOL (scale-relative) where it does, plus jaxpr checks that say WHICH fold ran, a mode-name
check, a range check, a signed-zero pin and a gradient pin.

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

# Scale-relative tolerance for fast-mode fixtures whose scatter table has colliding writes (XLA's accumulation order for
# colliding scatter-add updates is unspecified): |fast - lean| <= RTOL * max|lean| elementwise.
# Observed error on this CPU is exactly 0 (see README); the margin covers a reordered sum of a few terms.
RTOL = {"float64": 1e-12, "float32": 1e-5}

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


def require_close(got, want, label: str) -> None:
    g, w = np.asarray(got), np.asarray(want)
    if g.dtype != NDT or w.dtype != NDT or g.shape != w.shape:
        raise AssertionError(f"{label}: dtype/shape mismatch {g.dtype}{g.shape} vs {w.dtype}{w.shape}")
    if np.shares_memory(g, w):
        raise AssertionError(f"{label}: comparing a result against itself is vacuous")
    scale = float(np.max(np.abs(w.astype(np.float64)))) if w.size else 0.0
    if not np.all(np.abs(g.astype(np.float64) - w.astype(np.float64)) <= RTOL[_DT] * scale):
        raise AssertionError(f"{label}: not within rtol {RTOL[_DT]}: {g.tolist()} vs {w.tolist()}")


def collides(plan: dict) -> bool:
    return any(len(set(n["dest_flat_index"])) != len(n["dest_flat_index"])
               for n in plan["nodes"] if n.get("kind") == "scatter")


def scatter_adds(plan: dict, inputs: dict, mode: str | None) -> int:
    """How many `scatter-add` primitives the traced program contains: says which fold ran."""
    run = (lambda i: rt.run_named(plan, i, JDT)) if mode is None else (lambda i: rt.run_named(plan, i, JDT, mode))
    return str(jax.make_jaxpr(run)(inputs)).count("scatter-add")


def run_fast_fixture(f: dict) -> bool:
    plan, col = f["plan"], collides(f["plan"])
    inputs = {n: reconstruct(e) for n, e in f["inputs"].items()}
    expect_adds = sum(1 for n in plan["nodes"] if n.get("kind") == "scatter" and n["dest_flat_index"])
    for label, mode, want in (("default", None, 0), ("ordered", "ordered", 0), ("fast", "fast", expect_adds)):
        got = scatter_adds(plan, inputs, mode)
        if got != want:
            raise AssertionError(f"{f['name']}: {label} program has {got} scatter-add, expected {want}")
    eager = rt.run_named(plan, inputs, JDT, "fast")
    jitted = jax.jit(lambda i: rt.run_named(plan, i, JDT, "fast"))(inputs)
    same = True
    for name, exp in f["expected"].items():
        for tag, res in (("eager", eager), ("jit", jitted)):
            label = f"{f['name']} fast {tag} {name}"
            if col:
                require_close(res[name], reconstruct(exp), label)
                same = same and np.array_equal(np.asarray(res[name]).reshape(-1).view(UDT), np.array(exp["bits"], dtype=UDT))
            else:
                require_bits(res[name], exp, label)
    return col and same


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


def run_fast(mod, by: dict) -> None:
    cols = [f["name"] for f in mod.FIXTURES if collides(f["plan"])]
    assert sorted(cols) == sorted(k for k in by if k.startswith(("multi", "contract"))), cols
    agree = {f["name"]: run_fast_fixture(f) for f in mod.FIXTURES}
    n_exact = len(mod.FIXTURES) - len(cols)
    print(f"fast mode: {n_exact} collision-free fixtures bit-identical to Lean, {len(cols)} colliding "
          f"within rtol {RTOL[_DT]} (eager + jit); default/ordered traced without scatter-add, fast with it")
    print(f"fast colliding fixtures also bit-identical to Lean on this backend (observation, not a guarantee): "
          f"{ {k: agree[k] for k in cols} }")
    # Self-test of the tolerance check: a 1e-3 relative perturbation must be rejected (RTOL ceiling).
    probe = np.array([1.0, 2.0, 3.0], dtype=NDT)
    try:
        require_close(probe * NDT(1.001), probe.copy(), "tolerance self-test")
    except AssertionError:
        pass
    else:
        raise AssertionError("tolerance check accepts a 1e-3 relative perturbation: vacuous")
    # Well-conditioned colliding inputs: fast within RTOL of ordered (same plan, random values).
    rng = np.random.default_rng(0)
    for name in cols + [k for k in by if k.startswith("b5")]:  # b5*: private slots + ordered collector
        f = by[name]
        for _ in range(3):
            ins = {n: jnp.asarray(rng.normal(size=tuple(e["shape"])).astype(NDT)) for n, e in f["inputs"].items()}
            ordered = rt.run_named(f["plan"], ins, JDT)
            fast = rt.run_named(f["plan"], ins, JDT, "fast")
            for k in ordered:
                require_close(fast[k], np.array(ordered[k]), f"{name} random fast vs ordered {k}")
    print(f"fast mode: random well-conditioned collisions within rtol {RTOL[_DT]} of ordered")
    # Mode names and range check.
    f = by["stride"] if "stride" in by else by["stride32"]
    ins = {n: reconstruct(e) for n, e in f["inputs"].items()}
    for call in (lambda: rt.run_named(f["plan"], ins, JDT, "bogus"),
                 lambda: rt.run_plan_positional(f["plan"], [], JDT, "Fast")):
        try:
            call()
        except ValueError as e:
            assert "scatter_mode" in str(e), e
        else:
            raise AssertionError("unknown scatter_mode was accepted")
    for bad in (10**6, -1):
        plan = {**f["plan"], "nodes": [dict(n) for n in f["plan"]["nodes"]]}
        node = next(n for n in plan["nodes"] if n.get("kind") == "scatter")
        node["dest_flat_index"] = [bad] + list(node["dest_flat_index"][1:])
        try:
            rt.run_named(plan, ins, JDT, "fast")
        except ValueError as e:
            assert "outside" in str(e), e
        else:
            raise AssertionError(f"fast mode accepted out-of-range placement {bad}")
    print("fast mode: unknown scatter_mode and out-of-range placement rejected")


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

    run_fast(mod, by)

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
        g = np.asarray(jax.jit(jax.grad(lambda a: jnp.sum(rt.run_named(f["plan"], {"A": a}, JDT, "fast")["Y"])))(ins["A"]))
        assert g.tolist() == [1.0, 1.0, 1.0], g
        nz = np.asarray(rt.run_named(by["negZero"]["plan"], {n: reconstruct(e) for n, e in by["negZero"]["inputs"].items()},
                                     JDT, "fast")["Y"]).reshape(-1).view(np.uint64)
        assert nz[1] == 0, f"fast: zeros + (-0.0) must be +0.0, got bits {nz[1]:#x}"
        print("fast-mode gradient (jit(grad)) and signed-zero pins ok")


if __name__ == "__main__":
    main()
