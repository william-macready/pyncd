"""Pointwise/axiswise differential verifier (JAX pointwise slice, tolerance-compared).

Loads the Lean-generated module (`EvalPlanNonlinSmoke.lean`): per fixture the static plan data
(`renderAffinePlanNamed`, `.pointwise`/`.axiswise` nodes included) and the Lean reference worker's
own result bits (`runPreparedDense` / `runPreparedDense32`). Runs every fixture through the committed
runtime (`evalplan_affine_runtime.py`) eagerly and under `jax.jit` and requires every output to agree
with Lean WITHIN (RTOL, ATOL) — the only expected difference is the libm-vs-XLA implementation of
`exp`/`tanh`/`pow`/`sqrt`, since every sum and the softmax row maximum are sequential left folds in
both. Beside the tolerance gate it requires: the exact-zero pattern (masked, all-masked and zero-sum
entries are exactly 0 in BOTH), relu bit-exact (it is a selection, `relu(-0) = -0`), and a pinned
reduction-order fixture. Bit-exactness elsewhere is printed as an observation only.

Usage: evalplan_nonlin_smoke.py float64|float32 GENERATED_MODULE
float64 runs with x64 enabled; float32 with x64 DISABLED (no float64 can arise at all).
"""
from __future__ import annotations

import copy
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

# Chosen from the MEASURED differences below (see README): each is a stated margin over the worst
# observed relative / absolute difference of any function, eager or jit, over this corpus.
RTOL = {"float64": 1e-12, "float32": 1e-5}
ATOL = {"float64": 1e-14, "float32": 1e-6}

JDT = jnp.float64 if _DT == "float64" else jnp.float32
NDT = np.float64 if _DT == "float64" else np.float32
UDT = np.uint64 if _DT == "float64" else np.uint32

# fn -> [max_rel, max_abs, bit_exact_entries, total_entries], accumulated over every fixture/mode.
STATS: dict[str, list] = {}
# Transformer fixture only: output name -> [max_rel, max_abs, bit_exact_entries, total_entries].
OUT_STATS: dict[str, list] = {}


def reconstruct(entry: dict) -> jax.Array:
    arr = np.array(entry["bits"], dtype=UDT).view(NDT)
    return jnp.asarray(arr.reshape(tuple(entry["shape"])))


def lean_array(entry: dict) -> np.ndarray:
    return np.array(entry["bits"], dtype=UDT).view(NDT).reshape(tuple(entry["shape"]))


def out_fns(plan: dict) -> dict[str, str]:
    """Materialized output name -> the function of the node that wrote its slot."""
    by_slot = {n["dest"]: n["fn"] for n in plan["nodes"] if n.get("kind") in ("pointwise", "axiswise")}
    return {name: by_slot[slot] for name, slot in plan["materialized"] if slot in by_slot}


def within(g: np.ndarray, w: np.ndarray) -> bool:
    gg, ww = g.astype(np.float64), w.astype(np.float64)
    return bool(np.all(np.abs(gg - ww) <= ATOL[_DT] + RTOL[_DT] * np.abs(ww)))


def require_close(got, entry: dict, label: str, fn: str | None) -> None:
    g, w = np.asarray(got), lean_array(entry)
    if g.dtype != NDT:
        raise AssertionError(f"{label}: expected {NDT.__name__}, got {g.dtype}")
    if g.shape != w.shape:
        raise AssertionError(f"{label}: shape {g.shape} != {w.shape}")
    if not np.all(np.isfinite(g)) or not np.all(np.isfinite(w)):
        raise AssertionError(f"{label}: non-finite value: {g.tolist()} vs {w.tolist()}")
    if not np.array_equal(g == 0, w == 0):
        raise AssertionError(f"{label}: exact-zero pattern differs from Lean: {g.tolist()} vs {w.tolist()}")
    if not within(g, w):
        raise AssertionError(f"{label}: not within rtol {RTOL[_DT]} / atol {ATOL[_DT]}: {g.tolist()} vs {w.tolist()}")
    if fn is not None and g.size:
        diff = np.abs(g.astype(np.float64) - w.astype(np.float64))
        nz = w != 0
        rel = float(np.max(diff[nz] / np.abs(w.astype(np.float64))[nz])) if nz.any() else 0.0
        s = STATS.setdefault(fn, [0.0, 0.0, 0, 0])
        s[0], s[1] = max(s[0], rel), max(s[1], float(np.max(diff)))
        s[2] += int(np.sum(g.reshape(-1).view(UDT) == w.reshape(-1).view(UDT)))
        s[3] += g.size
        # jit may flip the sign of a zero only: the assign step feeding relu starts from `+0` and XLA drops
        # that seed under jit (AGENTS pitfall), so the jit run compares by value, the eager run by bits.
        if fn == "relu" and " jit " not in label and not np.array_equal(g.reshape(-1).view(UDT), w.reshape(-1).view(UDT)):
            raise AssertionError(f"{label}: relu is a selection and must be bit-exact: {g.tolist()} vs {w.tolist()}")


def record_output(key: str, got, entry: dict) -> None:
    """Per-output measurement for the transformer fixture (every materialized output, incl. assignments)."""
    g, w = np.asarray(got), lean_array(entry)
    diff = np.abs(g.astype(np.float64) - w.astype(np.float64))
    nz = w != 0
    rel = float(np.max(diff[nz] / np.abs(w.astype(np.float64))[nz])) if nz.any() else 0.0
    s = OUT_STATS.setdefault(key, [0.0, 0.0, 0, 0])
    s[0], s[1] = max(s[0], rel), max(s[1], float(np.max(diff)))
    s[2] += int(np.sum(g.reshape(-1).view(UDT) == w.reshape(-1).view(UDT)))
    s[3] += g.size


def run_fixture(f: dict) -> None:
    plan = f["plan"]
    kinds = [n.get("kind", "assign") for n in plan["nodes"]]
    if kinds.count("pointwise") != f["n_pointwise"] or kinds.count("axiswise") != f["n_axiswise"]:
        raise AssertionError(f"{f['name']}: plan nodes {kinds} vs counts {f['n_pointwise']}/{f['n_axiswise']}")
    if f["n_pointwise"] + f["n_axiswise"] < 1:
        raise AssertionError(f"{f['name']}: fixture exercises no nonlinearity")
    # Transformer: relu's INPUT already carries the upstream exp/normalize libm-vs-XLA difference (~1 ulp),
    # so "relu is bit-exact" does not apply; its outputs get the tolerance gate and `record_output` only.
    fns = {} if f["name"].startswith("transformer") else out_fns(plan)
    inputs = {n: reconstruct(e) for n, e in f["inputs"].items()}
    eager = rt.run_named(plan, inputs, JDT)
    jitted = jax.jit(lambda i: rt.run_named(plan, i, JDT))(inputs)
    for name, exp in f["expected"].items():
        require_close(eager[name], exp, f"{f['name']} eager {name}", fns.get(name))
        require_close(jitted[name], exp, f"{f['name']} jit {name}", fns.get(name))
        if f["name"].startswith("transformer"):
            record_output(name, eager[name], exp)
            record_output(name, jitted[name], exp)


def main() -> None:
    spec = importlib.util.spec_from_file_location("gen_nonlin", Path(sys.argv[2]).resolve())
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    by = {f["name"]: f for f in mod.FIXTURES}
    for f in mod.FIXTURES:
        run_fixture(f)
    print(f"{len(mod.FIXTURES)} {_DT} nonlinearity fixtures within rtol {RTOL[_DT]} / atol {ATOL[_DT]} "
          f"of Lean (eager + jit)")
    covered = set(STATS)
    want = {"relu", "sigmoid", "tanh", "gelu", "leakyrelu", "softmax", "normalize", "l2normalize"}
    assert covered == want, f"functions not exercised: {want - covered}"
    print(f"measured {_DT} differences vs Lean (max over fixtures, eager + jit):")
    for fn in sorted(STATS):
        rel, ab, ex, tot = STATS[fn]
        print(f"  {fn:12s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")

    sfx = "" if _DT == "float64" else "32"
    # Tolerance self-test: a 1e-3 relative perturbation of a real fixture output must be rejected.
    e = by["aw_plain" + sfx]["expected"]["Sm"]
    w = lean_array(e)
    assert not within((w * NDT(1.001)).astype(NDT), w), "tolerance accepts a 1e-3 perturbation: vacuous"
    assert not within(np.where(w > 0, NDT(0), w).astype(NDT), w), "tolerance accepts a zeroed output: vacuous"
    print("tolerance self-test: 1e-3 relative perturbation and a zeroed output are rejected")
    # `require_close` itself must reject a wrong value end to end (not only `within`): a verifier that
    # compared the JAX output with itself would accept this perturbed output.
    try:
        require_close((w * NDT(1.001)).astype(NDT), e, "canary", None)
    except AssertionError:
        pass
    else:
        raise AssertionError("require_close accepted a 1e-3 perturbed output: vacuous verifier")
    print("require_close canary: a 1e-3 perturbed output is rejected end to end")

    # Fixtures that exist to pin semantics a shift-invariant or finite-only comparison would miss:
    # Lean's `relu NaN` is +0 (`jnp.maximum` would give NaN); the softmax row max must range over the
    # UNMASKED entries only and start at the row's own first entry, not at 0 (the large-negative and
    # huge-masked rows underflow to all-zeros otherwise). They only discriminate if Lean's rows are
    # real distributions, which is asserted here.
    rn = lean_array(by["relu_nan" + sfx]["expected"]["R"])
    assert rn.tolist() == [0.0, 0.0, 2.0, 0.0] and not np.signbit(rn[0]), rn.tolist()
    nl = lean_array(by["aw_neglarge" + sfx]["expected"]["Sm"])
    assert np.all(np.abs(nl.sum(axis=1) - 1) < 1e-5) and np.all(nl > 0), nl.tolist()
    cb = lean_array(by["causal_big" + sfx]["expected"]["Sm"])
    assert cb[0].tolist() == [1.0, 0.0, 0.0] and abs(float(cb[1].sum()) - 1) < 1e-5, cb.tolist()
    print("pins: relu(NaN) = +0, large-negative and huge-masked softmax rows are real distributions")

    # Signed zero: the input `-0.0` reaches relu through the assign copy, which starts from +0 (`+0 + -0 =
    # +0`), so Lean's relu input is +0.0 and its output +0.0; relu is required bit-exact (eager) above.
    # A signed zero fed DIRECTLY into a pointwise step needs a raw-plan fixture (parked).
    R = lean_array(by["pw" + sfx]["expected"]["R"])
    assert R[3] == 0 and not np.signbit(R[3]) and not np.signbit(R[2]), R.tolist()
    print("relu signed zero: assign copy turns -0.0 into +0.0 in Lean; relu bit-exact in eager JAX")

    # Masked / zero-sum / all-zero / all-masked rows are exactly 0, not uniform, in Lean AND JAX
    # (the exact-zero-pattern gate above); pin the Lean values the fixtures were chosen for.
    am = lean_array(by["allmasked" + sfx]["expected"]["Sm"])
    assert np.all(am[0] == 0) and np.all(am[1:].sum(axis=1) > 0.99), am.tolist()  # row 0 all masked
    zs = lean_array(by["aw_zerosum" + sfx]["expected"]["Nm"])
    assert np.all(zs == 0), zs.tolist()  # zero-sum rows normalize to zeros
    z2 = lean_array(by["aw_zero" + sfx]["expected"]["L2"])
    assert np.all(z2 == 0), z2.tolist()  # all-zero row: l2normalize gives zeros
    lg = lean_array(by["aw_large" + sfx]["expected"]["Sm"])
    assert np.all(np.isfinite(lg)) and np.allclose(lg.sum(axis=1), 1.0, atol=1e-6), lg.tolist()
    print("pinned: all-masked row = zeros (not uniform), zero-sum normalize = zeros, all-zero l2 = zeros, "
          "large logits [1000, 1001, ...] finite and sum to 1 (max subtraction)")

    # Reduction ORDER: normalize over [big, 1, -big, 1]. Forward left fold: ((big+1)+-big)+1 = 1, so the
    # row is x / 1. A reversed fold or a pairwise tree sums to 0, so the row would be all zeros.
    row = np.array([1e16 if _DT == "float64" else 1e10, 1.0, -(1e16 if _DT == "float64" else 1e10), 1.0], dtype=NDT)
    fwd = ((row[0] + row[1]) + row[2]) + row[3]
    rev = ((row[3] + row[2]) + row[1]) + row[0]
    tree = (row[0] + row[1]) + (row[2] + row[3])
    assert fwd == NDT(1.0) and rev == 0 and tree == 0, (fwd, rev, tree)
    ord_out = lean_array(by["order" + sfx]["expected"]["Nm"])
    assert np.array_equal(ord_out, row / fwd), ord_out.tolist()  # Lean folded forward
    print(f"reduction order pinned: forward sum {fwd!r}, reversed {rev!r}, tree {tree!r}; Lean row = x / forward "
          f"sum, JAX matches it within tolerance (a reordered sum would give all zeros)")

    # Single-layer transformer (14 plan nodes): every materialized output was compared above within the
    # same tolerance; pin that the fixture is non-degenerate, then print the per-output measurement.
    tf = by["transformer" + sfx]
    outs = {n: lean_array(e) for n, e in tf["expected"].items()}
    assert {"S", "A", "H"} <= set(outs), sorted(outs)
    S3 = outs["S"]  # [h, q, s]: causal rows keep 1, 2, 3 entries (row q=1: more than one, not all)
    assert [int(np.sum(S3[0, q] != 0)) for q in range(3)] == [1, 2, 3], S3.tolist()
    assert np.all(S3[:, 0, 1:] == 0) and np.all(S3[:, 1, 2] == 0) and np.allclose(S3.sum(axis=2), 1.0, atol=1e-6)
    assert np.allclose(outs["H"].sum(axis=1), 1.0, atol=1e-6) and np.allclose(outs["A"].sum(axis=1), 1.0, atol=1e-6)
    if "F" in outs:  # relu clamps some entries and passes others
        assert np.any(outs["F"] == 0) and np.any(outs["F"] > 0), outs["F"].tolist()
    print(f"transformer: {len(outs)} outputs {sorted(outs)} within tolerance (eager + jit); "
          f"causal rows keep [1, 2, 3] entries; per-output measured difference vs Lean:")
    for n in sorted(OUT_STATS):
        rel, ab, ex, tot = OUT_STATS[n]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")

    # An unknown function name is refused loud, never given a default formula: clone a real fixture's
    # plan and change ONLY the first node of the kind to an unlisted `fn`; the unmodified plan is the
    # fixture that already passed above, so the refusal is attributable to the name alone.
    for fx, kind, what in (("pw" + sfx, "pointwise", "unsupported pointwise fn"),
                           ("aw_plain" + sfx, "axiswise", "unsupported axiswise fn")):
        f = by[fx]
        bad = copy.deepcopy(f["plan"])
        node = next(n for n in bad["nodes"] if n.get("kind") == kind)
        node["fn"] = "bogus"
        inputs = {n: reconstruct(e) for n, e in f["inputs"].items()}
        try:
            rt.run_named(bad, inputs, JDT)
        except ValueError as err:
            assert what in str(err) and "bogus" in str(err), (fx, str(err))
        else:
            raise AssertionError(f"{fx}: an unknown {kind} fn was accepted")
    print("unknown pointwise and axiswise function names are rejected (ValueError), not defaulted")

    # Differentiable: jit(grad) is finite for softmax (weighted sum, masked and unmasked) and gelu.
    for fx, name, shape in (("pw" + sfx, "G", (7,)), ("aw_plain" + sfx, "Sm", (2, 4)),
                            ("causal" + sfx, "Sm", (3, 3))):
        f = by[fx]
        in_name = next(iter(f["inputs"]))
        x0 = reconstruct(f["inputs"][in_name])
        wts = jnp.arange(1, x0.size + 1, dtype=JDT).reshape(x0.shape)
        grad = jax.jit(jax.grad(lambda x: jnp.sum(wts * rt.run_named(f["plan"], {in_name: x}, JDT)[name])))
        g = np.asarray(grad(x0))
        assert g.dtype == NDT and np.all(np.isfinite(g)), (fx, g.tolist())
        assert np.any(g != 0), (fx, "gradient is identically zero")
    print("jit(grad) finite and non-trivial for gelu, softmax and causal softmax")


if __name__ == "__main__":
    main()
