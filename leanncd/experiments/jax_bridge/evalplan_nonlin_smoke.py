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
OUT_STATS: dict[tuple[str, str], list] = {}  # (fixture, output name) -> stats; one table per transformer fixture
TRANSFORMER_FIXTURES = {"transformer", "transformer32", "transformer_rms", "transformer_rms32",
                        "transformer_scan", "transformer_scan32",
                        "transformer_head", "transformer_head32",
                        "transformer_unrolled", "transformer_unrolled32"}
# Scan-vs-unrolled oracle (both JAX results, no Lean): (rtol, atol) per precision. MEASURED: scan and
# unrolled are bit-identical in float64 and float32, eager and jit (24/24 entries per precision), so
# the tolerance is exactly zero (value equality; the observed bit-identical count is printed).
ORACLE_TOL = {"float64": (0.0, 0.0), "float32": (0.0, 0.0)}
# fixture name -> {"eager": outputs, "jit": outputs}, kept for the scan fixtures and the unrolled oracle.
EAGER: dict[str, dict] = {}


# Head pins (transformer_head): row-sum deviation of the vocabulary softmax and Logits-vs-numpy max abs, per
# precision. MEASURED (Lean, eager, jit): float64 1.1e-16 / 2.2e-16, float32 6.7e-8 / 8.5e-8; the tolerances
# leave ~3.7 orders (float64) / ~1.1 orders (float32) of headroom and are far below any wrong-head effect (~1e-1).
HEAD_ROWSUM_TOL = {"float64": 1e-12, "float32": 1e-6}
HEAD_LOGITS_TOL = {"float64": 1e-12, "float32": 1e-6}
# P vs the float64 row-wise softmax of the numpy Logits (pin (a')). MEASURED (Lean, eager, jit): float64
# 5.6e-17 / 4.2e-17, float32 2.6e-8 for all three; headroom ~4.7 orders (float64) / ~1.6 orders (float32).
HEAD_SOFTMAX_TOL = {"float64": 1e-12, "float32": 1e-6}


def flat_nodes(nodes):
    """Plan nodes with every scan record replaced by the nodes of its base then step block (the counts in
    the generated header, like Lean's `flatSteps`, are over those inner nodes)."""
    for n in nodes:
        if n.get("kind") == "scan":
            yield from flat_nodes(n["base"]["nodes"])
            yield from flat_nodes(n["step"]["nodes"])
        else:
            yield n


def is_transformer(name: str) -> bool:
    return name in TRANSFORMER_FIXTURES


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


def record_output(fixture: str, key: str, got, entry: dict) -> None:
    """Per-output measurement for a transformer fixture (every materialized output, incl. assignments)."""
    g, w = np.asarray(got), lean_array(entry)
    diff = np.abs(g.astype(np.float64) - w.astype(np.float64))
    nz = w != 0
    rel = float(np.max(diff[nz] / np.abs(w.astype(np.float64))[nz])) if nz.any() else 0.0
    s = OUT_STATS.setdefault((fixture, key), [0.0, 0.0, 0, 0])
    s[0], s[1] = max(s[0], rel), max(s[1], float(np.max(diff)))
    s[2] += int(np.sum(g.reshape(-1).view(UDT) == w.reshape(-1).view(UDT)))
    s[3] += g.size


def run_fixture(f: dict) -> None:
    plan = f["plan"]
    kinds = [n.get("kind", "assign") for n in flat_nodes(plan["nodes"])]
    if kinds.count("pointwise") != f["n_pointwise"] or kinds.count("axiswise") != f["n_axiswise"]:
        raise AssertionError(f"{f['name']}: plan nodes {kinds} vs counts {f['n_pointwise']}/{f['n_axiswise']}")
    n_unary_keys = sum("unary" in fac for n in flat_nodes(plan["nodes"]) for t in n.get("terms", []) for fac in t["factors"])
    if n_unary_keys != f["n_unary"]:
        raise AssertionError(f"{f['name']}: plan has {n_unary_keys} unary factors vs count {f['n_unary']}")
    if f["n_pointwise"] + f["n_axiswise"] + f["n_unary"] < 1 and not f.get("linear_ok"):
        raise AssertionError(f"{f['name']}: fixture exercises no nonlinearity")
    # Transformer: relu's INPUT already carries the upstream exp/normalize libm-vs-XLA difference (~1 ulp),
    # so "relu is bit-exact" does not apply; its outputs get the tolerance gate and `record_output` only.
    fns = {} if is_transformer(f["name"]) else out_fns(plan)
    inputs = {n: reconstruct(e) for n, e in f["inputs"].items()}
    eager = rt.run_named(plan, inputs, JDT)
    jitted = jax.jit(lambda i: rt.run_named(plan, i, JDT))(inputs)
    if any(n.get("kind") == "scan" for n in plan["nodes"]) or f["name"].startswith("transformer_unrolled"):
        EAGER[f["name"]] = {"eager": eager, "jit": jitted}
    for name, exp in f["expected"].items():
        require_close(eager[name], exp, f"{f['name']} eager {name}", fns.get(name))
        require_close(jitted[name], exp, f"{f['name']} jit {name}", fns.get(name))
        if is_transformer(f["name"]):
            record_output(f["name"], name, eager[name], exp)
            record_output(f["name"], name, jitted[name], exp)


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
    for n in sorted(n for fx, n in OUT_STATS if fx == "transformer" + sfx):
        rel, ab, ex, tot = OUT_STATS[("transformer" + sfx, n)]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")

    # Same layer with a REAL RMSNorm (`z / sqrt(mean(z^2) + eps)`): the differential above only says Lean
    # and JAX agree, so pin value-independently that the norm is what it claims. `A` and `H` are the norm
    # outputs: every row has unit mean square up to eps. A sum of squares (Inv = 1) or a dropped recip
    # would break that, while Lean and JAX would still agree with each other. The pre-norm inputs `Z1` and
    # `Z2` are far from unit mean square, so the unit-RMS check cannot hold vacuously (norm = identity).
    rn_name = "transformer_rms" + sfx
    rms = by[rn_name]
    ro = {n: lean_array(e) for n, e in rms["expected"].items()}
    assert {"S", "Z1", "A", "Z2", "H"} <= set(ro), sorted(ro)
    for out_name, pre_name in (("A", "Z1"), ("H", "Z2")):
        ms = np.mean(ro[out_name].astype(np.float64) ** 2, axis=1)
        assert np.all(np.abs(ms - 1.0) < 1e-3), (out_name, ms.tolist())
        pre = np.mean(ro[pre_name].astype(np.float64) ** 2, axis=1)
        assert np.any(np.abs(pre - 1.0) > 0.05), (pre_name, pre.tolist())
    assert rms["n_unary"] > 0 and (rms["n_axiswise"], rms["n_pointwise"]) == (1, 1), \
        (rms["n_unary"], rms["n_axiswise"], rms["n_pointwise"])
    print(f"transformer_rms: real RMSNorm rows of A and H have unit mean square (eps-close), pre-norm Z1/Z2 do "
          f"not; {rms['n_unary']} unary factors, {rms['n_axiswise']} axiswise (softmax) + {rms['n_pointwise']} "
          f"pointwise (relu); per-output measured difference vs Lean:")
    for n in sorted(n for fx, n in OUT_STATS if fx == rn_name):
        rel, ab, ex, tot = OUT_STATS[(rn_name, n)]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")

    # Two-layer transformer as ONE scan record (`lax.scan`, 2 steps over the layer axis). Lean and JAX agreeing
    # is not evidence the scan is right (a shared mistake passes), so the pins below are value-independent
    # properties of the state `H(q, m, l)`, checked on Lean's result and on the eager and jit JAX results.
    sc_name = "transformer_scan" + sfx
    sc = by[sc_name]
    scans = [n for n in sc["plan"]["nodes"] if n.get("kind") == "scan"]
    assert len(sc["plan"]["nodes"]) == 1 and len(scans) == 1 and scans[0]["step_count"] == 2, sc["plan"]["nodes"]
    sin = {n: lean_array(e) for n, e in sc["inputs"].items()}
    # (b) the layer-2 weight slice is NaN in the INPUTS, layers 0 and 1 are finite, and every output is
    # finite: a step that read past layer 1 would turn the whole state NaN.
    for w in ("W_Q", "W_K", "W_V", "W_O", "W_in", "W_out"):
        assert sin[w].shape[0] == 3 and np.all(np.isnan(sin[w][2])) and np.all(np.isfinite(sin[w][:2])), w
    views = {"lean": {n: lean_array(e) for n, e in sc["expected"].items()},
             "eager": {n: np.asarray(v) for n, v in EAGER[sc_name]["eager"].items()},
             "jit": {n: np.asarray(v) for n, v in EAGER[sc_name]["jit"].items()}}
    for who, outs_sc in views.items():
        assert "H" in outs_sc and all(np.all(np.isfinite(v)) for v in outs_sc.values()), (who, sorted(outs_sc))
        H = outs_sc["H"]
        assert H.shape == (3, 4, 3), (who, H.shape)
        # (c) layer 0 of the state is X, bit for bit (the base block's write)
        assert np.array_equal(np.ascontiguousarray(H[:, :, 0]).view(UDT), np.ascontiguousarray(sin["X"]).view(UDT)), who
        # (a) layers 1 and 2 are RMS-normalised (unit mean square up to eps); layer 0 (= X) is not
        ms = [np.mean(H[:, :, l].astype(np.float64) ** 2, axis=1) for l in range(3)]
        assert np.any(np.abs(ms[0] - 1.0) > 0.05), (who, ms[0].tolist())
        for l in (1, 2):
            assert np.all(np.abs(ms[l] - 1.0) < 1e-3), (who, l, ms[l].tolist())
        # (d) the two layers differ: a step that ignored its context coordinate would repeat layer 1
        gap = float(np.max(np.abs(H[:, :, 1].astype(np.float64) - H[:, :, 2].astype(np.float64))))
        assert gap > 1e-2, (who, gap)
    print(f"transformer_scan: one scan record, 2 steps, layer-2 weights NaN in the inputs and every output finite; "
          f"H layer 0 == X bitwise, layers 1 and 2 have unit mean square (eps-close) and differ (max abs gap "
          f"{gap:.3f}); pins hold on Lean, eager and jit; per-output measured difference vs Lean:")
    for n in sorted(n for fx, n in OUT_STATS if fx == sc_name):
        rel, ab, ex, tot = OUT_STATS[(sc_name, n)]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")

    # Scan transformer WITH A HEAD: after the scan, a final RMSNorm of the pre-norm residual
    # `Zf = H[:, :, 2] + X`, an unembedding `Logits = Hf @ W_U.T` over a vocabulary axis of extent 5, and a
    # softmax over the vocabulary. Lean and JAX agreeing proves nothing about the head, so every pin
    # recomputes the head in plain numpy (float64) from the fixture's INPUTS and the state `H` slice 2 of the
    # SAME view (Lean, eager, jit), never from that view's own Zf / Hf / Logits / P outputs.
    hd_name = "transformer_head" + sfx
    hd = by[hd_name]
    hin = {n: lean_array(e) for n, e in hd["inputs"].items()}
    hnodes = hd["plan"]["nodes"]
    h_scans = [i for i, n in enumerate(hnodes) if n.get("kind") == "scan"]
    h_after = hnodes[h_scans[0] + 1:] if h_scans else []
    # (d, plan) exactly one scan record, first, with the same body as transformer_scan; the head is the
    # plain nodes AFTER it (not inside the scan, not before it)
    assert len(h_scans) == 1 and h_scans[0] == 0 and hnodes[0]["step_count"] == 2, [n.get("kind") for n in hnodes]
    assert all(n.get("kind") != "scan" for n in h_after) and len(hnodes) == 1 + len(h_after), hnodes
    assert len(list(flat_nodes([hnodes[0]]))) == len(list(flat_nodes([scans[0]]))), "scan body differs from transformer_scan"
    hviews = {"lean": {n: lean_array(e) for n, e in hd["expected"].items()},
              "eager": {n: np.asarray(v) for n, v in EAGER[hd_name]["eager"].items()},
              "jit": {n: np.asarray(v) for n, v in EAGER[hd_name]["jit"].items()}}
    # (d, shapes) the vocabulary extent (derived from W_U, not a literal) differs from every other extent in
    # the other inputs and in the head's other outputs, and is the extent of Logits[1] and P[1]
    vocab = hin["W_U"].shape[0]
    other_extents = {d for n, a in hin.items() if n != "W_U" for d in a.shape}
    other_extents |= {d for o in hviews.values() for n, a in o.items() if n not in ("Logits", "P") for d in a.shape}
    assert set(hin) == set(sin) | {"W_U"}, sorted(hin)
    assert vocab not in other_extents, ("vocabulary extent collides with another extent", vocab, sorted(other_extents))
    assert all(o["P"].shape[1] == vocab and o["Logits"].shape[1] == vocab for o in hviews.values()), vocab
    print(f"  head vocabulary extent {vocab} (from W_U[0]) is not among the other extents {sorted(other_extents)}")
    # (e) the head fixture's scan is the transformer_scan fixture's scan, value for value: every shared input
    # is bitwise equal (NaN weight slices included), and H is bit-identical per view
    for n in sin:
        assert np.array_equal(np.ascontiguousarray(sin[n]).view(UDT), np.ascontiguousarray(hin[n]).view(UDT)), ("pin (e) head scan == transformer_scan, input", n)
    for who, outs_hd in hviews.items():
        hd_bits, sc_bits = np.ascontiguousarray(outs_hd["H"]).view(UDT), np.ascontiguousarray(views[who]["H"]).view(UDT)
        print(f"  head {who}: head H vs transformer_scan H bit-identical {bool(np.array_equal(hd_bits, sc_bits))}, "
              f"max abs {float(np.max(np.abs(outs_hd['H'].astype(np.float64) - views[who]['H'].astype(np.float64)))):.3e}")
        assert np.array_equal(hd_bits, sc_bits), ("pin (e) head scan == transformer_scan", who)
    for who, outs_hd in hviews.items():
        assert {"H", "Logits", "P", "Hf", "Zf"} <= set(outs_hd), (who, sorted(outs_hd))
        assert all(np.all(np.isfinite(v)) for v in outs_hd.values()), who
        P = outs_hd["P"].astype(np.float64)
        # (a) every row of P is a probability vector over the vocabulary
        rowdev = float(np.max(np.abs(P.sum(axis=1) - 1.0)))
        assert np.all(P > 0) and rowdev < HEAD_ROWSUM_TOL[_DT], ("pin (a) P rows positive and sum to 1", who, rowdev, P.tolist())
        # (c) the final norm output has unit mean square (Inv-weighted, eps-close); the pre-norm Zf does not
        X, Inv, Eps, WU = (hin[n].astype(np.float64) for n in ("X", "Inv", "Eps", "W_U"))
        Zf = outs_hd["H"][:, :, 2].astype(np.float64) + X
        Hf = Zf / np.sqrt(np.sum(Zf * Zf * Inv, axis=1) + Eps)[:, None]
        ms_hf = np.sum(Hf * Hf * Inv, axis=1)
        ms_hf_out = np.sum(outs_hd["Hf"].astype(np.float64) ** 2 * Inv, axis=1)
        ms_zf = np.sum(Zf * Zf * Inv, axis=1)
        assert np.all(np.abs(ms_hf - 1.0) < 1e-3) and np.all(np.abs(ms_hf_out - 1.0) < 1e-3), \
            ("pin (c) Hf unit mean square", who, ms_hf_out.tolist())
        assert np.any(np.abs(ms_zf - 1.0) > 0.05), ("pin (c) pre-norm Zf is not unit mean square", who, ms_zf.tolist())
        # (b) Logits recomputed in numpy from the inputs and THIS view's H slice 2
        want = Hf @ WU.T
        ldiff = float(np.max(np.abs(outs_hd["Logits"].astype(np.float64) - want)))
        assert ldiff < HEAD_LOGITS_TOL[_DT], ("pin (b) Logits == numpy from H slice 2", who, ldiff, outs_hd["Logits"].tolist(), want.tolist())
        # (a') P is the row-wise numerically stable softmax of the numpy Logits (NOT of this view's own outputs)
        ex = np.exp(want - want.max(axis=1, keepdims=True))
        sdiff = float(np.max(np.abs(P - ex / ex.sum(axis=1, keepdims=True))))
        assert sdiff < HEAD_SOFTMAX_TOL[_DT], ("pin (a') P == softmax(numpy Logits)", who, sdiff, P.tolist())
        print(f"  head {who}: P row-sum dev {rowdev:.3e}, P vs softmax(numpy Logits) max abs {sdiff:.3e}, Hf mean-square {[round(float(x), 6) for x in ms_hf_out]}, "
              f"pre-norm Zf mean-square {[round(float(x), 4) for x in ms_zf]}, Logits vs numpy max abs {ldiff:.3e}")
    print(f"transformer_head: plan = 1 scan + {len(h_after)} plain nodes {[n.get('kind', 'assign') for n in h_after]}; "
          f"vocabulary extent {vocab} (from W_U) differs from every other extent and is Logits[1], P[1]; head scan == "
          f"transformer_scan (inputs and H bitwise); P rows positive and sum to 1; Logits == numpy "
          f"recomputation from H slice 2; P == softmax(numpy Logits); Hf unit mean square, pre-norm Zf not; per-output measured difference vs Lean:")
    for n in sorted(n for fx, n in OUT_STATS if fx == hd_name):
        rel, ab, ex, tot = OUT_STATS[(hd_name, n)]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")

    # UNROLLED ORACLE: the same two layers as two hand-copied flat layers (no scan; the old, trusted flat
    # lowering). Scan and unrolled take their weights from ONE Lean definition; the inputs are re-checked
    # bitwise here. The JAX scan state `H[:, :, 1]`, `H[:, :, 2]` must equal the JAX unrolled `H1`, `H2` within
    # ORACLE_TOL, eager and jit. This ties the scan lowering to the flat lowering WITHOUT Lean.
    un_name = "transformer_unrolled" + sfx
    un = by[un_name]
    assert not any(n.get("kind") == "scan" for n in un["plan"]["nodes"]), "the oracle must not contain a scan"
    uin = {n: lean_array(e) for n, e in un["inputs"].items()}
    bits = lambda a: np.ascontiguousarray(a).view(UDT)  # noqa: E731
    for n in ("X", "Inv", "Eps"):
        assert np.array_equal(bits(sin[n]), bits(uin[n])), n
    for w in ("W_Q", "W_K", "W_V", "W_O", "W_in", "W_out"):
        for l in (0, 1):
            assert np.array_equal(bits(sin[w][l]), bits(uin[f"{w}{l + 1}"])), (w, l)
    assert len(uin) == 15 and not any(np.any(np.isnan(v)) for v in uin.values()), sorted(uin)
    o_rtol, o_atol = ORACLE_TOL[_DT]
    for mode in ("eager", "jit"):
        h_scan = np.asarray(EAGER[sc_name][mode]["H"])
        for l in (1, 2):
            g, u = h_scan[:, :, l], np.asarray(EAGER[un_name][mode][f"H{l}"])
            assert g.shape == u.shape == (3, 4) and g.dtype == u.dtype == NDT, (mode, l, g.shape, u.shape)
            d = np.abs(g.astype(np.float64) - u.astype(np.float64))
            nbit = int(np.sum(bits(g) == bits(u)))
            print(f"  oracle {mode} layer {l}: max abs {float(d.max()):.3e}  bit-identical {nbit}/{g.size}")
            assert np.all(d <= o_atol + o_rtol * np.abs(u.astype(np.float64))), (mode, l, g.tolist(), u.tolist())
        # non-vacuous: the layers differ, so swapping them is rejected by the same comparison
        assert float(np.max(np.abs(h_scan[:, :, 1].astype(np.float64)
                                   - np.asarray(EAGER[un_name][mode]["H2"]).astype(np.float64)))) > 1e-2
    print(f"scan-vs-unrolled oracle: JAX scan H layers 1, 2 == JAX unrolled H1, H2 within rtol {o_rtol} / atol "
          f"{o_atol} (eager + jit), identical inputs checked bitwise, layers swapped would be rejected")

    # Scan survey (binary64 only: the donors are f64). Value-independent pins: each recomputes the expected
    # state in plain Python/numpy from the fixture's own inputs, then checks Lean, eager and jit against it.
    if _DT == "float64":
        def views_of(n):
            return (lean_array, lambda e: e), {"lean": {k: lean_array(e) for k, e in by[n]["expected"].items()},
                    "eager": {k: np.asarray(v) for k, v in EAGER[n]["eager"].items()},
                    "jit": {k: np.asarray(v) for k, v in EAGER[n]["jit"].items()}}
        # extent one: zero steps, the result is exactly the base-written state (the step block never runs)
        s0 = float(lean_array(by["scan_extentone"]["inputs"]["S0"]))
        for who, o in views_of("scan_extentone")[1].items():
            assert o["S"].shape == (1,) and o["S"][0] == s0, (who, o["S"].tolist(), s0)
        assert by["scan_extentone"]["plan"]["nodes"][0]["step_count"] == 0, by["scan_extentone"]["plan"]["nodes"][0]
        # deep history: S[l+1] = S[l] + S[l-2] (zero-padded), recomputed with plain Python (reads at l and l-2)
        s0 = float(lean_array(by["scan_deephistory"]["inputs"]["S0"]))
        ref = [s0]
        for l in range(3):
            ref.append(ref[l] + (ref[l - 2] if l - 2 >= 0 else 0.0))
        assert ref != [s0] * 4 and ref[3] != ref[2], ref  # discriminates a wrong lag
        for who, o in views_of("scan_deephistory")[1].items():
            assert np.array_equal(o["S"], np.array(ref)), (who, o["S"].tolist(), ref)
        # two scans in one plan: both produce outputs; the plain statement Z reads both histories
        ts = by["scan_twoscan"]
        assert sum(n.get("kind") == "scan" for n in ts["plan"]["nodes"]) == 2, ts["plan"]["nodes"]
        a0, b0 = float(lean_array(ts["inputs"]["A0"])), float(lean_array(ts["inputs"]["B0"]))
        for who, o in views_of("scan_twoscan")[1].items():
            assert np.array_equal(o["A"], np.full(3, a0)) and np.array_equal(o["B"], np.full(3, b0)), (who, o)
            assert np.array_equal(o["Z"], np.full(3, a0 * b0)) and a0 != b0, (who, o["Z"].tolist())
        print(f"scan survey: {sum(1 for f in mod.FIXTURES if f.get('linear_ok'))} donor scan fixtures within tolerance; "
              f"extent-one result == base state, deep-history (l and l-2) == plain-Python {ref}, "
              f"two-scan outputs A, B, Z == plain-Python recomputation")

    # Inline unary read (`E[i] := exp(A[i + 1])`, A = [0.5, -1, 2]): the last lane reads A[3], out of
    # bounds, which Dense zero-pads FIRST and then applies exp to, so it is exactly exp(0) = 1. Applying
    # exp before the pad (or not at all) would give 0 there, so the two orderings differ on this lane.
    # Domain violations are an unchecked precondition (Lean errors, JAX does not): every lane is Lean-ok.
    ue = lean_array(by["unary_exp_oob" + sfx]["expected"]["E"])
    a_in = lean_array(by["unary_exp_oob" + sfx]["inputs"]["A"])
    assert ue[2] == NDT(1.0) and np.allclose(ue[:2], np.exp(a_in[1:].astype(np.float64)), rtol=1e-6), ue.tolist()
    assert any("unary" in fac for n in by["unary_exp_oob" + sfx]["plan"]["nodes"] for t in n["terms"] for fac in t["factors"])
    print(f"inline unary read: out-of-bounds lane is exp(0) = 1 (pad, then apply), in-bounds lanes exp(A[i+1]): "
          f"{ue.tolist()}")

    # The other five unary ops (all Lean-ok inputs). Each Lean output is checked against numpy on the
    # fixture's own inputs, and the op-swap alternatives are checked to DIFFER on those inputs, so a
    # runtime that swapped sin/cos, log/sqrt or dropped `1 / x` could not pass the tolerance gate above.
    uo = by["unary_ops" + sfx]
    ui = {k: lean_array(v).astype(np.float64) for k, v in uo["inputs"].items()}
    uex = {k: lean_array(v).astype(np.float64) for k, v in uo["expected"].items()}
    rt_ = 1e-5 if _DT == "float32" else 1e-12
    refs = {"Lg": np.log(ui["Pp"]), "Sq": np.sqrt(ui["Qq"]), "Sn": np.sin(ui["Tt"]),
            "Cs": np.cos(ui["Tt"]), "Rc": ui["Nn"] / ui["Rr"]}
    for k, r in refs.items():
        assert np.allclose(uex[k], r, rtol=rt_, atol=1e-6), (k, uex[k].tolist(), r.tolist())
    swaps = {"Lg": np.sqrt(ui["Pp"]), "Sq": np.log(np.maximum(ui["Qq"], 1e-300)), "Sn": np.cos(ui["Tt"]),
             "Cs": np.sin(ui["Tt"]), "Rc": ui["Nn"] * ui["Rr"]}
    for k, s in swaps.items():
        assert not np.allclose(uex[k], s, rtol=1e-3, atol=1e-3), (k, "op swap indistinguishable")
    assert uex["Sq"][0] == 0 and ui["Qq"][0] == 0  # sqrt(0) is Lean-ok and exactly 0
    um = by["unary_mix" + sfx]
    mi = {k: lean_array(v).astype(np.float64) for k, v in um["inputs"].items()}
    assert np.allclose(lean_array(um["expected"]["Mx"]), mi["Aa"] * np.sin(mi["Bb"]) * mi["Cc"], rtol=1e-5)
    ur = by["unary_red" + sfx]
    ri = {k: lean_array(v).astype(np.float64) for k, v in ur["inputs"].items()}
    assert np.allclose(lean_array(ur["expected"]["Zr"]), (np.exp(ri["Vv"]) * ri["Ww"]).sum(axis=1), rtol=1e-5)
    # LayerNorm-eps chain from source: Yl = Xl / sqrt(mean(Xl^2) + eps), through two unary reads of
    # intermediates (sqrt of Ve, recip of Sd); eps > 0 keeps sqrt's argument >= eps (Lean-ok).
    ul = by["unary_ln" + sfx]
    li = {k: lean_array(v).astype(np.float64) for k, v in ul["inputs"].items()}
    ln_ref = li["Xl"] / np.sqrt((li["Xl"] ** 2 * li["Inv"]).sum(axis=1) + li["Eps"])[:, None]
    assert np.allclose(lean_array(ul["expected"]["Yl"]), ln_ref, rtol=1e-5), ln_ref.tolist()
    assert sum("unary" in fac for n in ul["plan"]["nodes"] for t in n["terms"] for fac in t["factors"]) == 2
    # Empty source: exp over a zero-extent tensor is exp(0) = 1 on every lane (Dense pads, then applies).
    ue0 = lean_array(by["unary_empty" + sfx]["expected"]["Ee"])
    assert by["unary_empty" + sfx]["inputs"]["Ae"]["shape"] in ([0], (0,)) and ue0.tolist() == [1.0, 1.0, 1.0], ue0.tolist()
    print(f"unary LayerNorm-eps chain and empty-source exp match Lean: {lean_array(ul['expected']['Yl']).tolist()}, "
          f"{ue0.tolist()}")
    print("inline unary ops: log/sqrt/sin/cos/recip, a unary read between plain reads, and a unary read "
          "under a reduced axis match Lean within tolerance; op-swap alternatives differ on these inputs")

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
