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
                        "transformer_head", "transformer_head32", "scan_postrole", "scan_postrole32",
                        "transformer_unrolled", "transformer_unrolled32"}
# Scan-vs-unrolled oracle (both JAX results, no Lean): (rtol, atol) per precision. MEASURED: scan and
# unrolled are bit-identical in float64 (eager and jit) and in float32 jit (24/24 entries each), so
# the tolerance is exactly zero (value equality; the observed bit-identical count is printed).
ORACLE_TOL = {"float64": (0.0, 0.0), "float32": (0.0, 0.0)}
# EXCEPTION, MEASURED on the standard pre-norm model: binary32 EAGER differs by one ulp in layer 2 (2 of 12 entries,
# max abs 2.4e-7 at |H| ~ 2-5): the eager scan body is one compiled `lax.scan` while the eager unrolled oracle
# runs op by op. Every other combination (binary64 eager and jit, binary32 jit) stays bit-identical (tolerance 0).
# 2.4e-7 relative is between 2 and 4 binary32 ulps (2 at the bottom of a binade, 4 at the top), against the observed
# 1 ulp; it is applied to layer 2 only (layer 1 stays exact). A swapped layer (gap ~1) or a wrong gain (~0.6) is
# ~6 orders larger.
ORACLE_EAGER_TOL32 = (2.4e-7, 0.0)
# fixture name -> {"eager": outputs, "jit": outputs}, kept for the scan fixtures and the unrolled oracle.
EAGER: dict[str, dict] = {}


# Head pins (transformer_head): row-sum deviation of the vocabulary softmax and Logits-vs-numpy max abs, per
# precision. MEASURED (Lean, eager, jit): float64 2.2e-16 / 2.2e-16, float32 3.0e-8 / 1.9e-7; the tolerances
# leave ~3.7 orders (float64) / ~0.7 order (float32, Logits) of headroom and are far below any wrong-head effect (~1e-1).
HEAD_ROWSUM_TOL = {"float64": 1e-12, "float32": 1e-6}
HEAD_LOGITS_TOL = {"float64": 1e-12, "float32": 1e-6}
# P vs the float64 row-wise softmax of the numpy Logits (pin (a')). MEASURED (Lean, eager, jit): float64
# 2.8e-17 (Lean) / 5.6e-17, float32 3.0e-8 (Lean) / 2.0e-8; headroom ~5 orders (float64) / ~1.5 orders (float32).
HEAD_SOFTMAX_TOL = {"float64": 1e-12, "float32": 1e-6}
# Post-scan role pins (scan_postrole): max over entries of |view - numpy| / max(1, |numpy|) (the outputs reach
# ~5e4, so a float32 absolute bound would be meaningless), numpy float64 from the inputs only. MEASURED (Lean,
# eager, jit): float64 0 for every output except Lean's Sm 3.5e-18, float32 0 except Sm 2.8e-8; the tolerances leave
# ~6 orders (float64) / ~1.5 orders (float32) of headroom and are far below any wrong-reading effect (>= 3e-2 relative).
POSTROLE_TOL = {"float64": 1e-12, "float32": 1e-6}
# Standard pre-norm transformer pins (scan, head, unrolled oracle): max over entries of |view - numpy| /
# max(1, |numpy|), numpy float64 from the exported INPUTS only (`np_transformer`); the observed maxima per output
# and precision are printed under each fixture's summary line.
# MEASURED worst case (state H layer 2 / unrolled H2, all views): float64 6.7e-16, float32 9.4e-7 (the binary32
# headroom is thin, <10%: the residual stream reaches |H| ~ 5 after two layers, so binary32 rounding is ~3e-7 per op).
MODEL_TOL = {"float64": 1e-12, "float32": 1e-6}
# (fixture, output) -> [max scaled error, max abs error] over the Lean, eager and jit views
NUM_STATS: dict[tuple[str, str], list] = {}


def np_gelu(x):
    """gelu, tanh approximation, exactly the formula the model states (float64)."""
    return 0.5 * x * (1.0 + np.tanh(0.7978845608028654 * (x + 0.044715 * x ** 3)))


def np_softmax_last(z):
    e = np.exp(z - z.max(axis=-1, keepdims=True))
    return e / e.sum(axis=-1, keepdims=True)


def np_transformer(inp: dict, n_layers: int = 2, unit_gains: bool = False) -> list:
    """Independent float64 numpy model of the standard pre-norm transformer, from the inputs only: per layer
    N1 = H/sqrt(msq(H)+Eps) * G1[l]; Q,K,V from N1; S = causal softmax_s(Q.K * Sc); Attn = W_O . (S.V);
    R1 = H + Attn; N2 = R1/sqrt(msq(R1)+Eps) * G2[l]; F = gelu(W_in . N2); Y = W_out . F; H' = R1 + Y,
    msq(x) = sum_m x^2 * Inv[m]. Returns one dict per layer keyed like the unrolled oracle's outputs
    (Ssa, Vea, Sda, Na, Q, K, V, S, AO, At, Ra, Ssb, Veb, Sdb, Nb, F, Y, H); `H` is the layer's OUTPUT."""
    f = {k: np.asarray(v, dtype=np.float64) for k, v in inp.items()}
    h, layers = f["X"], []
    tril = np.tril(np.ones((h.shape[0], h.shape[0]), dtype=bool))  # [q, s]: s <= q
    for l in range(n_layers):
        g1 = np.ones_like(f["G1"][l]) if unit_gains else f["G1"][l]
        g2 = np.ones_like(f["G2"][l]) if unit_gains else f["G2"][l]
        o = {}
        o["Ssa"] = np.einsum("qm,qm,m->q", h, h, f["Inv"])
        o["Vea"] = o["Ssa"] + f["Eps"]
        o["Sda"] = np.sqrt(o["Vea"])
        o["Na"] = h / o["Sda"][:, None] * g1
        o["Q"] = np.einsum("hkm,qm->qhk", f["W_Q"][l], o["Na"])
        o["K"] = np.einsum("hkm,sm->shk", f["W_K"][l], o["Na"])
        o["V"] = np.einsum("hkm,sm->shk", f["W_V"][l], o["Na"])
        lg = np.einsum("qhk,shk->hqs", o["Q"], o["K"]) * f["Sc"]
        o["S"] = np_softmax_last(np.where(tril[None], lg, -np.inf))
        o["AO"] = np.einsum("hqs,shk->qhk", o["S"], o["V"])
        o["At"] = np.einsum("mhk,qhk->qm", f["W_O"][l], o["AO"])
        o["Ra"] = h + o["At"]
        o["Ssb"] = np.einsum("qm,qm,m->q", o["Ra"], o["Ra"], f["Inv"])
        o["Veb"] = o["Ssb"] + f["Eps"]
        o["Sdb"] = np.sqrt(o["Veb"])
        o["Nb"] = o["Ra"] / o["Sdb"][:, None] * g2
        o["F"] = np_gelu(np.einsum("dm,qm->qd", f["W_in"][l], o["Nb"]))
        o["Y"] = np.einsum("md,qd->qm", f["W_out"][l], o["F"])
        o["H"] = o["Ra"] + o["Y"]
        layers.append(o)
        h = o["H"]
    return layers


def np_state(inp: dict, layers: list) -> np.ndarray:
    """The scan state H[q, m, l] from the numpy model: layer 0 is X, layer l+1 the output of layer l."""
    return np.stack([np.asarray(inp["X"], dtype=np.float64)] + [o["H"] for o in layers], axis=2)


def np_head(inp: dict, h_last: np.ndarray) -> dict:
    """Final RMSNorm with gain Gf, unembedding over the vocabulary and row softmax, from the last residual."""
    f = {k: np.asarray(v, dtype=np.float64) for k, v in inp.items()}
    o = {"Ssf": np.einsum("qm,qm,m->q", h_last, h_last, f["Inv"])}
    o["Vef"] = o["Ssf"] + f["Eps"]
    o["Sdf"] = np.sqrt(o["Vef"])
    o["Hf"] = h_last / o["Sdf"][:, None] * f["Gf"]
    o["Logits"] = np.einsum("vm,qm->qv", f["W_U"], o["Hf"])
    o["P"] = np_softmax_last(o["Logits"])
    return o


def bits(a: np.ndarray) -> np.ndarray:
    """The raw bit pattern of a float array (uint64 / uint32 view), for bitwise equality."""
    return np.ascontiguousarray(a).view(UDT)


def check_np(fixture: str, who: str, name: str, got, want) -> None:
    """Pin one exported output against the numpy model within MODEL_TOL; record the observed maxima."""
    g, w = np.asarray(got).astype(np.float64), np.asarray(want, dtype=np.float64)
    assert g.shape == w.shape, (fixture, who, name, g.shape, w.shape)
    assert np.all(np.isfinite(g)), (fixture, who, name, "non-finite")
    err = float(np.max(np.abs(g - w) / np.maximum(1.0, np.abs(w))))
    s = NUM_STATS.setdefault((fixture, name), [0.0, 0.0])
    s[0], s[1] = max(s[0], err), max(s[1], float(np.max(np.abs(g - w))))
    assert err < MODEL_TOL[_DT], (f"pin numpy model: {fixture} {who} {name}", err, g.tolist(), w.tolist())


def print_np_stats(fixture: str) -> None:
    for n in sorted(n for fx, n in NUM_STATS if fx == fixture):
        sc_err, ab = NUM_STATS[(fixture, n)]
        print(f"  {n:8s} vs numpy: max scaled {sc_err:.3e}  max abs {ab:.3e}  (tol {MODEL_TOL[_DT]:.0e})")


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
    for w in ("W_Q", "W_K", "W_V", "W_O", "W_in", "W_out", "G1", "G2"):
        assert sin[w].shape[0] == 3 and np.all(np.isnan(sin[w][2])) and np.all(np.isfinite(sin[w][:2])), w
    # the attention scale is 1/sqrt(d_k), d_k the key extent (W_Q is [l, h, k, m]): pinned against the input's own
    # shape, not against the numpy model that reads the exported value, so a wrong scale in the fixture is seen
    assert abs(float(np.asarray(sin["Sc"]).reshape(-1)[0]) - sin["W_Q"].shape[2] ** -0.5) < 1e-7, ("Sc != 1/sqrt(d_k)", sin["Sc"])
    views = {"lean": {n: lean_array(e) for n, e in sc["expected"].items()},
             "eager": {n: np.asarray(v) for n, v in EAGER[sc_name]["eager"].items()},
             "jit": {n: np.asarray(v) for n, v in EAGER[sc_name]["jit"].items()}}
    sc_layers = np_transformer(sin)
    sc_H = np_state(sin, sc_layers)
    # the learned gains matter: the same numpy model with unit gains gives a clearly different state, so the
    # numpy pin below cannot hold for a runtime that ignores G1/G2 (or reads them at the wrong layer)
    unit_gap = float(np.max(np.abs(np_state(sin, np_transformer(sin, unit_gains=True)) - sc_H)))
    assert unit_gap > 1e-2, ("gains do not matter to H: the pin would not see them", unit_gap)
    for who, outs_sc in views.items():
        assert "H" in outs_sc and all(np.all(np.isfinite(v)) for v in outs_sc.values()), (who, sorted(outs_sc))
        H = outs_sc["H"]
        assert H.shape == (3, 4, 3), (who, H.shape)
        # (c) layer 0 of the state is X, bit for bit (the base block's write)
        assert np.array_equal(np.ascontiguousarray(H[:, :, 0]).view(UDT), np.ascontiguousarray(sin["X"]).view(UDT)), who
        # (a) the whole state (layers 0, 1, 2) equals the independent numpy model of the standard pre-norm layer
        check_np(sc_name, who, "H", H, sc_H)
        # (a2) each layer's input is RMS-normalised BEFORE the learned gain: H_l / sqrt(msq(H_l) + Eps) has
        # Inv-weighted mean square msq/(msq+Eps) = 1 - O(Eps/msq) (computed in numpy from this view's H); the
        # raw layer input is not itself unit mean square (X is not), so the check is not vacuous
        Inv, Eps = sin["Inv"].astype(np.float64), sin["Eps"].astype(np.float64)
        raw_gap = []
        for l in range(3):
            hl = H[:, :, l].astype(np.float64)
            msq = np.sum(hl * hl * Inv, axis=1)
            nrm = hl / np.sqrt(msq + Eps)[:, None]
            ms = np.sum(nrm * nrm * Inv, axis=1)
            assert np.all(np.abs(ms - 1.0) <= Eps / msq + 1e-12), (who, l, ms.tolist())
            raw_gap.append(float(np.max(np.abs(msq - 1.0))))
        assert max(raw_gap) > 0.05, (who, raw_gap)
        # (d) the two layers differ: a step that ignored its context coordinate would repeat layer 1
        gap = float(np.max(np.abs(H[:, :, 1].astype(np.float64) - H[:, :, 2].astype(np.float64))))
        assert gap > 1e-2, (who, gap)
    print(f"transformer_scan: one scan record, 2 steps, layer-2 weights NaN in the inputs and every output finite; "
          f"H layer 0 == X bitwise, H layers 0, 1, 2 == independent numpy pre-norm model (unit-gain model differs by "
          f"{unit_gap:.3f}), RMS-normalised layer inputs have mean square 1 - O(Eps/msq), layers 1 and 2 differ (max abs "
          f"gap {gap:.3f}); pins hold on Lean, eager and jit; per-output measured difference vs numpy and vs Lean:")
    print_np_stats(sc_name)
    for n in sorted(n for fx, n in OUT_STATS if fx == sc_name):
        rel, ab, ex, tot = OUT_STATS[(sc_name, n)]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")

    # Scan transformer WITH A HEAD: after the scan, a final RMSNorm with learned gain Gf of the residual stream
    # `H[:, :, 2]` (standard pre-norm: nothing is added back), an unembedding `Logits = Hf @ W_U.T` over a
    # vocabulary axis of extent 5, and a softmax over the vocabulary. Lean and JAX agreeing proves nothing
    # about the head, so the pins recompute the model in plain numpy (float64) from the fixture's INPUTS
    # only (`np_transformer` + `np_head`), and the head chain again from the state `H` slice 2 of the SAME
    # view (Lean, eager, jit), never from that view's own Hf / Logits / P outputs.
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
    assert set(hin) == set(sin) | {"W_U", "Gf"}, sorted(hin)
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
    hd_layers = np_transformer(hin)
    hd_H = np_state(hin, hd_layers)
    hd_np = np_head(hin, hd_H[:, :, 2])
    # the numpy head is not degenerate: the gain Gf matters, and the normalised stream is not already unit
    # mean square (so the norm is not the identity)
    Inv, Eps, WU, Gf = (hin[n].astype(np.float64) for n in ("Inv", "Eps", "W_U", "Gf"))
    msq_raw = np.sum(hd_H[:, :, 2] ** 2 * Inv, axis=1)
    assert np.any(np.abs(msq_raw - 1.0) > 0.05), ("final-norm input is already unit mean square", msq_raw.tolist())
    assert float(np.max(np.abs(hd_np["Hf"] - hd_np["Hf"] / Gf))) > 1e-2, "Gf is not distinguishable from 1"
    for who, outs_hd in hviews.items():
        assert {"H", "Logits", "P", "Hf"} <= set(outs_hd), (who, sorted(outs_hd))
        assert "Zf" not in outs_hd, (who, "stale post-norm output Zf is still exported")
        assert all(np.all(np.isfinite(v)) for v in outs_hd.values()), who
        P = outs_hd["P"].astype(np.float64)
        # (a) every row of P is a probability vector over the vocabulary
        rowdev = float(np.max(np.abs(P.sum(axis=1) - 1.0)))
        assert np.all(P > 0) and rowdev < HEAD_ROWSUM_TOL[_DT], ("pin (a) P rows positive and sum to 1", who, rowdev, P.tolist())
        # (n) every exported output equals the independent numpy model from the INPUTS only
        check_np(hd_name, who, "H", outs_hd["H"], hd_H)
        for n in ("Ssf", "Vef", "Sdf", "Hf", "Logits", "P"):
            if n in outs_hd:
                check_np(hd_name, who, n, outs_hd[n], hd_np[n])
        # (c) the final-norm output divided by its gain is RMS-normalised: Inv-weighted mean square
        # msq/(msq+Eps) = 1 - O(Eps/msq) (msq from THIS view's H slice 2)
        h2 = outs_hd["H"][:, :, 2].astype(np.float64)
        msq = np.sum(h2 * h2 * Inv, axis=1)
        ms_hf_out = np.sum((outs_hd["Hf"].astype(np.float64) / Gf) ** 2 * Inv, axis=1)
        assert np.all(np.abs(ms_hf_out - 1.0) <= Eps / msq + HEAD_LOGITS_TOL[_DT]), \
            ("pin (c) Hf / Gf is RMS-normalised", who, ms_hf_out.tolist())
        # (b) Logits == Hf @ W_U.T, with Hf recomputed in numpy from THIS view's H slice 2
        Hf = h2 / np.sqrt(msq + Eps)[:, None] * Gf
        want = Hf @ WU.T
        ldiff = float(np.max(np.abs(outs_hd["Logits"].astype(np.float64) - want)))
        assert ldiff < HEAD_LOGITS_TOL[_DT], ("pin (b) Logits == numpy from H slice 2", who, ldiff, outs_hd["Logits"].tolist(), want.tolist())
        # (a') P is the row-wise numerically stable softmax of the numpy Logits (NOT of this view's own outputs)
        ex = np.exp(want - want.max(axis=1, keepdims=True))
        sdiff = float(np.max(np.abs(P - ex / ex.sum(axis=1, keepdims=True))))
        assert sdiff < HEAD_SOFTMAX_TOL[_DT], ("pin (a') P == softmax(numpy Logits)", who, sdiff, P.tolist())
        print(f"  head {who}: P row-sum dev {rowdev:.3e}, P vs softmax(numpy Logits) max abs {sdiff:.3e}, "
              f"(Hf/Gf) mean-square {[round(float(x), 6) for x in ms_hf_out]}, Logits vs numpy max abs {ldiff:.3e}")
    # (k) CAUSALITY on the JAX runtime (eager): the standard model is causal, so changing the input X ONLY in
    # position row q = 2 must leave rows q = 0, 1 of H, Logits and P BITWISE unchanged and change row 2. A
    # non-causal runtime (a dropped or wrong mask, a future read) fails this without any reference to Lean.
    X_base = hin["X"]
    X_pert = X_base.copy()
    X_pert[2, :] += NDT(0.5)
    assert not np.array_equal(X_pert[2], X_base[2]) and np.array_equal(X_pert[:2], X_base[:2])
    hd_in = {n: jnp.asarray(a) for n, a in hin.items()}
    hd_in_pert = dict(hd_in, X=jnp.asarray(X_pert))
    run_pert = rt.run_named(hd["plan"], hd_in_pert, JDT)
    run_base = EAGER[hd_name]["eager"]
    for n in ("H", "Logits", "P"):
        b, p = np.asarray(run_base[n]), np.asarray(run_pert[n])
        assert b.dtype == p.dtype == NDT and b.shape == p.shape, (n, b.dtype, p.dtype)
        assert np.array_equal(bits(b[:2]), bits(p[:2])), ("causality: rows 0, 1 changed under a row-2 perturbation", n)
        row2 = float(np.max(np.abs(b[2].astype(np.float64) - p[2].astype(np.float64))))
        assert row2 > 1e-3, ("causality: row 2 did not respond to its own perturbation", n, row2)
        print(f"  causality {n}: rows 0, 1 bitwise identical under X[2, :] += 0.5, row 2 changes by max abs {row2:.3e}")
    # the same property of the numpy model (a sanity check of the pin's own reference)
    pert_layers = np_transformer(dict(hin, X=X_pert))
    pert_H = np_state(dict(hin, X=X_pert), pert_layers)
    pert_head = np_head(hin, pert_H[:, :, 2])
    for n, a, b in (("H", hd_H, pert_H), ("Logits", hd_np["Logits"], pert_head["Logits"]), ("P", hd_np["P"], pert_head["P"])):
        assert np.array_equal(a[:2], b[:2]) and not np.array_equal(a[2], b[2]), ("numpy causality", n)
    print(f"transformer_head: plan = 1 scan + {len(h_after)} plain nodes {[n.get('kind', 'assign') for n in h_after]}; "
          f"vocabulary extent {vocab} (from W_U) differs from every other extent and is Logits[1], P[1]; head scan == "
          f"transformer_scan (inputs and H bitwise); H, Ssf, Vef, Sdf, Hf, Logits, P == independent numpy model on Lean, "
          f"eager and jit; P rows positive and sum to 1; Logits == numpy Hf @ W_U.T from H slice 2; P == softmax(numpy "
          f"Logits); Hf / Gf RMS-normalised; causal (row-2 perturbation leaves rows 0, 1 bitwise unchanged); "
          f"per-output measured difference vs numpy and vs Lean:")
    print_np_stats(hd_name)
    for n in sorted(n for fx, n in OUT_STATS if fx == hd_name):
        rel, ab, ex, tot = OUT_STATS[(hd_name, n)]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")

    # POST-SCAN ROLE: `S[j, l+1] := S[j, l] . G[j]` (closed form `S = X * G**l`) and six statements nothing in
    # the recurrence reads, so each is a plain node AFTER the one scan node and `l` is an ordinary axis in it.
    # Lean and JAX agreeing proves nothing here, so every view (Lean, eager, jit) is recomputed in numpy float64
    # from the fixture's INPUTS only (X, G, V and the closed form), never from the view's own outputs.
    pr_name = "scan_postrole" + sfx
    pr = by[pr_name]
    pin_ = {n: lean_array(e).astype(np.float64) for n, e in pr["inputs"].items()}
    pnodes = pr["plan"]["nodes"]
    p_after = pnodes[1:]
    assert pnodes[0].get("kind") == "scan" and all(n.get("kind") != "scan" for n in p_after) and len(p_after) > 0, \
        [n.get("kind") for n in pnodes]
    assert sorted(pin_) == ["G", "M", "V", "X"], sorted(pin_)
    pX, pG, pV, pM = pin_["X"], pin_["G"], pin_["V"], pin_["M"]
    pL = pV.shape[0]
    assert pL == pnodes[0]["step_count"] + 1, (pL, pnodes[0]["step_count"])
    assert pM.shape == pV.shape and set(np.unique(pM)) <= {0.0, 1.0}, pM.tolist()
    assert pL not in set(pX.shape) | set(pG.shape), ("history extent collides with another extent", pL)
    pS = pX[:, None] * pG[:, None] ** np.arange(pL)[None, :]
    pSm = np.zeros_like(pS)
    pe = np.exp(pS[:, :2])
    pSm[:, :2] = pe / pe.sum(axis=1, keepdims=True)
    pwant = {"S": pS, "Zc": pS[:, 2] * pM.sum(), "Ysum": pS[:, 2] * pV.sum(), "Yfree": (pS * pV[None, :]).sum(axis=1),
             "T": pS * pV[None, :], "Bc": np.repeat(pS[:, 2:3], pL, axis=1), "Sm": pSm}
    pviews = {"lean": {n: lean_array(e) for n, e in pr["expected"].items()},
              "eager": {n: np.asarray(v) for n, v in EAGER[pr_name]["eager"].items()},
              "jit": {n: np.asarray(v) for n, v in EAGER[pr_name]["jit"].items()}}
    for who, po in pviews.items():
        assert set(pwant) <= set(po), (who, sorted(po))
        errs = {}
        for n, w in pwant.items():
            got = po[n].astype(np.float64)
            assert got.shape == w.shape, (who, n, got.shape, w.shape)
            errs[n] = (float(np.max(np.abs(got - w) / np.maximum(1.0, np.abs(w)))), float(np.max(np.abs(got - w))))
            assert errs[n][0] < POSTROLE_TOL[_DT], ("post-role pin: output vs numpy from the inputs", who, n, errs[n], got.tolist(), w.tolist())
        # the free read is the sum over every layer, NOT the per-step reading (last layer times last V entry)
        last = pS[:, -1] * pV[-1]
        gap = float(np.min(np.abs(po["Yfree"].astype(np.float64) - last) / np.abs(last)))
        assert gap > 1e-2, ("post-role pin: Yfree is not the per-step reading", who, gap)
        # Zc sums the mask over the full history extent, NOT over the steps {0..L-2} only
        zc_steps = pS[:, 2] * pM[:-1].sum()
        zgap = float(np.min(np.abs(po["Zc"].astype(np.float64) - zc_steps) / np.abs(zc_steps)))
        assert zgap > 1e-2, ("post-role pin: Zc is not the steps-only count", who, zgap)
        # the masked-out layers of Sm are exactly 0 and the allowed layers sum to 1
        assert np.all(po["Sm"][:, 2:] == 0) and np.allclose(po["Sm"].astype(np.float64).sum(axis=1), 1.0, atol=1e-6), (who, po["Sm"].tolist())
        print(f"  postrole {who}: " + ", ".join(f"{n} {errs[n][1]:.2e}/{errs[n][0]:.2e}" for n in pwant) +
              f" (max abs / scaled vs numpy), Yfree vs per-step reading min rel gap {gap:.3f}, Zc vs steps-only count min rel gap {zgap:.3f}")
    print(f"scan_postrole: plan = 1 scan + {len(p_after)} plain nodes {[n.get('kind', 'assign') for n in p_after]}; history "
          f"extent {pL} (from V[0]) differs from the other extents; S == X*G**l; Zc, Ysum, Yfree, T, Bc, Sm == numpy "
          f"recomputation from the inputs on Lean, eager and jit; Yfree is not the per-step reading; Sm masked layers are "
          f"exactly 0; per-output measured difference vs Lean:")
    for n in sorted(n for fx, n in OUT_STATS if fx == pr_name):
        rel, ab, ex, tot = OUT_STATS[(pr_name, n)]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")

    # UNROLLED ORACLE: the same two layers as two hand-copied flat layers (no scan; the old, trusted flat
    # lowering). Scan and unrolled take their weights from ONE Lean definition; the inputs are re-checked
    # bitwise here. The JAX scan state `H[:, :, 1]`, `H[:, :, 2]` must equal the JAX unrolled `H1`, `H2` within
    # ORACLE_TOL, eager and jit. This ties the scan lowering to the flat lowering WITHOUT Lean.
    un_name = "transformer_unrolled" + sfx
    un = by[un_name]
    assert not any(n.get("kind") == "scan" for n in un["plan"]["nodes"]), "the oracle must not contain a scan"
    uin = {n: lean_array(e) for n, e in un["inputs"].items()}
    for n in ("X", "Inv", "Eps", "Sc"):
        assert np.array_equal(bits(sin[n]), bits(uin[n])), n
    # per-layer weights and gains: `<name><layer>` (G11 = G1 of layer 1, G12 = G1 of layer 2, G21 = G2 of
    # layer 1, G22 = G2 of layer 2) are layers 0 and 1 of the scan's stacks, bit for bit
    stacked = ("W_Q", "W_K", "W_V", "W_O", "W_in", "W_out", "G1", "G2")
    for w in stacked:
        for l in (0, 1):
            assert np.array_equal(bits(sin[w][l]), bits(uin[f"{w}{l + 1}"])), (w, l)
    assert len(uin) == 4 + 2 * len(stacked) and not any(np.any(np.isnan(v)) for v in uin.values()), sorted(uin)
    # the two layers' gains differ, so a swapped G1/G2 or a layer-swapped gain changes the oracle
    assert not np.array_equal(uin["G11"], uin["G12"]) and not np.array_equal(uin["G21"], uin["G22"]) \
        and not np.array_equal(uin["G11"], uin["G21"])
    # EVERY exported output of the unrolled oracle (36 per view) equals the independent numpy model assembled
    # from the oracle's OWN per-layer inputs, on Lean, eager and jit
    un_stacks = dict(uin, **{w: np.stack([uin[f"{w}1"], uin[f"{w}2"]]) for w in stacked})
    un_layers = np_transformer(un_stacks)
    un_names = sorted(un["expected"])
    assert len(un_names) == 36, un_names
    un_views = {"lean": {n: lean_array(e) for n, e in un["expected"].items()},
                "eager": {n: np.asarray(v) for n, v in EAGER[un_name]["eager"].items()},
                "jit": {n: np.asarray(v) for n, v in EAGER[un_name]["jit"].items()}}
    for who, uo in un_views.items():
        assert sorted(uo) == un_names, (who, sorted(uo))
        for l, layer in enumerate(un_layers, start=1):
            for key, want in layer.items():
                check_np(un_name, who, f"{key}{l}", uo[f"{key}{l}"], want)
        # the unrolled normalised outputs, divided by their gain, are RMS-normalised: msq/(msq+Eps) = 1 - O(Eps/msq)
        for pre, post, gname in (("X", "Na1", "G11"), ("Ra1", "Nb1", "G21"), ("H1", "Na2", "G12"), ("Ra2", "Nb2", "G22")):
            hp = (uin["X"] if pre == "X" else uo[pre]).astype(np.float64)
            msq = np.sum(hp * hp * uin["Inv"].astype(np.float64), axis=1)
            nrm = uo[post].astype(np.float64) / uin[gname].astype(np.float64)
            ms = np.sum(nrm * nrm * uin["Inv"].astype(np.float64), axis=1)
            assert np.all(np.abs(ms - 1.0) <= uin["Eps"].astype(np.float64) / msq + HEAD_LOGITS_TOL[_DT]), (who, post, ms.tolist())
        # causal structure of the oracle's own attention probabilities (heads x rows x keys): row q keeps q+1 entries
        for sname in ("S1", "S2"):
            Sx = uo[sname]
            assert [int(np.sum(Sx[0, q] != 0)) for q in range(3)] == [1, 2, 3], (who, sname, Sx.tolist())
            assert np.all(Sx[:, 0, 1:] == 0) and np.all(Sx[:, 1, 2] == 0) and np.allclose(Sx.sum(axis=2), 1.0, atol=1e-6), (who, sname)
    print(f"transformer_unrolled: all {len(un_names)} exported outputs == independent numpy model (from the oracle's own "
          f"per-layer inputs) on Lean, eager and jit; G11, G12, G21, G22 are the scan stacks' layer slices bitwise; "
          f"normalised outputs / gain are RMS-normalised; S1, S2 causal; measured difference vs numpy (max over the 36 "
          f"outputs and the views):")
    worst = max(((NUM_STATS[(un_name, n)][0], n) for n in un_names), key=lambda t: t[0])
    print(f"  max scaled {worst[0]:.3e} at {worst[1]}; max abs {max(NUM_STATS[(un_name, n)][1] for n in un_names):.3e}; "
          f"H1 {NUM_STATS[(un_name, 'H1')][0]:.3e}, H2 {NUM_STATS[(un_name, 'H2')][0]:.3e}")
    for mode in ("eager", "jit"):
        h_scan = np.asarray(EAGER[sc_name][mode]["H"])
        for l in (1, 2):
            o_rtol, o_atol = ORACLE_EAGER_TOL32 if (_DT == "float32" and mode == "eager" and l == 2) else ORACLE_TOL[_DT]
            g, u = h_scan[:, :, l], np.asarray(EAGER[un_name][mode][f"H{l}"])
            assert g.shape == u.shape == (3, 4) and g.dtype == u.dtype == NDT, (mode, l, g.shape, u.shape)
            d = np.abs(g.astype(np.float64) - u.astype(np.float64))
            nbit = int(np.sum(bits(g) == bits(u)))
            print(f"  oracle {mode} layer {l}: max abs {float(d.max()):.3e}  bit-identical {nbit}/{g.size}")
            assert np.all(d <= o_atol + o_rtol * np.abs(u.astype(np.float64))), (mode, l, g.tolist(), u.tolist())
        # non-vacuous: the layers differ, so swapping them is rejected by the same comparison
        assert float(np.max(np.abs(h_scan[:, :, 1].astype(np.float64)
                                   - np.asarray(EAGER[un_name][mode]["H2"]).astype(np.float64)))) > 1e-2
    print(f"scan-vs-unrolled oracle: JAX scan H layers 1, 2 == JAX unrolled H1, H2 within rtol/atol "
          f"{ORACLE_TOL[_DT]} (eager + jit)" + (f", except binary32 eager within {ORACLE_EAGER_TOL32}" if _DT == "float32" else "")
          + ", identical inputs and gains checked bitwise, layers swapped would be rejected")

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
