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
                        "transformer_unrolled", "transformer_unrolled32",
                        "transformer_window", "transformer_window32", "transformer_strict", "transformer_strict32",
                        "transformer_sink", "transformer_sink32", "transformer_mqa", "transformer_mqa32",
                        "transformer_gqa", "transformer_gqa32", "transformer_gqa_split", "transformer_gqa_split32",
                        "transformer_gqa_mha", "transformer_gqa_mha32"}
# Predicate-mask scan fixtures (`transformer_<kind>`, q = s = 5): kind -> the perturbed position of the
# receptive-field pin (chosen so the reachable and the unreachable row sets are both non-empty).
MASK_FIXTURES = {"window": 0, "strict": 4, "sink": 3}
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
# Gradient pins (`grad_fixture_pins`): max over entries of |grad - reference| / max(1, |reference|) for the scan plan's `jax.grad`
# against the unrolled plan's and a pure-JAX model's (carrier dtype), MEASURED (eager and jit, max over inputs): float64 1.2e-15 (pure-JAX
# model) / 2.1e-15 (unrolled), float32 1.3e-6 / 1.5e-6; a wrong gradient entry is O(1e-1) or more. `GRAD_FD_TOL` bounds the directional
# derivative against float64 central differences of the numpy model (float64: the finite-difference error ~1e-9).
GRAD_TOL = {"float64": 1e-12, "float32": 1e-4}
GRAD_FD_TOL = {"float64": 1e-7, "float32": 1e-4}
# (fixture, output) -> [max scaled error, max abs error] over the Lean, eager and jit views
NUM_STATS: dict[tuple[str, str], list] = {}


def np_gelu(x):
    """gelu, tanh approximation, exactly the formula the model states (float64)."""
    return 0.5 * x * (1.0 + np.tanh(0.7978845608028654 * (x + 0.044715 * x ** 3)))


def np_softmax_last(z):
    e = np.exp(z - z.max(axis=-1, keepdims=True))
    return e / e.sum(axis=-1, keepdims=True)


def np_masked_softmax(lg, allow):
    """Softmax over the last axis of `lg[h, q, s]` restricted to the entries `allow[q][s]`; a query row that
    allows nothing is all ZERO (not uniform, not NaN), as the standalone all-masked fixtures pin."""
    out = np.zeros_like(lg)
    for h in range(lg.shape[0]):
        for q in range(lg.shape[1]):
            cols = [s for s in range(lg.shape[2]) if allow[q][s]]
            if cols:
                z = lg[h, q, cols]
                e = np.exp(z - z.max())
                out[h, q, cols] = e / e.sum()
    return out


def mask_allow(kind: str, n: int) -> np.ndarray:
    """`allow[q][s]` of each predicate mask, written from its English definition with plain loops:
    window = attend to the current and the previous position; strict = attend to strictly earlier positions only;
    sink = the causal window of width 2 plus position 0 (the attention sink)."""
    allow = np.zeros((n, n), dtype=bool)
    for q in range(n):
        for s in range(n):
            if kind == "window":
                allow[q][s] = (s <= q and q - s < 2)
            elif kind == "strict":
                allow[q][s] = (s < q)
            else:
                allow[q][s] = (s <= q and (s == 0 or q - s < 2))
    return allow


def np_transformer(inp: dict, n_layers: int = 2, unit_gains: bool = False, allow=None, mqa: bool = False) -> list:
    """Independent float64 numpy model of the standard pre-norm transformer, from the inputs only: per layer
    N1 = H/sqrt(msq(H)+Eps) * G1[l]; Q,K,V from N1; S = causal softmax_s(Q.K * Sc) (or over `allow[q][s]` when given: an all-masked query row is zero); Attn = W_O . (S.V);
    R1 = H + Attn; N2 = R1/sqrt(msq(R1)+Eps) * G2[l]; F = gelu(W_in . N2); Y = W_out . F; H' = R1 + Y,
    msq(x) = sum_m x^2 * Inv[m]. With `mqa` the key and value projections have no head axis (`W_K[l, k, m]`,
    `W_V[l, k, m]`, `K[s, k]`, `V[s, k]`, shared by every query head). Returns one dict per layer keyed like the unrolled oracle's outputs
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
        if mqa:
            o["K"] = np.einsum("km,sm->sk", f["W_K"][l], o["Na"])
            o["V"] = np.einsum("km,sm->sk", f["W_V"][l], o["Na"])
            lg = np.einsum("qhk,sk->hqs", o["Q"], o["K"]) * f["Sc"]
        else:
            o["K"] = np.einsum("hkm,sm->shk", f["W_K"][l], o["Na"])
            o["V"] = np.einsum("hkm,sm->shk", f["W_V"][l], o["Na"])
            lg = np.einsum("qhk,shk->hqs", o["Q"], o["K"]) * f["Sc"]
        o["S"] = (np_softmax_last(np.where(tril[None], lg, -np.inf)) if allow is None
                  else np_masked_softmax(lg, allow))
        o["AO"] = (np.einsum("hqs,sk->qhk", o["S"], o["V"]) if mqa
                   else np.einsum("hqs,shk->qhk", o["S"], o["V"]))
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


def reachable_rows(allow, p: int, steps: int) -> set:
    """Rows that depend on position p after `steps` layers: a row keeps itself (residual) and gains every row
    that attends to a row already reached (`allow[q][s]`: query q attends to position s)."""
    rows = {p}
    for _ in range(steps):
        rows = rows | {q for q in range(len(allow)) if any(allow[q][s] for s in rows)}
    return rows


def mask_fixture_pins(by: dict, kind: str, sfx: str) -> None:
    """Pins of one predicate-mask scan fixture (`transformer_<kind>`): value pin against the numpy model whose mask
    is written from the English definition, non-vacuity against the causal model and the other masks, and the
    receptive-field pin on the eager runtime (rows unreachable from the perturbed position stay BITWISE equal)."""
    name = f"transformer_{kind}{sfx}"
    fx = by[name]
    scans = [n for n in fx["plan"]["nodes"] if n.get("kind") == "scan"]
    assert len(fx["plan"]["nodes"]) == 1 and len(scans) == 1 and scans[0]["step_count"] == 2, fx["plan"]["nodes"]
    fin = {n: lean_array(e) for n, e in fx["inputs"].items()}
    n_pos = fin["X"].shape[0]
    assert fin["X"].shape == (5, 4) and fin["Eps"].shape == (5,) and n_pos == 5, (fin["X"].shape, fin["Eps"].shape)
    # the model's own layer-2 slice is NaN in the weight stacks, as in the standard scan fixture
    for w in ("W_Q", "W_K", "W_V", "W_O", "W_in", "W_out", "G1", "G2"):
        assert fin[w].shape[0] == 3 and np.all(np.isnan(fin[w][2])) and np.all(np.isfinite(fin[w][:2])), w
    allow = mask_allow(kind, n_pos)
    layers = np_transformer(fin, allow=allow)
    want = np_state(fin, layers)
    # non-vacuity: the pin tells this mask apart from the causal one and from the other two masks
    causal_gap = float(np.max(np.abs(want - np_state(fin, np_transformer(fin)))))
    assert causal_gap > 1e-2, (name, "mask is indistinguishable from the causal mask", causal_gap)
    other_gaps = {}
    for other in MASK_FIXTURES:
        if other != kind:
            other_gaps[other] = float(np.max(np.abs(
                want - np_state(fin, np_transformer(fin, allow=mask_allow(other, n_pos))))))
            assert other_gaps[other] > 1e-2, (name, "mask is indistinguishable from", other, other_gaps[other])
    views = {"lean": {n: lean_array(e) for n, e in fx["expected"].items()},
             "eager": {n: np.asarray(v) for n, v in EAGER[name]["eager"].items()},
             "jit": {n: np.asarray(v) for n, v in EAGER[name]["jit"].items()}}
    for who, outs in views.items():
        assert "H" in outs and all(np.all(np.isfinite(v)) for v in outs.values()), (name, who, sorted(outs))
        assert outs["H"].shape == (n_pos, 4, 3), (name, who, outs["H"].shape)
        check_np(name, who, "H", outs["H"], want)
    extra = ""
    if kind == "strict":
        # query row 0 attends nothing: the numpy attention row is exactly zero (not uniform, not NaN) and so is the
        # attention-weighted value, in every layer; a uniform row 0 would give a clearly different state
        for l, o in enumerate(layers):
            assert not allow[0].any() and np.all(o["S"][:, 0, :] == 0.0) and np.all(o["AO"][0] == 0.0), (name, l)
            assert np.all(o["At"][0] == 0.0) and np.all(o["Ra"][0] == (want[0, :, l])), (name, l)
        uniform = allow.copy()
        uniform[0, :] = True
        uni_gap = float(np.max(np.abs(want[0] - np_state(fin, np_transformer(fin, allow=uniform))[0])))
        assert uni_gap > 1e-3, (name, "a uniform row 0 is indistinguishable from the zero row", uni_gap)
        extra = f"; row 0 attends nothing (zero attention row in numpy, uniform row 0 would move H row 0 by {uni_gap:.3f})"
    # receptive field: perturb X at position p, rerun on the eager runtime. Rows that the mask's two-step reachability
    # (from `allow`, two layers) cannot reach from p are bitwise unchanged in every layer of H; some reachable row moves.
    p = MASK_FIXTURES[kind]
    reach = reachable_rows(allow, p, 2)
    unreach = sorted(set(range(n_pos)) - reach)
    assert reach and unreach and p in reach, (name, p, sorted(reach), unreach)
    X_pert = fin["X"].copy()
    X_pert[p, :] += NDT(0.5)
    run_pert = rt.run_named(fx["plan"], {n: jnp.asarray(a) for n, a in dict(fin, X=X_pert).items()}, JDT)
    b, pt = np.asarray(EAGER[name]["eager"]["H"]), np.asarray(run_pert["H"])
    assert b.dtype == pt.dtype == NDT and b.shape == pt.shape, (name, b.dtype, pt.dtype)
    assert np.array_equal(bits(b[unreach]), bits(pt[unreach])), (name, "rows", unreach, "changed under a perturbation of position", p)
    moved = float(np.max(np.abs(b[sorted(reach)].astype(np.float64) - pt[sorted(reach)].astype(np.float64))))
    assert moved > 1e-3, (name, "reachable rows did not respond to the perturbation", sorted(reach), moved)
    # the perturbed row moves trivially (H[p, :, 0] is X[p]); the perturbation must also PROPAGATE through attention
    # to every other reachable row's final state (none exists for strict: nothing attends to the last position)
    for r in sorted(reach - {p}):
        prop = float(np.max(np.abs(b[r, :, 2].astype(np.float64) - pt[r, :, 2].astype(np.float64))))
        assert prop > 1e-3, (name, "perturbation did not propagate to reachable row", r, prop)
    # the numpy model has the same receptive field (sanity of the pin's own reference)
    want_pert = np_state(dict(fin, X=X_pert), np_transformer(dict(fin, X=X_pert), allow=allow))
    assert np.array_equal(want[unreach], want_pert[unreach]), (name, "numpy receptive field")
    assert float(np.max(np.abs(want[sorted(reach)] - want_pert[sorted(reach)]))) > 1e-3, name
    print(f"{name}: allow rows {[''.join('1' if a else '0' for a in r) for r in allow]}; one scan record, 2 steps; "
          f"H layers 0, 1, 2 == numpy model with the English-definition mask on Lean, eager and jit; differs from the "
          f"causal model by {causal_gap:.3f} and from {', '.join(f'{k} by {v:.3f}' for k, v in other_gaps.items())}; "
          f"receptive field of X[{p}]: rows {sorted(reach)} respond (max abs {moved:.3e}), rows {unreach} bitwise "
          f"unchanged on the eager runtime{extra}; per-output measured difference vs numpy and vs Lean:")
    print_np_stats(name)
    sc_err = NUM_STATS[(name, "H")][0]
    print(f"  H headroom to MODEL_TOL: {MODEL_TOL[_DT] / max(sc_err, 1e-300):.1f}x (observed {sc_err:.3e} of {MODEL_TOL[_DT]:.0e})")
    for n in sorted(n for fx_, n in OUT_STATS if fx_ == name):
        rel, ab, ex, tot = OUT_STATS[(name, n)]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")


def mqa_fixture_pins(by: dict, sfx: str) -> None:
    """Pins of the multi-query scan fixture (`transformer_mqa`): `K[s, k]` and `V[s, k]` carry no head axis (weights
    `W_K[l, k, m]`, `W_V[l, k, m]`), `Q[q, h, k]` does. Value pin against the numpy model with head-free K and V,
    non-vacuity against the multi-head model and between the two query heads, equivalence to the STANDARD multi-head
    plan run on head-replicated weights (eager runtime, no Lean value involved), NaN layer-2 slices."""
    name = f"transformer_mqa{sfx}"
    std_name = f"transformer_scan{sfx}"
    fx, std = by[name], by[std_name]
    scans = [n for n in fx["plan"]["nodes"] if n.get("kind") == "scan"]
    assert len(fx["plan"]["nodes"]) == 1 and len(scans) == 1 and scans[0]["step_count"] == 2, fx["plan"]["nodes"]
    fin = {n: lean_array(e) for n, e in fx["inputs"].items()}
    sin = {n: lean_array(e) for n, e in std["inputs"].items()}
    assert sorted(fin) == sorted(sin), (sorted(fin), sorted(sin))
    n_heads, n_k = sin["W_Q"].shape[1], sin["W_Q"].shape[2]
    # the head axis is gone from the key and value weights (and only from those), the query weights keep it
    assert fin["W_Q"].shape == sin["W_Q"].shape and fin["W_O"].shape == sin["W_O"].shape, name
    assert fin["W_K"].shape == fin["W_V"].shape == (3, n_k, 4) and sin["W_K"].shape == (3, n_heads, n_k, 4), (name, fin["W_K"].shape)
    # every other input is the standard fixture's, bit for bit; layer 0 of the head-free stacks is head 1's slice of
    # the standard weights (not head 0: head 0's slices are binary32 ill-conditioned, see `mqaWK` in the Lean file; no new
    # magic numbers), layer 1 differs from layer 0 and layer 2 is NaN
    for n in sin:
        if n not in ("W_K", "W_V"):
            assert np.array_equal(bits(fin[n]), bits(sin[n])), (name, "input differs from the standard fixture", n)
    for w in ("W_K", "W_V"):
        assert np.array_equal(bits(fin[w][0]), bits(sin[w][0, 1])), (name, w)
        assert np.all(np.isnan(fin[w][2])) and np.all(np.isfinite(fin[w][:2])), (name, w)
        assert not np.array_equal(fin[w][0], fin[w][1]), (name, w)
    for w in ("W_Q", "W_O", "W_in", "W_out", "G1", "G2"):
        assert fin[w].shape[0] == 3 and np.all(np.isnan(fin[w][2])) and np.all(np.isfinite(fin[w][:2])), (name, w)
    layers = np_transformer(fin, mqa=True)
    want = np_state(fin, layers)
    # non-vacuity (a): the pin tells MQA apart from the multi-head model on the standard head-carrying weights
    mh_gap = float(np.max(np.abs(want - np_state(sin, np_transformer(sin)))))
    assert mh_gap > 1e-2, (name, "MQA is indistinguishable from the multi-head model", mh_gap)
    # non-vacuity (b): the two query heads attend differently (a model where every head had the same attention would
    # pass a broadcast test vacuously), in every layer
    head_gaps = [float(np.max(np.abs(o["S"][0] - o["S"][1]))) for o in layers]
    assert all(g > 1e-2 for g in head_gaps), (name, "heads attend alike", head_gaps)
    views = {"lean": {n: lean_array(e) for n, e in fx["expected"].items()},
             "eager": {n: np.asarray(v) for n, v in EAGER[name]["eager"].items()},
             "jit": {n: np.asarray(v) for n, v in EAGER[name]["jit"].items()}}
    for who, outs in views.items():
        # exactly the state is exported, and it is finite (a step reading layer 2 would turn it NaN)
        assert sorted(outs) == ["H"] and np.all(np.isfinite(outs["H"])), (name, who, sorted(outs))
        assert outs["H"].shape == (3, 4, 3), (name, who, outs["H"].shape)
        check_np(name, who, "H", outs["H"], want)
    # equivalence: the STANDARD multi-head plan on weights with the head-free K and V replicated over h computes the
    # same state as the MQA plan (eager runtime on both sides; a wrong K or V slice, or a broadcast over the wrong axis
    # in the MQA plan, breaks it). The standard plan on its own, head-distinct weights does NOT (non-vacuity).
    mh_in = dict(fin)
    for w in ("W_K", "W_V"):
        mh_in[w] = np.repeat(fin[w][:, None], n_heads, axis=1)
    assert mh_in["W_K"].shape == sin["W_K"].shape, (name, mh_in["W_K"].shape)
    run_mh = rt.run_named(std["plan"], {n: jnp.asarray(a) for n, a in mh_in.items()}, JDT)
    h_mqa, h_mh = np.asarray(EAGER[name]["eager"]["H"]), np.asarray(run_mh["H"])
    assert h_mqa.dtype == h_mh.dtype == NDT and h_mqa.shape == h_mh.shape, (name, h_mqa.dtype, h_mh.dtype)
    equal_bits = int(np.sum(bits(h_mqa) == bits(h_mh)))
    equiv_gap = float(np.max(np.abs(h_mqa.astype(np.float64) - h_mh.astype(np.float64))))
    assert equal_bits == h_mqa.size, (name, "MQA H is not bitwise the multi-head plan's H on head-replicated weights",
                                      equal_bits, h_mqa.size, equiv_gap)
    std_gap = float(np.max(np.abs(np.asarray(EAGER[std_name]["eager"]["H"]).astype(np.float64) - h_mqa.astype(np.float64))))
    assert std_gap > 1e-2, (name, "the equivalence pin cannot tell head-distinct weights apart", std_gap)
    print(f"{name}: one scan record, 2 steps; K[s, k], V[s, k] head-free (W_K, W_V {fin['W_K'].shape} = [l, k, m]), every other "
          f"input bitwise the standard fixture's, layer-2 slices NaN and H finite; H layers 0, 1, 2 == numpy MQA model on "
          f"Lean, eager and jit; differs from the numpy multi-head model by {mh_gap:.3f}; the two query heads' attention "
          f"differs by {', '.join(f'{g:.3f}' for g in head_gaps)} (layers 0, 1); eager H == the STANDARD plan on "
          f"head-replicated weights bitwise ({equal_bits}/{h_mqa.size} entries, max abs {equiv_gap:.1e}), and the standard "
          f"plan on its head-distinct weights differs by {std_gap:.3f}; per-output measured difference vs numpy and vs Lean:")
    print_np_stats(name)
    sc_err = NUM_STATS[(name, "H")][0]
    print(f"  H headroom to MODEL_TOL: {MODEL_TOL[_DT] / max(sc_err, 1e-300):.1f}x (observed {sc_err:.3e} of {MODEL_TOL[_DT]:.0e})")
    for n in sorted(n for fx_, n in OUT_STATS if fx_ == name):
        rel, ab, ex, tot = OUT_STATS[(name, n)]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")


def gqa_fixture_pins(by: dict, sfx: str) -> None:
    """Pins of the three grouped-query scan fixtures (G key/value groups, R query heads per group, query head
    `h = R * g + r` reads group `g`): `transformer_gqa` (flat head axis, affine read `Q[q, R * g + r, k]`),
    `transformer_gqa_split` (head axis split into `(g, r)`, no index arithmetic) and `transformer_gqa_mha` (the standard
    multi-head statements on key/value weights replicated per head). The reference is `np_transformer` on multi-head inputs
    whose key/value weights are `W_K[:, h // R]`: the division is the English definition of the map, exactly what the
    language lacks. Value pin on Lean, eager and jit; non-vacuity against three wrong models; flat == split on the eager
    and jit runtimes; flat == multi-head plan on weights replicated HERE in Python (no Lean value involved)."""
    names = {"flat": f"transformer_gqa{sfx}", "split": f"transformer_gqa_split{sfx}", "mha": f"transformer_gqa_mha{sfx}"}
    fxs = {k: by[n] for k, n in names.items()}
    ref = {n: lean_array(e) for n, e in by[f"transformer_window{sfx}"]["inputs"].items()}  # the mask fixtures' inputs
    fins = {k: {n: lean_array(e) for n, e in fx["inputs"].items()} for k, fx in fxs.items()}
    for k, fx in fxs.items():
        scans = [n for n in fx["plan"]["nodes"] if n.get("kind") == "scan"]
        assert len(fx["plan"]["nodes"]) == 1 and len(scans) == 1 and scans[0]["step_count"] == 2, (names[k], fx["plan"]["nodes"])
        assert sorted(fins[k]) == sorted(ref), (names[k], sorted(fins[k]), sorted(ref))
    fin = fins["flat"]
    n_g, n_k, n_m = fin["W_K"].shape[1], fin["W_K"].shape[2], fin["W_K"].shape[3]
    n_h, n_pos = fin["W_Q"].shape[1], fin["X"].shape[0]
    assert n_h % n_g == 0, (n_h, n_g)
    R = n_h // n_g
    # g, r, k and q (= s) are pairwise distinct, so no axis-order bug can hide behind equal extents on S, K, Q, AttnOut or W_O
    assert len({n_g, R, n_k, n_pos}) == 4 and n_pos == 5 and n_m == 4, (n_g, R, n_k, n_pos, n_m)
    # shapes: the same bytes in three layouts (flat head, split head, replicated K and V)
    assert fin["W_Q"].shape == (3, n_h, n_k, n_m) and fin["W_O"].shape == (3, n_m, n_h, n_k), (fin["W_Q"].shape, fin["W_O"].shape)
    assert fin["W_K"].shape == fin["W_V"].shape == (3, n_g, n_k, n_m)
    sp = fins["split"]
    assert sp["W_Q"].shape == (3, n_g, R, n_k, n_m) and sp["W_O"].shape == (3, n_m, n_g, R, n_k), (sp["W_Q"].shape, sp["W_O"].shape)
    assert sp["W_K"].shape == sp["W_V"].shape == (3, n_g, n_k, n_m)
    mh = fins["mha"]
    assert mh["W_Q"].shape == fin["W_Q"].shape and mh["W_K"].shape == mh["W_V"].shape == (3, n_h, n_k, n_m), mh["W_K"].shape
    # every input is the mask fixtures' bit for bit, except Sc and the four head-specific weights; the two grouped programs
    # read the very same arrays (`h = R * g + r` makes [g, r, k, m] and [h, k, m] one storage order); the multi-head
    # program's key/value weights are the grouped ones replicated per head (`np.repeat`, i.e. `W_K[:, h // R]`, built here)
    head_weights = ("W_Q", "W_K", "W_V", "W_O", "Sc")
    for k in fins:
        for n in ref:
            if n not in head_weights:
                assert np.array_equal(bits(fins[k][n]), bits(ref[n])), (names[k], "input differs from the mask fixtures'", n)
    for n in ("W_Q", "W_K", "W_V", "W_O", "Sc"):
        assert np.array_equal(bits(fin[n]).ravel(), bits(sp[n]).ravel()), (n, "flat and split programs read different data")
    for n in ("W_Q", "W_O", "Sc"):
        assert np.array_equal(bits(fin[n]), bits(mh[n])), (n, "multi-head program reads different data")
    for n in ("W_K", "W_V"):
        assert np.array_equal(bits(mh[n]), bits(np.repeat(fin[n], R, axis=1))), (n, "replication is not W[:, h // R]")
    # layer-2 slices are NaN in every weight stack (a step reading past layer 1 would turn every output NaN); layers 0, 1 differ
    for k in fins:
        for w in ("W_Q", "W_K", "W_V", "W_O", "W_in", "W_out", "G1", "G2"):
            a = fins[k][w]
            assert a.shape[0] == 3 and np.all(np.isnan(a[2])) and np.all(np.isfinite(a[:2])), (names[k], w)
            assert not np.array_equal(a[0], a[1]), (names[k], w)
    # Sc is 1 / sqrt(k) for the head width of W_Q itself
    assert fin["Sc"].shape == () and np.isclose(float(fin["Sc"]), 1.0 / np.sqrt(fin["W_Q"].shape[2]),
                                                 rtol=1e-6 if _DT == "float32" else 1e-14), fin["Sc"]
    group = [h // R for h in range(n_h)]  # the English definition of the head-to-group map
    gh = dict(fin, W_K=fin["W_K"][:, group], W_V=fin["W_V"][:, group])
    layers = np_transformer(gh)
    want = np_state(gh, layers)

    def gap(other):  # max |H_gqa - H_other| over the state
        return float(np.max(np.abs(want - np_state(other, np_transformer(other)))))

    # non-vacuity: GQA is none of (a) multi-head with distinct K/V per head (generated here from a different formula),
    # (b) one shared group (multi-query), (c) the wrong group map h % G (= the transposed head map `G * r + g` of mutant A)
    distinct = np.array([0.6 * np.sin(5.0 + 1.7 * i) for i in range(3 * n_h * n_k * n_m)]).reshape(3, n_h, n_k, n_m)
    gaps = {"distinct K/V per head": gap(dict(fin, W_K=distinct, W_V=distinct[::-1])),
            "one shared group": gap(dict(fin, W_K=fin["W_K"][:, [0] * n_h], W_V=fin["W_V"][:, [0] * n_h])),
            "wrong map h % G": gap(dict(fin, W_K=fin["W_K"][:, [h % n_g for h in range(n_h)]],
                                        W_V=fin["W_V"][:, [h % n_g for h in range(n_h)]]))}
    for what, g in gaps.items():
        assert g > 1e-2, (names["flat"], "GQA is indistinguishable from", what, g)
    # the R heads of one group attend differently from each other, and the groups differ, in layers 0 and 1
    r_gaps, g_gaps = [], []
    for o in layers:
        r_gaps.append(min(float(np.max(np.abs(o["S"][R * g + r] - o["S"][R * g + r2])))
                          for g in range(n_g) for r in range(R) for r2 in range(r + 1, R)))
        g_gaps.append(min(float(np.max(np.abs(o["S"][R * g] - o["S"][R * g2]))) for g in range(n_g) for g2 in range(g + 1, n_g)))
    assert all(x > 1e-2 for x in r_gaps + g_gaps), (names["flat"], "heads or groups attend alike", r_gaps, g_gaps)
    # value pin: exactly the state is exported, finite, on Lean, eager and jit, for all three programs
    for k, name in names.items():
        views = {"lean": {n: lean_array(e) for n, e in fxs[k]["expected"].items()},
                 "eager": {n: np.asarray(v) for n, v in EAGER[name]["eager"].items()},
                 "jit": {n: np.asarray(v) for n, v in EAGER[name]["jit"].items()}}
        for who, outs in views.items():
            assert sorted(outs) == ["H"] and np.all(np.isfinite(outs["H"])), (name, who, sorted(outs))
            assert outs["H"].shape == (n_pos, n_m, 3), (name, who, outs["H"].shape)
            check_np(name, who, "H", outs["H"], want)
    # flat read == split heads: the affine read `Q[q, R * g + r, k]` and the axis split are the same computation
    h_of = {k: {"lean": lean_array(fxs[k]["expected"]["H"]), "eager": np.asarray(EAGER[n]["eager"]["H"]),
                "jit": np.asarray(EAGER[n]["jit"]["H"])} for k, n in names.items()}
    flat_split = {v: int(np.sum(bits(h_of["flat"][v]) == bits(h_of["split"][v]))) for v in ("lean", "eager", "jit")}
    total = h_of["flat"]["eager"].size
    for v in ("eager", "jit"):
        assert flat_split[v] == total, (names["flat"], names["split"], "flat and split heads differ on", v, flat_split[v], total)
    # equivalence: the flat plan == the standard multi-head plan run on key/value weights replicated HERE (eager runtime
    # both sides); the multi-head plan on the head-DISTINCT weights does not agree (non-vacuity)
    run_mh = rt.run_named(fxs["mha"]["plan"], {n: jnp.asarray(a) for n, a in dict(mh, W_K=np.repeat(fin["W_K"], R, axis=1),
                                                                                   W_V=np.repeat(fin["W_V"], R, axis=1)).items()}, JDT)
    h_flat, h_mh = h_of["flat"]["eager"], np.asarray(run_mh["H"])
    assert h_flat.dtype == h_mh.dtype == NDT and h_flat.shape == h_mh.shape, (h_flat.dtype, h_mh.dtype)
    equal_bits = int(np.sum(bits(h_flat) == bits(h_mh)))
    equiv_gap = float(np.max(np.abs(h_flat.astype(np.float64) - h_mh.astype(np.float64))))
    assert equal_bits == h_flat.size, (names["flat"], "GQA H is not bitwise the multi-head plan's H on replicated weights",
                                       equal_bits, h_flat.size, equiv_gap)
    run_dist = rt.run_named(fxs["mha"]["plan"], {n: jnp.asarray(a) for n, a in dict(
        mh, W_K=distinct.astype(NDT), W_V=distinct[::-1].astype(NDT)).items()}, JDT)
    dist_gap = float(np.max(np.abs(np.asarray(run_dist["H"]).astype(np.float64) - h_flat.astype(np.float64))))
    assert dist_gap > 1e-2, (names["flat"], "the equivalence pin cannot tell head-distinct weights apart", dist_gap)
    print(f"gqa{sfx}: G={n_g} groups x R={R} heads (h={n_h}), k={n_k}, q=s={n_pos}: distinct extents; three programs, each ONE scan "
          f"record with 2 steps; inputs bitwise the mask fixtures' except Sc and the head weights; flat and split read the same "
          f"bytes, mha K/V = W[:, h // R]; layer-2 slices NaN, H finite; H layers 0, 1, 2 == numpy model (K/V = W[:, h // R]) on "
          f"Lean, eager and jit for all three; the numpy GQA H differs from "
          f"{', '.join(f'{w} by {g:.3f}' for w, g in gaps.items())}; heads of one group attend differently (min gap per layer "
          f"{', '.join(f'{x:.3f}' for x in r_gaps)}), groups differ (min gap {', '.join(f'{x:.3f}' for x in g_gaps)}); "
          f"flat == split H bitwise on eager {flat_split['eager']}/{total}, jit {flat_split['jit']}/{total}, "
          f"Lean {flat_split['lean']}/{total}; eager flat H == multi-head plan on replicated weights bitwise "
          f"({equal_bits}/{h_flat.size}, max abs {equiv_gap:.1e}); multi-head plan on distinct weights differs by {dist_gap:.3f}")
    for k, name in names.items():
        print(f"{name}: per-output measured difference vs numpy and vs Lean:")
        print_np_stats(name)
        sc_err = NUM_STATS[(name, "H")][0]
        print(f"  H headroom to MODEL_TOL: {MODEL_TOL[_DT] / max(sc_err, 1e-300):.1f}x (observed {sc_err:.3e} of {MODEL_TOL[_DT]:.0e})")
        for n in sorted(n for fx_, n in OUT_STATS if fx_ == name):
            rel, ab, ex, tot = OUT_STATS[(name, n)]
            print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")


def grad_fixture_pins(by: dict, sfx: str) -> None:
    """Gradient pins of the standard two-layer scan (`transformer_scan`): `jax.grad` of the scalar loss
    `L = sum(C * H[:, :, 2])` (a fixed, distinct-entried cotangent `C`) through the emitted `lax.scan` plan, over EVERY float input,
    against (a) the same loss through the hand-copied unrolled plan (`transformer_unrolled`, stacked per layer), (b) the autodiff of a
    pure-JAX transformer written from the definition (no plan, no scan, carrier dtype) and (c) central finite differences of the
    float64 numpy model (`np_transformer`) along random directions (no autodiff on the reference side at all). The layer-2 weight
    slices are NaN in the inputs and never read, so their gradient must be exactly zero and finite."""
    scan, unr = by["transformer_scan" + sfx], by["transformer_unrolled" + sfx]
    sin = {n: lean_array(e) for n, e in scan["inputs"].items()}
    uin = {n: lean_array(e) for n, e in unr["inputs"].items()}
    stacked = ("W_Q", "W_K", "W_V", "W_O", "W_in", "W_out", "G1", "G2")
    C = np.sin(1.0 + np.arange(12)).reshape(3, 4).astype(NDT)

    def loss_scan(inp):
        return jnp.sum(C * rt.run_named(scan["plan"], inp, JDT)["H"][:, :, 2])

    def loss_unrolled(inp):
        return jnp.sum(C * rt.run_named(unr["plan"], inp, JDT)["H2"])

    def loss_hand(inp):
        h, tril = inp["X"], jnp.tril(jnp.ones((3, 3), dtype=bool))
        for l in range(2):
            n1 = h / jnp.sqrt(jnp.einsum("qm,qm,m->q", h, h, inp["Inv"]) + inp["Eps"])[:, None] * inp["G1"][l]
            q = jnp.einsum("hkm,qm->qhk", inp["W_Q"][l], n1)
            k = jnp.einsum("hkm,sm->shk", inp["W_K"][l], n1)
            v = jnp.einsum("hkm,sm->shk", inp["W_V"][l], n1)
            lg = jnp.einsum("qhk,shk->hqs", q, k) * inp["Sc"]
            s = jax.nn.softmax(jnp.where(tril[None], lg, -jnp.inf), axis=-1)
            r1 = h + jnp.einsum("mhk,qhk->qm", inp["W_O"][l], jnp.einsum("hqs,shk->qhk", s, v))
            n2 = r1 / jnp.sqrt(jnp.einsum("qm,qm,m->q", r1, r1, inp["Inv"]) + inp["Eps"])[:, None] * inp["G2"][l]
            x = jnp.einsum("dm,qm->qd", inp["W_in"][l], n2)
            f = 0.5 * x * (1.0 + jnp.tanh(0.7978845608028654 * (x + 0.044715 * x ** 3)))
            h = r1 + jnp.einsum("md,qd->qm", inp["W_out"][l], f)
        return jnp.sum(C * h)

    def scaled(a, b):
        a, b = np.asarray(a, dtype=np.float64), np.asarray(b, dtype=np.float64)
        return float(np.max(np.abs(a - b) / np.maximum(1.0, np.abs(b))))

    jin = {n: jnp.asarray(a) for n, a in sin.items()}
    grads = {"eager": jax.grad(loss_scan)(jin), "jit": jax.jit(jax.grad(loss_scan))(jin)}
    g_hand = jax.grad(loss_hand)(jin)
    g_unr = jax.grad(loss_unrolled)({n: jnp.asarray(a) for n, a in uin.items()})
    ref_err, unr_err = {}, {}
    for who, g in grads.items():
        assert sorted(g) == sorted(sin), (who, sorted(g))
        assert all(np.all(np.isfinite(np.asarray(v))) and np.asarray(v).dtype == NDT for v in g.values()), (who, "gradient not finite")
        for w in stacked:
            gw = np.asarray(g[w])
            # the NaN layer-2 slice is never read, so it gets exactly zero gradient; layers 0 and 1 carry real gradient
            assert np.all(gw[2] == 0), ("layer-2 weight slice received gradient", who, w)
            assert all(float(np.max(np.abs(gw[l]))) > 1e-3 for l in (0, 1)), ("trivial gradient", who, w)
            # the two layers' gradients differ: a gradient that mixed layers up would not be seen otherwise
            assert float(np.max(np.abs(gw[0] - gw[1]))) > 1e-2, ("layers 0 and 1 have alike gradients", who, w)
        for n in sin:
            e_ref = scaled(g[n], g_hand[n])
            assert e_ref < GRAD_TOL[_DT], ("gradient pin: scan vs pure-JAX model", who, n, e_ref)
            ref_err[n] = max(ref_err.get(n, 0.0), e_ref)
            if n in stacked:
                e_unr = scaled(np.asarray(g[n])[:2], np.stack([np.asarray(g_unr[f"{n}1"]), np.asarray(g_unr[f"{n}2"])]))
            else:
                e_unr = scaled(g[n], g_unr[n])
            assert e_unr < GRAD_TOL[_DT], ("gradient pin: scan vs unrolled plan", who, n, e_unr)
            unr_err[n] = max(unr_err.get(n, 0.0), e_unr)
    # (c) directional derivatives against central differences of the independent numpy model; 3 fixed random directions
    # over all inputs (zero on the NaN layer-2 slices, which the model never reads), `|dot| > 1e-2` so none is trivial
    base = {n: a.astype(np.float64) for n, a in sin.items()}
    rng = np.random.default_rng(7)
    fd_err, dots = 0.0, []
    for _ in range(3):
        d = {n: rng.standard_normal(a.shape) for n, a in base.items()}
        for w in stacked:
            d[w][2] = 0.0
        eps = 1e-6
        loss = lambda inp: float(np.sum(C.astype(np.float64) * np_state(inp, np_transformer(inp))[:, :, 2]))
        fd = (loss({n: base[n] + eps * d[n] for n in base}) - loss({n: base[n] - eps * d[n] for n in base})) / (2 * eps)
        for who, g in grads.items():
            dot = float(sum(np.sum(np.asarray(g[n], dtype=np.float64) * d[n]) for n in base))
            assert abs(dot) > 1e-2, ("finite-difference direction is trivial", dot)
            fd_err = max(fd_err, abs(fd - dot) / max(1.0, abs(dot)))
        dots.append(dot)
    assert fd_err < GRAD_FD_TOL[_DT], ("gradient pin: directional derivative vs finite differences of the numpy model", fd_err)
    print(f"gradients: jax.grad of sum(C * H[:, :, 2]) through the transformer_scan plan (eager and jit), all {len(sin)} inputs "
          f"finite, layer-2 weight slices exactly zero, layers 0 and 1 non-trivial and distinct; scan == hand-copied unrolled plan "
          f"(max scaled {max(unr_err.values()):.3e}), == pure-JAX model autodiff (max scaled {max(ref_err.values()):.3e}, tol "
          f"{GRAD_TOL[_DT]:.0e}), directional derivatives == central differences of the float64 numpy model (3 directions, "
          f"|dot| {min(abs(x) for x in dots):.2f} to {max(abs(x) for x in dots):.2f}, max scaled {fd_err:.3e}, tol {GRAD_FD_TOL[_DT]:.0e}); "
          f"per-input scaled error vs the pure-JAX model: " + ", ".join(f"{n} {ref_err[n]:.1e}" for n in sorted(ref_err)))
    print(f"  headroom to GRAD_TOL: {GRAD_TOL[_DT] / max(max(ref_err.values()), 1e-300):.1f}x (vs pure-JAX model), "
          f"{GRAD_TOL[_DT] / max(max(unr_err.values()), 1e-300):.1f}x (vs unrolled); to GRAD_FD_TOL: {GRAD_FD_TOL[_DT] / max(fd_err, 1e-300):.1f}x")


# Scan fixtures that get gradient pins beyond the standard `transformer_scan`: name stem -> predicate-mask kind (None = causal).
GRAD_FIXTURES = {"mqa": None, "window": "window", "strict": "strict", "sink": "sink",
                 "gqa": None, "gqa_split": None, "gqa_mha": None}
# Query row of the receptive-field gradient pin per mask: its two-layer backward reach leaves some position outside it.
GRAD_ROW = {"window": 4, "strict": 1, "sink": 4}


def canon_heads(inp: dict, xp) -> dict:
    """Multi-head view of any scan fixture's inputs (`xp` is `np` or `jnp`, so the same view feeds the numpy and the autodiff model):
    split heads `W_Q[l, g, r, k, m]`, `W_O[l, m, g, r, k]` are flattened to `h = R * g + r`; head-free (`W_K[l, k, m]`) or grouped
    (`W_K[l, g, k, m]`) key and value weights are expanded to one slice per query head (`h // R`, written in Python)."""
    f = dict(inp)
    if f["W_Q"].ndim == 5:
        _, n_g, n_r, n_k, n_m = f["W_Q"].shape
        f["W_Q"] = xp.reshape(f["W_Q"], (3, n_g * n_r, n_k, n_m))
        f["W_O"] = xp.reshape(f["W_O"], (3, n_m, n_g * n_r, n_k))
    n_h = f["W_Q"].shape[1]
    for w in ("W_K", "W_V"):
        if f[w].ndim == 3:
            f[w] = xp.broadcast_to(f[w][:, None], (3, n_h) + tuple(f[w].shape[1:]))
        elif f[w].shape[1] != n_h:
            f[w] = f[w][:, [h // (n_h // f[w].shape[1]) for h in range(n_h)]]
    return f


def fixture_grad_pins(by: dict, sfx: str) -> None:
    """Gradient pins of the other scan fixtures (`transformer_mqa`, the three mask fixtures, the three GQA programs): `jax.grad` of
    `L = sum(C * H[:, :, 2])` through the emitted plan, over EVERY float input, eager and jit, against (b) the autodiff of a pure-JAX
    transformer written from the definition (heads canonicalised by `canon_heads`, mask `allow[q][s]` from its English definition;
    no plan, no scan) and (c) central finite differences of the float64 numpy model along random directions. Layer-2 weight slices
    (NaN, never read) get exactly zero gradient. Mask fixtures: a loss on ONE query row has exactly zero gradient at every position
    outside that row's two-layer backward reach and a real one inside (the mask in the backward pass). GQA: the three programs'
    gradients agree (flat == split on the same bytes; flat == multi-head with the replicated key/value gradients summed per group)."""
    stacked = ("W_Q", "W_K", "W_V", "W_O", "W_in", "W_out", "G1", "G2")

    def scaled(a, b):
        a, b = np.asarray(a, dtype=np.float64), np.asarray(b, dtype=np.float64)
        return float(np.max(np.abs(a - b) / np.maximum(1.0, np.abs(b))))

    def hand_loss(inp, C, allow):
        c = canon_heads(inp, jnp)
        am = jnp.asarray(allow)[None]
        h = c["X"]
        for l in range(2):
            n1 = h / jnp.sqrt(jnp.einsum("qm,qm,m->q", h, h, c["Inv"]) + c["Eps"])[:, None] * c["G1"][l]
            q = jnp.einsum("hkm,qm->qhk", c["W_Q"][l], n1)
            k = jnp.einsum("hkm,sm->shk", c["W_K"][l], n1)
            v = jnp.einsum("hkm,sm->shk", c["W_V"][l], n1)
            lg = jnp.einsum("qhk,shk->hqs", q, k) * c["Sc"]
            mx = jnp.max(jnp.where(am, lg, -1e30), axis=-1, keepdims=True)
            e = jnp.where(am, jnp.exp(jnp.where(am, lg - mx, 0.0)), 0.0)  # an all-masked row is exactly zero
            den = jnp.sum(e, axis=-1, keepdims=True)
            s = e / jnp.where(den == 0, 1.0, den)
            r1 = h + jnp.einsum("mhk,qhk->qm", c["W_O"][l], jnp.einsum("hqs,shk->qhk", s, v))
            n2 = r1 / jnp.sqrt(jnp.einsum("qm,qm,m->q", r1, r1, c["Inv"]) + c["Eps"])[:, None] * c["G2"][l]
            x = jnp.einsum("dm,qm->qd", c["W_in"][l], n2)
            f = 0.5 * x * (1.0 + jnp.tanh(0.7978845608028654 * (x + 0.044715 * x ** 3)))
            h = r1 + jnp.einsum("md,qd->qm", c["W_out"][l], f)
        return jnp.sum(C * h)

    all_grads: dict[str, dict] = {}
    lines = []
    for stem, kind in GRAD_FIXTURES.items():
        name = f"transformer_{stem}{sfx}"
        fx = by[name]
        sin = {n: lean_array(e) for n, e in fx["inputs"].items()}
        n_pos = sin["X"].shape[0]
        allow = mask_allow(kind, n_pos) if kind else np.tril(np.ones((n_pos, n_pos), dtype=bool))
        C = np.sin(1.0 + np.arange(n_pos * 4)).reshape(n_pos, 4).astype(NDT)
        jin = {n: jnp.asarray(a) for n, a in sin.items()}

        def loss_plan(inp, C=C, fx=fx):
            return jnp.sum(C * rt.run_named(fx["plan"], inp, JDT)["H"][:, :, 2])

        grads = {"eager": jax.grad(loss_plan)(jin), "jit": jax.jit(jax.grad(loss_plan))(jin)}
        g_hand = jax.grad(lambda inp: hand_loss(inp, C, allow))(jin)
        all_grads[stem] = grads["eager"]
        err = {}
        for who, g in grads.items():
            assert sorted(g) == sorted(sin), (name, who, sorted(g))
            assert all(np.all(np.isfinite(np.asarray(v))) and np.asarray(v).dtype == NDT for v in g.values()), (name, who, "gradient not finite")
            for w in stacked:
                gw = np.asarray(g[w])
                assert np.all(gw[2] == 0), (name, "layer-2 weight slice received gradient", who, w)
                assert all(float(np.max(np.abs(gw[l]))) > 1e-3 for l in (0, 1)), (name, "trivial gradient", who, w)
                assert float(np.max(np.abs(gw[0] - gw[1]))) > 1e-2, (name, "layers 0 and 1 have alike gradients", who, w)
            for n in sin:
                e_ref = scaled(g[n], g_hand[n])
                assert e_ref < GRAD_TOL[_DT], (f"gradient pin: {name} vs pure-JAX model", who, n, e_ref)
                err[n] = max(err.get(n, 0.0), e_ref)
        # tolerance self-test: a 1e-3 relative perturbation of a real gradient is rejected
        gq = np.asarray(grads["eager"]["W_Q"])
        assert scaled(gq * NDT(1.001), gq) >= GRAD_TOL[_DT], (name, "gradient tolerance accepts a 1e-3 perturbation: vacuous")
        # (c) directional derivatives against central differences of the numpy model (3 fixed directions, zero on the NaN slices)
        base = {n: a.astype(np.float64) for n, a in sin.items()}
        rng = np.random.default_rng(7)
        fd_err, dots = 0.0, []
        loss_np = lambda inp: float(np.sum(C.astype(np.float64) * np_state(
            canon_heads(inp, np), np_transformer(canon_heads(inp, np), allow=allow))[:, :, 2]))
        for _ in range(3):
            d = {n: rng.standard_normal(a.shape) for n, a in base.items()}
            for w in stacked:
                d[w][2] = 0.0
            eps = 1e-6
            fd = (loss_np({n: base[n] + eps * d[n] for n in base}) - loss_np({n: base[n] - eps * d[n] for n in base})) / (2 * eps)
            for who, g in grads.items():
                dot = float(sum(np.sum(np.asarray(g[n], dtype=np.float64) * d[n]) for n in base))
                assert abs(dot) > 1e-2, (name, "finite-difference direction is trivial", dot)
                fd_err = max(fd_err, abs(fd - dot) / max(1.0, abs(dot)))
            dots.append(dot)
        assert fd_err < GRAD_FD_TOL[_DT], (f"gradient pin: {name} directional derivative vs finite differences of the numpy model", fd_err)
        extra = ""
        if kind:
            # receptive field in the backward pass: a loss on ONE query row; positions outside that row's two-layer reach get
            # EXACTLY zero gradient (the masked entries contribute nothing), positions inside get a real one
            r = GRAD_ROW[kind]
            reach = {p for p in range(n_pos) if r in reachable_rows(allow, p, 2)}
            unreach = sorted(set(range(n_pos)) - reach)
            assert r in reach and unreach and len(reach) > 1, (name, r, sorted(reach), unreach)
            Cr = np.zeros((n_pos, 4), dtype=NDT)
            Cr[r] = np.sin(1.0 + np.arange(4)).astype(NDT)
            row_plan = lambda inp: jnp.sum(Cr * rt.run_named(fx["plan"], inp, JDT)["H"][:, :, 2])
            row_hand = jax.grad(lambda inp: hand_loss(inp, Cr, allow))(jin)
            for who, gr in (("eager", jax.grad(row_plan)(jin)), ("jit", jax.jit(jax.grad(row_plan))(jin))):
                gx = np.asarray(gr["X"])
                assert np.all(gx[unreach] == 0), (name, "gradient reaches a position outside the backward receptive field", who, r, unreach)
                assert all(float(np.max(np.abs(gx[p]))) > 1e-3 for p in sorted(reach)), (name, "no gradient inside the receptive field", who, r, sorted(reach))
                for n in sin:
                    assert scaled(gr[n], row_hand[n]) < GRAD_TOL[_DT], (f"gradient pin: {name} row loss vs pure-JAX model", who, n)
            extra = f"; row-{r} loss: X rows {unreach} exactly zero gradient, rows {sorted(reach)} real"
        lines.append(f"  {name}: vs pure-JAX model max scaled {max(err.values()):.3e} (headroom {GRAD_TOL[_DT] / max(max(err.values()), 1e-300):.1f}x), "
                     f"finite differences {fd_err:.3e} (|dot| {min(abs(x) for x in dots):.2f} to {max(abs(x) for x in dots):.2f}, "
                     f"headroom {GRAD_FD_TOL[_DT] / max(fd_err, 1e-300):.1f}x){extra}")
    # GQA: the three programs differentiate to the same thing
    gf, gs, gm = all_grads["gqa"], all_grads["gqa_split"], all_grads["gqa_mha"]
    n_g = gf["W_K"].shape[1]
    n_h = gm["W_K"].shape[1]
    R = n_h // n_g
    assert gf["W_Q"].shape == (3, n_h) + gf["W_Q"].shape[2:] and gs["W_Q"].shape == (3, n_g, R) + gf["W_Q"].shape[2:], (gf["W_Q"].shape, gs["W_Q"].shape)
    same_bits = {}
    for n in gf:
        assert scaled(np.asarray(gf[n]).reshape(-1), np.asarray(gs[n]).reshape(-1)) < GRAD_TOL[_DT], ("gradient pin: flat vs split heads", n)
        same_bits[n] = bool(np.array_equal(bits(np.asarray(gf[n]).reshape(-1)), bits(np.asarray(gs[n]).reshape(-1))))
        want = gf[n]
        got = gm[n]
        if n in ("W_K", "W_V"):  # chain rule through the replication: the replicas' gradients sum per group
            got = np.asarray(gm[n]).reshape((3, n_g, R) + tuple(gm[n].shape[2:])).sum(axis=2)
        assert scaled(got, want) < GRAD_TOL[_DT], ("gradient pin: flat vs multi-head (replicated K/V summed per group)", n)
    # non-vacuity of the group fold: replicas of one group receive DIFFERENT gradients (so a sum is not a copy) and groups differ
    rep_gap = min(float(np.max(np.abs(np.asarray(gm[w])[:, R * g] - np.asarray(gm[w])[:, R * g + 1]))) for w in ("W_K", "W_V") for g in range(n_g))
    grp_gap = min(float(np.max(np.abs(np.asarray(gf[w])[:, 0] - np.asarray(gf[w])[:, g]))) for w in ("W_K", "W_V") for g in range(1, n_g))
    assert rep_gap > 1e-2 and grp_gap > 1e-2, ("GQA gradient fold is vacuous", rep_gap, grp_gap)
    print(f"gradients of the other scan fixtures ({', '.join(f'transformer_{s}' for s in GRAD_FIXTURES)}; eager and jit, every float input): "
          f"finite, layer-2 weight slices exactly zero, layers 0 and 1 non-trivial and distinct; == autodiff of a pure-JAX model "
          f"(tol {GRAD_TOL[_DT]:.0e}) and directional derivatives == central differences of the float64 numpy model (tol {GRAD_FD_TOL[_DT]:.0e}); "
          f"GQA flat == split heads (bitwise inputs: {sum(same_bits.values())}/{len(same_bits)}) and == multi-head with replicated K/V "
          f"gradients summed per group (replicas of a group differ by {rep_gap:.3f}, groups by {grp_gap:.3f}):")
    for line in lines:
        print(line)


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

    # PREDICATE MASKS inside the layer scan (window, strict, sink; q = s = 5): see `mask_fixture_pins`.
    for mk in MASK_FIXTURES:
        mask_fixture_pins(by, mk, sfx)

    # MULTI-QUERY ATTENTION inside the layer scan (head-free K and V): see `mqa_fixture_pins`.
    mqa_fixture_pins(by, sfx)

    # GROUPED-QUERY ATTENTION inside the layer scan (flat head axis, split heads, multi-head on replicated weights):
    # see `gqa_fixture_pins`.
    gqa_fixture_pins(by, sfx)

    # GRADIENTS through the emitted scan (`jax.grad`): see `grad_fixture_pins`.
    grad_fixture_pins(by, sfx)

    # GRADIENTS through the other scan fixtures (MQA, masks, GQA): see `fixture_grad_pins`.
    fixture_grad_pins(by, sfx)

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
