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
                        "transformer_gqa_mha", "transformer_gqa_mha32",
                        "transformer_cross", "transformer_cross32", "transformer_cross_hoisted", "transformer_cross_hoisted32",
                        "transformer_cross_wide", "transformer_cross_wide32",
                        "conv1d_cnn", "conv1d_cnn32", "conv1d_causal", "conv1d_causal32", "vit_patch", "vit_patch32",
                        "rnn_gru", "rnn_gru32", "rnn_lstm", "rnn_lstm32", "rnn_bi", "rnn_bi32", "rnn_stack", "rnn_stack32"}
# Exported pre-scan tables stacked over the layer axis (`Kc[t, h, j, l]`, `Vc[t, h, j, l]` of the cross-attention fixture): built from the NaN
# layer-2 weight slice, so their layer-2 slice is NaN by construction. `require_close` and `record_output` compare layers 0 and 1 only and
# require that EXACTLY layer 2 is NaN (in Lean, eager and jit alike); every other output must be finite.
NAN_LAYER_OUTPUTS = {(f"transformer_cross{kind}{sfx}", n) for kind in ("", "_wide") for sfx in ("", "32") for n in ("Kc", "Vc")}
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


def np_cross_transformer(inp: dict, n_layers: int = 2, cross: bool = True, memory=None, hoisted: bool = False) -> list:
    """Independent float64 numpy model of one decoder layer, from the inputs only, per layer: causal self-attention exactly as
    `np_transformer` (N1 = RMSNorm(H) * G1[l], Q, K, V from N1, softmax_s(Q.K * Sc) over s <= q, R1 = H + W_O . (S.V)), then the
    CROSS-ATTENTION block (when `cross`): Nc = RMSNorm(R1) * Gc[l], Qc = W_Qc[l] . Nc, keys and values from an EXTERNAL memory
    `Mem[t, m]` (Kc = W_Kc[l] . Mem, Vc = W_Vc[l] . Mem; t != q), Sx = UNMASKED softmax_t(Qc.Kc * Scx), R2 = R1 + W_Oc[l] . (Sx.Vc);
    then the MLP on R2 (N2 = RMSNorm(R2) * G2[l], H' = R2 + W_out . gelu(W_in . N2)), msq(x) = sum_m x^2 * Inv[m].
    `memory` replaces `Mem` as the source of the cross keys and values (a wrong-source model; the string "state" takes the layer's own
    normalised state `Na` instead, per layer); `hoisted` takes the cross keys and values
    from the weights SUMMED over every layer, `einsum("lhjm,tm->thj", W_Kc, Mem)` (the pre-scan table of the naive program).
    Returns one dict per layer (the self-attention and MLP entries of `np_transformer`, plus Nc, Qc, Kc, Vc, Sx, Ac, Ax, R2)."""
    f = {k: np.asarray(v, dtype=np.float64) for k, v in inp.items()}
    h, layers = f["X"], []
    tril = np.tril(np.ones((h.shape[0], h.shape[0]), dtype=bool))
    mem = f["Mem"] if memory is None or isinstance(memory, str) else np.asarray(memory, dtype=np.float64)
    for l in range(n_layers):
        o = {}
        o["Ssa"] = np.einsum("qm,qm,m->q", h, h, f["Inv"])
        o["Na"] = h / np.sqrt(o["Ssa"] + f["Eps"])[:, None] * f["G1"][l]
        o["Q"] = np.einsum("hkm,qm->qhk", f["W_Q"][l], o["Na"])
        o["K"] = np.einsum("hkm,sm->shk", f["W_K"][l], o["Na"])
        o["V"] = np.einsum("hkm,sm->shk", f["W_V"][l], o["Na"])
        lg = np.einsum("qhk,shk->hqs", o["Q"], o["K"]) * f["Sc"]
        o["S"] = np_softmax_last(np.where(tril[None], lg, -np.inf))
        o["Ra"] = h + np.einsum("mhk,qhk->qm", f["W_O"][l], np.einsum("hqs,shk->qhk", o["S"], o["V"]))
        r2 = o["Ra"]
        if cross:
            o["Nc"] = o["Ra"] / np.sqrt(np.einsum("qm,qm,m->q", o["Ra"], o["Ra"], f["Inv"]) + f["Eps"])[:, None] * f["Gc"][l]
            o["Qc"] = np.einsum("hjm,qm->qhj", f["W_Qc"][l], o["Nc"])
            src = o["Na"] if memory == "state" else mem
            if hoisted:
                o["Kc"] = np.einsum("lhjm,tm->thj", f["W_Kc"], src)
                o["Vc"] = np.einsum("lhjm,tm->thj", f["W_Vc"], src)
            else:
                o["Kc"] = np.einsum("hjm,tm->thj", f["W_Kc"][l], src)
                o["Vc"] = np.einsum("hjm,tm->thj", f["W_Vc"][l], src)
            o["Sx"] = np_softmax_last(np.einsum("qhj,thj->hqt", o["Qc"], o["Kc"]) * f["Scx"])
            o["Ac"] = np.einsum("hqt,thj->qhj", o["Sx"], o["Vc"])
            o["Ax"] = np.einsum("mhj,qhj->qm", f["W_Oc"][l], o["Ac"])
            o["R2"] = r2 = o["Ra"] + o["Ax"]
        o["Nb"] = r2 / np.sqrt(np.einsum("qm,qm,m->q", r2, r2, f["Inv"]) + f["Eps"])[:, None] * f["G2"][l]
        o["F"] = np_gelu(np.einsum("dm,qm->qd", f["W_in"][l], o["Nb"]))
        o["H"] = r2 + np.einsum("md,qd->qm", f["W_out"][l], o["F"])
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


def trim_nan_layer(a: np.ndarray, label: str) -> np.ndarray:
    """Drop the layer-2 slice (last axis, index 2) of a pre-scan table stacked over the layer axis: it is built from the
    NaN layer-2 weight slice, so it is NaN by construction, and EXACTLY that slice must be NaN (the rest finite)."""
    assert a.shape[-1] == 3 and np.all(np.isnan(a[..., 2])) and np.all(np.isfinite(a[..., :2])), (label, "layer-2 slice is not the only NaN slice")
    return np.ascontiguousarray(a[..., :2])


def require_close(got, entry: dict, label: str, fn: str | None, nan_layer: bool = False) -> None:
    g, w = np.asarray(got), lean_array(entry)
    if g.dtype != NDT:
        raise AssertionError(f"{label}: expected {NDT.__name__}, got {g.dtype}")
    if g.shape != w.shape:
        raise AssertionError(f"{label}: shape {g.shape} != {w.shape}")
    if nan_layer:
        g, w = trim_nan_layer(g, label), trim_nan_layer(w, label)
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
    if (fixture, key) in NAN_LAYER_OUTPUTS:
        g, w = trim_nan_layer(g, f"{fixture} {key}"), trim_nan_layer(w, f"{fixture} {key}")
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
    if any(n.get("kind") == "scan" for n in plan["nodes"]) or f["name"].startswith(("transformer_unrolled", "conv1d_")):
        EAGER[f["name"]] = {"eager": eager, "jit": jitted}
    for name, exp in f["expected"].items():
        nan_layer = (f["name"], name) in NAN_LAYER_OUTPUTS
        require_close(eager[name], exp, f"{f['name']} eager {name}", fns.get(name), nan_layer)
        require_close(jitted[name], exp, f"{f['name']} jit {name}", fns.get(name), nan_layer)
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


CROSS_STACKS = ("W_Q", "W_K", "W_V", "W_O", "W_Qc", "W_Kc", "W_Vc", "W_Oc", "W_in", "W_out", "G1", "G2", "Gc")


def cross_fixture_pins(by: dict, sfx: str) -> None:
    """Pins of the cross-attention scan fixtures: `transformer_cross` (decoder layer = causal self-attention, then UNMASKED
    cross-attention to an external memory `Mem[t, m]` with t != q, then the MLP; the cross keys and values carry an explicit layer
    axis, `Kc[t, h, j, l]`) and `transformer_cross_hoisted` (the naive `Kc[t, h, j]`: a statement reading no scan state runs ONCE before
    the scan with `l` an ordinary axis and is SUMMED over every layer). The reference is `np_cross_transformer`, written from the English
    definition from the exported inputs only. Value pins on Lean, eager and jit; non-vacuity against wrong models (no cross block, every
    or any single memory row perturbed, memory taken from the layer state); the exported stacked tables against numpy; the hoisting trap
    pinned as the semantics it is."""
    name, hname = f"transformer_cross{sfx}", f"transformer_cross_hoisted{sfx}"
    ref = {n: lean_array(e) for n, e in by[f"transformer_window{sfx}"]["inputs"].items()}  # the mask fixtures' inputs
    fx, hx = by[name], by[hname]
    fin = {n: lean_array(e) for n, e in fx["inputs"].items()}
    hin = {n: lean_array(e) for n, e in hx["inputs"].items()}
    new_inputs = {"W_Qc", "W_Kc", "W_Vc", "W_Oc", "Mem", "Gc", "Scx"}
    assert sorted(fin) == sorted(set(ref) | new_inputs) and sorted(hin) == sorted(fin), (sorted(fin), sorted(hin), sorted(ref))
    # plan: the cross keys and values are two plain pre-scan tables, then ONE scan record with 2 steps; exactly H, Kc, Vc are exported
    for n_, f_ in ((name, fx), (hname, hx)):
        kinds = [n.get("kind", "assign") for n in f_["plan"]["nodes"]]
        scans = [n for n in f_["plan"]["nodes"] if n.get("kind") == "scan"]
        assert kinds == ["assign", "assign", "scan"] and scans[0]["step_count"] == 2, (n_, kinds)
        assert sorted(m for m, _ in f_["plan"]["materialized"]) == ["H", "Kc", "Vc"], (n_, f_["plan"]["materialized"])
    # every input other than the head weights, the memory, the cross gains and the scales is bitwise the mask fixtures'
    for n in ref:
        if n not in ("W_Q", "W_K", "W_V", "W_O", "Sc"):
            assert np.array_equal(bits(fin[n]), bits(ref[n])) and np.array_equal(bits(hin[n]), bits(ref[n])), (name, "input differs from the mask fixtures'", n)
    n_q, n_t, n_m = fin["X"].shape[0], fin["Mem"].shape[0], fin["X"].shape[1]
    n_h, n_k, n_j = fin["W_Q"].shape[1], fin["W_Q"].shape[2], fin["W_Qc"].shape[2]
    # q (= s), t, h, k, j, m are pairwise distinct, so no axis-order bug can hide behind equal extents on S, Sx, K, Kc, W_O, W_Oc, Ac
    assert len({n_q, n_t, n_h, n_k, n_j, n_m}) == 6 and fin["Mem"].shape == (n_t, n_m), (n_q, n_t, n_h, n_k, n_j, n_m)
    shapes = {"W_Q": (3, n_h, n_k, n_m), "W_K": (3, n_h, n_k, n_m), "W_V": (3, n_h, n_k, n_m), "W_O": (3, n_m, n_h, n_k),
              "W_Qc": (3, n_h, n_j, n_m), "W_Kc": (3, n_h, n_j, n_m), "W_Vc": (3, n_h, n_j, n_m), "W_Oc": (3, n_m, n_h, n_j), "Gc": (3, n_m)}
    for w, shp in shapes.items():
        assert fin[w].shape == hin[w].shape == shp, (w, fin[w].shape, shp)
    # the scales are 1 / sqrt(head width), from the input shapes (not from the numpy model that reads the exported value)
    tol = 1e-6 if _DT == "float32" else 1e-14
    assert fin["Sc"].shape == () and np.isclose(float(fin["Sc"]), n_k ** -0.5, rtol=tol), fin["Sc"]
    assert fin["Scx"].shape == () and np.isclose(float(fin["Scx"]), n_j ** -0.5, rtol=tol), fin["Scx"]
    assert np.array_equal(bits(fin["Sc"]), bits(hin["Sc"])) and np.array_equal(bits(fin["Scx"]), bits(hin["Scx"]))
    # layer-2 slices are NaN in every stack of the cross fixture (a step reading past layer 1 would turn every output NaN), layers 0, 1
    # finite and distinct; the hoisted fixture has the same stacks except FINITE layer-2 key and value cross weights (layers 0, 1 bitwise equal)
    for w in CROSS_STACKS:
        a = fin[w]
        assert a.shape[0] == 3 and np.all(np.isnan(a[2])) and np.all(np.isfinite(a[:2])) and not np.array_equal(a[0], a[1]), (name, w)
        if w in ("W_Kc", "W_Vc"):
            b = hin[w]
            assert np.all(np.isfinite(b)) and np.array_equal(bits(b[:2]), bits(a[:2])), (hname, w)
            assert not np.array_equal(b[2], b[0]) and not np.array_equal(b[2], b[1]), (hname, w, "layer 2 repeats a layer")
        else:
            assert np.array_equal(bits(hin[w]), bits(a)), (hname, w, "differs from the cross fixture's")
    # ---- transformer_cross: value pin on Lean, eager and jit
    layers = np_cross_transformer(fin)
    want = np_state(fin, layers)
    kc_want = np.einsum("lhjm,tm->thjl", fin["W_Kc"], fin["Mem"])  # NaN in layer 2 (from the NaN weight slice)
    vc_want = np.einsum("lhjm,tm->thjl", fin["W_Vc"], fin["Mem"])
    assert kc_want.shape == (n_t, n_h, n_j, 3) and np.all(np.isnan(kc_want[..., 2])) and np.all(np.isfinite(kc_want[..., :2]))
    # the cross block is real: the two layers' cross attention is not uniform (a uniform Sx would make the memory's keys irrelevant)
    unif = [float(np.max(np.abs(o["Sx"] - 1.0 / n_t))) for o in layers]
    assert all(u > 0.05 for u in unif), (name, "cross attention is near uniform", unif)

    def gap(**kw):  # max |H - H of the model with the given change| over the state
        inp = kw.pop("inp", fin)
        return float(np.max(np.abs(want - np_state(inp, np_cross_transformer(inp, **kw)))))

    # non-vacuity: the pin tells the cross block, EVERY memory row and each SINGLE memory row apart (permutation-invariance in t makes a
    # reversal useless), and the external memory from the layer state
    rng = np.random.default_rng(11)
    gaps = {"no cross block": gap(cross=False),
            "every memory row perturbed": gap(inp=dict(fin, Mem=fin["Mem"] + 0.5 * rng.standard_normal(fin["Mem"].shape))),
            "cross K and V from the layer state": gap(memory="state")}
    for what, g in gaps.items():
        assert g > 1e-2, (name, "the cross-attention pin is indistinguishable from", what, g)
    row_gaps = []
    for t in range(n_t):
        m_t = fin["Mem"].copy()
        m_t[t] += 0.5
        row_gaps.append(gap(inp=dict(fin, Mem=m_t)))
    assert min(row_gaps) > 1e-3, (name, "a memory row is ignored", row_gaps)
    views = {"lean": {n: lean_array(e) for n, e in fx["expected"].items()},
             "eager": {n: np.asarray(v) for n, v in EAGER[name]["eager"].items()},
             "jit": {n: np.asarray(v) for n, v in EAGER[name]["jit"].items()}}
    for who, outs in views.items():
        # exactly H, Kc, Vc are exported; H is finite (a step reading layer 2 would turn it NaN); the tables are NaN in layer 2 only
        assert sorted(outs) == ["H", "Kc", "Vc"] and np.all(np.isfinite(outs["H"])), (name, who, sorted(outs))
        assert outs["H"].shape == (n_q, n_m, 3) and outs["Kc"].shape == outs["Vc"].shape == (n_t, n_h, n_j, 3), (name, who)
        check_np(name, who, "H", outs["H"], want)
        check_np(name, who, "Kc", trim_nan_layer(outs["Kc"], name), kc_want[..., :2])
        check_np(name, who, "Vc", trim_nan_layer(outs["Vc"], name), vc_want[..., :2])
    # ---- transformer_cross_hoisted: the trap, pinned as the semantics it is
    hviews = {"lean": {n: lean_array(e) for n, e in hx["expected"].items()},
              "eager": {n: np.asarray(v) for n, v in EAGER[hname]["eager"].items()},
              "jit": {n: np.asarray(v) for n, v in EAGER[hname]["jit"].items()}}
    h_want = np_state(hin, np_cross_transformer(hin, hoisted=True))
    per_layer_gap = float(np.max(np.abs(h_want - np_state(hin, np_cross_transformer(hin)))))
    assert per_layer_gap > 1e-2, (hname, "hoisted cross-attention is indistinguishable from per-layer cross-attention", per_layer_gap)
    kc_sum = np.einsum("lhjm,tm->thj", hin["W_Kc"], hin["Mem"])  # summed over ALL THREE layers, layer 2 included
    vc_sum = np.einsum("lhjm,tm->thj", hin["W_Vc"], hin["Mem"])
    kc_l01 = np.einsum("lhjm,tm->thj", hin["W_Kc"][:2], hin["Mem"])  # the per-layer reading's sum over layers 0, 1 only
    assert float(np.max(np.abs(kc_sum - kc_l01))) > 1e-2, (hname, "layer 2 does not contribute to the summed table")
    for who, outs in hviews.items():
        assert sorted(outs) == ["H", "Kc", "Vc"] and all(np.all(np.isfinite(v)) for v in outs.values()), (hname, who, sorted(outs))
        assert outs["H"].shape == (n_q, n_m, 3) and outs["Kc"].shape == outs["Vc"].shape == (n_t, n_h, n_j), (hname, who, outs["Kc"].shape)
        check_np(hname, who, "H", outs["H"], h_want)
        check_np(hname, who, "Kc", outs["Kc"], kc_sum)
        check_np(hname, who, "Vc", outs["Vc"], vc_sum)
    print(f"cross{sfx}: q=s={n_q}, t={n_t}, h={n_h}, k={n_k}, j={n_j}, m={n_m} pairwise distinct; each plan = 2 plain pre-scan tables then ONE scan "
          f"record with 2 steps, exactly H, Kc, Vc exported; inputs bitwise the mask fixtures' except the head weights, Mem, Gc, Scx and the "
          f"scale; layer-2 slices NaN in all 13 stacks; H layers 0, 1, 2 and Kc, Vc layers 0, 1 == numpy decoder-layer model (English "
          f"definition) on Lean, eager and jit, Kc and Vc NaN in layer 2 only; numpy H differs from "
          f"{', '.join(f'{w} by {g:.3f}' for w, g in gaps.items())}; a single memory row moves H by {min(row_gaps):.3f} to {max(row_gaps):.3f}; "
          f"cross attention is not uniform (max deviation per layer {', '.join(f'{u:.3f}' for u in unif)}); HOISTED form (Kc[t, h, j], no "
          f"layer axis): Kc, Vc have no layer axis and equal the weights SUMMED over all three layers, H == numpy model with those tables and "
          f"differs from per-layer cross-attention by {per_layer_gap:.3f}")
    for n_ in (name, hname):
        print(f"{n_}: per-output measured difference vs numpy and vs Lean:")
        print_np_stats(n_)
        sc_err = NUM_STATS[(n_, "H")][0]
        print(f"  H headroom to MODEL_TOL: {MODEL_TOL[_DT] / max(sc_err, 1e-300):.1f}x (observed {sc_err:.3e} of {MODEL_TOL[_DT]:.0e})")
        for n in sorted(n for fx_, n in OUT_STATS if fx_ == n_):
            rel, ab, ex, tot = OUT_STATS[(n_, n)]
            print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")


def cross_wide_pins(by: dict, sfx: str) -> None:
    """Pins of `transformer_cross_wide`: `transformer_cross` with the memory `Mem[t, e]` and the cross key/value weights `W_Kc[l, h, j, e]`,
    `W_Vc[l, h, j, e]` over a memory width e that is NOT the model width m (and differs from q, t, h, k, j). In `transformer_cross` the memory
    shares the axis `m` with the layer state, so an axis mix-up between the state's width and the memory's width could not show. Same
    reference model (`np_cross_transformer`, whose einsums contract the memory's width axis under whatever extent it has), same plan shape and
    exports, and the inputs are the cross fixture's bit for bit except `W_Kc`, `W_Vc`, `Mem`."""
    name, base = f"transformer_cross_wide{sfx}", f"transformer_cross{sfx}"
    fx = by[name]
    fin = {n: lean_array(e) for n, e in fx["inputs"].items()}
    bin_ = {n: lean_array(e) for n, e in by[base]["inputs"].items()}
    assert sorted(fin) == sorted(bin_), (sorted(fin), sorted(bin_))
    kinds = [n.get("kind", "assign") for n in fx["plan"]["nodes"]]
    scans = [n for n in fx["plan"]["nodes"] if n.get("kind") == "scan"]
    assert kinds == ["assign", "assign", "scan"] and scans[0]["step_count"] == 2, (name, kinds)
    assert sorted(m for m, _ in fx["plan"]["materialized"]) == ["H", "Kc", "Vc"], (name, fx["plan"]["materialized"])
    for n in bin_:
        if n not in ("W_Kc", "W_Vc", "Mem"):
            assert np.array_equal(bits(fin[n]), bits(bin_[n])), (name, "input differs from the cross fixture's", n)
    n_q, n_m = fin["X"].shape
    n_t, n_e = fin["Mem"].shape
    n_h, n_k, n_j = fin["W_Q"].shape[1], fin["W_Q"].shape[2], fin["W_Qc"].shape[2]
    # the memory width e is a seventh extent, distinct from every other one (the model width m in particular)
    assert len({n_q, n_t, n_h, n_k, n_j, n_m, n_e}) == 7, (n_q, n_t, n_h, n_k, n_j, n_m, n_e)
    assert fin["W_Kc"].shape == fin["W_Vc"].shape == (3, n_h, n_j, n_e) and bin_["Mem"].shape == (n_t, n_m), (name, fin["W_Kc"].shape)
    for w in ("W_Kc", "W_Vc"):
        a = fin[w]
        assert np.all(np.isnan(a[2])) and np.all(np.isfinite(a[:2])) and not np.array_equal(a[0], a[1]), (name, w)
    layers = np_cross_transformer(fin)
    want = np_state(fin, layers)
    kc_want = np.einsum("lhje,te->thjl", fin["W_Kc"], fin["Mem"])
    vc_want = np.einsum("lhje,te->thjl", fin["W_Vc"], fin["Mem"])
    assert kc_want.shape == (n_t, n_h, n_j, 3) and np.all(np.isnan(kc_want[..., 2])) and np.all(np.isfinite(kc_want[..., :2]))
    unif = [float(np.max(np.abs(o["Sx"] - 1.0 / n_t))) for o in layers]
    assert all(u > 0.05 for u in unif), (name, "cross attention is near uniform", unif)

    def gap(inp=fin, **kw):
        return float(np.max(np.abs(want - np_state(inp, np_cross_transformer(inp, **kw)))))

    rng = np.random.default_rng(13)
    gaps = {"no cross block": gap(cross=False),
            "every memory entry perturbed": gap(dict(fin, Mem=fin["Mem"] + 0.5 * rng.standard_normal(fin["Mem"].shape))),
            # only the first m of the e width units (key/value weights and memory truncated): the extra width is real
            f"the memory truncated to its first {n_m} width units": gap(dict(
                fin, Mem=fin["Mem"][:, :n_m], W_Kc=fin["W_Kc"][..., :n_m], W_Vc=fin["W_Vc"][..., :n_m]))}
    for what, g in gaps.items():
        assert g > 1e-2, (name, "the wide-memory pin is indistinguishable from", what, g)
    row_gaps, col_gaps = [], []
    for t in range(n_t):
        m_ = fin["Mem"].copy()
        m_[t] += 0.5
        row_gaps.append(gap(dict(fin, Mem=m_)))
    for e in range(n_e):  # each memory WIDTH unit matters: none is ignored (an axis mix-up with m would ignore some)
        m_ = fin["Mem"].copy()
        m_[:, e] += 0.5
        col_gaps.append(gap(dict(fin, Mem=m_)))
    assert min(row_gaps) > 1e-3 and min(col_gaps) > 1e-3, (name, "a memory row or width unit is ignored", row_gaps, col_gaps)
    views = {"lean": {n: lean_array(e) for n, e in fx["expected"].items()},
             "eager": {n: np.asarray(v) for n, v in EAGER[name]["eager"].items()},
             "jit": {n: np.asarray(v) for n, v in EAGER[name]["jit"].items()}}
    for who, outs in views.items():
        assert sorted(outs) == ["H", "Kc", "Vc"] and np.all(np.isfinite(outs["H"])), (name, who, sorted(outs))
        assert outs["H"].shape == (n_q, n_m, 3) and outs["Kc"].shape == outs["Vc"].shape == (n_t, n_h, n_j, 3), (name, who)
        check_np(name, who, "H", outs["H"], want)
        check_np(name, who, "Kc", trim_nan_layer(outs["Kc"], name), kc_want[..., :2])
        check_np(name, who, "Vc", trim_nan_layer(outs["Vc"], name), vc_want[..., :2])
    print(f"cross_wide{sfx}: memory width e={n_e} != model width m={n_m}; q={n_q}, t={n_t}, h={n_h}, k={n_k}, j={n_j}, m={n_m}, e={n_e} pairwise distinct; "
          f"one scan record with 2 steps after 2 plain pre-scan tables, exactly H, Kc, Vc exported; inputs bitwise the cross fixture's except W_Kc, "
          f"W_Vc, Mem; H layers 0, 1, 2 and Kc, Vc layers 0, 1 == numpy decoder-layer model on Lean, eager and jit (Kc, Vc NaN in layer 2 only); numpy H "
          f"differs from {', '.join(f'{w} by {g:.3f}' for w, g in gaps.items())}; a single memory row moves H by {min(row_gaps):.3f} to "
          f"{max(row_gaps):.3f}, a single width unit by {min(col_gaps):.3f} to {max(col_gaps):.3f}")
    print(f"{name}: per-output measured difference vs numpy and vs Lean:")
    print_np_stats(name)
    sc_err = NUM_STATS[(name, "H")][0]
    print(f"  H headroom to MODEL_TOL: {MODEL_TOL[_DT] / max(sc_err, 1e-300):.1f}x (observed {sc_err:.3e} of {MODEL_TOL[_DT]:.0e})")
    for n in sorted(n for fx_, n in OUT_STATS if fx_ == name):
        rel, ab, ex, tot = OUT_STATS[(name, n)]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")


def cross_grad_pins(by: dict, sfx: str) -> None:
    """Gradient pins of `transformer_cross` (the cross-attention scan): `jax.grad` of `L = sum(C * H[:, :, 2])` through the emitted plan
    (two pre-scan tables, then the `lax.scan`), over EVERY float input INCLUDING the external memory `Mem`, eager and jit, against (b) the
    autodiff of a pure-JAX decoder layer written from the definition (no plan, no scan, carrier dtype) and (c) central finite differences of
    `np_cross_transformer` along random directions. Layer-2 weight slices (never read) get exactly zero gradient; the `Mem` gradient is finite,
    non-trivial and nonzero in every memory row. The inputs are the cross fixture's with the layer-2 key/value cross weights taken FINITE
    from the hoisted fixture (layers 0, 1 bitwise the same): on the NaN-stack inputs the `Mem` gradient is NaN in every entry, because
    `dMem = sum_l dKc[..., l] . W_Kc[l]` multiplies the exactly-zero layer-2 cotangent by the NaN layer-2 weights (0 * NaN); that is pinned
    below as what it is (a property of the NaN-sentinel stacks, not of the plan) and the finite-layer-2 inputs are what the pins differentiate."""
    name = f"transformer_cross{sfx}"
    fx, hx = by[name], by[f"transformer_cross_hoisted{sfx}"]
    nan_in = {n: lean_array(e) for n, e in fx["inputs"].items()}
    hin = {n: lean_array(e) for n, e in hx["inputs"].items()}
    sin = dict(nan_in, W_Kc=hin["W_Kc"], W_Vc=hin["W_Vc"])
    n_q = sin["X"].shape[0]
    C = np.sin(1.0 + np.arange(n_q * 4)).reshape(n_q, 4).astype(NDT)

    def loss_plan(inp):
        return jnp.sum(C * rt.run_named(fx["plan"], inp, JDT)["H"][:, :, 2])

    def loss_hand(inp):
        h, tril = inp["X"], jnp.tril(jnp.ones((n_q, n_q), dtype=bool))
        rms = lambda x: x / jnp.sqrt(jnp.einsum("qm,qm,m->q", x, x, inp["Inv"]) + inp["Eps"])[:, None]
        for l in range(2):
            n1 = rms(h) * inp["G1"][l]
            q = jnp.einsum("hkm,qm->qhk", inp["W_Q"][l], n1)
            k = jnp.einsum("hkm,sm->shk", inp["W_K"][l], n1)
            v = jnp.einsum("hkm,sm->shk", inp["W_V"][l], n1)
            s = jax.nn.softmax(jnp.where(tril[None], jnp.einsum("qhk,shk->hqs", q, k) * inp["Sc"], -jnp.inf), axis=-1)
            r1 = h + jnp.einsum("mhk,qhk->qm", inp["W_O"][l], jnp.einsum("hqs,shk->qhk", s, v))
            qc = jnp.einsum("hjm,qm->qhj", inp["W_Qc"][l], rms(r1) * inp["Gc"][l])
            kc = jnp.einsum("hjm,tm->thj", inp["W_Kc"][l], inp["Mem"])
            vc = jnp.einsum("hjm,tm->thj", inp["W_Vc"][l], inp["Mem"])
            sx = jax.nn.softmax(jnp.einsum("qhj,thj->hqt", qc, kc) * inp["Scx"], axis=-1)  # UNMASKED: every memory row is attended
            r2 = r1 + jnp.einsum("mhj,qhj->qm", inp["W_Oc"][l], jnp.einsum("hqt,thj->qhj", sx, vc))
            x = jnp.einsum("dm,qm->qd", inp["W_in"][l], rms(r2) * inp["G2"][l])
            f = 0.5 * x * (1.0 + jnp.tanh(0.7978845608028654 * (x + 0.044715 * x ** 3)))
            h = r2 + jnp.einsum("md,qd->qm", inp["W_out"][l], f)
        return jnp.sum(C * h)

    def scaled(a, b):
        a, b = np.asarray(a, dtype=np.float64), np.asarray(b, dtype=np.float64)
        return float(np.max(np.abs(a - b) / np.maximum(1.0, np.abs(b))))

    jin = {n: jnp.asarray(a) for n, a in sin.items()}
    grads = {"eager": jax.grad(loss_plan)(jin), "jit": jax.jit(jax.grad(loss_plan))(jin)}
    g_hand = jax.grad(loss_hand)(jin)
    err = {}
    for who, g in grads.items():
        assert sorted(g) == sorted(sin) and "Mem" in g, (name, who, sorted(g))
        assert all(np.all(np.isfinite(np.asarray(v))) and np.asarray(v).dtype == NDT for v in g.values()), (name, who, "gradient not finite")
        for w in CROSS_STACKS:
            gw = np.asarray(g[w])
            if w in ("W_Kc", "W_Vc"):  # layer 2 is finite in these inputs, but never read: still exactly zero
                assert sin[w].shape[0] == 3 and np.all(np.isfinite(sin[w]))
            assert np.all(gw[2] == 0), (name, "layer-2 weight slice received gradient", who, w)
            assert all(float(np.max(np.abs(gw[l]))) > 1e-3 for l in (0, 1)), (name, "trivial gradient", who, w)
            assert float(np.max(np.abs(gw[0] - gw[1]))) > 1e-2, (name, "layers 0 and 1 have alike gradients", who, w)
        gm = np.asarray(g["Mem"])  # the external memory: a real gradient in EVERY row (no memory position is ignored)
        assert float(np.max(np.abs(gm))) > 1e-3 and np.all(np.max(np.abs(gm), axis=1) > 0), (name, "memory gradient is trivial", who, gm.tolist())
        for n in sin:
            e_ref = scaled(g[n], g_hand[n])
            assert e_ref < GRAD_TOL[_DT], (f"gradient pin: {name} vs pure-JAX model", who, n, e_ref)
            err[n] = max(err.get(n, 0.0), e_ref)
    gq = np.asarray(grads["eager"]["W_Qc"])
    assert scaled(gq * NDT(1.001), gq) >= GRAD_TOL[_DT], (name, "gradient tolerance accepts a 1e-3 perturbation: vacuous")
    # the NaN-sentinel stacks: with the fixture's own NaN layer-2 key/value weights the Mem gradient is NaN everywhere (0 * NaN) while
    # every WEIGHT gradient stays finite with an exactly-zero layer-2 slice; finite layer-2 weights (above) remove it
    nan_g = jax.grad(loss_plan)({n: jnp.asarray(a) for n, a in nan_in.items()})
    assert np.all(np.isnan(np.asarray(nan_g["Mem"]))), (name, "Mem gradient on the NaN-stack inputs is expected NaN everywhere")
    assert all(np.all(np.isfinite(np.asarray(v))) for n, v in nan_g.items() if n != "Mem"), (name, "a non-Mem gradient is non-finite")
    # (c) directional derivatives against central differences of the numpy model (3 fixed directions over all inputs incl. Mem; zero on layer 2)
    base = {n: a.astype(np.float64) for n, a in sin.items()}
    rng = np.random.default_rng(7)
    fd_err, dots = 0.0, []
    loss_np = lambda inp: float(np.sum(C.astype(np.float64) * np_state(inp, np_cross_transformer(inp))[:, :, 2]))
    for _ in range(3):
        d = {n: rng.standard_normal(a.shape) for n, a in base.items()}
        for w in CROSS_STACKS:
            d[w][2] = 0.0
        eps = 1e-6
        fd = (loss_np({n: base[n] + eps * d[n] for n in base}) - loss_np({n: base[n] - eps * d[n] for n in base})) / (2 * eps)
        for who, g in grads.items():
            dot = float(sum(np.sum(np.asarray(g[n], dtype=np.float64) * d[n]) for n in base))
            assert abs(dot) > 1e-2, (name, "finite-difference direction is trivial", dot)
            fd_err = max(fd_err, abs(fd - dot) / max(1.0, abs(dot)))
        dots.append(dot)
    assert fd_err < GRAD_FD_TOL[_DT], (f"gradient pin: {name} directional derivative vs finite differences of the numpy model", fd_err)
    gm = np.asarray(grads["eager"]["Mem"])
    print(f"gradients of {name} (eager and jit, all {len(sin)} float inputs incl. Mem, layer-2 K/V cross weights finite): finite, layer-2 weight "
          f"slices exactly zero, layers 0 and 1 non-trivial and distinct; Mem gradient nonzero in every row (max abs {float(np.max(np.abs(gm))):.3f}, "
          f"min row max {float(np.min(np.max(np.abs(gm), axis=1))):.3f}); == autodiff of a pure-JAX decoder layer (max scaled {max(err.values()):.3e}, "
          f"headroom {GRAD_TOL[_DT] / max(max(err.values()), 1e-300):.1f}x) and directional derivatives == central differences of the float64 numpy "
          f"model (|dot| {min(abs(x) for x in dots):.2f} to {max(abs(x) for x in dots):.2f}, max scaled {fd_err:.3e}, headroom "
          f"{GRAD_FD_TOL[_DT] / max(fd_err, 1e-300):.1f}x); on the NaN-stack inputs the Mem gradient is NaN in every entry (0 * NaN), the weight gradients finite")


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


def np_conv(X, W, n_out, stride=1, dilation=1, bias=0, wrap=False):
    """1-D convolution written from the ENGLISH definition (no `np.convolve`, no windowing helpers, nothing shared with the plan):
    `Y[o, d] = sum over taps i and channels c of W[d, i, c] * X[stride * o + dilation * i + bias, c]`, with a zero for an index outside
    `[0, L)` (or, with `wrap`, the index taken modulo L: a circular model, used only as a wrong-model alternative)."""
    f_x, f_w = np.asarray(X, dtype=np.float64), np.asarray(W, dtype=np.float64)
    length, chans = f_x.shape
    n_d, n_k, n_c = f_w.shape
    assert n_c == chans, (f_w.shape, f_x.shape)
    y = np.zeros((n_out, n_d))
    for o in range(n_out):
        for d in range(n_d):
            acc = 0.0
            for i in range(n_k):
                t = stride * o + dilation * i + bias
                if wrap:
                    t %= length
                elif t < 0 or t >= length:
                    continue
                for c in range(chans):
                    acc += f_w[d, i, c] * f_x[t, c]
            y[o, d] = acc
    return y


def np_cnn(inp: dict, dilation2: int = 2, stride2: int = 2, flip: bool = False, bias: bool = True, relu: bool = True,
           pool: float | None = None) -> dict:
    """Float64 model of `conv1d_cnn` from the inputs only: Y1 = valid stride-1 convolution of X with W1 plus B1; A1 = relu; Y2 = convolution of A1
    with W2 (stride 2, dilation 2) plus B2; A2 = relu; Gp = mean over positions (divisor = the extent of Y2's position axis); Zc = Wc . Gp + Bc;
    Pr = softmax(Zc). The keyword arguments build the wrong models the non-vacuity pins compare against (the second layer keeps its output extent)."""
    f = {k: np.asarray(v, dtype=np.float64) for k, v in inp.items()}
    n_o = f["X"].shape[0] - f["W1"].shape[1] + 1
    n_p = (n_o - 1 - 2 * (f["W2"].shape[1] - 1)) // 2 + 1  # the canonical extent of Y2's position axis (stride 2, dilation 2)
    y1 = np_conv(f["X"], f["W1"][:, ::-1, :] if flip else f["W1"], n_o) + (f["B1"] if bias else 0.0)
    a1 = np.maximum(y1, 0.0) if relu else y1
    y2 = np_conv(a1, f["W2"], n_p, stride2, dilation2) + (f["B2"] if bias else 0.0)
    a2 = np.maximum(y2, 0.0) if relu else y2
    gp = a2.sum(axis=0) / (pool if pool is not None else n_p)
    zc = np.einsum("ne,e->n", f["Wc"], gp) + (f["Bc"] if bias else 0.0)
    return {"Y1": y1, "A1": a1, "Y2": y2, "A2": a2, "Gp": gp, "Zc": zc, "Pr": np_softmax_last(zc)}


def np_tcn(inp: dict, wrap: bool = False, centred: bool = False, skip: bool = True, dil1: int = 2, dil2: int = 4) -> dict:
    """Float64 model of `conv1d_causal` (a TCN residual block) from the inputs only: Y1 = causal dilated (dilation `dil1`) convolution of X with
    W1 plus B1 (left zero padding: tap i reads `X[o + dil1 * i - dil1 * (K - 1)]`, a negative index is zero); A1 = relu; Y2 = the same with W2,
    dilation `dil2`, plus B2; A2 = relu; Rs = 1x1 convolution of X with Wr; Out = A2 + Rs. `wrap` pads circularly, `centred` centres the window
    instead of making it causal, `skip=False` drops the residual path (the wrong models of the non-vacuity pins)."""
    f = {k: np.asarray(v, dtype=np.float64) for k, v in inp.items()}
    length, k = f["X"].shape[0], f["W1"].shape[1]
    shift = (lambda d: -(d * (k - 1)) // 2) if centred else (lambda d: -(d * (k - 1)))
    y1 = np_conv(f["X"], f["W1"], length, 1, dil1, shift(dil1), wrap) + f["B1"]
    a1 = np.maximum(y1, 0.0)
    y2 = np_conv(a1, f["W2"], length, 1, dil2, shift(dil2), wrap) + f["B2"]
    a2 = np.maximum(y2, 0.0)
    rs = np_conv(f["X"], f["Wr"][:, None, :], length)
    return {"Y1": y1, "A1": a1, "Y2": y2, "A2": a2, "Rs": rs, "Out": a2 + rs if skip else a2}


def np_vit(inp: dict, no_pos: bool = False, stride: int = 6, permute: bool = False):
    """Float64 model of `vit_patch` from the inputs only: the patch embedding Pe[q, m] = sum over window taps i and channels c of
    Wp[m, i, c] * Img[stride * q + i, c], plus Pos[q, m], is the scan's base state, then the two-layer standard pre-norm model `np_transformer`
    (unchanged) on `X = Pe`. Returns `(Pe, H[q, m, 3])`. `no_pos`, `stride` and `permute` (the window taps reversed) build the wrong models."""
    f = {k: np.asarray(v, dtype=np.float64) for k, v in inp.items()}
    n_q = f["Pos"].shape[0]
    pe = np_conv(f["Img"], f["Wp"][:, ::-1, :] if permute else f["Wp"], n_q, stride) + (0.0 if no_pos else f["Pos"])
    full = dict(f, X=pe)
    return pe, np_state(full, np_transformer(full))


def dict_gap(a: dict, b: dict) -> float:
    """Largest absolute difference over the entries (tensors) the two models share, which must all have equal shapes."""
    assert sorted(a) == sorted(b) and all(a[n].shape == b[n].shape for n in a), (sorted(a), sorted(b))
    return max(float(np.max(np.abs(a[n] - b[n]))) for n in a)


def conv_views(by: dict, name: str) -> dict:
    """The three views of a fixture's exported tensors: Lean's own result, the eager runtime and `jax.jit`."""
    return {"lean": {n: lean_array(e) for n, e in by[name]["expected"].items()},
            "eager": {n: np.asarray(v) for n, v in EAGER[name]["eager"].items()},
            "jit": {n: np.asarray(v) for n, v in EAGER[name]["jit"].items()}}


def print_conv_stats(name: str) -> None:
    print(f"{name}: per-output measured difference vs numpy and vs Lean:")
    print_np_stats(name)
    worst = max(NUM_STATS[(name, n)][0] for fx_, n in NUM_STATS if fx_ == name)
    room = "unbounded (bit-identical to numpy)" if worst == 0.0 else f"{MODEL_TOL[_DT] / worst:.1f}x"
    print(f"  worst scaled difference vs numpy {worst:.3e}: headroom to MODEL_TOL {room} (tol {MODEL_TOL[_DT]:.0e})")
    for n in sorted(n for fx_, n in OUT_STATS if fx_ == name):
        rel, ab, ex, tot = OUT_STATS[(name, n)]
        print(f"  {n:8s} max rel {rel:.3e}  max abs {ab:.3e}  bit-identical {ex}/{tot}")


def conv_cnn_pins(by: dict, sfx: str) -> None:
    """Pins of `conv1d_cnn` (a 1-D CNN classifier): a valid stride-1 convolution with bias and relu, then a stride-2 dilation-2 convolution that
    READS AN INTERMEDIATE through an affine slot (`A1[2 * p + 2 * j, d]`), bias, relu, a global mean pool (a sum times the scalar input
    `Ip = 1 / p`), a linear head and a softmax over the classes. The reference is `np_cnn` (explicit loops, from the exported inputs only).
    Value pins on Lean, eager and jit for EVERY exported tensor (the linear intermediates `Y1`, `Y2` included); non-vacuity against wrong
    models (dilation 1, stride 1, flipped kernel, no bias, no relu, a wrong pool divisor); relu clamps some entries and passes others;
    structure (shapes from the inputs, probabilities positive and summing to 1, nine pairwise distinct extents)."""
    name = f"conv1d_cnn{sfx}"
    fx = by[name]
    fin = {n: lean_array(e) for n, e in fx["inputs"].items()}
    assert sorted(fin) == ["B1", "B2", "Bc", "Ip", "W1", "W2", "Wc", "X"], sorted(fin)
    kinds = [n.get("kind", "assign") for n in fx["plan"]["nodes"]]
    assert kinds == ["assign", "assign", "pointwise", "assign", "assign", "pointwise", "assign", "assign", "assign", "axiswise"], kinds  # conv, bias, relu, conv, bias, relu, pool, head conv, head bias, softmax
    assert sorted(m for m, _ in fx["plan"]["materialized"]) == ["A1", "A2", "Gp", "Pr", "Y1", "Y2", "Zc"], fx["plan"]["materialized"]
    n_l, n_c = fin["X"].shape
    (n_d, n_k1, c1), (n_e, n_k2, d2), (n_cls, e3) = fin["W1"].shape, fin["W2"].shape, fin["Wc"].shape
    n_o = n_l - n_k1 + 1
    n_p = (n_o - 1 - 2 * (n_k2 - 1)) // 2 + 1
    ext = {"l": n_l, "c": n_c, "i": n_k1, "d": n_d, "o": n_o, "j": n_k2, "e": n_e, "p": n_p, "n": n_cls}
    # nine pairwise distinct extents: no axis-order bug can hide behind equal extents on any weight, intermediate or output
    assert len(set(ext.values())) == len(ext) and (c1, d2, e3) == (n_c, n_d, n_e), ext
    assert fin["B1"].shape == (n_d,) and fin["B2"].shape == (n_e,) and fin["Bc"].shape == (n_cls,), (fin["B1"].shape, fin["B2"].shape, fin["Bc"].shape)
    tol = 1e-6 if _DT == "float32" else 1e-14
    assert fin["Ip"].shape == () and np.isclose(float(fin["Ip"]), 1.0 / n_p, rtol=tol), fin["Ip"]  # the pool scale from the shapes
    want = np_cnn(fin)
    for n, shp in {"Y1": (n_o, n_d), "A1": (n_o, n_d), "Y2": (n_p, n_e), "A2": (n_p, n_e), "Gp": (n_e,), "Zc": (n_cls,), "Pr": (n_cls,)}.items():
        assert want[n].shape == shp, (n, want[n].shape, shp)
    # relu is real: it clamps some entries and passes others (a pass-through or an all-zero relu would be caught here)
    for y, a in (("Y1", "A1"), ("Y2", "A2")):
        assert np.array_equal(want[a], np.maximum(want[y], 0.0)) and np.any(want[y] < 0) and np.any(want[a] > 0) and np.any(want[a] == 0), (name, a)
    wrong = {"second-layer dilation 1": np_cnn(fin, dilation2=1), "second-layer stride 1": np_cnn(fin, stride2=1),
             "kernel flipped": np_cnn(fin, flip=True), "no bias": np_cnn(fin, bias=False), "no relu": np_cnn(fin, relu=False),
             "pool divisor 7": np_cnn(fin, pool=float(n_p - 1))}
    gaps = {what: dict_gap(want, m) for what, m in wrong.items()}
    for what, g in gaps.items():
        assert g > 1e-2, (name, "the CNN pin is indistinguishable from", what, g)
    for who, outs in conv_views(by, name).items():
        assert sorted(outs) == sorted(want), (name, who, sorted(outs))
        assert outs["Y1"].shape == (n_o, n_d) and outs["Y2"].shape == (n_p, n_e), (name, who)
        for n in sorted(want):
            check_np(name, who, n, outs[n], want[n])
        pr = outs["Pr"].astype(np.float64)
        assert np.all(pr > 0) and abs(float(pr.sum()) - 1.0) < HEAD_ROWSUM_TOL[_DT], (name, who, "Pr is not a probability vector", pr.tolist())
    print(f"conv1d_cnn{sfx}: extents l={n_l}, c={n_c}, i={n_k1}, d={n_d}, o={n_o}, j={n_k2}, e={n_e}, p={n_p}, n={n_cls} pairwise distinct; plan = 7 assign, "
          f"2 relu, 1 softmax, exactly Y1, A1, Y2, A2, Gp, Zc, Pr exported; Ip = 1/p from the shapes; every export == numpy explicit-loop model "
          f"(English definition) on Lean, eager and jit; relu clamps {int(np.sum(want['A1'] == 0))}/{want['A1'].size} of A1 and "
          f"{int(np.sum(want['A2'] == 0))}/{want['A2'].size} of A2; Pr positive, sums to 1; numpy differs from "
          f"{', '.join(f'{w} by {g:.3f}' for w, g in gaps.items())}")
    print_conv_stats(name)


def conv_causal_pins(by: dict, sfx: str) -> None:
    """Pins of `conv1d_causal` (a TCN residual block): two dilated CAUSAL convolutions (dilations 2 and 4; left zero padding by a negative index
    bias, output extent = input extent) with a relu after each, a 1x1 convolution on the skip path and the residual add. Reference `np_tcn`
    (explicit loops, zero outside `[0, L)`). Value pins on Lean, eager and jit for every export; non-vacuity (circular padding, a centred window,
    no skip, dilation 1; the skip weights and each bias must matter); CAUSALITY on the eager runtime: perturbing `X[t]` leaves every output
    `o < t` and every output beyond the receptive field `t + 12` BITWISE unchanged (a non-causal model of the same extent fails it), and the
    outputs that move are exactly at the offsets the two dilations reach (`o - t` even, `0 <= o - t <= 12`); the first output row is the
    zero-padded value (a wrapping runtime would read the end of the sequence)."""
    name = f"conv1d_causal{sfx}"
    fx = by[name]
    fin = {n: lean_array(e) for n, e in fx["inputs"].items()}
    assert sorted(fin) == ["B1", "B2", "W1", "W2", "Wr", "X"], sorted(fin)
    kinds = [n.get("kind", "assign") for n in fx["plan"]["nodes"]]
    assert kinds == ["assign", "assign", "pointwise", "assign", "assign", "pointwise", "assign", "assign"], kinds  # conv, bias, relu, conv, bias, relu, skip, add
    assert sorted(m for m, _ in fx["plan"]["materialized"]) == ["A1", "A2", "Out", "Rs", "Y1", "Y2"], fx["plan"]["materialized"]
    n_l, n_c = fin["X"].shape
    (n_d, n_k1, c1), (n_e, n_k2, d2), (e3, c3) = fin["W1"].shape, fin["W2"].shape, fin["Wr"].shape
    # l, c, k, d, e pairwise distinct (the two kernel widths are both k = 3: separate axes of separate tensors, the only equal pair)
    assert n_k1 == n_k2 and len({n_l, n_c, n_k1, n_d, n_e}) == 5 and (c1, d2, e3, c3) == (n_c, n_d, n_e, n_c), (n_l, n_c, n_k1, n_d, n_e)
    assert n_l == 17 and n_k1 == 3, (n_l, n_k1)
    reach = 2 * (n_k1 - 1) + 4 * (n_k1 - 1)  # receptive field: dilation 2 then dilation 4, K = 3 each, X[o - 12 .. o]
    assert reach == 12 and n_l > reach + 1, reach
    want = np_tcn(fin)
    wrong = {"circular padding": np_tcn(fin, wrap=True), "centred (non-causal) window": np_tcn(fin, centred=True),
             "no skip path": np_tcn(fin, skip=False), "first-layer dilation 1": np_tcn(fin, dil1=1)}
    gaps = {what: dict_gap(want, m) for what, m in wrong.items()}
    for what, g in gaps.items():
        assert g > 1e-2, (name, "the TCN pin is indistinguishable from", what, g)
    # the 1x1 skip and each bias are not ignorable
    moved = {"Wr": dict_gap(want, np_tcn(dict(fin, Wr=fin["Wr"] + 0.05))), "B1": dict_gap(want, np_tcn(dict(fin, B1=fin["B1"] + 0.05))),
             "B2": dict_gap(want, np_tcn(dict(fin, B2=fin["B2"] + 0.05)))}
    assert min(moved.values()) > 1e-3, (name, "the skip weights or a bias are ignorable", moved)
    # the first row is the zero-padded value: the layer-1 taps at X[-4], X[-2] are zero, only tap 2 reads X[0]
    f64 = {n: a.astype(np.float64) for n, a in fin.items()}
    y1_row0 = f64["B1"] + np.einsum("dc,c->d", f64["W1"][:, 2, :], f64["X"][0])
    assert np.allclose(want["Y1"][0], y1_row0, rtol=1e-12), (want["Y1"][0], y1_row0)
    views = conv_views(by, name)
    for who, outs in views.items():
        assert sorted(outs) == sorted(want), (name, who, sorted(outs))
        for n in sorted(want):
            assert outs[n].shape == (n_l, n_d if n in ("Y1", "A1") else n_e), (name, who, n, outs[n].shape)
            check_np(name, who, n, outs[n], want[n])
        row0 = float(np.max(np.abs(outs["Y1"][0].astype(np.float64) - y1_row0)))
        assert row0 < MODEL_TOL[_DT], (name, who, "the first output row is not the zero-padded value", row0)
    # CAUSALITY on the eager runtime (the pin does not read Lean): perturb X[t]; compare every export bitwise
    plan = fx["plan"]
    inputs = {n: reconstruct(e) for n, e in fx["inputs"].items()}
    base = EAGER[name]["eager"]
    hit, sizes = set(), {}
    # each export's own receptive field: layer 1 reaches back 2 * (K - 1) = 4, the 1x1 skip 0, everything after layer 2 the full 12
    reach_of = {"Y1": 2 * (n_k1 - 1), "A1": 2 * (n_k1 - 1), "Rs": 0, "Y2": reach, "A2": reach, "Out": reach}
    for t in range(n_l):
        x_p = np.array(fin["X"], dtype=NDT)
        x_p[t] += NDT(0.5)
        pert = rt.run_named(plan, dict(inputs, X=jnp.asarray(x_p)), JDT)
        for n in sorted(want):
            b, p = np.asarray(base[n]), np.asarray(pert[n])
            assert b.dtype == p.dtype == NDT and b.shape == p.shape, (name, n)
            for o in range(n_l):
                same = np.array_equal(bits(b[o]), bits(p[o]))
                if o < t or o > t + reach_of[n] or (o - t) % 2 == 1:
                    assert same, (f"causality: {n}[{o}] changed under a perturbation of X[{t}]", o - t)
                elif not same:
                    hit.add((n, o - t))
                    sizes[(n, o - t)] = max(sizes.get((n, o - t), 0.0), float(np.max(np.abs(b[o].astype(np.float64) - p[o].astype(np.float64)))))
        assert (("Out", 0)) in hit and ("Rs", 0) in hit, (name, "the skip path does not respond to its own position", t)
    # every even offset 0, 2, ..., 12 of the receptive field is reached by SOME perturbation in the output (a smaller or a dilation-1 field would not)
    for off in range(0, reach + 1, 2):
        assert ("Out", off) in hit and sizes[("Out", off)] > 1e-3, (name, "output offset never moves", off)
    print(f"conv1d_causal{sfx}: extents l={n_l}, c={n_c}, k={n_k1} (both layers), d={n_d}, e={n_e}; plan = 6 assign, 2 relu, exactly Y1, A1, Y2, A2, Rs, Out "
          f"exported; every export == numpy zero-padded explicit-loop model (English definition) on Lean, eager and jit; first row == zero-padded "
          f"value; numpy differs from {', '.join(f'{w} by {g:.3f}' for w, g in gaps.items())}; Wr/B1/B2 perturbed by 0.05 move Out by "
          f"{min(moved.values()):.3f} to {max(moved.values()):.3f}; CAUSALITY on the eager runtime for all {n_l} positions: perturbing X[t] leaves "
          f"every export row o < t, o > t + {reach} and (o - t) odd BITWISE unchanged, Out responds at every even offset 0..{reach} "
          f"(smallest max response {min(sizes[('Out', o)] for o in range(0, reach + 1, 2)):.3e})")
    print_conv_stats(name)


def vit_patch_pins(by: dict, sfx: str) -> None:
    """Pins of `vit_patch`: a patch embedding (windows of width 6, stride 6, plus a positional embedding) computed BEFORE the layer scan and used as
    its base state. Reference `np_vit`: the explicit-loop patch embedding feeding the unchanged `np_transformer`. Value pins on Lean, eager and jit
    (`Pe`, `H`); non-vacuity (no positional embedding, overlapping patches, a permuted window); PATCH LOCALITY on the eager runtime (perturbing
    `Img[u]` changes only patch `u // 6` of `Pe`, every other row BITWISE unchanged); plan shape (one pre-scan statement, ONE scan record with 2
    steps, exactly `Pe` and `H` exported); every other input bitwise the mask fixtures'."""
    name = f"vit_patch{sfx}"
    fx = by[name]
    ref = {n: lean_array(e) for n, e in by[f"transformer_window{sfx}"]["inputs"].items()}  # the mask fixtures' inputs
    fin = {n: lean_array(e) for n, e in fx["inputs"].items()}
    new_inputs = {"Img", "Wp", "Pos"}
    assert sorted(fin) == sorted((set(ref) - {"X"}) | new_inputs), (sorted(fin), sorted(ref))
    for n in ref:
        if n != "X":
            assert np.array_equal(bits(fin[n]), bits(ref[n])), (name, "input differs from the mask fixtures'", n)
    nodes = fx["plan"]["nodes"]
    scans = [n for n in nodes if n.get("kind") == "scan"]
    assert [n.get("kind", "assign") for n in nodes] == ["assign", "scan"] and scans[0]["step_count"] == 2, [n.get("kind", "assign") for n in nodes]
    assert sorted(m for m, _ in fx["plan"]["materialized"]) == ["H", "Pe"], fx["plan"]["materialized"]
    n_l, n_c = fin["Img"].shape
    n_m, n_w, c1 = fin["Wp"].shape
    n_q = fin["Pos"].shape[0]
    assert fin["Pos"].shape == (n_q, n_m) and c1 == n_c and n_w == 6 and n_l == n_w * n_q and n_q == fin["Eps"].shape[0], (fin["Pos"].shape, fin["Wp"].shape, n_l, n_q)
    assert len({n_l, n_c, n_w, n_q, n_m}) == 5, (n_l, n_c, n_w, n_q, n_m)  # l, c, window, q, m pairwise distinct
    for w in ("W_Q", "W_K", "W_V", "W_O", "W_in", "W_out", "G1", "G2"):  # the standard NaN layer-2 stacks
        a = fin[w]
        assert a.shape[0] == 3 and np.all(np.isnan(a[2])) and np.all(np.isfinite(a[:2])) and not np.array_equal(a[0], a[1]), (name, w)
    pe_want, h_want = np_vit(fin)
    assert pe_want.shape == (n_q, n_m) and h_want.shape == (n_q, n_m, 3), (pe_want.shape, h_want.shape)
    gaps = {"no positional embedding": float(np.max(np.abs(h_want - np_vit(fin, no_pos=True)[1]))),
            "overlapping patches (stride 3)": float(np.max(np.abs(h_want - np_vit(fin, stride=3)[1]))),
            "permuted window": float(np.max(np.abs(h_want - np_vit(fin, permute=True)[1])))}
    pe_gaps = {"no positional embedding": float(np.max(np.abs(pe_want - np_vit(fin, no_pos=True)[0]))),
               "overlapping patches (stride 3)": float(np.max(np.abs(pe_want - np_vit(fin, stride=3)[0]))),
               "permuted window": float(np.max(np.abs(pe_want - np_vit(fin, permute=True)[0])))}
    for what in gaps:
        assert gaps[what] > 1e-2 and pe_gaps[what] > 1e-2, (name, "the ViT pin is indistinguishable from", what, gaps[what], pe_gaps[what])
    for who, outs in conv_views(by, name).items():
        assert sorted(outs) == ["H", "Pe"] and np.all(np.isfinite(outs["H"])), (name, who, sorted(outs))
        assert outs["Pe"].shape == (n_q, n_m) and outs["H"].shape == (n_q, n_m, 3), (name, who)
        check_np(name, who, "Pe", outs["Pe"], pe_want)
        check_np(name, who, "H", outs["H"], h_want)
    # PATCH LOCALITY on the eager runtime: perturb Img[u]; only patch u // window of Pe changes, the other rows are bitwise unchanged
    inputs = {n: reconstruct(e) for n, e in fx["inputs"].items()}
    base = np.asarray(EAGER[name]["eager"]["Pe"])
    moves = []
    for u in range(n_l):
        img = np.array(fin["Img"], dtype=NDT)
        img[u] += NDT(0.5)
        p = np.asarray(rt.run_named(fx["plan"], dict(inputs, Img=jnp.asarray(img)), JDT)["Pe"])
        assert p.dtype == NDT and p.shape == base.shape
        for q in range(n_q):
            same = np.array_equal(bits(base[q]), bits(p[q]))
            if q != u // n_w:
                assert same, (f"patch locality: Pe[{q}] changed under a perturbation of Img[{u}]", u // n_w)
            else:
                assert not same, (name, "the patch does not respond to its own position", u, q)
                moves.append(float(np.max(np.abs(base[q].astype(np.float64) - p[q].astype(np.float64)))))
    assert min(moves) > 1e-3, (name, "a patch responds only weakly to a position", min(moves))
    print(f"vit_patch{sfx}: extents l={n_l}, c={n_c}, window={n_w}, q={n_q}, m={n_m} pairwise distinct; plan = 1 pre-scan statement then ONE scan record "
          f"with 2 steps, exactly Pe and H exported; inputs bitwise the mask fixtures' except Img, Wp, Pos (X replaced); layer-2 slices NaN in all 8 stacks; "
          f"Pe and H layers 0, 1, 2 == numpy explicit-loop patch embedding feeding np_transformer on Lean, eager and jit; numpy H differs from "
          f"{', '.join(f'{w} by {g:.3f}' for w, g in gaps.items())} (Pe by {', '.join(f'{g:.3f}' for g in pe_gaps.values())}); PATCH LOCALITY for all "
          f"{n_l} positions: perturbing Img[u] changes only Pe row u // {n_w} (by {min(moves):.3f} to {max(moves):.3f}), every other row bitwise unchanged")
    print_conv_stats(name)


def conv_grad_pins(by: dict, sfx: str) -> None:
    """Gradient pins of the three convolution fixtures: `jax.grad` of `L = sum(C * out)` through the emitted plan over EVERY float input (eager and
    jit) for the CNN (`out` = the logits `Zc`, not the softmax: a softmax loss is nearly degenerate), the TCN (`Out`) and the ViT (`H[:, :, 2]`),
    against (b) the autodiff of a pure-JAX model written from the definition WITHOUT the plan or the scan (`jax.lax.conv_general_dilated` for every
    strided, dilated or causally padded layer: nothing shared with the plan's gather) and (c) central finite differences of the float64 numpy models
    (explicit loops) along random directions. TCN: a loss on outputs `0 .. t` has EXACTLY zero gradient on `X` rows `> t` and a real one on every
    row `<= t`. ViT: layer-2 weight slices exactly zero, `Img` gradient real at every position, `Wp` and `Pos` real."""

    def scaled(a, b):
        a, b = np.asarray(a, dtype=np.float64), np.asarray(b, dtype=np.float64)
        return float(np.max(np.abs(a - b) / np.maximum(1.0, np.abs(b))))

    def lax_conv(x, w, stride=1, dilation=1, pad=(0, 0)):
        """x[L, C], w[D, K, C] -> y[n_out, D]: cross-correlation (no flip) with explicit (left, right) zero padding."""
        y = jax.lax.conv_general_dilated(x.T[None], jnp.transpose(w, (0, 2, 1)), (stride,), [pad], rhs_dilation=(dilation,),
                                         dimension_numbers=("NCH", "OIH", "NCH"))
        return y[0].T

    def cnn_hand(i):
        a1 = jnp.maximum(lax_conv(i["X"], i["W1"]) + i["B1"], 0.0)
        a2 = jnp.maximum(lax_conv(a1, i["W2"], 2, 2) + i["B2"], 0.0)
        return i["Wc"] @ (i["Ip"] * jnp.sum(a2, axis=0)) + i["Bc"]

    def tcn_hand(i):
        k = i["W1"].shape[1]
        a1 = jnp.maximum(lax_conv(i["X"], i["W1"], 1, 2, (2 * (k - 1), 0)) + i["B1"], 0.0)
        a2 = jnp.maximum(lax_conv(a1, i["W2"], 1, 4, (4 * (k - 1), 0)) + i["B2"], 0.0)
        return a2 + i["X"] @ i["Wr"].T

    def vit_hand(i):
        h = lax_conv(i["Img"], i["Wp"], 6) + i["Pos"]
        tril = jnp.tril(jnp.ones((h.shape[0], h.shape[0]), dtype=bool))
        rms = lambda x: x / jnp.sqrt(jnp.einsum("qm,qm,m->q", x, x, i["Inv"]) + i["Eps"])[:, None]
        for l in range(2):
            n1 = rms(h) * i["G1"][l]
            q = jnp.einsum("hkm,qm->qhk", i["W_Q"][l], n1)
            k = jnp.einsum("hkm,sm->shk", i["W_K"][l], n1)
            v = jnp.einsum("hkm,sm->shk", i["W_V"][l], n1)
            s = jax.nn.softmax(jnp.where(tril[None], jnp.einsum("qhk,shk->hqs", q, k) * i["Sc"], -jnp.inf), axis=-1)
            r1 = h + jnp.einsum("mhk,qhk->qm", i["W_O"][l], jnp.einsum("hqs,shk->qhk", s, v))
            x = jnp.einsum("dm,qm->qd", i["W_in"][l], rms(r1) * i["G2"][l])
            f = 0.5 * x * (1.0 + jnp.tanh(0.7978845608028654 * (x + 0.044715 * x ** 3)))
            h = r1 + jnp.einsum("md,qd->qm", i["W_out"][l], f)
        return h

    stacks = ("W_Q", "W_K", "W_V", "W_O", "W_in", "W_out", "G1", "G2")
    # name -> (plan output, hand model, loss cotangent shape, numpy model of the SAME scalar output, stacked weights)
    specs = {
        f"conv1d_cnn{sfx}": ("Zc", cnn_hand, (7,), lambda i: np_cnn(i)["Zc"], ()),  # np_cnn pools by the shape-derived 1 / p, not by `Ip`
        f"conv1d_causal{sfx}": ("Out", tcn_hand, (17, 6), lambda i: np_tcn(i)["Out"], ()),
        f"vit_patch{sfx}": ("H", lambda i: vit_hand(i), (5, 4), lambda i: np_vit(i)[1][:, :, 2], stacks),
    }
    lines = []
    for name, (out, hand, c_shape, np_model, stacked) in specs.items():
        fx = by[name]
        sin = {n: lean_array(e) for n, e in fx["inputs"].items()}
        C = np.sin(1.0 + np.arange(int(np.prod(c_shape)))).reshape(c_shape).astype(NDT)
        jin = {n: jnp.asarray(a) for n, a in sin.items()}
        take = (lambda o: o[:, :, 2]) if out == "H" else (lambda o: o)

        def loss_plan(inp, C=C, fx=fx, out=out, take=take):
            return jnp.sum(C * take(rt.run_named(fx["plan"], inp, JDT)[out]))

        def loss_hand(inp, C=C, hand=hand):
            return jnp.sum(C * hand(inp))

        grads = {"eager": jax.grad(loss_plan)(jin), "jit": jax.jit(jax.grad(loss_plan))(jin)}
        g_hand = jax.grad(loss_hand)(jin)
        err = {}
        for who, g in grads.items():
            assert sorted(g) == sorted(sin), (name, who, sorted(g))
            assert all(np.all(np.isfinite(np.asarray(v))) and np.asarray(v).dtype == NDT for v in g.values()), (name, who, "gradient not finite")
            for n, v in g.items():
                if n in stacked:
                    gw = np.asarray(v)
                    assert np.all(gw[2] == 0), (name, "layer-2 weight slice received gradient", who, n)
                    assert all(float(np.max(np.abs(gw[l]))) > 1e-3 for l in (0, 1)), (name, "trivial gradient", who, n)
                else:
                    assert float(np.max(np.abs(np.asarray(v)))) > 1e-3, (name, "trivial gradient", who, n)
                e_ref = scaled(v, g_hand[n])
                assert e_ref < GRAD_TOL[_DT], (f"gradient pin: {name} vs pure-JAX lax.conv model", who, n, e_ref)
                err[n] = max(err.get(n, 0.0), e_ref)
        gx = np.array(grads["eager"]["X" if "Img" not in sin else "Img"])
        gp = gx.copy()
        gp.flat[int(np.argmax(np.abs(gx)))] += NDT(1e-3)  # these gradients are O(0.1), so the test is an ABSOLUTE 1e-3 perturbation
        assert scaled(gp, gx) >= GRAD_TOL[_DT], (name, "gradient tolerance accepts a 1e-3 perturbation: vacuous")
        extra = ""
        if name.startswith("vit_patch"):  # every image position reaches the loss through its patch
            for who, g in grads.items():
                assert np.all(np.max(np.abs(np.asarray(g["Img"])), axis=1) > 0), (name, who, "an Img position has no gradient")
            extra = f"; Img gradient nonzero at all {sin['Img'].shape[0]} positions"
        if name.startswith("conv1d_causal"):  # a loss on outputs 0 .. t: X rows > t get EXACTLY zero gradient, every row <= t a real one
            t, n_l = 8, sin["X"].shape[0]
            c_t = jnp.asarray(C * (np.arange(n_l)[:, None] <= t).astype(NDT))
            rows = {}
            for who, fn in (("eager", lambda i: jnp.sum(c_t * rt.run_named(fx["plan"], i, JDT)["Out"])),
                            ("jit", jax.jit(lambda i: jnp.sum(c_t * rt.run_named(fx["plan"], i, JDT)["Out"])))):
                gxt = np.asarray(jax.grad(fn)(jin)["X"])
                assert np.all(gxt[t + 1:] == 0), (name, who, "X rows after the last loss row received gradient")
                assert np.all(np.max(np.abs(gxt[:t + 1]), axis=1) > 1e-3), (name, who, "an X row up to t has no real gradient", gxt.tolist())
                rows[who] = float(np.min(np.max(np.abs(gxt[:t + 1]), axis=1)))
            g_h = np.asarray(jax.grad(lambda i: jnp.sum(c_t * hand(i)))(jin)["X"])
            assert scaled(gxt, g_h) < GRAD_TOL[_DT] and np.all(g_h[t + 1:] == 0), (name, "causal-prefix gradient differs from the pure-JAX model")
            extra = (f"; loss on outputs 0..{t}: X rows {t + 1}..{n_l - 1} EXACTLY zero gradient (eager and jit and the pure-JAX model), "
                     f"every row 0..{t} real (smallest row max {min(rows.values()):.3f})")
        # (c) directional derivatives against central differences of the float64 numpy model (3 fixed directions over every input)
        base = {n: a.astype(np.float64) for n, a in sin.items()}
        rng = np.random.default_rng(7)
        loss_np = lambda inp, C=C, np_model=np_model: float(np.sum(C.astype(np.float64) * np_model(inp)))
        fd_err, dots = 0.0, []
        for _ in range(3):
            d = {n: rng.standard_normal(a.shape) for n, a in base.items()}
            for w in stacked:
                d[w][2] = 0.0
            if "Ip" in d:  # the numpy model reads no `Ip` (it divides by the shape-derived p): its gradient is pinned against the pure-JAX model only
                d["Ip"] = np.zeros_like(d["Ip"])
            eps = 1e-6
            fd = (loss_np({n: base[n] + eps * d[n] for n in base}) - loss_np({n: base[n] - eps * d[n] for n in base})) / (2 * eps)
            for who, g in grads.items():
                dot = float(sum(np.sum(np.asarray(g[n], dtype=np.float64) * d[n]) for n in base))
                assert abs(dot) > 1e-3, (name, "finite-difference direction is trivial", dot)
                fd_err = max(fd_err, abs(fd - dot) / max(1.0, abs(dot)))
            dots.append(dot)
        assert fd_err < GRAD_FD_TOL[_DT], (f"gradient pin: {name} directional derivative vs finite differences of the numpy model", fd_err)
        lines.append(f"  {name}: all {len(sin)} float inputs, eager and jit, finite and non-trivial; vs pure-JAX lax.conv model max scaled "
                     f"{max(err.values()):.3e} (headroom {GRAD_TOL[_DT] / max(max(err.values()), 1e-300):.1f}x); directional derivatives vs central "
                     f"differences of the numpy model (|dot| {min(abs(x) for x in dots):.2f} to {max(abs(x) for x in dots):.2f}) max scaled {fd_err:.3e} "
                     f"(headroom {GRAD_FD_TOL[_DT] / max(fd_err, 1e-300):.1f}x){extra}")
    print(f"gradients of the convolution fixtures (CNN logits, TCN output, ViT H[:, :, 2]; every float input, tol {GRAD_TOL[_DT]:.0e} vs pure-JAX "
          f"lax.conv models, {GRAD_FD_TOL[_DT]:.0e} vs finite differences):")
    for line in lines:
        print(line)


def np_sigmoid(x):
    return 1.0 / (1.0 + np.exp(-x))


def np_gru(inp: dict, no_update=False, no_reset=False, swap_gate=False, no_recur=False, head_step=6) -> tuple:
    """Float64 model of `rnn_gru` from the exported inputs only, explicit loop over the six time steps (English definition):
    z = sigmoid(Wz x + Uz h + bz), r = sigmoid(Wr x + Ur h + br), n = tanh(Wn x + r * (Un h) + bn), h' = (1 - z) * n + z * h (the minus is
    hard-coded here: the program writes it through the scalar input `Neg`); the head reads the state after `head_step` steps. Returns
    (the exports H [d, 7], Lg [v], Pr [v], the gate values z and r per step)."""
    f = {k: np.asarray(v, dtype=np.float64) for k, v in inp.items()}
    h = f["H0"].copy()
    hist, zs, rs = [h], [], []
    for t in range(6):
        x = f["X"][t]
        zero = np.zeros_like(h)
        z = np_sigmoid(f["Wz"] @ x + (zero if no_recur else f["Uz"] @ h) + f["Bz"])
        r = np_sigmoid(f["Wr"] @ x + (zero if no_recur else f["Ur"] @ h) + f["Br"])
        n = np.tanh(f["Wn"] @ x + (1.0 if no_reset else r) * (zero if no_recur else f["Un"] @ h) + f["Bn"])
        h = n if no_update else (z * n + (1.0 - z) * h if swap_gate else (1.0 - z) * n + z * h)
        hist.append(h)
        zs.append(z)
        rs.append(r)
    lg = f["Wy"] @ hist[head_step]
    return {"H": np.stack(hist, axis=1), "Lg": lg, "Pr": np_softmax_last(lg)}, {"z": np.array(zs), "r": np.array(rs)}


def np_lstm(inp: dict, no_forget=False, no_out=False, old_cell=False, no_cell=False, readout="same") -> tuple:
    """Float64 model of `rnn_lstm` from the exported inputs only, explicit loop over the six steps (English definition): i, f, o = sigmoid(W x + U h + b),
    g = tanh(Wg x + Ug h + bg), c' = f * c + i * g, h' = o * tanh(c'), and the readout Yt[t] = Wy h_t at EVERY t = 0 .. 6. Returns (the exports
    H [d, 7], Cc [d, 7], Yt [7, v], the gate values i, f, o per step)."""
    f = {k: np.asarray(v, dtype=np.float64) for k, v in inp.items()}
    h, c = f["H0"].copy(), f["C0"].copy()
    hs, cs, gates = [h], [c], {"i": [], "f": [], "o": []}
    for t in range(6):
        x = f["X"][t]
        ig = np_sigmoid(f["Wi"] @ x + f["Ui"] @ h + f["Bi"])
        fg = np_sigmoid(f["Wf"] @ x + f["Uf"] @ h + f["Bf"])
        og = np_sigmoid(f["Wo"] @ x + f["Uo"] @ h + f["Bo"])
        gg = np.tanh(f["Wg"] @ x + f["Ug"] @ h + f["Bg"])
        c_new = ig * gg if no_cell else (1.0 if no_forget else fg) * c + ig * gg
        h = (1.0 if no_out else og) * np.tanh(c if old_cell else c_new)
        c = c_new
        hs.append(h)
        cs.append(c)
        gates["i"].append(ig)
        gates["f"].append(fg)
        gates["o"].append(og)
    step = {"same": lambda t: t, "fixed": lambda t: 3, "next": lambda t: min(t + 1, 6)}[readout]
    yt = np.stack([f["Wy"] @ hs[step(t)] for t in range(7)])
    return {"H": np.stack(hs, axis=1), "Cc": np.stack(cs, axis=1), "Yt": yt}, {k: np.array(v) for k, v in gates.items()}


def np_birnn(inp: dict, forward_only=False, backward_only=False, no_reverse=False, swap_final=False, no_back_recur=False) -> dict:
    """Float64 model of `rnn_bi` from the exported inputs only, explicit loop over the six steps (English definition): forward hf' = tanh(Wf x_t + Uf hf)
    over x_0 .. x_5, backward hb' = tanh(Wb x_{5 - t} + Ub hb) (the sequence read from its end), Lg = Wo hf_6 + Wp hb_6. Returns the exports
    Hf [d, 7], Hb [d, 7], Lg [v], Pr [v]."""
    f = {k: np.asarray(v, dtype=np.float64) for k, v in inp.items()}
    hf, hb = f["Hf0"].copy(), f["Hb0"].copy()
    hfs, hbs = [hf], [hb]
    for t in range(6):
        hf = np.tanh(f["Wf"] @ f["X"][t] + f["Uf"] @ hf)
        hb = np.tanh(f["Wb"] @ f["X"][t if no_reverse else 5 - t] + (0.0 if no_back_recur else f["Ub"] @ hb))
        hfs.append(hf)
        hbs.append(hb)
    a, b = (hbs[6], hfs[6]) if swap_final else (hfs[6], hbs[6])
    lg = (0.0 if backward_only else f["Wo"] @ a) + (0.0 if forward_only else f["Wp"] @ b)
    return {"Hf": np.stack(hfs, axis=1), "Hb": np.stack(hbs, axis=1), "Lg": lg, "Pr": np_softmax_last(lg)}


def np_stack(inp: dict, old_state=False, no_recur2=False, no_input2=False, no_recur1=False, swap_out=False) -> dict:
    """Float64 model of `rnn_stack` from the exported inputs only, explicit loop over the six steps (English definition): n1 = tanh(W1 x_t + U1 h1),
    n2 = tanh(W2 n1 + U2 h2), h1' = n1, h2' = n2: layer 2 reads layer 1's NEW state n1 of the SAME step. Returns the exports H1, H2 [d, 7]
    (slot 0 = the initial state). The flags are the wrong models of the non-vacuity gaps."""
    f = {k: np.asarray(v, dtype=np.float64) for k, v in inp.items()}
    h1, h2 = f["H10"].copy(), f["H20"].copy()
    h1s, h2s = [h1], [h2]
    for t in range(6):
        n1 = np.tanh(f["W1"] @ f["X"][t] + (0.0 if no_recur1 else f["U1"] @ h1))
        n2 = np.tanh((0.0 if no_input2 else f["W2"] @ (h1 if old_state else n1)) + (0.0 if no_recur2 else f["U2"] @ h2))
        h1, h2 = n1, n2
        h1s.append(h1)
        h2s.append(h2)
    out = {"H1": np.stack(h1s, axis=1), "H2": np.stack(h2s, axis=1)}
    return {"H1": out["H2"], "H2": out["H1"]} if swap_out else out


def rnn_value_pins(by: dict, name: str, want: dict, wrong: dict) -> dict:
    """Non-vacuity of the numpy reference against each wrong model (> 1e-2, computed BEFORE the view loop so a data mutant fails here and not on a
    value pin), then every export on the Lean, eager and jit views against `want` at MODEL_TOL (check_np records the observed maxima). Returns the gaps."""
    gaps = {what: dict_gap(want, m) for what, m in wrong.items()}
    for what, g in gaps.items():
        assert g > 1e-2, (name, "the recurrent pin is indistinguishable from", what, g)
    for who, outs in conv_views(by, name).items():
        assert sorted(outs) == sorted(want), (name, who, sorted(outs))
        for n in sorted(want):
            check_np(name, who, n, outs[n], want[n])
        if "Pr" in want:
            pr = outs["Pr"].astype(np.float64)
            assert np.all(pr > 0) and abs(float(pr.sum()) - 1.0) < HEAD_ROWSUM_TOL[_DT], (name, who, "Pr is not a probability vector", pr.tolist())
        for n in sorted(want):  # the first state row is the initial state input, bitwise
            init = {"H": "H0", "Cc": "C0", "Hf": "Hf0", "Hb": "Hb0", "H1": "H10", "H2": "H20"}.get(n)
            if init is not None:
                assert np.array_equal(bits(outs[n][:, 0]), bits(lean_array(by[name]["inputs"][init]))), (name, who, n, "slot 0 is not the initial state")
    return gaps


def rnn_gate_ranges(name: str, gates: dict) -> str:
    """Every gate must be non-trivial: its min and max over the six steps and the four units are inside (0.05, 0.95)."""
    for g, v in gates.items():
        assert 0.05 < float(v.min()) and float(v.max()) < 0.95, (name, f"gate {g} is saturated for the chosen data", float(v.min()), float(v.max()))
    return ", ".join(f"{g} in [{float(v.min()):.2f}, {float(v.max()):.2f}]" for g, v in gates.items())


def rnn_plan_pins(fx: dict, kinds_after: list, exports: list) -> None:
    """ONE scan record with six steps, then exactly the stated post-scan nodes, and exactly the stated exports."""
    nodes = fx["plan"]["nodes"]
    assert nodes[0].get("kind") == "scan" and nodes[0]["step_count"] == 6, [n.get("kind") for n in nodes]
    assert [n.get("kind", "assign") for n in nodes[1:]] == kinds_after, [n.get("kind", "assign") for n in nodes]
    assert sorted(m for m, _ in fx["plan"]["materialized"]) == sorted(exports), fx["plan"]["materialized"]


def rnn_spare_slot(name: str, fx: dict) -> None:
    """The NEVER-READ slot: X row 6 is NaN and every export is finite (a step that read it would make the states NaN); setting it to 0.5 leaves
    EVERY export bitwise unchanged on the eager runtime (a step that read it would change the values)."""
    x = lean_array(fx["inputs"]["X"])
    assert np.all(np.isnan(x[6])) and np.all(np.isfinite(x[:6])), (name, "X is not six finite rows and a NaN spare row")
    xs = x.copy()
    xs[6, :] = NDT(0.5)
    base = {n: np.asarray(v) for n, v in EAGER[name]["eager"].items()}
    jin = {n: reconstruct(e) for n, e in fx["inputs"].items()}
    run = rt.run_named(fx["plan"], dict(jin, X=jnp.asarray(xs)), JDT)
    for n, b in base.items():
        assert np.all(np.isfinite(b)) and np.array_equal(bits(b), bits(np.asarray(run[n]))), (name, "export changed when the spare slot X[6] changed", n)


def rnn_causality(name: str, fx: dict, states: dict, heads: tuple = ()) -> str:
    """TIME CAUSALITY on the eager runtime: perturb `X[t]` (t = 0 .. 5). `states` maps an export to (time axis, backward?). A forward state is bitwise
    unchanged at every s <= t and moves at s = t + 1; a BACKWARD state (it has read X[5], .., X[6 - s] after s steps) is bitwise unchanged at every
    s <= 5 - t and moves at s = 6 - t. Every export in `heads` (reads the final state only) moves under every perturbation."""
    base = {n: np.asarray(v) for n, v in EAGER[name]["eager"].items()}
    x = lean_array(fx["inputs"]["X"])
    jin = {n: reconstruct(e) for n, e in fx["inputs"].items()}
    moved = []
    for t in range(6):
        xp = x.copy()
        xp[t, :] += NDT(0.5)
        run = rt.run_named(fx["plan"], dict(jin, X=jnp.asarray(xp)), JDT)
        for n, (axis, backward) in states.items():
            b, p = base[n], np.asarray(run[n])
            first = 6 - t if backward else t + 1
            for s in range(7):
                bs, ps = np.take(b, s, axis=axis), np.take(p, s, axis=axis)
                if s < first:
                    assert np.array_equal(bits(bs), bits(ps)), (name, n, f"slot {s} changed under a perturbation of X[{t}]", first)
                elif s == first:
                    d = float(np.max(np.abs(bs.astype(np.float64) - ps.astype(np.float64))))
                    assert d > 1e-4, (name, n, f"slot {s} did not respond to X[{t}]", d)
                    moved.append(d)
        for n in heads:
            d = float(np.max(np.abs(base[n].astype(np.float64) - np.asarray(run[n]).astype(np.float64))))
            assert d > 1e-4, (name, n, f"did not respond to X[{t}]", d)
    return f"smallest first response {min(moved):.2e}"


def rnn_gru_pins(by: dict, sfx: str) -> None:
    """Pins of `rnn_gru`: a GRU over six time steps (a per-step INPUT read `X[t, i]`, the state read through a renamed axis `Uz[d, e] · H[e, t]`,
    sigmoid and tanh gates, products of per-step intermediates, `1 - z` through the scalar input `Neg = -1`) and a sequence-to-one head `Lg[v] :=
    Wy[v, d] · H[d, 6]` (a PINNED read of the final state) with a softmax. Reference `np_gru`. Value pins on Lean, eager and jit for every export (H over
    all seven slots); non-vacuity against wrong models; gates non-trivial; structure; time causality; the never-read slot."""
    name = f"rnn_gru{sfx}"
    fx = by[name]
    fin = {n: lean_array(e) for n, e in fx["inputs"].items()}
    assert sorted(fin) == sorted(["X", "H0", "Wz", "Uz", "Bz", "Wr", "Ur", "Br", "Wn", "Un", "Bn", "Neg", "Wy"]), sorted(fin)
    rnn_plan_pins(fx, ["assign", "assign", "axiswise"], ["H", "Lg", "Pr"])
    assert fin["Neg"].shape == () and float(fin["Neg"]) == -1.0, fin["Neg"]
    n_t, n_i = fin["X"].shape
    n_d, n_v = fin["H0"].shape[0], fin["Wy"].shape[0]
    ext = {"t": n_t, "i": n_i, "d": n_d, "v": n_v}
    assert len(set(ext.values())) == len(ext) and n_t == fx["plan"]["nodes"][0]["step_count"] + 1, ext
    assert fin["Wz"].shape == (n_d, n_i) and fin["Uz"].shape == (n_d, n_d) and fin["Bz"].shape == (n_d,) and fin["Wy"].shape == (n_v, n_d)
    want, gates = np_gru(fin)
    assert want["H"].shape == (n_d, n_t) and want["Lg"].shape == (n_v,) and want["Pr"].shape == (n_v,)
    gate_txt = rnn_gate_ranges(name, gates)
    wrong = {"update gate removed (h' = n)": np_gru(fin, no_update=True)[0], "reset gate removed": np_gru(fin, no_reset=True)[0],
             "1 - z and z swapped": np_gru(fin, swap_gate=True)[0], "no recurrence (U = 0)": np_gru(fin, no_recur=True)[0],
             "head reads step 5": np_gru(fin, head_step=5)[0]}
    gaps = rnn_value_pins(by, name, want, wrong)
    rnn_spare_slot(name, fx)
    cz = rnn_causality(name, fx, {"H": (1, False)}, heads=("Lg", "Pr"))
    print(f"rnn_gru{sfx}: extents t={n_t}, i={n_i}, d={n_d}, v={n_v} pairwise distinct; plan = ONE scan (step_count 6) then 2 assign + 1 softmax, exactly H, Lg, Pr "
          f"exported; Neg == -1; every export == numpy explicit-loop GRU (English definition) on Lean, eager and jit (H over all {n_t} slots, slot 0 = H0); "
          f"gates {gate_txt}; Pr positive, sums to 1; numpy differs from {', '.join(f'{w} by {g:.3f}' for w, g in gaps.items())}; X[6] NaN spare slot: "
          f"setting it to 0.5 leaves every export bitwise unchanged; causal: X[t] leaves H[:, s] bitwise unchanged for s <= t and moves it at s = t + 1 ({cz}), "
          f"Lg and Pr respond to every X[t]")
    print_conv_stats(name)


def rnn_lstm_pins(by: dict, sfx: str) -> None:
    """Pins of `rnn_lstm`: an LSTM with TWO states (`H`, `Cc`) in one scan, the new cell state routed through the per-step intermediate `Cn` read by both
    updates, and a readout `Yt[t, v] := Wy[v, d] · H[d, t]` at EVERY step after the scan (it keeps the time axis, t = 0 included). Reference
    `np_lstm`. Value pins on Lean, eager and jit; non-vacuity (forget gate ignored, output gate ignored, old cell in the hidden update, no cell state,
    readout at a wrong step); gates non-trivial; structure; time causality of H, Cc and the rows of Yt; the never-read slot."""
    name = f"rnn_lstm{sfx}"
    fx = by[name]
    fin = {n: lean_array(e) for n, e in fx["inputs"].items()}
    assert sorted(fin) == sorted(["X", "H0", "C0"] + [f"{k}{g}" for g in "ifog" for k in "WUB"] + ["Wy"]), sorted(fin)
    rnn_plan_pins(fx, ["assign"], ["H", "Cc", "Yt"])
    n_t, n_i = fin["X"].shape
    n_d, n_v = fin["H0"].shape[0], fin["Wy"].shape[0]
    ext = {"t": n_t, "i": n_i, "d": n_d, "v": n_v}
    assert len(set(ext.values())) == len(ext) and n_t == fx["plan"]["nodes"][0]["step_count"] + 1, ext
    assert fin["C0"].shape == (n_d,) and fin["Ui"].shape == (n_d, n_d) and fin["Wy"].shape == (n_v, n_d)
    want, gates = np_lstm(fin)
    assert want["H"].shape == want["Cc"].shape == (n_d, n_t) and want["Yt"].shape == (n_t, n_v)
    gate_txt = rnn_gate_ranges(name, gates)
    wrong = {"forget gate ignored": np_lstm(fin, no_forget=True)[0], "output gate ignored": np_lstm(fin, no_out=True)[0],
             "hidden update from the OLD cell": np_lstm(fin, old_cell=True)[0], "no cell state (c' = i * g)": np_lstm(fin, no_cell=True)[0],
             "readout at step t + 1": np_lstm(fin, readout="next")[0], "readout at a fixed step": np_lstm(fin, readout="fixed")[0]}
    gaps = rnn_value_pins(by, name, want, wrong)
    for who, outs in conv_views(by, name).items():  # the readout is the product of the exported state with Wy, row by row, on every view
        assert np.max(np.abs(outs["Yt"].astype(np.float64) - outs["H"].astype(np.float64).T @ fin["Wy"].astype(np.float64).T)) < MODEL_TOL[_DT], (name, who)
    rnn_spare_slot(name, fx)
    cz = rnn_causality(name, fx, {"H": (1, False), "Cc": (1, False), "Yt": (0, False)})
    print(f"rnn_lstm{sfx}: extents t={n_t}, i={n_i}, d={n_d}, v={n_v} pairwise distinct; plan = ONE scan (step_count 6) then 1 assign, exactly H, Cc, Yt exported; "
          f"every export == numpy explicit-loop LSTM (English definition) on Lean, eager and jit (slot 0 = H0, C0; Yt has shape [{n_t}, {n_v}] and includes t = 0); "
          f"gates {gate_txt}; numpy differs from {', '.join(f'{w} by {g:.3f}' for w, g in gaps.items())}; X[6] spare slot: setting it to 0.5 leaves "
          f"every export bitwise unchanged; causal: X[t] leaves H, Cc, Yt row s bitwise unchanged for s <= t and moves it at s = t + 1 ({cz})")
    print_conv_stats(name)


def rnn_bi_pins(by: dict, sfx: str) -> None:
    """Pins of `rnn_bi`: a bidirectional tanh-RNN in ONE scan: the forward layer reads `X[t, i]`, the backward layer the REVERSED read `X[5 - t, i]`, and
    the two final states are read by pinned reads in ONE two-term head statement feeding a softmax. Reference `np_birnn`. Value pins on Lean,
    eager and jit; non-vacuity (forward only, backward only, backward NOT reversed, final states swapped, no backward recurrence); structure; time
    causality: the forward state is bitwise unchanged for s <= t and moves at s = t + 1, the BACKWARD state is unchanged for s <= 5 - t and moves at
    s = 6 - t; the never-read slot (the reversed read never touches row 6 either)."""
    name = f"rnn_bi{sfx}"
    fx = by[name]
    fin = {n: lean_array(e) for n, e in fx["inputs"].items()}
    assert sorted(fin) == sorted(["X", "Hf0", "Hb0", "Wf", "Uf", "Wb", "Ub", "Wo", "Wp"]), sorted(fin)
    rnn_plan_pins(fx, ["assign", "assign", "axiswise"], ["Hf", "Hb", "Lg", "Pr"])  # node 1 = Lg (ONE assign node with two terms), node 2 = the softmax operand, then the softmax
    n_t, n_i = fin["X"].shape
    n_d, n_v = fin["Hf0"].shape[0], fin["Wo"].shape[0]
    ext = {"t": n_t, "i": n_i, "d": n_d, "v": n_v}
    assert len(set(ext.values())) == len(ext) and n_t == fx["plan"]["nodes"][0]["step_count"] + 1, ext
    assert fin["Wo"].shape == fin["Wp"].shape == (n_v, n_d) and fin["Ub"].shape == (n_d, n_d)
    want = np_birnn(fin)
    assert want["Hf"].shape == want["Hb"].shape == (n_d, n_t) and want["Lg"].shape == (n_v,)
    assert not np.allclose(want["Hf"], want["Hb"]) and not np.array_equal(fin["Wo"], fin["Wp"])
    wrong = {"forward only": np_birnn(fin, forward_only=True), "backward only": np_birnn(fin, backward_only=True),
             "backward layer NOT reversed": np_birnn(fin, no_reverse=True), "final states swapped": np_birnn(fin, swap_final=True),
             "no backward recurrence (Ub = 0)": np_birnn(fin, no_back_recur=True)}
    gaps = rnn_value_pins(by, name, want, wrong)
    rnn_spare_slot(name, fx)
    cz = rnn_causality(name, fx, {"Hf": (1, False), "Hb": (1, True)}, heads=("Lg", "Pr"))
    print(f"rnn_bi{sfx}: extents t={n_t}, i={n_i}, d={n_d}, v={n_v} pairwise distinct; plan = ONE scan (step_count 6) then 2 assign (Lg with its two terms in one node, the softmax operand) + 1 softmax, "
          f"exactly Hf, Hb, Lg, Pr exported; every export == numpy explicit-loop bidirectional RNN (English definition) on Lean, eager and jit; "
          f"numpy differs from {', '.join(f'{w} by {g:.3f}' for w, g in gaps.items())}; X[6] spare slot: setting it to 0.5 leaves every export bitwise "
          f"unchanged; causal: X[t] leaves Hf[:, s] bitwise unchanged for s <= t and moves it at s = t + 1, leaves Hb[:, s] unchanged for s <= 5 - t and "
          f"moves it at s = 6 - t ({cz})")
    print_conv_stats(name)


def rnn_stack_pins(by: dict, sfx: str) -> None:
    """Pins of `rnn_stack`: a two-layer Elman RNN in ONE scan. Layer 2 reads layer 1's NEW state of the SAME step through the per-step intermediate `N1`
    (`A2[d] := W2[d, e] · N1[e] + U2[d, f] · H2[f, t]`): a within-step dependency between two states. Reference `np_stack`. Value pins on Lean,
    eager and jit for H1 and H2 over all seven slots; non-vacuity (layer 2 reads the OLD h1 [the key one], no recurrence in layer 2, no input to layer 2,
    no recurrence in layer 1, outputs swapped); structure (ONE scan, no post-scan node); the never-read slot. THE WITHIN-STEP DEPENDENCY PIN is the time
    causality: perturbing X[t] leaves H1 and H2 bitwise unchanged for s <= t and BOTH move at s = t + 1 (H2 moves in the SAME step because it reads
    N1); a model whose layer 2 read the old H1 would first move H2 at s = t + 2, so the `moves at s == first` assertion rejects it."""
    name = f"rnn_stack{sfx}"
    fx = by[name]
    fin = {n: lean_array(e) for n, e in fx["inputs"].items()}
    assert sorted(fin) == sorted(["X", "H10", "H20", "W1", "U1", "W2", "U2"]), sorted(fin)
    rnn_plan_pins(fx, [], ["H1", "H2"])
    n_t, n_i = fin["X"].shape
    n_d = fin["H10"].shape[0]
    ext = {"t": n_t, "i": n_i, "d": n_d}
    assert len(set(ext.values())) == len(ext) and n_t == fx["plan"]["nodes"][0]["step_count"] + 1, ext
    assert fin["W1"].shape == (n_d, n_i) and fin["U1"].shape == fin["W2"].shape == fin["U2"].shape == (n_d, n_d) and fin["H20"].shape == (n_d,)
    want = np_stack(fin)
    assert want["H1"].shape == want["H2"].shape == (n_d, n_t)
    assert not np.allclose(want["H1"], want["H2"])
    wrong = {"layer 2 reads the OLD h1": np_stack(fin, old_state=True), "no recurrence in layer 2 (U2 = 0)": np_stack(fin, no_recur2=True),
             "no input to layer 2 (W2 = 0)": np_stack(fin, no_input2=True), "no recurrence in layer 1 (U1 = 0)": np_stack(fin, no_recur1=True),
             "layers' outputs swapped": np_stack(fin, swap_out=True)}
    gaps = rnn_value_pins(by, name, want, wrong)  # the non-vacuity gaps fire first on a zeroed-matrix data mutant
    for w in ("W1", "U1", "W2", "U2"):  # generic weights: no zero entry, so a dropped term or a zeroed matrix is visible
        assert np.all(fin[w] != 0), (name, w, "a weight entry is zero")
    rnn_spare_slot(name, fx)
    cz = rnn_causality(name, fx, {"H1": (1, False), "H2": (1, False)})
    print(f"rnn_stack{sfx}: extents t={n_t}, i={n_i}, d={n_d} pairwise distinct; plan = ONE scan (step_count 6), no post-scan node, exactly H1, H2 exported; "
          f"every export == numpy explicit-loop two-layer RNN (English definition) on Lean, eager and jit (all {n_t} slots, slot 0 = the initial states); "
          f"numpy differs from {', '.join(f'{w} by {g:.3f}' for w, g in gaps.items())}; X[6] spare slot: setting it to 0.5 leaves every export bitwise "
          f"unchanged; WITHIN-STEP dependency: X[t] leaves H1 and H2 bitwise unchanged for s <= t and BOTH move at s = t + 1, H2 in the SAME step "
          f"({cz})")
    print_conv_stats(name)


def rnn_grad_pins(by: dict, sfx: str) -> None:
    """Gradient pins (backpropagation THROUGH TIME) of the three recurrent fixtures: `jax.grad` of `L = sum(C * out)` through the emitted scan over EVERY float
    input (eager and jit), with `out` = the logits `Lg` for the GRU and the bidirectional RNN (not the softmax: a softmax loss is nearly degenerate) and
    `H[:, 6]` together with the per-step readout `Yt` for the LSTM, against (a) the autodiff of a pure-JAX model written from the definition as an unrolled
    Python loop (no plan, no scan, `Neg` read as a plain input) and (b) central finite differences of the float64 numpy models (explicit loops) along
    random directions with `Neg` FROZEN (the numpy models hard-code the minus). X row 6 (never read) has EXACTLY zero gradient, X rows 0 .. 5 a real one
    (information flows back through all six steps), the gradients with respect to the initial states and every weight are non-trivial."""

    def scaled(a, b):
        a, b = np.asarray(a, dtype=np.float64), np.asarray(b, dtype=np.float64)
        return float(np.max(np.abs(a - b) / np.maximum(1.0, np.abs(b))))

    sig = jax.nn.sigmoid

    def gru_hand(i):
        h = i["H0"]
        for t in range(6):
            x = i["X"][t]
            z = sig(i["Wz"] @ x + i["Uz"] @ h + i["Bz"])
            r = sig(i["Wr"] @ x + i["Ur"] @ h + i["Br"])
            n = jnp.tanh(i["Wn"] @ x + r * (i["Un"] @ h) + i["Bn"])
            h = n + i["Neg"] * z * n + z * h  # (1 - z) * n + z * h with the minus through the scalar input Neg
        return [i["Wy"] @ h]

    def lstm_hand(i):
        h, c = i["H0"], i["C0"]
        hs = [h]
        for t in range(6):
            x = i["X"][t]
            ig = sig(i["Wi"] @ x + i["Ui"] @ h + i["Bi"])
            fg = sig(i["Wf"] @ x + i["Uf"] @ h + i["Bf"])
            og = sig(i["Wo"] @ x + i["Uo"] @ h + i["Bo"])
            gg = jnp.tanh(i["Wg"] @ x + i["Ug"] @ h + i["Bg"])
            c = fg * c + ig * gg
            h = og * jnp.tanh(c)
            hs.append(h)
        return [h, jnp.stack([i["Wy"] @ hh for hh in hs])]

    def bi_hand(i):
        hf, hb = i["Hf0"], i["Hb0"]
        for t in range(6):
            hf = jnp.tanh(i["Wf"] @ i["X"][t] + i["Uf"] @ hf)
            hb = jnp.tanh(i["Wb"] @ i["X"][5 - t] + i["Ub"] @ hb)
        return [i["Wo"] @ hf + i["Wp"] @ hb]

    def stack_hand(i):
        h1, h2 = i["H10"], i["H20"]
        for t in range(6):
            n1 = jnp.tanh(i["W1"] @ i["X"][t] + i["U1"] @ h1)
            h2 = jnp.tanh(i["W2"] @ n1 + i["U2"] @ h2)  # layer 2 reads the NEW layer-1 state of the same step
            h1 = n1
        return [h2]

    # name -> (the plan's outputs entering the loss, the pure-JAX model, the numpy model of the SAME outputs)
    specs = {
        f"rnn_gru{sfx}": (lambda r: [r["Lg"]], gru_hand, lambda i: [np_gru(i)[0]["Lg"]]),
        f"rnn_lstm{sfx}": (lambda r: [r["H"][:, 6], r["Yt"]], lstm_hand, lambda i: [np_lstm(i)[0]["H"][:, 6], np_lstm(i)[0]["Yt"]]),
        f"rnn_bi{sfx}": (lambda r: [r["Lg"]], bi_hand, lambda i: [np_birnn(i)["Lg"]]),
        f"rnn_stack{sfx}": (lambda r: [r["H2"][:, 6]], stack_hand, lambda i: [np_stack(i)["H2"][:, 6]]),  # H2 only: W1, U1, H10 reach the loss THROUGH layer 2
    }
    lines = []
    for name, (take, hand, np_model) in specs.items():
        fx = by[name]
        sin = {n: lean_array(e) for n, e in fx["inputs"].items()}
        jin = {n: jnp.asarray(a) for n, a in sin.items()}
        cs = [np.sin(1.0 + np.arange(o.size)).reshape(o.shape).astype(NDT) for o in np_model({n: a.astype(np.float64) for n, a in sin.items()})]

        def loss_plan(inp, cs=cs, fx=fx, take=take):
            return sum(jnp.sum(c * o) for c, o in zip(cs, take(rt.run_named(fx["plan"], inp, JDT))))

        def loss_hand(inp, cs=cs, hand=hand):
            return sum(jnp.sum(c * o) for c, o in zip(cs, hand(inp)))

        grads = {"eager": jax.grad(loss_plan)(jin), "jit": jax.jit(jax.grad(loss_plan))(jin)}
        g_hand = jax.grad(loss_hand)(jin)
        assert np.all(np.asarray(g_hand["X"])[6] == 0), (name, "the pure-JAX model reads X[6]")
        err, smallest = {}, {}
        for who, g in grads.items():
            assert sorted(g) == sorted(sin), (name, who, sorted(g))
            assert all(np.all(np.isfinite(np.asarray(v))) and np.asarray(v).dtype == NDT for v in g.values()), (name, who, "gradient not finite")
            assert np.all(np.asarray(g["X"])[6] == 0), (name, who, "the never-read X row 6 received gradient")
            rows = np.max(np.abs(np.asarray(g["X"])[:6]), axis=1)
            assert np.all(rows > 1e-3), (name, who, "an X row 0 .. 5 has no real gradient: information does not flow back through all six steps", rows.tolist())
            for n, v in g.items():
                smallest[n] = min(smallest.get(n, np.inf), float(np.max(np.abs(np.asarray(v)))))
                assert smallest[n] > 1e-3, (name, "trivial gradient", who, n, smallest[n])
                e_ref = scaled(v, g_hand[n])
                assert e_ref < GRAD_TOL[_DT], (f"gradient pin: {name} vs the pure-JAX unrolled model", who, n, e_ref)
                err[n] = max(err.get(n, 0.0), e_ref)
        gx = np.array(grads["eager"]["X"])
        gp = gx.copy()
        gp.flat[int(np.argmax(np.abs(gx)))] += NDT(1e-3)  # these gradients are O(0.1), so the test is an ABSOLUTE 1e-3 perturbation
        assert scaled(gp, gx) >= GRAD_TOL[_DT], (name, "gradient tolerance accepts a 1e-3 perturbation: vacuous")
        # (b) directional derivatives against central differences of the float64 numpy model (3 fixed directions over every input, Neg frozen)
        base = {n: a.astype(np.float64) for n, a in sin.items()}
        rng = np.random.default_rng(7)
        loss_np = lambda inp, cs=cs, np_model=np_model: float(sum(np.sum(c.astype(np.float64) * o) for c, o in zip(cs, np_model(inp))))
        fd_err, dots = 0.0, []
        for _ in range(3):
            d = {n: rng.standard_normal(a.shape) for n, a in base.items()}
            if "Neg" in d:  # the numpy model hard-codes the minus: the gradient of `Neg` is pinned against the pure-JAX model only
                d["Neg"] = np.zeros_like(d["Neg"])
            d["X"][6] = 0.0
            eps = 1e-6
            fd = (loss_np({n: base[n] + eps * d[n] for n in base}) - loss_np({n: base[n] - eps * d[n] for n in base})) / (2 * eps)
            for who, g in grads.items():
                dot = float(sum(np.sum(np.asarray(g[n], dtype=np.float64) * d[n]) for n in base))
                assert abs(dot) > 1e-3, (name, "finite-difference direction is trivial", dot)
                fd_err = max(fd_err, abs(fd - dot) / max(1.0, abs(dot)))
                dots.append(dot)
        assert fd_err < GRAD_FD_TOL[_DT], (f"gradient pin: {name} directional derivative vs finite differences of the numpy model", fd_err)
        lines.append(f"  {name}: all {len(sin)} float inputs, eager and jit, finite; X row 6 EXACTLY zero gradient (eager, jit and the pure-JAX model), X rows 0..5 and "
                     f"every input non-trivial (smallest per-input max {min(smallest.values()):.3f}); vs pure-JAX unrolled model max scaled {max(err.values()):.3e} "
                     f"(headroom {GRAD_TOL[_DT] / max(max(err.values()), 1e-300):.1f}x); directional derivatives vs central differences of the numpy model "
                     f"(|dot| {min(abs(x) for x in dots):.2f} to {max(abs(x) for x in dots):.2f}, Neg frozen) max scaled {fd_err:.3e} "
                     f"(headroom {GRAD_FD_TOL[_DT] / max(fd_err, 1e-300):.1f}x)")
    print(f"gradients of the recurrent fixtures (GRU logits Lg, LSTM H[:, 6] + Yt, bidirectional logits Lg; every float input, tol {GRAD_TOL[_DT]:.0e} vs pure-JAX "
          f"unrolled models, {GRAD_FD_TOL[_DT]:.0e} vs finite differences):")
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

    # CROSS-ATTENTION to an external memory (unequal extents, unmasked) inside the layer scan, and the hoisting trap of the naive
    # program: see `cross_fixture_pins`.
    cross_fixture_pins(by, sfx)

    # CROSS-ATTENTION to a memory of its own width (e != m): see `cross_wide_pins`.
    cross_wide_pins(by, sfx)

    # 1-D CONVOLUTION (a CNN, a causal TCN block, a patch embedding feeding the layer scan): see `conv_cnn_pins`, `conv_causal_pins`,
    # `vit_patch_pins`.
    conv_cnn_pins(by, sfx)
    conv_causal_pins(by, sfx)
    vit_patch_pins(by, sfx)

    # RECURRENT NETWORKS over a TIME axis (a GRU with a sequence-to-one head, an LSTM with a per-step readout, a bidirectional RNN): see
    # `rnn_gru_pins`, `rnn_lstm_pins`, `rnn_bi_pins`.
    rnn_gru_pins(by, sfx)
    rnn_lstm_pins(by, sfx)
    rnn_bi_pins(by, sfx)
    rnn_stack_pins(by, sfx)

    # GRADIENTS through the emitted scan (`jax.grad`): see `grad_fixture_pins`.
    grad_fixture_pins(by, sfx)

    # GRADIENTS through the other scan fixtures (MQA, masks, GQA): see `fixture_grad_pins`.
    fixture_grad_pins(by, sfx)

    # GRADIENTS through the cross-attention scan, incl. the external memory: see `cross_grad_pins`.
    cross_grad_pins(by, sfx)

    # GRADIENTS through the convolution fixtures (plan vs pure-JAX lax.conv models and finite differences): see `conv_grad_pins`.
    conv_grad_pins(by, sfx)

    # GRADIENTS through the recurrent fixtures (backpropagation through time; plan vs unrolled pure-JAX models and finite differences): see
    # `rnn_grad_pins`.
    rnn_grad_pins(by, sfx)

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
