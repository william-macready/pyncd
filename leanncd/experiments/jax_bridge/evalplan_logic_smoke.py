"""Independent exact pins for Lean-side max-plus Viterbi and Boolean reachability.

No JAX execution or autodiff is claimed: these scan algebras are still refused by that bridge.
Dyadic log-scores, infinities and Boolean values need no numerical tolerance.
"""
from __future__ import annotations

import importlib.util
import itertools
import math
import struct
import sys
from collections import deque
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Tensor:
    shape: tuple[int, ...]
    data: tuple[float, ...]

    def __getitem__(self, coord):
        if not isinstance(coord, tuple):
            coord = (coord,)
        assert len(coord) == len(self.shape), (self.shape, coord)
        offset = 0
        for i, size in zip(coord, self.shape):
            assert 0 <= i < size, (self.shape, coord)
            offset = offset * size + i
        return self.data[offset]


def decode(env, bits):
    out = {}
    integer, scalar = ("Q", "d") if bits == 64 else ("I", "f")
    for name, entry in env.items():
        shape = tuple(entry["shape"])
        data = tuple(struct.unpack(f"<{scalar}", struct.pack(f"<{integer}", x))[0]
                     for x in entry["bits"])
        assert len(data) == math.prod(shape), (name, shape, len(data))
        out[name] = Tensor(shape, data)
    return out


def viterbi_oracle(inp, *, transpose=False, masked=True, emissions=True, times=False):
    """Enumerate complete state paths, NOT the dynamic-programming recurrence under test."""
    init, trans, emit, allow = (inp[n] for n in ("Init", "Trans", "Emit", "Allow"))
    states, = init.shape
    history, width = emit.shape
    assert width == states and trans.shape == allow.shape == (states, states)
    assert set(allow.data) <= {0.0, 1.0}, "Viterbi transition mask must be Boolean"
    assert all(math.isfinite(x) or x == -math.inf for x in init.data)
    assert all(math.isfinite(x) for x in trans.data + emit.data[:(history - 1) * states])
    best = [[-math.inf] * history for _ in range(states)]
    for t in range(history):
        for path in itertools.product(range(states), repeat=t + 1):
            if masked and any(not allow[a, b] for a, b in zip(path, path[1:])):
                continue
            value = init[path[0]]
            for step, (a, b) in enumerate(zip(path, path[1:])):
                weight = trans[b, a] if transpose else trans[a, b]
                emission = emit[step, b] if emissions else 0.0
                value = value * weight * emission if times else value + weight + emission
            best[path[-1]][t] = max(best[path[-1]][t], value)
    return {"D": Tensor((states, history), tuple(x for row in best for x in row)),
            "Score": Tensor((), (max(row[-1] for row in best),))}


def distances(edge):
    """Directed, unweighted shortest distances by per-source queue-based BFS."""
    nodes, width = edge.shape
    assert width == nodes and set(edge.data) <= {0.0, 1.0}, "Boolean adjacency required"
    out = []
    for source in range(nodes):
        dist = [math.inf] * nodes
        dist[source] = 0
        queue = deque([source])
        while queue:
            i = queue.popleft()
            for j in range(nodes):
                if edge[i, j] and dist[j] == math.inf:
                    dist[j] = dist[i] + 1
                    queue.append(j)
        out.append(dist)
    return out


def reach_oracle(inp):
    edge = inp["Edge"]
    nodes, _ = edge.shape
    dist = distances(edge)
    history = nodes + 1
    return {"Reach": Tensor((nodes, nodes, history),
                            tuple(float(dist[i][j] <= h) for i in range(nodes)
                                  for j in range(nodes) for h in range(history))),
            "Closed": Tensor((nodes, nodes),
                             tuple(float(d <= nodes) for row in dist for d in row))}


def weighted_reach_oracle(inp, *, combine=min):
    """Bottleneck closure by enumerating every walk of length <= h, NOT the recurrence under test.

    The value of a walk is `combine` over its edge weights (min = the Boolean algebra's `·`, which
    never normalises its operands); the empty walk is 1 at i == j. `Reach[i,j,h]` is the max over
    walks of length <= h.
    """
    edge = inp["Edge"]
    nodes, _ = edge.shape
    history = nodes + 1
    best = {}
    for i in range(nodes):
        for j in range(nodes):
            by_length = [1.0 if i == j else 0.0]
            for length in range(1, history):
                top = 0.0
                for mid in itertools.product(range(nodes), repeat=length - 1):
                    path = (i, *mid, j)
                    weights = [edge[a, b] for a, b in zip(path, path[1:])]
                    value = weights[0]
                    for w in weights[1:]:
                        value = combine(value, w)
                    top = max(top, combine(1.0, value))
                by_length.append(top)
            running = 0.0
            for h in range(history):
                running = max(running, by_length[h])
                best[i, j, h] = running
    return {"Reach": Tensor((nodes, nodes, history), tuple(best[i, j, h] for i in range(nodes)
                                                           for j in range(nodes) for h in range(history))),
            "Closed": Tensor((nodes, nodes), tuple(best[i, j, nodes] for i in range(nodes)
                                                   for j in range(nodes)))}


def equal(actual, expected, label):
    assert set(actual) == set(expected), (label, "exports", set(actual), set(expected))
    for name, want in expected.items():
        got = actual[name]
        assert got.shape == want.shape, (label, name, "shape", got.shape, want.shape)
        for index, (a, b) in enumerate(zip(got.data, want.data)):
            assert a == b, (label, name, index, a, b)


def same_bits(a, b):
    return a.shape == b.shape and all(struct.pack("<d", x) == struct.pack("<d", y)
                                     for x, y in zip(a.data, b.data))


def greedy_score(inp):
    init, trans, emit, allow = (inp[n] for n in ("Init", "Trans", "Emit", "Allow"))
    state = max(range(4), key=lambda s: init[s])
    score = init[state]
    for t in range(5):
        nxt = max((s for s in range(4) if allow[state, s]),
                  key=lambda s: trans[state, s] + emit[t, s])
        score += trans[state, nxt] + emit[t, nxt]
        state = nxt
    return score


def viterbi_pins(by):
    base = by["viterbi"]
    inp = base["inputs"]
    expected = viterbi_oracle(inp)
    assert inp["Init"].shape == (4,) and inp["Emit"].shape == (6, 4)
    assert all(math.isnan(x) for x in inp["Emit"].data[20:]), "never-read emission sentinel"
    assert all(expected["D"][3, t] == -math.inf for t in range(6)), "unreachable state"
    assert all(x < 0 for x in expected["D"].data if math.isfinite(x) and x != 0), "negative log scores"
    for name, options in (("transposed transitions", {"transpose": True}),
                          ("missing Boolean mask cast", {"masked": False}),
                          ("missing emissions", {"emissions": False}),
                          ("max-times instead of max-plus", {"times": True})):
        wrong = viterbi_oracle(inp, **options)
        assert wrong["Score"] != expected["Score"], ("indistinguishable Viterbi control", name)
    assert greedy_score(inp) != expected["Score"][()], "must require dynamic programming, not greedy decoding"
    assert max(expected["D"][s, 4] for s in range(4)) != expected["Score"][()], "terminal step pin"
    permutation = (2, 0, 3, 1)
    for view in ("reference", "plan64", "plan32"):
        out = base[view]
        perm = by["viterbi_permuted"][view]
        assert perm["D"] == Tensor((4, 6), tuple(out["D"][s, t] for s in permutation for t in range(6)))
        assert perm["Score"] == out["Score"], (view, "state relabeling")
        for n in out:
            assert same_bits(out[n], by["viterbi_spare"][view][n]), (view, "never-read sentinel", n)
        changed = by["viterbi_changed"][view]["D"]
        assert all(changed[s, t] == out["D"][s, t] for s in range(4) for t in range(3)), (view, "time causality")
        assert changed[1, 3] != out["D"][1, 3], (view, "emission sensitivity")
        assert by["viterbi_changed"][view]["Score"] != out["Score"], (view, "final emission sensitivity")
        shifted = by["viterbi_shifted"][view]
        assert all(shifted["D"][s, t] == out["D"][s, t] + 0.5 * t
                   for s in range(4) for t in range(6)), (view, "additive score gauge")
        assert shifted["Score"][()] == out["Score"][()] + 2.5
        blocked = by["viterbi_blocked"][view]
        assert all(blocked["D"][s, 0] == inp["Init"][s] for s in range(4)), (view, "base case")
        assert all(blocked["D"][s, t] == -math.inf for s in range(4) for t in range(1, 6))
        assert blocked["Score"][()] == -math.inf, (view, "impossible sequence must not be zero")
        assert set(by["viterbi_tied"][view]["D"].data) == {0.0}, (view, "all paths tied")
        assert by["viterbi_tied"][view]["Score"][()] == 0.0
    print("Viterbi: final scores", [expected["D"][s, 5] for s in range(4)],
          "best", expected["Score"][()], "greedy", greedy_score(inp))


def reach_pins(by):
    base = by["reachability"]
    dist = distances(base["inputs"]["Edge"])
    assert dist[0][3] == 2 and dist[0][4] == 3 and dist[4][3] == 2, "diamond, chain and cycle"
    assert dist[0][5] == math.inf and dist[5][0] == math.inf, "isolated node"
    # Ordinary arithmetic would count the two arms of the diamond, rather than produce truth.
    edge = base["inputs"]["Edge"]
    assert sum(edge[0, k] * edge[k, 3] for k in range(6)) == 2
    permutation = (4, 2, 0, 5, 1, 3)
    for view in ("reference", "plan64", "plan32"):
        out = base[view]
        hist, closed = out["Reach"], out["Closed"]
        assert set(hist.data) == {0.0, 1.0} and set(closed.data) == {0.0, 1.0}, (view, "OR, not path count")
        assert all(hist[i, j, h] <= hist[i, j, h + 1] for i in range(6)
                   for j in range(6) for h in range(6)), (view, "at-most-hop monotonicity")
        assert all(hist[i, j, 5] == hist[i, j, 6] for i in range(6) for j in range(6)), (view, "closure fixed point")
        assert all(not (closed[i, k] and closed[k, j]) or closed[i, j]
                   for i in range(6) for j in range(6) for k in range(6)), (view, "transitive")
        assert closed[0, 4] == 1 and closed[4, 0] == 0, (view, "directed, not transposed or undirected")
        assert hist[0, 3, 1] == 0 and hist[0, 3, 2] == 1 and hist[0, 3, 3] == 1, (view, "at most, not exact length")
        perm = by["reachability_permuted"][view]
        assert perm["Reach"] == Tensor((6, 6, 7), tuple(hist[i, j, h] for i in permutation
                                                        for j in permutation for h in range(7))), (view, "node relabeling")
        assert perm["Closed"] == Tensor((6, 6), tuple(closed[i, j] for i in permutation for j in permutation))
        added = by["reachability_added"][view]
        assert all(a <= b for a, b in zip(hist.data, added["Reach"].data)), (view, "edge-addition monotonicity")
        assert added["Reach"][0, 5, 3] == 0 and added["Reach"][0, 5, 4] == 1, (view, "new edge sensitivity")
        for variant in ("empty", "self"):
            result = by[f"reachability_{variant}"][view]
            assert all(result["Reach"][i, j, h] == float(i == j) for i in range(6)
                       for j in range(6) for h in range(7)), (view, variant, "reflexive closure")
        chain = by["reachability_chain"][view]["Reach"]
        assert chain[0, 5, 4] == 0 and chain[0, 5, 5] == chain[0, 5, 6] == 1, (view, "full path length")
    print("Reachability: directed reflexive closure has", int(sum(base["plan64"]["Closed"].data)), "true pairs")


def weighted_reach_pins(by):
    """K3: non-0/1 Edge values through the plan entry points (D6: carried as floats, never cast)."""
    base = by["reachability_weighted"]
    edge = base["inputs"]["Edge"]
    assert set(edge.data) - {0.0, 1.0} == {0.5, 0.25, 0.75, 2.0, 0.125}, "non-0/1 inputs, one above 1"
    expected = weighted_reach_oracle(base["inputs"])
    hard = {"Edge": Tensor(edge.shape, tuple(float(x != 0) for x in edge.data))}
    # Each plausible boundary defect must give a DIFFERENT closure, or the fixture pins nothing.
    assert reach_oracle(hard)["Closed"] != expected["Closed"], "input cast to 0/1 is observable"
    assert weighted_reach_oracle(base["inputs"], combine=lambda a, b: a * b)["Closed"] != expected["Closed"], \
        "product instead of min is observable"
    clipped = {"Edge": Tensor(edge.shape, tuple(max(0.0, min(1.0, x)) for x in edge.data))}
    assert weighted_reach_oracle(clipped)["Reach"] == expected["Reach"], "values above 1 act as 1 (min with Reach)"
    assert expected["Closed"][0, 3] == 0.5, "two arms: min(.5,.75) beats min(.25,2)"
    assert expected["Closed"][2, 3] == 1.0 and expected["Closed"][1, 4] == 0.5
    for view in ("reference", "plan64", "plan32"):
        out = base[view]
        assert set(out["Reach"].data) - {0.0, 1.0} == {0.5, 0.25, 0.75, 0.125}, (view, "fractional history kept")
        assert all(out["Reach"][i, j, h] <= out["Reach"][i, j, h + 1] for i in range(6)
                   for j in range(6) for h in range(6)), (view, "monotone in hops")
        assert out["Reach"][0, 3, 2] == 0.5 and out["Reach"][0, 4, 3] == 0.5, (view, "bottleneck, not product")
    print("Weighted reachability: non-0/1 Edge closure differs from the 0/1-cast and product closures")


def verify(fixtures):
    names = {f"viterbi{s}" for s in ("", "_permuted", "_changed", "_spare", "_shifted", "_blocked", "_tied")}
    names |= {f"reachability{s}" for s in ("", "_permuted", "_added", "_empty", "_chain", "_self", "_weighted")}
    assert len(fixtures) == len(names) and {f["name"] for f in fixtures} == names, "fixture inventory"
    by = {}
    for fixture in fixtures:
        name = fixture["name"]
        inputs = decode(fixture["inputs64"], 64)
        inputs32 = decode(fixture["inputs32"], 32)
        required = {"Init", "Trans", "Emit", "Allow"} if name.startswith("viterbi") else {"Edge"}
        assert set(inputs) == required, (name, "required input inventory", set(inputs), required)
        assert set(inputs) == set(inputs32)
        for n, a in inputs.items():
            b = inputs32[n]
            assert a.shape == b.shape and all(x == y or math.isnan(x) and math.isnan(y)
                                              for x, y in zip(a.data, b.data)), (name, "shared exact inputs", n)
        want = (viterbi_oracle(inputs) if name.startswith("viterbi") else
                weighted_reach_oracle(inputs) if name == "reachability_weighted" else reach_oracle(inputs))
        views = {v: decode(fixture[v], 32 if v == "plan32" else 64)
                 for v in ("reference", "plan64", "plan32")}
        for view, actual in views.items():
            equal(actual, want, (name, view))
        by[name] = {"inputs": inputs, **views}
    viterbi_pins(by)
    reach_pins(by)
    weighted_reach_pins(by)
    print(f"PASS: {len(by)} fixtures x reference/checked64/checked32; every export and history cell exact; no skipped checks")


def main():
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} GENERATED_MODULE")
    spec = importlib.util.spec_from_file_location("logic_fixtures", sys.argv[1])
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load fixtures from {sys.argv[1]}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    verify(module.FIXTURES)


if __name__ == "__main__":
    main()
