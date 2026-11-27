"""Independent plain-Python expected values for the step-aware mask pins (no Lean, no numpy).

Each program is evaluated by direct simulation of its scan: at step `t` the mask sees the LIVE
step coordinate. Masked entries leave both the softmax max and sum; an all-masked row is zeros.
"""
import math


def softmax_masked(xs, keep):
    live = [x for x, k in zip(xs, keep) if k]
    if not live:
        return [0.0] * len(xs)
    m = max(live)
    den = sum(math.exp(x - m) for x in live)
    return [math.exp(x - m) / den if k else 0.0 for x, k in zip(xs, keep)]


def show(name, rows):
    flat = [v for r in rows for v in r]
    print(name, "[" + ", ".join(repr(v) for v in flat) + "]")


# (i) per-step intermediate: iter l = 4, S[j,0] := X[j]; Pa[j.] := softmax(where j <= l)(S[j,l]);
#     S[j,l+1] := Pa[j].  X = [0,0,0].  Output S[j][l], shape [3,4].
X = [0.0, 0.0, 0.0]
cols = [X]
for l in range(3):
    cols.append(softmax_masked(cols[-1], [j <= l for j in range(3)]))
show("inter S[3,4]", [[cols[l][j] for l in range(4)] for j in range(3)])
# what a ctx-0 reading would give
c0 = [X]
for l in range(3):
    c0.append(softmax_masked(c0[-1], [j <= 0 for j in range(3)]))
show("inter ctx0", [[c0[l][j] for l in range(4)] for j in range(3)])

# (ii) step statement: iter l = 4, S[j,0] := X[j]; S[j., l+1] := softmax(where l <= 1)(S[j,l]).
#      X = [0, ln 3].  Output S[j][l], shape [2,4].
X2 = [0.0, math.log(3.0)]
cols = [X2]
for l in range(3):
    cols.append(softmax_masked(cols[-1], [l <= 1] * 2))
show("step S[2,4]", [[cols[l][j] for l in range(4)] for j in range(2)])

# (iii)/(iv) slot-cache attention: iter t = 4, 3 slots, k = 2.
Kn = [[1.0, 0.0], [0.0, 1.0], [1.0, 1.0], [0.0, 0.0]]
Qr = [[1.0, 0.0], [2.0, 1.0], [1.0, -1.0], [0.0, 0.0]]


def kv(keep_fn):
    Kc = [[0.0, 0.0] for _ in range(3)]
    Yh = [[0.0] * 3]
    for t in range(3):
        Kw = [[Kc[s][k] + (1.0 if s == t else 0.0) * Kn[t][k] for k in range(2)] for s in range(3)]
        sc = [sum(Kw[s][k] * Qr[t][k] for k in range(2)) for s in range(3)]
        Yh.append(softmax_masked(sc, [keep_fn(s, t) for s in range(3)]))
        Kc = Kw
    return [[Yh[t][s] for t in range(4)] for s in range(3)]


show("kv causal Yh[3,4]", kv(lambda s, t: s <= t))
show("kv window Yh[3,4]", kv(lambda s, t: s <= t and s > t - 2))
show("kv causal ctx0", kv(lambda s, t: s <= 0))

# (b) plan-level block: X[ctx, o] read, then softmax over o with mask `o <= ctx`, X = [[1,2,3],[4,5,6]].
Xb = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]]
for c in (0, 1):
    print("block ctx", c, softmax_masked(Xb[c], [o <= c for o in range(3)]))
