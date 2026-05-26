# Transformer Example

An $L$-layer decoder-only transformer, assuming token embeddings are already
computed. The layer iteration is represented explicitly as a Scan over the layer
axis $\ell$: each step maps the hidden state $H[\ell, x, m]$ to $H[\ell+1, x, m]$
using per-layer weights $W_Q[\ell,\ldots]$, $W_K[\ell,\ldots]$, etc. (untied —
each layer has independent parameters). In the TL DSL, the $\ell$ index on
weights is realised by $L$ independent module instances chained with $@$, one
per layer. Axes and tensor-logic equations are given first; the TL DSL
translation follows.

---

## 1. Mathematical Tensor Logic

### Axes

| Symbol | Role | Typical size |
|---|---|---|
| $\ell$ | layer index | $L$ |
| $x$ | query token position | 512 |
| $x'$ | key/value token position | 512 |
| $m$ | model (embedding) dimension | 512 |
| $h$ | attention head | 8 |
| $k$ | head dimension | 64 |
| $d_{ff}$ | FFN hidden dimension | 2048 |

A trailing dot marks a normalisation axis (softmax or RMSnorm sums over that
index). $[x' \leq x]$ is an Iverson bracket — 1 when the predicate holds, 0
otherwise. The initial hidden state is $H[0, x, m] = X[x, m]$ (the input token
embeddings). The Scan iterates the step function below for $\ell = 0, \ldots, L-1$;
the $L$-layer output is $H[L, x, m]$.

### Attention sub-layer at step $\ell$

**Q, K, V projections** (contract $m$):

$$Q[\ell, x, h, k] = W_Q[\ell, h, k, m]\, H[\ell, x, m]$$
$$K[\ell, x', h, k] = W_K[\ell, h, k, m]\, H[\ell, x', m]$$
$$V[\ell, x', h, k] = W_V[\ell, h, k, m]\, H[\ell, x', m]$$

**QK scores → softmax** (contract $k$, normalise over $x'$):

$$\text{Comp}[\ell, h, x, x'.] = \text{softmax}\!\left(Q[\ell, x, h, k]\, K[\ell, x', h, k]\right)$$

**Causal mask + renormalise** (normalise over $x'$):

$$S[\ell, h, x, x'.] = \text{normalize}\!\left(\text{Comp}[\ell, h, x, x']\, [x' \leq x]\right)$$

**SV aggregation** (contract $x'$):

$$\text{Out}[\ell, x, h, k] = S[\ell, h, x, x']\, V[\ell, x', h, k]$$

**Output projection** (contract $h, k$):

$$\text{Attn}[\ell, x, m] = W_O[\ell, m, h, k]\, \text{Out}[\ell, x, h, k]$$

**Attention residual + RMSnorm** (normalise over $m$):

$$A[\ell, x, m.] = \text{rmsnorm}\!\left(\text{Attn}[\ell, x, m] + H[\ell, x, m]\right)$$

### FFN sub-layer at step $\ell$

**FFN in** — linear then ReLU (contract $m$):

$$F[\ell, x, d_{ff}] = \text{relu}\!\left(W_{\text{in}}[\ell, d_{ff}, m]\, A[\ell, x, m]\right)$$

**FFN out** (contract $d_{ff}$):

$$Y[\ell, x, m] = W_{\text{out}}[\ell, m, d_{ff}]\, F[\ell, x, d_{ff}]$$

### Scan recurrence

**FFN residual + RMSnorm → next hidden state** (normalise over $m$):

$$H[\ell+1, x, m.] = \text{rmsnorm}\!\left(Y[\ell, x, m] + A[\ell, x, m]\right)$$

---

## 2. TL DSL

Every computational step is expressed as a TL equation. When the same external
tensor feeds multiple equations in a program, `TL.to_morphism()` threads it
through the live pool automatically — no structural fork is needed.
`cat.Block.template()` wraps sub-graphs purely for display grouping.

```python
import data_structure.Category as cat
from data_structure.TensorDSL import TL, real_axis, softmax, normalize, relu

# Concrete axis sizes — required for LayerNorm and Iverson materialisation.
SEQ, D, H, K, DFF = 512, 512, 8, 64, 2048

def _m():     return real_axis('m',      D)
def _h():     return real_axis('h',      H)
def _k():     return real_axis('k',      K)
def _d_ff():  return real_axis('d_{ff}', DFF)


# ---------------------------------------------------------------------------
# Attention sub-layer + residual + RMSnorm
# ---------------------------------------------------------------------------
# H is an external tensor referenced in Q/K/V projections and in the final
# residual sum. TL.to_morphism() assigns H a single live-pool slot and routes
# it to every step that needs it.

def attn_res() -> cat.BroadcastedCategory:
    tl = TL()
    q = real_axis('q', SEQ)
    x = real_axis('x', SEQ)   # key/value token position
    m = _m(); h = _h(); k = _k()

    # Q/K/V projections (H threaded to all three)
    tl.Query[q, h, k]   = tl.W_Q[h, k, m] * tl.H[q, m]
    tl.Key[x, h, k]     = tl.W_K[h, k, m] * tl.H[x, m]
    tl.Value[x, h, k]   = tl.W_V[h, k, m] * tl.H[x, m]

    # QK scores → softmax (contract k)
    tl.Comp[h, q, x]    = softmax(tl.Query[q, h, k] * tl.Key[x, h, k])

    # Causal mask + renormalise (sized axes → Iverson auto-materialised)
    tl.S[h, q, x]       = normalize(tl.Comp[h, q, x] * (x <= q))

    # SV aggregation (contract x)
    tl.AttnOut[q, h, k] = tl.S[h, q, x] * tl.Value[x, h, k]

    # Output projection (contract h, k)
    tl.Attn[q, m]       = tl.W_O[m, h, k] * tl.AttnOut[q, h, k]

    # Residual + RMSnorm — H is threaded, no fork needed
    tl.A[q, m]          = normalize(tl.Attn[q, m] + tl.H[q, m])

    return cat.Block.template(
        tl.to_morphism(),
        title='Attention + Add & Norm', fill_color='#F1F4C1',
    )


# ---------------------------------------------------------------------------
# FFN sub-layer + residual + RMSnorm
# ---------------------------------------------------------------------------
# A (the attention output, FFN input) feeds both the FFN computation and the
# residual sum. TL.to_morphism() threads A automatically.

def ffn_res() -> cat.BroadcastedCategory:
    tl = TL()
    q = real_axis('q', SEQ); m = _m(); d = _d_ff()

    tl.F[q, d]   = relu(tl.W_in[d, m] * tl.A[q, m])
    tl.Y[q, m]   = tl.W_out[m, d] * tl.F[q, d]

    # Residual + RMSnorm — A is threaded, no fork needed
    tl.Out[q, m] = normalize(tl.Y[q, m] + tl.A[q, m])

    return cat.Block.template(
        tl.to_morphism(),
        title='FFN + Add & Norm', fill_color='#C1E8F7',
    )


# ---------------------------------------------------------------------------
# Transformer layer (one Scan step)
# ---------------------------------------------------------------------------

def transformer_layer() -> cat.BroadcastedCategory:
    return cat.Block.template(
        attn_res() @ ffn_res(),
        title='Transformer Layer', fill_color='#F3F3F4',
    )


# ---------------------------------------------------------------------------
# Transformer stack: L layers with independent (untied) weight parameters
# ---------------------------------------------------------------------------
# Each call to transformer_layer() allocates a fresh set of TL weight tensors,
# realising the per-layer weights W_Q[l,...], W_K[l,...], ... of the math.
# Chaining with @ composes them into a single morphism H[x,m] → H'[x,m].
#
# Weight-tied variant (same parameters shared across all L steps):
#   tl = TL(); tl.H[x, m, 0] = tl.X[x, m]
#   tl.H.recur(real_axis('l', L), transformer_layer())
#   return tl.to_morphism()

def transformer_stack(L: int) -> cat.BroadcastedCategory:
    from functools import reduce
    layers = reduce(lambda a, b: a @ b, (transformer_layer() for _ in range(L)))
    return cat.Block.template(layers, title='Transformer Stack', fill_color='#F3F3F4')
```

### Iverson predicate notes

`(x <= q)` in a TL equation produces an `IversonBinOp` factor. Two paths:

- **Sized axes** (`real_axis('x', N)`, used here): `bc_signature()` detects
  that all Iverson axes have concrete sizes and **omits the Bool weave from the
  domain entirely** — the predicate is invisible to morphism composition.  At
  compile time, `ConstructedTensorEquation` calls `materialise_iverson` and
  stores the resulting lower-triangular matrix as a named buffer. The caller
  passes only `Comp` — no explicit mask argument.
- **Unsized axes** (`axes('q x')`): the mask cannot be pre-built.  `bc_signature()`
  records a `Bool`-typed domain weave; the caller must supply the materialised
  mask tensor in that input slot.

The Iverson syntax supports `<=`, `<`, `==`, `!=`, `&`, `|`, `iabs(a - b) < c`,
and `ieq(a, b)`. See `data_structure/TensorExpr.py` for the full grammar.
