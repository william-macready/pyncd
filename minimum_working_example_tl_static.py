import data_structure.Category as cat
import data_structure.Numeric as nm
import data_structure.Operators as ops
import data_structure.Term as fd
import display as dpl
import display.node_category as dnc

from data_structure.TensorDSL import (
    TL, axes, norm_axis, nat_axis, real_axis, relu, softmax,
)


# ---------------------------------------------------------------------------
# Shared declaration-axis constructors.
# These carry type and size metadata; equation-level axes are always separate
# axes() calls so the computation graph is unaffected by the declarations.
# ---------------------------------------------------------------------------

def _seq():    return real_axis('p')           # sequence position (variable length, ℝ)
def _d():      return real_axis('d',    512)    # model dim, ℝ₅₁₂
def _d_ff():   return real_axis('d_{ff}', 2048) # FFN hidden dim, ℝ₂₀₄₈
def _h():      return real_axis('h',    8)      # attention heads, ℝ₈
def _k():      return real_axis('k',    64)     # key/value dim per head, ℝ₆₄
def _q():      return real_axis('q')            # query positions (variable, ℝ)
def _x():      return real_axis('x')            # key/value positions (variable, ℝ)


####################
## MATRIX MULTIPLY ##
####################

def matmul():
    tl = TL()
    i_s, j_s, k_s = real_axis('i'), real_axis('j'), real_axis('k')
    tl.W.tensor(i_s, k_s)
    tl.X.tensor(k_s, j_s)
    tl.Y.tensor(i_s, j_s)

    i, j, k = axes('i j k')
    tl.Y[i, j] = tl.W[i, k] * tl.X[k, j]
    return tl.bc_signature()


##########################
## ATTENTION QK MATMUL  ##
##########################

def attention_qk():
    tl = TL()
    tl.Query.tensor(_q(), _h(), _k())
    tl.Key.tensor(_x(), _h(), _k())
    tl.Comp.tensor(_h(), _q(), _x())

    q, h, k = axes('q h k')
    x = norm_axis('x')
    tl.Comp[h, q, x] = softmax(tl.Query[q, h, k] * tl.Key[x, h, k])
    return tl.bc_signature()


######################
## ATTENTION CORE   ##
######################

def attention_core():
    tl_qk = TL()
    tl_qk.Query.tensor(_q(), _h(), _k())
    tl_qk.Key.tensor(_x(), _h(), _k())
    tl_qk.Comp.tensor(_h(), _q(), _x())
    q1, h1, k1, x1 = axes('q h k x')
    tl_qk.Comp[h1, q1, x1] = softmax(tl_qk.Query[q1, h1, k1] * tl_qk.Key[x1, h1, k1])

    tl_sv = TL()
    tl_sv.Comp.tensor(_h(), _q(), _x())
    tl_sv.Value.tensor(_x(), _h(), _k())
    tl_sv.Out.tensor(_q(), _h(), _k())
    q2, h2, k2, x2 = axes('q h k x')
    tl_sv.Out[q2, h2, k2] = tl_sv.Comp[h2, q2, x2] * tl_sv.Value[x2, h2, k2]

    qk   = tl_qk.bc_signature()
    sv   = tl_sv.bc_signature()
    mask = ops.WeightedTriangularLower().template()

    return cat.Block.template(
        qk @ mask @ sv,
        title='Attention Core',
        fill_color='#C5BEDF'
    )


###########
## FFN   ##
###########

def ffn():
    tl = TL()
    tl.X.tensor(_seq(), _d())
    tl.W_in.tensor(_d_ff(), _d())
    tl.Hidden.tensor(_seq(), _d_ff())
    tl.W_out.tensor(_d(), _d_ff())
    tl.Output.tensor(_seq(), _d())

    p1, d1, d_ff1 = axes('p d d_{ff}')
    tl.Hidden[p1, d_ff1] = relu(tl.W_in[d_ff1, d1] * tl.X[p1, d1])

    p2, d2, d_ff2 = axes('p d d_{ff}')
    tl.Output[p2, d2] = tl.W_out[d2, d_ff2] * tl.Hidden[p2, d_ff2]

    return cat.Block.template(
        tl.to_program().to_morphism(),
        title='Feed Forward',
        fill_color='#C1E8F7'
    )


#############################
## ATTENTION MATMUL CHAIN  ##
#############################

def attention_chain():
    tl = TL()
    tl.Query.tensor(_q(), _h(), _k())
    tl.Key.tensor(_x(), _h(), _k())
    tl.Comp.tensor(_h(), _q(), _x())
    tl.Value.tensor(_x(), _h(), _k())
    tl.Out.tensor(_q(), _h(), _k())

    q1, h1, k1, x1 = axes('q h k x')
    tl.Comp[h1, q1, x1] = tl.Query[q1, h1, k1] * tl.Key[x1, h1, k1]

    q2, h2, k2, x2 = axes('q h k x')
    tl.Out[q2, h2, k2] = tl.Comp[h2, q2, x2] * tl.Value[x2, h2, k2]

    return cat.Block.template(
        tl.to_program().to_morphism(),
        title='Attention Matmul Chain',
        fill_color='#C5BEDF'
    )


#################
## TRANSFORMER ##
#################

def res(target: cat.BroadcastedCategory):
    return cat.Block.template(
        (0, 0) @ target @ ops.AdditionOp.template() @ ops.Normalize.template(),
        title='Add \\& Norm',
        fill_color='#F1F4C1'
    )

def attention_layer():
    _attention_core = attention_core()
    Lq = ops.Linear.template(('m',), 2, 'q')
    Lk = ops.Linear.template(('m',), 2, 'k')
    Lv = ops.Linear.template(('m',), 2, 'v')
    Lo = ops.Linear.template(2, ('m',), 'o')
    return (Lq * Lk * Lv) @ _attention_core @ Lo

def transformer_core():
    _attention_layer = attention_layer()
    _ffn_layer = ffn()
    return cat.Block.template(
        res(_attention_layer) @ res(_ffn_layer),
        title='Transformer Layer',
        fill_color='#F3F3F4',
        repetition=nm.Integer(6)
    )

def transformer():
    vocab_size = fd.DynamicName('v', settings=fd.DynamicNameSettings(overline=True))

    # Declare E as a selection tensor: ℕ vocab index → ℝ embedding dim.
    # Decorative only — the gather computation is still expressed via ops.Embedding.
    tl = TL()
    tl.E.selection(nat_axis('v'), _d())

    embedding = cat.Block.template(
        ops.Embedding.template(vocab_size),
        title='Embedding',
        fill_color='#FCE0E1'
    )
    aggregator = cat.Block.template(
        ops.Linear.template(1, (vocab_size,)) @ ops.SoftMax.template(),
        title='Aggregator',
        fill_color='#DBDFEF'
    )
    return embedding @ transformer_core() @ aggregator


# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------

def _render(obj) -> str:
    return dnc.display_category(obj).render()

def verify():
    import minimum_working_example_tl as orig

    cases = [
        ('matmul',            matmul,            orig.matmul),
        ('attention_qk',      attention_qk,      orig.attention_qk),
        ('attention_core',    attention_core,    orig.attention_core),
        ('ffn',               ffn,               orig.ffn),
        ('attention_chain',   attention_chain,   orig.attention_chain),
        ('transformer',       transformer,       orig.transformer),
    ]

    all_ok = True
    for name, static_fn, orig_fn in cases:
        s = _render(static_fn())
        o = _render(orig_fn())
        ok = s == o
        all_ok = all_ok and ok
        print(f"{'PASS' if ok else 'FAIL'}  {name}")
        if not ok:
            # show first differing line
            for i, (ls, lo) in enumerate(zip(s.splitlines(), o.splitlines())):
                if ls != lo:
                    print(f"  line {i}: static={ls!r}")
                    print(f"  line {i}:   orig={lo!r}")
                    break

    print()
    print('All outputs match.' if all_ok else 'MISMATCH detected.')
    return all_ok


if __name__ == '__main__':
    verify()
