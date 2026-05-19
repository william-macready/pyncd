"""Generate CSV serializations of tensor-logic examples into tests/cset_serialization/.

Run once (or re-run after schema changes) to populate the fixture directories used
by test_cset_roundtrip.py.

Examples serialized:
    matmul              Y[i,j] = W[i,k] X[k,j]                       (1 equation)
    attention_qk        Comp[h,q,x] = softmax(Query[q,h,k] Key[x,h,k])  (1 eq, NormAxis)
    attention_core_qk   QK step of attention core                     (1 equation)
    attention_core_sv   score-value step of attention core            (1 equation)
    ffn                 Hidden = relu(W_in X); Output = W_out Hidden  (2 equations)
    attention_chain     Comp = Query Key; Out = Comp Value            (2 equations)

attention_core is split into two separate directories because the two TL sub-programs
use independent declaration axes (Comp is not shared at the TL level; the causal mask
connects them at the BroadcastedCategory level, which is outside TL scope).

transformer is excluded: its TL content is already covered by attention_core_qk/sv
and ffn; the rest (embedding, linear projections, aggregator) is BroadcastedCategory
composition with no TensorProgram representation.
"""
from __future__ import annotations
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from data_structure.TensorDSL import TL, axes, norm_axis, real_axis, softmax, relu
from acset.convert import from_tensor_program
from acset.csv_io import write_sbr

OUT = Path(__file__).parent / 'cset_serialization'


def _seq():
    return real_axis('p')

def _d():
    return real_axis('d', 512)

def _d_ff():
    return real_axis('d_{ff}', 2048)

def _h():
    return real_axis('h', 8)

def _k():
    return real_axis('k', 64)

def _q():
    return real_axis('q')

def _x():
    return real_axis('x')


def _matmul():
    tl = TL()
    i_s, j_s, k_s = real_axis('i'), real_axis('j'), real_axis('k')
    tl.W.tensor(i_s, k_s)
    tl.X.tensor(k_s, j_s)
    tl.Y.tensor(i_s, j_s)
    i, j, k = axes('i j k')
    tl.Y[i, j] = tl.W[i, k] * tl.X[k, j]
    return tl.to_program()


def _attention_qk():
    tl = TL()
    tl.Query.tensor(_q(), _h(), _k())
    tl.Key.tensor(_x(), _h(), _k())
    tl.Comp.tensor(_h(), _q(), _x())
    q, h, k = axes('q h k')
    x = norm_axis('x')
    tl.Comp[h, q, x] = softmax(tl.Query[q, h, k] * tl.Key[x, h, k])
    return tl.to_program()


def _attention_core_qk():
    tl = TL()
    tl.Query.tensor(_q(), _h(), _k())
    tl.Key.tensor(_x(), _h(), _k())
    tl.Comp.tensor(_h(), _q(), _x())
    q, h, k, x = axes('q h k x')
    tl.Comp[h, q, norm_axis('x')] = softmax(tl.Query[q, h, k] * tl.Key[x, h, k])
    return tl.to_program()


def _attention_core_sv():
    tl = TL()
    tl.Comp.tensor(_h(), _q(), _x())
    tl.Value.tensor(_x(), _h(), _k())
    tl.Out.tensor(_q(), _h(), _k())
    q, h, k, x = axes('q h k x')
    tl.Out[q, h, k] = tl.Comp[h, q, x] * tl.Value[x, h, k]
    return tl.to_program()


def _ffn():
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
    return tl.to_program()


def _attention_chain():
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
    return tl.to_program()


_EXAMPLES: list[tuple[str, object]] = [
    ('matmul',             _matmul),
    ('attention_qk',       _attention_qk),
    ('attention_core_qk',  _attention_core_qk),
    ('attention_core_sv',  _attention_core_sv),
    ('ffn',                _ffn),
    ('attention_chain',    _attention_chain),
]


def generate() -> None:
    """Write all examples to tests/cset_serialization/ as CSV directories."""
    OUT.mkdir(parents=True, exist_ok=True)
    for name, build in _EXAMPLES:
        prog = build()
        inst = from_tensor_program(prog)
        dest = OUT / name
        write_sbr(inst, dest)
        n_eq = len(inst.equations)
        n_ax = len(inst.axis_sizes)
        print(f'  {name:<22}  {n_eq} equation(s), {n_ax} axes')
    print(f'\nWrote {len(_EXAMPLES)} examples to {OUT}')


if __name__ == '__main__':
    generate()
