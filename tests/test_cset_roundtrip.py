"""Round-trip tests for the cset_serialization fixtures.

Each fixture directory under tests/cset_serialization/ was written by
generate_cset_serialization.py. These tests:
  1. Load the CSV back into an SBrInstance.
  2. Rebuild the same TensorProgram from scratch and convert it freshly.
  3. Compare structural properties between the two instances.

Structural equality is checked by _id-based comparison throughout: UID equality
after a CSV round-trip is identity-by-_id, not by the Python object (uid._name
is not preserved — see the note in csv_io._numeric_str).
"""
from __future__ import annotations
from pathlib import Path

import pytest

from data_structure.TensorDSL import TL, axes, norm_axis, real_axis, softmax, relu
from acset.convert import from_tensor_program
from acset.csv_io import read_sbr
from acset.instances import SBrInstance

FIXTURES = Path(__file__).parent / 'cset_serialization'


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _axis_id_set(inst: SBrInstance) -> set[int]:
    return {u._id for u in inst.axis_sizes}


def _concrete_sizes(inst: SBrInstance) -> list[int]:
    """Sorted list of concrete integer axis sizes (FreeNumeric / variable axes excluded)."""
    from data_structure.Numeric import Integer
    return sorted(v._value for v in inst.axis_sizes.values() if isinstance(v, Integer))


def _op_tags(inst: SBrInstance) -> list[str]:
    return sorted(
        str(a.operator_tag) for a in inst.arrays if not a.is_input
    )


def _is_target_pairs(inst: SBrInstance) -> list[tuple[int, int, bool]]:
    return sorted(
        (aa.equation_idx, aa.array_slot, aa.is_target)
        for aa in inst.array_axes
    )


def _sample_pairs(inst: SBrInstance) -> list[tuple[int, int, int]]:
    return sorted(
        (s.equation_idx, s.src_uid._id, s.tgt_uid._id)
        for s in inst.samples
    )


# ---------------------------------------------------------------------------
# Axis helpers (matching generate_cset_serialization.py)
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# Fresh-instance builders (identical to generate_cset_serialization.py)
# ---------------------------------------------------------------------------

def _fresh_matmul() -> SBrInstance:
    tl = TL()
    i_s, j_s, k_s = real_axis('i'), real_axis('j'), real_axis('k')
    tl.W.tensor(i_s, k_s)
    tl.X.tensor(k_s, j_s)
    tl.Y.tensor(i_s, j_s)
    i, j, k = axes('i j k')
    tl.Y[i, j] = tl.W[i, k] * tl.X[k, j]
    return from_tensor_program(tl.to_program())


def _fresh_attention_qk() -> SBrInstance:
    tl = TL()
    tl.Query.tensor(_q(), _h(), _k())
    tl.Key.tensor(_x(), _h(), _k())
    tl.Comp.tensor(_h(), _q(), _x())
    q, h, k = axes('q h k')
    x = norm_axis('x')
    tl.Comp[h, q, x] = softmax(tl.Query[q, h, k] * tl.Key[x, h, k])
    return from_tensor_program(tl.to_program())


def _fresh_attention_core_qk() -> SBrInstance:
    tl = TL()
    tl.Query.tensor(_q(), _h(), _k())
    tl.Key.tensor(_x(), _h(), _k())
    tl.Comp.tensor(_h(), _q(), _x())
    q, h, k, x = axes('q h k x')
    tl.Comp[h, q, norm_axis('x')] = softmax(tl.Query[q, h, k] * tl.Key[x, h, k])
    return from_tensor_program(tl.to_program())


def _fresh_attention_core_sv() -> SBrInstance:
    tl = TL()
    tl.Comp.tensor(_h(), _q(), _x())
    tl.Value.tensor(_x(), _h(), _k())
    tl.Out.tensor(_q(), _h(), _k())
    q, h, k, x = axes('q h k x')
    tl.Out[q, h, k] = tl.Comp[h, q, x] * tl.Value[x, h, k]
    return from_tensor_program(tl.to_program())


def _fresh_ffn() -> SBrInstance:
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
    return from_tensor_program(tl.to_program())


def _fresh_attention_chain() -> SBrInstance:
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
    return from_tensor_program(tl.to_program())


# ---------------------------------------------------------------------------
# Parametrized fixture
# ---------------------------------------------------------------------------

_CASES: list[tuple[str, object]] = [
    ('matmul',             _fresh_matmul),
    ('attention_qk',       _fresh_attention_qk),
    ('attention_core_qk',  _fresh_attention_core_qk),
    ('attention_core_sv',  _fresh_attention_core_sv),
    ('ffn',                _fresh_ffn),
    ('attention_chain',    _fresh_attention_chain),
]


@pytest.fixture(params=_CASES, ids=[name for name, _ in _CASES])
def case(request):
    name, builder = request.param
    loaded = read_sbr(FIXTURES / name)
    fresh  = builder()
    return loaded, fresh


# ---------------------------------------------------------------------------
# Round-trip tests
# ---------------------------------------------------------------------------

def test_equation_count(case):
    loaded, fresh = case
    assert len(loaded.equations) == len(fresh.equations)


def test_array_count(case):
    loaded, fresh = case
    assert len(loaded.arrays) == len(fresh.arrays)


def test_array_axes_count(case):
    loaded, fresh = case
    assert len(loaded.array_axes) == len(fresh.array_axes)


def test_sample_count(case):
    loaded, fresh = case
    assert len(loaded.samples) == len(fresh.samples)


def test_axis_count(case):
    loaded, fresh = case
    assert len(loaded.axis_sizes) == len(fresh.axis_sizes)


def test_integer_sizes_preserved(case):
    """Axes with concrete integer sizes round-trip exactly."""
    loaded, fresh = case
    assert _concrete_sizes(loaded) == _concrete_sizes(fresh)


def test_operator_tags(case):
    loaded, fresh = case
    assert _op_tags(loaded) == _op_tags(fresh)


def test_is_target_flags(case):
    loaded, fresh = case
    assert sorted(aa.is_target for aa in loaded.array_axes) == \
           sorted(aa.is_target for aa in fresh.array_axes)


def test_is_input_flags(case):
    loaded, fresh = case
    assert sorted(a.is_input for a in loaded.arrays) == \
           sorted(a.is_input for a in fresh.arrays)


def test_positions(case):
    loaded, fresh = case
    orig = sorted((aa.equation_idx, aa.array_slot, aa.position) for aa in fresh.array_axes)
    got  = sorted((aa.equation_idx, aa.array_slot, aa.position) for aa in loaded.array_axes)
    assert orig == got


def test_norm_axis_present_iff_expected(case):
    """Output arrays have norm_axis set iff the fresh instance has it set."""
    loaded, fresh = case
    fresh_has  = [a.norm_axis is not None for a in fresh.arrays  if not a.is_input]
    loaded_has = [a.norm_axis is not None for a in loaded.arrays if not a.is_input]
    assert sorted(fresh_has) == sorted(loaded_has)


def test_datatype_tags(case):
    loaded, fresh = case
    assert sorted(str(a.datatype_tag) for a in loaded.arrays) == \
           sorted(str(a.datatype_tag) for a in fresh.arrays)
