import data_structure.Term as fd
from data_structure.TensorLogic import NormAxis, TensorEquation
from data_structure.StrideCategory import RawAxis, Axis
from data_structure.Operators import Identity, SoftMax


def test_norm_axis_is_rawaxis_subclass():
    ax = NormAxis()
    assert isinstance(ax, RawAxis)


def test_norm_axis_named_returns_norm_axis():
    ax = NormAxis.named('t')
    assert isinstance(ax, NormAxis)


def test_norm_axis_distinct_from_raw_axis():
    assert NormAxis is not RawAxis
    assert not isinstance(RawAxis(), NormAxis)


def _matmul_eq():
    """Y[i,j] = W[i,k] X[k,j]"""
    i = RawAxis.named('i')
    j = RawAxis.named('j')
    k = RawAxis.named('k')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i, j),
        rhs=(
            (fd.DynamicName('W'), (i, k)),
            (fd.DynamicName('X'), (k, j)),
        ),
        operator=Identity(),
    )
    return eq, i, j, k


def test_tensor_equation_construction():
    eq, i, j, k = _matmul_eq()
    assert eq.lhs_name == fd.DynamicName('Y')
    assert len(eq.lhs_indices) == 2
    assert len(eq.rhs) == 2


def test_retained_uids_contains_lhs_indices():
    eq, i, j, k = _matmul_eq()
    retained = eq.retained_uids()
    assert i.uid in retained
    assert j.uid in retained
    assert k.uid not in retained


def test_contracted_axes_are_rhs_only():
    eq, i, j, k = _matmul_eq()
    contracted = eq.contracted_axes()
    assert len(contracted) == 1
    assert contracted[0].uid == k.uid


def test_tensor_equation_with_norm_axis():
    b = RawAxis.named('b')
    p = RawAxis.named('p')
    d = RawAxis.named('d')
    t = NormAxis.named('t')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(b, p, t),
        rhs=(
            (fd.DynamicName('W_O'), (t, d)),
            (fd.DynamicName('Stream'), (b, p, d)),
        ),
        operator=SoftMax(),
    )
    retained = eq.retained_uids()
    assert t.uid in retained
    assert d.uid not in retained
    contracted = eq.contracted_axes()
    assert any(ax.uid == d.uid for ax in contracted)
