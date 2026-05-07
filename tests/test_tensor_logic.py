import sys
sys.path.insert(0, '.')

from data_structure.TensorLogic import NormAxis
from data_structure.StrideCategory import RawAxis, Axis


def test_norm_axis_is_rawaxis_subclass():
    ax = NormAxis()
    assert isinstance(ax, RawAxis)


def test_norm_axis_named_returns_norm_axis():
    ax = NormAxis.named('t')
    assert isinstance(ax, NormAxis)


def test_norm_axis_distinct_from_raw_axis():
    assert NormAxis is not RawAxis
    assert not isinstance(RawAxis(), NormAxis)
