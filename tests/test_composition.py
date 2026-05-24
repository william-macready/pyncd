import pytest
import data_structure.Term as fd
import data_structure.BroadcastedCategory as bc
import data_structure.ProductCategory as pc
from data_structure.StrideCategory import RawAxis
from construction_helpers.composition import align_axes


def _po(*arrays):
    return pc.ProdObject(content=tuple(arrays))


def _array(datatype, *axes):
    return bc.Array(datatype=datatype, _shape=axes)


# ---------------------------------------------------------------------------
# Matching datatypes — should pass
# ---------------------------------------------------------------------------

def test_reals_reals_passes():
    ax = RawAxis.named('i')
    ctx = fd.Context()
    align_axes(
        _po(_array(bc.Reals(), ax)),
        _po(_array(bc.Reals(), ax)),
        ctx,
    )


def test_bool_bool_passes():
    ax = RawAxis.named('i')
    ctx = fd.Context()
    align_axes(
        _po(_array(bc.Bool(), ax)),
        _po(_array(bc.Bool(), ax)),
        ctx,
    )


def test_natural_natural_passes():
    import data_structure.Numeric as nm
    ax = RawAxis.named('i')
    nat = bc.Natural(nm.Integer(10))
    ctx = fd.Context()
    align_axes(
        _po(_array(nat, ax)),
        _po(_array(nat, ax)),
        ctx,
    )


# ---------------------------------------------------------------------------
# Mismatched datatypes — should raise TypeError
# ---------------------------------------------------------------------------

def test_bool_into_reals_raises():
    ax = RawAxis.named('i')
    ctx = fd.Context()
    with pytest.raises(TypeError, match="Datatype mismatch"):
        align_axes(
            _po(_array(bc.Bool(), ax)),
            _po(_array(bc.Reals(), ax)),
            ctx,
        )


def test_reals_into_bool_raises():
    ax = RawAxis.named('i')
    ctx = fd.Context()
    with pytest.raises(TypeError, match="Datatype mismatch"):
        align_axes(
            _po(_array(bc.Reals(), ax)),
            _po(_array(bc.Bool(), ax)),
            ctx,
        )


def test_natural_into_reals_raises():
    import data_structure.Numeric as nm
    ax = RawAxis.named('i')
    nat = bc.Natural(nm.Integer(10))
    ctx = fd.Context()
    with pytest.raises(TypeError, match="Datatype mismatch"):
        align_axes(
            _po(_array(nat, ax)),
            _po(_array(bc.Reals(), ax)),
            ctx,
        )


def test_reals_into_natural_raises():
    import data_structure.Numeric as nm
    ax = RawAxis.named('i')
    nat = bc.Natural(nm.Integer(10))
    ctx = fd.Context()
    with pytest.raises(TypeError, match="Datatype mismatch"):
        align_axes(
            _po(_array(bc.Reals(), ax)),
            _po(_array(nat, ax)),
            ctx,
        )


# ---------------------------------------------------------------------------
# Error message content
# ---------------------------------------------------------------------------

def test_error_names_both_datatypes():
    ax = RawAxis.named('i')
    ctx = fd.Context()
    with pytest.raises(TypeError) as exc_info:
        align_axes(
            _po(_array(bc.Bool(), ax)),
            _po(_array(bc.Reals(), ax)),
            ctx,
        )
    msg = str(exc_info.value)
    assert "Bool" in msg
    assert "Reals" in msg
