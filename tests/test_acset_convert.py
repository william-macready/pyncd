import data_structure.Term as fd
from data_structure.StrideCategory import RawAxis, StrideMorphism
from data_structure.Numeric import Integer
from acset.convert import from_stride_morphism
from acset.instances import SStInstance, EntryRow


def _identity_morphism():
    """Identity on one axis: (p,) → (p,) with coeff=1."""
    return StrideMorphism.from_matrix(
        (1,), dom_names=('p',), cod_names=('p',)
    )

def _duplication_morphism():
    """Duplication: (p,) → (p0, p1) each coeff=1."""
    return StrideMorphism.from_matrix(
        (1,), (1,), dom_names=('p',), cod_names=('p0', 'p1')
    )

def _conv_shift_morphism():
    """Convolution shift: (x', w) → (x,) coeffs=(1,1)."""
    return StrideMorphism.from_matrix(
        (1, 1), dom_names=("x'", 'w'), cod_names=('x',), name='+'
    )


def test_from_stride_morphism_returns_sstinstance():
    result = from_stride_morphism(_identity_morphism())
    assert isinstance(result, SStInstance)


def test_identity_morphism():
    # from_matrix creates fresh dom and cod axes even with the same name,
    # so axis_sizes has 2 entries (one per distinct UID); entries has 1 row.
    m = _identity_morphism()
    inst = from_stride_morphism(m)
    assert len(inst.axis_sizes) == 2
    assert len(inst.entries) == 1
    assert inst.entries[0].coeff == Integer(1)


def test_duplication_has_three_axes():
    # dom: p; cod: p0, p1 — three distinct axes, two entry rows
    inst = from_stride_morphism(_duplication_morphism())
    assert len(inst.axis_sizes) == 3
    assert len(inst.entries) == 2
    for e in inst.entries:
        assert e.coeff == Integer(1)


def test_conv_shift_entries():
    # (x', w) → (x,): two entries, both coeff=1
    inst = from_stride_morphism(_conv_shift_morphism())
    assert len(inst.entries) == 2
    assert all(e.coeff == Integer(1) for e in inst.entries)
