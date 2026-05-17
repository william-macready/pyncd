import data_structure.Term as fd
from data_structure.StrideCategory import RawAxis, StrideMorphism
from data_structure.Numeric import Integer
from data_structure.TensorLogic import TensorEquation, TensorProgram
from data_structure.Operators import Identity, SoftMax
from acset.convert import from_stride_morphism, from_tensor_equation, from_tensor_program
from acset.instances import SStInstance, SBrInstance, OpTag


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


# ── from_tensor_equation ────────────────────────────────────────────────────

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


def test_from_tensor_equation_returns_sbr_instance():
    eq, *_ = _matmul_eq()
    assert isinstance(from_tensor_equation(eq), SBrInstance)


def test_matmul_has_three_arrays():
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert len(inst.arrays) == 3


def test_matmul_output_array_not_input():
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    output = next(a for a in inst.arrays if not a.is_input)
    assert output.name == fd.DynamicName('Y')
    assert output.operator_tag == OpTag.Identity


def test_matmul_contracted_axis_is_target():
    eq, i, j, k = _matmul_eq()
    inst = from_tensor_equation(eq)
    k_rows = [r for r in inst.array_axes if r.axis_uid == k.uid]
    assert len(k_rows) == 2
    assert all(r.is_target for r in k_rows)


def test_matmul_retained_axes_not_target():
    eq, i, j, k = _matmul_eq()
    inst = from_tensor_equation(eq)
    i_rows = [r for r in inst.array_axes if r.axis_uid == i.uid]
    assert all(not r.is_target for r in i_rows)


def test_matmul_samples_count():
    # W contributes i → one sample; X contributes j → one sample
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert len(inst.samples) == 2


def test_matmul_samples_have_unit_coeff():
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert all(s.coeff == Integer(1) for s in inst.samples)


def test_matmul_axis_sizes_contains_all_axes():
    eq, i, j, k = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert i.uid in inst.axis_sizes
    assert j.uid in inst.axis_sizes
    assert k.uid in inst.axis_sizes


def test_softmax_operator_tag():
    i = RawAxis.named('i')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i,),
        rhs=((fd.DynamicName('X'), (i,)),),
        operator=SoftMax(),
    )
    inst = from_tensor_equation(eq)
    output = next(a for a in inst.arrays if not a.is_input)
    assert output.operator_tag == OpTag.SoftMax


# ── from_tensor_program ─────────────────────────────────────────────────────

def _two_equation_program():
    """
    H[i, k] = W1[i, j] X[j, k]
    Y[i, k] = W2[i, m] H[m, k]
    """
    i  = RawAxis.named('i')
    j  = RawAxis.named('j')
    k  = RawAxis.named('k')
    m  = RawAxis.named('m')
    eq1 = TensorEquation(
        lhs_name=fd.DynamicName('H'),
        lhs_indices=(i, k),
        rhs=(
            (fd.DynamicName('W1'), (i, j)),
            (fd.DynamicName('X'),  (j, k)),
        ),
        operator=Identity(),
    )
    eq2 = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i, k),
        rhs=(
            (fd.DynamicName('W2'), (i, m)),
            (fd.DynamicName('H'),  (m, k)),
        ),
        operator=Identity(),
    )
    return TensorProgram(equations=(eq1, eq2)), i, j, k, m


def test_from_tensor_program_returns_list():
    prog, *_ = _two_equation_program()
    result = from_tensor_program(prog)
    assert isinstance(result, list)


def test_from_tensor_program_one_instance_per_equation():
    prog, *_ = _two_equation_program()
    result = from_tensor_program(prog)
    assert len(result) == 2
    assert all(isinstance(r, SBrInstance) for r in result)


def test_from_tensor_program_each_has_three_arrays():
    prog, *_ = _two_equation_program()
    instances = from_tensor_program(prog)
    assert all(len(inst.arrays) == 3 for inst in instances)


def test_from_tensor_program_shared_axis_same_uid():
    prog, i, j, k, m = _two_equation_program()
    instances = from_tensor_program(prog)
    assert i.uid in instances[0].axis_sizes
    assert i.uid in instances[1].axis_sizes
