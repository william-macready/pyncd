"""Tests for acset.convert: from_stride_morphism, from_tensor_equation, from_tensor_program."""

import data_structure.Term as fd
import data_structure.BroadcastedCategory as bc
from data_structure.StrideCategory import RawAxis, StrideMorphism
from data_structure.Numeric import Integer
from data_structure.TensorLogic import TensorEquation, TensorProgram
from data_structure.Operators import Identity, SoftMax, Linear, Elementwise
from data_structure.TensorLogic import NormAxis
from acset.convert import from_stride_morphism, from_tensor_equation, from_tensor_program
from acset.instances import SStInstance, SBrInstance, OpTag, DataTag


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
    """from_stride_morphism returns an SStInstance."""
    result = from_stride_morphism(_identity_morphism())
    assert isinstance(result, SStInstance)


def test_identity_morphism():
    """from_matrix creates fresh dom/cod axes; axis_sizes has 2 entries, entries has 1 row."""
    m = _identity_morphism()
    inst = from_stride_morphism(m)
    assert len(inst.axis_sizes) == 2
    assert len(inst.entries) == 1
    assert inst.entries[0].coeff == Integer(1)


def test_duplication_has_three_axes():
    """dom: p; cod: p0, p1 — three distinct axes, two entry rows."""
    inst = from_stride_morphism(_duplication_morphism())
    assert len(inst.axis_sizes) == 3
    assert len(inst.entries) == 2
    for e in inst.entries:
        assert e.coeff == Integer(1)


def test_conv_shift_entries():
    """(x', w) → (x,): two entries, both coeff=1."""
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
    """from_tensor_equation returns an SBrInstance."""
    eq, *_ = _matmul_eq()
    assert isinstance(from_tensor_equation(eq), SBrInstance)


def test_matmul_has_three_arrays():
    """Matmul equation produces three Array rows (Y, W, X)."""
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert len(inst.arrays) == 3


def test_matmul_output_array_not_input():
    """Output array Y is is_input=False with Identity operator_tag."""
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    output = next(a for a in inst.arrays if not a.is_input)
    assert output.name == fd.DynamicName('Y')
    assert output.operator_tag == OpTag.IDENTITY


def test_matmul_contracted_axis_is_target():
    """Contracted axis k appears in two ArrayAxis rows, both is_target=True."""
    eq, _i, _j, k = _matmul_eq()
    inst = from_tensor_equation(eq)
    k_rows = [r for r in inst.array_axes if r.axis_uid == k.uid]
    assert len(k_rows) == 2
    assert all(r.is_target for r in k_rows)


def test_matmul_retained_axes_not_target():
    """Retained axis i appears only in is_target=False rows."""
    eq, i, _j, _k = _matmul_eq()
    inst = from_tensor_equation(eq)
    i_rows = [r for r in inst.array_axes if r.axis_uid == i.uid]
    assert all(not r.is_target for r in i_rows)


def test_matmul_samples_count():
    """W contributes i → one sample; X contributes j → one sample."""
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert len(inst.samples) == 2


def test_matmul_samples_have_unit_coeff():
    """All TensorEquation samples have coeff=1 (identity reindexing)."""
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert all(s.coeff == Integer(1) for s in inst.samples)


def test_matmul_axis_sizes_contains_all_axes():
    """axis_sizes contains UIDs for all three axes i, j, k."""
    eq, i, j, k = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert i.uid in inst.axis_sizes
    assert j.uid in inst.axis_sizes
    assert k.uid in inst.axis_sizes


def test_matmul_output_positions():
    """Y[i,j]: lhs_indices=(i,j), so ya_i→position 0, ya_j→position 1."""
    eq, i, j, _k = _matmul_eq()
    inst = from_tensor_equation(eq)
    output_rows = {r.axis_uid: r.position for r in inst.array_axes if r.array_name == eq.lhs_name}
    assert output_rows[i.uid] == 0
    assert output_rows[j.uid] == 1


def test_matmul_input_positions():
    """W[i,k]: i→0, k→1; X[k,j]: k→0, j→1."""
    eq, i, j, k = _matmul_eq()
    inst = from_tensor_equation(eq)
    w_name = fd.DynamicName('W')
    x_name = fd.DynamicName('X')
    w_rows = {r.axis_uid: r.position for r in inst.array_axes if r.array_name == w_name}
    x_rows = {r.axis_uid: r.position for r in inst.array_axes if r.array_name == x_name}
    assert w_rows[i.uid] == 0
    assert w_rows[k.uid] == 1
    assert x_rows[k.uid] == 0
    assert x_rows[j.uid] == 1


def test_softmax_operator_tag():
    """SoftMax operator maps to OpTag.SOFTMAX; norm_axis points to the NormAxis UID."""
    i = NormAxis.named('i')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i,),
        rhs=((fd.DynamicName('X'), (i,)),),
        operator=SoftMax(),
    )
    inst = from_tensor_equation(eq)
    output = next(a for a in inst.arrays if not a.is_input)
    assert output.operator_tag == OpTag.SOFTMAX
    assert output.norm_axis == i.uid


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
    """from_tensor_program returns a list."""
    prog, *_ = _two_equation_program()
    result = from_tensor_program(prog)
    assert isinstance(result, list)


def test_from_tensor_program_one_instance_per_equation():
    """Two-equation program produces two SBrInstances."""
    prog, *_ = _two_equation_program()
    result = from_tensor_program(prog)
    assert len(result) == 2
    assert all(isinstance(r, SBrInstance) for r in result)


def test_from_tensor_program_each_has_three_arrays():
    """Each equation in the two-equation program has three Array rows."""
    prog, *_ = _two_equation_program()
    instances = from_tensor_program(prog)
    assert all(len(inst.arrays) == 3 for inst in instances)


def test_from_tensor_program_shared_axis_same_uid():
    """Axis i appears in both instances under the same UID."""
    prog, i, *_ = _two_equation_program()
    instances = from_tensor_program(prog)
    assert i.uid in instances[0].axis_sizes
    assert i.uid in instances[1].axis_sizes


# ── array_datatypes parameter ────────────────────────────────────────────────

def _embedding_eq():
    """Y[i] = E[i] where E has a Natural (vocabulary) input."""
    i = RawAxis.named('i')
    return TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i,),
        rhs=((fd.DynamicName('E'), (i,)),),
        operator=Identity(),
    ), i


def test_default_datatype_tag_is_reals():
    """Without array_datatypes, all arrays default to DataTag.REALS."""
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert all(a.datatype_tag == DataTag.REALS for a in inst.arrays)


def test_natural_datatype_tag():
    """Supplying a Natural datatype sets DataTag.NATURAL and max_value on that array."""
    eq, i = _embedding_eq()
    vocab_size = Integer(32000)
    datatypes = {fd.DynamicName('E'): bc.Natural(max_value=vocab_size)}
    inst = from_tensor_equation(eq, array_datatypes=datatypes)
    e_row = next(a for a in inst.arrays if a.name == fd.DynamicName('E'))
    assert e_row.datatype_tag == DataTag.NATURAL
    assert e_row.max_value == vocab_size


def test_output_datatype_tag_from_caller():
    """Output array datatype_tag is set when output name is in array_datatypes."""
    eq, i = _embedding_eq()
    datatypes = {fd.DynamicName('Y'): bc.Reals()}
    inst = from_tensor_equation(eq, array_datatypes=datatypes)
    y_row = next(a for a in inst.arrays if a.name == fd.DynamicName('Y'))
    assert y_row.datatype_tag == DataTag.REALS


def test_linear_bias_true():
    """Linear(bias=True) operator sets bias=True on output ArrayRow."""
    i = RawAxis.named('i')
    j = RawAxis.named('j')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i,),
        rhs=((fd.DynamicName('W'), (i, j)),),
        operator=Linear(bias=True),
    )
    inst = from_tensor_equation(eq)
    output = next(a for a in inst.arrays if not a.is_input)
    assert output.bias is True


def test_linear_bias_false():
    """Linear(bias=False) operator sets bias=False on output ArrayRow."""
    i = RawAxis.named('i')
    j = RawAxis.named('j')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i,),
        rhs=((fd.DynamicName('W'), (i, j)),),
        operator=Linear(bias=False),
    )
    inst = from_tensor_equation(eq)
    output = next(a for a in inst.arrays if not a.is_input)
    assert output.bias is False


def test_elementwise_fn_stored():
    """Elementwise operator stores the function name in elementwise_fn."""
    i = RawAxis.named('i')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i,),
        rhs=((fd.DynamicName('X'), (i,)),),
        operator=Elementwise(operator='relu'),
    )
    inst = from_tensor_equation(eq)
    output = next(a for a in inst.arrays if not a.is_input)
    assert output.elementwise_fn == 'relu'


def test_identity_has_no_elementwise_fn():
    """Identity (subclass of Elementwise) does not set elementwise_fn."""
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    output = next(a for a in inst.arrays if not a.is_input)
    assert output.elementwise_fn is None


def test_non_natural_arrays_have_no_max_value():
    """Arrays without a Natural datatype have max_value=None."""
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert all(a.max_value is None for a in inst.arrays)
