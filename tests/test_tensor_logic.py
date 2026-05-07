import data_structure.Term as fd
import data_structure.BroadcastedCategory as bc
import data_structure.ProductCategory as pc
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


def test_bc_signature_matrix_multiply_degree():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.degree() == pc.ProdObject((i, j))


def test_bc_signature_matrix_multiply_input_count():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert len(br.input_weaves) == 2
    assert len(br.output_weaves) == 1


def test_bc_signature_w_weave_shape():
    # W[i, k]: i is retained (TILED), k is contracted (concrete)
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.input_weaves[0]._shape == (bc.WeaveMode.TILED, k)


def test_bc_signature_x_weave_shape():
    # X[k, j]: k is contracted (concrete), j is retained (TILED)
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.input_weaves[1]._shape == (k, bc.WeaveMode.TILED)


def test_bc_signature_output_weave_all_tiled():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert all(p is bc.WeaveMode.TILED for p in br.output_weaves[0]._shape)
    assert len(br.output_weaves[0]._shape) == 2  # i, j


def test_bc_signature_operator_is_equation():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.operator is eq


def test_bc_signature_w_reindexing_cod():
    # W contributes degree axis i (pos 0) → cod = (i,)
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.reindexings[0].cod() == pc.ProdObject((i,))


def test_bc_signature_x_reindexing_cod():
    # X contributes degree axis j (pos 1) → cod = (j,)
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.reindexings[1].cod() == pc.ProdObject((j,))


def test_bc_signature_dom_reconstructs_input_shapes():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    dom = br.dom()
    # W shape: (i, k); X shape: (k, j)
    assert dom[0] == bc.Array(bc.Reals(), (i, k))
    assert dom[1] == bc.Array(bc.Reals(), (k, j))


def test_bc_signature_cod_is_output_shape():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    cod = br.cod()
    assert cod[0] == bc.Array(bc.Reals(), (i, j))
