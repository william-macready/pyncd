import data_structure.Term as fd
import data_structure.BroadcastedCategory as bc
import data_structure.ProductCategory as pc
from data_structure.TensorLogic import NormAxis, TensorEquation, TensorProgram, _topological_sort
from data_structure.ProductCategory import Composed
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


def _chain_equations():
    """eq1: Hidden[i,j] = W1[i,k] X[k,j];  eq2: Y[i,m] = W2[i,j] Hidden[j,m]"""
    i = RawAxis.named('i')
    j = RawAxis.named('j')
    k = RawAxis.named('k')
    eq1 = TensorEquation(
        lhs_name=fd.DynamicName('Hidden'),
        lhs_indices=(i, j),
        rhs=(
            (fd.DynamicName('W1'), (i, k)),
            (fd.DynamicName('X'), (k, j)),
        ),
        operator=Identity(),
    )
    m = RawAxis.named('m')
    eq2 = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i, m),
        rhs=(
            (fd.DynamicName('W2'), (i, j)),
            (fd.DynamicName('Hidden'), (j, m)),
        ),
        operator=Identity(),
    )
    return eq1, eq2


def test_topological_sort_already_ordered():
    eq1, eq2 = _chain_equations()
    result = _topological_sort((eq1, eq2))
    assert result[0] is eq1
    assert result[1] is eq2


def test_topological_sort_reversed_input():
    eq1, eq2 = _chain_equations()
    result = _topological_sort((eq2, eq1))
    assert result[0] is eq1
    assert result[1] is eq2


def test_tensor_program_single_equation():
    i = RawAxis.named('i')
    k = RawAxis.named('k')
    j = RawAxis.named('j')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i, j),
        rhs=(
            (fd.DynamicName('W'), (i, k)),
            (fd.DynamicName('X'), (k, j)),
        ),
        operator=Identity(),
    )
    prog = TensorProgram(equations=(eq,))
    morphism = prog.to_morphism()
    assert isinstance(morphism, Composed)
    assert len(morphism.content) == 1


def test_tensor_program_two_equation_chain():
    """Two equations in sequence; to_morphism() produces a Composed of length 2."""
    i = RawAxis.named('i')
    k = RawAxis.named('k')
    j = RawAxis.named('j')
    eq1 = TensorEquation(
        lhs_name=fd.DynamicName('Hidden'),
        lhs_indices=(i, j),
        rhs=(
            (fd.DynamicName('W1'), (i, k)),
            (fd.DynamicName('X'), (k, j)),
        ),
        operator=Identity(),
    )
    # eq2 uses fresh axes that will be unified with eq1's lhs_indices
    i2 = RawAxis.named('i')
    j2 = RawAxis.named('j')
    m = RawAxis.named('m')
    eq2 = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i2, m),
        rhs=(
            (fd.DynamicName('W2'), (i2, j2)),
            (fd.DynamicName('Hidden'), (j2, m)),
        ),
        operator=Identity(),
    )
    prog = TensorProgram(equations=(eq1, eq2))
    morphism = prog.to_morphism()
    assert isinstance(morphism, Composed)
    assert len(morphism.content) == 2


def test_tensor_program_cod_has_correct_rank():
    i = RawAxis.named('i')
    k = RawAxis.named('k')
    j = RawAxis.named('j')
    eq1 = TensorEquation(
        lhs_name=fd.DynamicName('Hidden'),
        lhs_indices=(i, j),
        rhs=(
            (fd.DynamicName('W1'), (i, k)),
            (fd.DynamicName('X'), (k, j)),
        ),
        operator=Identity(),
    )
    i2 = RawAxis.named('i')
    j2 = RawAxis.named('j')
    m = RawAxis.named('m')
    eq2 = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i2, m),
        rhs=(
            (fd.DynamicName('W2'), (i2, j2)),
            (fd.DynamicName('Hidden'), (j2, m)),
        ),
        operator=Identity(),
    )
    prog = TensorProgram(equations=(eq1, eq2))
    morphism = prog.to_morphism()
    cod = morphism.cod()
    # Final output is Y[i2, m] — one Array with 2 axes
    assert len(cod) == 1
    assert len(cod[0]._shape) == 2


def test_topological_sort_independent_equations():
    i = RawAxis.named('i')
    k = RawAxis.named('k')
    eq_a = TensorEquation(
        lhs_name=fd.DynamicName('A'),
        lhs_indices=(i,),
        rhs=((fd.DynamicName('X'), (i, k)),),
        operator=Identity(),
    )
    eq_b = TensorEquation(
        lhs_name=fd.DynamicName('B'),
        lhs_indices=(i,),
        rhs=((fd.DynamicName('Y'), (i, k)),),
        operator=Identity(),
    )
    result = _topological_sort((eq_a, eq_b))
    assert set(r.lhs_name for r in result) == {fd.DynamicName('A'), fd.DynamicName('B')}
    assert len(result) == 2


def test_exports_from_category():
    from data_structure.Category import NormAxis, TensorEquation, TensorProgram
    assert NormAxis is not None
    assert TensorEquation is not None
    assert TensorProgram is not None
