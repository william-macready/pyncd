import pytest
import torch
import data_structure.Category as cat
from data_structure.TensorDSL import TL, axes
from torch_compile.torch_compile import (
    ConstructedModule,
    ConstructedTensorEquation,
    generate_tensor_equation_signature,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _matmul_sig():
    tl = TL()
    i, j, k = axes('i j k')
    tl.Y[i, j] = tl.W[i, k] * tl.X[k, j]
    return tl.bc_signature()


def _bool_matmul_sig():
    tl = TL()
    i, j, k = axes('i j k')
    tl.Out.predicate(i, j)
    tl.Out[i, j] = tl.A[i, k] * tl.B[k, j]
    return tl.bc_signature()


def _copy_sig():
    tl = TL()
    i, j = axes('i j')
    tl.Y[i, j] = tl.X[i, j]
    return tl.bc_signature()


def _reduction_sig():
    tl = TL()
    i, k = axes('i k')
    tl.Y[i,] = tl.X[i, k]
    return tl.bc_signature()


# ---------------------------------------------------------------------------
# Signature generation
# ---------------------------------------------------------------------------

def test_signature_matmul_has_two_input_segments():
    sig = generate_tensor_equation_signature(_matmul_sig())
    lhs, _ = sig.split('->')
    segments = [s.strip() for s in lhs.split(',')]
    assert len(segments) == 2


def test_signature_matmul_contracted_tag_in_both_inputs():
    sig = generate_tensor_equation_signature(_matmul_sig())
    lhs, _ = sig.split('->')
    seg0, seg1 = [s.strip() for s in lhs.split(',')]
    # x0 is the contracted axis; it must appear in both input segments
    assert 'x0' in seg0
    assert 'x0' in seg1


def test_signature_matmul_contracted_tag_not_in_output():
    sig = generate_tensor_equation_signature(_matmul_sig())
    _, rhs = sig.split('->')
    assert 'x0' not in rhs


def test_signature_copy_no_contracted_tags():
    sig = generate_tensor_equation_signature(_copy_sig())
    assert 'x' not in sig.split('->')[0].replace('...', '')


def test_signature_reduction_contracted_tag_in_input_not_output():
    sig = generate_tensor_equation_signature(_reduction_sig())
    lhs, rhs = sig.split('->')
    assert 'x0' in lhs
    assert 'x0' not in rhs


def test_signature_arrow_present():
    sig = generate_tensor_equation_signature(_matmul_sig())
    assert '->' in sig


# ---------------------------------------------------------------------------
# Dispatch and construction
# ---------------------------------------------------------------------------

def test_tensor_equation_registered():
    assert cat.TensorEquation in ConstructedModule.operation_registry


def test_construct_returns_constructed_tensor_equation():
    module = ConstructedModule.construct(_matmul_sig())
    assert isinstance(module, ConstructedTensorEquation)


def test_demote_false_for_reals_output():
    module = ConstructedModule.construct(_matmul_sig())
    assert module.demote is False


def test_demote_true_for_bool_output():
    module = ConstructedModule.construct(_bool_matmul_sig())
    assert module.demote is True


def test_nonlinearity_raises():
    from data_structure.TensorLogic import TensorEquation
    from data_structure.Operators import SoftMax
    import data_structure.Term as fd
    from data_structure.TensorExpr import TensorRef
    i, j, k = axes('i j k')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i, j),
        rhs=(TensorRef(fd.DynamicName('W'), (i, k)), TensorRef(fd.DynamicName('X'), (k, j))),
        operator=SoftMax(),
    )
    br = eq.bc_signature()
    with pytest.raises(NotImplementedError):
        ConstructedTensorEquation(br)


# ---------------------------------------------------------------------------
# Forward — Reals output
# ---------------------------------------------------------------------------

def test_matmul_forward_shape():
    module = ConstructedModule.construct(_matmul_sig())
    W = torch.ones(3, 4)
    X = torch.ones(4, 5)
    result = module(W, X)
    assert result.shape == (3, 5)


def test_matmul_forward_values():
    module = ConstructedModule.construct(_matmul_sig())
    W = torch.ones(3, 4)
    X = torch.ones(4, 5)
    result = module(W, X)
    expected = torch.einsum('ik,kj->ij', W, X)
    assert torch.allclose(result, expected)


def test_matmul_forward_non_trivial_values():
    module = ConstructedModule.construct(_matmul_sig())
    W = torch.arange(6, dtype=torch.float).reshape(2, 3)
    X = torch.arange(6, dtype=torch.float).reshape(3, 2)
    result = module(W, X)
    expected = W @ X
    assert torch.allclose(result, expected)


def test_copy_forward_identity():
    module = ConstructedModule.construct(_copy_sig())
    X = torch.arange(6, dtype=torch.float).reshape(2, 3)
    result = module(X)
    assert torch.allclose(result, X)


def test_reduction_forward_sums_over_k():
    module = ConstructedModule.construct(_reduction_sig())
    X = torch.ones(3, 4)
    result = module(X)
    assert result.shape == (3,)
    assert torch.allclose(result, torch.full((3,), 4.0))


# ---------------------------------------------------------------------------
# Forward — Bool output (Heaviside demotion)
# ---------------------------------------------------------------------------

def test_bool_output_shape():
    module = ConstructedModule.construct(_bool_matmul_sig())
    A = torch.ones(3, 4)
    B = torch.ones(4, 5)
    result = module(A, B)
    assert result.shape == (3, 5)


def test_bool_output_positive_sum_yields_one():
    module = ConstructedModule.construct(_bool_matmul_sig())
    A = torch.ones(3, 4)
    B = torch.ones(4, 5)
    result = module(A, B)
    assert torch.all(result == 1.0)


def test_bool_output_zero_sum_yields_zero():
    module = ConstructedModule.construct(_bool_matmul_sig())
    A = torch.zeros(3, 4)
    B = torch.ones(4, 5)
    result = module(A, B)
    assert torch.all(result == 0.0)


def test_bool_output_negative_sum_yields_zero():
    module = ConstructedModule.construct(_bool_matmul_sig())
    A = -torch.ones(3, 4)
    B = torch.ones(4, 5)
    result = module(A, B)
    assert torch.all(result == 0.0)


def test_bool_output_preserves_dtype():
    module = ConstructedModule.construct(_bool_matmul_sig())
    A = torch.ones(3, 4, dtype=torch.float32)
    B = torch.ones(4, 5, dtype=torch.float32)
    result = module(A, B)
    assert result.dtype == torch.float32


# ---------------------------------------------------------------------------
# Modular materialisation interface
# ---------------------------------------------------------------------------
# These tests demonstrate the caller-materialisation contract: Iverson factors
# are passed as pre-built tensors in the same position they occupy in rhs.
# The module treats them identically to TensorRef tensors.

def test_pre_materialised_causal_mask():
    """Score[q,x] * [q<=x] with the mask supplied as a pre-built tensor."""
    from data_structure.TensorExpr import IversonBinOp
    tl = TL()
    q, x = axes('q x')
    tl.Attn[q, x] = tl.Score[q, x] * (q <= x)
    sig = tl.bc_signature()
    module = ConstructedModule.construct(sig)

    n = 4
    Score = torch.ones(n, n)
    # Materialise [q <= x] as lower-triangular (including diagonal)
    Mask = torch.tril(torch.ones(n, n))
    result = module(Score, Mask)

    expected = torch.tril(torch.ones(n, n))
    assert torch.allclose(result, expected)


def test_pre_materialised_mask_rhs_factor_order():
    """Verify rhs factor order: TensorRef first, Iverson second."""
    tl = TL()
    q, x = axes('q x')
    tl.Attn[q, x] = tl.Score[q, x] * (q <= x)
    sig = tl.bc_signature()
    assert len(sig.input_weaves) == 2


def test_pre_materialised_mask_bool_typed():
    """Inline Iverson input weave carries Bool() datatype."""
    tl = TL()
    q, x = axes('q x')
    tl.Attn[q, x] = tl.Score[q, x] * (q <= x)
    sig = tl.bc_signature()
    assert isinstance(sig.input_weaves[1].datatype, cat.Bool)
