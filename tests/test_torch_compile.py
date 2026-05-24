import pytest
import torch
import data_structure.Category as cat
from data_structure.TensorDSL import TL, axes, real_axis
from data_structure.TensorExpr import IversonConst, ieq, iabs
from data_structure.Numeric import Integer
from torch_compile.torch_compile import (
    ConstructedModule,
    ConstructedTensorEquation,
    generate_tensor_equation_signature,
)
from torch_compile.materialise import materialise_iverson


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


# ---------------------------------------------------------------------------
# materialise_iverson unit tests
# ---------------------------------------------------------------------------

def test_materialise_upper_triangular():
    """[q <= x] over 4x4 equals upper-triangular ones (q is row, x is col)."""
    q = real_axis('q', 4)
    x = real_axis('x', 4)
    result = materialise_iverson(q <= x)
    assert torch.allclose(result, torch.triu(torch.ones(4, 4)))


def test_materialise_diagonal():
    """[q == x] over 4x4 equals the identity matrix."""
    q = real_axis('q', 4)
    x = real_axis('x', 4)
    result = materialise_iverson(ieq(q, x))
    assert torch.allclose(result, torch.eye(4))


def test_materialise_banded():
    """|q - x| < 2 over 5x5 produces the tri-diagonal band."""
    q = real_axis('q', 5)
    x = real_axis('x', 5)
    result = materialise_iverson(iabs(q - x) < IversonConst(Integer(2)))
    expected = torch.tensor([
        [1, 1, 0, 0, 0],
        [1, 1, 1, 0, 0],
        [0, 1, 1, 1, 0],
        [0, 0, 1, 1, 1],
        [0, 0, 0, 1, 1],
    ], dtype=torch.float32)
    assert torch.allclose(result, expected)


def test_materialise_compound():
    """(q < x) & (x < k) with axes (q, x, x, k) has shape (3,4,4,5) and correct values."""
    q = real_axis('q', 3)
    x = real_axis('x', 4)
    k = real_axis('k', 5)
    result = materialise_iverson((q < x) & (x < k))
    assert result.shape == (3, 4, 4, 5)
    for qi in range(3):
        for x1 in range(4):
            for x2 in range(4):
                for ki in range(5):
                    assert result[qi, x1, x2, ki].item() == float((qi < x1) and (x2 < ki))


def test_materialise_free_axis_raises():
    """An unsized axis raises ValueError with a helpful message."""
    q, x = axes('q x')
    with pytest.raises(ValueError, match="no concrete size"):
        materialise_iverson(q <= x)


# ---------------------------------------------------------------------------
# ConstructedTensorEquation auto-materialisation integration tests
# ---------------------------------------------------------------------------

def _causal_mask_sig_sized():
    q = real_axis('q', 4)
    x = real_axis('x', 4)
    tl = TL()
    tl.Attn[q, x] = tl.Score[q, x] * (q <= x)
    return tl.bc_signature()


def test_auto_materialise_shape():
    """Sized Iverson factor is auto-materialised; caller passes only Score."""
    module = ConstructedModule.construct(_causal_mask_sig_sized())
    result = module(torch.ones(4, 4))
    assert result.shape == (4, 4)


def test_auto_materialise_values():
    """Auto-materialised [q<=x] mask produces upper-triangular output."""
    module = ConstructedModule.construct(_causal_mask_sig_sized())
    result = module(torch.ones(4, 4))
    assert torch.allclose(result, torch.triu(torch.ones(4, 4)))


def test_auto_materialise_buffer_registered():
    """The pre-built mask is stored as a named buffer on the module."""
    module = ConstructedModule.construct(_causal_mask_sig_sized())
    assert '_mask_1' in dict(module.named_buffers())


def test_auto_materialise_bool_output():
    """Bool-output + sized Iverson factor: ∃ semantics and {0,1} values."""
    q = real_axis('q', 4)
    x = real_axis('x', 4)
    k = real_axis('k', 4)
    tl = TL()
    tl.Gate.predicate(q, x)
    tl.Gate[q, x] = tl.A[q, k] * tl.B[k, x] * (q <= x)
    module = ConstructedModule.construct(tl.bc_signature())
    A = torch.ones(4, 4)
    B = torch.ones(4, 4)
    result = module(A, B)
    assert torch.all((result == 0) | (result == 1))
    # Gate[q,x] = ∃k: A[q,k] ∧ B[k,x] ∧ [q<=x] — true iff q<=x (since A,B are all-ones)
    assert torch.allclose(result, torch.triu(torch.ones(4, 4)))
