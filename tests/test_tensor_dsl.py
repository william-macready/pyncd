import pytest
from data_structure.TensorDSL import (
    TL, TensorProxy, IndexedTensor, RHSExpression,
    NatAxis, PredAxis, TensorKind, TensorDeclaration,
    axes, norm_axis, nat_axis, real_axis, relu, softmax,
)
from data_structure.TensorLogic import NormAxis, TensorEquation, TensorProgram
import data_structure.Numeric as nm
import data_structure.Operators as ops
import data_structure.StrideCategory as sc
import data_structure.Term as fd


# ---------------------------------------------------------------------------
# axes() / norm_axis()
# ---------------------------------------------------------------------------

def test_axes_variadic():
    i, j, k = axes('i', 'j', 'k')
    assert isinstance(i, sc.RawAxis)
    assert i.uid != j.uid != k.uid

def test_axes_single_string():
    i, j, k = axes('i j k')
    assert isinstance(k, sc.RawAxis)
    assert i.uid != k.uid

def test_axes_latex_name():
    (d_ff,) = axes('d_{ff}')
    assert isinstance(d_ff, sc.RawAxis)

def test_norm_axis_type():
    x = norm_axis('x')
    assert isinstance(x, NormAxis)
    assert isinstance(x, sc.RawAxis)


# ---------------------------------------------------------------------------
# TL / TensorProxy
# ---------------------------------------------------------------------------

def test_getattr_returns_proxy():
    tl = TL()
    proxy = tl.W
    assert isinstance(proxy, TensorProxy)
    assert proxy._name == 'W'

def test_getattr_underscore_raises():
    tl = TL()
    with pytest.raises(AttributeError):
        _ = tl._secret

def test_proxy_getitem_single_axis():
    tl = TL()
    (i,) = axes('i')
    it = tl.X[i]
    assert isinstance(it, IndexedTensor)
    assert it.indices == (i,)

def test_proxy_getitem_tuple():
    tl = TL()
    i, j = axes('i j')
    it = tl.W[i, j]
    assert it.indices == (i, j)


# ---------------------------------------------------------------------------
# IndexedTensor * composition
# ---------------------------------------------------------------------------

def test_mul_two_indexed_tensors():
    tl = TL()
    i, j, k = axes('i j k')
    expr = tl.W[i, k] * tl.X[k, j]
    assert isinstance(expr, RHSExpression)
    assert len(expr.factors) == 2
    assert isinstance(expr.operator, ops.Identity)

def test_mul_three_factors():
    tl = TL()
    a, b, c, d = axes('a b c d')
    expr = tl.A[a, b] * tl.B[b, c] * tl.C[c, d]
    assert len(expr.factors) == 3

def test_rmul_order():
    tl = TL()
    i, j, k = axes('i j k')
    w = tl.W[i, k]
    x = tl.X[k, j]
    expr = w * x
    assert expr.factors[0].name == fd.DynamicName('W')
    assert expr.factors[1].name == fd.DynamicName('X')


# ---------------------------------------------------------------------------
# relu / softmax wrappers
# ---------------------------------------------------------------------------

def test_relu_on_expression():
    tl = TL()
    i, j, k = axes('i j k')
    expr = relu(tl.W[i, k] * tl.X[k, j])
    assert isinstance(expr.operator, ops.ReLU)
    assert len(expr.factors) == 2

def test_relu_on_single_tensor():
    tl = TL()
    (i,) = axes('i')
    expr = relu(tl.X[i])
    assert isinstance(expr.operator, ops.ReLU)
    assert len(expr.factors) == 1

def test_softmax_on_expression():
    tl = TL()
    q, h, k = axes('q h k')
    expr = softmax(tl.Query[q, h, k] * tl.Key[q, h, k])
    assert isinstance(expr.operator, ops.SoftMax)


# ---------------------------------------------------------------------------
# __setitem__ captures equations
# ---------------------------------------------------------------------------

def test_setitem_captures_equation():
    tl = TL()
    i, j, k = axes('i j k')
    tl.Y[i, j] = tl.W[i, k] * tl.X[k, j]
    assert len(tl._equations) == 1
    eq = tl._equations[0]
    assert isinstance(eq, TensorEquation)
    assert eq.lhs_name == fd.DynamicName('Y')

def test_setitem_single_factor_coerced():
    tl = TL()
    i, j = axes('i j')
    tl.Y[i, j] = tl.X[i, j]
    eq = tl._equations[0]
    assert len(eq.rhs) == 1

def test_setitem_preserves_axis_uid_identity():
    tl = TL()
    i, j, k = axes('i j k')
    tl.Y[i, j] = tl.W[i, k] * tl.X[k, j]
    eq = tl._equations[0]
    # k appears in both rhs factors; uid must match
    k_in_W = eq.rhs[0][1][1]   # W's second index
    k_in_X = eq.rhs[1][1][0]   # X's first index
    assert k_in_W.uid == k_in_X.uid

def test_multiple_equations_ordered():
    tl = TL()
    p, d, d_ff = axes('p d d_ff')
    tl.Hidden[p, d_ff] = relu(tl.W_in[d_ff, d] * tl.X[p, d])
    tl.Output[p, d] = tl.W_out[d, d_ff] * tl.Hidden[p, d_ff]
    assert len(tl._equations) == 2
    assert tl._equations[0].lhs_name == fd.DynamicName('Hidden')
    assert tl._equations[1].lhs_name == fd.DynamicName('Output')


# ---------------------------------------------------------------------------
# to_equation / to_program
# ---------------------------------------------------------------------------

def test_to_equation_single():
    tl = TL()
    i, j, k = axes('i j k')
    tl.Y[i, j] = tl.W[i, k] * tl.X[k, j]
    eq = tl.to_equation()
    assert isinstance(eq, TensorEquation)

def test_to_equation_raises_on_multiple():
    tl = TL()
    i, j, k = axes('i j k')
    tl.Y[i, j] = tl.W[i, k] * tl.X[k, j]
    tl.Z[i, j] = tl.Y[i, j] * tl.B[i, j]
    with pytest.raises(ValueError):
        tl.to_equation()

def test_to_program():
    tl = TL()
    p, d, d_ff = axes('p d d_ff')
    tl.Hidden[p, d_ff] = relu(tl.W_in[d_ff, d] * tl.X[p, d])
    tl.Output[p, d] = tl.W_out[d, d_ff] * tl.Hidden[p, d_ff]
    prog = tl.to_program()
    assert isinstance(prog, TensorProgram)
    assert len(prog.equations) == 2


# ---------------------------------------------------------------------------
# End-to-end: bc_signature and to_morphism agree with manual construction
# ---------------------------------------------------------------------------

def test_matmul_bc_signature():
    tl = TL()
    i, j, k = axes('i j k')
    tl.Y[i, j] = tl.W[i, k] * tl.X[k, j]
    sig = tl.to_equation().bc_signature()
    # 2 inputs (W, X), 1 output
    assert len(sig.input_weaves) == 2
    assert len(sig.output_weaves) == 1

def test_ffn_to_morphism():
    tl = TL()
    p, d, d_ff = axes('p d d_ff')
    tl.Hidden[p, d_ff] = relu(tl.W_in[d_ff, d] * tl.X[p, d])
    tl.Output[p, d] = tl.W_out[d, d_ff] * tl.Hidden[p, d_ff]
    morph = tl.to_program().to_morphism()
    from data_structure.ProductCategory import Composed
    assert isinstance(morph, Composed)
    assert len(morph.content) == 2

def test_norm_axis_preserved_in_equation():
    tl = TL()
    q, h, k = axes('q h k')
    x = norm_axis('x')
    tl.Comp[h, q, x] = softmax(tl.Query[q, h, k] * tl.Key[x, h, k])
    eq = tl.to_equation()
    assert isinstance(eq.lhs_indices[2], NormAxis)
    assert isinstance(eq.operator, ops.SoftMax)


# ---------------------------------------------------------------------------
# nat_axis / real_axis helpers
# ---------------------------------------------------------------------------

def test_nat_axis_type():
    t = nat_axis('t')
    assert isinstance(t, NatAxis)
    assert isinstance(t, sc.RawAxis)

def test_nat_axis_concrete_size():
    t = nat_axis('t', 50000)
    assert isinstance(t._size, nm.Integer)

def test_nat_axis_free_size_when_no_size():
    t = nat_axis('t')
    assert isinstance(t._size, nm.FreeNumeric)

def test_real_axis_type():
    d = real_axis('d')
    assert isinstance(d, sc.RawAxis)
    assert not isinstance(d, NatAxis)

def test_real_axis_concrete_size():
    d = real_axis('d', 512)
    assert isinstance(d._size, nm.Integer)

def test_real_axis_free_size_when_no_size():
    d = real_axis('d')
    assert isinstance(d._size, nm.FreeNumeric)


# ---------------------------------------------------------------------------
# TensorDeclaration / TensorKind
# ---------------------------------------------------------------------------

def test_tensor_declaration_stored():
    tl = TL()
    d, d_ff = real_axis('d', 512), real_axis('d_ff', 2048)
    tl.W_in.tensor(d_ff, d)
    decl = tl._declarations['W_in']
    assert isinstance(decl, TensorDeclaration)
    assert decl.kind is TensorKind.TENSOR
    assert len(decl.shape) == 2

def test_predicate_declaration_stored():
    tl = TL()
    q, x = axes('q x')
    tl.Mask.predicate(q, x)
    decl = tl._declarations['Mask']
    assert decl.kind is TensorKind.PREDICATE

def test_selection_declaration_stored():
    tl = TL()
    t = nat_axis('t', 50000)
    d = real_axis('d', 512)
    tl.Emb.selection(t, d)
    decl = tl._declarations['Emb']
    assert decl.kind is TensorKind.SELECTION

def test_declaration_returns_proxy():
    tl = TL()
    (i,) = axes('i')
    result = tl.X.tensor(i)
    assert isinstance(result, TensorProxy)


# ---------------------------------------------------------------------------
# Axis promotion via __getitem__
# ---------------------------------------------------------------------------

def test_predicate_promotes_all_axes():
    tl = TL()
    q, x = axes('q x')
    tl.Mask.predicate(q, x)
    i, j = axes('i j')
    it = tl.Mask[i, j]
    assert all(isinstance(ax, PredAxis) for ax in it.indices)

def test_predicate_preserves_uid():
    tl = TL()
    q, x = axes('q x')
    tl.Mask.predicate(q, x)
    i, j = axes('i j')
    it = tl.Mask[i, j]
    assert it.indices[0].uid == i.uid
    assert it.indices[1].uid == j.uid

def test_tensor_no_promotion():
    tl = TL()
    d, d_ff = axes('d d_ff')
    tl.W.tensor(d_ff, d)
    i, j = axes('i j')
    it = tl.W[i, j]
    assert not isinstance(it.indices[0], (NatAxis, PredAxis))
    assert not isinstance(it.indices[1], (NatAxis, PredAxis))

def test_selection_promotes_nat_slots_only():
    tl = TL()
    t = nat_axis('t', 50000)
    d = real_axis('d', 512)
    tl.Emb.selection(t, d)
    i, j = axes('i j')
    it = tl.Emb[i, j]
    assert isinstance(it.indices[0], NatAxis)      # slot declared NatAxis → promoted
    assert not isinstance(it.indices[1], NatAxis)  # slot declared RawAxis → unchanged

def test_selection_type_only_no_size():
    tl = TL()
    tl.Emb.selection(nat_axis('t'), real_axis('d'))  # type only, no size
    i, j = axes('i j')
    it = tl.Emb[i, j]
    assert isinstance(it.indices[0], NatAxis)
    assert not isinstance(it.indices[1], NatAxis)

def test_no_declaration_unchanged():
    tl = TL()
    i, j = axes('i j')
    it = tl.X[i, j]
    assert it.indices == (i, j)


# ---------------------------------------------------------------------------
# Arity checking
# ---------------------------------------------------------------------------

def test_getitem_arity_mismatch_raises():
    tl = TL()
    d, d_ff = axes('d d_ff')
    tl.W.tensor(d_ff, d)
    (i,) = axes('i')
    with pytest.raises(ValueError, match="2 axes"):
        _ = tl.W[i]

def test_setitem_arity_mismatch_raises():
    tl = TL()
    i, j, k = axes('i j k')
    tl.Y.tensor(i, j)
    with pytest.raises(ValueError, match="2 axes"):
        tl.Y[i, j, k] = tl.X[i, j, k]


# ---------------------------------------------------------------------------
# End-to-end: declared matmul still produces valid bc_signature
# ---------------------------------------------------------------------------

def test_tensor_declared_matmul_bc_signature():
    tl = TL()
    i = real_axis('i', 64)
    j = real_axis('j', 64)
    k = real_axis('k', 64)
    tl.W.tensor(i, k)
    tl.X.tensor(k, j)
    tl.Y.tensor(i, j)
    i2, j2, k2 = axes('i j k')
    tl.Y[i2, j2] = tl.W[i2, k2] * tl.X[k2, j2]
    sig = tl.to_equation().bc_signature()
    assert len(sig.input_weaves) == 2
    assert len(sig.output_weaves) == 1
