from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

import data_structure.Term as fd
import data_structure.BroadcastedCategory as bc
import data_structure.Numeric as nm
import data_structure.StrideCategory as sc
import data_structure.Operators as ops
from data_structure.TensorLogic import NormAxis, TensorEquation, TensorProgram


# ---------------------------------------------------------------------------
# Axis subtypes
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class NatAxis(sc.RawAxis):
    """Marks a natural-number (ℕ) index dimension."""


@dataclass(frozen=True)
class PredAxis(sc.RawAxis):
    """Marks a predicate (Boolean-filter) index dimension."""


# ---------------------------------------------------------------------------
# Tensor-level declarations
# ---------------------------------------------------------------------------

class TensorKind(Enum):
    TENSOR    = 'tensor'
    PREDICATE = 'predicate'
    SELECTION = 'selection'


@dataclass
class TensorDeclaration:
    """Positional shape declaration for a named tensor."""
    kind:  TensorKind
    shape: tuple[sc.RawAxis, ...]


def _pred_wrap(ax: sc.RawAxis) -> PredAxis:
    return PredAxis(uid=ax.uid, _size=ax._size)


def _nat_wrap(ax: sc.RawAxis) -> NatAxis:
    return NatAxis(uid=ax.uid, _size=ax._size)


# ---------------------------------------------------------------------------
# TL registry
# ---------------------------------------------------------------------------

class TL:
    """Registry for tensor logic equations.

    Access tensor names as attributes to build equations, then call
    to_equation() or to_program() to extract the result.

        tl = TL()
        i, j, k = axes('i j k')
        tl.Y[i,j] = tl.W[i,k] * tl.X[k,j]
        eq = tl.to_equation()

    Optionally declare tensors before use to attach kind and shape metadata:

        d, d_ff = real_axis('d', 512), real_axis('d_ff', 2048)
        tl.W_in.contraction(d_ff, d)
    """

    def __init__(self) -> None:
        self._equations: list[TensorEquation] = []
        self._declarations: dict[str, TensorDeclaration] = {}

    def __getattr__(self, name: str) -> TensorProxy:
        if name.startswith('_'):
            raise AttributeError(name)
        return TensorProxy(name, self)

    def _register(self, eq: TensorEquation) -> None:
        self._equations.append(eq)

    def _register_declaration(self, name: str, decl: TensorDeclaration) -> None:
        self._declarations[name] = decl

    def to_equation(self) -> TensorEquation:
        if len(self._equations) != 1:
            raise ValueError(f"expected exactly one equation, got {len(self._equations)}")
        return self._equations[0]

    def to_program(self) -> TensorProgram:
        return TensorProgram(equations=tuple(self._equations))

    def bc_signature[B: bc.Datatype](
        self,
        signature: str = '',
        datatype: B = bc.Reals(),
        give_names: bool = True,
    ) -> bc.Broadcasted[B, sc.RawAxis]:
        return self.to_equation().bc_signature(signature, datatype, give_names)


class TensorProxy:
    """Handle for a named tensor in a TL registry.

    __getitem__ returns an IndexedTensor for use on the RHS of an equation.
    __setitem__ captures a completed equation into the parent registry.
    contraction/predicate/selection register a shape declaration.
    """

    def __init__(self, name: str, registry: TL) -> None:
        self._name = name
        self._registry = registry

    def _promote(self, indices: tuple[sc.RawAxis, ...]) -> tuple[sc.RawAxis, ...]:
        decl = self._registry._declarations.get(self._name)
        if decl is None:
            return indices
        if len(indices) != len(decl.shape):
            raise ValueError(
                f"tensor '{self._name}' declared with {len(decl.shape)} axes "
                f"but indexed with {len(indices)}"
            )
        if decl.kind is TensorKind.PREDICATE:
            return tuple(_pred_wrap(ax) for ax in indices)
        if decl.kind is TensorKind.SELECTION:
            return tuple(
                _nat_wrap(ax) if isinstance(decl_ax, NatAxis) else ax
                for ax, decl_ax in zip(indices, decl.shape)
            )
        return indices  # TENSOR — no promotion

    def __getitem__(self, indices: sc.RawAxis | tuple[sc.RawAxis, ...]) -> IndexedTensor:
        if not isinstance(indices, tuple):
            indices = (indices,)
        return IndexedTensor(fd.DynamicName(self._name), self._promote(indices))

    def __setitem__(
        self,
        indices: sc.RawAxis | tuple[sc.RawAxis, ...],
        value: IndexedTensor | RHSExpression,
    ) -> None:
        if not isinstance(indices, tuple):
            indices = (indices,)
        decl = self._registry._declarations.get(self._name)
        if decl is not None and len(indices) != len(decl.shape):
            raise ValueError(
                f"tensor '{self._name}' declared with {len(decl.shape)} axes "
                f"but assigned with {len(indices)}"
            )
        if isinstance(value, IndexedTensor):
            value = RHSExpression([value], ops.Identity())
        eq = TensorEquation(
            lhs_name=fd.DynamicName(self._name),
            lhs_indices=indices,
            rhs=tuple((t.name, t.indices) for t in value.factors),
            operator=value.operator,
        )
        self._registry._register(eq)

    def tensor(self, *shape: sc.RawAxis) -> TensorProxy:
        """Declare this tensor with the given shape (default contraction semantics)."""
        self._registry._register_declaration(
            self._name,
            TensorDeclaration(kind=TensorKind.TENSOR, shape=shape),
        )
        return self

    def predicate(self, *shape: sc.RawAxis) -> TensorProxy:
        """Declare this tensor as a predicate tensor; all indices promoted to PredAxis."""
        self._registry._register_declaration(
            self._name,
            TensorDeclaration(kind=TensorKind.PREDICATE, shape=shape),
        )
        return self

    def selection(self, *shape: sc.RawAxis) -> TensorProxy:
        """Declare this tensor as a selection tensor; NatAxis slots promote to NatAxis."""
        self._registry._register_declaration(
            self._name,
            TensorDeclaration(kind=TensorKind.SELECTION, shape=shape),
        )
        return self


class IndexedTensor:
    """A tensor name subscripted by a tuple of axes.

    Combine with * to accumulate factors into an RHSExpression.
    """

    def __init__(self, name: fd.DynamicName, indices: tuple[sc.RawAxis, ...]) -> None:
        self.name = name
        self.indices = indices

    def __mul__(self, other: IndexedTensor | RHSExpression) -> RHSExpression:
        if isinstance(other, IndexedTensor):
            return RHSExpression([self, other], ops.Identity())
        return RHSExpression([self, *other.factors], other.operator)

    def __rmul__(self, other: IndexedTensor) -> RHSExpression:
        return RHSExpression([other, self], ops.Identity())


class RHSExpression:
    """Accumulated factors on the RHS of an equation.

    Produced by combining IndexedTensors with *. Wrap in relu() or softmax()
    to attach a nonlinearity.
    """

    def __init__(self, factors: list[IndexedTensor], operator: bc.Operator) -> None:
        self.factors = factors
        self.operator = operator

    def __mul__(self, other: IndexedTensor) -> RHSExpression:
        return RHSExpression(self.factors + [other], self.operator)


# ---------------------------------------------------------------------------
# Axis helpers
# ---------------------------------------------------------------------------

def axes(*names: str) -> tuple[sc.RawAxis, ...]:
    """Return a tuple of RawAxis objects, one per name.

    Accepts either variadic strings or a single space-separated string:
        i, j, k = axes('i j k')
        i, j, k = axes('i', 'j', 'k')
    LaTeX-style names like d_{ff} work as-is.
    """
    flat: list[str] = []
    for n in names:
        flat.extend(n.split())
    return tuple(sc.RawAxis.named(n) for n in flat)


def norm_axis(name: str) -> NormAxis:
    """Return a NormAxis — marks the normalisation dimension (e.g. softmax axis)."""
    return NormAxis.named(name)


def nat_axis(name: str, size: int | None = None) -> NatAxis:
    """Return a NatAxis with an optional concrete integer size (ℕ dimension)."""
    base = sc.RawAxis.named(name)
    _size = nm.Integer(size) if size is not None else base._size
    return NatAxis(uid=base.uid, _size=_size)


def real_axis(name: str, size: int | None = None) -> sc.RawAxis:
    """Return a RawAxis with an optional concrete integer size (ℝ dimension)."""
    base = sc.RawAxis.named(name)
    if size is None:
        return base
    return sc.RawAxis(uid=base.uid, _size=nm.Integer(size))


# ---------------------------------------------------------------------------
# Operator wrappers
# ---------------------------------------------------------------------------

def relu(expr: IndexedTensor | RHSExpression) -> RHSExpression:
    """Wrap an expression with a ReLU nonlinearity."""
    if isinstance(expr, IndexedTensor):
        expr = RHSExpression([expr], ops.Identity())
    return RHSExpression(expr.factors, ops.ReLU())


def softmax(expr: IndexedTensor | RHSExpression) -> RHSExpression:
    """Wrap an expression with a SoftMax nonlinearity."""
    if isinstance(expr, IndexedTensor):
        expr = RHSExpression([expr], ops.Identity())
    return RHSExpression(expr.factors, ops.SoftMax())
