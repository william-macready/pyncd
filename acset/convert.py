from __future__ import annotations

import data_structure.Term as fd
import data_structure.Numeric as nm
from data_structure.StrideCategory import StrideMorphism
from data_structure.TensorLogic import TensorEquation, TensorProgram
import data_structure.Operators as ops

from acset.instances import (
    OpTag, EntryRow, SStInstance,
    ArrayRow, ArrayAxisRow, SampleRow, SBrInstance,
)


def _operator_to_tag(operator) -> OpTag:
    if operator is None:
        return OpTag.Identity
    # Check Identity before Elementwise: Identity is a subclass of Elementwise
    if isinstance(operator, ops.Identity):
        return OpTag.Identity
    if isinstance(operator, ops.Elementwise):
        return OpTag.Elementwise
    if isinstance(operator, ops.SoftMax):
        return OpTag.SoftMax
    if isinstance(operator, ops.Normalize):
        return OpTag.Normalize
    if isinstance(operator, ops.Embedding):
        return OpTag.Embedding
    if isinstance(operator, ops.AdditionOp):
        return OpTag.AdditionOp
    if isinstance(operator, ops.WeightedTriangularLower):
        return OpTag.WeightedTriangularLower
    if isinstance(operator, ops.Linear):
        return OpTag.Linear
    return OpTag.Identity


def from_stride_morphism(m: StrideMorphism) -> SStInstance:
    """Convert a StrideMorphism to an SStInstance.

    Each coefficient in the matrix becomes one EntryRow.
    Domain and codomain axes live together in axis_sizes, keyed by UID.
    """
    inst = SStInstance()
    for ax in m._dom:
        inst.axis_sizes[ax.uid] = ax.local_size()
    for cod_ax, coeffs in m._cod_stride:
        inst.axis_sizes[cod_ax.uid] = cod_ax.local_size()
        for dom_ax, coeff in zip(m._dom, coeffs):
            inst.entries.append(EntryRow(
                src=dom_ax.uid, tgt=cod_ax.uid, coeff=coeff
            ))
    return inst


def from_tensor_equation(eq: TensorEquation) -> SBrInstance:
    """Convert one TensorEquation to an SBrInstance.

    Retained indices (lhs_indices) become degree/TILED axes (is_target=False).
    Contracted indices (in rhs but not lhs_indices) become target axes (is_target=True).
    One SampleRow per (input_tensor, retained_axis) pair, all with coeff=Integer(1).
    """
    inst = SBrInstance()
    retained = eq.retained_uids()

    inst.arrays.append(ArrayRow(
        name=eq.lhs_name,
        is_input=False,
        operator_tag=_operator_to_tag(eq.operator),
    ))
    for ax in eq.lhs_indices:
        inst.axis_sizes[ax.uid] = ax.local_size()
        inst.array_axes.append(ArrayAxisRow(
            array_name=eq.lhs_name, axis_uid=ax.uid, is_target=False
        ))

    for tensor_name, input_axes in eq.rhs:
        inst.arrays.append(ArrayRow(
            name=tensor_name, is_input=True, operator_tag=None
        ))
        for ax in input_axes:
            inst.axis_sizes[ax.uid] = ax.local_size()
            inst.array_axes.append(ArrayAxisRow(
                array_name=tensor_name,
                axis_uid=ax.uid,
                is_target=ax.uid not in retained,
            ))
        for ax in input_axes:
            if ax.uid in retained:
                inst.samples.append(SampleRow(
                    src_uid=ax.uid,
                    tgt_uid=ax.uid,
                    coeff=nm.Integer(1),
                    reindexing_of=tensor_name,
                ))

    return inst


def from_tensor_program(prog: TensorProgram) -> list[SBrInstance]:
    """Convert a TensorProgram to one SBrInstance per equation.

    Instances are independent; shared axes are identified by UID across them.
    """
    return [from_tensor_equation(eq) for eq in prog.equations]
