"""Converters from pyncd data-structure types to acset instance dataclasses."""
from __future__ import annotations

from dataclasses import dataclass

import data_structure.Term as fd
import data_structure.Numeric as nm
import data_structure.BroadcastedCategory as bc
from data_structure.StrideCategory import StrideMorphism
from data_structure.TensorLogic import TensorEquation, TensorProgram, NormAxis
import data_structure.Operators as ops

from acset.instances import (
    OpTag, DataTag, EntryRow, SStInstance,
    ArrayRow, ArrayAxisRow, SampleRow, SBrInstance,
)


def _dt_fields(dt: bc.Datatype | None) -> tuple[DataTag, nm.Numeric | None]:
    """Return (DataTag, max_value) for a Datatype, handling None as Reals."""
    if isinstance(dt, bc.Natural):
        return DataTag.NATURAL, dt.max_value
    return DataTag.REALS, None


@dataclass
class _OpFields:
    tag: OpTag
    bias: bool | None
    elementwise_fn: str | None


_TAG_FROM_TYPE: dict[type, OpTag] = {
    ops.SoftMax:                 OpTag.SOFTMAX,
    ops.Normalize:               OpTag.NORMALIZE,
    ops.Embedding:               OpTag.EMBEDDING,
    ops.AdditionOp:              OpTag.ADDITION_OP,
    ops.WeightedTriangularLower: OpTag.WEIGHTED_TRIANGULAR_LOWER,
}


def _operator_fields(op) -> _OpFields:
    """Extract all operator-derived ArrayRow fields in one place.

    Identity is checked before Elementwise because Identity is a subclass of
    Elementwise; all other operator types are disjoint.
    """
    if op is None or isinstance(op, ops.Identity):
        return _OpFields(OpTag.IDENTITY, None, None)
    if isinstance(op, ops.Elementwise):
        # op.operator is None for Identity (caught above), name string otherwise
        return _OpFields(OpTag.ELEMENTWISE, None, op.operator)
    if isinstance(op, ops.Linear):
        return _OpFields(OpTag.LINEAR, op.bias, None)
    return _OpFields(_TAG_FROM_TYPE.get(type(op), OpTag.IDENTITY), None, None)


def from_stride_morphism(m: StrideMorphism) -> SStInstance:
    """Convert a StrideMorphism to an SStInstance.

    Each coefficient in the matrix becomes one EntryRow.
    Domain and codomain axes live together in axis_sizes, keyed by UID.
    """
    inst = SStInstance()
    for ax in m.dom():
        inst.axis_sizes[ax.uid] = ax.local_size()
    for cod_ax, coeffs in m.cod_strides:
        inst.axis_sizes[cod_ax.uid] = cod_ax.local_size()
        for dom_ax, coeff in zip(m.dom(), coeffs):
            inst.entries.append(EntryRow(
                src=dom_ax.uid, tgt=cod_ax.uid, coeff=coeff
            ))
    return inst


def from_tensor_equation(
    eq: TensorEquation,
    array_datatypes: dict[fd.DynamicName, bc.Datatype] | None = None,
) -> SBrInstance:
    """Convert one TensorEquation to an SBrInstance.

    Retained indices (lhs_indices) become degree/TILED axes (is_target=False).
    Contracted indices (in rhs but not lhs_indices) become target axes (is_target=True).
    One SampleRow per (input_tensor, retained_axis) pair, all with coeff=Integer(1).

    array_datatypes: optional mapping from tensor name to bc.Datatype; when supplied,
    populates datatype_tag, max_value, bias, and elementwise_fn on ArrayRow.
    """
    inst = SBrInstance()
    retained = eq.retained_uids()
    datatypes = array_datatypes or {}

    op = _operator_fields(eq.operator)
    out_datatype_tag, out_max_value = _dt_fields(datatypes.get(eq.lhs_name))
    inst.arrays.append(ArrayRow(
        name=eq.lhs_name,
        is_input=False,
        operator_tag=op.tag,
        norm_axis=next((ax.uid for ax in eq.lhs_indices if isinstance(ax, NormAxis)), None),
        datatype_tag=out_datatype_tag,
        max_value=out_max_value,
        bias=op.bias,
        elementwise_fn=op.elementwise_fn,
    ))
    for pos, ax in enumerate(eq.lhs_indices):
        inst.axis_sizes[ax.uid] = ax.local_size()
        inst.array_axes.append(ArrayAxisRow(
            array_name=eq.lhs_name, axis_uid=ax.uid, is_target=False, position=pos
        ))

    for tensor_name, input_axes in eq.rhs:
        in_datatype_tag, in_max_value = _dt_fields(datatypes.get(tensor_name))
        inst.arrays.append(ArrayRow(
            name=tensor_name,
            is_input=True,
            operator_tag=None,
            datatype_tag=in_datatype_tag,
            max_value=in_max_value,
        ))
        for pos, ax in enumerate(input_axes):
            inst.axis_sizes[ax.uid] = ax.local_size()
            inst.array_axes.append(ArrayAxisRow(
                array_name=tensor_name,
                axis_uid=ax.uid,
                is_target=ax.uid not in retained,
                position=pos,
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


def from_tensor_program(
    prog: TensorProgram,
    array_datatypes: dict[fd.DynamicName, bc.Datatype] | None = None,
) -> list[SBrInstance]:
    """Convert a TensorProgram to one SBrInstance per equation.

    Instances are independent; shared axes are identified by UID across them.
    array_datatypes is forwarded to each from_tensor_equation call.
    """
    return [from_tensor_equation(eq, array_datatypes) for eq in prog.equations]
