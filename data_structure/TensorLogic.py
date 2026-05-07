from __future__ import annotations
from dataclasses import dataclass

import data_structure.Term as fd
import data_structure.BroadcastedCategory as bc
import data_structure.ProductCategory as pc
import data_structure.StrideCategory as sc


@dataclass(frozen=True)
class NormAxis(sc.RawAxis):
    ...


@dataclass(frozen=True)
class TensorEquation(bc.Operator):
    # Inherits name: DynamicName | None = None from Operator.
    # All new fields must have defaults (dataclass inheritance constraint).
    name: fd.DynamicName | None = None
    lhs_name: fd.DynamicName | None = None
    lhs_indices: fd.Prod[sc.Axis] = ()
    rhs: fd.Prod[tuple[fd.DynamicName, fd.Prod[sc.Axis]]] = ()
    operator: bc.Operator | None = None  # nonlinearity; None means Identity

    def retained_uids(self) -> set[fd.UID]:
        return {ax.uid for ax in self.lhs_indices}

    def contracted_axes(self) -> tuple[sc.Axis, ...]:
        retained = self.retained_uids()
        seen: set[fd.UID] = set()
        result = []
        for _, input_axes in self.rhs:
            for ax in input_axes:
                if ax.uid not in retained and ax.uid not in seen:
                    seen.add(ax.uid)
                    result.append(ax)
        return tuple(result)

    def bc_signature[B: bc.Datatype](
        self,
        signature: str = '',
        datatype: B = bc.Reals(),
        give_names: bool = True,
    ) -> bc.Broadcasted:
        degree = self.lhs_indices
        retained_uid_to_pos = {ax.uid: i for i, ax in enumerate(degree)}

        input_weaves = tuple(
            bc.Weave(
                datatype,
                tuple(
                    bc.WeaveMode.TILED if ax.uid in retained_uid_to_pos else ax
                    for ax in input_axes
                ),
            )
            for _, input_axes in self.rhs
        )
        output_weave = bc.Weave(
            datatype,
            tuple(bc.WeaveMode.TILED for _ in degree),
        )
        reindexings = tuple(
            pc.Rearrangement(
                mapping=tuple(
                    retained_uid_to_pos[ax.uid]
                    for ax in input_axes
                    if ax.uid in retained_uid_to_pos
                ),
                _dom=degree,
            )
            for _, input_axes in self.rhs
        )
        return bc.Broadcasted(
            operator=self,
            input_weaves=input_weaves,
            output_weaves=(output_weave,),
            reindexings=reindexings,
        )


@dataclass(frozen=True)
class TensorProgram(fd.Term):
    equations: fd.Prod[TensorEquation] = ()

    def to_morphism(self) -> pc.Composed:
        ctx = fd.Context()
        morphisms = []
        name_to_axes: dict[fd.DynamicName, fd.Prod[sc.Axis]] = {}

        for eq in _topological_sort(self.equations):
            for tensor_name, input_axes in eq.rhs:
                if tensor_name in name_to_axes:
                    for prior_ax, eq_ax in zip(name_to_axes[tensor_name], input_axes):
                        ctx.append_iter((prior_ax, eq_ax))
            applied_eq = ctx.apply(eq)
            br = applied_eq.bc_signature()
            morphisms.append(br)
            name_to_axes[eq.lhs_name] = applied_eq.lhs_indices

        return pc.Composed(content=tuple(morphisms))


def _topological_sort(
    equations: fd.Prod['TensorEquation'],
) -> list['TensorEquation']:
    name_to_eq: dict[fd.DynamicName, TensorEquation] = {
        eq.lhs_name: eq for eq in equations
    }
    deps: dict[fd.DynamicName, set[fd.DynamicName]] = {
        eq.lhs_name: {
            name for name, _ in eq.rhs
            if name in name_to_eq
        }
        for eq in equations
    }
    result: list[TensorEquation] = []
    ready: list[TensorEquation] = [
        eq for eq in equations if not deps[eq.lhs_name]
    ]
    processed_names: set[fd.DynamicName] = set()
    ready_names: set[fd.DynamicName] = {eq.lhs_name for eq in ready}
    while ready:
        eq = ready.pop(0)
        result.append(eq)
        processed_names.add(eq.lhs_name)
        ready_names.discard(eq.lhs_name)
        for other in equations:
            if other.lhs_name not in processed_names and other.lhs_name not in ready_names:
                deps[other.lhs_name].discard(eq.lhs_name)
                if not deps[other.lhs_name]:
                    ready.append(other)
                    ready_names.add(other.lhs_name)
    return result
