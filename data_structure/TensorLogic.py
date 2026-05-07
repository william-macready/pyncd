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
