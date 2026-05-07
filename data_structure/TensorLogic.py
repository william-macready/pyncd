from __future__ import annotations
from dataclasses import dataclass

import data_structure.Term as fd
import data_structure.BroadcastedCategory as bc
import data_structure.ProductCategory as pc
import data_structure.StrideCategory as sc


# Marks the normalisation dimension in a TensorEquation (e.g. the softmax axis in
# Y[b, p, t.] = softmax(...)). bc_signature() treats it identically to RawAxis;
# the distinction is available for rendering and downstream tooling via isinstance.
@dataclass(frozen=True)
class NormAxis(sc.RawAxis):
    ...


# A single tensor logic equation stored as a pyncd Operator.
# Index identity is UID identity: passing the same Axis object in multiple positions
# encodes shared indices. An axis whose UID appears in lhs_indices is retained
# (output); one that appears only in rhs is contracted (summed over).
# Because TensorEquation is a Term, Context.apply() traverses lhs_indices and rhs
# via deep_reconstruct, keeping the equation and its Broadcasted in sync under
# axis unification.
@dataclass(frozen=True)
class TensorEquation(bc.Operator):
    # All fields need defaults: Operator already declares name with a default, and
    # Python dataclasses require that subclass fields without defaults precede those
    # with defaults — satisfied here by giving everything a default.
    name: fd.DynamicName | None = None
    lhs_name: fd.DynamicName | None = None
    lhs_indices: fd.Prod[sc.RawAxis] = ()
    rhs: fd.Prod[tuple[fd.DynamicName, fd.Prod[sc.RawAxis]]] = ()
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
    ) -> bc.Broadcasted[B, sc.RawAxis]:
        # Converts this equation to a Broadcasted by reading the contraction
        # structure from UID identity. The translation has three parts:
        #
        #   1. degree — the retained axes (lhs_indices), shared as _dom by every
        #      reindexing. Broadcasted.degree() calls iallequals(r.dom() for r in
        #      reindexings), so all reindexings must agree on their domain.
        #
        #   2. weaves — one Weave per input. Each position in the weave is either
        #      WeaveMode.TILED (retained axis: filled from the degree at runtime,
        #      i.e. the output loop index) or a concrete Axis (contracted axis:
        #      kept in place for the operator to sum over). The output weave is
        #      all-TILED because the output shape equals the degree exactly.
        #
        #   3. reindexings — one Rearrangement per input. mapping[i] is the
        #      position within degree of the i-th retained axis of that input,
        #      so Rearrangement.cod() yields the subset of degree axes this input
        #      actually uses. Broadcasted.dom() then calls
        #      weave.imprint_to_degree(reindexing.cod()) to recover the full input
        #      shape by filling TILED slots with those degree axes.
        #
        # operator=self so the full equation is preserved inside the Broadcasted
        # and remains accessible for display and round-trip editing.
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


# Collects a set of TensorEquation objects and converts them to a single
# Composed morphism via to_morphism().
#
# The key problem: each TensorEquation is constructed with its own fresh Axis
# objects. Two equations that both reference a tensor named 'Hidden' will use
# different Python objects for its axes — they need to be unified so the
# resulting Composed is coherent. to_morphism() solves this with a Context:
#
#   1. Topologically sort equations so each is processed after its dependencies.
#
#   2. For each equation, any rhs tensor that was produced by a prior equation
#      is looked up in name_to_axes. The prior output axes are unified pairwise
#      with this equation's rhs axes via ctx.append_iter((prior_ax, eq_ax)).
#      This tells the Context that the two axis objects represent the same index.
#
#   3. ctx.apply(eq) walks the equation's full data structure via deep_reconstruct
#      and replaces every axis whose UID was unified with its canonical
#      representative. The substitution reaches inside both lhs_indices and rhs,
#      so the equation and its resulting Broadcasted are self-consistent.
#
#   4. bc_signature() is called on the substituted equation to produce the
#      Broadcasted for this step.
#
#   5. applied_eq.lhs_indices (post-apply, canonical UIDs) is stored in
#      name_to_axes so that subsequent equations unify against the same
#      canonical axes rather than stale originals.
#
# The result is Composed(content=(br1, br2, ...)) where shared axes across
# adjacent morphisms carry consistent UIDs.
@dataclass(frozen=True)
class TensorProgram(fd.Term):
    equations: fd.Prod[TensorEquation] = ()

    def to_morphism(self) -> pc.Composed:
        ctx = fd.Context()
        morphisms = []
        name_to_axes: dict[fd.DynamicName | None, fd.Prod[sc.RawAxis]] = {}

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
    equations: fd.Prod[TensorEquation],
) -> list[TensorEquation]:
    # Kahn's algorithm. Only intra-program names (those with a defining equation)
    # count as dependencies; external tensors (weights, inputs) are ignored.
    name_to_eq: dict[fd.DynamicName | None, TensorEquation] = {
        eq.lhs_name: eq for eq in equations
    }
    deps: dict[fd.DynamicName | None, set[fd.DynamicName | None]] = {
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
    processed_names: set[fd.DynamicName | None] = set()
    ready_names: set[fd.DynamicName | None] = {eq.lhs_name for eq in ready}
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
    # A short result means at least one cycle exists — raise rather than silently
    # producing an incomplete Composed whose dom()/cod() would raise IndexError.
    if len(result) < len(equations):
        raise ValueError("TensorProgram has cyclic equation dependencies")
    return result
