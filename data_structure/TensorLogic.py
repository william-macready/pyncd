from __future__ import annotations
from collections import deque
from dataclasses import dataclass

import data_structure.Term as fd
import data_structure.BroadcastedCategory as bc
import data_structure.ProductCategory as pc
import data_structure.StrideCategory as sc
from data_structure.TensorExpr import TensorRef, IversonBinOp, IversonUnaryOp, _factor_axes


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
    lhs_name: fd.DynamicName | None = None
    lhs_indices: fd.Prod[sc.RawAxis] = ()
    rhs: fd.Prod[TensorRef | IversonBinOp | IversonUnaryOp] = ()
    operator: bc.Operator | None = None  # nonlinearity; None means Identity

    def retained_uids(self) -> set[fd.UID]:
        return {ax.uid for ax in self.lhs_indices}

    def contracted_axes(self) -> tuple[sc.RawAxis, ...]:
        retained = self.retained_uids()
        seen: set[fd.UID] = set()
        result = []
        for factor in self.rhs:
            for ax in _factor_axes(factor):
                if ax.uid not in retained and ax.uid not in seen:
                    seen.add(ax.uid)
                    result.append(ax)
        return tuple(result)

    def bc_signature[B: bc.Datatype](
        self,
        signature: str = '',
        datatype: B = bc.Reals(),
        give_names: bool = True,
        array_datatypes: dict[fd.DynamicName, bc.Datatype] | None = None,
    ) -> bc.Broadcasted[B, sc.RawAxis]:
        # `give_names` is accepted for interface compatibility with Operator.bc_signature()
        # (monkey-patched in Operators.py) but ignored — axis names come from UIDs.
        # `signature` must be empty; TensorEquation derives contraction structure from
        # axis UID identity, not from a string.
        #
        # Produces a homogeneously-typed Broadcasted: every weave (input and
        # output) shares the same `datatype`. This is intentional — Broadcasted
        # is parameterised by a single B, and bc_signature() is the path for
        # display, morphism composition, and structurally-typed reasoning.
        #
        # For equations whose tensors have mixed datatypes (e.g. a Natural-valued
        # embedding index alongside Reals-valued weights), use
        # acset.convert.from_tensor_equation() instead. That path produces an
        # SBrInstance where each ArrayRow carries its own datatype_tag, at the
        # cost of losing the Broadcasted type parameter.
        #
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
        if signature:
            raise ValueError(
                "TensorEquation.bc_signature() derives contraction structure from "
                f"axis UID identity; string signatures are not accepted (got {signature!r})"
            )
        degree = self.lhs_indices
        retained_uid_to_pos = {ax.uid: i for i, ax in enumerate(degree)}
        _dt = array_datatypes or {}

        input_weaves = tuple(
            bc.Weave(
                _dt.get(factor.name, datatype) if isinstance(factor, TensorRef) else bc.Bool(),
                tuple(
                    bc.WeaveMode.TILED if ax.uid in retained_uid_to_pos else ax
                    for ax in _factor_axes(factor)
                ),
            )
            for factor in self.rhs
        )
        out_dt = _dt.get(self.lhs_name, datatype) if self.lhs_name else datatype
        output_weave = bc.Weave(
            out_dt,
            tuple(bc.WeaveMode.TILED for _ in degree),
        )
        reindexings = tuple(
            pc.Rearrangement(
                mapping=tuple(
                    retained_uid_to_pos[ax.uid]
                    for ax in _factor_axes(factor)
                    if ax.uid in retained_uid_to_pos
                ),
                _dom=degree,
            )
            for factor in self.rhs
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

    def to_morphism(
        self,
        declarations: dict[fd.DynamicName, tuple[sc.RawAxis, ...]] | None = None,
        array_datatypes: dict[fd.DynamicName, bc.Datatype] | None = None,
    ) -> pc.Composed:
        ctx = fd.Context()
        morphisms = []
        name_to_axes: dict[fd.DynamicName | None, fd.Prod[sc.RawAxis]] = {}
        declarations = declarations or {}

        for eq in topological_sort(self.equations):
            # Unify declaration axes with lhs axes to propagate concrete sizes.
            if eq.lhs_name in declarations:
                decl_axes = declarations[eq.lhs_name]
                if len(decl_axes) != len(eq.lhs_indices):
                    raise ValueError(
                        f"declaration rank mismatch for {eq.lhs_name!r}: "
                        f"expected {len(eq.lhs_indices)}, got {len(decl_axes)}"
                    )
                for decl_ax, eq_ax in zip(decl_axes, eq.lhs_indices):
                    ctx.append_iter((decl_ax, eq_ax))
            seen_in_eq: set[fd.DynamicName | None] = set()
            for factor in eq.rhs:
                if not isinstance(factor, TensorRef):
                    continue  # Iverson factors have no tensor name to unify
                tensor_name = factor.name
                input_axes = factor.axes
                if tensor_name in name_to_axes and tensor_name not in seen_in_eq:
                    seen_in_eq.add(tensor_name)
                    prior_axes = name_to_axes[tensor_name]
                    if len(prior_axes) != len(input_axes):
                        raise ValueError(
                            f"axis rank mismatch for intermediate {tensor_name!r}: "
                            f"defined with rank {len(prior_axes)}, consumed with rank {len(input_axes)}"
                        )
                    for prior_ax, eq_ax in zip(prior_axes, input_axes):
                        ctx.append_iter((prior_ax, eq_ax))
                # Subsequent occurrences of the same intermediate tensor are
                # self-joins: skip unification so each reference keeps its own
                # axis UIDs. Size propagation for the extra reference requires
                # an explicit declaration.
            applied_eq = ctx.apply(eq)
            br = applied_eq.bc_signature(array_datatypes=array_datatypes)
            morphisms.append(br)
            name_to_axes[eq.lhs_name] = applied_eq.lhs_indices

        return pc.Composed(content=tuple(morphisms))


def topological_sort(
    equations: fd.Prod[TensorEquation],
) -> list[TensorEquation]:
    # Kahn's algorithm. Only intra-program names (those with a defining equation)
    # count as dependencies; external tensors (weights, inputs) are ignored.
    name_to_eq: dict[fd.DynamicName | None, TensorEquation] = {}
    for eq in equations:
        if eq.lhs_name in name_to_eq:
            raise ValueError(f"duplicate lhs_name {eq.lhs_name!r} in TensorProgram")
        name_to_eq[eq.lhs_name] = eq
    deps: dict[fd.DynamicName | None, set[fd.DynamicName | None]] = {
        eq.lhs_name: {
            factor.name for factor in eq.rhs
            if isinstance(factor, TensorRef) and factor.name in name_to_eq
        }
        for eq in equations
    }
    result: list[TensorEquation] = []
    ready: deque[TensorEquation] = deque(
        eq for eq in equations if not deps[eq.lhs_name]
    )
    processed_names: set[fd.DynamicName | None] = set()
    ready_names: set[fd.DynamicName | None] = {eq.lhs_name for eq in ready}
    while ready:
        eq = ready.popleft()
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
        cyclic = [eq.lhs_name for eq in equations if eq.lhs_name not in processed_names]
        raise ValueError(f"TensorProgram has cyclic equation dependencies: {cyclic!r}")
    return result
