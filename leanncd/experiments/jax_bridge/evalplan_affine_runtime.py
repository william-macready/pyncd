"""Generic ordered affine reference runtime for the Wave C JAX bridge.

This committed module executes STATIC plan data emitted by `EvalPlanCodegen.renderAffine*`
(`docs/superpowers/plans/2026-08-10-jax-full-affine-semantics.md`, Task 2). It owns only execution;
it computes no affine addresses of its own — every source index and validity mask was precomputed in
Lean with arbitrary-precision `Int` arithmetic and the shared `Eval.Plan.Coordinates` primitives.

Load-bearing properties (whole-branch review gate):

* **x64 required at the caller boundary.** `require_x64()` fails loud before any bit comparison.
  Float64 values are created only during execution, after that gate can have been enabled; importing
  this module while x64 is disabled cannot cache a silently narrowed scalar.
* **Safe index + mask zero padding.** A factor gathers ONLY through the precomputed safe indices
  (invalid entries carry the placeholder `0`) and re-zeros invalid entries with `jnp.where(mask, …,
  0.0)`. It never relies on JAX's own out-of-bounds gather, which may clamp rather than zero-pad.
* **No gather from empty source storage.** When a source tensor holds zero elements, an all-zero
  factor tensor is emitted directly — no index access is attempted.
* **Explicit ordered folds.** Factor products, per-row reductions, and term sums are each folded
  with a sequential `jax.lax.fori_loop` carry (reductions under `jax.vmap`), preserving Dense's
  source-declared `reference64` fold order rather than an XLA-chosen tree reduction.
* **Empty/zero boundaries.** An empty factor array yields ones; an empty term array yields an
  all-zero output; a zero reduction extent yields zeros; a zero output extent yields empty storage.
* **Graph order.** Positional nodes execute in checked order, each writing its destination slot
  before any later node reads it.
* **Differentiable** with respect to the floating input tensors (integer gather + `where` + loops).
"""

from __future__ import annotations

import math
from typing import Any

import jax
import jax.numpy as jnp

def require_x64() -> None:
    """Fail loud if JAX x64 is not enabled before reference execution."""
    if not jax.config.read("jax_enable_x64"):
        raise RuntimeError(
            "jax_enable_x64 must be enabled before running the affine reference runtime; "
            "the reference64 mode requires exact float64 arithmetic."
        )


def _prod(xs: list[int]) -> int:
    return math.prod(xs) if xs else 1


def _run_term(term: dict[str, Any], store: list[jax.Array]) -> jax.Array:
    iter_shape = tuple(term["iteration_shape"])
    output_pos = list(term["output_pos"])
    reduction_pos = list(term["reduction_pos"])
    factors = term["factors"]

    out_extents = [iter_shape[p] for p in output_pos]
    red_extents = [iter_shape[p] for p in reduction_pos]
    output_size = _prod(out_extents)
    reduction_size = _prod(red_extents)

    # A zero output extent yields empty storage; a zero reduction extent yields `reduceId` (0.0) per
    # output coordinate (the reduction fold never runs). Both short-circuit to zeros of the output
    # shape and avoid any size-0 gather/index — matching Dense's `runDenseAssign`.
    if output_size == 0 or reduction_size == 0:
        return jnp.zeros(tuple(out_extents), dtype=jnp.float64)

    # --- gather one full iteration-space tensor per factor -------------------------------------
    factor_tensors: list[jax.Array] = []
    for f in factors:
        source = store[f["source_slot"]]
        src_flat = jnp.reshape(source, (-1,))
        if int(src_flat.shape[0]) == 0:
            # Empty source storage: emit an all-zero factor tensor without any index access.
            factor_tensors.append(jnp.zeros(iter_shape, dtype=jnp.float64))
            continue
        safe = jnp.asarray(f["safe_index"], dtype=jnp.int64)
        mask = jnp.asarray(f["mask"], dtype=bool)
        gathered = src_flat[safe]
        padded = jnp.where(mask, gathered, jnp.float64(0.0))
        factor_tensors.append(jnp.reshape(padded, iter_shape))

    # --- fold the factor product from 1.0 in factor-array order (empty ⇒ ones) ------------------
    ones = jnp.ones(iter_shape, dtype=jnp.float64)
    if not factor_tensors:
        product = ones
    else:
        stacked = jnp.stack(factor_tensors, axis=0)

        def factor_body(k, acc):
            return acc * stacked[k]

        product = jax.lax.fori_loop(0, len(factor_tensors), factor_body, ones)

    # --- transpose into outputPos ++ reductionPos, reshape to (outputSize, reductionSize) -------
    perm = output_pos + reduction_pos
    transposed = jnp.transpose(product, perm) if perm else product
    mat = jnp.reshape(transposed, (output_size, reduction_size))

    # --- per-row sequential reduction fold from 0.0 in reduction-coordinate order ---------------
    def reduce_row(row):
        def red_body(k, acc):
            return acc + row[k]

        return jax.lax.fori_loop(0, reduction_size, red_body, jnp.float64(0.0))

    reduced = jax.vmap(reduce_row)(mat)
    return jnp.reshape(reduced, tuple(out_extents))


def _run_node(node: dict[str, Any], store: list[jax.Array]) -> jax.Array:
    output_shape = tuple(node["output_shape"])
    terms = node["terms"]
    if not terms:
        # Empty term array yields an all-zero output.
        return jnp.zeros(output_shape, dtype=jnp.float64)

    term_results = [_run_term(t, store) for t in terms]
    stacked = jnp.stack(term_results, axis=0)

    def term_body(k, acc):
        return acc + stacked[k]

    zero = jnp.zeros(output_shape, dtype=jnp.float64)
    return jax.lax.fori_loop(0, len(terms), term_body, zero)


def run_assign(node: dict[str, Any], store: list[jax.Array]) -> jax.Array:
    """Execute one positional checked-assignment node against a positional store, returning one
    result tensor — the direct parallel of `runDenseAssign`."""
    return _run_node(node, store)


def run_plan_positional(plan: dict[str, Any], inputs: list[jax.Array]) -> list[jax.Array]:
    """Execute a positional `CheckedEvalPlan` over positional inputs (in `input_slots` order),
    returning the full positional slot store after every node has run in checked graph order."""
    num_slots = plan["num_slots"]
    store: list[Any] = [None] * num_slots
    for slot, tensor in zip(plan["input_slots"], inputs):
        store[slot] = tensor
    for node in plan["nodes"]:
        store[node["dest"]] = _run_node(node, store)
    return store


def run_named(plan: dict[str, Any], inputs_by_name: dict[str, jax.Array]) -> dict[str, jax.Array]:
    """Execute a named `PreparedPlan`: place inputs by source-name binding, run every node in graph
    order, then reconstruct each materialized name (later writes overwrite earlier ones, matching
    `Adapter.unpack`)."""
    num_slots = plan["num_slots"]
    store: list[Any] = [None] * num_slots
    for name, slot in plan["required_inputs"]:
        store[slot] = inputs_by_name[name]
    for node in plan["nodes"]:
        store[node["dest"]] = _run_node(node, store)
    outputs: dict[str, jax.Array] = {}
    for name, slot in plan["materialized"]:
        outputs[name] = store[slot]
    return outputs
