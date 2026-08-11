"""Curated affine JAX reference verifier (`docs/superpowers/plans/2026-08-10-jax-full-affine-semantics.md`, Task 2).

Loads the Lean-generated static plan data + Dense expected bits (`generated_evalplan_affine_smoke.py`),
runs every hand fixture through the committed generic runtime (`evalplan_affine_runtime.py`) both
eagerly and under `jax.jit`, and requires exact dtype/shape/`UInt64`-bit agreement with Dense.
Additional gradient and fold-order low-bit assertions pin the semantics the exactly-representable
corpus cannot.
"""

from __future__ import annotations

import importlib.util
import math
import os
import subprocess
import sys
from pathlib import Path
from types import ModuleType

import jax

# Item: enable x64 at the caller boundary BEFORE importing jnp or the runtime. The reference64 mode
# is exact float64; anything narrower silently corrupts the bit fixtures.
jax.config.update("jax_enable_x64", True)

import jax.numpy as jnp  # noqa: E402  (must follow the x64 config update above)
import numpy as np  # noqa: E402

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

import evalplan_affine_runtime as rt  # noqa: E402


def load_generated_module(path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location("generated_evalplan_affine_smoke", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load generated module from {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def reconstruct(entry: dict) -> jax.Array:
    """Rebuild an exact float64 tensor from a `{"shape": .., "bits": ..}` entry. A destination-slot
    placeholder (declared shape, empty data) that the runtime never reads is materialized as zeros
    of the declared shape so the positional store stays well-formed."""
    shape = tuple(entry["shape"])
    bits = entry["bits"]
    size = math.prod(shape) if shape else 1
    arr = np.array(bits, dtype=np.uint64).view(np.float64)
    if arr.shape[0] != size:
        arr = np.zeros(size, dtype=np.float64)
    return jnp.asarray(arr.reshape(shape))


def require_bit_identical(actual: jax.Array, entry: dict, label: str) -> None:
    actual_np = np.asarray(actual)
    if actual_np.dtype != np.float64:
        raise AssertionError(f"{label}: expected float64, got {actual_np.dtype}")
    expected_shape = tuple(entry["shape"])
    if actual_np.shape != expected_shape:
        raise AssertionError(f"{label}: shape {actual_np.shape} != expected {expected_shape}")
    expected_bits = np.array(entry["bits"], dtype=np.uint64)
    actual_bits = actual_np.reshape(-1).view(np.uint64)
    if not np.array_equal(actual_bits, expected_bits):
        raise AssertionError(
            f"{label}: not bit-identical to Dense: {actual_bits.tolist()} vs {expected_bits.tolist()}"
        )


def run_named_fixture(f: dict) -> None:
    plan = f["plan"]
    inputs = {name: reconstruct(e) for name, e in f["inputs"].items()}
    eager = rt.run_named(plan, inputs)
    jitted = jax.jit(lambda inp: rt.run_named(plan, inp))(inputs)
    for name, exp in f["expected"].items():
        require_bit_identical(eager[name], exp, f"{f['name']} eager {name}")
        require_bit_identical(jitted[name], exp, f"{f['name']} jit {name}")


def run_assign_fixture(f: dict) -> None:
    node = f["assign"]
    store = [reconstruct(e) for e in f["store"]]
    eager = rt.run_assign(node, store)
    jitted = jax.jit(lambda s: rt.run_assign(node, s))(store)
    require_bit_identical(eager, f["expected"], f"{f['name']} eager")
    require_bit_identical(jitted, f["expected"], f"{f['name']} jit")


def run_positional_fixture(f: dict) -> None:
    plan = f["plan"]
    inputs = [reconstruct(e) for e in f["inputs"]]
    eager = rt.run_plan_positional(plan, inputs)
    jitted = jax.jit(lambda xs: rt.run_plan_positional(plan, xs))(inputs)
    for slot, exp in enumerate(f["expected_store"]):
        require_bit_identical(eager[slot], exp, f"{f['name']} eager slot {slot}")
        require_bit_identical(jitted[slot], exp, f"{f['name']} jit slot {slot}")


def check_import_before_x64() -> None:
    """A fresh process imports the runtime with x64 disabled, then enables it and executes eager/JIT."""
    code = """
import jax
assert not jax.config.read("jax_enable_x64")
import evalplan_affine_runtime as rt
jax.config.update("jax_enable_x64", True)
rt.require_x64()
import jax.numpy as jnp
node = {"dest": 1, "output_shape": [1], "terms": [{
    "iteration_shape": [1], "output_pos": [0], "reduction_pos": [],
    "factors": [{"source_slot": 0, "safe_index": [0], "mask": [False]}],
}]}
store = [jnp.asarray([7.0], dtype=jnp.float64), jnp.zeros((1,), dtype=jnp.float64)]
for actual in (rt.run_assign(node, store), jax.jit(lambda s: rt.run_assign(node, s))(store)):
    assert actual.dtype == jnp.float64
    assert int(actual.view(jnp.uint64)[0]) == 0
"""
    env = dict(os.environ)
    env["JAX_ENABLE_X64"] = "0"
    env["PYTHONPATH"] = str(_HERE)
    subprocess.run([sys.executable, "-c", code], check=True, env=env)


def check_grad_named(f: dict, wrt: str, expected_grad: list[float]) -> None:
    plan = f["plan"]
    inputs = {name: reconstruct(e) for name, e in f["inputs"].items()}
    out_name = next(iter(f["expected"]))

    def loss(a: jax.Array) -> jax.Array:
        call_inputs = dict(inputs)
        call_inputs[wrt] = a
        return jnp.sum(rt.run_named(plan, call_inputs)[out_name])

    grad = np.asarray(jax.grad(loss)(inputs[wrt]))
    if grad.dtype != np.float64:
        raise AssertionError(f"{f['name']} grad wrt {wrt}: expected float64, got {grad.dtype}")
    if not np.array_equal(grad, np.array(expected_grad, dtype=np.float64)):
        raise AssertionError(
            f"{f['name']} grad wrt {wrt}: got {grad.tolist()}, expected {expected_grad}"
        )


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} GENERATED_MODULE")

    # x64 dtype gate at the caller boundary, before any bit comparison.
    rt.require_x64()
    check_import_before_x64()

    module = load_generated_module(Path(sys.argv[1]).resolve())
    fixtures = module.FIXTURES
    by_name = {f["name"]: f for f in fixtures}

    named = [f for f in fixtures if f["kind"] == "named"]
    assign = [f for f in fixtures if f["kind"] == "assign"]
    positional = [f for f in fixtures if f["kind"] == "positional"]
    if len(named) != 9:
        raise AssertionError(f"expected 9 named source fixtures, got {len(named)}")
    if len(assign) != 10:
        raise AssertionError(f"expected 10 checked-assignment fixtures, got {len(assign)}")
    if len(positional) != 1:
        raise AssertionError(f"expected 1 positional graph fixture, got {len(positional)}")

    # Eager + JIT bit-exact agreement for every hand fixture.
    for f in named:
        run_named_fixture(f)
    for f in assign:
        run_assign_fixture(f)
    for f in positional:
        run_positional_fixture(f)

    # Gradient checks through the ordered runtime.
    check_grad_named(by_name["shift"], "A", [0.0, 1.0, 1.0])
    check_grad_named(by_name["scale"], "A", [1.0, 0.0, 1.0])

    # Reduction-order low-bit distinction: forward sequential fold of [1e16, 1, 1] lands on 1e16
    # (0x4341c37937e08000), NOT the reversed 1.0000000000000002e16 (0x4341c37937e08001). The eager
    # bit check above already pins this against Dense; assert the discriminating bit explicitly.
    ro_bits = by_name["reductionOrder"]["expected"]["Y"]["bits"][0]
    if ro_bits != 0x4341C37937E08000:
        raise AssertionError(f"reductionOrder expected bits {ro_bits:#018x} != 0x4341c37937e08000")

    # Term-order low-bit distinction: folding [1e16, 1, -1e16] in array order lands on 0.0, NOT the
    # reassociated 1.0 that grouping the ±1e16 terms first would give.
    fos_bits = by_name["fos"]["expected"]["bits"][0]
    if fos_bits != 0:
        raise AssertionError(f"fos expected bits {fos_bits:#018x} != 0x0 (0.0)")

    # Factor-order mutation: the exact finite, normal input bit patterns in the Lean fixture produce
    # adjacent binary64 outputs when `[a,b,c]` is reordered to `[b,c,a]`.
    factor_bits = by_name["factorOrder"]["expected"]["bits"][0]
    reordered_bits = by_name["factorOrderReordered"]["expected"]["bits"][0]
    if factor_bits != 0x52ACE21080787DC7 or reordered_bits != 0x52ACE21080787DC6:
        raise AssertionError(
            f"factor-order bits {factor_bits:#018x}, reordered {reordered_bits:#018x}"
        )

    print(f"JAX {jax.__version__} on {jax.default_backend()}: {jax.devices()}")
    print(
        f"affine reference: {len(named)} named + {len(assign)} checked-assignment"
        f" + {len(positional)} positional graph fixtures"
    )
    print("eager + jit bit-identical to Dense for every fixture")
    print("runtime import before x64 enable: eager + jit float64 zero bits passed")
    print("grad(sum(Y), A): shift=[0,1,1], scale=[1,0,1]")
    print("reduction-order bits 0x4341c37937e08000 (forward), term-order bits 0x0 (array order)")
    print("factor-order bits 0x52ace21080787dc7 (declared), 0x52ace21080787dc6 (reordered)")
    print("Lean checked plan -> affine lookup tables -> ordered JAX reference -> Dense agreement passed")


if __name__ == "__main__":
    main()
