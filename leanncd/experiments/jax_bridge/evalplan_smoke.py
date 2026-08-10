from __future__ import annotations

import ast
import importlib.util
import sys
from pathlib import Path
from types import ModuleType

import jax

# Item 1: enable JAX x64 before importing anything from the generated module. The generated
# module's INPUT_BITS/EXPECTED_OUTPUT_BITS are exact float64 bit patterns (`Float.toBits`
# payloads); reconstructing them into anything narrower than float64 would silently corrupt the
# fixture's exactly-representable values before a single tensor op runs.
jax.config.update("jax_enable_x64", True)

import jax.numpy as jnp  # noqa: E402  (must follow the x64 config update above)
import numpy as np  # noqa: E402


def load_generated_module(path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location("generated_evalplan_smoke", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load generated module from {path}")

    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def bits_to_float64(bits: list[int], shape: tuple[int, ...]) -> np.ndarray:
    """Reconstructs an exact float64 array from `Float.toBits` payloads (item 2 / item 6)."""
    return np.array(bits, dtype=np.uint64).view(np.float64).reshape(shape)


def require_real_einsum_call(source: str, expected_subscripts: str) -> None:
    """Item 3: an AST-level requirement that the generated source contains a real `jnp.einsum`
    call whose literal first argument is exactly `expected_subscripts`. Numeric agreement alone
    (checked separately below) cannot distinguish a real `einsum` lowering from a hand-written
    `@`/`matmul`/constant that happens to produce the same numbers — this walks the parsed AST,
    not the source text, so it cannot be fooled by a matching comment or string wrapped in
    something else.
    """
    tree = ast.parse(source)
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if not (isinstance(func, ast.Attribute) and func.attr == "einsum"):
            continue
        if not (isinstance(func.value, ast.Name) and func.value.id == "jnp"):
            continue
        if not node.args:
            continue
        first_arg = node.args[0]
        if isinstance(first_arg, ast.Constant) and first_arg.value == expected_subscripts:
            return
    raise AssertionError(
        f"no jnp.einsum({expected_subscripts!r}, ...) call found in generated source"
    )


def require_bit_identical(actual: jax.Array, expected: np.ndarray, label: str) -> None:
    actual_np = np.asarray(actual)
    if actual_np.dtype != np.float64:
        raise AssertionError(f"{label}: expected float64, got {actual_np.dtype}")
    if not np.array_equal(actual_np.view(np.uint64), expected.view(np.uint64)):
        raise AssertionError(f"{label}: not bit-identical to Dense: {actual_np} vs {expected}")


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} GENERATED_MODULE")

    generated_path = Path(sys.argv[1]).resolve()
    source = generated_path.read_text()

    # Item 3: require the AST-level einsum call before trusting anything the module computes.
    require_real_einsum_call(source, "ab,b->a")

    module = load_generated_module(generated_path)

    # Item 2: reconstruct inputs from the Lean-emitted shapes and bit payloads.
    inputs = {
        name: jnp.asarray(bits_to_float64(bits, module.INPUT_SHAPES[name]))
        for name, bits in module.INPUT_BITS.items()
    }

    # Item 6: reconstruct Dense's expected output the same way, independent of the generated
    # `forward` lowering.
    expected = bits_to_float64(module.EXPECTED_OUTPUT_BITS, module.EXPECTED_OUTPUT_SHAPE)
    expected_name = module.EXPECTED_OUTPUT_NAME

    # Item 4: eager forward.
    eager = module.forward(inputs)[expected_name]
    # Item 5: jax.jit forward.
    jitted = jax.jit(module.forward)(inputs)[expected_name]

    # Item 7: require eager and JIT to be bit-identical to Dense.
    require_bit_identical(eager, expected, "eager output")
    require_bit_identical(jitted, expected, "jit output")

    # Item 8: differentiate sum(Y) with respect to W and require [[5], [5]].
    def loss(w: jax.Array) -> jax.Array:
        call_inputs = dict(inputs)
        call_inputs["W"] = w
        return jnp.sum(module.forward(call_inputs)[expected_name])

    grad_w = jax.grad(loss)(inputs["W"])
    expected_grad_w = np.array([[5.0], [5.0]], dtype=np.float64)
    if grad_w.dtype != jnp.float64:
        raise AssertionError(f"grad(sum(Y), W): expected float64, got {grad_w.dtype}")
    if not np.array_equal(np.asarray(grad_w), expected_grad_w):
        raise AssertionError(f"grad(sum(Y), W) mismatch: got {np.asarray(grad_w)}")

    # Item 9: print the generated lowering kind, outputs, and gradient on success.
    print(f"JAX {jax.__version__} on {jax.default_backend()}: {jax.devices()}")
    print("lowering: jnp.einsum(\"ab,b->a\", ...) (confirmed by AST)")
    print(f"eager/jit {expected_name}: {np.asarray(eager).tolist()}")
    print(f"grad(sum({expected_name}), W): {np.asarray(grad_w).tolist()}")
    print("Lean checked plan -> generated jnp.einsum -> JAX evaluation smoke test passed")


if __name__ == "__main__":
    main()
