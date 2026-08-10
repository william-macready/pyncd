from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from types import ModuleType

import jax
import jax.numpy as jnp
import numpy as np


def load_generated_module(path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location("generated_bridge_smoke", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load generated module from {path}")

    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} GENERATED_MODULE")

    generated_path = Path(sys.argv[1]).resolve()
    module = load_generated_module(generated_path)

    inputs = jnp.asarray([[1.0, -2.0]], dtype=jnp.float32)
    params = module.init_params(jax.random.PRNGKey(0))
    eager = module.forward(params, inputs)
    compiled = jax.jit(module.forward)(params, inputs)
    gradients = jax.grad(lambda p: jnp.sum(module.forward(p, inputs)))(params)

    if eager.shape != (1, 1):
        raise AssertionError(f"unexpected output shape: {eager.shape}")
    np.testing.assert_allclose(eager, compiled, rtol=1e-6, atol=1e-6)
    if not np.all(np.isfinite(np.asarray(eager))):
        raise AssertionError(f"non-finite output: {eager}")
    if not all(np.all(np.isfinite(np.asarray(leaf))) for leaf in jax.tree.leaves(gradients)):
        raise AssertionError("autodiff produced non-finite gradients")

    print(f"JAX {jax.__version__} on {jax.default_backend()}: {jax.devices()}")
    print(f"eager/jit output: {np.asarray(eager).tolist()}")
    print(f"autodiff leaves: {len(jax.tree.leaves(gradients))}")
    print("Lean -> generated Python -> JAX evaluation smoke test passed")


if __name__ == "__main__":
    main()
