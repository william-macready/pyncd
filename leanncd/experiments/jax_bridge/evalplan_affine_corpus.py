"""Full PropertyOracle corpus verifier for the ordered affine JAX reference."""

from __future__ import annotations

import copy
import importlib.util
import math
import os
import sys
import time
from pathlib import Path
from types import ModuleType

import jax

jax.config.update("jax_enable_x64", True)

import jax.numpy as jnp  # noqa: E402
import numpy as np  # noqa: E402

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

import evalplan_affine_runtime as rt  # noqa: E402
import evalplan_affine_smoke as curated  # noqa: E402

EXPECTED_COUNT = 3832
FEATURE_NAMES = (
    "nonzero_bias",
    "nonunit_or_multiaxis_coeff",
    "negative_invalid",
    "zero_coeff_row",
    "multiple_factors",
    "multiple_terms",
    "reduction_domain",
    "multiple_graph_nodes",
    "internal_read",
    "zero_extents",
    "empty_factors",
    "empty_terms",
)
FEATURE_BITS = {name: 1 << i for i, name in enumerate(FEATURE_NAMES)}

# Features absent from the bounded generated source grammar are attributed to the named Task 2
# fixtures that actually exercise them. Other fixtures may cover additional bits; this table only
# records the minimum evidence needed for the coverage gate.
CURATED_FEATURES = {
    "lookback": ("nonzero_bias", "negative_invalid"),
    "scale": ("nonunit_or_multiaxis_coeff",),
    "zeroCoeffRow": ("zero_coeff_row", "multiple_factors", "reduction_domain"),
    "termScope": ("multiple_terms", "reduction_domain"),
    "positionalGraph": ("multiple_graph_nodes", "internal_read", "multiple_terms"),
    "zeroOutput": ("zero_extents",),
    "zeroReduction": ("zero_extents", "reduction_domain", "multiple_factors"),
    "efp": ("empty_factors",),
    "eta": ("empty_terms",),
}


def load_module(path: Path, name: str) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load generated module from {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def reconstruct(entry: dict) -> jax.Array:
    shape = tuple(entry["shape"])
    expected_size = math.prod(shape) if shape else 1
    bits = np.asarray(entry["bits"], dtype=np.uint64)
    if bits.size != expected_size:
        raise AssertionError(
            f"malformed corpus tensor: shape {shape} needs {expected_size} values, got {bits.size}"
        )
    return jnp.asarray(bits.view(np.float64).reshape(shape))


def matches_bits(actual: jax.Array, entry: dict) -> bool:
    arr = np.asarray(actual)
    return (
        arr.dtype == np.float64
        and arr.shape == tuple(entry["shape"])
        and np.array_equal(
            arr.reshape(-1).view(np.uint64), np.asarray(entry["bits"], dtype=np.uint64)
        )
    )


def selected_expected(case: dict, last_only: bool) -> list[tuple[str, dict]]:
    expected = case["expected"]
    return expected[-1:] if last_only else expected


def check_case(case: dict, *, jitted: bool, last_only: bool) -> int:
    inputs = {name: reconstruct(entry) for name, entry in case["inputs"].items()}
    plan = case["plan"]
    if jitted:
        actual = jax.jit(lambda xs: rt.run_named(plan, xs))(inputs)
    else:
        actual = rt.run_named(plan, inputs)
    mismatches = 0
    for name, expected in selected_expected(case, last_only):
        if name not in actual or not matches_bits(actual[name], expected):
            mismatches += 1
    return mismatches


def corrupt_earlier_output(cases: list[dict]) -> int:
    for case in cases:
        if len(case["expected"]) >= 2 and case["expected"][0][1]["bits"]:
            case["expected"][0][1]["bits"][0] ^= 1
            return case["index"]
    raise AssertionError("mutation requires a two-output case with a nonempty earlier output")


def run_curated(fixtures: list[dict]) -> None:
    for fixture in fixtures:
        kind = fixture["kind"]
        if kind == "named":
            curated.run_named_fixture(fixture)
        elif kind == "assign":
            curated.run_assign_fixture(fixture)
        elif kind == "positional":
            curated.run_positional_fixture(fixture)
        else:
            raise AssertionError(f"unknown curated fixture kind {kind!r}")


def feature_union(masks: list[int]) -> int:
    result = 0
    for mask in masks:
        result |= mask
    return result


def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit(
            f"usage: {Path(sys.argv[0]).name} CORPUS_MODULE CURATED_MODULE GENERATION_SECONDS"
        )
    rt.require_x64()
    corpus_path = Path(sys.argv[1]).resolve()
    corpus_module = load_module(corpus_path, "generated_evalplan_affine_corpus")
    curated_module = load_module(Path(sys.argv[2]).resolve(), "generated_evalplan_affine_curated")
    generation_seconds = float(sys.argv[3])

    if corpus_module.FEATURE_BITS != FEATURE_BITS:
        raise AssertionError(
            f"Lean/Python feature-bit tables differ: {corpus_module.FEATURE_BITS} != {FEATURE_BITS}"
        )
    if corpus_module.SOURCE_CASE_COUNT != EXPECTED_COUNT:
        raise AssertionError(
            f"expected source count {EXPECTED_COUNT}, got {corpus_module.SOURCE_CASE_COUNT}"
        )
    cases = copy.deepcopy(corpus_module.CASES)
    if len(cases) != EXPECTED_COUNT:
        raise AssertionError(f"expected {EXPECTED_COUNT} emitted cases, got {len(cases)}")
    if [case["index"] for case in cases] != list(range(EXPECTED_COUNT)):
        raise AssertionError("corpus case indices are not stable contiguous source indices")

    corrupt = os.environ.get("JAX_CORPUS_CORRUPT_EARLIER") == "1"
    last_only = os.environ.get("JAX_CORPUS_LAST_ONLY") == "1"
    corrupted_index = corrupt_earlier_output(cases) if corrupt else None

    eager_start = time.perf_counter()
    eager_mismatches = sum(check_case(case, jitted=False, last_only=last_only) for case in cases)
    eager_seconds = time.perf_counter() - eager_start
    if eager_mismatches:
        raise AssertionError(
            f"full corpus comparison found {eager_mismatches} mismatches across {len(cases)} cases"
        )

    representatives: dict[int, dict] = {}
    for case in cases:
        representatives.setdefault(case["feature_mask"], case)

    jit_start = time.perf_counter()
    jit_mismatches = sum(
        check_case(case, jitted=True, last_only=last_only)
        for case in representatives.values()
    )
    fixtures = curated_module.FIXTURES
    run_curated(fixtures)
    jit_seconds = time.perf_counter() - jit_start
    if jit_mismatches:
        raise AssertionError(f"JIT representatives produced {jit_mismatches} mismatches")

    generated_eager_mask = feature_union([case["feature_mask"] for case in cases])
    generated_jit_mask = feature_union(list(representatives))
    curated_mask = feature_union(
        [
            feature_union([FEATURE_BITS[name] for name in CURATED_FEATURES.get(f["name"], ())])
            for f in fixtures
        ]
    )
    required_mask = feature_union(list(FEATURE_BITS.values()))
    missing_eager = required_mask & ~(generated_eager_mask | curated_mask)
    missing_jit = required_mask & ~(generated_jit_mask | curated_mask)
    if missing_eager or missing_jit:
        missing = lambda mask: [name for name, bit in FEATURE_BITS.items() if mask & bit]
        raise AssertionError(
            f"missing required feature attribution: eager={missing(missing_eager)}, "
            f"jit={missing(missing_jit)}"
        )

    generated_features = [
        name for name, bit in FEATURE_BITS.items() if generated_eager_mask & bit
    ]
    curated_only = [
        name
        for name, bit in FEATURE_BITS.items()
        if curated_mask & bit and not generated_eager_mask & bit
    ]
    artifact_bytes = corpus_path.stat().st_size
    total_jit_cases = len(representatives) + len(fixtures)

    print(f"JAX {jax.__version__} on {jax.default_backend()}: {jax.devices()}")
    print(
        f"corpus: source_cases={len(cases)} eager_mismatches={eager_mismatches} "
        f"feature_masks={len(representatives)} jit_cases={total_jit_cases} "
        f"(corpus_representatives={len(representatives)}, curated={len(fixtures)})"
    )
    print(
        f"artifact_bytes={artifact_bytes} generation_seconds={generation_seconds:.3f} "
        f"eager_seconds={eager_seconds:.3f} jit_seconds={jit_seconds:.3f}"
    )
    print(f"generated feature coverage: {', '.join(generated_features)}")
    print(f"curated-only feature coverage: {', '.join(curated_only)}")
    if corrupt:
        mode = "last-output-only comparison missed" if last_only else "full comparison detected"
        print(f"mutation: corrupted earlier output in case {corrupted_index}; {mode}")
    print("full Wave C affine corpus -> ordered JAX reference -> Dense agreement passed")


if __name__ == "__main__":
    main()
