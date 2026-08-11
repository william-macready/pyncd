#!/usr/bin/env bash

set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
LEANNCD_ROOT=$(cd "$HERE/../.." && pwd)
CACHE_DIR="$HERE/.cache"
GENERATED="$CACHE_DIR/generated_evalplan_affine_smoke.py"
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
PYTHON="${PYTHON:-$CACHE_DIR/python/bin/python}"

if [[ ! -x "$LAKE" ]]; then
  echo "Lake not found at $LAKE; set LAKE to the executable path." >&2
  exit 1
fi
if [[ ! -x "$PYTHON" ]]; then
  echo "Experiment Python not found at $PYTHON; run ./setup-python.sh first (or set PYTHON)." >&2
  exit 1
fi
if ! "$PYTHON" -c 'import jax' >/dev/null 2>&1; then
  echo "JAX is not installed for $PYTHON; run ./setup-python.sh first." >&2
  exit 1
fi

mkdir -p "$CACHE_DIR"

# Build LeanNCD (production), the non-default JaxExperiment codegen library, and Tests (the affine
# smoke reuses the public `Eval.Plan.KernelDenseTest` checked-kernel fixtures), then generate the
# static affine plan data. Building through Elan from LeanNCD's own toolchain root; stays inside the
# already-warm project (no upstream clone, no cold Mathlib build).
(
  cd "$LEANNCD_ROOT"
  "$LAKE" build LeanNCD
  "$LAKE" build JaxExperiment
  "$LAKE" build Tests
  "$LAKE" env lean --run "$HERE/EvalPlanAffineSmoke.lean" "$GENERATED"
)

"$PYTHON" "$HERE/evalplan_affine_smoke.py" "$GENERATED"
