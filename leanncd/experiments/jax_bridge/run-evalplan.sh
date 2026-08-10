#!/usr/bin/env bash

set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
LEANNCD_ROOT=$(cd "$HERE/../.." && pwd)
CACHE_DIR="$HERE/.cache"
GENERATED="$CACHE_DIR/generated_evalplan_smoke.py"
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

# Build LeanNCD (through Elan, from LeanNCD's own toolchain root) before generating, so
# `lake env lean --run` below never checks the generator against stale .oleans. Deliberately does
# not touch upstream `run.sh`, clone `lean4-mlir`, or trigger a cold Mathlib build: this stays
# entirely inside LeanNCD's already-warm Lean 4.30.0 project.
(
  cd "$LEANNCD_ROOT"
  "$LAKE" build LeanNCD
  "$LAKE" env lean --run "$HERE/EvalPlanSmoke.lean" "$GENERATED"
)

"$PYTHON" "$HERE/evalplan_smoke.py" "$GENERATED"
