#!/usr/bin/env bash
# Pointwise/axiswise differential: generate the Lean fixtures (binary64 + binary32), then verify the
# committed runtime against the Lean reference worker's results within a measured tolerance in both
# precisions (JAX pointwise slice).
#
# Usage: ./run-evalplan-nonlin.sh        (needs ./setup-python.sh first)

set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
LEANNCD_ROOT=$(cd "$HERE/../.." && pwd)
CACHE_DIR="$HERE/.cache"
GEN64="$CACHE_DIR/generated_evalplan_nonlin_smoke64.py"
GEN32="$CACHE_DIR/generated_evalplan_nonlin_smoke32.py"
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

mkdir -p "$CACHE_DIR"
(
  cd "$LEANNCD_ROOT"
  "$LAKE" build LeanNCD
  "$LAKE" build JaxExperiment
  "$LAKE" build Eval.Plan.ScanCompileTest   # donor schedules for the scan survey fixtures
  "$LAKE" env lean --run "$HERE/EvalPlanNonlinSmoke.lean" "$GEN64" "$GEN32"
)

"$PYTHON" "$HERE/evalplan_nonlin_smoke.py" float64 "$GEN64"
"$PYTHON" "$HERE/evalplan_nonlin_smoke.py" float32 "$GEN32"
