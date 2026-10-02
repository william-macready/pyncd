#!/usr/bin/env bash
# Binary32 affineReference check (slice F32-JAX): the 7 named fixtures (6 spike + `termSum64`), 8
# standalone-assign and 2 positional fixtures, plus every STRIDE-th PropertyOracle corpus case
# retagged binary32, through the production gates and the shared ordered runtime with x64 disabled.
# Usage: ./run-evalplan-affine32.sh [STRIDE [JIT_STRIDE]]
# STRIDE: corpus sampling (default 100; 1 = all 3,832). JIT_STRIDE: JIT every JIT_STRIDE-th corpus
# case (default 1 = every case); non-corpus fixtures are always JIT-checked.

set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
LEANNCD_ROOT=$(cd "$HERE/../.." && pwd)
CACHE_DIR="$HERE/.cache"
GENERATED="$CACHE_DIR/generated_evalplan_affine_smoke32.py"
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
PYTHON="${PYTHON:-$CACHE_DIR/python/bin/python}"
STRIDE="${1:-100}"
JIT_STRIDE="${2:-1}"

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
  "$LAKE" build Tests
  "$LAKE" env lean --run "$HERE/EvalPlanAffineSmoke32.lean" "$GENERATED" "$STRIDE"
)

"$PYTHON" "$HERE/evalplan_affine_smoke32.py" "$GENERATED" "$JIT_STRIDE"
