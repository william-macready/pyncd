#!/usr/bin/env bash
# Lean-side logic algorithms; independent Python-standard-library oracles, no JAX execution.
set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
LEANNCD_ROOT=$(cd "$HERE/../.." && pwd)
OUT="$HERE/.cache/generated_evalplan_logic_smoke.py"
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
PYTHON="${PYTHON:-python3}"

mkdir -p "$HERE/.cache"
bash "$LEANNCD_ROOT/scripts/lake-build.sh" "$LEANNCD_ROOT" LeanNCD JaxExperiment
(
  cd "$LEANNCD_ROOT"
  "$LAKE" env lean --run "$HERE/EvalPlanLogicSmoke.lean" "$OUT"
)
"$PYTHON" "$HERE/evalplan_logic_smoke.py" "$OUT"
