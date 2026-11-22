#!/usr/bin/env bash
# Lean-side logic algorithms (max-plus Viterbi, Boolean reachability); independent Python-standard-library
# oracles, NO JAX execution: this checks only the Lean legs (reference, checked binary64/binary32).
# The same fixtures run on JAX, eager and jit in both precisions, under run-evalplan-maxplus.py
# (`python3 leanncd/experiments/jax_bridge/run-evalplan-maxplus.py --python /path/to/jax/python`).
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
