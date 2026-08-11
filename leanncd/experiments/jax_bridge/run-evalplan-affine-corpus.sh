#!/usr/bin/env bash

set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
LEANNCD_ROOT=$(cd "$HERE/../.." && pwd)
CACHE_DIR="$HERE/.cache"
GENERATED="$CACHE_DIR/generated_evalplan_affine_corpus.py"
CURATED="$CACHE_DIR/generated_evalplan_affine_smoke.py"
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

(
  cd "$LEANNCD_ROOT"
  # Every dependency is named explicitly. In particular, importing PropertyOracle.Gen requires
  # Tests and importing EvalPlanCodegen requires the non-default JaxExperiment library; never call
  # bare `lake build` here, which would leak through defaultTargets.
  "$LAKE" build LeanNCD Tests JaxExperiment
)

START_NS=$("$PYTHON" -c 'import time; print(time.perf_counter_ns())')
(
  cd "$LEANNCD_ROOT"
  "$LAKE" env lean --run "$HERE/EvalPlanAffineCorpus.lean" "$GENERATED"
  "$LAKE" env lean --run "$HERE/EvalPlanAffineSmoke.lean" "$CURATED"
)
END_NS=$("$PYTHON" -c 'import time; print(time.perf_counter_ns())')
GENERATION_SECONDS=$("$PYTHON" -c "print(($END_NS - $START_NS) / 1_000_000_000)")

"$PYTHON" "$HERE/evalplan_affine_corpus.py" "$GENERATED" "$CURATED" "$GENERATION_SECONDS"
