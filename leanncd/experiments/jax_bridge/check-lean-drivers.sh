#!/usr/bin/env bash
# Lean-side regression check for the four JAX-bridge drivers. NO Python and NO JAX: it only runs the
# Lean generators and fails if any of them exits non-zero.
#
# Why: the drivers are `lake env lean --run` scripts outside every Lake target (`JaxExperiment` globs
# only `EvalPlanCodegen`), so `lake build` never touches them. A precision-default or signature change
# breaks them at RUN time (a typed rejection from `prepareEvalPlan`, not a type error), so merely
# typechecking them would not catch it. The F32 default flip broke all four silently.
# Run it whenever a precision default, a storage rule or an `InputSignature` constructor changes.
#
# Usage: ./check-lean-drivers.sh [STRIDE]
# STRIDE: corpus sampling for EvalPlanAffineSmoke32 (default 100, as run-evalplan-affine32.sh).

set -uo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
LEANNCD_ROOT=$(cd "$HERE/../.." && pwd)
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
STRIDE="${1:-100}"

if [[ ! -x "$LAKE" ]]; then
  echo "Lake not found at $LAKE; set LAKE to the executable path." >&2
  exit 1
fi

OUT=$(mktemp -d "${TMPDIR:-/tmp}/jax-driver-check.XXXXXX")
trap 'rm -rf "$OUT"' EXIT

cd "$LEANNCD_ROOT" || exit 1

# Refresh the libraries first: with stale oleans the drivers abort (`lean::exception: incomplete
# case`, exit 134) even on a correct tree. Every dependency is named, never a bare `lake build`
# (that would leak through defaultTargets); Tests is imported by the affine drivers.
echo "== building LeanNCD JaxExperiment Tests"
# The build replays every library warning; keep it out of the output unless the build fails.
if ! "$LAKE" build LeanNCD JaxExperiment Tests >"$OUT/build.log" 2>&1; then
  tail -n 40 "$OUT/build.log"
  echo "FAIL: library build"
  exit 1
fi

failed=()
run_driver() {
  local name=$1; shift
  echo "== running $name"
  if "$LAKE" env lean --run "$HERE/$name.lean" "$@"; then
    echo "PASS  $name"
  else
    echo "FAIL  $name (exit $?)"
    failed+=("$name")
  fi
}

run_driver EvalPlanSmoke "$OUT/evalplan_smoke.py"
run_driver EvalPlanAffineSmoke "$OUT/evalplan_affine_smoke.py"
run_driver EvalPlanAffineCorpus "$OUT/evalplan_affine_corpus.py"
run_driver EvalPlanAffineSmoke32 "$OUT/evalplan_affine_smoke32.py" "$STRIDE"

if [[ ${#failed[@]} -gt 0 ]]; then
  echo "FAILED drivers: ${failed[*]}"
  exit 1
fi
echo "all four drivers ran clean (Lean side only; the Python/JAX verifiers were not run)"
