#!/usr/bin/env bash
# Compile a Lean snippet against the real leanncd environment.
#
# Exists so that "verify plan code compiles before writing it into the plan"
# costs one command instead of six. Plan code that merely *looks* right fails
# in Lean far more often than in most languages — real examples from Wave C:
#
#   decide (e1.error = e2.error)   -- EvalError has no DecidableEq (Float field)
#   structure Checked where private -- does NOT privatize; needs `private mk ::`
#   tlprog!{ axis i : N = size }    -- axis sizes must be literals, not variables
#
# Each of those looked fine on the page. Each cost a fix round or a review cycle.
#
# Usage:
#   check-snippet.sh <file.lean>     compile a snippet file you already wrote
#   check-snippet.sh -               read the snippet from stdin
#
# Writes into leanncd/spikes/ (gitignored scratch) under a unique name and
# removes it afterward, so nothing is left behind on success or failure.

set -euo pipefail

if [[ $# -ne 1 ]]; then
  sed -n '2,20p' "$0"
  exit 2
fi

REPO_ROOT=$(git rev-parse --show-toplevel)
SPIKES="$REPO_ROOT/leanncd/spikes"
LAKE="$HOME/.elan/bin/lake"

if [[ ! -x "$LAKE" ]]; then
  echo "check-snippet: lake not found at $LAKE" >&2
  exit 1
fi

mkdir -p "$SPIKES"
NAME="SnippetCheck_$$_${RANDOM}"
TARGET="$SPIKES/$NAME.lean"

cleanup() {
  rm -f "$TARGET"
  # lake may emit build artifacts for the scratch module; drop those too.
  find "$REPO_ROOT/leanncd/.lake/build" -name "$NAME.*" -delete 2>/dev/null || true
}
trap cleanup EXIT

if [[ "$1" == "-" ]]; then
  cat > "$TARGET"
else
  [[ -f "$1" ]] || { echo "check-snippet: no such file: $1" >&2; exit 1; }
  cp "$1" "$TARGET"
fi

echo "Compiling snippet as leanncd/spikes/$NAME.lean ..."
echo

cd "$REPO_ROOT/leanncd"
if "$LAKE" env lean "spikes/$NAME.lean"; then
  echo
  echo "COMPILES. Safe to write into the plan."
else
  status=$?
  echo
  echo "DOES NOT COMPILE (exit $status). Fix the snippet before putting it in a plan —"
  echo "  a plan that ships uncompilable code costs an implementer a fix round."
  exit $status
fi
