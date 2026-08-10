#!/usr/bin/env bash

set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
CACHE_DIR="$HERE/.cache"
UPSTREAM_DIR="$CACHE_DIR/lean4-mlir"
GENERATED="$CACHE_DIR/generated_bridge_smoke.py"
UPSTREAM_URL="https://github.com/brettkoonce/lean4-mlir.git"
UPSTREAM_REV="4f91e2a32d7eda0fc44f02a4b04c2fa0e5f59dab"
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
PYTHON="${PYTHON:-$CACHE_DIR/python/bin/python}"

if [[ ! -x "$LAKE" ]]; then
  echo "Lake not found at $LAKE; set LAKE to the executable path." >&2
  exit 1
fi
if [[ ! -x "$PYTHON" ]]; then
  echo "Experiment Python not found at $PYTHON; run ./setup-python.sh first." >&2
  exit 1
fi
if ! "$PYTHON" -c 'import jax' >/dev/null 2>&1; then
  echo "JAX is not installed for $PYTHON; run ./setup-python.sh first." >&2
  exit 1
fi

mkdir -p "$CACHE_DIR"
if [[ ! -d "$UPSTREAM_DIR/.git" ]]; then
  mkdir -p "$UPSTREAM_DIR"
  git -C "$UPSTREAM_DIR" init
  git -C "$UPSTREAM_DIR" remote add origin "$UPSTREAM_URL"
fi

if [[ "$(git -C "$UPSTREAM_DIR" rev-parse HEAD 2>/dev/null || true)" != "$UPSTREAM_REV" ]]; then
  git -C "$UPSTREAM_DIR" fetch --depth 1 origin "$UPSTREAM_REV"
  git -C "$UPSTREAM_DIR" checkout --detach FETCH_HEAD
fi

while IFS= read -r git_dir; do
  checkout=${git_dir%/.git}
  if [[ -n "$(git -C "$checkout" status --porcelain)" ]]; then
    echo "Cached checkout is dirty: $checkout" >&2
    echo "Remove $CACHE_DIR and rerun to restore pinned sources." >&2
    exit 1
  fi
done < <(find "$UPSTREAM_DIR" -type d -name .git -print -prune)

(
  cd "$UPSTREAM_DIR/jax"
  "$LAKE" build Jax
  "$LAKE" env lean --run "$HERE/BridgeSmoke.lean" "$GENERATED"
)

"$PYTHON" "$HERE/smoke.py" "$GENERATED"
