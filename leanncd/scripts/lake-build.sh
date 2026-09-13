#!/usr/bin/env bash
# Build Lake targets from a specified leanncd checkout using that checkout's
# pinned Lean toolchain. This gives permission rules one stable command shape
# without relying on a caller-side `cd` or an explicit Elan toolchain override.
#
# Usage:
#   lake-build.sh <leanncd-dir> [lake-target...]

set -euo pipefail

# Repository identity must come from the paths below, never caller-supplied Git overrides.
unset GIT_DIR GIT_WORK_TREE GIT_COMMON_DIR GIT_INDEX_FILE

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)

git_common_dir() {
  local repo=$1 common
  common=$(git -C "$repo" rev-parse --git-common-dir 2>/dev/null) || return 1
  if [[ "$common" != /* ]]; then
    common="$repo/$common"
  fi
  cd -- "$common" && pwd -P
}

is_registered_worktree() {
  local repo=$1 target=$2 field
  while IFS= read -r -d '' field; do
    if [[ "$field" == "worktree $target" ]]; then
      return 0
    fi
  done < <(git -C "$repo" worktree list --porcelain -z)
  return 1
}

if [[ $# -lt 1 ]]; then
  sed -n '2,7p' "$0"
  exit 125
fi

leanncd_dir=$1
shift

cd -- "$leanncd_dir" || exit 125
leanncd_dir=$(pwd -P)

script_repo=$(git -C "$script_dir/../.." rev-parse --show-toplevel 2>/dev/null) || exit 125
script_repo=$(realpath -- "$script_repo")
script_common=$(git_common_dir "$script_repo") || exit 125
target_repo=$(dirname -- "$leanncd_dir")
if [[ "$leanncd_dir" != "$target_repo/leanncd" ]] ||
   ! is_registered_worktree "$script_repo" "$target_repo"; then
  echo "error: $leanncd_dir is not a registered worktree's leanncd checkout" >&2
  exit 125
fi
target_repo=$(git -C "$leanncd_dir" rev-parse --show-toplevel 2>/dev/null) || {
  echo "error: $leanncd_dir is not in a Git worktree" >&2
  exit 125
}
target_repo=$(realpath -- "$target_repo")
target_common=$(git_common_dir "$target_repo") || exit 125

if [[ "$target_common" != "$script_common" || ! -f lakefile.toml || ! -f lean-toolchain ]]; then
  echo "error: $leanncd_dir is not this repository's leanncd checkout" >&2
  exit 125
fi

"$HOME/.elan/bin/lake" build "$@"
