#!/usr/bin/env bash
# Apply one exact-match textual mutation to a Lean source file, build the given
# lake targets, report error/completion lines, then ALWAYS restore the file --
# on success, on build failure, or on interruption.
#
# Exists so a mutation-testing cycle (mutate -> observe the intended failure ->
# restore -> confirm pass -- the discipline this repo's slice plans require for
# every fixture) is one auditable command instead of an inline heredoc that no
# permission rule can safely allow-list: this script's logic is fixed and
# reviewed, so only its plain-string arguments vary between invocations.
#
# Usage:
#   mutate-and-build.sh <leanncd-dir> <file> <old-string> <new-string> <lake-target>...
#
# <leanncd-dir>  path to the leanncd/ checkout to operate in (any worktree)
# <file>         path to the .lean file, relative to <leanncd-dir>
# <old-string>   must occur in <file> EXACTLY ONCE, or the script refuses
# <new-string>   replacement text
#
# Exit code is lake's own build exit code (0 = build succeeded despite the
# mutation, usually meaning the mutation-cycle failed to prove anything;
# nonzero = the mutation broke the build, as a real fixture-guarding mutation
# should).

set -euo pipefail

if [[ $# -lt 5 ]]; then
  sed -n '2,21p' "$0"
  exit 2
fi

leanncd_dir=$1 file=$2 old=$3 new=$4
shift 4
targets=("$@")

cd -- "$leanncd_dir"
[[ -f lakefile.toml ]] || { echo "error: $leanncd_dir is not a leanncd checkout (no lakefile.toml)" >&2; exit 2; }
[[ -f "$file" ]] || { echo "error: no such file: $file (relative to $leanncd_dir)" >&2; exit 2; }

backup=$(mktemp)
logfile=$(mktemp)
cleanup() { cp -- "$backup" "$file"; rm -f -- "$backup" "$logfile"; }
trap cleanup EXIT
cp -- "$file" "$backup"

python3 - "$file" "$old" "$new" <<'PY'
import sys
path, old, new = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(path).read()
n = s.count(old)
if n != 1:
    sys.exit(f"error: old-string occurs {n} times in {path} (expected exactly 1)")
open(path, "w").write(s.replace(old, new))
PY

echo "--- mutated $file: '$old' -> '$new' ---"

set +e
"$HOME/.elan/bin/lake" build "${targets[@]}" > "$logfile" 2>&1
build_status=$?
set -e

grep -E "error:|Build completed" "$logfile" | head || true

echo "--- lake build exit code: $build_status (restoring $file now) ---"
exit "$build_status"
