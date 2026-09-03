#!/usr/bin/env bash
# Run one full mutation-cycle record on top of mutate-and-build.sh: a labeled
# mutate+build, an optional restore-hash verification, and a rebuild of the
# same targets to confirm the restored pass. This is the evidentiary record
# this repo's slice plans require per fixture (baseline pass / exact mutation
# / intended failure / restored pass) as one auditable command instead of an
# ad hoc chain that no permission rule can safely allow-list.
#
# Usage:
#   mutation-cycle.sh [--hashes <manifest>] <label> <leanncd-dir> <file> \
#     <old-string> <new-string> <lake-target>...
#
# <label>          short name printed in the banner lines, e.g. 'M6b (source f32 guard)'
# --hashes <path>  optional `shasum -c` manifest, resolved relative to <leanncd-dir>
#                  (matching `file`'s own resolution) and checked after the mutation
#                  is restored; the step is skipped if this flag is omitted
# <file> <old-string> <new-string> <lake-target>...  passed straight through to
#   mutate-and-build.sh, then <lake-target>... is reused for the restored rebuild
#
# Exits 0 only if ALL of: the mutation broke the build (mutate-and-build.sh exits
# nonzero), the restore-hash check (if given) passed, and the restored rebuild of
# the same targets passed. A mutation that did NOT break the build is reported as
# a real finding (the fixture may not cover it), not silently treated as fine.

set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)

hashes=""
if [[ "${1:-}" == "--hashes" ]]; then
  hashes=$2
  shift 2
fi

if [[ $# -lt 6 ]]; then
  sed -n '2,20p' "$0"
  exit 2
fi

label=$1 leanncd_dir=$2 file=$3 old=$4 new=$5
shift 5
targets=("$@")

echo "=== $label MUTATE ==="
set +e
bash "$script_dir/mutate-and-build.sh" "$leanncd_dir" "$file" "$old" "$new" "${targets[@]}"
mutation_status=$?
set -e
echo "=== $label MUTATE exit=$mutation_status ==="

hash_status=0
if [[ -n "$hashes" ]]; then
  echo "=== $label RESTORE CHECK ==="
  set +e
  (cd -- "$leanncd_dir" && shasum -c "$hashes")
  hash_status=$?
  set -e
fi

echo "=== $label RESTORED BUILD ==="
restored_log=$(mktemp)
set +e
(cd -- "$leanncd_dir" && "$HOME/.elan/bin/lake" build "${targets[@]}") > "$restored_log" 2>&1
restored_build_status=$?
set -e
tail -5 "$restored_log"
rm -f "$restored_log"

echo "=== $label SUMMARY: mutation_exit=$mutation_status restore_hash_exit=$hash_status restored_build_exit=$restored_build_status ==="

if [[ "$mutation_status" -eq 0 ]]; then
  echo "$label: WARNING - mutation did not break the build; fixture may not cover it" >&2
fi

if [[ "$mutation_status" -ne 0 && "$hash_status" -eq 0 && "$restored_build_status" -eq 0 ]]; then
  echo "$label: PASS"
  exit 0
fi
echo "$label: FAIL"
exit 1
