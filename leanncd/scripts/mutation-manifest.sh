#!/usr/bin/env bash
# Run a slice plan's mutation cycles from one JSON manifest, so an implementer runs the cycles the
# plan author already designed (and usually already observed) instead of re-deriving each
# `mutation-cycle.sh` invocation and its multi-line quoting by hand.
#
# Usage:
#   mutation-manifest.sh [--cd <dir>] [--check] [--task <id>] [--out <file.md>] \
#     <leanncd-dir> <manifest.json> [label-prefix...]
#
# --cd <dir>     change directory first (as in mutation-cycle.sh); must come first if given
# --check        validate the manifest only: schema, file existence, and that every old-string
#                occurs EXACTLY ONCE. No build runs. Use it at plan-authoring time.
# --task <id>    run only entries whose "task" field equals <id>
# --out <file>   also write the summary table to <file> (markdown)
# label-prefix   run only entries whose label starts with one of these
#
# Manifest: a JSON array of objects —
#   { "label":   "M1 (payload bits constant 0)",          required, unique
#     "task":    "2",                                      optional
#     "file":    "LeanNCD/Eval/Plan/Dense.lean",           required, relative to <leanncd-dir>
#     "old":     "exact text, may span lines",             required, must occur exactly once
#     "new":     "replacement text",                       required
#     "targets": ["Eval.Plan.KernelDense32Test"],          required, lake targets to build
#     "expect":  ["fixture 3.2", "0x3f800000"] }           optional; EVERY string must appear in the
#                                                          mutated build's log, proving the build broke
#                                                          for the intended reason
#
# Each entry is run through mutation-cycle.sh unchanged (mutate, build, restore, rebuild), with a
# sha256 check that the file is byte-identical afterwards. An entry PASSes only if mutation-cycle.sh
# passes, the file is restored, and every `expect` string was seen. Exits 0 iff all selected entries
# pass; 125 on a malformed manifest or a --check failure.

set -euo pipefail
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)

if [[ "${1:-}" == "--cd" ]]; then
  cd -- "$2"
  shift 2
fi

exec python3 - "$script_dir" "$@" <<'PY'
import hashlib, json, os, subprocess, sys, tempfile

script_dir, *argv = sys.argv[1:]
check_only = False; task = None; out = None
while argv and argv[0].startswith("--"):
    flag = argv.pop(0)
    if flag == "--check": check_only = True
    elif flag == "--task": task = argv.pop(0)
    elif flag == "--out": out = argv.pop(0)
    else: sys.exit(f"error: unknown flag {flag}")
if len(argv) < 2:
    sys.exit("usage: mutation-manifest.sh [--cd <dir>] [--check] [--task <id>] [--out <file.md>] "
             "<leanncd-dir> <manifest.json> [label-prefix...]")
leanncd_dir, manifest_path, *prefixes = argv
leanncd_dir = os.path.abspath(leanncd_dir)

def die(msg):
    print(f"error: {msg}", file=sys.stderr); sys.exit(125)

try:
    entries = json.load(open(manifest_path))
except Exception as e:
    die(f"cannot read manifest {manifest_path}: {e}")
if not isinstance(entries, list): die("manifest must be a JSON array")

problems, labels = [], set()
for i, e in enumerate(entries):
    where = f"entry {i} ({e.get('label', '?')})" if isinstance(e, dict) else f"entry {i}"
    if not isinstance(e, dict): problems.append(f"{where}: not an object"); continue
    for k in ("label", "file", "old", "new"):
        if not isinstance(e.get(k), str): problems.append(f"{where}: '{k}' must be a string")
    if not (isinstance(e.get("targets"), list) and e["targets"] and all(isinstance(t, str) for t in e["targets"])):
        problems.append(f"{where}: 'targets' must be a non-empty list of strings")
    if "expect" in e and not (isinstance(e["expect"], list) and all(isinstance(s, str) for s in e["expect"])):
        problems.append(f"{where}: 'expect' must be a list of strings")
    if e.get("label") in labels: problems.append(f"{where}: duplicate label")
    labels.add(e.get("label"))
    if isinstance(e.get("file"), str) and isinstance(e.get("old"), str):
        path = os.path.join(leanncd_dir, e["file"])
        if not os.path.isfile(path): problems.append(f"{where}: no such file {e['file']}")
        else:
            n = open(path).read().count(e["old"])
            if n != 1: problems.append(f"{where}: old-string occurs {n} times in {e['file']} (expected 1)")
if problems:
    print("\n".join(problems), file=sys.stderr); sys.exit(125)

selected = [e for e in entries
            if (task is None or str(e.get("task")) == task)
            and (not prefixes or any(e["label"].startswith(p) for p in prefixes))]
if not selected: die("no manifest entries selected")
if check_only:
    print(f"manifest OK: {len(entries)} entries, {len(selected)} selected, every old-string unique")
    sys.exit(0)

def sha(path): return hashlib.sha256(open(path, "rb").read()).hexdigest()

rows = []
for e in selected:
    path = os.path.join(leanncd_dir, e["file"])
    before = sha(path)
    fd, log = tempfile.mkstemp(suffix=".log"); os.close(fd)
    cycle = subprocess.run(
        ["bash", os.path.join(script_dir, "mutation-cycle.sh"), e["label"], leanncd_dir,
         e["file"], e["old"], e["new"], *e["targets"]],
        env={**os.environ, "MUTATION_LOG": log}, capture_output=True, text=True)
    sys.stdout.write(cycle.stdout); sys.stdout.write(cycle.stderr)
    mutated_log = open(log).read(); os.unlink(log)
    missing = [s for s in e.get("expect", []) if s not in mutated_log]
    restored = sha(path) == before
    ok = cycle.returncode == 0 and restored and not missing
    why = ([] if cycle.returncode == 0 else ["cycle failed"]) + ([] if restored else ["file NOT restored"]) \
        + ([f"expected text not in mutated build log: {missing}"] if missing else [])
    print(f"=== {e['label']} MANIFEST VERDICT: {'PASS' if ok else 'FAIL (' + '; '.join(why) + ')'} ===",
          flush=True)
    rows.append((e["label"], cycle.returncode == 0, restored,
                 "n/a" if "expect" not in e else ("yes" if not missing else "NO"), ok))

table = ["| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |",
         "|---|---|---|---|---|"]
table += [f"| {l} | {'yes' if c else 'NO'} | {'yes' if r else 'NO'} | {x} | {'PASS' if ok else 'FAIL'} |"
          for l, c, r, x, ok in rows]
passed = sum(ok for *_, ok in rows)
table.append(f"\n{passed}/{len(rows)} cycles passed.")
print("\n" + "\n".join(table))
if out:
    open(out, "w").write("\n".join(table) + "\n")
sys.exit(0 if passed == len(rows) else 1)
PY
