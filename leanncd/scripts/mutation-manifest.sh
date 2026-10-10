#!/usr/bin/env bash
# Run a slice plan's mutation cycles from one JSON manifest, so an implementer runs the cycles the
# plan author already designed (and usually already observed) instead of re-deriving each
# `mutation-cycle.sh` invocation and its multi-line quoting by hand.
#
# Usage:
#   mutation-manifest.sh [--cd <dir>] [--check] [--task <id>] [--out <file.md>] \
#     <leanncd-dir> <manifest.json> [label-prefix...]
#   Filters select entries for both --check and runs; task and prefix filters intersect.
#
# --cd <dir>     change directory first (as in mutation-cycle.sh); must come first if given
# --check        validate global schema plus selected files and old-strings (EXACTLY ONCE).
#                No build runs. Use it at plan-authoring time, WITHOUT filters: a filtered check
#                leaves every entry outside the selection unvalidated (a successful filtered
#                check reports how many).
# --task <id>    select only entries whose "task" field equals <id>, for checking or running
#                IDs are exact strings; unknown IDs report available tasks
# --out <file>   also write the summary table to <file> (markdown)
# label-prefix   select only entries whose label starts with one of these
#
# Validation scope: schema and duplicate labels are checked across ALL entries. File existence
# and old-string uniqueness are checked only for selected entries; no filters means all entries.
# An empty selection is an error. Filtered --check output names entries outside validation.
# Schema, duplicate-label and selected-file problems are reported in one pass, in entry order;
# an unknown task or an empty selection is reported once those are fixed.
#
# Manifest: a JSON array of objects —
#   { "label":   "M1 (payload bits constant 0)",          required, unique
#     "task":    "2",                                      optional; a string not starting with "--"
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
# pass; 125 on a malformed manifest or a --check failure, which includes a selected file that cannot
# be read (not valid UTF-8, or no permission), and when --out cannot be written. An obviously
# unwritable --out (a directory, a missing or non-directory parent, a read-only directory or file)
# is refused just before the first cycle runs, after every manifest and selection diagnostic and
# never under --check; any other write failure is reported at the end, after the table is shown.
# A usage error (unknown flag, a flag without its value or followed by another flag, an empty --out,
# --cd without a value) exits 1. Task ids may not start with "--", which --task could not select.
# Each cycle's stdout/stderr and the mutated build log are decoded as UTF-8 with replacement, so a
# stray byte in build output never aborts a run.

set -euo pipefail
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)

if [[ "${1:-}" == "--cd" ]]; then
  if [[ $# -lt 2 ]]; then echo "error: --cd requires a value" >&2; exit 1; fi
  cd -- "$2"
  shift 2
fi

exec python3 - "$script_dir" "$@" <<'PY'
import hashlib, json, os, subprocess, sys, tempfile

script_dir, *argv = sys.argv[1:]
check_only = False; task = None; out = None
def flag_value(flag):
    if not argv: sys.exit(f"error: {flag} requires a value")
    if argv[0].startswith("--"): sys.exit(f"error: {flag} requires a value, not the flag {argv[0]}")
    return argv.pop(0)
while argv and argv[0].startswith("--"):
    flag = argv.pop(0)
    if flag == "--check": check_only = True
    elif flag == "--task": task = flag_value(flag)
    elif flag == "--out":
        out = flag_value(flag)
        if out == "": sys.exit("error: --out requires a non-empty path")
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

problems, labels = [], set()   # problems: (entry index, message)
def problem(i, msg): problems.append((i, msg))
def fail_if_problems():
    # One report, in entry order (stable within an entry: schema, then duplicate label, then disk).
    if problems:
        print("\n".join(m for _, m in sorted(problems, key=lambda p: p[0])), file=sys.stderr)
        sys.exit(125)

for i, e in enumerate(entries):
    where = f"entry {i} ({e.get('label', '?')})" if isinstance(e, dict) else f"entry {i}"
    if not isinstance(e, dict): problem(i, f"{where}: not an object"); continue
    for k in ("label", "file", "old", "new"):
        if not isinstance(e.get(k), str): problem(i, f"{where}: '{k}' must be a string")
    if "task" in e and not isinstance(e["task"], str):
        problem(i, f"{where}: 'task' must be a string (got {json.dumps(e['task'])}); "
                   "quote task ids, e.g. \"task\": \"2\"")
    elif isinstance(e.get("task"), str) and e["task"].startswith("--"):
        problem(i, f"{where}: 'task' must not start with '--' (--task could not select it)")
    if not (isinstance(e.get("targets"), list) and e["targets"] and all(isinstance(t, str) for t in e["targets"])):
        problem(i, f"{where}: 'targets' must be a non-empty list of strings")
    if "expect" in e and not (isinstance(e["expect"], list) and all(isinstance(s, str) for s in e["expect"])):
        problem(i, f"{where}: 'expect' must be a list of strings")
    if isinstance(e.get("label"), str):
        if e["label"] in labels: problem(i, f"{where}: duplicate label")
        labels.add(e["label"])

# Selection tolerates entries that already have schema problems, so their problems are reported
# together with the filesystem problems of the selected entries instead of one class per run.
def selectable(e):
    if not isinstance(e, dict): return False
    if task is not None and e.get("task") != task: return False
    return not prefixes or (isinstance(e.get("label"), str) and any(e["label"].startswith(p) for p in prefixes))

selected = [(i, e) for i, e in enumerate(entries) if selectable(e)]

for i, e in selected:
    if isinstance(e.get("file"), str) and isinstance(e.get("old"), str):
        where = f"entry {i} ({e.get('label', '?')})"
        path = os.path.join(leanncd_dir, e["file"])
        if not os.path.isfile(path): problem(i, f"{where}: no such file {e['file']}")
        else:
            try:
                n = open(path, encoding="utf-8").read().count(e["old"])
            except UnicodeDecodeError:
                problem(i, f"{where}: cannot read {e['file']}: not valid UTF-8")
            except OSError as exc:
                problem(i, f"{where}: cannot read {e['file']}: {exc.strerror or exc}")
            else:
                if n != 1: problem(i, f"{where}: old-string occurs {n} times in {e['file']} (expected 1)")
fail_if_problems()

if not selected:
    if task is not None:
        available = sorted({e["task"] for e in entries if "task" in e})
        if task not in available:
            hint = ", ".join(repr(t) for t in available) or "(none)"
            die(f"no manifest entries selected: unknown task {task!r}; available tasks: {hint}")
    die("no manifest entries selected")

if check_only:
    if len(selected) == len(entries):
        print(f"manifest OK: {len(entries)} entries, {len(selected)} selected, every old-string unique")
    else:
        print(f"manifest OK: {len(entries)} entries, {len(selected)} selected; "
              f"{len(entries) - len(selected)} outside the selection not validated; "
              "every selected old-string unique")
    sys.exit(0)

# Judge --out only now: every manifest, selection and --check diagnostic has priority, and it must
# still happen before any cycle runs, not after a long run when the table cannot be written.
if out is not None:
    out_dir = os.path.dirname(os.path.abspath(out))
    if os.path.isdir(out): die(f"cannot write --out {out}: it is a directory")
    if os.path.exists(out_dir) and not os.path.isdir(out_dir):
        die(f"cannot write --out {out}: {out_dir} is not a directory")
    if not os.path.isdir(out_dir): die(f"cannot write --out {out}: directory {out_dir} does not exist")
    if not os.access(out_dir, os.W_OK): die(f"cannot write --out {out}: directory {out_dir} is not writable")
    if os.path.exists(out) and not os.access(out, os.W_OK): die(f"cannot write --out {out}: file is not writable")

def sha(path): return hashlib.sha256(open(path, "rb").read()).hexdigest()

rows = []
for _, e in selected:
    path = os.path.join(leanncd_dir, e["file"])
    before = sha(path)
    fd, log = tempfile.mkstemp(suffix=".log"); os.close(fd)
    cycle = subprocess.run(
        ["bash", os.path.join(script_dir, "mutation-cycle.sh"), e["label"], leanncd_dir,
         e["file"], e["old"], e["new"], *e["targets"]],
        env={**os.environ, "MUTATION_LOG": log}, capture_output=True,
        text=True, encoding="utf-8", errors="replace")
    sys.stdout.write(cycle.stdout); sys.stdout.write(cycle.stderr)
    mutated_log = open(log, encoding="utf-8", errors="replace").read(); os.unlink(log)
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
    try:
        open(out, "w").write("\n".join(table) + "\n")
    except OSError as exc:
        # The table is already on stdout; do not let a late write failure look like a test result.
        print(f"error: cannot write --out {out}: {exc.strerror or exc}", file=sys.stderr)
        sys.exit(125)
sys.exit(0 if passed == len(rows) else 1)
PY
