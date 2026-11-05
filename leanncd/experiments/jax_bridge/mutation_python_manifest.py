"""Mutation runner for the PYTHON half of a JAX-bridge mutation record (stdlib only).

`leanncd/scripts/mutation-manifest.sh` only builds Lake targets, so it cannot kill a mutation of
`evalplan_affine_runtime.py`. This is its Python counterpart, over the SAME entry fields
(`label`, `task`, `file`, `old`, `new`, `expect`), except that `targets` is replaced by `runs`: the
verifier invocations (`float64` / `float32`) executed against the pre-generated Lean modules in
`.cache` (produced by `run-evalplan-scatter.sh`). An entry may carry `"verifier": "<stem>"` (default
`evalplan_scatter_smoke`) to run `<stem>.py` against `.cache/generated_<stem>{64,32}.py` instead, e.g.
`evalplan_nonlin_smoke` (produced by `run-evalplan-nonlin.sh`).

Usage: mutation_python_manifest.py [--observe] <manifest.json>   (run from anywhere)
Per entry: sha256 the file, require `old` to occur exactly once, mutate, run every verifier, require
a non-zero exit and every `expect` string in the combined output (a mutation that survives is a
FINDING and fails the run), restore, require the sha256 is unchanged, rerun and require a clean
pass. `--observe` instead RECORDS, as the `expect` of each killed mutation, the first failure line
(the assertion KIND) plus each failing run's `AssertionError: <fixture> <mode> <output>` prefix (WHICH
fixture killed it), so a mutant killed by an unrelated earlier assertion no longer passes.
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PY = HERE / ".cache" / "python" / "bin" / "python"
DEFAULT_VERIFIER = "evalplan_scatter_smoke"  # an entry may name another with a `verifier` field
SUFFIX = {"float64": "64", "float32": "32"}
# A mutation that keeps the file size, restored within the same second, would leave a stale `.pyc`
# (validated by whole-second mtime and size) and make the post-restore baseline run the mutant.
ENV = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}


def verify(runs: list[str], verifier: str = DEFAULT_VERIFIER) -> tuple[int, str]:
    out, code = "", 0
    for r in runs:
        module = HERE / ".cache" / f"generated_{verifier}{SUFFIX[r]}.py"
        p = subprocess.run([str(PY), str(HERE / f"{verifier}.py"), r, str(module)],
                           capture_output=True, text=True, env=ENV)
        out += p.stdout + p.stderr
        code = code or p.returncode
    return code, out


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> int:
    args = sys.argv[1:]
    observe = "--observe" in args
    manifest = Path([a for a in args if not a.startswith("--")][0]).resolve()
    entries = json.loads(manifest.read_text())
    for v in sorted({e.get("verifier", DEFAULT_VERIFIER) for e in entries}):
        code0, out0 = verify(["float64", "float32"], v)
        if code0:
            print(f"baseline FAILS ({v}):\n" + out0)
            return 1
    failed = 0
    for e in entries:
        v = e.get("verifier", DEFAULT_VERIFIER)
        path = HERE / e["file"]
        before, text = sha(path), path.read_text()
        if text.count(e["old"]) != 1:
            print(f"FAIL {e['label']}: old-string occurs {text.count(e['old'])} times")
            failed += 1
            continue
        try:
            path.write_text(text.replace(e["old"], e["new"]))
            code, out = verify(e["runs"], v)
        finally:
            path.write_text(text)
        restored = sha(path) == before
        rcode, _ = verify(["float64", "float32"], v)
        killed = code != 0
        if observe and killed:
            lines = [l for l in out.splitlines() if "Error" in l]
            # The traceback's `raise` line only names the assertion KIND; also pin WHICH fixture failed
            # (the `AssertionError: <fixture> <mode> <output>` prefix of each failing run's last line),
            # so a mutant killed by an unrelated earlier assertion no longer passes.
            who = []
            for l in out.splitlines():
                if l.startswith("AssertionError: "):
                    w = "AssertionError: " + l[len("AssertionError: "):].split(": ")[0]
                    if w not in who:
                        who.append(w)
            e["expect"] = ([lines[0][:90]] if lines else []) + who
        ok = killed and restored and rcode == 0 and all(x in out for x in e.get("expect", []))
        print(("PASS" if ok else "FAIL"), e["label"], "| killed" if killed else "| SURVIVED",
              "| restored" if restored and rcode == 0 else "| NOT RESTORED/GREEN")
        failed += not ok
    if observe:
        manifest.write_text(json.dumps(entries, indent=1, ensure_ascii=False) + "\n")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
