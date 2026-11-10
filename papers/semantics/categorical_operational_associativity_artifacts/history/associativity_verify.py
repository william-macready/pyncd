#!/usr/bin/env python3
"""Package the verified structural law and check owned-copy destructive controls."""
import difflib
import hashlib
import json
from pathlib import Path
import subprocess

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
LEAN = ROOT / "leanncd"
REL = "experiments/indexed_execution/IndexedOperationalHistoryAssociativity.lean"
SOURCE = LEAN / REL
GENERATED = SOURCE.with_name("IndexedOperationalHistoryAssociativityMutation.lean")
source = SOURCE.read_text()
controls = [
    ("wrong-B-identity", "  · exact identity_B", "  · exact identity_A"),
    ("wrong-C-identity", "  · exact identity_C", "  · exact identity_B"),
    ("forget-completed-private-state",
     "downstreamState A (compose B C bc) a (downstreamState B C b c) := by",
     "downstreamState A (compose B C bc) a (upstreamState B C b) := by"),
]
manifest = []
try:
    for label, old, new in controls:
        assert source.count(old) == 1, (label, source.count(old))
        GENERATED.write_text(source.replace(old, new))
        run = subprocess.run(
            ["bash", str(LEAN / "scripts/lean-file.sh"), str(LEAN),
             str(GENERATED.relative_to(LEAN))],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (OUT / f"associativity-{label}.log").write_text(run.stdout)
        errors = [line.split("error:", 1)[1].strip()
                  for line in run.stdout.splitlines() if "error:" in line]
        assert run.returncode != 0 and errors, (label, run.returncode)
        manifest.append({"label": f"history-associativity/{label}", "file": REL,
                         "old": old, "new": new,
                         "targets": ["IndexedOperationalHistoryAssociativity"],
                         "expect": [errors[0]]})
        print(f"{label}: rejected ({errors[0]})")
finally:
    GENERATED.unlink(missing_ok=True)
(OUT / "associativity_mutations.json").write_text(json.dumps(manifest, indent=2) + "\n")
rel = f"leanncd/{REL}"
patch = f"diff --git a/{rel} b/{rel}\nnew file mode 100644\n"
patch += "".join(difflib.unified_diff(
    [], source.splitlines(keepends=True), fromfile="/dev/null", tofile=f"b/{rel}"))
(OUT / "associativity.patch").write_text(patch)
(OUT / "associativity_source.json").write_text(json.dumps(
    {"path": rel, "sha256": hashlib.sha256(source.encode()).hexdigest(),
     "lines": len(source.splitlines())}, indent=2) + "\n")
