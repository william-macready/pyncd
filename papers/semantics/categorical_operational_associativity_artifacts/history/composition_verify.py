#!/usr/bin/env python3
"""Verify owned-copy controls and package the separate binary integration patch."""
import difflib
import hashlib
import json
from pathlib import Path
import subprocess

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
LEAN = ROOT / "leanncd"
REL = "experiments/indexed_execution/IndexedOperationalHistoryComposition.lean"
SOURCE = LEAN / REL
GENERATED = SOURCE.with_name("IndexedOperationalHistoryCompositionMutation.lean")
CONTROLS = [
    ("drop-prefix", "h.bind (fun _ _ => k)", "k"),
    ("forget-private-ledger",
     "mapLedger upstreamId completed.produced ++ mapLedger downstreamId s.produced",
     "mapLedger downstreamId s.produced"),
    ("forget-private-store",
     "| ⟨.inl t, p⟩ => completed.available ⟨t, p⟩",
     "| ⟨.inl _, _⟩ => none"),
    ("accept-incompatible-cut", "(shared : suffix.start = s)",
     "(shared : True)"),
]
source = SOURCE.read_text()
manifest = []
try:
    for label, old, new in CONTROLS:
        assert source.count(old) == 1, (label, source.count(old))
        GENERATED.write_text(source.replace(old, new))
        run = subprocess.run(
            ["bash", str(LEAN / "scripts/lean-file.sh"), str(LEAN),
             str(GENERATED.relative_to(LEAN))],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        (OUT / f"composition-{label}.log").write_text(run.stdout)
        errors = [line.split("error:", 1)[1].strip()
                  for line in run.stdout.splitlines() if "error:" in line]
        assert run.returncode != 0 and errors, (label, run.returncode, run.stdout)
        manifest.append({"label": f"history-composition/{label}",
                         "file": REL, "old": old, "new": new,
                         "targets": ["IndexedOperationalHistoryComposition"],
                         "expect": [errors[0]]})
        print(f"{label}: rejected ({errors[0]})")
finally:
    GENERATED.unlink(missing_ok=True)
(OUT / "composition_mutations.json").write_text(json.dumps(manifest, indent=2) + "\n")
patchrel = f"leanncd/{REL}"
patch = f"diff --git a/{patchrel} b/{patchrel}\nnew file mode 100644\n"
patch += "".join(difflib.unified_diff(
    [], source.splitlines(keepends=True), fromfile="/dev/null", tofile=f"b/{patchrel}"))
(OUT / "composition.patch").write_text(patch)
original = json.loads((OUT / "source.json").read_text())
unchanged = hashlib.sha256((ROOT / original["path"]).read_bytes()).hexdigest() == original["sha256"]
assert unchanged, "Original finalized history source changed"
(OUT / "composition_source.json").write_text(json.dumps(
    {"base": "8268da1f", "path": patchrel,
     "sha256": hashlib.sha256(source.encode()).hexdigest(),
     "lines": len(source.splitlines()), "original_history_unchanged": unchanged},
    indent=2) + "\n")
