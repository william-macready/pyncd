#!/usr/bin/env python3
"""Generate the additive patch directly from the kernel-checked source."""
import difflib
import hashlib
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
REL = "leanncd/experiments/indexed_execution/IndexedOperationalHistory.lean"
data = (ROOT / REL).read_bytes()
patch = f"diff --git a/{REL} b/{REL}\nnew file mode 100644\n"
patch += "".join(difflib.unified_diff(
    [], data.decode().splitlines(keepends=True),
    fromfile="/dev/null", tofile=f"b/{REL}",
))
(OUT / "prototype.patch").write_text(patch)
(OUT / "source.json").write_text(json.dumps(
    {"base": "8268da1f", "path": REL, "sha256": hashlib.sha256(data).hexdigest(),
     "lines": len(data.splitlines())}, indent=2) + "\n")
