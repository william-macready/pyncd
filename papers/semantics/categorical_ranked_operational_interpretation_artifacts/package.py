#!/usr/bin/env python3
"""Freeze this slice with the established private-index replay/snippet verifier."""

import importlib.util
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
HELPER = OUT.parent / "categorical_operational_associativity_artifacts/package.py"
spec = importlib.util.spec_from_file_location("operational_package", HELPER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"Cannot load package verifier: {HELPER}")
package = importlib.util.module_from_spec(spec)
spec.loader.exec_module(package)
package.ROOT = ROOT
package.OUT = OUT
package.BASE = "921cca7e"
package.TASKS = [
    ("units", ["IndexedOperationalUnits", "IndexedOperationalWireFrame"]),
    ("core", ["IndexedRankedOperationalCore"]),
    ("scope", ["IndexedOperationalScopeNaturality"]),
    ("category", ["IndexedRankedOperationalCategory"]),
    ("source", [
        "IndexedRankedOperationalSource", "IndexedRankedOperationalReference",
    ]),
    ("interpretation", [
        "IndexedRankedOperationalInterpretation", "IndexedRankedOperationalSemantics",
    ]),
    ("acceptance", ["IndexedRankedOperationalTest", "IndexedRankedOperationalAudit"]),
]
package.DOCS = [
    "leanncd/AGENTS.md",
    "papers/semantics/categorical_tensor_logic_semantics.md",
]

if sys.argv[1:] == ["--snippets"]:
    package.snippets()
elif not sys.argv[1:]:
    package.main()
else:
    raise SystemExit("usage: package.py [--snippets]")
