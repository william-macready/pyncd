#!/usr/bin/env python3
"""Freeze affine-scan sources with the existing ordered replay verifier."""

import importlib.util
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
HELPER = OUT.parent / "categorical_operational_associativity_artifacts/package.py"
spec = importlib.util.spec_from_file_location("affine_scan_package", HELPER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"Cannot load package verifier: {HELPER}")
package = importlib.util.module_from_spec(spec)
spec.loader.exec_module(package)
package.ROOT = ROOT
package.OUT = OUT
package.BASE = "13ee25a38366b2069c970754fa371f06d3f15ff9"
package.TASKS = [
    ("admission", [
        "IndexedAffineScanRead", "IndexedAffineScanProfile",
        "IndexedAffineScanPrototypeTest",
    ]),
    ("component", [
        "IndexedAffineScanConstruction", "IndexedAffineScanMatch",
        "IndexedAffineScanRank",
    ]),
    ("access", ["IndexedAffineScanAccessAgreement"]),
    ("history", ["IndexedAffineScanHistory"]),
    ("interpretation", [
        "IndexedAffineScanInterpretation", "IndexedAffineScanHistoryTest",
        "IndexedAffineScanSemantics",
    ]),
    ("compiler", [
        "IndexedAffineScanCompilerExamples", "IndexedAffineScanCompilerCertificates",
    ]),
    ("mixed", ["IndexedAffineScanMixedCompilerCertificate"]),
    ("acceptance", [
        "IndexedAffineScanHistoryCompilerTest", "IndexedAffineScanNamespaceAudit",
    ]),
]
package.DOCS = [
    "leanncd/AGENTS.md",
    "papers/semantics/categorical_tensor_logic_semantics.md",
]

if not sys.argv[1:]:
    package.main()
else:
    raise SystemExit("usage: package.py")
