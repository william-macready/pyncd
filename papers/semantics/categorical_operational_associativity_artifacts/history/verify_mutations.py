#!/usr/bin/env python3
"""Compile destructive controls in an owned generated module, restoring no source."""
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "leanncd"
SOURCE = LEAN / "experiments/indexed_execution/IndexedOperationalHistory.lean"
GENERATED = SOURCE.with_name("IndexedOperationalHistoryMutation.lean")
OUT = Path(__file__).resolve().parent
CONTROLS = [
    ("drop-failure-event", "| .failed _ e _ => [e]", "| .failed _ e _ => []"),
    ("duplicate-snapshot", "| .step s _ h => s :: h.states",
     "| .step s _ h => s :: s :: h.states"),
    ("drop-private-prefix", "| .step s e tail => .step s e (tail.bind k)",
     "| .step _ _ tail => tail.bind k"),
    ("reverse-ledger", "mapLedger t.identity s.produced",
     "mapLedger t.identity s.produced.reverse"),
    ("erase-private-availability", "fun a => s.available (t.address.symm a)",
     "fun _ => none"),
    ("erase-empty-input-port", "⟨A.inputs, A.outputs, A.program.input",
     "⟨[], A.outputs, A.program.input"),
]

source = SOURCE.read_text()
results = []
try:
    for name, old, new in CONTROLS:
        assert source.count(old) == 1, (name, source.count(old))
        GENERATED.write_text(source.replace(old, new))
        run = subprocess.run(
            ["bash", str(LEAN / "scripts/lean-file.sh"), str(LEAN),
             str(GENERATED.relative_to(LEAN))],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        (OUT / f"{name}.log").write_text(run.stdout)
        errors = [line for line in run.stdout.splitlines() if "error:" in line]
        assert run.returncode != 0 and errors, (name, run.returncode, run.stdout)
        results.append({"name": name, "old": old, "new": new,
                        "exit": run.returncode, "expect": errors[0]})
        print(f"{name}: rejected ({errors[0]})")
finally:
    GENERATED.unlink(missing_ok=True)
(OUT / "mutations.json").write_text(json.dumps(results, indent=2) + "\n")
