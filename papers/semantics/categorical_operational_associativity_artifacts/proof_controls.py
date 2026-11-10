#!/usr/bin/env python3
"""Convert observed prototype proof controls to the repository mutation runner schema."""

import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEAN = "experiments/indexed_execution/"
entries = []


def add(label, module, old, new, diagnostic):
    entries.append({
        "label": label,
        "task": "live-proof",
        "file": f"{LEAN}{module}.lean",
        "old": old,
        "new": new,
        "targets": [module],
        "expect": [diagnostic],
    })


for item in json.loads((HERE / "history/mutations.json").read_text()):
    diagnostic = item["expect"].split(": error: ", 1)[1]
    add(f"P/history/{item['name']}", "IndexedOperationalHistory",
        item["old"], item["new"], diagnostic)

for item in json.loads((HERE / "history/composition_mutations.json").read_text()):
    entries.append({"task": "live-proof", **item})

add("P/runs/ordered-events", "IndexedOperationalRuns",
    "target.events = source.events.map (mapEvent f rename)",
    "target.events = (source.events.map (mapEvent f rename)).reverse", "Type mismatch")
add("P/runs/ordered-states", "IndexedOperationalRuns",
    "states : List.Forall₂ (StateRelated f rename) source.states target.states",
    "states : List.Forall₂ (StateRelated f rename) source.states target.states.reverse",
    "Type mismatch")
add("P/runs/leaf-B-identity", "IndexedOperationalRuns",
    "exact (identity_B n).symm", "exact (identity_A n).symm", "Type mismatch")

for item in json.loads((HERE / "runs/phases-controls.json").read_text()):
    add(f"P/phases/{item['name']}", "IndexedOperationalRunsPhases",
        item["old"], item["new"], "mismatch")

for item in json.loads((HERE / "history/associativity_mutations.json").read_text()):
    entries.append({"task": "live-proof", **item})

add("P/metadata/absent-versus-present-empty-neighbor", "IndexedOperationalObservationLaws",
    """def absentEmptyMetadata : GraphMetadata emptyProducerDeclarations Unit where
  inputs := []
  outputs := Fixtures.emptyMetadata.outputs
  inputRole := fun _ => false
  input := fun _ => none
  valid := fun _ => rfl
  adapters := ()
  inputs_nodup := by simp
  outputs_nodup := Fixtures.emptyMetadata.outputs_nodup
  inputs_exact := by intro a; simp""",
    """def absentEmptyMetadata : GraphMetadata emptyProducerDeclarations Unit :=
  Fixtures.emptyMetadata""", "Type mismatch")

destination = ROOT / "papers/semantics/categorical_operational_associativity_proof_mutations_post.json"
destination.write_text(json.dumps(entries, indent=2) + "\n")
print(f"Wrote {len(entries)} live-proof controls to {destination}")
