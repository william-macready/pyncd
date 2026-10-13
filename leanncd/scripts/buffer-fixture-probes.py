#!/usr/bin/env python3
"""Probe buffer fixtures without changing production definitions or admitting proofs.

Usage: python3 buffer-fixture-probes.py <leanncd-dir> <evidence-dir>

Extract current definitions and fixture expressions into a fresh namespace. Each
control proves its copy agrees with production; mutants apply the exact existing
manifest substitution only to that copy. This measures component observations,
not complete mutated runPlan executions. R.dead is a separate consumer-contract
probe, not a computed executor row.
"""

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path


CASES = {
    "S3-M1": ("execRet", "retire-kernel-members-and-neighbour"),
    "S3-M2": ("execRet", "retire-kernel-members-and-neighbour"),
    "S3-M3": ("checkRet", "retire-check-live-and-output-conditions"),
    "S3-M4": ("checkRet", "retire-check-live-and-output-conditions"),
    "S3-M5": ("checkRet", "retire-check-live-and-output-conditions"),
    "S3-M6": ("checkReady", "retire-ready-condition-and-neighbour"),
    "S3-M7": ("SlotView", "reuse-retired-slot-view-and-live-neighbour"),
    "S3-M8": ("ReadyOK", "retire-ready-condition-and-neighbour"),
    "S3-M9": ("readPub", "reuse-retired-ghost-vs-live"),
    "S3-M10": ("RetOK", "retire-prop-output-condition-and-neighbour"),
    "S4-M1": ("checkPlan", "reuse-bad-live-alias-run"),
    "S4-M2": ("checkLayouts", "reuse-final-boundary-coverage"),
    "S4-M3": ("resourceList", "reuse-resource-kind-enumeration"),
    "S4-M4": ("resourceList", "reuse-resource-kind-enumeration"),
    "S4-M5": ("SlotView", "reuse-acc-role-before-and-after-publish"),
    "S4-M6": ("dead", None),
    "S4-M7": ("execRet", "retire-kernel-members-and-neighbour"),
}

PARAMETERS = {
    "execRet": "(B : List (DefAddr P)) (M : Memory K π.allocation)",
    "checkRet": "(pc : Nat) (B : List (DefAddr P))",
    "checkReady": "(pc : Nat) (G : List (OccRef P))",
    "SlotView": "(pc : Nat) (res : Resource P)",
    "ReadyOK": "(pc : Nat) (G : List (OccRef P))",
    "readPub": "(pc : Nat) (M : Memory K π.allocation) (a : Address σ)",
    "RetOK": "(pc : Nat) (B : List (DefAddr P))",
    "checkPlan": "", "checkLayouts": "", "resourceList": "",
}
ARGUMENTS = {
    "execRet": "B M", "checkRet": "pc B", "checkReady": "pc G",
    "SlotView": "pc res", "ReadyOK": "pc G", "readPub": "pc M a", "RetOK": "pc B",
    "checkPlan": "", "checkLayouts": "", "resourceList": "",
}

HEADER = """import Semantics.PlanReuseTest

namespace LeanNCD.Semantics.Program.Plan.BufferFixtureProbe
open Executor
variable {K : S → Type} {σ : Declarations S} {r : Registry K} {P : Program K σ r}
variable [DecidableEq σ.Tensor]
variable [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (π : P.Plan)

"""
OBSERVATIONS = """
end LeanNCD.Semantics.Program.Plan.BufferFixtureProbe

namespace LeanNCD.Semantics.PlanFixtures.BufferFixtureObservations
open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

"""
END = "\nend LeanNCD.Semantics.PlanFixtures.BufferFixtureObservations\n"


def definition(text, name):
    start = re.search(rf"(?m)^def {re.escape(name)}\b", text)
    if start is None:
        raise ValueError(f"Definition not found: {name}")
    return text[start.start():text.index("\n\n", start.start())]


def row(text, name):
    marker = f'#eval check "{name}"'
    if text.count(marker) != 1:
        raise ValueError(f"Expected one fixture named {name}")
    start = text.index(marker)
    end = text.index("\n\n", start)
    next_row = text.find("\n#eval ", start + len(marker))
    if next_row != -1:
        end = min(end, next_row)
    return text[start:end]


def redirect(text, name):
    text = re.sub(rf"\b(\w+)\.{re.escape(name)}\b",
                  rf"(BufferFixtureProbe.{name} \1)", text)
    text = re.sub(rf"\((reuseAccPair \w+)\)\.{re.escape(name)}\b",
                  rf"(BufferFixtureProbe.{name} (\1))", text)
    return text.replace(f"unfold {name}\n", f"unfold BufferFixtureProbe.{name}\n")


def component_source(source, name, expression, instances, control):
    parity = ""
    if control:
        args = ARGUMENTS[name]
        parity = (f"\nexample {PARAMETERS[name]} : {name} π {args} = "
                  f"LeanNCD.Semantics.Program.Plan.{name} π {args} := rfl\n")
    return (HEADER + definition(source, name) + "\n" + parity + OBSERVATIONS +
            redirect(instances + expression, name) + "\nend\n" + END)


def dead_source(source, reuse, control):
    field = re.search(r"(?m)^  dead : (.+)$", source)
    if field is None:
        raise ValueError("R.dead field not found")
    copy = "def dead (pc : Nat) (M : Memory K π.allocation) : Prop :=\n  " + field[1]
    parity = """
example (ops : (s : S) → ScalarOps (K s)) {η : P.Input} {pc : Nat}
    {M : Memory K π.allocation} {c : P.Running} (hR : π.R ops η pc M c) :
    dead π pc M := hR.dead
""" if control else ""
    start = reuse.index("  have hCapacity :", reuse.index("theorem reuseGood_unused_dead_every_pc"))
    end = reuse.index("\n\n", start)
    consumer = reuse[start:end].replace("hR.dead", "hdead")
    return HEADER + copy + "\n" + parity + OBSERVATIONS + """
example {pc : Nat} {M : Memory Carrier reuseGood.allocation}
    (hdead : BufferFixtureProbe.dead reuseGood pc M) :
    M reuseSpareCapacity = none ∧ M reuseSpareBuffer = none := by
""" + consumer + "\n" + END


def typecheck(root, text):
    with tempfile.NamedTemporaryFile(
        prefix="BufferFixtureProbe_", suffix=".lean",
        dir=root / "test/Semantics", mode="w", delete=False
    ) as handle:
        handle.write(text)
        path = Path(handle.name)
    try:
        result = subprocess.run(
            ["bash", str(root / "scripts/lean-file.sh"), str(root), str(path)],
            capture_output=True, text=True, check=False
        )
        return result.returncode, result.stdout + result.stderr
    finally:
        path.unlink()


def hashes(paths):
    return {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("leanncd_dir", type=Path)
    parser.add_argument("evidence_dir", type=Path)
    args = parser.parse_args()
    root = args.leanncd_dir.resolve()
    evidence = args.evidence_dir.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    build = subprocess.run(
        ["bash", str(root / "scripts/lake-build.sh"), str(root), "Semantics.PlanReuseTest"],
        capture_output=True, text=True, check=False
    )
    build_log = build.stdout + build.stderr
    (evidence / "build.log").write_text(build_log)
    if build.returncode != 0:
        raise RuntimeError(f"Fixture dependency refresh failed\n{build_log}")
    retirement = (root / "test/Semantics/PlanRetireTest.lean").read_text()
    reuse = (root / "test/Semantics/PlanReuseTest.lean").read_text()
    start = retirement.index("section\nattribute [local instance 2000]")
    end = retirement.index('#eval check "retire-ready-condition-and-neighbour"', start)
    instances = retirement[start:end]
    manifests = [root.parent / "papers/semantics" / f"plan_layer_slice{s}_mutations_post.json"
                 for s in (3, 4)]
    entries = {entry["label"].split()[0]: entry for path in manifests
               for entry in json.loads(path.read_text())}
    paths = [*sorted((root / "LeanNCD/Semantics/Plan").glob("*.lean")),
             *sorted((root / "test/Semantics").glob("Plan*.lean")), *manifests]
    before = hashes(paths)
    results = []
    try:
        for label, (name, observation) in CASES.items():
            entry = entries[label]
            path = (root / entry["file"]).resolve()
            if not path.is_relative_to(root):
                raise ValueError(f"Mutation source outside checkout: {path}")
            source = path.read_text()
            if source.count(entry["old"]) != 1:
                raise ValueError(f"{label}: expected one old string")
            if name != "dead" and definition(source, name).count(entry["old"]) != 1:
                raise ValueError(f"{label}: mutation does not belong to {name}")
            changed = source.replace(entry["old"], entry["new"], 1)
            if name == "dead":
                control = dead_source(source, reuse, True)
                mutant = dead_source(changed, reuse, False)
                kind = "consumer contract"
            else:
                fixture = row(reuse if observation.startswith("reuse-") else retirement,
                              observation)
                if name == "checkPlan":
                    fixture += "\n\n" + row(reuse, "reuse-good-run")
                control = component_source(source, name, fixture, instances, True)
                mutant = component_source(changed, name, fixture, instances, False)
                kind = "computed component"
            (evidence / f"{label}-control.lean").write_text(control)
            (evidence / f"{label}-mutant.lean").write_text(mutant)
            for stage, text in (("control", control), ("mutant", mutant), ("restored", control)):
                status, log = typecheck(root, text)
                (evidence / f"{label}-{stage}.log").write_text(log)
                if stage == "mutant":
                    errors = [line for line in log.splitlines()
                              if re.search(r"(?:^|: )error(?:\([^)]+\))?:", line)]
                    if observation is None:
                        intended = (
                            bool(errors)
                            and all("Application type mismatch:" in line for line in errors)
                            and "hdead reuseSpareCapacity hCapacity" in log
                            and "M reuseSpareCapacity = none ∨ True" in log
                        )
                    else:
                        intended = bool(errors) and all(
                            f"{observation}: expected" in line for line in errors)
                    if status in (0, 125) or not intended:
                        raise RuntimeError(f"{label}: no intended {kind} failure\n{log}")
                    print(f"{label} {kind}: " + " | ".join(errors), flush=True)
                elif status != 0:
                    raise RuntimeError(f"{label}: {stage} failed\n{log}")
            if hashes(paths) != before:
                raise RuntimeError(f"{label}: production source or manifest changed")
            results.append({"label": label, "kind": kind, "fixture": observation,
                            "control": True, "killed": True, "restored": True,
                            "production_unchanged": True})
    finally:
        (evidence / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        if hashes(paths) != before:
            raise RuntimeError("Production source or manifest changed during probes")
    print("\n| Mutation | Level | Fixture / consumer | Control | Intended kill | Restored |")
    print("|---|---|---|---|---|---|")
    for result in results:
        print(f"| {result['label']} | {result['kind']} | "
              f"{result['fixture'] or 'reuseGood unused-capacity/buffer consumer'} | "
              "PASS | PASS | PASS |")
    print(f"\n{len(results)}/{len(CASES)} probes passed; production files unchanged.")


if __name__ == "__main__":
    main()
