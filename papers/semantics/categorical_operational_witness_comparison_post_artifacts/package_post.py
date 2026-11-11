#!/usr/bin/env python3
"""Measure authoring controls or package the additive post-09 source delta."""

import difflib
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEAN = ROOT / "leanncd"
MANIFEST = ROOT / "papers/semantics/categorical_operational_witness_comparison_mutations_post.json"
SOURCES = sorted((LEAN / "experiments/indexed_execution").glob("IndexedRankedWitness*.lean"))
PATHS = [LEAN / "lakefile.toml", LEAN / "AGENTS.md", *SOURCES]
MODULES = ["IndexedRankedWitnessControlTest", "IndexedRankedWitnessNamespaceAudit"]


def hashes():
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in PATHS}


def run(args, name, env=None, require=True):
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, env=env)
    (HERE / f"{name}.log").write_text(result.stdout + result.stderr)
    record = {"command": args, "exit": result.returncode, "log": f"{name}.log"}
    print(f"{name}: exit {result.returncode}", flush=True)
    if require and result.returncode:
        raise RuntimeError(record)
    return record


def build(name):
    return run(["bash", str(LEAN / "scripts/lake-build.sh"), str(LEAN), *MODULES], name)


def measure(labels=()):
    import os
    before = hashes()
    evidence_path = HERE / "authoring-evidence.json"
    evidence = (json.loads(evidence_path.read_text()) if labels else
                {"phase": "AUTHORING measurements, not controller replay", "cycles": []})
    if labels and evidence["source_sha256_before"] != before:
        raise RuntimeError("selective measurement requires identical source baseline")
    evidence.update({"source_sha256_before": before, "baseline": build("baseline")})
    for entry in json.loads(MANIFEST.read_text()):
        label = entry["label"].split()[0]
        if labels and label not in labels:
            continue
        log = HERE / f"{label}-mutated.log"
        args = ["bash", str(LEAN / "scripts/mutation-cycle.sh"), entry["label"], str(LEAN),
                entry["file"], entry["old"], entry["new"], *entry["targets"]]
        result = run(args, f"{label}-cycle", {**os.environ, "MUTATION_LOG": str(log)},
                     require=False)
        restored = hashes() == before
        text = log.read_text()
        result.update({"label": entry["label"], "classification": entry["classification"],
                       "mutated_log": log.name, "source_byte_identical": restored,
                       "diagnostics": [s for s in text.splitlines() if s.startswith("error:")]})
        evidence["cycles"] = [c for c in evidence["cycles"] if c["label"].split()[0] != label]
        evidence["cycles"].append(result)
        evidence["cycles"].sort(key=lambda c: c["label"])
        (HERE / "authoring-evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
        if result["exit"] or not restored or not result["diagnostics"]:
            raise RuntimeError(f"unverified control {entry['label']}")
    evidence["restored_build"] = build("all-restored")
    evidence["source_sha256_after"] = hashes()
    if hashes() != before:
        raise RuntimeError("source changed after controls")
    (HERE / "authoring-evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")


def change(path, old, new):
    return (f"diff --git a/{path} b/{path}\n"
            + ("new file mode 100644\n" if old is None else "")
            + "".join(difflib.unified_diff(
                [] if old is None else old.splitlines(keepends=True),
                new.splitlines(keepends=True),
                fromfile="/dev/null" if old is None else f"a/{path}",
                tofile=f"b/{path}")))


def package():
    audit = build("namespace-audit")
    log = (HERE / audit["log"]).read_text()
    namespaces = set()
    for path in SOURCES:
        text = path.read_text()
        if re.search(r"^\s*(?:sorry|admit|axiom)\b|\b(?:sorry|admit)\b", text, re.M):
            raise RuntimeError(f"placeholder/axiom in {path}")
        namespaces.update(re.findall(r"^namespace (IndexedRankedWitness\w+)\s*$", text, re.M))
    for ns in sorted(namespaces):
        if not re.search(rf"axiom audit: [1-9]\d* constants under {ns} use only standard axioms", log):
            raise RuntimeError(f"missing namespace audit: {ns}")
    check = run(["bash", str(LEAN / "scripts/mutation-manifest.sh"), "--check", str(LEAN),
                 str(MANIFEST)], "manifest-check")
    entries = json.loads(MANIFEST.read_text())
    coverage = {}
    for entry in entries:
        log_text = (HERE / f"{entry['label'].split()[0]}-mutated.log").read_text()
        if not entry["expect"] or any(s not in log_text for s in entry["expect"]):
            raise RuntimeError(f"unobserved expect: {entry['label']}")
        if not entry["nearest_neighbor"] or not entry["donors"]:
            raise RuntimeError("missing donor/neighbor")
        for goal in entry["acceptance_goals"]:
            coverage.setdefault(goal, []).append(entry["label"])
    if len(coverage) != 7:
        raise RuntimeError("acceptance row coverage incomplete")
    full = run(["bash", str(LEAN / "scripts/lake-build.sh"), str(LEAN),
                "LeanNCD", "Tests", "IndexedExecutionExperiment"], "full-build-post")
    full_log = (HERE / full["log"]).read_text()
    if "sorryAx" in full_log or "Build completed successfully (8964 jobs)." not in full_log:
        raise RuntimeError("full post-control build/audit incomplete")
    run(["/usr/bin/git", "-C", str(ROOT), "diff", "--check"], "whitespace")
    previous = ROOT / "papers/semantics/categorical_operational_witness_comparison_acceptance_artifacts"
    saved = json.loads((previous / "evidence.json").read_text())
    old_lake = (LEAN / "lakefile.toml").read_text()
    for name in MODULES:
        old_lake = old_lake.replace(f'         "{name}",\n', "")
    if hashlib.sha256(old_lake.encode()).hexdigest() != saved["source_sha256"]["leanncd/lakefile.toml"]:
        raise RuntimeError("post-09 lakefile baseline mismatch")
    for path, digest in saved["source_sha256"].items():
        if path != "leanncd/lakefile.toml" and hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
            raise RuntimeError(f"previous source changed: {path}")
    old_agents = (LEAN / "AGENTS.md").read_text()
    start = old_agents.index("The additive, nondefault comparison entry point is\n")
    stop = old_agents.index("The nondefault `IndexedExecutionExperiment`", start)
    old_agents = old_agents[:start] + old_agents[stop:]
    baseline = {Path("leanncd/lakefile.toml"): old_lake, Path("leanncd/AGENTS.md"): old_agents}
    paths = [*baseline, *[Path("leanncd/experiments/indexed_execution") / f"{m}.lean" for m in MODULES],
             MANIFEST.relative_to(ROOT)]
    patch = "".join(change(p, baseline.get(p), (ROOT / p).read_text()) for p in paths)
    patch_path = HERE / "10-controls-and-namespace-audit.patch"
    patch_path.write_text(patch)
    replay = HERE / "patch-validation"
    if replay.exists():
        raise RuntimeError("refusing existing replay tree")
    replay.mkdir()
    try:
        for path, text in baseline.items():
            (replay / path).parent.mkdir(parents=True, exist_ok=True)
            (replay / path).write_text(text)
        prefix = str(replay.relative_to(ROOT))
        patch_check = run(["/usr/bin/git", "-C", str(ROOT), "apply", "--check",
                          f"--directory={prefix}", str(patch_path)], "patch-check")
        run(["/usr/bin/git", "-C", str(ROOT), "apply",
             f"--directory={prefix}", str(patch_path)], "patch-apply")
        for path in paths:
            if (replay / path).read_bytes() != (ROOT / path).read_bytes():
                raise RuntimeError(f"replay differs: {path}")
    finally:
        shutil.rmtree(replay)
    evidence = {"phase": "post-09 additive packaging, not controller release gate",
                "baseline": "compiled acceptance patches 01-09; previous sources byte-identical",
                "audit": audit, "full_build": full,
                "namespaces": sorted(namespaces), "source_sha256": hashes(),
                "source_audit": "all IndexedRankedWitness*.lean: no sorry, admit, or axiom declarations",
                "manifest_check": check, "patch_check": patch_check, "patch_replay_byte_equal": True,
                "patch_sha256": hashlib.sha256(patch_path.read_bytes()).hexdigest(),
                "manifest_sha256": hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),
                "log_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted(HERE.glob("*.log"))},
                "acceptance_goal_controls": coverage,
                "counts": {"controls": 12, "runtime_fixture_observations": 3, "live_proof_controls": 9,
                           "new_generic_laws": 2, "new_executable_assertions": 1,
                           "new_concrete_fixture_instances": 0}}
    (HERE / "package-evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print("Post-09 patch replay byte-exact; all namespaces standard-only.", flush=True)


def replay():
    before = hashes()
    result = run(["bash", str(LEAN / "scripts/mutation-manifest.sh"), str(LEAN), str(MANIFEST)],
                 "authoring-unfiltered-manifest", require=False)
    evidence = {"phase": "AUTHORING canonical wrapper replay, not later controller release gate",
                "command": result, "source_sha256_before": before,
                "source_sha256_after": hashes(), "byte_identical": hashes() == before}
    (HERE / "authoring-replay-evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    if result["exit"] or hashes() != before:
        raise RuntimeError("canonical authoring replay failed")


if __name__ == "__main__":
    if sys.argv[1:2] == ["measure"]:
        measure(sys.argv[2:])
    elif sys.argv[1:] == ["package"]:
        package()
    elif sys.argv[1:] == ["replay"]:
        replay()
    else:
        raise SystemExit("usage: package_post.py measure [Pxx...]|package|replay")
