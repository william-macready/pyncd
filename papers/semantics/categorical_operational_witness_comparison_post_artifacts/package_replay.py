#!/usr/bin/env python3
"""Freeze and replay the compiled 01-10 prototype plus documentation patch 11."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = "37500cab85a2989a1422da2ef21256cb5648e8da"
STEM = "papers/semantics/categorical_operational_witness_comparison"
DOC = "papers/semantics/categorical_tensor_logic_semantics.md"
MANIFEST = HERE / "replay-manifest.json"
TREE = HERE / "ordered-replay-tree"
GROUPS = ("artifacts", "stage2_artifacts", "acceptance_artifacts", "post_artifacts")
TARGETS = (
    ["IndexedRankedWitnessBridge"],
    ["IndexedRankedWitnessDescent"],
    ["IndexedRankedWitnessBridge", "IndexedRankedWitnessDescent"],
    ["IndexedRankedWitnessComparison"],
    ["IndexedRankedWitnessSource"],
    ["IndexedRankedWitnessOutcomes"],
    ["IndexedRankedWitnessOutcomeTest"],
    ["IndexedRankedWitnessCategoryTest"],
    ["IndexedRankedWitnessBoundaryTest", "IndexedRankedWitnessSemantics"],
    ["IndexedRankedWitnessControlTest", "IndexedRankedWitnessNamespaceAudit"],
    [],
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None


def run(args, commands=None):
    result = subprocess.run(args, cwd=ROOT, capture_output=True)
    if commands is not None:
        commands.append({"command": args, "exit": result.returncode})
    if result.returncode:
        raise RuntimeError(f"{args!r}: {result.stderr.decode(errors='replace')}")
    return result.stdout


def git(*args, commands=None):
    return run(["/usr/bin/git", "-C", str(ROOT), *args], commands)


def base_files():
    return set(git("ls-tree", "-r", "--name-only", BASE).decode().splitlines())


def snapshot(root, paths):
    for path in paths:
        if (root / path).is_symlink():
            raise RuntimeError(f"refusing symlink: {root / path}")
    return {path: digest(root / path) for path in sorted(paths)}


def require_state(root, expected):
    if snapshot(root, expected) != expected:
        raise RuntimeError(f"owned-file drift under {root}; no overwrite permitted")


def apply(patch, root, reverse=False, commands=None):
    args = ["apply"]
    if reverse:
        args.append("--reverse")
    if root != ROOT:
        args.append(f"--directory={root.relative_to(ROOT)}")
    git(*args, "--check", str(ROOT / patch), commands=commands)
    git(*args, str(ROOT / patch), commands=commands)


def replay(data, freeze=False):
    if TREE.exists() or TREE.is_symlink():
        raise RuntimeError(f"refusing existing replay tree: {TREE}")
    TREE.mkdir()
    commands = []
    try:
        for path, sha in data["base_sha256"].items():
            if sha is not None:
                target = TREE / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(git("show", f"{BASE}:{path}"))
        require_state(TREE, data["base_sha256"])
        for step in data["patches"]:
            before = snapshot(TREE, step["files"])
            apply(step["path"], TREE, commands=commands)
            after = snapshot(TREE, step["files"])
            if freeze:
                step.update(before_sha256=before, after_sha256=after)
            elif before != step["before_sha256"] or after != step["after_sha256"]:
                raise RuntimeError(f"step drift: {step['number']}")
        require_state(TREE, data["final_sha256"])
        for path in data["final_sha256"]:
            if (TREE / path).read_bytes() != (ROOT / path).read_bytes():
                raise RuntimeError(f"compiled/documented byte mismatch: {path}")
        for step in reversed(data["patches"]):
            apply(step["path"], TREE, reverse=True, commands=commands)
        require_state(TREE, data["base_sha256"])
        for step in data["patches"]:
            apply(step["path"], TREE, commands=commands)
        require_state(TREE, data["final_sha256"])
    finally:
        # Only the tree created by this invocation is removed.
        shutil.rmtree(TREE)
    (HERE / "ordered-replay-evidence.json").write_text(json.dumps({
        "phase": "AUTHORING only; not controller execution",
        "base": BASE, "ordered_check_apply_reverse_forward": commands,
        "final_byte_equal": True, "base_restored_in_disposable_tree": True,
        "owned_replay_tree_removed": True,
    }, indent=2) + "\n")


def package():
    if git("rev-parse", "HEAD").decode().strip() != BASE:
        raise RuntimeError("packaging requires the exact compiled prototype base")
    post = json.loads((HERE / "package-evidence.json").read_text())
    require_state(ROOT, post["source_sha256"])
    mutation = ROOT / f"{STEM}_mutations_post.json"
    if digest(mutation) != post["manifest_sha256"]:
        raise RuntimeError("compiled control manifest changed")
    for group in GROUPS[:-1]:
        evidence = json.loads((ROOT / f"{STEM}_{group}/evidence.json").read_text())
        require_state(ROOT, {p: h for p, h in evidence["source_sha256"].items()
                             if p != "leanncd/lakefile.toml"})
    patch11 = HERE / "11-synthesis.patch"
    patch11.write_bytes(git("diff", "--binary", BASE, "--", DOC))
    if not patch11.stat().st_size:
        raise RuntimeError("missing documentation delta")
    patches = sorted(
        (p for group in GROUPS for p in (ROOT / f"{STEM}_{group}").glob("*.patch")),
        key=lambda p: p.name,
    )
    if [int(p.name[:2]) for p in patches] != list(range(1, 12)):
        raise RuntimeError("expected exactly patches 01-11")
    data = {"base": BASE, "patches": [], "phase": "execution PENDING"}
    for number, patch in enumerate(patches, 1):
        files = re.findall(r"^diff --git a/(\S+) b/\1$", patch.read_text(), re.M)
        if not files or any(".." in Path(p).parts or Path(p).is_absolute() for p in files):
            raise RuntimeError(f"unsafe/empty ownership: {patch}")
        data["patches"].append({
            "number": number, "path": str(patch.relative_to(ROOT)),
            "sha256": digest(patch), "files": files, "targets": TARGETS[number - 1],
            "replay_after": list(range(1, number)),
        })
    owned = sorted({p for step in data["patches"] for p in step["files"]})
    tracked = base_files()
    data["base_sha256"] = {
        p: hashlib.sha256(git("show", f"{BASE}:{p}")).hexdigest() if p in tracked else None
        for p in owned
    }
    data["final_sha256"] = snapshot(ROOT, owned)
    evidence_paths = [
        p for group in GROUPS for p in (ROOT / f"{STEM}_{group}").iterdir()
        if p.is_file() and p.suffix in (".json", ".log", ".py")
        and p.name not in ("replay-manifest.json", "ordered-replay-evidence.json")
    ]
    data["evidence_sha256"] = snapshot(ROOT, [str(p.relative_to(ROOT)) for p in evidence_paths])
    replay(data, freeze=True)
    MANIFEST.write_text(json.dumps(data, indent=2) + "\n")
    print(f"PASS package: {len(patches)} patches; {len(owned)} exact owned files")


def audit(data):
    require_state(ROOT, data["evidence_sha256"])
    for step in data["patches"]:
        if digest(ROOT / step["path"]) != step["sha256"]:
            raise RuntimeError(f"patch drift: {step['path']}")
    print("PASS hashes: patches, evidence/scripts/logs")


def source_audit(data):
    require_state(ROOT, data["final_sha256"])
    sources = sorted((ROOT / "leanncd/experiments/indexed_execution").glob("IndexedRankedWitness*.lean"))
    if len(sources) != 13:
        raise RuntimeError("expected 13 frozen Lean files")
    namespaces = set()
    for path in sources:
        text = path.read_text()
        if re.search(r"\b(?:sorry|admit|sorryAx)\b|^\s*axiom\b", text, re.M):
            raise RuntimeError(f"placeholder/new axiom: {path}")
        namespaces.update(re.findall(r"^namespace (IndexedRankedWitness\w+)\s*$", text, re.M))
    expected = json.loads((HERE / "package-evidence.json").read_text())["namespaces"]
    if namespaces != set(expected) or len(namespaces) != 9:
        raise RuntimeError("namespace coverage drift")
    changed = git("diff", "--name-only", BASE, "--", "leanncd").decode().splitlines()
    if any(p.endswith(".lean") and p not in data["final_sha256"] for p in changed):
        raise RuntimeError("existing Lean/default import changed")
    old = tomllib.loads(git("show", f"{BASE}:leanncd/lakefile.toml").decode())
    new = tomllib.loads((ROOT / "leanncd/lakefile.toml").read_text())
    for config in (old, new):
        libs = config["lean_lib"]
        experiment = [lib for lib in libs if lib["name"] == "IndexedExecutionExperiment"]
        if len(experiment) != 1:
            raise RuntimeError("missing nondefault experiment")
        config["lean_lib"] = [lib for lib in libs if lib["name"] != "IndexedExecutionExperiment"]
    if old != new:
        raise RuntimeError("default configuration/import registrations changed")
    print("PASS source scan: 13 files; nine namespaces; no default import/config changes")


def expected_at(data, number):
    state = dict(data["base_sha256"])
    for step in data["patches"][:number]:
        state.update(step["after_sha256"])
    return state


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("package", "audit", "replay", "reverse", "forward", "source-audit"))
    parser.add_argument("number", nargs="?", type=int)
    args = parser.parse_args()
    if args.action == "package":
        package()
        return
    data = json.loads(MANIFEST.read_text())
    if data["base"] != BASE:
        raise RuntimeError("base mismatch")
    audit(data)
    if args.action == "audit":
        require_state(ROOT, data["final_sha256"])
    elif args.action == "source-audit":
        source_audit(data)
    elif args.action == "replay":
        require_state(ROOT, data["final_sha256"])
        replay(data)
        print("PASS ordered replay/reverse/forward; byte-equal; own tree removed")
    elif args.action == "reverse":
        require_state(ROOT, data["final_sha256"])
        replay(data)
        for step in reversed(data["patches"]):
            require_state(ROOT, expected_at(data, step["number"]))
            apply(step["path"], ROOT, reverse=True)
        require_state(ROOT, data["base_sha256"])
        print("PASS reverse: only owned patches 11-01 removed; package retained")
    else:
        if args.number is None or not 1 <= args.number <= 11:
            parser.error("forward requires a patch number 1-11")
        require_state(ROOT, expected_at(data, args.number - 1))
        step = data["patches"][args.number - 1]
        apply(step["path"], ROOT)
        require_state(ROOT, expected_at(data, args.number))
        print(f"PASS forward {args.number:02d}: {step['files']}")


if __name__ == "__main__":
    main()
