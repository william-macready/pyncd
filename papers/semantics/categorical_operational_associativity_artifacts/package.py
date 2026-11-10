#!/usr/bin/env python3
"""Freeze verified slice sources as ordered patches and replay them in a private index."""

import difflib
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
BASE = "8268da1f"
LEAN = "leanncd/experiments/indexed_execution/"
TASKS = [
    ("history", ["IndexedOperationalHistory", "IndexedOperationalObservationLaws"]),
    ("transport", ["IndexedOperationalReassociation", "IndexedOperationalRuns"]),
    ("composition", [
        "IndexedOperationalHistoryComposition",
        "IndexedOperationalHistoryAssociativity",
        "IndexedOperationalRunsPhases",
        "IndexedOperationalAssociativity",
        "IndexedOperationalSemantics",
    ]),
    ("acceptance", [
        "IndexedOperationalAssociativityFixtures",
        "IndexedOperationalAssociativityTest",
        "IndexedOperationalAssociativityAudit",
    ]),
]
DOCS = [
    "leanncd/AGENTS.md",
    "papers/semantics/categorical_tensor_logic_semantics.md",
    "papers/semantics/categorical_operational_associativity_mutations_post.json",
    "papers/semantics/categorical_operational_associativity_proof_mutations_post.json",
]


def git(*args, env=None):
    return subprocess.run(
        ["/usr/bin/git", "-C", str(ROOT), *args],
        check=True, text=True, capture_output=True, env=env,
    ).stdout


def original(path):
    exists = subprocess.run(
        ["/usr/bin/git", "-C", str(ROOT), "cat-file", "-e", f"{BASE}:{path}"],
        capture_output=True,
    )
    if exists.returncode == 0:
        return git("show", f"{BASE}:{path}")
    if exists.returncode != 128:
        raise RuntimeError(f"Unexpected git object lookup failure for {path}")
    return ""


def diff(path, before, after):
    return "".join(difflib.unified_diff(
        before.splitlines(keepends=True), after.splitlines(keepends=True),
        fromfile=f"a/{path}" if before else "/dev/null", tofile=f"b/{path}",
    ))


def main():
    lakefile = "leanncd/lakefile.toml"
    base_lake = original(lakefile)
    final_lake = (ROOT / lakefile).read_text()
    modules = [module for _, group in TASKS for module in group]
    included = set()
    previous_lake = base_lake
    hashes = {}
    patches = []
    for task, group in TASKS:
        included.update(group)
        next_lake = "".join(
            line for line in final_lake.splitlines(keepends=True)
            if not any(f'"{name}"' in line and name not in included for name in modules)
        )
        patch = diff(lakefile, previous_lake, next_lake)
        for module in group:
            path = f"{LEAN}{module}.lean"
            content = (ROOT / path).read_text()
            patch += diff(path, original(path), content)
            hashes[path] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        destination = OUT / f"{task}.patch"
        destination.write_text(patch)
        patches.append(destination)
        previous_lake = next_lake
    if previous_lake != final_lake:
        raise RuntimeError("Incremental module wiring does not reproduce the final lakefile")
    docs_patch = ""
    for path in DOCS:
        docs_patch += diff(path, original(path), (ROOT / path).read_text())
        hashes[path] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
    destination = OUT / "documentation.patch"
    destination.write_text(docs_patch)
    patches.append(destination)
    hashes[lakefile] = hashlib.sha256((ROOT / lakefile).read_bytes()).hexdigest()

    fd, index_name = tempfile.mkstemp(prefix="replay-index-", dir=OUT)
    os.close(fd)
    index = Path(index_name)
    index.unlink()
    env = dict(os.environ, GIT_INDEX_FILE=str(index))
    try:
        git("read-tree", BASE, env=env)
        for patch in patches:
            git("apply", "--cached", "--check", str(patch), env=env)
            git("apply", "--cached", str(patch), env=env)
        for path, digest in hashes.items():
            content = git("show", f":{path}", env=env).encode()
            if hashlib.sha256(content).hexdigest() != digest:
                raise RuntimeError(f"Replay source identity mismatch: {path}")
    finally:
        index.unlink(missing_ok=True)
        Path(f"{index}.lock").unlink(missing_ok=True)
    receipt = {
        "base": git("rev-parse", BASE).strip(),
        "patches": [
            {"path": p.name, "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
            for p in patches
        ],
        "sources": hashes,
        "ordered_private_index_replay": "PASS",
    }
    (OUT / "package.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"PASS: {len(patches)} ordered patches, {len(hashes)} byte-identical files")


def snippets():
    logs = OUT / "snippets"
    logs.mkdir(exist_ok=True)
    receipts = []
    for _, modules in TASKS:
        for module in modules:
            source = ROOT / LEAN / f"{module}.lean"
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            result = subprocess.run(
                ["bash", str(ROOT / ".claude/skills/slice-plan/check-snippet.sh"), str(source)],
                cwd=ROOT, text=True, capture_output=True,
            )
            (logs / f"{module}.log").write_text(result.stdout + result.stderr)
            if result.returncode:
                raise RuntimeError(f"{module} snippet failed:\n{result.stdout}\n{result.stderr}")
            if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
                raise RuntimeError(f"{module} changed during snippet verification")
            receipts.append({"module": module, "source_sha256": digest, "exit": 0})
            print(f"PASS: {module}")
    (OUT / "snippets.json").write_text(json.dumps(receipts, indent=2) + "\n")


if __name__ == "__main__":
    if sys.argv[1:] == ["--snippets"]:
        snippets()
    elif not sys.argv[1:]:
        main()
    else:
        raise SystemExit("usage: package.py [--snippets]")
