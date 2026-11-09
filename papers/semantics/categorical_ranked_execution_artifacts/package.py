#!/usr/bin/env python3
"""Freeze compiled task patches, or verify their immutable application package."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = "a8568ddb9df27867bfd40d8c5a3fb590cfbab6d8"
LEAN = "leanncd/experiments/indexed_execution/"
DOCS = "papers/semantics/"
TASKS = [
    ("01-ranks", ["leanncd/lakefile.toml", LEAN + "IndexedComponentCompositionRanks.lean"],
     ["IndexedComponentCompositionRanks"]),
    ("02-state-transport", [LEAN + name + ".lean" for name in [
        "IndexedComponentExecutionFuel", "IndexedComponentExecutionTransport",
        "IndexedComponentExecutionPhase"]],
     ["IndexedComponentExecutionFuel", "IndexedComponentExecutionTransport",
      "IndexedComponentExecutionPhase"]),
    ("03-graph-runs", [LEAN + "IndexedComponentExecutionRuns.lean"],
     ["IndexedComponentExecutionRuns"]),
    ("04-reference-runs", [LEAN + "IndexedComponentExecutionReference.lean",
                           LEAN + "IndexedRankedExecutionSemantics.lean"],
     ["IndexedComponentExecutionReference", "IndexedRankedExecutionSemantics"]),
    ("05-acceptance", [LEAN + name + ".lean" for name in [
        "IndexedComponentRankedExecutionFixtures", "IndexedComponentRankedExecutionRankTest",
        "IndexedComponentRankedExecutionTest", "IndexedComponentRankedExecutionAudit"]] + [
        DOCS + "categorical_ranked_execution_mutations.json",
        DOCS + "categorical_ranked_execution_mutations_post.json",
        DOCS + "categorical_ranked_execution_fixture_mutation_results.md",
        DOCS + "categorical_ranked_execution_snapshot_mutation_results.md",
        DOCS + "categorical_ranked_execution_inherited_mutation_results.md"],
     ["IndexedComponentRankedExecutionAudit"]),
    ("06-documentation", ["leanncd/AGENTS.md",
                           DOCS + "categorical_tensor_logic_semantics.md",
                           DOCS + "categorical_tensor_logic_component_interfaces.md",
                           DOCS + "categorical_ranked_execution_record.md"], []),
]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(*args, env=None, diff=False):
    result = subprocess.run(
        ["/usr/bin/git", "-C", str(ROOT), *args],
        capture_output=True, env=env, check=False,
    )
    if result.returncode not in ({0, 1} if diff else {0}):
        raise RuntimeError(result.stderr.decode(errors="replace"))
    return result.stdout


def emit():
    package = {"base": BASE, "tasks": []}
    for task, paths, targets in TASKS:
        chunks = []
        files = []
        for path in paths:
            data = (ROOT / path).read_bytes()
            tracked = subprocess.run(
                ["/usr/bin/git", "-C", str(ROOT), "cat-file", "-e", BASE + ":" + path],
                capture_output=True, check=False,
            ).returncode == 0
            chunks.append(
                git("diff", "--binary", BASE, "--", path) if tracked
                else git("diff", "--no-index", "--binary", "--", "/dev/null", path, diff=True)
            )
            files.append({"path": path, "sha256": digest(data)})
        patch = b"".join(chunks)
        name = task + ".patch"
        (HERE / name).write_bytes(patch)
        package["tasks"].append({
            "id": task, "patch": name, "sha256": digest(patch),
            "targets": targets, "files": files,
        })
    (HERE / "package.json").write_text(json.dumps(package, indent=2) + "\n")
    return package


def verify(package):
    with tempfile.TemporaryDirectory(prefix="ranked-execution-index-") as directory:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(directory) / "index"))
        git("read-tree", package["base"], env=env)
        for task in package["tasks"]:
            patch = HERE / task["patch"]
            if digest(patch.read_bytes()) != task["sha256"]:
                raise RuntimeError("patch hash mismatch: " + str(patch))
            git("apply", "--cached", str(patch), env=env)
            for file in task["files"]:
                if digest(git("show", ":" + file["path"], env=env)) != file["sha256"]:
                    raise RuntimeError("applied source mismatch: " + file["path"])
    count = sum(len(task["files"]) for task in package["tasks"])
    print(f"{len(package['tasks'])} task patches, {count} files: hashes and ordered application PASS")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify the frozen package only")
    args = parser.parse_args()
    package = json.loads((HERE / "package.json").read_text()) if args.check else emit()
    verify(package)


if __name__ == "__main__":
    main()
