"""Export compiled task bytes and execute them in the task-owned replay checkout."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
ARTIFACTS = Path(__file__).resolve().parent
BASE = "2212263c"
PREFIX = "leanncd/experiments/indexed_execution/"
LAKE = "leanncd/lakefile.toml"
TASKS = [
    ("inputs", ["IndexedComponentModelInputs"], []),
    ("transport", ["IndexedComponentModelTransport"], []),
    ("witnesses", ["IndexedComponentModelWitnesses"], []),
    ("denotation", ["IndexedComponentModelDenotation"], []),
    ("local-fixtures", ["IndexedComponentModelLocalFixtures", "IndexedComponentModelLocalTest"], []),
    ("geometry-fixtures", ["IndexedComponentModelGeometryFixtures", "IndexedComponentModelGeometryTest"], []),
    ("cycle-fixtures", ["IndexedComponentModelCycleFixtures", "IndexedComponentModelCycleTest"], []),
    ("discovery", ["IndexedComponentModelTest"],
     ["leanncd/AGENTS.md", "papers/semantics/categorical_tensor_logic_component_interfaces.md"]),
]


def git(*args, cwd=ROOT, env=None, data=None):
    return subprocess.run(
        ["git", *args], cwd=cwd, env=env, input=data, stdout=subprocess.PIPE,
        check=True,
    ).stdout


def digest(data):
    return hashlib.sha256(data).hexdigest()


def emit():
    lake = git("show", f"{BASE}:{LAKE}").decode()
    previous = git("rev-parse", f"{BASE}^{{tree}}").decode().strip()
    rows = []
    with tempfile.TemporaryDirectory(prefix="component-model-index-") as directory:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(directory) / "index"))
        git("read-tree", BASE, env=env)
        for index, (task, modules, docs) in enumerate(TASKS, 1):
            sources = [PREFIX + module + ".lean" for module in modules]
            files = sources + docs + [LAKE]
            added = ", ".join(json.dumps(module) for module in modules)
            lake = lake.rstrip()[:-1] + f",\n         {added}]\n"
            hashes = {}
            for path in files:
                data = lake.encode() if path == LAKE else (ROOT / path).read_bytes()
                blob = git("hash-object", "-w", "--stdin", data=data).decode().strip()
                git("update-index", "--add", "--cacheinfo", "100644", blob, path, env=env)
                hashes[path] = digest(data)
            tree = git("write-tree", env=env).decode().strip()
            patch = git("diff", "--binary", "--full-index", previous, tree)
            name = f"task_{index:02d}_{task}.patch"
            (ARTIFACTS / name).write_bytes(patch)
            rows.append({
                "task": task, "patch": name, "sha256": digest(patch),
                "files": files, "sources": sources, "targets": modules,
                "source_hashes": hashes,
            })
            previous = tree
    if lake.encode() != (ROOT / LAKE).read_bytes():
        raise RuntimeError("Task registration order does not match the compiled lakefile")
    (ARTIFACTS / "task_patches.json").write_text(
        json.dumps({"base": BASE, "tasks": rows}, indent=2) + "\n"
    )
    print(f"Exported {len(rows)} compiled task patches.")


def check():
    package = json.loads((ARTIFACTS / "task_patches.json").read_text())
    final_hashes = {}
    with tempfile.TemporaryDirectory(prefix="component-model-check-") as directory:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(directory) / "index"))
        git("read-tree", package["base"], env=env)
        for row in package["tasks"]:
            patch = ARTIFACTS / row["patch"]
            if digest(patch.read_bytes()) != row["sha256"]:
                raise RuntimeError(f"Patch hash mismatch: {row['patch']}")
            git("apply", "--cached", "--check", str(patch), env=env)
            git("apply", "--cached", str(patch), env=env)
            final_hashes.update(row["source_hashes"])
            print(f"{row['task']}: applies cleanly")
        tree = git("write-tree", env=env).decode().strip()
        for path, expected in final_hashes.items():
            if digest(git("show", f"{tree}:{path}")) != expected:
                raise RuntimeError(f"Replayed tree hash mismatch: {path}")
            if digest((ROOT / path).read_bytes()) != expected:
                raise RuntimeError(f"Compiled source changed: {path}")
    print("All patch bytes and final sources match the compiled prototype.")


def replay(target):
    target = target.resolve()
    if target.name != "component-model-gluing-replay" or target == ROOT:
        raise RuntimeError("Refusing a checkout other than the task-owned replay")
    package = json.loads((ARTIFACTS / "task_patches.json").read_text())
    if git("rev-parse", "HEAD", cwd=target).decode().strip() != git(
        "rev-parse", package["base"]
    ).decode().strip():
        raise RuntimeError("Replay must start at the package base")
    if git("status", "--porcelain", cwd=target).strip():
        raise RuntimeError("Replay checkout is not clean")
    results = []
    for row in package["tasks"]:
        patch = ARTIFACTS / row["patch"]
        if digest(patch.read_bytes()) != row["sha256"]:
            raise RuntimeError(f"Patch hash mismatch: {patch.name}")
        git("apply", "--check", str(patch), cwd=target)
        git("apply", str(patch), cwd=target)
        log = ARTIFACTS / f"replay_{row['task']}.log"
        print(f"{row['task']}: validating; log {log}", flush=True)
        with log.open("w") as output:
            subprocess.run(
                ["bash", str(target / "leanncd/scripts/lake-build.sh"),
                 str(target / "leanncd"), *row["targets"]],
                cwd=target, stdout=output, stderr=subprocess.STDOUT, check=True,
            )
            for source in row["sources"]:
                subprocess.run(
                    ["bash", str(target / ".claude/skills/slice-plan/check-snippet.sh"),
                     str(target / source)],
                    cwd=target, stdout=output, stderr=subprocess.STDOUT, check=True,
                )
        for path, expected in row["source_hashes"].items():
            if digest((target / path).read_bytes()) != expected:
                raise RuntimeError(f"Execution source hash mismatch: {path}")
        git("add", "--", *row["files"], cwd=target)
        git("commit", "-m", f"feat(semantics): execute model gluing {row['task']}",
            "-m", "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>",
            cwd=target)
        results.append({"task": row["task"], "build": "pass", "snippets": "pass",
                        "source_hashes": "match", "commit":
                        git("rev-parse", "HEAD", cwd=target).decode().strip()})
        (ARTIFACTS / "execution_replay.json").write_text(
            json.dumps(results, indent=2) + "\n"
        )
        print(f"{row['task']}: applied, built, source-copy checked and committed", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--emit", action="store_true")
    actions.add_argument("--check", action="store_true")
    actions.add_argument("--replay", type=Path)
    arguments = parser.parse_args()
    if arguments.emit:
        emit()
    elif arguments.check:
        check()
    else:
        replay(arguments.replay)
