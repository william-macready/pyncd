#!/usr/bin/env python3
"""Freeze compiled task patches, verify a private-index replay, or execute them."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


BASE = "a9c9a647a04e260e21c8e5c624a0bac3fa13ef20"
ARTIFACTS = Path(__file__).resolve().parent
ROOT = ARTIFACTS.parents[2]
TASKS = [
    ("1", "feat(semantics): add whole-interface witness-span category",
     "3fc437a28834d614ca730caaa78c1026c658efd0",
     ["IndexedWitnessInterface", "IndexedWitnessSpan", "IndexedWitnessTest"]),
    ("2", "feat(semantics): interpret component composition as witness pullback",
     "c71ee3d3", ["IndexedWitnessComposition", "IndexedWitnessTest"]),
    ("3", "feat(semantics): prove nested composition witness coherence",
     "451a5bb5", ["IndexedWitnessCoherence", "IndexedWitnessCoherenceTest"]),
    ("4", "feat(semantics): restrict witness spans to partial maps",
     "0a3b8e97", ["IndexedWitnessPartial", "IndexedWitnessPartialTest"]),
    ("5", "test(semantics): discriminate witness composition observations",
     "2cbf39e9", ["IndexedWitnessCompositionTest"]),
    ("6", "test(semantics): isolate copied witness observation probes",
     None, ["IndexedWitnessObservationProbeTest", "IndexedWitnessObservationParity"]),
    ("7", "docs(semantics): expose proved witness semantics and scope",
     None, ["IndexedWitnessSemantics"]),
]


def run(argv, *, cwd=None, env=None):
    result = subprocess.run(argv, cwd=cwd, env=env, capture_output=True)
    if result.returncode:
        print(result.stdout.decode("utf-8", errors="replace"))
        print(result.stderr.decode("utf-8", errors="replace"))
        raise subprocess.CalledProcessError(result.returncode, argv)
    return result.stdout


def git(root, *args, env=None):
    return run(["git", "-C", str(root), *args], env=env)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def emit(prototype, task6, task7):
    patches = ARTIFACTS / "patches"
    patches.mkdir(exist_ok=True)
    before = BASE
    tasks = []
    for task_id, title, commit, targets in TASKS:
        after = git(prototype, "rev-parse",
                    task6 if task_id == "6" else task7 if task_id == "7" else commit).decode().strip()
        git(prototype, "merge-base", "--is-ancestor", before, after)
        patch = git(prototype, "diff", "--binary", before, after, "--")
        filename = f"task-{task_id}.patch"
        (patches / filename).write_bytes(patch)
        paths = git(prototype, "diff", "--name-only", before, after).decode().splitlines()
        files = {p: digest(git(prototype, "show", f"{after}:{p}")) for p in paths}
        tasks.append(dict(id=task_id, title=title, source_commit=after,
                          patch=f"patches/{filename}", patch_sha256=digest(patch),
                          files=files, targets=targets))
        before = after
    package = dict(base=BASE, source_head=before,
                   source_tree=git(prototype, "rev-parse", f"{before}^{{tree}}").decode().strip(),
                   tasks=tasks)
    (ARTIFACTS / "package.json").write_text(json.dumps(package, indent=2) + "\n")
    print(f"EMITTED {len(tasks)} compiled task patches")


def load():
    package = json.loads((ARTIFACTS / "package.json").read_text())
    for task in package["tasks"]:
        if digest((ARTIFACTS / task["patch"]).read_bytes()) != task["patch_sha256"]:
            raise ValueError(f"patch hash mismatch: task {task['id']}")
    return package


def check(root, package):
    with tempfile.TemporaryDirectory(prefix="witness-index-") as temp:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(temp) / "index"))
        git(root, "read-tree", package["base"], env=env)
        for task in package["tasks"]:
            patch = str(ARTIFACTS / task["patch"])
            git(root, "apply", "--cached", "--check", patch, env=env)
            git(root, "apply", "--cached", patch, env=env)
            for path, expected in task["files"].items():
                if digest(git(root, "show", f":{path}", env=env)) != expected:
                    raise ValueError(f"intermediate source mismatch: task {task['id']}, {path}")
        tree = git(root, "write-tree", env=env).decode().strip()
        if tree != package["source_tree"]:
            raise ValueError("replayed tree differs from compiled prototype tree")
    print("PASS: every patch/intermediate hash and exact final tree")


def replay(root, package):
    if git(root, "diff", "--name-only").strip() or git(root, "diff", "--cached", "--name-only").strip():
        raise ValueError("execution checkout has tracked uncommitted edits")
    git(root, "merge-base", "--is-ancestor", package["base"], "HEAD")
    changed = git(root, "diff", "--name-only", package["base"], "HEAD").decode().splitlines()
    if any(not p.startswith("papers/semantics/categorical_witness_semantics") for p in changed):
        raise ValueError("execution checkout differs from base outside the plan package")
    checkpoints = []
    for task in package["tasks"]:
        patch = str(ARTIFACTS / task["patch"])
        git(root, "apply", "--check", patch)
        git(root, "apply", patch)
        run(["bash", str(root / "leanncd/scripts/lake-build.sh"),
             str(root / "leanncd"), *task["targets"]])
        for path, expected in task["files"].items():
            if digest((root / path).read_bytes()) != expected:
                raise ValueError(f"execution source mismatch: task {task['id']}, {path}")
            if path.endswith(".lean"):
                run(["bash", str(root / ".claude/skills/slice-plan/check-snippet.sh"),
                     str(root / path)], cwd=root)
        if task["id"] in ("6", "7"):
            run(["python3", str(ARTIFACTS / "probes.py"),
                 "--check", "--prototype", str(root)])
        git(root, "add", "--", *task["files"])
        git(root, "diff", "--cached", "--check")
        git(root, "commit", "-m", task["title"], "-m",
            "Execute the frozen, compiled task patch; targeted build, exact source "
            "hashes and post-application snippet checks passed.\n\n"
            "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>")
        checkpoints.append(dict(task=task["id"], commit=git(root, "rev-parse", "HEAD").decode().strip(),
                                targets=task["targets"], source_hashes="pass",
                                snippets="pass", controller_review="exact frozen bytes"))
        (ARTIFACTS / "execution_replay.json").write_text(json.dumps(checkpoints, indent=2) + "\n")
        print(f"PASS task {task['id']}: built, hash-checked, snippet-checked, committed", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkout", type=Path, default=ROOT)
    parser.add_argument("--prototype", type=Path)
    parser.add_argument("--task6")
    parser.add_argument("--task7")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--emit", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    if args.emit:
        if not (args.prototype and args.task6 and args.task7):
            parser.error("--emit requires --prototype, --task6 and --task7")
        emit(args.prototype.resolve(), args.task6, args.task7)
    else:
        package = load()
        check(args.checkout.resolve(), package)
        if args.replay:
            replay(args.checkout.resolve(), package)


if __name__ == "__main__":
    main()
