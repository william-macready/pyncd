"""Verify immutable patch assets, ordered patch replay and the current task boundary.

Usage: python3 papers/semantics/jax_boolean_reach_files/verify_package.py [--task N]
--task N: the working tree is expected to hold exactly the files of task N's snapshot (0 = unimplemented baseline).
The real Git index is never modified (replay uses a temporary index file).
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
GIT = ["git", "-C", str(ROOT)]
parser = argparse.ArgumentParser()
parser.add_argument("--task", type=int, choices=range(5), default=0,
                    help="current working-tree boundary; 0 means unimplemented source baseline")
args = parser.parse_args()
package = json.loads((HERE / "package.json").read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(*argv, **kwargs):
    return subprocess.check_output([*GIT, *argv], **kwargs)


snapshots = {}
for task in package["tasks"]:
    assert sha((ROOT / task["patch"]).read_bytes()) == task["patch_sha256"], task["patch"]
    assert sha((ROOT / task["snapshot"]).read_bytes()) == task["snapshot_sha256"], task["snapshot"]
    snapshots[int(task["id"][1:])] = json.loads((ROOT / task["snapshot"]).read_text())

final = snapshots[4]
if args.task:
    for path, hashes in snapshots[args.task].items():
        assert sha((ROOT / path).read_bytes()) == hashes["sha256"], ("task boundary", args.task, path)
else:
    for path, hashes in final.items():
        actual = ROOT / path
        if hashes["baseline_sha256"] is None:
            assert not actual.exists(), ("new implementation file already exists", path)
        else:
            assert sha(actual.read_bytes()) == hashes["baseline_sha256"], ("source baseline", path)

before = git("diff", "--cached", "--binary")
subprocess.run([*GIT, "merge-base", "--is-ancestor", package["source_baseline"], "HEAD"], check=True)
with tempfile.TemporaryDirectory(prefix="boolean-reach-plan-index-") as temp:
    env = dict(os.environ, GIT_INDEX_FILE=str(Path(temp) / "index"))
    git("read-tree", package["source_baseline"], env=env)
    for task in package["tasks"]:
        number = int(task["id"][1:])
        git("apply", "--cached", "--check", str(ROOT / task["patch"]), env=env)
        git("apply", "--cached", str(ROOT / task["patch"]), env=env)
        for path, hashes in snapshots[number].items():
            assert sha(git("show", ":" + path, env=env)) == hashes["sha256"], (number, path)
            assert git("rev-parse", ":" + path, env=env).decode().strip() == hashes["blob"], (number, path)
assert git("diff", "--cached", "--binary") == before, "real Git index changed"
print(f"Package OK: {len(package['tasks'])} ordered patches, task {args.task} boundary; index unchanged.")
