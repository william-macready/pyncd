#!/usr/bin/env python3
"""Assemble or verify B5 patch snapshots without checking out Lean source."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
INDEX = HERE / ".assembly-index"


def git(*args, data=None):
    env = dict(os.environ, GIT_INDEX_FILE=str(INDEX))
    return subprocess.check_output(
        ["/usr/bin/git", "-C", str(ROOT), *args], input=data, env=env
    )


def sha(data):
    return hashlib.sha256(data).hexdigest()


def tree():
    return git("write-tree").decode().strip()


def blob(tree_id, path):
    return git("show", f"{tree_id}:{path}")


def file_rows(tree_id, paths):
    return [
        {"path": p, "bytes": len(blob(tree_id, p)), "sha256": sha(blob(tree_id, p))}
        for p in paths
    ]


def verify():
    meta = json.loads((HERE / "snapshots.json").read_text())
    git("read-tree", meta["base"])
    for stage in meta["stages"]:
        data = (HERE / stage["patch"]).read_bytes()
        assert sha(data) == stage["sha256"], stage["patch"]
        git("apply", "--cached", "--whitespace=error", "--check", "-", data=data)
        git("apply", "--cached", "-", data=data)
        assert tree() == stage["tree"], stage["patch"]
    assert tree() == meta["final_tree"]
    assert file_rows(tree(), [r["path"] for r in meta["files"]]) == meta["files"]
    print(f"PASS: {len(meta['stages'])} ordered patches; {len(meta['files'])} files; "
          f"final tree {meta['final_tree']}")


def generate(evidence, increments=()):
    base = git("rev-parse", "d62c8857^{commit}").decode().strip()
    git("read-tree", base)
    inputs = []
    for name in ("native_prototype.patch", "oracle_prototype.patch",
                 "boundary_prototype.patch"):
        data = (evidence / name).read_bytes()
        git("apply", "--cached", "--check", "-", data=data)
        git("apply", "--cached", "-", data=data)
        inputs.append({"name": name, "bytes": len(data), "sha256": sha(data)})
    before_registration = tree()
    lake = "leanncd/lakefile.toml"
    content = blob(before_registration, lake)
    old = b'"Eval.Plan.B5NativeTest",'
    assert content.count(old) == 1
    content = content.replace(
        old, b'"Eval.Plan.B5NativeTest", "Eval.Plan.B5BoundaryTest",'
    )
    oid = git("hash-object", "-w", "--stdin", data=content).decode().strip()
    git("update-index", "--add", "--cacheinfo", f"100644,{oid},{lake}")
    for increment in increments:
        data = increment.read_bytes()
        git("apply", "--cached", "--check", "-", data=data)
        git("apply", "--cached", "-", data=data)
        inputs.append({"name": increment.name, "bytes": len(data), "sha256": sha(data)})
    full = tree()
    paths = git("diff", "--name-only", base, full).decode().splitlines()
    api = ["leanncd/LeanNCD/DSL/Ast.lean", "leanncd/LeanNCD/Exec/Uid.lean"]
    tests = ["leanncd/test/Eval/Plan/B5NativeTest.lean",
             "leanncd/test/Eval/Plan/B5BoundaryTest.lean", lake]
    tests.extend(p for p in paths if p.startswith("leanncd/experiments/jax_bridge/")
                 and p.endswith(".lean"))
    oracle = [
        "leanncd/LeanNCD/Semantics/Source/Differential.lean",
        "leanncd/LeanNCD/Semantics/Source/NumericalProfile.lean",
        "leanncd/test/Semantics/OracleMixedRefusalTest.lean",
        "leanncd/test/Semantics/OracleSortRules.lean",
        "leanncd/test/Semantics/OracleSortRulesTest.lean",
        "leanncd/test/Semantics/SourceDifferentialScatterTest.lean",
    ]
    production = [p for p in paths if p not in api + tests + oracle]
    groups = [
        ("T1", "T1-api.patch", api),
        ("T2a", "T2a-native-activation.patch", production),
        ("T2b", "T2b-independent-oracle.patch", oracle),
        ("T3", "T3-native-boundary-tests.patch", tests),
    ]
    assert sorted(p for _, _, ps in groups for p in ps) == sorted(paths)
    git("read-tree", base)
    previous = git("rev-parse", f"{base}^{{tree}}").decode().strip()
    stages = []
    for task, name, selected in groups:
        for path in selected:
            row = git("ls-tree", full, "--", path).decode().strip()
            mode, _, tail = row.split(" ", 2)
            oid, actual = tail.split("\t")
            assert actual == path
            git("update-index", "--add", "--cacheinfo", f"{mode},{oid},{path}")
        current = tree()
        patch = git("diff", "--binary", "--full-index", previous, current, "--")
        (HERE / name).write_bytes(patch)
        stages.append({"task": task, "patch": name, "paths": selected,
                       "sha256": sha(patch), "bytes": len(patch), "tree": current})
        previous = current
    assert previous == full
    meta = {"base": base, "inputs": inputs, "final_tree": full, "stages": stages,
            "files": file_rows(full, paths)}
    (HERE / "snapshots.json").write_text(json.dumps(meta, indent=2) + "\n")
    verify()


try:
    if len(sys.argv) == 2 and sys.argv[1] == "--verify":
        verify()
    elif len(sys.argv) >= 3 and sys.argv[1] == "--generate":
        generate(Path(sys.argv[2]).resolve(),
                 [Path(p).resolve() for p in sys.argv[3:]])
    else:
        sys.exit("usage: assemble.py --generate <evidence-dir> [increment.patch ...] | --verify")
finally:
    INDEX.unlink(missing_ok=True)
    INDEX.with_name(INDEX.name + ".lock").unlink(missing_ok=True)
