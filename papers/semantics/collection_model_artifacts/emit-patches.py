"""Emit full-index task patches from compiled commits and replay in a temporary index."""
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
GIT = ["/usr/bin/git", "-C", str(ROOT)]
BASE = "26fcfe6b8b209b8bd05b871705f6b731b1caba0a"
TASK1 = "067a26416040ca0050a12c1a0405ed029a85ef8b"
TASK2 = "53034be98e6af24fda8e26699386784e317a8f04"
TASK3 = "8c377721298a18d57906f1412fa9703efbd0b4a8"
PATCHES = ROOT / "papers/semantics/collection_model_patches"


def git(*args, env=None):
    return subprocess.check_output(GIT + list(args), env=env)


def main():
    PATCHES.mkdir(exist_ok=True)
    tasks = [
        ("01-finite-pushforward.patch", BASE, TASK1,
         ["leanncd/LeanNCD/Semantics/Collection.lean"]),
        ("02-program-models.patch", TASK1, TASK2,
         ["leanncd/LeanNCD/Semantics/Program.lean", "leanncd/LeanNCD/Semantics/Models.lean"]),
        ("03-fixtures-integration.patch", TASK2, TASK3,
         ["leanncd/test/Semantics/CollectionModelTest.lean", "leanncd/LeanNCD/Semantics.lean",
          "leanncd/lakefile.toml", "leanncd/LeanNCD/Semantics/AGENTS.md",
          "leanncd/AGENTS.md", "papers/semantics/tensor_logic_semantics.md"]),
    ]
    for name, before, after, files in tasks:
        patch = git("diff", "--full-index", "--binary", before, after, "--", *files)
        if not patch:
            raise RuntimeError(f"empty task patch: {name}")
        (PATCHES / name).write_bytes(patch)
    with tempfile.TemporaryDirectory(prefix="collection-model-index-") as tmp:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(tmp) / "index"))
        git("read-tree", BASE, env=env)
        for name, *_ in tasks:
            path = str(PATCHES / name)
            git("apply", "--cached", "--check", path, env=env)
            git("apply", "--cached", path, env=env)
            print(f"{name}: sequential apply --check PASS")
        actual = git("write-tree", env=env).strip()
        expected = git("rev-parse", f"{TASK3}^{{tree}}").strip()
        if actual != expected:
            raise RuntimeError(f"replayed tree {actual!r} differs from candidate {expected!r}")
        print(f"exact candidate tree replay PASS: {actual.decode()}")


if __name__ == "__main__":
    main()
