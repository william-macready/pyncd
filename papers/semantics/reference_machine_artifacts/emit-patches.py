"""Reproduce compiled task patches and verify exact sequential temporary-index replay."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
BASE = "53bcbbd610a1791a5a769a40e33fd47b5a3abc7e"
TASKS = [
    ("01-machine", "82eba635c9c25f39e0f94358b9d8d8893070ad62",
     ["leanncd/LeanNCD/Semantics/Machine.lean"]),
    ("02-invariants-soundness", "e70aa2d9dfb8d723a0cabdae38dab2ac2aaa5240",
     ["leanncd/LeanNCD/Semantics/Invariants.lean", "leanncd/LeanNCD/Semantics/Soundness.lean"]),
    ("03-fixtures-integration", "1c99cf0fad676268961e6ba201d15fa718adc1bd",
     ["leanncd/test/Semantics/ReferenceMachineTest.lean", "leanncd/LeanNCD/Semantics.lean",
      "leanncd/lakefile.toml", "leanncd/LeanNCD/Semantics/AGENTS.md", "leanncd/AGENTS.md"]),
]
TREE = "f5ae8635700b025128567bc7c72eff32deedce6e"
PROTECTED = [
    "leanncd/LeanNCD/Semantics/Types.lean",
    "leanncd/LeanNCD/Semantics/Expr.lean",
    "leanncd/LeanNCD/Semantics/Interpret.lean",
    "leanncd/LeanNCD/Semantics/Readiness.lean",
    "leanncd/LeanNCD/Semantics/Completeness.lean",
    "leanncd/LeanNCD/Semantics/Collection.lean",
    "leanncd/LeanNCD/Semantics/Program.lean",
    "leanncd/LeanNCD/Semantics/Models.lean",
    "leanncd/test/Semantics/ExpressionTest.lean",
    "leanncd/test/Semantics/CollectionModelTest.lean",
    "papers/semantics/tensor_logic_semantics.md",
    "leanncd/scripts/lake-build.sh",
    "leanncd/scripts/lean-file.sh",
    "leanncd/scripts/mutation-manifest.sh",
    "leanncd/scripts/mutation-cycle.sh",
    ".claude/skills/new-slice/prepare-worktree.sh",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=ROOT,
                        help="checkout sharing the compiled task commit objects")
    parser.add_argument("--observations", type=Path,
                        help="directory containing the original raw build/mutation logs")
    args = parser.parse_args()
    command = ["/usr/bin/git", "-C", str(args.repo.resolve())]

    def git(*arguments, env=None):
        return subprocess.check_output(command + list(arguments), env=env)

    patches = ROOT / "papers/semantics/reference_machine_patches"
    patches.mkdir(exist_ok=True)
    before = BASE
    patch_hashes = {}
    for name, after, files in TASKS:
        parent = git("rev-parse", after + "^").decode().strip()
        if parent != before:
            raise RuntimeError(f"{name}: parent {parent} != {before}")
        patch = git("diff", "--full-index", "--binary", before, after, "--", *files)
        if not patch:
            raise RuntimeError(f"{name}: empty patch")
        (patches / (name + ".patch")).write_bytes(patch)
        patch_hashes[name] = hashlib.sha256(patch).hexdigest()
        before = after
    with tempfile.TemporaryDirectory(prefix="reference-machine-index-") as tmp:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(tmp) / "index"))
        git("read-tree", BASE, env=env)
        for name, _, _ in TASKS:
            path = str(patches / (name + ".patch"))
            git("apply", "--cached", "--check", path, env=env)
            git("apply", "--cached", path, env=env)
            print(f"{name}: sequential apply --check PASS")
        actual = git("write-tree", env=env).decode().strip()
        if actual != TREE or git("rev-parse", before + "^{tree}").decode().strip() != TREE:
            raise RuntimeError(f"replay tree {actual} != candidate {TREE}")
        print(f"exact candidate tree replay PASS: {actual}")
    protected_hashes = {}
    for path in PROTECTED:
        base = git("show", BASE + ":" + path)
        if base != git("show", before + ":" + path):
            raise RuntimeError(f"protected source changed: {path}")
        protected_hashes[path] = hashlib.sha256(base).hexdigest()
    print(f"protected input equality PASS: {len(PROTECTED)} files")
    fixture = git("show", before + ":leanncd/test/Semantics/ReferenceMachineTest.lean").decode()
    count = len(re.findall(r"^theorem ", fixture, re.MULTILINE))
    if count != 33:
        raise RuntimeError(f"fixture assertion count changed: {count}")
    audit = {
        "baseline": BASE, "candidate_tree": TREE, "patch_sha256": patch_hashes,
        "protected_input_sha256": protected_hashes, "fixture_theorem_count": count,
    }
    if args.observations:
        log = (args.observations / "reference-machine-mutations.log").read_text()
        manifest = json.loads((ROOT / "papers/semantics/reference_machine_mutations_post.json").read_text())
        for entry in manifest:
            label = entry["label"]
            cycle = log.split(f"=== {label} MUTATE ===\n", 1)[1].split(
                f"=== {label} MANIFEST VERDICT: PASS ===", 1)[0]
            mutated = cycle.split(f"=== {label} MUTATE exit=1 ===", 1)[0]
            if not all(text in mutated for text in entry["expect"]):
                raise RuntimeError(f"observed diagnostic does not match {label}")
            if "mutation_exit=1 restore_hash_exit=0 restored_build_exit=0" not in cycle:
                raise RuntimeError(f"missing byte-identical restored green verdict: {label}")
        full = (args.observations / "reference-machine-full-build.log").read_text()
        if "Build completed successfully (8694 jobs)." not in full:
            raise RuntimeError("full default build success not observed")
        audit["mutation_diagnostics_matched"] = len(manifest)
        audit["full_default_build_jobs"] = 8694
        print(f"observed failure diagnostics and byte-identical restores PASS: {len(manifest)}")
    (ROOT / "papers/semantics/reference_machine_artifacts/replay-audit.json").write_text(
        json.dumps(audit, indent=2) + "\n")


if __name__ == "__main__":
    main()
