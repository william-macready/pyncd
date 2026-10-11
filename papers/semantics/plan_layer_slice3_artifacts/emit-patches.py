"""Emit Plan-layer slice 3 (buffer retirement) per-task patches and verify exact sequential replay.

Mechanical: each patch is `git diff BASE CODE_HEAD -- <path set>` (no retyping, no intermediate-state
surgery: the four path sets are disjoint, so applying 01..04 in order reproduces CODE_HEAD for every
non-papers path). Run from anywhere:

  python3 emit-patches.py --proto <prototype worktree> --repo <scratch DETACHED worktree at BASE>

Steps: (1) emit the four patches + manifest.json; (2) replay 1: temporary index, `git apply --cached
--check` then `--cached` per patch; the resulting leanncd tree must equal CODE_HEAD's; (3) replay 2: in
the scratch worktree at BASE, `git apply --check` then `git apply` per patch, `git add -A leanncd`,
`git diff --cached --stat CODE_HEAD -- leanncd` must be empty; (4) write artifacts/evidence.json.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

BASE = "69214c64"
CODE_HEAD = "e452e970"  # last production/test commit of the prototype; later commits are papers/ only
P = "leanncd/LeanNCD/Semantics/Plan/"
T = "leanncd/test/Semantics/"
TASKS = [
    ("01-core", [P + f + ".lean" for f in ("Syntax", "Memory", "Step", "Simulation")],
     "LeanNCD.Semantics.Plan.Simulation"),
    ("02-validity-run-correctness", [P + f + ".lean" for f in ("Validity", "Run", "Correctness")],
     "LeanNCD.Semantics.Plan.Correctness"),
    ("03-fusion", [P + "Fusion.lean", P + "FusionCorrectness.lean"],
     "LeanNCD.Semantics.Plan.FusionCorrectness, then full LeanNCD"),
    ("04-fixtures", [T + "PlanRetireTest.lean", "leanncd/lakefile.toml"],
     "default targets (lake build with no argument)"),
]
MUTATIONS = "papers/semantics/plan_layer_slice3_mutations_post.json"
RESULTS = "papers/semantics/plan_layer_slice3_mutation_results.md"
# Observed values quoted from the A1..A3a notes (each was a real `lake-build.sh` run, last line of the log).
BUILD_JOBS = {
    "LeanNCD.Semantics.Plan.Simulation": 2963,
    "LeanNCD.Semantics.Plan.Validity": 2964,
    "LeanNCD.Semantics.Plan.Run": 2965,
    "LeanNCD.Semantics.Plan.Correctness": 2966,
    "LeanNCD.Semantics.Plan.Fusion": 2966,
    "LeanNCD.Semantics.Plan.FusionCorrectness": 2968,
    "LeanNCD.Semantics.Plan.Faults": 2969,
    "LeanNCD": 8598,
    "Semantics.PlanRetireTest": 2982,
    "default targets": 8793,
}
FIXTURES = {"plans": 10, "check_rows": 17, "decide_examples": 10, "theorems": 1,
            "source": "papers/semantics/plan_layer_slice3_artifacts/a3a_notes.md"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--proto", required=True)
    ap.add_argument("--repo", required=True)
    a = ap.parse_args()
    proto, repo = Path(a.proto), Path(a.repo)
    artifacts = proto / "papers/semantics/plan_layer_slice3_artifacts"
    patches = proto / "papers/semantics/plan_layer_slice3_patches"
    patches.mkdir(exist_ok=True)

    def git(*args, cwd=proto, env=None, check=True):
        r = subprocess.run(["git", "-C", str(cwd), *args], capture_output=True, env=env)
        if check and r.returncode != 0:
            raise SystemExit(f"git {' '.join(args)} failed: {r.stderr.decode()}")
        return r.stdout

    base_full = git("rev-parse", BASE).decode().strip()
    code_full = git("rev-parse", CODE_HEAD).decode().strip()
    head = git("rev-parse", "HEAD").decode().strip()
    assert git("diff", "--name-only", code_full, "HEAD", "--", "leanncd").decode() == "", \
        "HEAD differs from CODE_HEAD under leanncd"
    shipped = [f for _, fs, _ in TASKS for f in fs]
    changed = {f for f in git("diff", "--name-only", base_full, code_full).decode().splitlines()
               if not f.startswith(("papers/", "docs/"))}
    assert changed == set(shipped), sorted(changed ^ set(shipped))

    tasks = []
    for name, files, gate in TASKS:
        patch = git("diff", "--no-color", "--no-ext-diff", base_full, code_full, "--", *files)
        pf = patches / f"{name}.patch"
        pf.write_bytes(patch)
        stat = git("diff", "--numstat", base_full, code_full, "--", *files).decode().splitlines()
        tasks.append({
            "task": name, "files": files, "gate": gate,
            "patch": f"papers/semantics/plan_layer_slice3_patches/{name}.patch",
            "patch_lines": patch.decode().count("\n"),
            "sha256": hashlib.sha256(patch).hexdigest(),
            "git_patch_id": subprocess.run(["git", "-C", str(proto), "patch-id", "--stable"], input=patch,
                                           capture_output=True).stdout.decode().split()[0],
            "blobs_at_code_head": {f: git("rev-parse", f"{code_full}:{f}").decode().strip() for f in files},
            "numstat": [dict(zip(("added", "deleted", "path"), l.split("\t"))) for l in stat],
        })
    (patches / "manifest.json").write_text(json.dumps(tasks, indent=2) + "\n")

    # Replay 1: temporary index.
    with tempfile.TemporaryDirectory(prefix="plan3-replay-") as d:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(d) / "index"))
        git("read-tree", base_full, env=env)
        for t in tasks:
            pfull = str(proto / t["patch"])
            git("apply", "--cached", "--check", pfull, env=env)
            git("apply", "--cached", pfull, env=env)
        tree = git("write-tree", env=env).decode().strip()
    assert git("rev-parse", f"{tree}:leanncd").decode() == git("rev-parse", f"{code_full}:leanncd").decode(), \
        "replayed leanncd tree != CODE_HEAD leanncd tree"

    # Replay 2: scratch worktree at BASE.
    git("checkout", "--detach", base_full, cwd=repo)
    assert not git("status", "--porcelain", "--untracked-files=no", cwd=repo).strip()
    for t in tasks:
        pfull = str(proto / t["patch"])
        git("apply", "--check", pfull, cwd=repo)
        git("apply", pfull, cwd=repo)
    git("add", "-A", "leanncd", cwd=repo)
    diff_stat = git("diff", "--cached", "--stat", code_full, "--", "leanncd", cwd=repo).decode()
    assert diff_stat == "", diff_stat
    git("reset", "-q", "--hard", "HEAD", cwd=repo)

    # Mutation manifest summary (from the committed results table, if present).
    results = proto / RESULTS
    muts = None
    if results.exists():
        rows = re.findall(r"^\| (S3-M\d+[^|]*)\|([^|]*)\|([^|]*)\|([^|]*)\|([^|]*)\|$",
                          results.read_text(), re.M)
        muts = [{"label": r[0].strip(), "cycle": r[1].strip(), "restored": r[2].strip(),
                 "expect_seen": r[3].strip(), "result": r[4].strip()} for r in rows]
    evidence = {
        "base": base_full, "prototype_code_head": code_full, "prototype_head_at_emit": head,
        "build_jobs": BUILD_JOBS, "fixtures": FIXTURES,
        "patches": [{k: t[k] for k in ("task", "gate", "patch", "patch_lines", "sha256", "git_patch_id", "numstat")}
                    for t in tasks],
        "overall_numstat_non_papers": git("diff", "--shortstat", base_full, code_full).decode().strip(),
        "replay": "PASS: (1) temporary-index git apply --cached per patch, leanncd tree equals CODE_HEAD's; "
                  "(2) scratch worktree at BASE, git apply --check then git apply in order, "
                  "`git diff --cached --stat CODE_HEAD -- leanncd` empty",
        "mutation_manifest": MUTATIONS, "mutation_results_file": RESULTS, "mutation_rows": muts,
    }
    (artifacts / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(json.dumps({"replay": "PASS", "scratch_diff_cached_stat_vs_code_head_leanncd": diff_stat,
                      "applied_in_order": [t["task"] for t in tasks],
                      "replayed_leanncd_tree": tree,"patch_lines": {t["task"]: t["patch_lines"] for t in tasks}}, indent=1))


if __name__ == "__main__":
    main()
