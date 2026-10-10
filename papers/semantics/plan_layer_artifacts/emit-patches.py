"""Emit Plan-layer slice 1 per-task patches; verify exact sequential replay and evidence.

--repo is the scratch worktree whose last five first-parent commits are the task
commits `plan(slice1): T<N> <name>` stacked on BASE. --proto is the prototype
worktree; its commit PROTO is the verified code state every patch must replay to.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

BASE = "0bf02e47ced1b380ab3249aefe5a62dbab877329"
PROTO = "3625b2fe309b15fc0000f228071fd607250fa8b4"
P = "leanncd/LeanNCD/Semantics/Plan/"
T = "leanncd/test/Semantics/"
TASKS = [
    ("01-syntax-batch", [P + "Syntax.lean", P + "Batch.lean"],
     ["LeanNCD.Semantics.Plan.Syntax", "LeanNCD.Semantics.Plan.Batch"]),
    ("02-memory", [P + "Memory.lean"], ["LeanNCD.Semantics.Plan.Memory"]),
    ("03-step-simulation", [P + "Step.lean", P + "Simulation.lean"],
     ["LeanNCD.Semantics.Plan.Step", "LeanNCD.Semantics.Plan.Simulation"]),
    ("04-validity-run-correctness",
     [P + "Validity.lean", P + "Run.lean", P + "Correctness.lean"],
     ["LeanNCD.Semantics.Plan.Validity", "LeanNCD.Semantics.Plan.Run",
      "LeanNCD.Semantics.Plan.Correctness"]),
    ("05-aggregator-fixtures",
     ["leanncd/LeanNCD/Semantics/Plan.lean", "leanncd/LeanNCD/Semantics.lean",
      "leanncd/lakefile.toml"]
     + [T + n + ".lean" for n in ["PlanBatchTest", "PlanCorrectnessTest", "PlanFixtures",
                                  "PlanMemoryTest", "PlanRunTest", "PlanSimulationTest",
                                  "PlanStepTest", "PlanValidityTest"]],
     ["<default targets>"]),
]
# Build logs per task (in --logs). T1's build ran before logging was set up; its
# result was observed on the console and is recorded here, not re-derived.
LOGS = {1: None, 2: "t2.log", 3: "t3.log", 4: "t4.log", 5: "t5.log"}
T1_OBSERVED_JOBS = 2960
SYMBOL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?"
                    r"(?:def|abbrev|theorem|lemma|inductive|structure|instance) (\S+)", re.M)
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--proto", type=Path, required=True)
    parser.add_argument("--logs", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    artifacts = Path(__file__).resolve().parent
    patches = artifacts.parent / "plan_layer_patches"
    patches.mkdir(exist_ok=True)

    def git(*argv, env=None, cwd=repo):
        return subprocess.check_output(["/usr/bin/git", "-C", str(cwd)] + list(argv), env=env)

    def proto_git(*argv):
        return git(*argv, cwd=args.proto.resolve())

    head = git("rev-parse", "HEAD").decode().strip()
    chain = git("rev-list", "--first-parent", "--max-count=%d" % len(TASKS), head).decode().split()
    chain.reverse()
    assert not git("status", "--porcelain", "--untracked-files=no").strip()
    assert proto_git("rev-parse", PROTO).decode().strip() == PROTO

    before = BASE
    tasks = []
    for n, ((name, files, targets), commit) in enumerate(zip(TASKS, chain), start=1):
        subject = git("log", "-1", "--format=%s", commit).decode().strip()
        assert subject == "plan(slice1): T%d %s" % (n, name), (n, subject)
        assert git("rev-parse", commit + "^").decode().strip() == before, name
        actual = git("diff", "--name-only", before, commit).decode().splitlines()
        assert sorted(actual) == sorted(files), (name, actual)
        patch = git("diff", "--binary", "--full-index", before, commit, "--", *files)
        path = patches / (name + ".patch")
        path.write_bytes(patch)
        if LOGS[n] is None:
            build = {"targets": targets, "result": "Build completed successfully",
                     "jobs": T1_OBSERVED_JOBS, "log": None,
                     "source": "console output observed during emission; not logged"}
        else:
            raw = (args.logs / LOGS[n]).read_bytes()
            text = raw.decode()
            jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", text)
            assert len(jobs) == 1 and not re.search(r"(?m)^error", text), (name, jobs)
            build = {"targets": targets, "result": "Build completed successfully",
                     "jobs": int(jobs[0]), "log": str((args.logs / LOGS[n]).resolve()),
                     "log_sha256": digest(raw),
                     "warnings": len(re.findall(r"(?m)^warning:", text))}
        tasks.append({
            "task": "T%d" % n, "name": name, "commit": commit, "parent": before,
            "tree": git("rev-parse", commit + "^{tree}").decode().strip(),
            "files": files, "patch": str(path.relative_to(artifacts.parent.parent.parent)),
            "patch_lines": patch.count(b"\n"), "sha256": digest(patch), "build": build,
            "symbols": {f: SYMBOL.findall(git("show", commit + ":" + f).decode())
                        for f in files if f.endswith(".lean")},
        })
        before = commit
    assert before == head, (before, head)

    shipped = [f for _, files, _ in TASKS for f in files]
    with tempfile.TemporaryDirectory(prefix="plan-replay-") as directory:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(directory) / "index"))
        git("read-tree", BASE, env=env)
        for task in tasks:
            patch = str(artifacts.parent.parent.parent / task["patch"])
            git("apply", "--cached", "--check", patch, env=env)
            git("apply", "--cached", patch, env=env)
            replayed = git("write-tree", env=env).decode().strip()
            assert replayed == task["tree"], task["task"]
    # Final replayed tree must equal the prototype's code state on every shipped path.
    # The prototype object store is shared (same repository), so diff directly.
    subprocess.check_call(["/usr/bin/git", "-C", str(repo), "diff", "--quiet",
                           replayed, PROTO, "--"] + shipped)
    # Everything else outside the notes directory must equal BASE in the prototype too.
    outside = proto_git("diff", "--name-only", BASE, PROTO).decode().splitlines()
    extra = sorted(set(outside) - set(shipped))
    assert all(f.startswith("papers/semantics/plan_layer_artifacts/") for f in extra), extra

    hits = []
    for f in shipped:
        if f.endswith(".lean"):
            for i, line in enumerate(git("show", head + ":" + f).decode().splitlines(), 1):
                if FORBIDDEN.search(line):
                    hits.append("%s:%d:%s" % (f, i, line))
    assert not hits, hits

    manifest = [{k: t[k] for k in ("task", "name", "commit", "parent", "files", "patch",
                                   "sha256", "symbols")} for t in tasks]
    (patches / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    evidence = {
        "base": BASE, "prototype_code_head": PROTO, "scratch_head": head,
        "scratch_tree": git("rev-parse", head + "^{tree}").decode().strip(),
        "tasks": [{k: t[k] for k in ("task", "name", "commit", "parent", "tree",
                                     "patch", "patch_lines", "sha256", "build")}
                  for t in tasks],
        "replay": "PASS: temporary-index git apply --cached of each patch onto BASE yields "
                  "each task commit's tree; final tree equals PROTO on all %d shipped paths"
                  % len(shipped),
        "excluded_from_patches": extra,
        "forbidden_token_grep": {"pattern": FORBIDDEN.pattern, "files": len(
            [f for f in shipped if f.endswith(".lean")]), "hits": hits},
        "boundary_moves": [],
        "source_edits": "none: every file is byte-copied from PROTO via git checkout",
    }
    (artifacts / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(json.dumps({"head": head, "replay": "PASS", "grep_hits": len(hits),
                      "patch_lines": {t["name"]: t["patch_lines"] for t in tasks}}, indent=2))


if __name__ == "__main__":
    main()
