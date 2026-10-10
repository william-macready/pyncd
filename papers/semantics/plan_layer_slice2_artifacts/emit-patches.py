"""Emit Plan-layer slice 2 (fusion) per-task patches; verify exact sequential replay.

Mechanical: every task state takes whole files from PROTO, except four files whose
intermediate states are derived here by text surgery (Fusion.lean split at SPLIT_MARKER,
Run.lean minus execAnns_not_stuck for T1, lakefile.toml test list, Plan.lean imports).
The final state of every file equals PROTO byte for byte (asserted).

Subcommands (all take --repo <scratch worktree> --proto <prototype worktree>):
  commit   stack one commit per task on BASE in --repo (detached)
  build    check out each task commit in turn and build its target(s); log to --logs
  finish   emit patches, replay them on a fresh BASE checkout, run the unfiltered mutation
           manifest --check on the replayed tree, write manifest.json and evidence.json
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import os

BASE = "4570a794"
PROTO = "b554437f"
P = "leanncd/LeanNCD/Semantics/Plan/"
T = "leanncd/test/Semantics/"
SPLIT_MARKER = "/-! ### Run bridge (T3): a fused run and the run of its expansion agree -/"
FUSION = P + "Fusion.lean"
RUN = P + "Run.lean"
LAKEFILE = "leanncd/lakefile.toml"
PLANLEAN = "leanncd/LeanNCD/Semantics/Plan.lean"
MANIFEST_JSON = "papers/semantics/plan_layer_slice2_mutations_post.json"
END_NS = "end LeanNCD.Semantics.Program.Plan\n"

TASKS = [
    ("01-expand-step",
     [P + "Syntax.lean", P + "Step.lean", P + "Simulation.lean", RUN,
      T + "PlanStepTest.lean", T + "PlanValidityTest.lean"],
     "slice-1 Plan test targets"),
    ("02-fold-lemmas",
     [FUSION, RUN, PLANLEAN, T + "PlanFusionTest.lean", LAKEFILE],
     "Semantics.PlanFusionTest"),
    ("03-fused-run-theorems",
     [FUSION, P + "FusionCorrectness.lean", PLANLEAN, T + "PlanFusionCorrectnessTest.lean",
      LAKEFILE],
     "LeanNCD + Semantics.PlanFusionCorrectnessTest"),
    ("04-checker-fixtures", [T + "PlanFusionCheckerTest.lean", LAKEFILE],
     "Semantics.PlanFusionCheckerTest"),
]
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")
SYMBOL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?"
                    r"(?:def|abbrev|theorem|lemma|inductive|structure|instance) (\S+)", re.M)

LAKE_FULL = ('"Semantics.PlanFusionTest", "Semantics.PlanFusionCorrectnessTest",\n'
             '         "Semantics.PlanFusionCheckerTest",         "Semantics.SourceBindingUIDTest"')
LAKE_STAGE = {
    2: '"Semantics.PlanFusionTest",\n         "Semantics.SourceBindingUIDTest"',
    3: '"Semantics.PlanFusionTest", "Semantics.PlanFusionCorrectnessTest",\n'
       '         "Semantics.SourceBindingUIDTest"',
    4: LAKE_FULL,
}
RUN_BLOCK_START = "/-- **Progress for a run of annotations.**"
RUN_BLOCK_END = "/-! ### The multi-step run lemma -/"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("cmd", choices=["commit", "build", "finish"])
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--proto", type=Path, required=True)
    ap.add_argument("--logs", type=Path, required=True)
    args = ap.parse_args()
    repo = args.repo.resolve()
    proto = args.proto.resolve()
    artifacts = Path(__file__).resolve().parent
    patches = artifacts.parent / "plan_layer_slice2_patches"

    def git(*argv, env=None, cwd=repo, check=True):
        r = subprocess.run(["/usr/bin/git", "-C", str(cwd)] + list(argv), env=env,
                           capture_output=True)
        if check and r.returncode:
            raise SystemExit("git %s failed: %s" % (argv, r.stderr.decode()))
        return r.stdout

    base_full = git("rev-parse", BASE).decode().strip()
    proto_full = git("rev-parse", PROTO).decode().strip()

    def proto_file(path):
        return git("show", proto_full + ":" + path)

    def content(n, path):
        """Bytes of `path` in the state after task n (1-based)."""
        data = proto_file(path)
        if path == FUSION:
            text = data.decode()
            i = text.index(SPLIT_MARKER)
            assert text.count(SPLIT_MARKER) == 1
            if n == 2:
                return (text[:i].rstrip("\n") + "\n\n" + END_NS).encode()
        elif path == RUN and n == 1:
            text = data.decode()
            a, b = text.index(RUN_BLOCK_START), text.index(RUN_BLOCK_END)
            assert text.count(RUN_BLOCK_START) == 1 and a < b
            return (text[:a] + text[b:]).encode()
        elif path == LAKEFILE and n in LAKE_STAGE:
            text = data.decode()
            assert text.count(LAKE_FULL) == 1
            return text.replace(LAKE_FULL, LAKE_STAGE[n]).encode()
        elif path == PLANLEAN and n == 2:
            text = data.decode()
            tail = "import LeanNCD.Semantics.Plan.FusionCorrectness\n"
            assert text.endswith(tail)
            return text[:-len(tail)].encode()
        return data

    def commits():
        head = git("rev-parse", "HEAD").decode().strip()
        chain = git("rev-list", "--first-parent", "--max-count=%d" % len(TASKS),
                    head).decode().split()
        chain.reverse()
        return head, chain

    def targets_of(n):
        if n == 1:
            lake = git("show", base_full + ":" + LAKEFILE).decode()
            return sorted(set(re.findall(r'"(Semantics\.Plan[A-Za-z]*)"', lake)),
                          key=lake.index)
        return {2: ["Semantics.PlanFusionTest"],
                3: ["LeanNCD", "Semantics.PlanFusionCorrectnessTest"],
                4: ["Semantics.PlanFusionCheckerTest"]}[n]

    if args.cmd == "commit":
        git("checkout", "--detach", base_full)
        assert not git("status", "--porcelain", "--untracked-files=no").strip()
        for n, (name, files, _) in enumerate(TASKS, start=1):
            for f in files:
                (repo / f).write_bytes(content(n, f))
            git("add", "--", *files)
            git("commit", "-q", "-m", "plan(slice2): T%d %s\n\nCo-Authored-By: Claude Sonnet 5.5 "
                "<noreply@anthropic.com>" % (n, name))
            actual = git("diff", "--name-only", "HEAD^", "HEAD").decode().splitlines()
            assert sorted(actual) == sorted(files), (name, actual)
            print("committed", n, name)
        return

    head, chain = commits()
    if args.cmd == "build":
        args.logs.mkdir(parents=True, exist_ok=True)
        for n, commit in enumerate(chain, start=1):
            git("checkout", "--detach", commit)
            log = args.logs / ("t%d.log" % n)
            with open(log, "wb") as fh:
                rc = subprocess.call(
                    ["bash", str(repo / "leanncd/scripts/lake-build.sh"), str(repo / "leanncd")]
                    + targets_of(n), stdout=fh, stderr=subprocess.STDOUT)
            print("T%d" % n, "rc", rc, flush=True)
            if rc:
                raise SystemExit("T%d build failed; see %s" % (n, log))
        return

    # ---- finish
    assert head == chain[-1]
    assert not git("status", "--porcelain", "--untracked-files=no").strip()
    assert git("rev-parse", chain[0] + "^").decode().strip() == base_full
    patches.mkdir(exist_ok=True)
    shipped = sorted({f for _, files, _ in TASKS for f in files})
    before = base_full
    tasks = []
    for n, ((name, files, bt), commit) in enumerate(zip(TASKS, chain), start=1):
        assert git("rev-parse", commit + "^").decode().strip() == before
        for f in files:
            assert git("show", commit + ":" + f) == content(n, f), (n, f)
        patch = git("diff", "--binary", "--full-index", before, commit, "--", *files)
        path = patches / (name + ".patch")
        path.write_bytes(patch)
        log = args.logs / ("t%d.log" % n)
        text = log.read_bytes().decode()
        jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", text)
        assert len(jobs) == 1 and not re.search(r"(?m)^error", text), (name, jobs)
        stat = git("diff", "--numstat", before, commit).decode().split("\n")
        tasks.append({
            "task": "T%d" % n, "name": name, "commit": commit, "parent": before,
            "tree": git("rev-parse", commit + "^{tree}").decode().strip(),
            "files": files, "line_counts": {s.split("\t")[2]: {"added": int(s.split("\t")[0]),
                                                                "deleted": int(s.split("\t")[1])}
                                              for s in stat if s},
            "patch": str(path.relative_to(artifacts.parent.parent.parent)),
            "patch_lines": patch.count(b"\n"), "sha256": digest(patch),
            "build": {"target": bt, "lake_targets": targets_of(n),
                      "result": "Build completed successfully", "jobs": int(jobs[0]),
                      "warnings": len(re.findall(r"(?m)^warning:", text)),
                      "log": str(log.resolve()), "log_sha256": digest(log.read_bytes())},
            "symbols": {f: SYMBOL.findall(git("show", commit + ":" + f).decode())
                        for f in files if f.endswith(".lean")},
        })
        before = commit

    # Replay 1: temporary index (as slice 1).
    with tempfile.TemporaryDirectory(prefix="plan2-replay-") as d:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(d) / "index"))
        git("read-tree", base_full, env=env)
        for t in tasks:
            pf = str(artifacts.parent.parent.parent / t["patch"])
            git("apply", "--cached", "--check", pf, env=env)
            git("apply", "--cached", pf, env=env)
            assert git("write-tree", env=env).decode().strip() == t["tree"], t["task"]

    # Replay 2: fresh BASE checkout of the scratch worktree, git apply --check then apply.
    git("checkout", "--detach", base_full)
    assert not git("status", "--porcelain", "--untracked-files=no").strip()
    for t in tasks:
        pf = str(artifacts.parent.parent.parent / t["patch"])
        git("apply", "--check", pf)
        git("apply", pf)
    git("add", "-A", "leanncd")
    diff_stat = git("diff", "--cached", "--stat", proto_full, "--", "leanncd").decode()
    assert diff_stat == "", diff_stat
    outside = git("diff", "--name-only", base_full, proto_full, cwd=proto).decode().splitlines()
    extra = sorted(set(outside) - set(shipped))
    assert all(f.startswith("papers/semantics/") for f in extra), extra

    # Unfiltered mutation-manifest --check on the replayed tree.
    mm = subprocess.run(
        ["bash", str(repo / "leanncd/scripts/mutation-manifest.sh"), "--check",
         str(repo / "leanncd"), str(proto / MANIFEST_JSON)], capture_output=True, text=True)
    mm_out = (mm.stdout + mm.stderr)
    git("reset", "-q", "--hard", "HEAD")

    # Manifest-entry vs task-tag audit: earliest task state holding `old` (exactly once) and
    # earliest task that has each built target.
    entries = json.loads((proto / MANIFEST_JSON).read_text())
    paths_at = {n: set(git("ls-tree", "-r", "--name-only", base_full).decode().splitlines())
                | {f for m in range(1, n + 1) for f in TASKS[m - 1][1]} for n in range(1, 5)}

    def target_path(tg):
        if tg.startswith("LeanNCD."):
            return "leanncd/" + tg.replace(".", "/") + ".lean"
        return T + tg.split(".", 1)[1] + ".lean" if tg.startswith("Semantics.") else None

    audit = []
    for e in entries:
        full = "leanncd/" + e["file"]
        # earliest task state whose version of the file contains `old` exactly once
        intro = next((n for n in range(1, 5) if git("show", chain[n - 1] + ":" + full,
                      check=False).decode().count(e["old"]) == 1), None)
        tgt_intro = {}
        for tg in e["targets"]:
            tp = target_path(tg)
            tgt_intro[tg] = next((n for n in range(1, 5) if tp is None or tp in paths_at[n]), None)
        tag = int(e["task"][1:])
        audit.append({"label": e["label"], "tag": e["task"], "file": e["file"],
                      "old_first_present_in": "T%s" % intro,
                      "targets_first_present_in": {k: "T%s" % v for k, v in tgt_intro.items()},
                      "tag_before_code": intro is None or tag < intro,
                      "tag_before_target": any(v is None or tag < v for v in tgt_intro.values())})

    hits = [f for f in shipped if f.endswith(".lean") and FORBIDDEN.search(proto_file(f).decode())]
    manifest = [{k: t[k] for k in ("task", "name", "commit", "parent", "files", "line_counts",
                                   "patch", "patch_lines", "sha256", "symbols")}
                | {"build_target": t["build"]["target"]} for t in tasks]
    (patches / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    evidence = {
        "base": base_full, "prototype_code_head": proto_full, "scratch_head": head,
        "fusion_split_marker": SPLIT_MARKER,
        "tasks": [{k: t[k] for k in ("task", "name", "commit", "parent", "tree", "patch",
                                     "patch_lines", "sha256", "build")} for t in tasks],
        "replay": "PASS: (1) temporary-index git apply --cached per patch equals each task "
                  "commit tree; (2) fresh BASE checkout, git apply --check then git apply in "
                  "order, `git diff --cached --stat PROTO -- leanncd` empty",
        "excluded_from_patches": extra,
        "forbidden_token_grep": {"pattern": FORBIDDEN.pattern, "hits": hits},
        "mutation_manifest_check_unfiltered": {"rc": mm.returncode, "output": mm_out.strip()},
        "mutation_task_tag_audit": audit,
        "derived_intermediate_files": [FUSION, RUN, LAKEFILE, PLANLEAN],
    }
    (artifacts / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(json.dumps({"head": head, "replay": "PASS", "mm_rc": mm.returncode, "grep_hits": hits,
                      "patch_lines": {t["name"]: t["patch_lines"] for t in tasks},
                      "tag_defects": [a["label"] for a in audit
                                      if a["tag_before_code"] or a["tag_before_target"]]},
                     indent=2))


if __name__ == "__main__":
    main()
