#!/usr/bin/env python3
"""Capture exact compiled diffs, validate ordered application, or restore this prototype only."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
ARTIFACTS = Path(__file__).resolve().parent
PATCHES = ROOT / "papers/semantics/raw_source_admission_patches"
LOGS = Path("/Users/williammacready/.copilot/session-state/f0f50335-e56d-401a-a010-11d0d43c0404/files")
TASKS = {
    "1": [
        "leanncd/LeanNCD/DSL/Pipeline/Structural.lean",
        "leanncd/LeanNCD/Semantics/Source/Adapter.lean",
    ],
    "2": ["leanncd/LeanNCD/Semantics/Source/Admission.lean"],
    "3": [
        "leanncd/LeanNCD/Semantics/Source/RawCorrespondence.lean",
        "leanncd/LeanNCD/Semantics/Source.lean",
        "leanncd/test/Semantics/SourceRawCorrespondenceTest.lean",
        "leanncd/test/Semantics/SourceAdmissionTest.lean",
        "leanncd/lakefile.toml",
    ],
}
FILES = [p for paths in TASKS.values() for p in paths]


def git(*args, env=None):
    return subprocess.run(
        ["/usr/bin/git", "-C", str(ROOT), *args],
        env=env, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    ).stdout


def sha(data):
    return hashlib.sha256(data).hexdigest()


def receipt(log, name, prefixes):
    lines = log.read_text().splitlines()
    selected = []
    taking = False
    for line in lines:
        if line.startswith(("info:", "warning:", "error:", "trace:", "✔", "⚠", "✖")):
            taking = any(prefix in line for prefix in prefixes)
        if taking and not line.startswith("trace:"):
            selected.append(line)
    (ARTIFACTS / name).write_text("\n".join(selected) + "\n")


def capture(evidence):
    expected = git("rev-parse", "HEAD").decode().strip()
    assert expected.startswith(evidence["base_commit"]), expected
    PATCHES.mkdir(exist_ok=True)
    fd, index = tempfile.mkstemp(prefix="raw-admission-index-")
    os.close(fd)
    os.unlink(index)
    env = {**os.environ, "GIT_INDEX_FILE": index}
    compiled = {p: (ROOT / p).read_bytes() for p in FILES}
    try:
        git("read-tree", "HEAD", env=env)
        git("add", "--", *[str(ROOT / p) for p in FILES], env=env)
        for task, paths in TASKS.items():
            patch = git("diff", "--cached", "--no-ext-diff", "--binary",
                        "HEAD", "--", *[str(ROOT / p) for p in paths], env=env)
            assert patch, task
            (PATCHES / f"task-{task}.patch").write_bytes(patch)
        git("read-tree", "HEAD", env=env)
        for task in TASKS:
            path = str(PATCHES / f"task-{task}.patch")
            git("apply", "--cached", "--check", path, env=env)
            git("apply", "--cached", path, env=env)
        for path, data in compiled.items():
            assert git("show", f":{path}", env=env) == data, path
    finally:
        if Path(index).exists():
            os.unlink(index)
        lock = Path(index + ".lock")
        if lock.exists():
            lock.unlink()
    evidence["base_commit"] = expected
    evidence["mechanical_patches"] = {
        "ordered_cached_apply_checked": True,
        "result_matches_compiled_bytes": True,
        "compiled_file_sha256": {p: sha(d) for p, d in compiled.items()},
        "patch_sha256": {
            f"task-{t}.patch": sha((PATCHES / f"task-{t}.patch").read_bytes()) for t in TASKS
        },
        "method": "isolated temporary git index, explicit source paths only; ordered cached apply checked against each exact compiled file; real index untouched",
    }
    receipt(LOGS / "prototype-endpoint.log", "fixtures.log",
            ["info: test/Semantics/SourceRawCorrespondenceTest.lean"])
    audit_lines = [
        line for line in (LOGS / "prototype-endpoint.log").read_text().splitlines()
        if "Source/RawCorrespondence.lean:" in line and
        ("depends on axioms" in line or "does not depend" in line)
    ]
    assert len(audit_lines) == 15, len(audit_lines)
    assert not any("sorryAx" in line or "Lean.ofReduceBool" in line for line in audit_lines)
    (ARTIFACTS / "axioms.log").write_text("\n".join(audit_lines) + "\n")
    for label in ["existing", "post"]:
        text = (LOGS / f"mutations-{label}.log").read_text()
        (ARTIFACTS / f"mutations-{label}.log").write_text(text)
    command = f"bash {ROOT}/leanncd/scripts/lake-build.sh {ROOT}/leanncd"
    evidence["validation"]["builds"] = []
    for name, targets in [
        ("prototype-build.log", "LeanNCD.Semantics.Source.Admission"),
        ("prototype-endpoint.log", "Semantics.SourceAdmissionTest LeanNCD"),
        ("prototype-full.log", ""),
    ]:
        text = (LOGS / name).read_text()
        successes = [s for s in text.splitlines() if "Build completed successfully" in s]
        assert successes, name
        evidence["validation"]["builds"].append({
            "command": command + (" " + targets if targets else ""),
            "exit_code": 0, "observed_summary": successes[-1],
        })
    (ARTIFACTS / "builds.log").write_text("\n".join(
        f"{x['command']}\nexit=0: {x['observed_summary']}"
        for x in evidence["validation"]["builds"]) + "\n")
    evidence["validation"]["mutation_cycles"] = []
    for manifest in [
        ROOT / "papers/semantics/raw_source_admission_mutations.json",
        ROOT / "papers/semantics/raw_source_admission_mutations_post.json",
    ]:
        group = "post" if "_post" in manifest.name else "existing"
        text = (LOGS / f"mutations-{group}.log").read_text()
        for mutation in json.loads(manifest.read_text()):
            assert f"{mutation['label']} MANIFEST VERDICT: PASS" in text, mutation["label"]
            assert all(s in text for s in mutation["expect"]), mutation["label"]
            evidence["validation"]["mutation_cycles"].append({
                "label": mutation["label"], "task": mutation["task"],
                "targets": mutation["targets"], "expect": mutation["expect"],
                "observed": "mutation build failed; original bytes restored; restored build passed",
            })
    evidence["validation"]["earlier_failures"] = [
        "Initial EStateM proof elaboration failures corrected by explicitly unfolding bind/pure/Functor.map.",
        "Unregistered new test target rejected, then missing olean through aggregator; fixed by adding explicit lakefile Tests glob.",
        "First mutation run executed/restored both cycles successfully but receipt write failed because artifact directory did not yet exist; rerun with directory and expect strings.",
        "Earlier exploratory mutation of new assignUIDs tail rejected by kernel; superseded by mutation of original axis-name mint loop.",
    ]
    print("Captured three ordered patches; replay equals all eight exact compiled files.")


def restore(evidence):
    for task in reversed(TASKS):
        git("apply", "-R", "--check", str(PATCHES / f"task-{task}.patch"))
        git("apply", "-R", str(PATCHES / f"task-{task}.patch"))
    status = git("status", "--porcelain", "--", *[str(ROOT / p) for p in FILES])
    assert not status, status.decode()
    git("diff", "--exit-code", "HEAD", "--", str(ROOT / "leanncd"))
    evidence["restoration"] = {
        "source_equals_base": True,
        "method": "git apply -R task3/task2/task1; source-path status and all-leanncd diff empty",
        "no_checkout_reset_commit_merge": True,
    }
    print("Restored only prototype source changes; leanncd equals base.")


if __name__ == "__main__":
    evidence_path = ARTIFACTS / "evidence.json"
    evidence = json.loads(evidence_path.read_text())
    if sys.argv[1:] == ["capture"]:
        capture(evidence)
    elif sys.argv[1:] == ["restore"]:
        restore(evidence)
    else:
        raise SystemExit("usage: capture.py capture|restore")
    evidence_path.write_text(json.dumps(evidence, indent=2) + "\n")
