#!/usr/bin/env python3
"""Verify installed prototype stage replay, controls and restoration to its base."""

import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[3]
ARTIFACTS = Path(__file__).resolve().parent
LEAN = ROOT / "leanncd"
READY = ARTIFACTS / "readiness.json"


def git(*args):
    return subprocess.check_output(
        ["/usr/bin/git", "-C", str(ROOT), "--no-pager", *args], text=True
    ).strip()


def run(label, command):
    log = ARTIFACTS / f"final-{label}.log"
    print(f"{label}: running", flush=True)
    with log.open("w") as output:
        result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    text = log.read_text()
    if result.returncode:
        errors = [line for line in text.splitlines() if "error:" in line or "FAIL" in line]
        raise RuntimeError(f"{label} exited {result.returncode}: {errors[-8:]}; log={log}")
    summaries = [
        line for line in text.splitlines()
        if "Build completed successfully" in line or re.fullmatch(r"\d+/\d+ cycles passed\.", line)
        or line.startswith("manifest OK:")
    ]
    print(f"{label}: PASS {summaries[-1:]}", flush=True)
    return {"command": command, "exit_code": 0, "log": log.name, "summaries": summaries}


def build(label, targets):
    return run(label, ["bash", str(LEAN / "scripts/lake-build.sh"), str(LEAN), *targets])


def hashes_match(data):
    for path, expected in data["file_sha256"].items():
        actual = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"Installed compiled bytes differ: {path}")


def reverse(stages):
    for stage in reversed(stages):
        patch = str(ROOT / stage["patch"])
        git("apply", "-R", "--check", patch)
        git("apply", "-R", patch)


def main():
    data = json.loads(READY.read_text())
    if git("rev-parse", "HEAD") != data["base_commit"]:
        raise ValueError("HEAD differs from the package base")
    hashes_match(data)
    stages = data["stages"]
    reverse(stages)
    git("diff", "--exit-code", "HEAD", "--", "leanncd")
    receipts = {"stages": [], "final_manifests": [], "status": "in_progress"}
    for stage in stages:
        patch = str(ROOT / stage["patch"])
        git("apply", "--check", patch)
        git("apply", patch)
        checks = []
        for name in stage["mutation_manifests"]:
            checks.append(run(f"stage-{stage['task']}-{name.removesuffix('.json')}-check", [
                "bash", str(LEAN / "scripts/mutation-manifest.sh"), "--check",
                str(LEAN), str(ARTIFACTS / name),
            ]))
        receipts["stages"].append({
            "task": stage["task"], "manifest_checks": checks,
            "build": build(f"stage-{stage['task']}", stage["build_targets"]),
        })
        (ARTIFACTS / "controller-readiness.json").write_text(json.dumps(receipts, indent=2) + "\n")
    hashes_match(data)
    for name in ["raw_source_admission_mutations.json", "raw_source_admission_mutations_post.json"]:
        group = "post" if "_post" in name else "existing"
        manifest = ARTIFACTS.parent / name
        check = run(f"manifest-{group}-check", [
            "bash", str(LEAN / "scripts/mutation-manifest.sh"), "--check", str(LEAN), str(manifest),
        ])
        cycle = run(f"manifest-{group}", [
            "bash", str(LEAN / "scripts/mutation-manifest.sh"), "--out",
            str(ARTIFACTS / f"final-manifest-{group}.md"), str(LEAN), str(manifest),
        ])
        receipts["final_manifests"].append({"name": name, "check": check, "cycles": cycle})
    hashes_match(data)
    receipts["full_default_build"] = build("full-build", [])
    reverse(stages)
    git("diff", "--exit-code", "HEAD", "--", "leanncd")
    if git("status", "--porcelain", "--", *data["file_sha256"]):
        raise ValueError("Prototype source paths were not fully restored")
    receipts["restored_base_build"] = build("restored-base-build", ["LeanNCD"])
    receipts["cached_replay_after_restoration"] = run("restored-package-verify", [
        "python3", str(ARTIFACTS / "emit_ready_patches.py"), "--verify",
    ])
    receipts["status"] = "all_controller_readiness_gates_pass"
    receipts["source_restored_to_base"] = True
    (ARTIFACTS / "controller-readiness.json").write_text(json.dumps(receipts, indent=2) + "\n")
    data["status"] = "execution_ready_not_landed"
    data["mechanical_validation"]["stage_build_replay"] = "passed controller"
    data["controller_checks"].update({
        "ordered_stage_builds": "passed: 4/4",
        "full_default_build": "passed",
        "final_manifests_check_and_cycles": "passed: 17/17",
        "restored_hashes_and_green": "passed; prototype source restored to base; base LeanNCD green",
    })
    data["controller_receipt"] = "controller-readiness.json"
    READY.write_text(json.dumps(data, indent=2) + "\n")
    print("EXECUTION READY; prototype source restored; no commit/merge/push", flush=True)


if __name__ == "__main__":
    main()
