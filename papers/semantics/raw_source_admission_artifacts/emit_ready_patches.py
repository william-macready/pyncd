#!/usr/bin/env python3
"""Package installed compiled bytes without changing source files or the real index."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[3]
ARTIFACTS = Path(__file__).resolve().parent
PAPERS = ARTIFACTS.parent
PATCHES = PAPERS / "raw_source_admission_patches"
BASE = "3d721f9631de8642163446f98b4efc8fe1d078d5"
STAGES = [
    ("01-certified-binding.patch", [
        "leanncd/LeanNCD/DSL/Traverse.lean",
        "leanncd/LeanNCD/DSL/Pipeline/Structural.lean",
        "leanncd/LeanNCD/Semantics/Source/Adapter.lean",
    ], ["LeanNCD.Semantics.Source.Adapter"]),
    ("02-resolved-occurrences.patch", [
        "leanncd/LeanNCD/Semantics/Source/Admission.lean",
    ], ["LeanNCD.Semantics.Source.Admission"]),
    ("03-raw-correspondence.patch", [
        "leanncd/LeanNCD/Semantics/Source/RawCorrespondence.lean",
    ], ["LeanNCD.Semantics.Source.RawCorrespondence"]),
    ("04-semantic-fixtures.patch", [
        "leanncd/LeanNCD/Semantics/Source/RawSemanticConnection.lean",
        "leanncd/LeanNCD/Semantics/Source.lean",
        "leanncd/test/Semantics/SourceRawCorrespondenceTest.lean",
        "leanncd/test/Semantics/SourceAdmissionTest.lean",
        "leanncd/lakefile.toml",
    ], [
        "LeanNCD.Semantics.Source.RawSemanticConnection",
        "Semantics.SourceRawCorrespondenceTest",
        "Semantics.SourceAdmissionTest", "LeanNCD",
    ]),
]
FILES = [path for _, paths, _ in STAGES for path in paths]
RECEIPTS = [
    "declaration_invariants.json", "resolver_binding.json", "raw_bridge.json",
    "semantic_connection.json", "structural_fixtures.json", "endpoint_fixtures.json",
    "soundness_review.json", "fidelity_review.json",
    "controller-existing.md", "controller-existing.log",
    "controller-post.md", "controller-post.log",
    "controller-structural.md", "controller-structural.log",
    "controller-endpoint.md", "controller-endpoint.log",
]
CONTROLS = {
    "M1": ("1", "unsolved goals"),
    "M2": ("2", "`simp` made no progress"),
    "M3": ("2", "Application type mismatch"),
    "M4": ("4", "Expression"),
    "S1": ("1", "Application type mismatch"),
    "S2": ("1", "Application type mismatch"),
    "S3": ("1", "Application type mismatch"),
    "S4": ("2", "Application type mismatch"),
    "S5": ("2", "Application type mismatch"),
    "S6": ("1", "unsolved goals"),
    "S7": ("1", "Application type mismatch"),
    "S8": ("1", "unsolved goals"),
    "E1": ("2", "unsolved goals"),
    "E2": ("2", "`simp` made no progress"),
    "E3": ("2", "unsolved goals"),
    "E4": ("4", "Application type mismatch"),
    "E5": ("4", "Expression"),
}
LABELS = {
    "M1": "bypass original axis-name mint loop",
    "M2": "table position used as declaration origin",
    "M3": "reverse certified checked read order",
    "M4": "asymmetric ordered oracle swaps distinct tensors",
    "S1": "original declaration ID becomes tensor table index",
    "S2": "reverse declared axis accumulation",
    "S3": "drop first untyped declared axis",
    "S4": "reverse raw factor occurrence traversal",
    "S5": "drop raw factor occurrence",
    "S6": "use initial UID despite covering name memo",
    "S7": "replace external role by defined role",
    "S8": "classify typed f64 as f32",
    "E1": "nonSum guard deletion",
    "E2": "nonSum and nonIdentity guard deletion",
    "E3": "constant Z output lookup",
    "E4": "reverse certified raw read coordinate witness",
    "E5": "refusal max-to-sum donor contrast",
}


def git(*args, env=None):
    try:
        return subprocess.run(
            ["/usr/bin/git", "-C", str(ROOT), "--no-pager", *args],
            env=env, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout
    except subprocess.CalledProcessError as error:
        raise RuntimeError(error.stderr.decode()) from error


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(path):
    return json.loads(path.read_text())


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def real_index_hash():
    path = Path(git("rev-parse", "--git-path", "index").decode().strip())
    if not path.is_absolute():
        path = ROOT / path
    return sha(path.read_bytes()) if path.exists() else None


def temporary_index(directory):
    env = os.environ.copy()
    env["GIT_INDEX_FILE"] = str(Path(directory) / "index")
    git("read-tree", "HEAD", env=env)
    return env


def consolidate():
    entries = []
    for name in ("raw_source_admission_mutations.json",
                 "raw_source_admission_mutations_post.json"):
        entries.extend(e for e in load(PAPERS / name)
                       if e["label"].split()[0].startswith("M"))
    for name in ("structural_mutations_candidates.json",
                 "endpoint_mutations_candidates.json"):
        entries.extend(load(ARTIFACTS / name))
    by_id = {e["label"].split()[0]: e for e in entries}
    if len(entries) != 17 or set(by_id) != set(CONTROLS):
        raise ValueError("Expected exactly one entry for every M/S/E stable prefix")
    logs = "\n".join((ARTIFACTS / name).read_text() for name in RECEIPTS
                     if name.startswith("controller-") and name.endswith(".log"))
    existing, post = [], []
    for prefix, (task, message) in CONTROLS.items():
        original = by_id[prefix]
        match = re.search(rf"^=== ({prefix} .*) MUTATE ===$", logs, re.MULTILINE)
        if match is None:
            raise ValueError(f"{prefix}: missing mutation receipt")
        label = match.group(1)
        begin = match.start()
        end = logs.index(f"=== {label} MUTATE exit=", begin)
        observation = logs[begin:end]
        error_prefix = "error: " + original["file"]
        if not any(line.startswith(error_prefix + ":") and message in line
                   for line in observation.splitlines()):
            raise ValueError(f"{prefix}: expected message not observed in mutation log")
        if f"=== {label} SUMMARY: mutation_exit=1 restore_hash_exit=0 restored_build_exit=0 ===" not in logs:
            raise ValueError(f"{prefix}: missing successful controller cycle receipt")
        target = {
            "1": "LeanNCD.Semantics.Source.Adapter",
            "2": "LeanNCD.Semantics.Source.Admission",
            "4": "LeanNCD.Semantics.Source.RawSemanticConnection",
        }[task]
        kind = "fixture-contrast" if prefix in ("M4", "E5") else "proof-protected rejection"
        if kind == "fixture-contrast":
            target = "Semantics.SourceRawCorrespondenceTest"
        entry = {
            "label": f"{prefix} {LABELS[prefix]} ({kind})",
            "task": task, "file": original["file"],
            "old": original["old"], "new": original["new"],
            "targets": [target], "expect": [error_prefix, message],
        }
        installed = (ROOT / "leanncd" / entry["file"]).read_text()
        if installed.count(entry["old"]) != 1:
            raise ValueError(f"{prefix}: installed old text is not unique")
        base_path = "leanncd/" + entry["file"]
        tracked = git("ls-tree", "--name-only", BASE, "--", base_path)
        base_text = git("show", f"{BASE}:{base_path}").decode() if tracked else ""
        (existing if entry["old"] in base_text else post).append(entry)
    write_json(PAPERS / "raw_source_admission_mutations.json", existing)
    write_json(PAPERS / "raw_source_admission_mutations_post.json", post)
    print(f"Consolidated {len(existing)} base-text and {len(post)} post-text controls; cycles NOT rerun")


def stage_manifests():
    projections = {}
    for kind, name in (
        ("existing", "raw_source_admission_mutations.json"),
        ("post", "raw_source_admission_mutations_post.json"),
    ):
        entries = load(PAPERS / name)
        for task in ("1", "2", "4"):
            selected = [entry for entry in entries if entry["task"] == task]
            if selected:
                path = ARTIFACTS / f"stage-{task}-{kind}.json"
                write_json(path, selected)
                projections[path.name] = sha(path.read_bytes())
    return projections


def verify(data):
    if data["base_commit"] != BASE:
        raise ValueError("Readiness base mismatch")
    for name, expected in data["receipts"].items():
        if sha((ARTIFACTS / name).read_bytes()) != expected:
            raise ValueError(f"Receipt hash mismatch: {name}")
    for name, expected in data["manifest_sha256"].items():
        if sha((PAPERS / name).read_bytes()) != expected:
            raise ValueError(f"Manifest hash mismatch: {name}")
    for name, expected in data["stage_manifest_sha256"].items():
        path = ARTIFACTS / name
        if sha(path.read_bytes()) != expected:
            raise ValueError(f"Stage manifest hash mismatch: {name}")
        _, task, kind = path.stem.split("-")
        authority = "raw_source_admission_mutations" + ("_post" if kind == "post" else "") + ".json"
        if load(path) != [entry for entry in load(PAPERS / authority) if entry["task"] == task]:
            raise ValueError(f"Stage manifest is not an exact authority projection: {name}")
    history = data["history_only"]
    if sha((ARTIFACTS / "evidence.json").read_bytes()) != history["evidence.json"]:
        raise ValueError("Historical evidence hash mismatch")
    for name in ("task-1.patch", "task-2.patch", "task-3.patch"):
        if sha((PATCHES / name).read_bytes()) != history[name]:
            raise ValueError(f"Historical seed patch hash mismatch: {name}")
    for name, expected in history["candidate_manifest_sha256"].items():
        if sha((ARTIFACTS / name).read_bytes()) != expected:
            raise ValueError(f"Historical candidate manifest hash mismatch: {name}")
    with tempfile.TemporaryDirectory(prefix="raw-admission-replay-") as directory:
        env = temporary_index(directory)
        for stage in data["stages"]:
            patch = ROOT / stage["patch"]
            if sha(patch.read_bytes()) != stage["sha256"]:
                raise ValueError(f"Patch hash mismatch: {patch}")
            git("apply", "--cached", "--check", str(patch), env=env)
            git("apply", "--cached", str(patch), env=env)
            for path, expected in stage["file_sha256"].items():
                if sha(git("show", ":" + path, env=env)) != expected:
                    raise ValueError(f"Stage {stage['task']} byte mismatch: {path}")
            for name in stage["mutation_manifests"]:
                for entry in load(ARTIFACTS / name):
                    text = git("show", ":leanncd/" + entry["file"], env=env).decode()
                    if text.count(entry["old"]) != 1:
                        raise ValueError(f"Stage {stage['task']} mutation old text is not unique: {entry['label']}")
        for path, expected in data["file_sha256"].items():
            if sha(git("show", ":" + path, env=env)) != expected:
                raise ValueError(f"Final cached byte mismatch: {path}")
        changed = set(git("diff", "--cached", "--name-only", "HEAD", env=env).decode().splitlines())
        if changed != set(FILES):
            raise ValueError(f"Unexpected cached replay path set: {sorted(changed)}")
    print("Ordered cached replay: all 10 source-file SHA256 values match captured compiled bytes")
    print("Task projections: every mutation old text exists uniquely at its cached stage prefix")


def capture():
    installed = {path: sha((ROOT / path).read_bytes()) for path in FILES}
    projection_hashes = stage_manifests()
    stages = []
    with tempfile.TemporaryDirectory(prefix="raw-admission-capture-") as directory:
        env = temporary_index(directory)
        for task, (name, paths, targets) in enumerate(STAGES, 1):
            git("add", "--", *paths, env=env)
            patch = git("diff", "--cached", "--binary", "--no-ext-diff",
                        "--no-textconv", "HEAD", "--", *paths, env=env)
            if not patch:
                raise ValueError(f"Empty stage {task}")
            (PATCHES / name).write_bytes(patch)
            stages.append({
                "task": str(task), "depends_on": [] if task == 1 else [str(task - 1)],
                "patch": str((PATCHES / name).relative_to(ROOT)),
                "sha256": sha(patch), "paths": paths, "build_targets": targets,
                "file_sha256": {path: installed[path] for path in paths},
                "controls": [p for p, (t, _) in CONTROLS.items() if t == str(task)],
                "fixture_families_run_at_stage": 10 if task == 4 else 0,
                "mutation_manifests": [
                    name for name in projection_hashes if name.startswith(f"stage-{task}-")
                ],
            })
    data = {
        "status": "verified proof, pending controller stage replay/full build",
        "base_commit": BASE, "stages": stages, "file_sha256": installed,
        "mechanical_validation": {
            "ordered_cached_application": "passed",
            "compiled_byte_hash_match": "passed",
            "source_worktree_unchanged": True, "real_index_untouched": True,
            "stage_build_replay": "pending controller",
        },
        "receipts": {name: sha((ARTIFACTS / name).read_bytes()) for name in RECEIPTS},
        "contracts": {
            "A": "resolver_binding.json and declaration_invariants.json: actual memo coverage, original declaration IDs, ordered pins/slots, specs roles/shapes",
            "B": "raw_bridge.json: actual-success original-raw indexed AST/slot/declaration correspondence",
            "C": "semantic_connection.json: certified checked/global semantics; reached equations relative to result.input, with complete-outcome premises",
            "fixtures": load(ARTIFACTS / "endpoint_fixtures.json")["ten_family_inventory"],
            "mutation_counts_observed_before_consolidation": {
                "total": 17, "proof_protected_rejections": 15,
                "fixture_contrasts": 2, "runtime_kills": 0,
            },
            "reviews": "soundness/fidelity reports clean within installed-source scope, not package or whole-branch approval",
        },
        "manifest_sha256": {
            name: sha((PAPERS / name).read_bytes()) for name in (
                "raw_source_admission_mutations.json", "raw_source_admission_mutations_post.json")
        },
        "stage_manifest_sha256": projection_hashes,
        "stage_manifest_note": "Exact task projections of the two authoritative manifests, not independent authority. Runner validates all entries before --task filtering.",
        "history_only": {
            "evidence.json": sha((ARTIFACTS / "evidence.json").read_bytes()),
            **{name: sha((PATCHES / name).read_bytes()) for name in (
                "task-1.patch", "task-2.patch", "task-3.patch")},
            "candidate_manifest_sha256": {
                name: sha((ARTIFACTS / name).read_bytes()) for name in (
                    "structural_mutations_candidates.json", "endpoint_mutations_candidates.json")
            },
            "note": "Partial seed and candidate manifests are historical design evidence, not final readiness receipts.",
        },
        "controller_checks": {
            "ordered_stage_builds": "pending", "full_default_build": "pending",
            "final_manifests_check_and_cycles": "pending",
            "restored_hashes_and_green": "pending",
            "execution_docs_and_whole_branch_reviews": "future execution",
        },
        "runtime_docs": "Task 4 execution edits; not included in compiled prototype patch",
        "budget": "SDK exact turns/context/cumulative input unavailable; no measured 50M compliance claimed",
        "commands": {
            "capture": f"python3 {Path(__file__).resolve()} --capture",
            "verify": f"python3 {Path(__file__).resolve()} --verify",
            "consolidate": f"python3 {Path(__file__).resolve()} --consolidate",
        },
    }
    verify(data)
    if installed != {path: sha((ROOT / path).read_bytes()) for path in FILES}:
        raise ValueError("Source bytes changed during capture")
    write_json(ARTIFACTS / "readiness.json", data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--capture", action="store_true")
    group.add_argument("--verify", action="store_true")
    group.add_argument("--consolidate", action="store_true")
    args = parser.parse_args()
    if git("rev-parse", "HEAD").decode().strip() != BASE:
        raise ValueError("HEAD must equal the recorded base; do not silently rebase the package")
    index_before = real_index_hash()
    try:
        if args.consolidate:
            consolidate()
        elif args.capture:
            capture()
        else:
            verify(load(ARTIFACTS / "readiness.json"))
    finally:
        if real_index_hash() != index_before:
            raise RuntimeError("Real git index changed during packaging")


if __name__ == "__main__":
    main()
