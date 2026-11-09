#!/usr/bin/env python3
"""Export checked real-split sources, exact copy audit, task patches, and donor controls."""
import argparse
import difflib
import hashlib
import json
import os
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[3]
OUT = pathlib.Path(__file__).resolve().parent
SRC = "leanncd/experiments/indexed_execution/"
TASKS = {
    "1": ["IndexedSourceWire"],
    "2": ["IndexedSourceSyntax", "IndexedSourceFunctor", "IndexedSourceSemantics"],
    "3": ["IndexedSourceTest", "IndexedSourceObservationProbe",
          "IndexedSourceObservationProbeTest", "IndexedSourceObservationParity"],
}


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def body(text, name, stop):
    return text.split("def " + name, 1)[1].split(stop, 1)[0]


def copies():
    original = (ROOT / (SRC + "IndexedSourceWire.lean")).read_text()
    probe = (ROOT / (SRC + "IndexedSourceObservationProbe.lean")).read_text()
    computational = body(original, "Wire.env ", "\ntheorem").split(":=", 1)[1].strip()
    rows = []
    for name in ["boundaryCopy", "inputCopy", "outputCopy"]:
        copied = body(probe, name + " ", "\ndef").split(":=", 1)[1].strip()
        assert copied == computational, name
        rows.append({"copy": name, "donor": "IndexedSource.Wire.env", "body_sha256": sha(copied)})
    return rows


def patch(path, old, new):
    return f"diff --git a/{path} b/{path}\n" + ("new file mode 100644\n" if not old else "") + "".join(difflib.unified_diff(
        old.splitlines(True), new.splitlines(True),
        fromfile="a/" + path if old else "/dev/null", tofile="b/" + path))


def export():
    copies_audit = copies()
    base = subprocess.check_output(
        ["/usr/bin/git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
    lake = "leanncd/lakefile.toml"
    old_lake = subprocess.check_output(
        ["/usr/bin/git", "-C", str(ROOT), "show", "HEAD:" + lake], text=True)
    middle_lake = old_lake.replace('"IndexedWitnessObservationParity"]',
        '"IndexedWitnessObservationParity",\n'
        '         "IndexedSourceWire", "IndexedSourceSyntax", "IndexedSourceFunctor",\n'
        '         "IndexedSourceSemantics"]')
    final_lake = (ROOT / lake).read_text()
    files = []
    patches = []
    for task, names in TASKS.items():
        text = ""
        for name in names:
            path = SRC + name + ".lean"
            content = (ROOT / path).read_text()
            text += patch(path, "", content)
            files.append({"task": task, "path": path, "sha256": sha(content)})
        if task == "2":
            text += patch(lake, old_lake, middle_lake)
        if task == "3":
            text += patch(lake, middle_lake, final_lake)
        target = OUT / ("task" + task + ".patch")
        target.write_text(text)
        patches.append({"task": task, "path": target.name, "sha256": sha(text)})
    package = {"base": base, "files": files, "patches": patches,
               "exact_computational_copies": copies_audit,
               "final_lakefile_sha256": sha(final_lake)}
    (OUT / "package.json").write_text(json.dumps(package, indent=2) + "\n")
    return package


def propose():
    entries = []
    probe = (ROOT / (SRC + "IndexedSourceObservationProbe.lean")).read_text()
    for num, name in enumerate(["boundaryCopy", "inputCopy", "outputCopy"], 1):
        old = "def " + name + body(probe, name, "\ndef")
        new = old.replace("Equiv.refl ℚ", "Equiv.addRight (1 : ℚ)")
        entries.append({"label": f"M{num} ({name} changes values)", "task": "3",
                        "file": SRC.removeprefix("leanncd/") + "IndexedSourceObservationProbe.lean",
                        "old": old.rstrip(), "new": new.rstrip(),
                        "targets": ["IndexedSourceObservationProbeTest"]})
    entries.append({"label": "M4 (inverse coordinate reversal)", "task": "3",
        "file": SRC.removeprefix("leanncd/") + "IndexedSourceObservationProbe.lean",
        "old": "  (boundaryCopy a).symm",
        "new": "  (boundaryCopy a).symm.trans\n    (IndexedWitnessObservationProbe.reverseEnvironment X.interface)",
        "targets": ["IndexedSourceObservationProbeTest"]})
    deltas = [
        ("M5 (hidden private donor collapse)", "def second := IndexedWitnessTest.hiddenOne",
         "def second := IndexedWitnessTest.hiddenZero"),
        ("M6 (nested private identity donor)", "def privateId : Nat := (declarations (compose A B ab) C).uid (.inl (.inl 1))",
         "def privateId : Nat := (declarations A (compose B C bc)).uid (.inl 1)"),
        ("M7 (empty input absence donor)",
         "  (((inputEquiv emptyProducerComponent) IndexedWitnessTest.emptyInputEnv).val\n    external.val).isSome",
         "  (none : Option (Coord [] → ℚ)).isSome"),
        ("M8 (strict-to-total theorem donor)", "def profile : Nat := 0", "def profile : Nat := 4"),
        ("M9 (total-to-strict theorem donor)", "def totalProfile : Nat := 4", "def totalProfile : Nat := 0"),
        ("M10 (empty metadata object donor)", "def original := output emptyProducerComponent",
         "def original := output IndexedWitnessCompositionTest.Empty.composite"),
    ]
    for label, old, new in deltas:
        entries.append({"label": label, "task": "3",
            "file": SRC.removeprefix("leanncd/") + "IndexedSourceObservationProbeTest.lean",
            "old": old, "new": new, "targets": ["IndexedSourceObservationProbeTest"]})
    path = ROOT / "papers/semantics/categorical_source_functor_mutations_post.json"
    assert not path.exists(), "Do not overwrite observed expectations"
    path.write_text(json.dumps(entries, indent=2) + "\n")


def audit():
    package = json.loads((OUT / "package.json").read_text())
    for row in package["files"]:
        assert sha((ROOT / row["path"]).read_text()) == row["sha256"], row["path"]
    for row in package["patches"]:
        assert sha((OUT / row["path"]).read_text()) == row["sha256"], row["path"]
    assert copies() == package["exact_computational_copies"]
    assert sha((ROOT / "leanncd/lakefile.toml").read_text()) == package["final_lakefile_sha256"]
    print("Artifact/copy audit PASS:", len(package["files"]), "files;", len(package["patches"]), "patches")

def snippets():
    rows = []
    for names in TASKS.values():
        for name in names:
            command = ["bash", str(ROOT / ".claude/skills/slice-plan/check-snippet.sh"),
                       str(ROOT / (SRC + name + ".lean"))]
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            (OUT / (name + ".snippet.log")).write_text(result.stdout + result.stderr)
            rows.append({"module": name, "command": command, "exit": result.returncode})
            assert result.returncode == 0, name
    (OUT / "snippets.json").write_text(json.dumps(rows, indent=2) + "\n")
    print("Post-edit check-snippet PASS:", len(rows), "real-split modules")


def replay_check():
    package = json.loads((OUT / "package.json").read_text())
    index = OUT / "replay.index"
    assert not index.exists(), "Do not overwrite an existing index"
    env = {**os.environ, "GIT_INDEX_FILE": str(index)}
    git = ["/usr/bin/git", "-C", str(ROOT)]
    try:
        subprocess.run(git + ["read-tree", package["base"]], env=env, check=True)
        for row in package["patches"]:
            subprocess.run(git + ["apply", "--cached", str(OUT / row["path"])], env=env, check=True)
        for row in package["files"] + [{"path": "leanncd/lakefile.toml",
                                       "sha256": package["final_lakefile_sha256"]}]:
            staged = subprocess.check_output(git + ["show", ":" + row["path"]], env=env)
            assert hashlib.sha256(staged).hexdigest() == row["sha256"], row["path"]
        (OUT / "replay.json").write_text(json.dumps({"base": package["base"],
            "patches_applied_in_order": [r["path"] for r in package["patches"]],
            "all_replayed_bytes_equal_compiled_sources": True}, indent=2) + "\n")
        print("Ordered alternate-index replay PASS; real worktree/index untouched")
    finally:
        index.unlink(missing_ok=True)

def freeze_expectations():
    path = ROOT / "papers/semantics/categorical_source_functor_mutations_post.json"
    entries = json.loads(path.read_text())
    log = (OUT / "mutations_initial.log").read_text()
    observations = []
    for entry in entries:
        section = log.split("=== " + entry["label"] + " MUTATE ===\n", 1)[1].split(
            "=== " + entry["label"] + " MUTATE exit=", 1)[0]
        diagnostic = re.search(r"error: experiments/[^\n]+\.lean:\d+:\d+: (.+)", section)[1]
        fixture = re.search(
            r"(IndexedSourceObservationProbeTest\.[\w.]+) uses #", section)[1]
        assert diagnostic in section and fixture in section
        entry["expect"] = [diagnostic, fixture]
        observations.append({"label": entry["label"], "diagnostic": diagnostic,
                             "failed_fixture": fixture,
                             "initial_restore_byte_identical": True})
    path.write_text(json.dumps(entries, indent=2) + "\n")
    (OUT / "observed_controls.json").write_text(json.dumps(observations, indent=2) + "\n")
    print("Frozen expectations copied from real mutation diagnostics:", len(entries))

def receipt():
    audit()
    package = json.loads((OUT / "package.json").read_text())
    build_log = ROOT / "papers/semantics/categorical_source_functor_full_build.log"
    build = build_log.read_text()
    assert "Build completed successfully (8919 jobs)." in build
    assert not re.search(r"^error:", build, re.MULTILINE)
    mutation_log = (OUT / "mutations_verified.log").read_text()
    table = (OUT / "mutations_verified.md").read_text()
    assert "10/10 cycles passed." in table
    assert table.count("| yes | yes | yes | PASS |") == 10
    entries = json.loads((ROOT / "papers/semantics/categorical_source_functor_mutations_post.json").read_text())
    for entry in entries:
        section = mutation_log.split("=== " + entry["label"] + " MUTATE ===\n", 1)[1].split(
            "=== " + entry["label"] + " MUTATE exit=", 1)[0]
        assert all(expected in section for expected in entry["expect"]), entry["label"]
    snippets_data = json.loads((OUT / "snippets.json").read_text())
    assert len(snippets_data) == 8 and all(row["exit"] == 0 for row in snippets_data)
    assert "COMPILES. Safe to write into the plan." in (OUT / "universe_check.log").read_text()
    assert json.loads((OUT / "replay.json").read_text())["all_replayed_bytes_equal_compiled_sources"]
    for row in package["files"]:
        assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b", (ROOT / row["path"]).read_text()), row["path"]
    changed = subprocess.check_output(
        ["/usr/bin/git", "-C", str(ROOT), "diff", "--name-only"], text=True).splitlines()
    assert changed == ["leanncd/lakefile.toml"], changed
    artifacts = [OUT / row["path"] for row in package["patches"]]
    artifacts += [OUT / name for name in ["package.py", "package.json", "snippets.json",
        "replay.json", "observed_controls.json", "mutations_verified.log", "mutations_verified.md",
        "universe_check.lean", "universe_check.log"]]
    artifacts += [ROOT / "papers/semantics/categorical_source_functor_mutations_post.json", build_log]
    data = {
        "scope": "authoring (a), compiled prototype; not an integration/release receipt",
        "base": package["base"], "full_build_jobs": 8919, "full_build_exit": 0,
        "populated_unfiltered_mutations": "10/10; expected diagnostics and identical restores",
        "post_edit_real_module_snippets": 8, "universe_snippet": "pass",
        "ordered_replay": "pass; exact bytes", "source_and_copy_audit": "pass",
        "only_tracked_edit": changed, "committed": False, "merged": False,
        "turn_aim_55_exceeded": True, "context_and_token_measurement": "no transcript; unavailable",
        "identities": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in artifacts},
    }
    (OUT / "verification_receipt.json").write_text(json.dumps(data, indent=2) + "\n")
    print("Authoring verification receipt PASS (not release/integration)")


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--propose", action="store_true")
    p.add_argument("--audit", action="store_true")
    p.add_argument("--snippets", action="store_true")
    p.add_argument("--replay-check", action="store_true")
    p.add_argument("--freeze-expectations", action="store_true")
    p.add_argument("--receipt", action="store_true")
    args = p.parse_args()
    if args.audit:
        audit()
    elif args.snippets:
        snippets()
    elif args.replay_check:
        replay_check()
    elif args.freeze_expectations:
        freeze_expectations()
    elif args.receipt:
        receipt()
    else:
        export()
        if args.propose:
            propose()
