"""Emit compiled prototype patches; verify exact sequential replay and evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

BASE = "a2be7b9048ccfc70ab9d74cb19c5e5ee79861357"
TASKS = [
    ("01-ranks-measure", "2de6c4d2a2d37043d22fed1cf5d608497450a517", [
        "leanncd/LeanNCD/Semantics/Ranks.lean",
        "leanncd/LeanNCD/Semantics/Measure.lean"]),
    ("02-progress-correspondence", "08297501d4e1f8310b4f5901861b2683fc79e600", [
        "leanncd/LeanNCD/Semantics/Progress.lean"]),
    ("03-fixtures-integration", "426fe58", [
        "leanncd/test/Semantics/RankedMachineTest.lean",
        "leanncd/LeanNCD/Semantics.lean", "leanncd/lakefile.toml",
        "leanncd/LeanNCD/Semantics/AGENTS.md", "leanncd/AGENTS.md"]),
]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--logs", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    artifacts = Path(__file__).resolve().parent
    patches = artifacts.parent / "coordinate_ranks_finite_measure_patches"
    patches.mkdir(exist_ok=True)
    command = ["/usr/bin/git", "-C", str(repo)]

    def git(*argv, env=None):
        return subprocess.check_output(command + list(argv), env=env)

    before = BASE
    tasks = []
    for name, reference, files in TASKS:
        commit = git("rev-parse", reference).decode().strip()
        assert git("rev-parse", commit + "^").decode().strip() == before
        actual = git("diff", "--name-only", before, commit).decode().splitlines()
        assert sorted(actual) == sorted(files), (name, actual)
        patch = git("diff", "--binary", "--full-index", before, commit, "--", *files)
        path = patches / (name + ".patch")
        path.write_bytes(patch)
        tasks.append({"task": name, "commit": commit, "parent": before, "files": files,
                      "patch": str(path), "sha256": digest(patch),
                      "symbols": {
                          f: re.findall(r"^(?:noncomputable )?(?:def|abbrev|theorem|inductive|structure|instance) (\w+)",
                                        git("show", commit + ":" + f).decode(), re.M)
                          for f in files if f.endswith(".lean")
                      }})
        before = commit
    candidate = before
    assert git("rev-parse", "HEAD").decode().strip() == candidate
    assert not git("status", "--porcelain", "--untracked-files=all").strip()
    tree = git("rev-parse", candidate + "^{tree}").decode().strip()
    with tempfile.TemporaryDirectory(prefix="coordinate-replay-") as directory:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(directory) / "index"))
        git("read-tree", BASE, env=env)
        for task in tasks:
            git("apply", "--cached", "--check", task["patch"], env=env)
            git("apply", "--cached", task["patch"], env=env)
            replayed = git("write-tree", env=env).decode().strip()
            expected = git("rev-parse", task["commit"] + "^{tree}").decode().strip()
            assert replayed == expected, task["task"]
        assert replayed == tree

    protected_paths = git("ls-tree", "-r", "--name-only", BASE, "--",
                          "leanncd/LeanNCD/Semantics", "leanncd/test/Semantics",
                          "papers/semantics/tensor_logic_semantics.md",
                          "papers/semantics/lean_executable_semantics_path.md",
                          "papers/semantics/reference_machine_artifacts",
                          "leanncd/scripts", ".claude/settings.json").decode().splitlines()
    changed = {f for task in tasks for f in task["files"]}
    protected = {}
    for path in protected_paths:
        if path in changed:
            continue
        original = git("show", BASE + ":" + path)
        assert original == git("show", candidate + ":" + path), path
        assert original == (repo / path).read_bytes(), path
        protected[path] = digest(original)

    log_specs = [
        ("baseline", "coordinate-baseline.log", ["LeanNCD"]),
        ("targeted", "coordinate-targeted.log", ["Semantics.RankedMachineTest"]),
        ("full", "coordinate-full.log", ["LeanNCD", "Tests"]),
        ("mutations", "coordinate-mutations-observed.log", ["Semantics.RankedMachineTest"]),
        ("post_mutation_full", "coordinate-post-mutation-full.log", ["LeanNCD", "Tests"]),
    ]
    builds = []
    inventories = {}
    all_warnings = []
    for kind, filename, targets in log_specs:
        raw = (args.logs / filename).read_bytes()
        text = raw.decode()
        if kind == "mutations":
            assert "6/6 cycles passed." in text
        else:
            assert "Build completed successfully" in text and "error:" not in text
        for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
            if name.startswith(("LeanNCD.Semantics.Program.", "LeanNCD.Semantics.RankedMachineFixtures.")):
                values = [s.strip() for s in axioms.split(",") if s.strip()]
                assert set(values) <= {"propext", "Classical.choice", "Quot.sound"}, (name, values)
                inventories[name] = values
        warnings = [line for line in text.splitlines() if line.startswith("warning:")]
        if kind == "full":
            all_warnings = warnings
        builds.append({"kind": kind, "targets": targets, "exit_code": 0,
                       "log": str((args.logs / filename).resolve()), "sha256": digest(raw),
                       "warnings_count": len(warnings)})

    manifest_path = artifacts.parent / "coordinate_ranks_finite_measure_mutations_post.json"
    manifest = json.loads(manifest_path.read_text())
    mutation_log = (args.logs / "coordinate-mutations-observed.log").read_text()
    mutations = []
    for mutation in manifest:
        source = (repo / "leanncd" / mutation["file"]).read_text()
        assert source.count(mutation["old"]) == 1, mutation["label"]
        start = mutation_log.index("=== " + mutation["label"] + " MUTATE ===")
        end = mutation_log.index("=== " + mutation["label"] + " RESTORED BUILD ===", start)
        observed = mutation_log[start:end]
        assert mutation["expect"] and all(s in observed for s in mutation["expect"])
        assert mutation["label"] + " MANIFEST VERDICT: PASS" in mutation_log
        mutations.append({"label": mutation["label"], "result": "PASS",
                          "evidence_kind": "kernel proof rejection, not runtime oracle",
                          "expect_observed": mutation["expect"]})

    fixtures = git("show", candidate + ":leanncd/test/Semantics/RankedMachineTest.lean").decode()
    coverage = json.loads((artifacts / "coverage-audit.json").read_text())
    declarations = re.findall(r"^(?:def|abbrev|theorem|@\[reducible\] def) (\w+)", fixtures, re.M)
    for family in coverage["fixture_families"]:
        assert set(family["witnesses"]) <= set(declarations), family["case"]
    counts = {
        "task_commits": len(tasks), "patches": len(tasks), "changed_files": len(changed),
        "fixture_families": len(coverage["fixture_families"]),
        "fixture_declarations": len(declarations),
        "fixture_theorems": len(re.findall(r"^theorem ", fixtures, re.M)),
        "fixture_definitions_and_abbreviations": len(declarations) - len(re.findall(r"^theorem ", fixtures, re.M)),
        "program_construction_definitions": 8,
        "program_instances": 9,
        "mutation_cycles": len(mutations), "printed_axiom_inventories": len(inventories),
        "protected_inputs": len(protected),
    }
    guidance = {}
    for path in ["leanncd/AGENTS.md", "leanncd/LeanNCD/Semantics/AGENTS.md"]:
        text = git("show", BASE + ":" + path).decode()
        sections = re.split(r"(?m)^(#{2,3} .+)\n", text)
        injected = {sections[i]: len(sections[i + 1])
                    for i in range(1, len(sections), 2)
                    if re.search(r"Pitfalls|Checks|Patterns|Context", sections[i])}
        guidance[path] = {
            "base_total_characters": len(text),
            "base_injectible_named_section_characters": injected,
            "relevant_semantics_guidance_characters": len(
                "\n".join(line for line in text.splitlines() if "Semantic explorations" in line)),
            "unrelated_guidance_trimmed": False,
        }

    evidence = {
        "phase": "A verified disposable prototype",
        "base": BASE, "candidate": candidate, "candidate_tree": tree, "tasks": tasks,
        "sequential_temporary_index_replay": "PASS: exact tree at every task boundary",
        "builds": builds, "proof_axioms": inventories, "counts": counts,
        "protected_input_sha256": protected,
        "fixture_donors_and_audit": "coverage-audit.json",
        "observed_values": {
            "method": "equalities elaborated by actual targeted/full Lean proof builds; not executable relation evaluation",
            "duplicate_initial_count": 5, "duplicate_consume_count": 4,
            "singleton_initial_count": 1, "empty_initial_count": 0,
            "singleton_rank_zero": 0,
            "exact_zero_consumption_empty_fiber_nonoutput_decrease": 1,
        },
        "mutation_manifest": {"path": str(manifest_path), "sha256": digest(manifest_path.read_bytes()),
                              "runnable": True, "cycles": mutations},
        "guidance": guidance, "warnings": all_warnings,
        "unresolved_issues": [],
        "limitations": [
            "No executable scheduler, source checker, rank synthesis or acyclicity equivalence.",
            "Second success schedule uses a proved terminal extension from a different first step; no computed schedule is advertised.",
            "Mutation failures are proof rejection, not isolated runtime fixture failure.",
            "Full build has pre-existing sorry/linter warnings outside this slice; new printed inventories are standard axioms only.",
            "token-report.py returned 'no transcript for session'; token usage cannot be measured by that tool.",
            "Semantics AGENTS has no Pitfalls/Checks/Patterns/Context headings; parent named sections include unrelated material and were not trimmed.",
        ],
        "budget": {"turn_limit": 60, "peak_token_limit_approx": 250000,
                   "dispatch_turns_upper_bound": 60, "reported_breach": False,
                   "measured_token_usage": None,
                   "qualification": "Within turn cap; peak/cumulative usage unavailable from token-report.py. No known context breach."},
        "no_push_no_merge": True,
    }
    (artifacts / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(json.dumps({"candidate": candidate, "tree": tree, "counts": counts,
                      "replay": "PASS", "evidence": str(artifacts / "evidence.json")}, indent=2))


if __name__ == "__main__":
    main()
