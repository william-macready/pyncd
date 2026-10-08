"""Reproduce the authoring handoff from compiled commits and retained observations."""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


PARENT = Path("/Users/williammacready/code/python/pyncd.worktrees/executable-semantics-plan-differential-debugging")
PROTOTYPE = Path("/Users/williammacready/code/python/pyncd.worktrees/source-correspondence-prototype-57a40649")
ARTIFACTS = PARENT / "papers/semantics/source_correspondence_artifacts"
PATCHES = PARENT / "papers/semantics/source_correspondence_patches"


def git(*args, env=None):
    return subprocess.check_output(
        ["/usr/bin/git", "-C", str(PROTOTYPE), *args], text=True, env=env
    ).strip()


base = git("rev-parse", "1e7be32")
commits = git("rev-list", "--reverse", f"{base}..HEAD").splitlines()
patches = sorted(PATCHES.glob("*.patch"))
assert len(commits) == len(patches) == 3
assert git("status", "--porcelain") == "", "Prototype must be clean"
git("diff", "--check", base, "HEAD")

fd, index_name = tempfile.mkstemp(prefix="replay-", suffix=".index", dir=ARTIFACTS)
os.close(fd)
Path(index_name).unlink()
env = dict(os.environ, GIT_INDEX_FILE=index_name)
try:
    git("read-tree", base, env=env)
    for patch in patches:
        git("apply", "--cached", "--check", str(patch), env=env)
        git("apply", "--cached", str(patch), env=env)
    replay_tree = git("write-tree", env=env)
    assert replay_tree == git("rev-parse", "HEAD^{tree}")
finally:
    Path(index_name).unlink(missing_ok=True)
    Path(index_name + ".lock").unlink(missing_ok=True)

task_labels = [
    "UID resolution, positional enumeration, and nested Expr reduction interpretation",
    "Checked normalized products and single-target Program/global-fiber correspondence",
    "Rational differential fixtures, admission controls, and public/default integration",
]
tasks = []
inventory = []
verified_paths = []
for label, commit, patch in zip(task_labels, commits, patches):
    files = git("diff-tree", "--no-commit-id", "--name-only", "-r", commit).splitlines()
    assert not any("/DSL/" in f or "/Eval/" in f for f in files)
    tasks.append({
        "boundary": label,
        "commit": commit,
        "files": files,
        "patch": str(patch.relative_to(PARENT)),
        "patch_sha256": hashlib.sha256(patch.read_bytes()).hexdigest(),
    })
    for file in files:
        path = PROTOTYPE / file
        assert path.is_file()
        verified_paths.append(str(path))
        if path.suffix == ".lean":
            for match in re.finditer(
                r"^(?:@\[[^\n]*\]\s*)?(def|abbrev|structure|inductive|theorem|instance)\s+([A-Za-z_][\w.]*)",
                path.read_text(), re.MULTILINE,
            ):
                inventory.append({"kind": match[1], "identifier": match[2], "file": file})

fixture_log = (ARTIFACTS / "fixtures.log").read_text()
full_log = (ARTIFACTS / "full-build.log").read_text()
mutation_log = (ARTIFACTS / "mutations.log").read_text()
assert "Build completed successfully" in fixture_log
assert "Build completed successfully" in full_log
assert "sorryAx" not in fixture_log
assert "6/6 cycles passed" in mutation_log

observations = []
for line in fixture_log.splitlines():
    match = re.search(r"SourceCorrespondenceTest\.lean:\d+:\d+: ([^:]+): (.*)", line)
    if match:
        observations.append({"fixture": match[1], "observed": match[2]})
assert len(observations) == 14
mutations = json.loads((ARTIFACTS / "mutations.json").read_text())
failures = [line for line in mutation_log.splitlines()
            if line.startswith("error: test/Semantics/SourceCorrespondenceTest.lean:")
            and ": expected " in line]
assert len(failures) == 6
for mutation, failure in zip(mutations, failures):
    assert f"{mutation['label']}: PASS" in mutation_log
    assert all(expected in mutation_log for expected in mutation["expect"])
    mutation["observed_failure"] = failure
    mutation["restored_byte_identical"] = True
    mutation["restored_build_passed"] = True
    mutation["classification"] = "fixture-input semantic discriminator, not implementation mutation"

for path in (PROTOTYPE / "leanncd/LeanNCD/Semantics/Source").glob("*.lean"):
    assert not re.search(r"\bsorry\b|^axiom\s|^unsafe\s|^noncomputable\s|\bclassical\b",
                         path.read_text(), re.MULTILINE), path
for name in [
    "papers/semantics/tensor_logic_semantics.md",
    "papers/semantics/lean_executable_semantics_path.md",
    "leanncd/LeanNCD/Semantics/Types.lean",
    "leanncd/LeanNCD/Semantics/Expr.lean",
    "leanncd/LeanNCD/Semantics/Interpret.lean",
    "leanncd/LeanNCD/Semantics/Program.lean",
    "leanncd/LeanNCD/Semantics/Collection.lean",
    "leanncd/LeanNCD/Semantics/ExecutableState.lean",
    "leanncd/LeanNCD/Semantics/ReferenceExecutor.lean",
    "leanncd/LeanNCD/Semantics/RationalReference.lean",
    "leanncd/test/Semantics/ExpressionTest.lean",
    "leanncd/test/Semantics/CollectionModelTest.lean",
    "leanncd/test/Semantics/ExecutableReferenceTest.lean",
]:
    assert (PROTOTYPE / name).is_file()
    verified_paths.append(str(PROTOTYPE / name))

evidence = {
    "phase": "Authoring Phase A, partial scoped prototype; NOT an execution-ready slice",
    "base": base,
    "prototype_location": str(PROTOTYPE),
    "prototype_head": commits[-1],
    "production_DSL_Eval_edited": False,
    "plan_written": False,
    "merged": False,
    "remote_operations": False,
    "tasks": tasks,
    "symbol_inventory": inventory,
    "verified_claims": [
        "UID resolution ignores printed names and enforces full finite slot extents.",
        "Context uniqueness prevents duplicate UID binders; repeated slots reuse a Ref.",
        "PositionalVal (currently named NamedVal) is equivalent to typed Coord by namedEquiv.",
        "appendEquiv splits global typed valuations into output and contracted valuations.",
        "interpret_product and interpret_contract reach existing typed Expr, not an oracle AST.",
        "sumBody contracts each term independently before addition.",
        "elaborate builds an existing Program with one statement and one defined target.",
        "pure_correspondence connects actual nested Expr interpretation and Program.collect to independent canonicalFiber.",
        "collect_elaborate uses existing Program.collect_relabel.",
        "Full destination coordinates retain repeated-output off-diagonal empty fibers.",
        "All six runtime fixtures compare real runValidated results with independently evaluated global fibers.",
    ],
    "proof_dependencies": ["propext", "Classical.choice", "Quot.sound"],
    "proof_dependency_note": "Standard Lean/Mathlib proof dependencies only. No new axioms, sorry, unsafe, noncomputable definitions, Classical computational execution, or model witnesses.",
    "observed_fixtures": observations,
    "fixture_donors": {
        "read_policy_and_nested_reductions": "ExpressionTest.direct/nested",
        "collection_and_multiplicity": "CollectionModelTest.vectorProgram/collision",
        "schedule_run_and_observation": "ExecutableReferenceTest.program/schedule/summarize/checkSmoke",
    },
    "mutations": mutations,
    "validation": {
        "target": "+Semantics.SourceCorrespondenceTest",
        "fixture_build": "passed",
        "full_default_build": "passed, 8710 jobs",
        "mutations": "6/6 cycles passed with intended failures and byte-identical restoration",
        "ordered_patch_replay": "passed with temporary index; reconstructed tree equals prototype HEAD",
        "replay_tree": replay_tree,
        "warnings": "Existing imported Semantics warnings remain; no new prototype warnings in successful fixture build.",
        "logs": ["fixtures.log", "full-build.log", "mutations.log", "mutations-summary.txt"],
    },
    "unsupported_items": [
        "UID-keyed dependent valuation-to-Coord equivalence is UNVERIFIED: NamedVal is positional, despite its current name; do not advertise named UID valuation correctness.",
        "Capture-avoiding binder renaming and variable substitution are UNVERIFIED and NOT implemented, even for the admitted reduction fragment.",
        "Source statement permutation preserving tags is UNVERIFIED: only one statement is generated. Existing collect_relabel is used for valuation enumeration, not a multi-statement permutation theorem.",
        "No schedule event-order invariance claim.",
        "Explicit supplied out/bound partitions are checked, not automatically synthesized from a single unordered resolved source context.",
        "No theorem proving raw admission computes the exact source support partition; runtime guards enforce the supplied fragment.",
        "No production TLProgram/Factor adapter or production differential leg: parent owns DSL/Eval audit and probes.",
        "Diagnostics identify UIDs/domains but do not yet carry source statement/term/factor/slot provenance or spans.",
        "Single defined target with every other tensor input; arbitrary supplied roles and multi-statement targets need a later adapter.",
        "Read factors only; optional reciprocal factors omitted. Empty-product identity is core lowering, not an invented DSL source literal.",
        "No affine maps, guards, Iverson factors, marked slices, scans, dimension inference, parser changes, dtype expansion, floats, or backend proof.",
        "No implementation-level mutation coverage; six completed cycles mutate fixture source inputs.",
        "No whole-branch external review was requested or performed for this detached authoring prototype.",
    ],
    "fresh_dispatch_guidance": [
        "Use task patches mechanically; do not transcribe Lean code into a plan.",
        "Complete UID-keyed valuation and scoped substitution seams before labeling the first full slice execution-ready.",
        "Add multi-statement tag-preserving permutation, source-linked provenance, and explicit-role adapter tasks.",
        "Combine parent production audit/probes with this independent core evidence; never hide cross-statement production collection divergence.",
    ],
    "paths_verified": sorted(set(verified_paths)),
    "budget": {
        "turn_limit": "~60",
        "context_peak_limit": "~250k",
        "token_report_attempt": "no transcript for session 57a40649-2fd4-4710-b619-902d9b8b78de",
        "measured_usage": None,
        "breach_detected": False,
        "qualification": "Telemetry unavailable; cannot certify measured cumulative tokens or context peak. Stopped within the visible approximate turn allowance.",
    },
}
(ARTIFACTS / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
print(json.dumps({
    "evidence": str(ARTIFACTS / "evidence.json"),
    "commits": commits,
    "observations": len(observations),
    "mutation_cycles": len(mutations),
    "ordered_replay_tree_verified": replay_tree,
}, indent=2))
