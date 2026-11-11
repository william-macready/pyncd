#!/usr/bin/env python3
"""Rebuild, audit and package the additive bridge/descent prototype."""

import difflib
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEAN = ROOT / "leanncd"
MODULES = (
    "IndexedRankedWitnessBridge",
    "IndexedRankedWitnessDescent",
    "IndexedRankedWitnessAudit",
)
SOURCE = Path("leanncd/experiments/indexed_execution")
LAKE = Path("leanncd/lakefile.toml")


def command(args, log=None):
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    if log is not None:
        (HERE / log).write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f"{args!r}: exit {result.returncode}\n{result.stdout}{result.stderr}")
    return result.stdout + result.stderr


def change(path, old, new):
    header = f"diff --git a/{path} b/{path}\n"
    if old is None:
        header += "new file mode 100644\n"
    return header + "".join(
        difflib.unified_diff(
            [] if old is None else old.splitlines(keepends=True),
            new.splitlines(keepends=True),
            fromfile="/dev/null" if old is None else f"a/{path}",
            tofile=f"b/{path}",
        )
    )


def main():
    head = command(["/usr/bin/git", "-C", str(ROOT), "rev-parse", "HEAD"]).strip()
    if not head.startswith("37500cab"):
        raise RuntimeError(f"unexpected prototype base: {head}")
    build = [
        "bash", str(LEAN / "scripts/lake-build.sh"), str(LEAN),
        "IndexedRankedWitnessBridge", "IndexedRankedWitnessDescent",
    ]
    command(build, "targeted-build.log")
    audit = [
        "bash", str(LEAN / "scripts/lean-file.sh"), str(LEAN),
        str(SOURCE.relative_to("leanncd") / f"{MODULES[2]}.lean"),
    ]
    report = command(audit, "signatures-and-axioms.log")
    axiom_lines = [line for line in report.splitlines() if "depends on axioms:" in line]
    if len(axiom_lines) != 11 or "sorryAx" in report:
        raise RuntimeError("unexpected proof-axiom audit")
    for module in MODULES:
        text = (ROOT / SOURCE / f"{module}.lean").read_text()
        if any(word in text.split() for word in ("sorry", "admit", "axiom")):
            raise RuntimeError(f"placeholder in {module}")

    original_lake = command(
        ["/usr/bin/git", "-C", str(ROOT), "show", f"HEAD:{LAKE}"]
    )
    final_lake = (ROOT / LAKE).read_text()
    middle_lake = final_lake.replace('         "IndexedRankedWitnessDescent",\n', "")
    patches = []
    for index, module in enumerate(MODULES):
        source = SOURCE / f"{module}.lean"
        patch = change(source, None, (ROOT / source).read_text())
        if index == 0:
            patch += change(LAKE, original_lake, middle_lake)
        if index == 1:
            patch += change(LAKE, middle_lake, final_lake)
        path = HERE / f"0{index + 1}-{module}.patch"
        path.write_text(patch)
        patches.append(path)

    # Validate actual git-application in task order, without touching prototype sources.
    validation = HERE / "patch-validation"
    if validation.exists():
        raise RuntimeError(f"refusing to overwrite {validation}")
    (validation / LAKE).parent.mkdir(parents=True)
    (validation / LAKE).write_text(original_lake)
    try:
        for patch in patches:
            prefix = str(validation.relative_to(ROOT))
            command(["/usr/bin/git", "-C", str(ROOT), "apply", "--check",
                     f"--directory={prefix}", str(patch)])
            command(["/usr/bin/git", "-C", str(ROOT), "apply",
                     f"--directory={prefix}", str(patch)])
        compared = [LAKE] + [SOURCE / f"{module}.lean" for module in MODULES]
        for path in compared:
            if (validation / path).read_bytes() != (ROOT / path).read_bytes():
                raise RuntimeError(f"patch round-trip differs: {path}")
    finally:
        shutil.rmtree(validation)

    paths = [LAKE] + [SOURCE / f"{module}.lean" for module in MODULES]
    hashes = {
        str(path): hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        for path in paths
    }
    evidence = {
        "base": head,
        "build_command": build,
        "build_exit": 0,
        "audit_command": audit,
        "audit_exit": 0,
        "axiom_audits": axiom_lines,
        "patches": [path.name for path in patches],
        "patch_application": "git apply --check then apply, in order; byte-equal to compiled sources",
        "source_sha256": hashes,
        "fixtures": "none added in this bounded proof prototype",
        "mutation_cycles": "not run; no new runtime/regression fixtures",
    }
    (HERE / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"PASS: targeted split build; {len(axiom_lines)} axiom audits; "
          f"{len(patches)} ordered patches byte-verified")


if __name__ == "__main__":
    main()
