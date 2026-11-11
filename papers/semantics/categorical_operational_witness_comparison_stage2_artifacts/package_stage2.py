#!/usr/bin/env python3
"""Compile and replay the three additive comparison-stage patches."""

import difflib
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEAN = ROOT / "leanncd"
SOURCE = Path("leanncd/experiments/indexed_execution")
LAKE = Path("leanncd/lakefile.toml")
MODULES = (
    "IndexedRankedWitnessComparison",
    "IndexedRankedWitnessSource",
    "IndexedRankedWitnessOutcomes",
)
AUDIT = "IndexedRankedWitnessStage2Audit"
PREVIOUS = HERE.parent / "categorical_operational_witness_comparison_artifacts"


def command(args, log=None):
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    text = result.stdout + result.stderr
    if log:
        (HERE / log).write_text(text)
    if result.returncode:
        start = text.find("error:")
        print(text[start:] if start >= 0 else text[-5000:])
        raise SystemExit(result.returncode)
    print(f"exit 0: {' '.join(map(str, args))}")
    return text


def change(path, old, new):
    return (
        f"diff --git a/{path} b/{path}\n"
        + ("new file mode 100644\n" if old is None else "")
        + "".join(difflib.unified_diff(
            [] if old is None else old.splitlines(keepends=True),
            new.splitlines(keepends=True),
            fromfile="/dev/null" if old is None else f"a/{path}",
            tofile=f"b/{path}",
        ))
    )


def main():
    build = ["bash", str(LEAN / "scripts/lake-build.sh"), str(LEAN), *MODULES]
    command(build, "targeted-build.log")
    if "--build-only" in sys.argv:
        return
    audit = ["bash", str(LEAN / "scripts/lean-file.sh"), str(LEAN),
             str(SOURCE.relative_to("leanncd") / f"{AUDIT}.lean")]
    report = command(audit, "signatures-and-axioms.log")
    if "sorryAx" in report:
        raise RuntimeError("placeholder axiom in audit")
    head = command(["/usr/bin/git", "-C", str(ROOT), "rev-parse", "HEAD"]).strip()
    if not head.startswith("37500cab"):
        raise RuntimeError(f"unexpected base: {head}")
    original_lake = command(["/usr/bin/git", "-C", str(ROOT), "show", f"HEAD:{LAKE}"])
    final_lake = (ROOT / LAKE).read_text()
    baseline = final_lake
    for module in MODULES:
        baseline = baseline.replace(f'         "{module}",\n', "")
    patches = []
    current = baseline
    for index, module in enumerate(MODULES):
        source = SOURCE / f"{module}.lean"
        text = (ROOT / source).read_text()
        if any(word in text.split() for word in ("sorry", "admit", "axiom")):
            raise RuntimeError(f"placeholder in {module}")
        patch = change(source, None, text)
        anchor = "IndexedRankedWitnessDescent" if index == 0 else MODULES[index - 1]
        updated = current.replace(f'         "{anchor}",\n',
                                  f'         "{anchor}",\n         "{module}",\n')
        patch += change(LAKE, current, updated)
        current = updated
        if index == 2:
            audit_path = SOURCE / f"{AUDIT}.lean"
            patch += change(audit_path, None, (ROOT / audit_path).read_text())
        path = HERE / f"0{index + 4}-{module}.patch"
        path.write_text(patch)
        patches.append(path)
    if current != final_lake:
        raise RuntimeError("registration reconstruction differs")
    previous_patches = [PREVIOUS / name for name in (
        "01-IndexedRankedWitnessBridge.patch",
        "02-IndexedRankedWitnessDescent.patch",
        "03-IndexedRankedWitnessAudit.patch",
    )]
    validation = HERE / "patch-validation"
    if validation.exists():
        raise RuntimeError(f"refusing to overwrite {validation}")
    (validation / LAKE).parent.mkdir(parents=True)
    (validation / LAKE).write_text(original_lake)
    old_modules = ("IndexedRankedWitnessBridge", "IndexedRankedWitnessDescent",
                   "IndexedRankedWitnessAudit")
    paths = [LAKE] + [SOURCE / f"{name}.lean"
                     for name in (*old_modules, *MODULES, AUDIT)]
    try:
        prefix = str(validation.relative_to(ROOT))
        for patch in previous_patches + patches:
            command(["/usr/bin/git", "-C", str(ROOT), "apply", "--check",
                     f"--directory={prefix}", str(patch)])
            command(["/usr/bin/git", "-C", str(ROOT), "apply",
                     f"--directory={prefix}", str(patch)])
        for path in paths:
            if (validation / path).read_bytes() != (ROOT / path).read_bytes():
                raise RuntimeError(f"replay differs: {path}")
    finally:
        shutil.rmtree(validation)
    evidence = {
        "base": head, "build_command": build, "build_exit": 0,
        "audit_command": audit, "audit_exit": 0,
        "axiom_audits": [line for line in report.splitlines()
                         if "depends on axioms:" in line],
        "patches": [str(path.relative_to(ROOT)) for path in previous_patches + patches],
        "patch_replay": "git apply --check and apply in order; all eight files byte-equal",
        "source_sha256": {str(path): hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                          for path in paths},
    }
    (HERE / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print("All six patches replayed; all eight source files byte-equal.")


if __name__ == "__main__":
    main()
