#!/usr/bin/env python3
"""Build acceptance donors and mechanically package three additive task patches."""

import difflib
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEAN = ROOT / "leanncd"
SOURCE = Path("leanncd/experiments/indexed_execution")
LAKE = Path("leanncd/lakefile.toml")
MODULES = (
    "IndexedRankedWitnessOutcomeTest",
    "IndexedRankedWitnessCategoryTest",
    "IndexedRankedWitnessBoundaryTest",
    "IndexedRankedWitnessSemantics",
)


def command(args, log=None):
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    text = result.stdout + result.stderr
    if log:
        (HERE / log).write_text(text)
    if result.returncode:
        print(text[-12000:])
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
    targeted = ["bash", str(LEAN / "scripts/lake-build.sh"), str(LEAN), *MODULES]
    log = command(targeted, "targeted-build.log")
    if "sorryAx" in log:
        raise RuntimeError("placeholder axiom in compiled audit")
    full = ["bash", str(LEAN / "scripts/lake-build.sh"), str(LEAN),
            "LeanNCD", "Tests", "IndexedExecutionExperiment"]
    full_log = command(full, "full-build.log")
    if "sorryAx" in full_log:
        raise RuntimeError("placeholder axiom in full build")
    command(["/usr/bin/git", "-C", str(ROOT), "diff", "--check"])
    head = command(["/usr/bin/git", "-C", str(ROOT), "rev-parse", "HEAD"]).strip()
    if not head.startswith("37500cab"):
        raise RuntimeError(f"unexpected base: {head}")
    final = (ROOT / LAKE).read_text()
    baseline = final
    for module in MODULES:
        baseline = baseline.replace(f'         "{module}",\n', "")
    current = baseline
    patches = []
    for index, module in enumerate(MODULES[:3]):
        names = [module] if index < 2 else [module, MODULES[3]]
        patch = ""
        for name in names:
            path = SOURCE / f"{name}.lean"
            source = (ROOT / path).read_text()
            if any(word in source.split() for word in ("sorry", "admit", "axiom")):
                raise RuntimeError(f"placeholder in {name}")
            patch += change(path, None, source)
        anchor = "IndexedRankedWitnessOutcomes" if index == 0 else MODULES[index - 1]
        registrations = "".join(f'         "{name}",\n' for name in names)
        updated = current.replace(f'         "{anchor}",\n',
                                  f'         "{anchor}",\n{registrations}')
        patch += change(LAKE, current, updated)
        current = updated
        path = HERE / f"0{index + 7}-{module}.patch"
        path.write_text(patch)
        patches.append(path)
    if current != final:
        raise RuntimeError("registration replay differs")
    validation = HERE / "patch-validation"
    if validation.exists():
        raise RuntimeError(f"refusing to overwrite {validation}")
    (validation / LAKE).parent.mkdir(parents=True)
    (validation / LAKE).write_text(baseline)
    checks = []
    try:
        prefix = str(validation.relative_to(ROOT))
        for patch in patches:
            check = ["/usr/bin/git", "-C", str(ROOT), "apply", "--check",
                     f"--directory={prefix}", str(patch)]
            command(check)
            checks.append(check)
            command(["/usr/bin/git", "-C", str(ROOT), "apply",
                     f"--directory={prefix}", str(patch)])
        for path in [LAKE, *[SOURCE / f"{name}.lean" for name in MODULES]]:
            if (validation / path).read_bytes() != (ROOT / path).read_bytes():
                raise RuntimeError(f"replay differs: {path}")
    finally:
        shutil.rmtree(validation)
    paths = [LAKE, *sorted(SOURCE / path.name for path in (ROOT / SOURCE).glob(
        "IndexedRankedWitness*.lean"))]
    evidence = {
        "base": head,
        "build_commands": [targeted, full],
        "build_exits": [0, 0],
        "patch_baseline": "Existing Bridge/Descent/Comparison/Source/Outcomes stage2, not bare main",
        "patch_checks": checks,
        "source_sha256": {str(path): hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                          for path in paths},
        "patch_sha256": {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in patches},
        "audits": [line for line in log.splitlines()
                   if "IndexedRankedWitness" in line and "axioms:" in line],
        "observations": [line for line in log.splitlines()
                         if "info: experiments/indexed_execution/IndexedRankedWitness" in line
                         and "axioms" not in line],
        "mutations_run": False,
    }
    (HERE / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    stray = ROOT / "acceptance-build.log"
    if stray.exists():
        stray.unlink()
    print(f"Packaged {len(patches)} replay-checked patches; targeted and full builds green.")


if __name__ == "__main__":
    main()
