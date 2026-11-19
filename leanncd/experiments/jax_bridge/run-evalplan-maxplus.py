#!/usr/bin/env python3
"""Generate checked/source fixtures and verify JAX max-plus in both precisions. No installs."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("--python", default=sys.executable, help="existing JAX Python environment")
parser.add_argument("--out-dir", type=Path, default=HERE / ".cache/maxplus")
parser.add_argument("--checked-only", action="store_true", help="T2 checked fixtures before source integration")
args = parser.parse_args()
out = args.out_dir.resolve()
out.mkdir(parents=True, exist_ok=True)
commands = []


def run(command, name):
    p = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    (out / (name + ".log")).write_text(p.stdout + p.stderr)
    commands.append({"command": command, "cwd": str(ROOT), "exit_code": p.returncode,
                     "log": name + ".log"})
    (out / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
    if p.returncode:
        print(p.stdout, p.stderr)
        raise SystemExit(p.returncode)
    print(p.stdout.strip())


run(["bash", str(ROOT / "scripts/lake-build.sh"), str(ROOT), "JaxExperiment",
     "Eval.Plan.ScanJaxGateTest"], "build")
lake = str(Path.home() / ".elan/bin/lake")
drivers = [("EvalPlanMaxPlusSmoke.lean", "checked.py")]
if not args.checked_only:
    drivers.insert(0, ("EvalPlanLogicSmoke.lean", "logic.py"))
for driver, target in drivers:
    run([lake, "env", "lean", "--run", str(HERE / driver), str(out / target)], driver)
for precision in (64, 32):
    bundle = HERE / ".cache" / f"generated_evalplan_maxplus_smoke{precision}.py"
    logic = ("None" if args.checked_only else
             f"Path(__file__).parent / {os.path.relpath(out / 'logic.py', bundle.parent)!r}")
    bundle.write_text(
        "from pathlib import Path\n"
        f"CHECKED_PATH = Path(__file__).parent / {os.path.relpath(out / 'checked.py', bundle.parent)!r}\n"
        f"LOGIC_PATH = {logic}\n")
    argv = ["evalplan_maxplus_smoke.py", f"float{precision}", str(bundle),
            "--out", str(out / f"result{precision}.json")]
    code = ("import runpy,sys; sys.path.insert(0," + repr(str(HERE)) +
            "); sys.argv=" + repr(argv) +
            "; runpy.run_module('evalplan_maxplus_smoke',run_name='__main__')")
    run([args.python, "-c", code], f"runtime{precision}")
