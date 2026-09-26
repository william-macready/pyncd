#!/usr/bin/env python3
"""Run manifest mutations against rv_build's real-split copies (leanncd/spikes/F32DRV_*.lean).
Run rv_build.py first (clean oleans in f32d_rv_olean). Each mutation compiles the mutated module
and its dependents into a private dir shadowing the clean oleans; the clean tree is never touched.
Usage: mut_run.py <manifest.json> [label-prefix...]   -> prints per-entry: modules failed, error
heads, and whether each `expect` string (if any) appears in the combined log."""
import json, os, re, shutil, subprocess, sys
LN = "/Users/williammacready/code/python/pyncd/leanncd"; SP = LN + "/spikes"; OL = SP + "/f32d_rv_olean"
lake = os.path.expanduser("~/.elan/bin/lake")
ORDER = ["Check", "Dense", "Block", "Scan", "EvalPlan", "Dense32", "Prepared", "Compile", "Adapter", "Adapter32",
         "KernelCheckTest", "KernelDenseTest", "KernelDense32Test", "ScatterDenseTest", "ScatterDense32Test",
         "GraphCheckTest", "EvalPlan32Test", "CompileTest", "Scatter32OracleTest"]
imps = {m: set(re.findall(r"^import F32DRV_(\w+)", open(f"{SP}/F32DRV_{m}.lean").read(), re.M)) for m in ORDER}
def deps_on(m, x, seen=None):
    return x in imps[m] or any(deps_on(i, x) for i in imps[m])
man = json.load(open(sys.argv[1])); pre = sys.argv[2:]
for e in man:
    if pre and not any(e["label"].startswith(p) for p in pre): continue
    mod = os.path.basename(e["file"])[:-5]
    tg = [t.split(".")[-1] for t in e["targets"]]
    path = f"{SP}/F32DRV_{mod}.lean"; clean = open(path).read()
    assert clean.count(e["old"]) == 1, (e["label"], clean.count(e["old"]))
    open(path, "w").write(clean.replace(e["old"], e["new"]))
    OM = SP + "/f32d_mut_olean"; shutil.rmtree(OM, ignore_errors=True); os.makedirs(OM)
    need = [m for m in ORDER if m == mod or (deps_on(m, mod) and any(m == t or deps_on(t, m) for t in tg))]
    failed, log = set(), ""
    try:
        for m in need:
            if imps[m] & failed: failed.add(m); continue
            r = subprocess.run([lake, "env", "bash", "-c", f"LEAN_PATH={OM}:$LEAN_PATH:{OL} lean -o {OM}/F32DRV_{m}.olean spikes/F32DRV_{m}.lean"],
                               cwd=LN, capture_output=True, text=True)
            out = r.stdout + r.stderr; log += f"\n=== {m}\n" + out
            if r.returncode: failed.add(m)
    finally:
        open(path, "w").write(clean)
    open(f"{SP}/mut_{re.sub(r'[^A-Za-z0-9]', '_', e['label'].split()[0])}.log", "w").write(log)
    heads = [l for l in log.splitlines() if re.search(r"error", l)]
    print(f"## {e['label']}\n  built: {need}\n  failed: {[m for m in need if m in failed]}")
    for h in heads[:14]: print("   ", h[:230])
    for x in e.get("expect", []): print(f"  expect {'OK ' if x in log else 'MISSING'}: {x}")
