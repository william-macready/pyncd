#!/usr/bin/env python3
"""Real-split verification of the F32-D plan: every edit applied to FULL copies of the real modules
(real namespace, real module split, real headers), imports rewritten to the copies, compiled in
dependency order to a private LEAN_PATH. Outputs only under leanncd/spikes/ (gitignored)."""
import os, re, subprocess, sys
REPO = "/Users/williammacready/code/python/pyncd"; LN = REPO + "/leanncd"; SP = LN + "/spikes"
OL = SP + "/f32d_rv_olean"; os.makedirs(OL, exist_ok=True)
plan = open(REPO + "/papers/f32d_evalplan.md").read()
B = dict(re.findall(r"<!-- block:([\w-]+) -->\n```lean\n(.*?)```\n", plan, re.S))
def rep(s, old, new, tag):
    n = s.count(old)
    if n != 1: print(f"ANCHOR {tag}: count={n}: {old[:100]!r}"); sys.exit(2)
    return s.replace(old, new)
def rd(p): return open(LN + "/" + p).read()
PROD = ["Check", "Dense", "Block", "Scan", "EvalPlan", "Dense32", "Prepared", "Compile", "Adapter", "Adapter32"]
TESTS = ["KernelCheckTest", "KernelDenseTest", "KernelDense32Test", "ScatterDenseTest", "ScatterDense32Test",
         "GraphCheckTest", "EvalPlan32Test", "CompileTest", "Scatter32OracleTest"]
def fix_imports(s):
    for m in PROD: s = re.sub(rf"^import LeanNCD\.Eval\.Plan\.{m}\b", f"import F32DRV_{m}", s, flags=re.M)
    for t in TESTS: s = re.sub(rf"^import Eval\.Plan\.{t}\b", f"import F32DRV_{t}", s, flags=re.M)
    return s
src = {m: rd(f"LeanNCD/Eval/Plan/{m}.lean") for m in PROD}
# ---- Task 1
c = src["Check"]
i = c.index("/-- Evidence that one `ScatterPlan` satisfies every local invariant.")
j = c.index("  deriving Repr\n", i) + len("  deriving Repr\n")
c = c[:i] + B["t1-checked"] + c[j:]
c = rep(c, "def checkScatter (sigs : Array TensorSignature) (s : ScatterPlan) :\n    Except PlanError CheckedScatterPlan := do\n  let _ ← checkAssign sigs s.compute (some s.destShape)\n", B["t1-core-head"], "t1-head")
c = rep(c, "  return CheckedScatterPlan.mk s\n", B["t1-core-tail"], "t1-tail"); src["Check"] = c
d = src["Dense"]
i = d.index("def runDenseScatter (c : CheckedScatterPlan) (store : Array DenseTensor) :")
j = d.index("  return { shape := destShape, data := data }\n", i) + len("  return { shape := destShape, data := data }\n")
src["Dense"] = d[:i] + B["t1-dense"] + d[j:]
# ---- Task 2
e = src["EvalPlan"]
e = rep(e, "      | .scatter _   => throw (.f32UnsupportedStep ni .scatter)\n", B["t2-cap"], "t2-cap")
e = rep(e, "          | .scatter s =>\n              match checkScatter raw.tensorSigs s with\n              | .error e => throw (.assign (.nodeError ni e))\n", B["t2-local"], "t2-local")
src["EvalPlan"] = e
src["Dense32"] = rep(src["Dense32"], "    | .scatter _ => throw (.storageKindMismatch .float32 .float64)\n", B["t2-dense32"], "t2-d32")
# ---- Task 3
k = src["Compile"]
i = k.index("/-- One top-level statement's binary32 capability check"); j = k.index("  | .assign _ _ _ => pure ()\n\n", i) + len("  | .assign _ _ _ => pure ()\n\n")
k = k[:i] + k[j:]
i = k.index("/-- The whole-schedule binary32 capability pass"); j = k.index("    | .scanPre nm .. => throw (.unsupportedDtype s!\"{nm}: f32 scan\")\n", i) + len("    | .scanPre nm .. => throw (.unsupportedDtype s!\"{nm}: f32 scan\")\n")
k = k[:i] + B["t3-cap"] + k[j:]
k = rep(k, "    -- unreachable: only a `.float32` schedule selects an f32 algebra, and Step 0c (`checkF32Stmt`)\n    -- refuses every f32 top-level scatter as `unsupportedDtype \"{nm}: f32 scatter\"` before Step D\n    | .f32 _    => false\n", B["t3-fill"], "t3-fill")
src["Compile"] = k
for m in PROD: open(f"{SP}/F32DRV_{m}.lean", "w").write(fix_imports(src[m]))
# ---- tests
T = {t: rd(f"test/Eval/Plan/{t}.lean") for t in ["KernelCheckTest", "KernelDenseTest", "KernelDense32Test", "ScatterDenseTest", "GraphCheckTest", "EvalPlan32Test", "CompileTest"]}
T["ScatterDense32Test"] = open(REPO + "/papers/f32d_files/ScatterDense32Test.lean").read()
T["Scatter32OracleTest"] = open(REPO + "/papers/f32d_files/Scatter32OracleTest.lean").read()
g = T["GraphCheckTest"]
g = rep(g, "#guard errOf (checkPlan f32UnsupportedStepOrder) == some (.f32UnsupportedStep 2 .scatter)\n", B["t2-g14"], "g14")
g = rep(g, "#guard errOf (checkPlan f32ScatterPlan) == some (.f32UnsupportedStep 0 .scatter)\n", B["t2-g16"], "g16")
g = rep(g, "#guard !(isF32Unsupported 0 .scatter (checkPlan\n  { f32ScatterPlan with\n    tensorSigs := #[ { shape := #[3], dtype := .f64 }, { shape := #[6], dtype := .f64 } ] }))\n", "", "g16-del")
g = rep(g, "-- Axiswise.", B["t2-g14c"] + "\n-- Axiswise.", "g14c")
T["GraphCheckTest"] = g
v = T["EvalPlan32Test"]
v = rep(v, "import Eval.Plan.KernelDense32Test", "import Eval.Plan.GraphCheckTest\nimport Eval.Plan.KernelDense32Test", "e32-imp")
v = rep(v, "open LeanNCD.Eval.Plan.KernelDense32Test (t32)\n", "open LeanNCD.Eval.Plan.KernelDense32Test (t32)\nopen LeanNCD.Eval.Plan.GraphCheckTest (f32ScatterPlan f32UnsupportedStepOrder)\n", "e32-open")
i = v.rindex("end LeanNCD.Eval.Plan.EvalPlan32Test"); v = v[:i] + B["t2-evalplan32"] + "\n" + v[i:]
T["EvalPlan32Test"] = v
ct = T["CompileTest"]
ct = rep(ct, "#guard causeOf (prepareEvalPlan f32ScatterProg f32IdentitySig) ==\n  some { cause := .capability (.unsupportedDtype \"Y: f32 scatter\"), warnings := [] }\n", B["t3-15c"] + "\n" + B["t3-15c-refuse"], "15c")
ct = rep(ct, "#guard causeOf (prepareEvalPlan f32ScatterThenScanProg f32IdentitySig) ==\n  some { cause := .capability (.unsupportedDtype \"Y: f32 scatter\"), warnings := [] }\n",
         "#guard causeOf (prepareEvalPlan f32ScatterThenScanProg f32IdentitySig) ==\n  some { cause := .capability (.unsupportedDtype \"S: f32 scan\"), warnings := [] }\n", "29fwd")
rev = "#guard causeOf (prepareEvalPlan f32ScanThenScatterProg f32IdentitySig) ==\n  some { cause := .capability (.unsupportedDtype \"S: f32 scan\"), warnings := [] }\n"
ct = rep(ct, rev, rev + "\n" + B["t3-29"], "29rev")
i = ct.index("run_cmd do\n  match prepareEvalPlan f32ScatterReluProg f32IdentitySig with")
j = ct.index("  | .ok _ => throwError \"fixture FW2a: accepted an f32 scatter\"\n", i) + len("  | .ok _ => throwError \"fixture FW2a: accepted an f32 scatter\"\n")
ct = ct[:i] + B["t3-fw2"] + ct[j:]
T["CompileTest"] = ct
for t in TESTS: open(f"{SP}/F32DRV_{t}.lean", "w").write(fix_imports(T[t]))
print("files written")
ORDER = ["Check", "Dense", "Block", "Scan", "EvalPlan", "Dense32", "Prepared", "Compile", "Adapter", "Adapter32",
         "KernelCheckTest", "KernelDenseTest", "KernelDense32Test", "ScatterDenseTest", "ScatterDense32Test",
         "GraphCheckTest", "EvalPlan32Test", "CompileTest", "Scatter32OracleTest"]
only = sys.argv[1:]
lake = os.path.expanduser("~/.elan/bin/lake")
for m in ORDER:
    if only and m not in only: continue
    r = subprocess.run([lake, "env", "bash", "-c", f"LEAN_PATH=$LEAN_PATH:{OL} lean -o {OL}/F32DRV_{m}.olean spikes/F32DRV_{m}.lean"],
                       cwd=LN, capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip()
    errs = [l for l in out.splitlines() if "error" in l]
    print(f"== {m}: exit {r.returncode}", *errs[:8], sep="\n  ", flush=True)
    if r.returncode: print(out[:2500]); sys.exit(1)
print("ALL COMPILED")
