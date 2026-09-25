#!/usr/bin/env python3
"""Rebuild the F32-D prototype FROM THE PLAN'S OWN BLOCKS and compile every test block.

1. Extract `<!-- block:NAME -->` lean blocks from papers/f32d_evalplan.md.
2. Apply them to namespace-renamed copies of the real sources (namespace LeanNCD.Eval.Plan.P).
3. Compile the three prototype modules to spikes/f32d_olean.
4. Run check-snippet.sh (with LEAN_PATH += f32d_olean) on: the Task 1 test file, the Task 2
   re-point harness, the Task 3 oracle file, the Task 3 CompileTest harness.
5. Compile the oracle against the REAL tree and require its red message.
"""
import os, re, subprocess, sys

REPO = "/Users/williammacready/code/python/pyncd"
LN = REPO + "/leanncd"
SP = LN + "/spikes"
OL = SP + "/f32d_olean"
plan = open(REPO + "/papers/f32d_evalplan.md").read()
blocks = dict(re.findall(r"<!-- block:([\w-]+) -->\n```lean\n(.*?)```\n", plan, re.S))
print("blocks:", sorted(blocks))

def src(rel, a, b):  # 1-based inclusive line range
    return "".join(open(LN + "/" + rel).readlines()[a - 1:b])

def body(rel):  # text strictly between `namespace LeanNCD.Eval.Plan` and `end LeanNCD.Eval.Plan`
    s = open(LN + "/" + rel).read()
    i = s.index("namespace LeanNCD.Eval.Plan\n") + len("namespace LeanNCD.Eval.Plan\n")
    j = s.rindex("end LeanNCD.Eval.Plan")
    return s[i:j]

def rep(s, old, new):
    assert s.count(old) == 1, (s.count(old), old[:90])
    return s.replace(old, new)

def cut(s, start, end_incl):
    i = s.index(start); j = s.index(end_incl, i) + len(end_incl)
    return s, i, j

# ---- proto 1: Check + Dense
check = body("LeanNCD/Eval/Plan/Check.lean")
s, i, j = cut(check, "/-- Evidence that one `ScatterPlan` satisfies every local invariant.",
              "structure CheckedScatterPlan where private mk ::\n  raw : ScatterPlan\n  deriving Repr\n")
check = s[:i] + blocks["t1-checked"] + s[j:]
check = rep(check, "def checkScatter (sigs : Array TensorSignature) (s : ScatterPlan) :\n"
                   "    Except PlanError CheckedScatterPlan := do\n"
                   "  let _ ← checkAssign sigs s.compute (some s.destShape)\n", blocks["t1-core-head"])
check = rep(check, "  return CheckedScatterPlan.mk s\n", blocks["t1-core-tail"])
dense = body("LeanNCD/Eval/Plan/Dense.lean")
s, i, j = cut(dense, "def runDenseScatter (c : CheckedScatterPlan) (store : Array DenseTensor) :",
              "  return { shape := destShape, data := data }\n")
dense = s[:i] + blocks["t1-dense"] + s[j:]
open(SP + "/F32DProto.lean", "w").write(
    "import LeanNCD.Eval.Tensor\nimport LeanNCD.Eval.Plan.Check\nimport LeanNCD.Eval.Plan.Coordinates\n\n"
    "namespace LeanNCD.Eval.Plan.P\n" + check + dense + "end LeanNCD.Eval.Plan.P\n")

# ---- proto 2: EvalPlan + Dense32
ev = body("LeanNCD/Eval/Plan/EvalPlan.lean")
ev = rep(ev, "      | .scatter _   => throw (.f32UnsupportedStep ni .scatter)\n", blocks["t2-cap"])
ev = rep(ev, "          | .scatter s =>\n              match checkScatter raw.tensorSigs s with\n"
             "              | .error e => throw (.assign (.nodeError ni e))\n", blocks["t2-local"])
d32 = body("LeanNCD/Eval/Plan/Dense32.lean")
d32 = rep(d32, "    | .scatter _ => throw (.storageKindMismatch .float32 .float64)\n", blocks["t2-dense32"])
open(SP + "/F32DProto2.lean", "w").write(
    "import LeanNCD.Eval.Plan.EvalPlan\nimport F32DProto\n\nnamespace LeanNCD.Eval.Plan.P\n"
    + ev + d32 + "end LeanNCD.Eval.Plan.P\n")

# ---- proto 3: Prepared + Compile + Adapter + Adapter32
comp = body("LeanNCD/Eval/Plan/Compile.lean")
s, i, j = cut(comp, "/-- One top-level statement's binary32 capability check",
              "  | .assign _ _ _ => pure ()\n\n")
comp = s[:i] + s[j:]
s, i, j = cut(comp, "/-- The whole-schedule binary32 capability pass",
              "    | .scanPre nm .. => throw (.unsupportedDtype s!\"{nm}: f32 scan\")\n")
comp = s[:i] + blocks["t3-cap"] + s[j:]
comp = rep(comp, "    -- unreachable: only a `.float32` schedule selects an f32 algebra, and Step 0c (`checkF32Stmt`)\n"
                 "    -- refuses every f32 top-level scatter as `unsupportedDtype \"{nm}: f32 scatter\"` before Step D\n"
                 "    | .f32 _    => false\n", blocks["t3-fill"])
assert "checkF32Stmt s" not in comp
open(SP + "/F32DProto3.lean", "w").write(
    "import F32DProto2\nimport LeanNCD.Eval.Plan.Adapter32\n\nnamespace LeanNCD.Eval.Plan.P\n"
    + body("LeanNCD/Eval/Plan/Prepared.lean") + comp + "open LeanNCD.Eval Std\n"
    + body("LeanNCD/Eval/Plan/Adapter.lean").replace("open LeanNCD.Eval Std\n", "", 1)
    + body("LeanNCD/Eval/Plan/Adapter32.lean").replace("open LeanNCD.Eval Std\n", "", 1)
    + "end LeanNCD.Eval.Plan.P\n")

env = dict(os.environ, LEAN_PATH=OL)
lake = os.path.expanduser("~/.elan/bin/lake")
os.makedirs(OL, exist_ok=True)
for m in ["F32DProto", "F32DProto2", "F32DProto3"]:
    r = subprocess.run([lake, "env", "bash", "-c",
                        f"LEAN_PATH=$LEAN_PATH:{OL} lean -o {OL}/{m}.olean spikes/{m}.lean"],
                       cwd=LN, capture_output=True, text=True)
    errs = [l for l in (r.stdout + r.stderr).splitlines() if "error" in l]
    print(f"proto {m}: exit {r.returncode}", *errs[:10], sep="\n  ")
    if r.returncode: sys.exit(1)

def snippet(name, text):
    path = SP + f"/f32d_check_{name}.lean"
    open(path, "w").write(text)
    r = subprocess.run(["bash", REPO + "/.claude/skills/slice-plan/check-snippet.sh", path],
                       cwd=REPO, env=env, capture_output=True, text=True)
    print(f"--- check-snippet {name} (exit {r.returncode})\n" + (r.stdout + r.stderr).strip())
    return r.returncode

rc = 0
t1 = open(REPO + "/papers/f32d_files/ScatterDense32Test.lean").read()
t1 = rep(t1, "import LeanNCD.Eval.Plan.Dense\n", "import F32DProto\n")
t1 = t1.replace("LeanNCD.Eval.Plan.ScatterDense32Test", "LeanNCD.Eval.Plan.P.ScatterDense32Test")
rc |= snippet("t1", t1)

t2 = """import F32DProto2
import Eval.Plan.GraphCheckTest
import Eval.Plan.KernelDense32Test
namespace LeanNCD.Eval.Plan.P.T2
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan
open LeanNCD.Eval.Plan.GraphCheckTest (f32ScatterPlan f32UnsupportedStepOrder f32Scan stepOrderScatter idNode)
open LeanNCD.Eval.Plan.KernelDense32Test (t32)
-- P-typed copies of the GraphCheckTest / EvalPlan32Test helpers, same text
def errOf : Except PlanStepError CheckedEvalPlan → Option PlanStepError
  | .ok _ => none | .error e => some e
def storageOf : Except PlanStepError CheckedEvalPlan → Option LeanNCD.StorageKind
  | .ok c => some c.storageKind | .error _ => none
def isF32Unsupported (i : Nat) (k : PlanStepKind) : Except PlanStepError CheckedEvalPlan → Bool
  | .error (.f32UnsupportedStep i' k') => i == i' && k == k'
  | _ => false
def runGraph32 (raw : RawEvalPlan) (inputs : Array DenseTensor32) :
    Except String (Array DenseTensor32) :=
  match checkPlan raw with
  | .error e => .error s!"check failed: {repr e}"
  | .ok c => match runDensePlan32 c inputs with
             | .error e => .error s!"run failed: {repr e}"
             | .ok store => .ok store
def bitsAt (store : Except String (Array DenseTensor32)) (slot : TensorSlot) :
    Option (Array UInt32) :=
  match store with
  | .error _ => none
  | .ok s => (s[slot]?).map (fun t => t.data.map Float32.toBits)
""" + blocks["t2-g14"] + blocks["t2-g16"] + blocks["t2-g14c"] + blocks["t2-evalplan32"] + \
    "end LeanNCD.Eval.Plan.P.T2\n"
rc |= snippet("t2", t2)

orc = open(REPO + "/papers/f32d_files/Scatter32OracleTest.lean").read()
orcP = rep(orc, "import LeanNCD.Eval.Plan.Adapter32\n", "import F32DProto3\n")
orcP = orcP.replace("LeanNCD.Eval.Plan.Scatter32OracleTest", "LeanNCD.Eval.Plan.P.Scatter32OracleTest")
rc |= snippet("t3oracle", orcP)

t3 = """import F32DProto3
import Eval.Plan.CompileTest
namespace LeanNCD.Eval.Plan.P.T3
open LeanNCD LeanNCD.Eval.Plan Std
open LeanNCD.Eval.Plan.CompileTest (f32ScatterProg f32IdentitySig f32ScatterThenScanProg
  f32ScanThenScatterProg f32ScatterReluProg f32ScanProg f32ScanSig errOf)
def causeOf (r : Except PlanCompileFailure PreparedPlan) : Option PlanCompileFailure :=
  match r with | .ok _ => none | .error e => some e
-- 2.9's edited forward guard, and its unchanged reverse guard
#guard causeOf (prepareEvalPlan f32ScatterThenScanProg f32IdentitySig) ==
  some { cause := .capability (.unsupportedDtype "S: f32 scan"), warnings := [] }
#guard causeOf (prepareEvalPlan f32ScanThenScatterProg f32IdentitySig) ==
  some { cause := .capability (.unsupportedDtype "S: f32 scan"), warnings := [] }
""" + blocks["t3-15c"] + blocks["t3-29"] + blocks["t3-fw2"] + "end LeanNCD.Eval.Plan.P.T3\n"
rc |= snippet("t3compile", t3)

# red: the oracle against the REAL, unmodified tree
red = orc.replace("LeanNCD.Eval.Plan.Scatter32OracleTest", "LeanNCD.Eval.Plan.Scatter32OracleRed")
open(SP + "/f32d_red.lean", "w").write(red)
r = subprocess.run([lake, "env", "lean", "spikes/f32d_red.lean"], cwd=LN, capture_output=True, text=True)
redmsg = [l for l in (r.stdout + r.stderr).splitlines() if "error" in l]
print("--- oracle on the real tree (must be red):", *redmsg, sep="\n  ")
want = "BINARY32 SCATTER ORACLE FAILED: O1 strided, unary, carrier-discriminating: prepare failed"
if not (r.returncode != 0 and len(redmsg) == 1 and want in redmsg[0]):
    print("RED CHECK FAILED"); rc = 1
print("ALL OK" if rc == 0 else "FAILURES")
sys.exit(rc)
