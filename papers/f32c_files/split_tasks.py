#!/usr/bin/env python3
"""Split the f32c-proto prototype commit into three cumulative task commits on branch f32c-tasks
(from base 49c1ed6) and emit papers/f32c_files/task{1,2,3}.patch. Mechanical: every file content
comes from the prototype commit's tree (git show), the test file is cut at its Part markers."""
import subprocess, sys, os
WT = "/Users/williammacready/code/python/pyncd/.claude/worktrees/f32c-scans-plan"
BASE, PROTO = sys.argv[1], sys.argv[2]
G = ["/usr/bin/git", "-C", WT]
def sh(*a, **k): return subprocess.run(G + list(a), check=True, capture_output=True, text=True, **k).stdout
def show(path): return sh("show", f"{PROTO}:{path}")
T = "leanncd/test/Eval/Plan/ScanDense32Test.lean"
full = show(T)
END = "end LeanNCD.Eval.Plan.ScanDense32Test\n"
stage = {1: full[:full.index("/-! ## Part B")] + END,
         2: full[:full.index("/-! ## Part C")] + END,
         3: full}
files = {1: ["leanncd/LeanNCD/Eval/Plan/Block.lean", "leanncd/LeanNCD/Eval/Plan/Scan.lean",
             "leanncd/lakefile.toml"],
         2: ["leanncd/LeanNCD/Eval/Plan/EvalPlan.lean", "leanncd/LeanNCD/Eval/Plan/Dense32.lean",
             "leanncd/test/Eval/Plan/GraphCheckTest.lean"],
         3: ["leanncd/LeanNCD/Eval/Plan/Compile.lean", "leanncd/test/Eval/Plan/CompileTest.lean"]}
msgs = {1: "carrier-parametric checked block and scan", 2: "graph-level binary32 scan admission",
        3: "source admission, nonlinear result-slot dtypes, oracle"}
sh("switch", "-C", "f32c-tasks", BASE)
prev = BASE
os.makedirs(f"{WT}/papers/f32c_files", exist_ok=True)
for t in (1, 2, 3):
    for f in files[t]:
        open(f"{WT}/{f}", "w").write(show(f))
    open(f"{WT}/{T}", "w").write(stage[t])
    sh("add", *files[t], T)
    sh("commit", "-q", "-m", f"wip(f32c-tasks): task {t} — {msgs[t]} (scratch)")
    head = sh("rev-parse", "HEAD").strip()
    patch = sh("diff", "--binary", prev, head)
    open(f"{WT}/papers/f32c_files/task{t}.patch", "w").write(patch)
    print(f"task{t}: {head[:7]} {len(patch.splitlines())} patch lines")
    prev = head
print("final tree == proto tree (code paths):",
      sh("diff", "--stat", PROTO, prev, "--", "leanncd").strip() == "")
