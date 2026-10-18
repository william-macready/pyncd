# P0 probe: declared-vs-derived scatter extent

Question: `S[2*i] := X[i]` (`axis i = 4`, `X : f64 [4]`) derives extent 8. What happens when `S` is also
declared over a pinned axis `k` of size N that disagrees?

Backends probed (single-file `lake env lean`, production modules only, nothing under LeanNCD/ or test/
edited): (1) reference `evalScheduled`; (2) checked plan `prepareEvalPlan` then `runPreparedDense`.
(3) pre-collection evaluator: NOT probed (no cheap handle; the pre-collection code is only in git history).

Scheduling: `p.compileToScheduled.run 0` directly (every tensor in each program is declared `tensor f64`,
so `explicitF64` is not needed). The surface DSL has NO collision-policy / `reduce := sum` syntax
(`ScatterOpts` is only reachable through hand-built `Stmt.scatter`), so the `reduce := sum` variant is
NOT expressible from source and was not run. Default policy is `rejectCollisions`; `S[2*i]` has no collisions.

## Results

`S` expected values for the scatter: `[1,0,2,0,3,0,4,0]` (shape `[8]`).

| variant | reference | checked plan |
|---|---|---|
| `S(k)`, `k = 6` (too small) | ok, S shape [8], full values | ok, S shape [8], full values |
| `S(k)`, `k = 7` (too small) | ok, S shape [8], full values | ok, S shape [8], full values |
| `S(k)`, `k = 8` (equal) | ok, S shape [8] | ok, S shape [8] |
| `S(k)`, `k = 9` (larger) | ok, S shape [8] (NOT 9) | ok, S shape [8] (NOT 9) |
| baseline B: `S(k)` declared, `k` unpinned | ok, S shape [8] | ok, S shape [8] |
| baseline A: `S` undeclared | ERROR `unsupported dtype: tensor S is declared f32` (default f32; reference is f64-only) | prepare ERROR `capability` (same f32 reason) |
| consumer `Z[k] := S[k]`, `k = 6` | ERROR `axis size conflict for uid 2: 6 vs 8` | prepare ERROR `shape` |
| consumer `Z[k] := S[k]`, `k = 8` | ok, S and Z shape [8] | ok, S and Z shape [8] |
| consumer `Z[k] := S[k]`, `k = 9` | ERROR `axis size conflict for uid 2: 9 vs 8` | prepare ERROR `shape` |
| constant slot `S[3] := W[j]` (`j = 1`), `k = 3` / `5` / unpinned | ERROR `evalScan: scan node has no iteration axis` | prepare ERROR `capability` |

## Findings

* The pin `axis k = N` on the declaration `S(k)` has NO effect on the scatter's destination: the slot `2*i`
  is over `i`, not `k`, so `S`'s declared axis is never unified with the derived extent. Declared `k` of
  6 or 7 does not make the write at coordinate 6 or 7 an error, it is written (S has shape [8]); `k = 9`
  does not enlarge S. No write is skipped or clipped. Both backends agree in every variant.
* The disagreement surfaces only when `S` is READ through the pinned axis downstream (`Z[k] := S[k]`):
  then it is a size conflict (reference: `axis size conflict 6 vs 8`; checked plan: `shape` cause at
  prepare). So the conflict error exists but is raised at the consumer, not at the scatter.
* Constant-slot variant: constructed, but all three variants fail identically with an UNRELATED
  `evalScan: scan node has no iteration axis` / `capability` error (an `i`-free statement with a size-1
  free axis `j` is routed through the scan path). Inconclusive about extent; not retried within budget.
  A different RHS shape would be needed to probe a constant slot.
* No backend skipped a write, and neither raised an out-of-range error for an affine slot.

## Exact scratch program text (`p0_probe.lean`, scratchpad)

```lean
import LeanNCD
import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Compile
import LeanNCD.Eval.Plan.Adapter

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

def dt (shape : List Nat) (xs : List Float) : DenseTensor := ⟨shape, xs.toArray⟩
def env4 : HashMap String DenseTensor :=
  HashMap.ofList [("X", dt [4] [1.0, 2.0, 3.0, 4.0]), ("W", dt [1] [5.0])]

def pN6 : TLProgram := tlprog!{
  axis i : ℕ = 4
  axis k : ℕ = 6
  tensor f64 X(i), S(k)
  S[2*i] := X[i]
}
-- pN7, pN8, pN9: identical with k = 7, 8, 9
def pBaseA : TLProgram := tlprog!{   -- S undeclared
  axis i : ℕ = 4
  tensor f64 X(i)
  S[2*i] := X[i]
}
def pBaseB : TLProgram := tlprog!{   -- S(k), k unpinned
  axis i : ℕ = 4
  tensor f64 X(i), S(k)
  S[2*i] := X[i]
}
def pC6 : TLProgram := tlprog!{      -- consumer through the pinned axis; pC8, pC9 likewise
  axis i : ℕ = 4
  axis k : ℕ = 6
  tensor f64 X(i), S(k), Z(k)
  S[2*i] := X[i]
  Z[k] := S[k]
}
def pK3 : TLProgram := tlprog!{      -- constant slot; pK5 has k = 5, pKbase leaves k unpinned
  axis j : ℕ = 1
  axis k : ℕ = 3
  tensor f64 W(j), S(k)
  S[3] := W[j]
}

def showEnv (e : HashMap String DenseTensor) : String :=
  String.intercalate "; " (["S", "Z"].filterMap fun nm =>
    (e[nm]?).map fun t => s!"{nm} shape={t.shape} data={t.data.toList}")

def causeTag : PlanCompileCause → String
  | .inputSignature _ => "inputSignature" | .capability _ => "capability"
  | .shape _ => "shape" | .scan _ => "scan" | .invalidPlan _ => "invalidPlan"
  | .bindings _ => "bindings" | .nonlin _ => "nonlin" | _ => "other"

def probe (nm : String) (p : TLProgram) : IO Unit := do
  IO.println s!"== {nm}"
  match p.compileToScheduled.run 0 with
  | .error e _ => IO.println s!"  compile: ERROR {repr e}"
  | .ok sched _ =>
    IO.println "  compile: ok"
    match evalScheduled sched env4 with
    | .error e => IO.println s!"  ref: ERROR {e.error}"
    | .ok r => IO.println s!"  ref: ok {showEnv r.env}"
    match prepareEvalPlan sched (InputSignature.ofDenseInputs env4) with
    | .error e => IO.println s!"  prepare: ERROR {causeTag e.cause}"
    | .ok pp =>
      IO.println "  prepare: ok"
      match runPreparedDense pp env4 with
      | .error e => IO.println s!"  plan run: ERROR {repr e.cause}"
      | .ok r => IO.println s!"  plan run: ok {showEnv r.env}"

#eval probe "N=6" pN6   -- and N=7,8,9, baseA, baseB, consumer 6/8/9, const 3/5/unpinned
```

Run with `lake --dir <worktree>/leanncd env lean p0_probe.lean`.
