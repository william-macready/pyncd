import LeanNCD.Eval.Entry
import LeanNCD.DSL.Compile
import LeanNCD.Eval.Plan.Adapter32
import EvalPlanCodegen

/-!
# JAX scatter smoke — driver (JAX scatter slice, ordered mode)

Emits static plan DATA (`renderAffinePlanNamed`) for source programs whose prepared plan CONTAINS
scatter steps, plus the Lean reference worker's own result (`runPreparedDense` /
`runPreparedDense32`) as raw bit payloads, for `evalplan_scatter_smoke.py` to compare bit-for-bit
against the committed runtime (`evalplan_affine_runtime.py`). Two outputs: argv[0] the binary64
module, argv[1] the binary32 module. Like the other drivers it lives outside every Lake target; run
via `lake env lean --run` (`run-evalplan-scatter.sh`).

Every fixture asserts, before any Python is written, that its prepared plan really has a scatter
step (a program that silently compiled to plain assignments would test nothing), that
`einsumOnly` still refuses it, and that `affineReference` renders it.
-/

namespace JaxBridge.ScatterSmoke

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std
open JaxBridge

/-- Local copy of `EvalPlanAffineSmoke32`'s binary32 payload renderer (that driver's only caller; a
    `main` file cannot be imported). Parked: factor both into `EvalPlanCodegen`. -/
def pyTensorEntry32 (t : DenseTensor32) : String :=
  "{\"shape\": " ++ pyShapeTuple t.shape.toArray ++ ", \"dtype\": \"float32\", \"bits\": [" ++
  String.intercalate ", " (t.data.toList.map fun x => toString x.toBits) ++ "]}"

def countScatters (p : PreparedPlan) : Nat :=
  p.plan.raw.steps.foldl (fun n st => match st with | .scatter _ => n + 1 | _ => n) 0

/-- The assertions every fixture shares; returns the rendered plan data. -/
def checkAndRender (name : String) (p : PreparedPlan) (minScatters : Nat) : IO String := do
  unless countScatters p ≥ minScatters do
    throw (IO.userError s!"{name}: expected >= {minScatters} scatter steps, prepared plan has {countScatters p}")
  match generateNamed .einsumOnly p with
  | .error (.unsupportedStep _) | .error (.unsupportedStorageKind _) => pure ()
  | other => throw (IO.userError s!"{name}: einsumOnly did not refuse: {repr other.toOption}")
  match renderAffinePlanNamed p with
  | .ok s => pure s
  | .error e => throw (IO.userError s!"{name} affineReference render failed: {repr e}")

def scheduled (name : String) (prog : TLProgram) : IO ScheduledProgram :=
  match prog.compileToScheduled.run 0 with
  | .ok s _ => pure s
  | .error e _ => throw (IO.userError s!"{name} compile failed: {repr e}")

def prepared (name : String) (sched : ScheduledProgram) (sig : InputSignature) : IO PreparedPlan :=
  match prepareEvalPlan sched sig with
  | .ok p => pure p
  | .error f => throw (IO.userError s!"{name} prepare failed: {renderCompileCause f.cause}")

/-- One binary64 named fixture: `{"name", "kind": "named", "plan", "inputs", "expected", "n_scatter"}`. -/
def fixture64 (name : String) (prog : TLProgram) (inputs : HashMap String DenseTensor)
    (minScatters : Nat := 1) : IO String := do
  let sched ← scheduled name prog
  let p ← prepared name sched (InputSignature.ofDenseInputs inputs)
  let planData ← checkAndRender name p minScatters
  let report ← match runPreparedDense p inputs with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{name} Dense run failed: {repr e.cause}")
  let mut ins : Array String := #[]
  for b in p.bindings.requiredInputs.bindings do
    let t ← match inputs[b.name]? with
      | some t => pure t
      | none => throw (IO.userError s!"{name}: missing input {b.name}")
    ins := ins.push (pyStrLit b.name ++ ": " ++ pyTensorEntry t)
  let mut outs : Array String := #[]
  for b in p.bindings.materializedNames do
    let t ← match report.env[b.name]? with
      | some t => pure t
      | none => throw (IO.userError s!"{name}: materialized {b.name} absent")
    outs := outs.push (pyStrLit b.name ++ ": " ++ pyTensorEntry t)
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"named\", \"n_scatter\": " ++
    toString (countScatters p) ++ ", \"plan\": " ++ planData ++
    ", \"inputs\": {" ++ String.intercalate ", " ins.toList ++
    "}, \"expected\": {" ++ String.intercalate ", " outs.toList ++ "}}")

/-- The binary32 sibling, over `runPreparedDense32`; also pins that the plan is binary32. -/
def fixture32 (name : String) (prog : TLProgram) (inputs : NamedDenseEnv32)
    (minScatters : Nat := 1) : IO String := do
  let sched ← scheduled name prog
  let sig ← match InputSignature.ofDenseInputs32ForDecls sched.decls inputs with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name} binary32 signature failed: {repr e}")
  let p ← prepared name sched sig
  unless p.plan.storageKind == .float32 do throw (IO.userError s!"{name} is not a binary32 plan")
  let planData ← checkAndRender name p minScatters
  let report ← match runPreparedDense32 p inputs with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{name} binary32 Dense run failed: {repr e.cause}")
  let mut ins : Array String := #[]
  for b in p.bindings.requiredInputs.bindings do
    let t ← match inputs[b.name]? with
      | some t => pure t
      | none => throw (IO.userError s!"{name}: missing input {b.name}")
    ins := ins.push (pyStrLit b.name ++ ": " ++ pyTensorEntry32 t)
  let mut outs : Array String := #[]
  for b in p.bindings.materializedNames do
    let t ← match report.env[b.name]? with
      | some t => pure t
      | none => throw (IO.userError s!"{name}: materialized {b.name} absent")
    outs := outs.push (pyStrLit b.name ++ ": " ++ pyTensorEntry32 t)
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"named\", \"n_scatter\": " ++
    toString (countScatters p) ++ ", \"plan\": " ++ planData ++
    ", \"inputs\": {" ++ String.intercalate ", " ins.toList ++
    "}, \"expected\": {" ++ String.intercalate ", " outs.toList ++ "}}")

def t64 (shape : List Nat) (data : Array Float) : DenseTensor := ⟨shape, data⟩
def t32 (shape : List Nat) (data : Array Float) : DenseTensor32 :=
  ⟨shape, data.map Float.toFloat32⟩
def env64 (xs : List (String × DenseTensor)) : HashMap String DenseTensor := HashMap.ofList xs
def env32 (xs : List (String × DenseTensor32)) : NamedDenseEnv32 := HashMap.ofList xs

/-! ## binary64 corpus -/

-- Biased stride `Y[2*i+1]` (`Y[i+1]` parses as a scan lookback, not a scatter): extent 6, the even
-- cells are never written (hold `reduceId`).
def shiftProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  axis k : ℕ = 6
  tensor f64 A(i), Y(k)
  Y[2 * i + 1] := A[i]
}
-- Strided placement `Y[2*i]` (donor: `Scatter32OracleTest` O1 placement): odd cells unwritten.
def strideProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  tensor f64 A(i), Y(i)
  Y[2 * i] := A[i]
}
-- Multi-axis `Y[a+b]`: cell 2 collects three writes in row-major order [1e16, 1, 1] — forward fold
-- lands on 1e16, the reversed fold on 1.0000000000000002e16.
def multiProg : TLProgram := tlprog!{
  axis a : ℕ = 3
  axis b : ℕ = 3
  axis k : ℕ = 5
  tensor f64 X(a, b), Y(k)
  Y[a + b] := X[a, b]
}
-- Constant slot (`=2`): a unit-axis row, every write lands in column 2.
def constProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  axis k : ℕ = 3
  tensor f64 A(i), Y(i, k)
  Y[i, =2] := A[i]
}
-- Compute half with a contraction: scatter `Y[2*i] := Σ_j A[i,j]·B[j]`.
def contractProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  tensor f64 A(i, j), B(j), Y(i)
  Y[2 * i] := A[i, j] · B[j]
}
-- Empty source box: `i` has extent 0, nothing is written.
def emptyProg : TLProgram := tlprog!{
  axis i : ℕ = 0
  tensor f64 A(i), Y(i)
  Y[2 * i] := A[i]
}
-- B5 interleave (donor: `EvalPlanCodegen.b5ScatterScheduled`): two writers, a collector, private slots.
def b5Prog : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 4
  tensor f64 A(i), B(i), S(k)
  S[2 * i] := A[i]
  S[2 * i + 1] := B[i]
}
-- B5 with OVERLAPPING writers (`S[2*i]`, `S[2*i+2]`, k = 6): cell 2 receives A[1] and B[0] — the
-- collector sums them.
def b5OverlapProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 6
  tensor f64 A(i), B(i), S(k)
  S[2 * i] := A[i]
  S[2 * i + 2] := B[i]
}
-- A later assignment READS the scatter's destination (graph order, strided read of the placed cells).
def chainProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  axis m : ℕ = 6
  tensor f64 A(i), Y(m), Z(i)
  Y[2 * i] := A[i]
  Z[i] := Y[2 * i]
}

def corpus64 : IO (Array String) := do
  let one := #[1.0, 2.0, 3.0]
  return #[
    ← fixture64 "shift" shiftProg (env64 [("A", t64 [3] one)]),
    ← fixture64 "stride" strideProg (env64 [("A", t64 [3] #[1.5, 2.5, -4.0])]),
    ← fixture64 "multi" multiProg
        (env64 [("X", t64 [3, 3] #[0.0, 0.0, 1e16, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0])]),
    ← fixture64 "const" constProg (env64 [("A", t64 [3] one)]),
    ← fixture64 "contract" contractProg
        (env64 [("A", t64 [2, 3] #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]), ("B", t64 [3] #[0.5, 0.25, 2.0])]),
    ← fixture64 "empty" emptyProg (env64 [("A", t64 [0] #[])]),
    ← fixture64 "b5" b5Prog (env64 [("A", t64 [2] #[-5.0, -2.0]), ("B", t64 [2] #[-7.0, -3.0])]) 2,
    ← fixture64 "b5Overlap" b5OverlapProg
        (env64 [("A", t64 [2] #[1e16, 1.0]), ("B", t64 [2] #[1.0, 7.0])]) 2,
    ← fixture64 "chain" chainProg (env64 [("A", t64 [3] one)]),
    -- Signed zero: `reduceId + (-0.0)` is `+0.0` in the worker; a copy-on-first-write runtime
    -- would produce `-0.0`. Eager-only in the verifier (jit drops the +0 fold seed).
    ← fixture64 "negZero" shiftProg (env64 [("A", t64 [3] #[-0.0, 0.0, 2.0])])]

/-! ## binary32 corpus -/

def stride32Prog : TLProgram := tlprog!{
  axis i : ℕ = 3
  tensor f32 A(i), B(i), Out(i)
  Out[2 * i + 1] := A[i] · B[i]
}
-- f32 collision order: row-major writes [2^24, 1, 1] into one cell; forward fold stays at 2^24
-- (each +1 ties to even), the reversed fold gives 2^24 + 2.
def multi32Prog : TLProgram := tlprog!{
  axis a : ℕ = 3
  axis b : ℕ = 3
  axis k : ℕ = 5
  tensor f32 X(a, b), Y(k)
  Y[a + b] := X[a, b]
}
def contract32Prog : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  tensor f32 A(i, j), B(j), Y(i)
  Y[2 * i] := A[i, j] · B[j]
}
def b5Overlap32Prog : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 6
  tensor f32 A(i), B(i), S(k)
  S[2 * i] := A[i]
  S[2 * i + 2] := B[i]
}
def empty32Prog : TLProgram := tlprog!{
  axis i : ℕ = 0
  tensor f32 A(i), Y(i)
  Y[2 * i] := A[i]
}

def corpus32 : IO (Array String) := do
  return #[
    ← fixture32 "stride32" stride32Prog
        (env32 [("A", t32 [3] #[4097.0, 3.0, 0.1]), ("B", t32 [3] #[4097.0, 0.1, 3.0])]),
    ← fixture32 "multi32" multi32Prog
        (env32 [("X", t32 [3, 3] #[0.0, 0.0, 16777216.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0])]),
    ← fixture32 "contract32" contract32Prog
        (env32 [("A", t32 [2, 3] #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]), ("B", t32 [3] #[0.5, 0.25, 2.0])]),
    ← fixture32 "b5Overlap32" b5Overlap32Prog
        (env32 [("A", t32 [2] #[16777216.0, 1.0]), ("B", t32 [2] #[1.0, 0.1])]) 2,
    ← fixture32 "empty32" empty32Prog (env32 [("A", t32 [0] #[])])]

end JaxBridge.ScatterSmoke

open JaxBridge.ScatterSmoke in
def main (args : List String) : IO Unit := do
  let out64 := args.head?.getD "generated_evalplan_scatter_smoke64.py"
  let out32 := (args.drop 1).head?.getD "generated_evalplan_scatter_smoke32.py"
  let f64s ← corpus64
  let f32s ← corpus32
  IO.FS.writeFile out64
    ("# Generated by EvalPlanScatterSmoke.lean — do not edit.\nFIXTURES = [\n" ++
      String.intercalate ",\n" f64s.toList ++ "\n]\n")
  IO.FS.writeFile out32
    ("# Generated by EvalPlanScatterSmoke.lean — do not edit.\nFIXTURES = [\n" ++
      String.intercalate ",\n" f32s.toList ++ "\n]\n")
  IO.println s!"wrote {f64s.size} binary64 fixtures to {out64} and {f32s.size} binary32 to {out32}"
