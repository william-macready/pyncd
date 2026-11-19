import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter32
import EvalPlanCodegen

/-!
# Logic algorithm fixtures

Source Tensor Logic -> scheduled reference and checked plans in both precisions.
The Python verifier independently enumerates HMM paths and computes graph distances by BFS.
Max-plus additionally renders to JAX; Boolean reachability remains checked/reference-only.
Viterbi exports scores, not argmax indices or a traceback (neither has a native TL operator).
-/
namespace JaxBridge.LogicSmoke

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std JaxBridge

def viterbiProg : TLProgram := tlprog!{
  axis s : ℕ = 4, p : ℕ = 4
  iter t = 6
  predicate Allow(p, s)
  tensor f64 Init(s), Trans(p, s), Emit(t, s), D(s, t), Score()
  D[s, 0] := Init[s]
  D[s, t +1] := maxreduce(D[p, t] · Trans[p, s] · Emit[t, s] · Allow[p, s])
  Score[] := maxreduce(D[s, 5])
}

def reachProg : TLProgram := tlprog!{
  axis i : ℕ = 6, j : ℕ = 6, k : ℕ = 6
  iter h = 7
  predicate Edge(i, j), Reach(i, j, h)
  tensor f64 Closed(i, j)
  Reach[i, j, 0] := [i = j]
  Reach[i, j, h +1] := Reach[i, j, h] + Reach[i, k, h] · Edge[k, j]
  Closed[i, j] := Reach[i, j, 6]
}

def dense (shape : List Nat) (data : Array Float) : DenseTensor := ⟨shape, data⟩

def viterbiInputs : NamedDenseEnv := HashMap.ofList [
  ("Init", dense [4] #[0, -1.25, -2.5, -1.0 / 0.0]),
  ("Trans", dense [4, 4] #[-0.5, -0.25, 4, 8, -1.5, 6, -0.5, 8,
    5, -1.25, -1, 8, 8, 8, 8, 8]),
  ("Allow", dense [4, 4] #[1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0]),
  ("Emit", dense [6, 4] #[-1, -0.25, -2, -0.5, -0.5, -2, -0.25, -1,
    -2, -0.5, -0.25, -1, -0.25, -1, -2, -0.5, -1, -0.25, -0.5, -2,
    0.0 / 0.0, 0.0 / 0.0, 0.0 / 0.0, 0.0 / 0.0])]

def edgeInputs (edges : List (Nat × Nat)) : NamedDenseEnv :=
  HashMap.ofList [("Edge", dense [6, 6] ((List.range 36).toArray.map fun q =>
    if edges.contains (q / 6, q % 6) then 1 else 0))]

def graphEdges : List (Nat × Nat) := [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (4, 1)]

def permuteViterbi (env : NamedDenseEnv) : NamedDenseEnv :=
  let perm := #[2, 0, 3, 1]
  env.map fun n a => { a with data := a.data.mapIdx fun q _ =>
    let offset := if n == "Init" then perm[q]!
      else if n == "Emit" then (q / 4) * 4 + perm[q % 4]!
      else perm[q / 4]! * 4 + perm[q % 4]!
    a.data[offset]! }

def permuteGraph (env : NamedDenseEnv) : NamedDenseEnv :=
  let perm := #[4, 2, 0, 5, 1, 3]
  env.map fun _ a => { a with data := a.data.mapIdx fun q _ =>
    a.data[perm[q / 6]! * 6 + perm[q % 6]!]! }

structure Fixture where
  name : String
  program : TLProgram
  inputs : NamedDenseEnv
  outputs : List String
  tropical : Bool

def fixtures : List Fixture :=
  let v := viterbiInputs
  let graph := edgeInputs graphEdges
  let withEmit := fun f => v.modify "Emit" fun a => { a with data := a.data.mapIdx f }
  [⟨"viterbi", viterbiProg, v, ["D", "Score"], true⟩,
   ⟨"viterbi_permuted", viterbiProg, permuteViterbi v, ["D", "Score"], true⟩,
   ⟨"viterbi_changed", viterbiProg, withEmit (fun q x => if q == 9 then x + 2 else x),
     ["D", "Score"], true⟩,
   ⟨"viterbi_spare", viterbiProg, withEmit (fun q x => if q ≥ 20 then 0 else x),
     ["D", "Score"], true⟩,
   ⟨"viterbi_shifted", viterbiProg, withEmit (fun q x => if q < 20 then x + 0.5 else x),
     ["D", "Score"], true⟩,
   ⟨"viterbi_blocked", viterbiProg,
     v.modify "Allow" (fun a => { a with data := a.data.map fun _ => 0 }), ["D", "Score"], true⟩,
   ⟨"viterbi_tied", viterbiProg, v.map (fun n a =>
     { a with data := a.data.map fun _ => if n == "Allow" then 1 else 0 }),
     ["D", "Score"], true⟩,
   ⟨"reachability", reachProg, graph, ["Reach", "Closed"], false⟩,
   ⟨"reachability_permuted", reachProg, permuteGraph graph, ["Reach", "Closed"], false⟩,
   ⟨"reachability_added", reachProg, edgeInputs (graphEdges ++ [(4, 5)]),
     ["Reach", "Closed"], false⟩,
   ⟨"reachability_empty", reachProg, edgeInputs [], ["Reach", "Closed"], false⟩,
   ⟨"reachability_chain", reachProg, edgeInputs [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)],
     ["Reach", "Closed"], false⟩,
   ⟨"reachability_self", reachProg, edgeInputs ((List.range 6).map fun i => (i, i)),
     ["Reach", "Closed"], false⟩]

def retag32 (p : TLProgram) : TLProgram :=
  { p with decls := p.decls.map fun d => match d with
      | .typedTensor .f64 n ax => .typedTensor .f32 n ax
      | d => d }

def compile (name : String) (p : TLProgram) : IO ScheduledProgram :=
  match p.compileToScheduled.run 0 with
  | .ok s _ => pure s
  | .error e _ => throw (IO.userError s!"{name}: compile: {repr e}")

def prepare (name : String) (s : ScheduledProgram) (sig : InputSignature) : IO PreparedPlan :=
  match prepareEvalPlan s sig with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"{name}: prepare: {renderCompileCause e.cause}")

def checkStructure (f : Fixture) (p : PreparedPlan) (kind : StorageKind) : IO Unit := do
  unless p.plan.storageKind == kind do throw (IO.userError s!"{f.name}: wrong storage kind")
  unless (p.bindings.materializedNames.map (·.name)).toList == f.outputs do
    throw (IO.userError s!"{f.name}: wrong exports: {repr p.bindings.materializedNames}")
  let #[.scan sc, .assign _] := p.plan.raw.steps
    | throw (IO.userError s!"{f.name}: expected a scan then a terminal consumer")
  unless sc.historyExtents == (if f.tropical then #[6] else #[7]) &&
      sc.states.size == 1 && sc.baseWrites.size == 1 && sc.stepWrites.size == 1 do
    throw (IO.userError s!"{f.name}: wrong scan geometry")
  let #[.assign base] := sc.baseBlock.steps
    | throw (IO.userError s!"{f.name}: expected one base assign")
  let #[.assign step] := sc.stepBlock.steps
    | throw (IO.userError s!"{f.name}: expected one step assign")
  let algebra := if f.tropical then
    (if kind == .float64 then admittedAlgebraMax else admittedAlgebraF32Max)
    else admittedAlgebraBool
  unless base.algebra == algebra && step.algebra == algebra &&
      sc.states[0]!.initValue == (if f.tropical then .negInf else .zero) do
    throw (IO.userError s!"{f.name}: wrong scan algebra or neutral initialization")
  match renderAffinePlanNamed p with
  | .error (.unsupportedDestDType 0 _ .bool) => unless !f.tropical do
      throw (IO.userError s!"{f.name}: unexpected Boolean JAX refusal")
  | .error e => throw (IO.userError s!"{f.name}: unexpected JAX refusal: {repr e}")
  | .ok _ => unless f.tropical do
      throw (IO.userError s!"{f.name}: JAX unexpectedly admitted a Boolean scan")
  match renderAffinePlanPositional p.plan with
  | .ok _ => unless f.tropical do throw (IO.userError s!"{f.name}: positional Boolean admitted")
  | .error (.unsupportedDestDType 0 _ .bool) =>
      unless !f.tropical do throw (IO.userError s!"{f.name}: positional max-plus refused")
  | .error e => throw (IO.userError s!"{f.name}: positional: {repr e}")

def pyEnv (env : NamedDenseEnv) (names : List String) : IO String := do
  let xs ← names.mapM fun n => do
    let some t := env[n]? | throw (IO.userError s!"missing tensor {n}")
    pure (pyStrLit n ++ ": " ++ pyTensorEntry t)
  pure ("{" ++ String.intercalate ", " xs ++ "}")

def pyEnv32 (env : NamedDenseEnv32) (names : List String) : IO String := do
  let xs ← names.mapM fun n => do
    let some t := env[n]? | throw (IO.userError s!"missing tensor {n}")
    pure (pyStrLit n ++ ": {\"shape\": " ++ pyShapeTuple t.shape.toArray ++
      ", \"bits\": [" ++ String.intercalate ", " (t.data.toList.map fun x => toString x.toBits) ++ "]}")
  pure ("{" ++ String.intercalate ", " xs ++ "}")

def emit (f : Fixture) : IO String := do
  let sched ← compile f.name f.program
  let sig ← match InputSignature.ofDenseInputsForDecls sched.decls f.inputs with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{f.name}: signature64: {repr e}")
  let p ← prepare f.name sched sig
  checkStructure f p .float64
  let reference ← match evalScheduled sched f.inputs with
    | .ok r => pure r.env
    | .error e => throw (IO.userError s!"{f.name}: reference: {e}")
  let out64 ← match runPreparedDense p f.inputs with
    | .ok r => pure r.env
    | .error e => throw (IO.userError s!"{f.name}: plan64: {repr e.cause}")
  let inputs32 : NamedDenseEnv32 := f.inputs.map fun _ t => ⟨t.shape, t.data.map Float.toFloat32⟩
  let sched32 ← compile f.name (retag32 f.program)
  let sig32 ← match InputSignature.ofDenseInputs32ForDecls sched32.decls inputs32 with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{f.name}: signature32: {repr e}")
  let p32 ← prepare f.name sched32 sig32
  checkStructure f p32 .float32
  let out32 ← match runPreparedDense32 p32 inputs32 with
    | .ok r => pure r.env
    | .error e => throw (IO.userError s!"{f.name}: plan32: {repr e.cause}")
  let names := (p.bindings.requiredInputs.bindings.map (·.name)).toList
  let jaxFields ← if !f.tropical then pure "" else do
    let named ← match renderAffinePlanNamed p with
      | .ok x => pure x | .error e => throw (IO.userError s!"{repr e}")
    let positional ← match renderAffinePlanPositional p.plan with
      | .ok x => pure x | .error e => throw (IO.userError s!"{repr e}")
    let named32 ← match renderAffinePlanNamed p32 with
      | .ok x => pure x | .error e => throw (IO.userError s!"{repr e}")
    let positional32 ← match renderAffinePlanPositional p32.plan with
      | .ok x => pure x | .error e => throw (IO.userError s!"{repr e}")
    pure (", \"jax64\": " ++ named ++ ", \"jaxpos64\": " ++ positional ++
      ", \"jax32\": " ++ named32 ++ ", \"jaxpos32\": " ++ positional32)
  pure ("{\"name\": " ++ pyStrLit f.name ++ ", \"inputs64\": " ++ (← pyEnv f.inputs names) ++
    ", \"inputs32\": " ++ (← pyEnv32 inputs32 names) ++
    ", \"reference\": " ++ (← pyEnv reference f.outputs) ++
    ", \"plan64\": " ++ (← pyEnv out64 f.outputs) ++
    ", \"plan32\": " ++ (← pyEnv32 out32 f.outputs) ++ jaxFields ++ "}")

end JaxBridge.LogicSmoke

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "usage: EvalPlanLogicSmoke.lean OUTPUT.py")
  let cases ← JaxBridge.LogicSmoke.fixtures.mapM JaxBridge.LogicSmoke.emit
  IO.FS.writeFile out ("# Generated by EvalPlanLogicSmoke.lean\nFIXTURES = [\n" ++
    String.intercalate ",\n" cases ++ "\n]\n")
  IO.println s!"logic: generated {cases.length} fixtures, reference + checked binary64/binary32"
