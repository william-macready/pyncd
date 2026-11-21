import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter32
import EvalPlanCodegen

/-! Preflight scratch: Dense (checked plan, both precisions) and reference outputs of `reachProg`
on Edge tensors with non-0/1 values. Prints raw bit patterns so signed zeros and NaN payloads show. -/
namespace PreflightEdge
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std JaxBridge

def reachProg : TLProgram := tlprog!{
  axis i : ℕ = 6, j : ℕ = 6, k : ℕ = 6
  iter h = 7
  predicate Edge(i, j), Reach(i, j, h)
  tensor f64 Closed(i, j)
  Reach[i, j, 0] := [i = j]
  Reach[i, j, h +1] := Reach[i, j, h] + Reach[i, k, h] · Edge[k, j]
  Closed[i, j] := Reach[i, j, 6]
}

def retag32 (p : TLProgram) : TLProgram :=
  { p with decls := p.decls.map fun d => match d with
      | .typedTensor .f64 n ax => .typedTensor .f32 n ax
      | d => d }

def graphEdges : List (Nat × Nat) := [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (4, 1)]

/-- Edge tensor: `onVal` at listed edges, `offVal` elsewhere, then point overrides. -/
def edgeWith (onVal offVal : Float) (overrides : List (Nat × Float)) : NamedDenseEnv :=
  HashMap.ofList [("Edge", ⟨[6, 6], (List.range 36).toArray.map fun q =>
    match overrides.find? (·.1 == q) with
    | some (_, v) => v
    | none => if graphEdges.contains (q / 6, q % 6) then onVal else offVal⟩)]

def nan : Float := 0.0 / 0.0
def inf : Float := 1.0 / 0.0
def negZero : Float := -0.0

def cases : List (String × NamedDenseEnv) :=
  [("baseline 0/1", edgeWith 1 0 []),
   ("true=0.5", edgeWith 0.5 0 []),
   ("true=2.0", edgeWith 2.0 0 []),
   ("true=+inf", edgeWith inf 0 []),
   ("true=-1.0", edgeWith (-1.0) 0 []),
   ("false=-0.0", edgeWith 1 negZero []),
   ("Edge[0,1]=NaN", edgeWith 1 0 [(1, nan)]),
   ("Edge[5,5]=NaN (unreachable row)", edgeWith 1 0 [(35, nan)])]

def compile (p : TLProgram) : IO ScheduledProgram :=
  match p.compileToScheduled.run 0 with
  | .ok s _ => pure s
  | .error e _ => throw (IO.userError s!"compile: {repr e}")

def prepare (s : ScheduledProgram) (sig : InputSignature) : IO PreparedPlan :=
  match prepareEvalPlan s sig with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"prepare: {renderCompileCause e.cause}")

def hex64 (x : Float) : String := String.mk (Nat.toDigits 16 x.toBits.toNat)
def hex32 (x : Float32) : String := String.mk (Nat.toDigits 16 x.toBits.toNat)

/-- Distinct bit patterns with counts, so the dump stays short. -/
def histo (xs : List String) : List (String × Nat) :=
  xs.foldl (fun acc x => match acc.find? (·.1 == x) with
    | some _ => acc.map fun (k, n) => if k == x then (k, n + 1) else (k, n)
    | none => acc ++ [(x, 1)]) []

#eval show IO Unit from do
  let sched ← compile reachProg
  let sched32 ← compile (retag32 reachProg)
  for (label, env) in cases do
    IO.println s!"===== {label}"
    let sig ← match InputSignature.ofDenseInputsForDecls sched.decls env with
      | .ok s => pure s | .error e => throw (IO.userError s!"sig64: {repr e}")
    let p ← prepare sched sig
    let out ← match runPreparedDense p env with
      | .ok r => pure r.env | .error e => throw (IO.userError s!"plan64: {repr e.cause}")
    let refOut := evalScheduled sched env
    let env32 : NamedDenseEnv32 := env.map fun _ t => ⟨t.shape, t.data.map Float.toFloat32⟩
    let sig32 ← match InputSignature.ofDenseInputs32ForDecls sched32.decls env32 with
      | .ok s => pure s | .error e => throw (IO.userError s!"sig32: {repr e}")
    let p32 ← prepare sched32 sig32
    let out32 ← match runPreparedDense32 p32 env32 with
      | .ok r => pure r.env | .error e => throw (IO.userError s!"plan32: {repr e.cause}")
    for n in ["Reach", "Closed"] do
      let t := out[n]!
      let t32 := out32[n]!
      IO.println s!"  plan64 {n}: value histogram (hex bits): {histo (t.data.toList.map hex64)}"
      IO.println s!"  plan32 {n}: value histogram (hex bits): {histo (t32.data.toList.map hex32)}"
      -- elementwise f64 -> f32 bit agreement (narrowed f64 vs native f32)
      let agree := (t.data.toList.zip t32.data.toList).all fun (a, b) => a.toFloat32.toBits == b.toBits
      IO.println s!"  {n}: plan32 == narrow(plan64) bitwise: {agree}"
      match refOut with
      | .ok r =>
        match r.env[n]? with
        | some rt => IO.println s!"  {n}: reference == plan64 bitwise: {(rt.data.toList.zip t.data.toList).all fun (a, b) => a.toBits == b.toBits} (sizes {rt.data.size}/{t.data.size})"
        | none => IO.println s!"  {n}: reference has no {n}"
      | .error e => IO.println s!"  reference error: {e}"
    -- Closed row 0 and Reach[0, :, 6] in decimal for readability
    let c := out["Closed"]!
    IO.println s!"  plan64 Closed row 0: {(List.range 6).map fun q => c.data[q]!}"
    let r := out["Reach"]!
    IO.println s!"  plan64 Reach[0, :, h] for h=0..6, j=1: {(List.range 7).map fun h => r.data[(0 * 6 + 1) * 7 + h]!}"

end PreflightEdge
