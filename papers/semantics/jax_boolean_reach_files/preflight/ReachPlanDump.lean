import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter32
import EvalPlanCodegen

/-! Preflight scratch: dump the checked plan of `reachProg` (copied verbatim from
experiments/jax_bridge/EvalPlanLogicSmoke.lean) in both precisions, the JAX gate verdicts, the
Lean-decided Iverson tables, and Dense outputs on edge-value Edge inputs. -/
namespace Preflight
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

def dense (shape : List Nat) (data : Array Float) : DenseTensor := ⟨shape, data⟩

def edgeInputs (edges : List (Nat × Nat)) : NamedDenseEnv :=
  HashMap.ofList [("Edge", dense [6, 6] ((List.range 36).toArray.map fun q =>
    if edges.contains (q / 6, q % 6) then 1 else 0))]

def graphEdges : List (Nat × Nat) := [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (4, 1)]

def compile (p : TLProgram) : IO ScheduledProgram :=
  match p.compileToScheduled.run 0 with
  | .ok s _ => pure s
  | .error e _ => throw (IO.userError s!"compile: {repr e}")

def prepare (s : ScheduledProgram) (sig : InputSignature) : IO PreparedPlan :=
  match prepareEvalPlan s sig with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"prepare: {renderCompileCause e.cause}")

def prep64 (env : NamedDenseEnv) : IO (ScheduledProgram × PreparedPlan) := do
  let sched ← compile reachProg
  let sig ← match InputSignature.ofDenseInputsForDecls sched.decls env with
    | .ok s => pure s | .error e => throw (IO.userError s!"sig64: {repr e}")
  pure (sched, ← prepare sched sig)

def to32 (env : NamedDenseEnv) : NamedDenseEnv32 := env.map fun _ t => ⟨t.shape, t.data.map Float.toFloat32⟩

def prep32 (env : NamedDenseEnv) : IO PreparedPlan := do
  let sched ← compile (retag32 reachProg)
  let sig ← match InputSignature.ofDenseInputs32ForDecls sched.decls (to32 env) with
    | .ok s => pure s | .error e => throw (IO.userError s!"sig32: {repr e}")
  prepare sched sig

/-- Column indices a positional predicate references with a nonzero coefficient. -/
partial def arithCols : PosPredArith → List Nat
  | .affine a => (List.range a.coeffs.size).filter fun c => a.coeffs[c]! != 0
  | .mul a b => arithCols a ++ arithCols b
  | .iabs a => arithCols a
partial def boolCols : PosBoolExpr → List Nat
  | .rel _ a b => arithCols a ++ arithCols b
  | .ieq a b => arithCols a ++ arithCols b
  | .and a b => boolCols a ++ boolCols b
  | .or a b => boolCols a ++ boolCols b
  | .not a => boolCols a

def dumpBlockAssigns (label : String) (ev : CheckedPlanBlock) : IO Unit := do
  for e in ev.checkedNodes do
    match e with
    | .assign a =>
      let pl := a.plan
      IO.println s!"  [{label}] assign dest={pl.destinationSlot} outputShape={pl.outputShape} contextShape={pl.contextShape} algebra={repr pl.algebra}"
      for h : ti in [0 : pl.terms.size] do
        let t := pl.terms[ti]
        IO.println s!"    term {ti}: iterationShape={t.iterationShape} contextPos={t.contextPos} outputPos={t.outputPos} reductionPos={t.reductionPos}"
        for h2 : fi in [0 : t.factors.size] do
          match t.factors[fi] with
          | .read r => IO.println s!"      factor {fi}: READ {repr r}"
          | .iverson b =>
            IO.println s!"      factor {fi}: IVERSON {repr b}"
            IO.println s!"        referenced iteration columns: {boolCols b}; contextPos={t.contextPos}"
            let coords := allCoords t.iterationShape.toList
            let vals := coords.map fun c => match evalPosBool c b with
              | .ok true => "1" | .ok false => "0" | .error e => s!"ERR({repr e})"
            IO.println s!"        Lean-decided table (allCoords order over iterationShape, {coords.length} entries): {vals}"
    | .pointwise _ => IO.println s!"  [{label}] pointwise"
    | .axiswise _ => IO.println s!"  [{label}] axiswise"

def gateReport (p : PreparedPlan) : IO Unit := do
  let c := p.plan
  let sigs := c.raw.tensorSigs
  for h : ni in [0 : c.checkedNodes.size] do
    match c.checkedNodes[ni] with
    | .scan sc =>
      IO.println s!"node {ni}: SCAN historyExtents={sc.raw.historyExtents} stepExtents={sc.stepExtents}"
      for st in sc.raw.states do IO.println s!"  state {repr st}"
      IO.println s!"  baseCaptures={repr sc.raw.baseCaptures} stepCaptures={repr sc.raw.stepCaptures}"
      IO.println s!"  baseWrites={repr sc.raw.baseWrites}"
      IO.println s!"  stepWrites={repr sc.raw.stepWrites}"
      IO.println s!"  baseBlock.tensorSigs={repr sc.raw.baseBlock.tensorSigs} inputs={sc.raw.baseBlock.inputs}"
      IO.println s!"  stepBlock.tensorSigs={repr sc.raw.stepBlock.tensorSigs} inputs={sc.raw.stepBlock.inputs}"
      dumpBlockAssigns "base" sc.checkedBase
      dumpBlockAssigns "step" sc.checkedStep
      IO.println s!"  checkJaxScanSupport realOnly: {repr (checkJaxScanSupport ni sc (profile := .realOnly))}"
      IO.println s!"  checkJaxScanSupport maxPlus : {repr (checkJaxScanSupport ni sc (profile := .maxPlus))}"
      for e in sc.checkedBase.checkedNodes do
        match e with
        | .assign a => IO.println s!"  base assign alone, maxPlus, allowUnary: {repr (checkJaxAssignSupport sc.raw.baseBlock.tensorSigs ni a true .maxPlus)}"
        | _ => pure ()
      for e in sc.checkedStep.checkedNodes do
        match e with
        | .assign a => IO.println s!"  step assign alone (no ctx opt-in), maxPlus: {repr (checkJaxAssignSupport sc.raw.stepBlock.tensorSigs ni a true .maxPlus)}"
        | _ => pure ()
    | .assign a =>
      let pl := a.plan
      IO.println s!"node {ni}: ASSIGN dest={pl.destinationSlot} outputShape={pl.outputShape} algebra={repr pl.algebra}"
      for t in pl.terms do
        IO.println s!"    term: iterationShape={t.iterationShape} outputPos={t.outputPos} reductionPos={t.reductionPos}"
        for f in t.factors do
          match f with
          | .read r => IO.println s!"      READ {repr r}"
          | .iverson b => IO.println s!"      IVERSON {repr b}"
      IO.println s!"  checkJaxAssignSupport realOnly: {repr (checkJaxAssignSupport sigs ni a true .realOnly)}"
      IO.println s!"  checkJaxAssignSupport maxPlus : {repr (checkJaxAssignSupport sigs ni a true .maxPlus)}"
    | _ => IO.println s!"node {ni}: other"
  IO.println s!"renderAffinePlanNamed: {match renderAffinePlanNamed p with | .ok _ => "ok" | .error e => reprStr e}"
  IO.println s!"renderAffinePlanPositional: {match renderAffinePlanPositional p.plan with | .ok _ => "ok" | .error e => reprStr e}"

def dumpPlan (label : String) (p : PreparedPlan) : IO Unit := do
  IO.println s!"===================== {label}"
  IO.println s!"storageKind={repr p.plan.storageKind}"
  IO.println s!"tensorSigs={repr p.plan.raw.tensorSigs}"
  IO.println s!"inputSlots={p.plan.raw.inputSlots}"
  IO.println s!"requiredInputs={repr p.bindings.requiredInputs.bindings}"
  IO.println s!"materialized={repr p.bindings.materializedNames}"
  gateReport p

#eval show IO Unit from do
  let env := edgeInputs graphEdges
  let (_, p64) ← prep64 env
  dumpPlan "reachProg f64" p64
  let p32 ← prep32 env
  dumpPlan "reachProg f32 (retag32)" p32

end Preflight
