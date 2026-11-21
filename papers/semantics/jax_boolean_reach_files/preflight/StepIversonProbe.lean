import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter32
import EvalPlanCodegen

/-! Preflight scratch: how a step-block Iverson factor that references the scan step index is lowered
(which iteration column carries it), and the Lean-decided table over the full stacked iteration grid. -/
namespace PreflightStep
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std JaxBridge

def inputs : HashMap String DenseTensor := HashMap.ofList [("X", ⟨[3], #[1.0, 2.0, 3.0]⟩)]

def stepDep : TLProgram := tlprog!{
  axis j : ℕ = 3
  iter l = 4
  tensor f64 X(j), S(j, l)
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l] · [j ≤ l]
}

def stepFree : TLProgram := tlprog!{
  axis j : ℕ = 3
  iter l = 4
  tensor f64 X(j), S(j, l)
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l] · [j ≤ 1]
}

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

def probe (label : String) (p : TLProgram) : IO Unit := do
  IO.println s!"===== {label}"
  let .ok s _ := p.compileToScheduled.run 0 | throw (IO.userError "compile")
  let .ok pp := prepareEvalPlan s (InputSignature.ofDenseInputs inputs) | throw (IO.userError "prepare")
  for n in pp.plan.checkedNodes do
    match n with
    | .scan sc =>
      IO.println s!"stepExtents={sc.stepExtents}"
      for e in sc.checkedStep.checkedNodes do
        match e with
        | .assign a =>
          for t in a.plan.terms do
            IO.println s!"  step term iterationShape={t.iterationShape} contextPos={t.contextPos} outputPos={t.outputPos} reductionPos={t.reductionPos}"
            for f in t.factors do
              match f with
              | .iverson b =>
                let cols := boolCols b
                IO.println s!"    IVERSON {repr b}"
                IO.println s!"    referenced columns {cols}; references step/context column: {cols.any (t.contextPos.contains ·)}"
                IO.println s!"    table (allCoords over full iterationShape, step-major): {(allCoords t.iterationShape.toList).map fun c => match evalPosBool c b with | .ok true => 1 | .ok false => 0 | .error _ => 9}"
              | .read _ => pure ()
        | _ => pure ()
      IO.println s!"  renderScanNode: {match renderScanNode 0 sc with | .ok _ => "ok" | .error e => reprStr e}"
    | _ => pure ()
  match runPreparedDense pp inputs with
  | .ok r => IO.println s!"  Dense S: {r.env["S"]!.data}"
  | .error e => IO.println s!"  Dense error {repr e.cause}"

#eval show IO Unit from do
  probe "step-dependent [j <= l]" stepDep
  probe "step-free [j <= 1] (ScanIversonRefusalTest.iverStep shape)" stepFree

end PreflightStep
