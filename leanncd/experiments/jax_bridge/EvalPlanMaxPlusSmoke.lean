import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter32
import EvalPlanCodegen

namespace JaxBridge.MaxPlusSmoke
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std JaxBridge
def dense (s : List Nat) (d : Array Float) : DenseTensor := ⟨s, d⟩
def retag32 (p : TLProgram) : TLProgram :=
  { p with decls := p.decls.map fun d => match d with
      | .typedTensor .f64 n ax => .typedTensor .f32 n ax
      | d => d }
def compile (name : String) (p : TLProgram) : IO ScheduledProgram :=
  match p.compileToScheduled.run 0 with
  | .ok s _ => pure s | .error e _ => throw (IO.userError s!"{name}: {repr e}")
def prepare (name : String) (s : ScheduledProgram) (sig : InputSignature) : IO PreparedPlan :=
  match prepareEvalPlan s sig with
  | .ok p => pure p | .error e => throw (IO.userError s!"{name}: {renderCompileCause e.cause}")

def gateMatrix : Bool := Id.run do
  for alg in [admittedAlgebraMax, admittedAlgebraMin, admittedAlgebraBool] do
    let sigs := if alg == admittedAlgebraBool then
      idSigs.modify 1 (fun s => { s with dtype := .bool }) else idSigs
    let .ok c := checkAssign sigs { idAssign with algebra := alg } | return false
    if alg == admittedAlgebraMax then
      unless (renderAffineAssign sigs c).isOk do return false
    else
      unless (renderAffineAssign sigs c).toOption.isNone do return false
    unless (checkJaxAssignSupport sigs 7 c).toOption.isNone &&
      (loweringToAffineTableCandidate sigs 7 c).toOption.isNone &&
      (loweringToEinsumCandidate sigs 7 c).toOption.isNone do return false
    let tables := c.plan.terms.map fun t => t.factors.filterMap fun f => match f with
      | .iverson _ => none
      | .read r =>
          let (safeIndex, validMask) := buildFactorTable t.iterationShape r
          some ({ source := r.sourceSlot, safeIndex, validMask } : AffineTableReadCandidate)
    unless (validateAndConstructKernel sigs (.affineTable { semanticAssignment := c, tables })).toOption.isNone &&
      (validateAndConstructKernel sigs (.einsum { semanticAssignment := c, destination := 1, operands := #[#[0, 0]], outputAxes := #[0] })).toOption.isNone do return false
  let .ok c := checkAssign idSigs { idAssign with algebra := admittedAlgebraMax } | return false
  unless (match renderAffineAssign (idSigs.modify 0 (fun s => { s with shape := #[4] })) c with
    | .error (.invalidSignatureContext 0 _) => true | _ => false) do return false
  let .ok iv := checkAssign idSigs { idIversonAssign with algebra := admittedAlgebraMax } | return false
  unless (match renderAffineAssign idSigs iv with
    | .error (.iversonFactor 0 0 _) => true | _ => false) do return false
  return true

run_cmd unless gateMatrix do throwError "MAX-T3-GATE-MATRIX: render-only admission leaked"

def pyTensor32 (t : DenseTensor32) : String :=
  "{\"shape\": " ++ pyShapeTuple t.shape.toArray ++ ", \"bits\": [" ++
  String.intercalate ", " (t.data.toList.map fun x => toString x.toBits) ++ "]}"

def rawFixture (name : String) (sigs : Array TensorSignature) (a : AssignPlan)
    (store : Array DenseTensor) : IO String := do
  let a32 := { a with algebra := if a.algebra == admittedAlgebraMax then admittedAlgebraF32Max
    else if a.algebra == admittedAlgebra then admittedAlgebraF32 else a.algebra }
  let sigs32 := sigs.map fun s => { s with dtype := if s.dtype == .f64 then .f32 else s.dtype }
  let c ← match checkAssign sigs a with
    | .ok x => pure x | .error e => throw (IO.userError s!"{name}: check64 {repr e}")
  let c32 ← match checkAssignF32 sigs32 a32 with
    | .ok x => pure x | .error e => throw (IO.userError s!"{name}: check32 {repr e}")
  let expected ← match runDenseAssign c store with
    | .ok x => pure x | .error e => throw (IO.userError s!"{name}: run64 {repr e}")
  let store32 : Array DenseTensor32 := store.map fun t => ⟨t.shape, t.data.map Float.toFloat32⟩
  let expected32 ← match runDenseAssign32 c32 store32 with
    | .ok x => pure x | .error e => throw (IO.userError s!"{name}: run32 {repr e}")
  let node ← match renderAffineAssign sigs c with
    | .ok x => pure x | .error e => throw (IO.userError s!"{name}: render64 {repr e}")
  let node32 ← match renderAffineAssign sigs32 c32 with
    | .ok x => pure x | .error e => throw (IO.userError s!"{name}: render32 {repr e}")
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"assign64\": " ++ node ++
    ", \"assign32\": " ++ node32 ++ ", \"store64\": [" ++
    String.intercalate ", " (store.toList.map pyTensorEntry) ++ "], \"store32\": [" ++
    String.intercalate ", " (store32.toList.map pyTensor32) ++ "], \"expected64\": " ++
    pyTensorEntry expected ++ ", \"expected32\": " ++ pyTensor32 expected32 ++ "}")

def vectorRaw (alg : ContractionAlgebra) (r : ReadPlan) (n : Nat) : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[n], algebra := alg
    terms := #[{ contextPos := #[], iterationShape := #[n], outputPos := #[0], reductionPos := #[], factors := #[.read r] }] }

def mixedContextProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  iter t = 4
  tensor f64 X(i), Y(t, i), S(i, t), R(i, t)
  S[i, 0] := X[i]
  R[i, 0] := maxreduce(X[i])
  S[i, t +1] := Y[t, i]
  R[i, t +1] := maxreduce(Y[t, i])
}

def mixedContextFixture : IO String := do
  let name := "scan_mixed_init_holes"
  let inputs : NamedDenseEnv := HashMap.ofList [("X", dense [2] #[3, 5]), ("Y", dense [4, 2] #[7, 11, 13, 17, 19, 23, 29, 31])]
  let mut fields := []
  for is32 in [false, true] do
    let s ← compile name (if is32 then retag32 mixedContextProg else mixedContextProg)
    let inputs32 : NamedDenseEnv32 := inputs.map fun _ t => ⟨t.shape, t.data.map Float.toFloat32⟩
    let sig ← if is32 then match InputSignature.ofDenseInputs32ForDecls s.decls inputs32 with
      | .ok x => pure x | .error e => throw (IO.userError s!"{repr e}")
      else match InputSignature.ofDenseInputsForDecls s.decls inputs with
      | .ok x => pure x | .error e => throw (IO.userError s!"{repr e}")
    let p ← prepare name s sig
    let #[.scan sc] := p.plan.raw.steps | throw (IO.userError "mixed: expected one scan")
    unless sc.states.size == 2 && sc.states.any (·.initValue == .zero) &&
        sc.states.any (·.initValue == .negInf) do
      throw (IO.userError "mixed: expected two states with distinct zero/negInf init")
    let sigs := p.plan.raw.tensorSigs
    let steps := sc.baseBlock.steps.map fun step => match step with
      | .assign base => .assign { base with outputShape := #[], terms := base.terms.map fun t =>
          { t with iterationShape := #[], outputPos := #[], factors := t.factors.map fun f => match f with
            | .read r => .read { r with map := LeanNCD.Eval.Plan.AffineMap.mk (r.map.coeffs.map fun _ => #[]) r.map.bias }
            | .iverson b => .iverson b } }
      | x => x
    let mut block := { sc.baseBlock with steps := steps }
    for step in steps do
      let .assign base := step | throw (IO.userError "mixed: expected base assign")
      block := { block with tensorSigs := block.tensorSigs.modify base.destinationSlot (fun s => { s with shape := #[] }) }
    let writes := sc.baseWrites.map fun w => { w with map := LeanNCD.Eval.Plan.AffineMap.mk (w.map.coeffs.map fun _ => #[]) w.map.bias }
    let sc := { sc with baseBlock := block, baseWrites := writes }
    let c ← match (if is32 then checkScanPlanF32 else checkScanPlan) sigs sc with
      | .ok x => pure x | .error e => throw (IO.userError s!"mixed check: {repr e}")
    let rendered ← match renderScanNode 0 c with
      | .ok x => pure x | .error e => throw (IO.userError s!"mixed render: {repr e}")
    let mut store := sigs.map fun sig =>
      dense sig.shape.toList (Array.replicate (sig.shape.foldl (· * ·) 1) 0)
    for b in p.bindings.requiredInputs.bindings do
      let some t := inputs[b.name]? | throw (IO.userError "missing mixed input")
      store := store.set! b.slot t
    let result ← if is32 then
      match runDenseScan32 c.sigs c (store.map fun t => ⟨t.shape, t.data.map Float.toFloat32⟩) with
      | .ok x => pure ("[" ++ String.intercalate ", " (x.toList.map pyTensor32) ++ "]")
      | .error e => throw (IO.userError s!"mixed run32: {repr e}")
      else match runDenseScan c.sigs c store with
      | .ok x => pure ("[" ++ String.intercalate ", " (x.toList.map pyTensorEntry) ++ "]")
      | .error e => throw (IO.userError s!"mixed run64: {repr e}")
    let suffix := if is32 then "32" else "64"
    fields := fields ++ [pyStrLit ("scan" ++ suffix) ++ ": " ++ rendered,
      pyStrLit ("store" ++ suffix) ++ ": [" ++ String.intercalate ", "
        (store.toList.map fun t => if is32 then pyTensor32 ⟨t.shape, t.data.map Float.toFloat32⟩ else pyTensorEntry t) ++ "]",
      pyStrLit ("expected" ++ suffix) ++ ": " ++ result]
  pure ("{\"name\": " ++ pyStrLit name ++ ", " ++ String.intercalate ", " fields ++ "}")

def adversarial : IO (List String) := do
  let nan : Float := 0.0 / 0.0
  let inf : Float := 1.0 / 0.0
  let nz : Float := Float.ofBits 9223372036854775808
  let values := #[0, nz, -2, 0.25, nan, inf, -inf]
  let r : ReadPlan := { sourceSlot := 0, sourceShape := #[7], map := LeanNCD.Eval.Plan.AffineMap.mk #[#[1]] #[0], oobPolicy := .zeroPad }
  let mut out := []
  for flag in [true, false] do
    out := out ++ [← rawFixture s!"bool_to_tropical_{flag}" #[⟨#[7], .bool⟩, ⟨#[7], .f64⟩]
      (vectorRaw admittedAlgebraMax { r with boolToTropical := flag } 7) #[dense [7] values]]
  let empty : AssignPlan := { contextShape := #[], destinationSlot := 0, outputShape := #[], algebra := admittedAlgebraMax, terms := #[] }
  out := out ++ [← rawFixture "max_empty_terms" #[⟨#[], .f64⟩] empty #[]]
  out := out ++ [← rawFixture "max_empty_factors" #[⟨#[], .f64⟩]
    { empty with terms := #[{ contextPos := #[], iterationShape := #[], outputPos := #[], reductionPos := #[], factors := #[] }] } #[]]
  out := out ++ [← rawFixture "max_zero_reduction" #[⟨#[], .f64⟩]
    { empty with terms := #[{ contextPos := #[], iterationShape := #[0], outputPos := #[], reductionPos := #[0], factors := #[] }] } #[]]
  let oob : ReadPlan := { r with sourceShape := #[1] }
  out := out ++ [← rawFixture "max_bare_oob" #[⟨#[1], .f64⟩, ⟨#[3], .f64⟩]
    (vectorRaw admittedAlgebraMax oob 3) #[dense [1] #[2]]]
  out := out ++ [← rawFixture "max_log_oob_bypass" #[⟨#[0], .f64⟩, ⟨#[3], .f64⟩]
    (vectorRaw admittedAlgebraMax { oob with sourceShape := #[0], unary := some .log } 3) #[dense [0] #[]]]
  let poison := vectorRaw admittedAlgebraMax { r with sourceShape := #[1] } 1
  let term := poison.terms[0]!
  out := out ++ [← rawFixture "false_source_opposing_infinity"
    #[⟨#[1], .bool⟩, ⟨#[1], .f64⟩, ⟨#[1], .f64⟩]
    { poison with destinationSlot := 2, terms := #[{ term with factors :=
      #[.read { r with sourceShape := #[1], boolToTropical := true },
        .read { r with sourceSlot := 1, sourceShape := #[1] }] }] }
    #[dense [1] #[0], dense [1] #[inf]]]
  out := out ++ [← rawFixture "max_empty_output" #[⟨#[0], .f64⟩]
    { empty with outputShape := #[0], terms := #[{ contextPos := #[], iterationShape := #[0], outputPos := #[0], reductionPos := #[], factors := #[] }] } #[]]
  let scalarRead : ReadPlan := { sourceSlot := 0, sourceShape := #[], map := LeanNCD.Eval.Plan.AffineMap.mk #[] #[], oobPolicy := .zeroPad }
  out := out ++ [← rawFixture "max_factor_order_cancellation"
    #[⟨#[], .f64⟩, ⟨#[], .f64⟩, ⟨#[], .f64⟩, ⟨#[], .f64⟩]
    { empty with destinationSlot := 3, terms := #[{ contextPos := #[], iterationShape := #[], outputPos := #[], reductionPos := #[], factors := #[.read scalarRead,
        .read { scalarRead with sourceSlot := 1 }, .read { scalarRead with sourceSlot := 2 }] }] }
    #[dense [] #[18014398509481984], dense [] #[-18014398509481984], dense [] #[1]]]
  out := out ++ [← rawFixture "max_reciprocal_partial_oob" #[⟨#[1], .f64⟩, ⟨#[3], .f64⟩]
    (vectorRaw admittedAlgebraMax { oob with unary := some .recip } 3) #[dense [1] #[2]]]
  out := out ++ [← mixedContextFixture]
  return out

def contextProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  iter t = 4
  tensor f64 X(i), Y(t, i), S(i, t)
  S[i, 0] := X[i]
  S[i, t +1] := maxreduce(Y[t, i])
}

def contextFixture : IO String := do
  let inputs : NamedDenseEnv := HashMap.ofList [("X", dense [2] #[3, 5]), ("Y", dense [4, 2] #[7, 11, 13, 17, 19, 23, 29, 31])]
  let mut fields := []
  for is32 in [false, true] do
    let s ← compile "context_holes" (if is32 then retag32 contextProg else contextProg)
    let inputs32 : NamedDenseEnv32 := inputs.map fun _ t => ⟨t.shape, t.data.map Float.toFloat32⟩
    let sig ← if is32 then match InputSignature.ofDenseInputs32ForDecls s.decls inputs32 with
      | .ok x => pure x | .error e => throw (IO.userError s!"{repr e}")
      else match InputSignature.ofDenseInputsForDecls s.decls inputs with
      | .ok x => pure x | .error e => throw (IO.userError s!"{repr e}")
    let p ← prepare "context_holes" s sig
    let #[.scan sc] := p.plan.raw.steps | throw (IO.userError "expected scan")
    let sigs := p.plan.raw.tensorSigs
    let #[.assign base] := sc.baseBlock.steps | throw (IO.userError "expected base assign")
    let terms := base.terms.map fun t => { t with iterationShape := #[], outputPos := #[], factors := t.factors.map fun f =>
      match f with
      | .read r => .read { r with map := LeanNCD.Eval.Plan.AffineMap.mk (r.map.coeffs.map fun _ => #[]) r.map.bias }
      | .iverson b => .iverson b }
    let base := { base with outputShape := #[], terms := terms }
    let block := { sc.baseBlock with tensorSigs := sc.baseBlock.tensorSigs.modify base.destinationSlot (fun s => { s with shape := #[] }), steps := #[.assign base] }
    let writes := sc.baseWrites.map fun w => { w with map := LeanNCD.Eval.Plan.AffineMap.mk (w.map.coeffs.map fun _ => #[]) w.map.bias }
    let sc := { sc with baseBlock := block, baseWrites := writes }
    let c ← match (if is32 then checkScanPlanF32 else checkScanPlan) sigs sc with
      | .ok x => pure x | .error e => throw (IO.userError s!"holes check: {repr e}")
    let rendered ← match renderScanNode 0 c with
      | .ok x => pure x | .error e => throw (IO.userError s!"holes render: {repr e}")
    let mut store := sigs.map fun sig =>
      dense sig.shape.toList (Array.replicate (sig.shape.foldl (· * ·) 1) 0)
    for b in p.bindings.requiredInputs.bindings do
      let some t := inputs[b.name]? | throw (IO.userError "missing input")
      store := store.set! b.slot t
    let result ← if is32 then
      match runDenseScan32 c.sigs c (store.map fun t => ⟨t.shape, t.data.map Float.toFloat32⟩) with
      | .ok x => pure ("[" ++ String.intercalate ", " (x.toList.map pyTensor32) ++ "]")
      | .error e => throw (IO.userError s!"holes run32: {repr e}")
      else match runDenseScan c.sigs c store with
      | .ok x => pure ("[" ++ String.intercalate ", " (x.toList.map pyTensorEntry) ++ "]")
      | .error e => throw (IO.userError s!"holes run64: {repr e}")
    let suffix := if is32 then "32" else "64"
    fields := fields ++ [pyStrLit ("scan" ++ suffix) ++ ": " ++ rendered,
      pyStrLit ("store" ++ suffix) ++ ": [" ++ String.intercalate ", "
        (store.toList.map fun t => if is32 then pyTensor32 ⟨t.shape, t.data.map Float.toFloat32⟩ else pyTensorEntry t) ++ "]",
      pyStrLit ("expected" ++ suffix) ++ ": " ++ result]
  pure ("{\"name\": \"scan_context_holes\", " ++ String.intercalate ", " fields ++ "}")


end JaxBridge.MaxPlusSmoke
def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "usage: MaxPlus OUTPUT.py")
  let adv ← JaxBridge.MaxPlusSmoke.adversarial
  let ctx ← JaxBridge.MaxPlusSmoke.contextFixture
  IO.FS.writeFile out ("ADVERSARIAL = [\n" ++ String.intercalate ",\n" (adv ++ [ctx]) ++ "\n]\n")
  IO.println s!"max-plus: generated {adv.length + 1} checked edge cases"
