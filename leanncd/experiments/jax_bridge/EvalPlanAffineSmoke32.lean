import LeanNCD.Eval.Entry
import LeanNCD.DSL.Compile
import LeanNCD.Eval.Plan.Adapter32
import EvalPlanCodegen
import Eval.PropertyOracle.Gen
import Eval.Plan.KernelDense32Test
import Eval.Plan.EvalPlan32Test

/-!
# Binary32 `affineReference` smoke + corpus slice driver (slice F32-JAX)

Every fixture crosses the real binary32 source boundary (`compileToScheduled →
InputSignature.ofDenseInputs32ForDecls → prepareEvalPlan → runPreparedDense32`) and is rendered by
the PRODUCTION gates — no shim — through `renderAffinePlanNamed`, `lowerCheckPlanToCandidate`, and
`validateAndConstructExecutable`, which must report `orderedReference32`. The same prepared plan is
also handed to `generateNamed .einsumOnly`, which must refuse it with `unsupportedStorageKind
.float32` (the dedicated einsum door). Inputs and Lean expected outputs are `Float32.toBits`
payloads (`pyTensorEntry32`, below — local to this driver, its only caller). Outside every Lake target, like the other drivers.

Four groups: the six `papers/f32_jax_spike_results.md` fixtures (two of which broke `einsumOnly`)
plus `termSum64` (the term-fold discriminator); every `stride`-th `PropertyOracle.enumPrograms` case
retagged binary32 (`retag32`); the standalone-assign route (`buildAssignFixture32`, the binary32
`KernelDense32Test` kernels + the zero-pad label-extent mismatch); and the positional route
(`buildPositionalFixture32`, the `EvalPlan32Test` graphs).
-/

namespace JaxBridge.AffineSmoke32

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.PropertyOracle Std
open JaxBridge

/-- `UInt32` list literal — the binary32 counterpart of `pyUInt64ListLit`. -/
def pyUInt32ListLit (xs : Array UInt32) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map toString) ++ "]"

/-- The binary32 counterpart of `EvalPlanCodegen.pyTensorEntry` (slice F32-JAX): `Float32.toBits` payloads, plus a
    `"dtype": "float32"` tag so a Python consumer reconstructs `np.uint32` bits and never mistakes
    them for binary64 ones. Binary64 entries stay untagged, byte-identical to before. -/
def pyTensorEntry32 (t : DenseTensor32) : String :=
  "{\"shape\": " ++ pyShapeTuple t.shape.toArray ++
  ", \"dtype\": \"float32\", \"bits\": " ++ pyUInt32ListLit (t.data.map Float32.toBits) ++ "}"

/-- Rebuild a source fixture for the binary32 graph: first `p.explicitF64` spells the corpus's
    binary64 reading out (it declares every undeclared used name, outputs included,
    `.typedTensor .f64`); then every `.tensor` and `.typedTensor .f64` declaration becomes
    `.typedTensor .f32` (axes unchanged), every statement output still lacking a declaration gets a
    binary32 one over its own LHS axes, and
    every DECLARED input converts with `Float.toFloat32` (the generator's inputs are small integers,
    exact in binary32); undeclared extra inputs are dropped. Nothing else changes, so the case set is the binary64 corpus's own. -/
def retag32 (p : TLProgram) (env : HashMap String DenseTensor) : TLProgram × NamedDenseEnv32 :=
  -- Under the f32 default flip an undeclared name is binary32, not binary64: first spell the
  -- source corpus's binary64 reading explicitly (`explicitF64`), then retag it to binary32.
  let p := p.explicitF64
  let decls := p.decls.map fun d => match d with
    | .tensor n ax => .typedTensor .f32 n ax
    | .typedTensor .f64 n ax => .typedTensor .f32 n ax
    | d => d
  let inDecls := decls.filterMap fun d => match d with
    | .typedTensor _ n _ => some n
    | _ => none
  -- Undeclared statement outputs default to binary64 (master plan §1.4 point 5), which would make
  -- every program a mixed-precision rejection; declare each one binary32 over its own LHS axes.
  let outDecls := p.stmts.foldl (init := ([] : List Decl)) fun acc st => match st with
    | .assign n lhs _ =>
        if inDecls.contains n || acc.any (fun d => match d with
            | .typedTensor _ m _ => m == n | _ => false) then acc
        else
          match lhs.mapM (fun s => match s with | .free a => some a | _ => none) with
          | some axes => acc ++ [.typedTensor .f32 n axes]
          | none => acc
    | _ => acc
  let decls := decls ++ outDecls
  let declared := inDecls
  -- `inputEnv` is shared by every generated program and also carries `P`, which only the
  -- contraction programs declare; an undeclared extra input would be read as binary64.
  let env32 : NamedDenseEnv32 := env.fold (init := {}) fun acc k t =>
    if declared.contains k then acc.insert k ⟨t.shape, t.data.map Float.toFloat32⟩ else acc
  ({ p with decls }, env32)

def prepare32 (name : String) (p : TLProgram) (inputs : NamedDenseEnv32) :
    IO (PreparedPlan × EvalReport32) := do
  let sched ← match p.compileToScheduled.run 0 with
    | .ok s _ => pure s
    | .error e _ => throw (IO.userError s!"{name} compile failed: {repr e}")
  let sig ← match InputSignature.ofDenseInputs32ForDecls sched.decls inputs with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name} binary32 signature failed: {repr e}")
  let prepared ← match prepareEvalPlan sched sig with
    | .ok p => pure p
    | .error f => throw (IO.userError s!"{name} prepare failed: {renderCompileCause f.cause}")
  unless prepared.plan.storageKind == .float32 do
    throw (IO.userError s!"{name} is not a binary32 plan")
  let report ← match runPreparedDense32 prepared inputs with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{name} binary32 Dense run failed: {repr e.cause}")
  pure (prepared, report)

def buildNamedFixture32 (name : String) (prog : TLProgram) (inputs : NamedDenseEnv32) :
    IO String := do
  let (prepared, report) ← prepare32 name prog inputs
  -- The dedicated einsum door: the same binary32 plan is refused, before any Python.
  match generateNamed .einsumOnly prepared with
  | .error (.unsupportedStorageKind .float32) => pure ()
  | other => throw (IO.userError s!"{name}: einsumOnly did not refuse binary32: {repr other.toOption}")
  -- The evidence claim, end to end through the production validator.
  match lowerCheckPlanToCandidate prepared with
  | .ok c =>
      match validateAndConstructExecutable c with
      | .ok e =>
          unless e.evidence == .orderedReference32 do
            throw (IO.userError s!"{name}: evidence {repr e.evidence}, expected orderedReference32")
      | .error e => throw (IO.userError s!"{name}: executable rejected: {repr e}")
  | .error e => throw (IO.userError s!"{name}: candidate rejected: {repr e}")
  let planData ← match renderAffinePlanNamed prepared with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name} affineReference render failed: {repr e}")
  let mut ins : Array String := #[]
  for b in prepared.bindings.requiredInputs.bindings do
    let t ← match inputs[b.name]? with
      | some t => pure t
      | none => throw (IO.userError s!"{name}: missing input {b.name}")
    ins := ins.push (pyStrLit b.name ++ ": " ++ pyTensorEntry32 t)
  let mut outs : Array String := #[]
  for b in prepared.bindings.materializedNames do
    let t ← match report.env[b.name]? with
      | some t => pure t
      | none => throw (IO.userError s!"{name}: materialized {b.name} absent")
    outs := outs.push (pyStrLit b.name ++ ": " ++ pyTensorEntry32 t)
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"named\", \"plan\": " ++ planData ++
    ", \"inputs\": {" ++ String.intercalate ", " ins.toList ++
    "}, \"expected\": {" ++ String.intercalate ", " outs.toList ++ "}}")

/-- The binary32 counterpart of `EvalPlanCodegen.buildAssignFixture`, over `checkAssignF32` and
    `runDenseAssign32`: also pins, per fixture, that the standalone einsum door refuses it and that
    its affine kernel validates as `orderedReference32`. `{"name", "kind": "assign", ...}`. -/
def buildAssignFixture32 (name : String) (sigs : Array TensorSignature) (a : AssignPlan)
    (store : Array DenseTensor32) : IO String := do
  let checked ← match checkAssignF32 sigs a with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"{name} binary32 check failed: {repr e}")
  let expected ← match runDenseAssign32 checked store with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"{name} binary32 Dense run failed: {repr e}")
  match lowerAssign sigs 0 checked with
  | .error (.unsupportedStorageKind .float32) => pure ()
  | _ => throw (IO.userError s!"{name}: standalone einsum door did not refuse binary32")
  match loweringToAffineTableCandidate sigs 0 checked with
  | .ok c =>
      match validateAndConstructKernel sigs (.affineTable c) with
      | .ok k =>
          unless k.evidence == .orderedReference32 do
            throw (IO.userError s!"{name}: kernel evidence {repr k.evidence}")
      | .error e => throw (IO.userError s!"{name}: kernel rejected: {repr e}")
  | .error e => throw (IO.userError s!"{name}: candidate rejected: {repr e}")
  let rendered ← match renderAffineAssign sigs checked with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name} render failed: {repr e}")
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"assign\", \"assign\": " ++ rendered ++
    ", \"store\": [" ++ String.intercalate ", " (store.toList.map pyTensorEntry32) ++
    "], \"expected\": " ++ pyTensorEntry32 expected ++ "}")

/-- Positional `CheckedEvalPlan` route over `runDensePlan32`; the einsum plan door (`lowerPlan`)
    must refuse it. `{"name", "kind": "positional", "plan", "inputs", "expected_store"}`. -/
def buildPositionalFixture32 (name : String) (raw : RawEvalPlan) (inputs : Array DenseTensor32) :
    IO String := do
  let checked ← match checkPlan raw with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"{name} graph check failed: {repr e}")
  unless checked.storageKind == .float32 do throw (IO.userError s!"{name} is not binary32")
  let expected ← match runDensePlan32 checked inputs with
    | .ok st => pure st
    | .error e => throw (IO.userError s!"{name} binary32 graph run failed: {repr e}")
  match lowerPlan checked with
  | .error (.unsupportedStorageKind .float32) => pure ()
  | _ => throw (IO.userError s!"{name}: einsum plan door did not refuse binary32")
  let planData ← match renderAffinePlanPositional checked with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name} positional render failed: {repr e}")
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"positional\", \"plan\": " ++ planData ++
    ", \"inputs\": [" ++ String.intercalate ", " (inputs.toList.map pyTensorEntry32) ++
    "], \"expected_store\": [" ++ String.intercalate ", " (expected.toList.map pyTensorEntry32) ++ "]}")

/-! ## The term-fold discriminator

`Y[i] := A[i] + B[i] + … + B[i] + D[i]` with 62 copies of `B`, `A = 2^24`, `B = 1`, `D = -2^24`: a
strict left fold absorbs every `1` (`2^24 + 1` ties to even, back to `2^24`) and ends at exactly `0`.
XLA CPU's `jnp.sum` over a stacked term axis is sequential up to 32 terms on the measured platform
but blocked at 64 (probe: `31`), so this — and not `termSum4` — is what distinguishes the runtime's
ordered term fold from a `jnp.sum` (mutant P2). Built from the AST because 64 source terms is not
something to type. -/

def ax4 : AxisSpec := ⟨"i", 1, .real⟩

def termSum64Prog : TLProgram :=
  let rd (n : String) : ProdTerm := ⟨[Factor.read n [.axis ax4]]⟩
  { decls := [.axis ax4 (some 4), .typedTensor .f32 "A" [ax4], .typedTensor .f32 "B" [ax4]
             , .typedTensor .f32 "D" [ax4], .typedTensor .f32 "Y" [ax4]]
  , stmts := [Stmt.assign "Y" [.free ax4]
      ({ body := ⟨[rd "A"] ++ List.replicate 62 (rd "B") ++ [rd "D"]⟩, nonlin := .identity
       , agg := .sum } : RHSExpr)] }

def termSum64In : NamedDenseEnv32 :=
  HashMap.ofList [("A", ⟨[4], Array.replicate 4 16777216.0⟩), ("B", ⟨[4], Array.replicate 4 1.0⟩)
                 , ("D", ⟨[4], Array.replicate 4 (-16777216.0)⟩)]

/-! ## The six spike fixtures -/

def gen32 (n : Nat) (f : Nat → Float) : Array Float32 := (Array.range n).map (fun k => (f k).toFloat32)
def t32 (shape : List Nat) (data : Array Float32) : DenseTensor32 := ⟨shape, data⟩
def env32 (xs : List (String × DenseTensor32)) : NamedDenseEnv32 := HashMap.ofList xs

def baselineProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 1
  tensor f32 W(i, j), x(j), b(i), Y(i)
  Y[i] := W[i, j] · x[j] + b[i]
}
def baselineIn : NamedDenseEnv32 :=
  env32 [("W", t32 [2, 1] #[2.0, 3.0]), ("x", t32 [1] #[5.0]), ("b", t32 [2] #[1.0, 1.0])]

def reduction64Prog : TLProgram := tlprog!{
  axis k : ℕ = 64
  tensor f32 A(k), B(k), Y()
  Y[] := A[k] · B[k]
}
def reduction64In : NamedDenseEnv32 :=
  env32 [("A", t32 [64] (#[16777216.0] ++ (Array.replicate 62 1.0) ++ #[-16777216.0]))
        , ("B", t32 [64] (Array.replicate 64 1.0))]

def termSum4Prog : TLProgram := tlprog!{
  axis i : ℕ = 4
  tensor f32 A(i), B(i), E(i), D(i), Y(i)
  Y[i] := A[i] + B[i] + E[i] + D[i]
}
def termSum4In : NamedDenseEnv32 :=
  env32 [("A", t32 [4] (Array.replicate 4 16777216.0)), ("B", t32 [4] (Array.replicate 4 1.0))
        , ("E", t32 [4] (Array.replicate 4 1.0)), ("D", t32 [4] (Array.replicate 4 (-16777216.0)))]

def factorProduct3Prog : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 8
  tensor f32 A(i, j), B(i, j), E(j), Y(i)
  Y[i] := A[i, j] · B[i, j] · E[j]
}
def factorProduct3In : NamedDenseEnv32 :=
  env32 [("A", t32 [2, 8] (gen32 16 (fun n => n.toFloat * 0.0137 + 0.41)))
        , ("B", t32 [2, 8] (gen32 16 (fun n => n.toFloat * 0.0091 + 1.07)))
        , ("E", t32 [8] (gen32 8 (fun n =>
            (if n % 2 == 0 then 1.0 else -1.0) * (n.toFloat * 0.273 + 0.53))))]

def mixedMagnitudeProg : TLProgram := tlprog!{
  axis k : ℕ = 16
  tensor f32 A(k), Y()
  Y[] := A[k]
}
def mixedMagnitudeIn : NamedDenseEnv32 :=
  env32 [("A", t32 [16] (gen32 16 (fun n => if n % 2 == 0 then 10000.0 else 0.0001)))]

def contraction64Prog : TLProgram := tlprog!{
  axis i : ℕ = 64
  axis j : ℕ = 64
  tensor f32 W(i, j), x(j), Y(i)
  Y[i] := W[i, j] · x[j]
}
def contraction64In : NamedDenseEnv32 :=
  env32 [("W", t32 [64, 64] (gen32 4096 (fun n => n.toFloat * 0.00031 + 0.17)))
        , ("x", t32 [64] (gen32 64 (fun n =>
            (if n % 2 == 0 then 1.0 else -1.0) * (n.toFloat * 0.013 + 0.2))))]

end JaxBridge.AffineSmoke32

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.PropertyOracle Std
open JaxBridge JaxBridge.AffineSmoke32

def main (args : List String) : IO Unit := do
  let outputPath := args.head?.getD "generated_evalplan_affine_smoke32.py"
  let stride := (args.drop 1).head?.bind String.toNat? |>.getD 100
  let spike ← #[
      ("baseline", baselineProg, baselineIn),
      ("reduction64", reduction64Prog, reduction64In),
      ("termSum4", termSum4Prog, termSum4In),
      ("factorProduct3", factorProduct3Prog, factorProduct3In),
      ("mixedMagnitude", mixedMagnitudeProg, mixedMagnitudeIn),
      ("contraction64x64", contraction64Prog, contraction64In),
      ("termSum64", termSum64Prog, termSum64In)
    ].mapM (fun (nm, p, i) => buildNamedFixture32 nm p i)
  -- Standalone-assign route: every binary32 kernel fixture `KernelDense32Test` exports (all reused,
  -- none declared here) plus the zero-pad label-extent mismatch from `EvalPlanCodegen`.
  let assign ← #[
      buildAssignFixture32 "f32Identity"
        KernelDense32Test.identitySigs32 KernelDense32Test.f32Identity KernelDense32Test.f32IdentityStore,
      buildAssignFixture32 "f32ReductionRounding"
        KernelDense32Test.redSigs32 KernelDense32Test.f32ReductionRounding KernelDense32Test.f32ReductionStore,
      buildAssignFixture32 "f32MultiplicationRounding"
        KernelDense32Test.scalarSigs32 KernelDense32Test.f32MultiplicationRounding KernelDense32Test.mulStore,
      buildAssignFixture32 "f32FactorOrder"
        KernelDense32Test.factorOrderSigs32 KernelDense32Test.f32FactorOrder KernelDense32Test.factorOrderStore32,
      buildAssignFixture32 "f32Efp"
        KernelDense32Test.efpSigs32 KernelDense32Test.f32Efp KernelDense32Test.efpStore32,
      buildAssignFixture32 "f32Zerd"
        KernelDense32Test.zerdSigs32 KernelDense32Test.f32Zerd KernelDense32Test.zerdStore32,
      buildAssignFixture32 "f32TermOrder"
        KernelDense32Test.termOrderSigs32 KernelDense32Test.f32TermOrder KernelDense32Test.termOrderStore32,
      buildAssignFixture32 "f32Pad" f32PadSigs f32PadAssign
        #[⟨[2], #[(5.0 : Float32), 7.0]⟩, ⟨[3], #[]⟩]
    ].mapM id
  let positional ← #[
      buildPositionalFixture32 "f32ProductChain"
        EvalPlan32Test.f32ProductChain EvalPlan32Test.productChainInputs,
      buildPositionalFixture32 "f32ReductionGraph"
        EvalPlan32Test.f32ReductionGraph EvalPlan32Test.reductionGraphInputs
    ].mapM id
  let mut corpus : Array String := #[]
  let all := enumPrograms.toArray
  for h : k in [0 : all.size] do
    if k % stride == 0 then
      let (p, env) := all[k]
      let (p32, env32) := retag32 p env
      corpus := corpus.push (← buildNamedFixture32 s!"corpus{k}" p32 env32)
  let fixtures := spike ++ assign ++ positional ++ corpus
  IO.FS.writeFile outputPath
    ("# Generated by EvalPlanAffineSmoke32.lean — do not edit.\nFIXTURES = [\n" ++
      String.intercalate ",\n" fixtures.toList ++ "\n]\n")
  IO.println s!"Generated {outputPath}: {spike.size} named + {assign.size} assign + \
{positional.size} positional + {corpus.size} corpus (stride {stride} of {all.size})"
