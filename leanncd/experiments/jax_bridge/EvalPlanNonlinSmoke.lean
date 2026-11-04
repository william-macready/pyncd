import LeanNCD.Eval.Entry
import LeanNCD.DSL.Compile
import LeanNCD.Eval.Plan.Adapter32
import EvalPlanCodegen

/-!
# JAX pointwise/axiswise smoke — driver (JAX pointwise slice, tolerance-compared)

Emits static plan DATA (`renderAffinePlanNamed`) for source programs whose prepared plan CONTAINS
`.pointwise`/`.axiswise` steps, plus the Lean reference worker's own result (`runPreparedDense` /
`runPreparedDense32`) as raw bit payloads, for `evalplan_nonlin_smoke.py` to compare against the
committed runtime (`evalplan_affine_runtime.py`) WITHIN A TOLERANCE (the libm-vs-XLA `exp`/`tanh`/
`pow`/`sqrt` difference). Two outputs: argv[0] the binary64 module, argv[1] the binary32 module.
Like the other drivers it lives outside every Lake target; run via `lake env lean --run`
(`run-evalplan-nonlin.sh`).

Every fixture asserts, before any Python is written, that its prepared plan really has at least the
expected number of pointwise/axiswise steps (a program that silently compiled to plain assignments
would test nothing), that `einsumOnly` and the evidence door (`lowerCheckPlanToCandidate`) still
refuse it, and that `affineReference` renders it.
-/

namespace JaxBridge.NonlinSmoke

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std
open JaxBridge

/-- Local copy of `EvalPlanScatterSmoke`'s binary32 payload renderer (a `main` file cannot be
    imported). Parked: factor the drivers' copies into `EvalPlanCodegen`. -/
def pyTensorEntry32 (t : DenseTensor32) : String :=
  "{\"shape\": " ++ pyShapeTuple t.shape.toArray ++ ", \"dtype\": \"float32\", \"bits\": [" ++
  String.intercalate ", " (t.data.toList.map fun x => toString x.toBits) ++ "]}"

def countSteps (p : PreparedPlan) : Nat × Nat :=
  p.plan.raw.steps.foldl (fun (pw, aw) st => match st with
    | .pointwise _ => (pw + 1, aw) | .axiswise _ => (pw, aw + 1) | _ => (pw, aw)) (0, 0)

/-- Exact step-kind counts `(assign, pointwise, axiswise)`; any other step kind is counted nowhere,
    so a plan with a scatter or scan step fails an exact pin. -/
def countKinds (p : PreparedPlan) : Nat × Nat × Nat :=
  p.plan.raw.steps.foldl (fun (a, pw, aw) st => match st with
    | .assign _ => (a + 1, pw, aw) | .pointwise _ => (a, pw + 1, aw)
    | .axiswise _ => (a, pw, aw + 1) | _ => (a, pw, aw)) (0, 0, 0)

/-- The assertions every fixture shares; returns the rendered plan data. `exact`, when given, pins
    the total step count and the `(assign, pointwise, axiswise)` counts exactly, so a silent change
    to how a program compiles is loud. -/
def checkAndRender (name : String) (p : PreparedPlan) (minPw minAw : Nat)
    (exact : Option (Nat × Nat × Nat) := none) : IO String := do
  let (pw, aw) := countSteps p
  unless pw ≥ minPw && aw ≥ minAw do
    throw (IO.userError s!"{name}: expected >= {minPw} pointwise and >= {minAw} axiswise steps, prepared plan has {pw} and {aw}")
  if let some (ea, epw, eaw) := exact then
    let (a, pw', aw') := countKinds p
    unless (a, pw', aw') == (ea, epw, eaw) && p.plan.raw.steps.size == ea + epw + eaw do
      throw (IO.userError s!"{name}: expected {ea} assign / {epw} pointwise / {eaw} axiswise ({ea + epw + eaw} steps), prepared plan has {a} / {pw'} / {aw'} ({p.plan.raw.steps.size} steps)")
  match generateNamed .einsumOnly p with
  | .error (.unsupportedStep _) | .error (.unsupportedStorageKind _) => pure ()
  | other => throw (IO.userError s!"{name}: einsumOnly did not refuse: {repr other.toOption}")
  match lowerCheckPlanToCandidate p with
  | .error (.unsupportedStep _) | .error (.unsupportedStorageKind _) => pure ()
  | _ => throw (IO.userError s!"{name}: the evidence door did not refuse")
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

def header (name : String) (p : PreparedPlan) (planData : String) : String :=
  let (pw, aw) := countSteps p
  "{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"named\", \"n_pointwise\": " ++ toString pw ++
    ", \"n_axiswise\": " ++ toString aw ++ ", \"plan\": " ++ planData

/-- One binary64 named fixture. -/
def fixture64 (name : String) (prog : TLProgram) (inputs : HashMap String DenseTensor)
    (minPw : Nat := 0) (minAw : Nat := 0) (exact : Option (Nat × Nat × Nat) := none) : IO String := do
  let sched ← scheduled name prog
  let p ← prepared name sched (InputSignature.ofDenseInputs inputs)
  let planData ← checkAndRender name p minPw minAw exact
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
  pure (header name p planData ++ ", \"inputs\": {" ++ String.intercalate ", " ins.toList ++
    "}, \"expected\": {" ++ String.intercalate ", " outs.toList ++ "}}")

/-- The binary32 sibling, over `runPreparedDense32`; also pins that the plan is binary32. -/
def fixture32 (name : String) (prog : TLProgram) (inputs : NamedDenseEnv32)
    (minPw : Nat := 0) (minAw : Nat := 0) (exact : Option (Nat × Nat × Nat) := none) : IO String := do
  let sched ← scheduled name prog
  let sig ← match InputSignature.ofDenseInputs32ForDecls sched.decls inputs with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name} binary32 signature failed: {repr e}")
  let p ← prepared name sched sig
  unless p.plan.storageKind == .float32 do throw (IO.userError s!"{name} is not a binary32 plan")
  let planData ← checkAndRender name p minPw minAw exact
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
  pure (header name p planData ++ ", \"inputs\": {" ++ String.intercalate ", " ins.toList ++
    "}, \"expected\": {" ++ String.intercalate ", " outs.toList ++ "}}")

def t64 (shape : List Nat) (data : Array Float) : DenseTensor := ⟨shape, data⟩
def t32 (shape : List Nat) (data : Array Float) : DenseTensor32 :=
  ⟨shape, data.map Float.toFloat32⟩
def env64 (xs : List (String × DenseTensor)) : HashMap String DenseTensor := HashMap.ofList xs
def env32 (xs : List (String × DenseTensor32)) : NamedDenseEnv32 := HashMap.ofList xs

/-! ## Programs (binary64; the binary32 siblings differ only in the `f32` tag) -/

-- All five pointwise functions over one input (negative, zero, signed zero, positive).
def pwProg : TLProgram := tlprog!{
  axis i : ℕ = 7
  tensor f64 X(i), R(i), S(i), Th(i), G(i), L(i)
  R[i] := relu(X[i])
  S[i] := sigmoid(X[i])
  Th[i] := tanh(X[i])
  G[i] := gelu(X[i])
  L[i] := leakyrelu(X[i])
}
-- The three axiswise functions along the last axis of a `[2, 4]` tensor.
def awProg : TLProgram := tlprog!{
  axis q : ℕ = 2
  axis s : ℕ = 4
  tensor f64 A(q, s), Sm(q, s), Nm(q, s), L2(q, s)
  Sm[q, s.] := softmax(A[q, s])
  Nm[q, s.] := normalize(A[q, s])
  L2[q, s.] := l2normalize(A[q, s])
}
-- Causal mask `s ≤ q` (donor: `test/Eval/EvalExamplesTest.lean` example 2): softmax, normalize, L2.
def causalProg : TLProgram := tlprog!{
  axis q : ℕ = 3
  axis s : ℕ = 3
  tensor f64 X(q, s), Sm(q, s), Nm(q, s), L2(q, s)
  Sm[q, s.] := softmax(where s ≤ q)(X[q, s])
  Nm[q, s.] := normalize(where s ≤ q)(X[q, s])
  L2[q, s.] := l2normalize(where s ≤ q)(X[q, s])
}
-- Strict mask `s < q`: row q=0 has NO unmasked entry (all zeros, not uniform).
def allMaskedProg : TLProgram := tlprog!{
  axis q : ℕ = 3
  axis s : ℕ = 3
  tensor f64 X(q, s), Sm(q, s), Nm(q, s)
  Sm[q, s.] := softmax(where s < q)(X[q, s])
  Nm[q, s.] := normalize(where s < q)(X[q, s])
}
-- Softmax over the FIRST axis (`q.`), a non-last axis, of a `[3, 2]` tensor.
def firstAxisProg : TLProgram := tlprog!{
  axis q : ℕ = 3
  axis s : ℕ = 2
  tensor f64 A(q, s), Y(q, s)
  Y[q., s] := softmax(A[q, s])
}
-- Rank 3: softmax over the last axis and over the MIDDLE axis.
def rank3Prog : TLProgram := tlprog!{
  axis b : ℕ = 2
  axis q : ℕ = 2
  axis s : ℕ = 3
  tensor f64 A(b, q, s), Last(b, q, s), Mid(b, q, s)
  Last[b, q, s.] := softmax(A[b, q, s])
  Mid[b, q., s] := softmax(A[b, q, s])
}
-- assign -> pointwise (donor: example 10) and assign -> axiswise (donor: example 12 unmasked).
def chainProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 2
  axis q : ℕ = 2
  axis s : ℕ = 2
  axis d : ℕ = 2
  tensor f64 W(i, k), X(k), Y(i), Q(q, d), K(s, d), A(q, s)
  Y[i] := relu(W[i, k] · X[k])
  A[q, s.] := softmax(Q[q, d] · K[s, d])
}
-- Reduction ORDER: one row whose left-to-right sum differs from every other order. `[1e16, 1, -1e16, 1]`:
-- the forward fold gives 1 (so the row is `x / 1`), the reversed fold and the pairwise tree give 0
-- (so the row would be all zeros).
def orderProg : TLProgram := tlprog!{
  axis s : ℕ = 4
  tensor f64 A(s), Nm(s)
  Nm[s.] := normalize(A[s])
}
-- The repo's one-layer transformer (donor: `test/Eval/EvalExamplesTest.lean` example 12, nine
-- equations verbatim), explicit binary64. Sizes SEQ=3 (q, s), D=4 (m), H=2 (h), K=2 (k), DFF=4 (d).
-- Plan: 10 assignments, 3 axiswise (causal softmax, two normalize), 1 pointwise (relu).
-- Every tensor is declared `f64` by hand (what `TLProgram.explicitF64` would add): that helper lives
-- in the test library, which this driver's run script does not build.
def transformerProg : TLProgram := tlprog!{
  tensor f64 X(q, m), W_Q(h, k, m), W_K(h, k, m), W_V(h, k, m), W_O(m, h, k), W_in(d, m), W_out(m, d)
  tensor f64 Q(q, h, k), K(s, h, k), V(s, h, k), AttnOut(q, h, k), Attn(q, m), F(q, d), Y(q, m)
  Q[q, h, k]       := W_Q[h, k, m] · X[q, m]
  K[s, h, k]       := W_K[h, k, m] · X[s, m]
  V[s, h, k]       := W_V[h, k, m] · X[s, m]
  tensor f64 S(h, q, s)
  S[h, q, s.]      := softmax(where s ≤ q)(Q[q, h, k] · K[s, h, k])
  AttnOut[q, h, k] := S[h, q, s] · V[s, h, k]
  Attn[q, m]       := W_O[m, h, k] · AttnOut[q, h, k]
  tensor f64 A(q, m)
  A[q, m.]         := normalize(Attn[q, m] + X[q, m])
  F[q, d]          := relu(W_in[d, m] · A[q, m])
  Y[q, m]          := W_out[m, d] · F[q, d]
  tensor f64 H(q, m)
  H[q, m.]         := normalize(Y[q, m] + A[q, m])
}

def pwProg32 : TLProgram := tlprog!{
  axis i : ℕ = 7
  tensor f32 X(i), R(i), S(i), Th(i), G(i), L(i)
  R[i] := relu(X[i])
  S[i] := sigmoid(X[i])
  Th[i] := tanh(X[i])
  G[i] := gelu(X[i])
  L[i] := leakyrelu(X[i])
}
def awProg32 : TLProgram := tlprog!{
  axis q : ℕ = 2
  axis s : ℕ = 4
  tensor f32 A(q, s), Sm(q, s), Nm(q, s), L2(q, s)
  Sm[q, s.] := softmax(A[q, s])
  Nm[q, s.] := normalize(A[q, s])
  L2[q, s.] := l2normalize(A[q, s])
}
def causalProg32 : TLProgram := tlprog!{
  axis q : ℕ = 3
  axis s : ℕ = 3
  tensor f32 X(q, s), Sm(q, s), Nm(q, s), L2(q, s)
  Sm[q, s.] := softmax(where s ≤ q)(X[q, s])
  Nm[q, s.] := normalize(where s ≤ q)(X[q, s])
  L2[q, s.] := l2normalize(where s ≤ q)(X[q, s])
}
def allMaskedProg32 : TLProgram := tlprog!{
  axis q : ℕ = 3
  axis s : ℕ = 3
  tensor f32 X(q, s), Sm(q, s), Nm(q, s)
  Sm[q, s.] := softmax(where s < q)(X[q, s])
  Nm[q, s.] := normalize(where s < q)(X[q, s])
}
def firstAxisProg32 : TLProgram := tlprog!{
  axis q : ℕ = 3
  axis s : ℕ = 2
  tensor f32 A(q, s), Y(q, s)
  Y[q., s] := softmax(A[q, s])
}
def rank3Prog32 : TLProgram := tlprog!{
  axis b : ℕ = 2
  axis q : ℕ = 2
  axis s : ℕ = 3
  tensor f32 A(b, q, s), Last(b, q, s), Mid(b, q, s)
  Last[b, q, s.] := softmax(A[b, q, s])
  Mid[b, q., s] := softmax(A[b, q, s])
}
def chainProg32 : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 2
  axis q : ℕ = 2
  axis s : ℕ = 2
  axis d : ℕ = 2
  tensor f32 W(i, k), X(k), Y(i), Q(q, d), K(s, d), A(q, s)
  Y[i] := relu(W[i, k] · X[k])
  A[q, s.] := softmax(Q[q, d] · K[s, d])
}
def orderProg32 : TLProgram := tlprog!{
  axis s : ℕ = 4
  tensor f32 A(s), Nm(s)
  Nm[s.] := normalize(A[s])
}
-- The same transformer under the default-f32 reading: only the two declarations that pin an
-- axiswise output's axis order remain, untyped (a plain tensor is binary32); no `explicitF64`.
def transformerProg32 : TLProgram := tlprog!{
  Q[q, h, k]       := W_Q[h, k, m] · X[q, m]
  K[s, h, k]       := W_K[h, k, m] · X[s, m]
  V[s, h, k]       := W_V[h, k, m] · X[s, m]
  tensor S(h, q, s)
  S[h, q, s.]      := softmax(where s ≤ q)(Q[q, h, k] · K[s, h, k])
  AttnOut[q, h, k] := S[h, q, s] · V[s, h, k]
  Attn[q, m]       := W_O[m, h, k] · AttnOut[q, h, k]
  tensor A(q, m)
  A[q, m.]         := normalize(Attn[q, m] + X[q, m])
  F[q, d]          := relu(W_in[d, m] · A[q, m])
  Y[q, m]          := W_out[m, d] · F[q, d]
  tensor H(q, m)
  H[q, m.]         := normalize(Y[q, m] + A[q, m])
}

/-! ## Inputs (shared by both precisions; `t32` narrows) -/

def pwX : Array Float := #[-3.0, -0.5, 0.0, -0.0, 0.5, 1.0, 2.5]
def awPlain : Array Float := #[1.0, 2.0, 3.0, 4.0, 0.5, -1.5, 2.0, 0.25]
def awZeroSum : Array Float := #[1.0, -1.0, 2.0, -2.0, 3.0, -3.0, 0.5, -0.5]
def awZero : Array Float := #[0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
def awLarge : Array Float := #[1000.0, 1001.0, 999.0, 1000.0, -1000.0, -1001.0, 5.0, 6.0]
def sq3 : Array Float := #[0.5, -1.0, 2.0, 1.5, 0.25, -0.75, 3.0, 1.0, -2.0]
def firstAxisX : Array Float := #[0.5, -1.0, 2.0, 1.5, -0.25, 3.0]
def rank3X : Array Float := #[0.5, -1.0, 2.0, 1.5, 0.25, -0.75, 3.0, 1.0, -2.0, 0.0, 0.1, 4.0]

/-- Transformer inputs, hand-chosen and non-identity: `X[q=3, m=4]`, the three head projections
    `[h=2, k=2, m=4]`, `W_O[m=4, h=2, k=2]`, `W_in[d=4, m=4]`, `W_out[m=4, d=4]`. Every weight array
    has distinct entries of both signs, so a transposed or swapped operand changes the result. -/
def trX : Array Float :=
  #[0.5, -1.0, 0.75, 0.25,  1.25, 0.5, -0.5, 1.0,  -0.75, 1.5, 0.25, -1.25]
def trWQ : Array Float :=
  #[0.5, -0.25, 0.75, 0.1,  0.3, 0.6, -0.4, 0.2,  -0.5, 0.35, 0.15, 0.8,  0.45, -0.65, 0.25, -0.15]
def trWK : Array Float :=
  #[0.2, 0.7, -0.3, 0.4,  -0.6, 0.1, 0.55, -0.2,  0.35, -0.45, 0.65, 0.05,  0.15, 0.25, -0.75, 0.5]
def trWV : Array Float :=
  #[0.9, -0.1, 0.3, -0.5,  0.2, 0.4, -0.8, 0.6,  -0.3, 0.7, 0.1, 0.45,  0.55, -0.35, 0.25, 0.15]
def trWO : Array Float :=
  #[0.6, -0.2, 0.3, 0.5,  -0.4, 0.8, 0.1, -0.7,  0.25, 0.45, -0.55, 0.35,  0.7, -0.3, 0.2, 0.9]
def trWin : Array Float :=
  #[0.5, -0.3, 0.8, 0.1,  -0.6, 0.4, 0.2, 0.7,  0.3, 0.9, -0.5, -0.2,  0.15, -0.45, 0.65, 0.35]
def trWout : Array Float :=
  #[0.4, 0.6, -0.2, 0.3,  -0.5, 0.1, 0.7, -0.3,  0.8, -0.4, 0.25, 0.5,  0.2, 0.35, -0.6, 0.9]

def corpus64 : IO (Array String) := do
  return #[
    ← fixture64 "pw" pwProg (env64 [("X", t64 [7] pwX)]) 5,
    ← fixture64 "aw_plain" awProg (env64 [("A", t64 [2, 4] awPlain)]) 0 3,
    ← fixture64 "aw_zerosum" awProg (env64 [("A", t64 [2, 4] awZeroSum)]) 0 3,
    ← fixture64 "aw_zero" awProg (env64 [("A", t64 [2, 4] awZero)]) 0 3,
    ← fixture64 "aw_large" awProg (env64 [("A", t64 [2, 4] awLarge)]) 0 3,
    ← fixture64 "causal" causalProg (env64 [("X", t64 [3, 3] sq3)]) 0 3,
    ← fixture64 "allmasked" allMaskedProg (env64 [("X", t64 [3, 3] sq3)]) 0 2,
    ← fixture64 "firstaxis" firstAxisProg (env64 [("A", t64 [3, 2] firstAxisX)]) 0 1,
    ← fixture64 "rank3" rank3Prog (env64 [("A", t64 [2, 2, 3] rank3X)]) 0 2,
    ← fixture64 "chain" chainProg
        (env64 [("W", t64 [2, 2] #[1.0, -2.0, -1.0, 1.0]), ("X", t64 [2] #[3.0, 1.0]),
                ("Q", t64 [2, 2] #[1.0, 0.0, 0.0, 1.0]), ("K", t64 [2, 2] #[0.5, -0.5, 1.0, 2.0])]) 1 1,
    ← fixture64 "order" orderProg (env64 [("A", t64 [4] #[1e16, 1.0, -1e16, 1.0])]) 0 1,
    ← fixture64 "transformer" transformerProg
        (env64 [("X", t64 [3, 4] trX), ("W_Q", t64 [2, 2, 4] trWQ), ("W_K", t64 [2, 2, 4] trWK),
                ("W_V", t64 [2, 2, 4] trWV), ("W_O", t64 [4, 2, 2] trWO),
                ("W_in", t64 [4, 4] trWin), ("W_out", t64 [4, 4] trWout)])
        1 3 (some (10, 1, 3))]

def corpus32 : IO (Array String) := do
  return #[
    ← fixture32 "pw32" pwProg32 (env32 [("X", t32 [7] pwX)]) 5,
    ← fixture32 "aw_plain32" awProg32 (env32 [("A", t32 [2, 4] awPlain)]) 0 3,
    ← fixture32 "aw_zerosum32" awProg32 (env32 [("A", t32 [2, 4] awZeroSum)]) 0 3,
    ← fixture32 "aw_zero32" awProg32 (env32 [("A", t32 [2, 4] awZero)]) 0 3,
    ← fixture32 "aw_large32" awProg32 (env32 [("A", t32 [2, 4] awLarge)]) 0 3,
    ← fixture32 "causal32" causalProg32 (env32 [("X", t32 [3, 3] sq3)]) 0 3,
    ← fixture32 "allmasked32" allMaskedProg32 (env32 [("X", t32 [3, 3] sq3)]) 0 2,
    ← fixture32 "firstaxis32" firstAxisProg32 (env32 [("A", t32 [3, 2] firstAxisX)]) 0 1,
    ← fixture32 "rank332" rank3Prog32 (env32 [("A", t32 [2, 2, 3] rank3X)]) 0 2,
    ← fixture32 "chain32" chainProg32
        (env32 [("W", t32 [2, 2] #[1.0, -2.0, -1.0, 1.0]), ("X", t32 [2] #[3.0, 1.0]),
                ("Q", t32 [2, 2] #[1.0, 0.0, 0.0, 1.0]), ("K", t32 [2, 2] #[0.5, -0.5, 1.0, 2.0])]) 1 1,
    ← fixture32 "order32" orderProg32 (env32 [("A", t32 [4] #[1e10, 1.0, -1e10, 1.0])]) 0 1,
    ← fixture32 "transformer32" transformerProg32
        (env32 [("X", t32 [3, 4] trX), ("W_Q", t32 [2, 2, 4] trWQ), ("W_K", t32 [2, 2, 4] trWK),
                ("W_V", t32 [2, 2, 4] trWV), ("W_O", t32 [4, 2, 2] trWO),
                ("W_in", t32 [4, 4] trWin), ("W_out", t32 [4, 4] trWout)])
        1 3 (some (10, 1, 3))]

end JaxBridge.NonlinSmoke

open JaxBridge.NonlinSmoke in
def main (args : List String) : IO Unit := do
  let out64 := args.head?.getD "generated_evalplan_nonlin_smoke64.py"
  let out32 := (args.drop 1).head?.getD "generated_evalplan_nonlin_smoke32.py"
  let f64s ← corpus64
  let f32s ← corpus32
  IO.FS.writeFile out64
    ("# Generated by EvalPlanNonlinSmoke.lean — do not edit.\nFIXTURES = [\n" ++
      String.intercalate ",\n" f64s.toList ++ "\n]\n")
  IO.FS.writeFile out32
    ("# Generated by EvalPlanNonlinSmoke.lean — do not edit.\nFIXTURES = [\n" ++
      String.intercalate ",\n" f32s.toList ++ "\n]\n")
  IO.println s!"wrote {f64s.size} binary64 fixtures to {out64} and {f32s.size} binary32 to {out32}"
