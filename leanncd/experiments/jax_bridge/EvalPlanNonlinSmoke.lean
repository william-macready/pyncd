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
refuse it, and that `affineReference` renders it. A fixture with an inline unary read (`unaryOk`)
is the one place those two doors refuse with `unaryFactor` (binary64) instead of `unsupportedStep`:
they keep refusing unary reads; only `affineReference` admits one.
-/

namespace JaxBridge.NonlinSmoke

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std
open JaxBridge

/-- Local copy of `EvalPlanScatterSmoke`'s binary32 payload renderer (a `main` file cannot be
    imported). Parked: factor the drivers' copies into `EvalPlanCodegen`. -/
def pyTensorEntry32 (t : DenseTensor32) : String :=
  "{\"shape\": " ++ pyShapeTuple t.shape.toArray ++ ", \"dtype\": \"float32\", \"bits\": [" ++
  String.intercalate ", " (t.data.toList.map fun x => toString x.toBits) ++ "]}"

/-- The prepared plan's steps with every `.scan` step replaced by its base-block then step-block steps
    (blocks hold ordinary steps), so a scan's nonlinearities and unary reads are counted like any
    other fixture's. A plan without a scan is returned unchanged. The scan itself is counted by
    `countScans`. -/
def flatSteps (p : PreparedPlan) : Array PlanStep :=
  let asPlan : BlockStep → PlanStep
    | .assign a => .assign a | .pointwise q => .pointwise q | .axiswise a => .axiswise a
  p.plan.raw.steps.foldl (fun acc st => match st with
    | .scan sc => acc ++ sc.baseBlock.steps.map asPlan ++ sc.stepBlock.steps.map asPlan
    | _ => acc.push st) #[]

/-- Number of `.scan` steps of the prepared plan (top level). -/
def countScans (p : PreparedPlan) : Nat :=
  p.plan.raw.steps.foldl (fun n st => match st with | .scan _ => n + 1 | _ => n) 0

def countSteps (p : PreparedPlan) : Nat × Nat :=
  (flatSteps p).foldl (fun (pw, aw) st => match st with
    | .pointwise _ => (pw + 1, aw) | .axiswise _ => (pw, aw + 1) | _ => (pw, aw)) (0, 0)

/-- Exact step-kind counts `(assign, pointwise, axiswise)`; any other step kind is counted nowhere,
    so a plan with a scatter or scan step fails an exact pin. -/
def countKinds (p : PreparedPlan) : Nat × Nat × Nat :=
  (flatSteps p).foldl (fun (a, pw, aw) st => match st with
    | .assign _ => (a + 1, pw, aw) | .pointwise _ => (a, pw + 1, aw)
    | .axiswise _ => (a, pw, aw + 1) | _ => (a, pw, aw)) (0, 0, 0)

/-- Number of inline unary reads in the prepared plan's assignment steps. -/
def countUnary (p : PreparedPlan) : Nat :=
  (flatSteps p).foldl (fun n st => match st with
    | .assign a => a.terms.foldl (fun n t => t.factors.foldl (fun n f => match f with
        | .read r => if r.unary.isSome then n + 1 else n
        | .iverson _ => n) n) n
    | _ => n) 0

/-- The assertions every fixture shares; returns the rendered plan data. `exact`, when given, pins
    the total step count and the `(assign, pointwise, axiswise)` counts exactly, so a silent change
    to how a program compiles is loud. For a scan fixture those counts are over the steps INSIDE the
    scan's base and step blocks (`flatSteps`), and `scans` pins the number of scan steps (default 0:
    a fixture that unexpectedly compiles to a scan fails). -/
def checkAndRender (name : String) (p : PreparedPlan) (minPw minAw : Nat)
    (exact : Option (Nat × Nat × Nat) := none) (unaryOk : Bool := false) (scans : Nat := 0) :
    IO String := do
  unless countScans p == scans do
    throw (IO.userError s!"{name}: expected {scans} scan step(s), prepared plan has {countScans p}")
  let (pw, aw) := countSteps p
  unless pw ≥ minPw && aw ≥ minAw do
    throw (IO.userError s!"{name}: expected >= {minPw} pointwise and >= {minAw} axiswise steps, prepared plan has {pw} and {aw}")
  if let some (ea, epw, eaw) := exact then
    let (a, pw', aw') := countKinds p
    unless (a, pw', aw') == (ea, epw, eaw) && (flatSteps p).size == ea + epw + eaw do
      throw (IO.userError s!"{name}: expected {ea} assign / {epw} pointwise / {eaw} axiswise ({ea + epw + eaw} steps), prepared plan has {a} / {pw'} / {aw'} ({(flatSteps p).size} steps)")
  match generateNamed .einsumOnly p with
  | .error (.unsupportedStep _) | .error (.unsupportedStorageKind _) => pure ()
  | .error (.unaryFactor _ _ _) => unless unaryOk do throw (IO.userError s!"{name}: einsumOnly refused with unaryFactor on a fixture without a unary read")
  | other => throw (IO.userError s!"{name}: einsumOnly did not refuse: {repr other.toOption}")
  match lowerCheckPlanToCandidate p with
  | .error (.unsupportedStep _) | .error (.unsupportedStorageKind _) => pure ()
  | .error (.unaryFactor _ _ _) => unless unaryOk do throw (IO.userError s!"{name}: the evidence door refused with unaryFactor on a fixture without a unary read")
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
    ", \"n_axiswise\": " ++ toString aw ++ ", \"n_unary\": " ++ toString (countUnary p) ++
    ", \"plan\": " ++ planData

/-- One binary64 named fixture. -/
def fixture64 (name : String) (prog : TLProgram) (inputs : HashMap String DenseTensor)
    (minPw : Nat := 0) (minAw : Nat := 0) (exact : Option (Nat × Nat × Nat) := none)
    (unaryOk : Bool := false) (scans : Nat := 0) : IO String := do
  let sched ← scheduled name prog
  let p ← prepared name sched (InputSignature.ofDenseInputs inputs)
  let planData ← checkAndRender name p minPw minAw exact unaryOk scans
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
    (minPw : Nat := 0) (minAw : Nat := 0) (exact : Option (Nat × Nat × Nat) := none)
    (unaryOk : Bool := false) (scans : Nat := 0) : IO String := do
  let sched ← scheduled name prog
  let sig ← match InputSignature.ofDenseInputs32ForDecls sched.decls inputs with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name} binary32 signature failed: {repr e}")
  let p ← prepared name sched sig
  unless p.plan.storageKind == .float32 do throw (IO.userError s!"{name} is not a binary32 plan")
  let planData ← checkAndRender name p minPw minAw exact unaryOk scans
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

-- The same layer with a REAL RMSNorm, `z / sqrt(mean(z^2) + eps)`, in place of the `normalize` stand-in
-- (a sum-normalisation). Each norm is the `unaryLnProg` chain: `Ss` = mean of squares (`Inv` = 1/m per
-- lane), `Ve = Ss + Eps` (eps > 0, so sqrt's argument is >= eps: Lean-ok), `Sd = sqrt(Ve)`, then
-- `z / Sd` (recip, a unary read of the intermediate `Sd`, times the plain `z`). The only axiswise step
-- left is the causal softmax; the only pointwise step is relu. Every tensor is declared `f64` by hand.
def transformerRmsProg : TLProgram := tlprog!{
  tensor f64 X(q, m), W_Q(h, k, m), W_K(h, k, m), W_V(h, k, m), W_O(m, h, k), W_in(d, m), W_out(m, d)
  tensor f64 Inv(m), Eps(q)
  tensor f64 Q(q, h, k), K(s, h, k), V(s, h, k), AttnOut(q, h, k), Attn(q, m), F(q, d), Y(q, m)
  tensor f64 Z1(q, m), Ss1(q), Ve1(q), Sd1(q), Z2(q, m), Ss2(q), Ve2(q), Sd2(q)
  Q[q, h, k]       := W_Q[h, k, m] · X[q, m]
  K[s, h, k]       := W_K[h, k, m] · X[s, m]
  V[s, h, k]       := W_V[h, k, m] · X[s, m]
  tensor f64 S(h, q, s)
  S[h, q, s.]      := softmax(where s ≤ q)(Q[q, h, k] · K[s, h, k])
  AttnOut[q, h, k] := S[h, q, s] · V[s, h, k]
  Attn[q, m]       := W_O[m, h, k] · AttnOut[q, h, k]
  Z1[q, m]         := Attn[q, m] + X[q, m]
  Ss1[q]           := Z1[q, m] · Z1[q, m] · Inv[m]
  Ve1[q]           := Ss1[q] + Eps[q]
  Sd1[q]           := sqrt(Ve1[q])
  tensor f64 A(q, m)
  A[q, m]          := Z1[q, m] / Sd1[q]
  F[q, d]          := relu(W_in[d, m] · A[q, m])
  Y[q, m]          := W_out[m, d] · F[q, d]
  Z2[q, m]         := Y[q, m] + A[q, m]
  Ss2[q]           := Z2[q, m] · Z2[q, m] · Inv[m]
  Ve2[q]           := Ss2[q] + Eps[q]
  Sd2[q]           := sqrt(Ve2[q])
  tensor f64 H(q, m)
  H[q, m]          := Z2[q, m] / Sd2[q]
}
def transformerRmsProg32 : TLProgram := tlprog!{
  Q[q, h, k]       := W_Q[h, k, m] · X[q, m]
  K[s, h, k]       := W_K[h, k, m] · X[s, m]
  V[s, h, k]       := W_V[h, k, m] · X[s, m]
  tensor S(h, q, s)
  S[h, q, s.]      := softmax(where s ≤ q)(Q[q, h, k] · K[s, h, k])
  AttnOut[q, h, k] := S[h, q, s] · V[s, h, k]
  Attn[q, m]       := W_O[m, h, k] · AttnOut[q, h, k]
  Z1[q, m]         := Attn[q, m] + X[q, m]
  Ss1[q]           := Z1[q, m] · Z1[q, m] · Inv[m]
  Ve1[q]           := Ss1[q] + Eps[q]
  Sd1[q]           := sqrt(Ve1[q])
  tensor A(q, m)
  A[q, m]          := Z1[q, m] / Sd1[q]
  F[q, d]          := relu(W_in[d, m] · A[q, m])
  Y[q, m]          := W_out[m, d] · F[q, d]
  Z2[q, m]         := Y[q, m] + A[q, m]
  Ss2[q]           := Z2[q, m] · Z2[q, m] · Inv[m]
  Ve2[q]           := Ss2[q] + Eps[q]
  Sd2[q]           := sqrt(Ve2[q])
  tensor H(q, m)
  H[q, m]          := Z2[q, m] / Sd2[q]
}

-- relu alone, so a NaN input leaves the output finite (Lean's `relu NaN = +0`: `max 0 x` is `x` only
-- when `0 ≤ x`); the other four functions would return NaN and are covered by `pw`/`pw32`.
def reluNanProg : TLProgram := tlprog!{
  axis i : ℕ = 4
  tensor f64 X(i), R(i)
  R[i] := relu(X[i])
}
def reluNanProg32 : TLProgram := tlprog!{
  axis i : ℕ = 4
  tensor f32 X(i), R(i)
  R[i] := relu(X[i])
}

-- One inline unary read whose last output lane reads out of bounds: `A[i + 1]` at `i = 2` is
-- `A[3]`, zero-padded, and Dense applies `exp` AFTER the pad, so that lane is `exp 0 = 1` (a runtime
-- that applied `exp` before the pad, or dropped it, would give 0 or the raw padded value there).
-- Every lane is a Lean-ok input (`exp` is total).
def unaryExpProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  tensor f64 A(i), E(i)
  E[i] := exp(A[i + 1])
}
def unaryExpProg32 : TLProgram := tlprog!{
  axis i : ℕ = 3
  tensor f32 A(i), E(i)
  E[i] := exp(A[i + 1])
}

-- The five remaining unary ops, one output each (`recip` is the source's friendly division
-- `Nn[i] / Rr[i]`, i.e. `Nn * recip(Rr)`, so it is also a unary-times-plain product). Every lane is
-- a Lean-ok input: `log` over strictly positive `Pp`, `sqrt` over `Qq` incl. an exact `0.0` (ok),
-- `recip` over nonzero `Rr` of both signs. `sin`/`cos` share `Tt`, so swapping them changes every lane.
def unaryOpsProg : TLProgram := tlprog!{
  axis i : ℕ = 4
  tensor f64 Pp(i), Qq(i), Tt(i), Rr(i), Nn(i), Lg(i), Sq(i), Sn(i), Cs(i), Rc(i)
  Lg[i] := log(Pp[i])
  Sq[i] := sqrt(Qq[i])
  Sn[i] := sin(Tt[i])
  Cs[i] := cos(Tt[i])
  Rc[i] := Nn[i] / Rr[i]
}
def unaryOpsProg32 : TLProgram := tlprog!{
  axis i : ℕ = 4
  tensor f32 Pp(i), Qq(i), Tt(i), Rr(i), Nn(i), Lg(i), Sq(i), Sn(i), Cs(i), Rc(i)
  Lg[i] := log(Pp[i])
  Sq[i] := sqrt(Qq[i])
  Sn[i] := sin(Tt[i])
  Cs[i] := cos(Tt[i])
  Rc[i] := Nn[i] / Rr[i]
}
-- A unary read between two plain reads in one term. This pins that the unary attaches to ITS OWN
-- factor (`Aa · sin(Bb) · Cc`); it does not pin the product order, since a reordering differs by
-- about 1e-16 relative, inside the comparison tolerance.
def unaryMixProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  tensor f64 Aa(i), Bb(i), Cc(i), Mx(i)
  Mx[i] := Aa[i] · sin(Bb[i]) · Cc[i]
}
def unaryMixProg32 : TLProgram := tlprog!{
  axis i : ℕ = 3
  tensor f32 Aa(i), Bb(i), Cc(i), Mx(i)
  Mx[i] := Aa[i] · sin(Bb[i]) · Cc[i]
}
-- A unary read inside a REDUCED axis: `Zr[i] = Σ_j exp(Vv[i, j]) · Ww[j]`, so the per-row fold sums
-- unary-applied factors.
def unaryRedProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  tensor f64 Vv(i, j), Ww(j), Zr(i)
  Zr[i] := exp(Vv[i, j]) · Ww[j]
}
def unaryRedProg32 : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  tensor f32 Vv(i, j), Ww(j), Zr(i)
  Zr[i] := exp(Vv[i, j]) · Ww[j]
}

-- LayerNorm-with-eps shape, from source: `Vs` = mean of squares (`Inv` = 1/3 per lane), `Ve = Vs + eps`
-- (eps > 0, so sqrt's argument is >= eps), `Sd = sqrt(Ve)` (unary read of an intermediate) and
-- `Yl = Xl / Sd` (recip, a unary read of the intermediate `Sd`, times the plain `Xl`).
def unaryLnProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 3
  tensor f64 Xl(i, k), Inv(k), Eps(i), Vs(i), Ve(i), Sd(i), Yl(i, k)
  Vs[i] := Xl[i, k] · Xl[i, k] · Inv[k]
  Ve[i] := Vs[i] + Eps[i]
  Sd[i] := sqrt(Ve[i])
  Yl[i, k] := Xl[i, k] / Sd[i]
}
def unaryLnProg32 : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 3
  tensor f32 Xl(i, k), Inv(k), Eps(i), Vs(i), Ve(i), Sd(i), Yl(i, k)
  Vs[i] := Xl[i, k] · Xl[i, k] · Inv[k]
  Ve[i] := Vs[i] + Eps[i]
  Sd[i] := sqrt(Ve[i])
  Yl[i, k] := Xl[i, k] / Sd[i]
}
-- Empty source: a constant read `Ae[0]` of a ZERO-extent tensor by a non-empty iteration; the read is
-- out of bounds on every lane, so Dense zero-pads and applies `exp`: `exp 0 = 1` per lane.
def unaryEmptyProg : TLProgram := tlprog!{
  axis e : ℕ = 0
  axis i : ℕ = 3
  tensor f64 Ae(e), Ee(i)
  Ee[i] := exp(Ae[0])
}
def unaryEmptyProg32 : TLProgram := tlprog!{
  axis e : ℕ = 0
  axis i : ℕ = 3
  tensor f32 Ae(e), Ee(i)
  Ee[i] := exp(Ae[0])
}

/-! ## Inputs (shared by both precisions; `t32` narrows) -/

def pwX : Array Float := #[-3.0, -0.5, 0.0, -0.0, 0.5, 1.0, 2.5]
def awPlain : Array Float := #[1.0, 2.0, 3.0, 4.0, 0.5, -1.5, 2.0, 0.25]
def awZeroSum : Array Float := #[1.0, -1.0, 2.0, -2.0, 3.0, -3.0, 0.5, -0.5]
def awZero : Array Float := #[0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
def awLarge : Array Float := #[1000.0, 1001.0, 999.0, 1000.0, -1000.0, -1001.0, 5.0, 6.0]
-- Every entry of row 0 is below `-999`, so a row max folded from `0` instead of from the row's own first
-- entry makes `exp (x - 0)` underflow to exactly 0 and the whole row collapse to zeros (Lean: a real
-- distribution). Row 1 is large-negative too.
def awNegLarge : Array Float := #[-1000.0, -1001.0, -999.0, -1000.0, -500.0, -501.0, -502.0, -503.0]
-- Causal mask `s ≤ q`: every MASKED entry (row 0: s = 1, 2; row 1: s = 2) is huge. A row max that
-- includes masked entries makes `exp (x - 2000)` underflow and the row collapse to zeros.
def causalBig : Array Float := #[0.5, 1000.0, 2000.0, 1.5, 0.25, 900.0, 3.0, 1.0, -2.0]
def nanX : Float := 0.0 / 0.0
def reluNanX : Array Float := #[nanX, -1.0, 2.0, 0.0]
def unaryExpA : Array Float := #[0.5, -1.0, 2.0]
def unaryPp : Array Float := #[0.25, 1.0, 2.0, 7.5]
def unaryQq : Array Float := #[0.0, 0.25, 2.0, 9.0]
def unaryTt : Array Float := #[0.5, -1.0, 2.0, 3.0]
def unaryRr : Array Float := #[0.5, -2.0, 4.0, -0.125]
def unaryNn : Array Float := #[1.0, 3.0, -2.0, 5.0]
def unaryAa : Array Float := #[1.5, -2.0, 0.5]
def unaryBb : Array Float := #[0.5, -1.0, 2.0]
def unaryCc : Array Float := #[3.0, 0.25, -1.5]
def unaryVv : Array Float := #[0.5, -1.0, 2.0, 1.5, 0.25, -0.75]
def unaryWw : Array Float := #[1.0, -0.5, 2.0]
def unaryXl : Array Float := #[1.0, 2.0, 3.0, -1.0, 0.5, 0.0]
def unaryInv : Array Float := #[0.3333333333333333, 0.3333333333333333, 0.3333333333333333]
def unaryEps : Array Float := #[1e-5, 1e-5]
def sq3 : Array Float :=#[0.5, -1.0, 2.0, 1.5, 0.25, -0.75, 3.0, 1.0, -2.0]
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

/-- RMSNorm inputs of `transformerRmsProg`: `Inv[m=4]` = 1/4 per lane (mean of squares), `Eps[q=3]` = 1e-5. -/
def trInv : Array Float := #[0.25, 0.25, 0.25, 0.25]
def trEps : Array Float := #[1e-5, 1e-5, 1e-5]

/-! ### Two-layer transformer as a scan over the layer axis (`transformer_scan`, `transformer_scan32`)

The one-layer `transformerRmsProg` with `iter l = 3` (history extent 3 = two steps, state `H(q, m, l)`)
and UNTIED per-layer weights read as `W[l, ...]`. Weight stacks hold layer 0 (the one-layer fixture's
weights), a derived, genuinely different layer 1 and a NaN layer-2 slice that a correct two-step scan
never reads (a step reading past layer 1 would make every output NaN). -/

/-- Layer-1 weights: layer 0's entries rotated by 5 positions and scaled by 0.8 (both signs, distinct). -/
def scanLayer1 (w : Array Float) : Array Float :=
  (Array.range w.size).map fun i => 0.8 * w[(i + 5) % w.size]!
def scanNanSlice (w : Array Float) : Array Float := w.map fun _ => (0.0 : Float) / 0.0
def scanStack (w : Array Float) : Array Float := w ++ scanLayer1 w ++ scanNanSlice w

def scanProg : TLProgram := tlprog!{
  iter l = 3
  axis s : ℕ = 3
  tensor f64 X(q, m), W_Q(l, h, k, m), W_K(l, h, k, m), W_V(l, h, k, m), W_O(l, m, h, k)
  tensor f64 W_in(l, d, m), W_out(l, m, d), Inv(m), Eps(q)
  tensor f64 H(q, m, l)
  tensor f64 Q(q, h, k), K(s, h, k), V(s, h, k), S(h, q, s), AttnOut(q, h, k), Attn(q, m)
  tensor f64 Z1(q, m), Ss1(q), Ve1(q), Sd1(q), A(q, m), F(q, d), Y(q, m)
  tensor f64 Z2(q, m), Ss2(q), Ve2(q), Sd2(q)
  H[q, m, 0]       := X[q, m]
  Q[q, h, k]       := W_Q[l, h, k, m] · H[q, m, l]
  K[s, h, k]       := W_K[l, h, k, m] · H[s, m, l]
  V[s, h, k]       := W_V[l, h, k, m] · H[s, m, l]
  S[h, q, s.]      := softmax(where s ≤ q)(Q[q, h, k] · K[s, h, k])
  AttnOut[q, h, k] := S[h, q, s] · V[s, h, k]
  Attn[q, m]       := W_O[l, m, h, k] · AttnOut[q, h, k]
  Z1[q, m]         := Attn[q, m] + H[q, m, l]
  Ss1[q]           := Z1[q, m] · Z1[q, m] · Inv[m]
  Ve1[q]           := Ss1[q] + Eps[q]
  Sd1[q]           := sqrt(Ve1[q])
  A[q, m]          := Z1[q, m] / Sd1[q]
  F[q, d]          := relu(W_in[l, d, m] · A[q, m])
  Y[q, m]          := W_out[l, m, d] · F[q, d]
  Z2[q, m]         := Y[q, m] + A[q, m]
  Ss2[q]           := Z2[q, m] · Z2[q, m] · Inv[m]
  Ve2[q]           := Ss2[q] + Eps[q]
  Sd2[q]           := sqrt(Ve2[q])
  H[q, m, l +1]    := Z2[q, m] / Sd2[q]
}
/-- The binary32 sibling: only the declarations that pin axis order and the history shape. -/
def scanProg32 : TLProgram := tlprog!{
  iter l = 3
  axis s : ℕ = 3
  tensor H(q, m, l)
  tensor S(h, q, s)
  H[q, m, 0]       := X[q, m]
  Q[q, h, k]       := W_Q[l, h, k, m] · H[q, m, l]
  K[s, h, k]       := W_K[l, h, k, m] · H[s, m, l]
  V[s, h, k]       := W_V[l, h, k, m] · H[s, m, l]
  S[h, q, s.]      := softmax(where s ≤ q)(Q[q, h, k] · K[s, h, k])
  AttnOut[q, h, k] := S[h, q, s] · V[s, h, k]
  Attn[q, m]       := W_O[l, m, h, k] · AttnOut[q, h, k]
  Z1[q, m]         := Attn[q, m] + H[q, m, l]
  Ss1[q]           := Z1[q, m] · Z1[q, m] · Inv[m]
  Ve1[q]           := Ss1[q] + Eps[q]
  Sd1[q]           := sqrt(Ve1[q])
  A[q, m]          := Z1[q, m] / Sd1[q]
  F[q, d]          := relu(W_in[l, d, m] · A[q, m])
  Y[q, m]          := W_out[l, m, d] · F[q, d]
  Z2[q, m]         := Y[q, m] + A[q, m]
  Ss2[q]           := Z2[q, m] · Z2[q, m] · Inv[m]
  Ve2[q]           := Ss2[q] + Eps[q]
  Sd2[q]           := sqrt(Ve2[q])
  H[q, m, l +1]    := Z2[q, m] / Sd2[q]
}

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
    ← fixture64 "aw_neglarge" awProg (env64 [("A", t64 [2, 4] awNegLarge)]) 0 3,
    ← fixture64 "causal_big" causalProg (env64 [("X", t64 [3, 3] causalBig)]) 0 3,
    ← fixture64 "relu_nan" reluNanProg (env64 [("X", t64 [4] reluNanX)]) 1,
    ← fixture64 "transformer" transformerProg
        (env64 [("X", t64 [3, 4] trX), ("W_Q", t64 [2, 2, 4] trWQ), ("W_K", t64 [2, 2, 4] trWK),
                ("W_V", t64 [2, 2, 4] trWV), ("W_O", t64 [4, 2, 2] trWO),
                ("W_in", t64 [4, 4] trWin), ("W_out", t64 [4, 4] trWout)])
        1 3 (some (10, 1, 3)),
    ← fixture64 "transformer_rms" transformerRmsProg
        (env64 [("X", t64 [3, 4] trX), ("W_Q", t64 [2, 2, 4] trWQ), ("W_K", t64 [2, 2, 4] trWK),
                ("W_V", t64 [2, 2, 4] trWV), ("W_O", t64 [4, 2, 2] trWO),
                ("W_in", t64 [4, 4] trWin), ("W_out", t64 [4, 4] trWout),
                ("Inv", t64 [4] trInv), ("Eps", t64 [3] trEps)])
        1 1 (some (18, 1, 1)) true,
    ← fixture64 "unary_exp_oob" unaryExpProg (env64 [("A", t64 [3] unaryExpA)])
        0 0 (some (1, 0, 0)) true,
    ← fixture64 "unary_ops" unaryOpsProg
        (env64 [("Pp", t64 [4] unaryPp), ("Qq", t64 [4] unaryQq), ("Tt", t64 [4] unaryTt),
                ("Rr", t64 [4] unaryRr), ("Nn", t64 [4] unaryNn)])
        0 0 (some (5, 0, 0)) true,
    ← fixture64 "unary_mix" unaryMixProg
        (env64 [("Aa", t64 [3] unaryAa), ("Bb", t64 [3] unaryBb), ("Cc", t64 [3] unaryCc)])
        0 0 (some (1, 0, 0)) true,
    ← fixture64 "unary_red" unaryRedProg
        (env64 [("Vv", t64 [2, 3] unaryVv), ("Ww", t64 [3] unaryWw)])
        0 0 (some (1, 0, 0)) true,
    ← fixture64 "unary_ln" unaryLnProg
        (env64 [("Xl", t64 [2, 3] unaryXl), ("Inv", t64 [3] unaryInv), ("Eps", t64 [2] unaryEps)])
        0 0 (some (4, 0, 0)) true,
    ← fixture64 "unary_empty" unaryEmptyProg (env64 [("Ae", t64 [0] #[])])
        0 0 (some (1, 0, 0)) true,
    ← fixture64 "transformer_scan" scanProg
        (env64 [("X", t64 [3, 4] trX),
                ("W_Q", t64 [3, 2, 2, 4] (scanStack trWQ)), ("W_K", t64 [3, 2, 2, 4] (scanStack trWK)),
                ("W_V", t64 [3, 2, 2, 4] (scanStack trWV)), ("W_O", t64 [3, 4, 2, 2] (scanStack trWO)),
                ("W_in", t64 [3, 4, 4] (scanStack trWin)), ("W_out", t64 [3, 4, 4] (scanStack trWout)),
                ("Inv", t64 [4] trInv), ("Eps", t64 [3] trEps)])
        1 1 (some (19, 1, 1)) true (scans := 1)]

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
    ← fixture32 "aw_neglarge32" awProg32 (env32 [("A", t32 [2, 4] awNegLarge)]) 0 3,
    ← fixture32 "causal_big32" causalProg32 (env32 [("X", t32 [3, 3] causalBig)]) 0 3,
    ← fixture32 "relu_nan32" reluNanProg32 (env32 [("X", t32 [4] reluNanX)]) 1,
    ← fixture32 "transformer32" transformerProg32
        (env32 [("X", t32 [3, 4] trX), ("W_Q", t32 [2, 2, 4] trWQ), ("W_K", t32 [2, 2, 4] trWK),
                ("W_V", t32 [2, 2, 4] trWV), ("W_O", t32 [4, 2, 2] trWO),
                ("W_in", t32 [4, 4] trWin), ("W_out", t32 [4, 4] trWout)])
        1 3 (some (10, 1, 3)),
    ← fixture32 "transformer_rms32" transformerRmsProg32
        (env32 [("X", t32 [3, 4] trX), ("W_Q", t32 [2, 2, 4] trWQ), ("W_K", t32 [2, 2, 4] trWK),
                ("W_V", t32 [2, 2, 4] trWV), ("W_O", t32 [4, 2, 2] trWO),
                ("W_in", t32 [4, 4] trWin), ("W_out", t32 [4, 4] trWout),
                ("Inv", t32 [4] trInv), ("Eps", t32 [3] trEps)])
        1 1 (some (18, 1, 1)) true,
    ← fixture32 "unary_exp_oob32" unaryExpProg32 (env32 [("A", t32 [3] unaryExpA)])
        0 0 (some (1, 0, 0)) true,
    ← fixture32 "unary_ops32" unaryOpsProg32
        (env32 [("Pp", t32 [4] unaryPp), ("Qq", t32 [4] unaryQq), ("Tt", t32 [4] unaryTt),
                ("Rr", t32 [4] unaryRr), ("Nn", t32 [4] unaryNn)])
        0 0 (some (5, 0, 0)) true,
    ← fixture32 "unary_mix32" unaryMixProg32
        (env32 [("Aa", t32 [3] unaryAa), ("Bb", t32 [3] unaryBb), ("Cc", t32 [3] unaryCc)])
        0 0 (some (1, 0, 0)) true,
    ← fixture32 "unary_red32" unaryRedProg32
        (env32 [("Vv", t32 [2, 3] unaryVv), ("Ww", t32 [3] unaryWw)])
        0 0 (some (1, 0, 0)) true,
    ← fixture32 "unary_ln32" unaryLnProg32
        (env32 [("Xl", t32 [2, 3] unaryXl), ("Inv", t32 [3] unaryInv), ("Eps", t32 [2] unaryEps)])
        0 0 (some (4, 0, 0)) true,
    ← fixture32 "unary_empty32" unaryEmptyProg32 (env32 [("Ae", t32 [0] #[])])
        0 0 (some (1, 0, 0)) true,
    ← fixture32 "transformer_scan32" scanProg32
        (env32 [("X", t32 [3, 4] trX),
                ("W_Q", t32 [3, 2, 2, 4] (scanStack trWQ)), ("W_K", t32 [3, 2, 2, 4] (scanStack trWK)),
                ("W_V", t32 [3, 2, 2, 4] (scanStack trWV)), ("W_O", t32 [3, 4, 2, 2] (scanStack trWO)),
                ("W_in", t32 [3, 4, 4] (scanStack trWin)), ("W_out", t32 [3, 4, 4] (scanStack trWout)),
                ("Inv", t32 [4] trInv), ("Eps", t32 [3] trEps)])
        1 1 (some (19, 1, 1)) true (scans := 1)]

/-! ## Boundary pins: Lean REJECTS domain-violating unary reads (the JAX runtime does not check)

The JAX runtime treats `log(v <= 0)`, `sqrt(v < 0)` and `recip(0)` as an unchecked precondition and
agrees with Lean only where Lean returns ok. These pins observe the Lean side end to end (source ->
prepared plan -> Dense): each violating input returns the typed unary-domain error for that op, in
both precisions. They run on every driver invocation and throw (so the runner fails) if one stops
erroring. -/

def domainOpName : UnaryDomainOp → String
  | .log => "log" | .sqrt => "sqrt" | .recip => "recip"

def domainPins : IO Unit := do
  let okEnv : List (String × Array Float) :=
    [("Pp", unaryPp), ("Qq", unaryQq), ("Tt", unaryTt), ("Rr", unaryRr), ("Nn", unaryNn)]
  let swap (k : String) (v : Array Float) := okEnv.map fun (n, d) => (n, if n == k then v else d)
  let cases : List (String × String × Array Float × String) :=
    [("log of 0.0", "Pp", #[0.25, 0.0, 2.0, 7.5], "log"),
     ("log of -1.0", "Pp", #[0.25, -1.0, 2.0, 7.5], "log"),
     ("sqrt of -4.0", "Qq", #[0.0, 0.25, -4.0, 9.0], "sqrt"),
     ("recip of 0.0", "Rr", #[0.5, -2.0, 0.0, -0.125], "recip")]
  -- The un-violated environment must run (so each error below is caused by the one swapped tensor).
  let sched64 ← scheduled "domain" unaryOpsProg
  let sched32 ← scheduled "domain32" unaryOpsProg32
  let ok64 := env64 (okEnv.map fun (n, d) => (n, t64 [4] d))
  let p64ok ← prepared "domain" sched64 (InputSignature.ofDenseInputs ok64)
  match runPreparedDense p64ok ok64 with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"domain pins: the in-domain environment failed: {repr e.cause}")
  for (label, k, v, want) in cases do
    let in64 := env64 ((swap k v).map fun (n, d) => (n, t64 [4] d))
    let p64 ← prepared "domain" sched64 (InputSignature.ofDenseInputs in64)
    match runPreparedDense p64 in64 with
    | .error e => match e.cause with
      | .execution (.unaryDomain op _ _) =>
        unless domainOpName op == want do throw (IO.userError s!"domain pin (binary64) {label}: got op {domainOpName op}")
      | other => throw (IO.userError s!"domain pin (binary64) {label}: wrong error {repr other}")
    | .ok _ => throw (IO.userError s!"domain pin (binary64) {label}: Dense returned ok")
    let in32 := env32 ((swap k v).map fun (n, d) => (n, t32 [4] d))
    let sig32 ← match InputSignature.ofDenseInputs32ForDecls sched32.decls in32 with
      | .ok s => pure s
      | .error e => throw (IO.userError s!"domain pin signature failed: {repr e}")
    let p32 ← prepared "domain32" sched32 sig32
    match runPreparedDense32 p32 in32 with
    | .error e => match e.cause with
      | .execution (.unaryDomain32 op _ _) =>
        unless domainOpName op == want do throw (IO.userError s!"domain pin (binary32) {label}: got op {domainOpName op}")
      | other => throw (IO.userError s!"domain pin (binary32) {label}: wrong error {repr other}")
    | .ok _ => throw (IO.userError s!"domain pin (binary32) {label}: Dense returned ok")
  IO.println "domain pins: log(0.0), log(-1.0), sqrt(-4.0), recip(0.0) are typed unary-domain errors in Dense (binary64 and binary32)"

end JaxBridge.NonlinSmoke

open JaxBridge.NonlinSmoke in
def main (args : List String) : IO Unit := do
  let out64 := args.head?.getD "generated_evalplan_nonlin_smoke64.py"
  let out32 := (args.drop 1).head?.getD "generated_evalplan_nonlin_smoke32.py"
  domainPins
  let f64s ← corpus64
  let f32s ← corpus32
  IO.FS.writeFile out64
    ("# Generated by EvalPlanNonlinSmoke.lean — do not edit.\nFIXTURES = [\n" ++
      String.intercalate ",\n" f64s.toList ++ "\n]\n")
  IO.FS.writeFile out32
    ("# Generated by EvalPlanNonlinSmoke.lean — do not edit.\nFIXTURES = [\n" ++
      String.intercalate ",\n" f32s.toList ++ "\n]\n")
  IO.println s!"wrote {f64s.size} binary64 fixtures to {out64} and {f32s.size} binary32 to {out32}"
