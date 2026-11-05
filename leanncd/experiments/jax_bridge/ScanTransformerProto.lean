import LeanNCD.Eval.Entry
import LeanNCD.DSL.Compile
import LeanNCD.Eval.Plan.Adapter32
import EvalPlanCodegen

/-!
# Two-layer transformer as a SCAN over the layer axis, on the checked-plan Dense path (prototype)

Scratch prototype for the "scan on JAX via lax.scan" design note
(`docs/superpowers/specs/2026-11-05-jax-scan-lax-design.md`, open questions 1-3). NOT registered in the
lakefile, not part of any default build. Lean only: nothing here touches JAX codegen or production Lean.

Run: `bash leanncd/scripts/lean-file.sh <worktree>/leanncd experiments/jax_bridge/ScanTransformerProto.lean`
(the output is the `#eval` messages; any assertion failure is an error).

Model: the one-layer `transformerRmsProg` of `EvalPlanNonlinSmoke.lean` (SEQ=3, m=4, h=2, k=2, d=4, a real
RMSNorm built from `Z·Z·Inv`, `+Eps`, `sqrt`, `/`) rewritten as `iter l = 3` (history extent 3 = two steps)
with UNTIED per-layer weights read as `W[l, ...]`. The layer-2 weight slice is NaN: if a step ever read it,
every output would be NaN, so the layer-2 slice proves the context coordinate never leaves 0..1.

Path: `compileToScheduled` -> `prepareEvalPlan` -> `runPreparedDense` / `runPreparedDense32` (checked plan),
never the legacy `TLProgram.eval`.
-/

namespace ScanProto

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std
open JaxBridge

def t64 (shape : List Nat) (data : Array Float) : DenseTensor := ⟨shape, data⟩
def t32 (shape : List Nat) (data : Array Float) : DenseTensor32 := ⟨shape, data.map Float.toFloat32⟩
def env64 (xs : List (String × DenseTensor)) : HashMap String DenseTensor := HashMap.ofList xs
def env32 (xs : List (String × DenseTensor32)) : NamedDenseEnv32 := HashMap.ofList xs

/-! ## Inputs (layer 0 weights are the one-layer fixture's; layer 1 is a derived, genuinely different set) -/

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
def trInv : Array Float := #[0.25, 0.25, 0.25, 0.25]
def trEps : Array Float := #[1e-5, 1e-5, 1e-5]

/-- Layer-1 weights: layer 0's entries rotated by 5 positions and scaled by 0.8 (distinct values, both signs). -/
def layer1 (w : Array Float) : Array Float :=
  (Array.range w.size).map fun i => 0.8 * w[(i + 5) % w.size]!
/-- Layer-2 slice: NaN sentinel (never read by a correct two-step scan). -/
def nanSlice (w : Array Float) : Array Float := w.map fun _ => (0.0 : Float) / 0.0

def stack (w : Array Float) : Array Float := w ++ layer1 w ++ nanSlice w
/-- Stack with only the two real layers (extent 2), for the declared-size probe. -/
def stack2 (w : Array Float) : Array Float := w ++ layer1 w

def scanInputs64 : HashMap String DenseTensor :=
  env64 [("X", t64 [3, 4] trX),
         ("W_Q", t64 [3, 2, 2, 4] (stack trWQ)), ("W_K", t64 [3, 2, 2, 4] (stack trWK)),
         ("W_V", t64 [3, 2, 2, 4] (stack trWV)), ("W_O", t64 [3, 4, 2, 2] (stack trWO)),
         ("W_in", t64 [3, 4, 4] (stack trWin)), ("W_out", t64 [3, 4, 4] (stack trWout)),
         ("Inv", t64 [4] trInv), ("Eps", t64 [3] trEps)]
def scanInputs32 : NamedDenseEnv32 :=
  env32 [("X", t32 [3, 4] trX),
         ("W_Q", t32 [3, 2, 2, 4] (stack trWQ)), ("W_K", t32 [3, 2, 2, 4] (stack trWK)),
         ("W_V", t32 [3, 2, 2, 4] (stack trWV)), ("W_O", t32 [3, 4, 2, 2] (stack trWO)),
         ("W_in", t32 [3, 4, 4] (stack trWin)), ("W_out", t32 [3, 4, 4] (stack trWout)),
         ("Inv", t32 [4] trInv), ("Eps", t32 [3] trEps)]
/-- Weight tensors with layer extent 2 (the number of steps) instead of the declared history extent 3. -/
def scanInputs64Ext2 : HashMap String DenseTensor :=
  env64 [("X", t64 [3, 4] trX),
         ("W_Q", t64 [2, 2, 2, 4] (stack2 trWQ)), ("W_K", t64 [2, 2, 2, 4] (stack2 trWK)),
         ("W_V", t64 [2, 2, 2, 4] (stack2 trWV)), ("W_O", t64 [2, 4, 2, 2] (stack2 trWO)),
         ("W_in", t64 [2, 4, 4] (stack2 trWin)), ("W_out", t64 [2, 4, 4] (stack2 trWout)),
         ("Inv", t64 [4] trInv), ("Eps", t64 [3] trEps)]

def unrollInputs64 : HashMap String DenseTensor :=
  env64 [("X", t64 [3, 4] trX),
         ("W_Q1", t64 [2, 2, 4] trWQ), ("W_K1", t64 [2, 2, 4] trWK), ("W_V1", t64 [2, 2, 4] trWV),
         ("W_O1", t64 [4, 2, 2] trWO), ("W_in1", t64 [4, 4] trWin), ("W_out1", t64 [4, 4] trWout),
         ("W_Q2", t64 [2, 2, 4] (layer1 trWQ)), ("W_K2", t64 [2, 2, 4] (layer1 trWK)),
         ("W_V2", t64 [2, 2, 4] (layer1 trWV)), ("W_O2", t64 [4, 2, 2] (layer1 trWO)),
         ("W_in2", t64 [4, 4] (layer1 trWin)), ("W_out2", t64 [4, 4] (layer1 trWout)),
         ("Inv", t64 [4] trInv), ("Eps", t64 [3] trEps)]
def unrollInputs32 : NamedDenseEnv32 :=
  env32 [("X", t32 [3, 4] trX),
         ("W_Q1", t32 [2, 2, 4] trWQ), ("W_K1", t32 [2, 2, 4] trWK), ("W_V1", t32 [2, 2, 4] trWV),
         ("W_O1", t32 [4, 2, 2] trWO), ("W_in1", t32 [4, 4] trWin), ("W_out1", t32 [4, 4] trWout),
         ("W_Q2", t32 [2, 2, 4] (layer1 trWQ)), ("W_K2", t32 [2, 2, 4] (layer1 trWK)),
         ("W_V2", t32 [2, 2, 4] (layer1 trWV)), ("W_O2", t32 [4, 2, 2] (layer1 trWO)),
         ("W_in2", t32 [4, 4] (layer1 trWin)), ("W_out2", t32 [4, 4] (layer1 trWout)),
         ("Inv", t32 [4] trInv), ("Eps", t32 [3] trEps)]

/-! ## Programs. Scan: `iter l = 3` (history extent 3 = layers 0,1,2 = two steps). -/

def scanProg64 : TLProgram := tlprog!{
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

/-- The binary32 sibling: no declarations except the ones that pin axis order / history shape. -/
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

/-- Unrolled reference: two hand-copied flat layers (no scan), layer n writes `Hn`. -/
def unrollProg64 : TLProgram := tlprog!{
  tensor f64 X(q, m), W_Q1(h, k, m), W_K1(h, k, m), W_V1(h, k, m), W_O1(m, h, k), W_in1(d, m), W_out1(m, d)
  tensor f64 W_Q2(h, k, m), W_K2(h, k, m), W_V2(h, k, m), W_O2(m, h, k), W_in2(d, m), W_out2(m, d)
  tensor f64 Inv(m), Eps(q)
  tensor f64 Q1(q, h, k), K1(s, h, k), V1(s, h, k), AO1(q, h, k), At1(q, m), F1(q, d), Y1(q, m)
  tensor f64 Za1(q, m), Ssa1(q), Vea1(q), Sda1(q), Zb1(q, m), Ssb1(q), Veb1(q), Sdb1(q)
  tensor f64 Q2(q, h, k), K2(s, h, k), V2(s, h, k), AO2(q, h, k), At2(q, m), F2(q, d), Y2(q, m)
  tensor f64 Za2(q, m), Ssa2(q), Vea2(q), Sda2(q), Zb2(q, m), Ssb2(q), Veb2(q), Sdb2(q)
  Q1[q, h, k]      := W_Q1[h, k, m] · X[q, m]
  K1[s, h, k]      := W_K1[h, k, m] · X[s, m]
  V1[s, h, k]      := W_V1[h, k, m] · X[s, m]
  tensor f64 S1(h, q, s)
  S1[h, q, s.]     := softmax(where s ≤ q)(Q1[q, h, k] · K1[s, h, k])
  AO1[q, h, k]     := S1[h, q, s] · V1[s, h, k]
  At1[q, m]        := W_O1[m, h, k] · AO1[q, h, k]
  Za1[q, m]        := At1[q, m] + X[q, m]
  Ssa1[q]          := Za1[q, m] · Za1[q, m] · Inv[m]
  Vea1[q]          := Ssa1[q] + Eps[q]
  Sda1[q]          := sqrt(Vea1[q])
  tensor f64 A1(q, m)
  A1[q, m]         := Za1[q, m] / Sda1[q]
  F1[q, d]         := relu(W_in1[d, m] · A1[q, m])
  Y1[q, m]         := W_out1[m, d] · F1[q, d]
  Zb1[q, m]        := Y1[q, m] + A1[q, m]
  Ssb1[q]          := Zb1[q, m] · Zb1[q, m] · Inv[m]
  Veb1[q]          := Ssb1[q] + Eps[q]
  Sdb1[q]          := sqrt(Veb1[q])
  tensor f64 H1(q, m)
  H1[q, m]         := Zb1[q, m] / Sdb1[q]
  Q2[q, h, k]      := W_Q2[h, k, m] · H1[q, m]
  K2[s, h, k]      := W_K2[h, k, m] · H1[s, m]
  V2[s, h, k]      := W_V2[h, k, m] · H1[s, m]
  tensor f64 S2(h, q, s)
  S2[h, q, s.]     := softmax(where s ≤ q)(Q2[q, h, k] · K2[s, h, k])
  AO2[q, h, k]     := S2[h, q, s] · V2[s, h, k]
  At2[q, m]        := W_O2[m, h, k] · AO2[q, h, k]
  Za2[q, m]        := At2[q, m] + H1[q, m]
  Ssa2[q]          := Za2[q, m] · Za2[q, m] · Inv[m]
  Vea2[q]          := Ssa2[q] + Eps[q]
  Sda2[q]          := sqrt(Vea2[q])
  tensor f64 A2(q, m)
  A2[q, m]         := Za2[q, m] / Sda2[q]
  F2[q, d]         := relu(W_in2[d, m] · A2[q, m])
  Y2[q, m]         := W_out2[m, d] · F2[q, d]
  Zb2[q, m]        := Y2[q, m] + A2[q, m]
  Ssb2[q]          := Zb2[q, m] · Zb2[q, m] · Inv[m]
  Veb2[q]          := Ssb2[q] + Eps[q]
  Sdb2[q]          := sqrt(Veb2[q])
  tensor f64 H2(q, m)
  H2[q, m]         := Zb2[q, m] / Sdb2[q]
}

def unrollProg32 : TLProgram := tlprog!{
  Q1[q, h, k]      := W_Q1[h, k, m] · X[q, m]
  K1[s, h, k]      := W_K1[h, k, m] · X[s, m]
  V1[s, h, k]      := W_V1[h, k, m] · X[s, m]
  tensor S1(h, q, s)
  S1[h, q, s.]     := softmax(where s ≤ q)(Q1[q, h, k] · K1[s, h, k])
  AO1[q, h, k]     := S1[h, q, s] · V1[s, h, k]
  At1[q, m]        := W_O1[m, h, k] · AO1[q, h, k]
  Za1[q, m]        := At1[q, m] + X[q, m]
  Ssa1[q]          := Za1[q, m] · Za1[q, m] · Inv[m]
  Vea1[q]          := Ssa1[q] + Eps[q]
  Sda1[q]          := sqrt(Vea1[q])
  tensor A1(q, m)
  A1[q, m]         := Za1[q, m] / Sda1[q]
  F1[q, d]         := relu(W_in1[d, m] · A1[q, m])
  Y1[q, m]         := W_out1[m, d] · F1[q, d]
  Zb1[q, m]        := Y1[q, m] + A1[q, m]
  Ssb1[q]          := Zb1[q, m] · Zb1[q, m] · Inv[m]
  Veb1[q]          := Ssb1[q] + Eps[q]
  Sdb1[q]          := sqrt(Veb1[q])
  tensor H1(q, m)
  H1[q, m]         := Zb1[q, m] / Sdb1[q]
  Q2[q, h, k]      := W_Q2[h, k, m] · H1[q, m]
  K2[s, h, k]      := W_K2[h, k, m] · H1[s, m]
  V2[s, h, k]      := W_V2[h, k, m] · H1[s, m]
  tensor S2(h, q, s)
  S2[h, q, s.]     := softmax(where s ≤ q)(Q2[q, h, k] · K2[s, h, k])
  AO2[q, h, k]     := S2[h, q, s] · V2[s, h, k]
  At2[q, m]        := W_O2[m, h, k] · AO2[q, h, k]
  Za2[q, m]        := At2[q, m] + H1[q, m]
  Ssa2[q]          := Za2[q, m] · Za2[q, m] · Inv[m]
  Vea2[q]          := Ssa2[q] + Eps[q]
  Sda2[q]          := sqrt(Vea2[q])
  tensor A2(q, m)
  A2[q, m]         := Za2[q, m] / Sda2[q]
  F2[q, d]         := relu(W_in2[d, m] · A2[q, m])
  Y2[q, m]         := W_out2[m, d] · F2[q, d]
  Zb2[q, m]        := Y2[q, m] + A2[q, m]
  Ssb2[q]          := Zb2[q, m] · Zb2[q, m] · Inv[m]
  Veb2[q]          := Ssb2[q] + Eps[q]
  Sdb2[q]          := sqrt(Veb2[q])
  tensor H2(q, m)
  H2[q, m]         := Zb2[q, m] / Sdb2[q]
}

/-! ## Pipeline drivers: surface -> ScheduledProgram -> PreparedPlan -> checked Dense run -/

def sched (prog : TLProgram) : Except String ScheduledProgram :=
  match prog.compileToScheduled.run 0 with
  | .ok s _ => .ok s
  | .error e _ => .error s!"compileToScheduled: {repr e}"

def prep64 (prog : TLProgram) (inputs : HashMap String DenseTensor) : Except String PreparedPlan := do
  let s ← sched prog
  match prepareEvalPlan s (InputSignature.ofDenseInputs inputs) with
  | .ok p => pure p
  | .error f => throw s!"prepareEvalPlan: {renderCompileCause f.cause}"

def prep32 (prog : TLProgram) (inputs : NamedDenseEnv32) : Except String PreparedPlan := do
  let s ← sched prog
  let sig ← match InputSignature.ofDenseInputs32ForDecls s.decls inputs with
    | .ok g => pure g
    | .error e => throw s!"binary32 signature: {repr e}"
  match prepareEvalPlan s sig with
  | .ok p => pure p
  | .error f => throw s!"prepareEvalPlan: {renderCompileCause f.cause}"

def run64 (p : PreparedPlan) (inputs : HashMap String DenseTensor) : Except String EvalReport :=
  match runPreparedDense p inputs with
  | .ok r => .ok r
  | .error e => .error s!"runPreparedDense: {repr e.cause}"

def run32 (p : PreparedPlan) (inputs : NamedDenseEnv32) : Except String (EvalReportOf Float32) :=
  match runPreparedDense32 p inputs with
  | .ok r => .ok r
  | .error e => .error s!"runPreparedDense32: {repr e.cause}"

def okOrThrow {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

/-! ## Plan-structure printers -/

def showSigs (xs : Array TensorSignature) : String :=
  String.intercalate " " (xs.toList.zipIdx.map fun (s, i) => s!"[{i}]{s.shape}")

def readUsesCtx (t : TermPlan) (r : ReadPlan) : Bool :=
  r.map.coeffs.any fun row => t.contextPos.any fun c => (row[c]?.getD 0) != 0

def showBlockStep (bs : BlockStep) : String :=
  match bs with
  | .assign a =>
    let reads := a.terms.toList.flatMap fun t => t.factors.toList.filterMap fun f => match f with
      | .read r => some s!"{r.sourceSlot}{if readUsesCtx t r then "*ctx" else ""}{if r.unary.isSome then "/unary" else ""}"
      | .iverson _ => some "iverson"
    s!"assign dst={a.destinationSlot} out={a.outputShape} ctx={a.contextShape} terms={a.terms.size} reads=[{String.intercalate "," reads}]"
  | .pointwise p => s!"pointwise {repr p.fn} src={p.sourceSlot} dst={p.destinationSlot} shape={p.shape}"
  | .axiswise a => s!"axiswise {repr a.fn} src={a.sourceSlot} dst={a.destinationSlot} shape={a.shape} axisPos={a.axisPos} mask={a.mask.isSome}"

def showCapture (c : BlockCapture) : String :=
  match c.source with
  | .external o => s!"in{c.inputSlot}<-external({o})"
  | .state i => s!"in{c.inputSlot}<-state({i})"

def showWrite (w : StateWriteMap) : String :=
  s!"out{w.outputSlot}->state{w.stateIndex} coeffs={w.map.coeffs} bias={w.map.bias}"

def showBlock (name : String) (b : RawPlanBlock) : List String :=
  [s!"  {name}: contextShape={b.contextShape} inputs={b.inputs} outputs={b.outputs} steps={b.steps.size}",
   s!"    block sigs: {showSigs b.tensorSigs}"] ++
  (b.steps.toList.zipIdx.map fun (s, i) => s!"    step {i}: {showBlockStep s}")

/-- Full read-plan rows of every step-block read that uses the context coordinate. -/
def ctxReads (b : RawPlanBlock) : List String :=
  b.steps.toList.zipIdx.flatMap fun (s, i) => match s with
    | .assign a => a.terms.toList.flatMap fun t => t.factors.toList.filterMap fun f => match f with
        | .read r => if readUsesCtx t r then
            some s!"    step {i} ctx read: src={r.sourceSlot} sourceShape={r.sourceShape} iterShape={t.iterationShape} contextPos={t.contextPos} outputPos={t.outputPos} reductionPos={t.reductionPos} coeffs={r.map.coeffs} bias={r.map.bias}"
          else none
        | .iverson _ => none
    | _ => []

def showScan (sc : RawScanPlan) : List String :=
  [s!"  states={sc.states.size} historyExtents={sc.historyExtents} order={repr sc.iterationOrder} boundary={repr sc.boundaryPolicy} snapshot={repr sc.snapshotPolicy}"] ++
  (sc.states.toList.zipIdx.map fun (st, i) =>
    s!"  state{i}: destSlot={st.destSlot} advancingDims={st.advancingDims} init={repr st.initValue}") ++
  showBlock "base" sc.baseBlock ++
  [s!"  baseCaptures: {sc.baseCaptures.toList.map showCapture}"] ++
  [s!"  baseWrites: {sc.baseWrites.toList.map showWrite}"] ++
  showBlock "step" sc.stepBlock ++
  [s!"  stepCaptures: {sc.stepCaptures.toList.map showCapture}"] ++
  [s!"  stepWrites: {sc.stepWrites.toList.map showWrite}"] ++
  ctxReads sc.stepBlock

def showPlan (p : PreparedPlan) : List String :=
  let raw := p.plan.raw
  [s!"outer sigs: {showSigs raw.tensorSigs}",
   s!"outer inputSlots={raw.inputSlots} steps={raw.steps.size}",
   s!"required inputs: {p.bindings.requiredInputs.bindings.toList.map fun b => s!"{b.name}:{b.slot}"}",
   s!"materialized: {p.bindings.materializedNames.toList.map fun b => s!"{b.name}:{b.slot}"}"] ++
  (raw.steps.toList.zipIdx.flatMap fun (st, i) => match st with
    | .scan sc => s!"outer step {i}: SCAN" :: showScan sc
    | .assign a => [s!"outer step {i}: assign dst={a.destinationSlot} out={a.outputShape}"]
    | .scatter _ => [s!"outer step {i}: scatter"]
    | .pointwise _ => [s!"outer step {i}: pointwise"]
    | .axiswise _ => [s!"outer step {i}: axiswise"])


/-- Structural pins of the checked scan plan (so a change in how the layer compiles is loud). -/
def checkStructure (what : String) (p : PreparedPlan) : IO Unit := do
  let some (PlanStep.scan sc) := p.plan.raw.steps[0]? | throw (IO.userError s!"{what}: outer step 0 is not a scan")
  unless p.plan.raw.steps.size == 1 do throw (IO.userError s!"{what}: expected exactly 1 outer step")
  unless sc.states.size == 1 && sc.historyExtents == #[3] do
    throw (IO.userError s!"{what}: expected 1 state with historyExtents #[3]")
  unless sc.stepBlock.contextShape == #[2] do throw (IO.userError s!"{what}: step contextShape {sc.stepBlock.contextShape} /= #[2]")
  let kinds := sc.stepBlock.steps.map fun s => match s with | .assign _ => 'a' | .pointwise _ => 'p' | .axiswise _ => 'w'
  unless kinds.size == 20 && (kinds.filter (· == 'a')).size == 18 && (kinds.filter (· == 'p')).size == 1
      && (kinds.filter (· == 'w')).size == 1 do
    throw (IO.userError s!"{what}: step kinds {kinds}")
  -- exactly the six per-layer weights and the state H read the context coordinate
  let ctxN := (sc.stepBlock.steps.toList.map fun s => match s with
    | .assign a => (a.terms.toList.map fun t => (t.factors.toList.filter fun f => match f with
        | .read r => readUsesCtx t r | .iverson _ => false).length).foldl (· + ·) 0
    | _ => 0).foldl (· + ·) 0
  unless ctxN == 10 do throw (IO.userError s!"{what}: {ctxN} context-reading reads, expected 10 (6 per-layer weights + 4 reads of state H)")
  IO.println s!"{what}: structure pins hold (1 scan, 1 state, step ctx #[2], 18 assign / 1 axiswise / 1 pointwise, 10 ctx-column reads)"

/-! ## Numeric helpers -/

def sliceLayer (t : Array Float) (l : Nat) : Array Float :=  -- H[q, m, l], shape [3,4,3]
  (Array.range 12).map fun qm => t[qm * 3 + l]!
def sliceLayer32 (t : Array Float32) (l : Nat) : Array Float32 :=
  (Array.range 12).map fun qm => t[qm * 3 + l]!

def maxAbsDiff (a b : Array Float) : Float :=
  (Array.range a.size).foldl (fun m i => max m (Float.abs (a[i]! - b[i]!))) 0.0
def maxAbsDiff32 (a b : Array Float32) : Float :=
  (Array.range a.size).foldl (fun m i => max m (Float.abs ((a[i]!).toFloat - (b[i]!).toFloat))) 0.0
def bitsEq (a b : Array Float) : Bool := a.size == b.size && (Array.range a.size).all fun i => a[i]!.toBits == b[i]!.toBits
def bitsEq32 (a b : Array Float32) : Bool := a.size == b.size && (Array.range a.size).all fun i => a[i]!.toBits == b[i]!.toBits

/-- Per-row mean of squares over `m` of a `[3,4]` row-major layer. -/
def rowMs (h : Array Float) : List Float :=
  (List.range 3).map fun q => ((List.range 4).foldl (fun acc m => acc + h[q * 4 + m]! * h[q * 4 + m]!) 0.0) / 4.0

def checkUnitMs (what : String) (h : Array Float) : IO Unit := do
  for ms in rowMs h do
    unless Float.abs (ms - 1.0) < 1e-3 do
      throw (IO.userError s!"{what}: row mean-square {ms} is not ~1 (RMSNorm invariant broken)")

def checkFinite (what : String) (h : Array Float) : IO Unit :=
  for x in h do
    if x.isNaN || x.isInf then throw (IO.userError s!"{what}: non-finite entry {x}")

def printLayer (what : String) (h : Array Float) : IO Unit :=
  IO.println s!"{what}: {h.toList}"

/-! ## Experiment -/

def experiment : IO Unit := do
  IO.println "=== f64 scan: prepare + run ==="
  let p ← okOrThrow "f64 scan prepare" (prep64 scanProg64 scanInputs64)
  for l in showPlan p do IO.println l
  checkStructure "f64" p
  let r ← okOrThrow "f64 scan run" (run64 p scanInputs64)
  let H ← match r.env["H"]? with | some t => pure t | none => throw (IO.userError "no H")
  IO.println s!"H shape={H.shape} (expect [3,4,3])"
  let h0 := sliceLayer H.data 0
  let h1 := sliceLayer H.data 1
  let h2 := sliceLayer H.data 2
  printLayer "H[:,:,0] (= X)" h0
  printLayer "H[:,:,1]" h1
  printLayer "H[:,:,2]" h2
  IO.println s!"H0 == X bitwise: {bitsEq h0 trX}"
  IO.println s!"max|H1-H2| = {maxAbsDiff h1 h2} (layers differ if > 0)"
  unless maxAbsDiff h1 h2 > 1e-3 do throw (IO.userError "layers 1 and 2 do not differ")
  checkFinite "H layers (a NaN means the layer-2 weight slice was read)" H.data
  IO.println s!"(contrast, pin can fail) mean-square rows of H[:,:,0] = X: {rowMs h0}"
  checkUnitMs "f64 H layer 1" h1
  checkUnitMs "f64 H layer 2" h2
  IO.println s!"f64 unit-mean-square rows: layer1={rowMs h1} layer2={rowMs h2}"
  -- unrolled reference
  IO.println "=== f64 unrolled reference ==="
  let pu ← okOrThrow "f64 unrolled prepare" (prep64 unrollProg64 unrollInputs64)
  let ru ← okOrThrow "f64 unrolled run" (run64 pu unrollInputs64)
  let U1 ← match ru.env["H1"]? with | some t => pure t | none => throw (IO.userError "no H1")
  let U2 ← match ru.env["H2"]? with | some t => pure t | none => throw (IO.userError "no H2")
  IO.println s!"unrolled plan: {pu.plan.raw.steps.size} outer steps"
  IO.println s!"f64 scan-vs-unrolled layer1: bitwise={bitsEq h1 U1.data} maxabs={maxAbsDiff h1 U1.data}"
  IO.println s!"f64 scan-vs-unrolled layer2: bitwise={bitsEq h2 U2.data} maxabs={maxAbsDiff h2 U2.data}"
  checkUnitMs "f64 unrolled H1" U1.data
  checkUnitMs "f64 unrolled H2" U2.data
  unless maxAbsDiff h1 U1.data < 1e-12 && maxAbsDiff h2 U2.data < 1e-12 do
    throw (IO.userError "f64 scan and unrolled disagree beyond 1e-12")
  -- f32
  IO.println "=== f32 scan: prepare + run ==="
  let p32 ← okOrThrow "f32 scan prepare" (prep32 scanProg32 scanInputs32)
  IO.println s!"f32 storageKind={repr p32.plan.storageKind} outer steps={p32.plan.raw.steps.size}"
  checkStructure "f32" p32
  let r32 ← okOrThrow "f32 scan run" (run32 p32 scanInputs32)
  let H32 ← match r32.env["H"]? with | some t => pure t | none => throw (IO.userError "no H (f32)")
  let g0 := sliceLayer32 H32.data 0
  let g1 := sliceLayer32 H32.data 1
  let g2 := sliceLayer32 H32.data 2
  IO.println s!"H32 shape={H32.shape}"
  IO.println s!"H32[:,:,1]: {g1.toList}"
  IO.println s!"H32[:,:,2]: {g2.toList}"
  let g1f := g1.map Float32.toFloat
  let g2f := g2.map Float32.toFloat
  checkFinite "H32 layers" (g0.map Float32.toFloat ++ g1f ++ g2f)
  checkUnitMs "f32 H layer 1" g1f
  checkUnitMs "f32 H layer 2" g2f
  IO.println s!"f32 unit-mean-square rows: layer1={rowMs g1f} layer2={rowMs g2f}"
  IO.println s!"f32 layers differ: max|H1-H2|={maxAbsDiff32 g1 g2}"
  let pu32 ← okOrThrow "f32 unrolled prepare" (prep32 unrollProg32 unrollInputs32)
  let ru32 ← okOrThrow "f32 unrolled run" (run32 pu32 unrollInputs32)
  let V1 ← match ru32.env["H1"]? with | some t => pure t | none => throw (IO.userError "no H1 (f32)")
  let V2 ← match ru32.env["H2"]? with | some t => pure t | none => throw (IO.userError "no H2 (f32)")
  IO.println s!"f32 scan-vs-unrolled layer1: bitwise={bitsEq32 g1 V1.data} maxabs={maxAbsDiff32 g1 V1.data}"
  IO.println s!"f32 scan-vs-unrolled layer2: bitwise={bitsEq32 g2 V2.data} maxabs={maxAbsDiff32 g2 V2.data}"
  -- f64 vs f32 scan, for orientation
  IO.println s!"f32 scan vs f64 scan (x1e9): layer1 maxabs={maxAbsDiff g1f h1 * 1e9} layer2 maxabs={maxAbsDiff g2f h2 * 1e9}"

#eval experiment

/-- Declared-size probe: weight tensors with layer extent 2 (steps) instead of 3 (history extent). -/
def probeExt2 : IO Unit := do
  match prep64 scanProg64 scanInputs64Ext2 with
  | .ok p =>
    IO.println "probe weights l-extent 2: prepare ACCEPTED"
    match run64 p scanInputs64Ext2 with
    | .ok r => IO.println s!"  run ok, H shape={(r.env["H"]?).map (·.shape)}"
    | .error e => IO.println s!"  run error: {e}"
  | .error e => IO.println s!"probe weights l-extent 2: REJECTED: {e}"

#eval probeExt2

/-! ## Workaround probes (item 5): which declarations/markers does the scan actually need?
    Each variant drops ONE piece of the binary32 program (or the f64 scratch declarations) and reports
    whether prepare+run is accepted and whether H still equals the baseline bitwise. -/

def probeVariant (label : String) (prog : TLProgram) : IO Unit := do
  match prep32 prog scanInputs32 with
  | .error e => IO.println s!"probe {label}: REJECTED at prepare: {e}"
  | .ok p =>
    match run32 p scanInputs32 with
    | .error e => IO.println s!"probe {label}: prepared, RUN REJECTED: {e}"
    | .ok r =>
      let base ← okOrThrow "baseline" (do let q ← prep32 scanProg32 scanInputs32; run32 q scanInputs32)
      let same := match r.env["H"]?, base.env["H"]? with
        | some a, some b => bitsEq32 a.data b.data && a.shape == b.shape
        | _, _ => false
      IO.println s!"probe {label}: ACCEPTED, H shape/bits equal baseline = {same}"

-- no `axis s : ℕ = 3` declaration (s's size must then be inferred)
def vNoAxisS : TLProgram := tlprog!{
  iter l = 3
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

-- no `tensor S(h, q, s)` declaration (axis order of the softmax output left to inference)
def vNoDeclS : TLProgram := tlprog!{
  iter l = 3
  axis s : ℕ = 3
  tensor H(q, m, l)
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

-- no `tensor H(q, m, l)` declaration (the state's axis order left to inference)
def vNoDeclH : TLProgram := tlprog!{
  iter l = 3
  axis s : ℕ = 3
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

-- no softmax marker: `S[h, q, s]` instead of `S[h, q, s.]`
def vNoMarker : TLProgram := tlprog!{
  iter l = 3
  axis s : ℕ = 3
  tensor H(q, m, l)
  tensor S(h, q, s)
  H[q, m, 0]       := X[q, m]
  Q[q, h, k]       := W_Q[l, h, k, m] · H[q, m, l]
  K[s, h, k]       := W_K[l, h, k, m] · H[s, m, l]
  V[s, h, k]       := W_V[l, h, k, m] · H[s, m, l]
  S[h, q, s]       := softmax(where s ≤ q)(Q[q, h, k] · K[s, h, k])
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

-- f64 inputs with ONLY the state H and the softmax output S declared f64 (scratch left undeclared)
def vF64MinimalDecls : TLProgram := tlprog!{
  iter l = 3
  axis s : ℕ = 3
  tensor f64 H(q, m, l)
  tensor f64 S(h, q, s)
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

def probeF64Minimal : IO Unit := do
  match prep64 vF64MinimalDecls scanInputs64 with
  | .error e => IO.println s!"probe f64 minimal decls: REJECTED at prepare: {e}"
  | .ok p =>
    match run64 p scanInputs64 with
    | .error e => IO.println s!"probe f64 minimal decls: prepared, RUN REJECTED: {e}"
    | .ok _ => IO.println s!"probe f64 minimal decls: ACCEPTED (storage {repr p.plan.storageKind})"

#eval probeVariant "no `axis s`" vNoAxisS
#eval probeVariant "no `tensor S(...)` decl" vNoDeclS
#eval probeVariant "no `tensor H(...)` decl" vNoDeclH
#eval probeVariant "no `s.` marker" vNoMarker
#eval probeF64Minimal

end ScanProto
