import LeanNCD.Eval.Entry
import LeanNCD.DSL.Compile
import LeanNCD.Eval.Plan.Adapter32
import EvalPlanCodegen

/-!
# `renderScanNode` structural pins on the two-layer transformer scan

The plan is the real checked scan of the two-layer transformer (as `scanProg` in `EvalPlanNonlinSmoke.lean`;
`iter l = 3`, history extent 3 = two steps, state `H(q, m, l)` of shape `[3, 4, 3]`, untied weights read
as `W[l, ...]`), built through `compileToScheduled` -> `prepareEvalPlan`. Only SIGNATURES matter here
(zero-filled inputs): every pin below is VALUE-INDEPENDENT and is computed from the plan's own geometry
with plain loops, never copied from the emitted string.
-/

namespace ScanAffineEmitTest

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std
open JaxBridge

def zeros (shape : List Nat) : DenseTensor :=
  ⟨shape, Array.replicate (shape.foldl (· * ·) 1) 0.0⟩

def inputs : HashMap String DenseTensor :=
  HashMap.ofList
    [ ("X", zeros [3, 4])
    , ("W_Q", zeros [3, 2, 2, 4]), ("W_K", zeros [3, 2, 2, 4]), ("W_V", zeros [3, 2, 2, 4])
    , ("W_O", zeros [3, 4, 2, 2]), ("W_in", zeros [3, 4, 4]), ("W_out", zeros [3, 4, 4])
    , ("Inv", zeros [4]), ("Eps", zeros [3]) ]

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

def prepared : Option PreparedPlan :=
  match prog.compileToScheduled.run 0 with
  | .error _ _ => none
  | .ok s _ =>
    match prepareEvalPlan s (InputSignature.ofDenseInputs inputs) with
    | .ok p => some p
    | .error _ => none
where prog := scanProg64

/-- The plan's one scan node and its outer step index. -/
def scanNode : Option (Nat × CheckedScanPlan) :=
  match prepared with
  | none => none
  | some p => p.plan.checkedNodes.toList.zipIdx.findSome? fun (n, i) =>
      match n with | .scan c => some (i, c) | _ => none

def withScan (f : Nat → CheckedScanPlan → Bool) : Bool :=
  match scanNode with | some (i, c) => f i c | none => false

def rendered (i : Nat) (c : CheckedScanPlan) : String :=
  match renderScanNode i c with | .ok s => s | .error _ => ""

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

-- Sanity: the plan is the one we think it is (one scan, one state of shape [3,4,3], T = 2 steps).
#guard withScan fun _ c =>
  c.raw.states.size == 1 && c.stepExtents == #[2] &&
  (c.sigs[c.raw.states[0]!.destSlot]?.map (·.shape)) == some #[3, 4, 3]
#guard withScan fun i c => (renderScanNode i c).toOption.isSome

-- (a) one node record per block step, in both blocks, and every record appears in the scan record.
#guard withScan fun i c =>
  let r := rendered i c
  (match renderScanBlockNodes i false c.checkedBase with
    | .ok ns => ns.size == c.raw.baseBlock.steps.size && ns.all (has r)
    | .error _ => false) &&
  (match renderScanBlockNodes i true c.checkedStep with
    | .ok ns => ns.size == c.raw.stepBlock.steps.size && ns.size > 1 && ns.all (has r)
    | .error _ => false)

-- (b) write index tables: state `H[q, m, l]` of shape `[3, 4, 3]`. The step write sends the layer
-- output `[3, 4]` at context `r` to `H[q, m, r + 1]`: step-major, then `(q, m)` row-major, flat offset
-- `(q * 4 + m) * 3 + (r + 1)`. The base write sends `X[q, m]` to `H[q, m, 0]`.
def expectedStepIndex : List Nat :=
  (List.range 2).flatMap fun r => (List.range 3).flatMap fun q =>
    (List.range 4).map fun m => (q * 4 + m) * 3 + (r + 1)
def expectedBaseIndex : List Nat :=
  (List.range 3).flatMap fun q => (List.range 4).map fun m => (q * 4 + m) * 3

#guard expectedStepIndex.length == 2 * 12
#guard withScan fun i c =>
  let r := rendered i c
  has r ("\"state\": 0, \"index\": " ++ pyNatListLit expectedStepIndex.toArray) &&
  has r ("\"state\": 0, \"index\": " ++ pyNatListLit expectedBaseIndex.toArray)

-- (c) a weight read's table is STACKED over the step axis: the step block's `W_Q[l, h, k, m]` read has
-- a term iteration shape `[T, local...]` with the step axis at position 0, a table of length
-- `T * local`, and step `r`'s slice addresses layer `r` of the weight: flat `r*16 + h*8 + k*4 + m`.
def weightRead (c : CheckedScanPlan) : Option (TermPlan × ReadPlan) :=
  c.raw.stepBlock.steps.toList.findSome? fun st => match st with
    | .assign a => a.terms.toList.findSome? fun t => t.factors.toList.findSome? fun f => match f with
        | .read r => if r.sourceShape == #[3, 2, 2, 4] then some (t, r) else none
        | .iverson _ => none
    | _ => none

def expectedLayerSlice (r : Nat) : List Nat :=
  (List.range 3).flatMap fun _q => (List.range 2).flatMap fun h => (List.range 2).flatMap fun k =>
    (List.range 4).map fun m => r * 16 + h * 8 + k * 4 + m

#guard withScan fun i c =>
  match weightRead c with
  | none => false
  | some (t, f) =>
    let (idxs, masks) := buildFactorTable t.iterationShape f
    t.contextPos == #[0] && t.iterationShape == #[2, 3, 2, 2, 4] &&
    idxs.size == 2 * 48 && masks.all id &&
    idxs.toList.take 48 == expectedLayerSlice 0 &&
    (idxs.toList.drop 48).take 48 == expectedLayerSlice 1 &&
    has (rendered i c) ("\"safe_index\": " ++ pyNatListLit idxs)

-- The step block's assignments carry the context contract; pointwise/axiswise records are present.
#guard withScan fun i c =>
  let r := rendered i c
  has r "\"context_pos\": [0]" && has r "\"kind\": \"scan\"" && has r "\"step_count\": 2" &&
  has r "\"kind\": \"pointwise\"" && has r "\"kind\": \"axiswise\"" && has r "\"include\""

/-! ### Boolean reachability (`.booleanReach`) emitter pins

Donors: `brReach` (`reachProg`, copied verbatim from `EvalPlanLogicSmoke.lean` / `ScanJaxGateTest.lean`;
a Boolean scan state `Reach` plus a later real `Closed` reading it) and `brStep`, the step-dependent toy
`S[j, l+1] := S[j, l] · [j ≤ l]`. The Iverson `include` tables are pinned against the plan's OWN geometry
(plain loops), never copied from the emitted string. -/

def brReach : TLProgram := tlprog!{
  axis i : ℕ = 6, j : ℕ = 6, k : ℕ = 6
  iter h = 7
  predicate Edge(i, j), Reach(i, j, h)
  tensor f64 Closed(i, j)
  Reach[i, j, 0] := [i = j]
  Reach[i, j, h +1] := Reach[i, j, h] + Reach[i, k, h] · Edge[k, j]
  Closed[i, j] := Reach[i, j, 6]
}

def brStep : TLProgram := tlprog!{
  axis j : ℕ = 3
  iter l = 4
  predicate Seed(j), S(j, l)
  S[j, 0] := Seed[j]
  S[j, l +1] := S[j, l] · [j ≤ l]
}

def brRetag32 (p : TLProgram) : TLProgram :=
  { p with decls := p.decls.map fun d => match d with
      | .typedTensor .f64 n ax => .typedTensor .f32 n ax
      | d => d }

def brEdgeEnv : NamedDenseEnv := HashMap.ofList [("Edge", ⟨[6, 6], Array.replicate 36 0.0⟩)]
def brSeedEnv : NamedDenseEnv := HashMap.ofList [("Seed", ⟨[3], #[1.0, 0.0, 1.0]⟩)]

def brPrepared? (p : TLProgram) (env : NamedDenseEnv) (f32 : Bool) : Option PreparedPlan :=
  match ((if f32 then brRetag32 p else p).compileToScheduled).run 0 with
  | .error _ _ => none
  | .ok sched _ =>
    if f32 then
      match InputSignature.ofDenseInputs32ForDecls sched.decls
          (env.map fun _ t => ⟨t.shape, t.data.map Float.toFloat32⟩) with
      | .ok sig => (prepareEvalPlan sched sig).toOption
      | .error _ => none
    else
      match InputSignature.ofDenseInputsForDecls sched.decls env with
      | .ok sig => (prepareEvalPlan sched sig).toOption
      | .error _ => none

def brRendered? (p : TLProgram) (env : NamedDenseEnv) (f32 : Bool) : Option String :=
  (brPrepared? p env f32).bind fun pp => (renderAffinePlanNamed pp).toOption

def brCount (s sub : String) : Nat := (s.splitOn sub).length - 1

def brIverson (table : List Nat) : String :=
  "{\"tag\": \"iverson\", \"include\": " ++ pyNatListLit table.toArray ++ "}"

-- The donors prepare and render in both precisions.
#guard (brRendered? brReach brEdgeEnv false).isSome
#guard (brRendered? brReach brEdgeEnv true).isSome

-- (a) `reachProg`: the Boolean base and step statements are tagged Boolean (two assignment nodes:
-- the base block's and the step block's), every step read carries `tag: read` with an explicit
-- `real_to_bool: False` and NO `bool_to_tropical` (that key is max-plus-only), the scan record has no
-- `state_init`, and the one Iverson factor (the base statement `[i = j]`) is the identity diagonal of
-- the 6x6 iteration shape, in `allCoords` order.
def brDiag6 : List Nat :=
  (List.range 6).flatMap fun i => (List.range 6).map fun j => if i == j then 1 else 0

#guard match brRendered? brReach brEdgeEnv false with
  | none => false
  | some s =>
    brDiag6.length == 36 &&
    brCount s "\"algebra\"" == 2 && brCount s "\"algebra\": \"boolean\"" == 2 &&
    brCount s "\"semantics\": \"ordered_boolean_v1\"" == 2 &&
    brCount s "\"tag\": \"read\"" == 3 && brCount s "real_to_bool\": False" == 3 &&
    brCount s "\"tag\": \"iverson\"" == 1 && brCount s "\"include\"" == 1 &&
    has s (brIverson brDiag6) &&
    brCount s "bool_to_tropical" == 0 && brCount s "state_init" == 0

-- The `Closed`-shaped node (a real sum-product destination reading the Boolean state) is the ACCEPT/
-- REFUSE contrast inside the same plan: a plain real record, NO `algebra`/`semantics`/`tag` key — the
-- silent-miscompile hazard if Boolean metadata leaked onto (or off) either side. Rendered through the
-- public single-node renderer; the plan's `Closed` step is its only terminal assignment.
#guard match brPrepared? brReach brEdgeEnv false with
  | none => false
  | some pp =>
    match pp.plan.checkedNodes.findSome? (fun | .assign a => some a | _ => none) with
    | none => false
    | some a =>
      match renderAffineAssign pp.plan.raw.tensorSigs a with
      | .error _ => false
      | .ok r =>
        brCount r "\"algebra\"" == 0 && brCount r "\"semantics\"" == 0 && brCount r "\"tag\"" == 0 &&
        brCount r "\"source_slot\": 1" == 1

-- (b) the binary32 retag renders BYTE-IDENTICALLY to binary64: the renderer emits shapes, index and
-- mask tables, include tables and algebra tags, never the element dtype (the caller supplies it), and
-- the Boolean algebra's constants are the same `.bool` ones at both precisions.
#guard brRendered? brReach brEdgeEnv false == brRendered? brReach brEdgeEnv true
#guard (brRendered? brReach brEdgeEnv true).isSome

-- (c) step-dependent predicate `[j ≤ l]` in a step block (j = 3, steps r = 0..2): the include table is
-- STACKED step-major like the term's read tables, entry `(r, j)` holds iff `j ≤ r`.
def brStepInclude : List Nat :=
  (List.range 3).flatMap fun r => (List.range 3).map fun j => if j ≤ r then 1 else 0

#guard brStepInclude.length == 9
#guard match brRendered? brStep brSeedEnv false with
  | none => false
  | some s =>
    has s (brIverson brStepInclude) && brCount s "\"include\"" == 1 &&
    brCount s "\"algebra\": \"boolean\"" == 2 && brCount s "\"context_pos\": [0]" == 1

end ScanAffineEmitTest
