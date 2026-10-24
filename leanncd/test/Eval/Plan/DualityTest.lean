import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter
import LeanNCD.Eval.Plan.Adapter32
import Eval.ExplicitF64
import Eval.PropertyOracle.Gen
import Eval.PropertyOracle.ScanGen

/-!
# Negation duality of the max-plus and min-plus algebras (S3b T8)

Max-plus and min-plus share ONE definition per layer (`Combine.tropical`, the Iverson/pad values, the
bool cast, the scan state init, the oracle's fibre fold), so a bug that is symmetric in the two sorts
passes any suite that checks each sort on its own. Negation is an isomorphism between them when
`⊗ = +`: `min-plus(x) = -max-plus(-x)` EXACTLY (`0_K` maps `-inf <-> +inf`, `1_K = 0` is fixed, the
out-of-range pad, the Iverson false value and the bool cast `false` are all `0_K`).

This module states that as a PROPERTY over the existing generators instead of fixture-by-fixture twins:

* the scan-free `PropertyOracle.enumPrograms` sweep (3,832 programs, every statement `agg := .sum`) is
  TROPICALISED: every statement gets `agg := .max` (program `P`) and `agg := .min` (twin `P'`, run on
  the NEGATED inputs). Every statement then has its own sort (a scan-free statement is never neutral:
  its annotation chooses its pad), so the whole sweep is in the property.
* the curated scan corpus `PropertyOracle.enumScanCases` (17 cases) is tropicalised the same way. A
  scan state's sort is taken from its non-neutral statements and its neutral base adopts it, so the
  tagging reaches every state; template 2 has a `relu` and is skipped (tropical + nonlinearity is
  refused, and a nonlinear scan is not in the property).

For each program and each backend: `result(P', -x)` must equal `-result(P, x)` cell for cell (IEEE
`==`, so `+0 = -0`, equal infinities equal; a NaN anywhere fails). Backends: the REFERENCE evaluator
(`evalScheduled`, f64 only), the CHECKED plan on f64 (`prepareEvalPlan` + `runPreparedDense`), and the
CHECKED plan on binary32 (`runPreparedDense32`, the same program with its inputs declared `f32`; the
reference evaluator is f64-only, so there is no f32 reference leg). A refusal must be SYMMETRIC: `P`
refused iff `P'` refused.

Non-vacuity. A sum-only program is its own negation dual under the REAL algebra (`-(a+b) = -a + -b`), so
agreement alone would not show the sorts are applied. `distinguished` counts the programs whose max
result differs from the untouched real (`sum`) result on the reference backend, and is pinned.

No circularity: the property compares production with ITSELF under a symmetry; it borrows no
production state init, no fibre fold and no expected value. The expectation `-result(P, x)` is just
the max-plus run negated, and a symmetric production bug moves both sides identically ONLY if it
preserves the symmetry, which is what the property is for: it fails exactly when the two sorts are
not mirror images.
-/

namespace LeanNCD.Eval.Plan.DualityTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.PropertyOracle Std

/-- Tag every statement of `p` with `agg := a`. -/
private def retagAll (a : AggOp) (p : TLProgram) : TLProgram :=
  { p with stmts := p.stmts.map (Stmt.withAgg a) }

/-- The property excludes a nonlinearity (tropical + nonlinearity is refused) and a predicate
    destination (bool is not tropical). -/
private def outsideProperty (p : TLProgram) : Bool :=
  p.stmts.any (fun s => match s with
    | .assign _ _ r | .scatter _ _ r => !(r.nonlin == .identity)
    | .recurMorphism _ _ _ => false) ||
  p.decls.any (fun d => match d with
    | .predicate _ _ => true
    | _ => false)

private def negEnv (env : HashMap String DenseTensor) : HashMap String DenseTensor :=
  env.map fun _ t => { t with data := t.data.map (fun x => -x) }

private def to32Decl : Decl → Decl
  | .typedTensor .f64 n ax => .typedTensor .f32 n ax
  | d => d

private def env32 (env : HashMap String DenseTensor) : NamedDenseEnv32 :=
  env.map fun _ t => { shape := t.shape, data := t.data.map Float.toFloat32 }

/-- `e'` is the cell-wise negation of `e`: same keys, same shapes, `a == -b` everywhere. -/
private def dualEqOf {α : Type} [BEq α] [Neg α]
    (e e' : HashMap String (DenseTensorOf α)) : Bool :=
  e.size == e'.size && e.toList.all fun (k, t) => match e'[k]? with
    | some t' => t.shape == t'.shape && t.data.size == t'.data.size &&
        (t.data.zip t'.data).all fun (a, b) => b == -a
    | none => false

private def sameEnv (e e' : HashMap String DenseTensor) : Bool :=
  e.size == e'.size && e.toList.all fun (k, t) => match e'[k]? with
    | some t' => t.shape == t'.shape && t.data == t'.data
    | none => false

private def refRun (p : TLProgram) (env : HashMap String DenseTensor) :
    Option (HashMap String DenseTensor) :=
  match p.explicitF64.compileToScheduled.run 0 with
  | .ok sched _ => (evalScheduled sched env).toOption.map (·.env)
  | .error _ _ => none

private def planRun (p : TLProgram) (env : HashMap String DenseTensor) :
    Option (HashMap String DenseTensor) :=
  match p.explicitF64.compileToScheduled.run 0 with
  | .ok sched _ =>
      match (prepareEvalPlan sched (InputSignature.ofDenseInputs env)).toOption with
      | some prepared => (runPreparedDense prepared env).toOption.map (·.env)
      | none => none
  | .error _ _ => none

private def planRun32 (p : TLProgram) (env : NamedDenseEnv32) : Option NamedDenseEnv32 :=
  match ({ p with decls := p.decls.map to32Decl } : TLProgram).compileToScheduled.run 0 with
  | .ok sched _ =>
      match (InputSignature.ofDenseInputs32ForDecls sched.decls env).toOption with
      | some sig =>
          match (prepareEvalPlan sched sig).toOption with
          | some prepared => (runPreparedDense32 prepared env).toOption.map (·.env)
          | none => none
      | none => none
  | .error _ _ => none

/-- Per-backend tallies: programs whose twins agreed under negation, and programs refused by BOTH
    twins. `skipped` counts programs outside the property; `distinguished` is the non-vacuity count. -/
private structure Tally where
  refDual : Nat := 0
  refRefused : Nat := 0
  planDual : Nat := 0
  planRefused : Nat := 0
  plan32Dual : Nat := 0
  plan32Refused : Nat := 0
  skipped : Nat := 0
  distinguished : Nat := 0
  total : Nat := 0

private def pairVerdict {α : Type} (label : String) (p : TLProgram)
    (a b : Option α) (dual : α → α → Bool) : Except String Bool :=
  match a, b with
  | some x, some y =>
      if dual x y then pure true
      else throw s!"DUALITY VIOLATED on {label}\nprogram: {repr p}"
  | none, none => pure false
  | _, _ => throw s!"ASYMMETRIC REFUSAL on {label} (max twin {a.isSome}, min twin {b.isSome})\nprogram: {repr p}"

private def checkOne (t : Tally) (p : TLProgram) (env : HashMap String DenseTensor) :
    Except String Tally := do
  if outsideProperty p then return { t with skipped := t.skipped + 1, total := t.total + 1 }
  let pMax := retagAll .max p
  let pMin := retagAll .min p
  let nEnv := negEnv env
  let r1 ← pairVerdict "reference" pMax (refRun pMax env) (refRun pMin nEnv) (dualEqOf (α := Float))
  let r2 ← pairVerdict "checked plan f64" pMax (planRun pMax env) (planRun pMin nEnv) (dualEqOf (α := Float))
  let r3 ← pairVerdict "checked plan f32" pMax (planRun32 pMax (env32 env)) (planRun32 pMin (env32 nEnv))
    (dualEqOf (α := Float32))
  let dist := match refRun pMax env, refRun (retagAll .sum p) env with
    | some a, some b => !(sameEnv a b)
    | _, _ => false
  return { t with
    refDual := t.refDual + (if r1 then 1 else 0), refRefused := t.refRefused + (if r1 then 0 else 1),
    planDual := t.planDual + (if r2 then 1 else 0), planRefused := t.planRefused + (if r2 then 0 else 1),
    plan32Dual := t.plan32Dual + (if r3 then 1 else 0),
    plan32Refused := t.plan32Refused + (if r3 then 0 else 1),
    distinguished := t.distinguished + (if dist then 1 else 0), total := t.total + 1 }

-- Top-level scatters (`enumPrograms` has none): a strided write `Out[2i]` and an odd-offset strided write
-- `Out[2i+1]`, each with empty fibres (donor: `DifferentialTest`'s `maxScatterProg`). NB `Out[i + 1]`
-- would be a SCAN advance in this syntax (`scanAxisNotIter`), not an affine scatter.
private def stridedScatter : TLProgram := tlprog!{
  axis i : ℕ = 3
  axis j : ℕ = 2
  Out[2 * i] := maxreduce(X[i, j])
}
private def shiftedScatter : TLProgram := tlprog!{
  axis i : ℕ = 3
  axis j : ℕ = 2
  Out[2 * i + 1] := maxreduce(X[i, j])
}
private def scatterX : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[3, 2], #[5.0, 1.0, 3.0, 7.0, 2.0, 4.0]⟩

private def runAll : Except String (Tally × Tally × Tally × Tally) := do
  let sweep ← enumPrograms.foldlM (fun t pe => checkOne t pe.1 pe.2) ({} : Tally)
  let scans ← enumScanCases.foldlM (fun t c => checkOne t c.prog c.inputs) ({} : Tally)
  let grid ← tropicalUnwrittenScanCases.foldlM (fun t c => checkOne t c.prog c.inputs) ({} : Tally)
  let sc ← [stridedScatter, shiftedScatter].foldlM (fun t p => checkOne t p scatterX) ({} : Tally)
  pure (sweep, scans, grid, sc)

private def render (n : String) (t : Tally) : String :=
  s!"{n}: total={t.total} skipped={t.skipped} ref={t.refDual}/{t.refRefused} plan64={t.planDual}/{t.planRefused} \
plan32={t.plan32Dual}/{t.plan32Refused} distinguished={t.distinguished}"

run_cmd do
  match runAll with
  | .error msg => throwError msg
  | .ok (s, c, g, x) =>
      Lean.logInfo m!"{render "enumPrograms" s}\n{render "enumScanCases" c}\n{render "tropicalUnwrittenScanCases" g}\n{render "scatters" x}"

-- Pinned coverage (observed): a drop in any count means programs silently left the property.
-- The sweep has zero skips and zero refusals on every backend; the scan corpus skips exactly the four
-- template-2 (`relu`) cases and every other case is checked on all three backends.
#guard match runAll with
  | .ok (s, c, g, x) =>
      x.total == 2 && x.skipped == 0 && x.distinguished == 2 &&
      x.refDual == 2 && x.planDual == 2 && x.plan32Dual == 2 &&
      x.refRefused == 0 && x.planRefused == 0 && x.plan32Refused == 0 &&
      g.total == 2 && g.skipped == 0 && g.distinguished == 2 &&
      g.refDual == 2 && g.planDual == 2 && g.plan32Dual == 2 &&
      g.refRefused == 0 && g.planRefused == 0 && g.plan32Refused == 0 &&
      s.total == 3832 && s.skipped == 0 && s.distinguished == 3754 &&
      s.refDual == 3832 && s.planDual == 3832 && s.plan32Dual == 3832 &&
      s.refRefused == 0 && s.planRefused == 0 && s.plan32Refused == 0 &&
      c.total == 17 && c.skipped == 4 && c.distinguished == 13 &&
      c.refDual == 13 && c.planDual == 13 && c.plan32Dual == 13 &&
      c.refRefused == 0 && c.planRefused == 0 && c.plan32Refused == 0
  | .error _ => false

private def pinf : Float := 1.0 / 0.0

-- TEST THE TESTER: the comparison is a real negation check, not a shape check.
#guard dualEqOf (α := Float) (HashMap.ofList [("Y", ⟨[2], #[1.0, -2.0]⟩)])
  (HashMap.ofList [("Y", ⟨[2], #[-1.0, 2.0]⟩)])
#guard !dualEqOf (α := Float) (HashMap.ofList [("Y", ⟨[2], #[1.0, -2.0]⟩)])
  (HashMap.ofList [("Y", ⟨[2], #[1.0, 2.0]⟩)])           -- equal, not negated
#guard dualEqOf (α := Float) (HashMap.ofList [("Y", ⟨[2], #[-pinf, 0.0]⟩)])
  (HashMap.ofList [("Y", ⟨[2], #[pinf, -0.0]⟩)])    -- -inf <-> +inf, sign of zero ignored
#guard !dualEqOf (α := Float) (HashMap.ofList [("Y", ⟨[1], #[-pinf]⟩)])
  (HashMap.ofList [("Y", ⟨[1], #[-pinf]⟩)])          -- the max pad (-inf) vs the real pad is the bug this catches
#guard !dualEqOf (α := Float) (HashMap.ofList [("Y", ⟨[1], #[0.0 / 0.0]⟩)])
  (HashMap.ofList [("Y", ⟨[1], #[0.0 / 0.0]⟩)])           -- a NaN never agrees

-- The unwritten grid cell G[0,1] is 0_K of the state's sort on the reference AND the checked plan
-- (RC10 / RC10m values; row-major [r][c]): max-plus [2,-inf,5,5], min-plus [-2,+inf,-5,-5].
private def gridG (run : TLProgram → HashMap String DenseTensor → Option (HashMap String DenseTensor))
    (useMax : Bool) : Option (Array Float) :=
  let c := templateTropGrid useMax
  (run c.prog c.inputs).bind (fun e => e["G"]?) |>.map (·.data)
#guard gridG refRun true == some #[2.0, -pinf, 5.0, 5.0]
#guard gridG planRun true == some #[2.0, -pinf, 5.0, 5.0]
#guard gridG refRun false == some #[-2.0, pinf, -5.0, -5.0]
#guard gridG planRun false == some #[-2.0, pinf, -5.0, -5.0]

-- PARKED (S3b): an ALL-NEUTRAL scan state whose statements carry a tropical annotation is evaluated
-- as REAL. `M[j,0] := maxreduce(X0[j+1])` and `M[j,l+1] := maxreduce(M[j,l])` are both sort-neutral
-- writers (one term, one read, no contracted axis), so they contribute no sort, and a state with no
-- non-neutral statement is `real` (`scanStateAlgebra` = `.headD .real`); the neutral annotations are
-- rewritten to `.sum` (`scanStateStmts`), so the out-of-range read `X0[2]` pads with the REAL zero:
-- M[1,0] = 0 and the recurrence copies it, giving [[4,4],[0,0]].
-- The alternative design would let a neutral annotation SELECT the sort when nothing else does (a
-- `maxreduce` copy chain is max-plus): the pad would be -inf, giving [[4,4],[-inf,-inf]]. Which of
-- the two is right is a design decision for the task that revisits neutral writers
-- (design note S3b section 3 / A4 follow-up: "neutral annotation as a sort vote"); no such task is
-- planned in S3b. A change in either direction fails this fixture loudly on BOTH backends.
private def parkedJ : AxisSpec := ⟨"j", 271, .real⟩
private def parkedL : AxisSpec := ⟨"l", 272, .nat⟩
private def parkedAllNeutralScanState : TLProgram :=
  { decls := [.axis parkedJ (some 2), .axis parkedL (some 2), .typedTensor .f64 "X0" [parkedJ]]
    stmts :=
      [ .assign "M" [.free parkedJ, .iterAt parkedL 0]
          { body := { terms := [{ factors := [.read "X0" [.shift parkedJ 1]] }] },
            nonlin := .identity, agg := .max }
      , .assign "M" [.free parkedJ, .iterNext parkedL]
          { body := { terms := [{ factors := [.read "M" [.axis parkedJ, .axis parkedL]] }] },
            nonlin := .identity, agg := .max } ] }
private def parkedAllNeutralInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X0" ⟨[2], #[3.0, 4.0]⟩
#guard ((refRun parkedAllNeutralScanState parkedAllNeutralInputs).bind (fun e => e["M"]?)).map
    (fun t => (t.shape, t.data)) == some ([2, 2], #[4.0, 4.0, 0.0, 0.0])
#guard ((planRun parkedAllNeutralScanState parkedAllNeutralInputs).bind (fun e => e["M"]?)).map
    (fun t => (t.shape, t.data)) == some ([2, 2], #[4.0, 4.0, 0.0, 0.0])

end LeanNCD.Eval.Plan.DualityTest
