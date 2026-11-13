import IndexedAffineScanCompilerCertificates
import Batteries.Tactic.OpenPrivate

namespace IndexedExecutionExperiment.AffineScan.CompilerExamples

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.Semantics
open LeanNCD.Eval.Plan.ScanCompileTest Std

open private AffinePosition AffinePosition.coeffs AffinePosition.const AffinePosition.dim
  affinePositionsOf from LeanNCD.Eval.SizeInfer

/-! Generic loop facts: no compiler data appears here. -/

theorem foldl_invariant {α β : Type} (I : β → Prop) (f : β → α → β) (l : List α) (b : β)
    (hb : I b) (h : ∀ b, I b → ∀ a ∈ l, I (f b a)) : I (l.foldl f b) := by
  induction l generalizing b with
  | nil => exact hb
  | cons a as ih =>
      exact ih (f b a) (h b hb a List.mem_cons_self)
        (fun b hb a ha => h b hb a (List.mem_cons_of_mem _ ha))

theorem foldl_fixed {α β : Type} (f : β → α → β) (l : List α) (b : β)
    (h : ∀ a ∈ l, f b a = b) : l.foldl f b = b := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [List.foldl_cons, h a List.mem_cons_self]
      exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem forIn_yield_invariant {α β ε : Type} (P : β → Prop)
    (f : α → β → Except ε (ForInStep β)) (l : List α) (b : β) (hb : P b)
    (hstep : ∀ a ∈ l, ∀ b, P b → ∃ b', f a b = .ok (.yield b') ∧ P b') :
    ∃ b', forIn l b f = .ok b' ∧ P b' := by
  induction l generalizing b with
  | nil => exact ⟨b, rfl, hb⟩
  | cons a as ih =>
      obtain ⟨b₁, h₁, hP₁⟩ := hstep a List.mem_cons_self b hb
      obtain ⟨b₂, h₂, hP₂⟩ := ih b₁ hP₁ (fun a ha => hstep a (List.mem_cons_of_mem _ ha))
      refine ⟨b₂, ?_, hP₂⟩
      rw [List.forIn_cons, h₁]
      exact h₂

/-- A loop whose every step yields, followed by a continuation that stops the enclosing loop. -/
theorem forIn_append_bind_done {α β σ ε : Type} (l l' : List α) (b₀ : β)
    (f : α → β → Except ε (ForInStep β)) (k : β → Except ε (ForInStep σ))
    (P : β → Prop) (Q : σ → Prop) (hl' : l' = []) (hb₀ : P b₀)
    (hstep : ∀ a ∈ l, ∀ b, P b → ∃ b', f a b = .ok (.yield b') ∧ P b')
    (hk : ∀ b, P b → ∃ s, k b = .ok (.done s) ∧ Q s) :
    ∃ s, (forIn (l ++ l') b₀ f >>= k) = .ok (.done s) ∧ Q s := by
  subst hl'
  rw [List.append_nil]
  obtain ⟨b', hb', hP⟩ := forIn_yield_invariant P f l b₀ hb₀ hstep
  obtain ⟨s, hs, hQ⟩ := hk b' hP
  exact ⟨s, by rw [hb']; exact hs, hQ⟩

/-- An outer fuel loop whose first iteration stops, followed by a successful continuation. -/
theorem forIn_range_succ_bind_of_done {σ ρ ε : Type} (n : Nat) (s₀ : σ)
    (F : Nat → σ → Except ε (ForInStep σ)) (G : σ → Except ε ρ) (Q : σ → Prop) (R : ρ → Prop)
    (hF : ∃ s, F 0 s₀ = .ok (.done s) ∧ Q s)
    (hG : ∀ s, Q s → ∃ r, G s = .ok r ∧ R r) :
    ∃ r, (forIn (List.range (n + 1)) s₀ F >>= G) = .ok r ∧ R r := by
  obtain ⟨s, hs, hQ⟩ := hF
  obtain ⟨r, hr, hR⟩ := hG s hQ
  refine ⟨r, ?_, hR⟩
  rw [List.range_succ_eq_map, List.forIn_cons, hs]
  exact hr

/-! Checkable side conditions, stated over public compiler functions only. -/

/-- Every axis of one read position is already sized, and a bare-axis read agrees with its
    declared size. No diagnostic text is mentioned. -/
def positionSized (seed : HashMap UID Nat) (e : IdxExpr) (d : Nat) : Bool :=
  let form := idxAffineForm e
  let coeffs := SizeSolve.normalizeCoeffs form.2
  (SizeSolve.upperEnvelopeCoeffs coeffs).all (fun cu => seed.contains cu.2) &&
    coeffs.all (fun cu => seed.contains cu.2) &&
    (match form.1, coeffs with
      | 0, [(1, u)] => seed[u]? == some d
      | _, _ => true)

def readsSized (seed : HashMap UID Nat) (shapeOf : String → Option (List Nat))
    (stmts : List Stmt) : Bool :=
  stmts.all fun s => s.readFactors.all fun x =>
    match shapeOf x.1 with
    | none => true
    | some shape => (x.2.zip shape).all fun ed => positionSized seed ed.1 ed.2

def scatterFree (stmts : List Stmt) : Bool :=
  stmts.all fun s => match s with
    | .scatter .. => false
    | _ => true

theorem scatterOutputShapes_of_scatterFree (sizes : HashMap UID Nat) (stmts : List Stmt)
    (h : scatterFree stmts = true) : scatterOutputShapes sizes stmts = {} := by
  unfold scatterOutputShapes
  refine foldl_fixed _ _ _ ?_
  intro s hs
  have hs' := List.all_eq_true.mp h s hs
  cases s <;> simp_all

private def GoodPos (seed : HashMap UID Nat) (pos : AffinePosition) : Prop :=
  (∀ cu ∈ SizeSolve.upperEnvelopeCoeffs (AffinePosition.coeffs pos), seed.contains cu.2 = true) ∧
    (∀ cu ∈ AffinePosition.coeffs pos, seed.contains cu.2 = true) ∧
    (∀ u, AffinePosition.const pos = 0 → AffinePosition.coeffs pos = [(1, u)] →
      seed[u]? = some (AffinePosition.dim pos))

/-- When every read position is already sized and no statement is a scatter, inference returns
    the seed unchanged. The warning list is whatever the actual run produces. -/
theorem inferAxisSizesCore_of_sized (seed : HashMap UID Nat)
    (shapeOf : String → Option (List Nat)) (stmts : List Stmt)
    (hscatter : scatterFree stmts = true) (hsized : readsSized seed shapeOf stmts = true) :
    ∃ r, inferAxisSizesCore seed shapeOf stmts = .ok r ∧ r.1 = seed := by
  unfold inferAxisSizesCore
  generalize hp : List.flatMap _ stmts = positions
  have hgood : ∀ pos ∈ positions, GoodPos seed pos := by
    intro pos hpos
    subst hp
    simp only [List.mem_flatMap] at hpos
    obtain ⟨s, hs, ⟨nm, es⟩, hx, hpos⟩ := hpos
    have hx' := List.all_eq_true.mp (List.all_eq_true.mp hsized s hs) (nm, es) hx
    dsimp only at hpos hx'
    cases hshape : shapeOf nm with
    | none => simp [hshape] at hpos
    | some shape =>
        simp only [hshape, affinePositionsOf, List.mem_map] at hpos hx'
        obtain ⟨⟨e, d⟩, hed, rfl⟩ := hpos
        have hsz := List.all_eq_true.mp hx' (e, d) hed
        unfold positionSized at hsz
        rcases hform : idxAffineForm e with ⟨c₀, cf⟩
        simp only [hform, Bool.and_eq_true, List.all_eq_true] at hsz
        obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hsz
        refine ⟨h₁, h₂, ?_⟩
        intro u hconst hcoeffs
        dsimp only at hconst hcoeffs
        subst hconst
        rw [hcoeffs] at h₃
        simpa using h₃
  clear hp
  dsimp only
  refine forIn_range_succ_bind_of_done _ _ _ _ (fun s => s.fst = seed) _ ?hF ?hG
  case hF =>
    dsimp only
    refine forIn_append_bind_done positions _ _ _ _ (fun b => b.fst = []) _ ?hl' rfl ?hstep ?hk
    case hl' =>
      rw [scatterOutputShapes_of_scatterFree seed stmts hscatter]
      simp
    case hstep =>
      rintro pos hpos ⟨deferred, warns⟩ hb
      dsimp only at hb
      subst hb
      obtain ⟨hup, -, hbare⟩ := hgood pos hpos
      dsimp only
      rw [List.filter_eq_nil_iff.mpr (fun cu hcu => by simpa using hup cu hcu)]
      dsimp only
      split
      · rename_i u hconst hcoeffs
        rw [hbare u hconst hcoeffs]
        dsimp only
        rw [if_neg (by simp)]
        exact ⟨_, rfl, rfl⟩
      · split <;> exact ⟨_, rfl, rfl⟩
    case hk =>
      rintro ⟨deferred, warns⟩ hb
      dsimp only at hb
      subst hb
      dsimp only
      rw [if_pos (by simp)]
      exact ⟨_, rfl, rfl⟩
  case hG =>
    rintro ⟨sizes, warns⟩ hs
    dsimp only at hs
    subst sizes
    dsimp only
    rw [foldl_fixed (β := List UID) _ _ [] ?_]
    · exact ⟨_, rfl, rfl⟩
    · rintro ⟨u, c⟩ hmem
      have hc : seed.contains u = true := by
        rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hmem
        refine foldl_invariant
          (fun m : HashMap UID Int => ∀ k c, m[k]? = some c → seed.contains k = true)
          _ _ _ (by simp) ?_ u c hmem
        intro m hm pos hpos
        refine foldl_invariant
          (fun m : HashMap UID Int => ∀ k c, m[k]? = some c → seed.contains k = true)
          _ _ _ hm ?_
        intro m hm cu hcu k c hk
        rw [Std.HashMap.getElem?_insert] at hk
        split at hk
        · rename_i hkey
          rw [← beq_iff_eq.mp hkey]
          exact (hgood pos hpos).2.1 cu hcu
        · exact hm k c hk
      simp [hc]

attribute [local cbv_opaque] Std.HashMap.toList
attribute [local cbv_opaque] Std.HashMap.contains Std.HashMap.get? Std.HashMap.getD
attribute [local cbv_eval] string_beq_self word_beq_self decide_eq_self
attribute [local cbv_eval] hashMap_toList_singleton hashMap_toList_singleton_capacity
attribute [local cbv_eval] Std.HashMap.toList_emptyWithCapacity
attribute [local cbv_opaque] LeanNCD.scheduleAlgebras LeanNCD.checkSortCasts
attribute [local cbv_opaque] LeanNCD.Eval.Plan.inferAxisSizesFromSignature
attribute [local cbv_opaque] LeanNCD.collectDefinitions LeanNCD.collectorShapeObligations
attribute [local cbv_opaque] LeanNCD.Eval.Plan.InputSignature.ofDenseInputs
attribute [local cbv_opaque] certifyProfile LeanNCD.validateScheduled

local cbv_simproc cbv_eval mixedFoldLiteralList (@List.foldl _ _ _ _ _) :=
  foldLiteralList

attribute [local cbv_opaque] List.foldl

theorem perm_triple_cases {α : Type} {l : List α} {a b c : α} (h : l.Perm [a, b, c]) :
    l = [a, b, c] ∨ l = [a, c, b] ∨ l = [b, a, c] ∨
      l = [b, c, a] ∨ l = [c, a, b] ∨ l = [c, b, a] := by
  cases l with
  | nil => have hl := h.length_eq; simp at hl
  | cons x xs =>
      have hx : x = a ∨ x = b ∨ x = c := by
        simpa using h.mem_iff.mp List.mem_cons_self
      rcases hx with hx | hx | hx
      · subst x
        rcases perm_pair_cases h.cons_inv with hh | hh <;> simp [hh]
      · subst x
        have hs : [a, b, c].Perm [b, a, c] := .swap _ _ _
        rcases perm_pair_cases (h.trans hs).cons_inv with hh | hh <;> simp [hh]
      · subst x
        have hs₁ : [a, b, c].Perm [a, c, b] := .cons _ (.swap _ _ _)
        have hs₂ : [a, c, b].Perm [c, a, b] := .swap _ _ _
        rcases perm_pair_cases (h.trans (hs₁.trans hs₂)).cons_inv with hh | hh <;> simp [hh]

def mixedDeclEnv : DeclEnv := spatialDeclEnv.insert "X" (.typedTensor .f64 "X" [axJ])
def mixedSource : ScheduledProgram := { explicitF64Sched mixedSched with env := mixedDeclEnv }
def mixedSizes : HashMap UID Nat := declaredAxisSizes mixedSource.decls

set_option maxHeartbeats 0 in
theorem mixed_algebras :
    scheduleAlgebras mixedDeclEnv mixedSched.stmts =
      .ok (({} : HashMap String SortAlgebra).insert "S" .real) := by
  unfold scheduleAlgebras mixedDeclEnv spatialDeclEnv
  have ht := Std.HashMap.toList_insert_perm (m := spatialDeclEnv) (k := "X")
    (v := Decl.typedTensor .f64 "X" [axJ])
  simp only [spatialDeclEnv] at ht
  have htwo := hashMap_toList_two "S" "S0"
    (Decl.typedTensor .f64 "S" [axJ, axL]) (Decl.typedTensor .f64 "S0" [axJ]) (by decide)
  rcases htwo with htwo | htwo
  all_goals
    rw [htwo] at ht
    simp at ht
    rcases perm_triple_cases ht with h | h | h | h | h | h
    all_goals rw [h]; cbv

set_option maxHeartbeats 0 in
theorem mixed_casts :
    checkSortCasts mixedDeclEnv (({} : HashMap String SortAlgebra).insert "S" .real)
      mixedSched.stmts = .ok () := by
  unfold checkSortCasts
  actual_table_cbv

set_option maxHeartbeats 0 in
theorem mixed_collection :
    collectDefinitions mixedSource mixedSizes = .ok (mixedSource, []) := by
  unfold collectDefinitions
  cbv

set_option maxHeartbeats 0 in
theorem mixed_obligations :
    collectorShapeObligations mixedSource mixedSizes = .ok [] := by
  unfold collectorShapeObligations
  cbv

def externalZ : DenseTensor := vectorInputs.getD "S0" ⟨[], #[]⟩
def externalX : DenseTensor := externalInputs.getD "X" ⟨[], #[]⟩

theorem external_inputs_decompose :
    externalInputs =
      (({} : HashMap String DenseTensor).insert "S0" externalZ).insert "X" externalX := by
  simp [externalInputs, vectorInputs, externalZ, externalX]

def mixedSignature (swapped : Bool) : InputSignature :=
  if swapped then
    { tensors := (({} : HashMap String TensorSignature).insert "X" { shape := #[9], dtype := .f64 })
        |>.insert "S0" { shape := #[4], dtype := .f64 } }
  else
    { tensors := (({} : HashMap String TensorSignature).insert "S0" { shape := #[4], dtype := .f64 })
        |>.insert "X" { shape := #[9], dtype := .f64 } }

set_option maxHeartbeats 0 in
theorem mixed_signature_cases :
    InputSignature.ofDenseInputs externalInputs = mixedSignature true ∨
      InputSignature.ofDenseInputs externalInputs = mixedSignature false := by
  unfold InputSignature.ofDenseInputs
  rw [external_inputs_decompose]
  have h := hashMap_toList_two "S0" "X" externalZ externalX (by decide)
  rcases h with h | h
  · left
    rw [h]
    cbv
  · right
    rw [h]
    cbv

attribute [-cbv_eval] hashMap_toList_singleton hashMap_toList_singleton_capacity
  Std.HashMap.toList_emptyWithCapacity

theorem mixed_scatterFree :
    scatterFree (mixedSource.stmts.flatMap ScanStmt.sourceStmts) = true := by
  cbv

theorem mixed_readsSized (swapped : Bool) :
    readsSized mixedSizes
      (fun nm => ((mixedSignature swapped).tensors[nm]?).map (fun ts => ts.shape.toList))
      (mixedSource.stmts.flatMap ScanStmt.sourceStmts) = true := by
  cases swapped <;> cbv

theorem mixed_inference_fst (swapped : Bool) :
    (inferAxisSizesFromSignature mixedSizes (mixedSignature swapped)
      (mixedSource.stmts.flatMap ScanStmt.sourceStmts)).map Prod.fst = .ok mixedSizes := by
  obtain ⟨r, hr, hfst⟩ :=
    inferAxisSizesCore_of_sized _ _ _ mixed_scatterFree (mixed_readsSized swapped)
  unfold inferAxisSizesFromSignature
  rw [hr]
  exact congrArg Except.ok hfst

theorem mixed_inference_success (swapped : Bool) :
    (inferAxisSizesFromSignature mixedSizes (mixedSignature swapped)
      (mixedSource.stmts.flatMap ScanStmt.sourceStmts)).isOk = true := by
  have h := mixed_inference_fst swapped
  cases he : inferAxisSizesFromSignature mixedSizes (mixedSignature swapped)
      (mixedSource.stmts.flatMap ScanStmt.sourceStmts) <;>
    simp_all [Except.map, Except.isOk, Except.toBool]

def mixedInference (swapped : Bool) : HashMap UID Nat × List EvalWarning :=
  successfulValue (inferAxisSizesFromSignature mixedSizes (mixedSignature swapped)
    (mixedSource.stmts.flatMap ScanStmt.sourceStmts)) (mixed_inference_success swapped)

theorem mixedInference_origin (swapped : Bool) :
    inferAxisSizesFromSignature mixedSizes (mixedSignature swapped)
      (mixedSource.stmts.flatMap ScanStmt.sourceStmts) = .ok (mixedInference swapped) :=
  successfulValue_origin _ (mixed_inference_success swapped)

attribute [local cbv_opaque] mixedInference

theorem mixedInference_sizes (swapped : Bool) : (mixedInference swapped).1 = mixedSizes := by
  have h := mixed_inference_fst swapped
  rw [mixedInference_origin] at h
  exact Except.ok.inj h

theorem mixed_inferred (swapped : Bool) :
    inferAxisSizesFromSignature mixedSizes (mixedSignature swapped)
      (mixedSource.stmts.flatMap ScanStmt.sourceStmts) =
      .ok (mixedSizes, (mixedInference swapped).2) := by
  exact (mixedInference_origin swapped).trans
    (congrArg Except.ok (Prod.ext (mixedInference_sizes swapped) rfl))

set_option cbv.maxSteps 500000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem mixed_success : mixedExample.isOk = true := by
  change (compileExample mixedSched externalInputs 4 3).isOk = true
  rw [compileExample_isOk]
  actual_table_cbv
  unfold validateScheduled
  actual_table_cbv
  have ha := mixed_algebras
  cbv at ha
  rw [ha]
  actual_table_cbv
  have hc := mixed_casts
  cbv at hc
  rw [hc]
  actual_table_cbv
  have hcollect := mixed_collection
  cbv at hcollect
  rw [hcollect]
  actual_table_cbv
  have ho := mixed_obligations
  cbv at ho
  rw [ho]
  actual_table_cbv
  rcases mixed_signature_cases with hs | hs
  · cbv at hs
    rw [hs]
    actual_table_cbv
    have hi := mixed_inferred true
    cbv at hi
    rw [hi]
    actual_table_cbv
    change (certifyProfile _ _ 4 3).isOk = true
    rw [certifyProfile_isOk]
    actual_table_cbv
  · cbv at hs
    rw [hs]
    actual_table_cbv
    have hi := mixed_inferred false
    cbv at hi
    rw [hi]
    actual_table_cbv
    change (certifyProfile _ _ 4 3).isOk = true
    rw [certifyProfile_isOk]
    actual_table_cbv

def mixedCompiled : CompiledExample 4 3 := successfulValue mixedExample mixed_success
def mixedCertifiedProfile : Profile 4 3 := mixedCompiled.profile

theorem mixedCompiled_origin : mixedExample = .ok mixedCompiled :=
  successfulValue_origin _ mixed_success

theorem mixed_profile_inhabited : Nonempty (Profile 4 3) := ⟨mixedCertifiedProfile⟩


end IndexedExecutionExperiment.AffineScan.CompilerExamples

#audit_axioms IndexedExecutionExperiment.AffineScan.CompilerExamples
