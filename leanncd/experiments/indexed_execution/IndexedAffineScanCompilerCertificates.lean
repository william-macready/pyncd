import IndexedAffineScanCompilerExamples

namespace IndexedExecutionExperiment.AffineScan.CompilerExamples

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.Semantics
open LeanNCD.Eval.Plan.ScanCompileTest Std

attribute [local cbv_opaque] Std.HashMap.toList
attribute [local cbv_opaque] Std.HashMap.contains Std.HashMap.get? Std.HashMap.getD

@[local cbv_eval]
theorem string_beq_self (s : String) : (s == s) = true := by simp

@[local cbv_eval]
theorem word_beq_self (x : UInt64) : (x == x) = true := by simp

@[local cbv_eval]
theorem decide_eq_self {α : Type} [DecidableEq α] (x : α) : decide (x = x) = true := by simp

theorem perm_pair_cases {α : Type} {l : List α} {a b : α} (h : l.Perm [a, b]) :
    l = [a, b] ∨ l = [b, a] := by
  have hlen := h.length_eq
  cases l with
  | nil => simp at hlen
  | cons x xs =>
      cases xs with
      | nil => simp at hlen
      | cons y ys =>
          have hz : ys.length = 0 := by simpa using hlen
          have he : ys = [] := by simpa using hz
          subst ys
          have hx : x = a ∨ x = b := by
            simpa using h.mem_iff.mp (List.mem_cons_self)
          rcases hx with hx | hx
          · subst x
            have hy : y = b := by simpa using h.cons_inv.eq_singleton
            subst y
            exact Or.inl rfl
          · subst x
            have hs : [a, b].Perm [b, a] := .swap _ _ _
            have hy : y = a := by simpa using (h.trans hs).cons_inv.eq_singleton
            subst y
            exact Or.inr rfl

@[local cbv_eval]
theorem hashMap_toList_singleton {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] (k : α) (v : β) :
    ((∅ : Std.HashMap α β).insert k v).toList = [(k, v)] := by
  have h := Std.HashMap.toList_insert_perm (m := (∅ : Std.HashMap α β)) (k := k) (v := v)
  simp only [Std.HashMap.toList_empty, List.filter_nil] at h
  exact h.eq_singleton

@[local cbv_eval]
theorem hashMap_toList_singleton_capacity {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] (capacity : Nat) (k : α) (v : β) :
    ((Std.HashMap.emptyWithCapacity capacity : Std.HashMap α β).insert k v).toList = [(k, v)] := by
  have h := Std.HashMap.toList_insert_perm
    (m := (Std.HashMap.emptyWithCapacity capacity : Std.HashMap α β)) (k := k) (v := v)
  simp only [Std.HashMap.toList_emptyWithCapacity, List.filter_nil] at h
  exact h.eq_singleton

attribute [local cbv_eval] Std.HashMap.toList_emptyWithCapacity

theorem hashMap_toList_two {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] (k k' : α) (v v' : β)
    (hne : (k' == k) = false) :
    ((∅ : Std.HashMap α β).insert k v |>.insert k' v').toList = [(k', v'), (k, v)] ∨
    ((∅ : Std.HashMap α β).insert k v |>.insert k' v').toList = [(k, v), (k', v')] := by
  have h := Std.HashMap.toList_insert_perm
    (m := (∅ : Std.HashMap α β).insert k v) (k := k') (v := v')
  simp [hashMap_toList_singleton, hne] at h
  exact perm_pair_cases h

theorem compileExample_isOk (sched : ScheduledProgram) (inputs : HashMap String DenseTensor)
    (d n : Nat) :
    (compileExample sched inputs d n).isOk =
      match prepareEvalPlan (explicitF64Sched sched) (InputSignature.ofDenseInputs inputs) with
      | .error _ => false
      | .ok p =>
          match scanAt p 0 with
          | none => false
          | some raw => (certifyProfile p.plan.raw.tensorSigs raw d n).isOk := by
  dsimp only [compileExample]
  split <;> rename_i hp
  · simp only [hp, Except.isOk, Except.toBool]
  · simp only [hp]
    split <;> rename_i hs
    · simp only [hs, Except.isOk, Except.toBool]
    · simp only [hs]
      split <;> rename_i hc <;> simp only [hc, Except.isOk, Except.toBool]

theorem certifyProfile_isOk (sigs : Array TensorSignature) (raw : RawScanPlan) (d n : Nat) :
    (certifyProfile sigs raw d n).isOk =
      match checkScanPlan sigs raw with
      | .error _ => false
      | .ok c => profileOk c d n := by
  unfold certifyProfile
  split <;> rename_i hc
  · simp only [hc, Except.isOk, Except.toBool]
  · simp only [hc]
    split <;> simp_all [Except.isOk, Except.toBool]

theorem shift_algebras :
    scheduleAlgebras
      ((({} : DeclEnv).insert "S" (.typedTensor .f64 "S" [axJ, axL])).insert
        "S0" (.typedTensor .f64 "S0" [axJ])) shiftSched.stmts =
      .ok (({} : HashMap String SortAlgebra).insert "S" .real) := by
  unfold scheduleAlgebras
  have h := hashMap_toList_two "S" "S0"
    (Decl.typedTensor .f64 "S" [axJ, axL]) (Decl.typedTensor .f64 "S0" [axJ]) (by decide)
  rcases h with h | h <;> rw [h] <;> cbv

attribute [local cbv_opaque] LeanNCD.scheduleAlgebras

theorem shift_casts :
    checkSortCasts
      ((({} : DeclEnv).insert "S" (.typedTensor .f64 "S" [axJ, axL])).insert
        "S0" (.typedTensor .f64 "S0" [axJ]))
      (({} : HashMap String SortAlgebra).insert "S" .real) shiftSched.stmts = .ok () := by
  cbv

def spatialDeclEnv : DeclEnv :=
  (({} : DeclEnv).insert "S" (.typedTensor .f64 "S" [axJ, axL])).insert
    "S0" (.typedTensor .f64 "S0" [axJ])

def shiftSource : ScheduledProgram := { explicitF64Sched shiftSched with env := spatialDeclEnv }
def shiftSizes : HashMap UID Nat := declaredAxisSizes shiftSource.decls

theorem shift_collection :
    collectDefinitions shiftSource shiftSizes = .ok (shiftSource, []) := by
  cbv

theorem shift_obligations :
    collectorShapeObligations shiftSource shiftSizes = .ok [] := by
  cbv

theorem vector_signature :
    InputSignature.ofDenseInputs vectorInputs =
      { tensors := ({} : HashMap String TensorSignature).insert "S0" { shape := #[4], dtype := .f64 } } := by
  simp only [InputSignature.ofDenseInputs, vectorInputs, hashMap_toList_singleton,
    List.foldl_cons, List.foldl_nil]
  rfl

theorem shift_inferred :
    inferAxisSizesFromSignature shiftSizes (InputSignature.ofDenseInputs vectorInputs)
      (shiftSource.stmts.flatMap ScanStmt.sourceStmts) = .ok (shiftSizes, []) := by
  rw [vector_signature]
  cbv

attribute [local cbv_opaque] LeanNCD.checkSortCasts
attribute [local cbv_opaque] LeanNCD.Eval.Plan.inferAxisSizesFromSignature
attribute [local cbv_opaque] LeanNCD.collectDefinitions LeanNCD.collectorShapeObligations
attribute [local cbv_opaque] LeanNCD.Eval.Plan.InputSignature.ofDenseInputs
attribute [local cbv_opaque] certifyProfile

set_option cbv.maxSteps 500000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem shift_success : shiftExample.isOk = true := by
  rw [show shiftExample = compileExample shiftSched vectorInputs 4 3 from rfl, compileExample_isOk]
  cbv
  have ha := shift_algebras
  dsimp only [shiftSched, recurrenceSched, stateFactor, Prototype.spatialSched, axisPosSched, axJ, axL,
    Std.HashMap.instEmptyCollection, EmptyCollection.emptyCollection] at ha
  rw [ha]
  cbv
  have hc := shift_casts
  dsimp only [shiftSched, recurrenceSched, stateFactor, Prototype.spatialSched, axisPosSched, axJ, axL,
    Std.HashMap.instEmptyCollection, EmptyCollection.emptyCollection] at hc
  rw [hc]
  cbv
  have hcollect := shift_collection
  cbv at hcollect
  rw [hcollect]
  cbv
  have ho := shift_obligations
  cbv at ho
  rw [ho]
  cbv
  have hs := vector_signature
  cbv at hs
  rw [hs]
  cbv
  have hi := shift_inferred
  rw [vector_signature] at hi
  cbv at hi
  rw [hi]
  cbv
  change (certifyProfile _ _ 4 3).isOk = true
  rw [certifyProfile_isOk]
  cbv

def successfulValue {ε α : Type} (result : Except ε α) (h : result.isOk = true) : α :=
  result.toOption.get (by cases result <;> simpa [Except.isOk, Except.toBool, Except.toOption] using h)

theorem successfulValue_origin {ε α : Type} (result : Except ε α) (h : result.isOk = true) :
    result = .ok (successfulValue result h) := by
  cases result with
  | error err => simp [Except.isOk, Except.toBool] at h
  | ok value => rfl

def shiftCompiled : CompiledExample 4 3 := successfulValue shiftExample shift_success
def shiftCertifiedProfile : Profile 4 3 := shiftCompiled.profile

theorem shiftCompiled_origin : shiftExample = .ok shiftCompiled :=
  successfulValue_origin shiftExample shift_success

theorem shift_profile_inhabited : Nonempty (Profile 4 3) := ⟨shiftCertifiedProfile⟩

inductive SpatialDonor
  | shift | stride | reversal | deep | boundary22 | boundary20 | boundary02 | boundary00
  deriving Repr

def spatialDonorSched : SpatialDonor → ScheduledProgram
  | .shift => shiftSched
  | .stride => strideSched
  | .reversal => reversalSched
  | .deep => deepSched
  | .boundary22 => Prototype.spatialSched 2 2
  | .boundary20 => Prototype.spatialSched 2 0
  | .boundary02 => Prototype.spatialSched 0 2
  | .boundary00 => Prototype.spatialSched 0 0

def spatialDonorD : SpatialDonor → Nat
  | .boundary22 | .boundary20 => 2
  | .boundary02 | .boundary00 => 0
  | _ => 4

def spatialDonorN : SpatialDonor → Nat
  | .boundary22 | .boundary02 => 2
  | .boundary20 | .boundary00 => 0
  | _ => 3

def spatialDonorInputs (donor : SpatialDonor) : HashMap String DenseTensor :=
  match donor with
  | .boundary22 | .boundary20 => Prototype.spatialInputs 2
  | .boundary02 | .boundary00 => Prototype.spatialInputs 0
  | _ => vectorInputs

def spatialDonorSource (donor : SpatialDonor) : ScheduledProgram :=
  { explicitF64Sched (spatialDonorSched donor) with env := spatialDeclEnv }

def spatialDonorSizes (donor : SpatialDonor) : HashMap UID Nat :=
  declaredAxisSizes (spatialDonorSource donor).decls

def spatialDonorExample (donor : SpatialDonor) :=
  compileExample (spatialDonorSched donor) (spatialDonorInputs donor)
    (spatialDonorD donor) (spatialDonorN donor)

set_option maxHeartbeats 0 in
theorem spatialDonor_algebras (donor : SpatialDonor) :
    scheduleAlgebras spatialDeclEnv (spatialDonorSched donor).stmts =
      .ok (({} : HashMap String SortAlgebra).insert "S" .real) := by
  unfold scheduleAlgebras spatialDeclEnv
  have h := hashMap_toList_two "S" "S0"
    (Decl.typedTensor .f64 "S" [axJ, axL]) (Decl.typedTensor .f64 "S0" [axJ]) (by decide)
  rcases h with h | h <;> rw [h] <;> cases donor <;> cbv

set_option maxHeartbeats 0 in
theorem spatialDonor_casts (donor : SpatialDonor) :
    checkSortCasts spatialDeclEnv (({} : HashMap String SortAlgebra).insert "S" .real)
      (spatialDonorSched donor).stmts = .ok () := by
  unfold checkSortCasts
  cases donor <;> cbv

set_option maxHeartbeats 0 in
theorem spatialDonor_collection (donor : SpatialDonor) :
    collectDefinitions (spatialDonorSource donor) (spatialDonorSizes donor) =
      .ok (spatialDonorSource donor, []) := by
  unfold collectDefinitions
  cases donor <;> cbv

set_option maxHeartbeats 0 in
theorem spatialDonor_obligations (donor : SpatialDonor) :
    collectorShapeObligations (spatialDonorSource donor) (spatialDonorSizes donor) = .ok [] := by
  unfold collectorShapeObligations
  cases donor <;> cbv

set_option maxHeartbeats 0 in
theorem spatialDonor_signature (donor : SpatialDonor) :
    InputSignature.ofDenseInputs (spatialDonorInputs donor) =
      { tensors := ({} : HashMap String TensorSignature).insert "S0"
          { shape := #[spatialDonorD donor], dtype := .f64 } } := by
  cases donor <;> first
  | exact vector_signature
  | unfold InputSignature.ofDenseInputs; cbv

set_option maxHeartbeats 0 in
theorem spatialDonor_inferred (donor : SpatialDonor) :
    inferAxisSizesFromSignature (spatialDonorSizes donor)
      (InputSignature.ofDenseInputs (spatialDonorInputs donor))
      ((spatialDonorSource donor).stmts.flatMap ScanStmt.sourceStmts) =
      .ok (spatialDonorSizes donor, []) := by
  rw [spatialDonor_signature]
  unfold inferAxisSizesFromSignature
  cases donor <;> cbv

attribute [local cbv_opaque] LeanNCD.validateScheduled

local cbv_simproc cbv_eval foldLiteralList (@List.foldl _ _ _ _ _) := fun e => do
  let args := e.getAppArgs
  let xs := args[4]!.consumeMData
  let result :=
    if xs.isAppOf ``List.nil then
      args[3]!
    else if xs.isAppOf ``List.cons then
      let parts := xs.getAppArgs
      Lean.mkAppN e.getAppFn
        #[args[0]!, args[1]!, args[2]!, Lean.mkApp2 args[2]! args[3]! parts[1]!, parts[2]!]
    else
      e
  if result == e then return .rfl
  let result ← Lean.Meta.Sym.share result
  return .step result (← Lean.Meta.Sym.mkEqRefl result)

attribute [local cbv_opaque] List.foldl

private def actualTableCbvLoop : Lean.Elab.Tactic.TacticM Unit := do
  for _ in [:4] do
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return
    Lean.Elab.Tactic.evalTactic (← `(tactic| cbv))
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return
    Lean.Elab.Tactic.evalTactic (← `(tactic| try simp only [List.foldl_cons, List.foldl_nil]))

elab "actual_table_cbv" : tactic => actualTableCbvLoop

macro "close_spatial_donor " donor:term : tactic =>
  `(tactic|
    (change (spatialDonorExample $donor).isOk = true
     unfold spatialDonorExample
     rw [compileExample_isOk]
     actual_table_cbv
     unfold validateScheduled
     actual_table_cbv
     have ha := spatialDonor_algebras $donor
     cbv at ha
     rw [ha]
     actual_table_cbv
     have hc := spatialDonor_casts $donor
     cbv at hc
     rw [hc]
     actual_table_cbv
     have hcollect := spatialDonor_collection $donor
     cbv at hcollect
     rw [hcollect]
     actual_table_cbv
     have ho := spatialDonor_obligations $donor
     cbv at ho
     rw [ho]
     actual_table_cbv
     have hs := spatialDonor_signature $donor
     cbv at hs
     rw [hs]
     try simp only [List.foldl_cons, List.foldl_nil]
     actual_table_cbv
     have hi := spatialDonor_inferred $donor
     rw [spatialDonor_signature] at hi
     cbv at hi
     rw [hi]
     actual_table_cbv
     change (certifyProfile _ _ _ _).isOk = true
     rw [certifyProfile_isOk]
     actual_table_cbv))

set_option cbv.maxSteps 500000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem stride_success : strideExample.isOk = true := by close_spatial_donor SpatialDonor.stride

set_option cbv.maxSteps 500000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem reversal_success : reversalExample.isOk = true := by close_spatial_donor SpatialDonor.reversal

set_option cbv.maxSteps 500000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem deep_success : deepExample.isOk = true := by close_spatial_donor SpatialDonor.deep

set_option cbv.maxSteps 500000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem boundary22_success : (spatialDonorExample .boundary22).isOk = true := by
  close_spatial_donor SpatialDonor.boundary22

set_option cbv.maxSteps 500000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem boundary20_success : (spatialDonorExample .boundary20).isOk = true := by
  close_spatial_donor SpatialDonor.boundary20

set_option cbv.maxSteps 500000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem boundary02_success : (spatialDonorExample .boundary02).isOk = true := by
  close_spatial_donor SpatialDonor.boundary02

set_option cbv.maxSteps 500000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem boundary00_success : (spatialDonorExample .boundary00).isOk = true := by
  close_spatial_donor SpatialDonor.boundary00

theorem spatialDonor_success (donor : SpatialDonor) :
    (spatialDonorExample donor).isOk = true := by
  cases donor
  · exact shift_success
  · exact stride_success
  · exact reversal_success
  · exact deep_success
  · exact boundary22_success
  · exact boundary20_success
  · exact boundary02_success
  · exact boundary00_success

def spatialDonorCompiled (donor : SpatialDonor) :
    CompiledExample (spatialDonorD donor) (spatialDonorN donor) :=
  successfulValue (spatialDonorExample donor) (spatialDonor_success donor)

theorem spatialDonorCompiled_origin (donor : SpatialDonor) :
    spatialDonorExample donor = .ok (spatialDonorCompiled donor) :=
  successfulValue_origin _ (spatialDonor_success donor)

def strideCompiled : CompiledExample 4 3 := spatialDonorCompiled .stride
def reversalCompiled : CompiledExample 4 3 := spatialDonorCompiled .reversal
def deepCompiled : CompiledExample 4 3 := spatialDonorCompiled .deep
def boundaryCompiled : CompiledExample 2 2 := spatialDonorCompiled .boundary22
def zeroRecurrenceCompiled : CompiledExample 2 0 := spatialDonorCompiled .boundary20
def emptySpatialCompiled : CompiledExample 0 2 := spatialDonorCompiled .boundary02
def emptyBothCompiled : CompiledExample 0 0 := spatialDonorCompiled .boundary00

def strideCertifiedProfile : Profile 4 3 := strideCompiled.profile
def reversalCertifiedProfile : Profile 4 3 := reversalCompiled.profile
def deepCertifiedProfile : Profile 4 3 := deepCompiled.profile
def zeroRecurrenceCertifiedProfile : Profile 2 0 := zeroRecurrenceCompiled.profile
def emptySpatialCertifiedProfile : Profile 0 2 := emptySpatialCompiled.profile
def emptyBothCertifiedProfile : Profile 0 0 := emptyBothCompiled.profile

theorem strideCompiled_origin : strideExample = .ok strideCompiled :=
  spatialDonorCompiled_origin .stride
theorem reversalCompiled_origin : reversalExample = .ok reversalCompiled :=
  spatialDonorCompiled_origin .reversal
theorem deepCompiled_origin : deepExample = .ok deepCompiled :=
  spatialDonorCompiled_origin .deep

theorem zeroRecurrence_profile_inhabited : Nonempty (Profile 2 0) :=
  ⟨zeroRecurrenceCertifiedProfile⟩
theorem emptySpatial_profile_inhabited : Nonempty (Profile 0 2) :=
  ⟨emptySpatialCertifiedProfile⟩
theorem emptyBoth_profile_inhabited : Nonempty (Profile 0 0) :=
  ⟨emptyBothCertifiedProfile⟩


end IndexedExecutionExperiment.AffineScan.CompilerExamples

#audit_axioms IndexedExecutionExperiment.AffineScan.CompilerExamples
