import LeanNCD.Semantics.Source.Correspondence
import LeanNCD.Semantics.Source.Permutation
import LeanNCD.Semantics.Source.Schedule

namespace LeanNCD.Semantics.Source

variable {K : Type} [Semiring K] {r : Registry (fun _ : Unit => K)}

def AdmittedStatement.globalFiber (statement : AdmittedStatement source)
    (ρ : Store (fun _ => K) source.table.declarations)
    (p : Coord (source.table.declarations.signature statement.output.tensor).axes) : K :=
  (statement.terms.map (fun term => term.globalFiber statement.output ρ p)).sum

theorem AdmittedStatement.body_correspondence (statement : AdmittedStatement source)
    (ρ : Store (fun _ => K) source.table.declarations)
    (env : Γ → Coord statement.output.context.axes) (γ : Γ) :
    interpret semiringOps ρ (statement.body (r := r) env) γ =
      some ((statement.terms.map fun term =>
        ∑ v : UIDVal term.globalContext,
          if (term.partitionCoordEquiv v).1 = env γ then term.globalProduct ρ v else 0).sum) := by
  rw [statement.interpret_body]
  simp_rw [Term.value_eq_globalSlice]

theorem AdmittedStatement.fiber_partition (statement : AdmittedStatement source)
    (ρ : Store (fun _ => K) source.table.declarations)
    (p : Coord (source.table.declarations.signature statement.output.tensor).axes) :
    statement.globalFiber ρ p =
      ∑ x : Coord statement.output.context.axes,
        if statement.destination x = p then
          (statement.terms.map (fun term => term.value ρ x)).sum else 0 := by
  have linear (terms : List (Term source.context statement.output.context
      source.table.declarations)) :
      (terms.map (fun term => term.globalFiber statement.output ρ p)).sum =
        ∑ x : Coord statement.output.context.axes,
          if statement.destination x = p then
            (terms.map (fun term => term.value ρ x)).sum else 0 := by
    induction terms with
    | nil => simp
    | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, term.fiber_partition, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : statement.output.slots.project x = p <;>
        simp [AdmittedStatement.destination, h]
  exact linear statement.terms

/-- Every original position contributes separately, using only its own term fibers. -/
def AdmittedSource.globalFiber (source : AdmittedSource)
    (ρ : Store (fun _ => K) source.source.table.declarations)
    (t : source.source.table.declarations.Tensor)
    (p : Coord (source.source.table.declarations.signature t).axes) : K :=
  ∑ i : Fin source.statements.length,
    let statement := source.statements.get i
    if h : statement.output.tensor = t then
      statement.globalFiber ρ (h.symm ▸ p) else 0

def StatementTag.globalFiber (tag : StatementTag source t)
    (ρ : Store (fun _ => K) source.source.table.declarations)
    (p : Coord (source.source.table.declarations.signature t).axes) : K :=
  tag.statement.globalFiber ρ (tag.target.symm ▸ p)

theorem AdmittedSource.globalFiber_grouped (source : AdmittedSource)
    (ρ : Store (fun _ => K) source.source.table.declarations) (t p) :
    source.globalFiber ρ t p =
      ((targetStatements source t).map (fun tag => tag.globalFiber ρ p)).sum := by
  have grouped (indices : List (Fin source.statements.length)) :
      ((indices.filterMap fun i =>
        if h : (source.statements.get i).output.tensor = t then
          some (⟨i, h⟩ : StatementTag source t) else none).map
            (fun tag => tag.globalFiber ρ p)).sum =
        (indices.map fun i =>
          if h : (source.statements.get i).output.tensor = t then
            (source.statements.get i).globalFiber ρ (h.symm ▸ p) else 0).sum := by
    induction indices with
    | nil => rfl
    | cons i indices ih =>
      by_cases h : (source.statements.get i).output.tensor = t
      · simp only [List.filterMap_cons, dif_pos h, List.map_cons, List.sum_cons, ih]
        rfl
      · simp only [List.filterMap_cons, dif_neg h, List.map_cons, List.sum_cons, zero_add, ih]
  rw [targetStatements, grouped]
  simp only [List.finRange, List.map_ofFn, List.sum_ofFn]
  rfl

theorem AdmittedSource.total_admEnv (source : AdmittedSource)
    (ρ : Store (fun _ => K) source.source.table.declarations) :
    (source.program r).AdmEnv semiringOps ρ := by
  intro t o
  unfold Program.outcome
  rw [source.program_interpret_body]
  rfl

theorem AdmittedSource.contribution_value (source : AdmittedSource)
    (ρ : Store (fun _ => K) source.source.table.declarations)
    (h : (source.program r).AdmEnv semiringOps ρ)
    (t : (source.program r).Defined) (o : (source.program r).Occurrence t) :
    (source.program r).contribution semiringOps ρ h t o =
      ((source.statementTag r t o.1).statement.terms.map
        (fun term => term.value ρ ((source.statementTag r t o.1).valuation o.2.val))).sum := by
  unfold Program.contribution Program.outcome
  simp only [source.program_interpret_body, Option.get_some]

def AdmittedSource.valuationEquiv (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t : (source.program r).Defined)
    (s : Fin ((source.program r).statements t)) :
    {v : Fin ((source.program r).valuations t s) // (source.program r).guard t s v = true} ≃
      Coord (source.statementTag r t s).statement.output.context.axes where
  toFun v := (source.statementTag r t s).valuation v.val
  invFun x := ⟨(source.statementTag r t s).layout.enumerate.symm x, rfl⟩
  left_inv v := Subtype.ext ((source.statementTag r t s).layout.enumerate.symm_apply_apply v.val)
  right_inv x := (source.statementTag r t s).layout.enumerate.apply_symm_apply x

theorem AdmittedSource.collect_statement (source : AdmittedSource)
    (ρ : Store (fun _ => K) source.source.table.declarations)
    (h : (source.program r).AdmEnv semiringOps ρ) (t : (source.program r).Defined)
    (s : Fin ((source.program r).statements t))
    (p : Coord (source.source.table.declarations.signature t.val).axes) :
    (letI := coordDecidableEq (source.source.table.declarations.signature t.val).axes;
      pushforward ((source.program r).destination t s)
        (fun v => (source.program r).contribution semiringOps ρ h t ⟨s, v⟩) p) =
      (source.statementTag r t s).globalFiber ρ p := by
  classical
  let tag := source.statementTag r t s
  rw [pushforward]
  simp_rw [source.contribution_value, source.program_destination]
  rw [← Equiv.sum_comp (source.valuationEquiv r t s).symm
    (fun v => if (tag.target ▸ tag.statement.destination (tag.valuation v.val)) = p then
      (tag.statement.terms.map (fun term => term.value ρ (tag.valuation v.val))).sum else 0)]
  have hv (x : Coord tag.statement.output.context.axes) :
      tag.valuation ((source.valuationEquiv r t s).symm x).val = x :=
    (source.valuationEquiv r t s).apply_symm_apply x
  simp_rw [hv]
  change (∑ x : Coord tag.statement.output.context.axes,
    if (tag.target ▸ tag.statement.destination x) = p then
      (tag.statement.terms.map (fun term => term.value ρ x)).sum else 0) =
        tag.globalFiber ρ p
  unfold StatementTag.globalFiber
  rw [tag.statement.fiber_partition]
  apply Finset.sum_congr rfl
  intro x _
  have transport (a b : source.source.table.declarations.Tensor) (e : a = b)
      (x : Coord (source.source.table.declarations.signature a).axes)
      (y : Coord (source.source.table.declarations.signature b).axes) :
      (e ▸ x) = y ↔ x = (e.symm ▸ y) := by
    cases e
    rfl
  simp only [transport]
  split_ifs <;> simp_all

theorem AdmittedSource.collect_correspondence (source : AdmittedSource)
    (ρ : Store (fun _ => K) source.source.table.declarations)
    (h : (source.program r).AdmEnv semiringOps ρ) (t : (source.program r).Defined)
    (p : Coord (source.source.table.declarations.signature t.val).axes) :
    (source.program r).collect semiringOps ρ h t p = source.globalFiber ρ t.val p := by
  rw [Program.collect_grouped]
  simp_rw [source.collect_statement]
  rw [source.globalFiber_grouped]
  change (∑ s : Fin (targetStatements source t.val).length,
      ((targetStatements source t.val).get s).globalFiber ρ p) = _
  rw [← List.sum_ofFn]
  change (List.ofFn ((fun tag : StatementTag source t.val => tag.globalFiber ρ p) ∘
    (targetStatements source t.val).get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem AdmittedSource.collect_relabel_correspondence (source : AdmittedSource)
    {O : (source.program r).Defined → Type} [∀ t, Fintype (O t)]
    (e : ∀ t, O t ≃ (source.program r).Occurrence t)
    (ρ : Store (fun _ => K) source.source.table.declarations)
    (h : (source.program r).AdmEnv semiringOps ρ) (t : (source.program r).Defined)
    (p : Coord (source.source.table.declarations.signature t.val).axes) :
    (source.program r).relabeledCollect semiringOps e ρ h t p =
      source.globalFiber ρ t.val p := by
  rw [Program.collect_relabel, source.collect_correspondence]

def IdentifiedSource.originalGlobalFiber (source : IdentifiedSource)
    (ρ : Store (fun _ => K) source.admitted.source.table.declarations)
    (t : source.admitted.source.table.declarations.Tensor)
    (p : Coord (source.admitted.source.table.declarations.signature t).axes) : K :=
  ∑ i : OriginalStatement source.admitted,
    let tag := (source.originalTagEquiv i).2
    if h : (source.originalTagEquiv i).1 = t then tag.globalFiber ρ (h.symm ▸ p) else 0

theorem IdentifiedSource.globalFiber_original (source : IdentifiedSource)
    (ρ : Store (fun _ => K) source.admitted.source.table.declarations) (t p) :
    source.admitted.globalFiber ρ t p = source.originalGlobalFiber ρ t p := by
  unfold IdentifiedSource.originalGlobalFiber
  let f : OriginalStatement source.admitted → K := fun i =>
    let tag := (source.originalTagEquiv i).2
    if h : (source.originalTagEquiv i).1 = t then tag.globalFiber ρ (h.symm ▸ p) else 0
  change source.admitted.globalFiber ρ t p = ∑ i, f i
  rw [← Equiv.sum_comp source.originalEquiv f]
  unfold AdmittedSource.globalFiber
  apply Finset.sum_congr rfl
  intro i _
  change (if h : (source.admitted.statements.get i).output.tensor = t then
    (source.admitted.statements.get i).globalFiber ρ (h.symm ▸ p) else 0) =
      (fun j : Fin source.admitted.statements.length =>
        if h : (source.admitted.statements.get j).output.tensor = t then
          (source.admitted.statements.get j).globalFiber ρ (h.symm ▸ p) else 0)
        (source.originalEquiv.symm (source.originalEquiv i))
  rw [Equiv.symm_apply_apply]

theorem IdentifiedSource.collect_correspondence (source : IdentifiedSource)
    (ρ : Store (fun _ => K) source.admitted.source.table.declarations)
    (h : (source.admitted.program r).AdmEnv semiringOps ρ)
    (t : (source.admitted.program r).Defined)
    (p : Coord (source.admitted.source.table.declarations.signature t.val).axes) :
    (source.admitted.program r).collect semiringOps ρ h t p =
      source.originalGlobalFiber ρ t.val p := by
  rw [source.admitted.collect_correspondence, source.globalFiber_original]

theorem StatementPermutation.globalFiber (permutation : StatementPermutation source)
    (ρ : Store (fun _ => K) source.source.table.declarations)
    (t : (source.program r).Defined)
    (p : Coord (source.source.table.declarations.signature t.val).axes) :
    permutation.reordered.globalFiber ρ t.val p = source.globalFiber ρ t.val p := by
  rw [← permutation.reordered.collect_correspondence (r := r) ρ
    (permutation.reordered.total_admEnv ρ) t p]
  rw [permutation.collect r ρ _ (source.total_admEnv ρ),
    source.collect_correspondence]

def AdmittedSource.GlobalModels (source : AdmittedSource)
    (η : (source.program r).Input)
    (ρ : Store (fun _ => K) source.source.table.declarations) : Prop :=
  (source.program r).InputAgreement η ρ ∧
    ∀ t : (source.program r).Defined, ∀ p, ρ ⟨t.val, p⟩ = source.globalFiber ρ t.val p

theorem AdmittedSource.models_iff_global (source : AdmittedSource)
    (η : (source.program r).Input)
    (ρ : Store (fun _ => K) source.source.table.declarations) :
    (source.program r).Models semiringOps η ρ ↔ source.GlobalModels η ρ := by
  constructor
  · rintro ⟨h, agree, equations⟩
    exact ⟨agree, fun t p => (equations t p).trans (source.collect_correspondence ρ h t p)⟩
  · rintro ⟨agree, equations⟩
    refine ⟨source.total_admEnv ρ, agree, ?_⟩
    intro t p
    rw [source.collect_correspondence]
    exact equations t p

open Program.Executor

/-- The existing result carries Execution from the validated initial state. -/
abbrev ActualValidatedResult (source : AdmittedSource) :=
  ValidatedResult (elaborateSource source) RationalReference.ops

theorem sourceResult_globalModel (source : AdmittedSource)
    (result : ActualValidatedResult source) (c complete)
    (h : result.result.outcome = .complete c complete) :
    source.GlobalModels (r := RationalReference.registry) result.input
      ((elaborateSource source).finalStore c complete) :=
  (source.models_iff_global _ _).mp (sourceResult_model source result c complete h)

theorem sourceResult_globalEquations (source : AdmittedSource)
    (result : ActualValidatedResult source) (c complete)
    (h : result.result.outcome = .complete c complete) :
    ∀ t : (elaborateSource source).Defined, ∀ p,
      (elaborateSource source).finalStore c complete ⟨t.val, p⟩ =
        source.globalFiber ((elaborateSource source).finalStore c complete) t.val p :=
  (sourceResult_globalModel source result c complete h).2

theorem sourceResult_globalUnique (source : AdmittedSource)
    (result : ActualValidatedResult source) (c complete)
    (h : result.result.outcome = .complete c complete) :
    ∀ ρ, source.GlobalModels (r := RationalReference.registry) result.input ρ →
      ρ = (elaborateSource source).finalStore c complete := by
  intro ρ model
  exact sourceResult_unique source result c complete h ρ ((source.models_iff_global _ _).mpr model)

theorem sourceResult_globalDenotation (source : AdmittedSource)
    (result : ActualValidatedResult source) (c complete)
    (h : result.result.outcome = .complete c complete)
    (t : {t // (elaborateSource source).output t = true})
    (p : Coord (source.source.table.declarations.signature t.val).axes) :
    (elaborateSource source).denotation RationalReference.ops result.input
      ((elaborateSource source).successful_admInput RationalReference.ops result.input c
        (result_success _ _ result.input result.result c complete h)) t p =
      source.globalFiber ((elaborateSource source).finalStore c complete) t.val p := by
  rw [sourceResult_denotation source result c complete h]
  exact sourceResult_globalEquations source result c complete h
    ⟨t.val, (elaborateSource source).output_defined t.val t.property⟩ p

end LeanNCD.Semantics.Source
