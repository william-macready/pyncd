import LeanNCD.Semantics.Source.Provenance
import LeanNCD.Semantics.Models

namespace LeanNCD.Semantics.Source

/-- A bijection of positions transports whole checked statements, including their attached IDs. -/
structure StatementPermutation (source : AdmittedSource) where
  statements : List (AdmittedStatement source.source)
  index : Fin statements.length ≃ Fin source.statements.length
  get_eq : ∀ i, statements.get i = source.statements.get (index i)

def permuteStatements (source : AdmittedSource)
    (e : Equiv.Perm (Fin source.statements.length)) : StatementPermutation source where
  statements := List.ofFn (fun i => source.statements.get (e i))
  index := (finCongr List.length_ofFn).trans e
  get_eq i := by simp [Fin.cast]

namespace StatementPermutation

variable {source : AdmittedSource} (p : StatementPermutation source)

def reordered : AdmittedSource := ⟨source.source, p.statements⟩

@[simp] theorem source_unchanged : p.reordered.source = source.source := rfl

def tagEquiv (t : source.source.table.declarations.Tensor) :
    StatementTag p.reordered t ≃ StatementTag source t where
  toFun tag := ⟨p.index tag.sourceIndex, by
    rw [← p.get_eq]; exact tag.target⟩
  invFun tag := ⟨p.index.symm tag.sourceIndex, by
    change (p.statements.get _).output.tensor = t
    rw [p.get_eq, p.index.apply_symm_apply]; exact tag.target⟩
  left_inv tag := by
    cases tag
    simp only [Equiv.symm_apply_apply]
  right_inv tag := by
    cases tag
    simp only [Equiv.apply_symm_apply]

@[simp] theorem tag_statement (t) (tag : StatementTag p.reordered t) :
    tag.statement = (p.tagEquiv t tag).statement :=
  p.get_eq tag.sourceIndex

@[simp] theorem tag_original (t) (tag : StatementTag p.reordered t) :
    (p.tagEquiv t tag).original = tag.original :=
  congrArg AdmittedStatement.original (p.tag_statement t tag).symm

def localEquiv (t : source.source.table.declarations.Tensor) :
    Fin (targetStatements p.reordered t).length ≃ Fin (targetStatements source t).length :=
  (targetTagEquiv p.reordered t).trans
    ((p.tagEquiv t).trans (targetTagEquiv source t).symm)

theorem local_statement (t) (s : Fin (targetStatements p.reordered t).length) :
    ((targetStatements p.reordered t).get s).statement =
      ((targetStatements source t).get (p.localEquiv t s)).statement := by
  simp [localEquiv, targetTagEquiv]

def identified (source : IdentifiedSource) (p : StatementPermutation source.admitted) :
    IdentifiedSource where
  admitted := p.reordered
  unique := by
    apply List.nodup_iff_injective_get.mpr
    intro i j hij
    let i' : Fin p.statements.length := ⟨i.val, by simpa using i.isLt⟩
    let j' : Fin p.statements.length := ⟨j.val, by simpa using j.isLt⟩
    have hids : (p.statements.get i').original = (p.statements.get j').original := by
      simpa [List.get_eq_getElem] using hij
    have he : p.index i' = p.index j' := by
      apply source.originalEquiv.injective
      apply Subtype.ext
      rw [source.originalEquiv_val, source.originalEquiv_val,
        ← p.get_eq i', ← p.get_eq j']
      exact hids
    exact Fin.ext (congrArg (fun k : Fin p.statements.length => k.val)
      (p.index.injective he))

theorem original_index (source : IdentifiedSource) (p : StatementPermutation source.admitted)
    (i : Fin p.statements.length) :
    ((identified source p).originalEquiv i).val =
      (source.originalEquiv (p.index i)).val := by
  rw [IdentifiedSource.originalEquiv_val, IdentifiedSource.originalEquiv_val]
  exact congrArg AdmittedStatement.original (p.get_eq i)

private def guardedFinEquiv {n m : Nat} (h : n = m) :
    {_v : Fin n // true = true} ≃ {_v : Fin m // true = true} :=
  Equiv.subtypeEquiv (finCongr h) (fun _ => Iff.rfl)

variable {K : Type} [Semiring K] (r : Registry (fun _ : Unit => K))

def occurrenceEquiv (t : (source.program r).Defined) :
    (p.reordered.program r).Occurrence t ≃ (source.program r).Occurrence t :=
  Equiv.sigmaCongr (p.localEquiv t.val) fun s =>
    guardedFinEquiv (congrArg (fun st : AdmittedStatement source.source =>
      (canonicalLayout st.output.context.axes).count) (p.local_statement t.val s))

private theorem value_transport (a b : AdmittedStatement adapted) (h : a = b)
    (ρ : Store (fun _ => K) adapted.table.declarations)
    (v : Fin (canonicalLayout a.output.context.axes).count) :
    (b.terms.map (fun term => term.value ρ
      ((canonicalLayout b.output.context.axes).enumerate
        (finCongr (congrArg (fun st : AdmittedStatement adapted =>
          (canonicalLayout st.output.context.axes).count) h) v)))).sum =
      (a.terms.map (fun term => term.value ρ
        ((canonicalLayout a.output.context.axes).enumerate v))).sum := by
  cases h
  rfl

private theorem body_transport (a b : AdmittedStatement adapted) (h : a = b) :
    HEq (a.body (r := r) (fun v : {_v : Fin (canonicalLayout a.output.context.axes).count //
      true = true} => (canonicalLayout a.output.context.axes).enumerate v.val))
      (b.body (r := r) (fun v : {_v : Fin (canonicalLayout b.output.context.axes).count //
      true = true} => (canonicalLayout b.output.context.axes).enumerate v.val)) := by
  cases h
  rfl

theorem bodies (t : (source.program r).Defined)
    (s : Fin ((p.reordered.program r).statements t)) :
    HEq ((p.reordered.program r).body t s)
      ((source.program r).body t (p.localEquiv t.val s)) :=
  body_transport r _ _ (p.local_statement t.val s)

private theorem footprint_transport (a b : AdmittedStatement adapted) (h : a = b)
    (v : Fin (canonicalLayout a.output.context.axes).count) :
    b.terms.flatMap (fun term => term.readFootprint
      ((canonicalLayout b.output.context.axes).enumerate
        (finCongr (congrArg (fun st : AdmittedStatement adapted =>
          (canonicalLayout st.output.context.axes).count) h) v))) =
      a.terms.flatMap (fun term => term.readFootprint
        ((canonicalLayout a.output.context.axes).enumerate v)) := by
  cases h
  rfl

private theorem destination_transport (a b : AdmittedStatement adapted) (h : a = b)
    (t : adapted.table.declarations.Tensor) (ha : a.output.tensor = t)
    (hb : b.output.tensor = t) (v : Fin (canonicalLayout a.output.context.axes).count) :
    (hb ▸ b.destination ((canonicalLayout b.output.context.axes).enumerate
      (finCongr (congrArg (fun st : AdmittedStatement adapted =>
        (canonicalLayout st.output.context.axes).count) h) v))) =
      (ha ▸ a.destination ((canonicalLayout a.output.context.axes).enumerate v)) := by
  cases h
  rfl

theorem outcome (ρ : Store (fun _ => K) source.source.table.declarations)
    (t : (source.program r).Defined) (o : (p.reordered.program r).Occurrence t) :
    (source.program r).outcome semiringOps ρ t (p.occurrenceEquiv r t o) =
      (p.reordered.program r).outcome semiringOps ρ t o := by
  unfold Program.outcome
  rw [source.program_interpret_body r ρ t _ _,
    p.reordered.program_interpret_body r ρ t o.1 o.2]
  exact congrArg some (value_transport _ _ (p.local_statement t.val o.1) ρ o.2.val)

theorem footprints (t : (source.program r).Defined)
    (o : (p.reordered.program r).Occurrence t) :
    footprint ((source.program r).body t (p.occurrenceEquiv r t o).1)
      (p.occurrenceEquiv r t o).2 =
      footprint ((p.reordered.program r).body t o.1) o.2 := by
  simp only [AdmittedSource.program_footprint_body]
  exact footprint_transport _ _ (p.local_statement t.val o.1) o.2.val

theorem destinations (t : (source.program r).Defined)
    (o : (p.reordered.program r).Occurrence t) :
    (source.program r).destination t (p.occurrenceEquiv r t o).1
      (p.occurrenceEquiv r t o).2 =
      (p.reordered.program r).destination t o.1 o.2 := by
  exact destination_transport _ _ (p.local_statement t.val o.1) t.val _ _ o.2.val

theorem guards (t : (source.program r).Defined)
    (o : (p.reordered.program r).Occurrence t) :
    (source.program r).guard t (p.occurrenceEquiv r t o).1
      (p.occurrenceEquiv r t o).2.val =
      (p.reordered.program r).guard t o.1 o.2.val := rfl

theorem originals (t : (source.program r).Defined)
    (o : (p.reordered.program r).Occurrence t) :
    (source.statementTag r t (p.occurrenceEquiv r t o).1).original =
      (p.reordered.statementTag r t o.1).original :=
  congrArg AdmittedStatement.original (p.local_statement t.val o.1).symm

private theorem assignments_transport (a b : AdmittedStatement adapted) (h : a = b)
    (v : Fin (canonicalLayout a.output.context.axes).count) :
    outputAssignments b (finCongr (congrArg (fun st : AdmittedStatement adapted =>
      (canonicalLayout st.output.context.axes).count) h) v) = outputAssignments a v := by
  cases h
  rfl

theorem identities (t : (source.program r).Defined)
    (o : (p.reordered.program r).Occurrence t) :
    (source.statementTag r t (p.occurrenceEquiv r t o).1).occurrenceIdentity
      (p.occurrenceEquiv r t o).2.val =
      (p.reordered.statementTag r t o.1).occurrenceIdentity o.2.val := by
  apply Prod.ext
  · exact p.originals r t o
  · exact assignments_transport _ _ (p.local_statement t.val o.1) o.2.val

theorem admEnv (ρ : Store (fun _ => K) source.source.table.declarations) :
    (p.reordered.program r).AdmEnv semiringOps ρ ↔ (source.program r).AdmEnv semiringOps ρ := by
  rw [← (source.program r).admEnv_relabel semiringOps (p.occurrenceEquiv r) ρ]
  simp only [p.outcome]
  rfl

theorem contribution (ρ : Store (fun _ => K) source.source.table.declarations)
    (hnew : (p.reordered.program r).AdmEnv semiringOps ρ)
    (hold : (source.program r).AdmEnv semiringOps ρ)
    (t : (source.program r).Defined) (o : (p.reordered.program r).Occurrence t) :
    (source.program r).contribution semiringOps ρ hold t (p.occurrenceEquiv r t o) =
      (p.reordered.program r).contribution semiringOps ρ hnew t o := by
  unfold Program.contribution
  simp only [p.outcome]

theorem collect (ρ : Store (fun _ => K) source.source.table.declarations)
    (hnew : (p.reordered.program r).AdmEnv semiringOps ρ)
    (hold : (source.program r).AdmEnv semiringOps ρ)
    (t : (source.program r).Defined) :
    (p.reordered.program r).collect semiringOps ρ hnew t =
      (source.program r).collect semiringOps ρ hold t := by
  rw [← (source.program r).collect_relabel semiringOps (p.occurrenceEquiv r) ρ hold t]
  unfold Program.collect Program.relabeledCollect
  simp only [p.destinations, p.contribution r ρ hnew hold]
  rfl

theorem models (η : (source.program r).Input)
    (ρ : Store (fun _ => K) source.source.table.declarations) :
    (p.reordered.program r).Models semiringOps η ρ ↔
      (source.program r).Models semiringOps η ρ := by
  constructor
  · rintro ⟨h, agree, equations⟩
    refine ⟨(p.admEnv r ρ).mp h, agree, ?_⟩
    intro t x
    rw [← p.collect r ρ h ((p.admEnv r ρ).mp h)]
    exact equations t x
  · rintro ⟨h, agree, equations⟩
    refine ⟨(p.admEnv r ρ).mpr h, agree, ?_⟩
    intro t x
    rw [p.collect r ρ ((p.admEnv r ρ).mpr h) h]
    exact equations t x

end StatementPermutation
end LeanNCD.Semantics.Source
