import LeanNCD.Semantics.Source.Program
import Mathlib.Data.List.Sigma

namespace LeanNCD.Semantics.Source

theorem admitStatement_original (source : AdaptedSource) (i : Nat) (stmt : Stmt)
    (checked : AdmittedStatement source) (h : admitStatement source i stmt = .ok checked) :
    checked.original = i := by
  cases stmt <;> simp only [admitStatement, bind, pure, Except.bind, Except.pure,
    throw, MonadExceptOf.throw, throwThe] at h
  all_goals repeat' (first | contradiction | split at h)
  all_goals simp_all
  all_goals subst checked; rfl

private theorem mapM_originals {α β ε : Type} (f : α → Except ε β)
    (a : α → Nat) (b : β → Nat)
    (hf : ∀ x y, f x = .ok y → b y = a x)
    (xs : List α) (ys : List β) (h : xs.mapM f = .ok ys) :
    ys.map b = xs.map a := by
  induction xs generalizing ys with
  | nil => simpa [pure, Except.pure] using h.symm
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, Except.bind, Except.pure] at h
    cases hx : f x with
    | error e => simp [hx] at h
    | ok y =>
      cases hs : xs.mapM f with
      | error e => simp [hx, hs] at h
      | ok zs =>
        have hy : y :: zs = ys := by simpa [hx, hs] using h
        subst ys
        simp [hf x y hx, ih zs hs]

theorem adaptSource_originals (snapshot : SourceSnapshot) (source : AdaptedSource)
    (h : adaptSource snapshot = .ok source) :
    (source.statements.map Prod.fst).Nodup := by
  unfold adaptSource at h
  simp only [bind, pure, Except.bind, Except.pure] at h
  repeat' split at h
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at h
  all_goals subst source
  all_goals simpa [List.map_map, Function.comp_def] using
    List.nodup_zipIdx_map_snd snapshot.resolved.stmts

theorem admitSource_originals (snapshot : SourceSnapshot) (source : AdmittedSource)
    (h : admitSource snapshot = .ok source) :
    (source.statements.map AdmittedStatement.original).Nodup := by
  unfold admitSource at h
  simp only [bind, pure, Except.bind, Except.pure] at h
  cases ha : adaptSource snapshot with
  | error e => simp [ha] at h
  | ok adapted =>
    cases hs : adapted.statements.mapM (fun (i, s) => admitStatement adapted i s) with
    | error e => simp [ha, hs] at h
    | ok statements =>
      have he : (⟨adapted, statements⟩ : AdmittedSource) = source := by
        simpa [ha, hs, Except.bind, Except.pure] using h
      subst source
      rw [mapM_originals _ Prod.fst AdmittedStatement.original
        (fun x y hxy => admitStatement_original adapted x.1 x.2 y hxy) _ _ hs]
      exact adaptSource_originals snapshot adapted ha

/-- Certification is produced by admission, not assumed of arbitrary admitted records. -/
structure IdentifiedSource where
  admitted : AdmittedSource
  unique : (admitted.statements.map AdmittedStatement.original).Nodup

def admitIdentifiedSource (snapshot : SourceSnapshot) :
    Except SourceDiagnostic IdentifiedSource :=
  match h : admitSource snapshot with
  | .error e => .error e
  | .ok source => .ok ⟨source, admitSource_originals snapshot source h⟩

def admitRawIdentifiedSource (raw : TLProgram) (specs : List TensorSpec)
    (inputs : List InputBinding) : Except SourceDiagnostic IdentifiedSource := do
  let snapshot ← resolveSource raw specs inputs
  admitIdentifiedSource snapshot

abbrev OriginalStatement (source : AdmittedSource) :=
  {i : Nat // i ∈ source.statements.map AdmittedStatement.original}

def IdentifiedSource.originalEquiv (source : IdentifiedSource) :
    Fin source.admitted.statements.length ≃ OriginalStatement source.admitted :=
  (finCongr (List.length_map (f := AdmittedStatement.original)
    (as := source.admitted.statements)).symm).trans
    (List.Nodup.getEquiv _ source.unique)

theorem IdentifiedSource.originalEquiv_val (source : IdentifiedSource)
    (i : Fin source.admitted.statements.length) :
    (source.originalEquiv i).val = (source.admitted.statements.get i).original := by
  simp [IdentifiedSource.originalEquiv]

def statementIndexEquiv (source : AdmittedSource) :
    Fin source.statements.length ≃
      (t : source.source.table.declarations.Tensor) × StatementTag source t where
  toFun i := ⟨(source.statements.get i).output.tensor, ⟨i, rfl⟩⟩
  invFun tag := tag.2.sourceIndex
  left_inv _ := rfl
  right_inv tag := by
    rcases tag with ⟨t, i, h⟩
    cases h
    rfl

instance : DecidableEq (StatementTag source t) :=
  fun a b => decidable_of_iff (a.sourceIndex = b.sourceIndex) (by
    constructor
    · cases a; cases b; intro h; cases h; rfl
    · intro h; exact congrArg StatementTag.sourceIndex h)

theorem targetStatements_nodup (source : AdmittedSource) (t) :
    (targetStatements source t).Nodup := by
  apply List.Nodup.filterMap _ (List.nodup_finRange _)
  intro a b tag ha hb
  split at ha <;> simp_all
  obtain ⟨_, hb⟩ := hb
  exact (congrArg StatementTag.sourceIndex ha).trans
    (congrArg StatementTag.sourceIndex hb).symm

def targetTagEquiv (source : AdmittedSource) (t) :
    Fin (targetStatements source t).length ≃ StatementTag source t :=
  List.Nodup.getEquivOfForallMemList _ (targetStatements_nodup source t)
    StatementTag.mem_targetStatements

def IdentifiedSource.originalTagEquiv (source : IdentifiedSource) :
    OriginalStatement source.admitted ≃
      (t : source.admitted.source.table.declarations.Tensor) × StatementTag source.admitted t :=
  source.originalEquiv.symm.trans (statementIndexEquiv source.admitted)

def IdentifiedSource.originalLocalEquiv (source : IdentifiedSource) :
    OriginalStatement source.admitted ≃
      (t : source.admitted.source.table.declarations.Tensor) ×
        Fin (targetStatements source.admitted t).length :=
  source.originalTagEquiv.trans
    (Equiv.sigmaCongrRight fun t => (targetTagEquiv source.admitted t).symm)

theorem IdentifiedSource.originalTag_original (source : IdentifiedSource)
    (i : OriginalStatement source.admitted) :
    (source.originalTagEquiv i).2.original = i.val := by
  have h := congrArg Subtype.val (source.originalEquiv.apply_symm_apply i)
  rw [source.originalEquiv_val] at h
  exact h

def IdentifiedSource.originalToLocal (source : IdentifiedSource) :=
  source.originalLocalEquiv

def IdentifiedSource.localToOriginal (source : IdentifiedSource) :=
  source.originalLocalEquiv.symm

theorem IdentifiedSource.local_original_inverse (source : IdentifiedSource)
    (i : OriginalStatement source.admitted) :
    source.localToOriginal (source.originalToLocal i) = i :=
  source.originalLocalEquiv.symm_apply_apply i

theorem IdentifiedSource.original_local_inverse (source : IdentifiedSource)
    (tag : (t : source.admitted.source.table.declarations.Tensor) ×
      Fin (targetStatements source.admitted t).length) :
    source.originalToLocal (source.localToOriginal tag) = tag :=
  source.originalLocalEquiv.apply_symm_apply tag

theorem IdentifiedSource.originalTag_coverage (source : IdentifiedSource)
    (tag : (t : source.admitted.source.table.declarations.Tensor) ×
      StatementTag source.admitted t) :
    ∃ i, source.originalTagEquiv i = tag :=
  source.originalTagEquiv.surjective tag

theorem IdentifiedSource.originalLocal_coverage (source : IdentifiedSource)
    (tag : (t : source.admitted.source.table.declarations.Tensor) ×
      Fin (targetStatements source.admitted t).length) :
    ∃ i, source.originalToLocal i = tag :=
  source.originalLocalEquiv.surjective tag

def StatementTag.uidValuationEquiv (tag : StatementTag source t) :
    Fin tag.layout.count ≃ UIDVal tag.statement.output.context :=
  tag.layout.enumerate.trans (uidCoordEquiv tag.statement.output.context).symm

def outputAssignments (statement : AdmittedStatement adapted)
    (v : Fin (canonicalLayout statement.output.context.axes).count) : List (UID × Nat) :=
  let c := statement.output.context
  let values := (uidCoordEquiv c).symm ((canonicalLayout c.axes).enumerate v)
  (List.finRange c.axes.length).map fun i =>
    let u := c.uidEquiv i
    (u.val, (values u).val)

def StatementTag.occurrenceIdentity (tag : StatementTag source t)
    (v : Fin tag.layout.count) : Nat × List (UID × Nat) :=
  (tag.original, outputAssignments tag.statement v)

end LeanNCD.Semantics.Source
