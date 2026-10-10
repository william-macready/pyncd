import LeanNCD.Semantics.Source.RawCorrespondence
import LeanNCD.Semantics.Source.ProgramCorrespondence

namespace LeanNCD.Semantics.Source

theorem Slots.uids_length (slots : Slots ctx sh) : slots.uids.length = sh.length := by
  induction slots with
  | nil => rfl
  | cons _ _ ih => simpa [Slots.uids] using ih

/-- The position is a tensor slot, not a deduplicated support position. -/
theorem Slots.project_lookup (c : Context) (slots : Slots c.axes sh)
    (v : UIDVal c) (j : Fin sh.length) :
    ∃ u : c.Key, slots.uids[j.val]? = some u.val ∧
      Coord.raw (slots.project (uidCoordEquiv c v)) j = (v u).val := by
  induction slots with
  | nil => exact Fin.elim0 j
  | cons ref rest ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨ref.key c, ?_, ?_⟩
      · simp [Slots.uids]
      · simp only [Slots.project, Coord.raw, Fin.cases_zero]
        rw [ref.get_uidCoordEquiv]
        rfl
    · obtain ⟨u, hu, hv⟩ := ih j
      exact ⟨u, by simpa [Slots.uids] using hu,
        by simpa [Slots.project, Coord.raw] using hv⟩

theorem RawReadSlots.coordinate {raw : TLProgram} {memo : Std.HashMap String UID}
    {es : List IdxExpr} {c : Context} {sh : Shape} {slots : Slots c.axes sh}
    (h : RawReadSlots raw memo es slots.uids) (v : UIDVal c) (j : Fin sh.length) :
    ∃ a, ∃ u : c.Key, es[j.val]? = some (.axis a) ∧
      RawAxisFields raw memo a u.val ∧ memo[a.name]? = some u.val ∧
      Coord.raw (slots.project (uidCoordEquiv c v)) j = (v u).val := by
  obtain ⟨u, hu, hv⟩ := slots.project_lookup c v j
  let k : Fin slots.uids.length := ⟨j.val, by rw [slots.uids_length]; exact j.isLt⟩
  obtain ⟨a, ha, hf⟩ := h.slot k
  have he : slots.uids.get k = u.val := by
    exact Option.some.inj ((List.getElem?_eq_getElem k.isLt).symm.trans hu)
  rw [he] at hf
  exact ⟨a, u, ha, hf, hf.lookup, hv⟩

theorem RawOutputSlots.coordinate {raw : TLProgram} {memo : Std.HashMap String UID}
    {es : List LHSSlot} {c : Context} {sh : Shape} {slots : Slots c.axes sh}
    (h : RawOutputSlots raw memo es slots.uids) (v : UIDVal c) (j : Fin sh.length) :
    ∃ a, ∃ u : c.Key, es[j.val]? = some (.free a) ∧
      RawAxisFields raw memo a u.val ∧ memo[a.name]? = some u.val ∧
      Coord.raw (slots.project (uidCoordEquiv c v)) j = (v u).val := by
  obtain ⟨u, hu, hv⟩ := slots.project_lookup c v j
  let k : Fin slots.uids.length := ⟨j.val, by rw [slots.uids_length]; exact j.isLt⟩
  obtain ⟨a, ha, hf⟩ := h.slot k
  have he : slots.uids.get k = u.val := by
    exact Option.some.inj ((List.getElem?_eq_getElem k.isLt).symm.trans hu)
  rw [he] at hf
  exact ⟨a, u, ha, hf, hf.lookup, hv⟩

variable {raw : TLProgram} {specs : List TensorSpec} {inputs : List InputBinding}
  {admitted : AdmittedSource} {snapshot : SourceSnapshot} {memo : Std.HashMap String UID}

structure CertifiedRawStatement (raw : TLProgram) (specs : List TensorSpec)
    (admitted : AdmittedSource) (snapshot : SourceSnapshot) (memo : Std.HashMap String UID)
    (i : Fin admitted.statements.length) (ast : Stmt) : Prop where
  occurrence : raw.stmts[i.val]? = some ast
  fields : RawStatementFields raw memo admitted.source i.val ast (admitted.statements.get i)
  declaration : RawTensorEntryFields raw memo admitted.source.context specs
    snapshot.resolved.decls (admitted.source.table.entry (admitted.statements.get i).output.tensor)

structure CertifiedRawTerm (raw : TLProgram) (specs : List TensorSpec)
    (admitted : AdmittedSource) (snapshot : SourceSnapshot) (memo : Std.HashMap String UID)
    (i : Fin admitted.statements.length) (j : Fin (admitted.statements.get i).terms.length)
    (ast : Stmt) (product : ProdTerm) : Prop where
  statement : CertifiedRawStatement raw specs admitted snapshot memo i ast
  occurrence : ∃ name slots rhs, ast = .assign name slots rhs ∧
    rhs.body.terms[j.val]? = some product
  fields : RawTermFields raw memo admitted.source
    { side := .read, statement := some i.val, term := some j.val }
    product ((admitted.statements.get i).terms.get j)

theorem RawCorrespondence.certifiedStatement
    (h : RawCorrespondence raw specs inputs admitted snapshot memo)
    (i : Fin admitted.statements.length) :
    ∃ ast, CertifiedRawStatement raw specs admitted snapshot memo i ast := by
  obtain ⟨ast, ha, hs⟩ := h.statement i
  exact ⟨ast, ha, hs, h.tensor (admitted.statements.get i).output.tensor⟩

theorem CertifiedRawStatement.term {i : Fin admitted.statements.length} {ast : Stmt}
    (h : CertifiedRawStatement raw specs admitted snapshot memo i ast)
    (j : Fin (admitted.statements.get i).terms.length) :
    ∃ product, CertifiedRawTerm raw specs admitted snapshot memo i j ast product := by
  obtain ⟨name, slots, rhs, product, he, hp, ht⟩ := h.fields.term j
  exact ⟨product, h, ⟨name, slots, rhs, he, hp⟩, ht⟩

theorem CertifiedRawTerm.read_projection
    (hc : RawCorrespondence raw specs inputs admitted snapshot memo)
    {i : Fin admitted.statements.length} {j : Fin (admitted.statements.get i).terms.length}
    {ast : Stmt} {product : ProdTerm}
    (h : CertifiedRawTerm raw specs admitted snapshot memo i j ast product)
    (k : Fin ((admitted.statements.get i).terms.get j).sourceReads.length)
    (v : UIDVal admitted.source.context) :
    let term := (admitted.statements.get i).terms.get j
    let read := term.sourceReads.get k
    ∃ name es,
      product.factors[k.val]? = some (.read name es) ∧
      RawCheckedFactorFields raw memo admitted.source
        { side := .read, statement := some i.val, term := some j.val, factor := some k.val }
        (.read name es) read ∧
      RawTensorEntryFields raw memo admitted.source.context specs snapshot.resolved.decls
        (admitted.source.table.entry read.read.tensor) ∧
      (admitted.source.table.entry read.read.tensor).name = name ∧
      RawReadSlots raw memo es read.read.slots.uids ∧
      (term.reads k).slots.project
        (uidCoordEquiv term.partition.context (indexPullback term.partition.embedding.map v)) =
        read.read.slots.project (uidCoordEquiv admitted.source.context v) ∧
      ∀ q : Fin (admitted.source.table.declarations.signature read.read.tensor).axes.length,
        ∃ a, ∃ u : admitted.source.context.Key, es[q.val]? = some (.axis a) ∧
          RawAxisFields raw memo a u.val ∧ memo[a.name]? = some u.val ∧
          Coord.raw ((term.reads k).slots.project
            (uidCoordEquiv term.partition.context
              (indexPullback term.partition.embedding.map v))) q = (v u).val ∧
          Coord.raw (read.read.slots.project
            (uidCoordEquiv admitted.source.context v)) q = (v u).val := by
  obtain ⟨factor, hf, hr⟩ := h.fields.factor k
  obtain ⟨name, es, he, hd, hn, hs, _⟩ := hc.read hr
  subst factor
  refine ⟨name, es, hf, hr, hd, hn, hs, Term.read_projection _ k v, ?_⟩
  intro q
  obtain ⟨a, u, ha, hu, hm, hv⟩ := hs.coordinate v q
  exact ⟨a, u, ha, hu, hm, by rw [Term.read_projection]; exact hv, hv⟩

theorem CertifiedRawStatement.output_projection
    {i : Fin admitted.statements.length} {ast : Stmt}
    (h : CertifiedRawStatement raw specs admitted snapshot memo i ast)
    (v : UIDVal admitted.source.context) :
    let statement := admitted.statements.get i
    ∃ name slots rhs, ast = .assign name slots rhs ∧ statement.original = i.val ∧
      RawTensorEntryFields raw memo admitted.source.context specs snapshot.resolved.decls
        (admitted.source.table.entry statement.output.tensor) ∧
      (admitted.source.table.entry statement.output.tensor).name = name ∧
      RawOutputSlots raw memo slots statement.output.slots.uids ∧
      RawOutputSlots raw memo slots statement.output.sourceSlots.uids ∧
      statement.output.origin = {
        side := .output, statement := some i.val,
        declaration := some (admitted.source.table.entry statement.output.tensor).declaration } ∧
      statement.destination
        (uidCoordEquiv statement.output.context
          (indexPullback statement.output.embedding.map v)) =
        statement.output.sourceSlots.project (uidCoordEquiv admitted.source.context v) ∧
      ∀ q : Fin (admitted.source.table.declarations.signature statement.output.tensor).axes.length,
        ∃ a, ∃ u : admitted.source.context.Key, slots[q.val]? = some (.free a) ∧
          RawAxisFields raw memo a u.val ∧ memo[a.name]? = some u.val ∧
          Coord.raw (statement.destination
            (uidCoordEquiv statement.output.context
              (indexPullback statement.output.embedding.map v))) q = (v u).val ∧
          Coord.raw (statement.output.sourceSlots.project
            (uidCoordEquiv admitted.source.context v)) q = (v u).val := by
  obtain ⟨name, slots, rhs, he, hi, _, _, _, hn, _, ho, _⟩ := h.fields
  have hs := h.fields
  rw [he] at hs
  obtain ⟨hl, hg⟩ := hs.output_slots
  refine ⟨name, slots, rhs, he, hi, h.declaration, hn, hl, hg, ho,
    AdmittedStatement.destination_pullback _ v, ?_⟩
  intro q
  obtain ⟨a, u, ha, hu, hm, hv⟩ := hg.coordinate v q
  exact ⟨a, u, ha, hu, hm, by rw [AdmittedStatement.destination_pullback]; exact hv, hv⟩

variable {K : Type} [Semiring K] {r : Registry (fun _ : Unit => K)}

theorem CertifiedRawTerm.semantics
    {i : Fin admitted.statements.length} {j : Fin (admitted.statements.get i).terms.length}
    {ast : Stmt} {product : ProdTerm}
    (h : CertifiedRawTerm raw specs admitted snapshot memo i j ast product)
    (ρ : Store (fun _ => K) admitted.source.table.declarations)
    (x : Coord (admitted.statements.get i).output.context.axes)
    (p : Coord (admitted.source.table.declarations.signature
      (admitted.statements.get i).output.tensor).axes)
    (v : UIDVal admitted.source.context) :
    let statement := admitted.statements.get i
    let term := statement.terms.get j
    CertifiedRawTerm raw specs admitted snapshot memo i j ast product ∧
      product.factors.length = term.sourceReads.length ∧
      (∀ uid, uid ∈ term.globalContext.axes.map Axis.uid ↔
        uid ∈ term.support ∨ uid ∈ statement.output.context.axes.map Axis.uid) ∧
      interpret semiringOps ρ (term.body (r := r) id) x =
        some (∑ w : UIDVal term.globalContext,
          if (term.partitionCoordEquiv w).1 = x then term.globalProduct ρ w else 0) ∧
      term.collectedBody (r := r) statement.output ρ p =
        some (term.globalFiber statement.output ρ p) ∧
      footprint (term.body (K := K) (r := r) id) x = term.readFootprint x ∧
      term.readAddresses
        (uidCoordEquiv term.partition.context (indexPullback term.partition.embedding.map v)) =
        term.sourceReads.map
          (fun read => ⟨read.read.tensor,
            read.read.slots.project (uidCoordEquiv admitted.source.context v)⟩) :=
  ⟨h, h.fields.factor_count, Term.global_support _, Term.body_correspondence _ ρ id x,
    Term.collectedBody_correspondence _ _ ρ p, Term.footprint_body _ id x,
    Term.readAddresses_pullback _ v⟩

theorem CertifiedRawStatement.semantics
    {i : Fin admitted.statements.length} {ast : Stmt}
    (h : CertifiedRawStatement raw specs admitted snapshot memo i ast)
    (ρ : Store (fun _ => K) admitted.source.table.declarations)
    (x : Coord (admitted.statements.get i).output.context.axes)
    (p : Coord (admitted.source.table.declarations.signature
      (admitted.statements.get i).output.tensor).axes) :
    let statement := admitted.statements.get i
    CertifiedRawStatement raw specs admitted snapshot memo i ast ∧
      (∃ name slots rhs, ast = .assign name slots rhs ∧
        rhs.body.terms.length = statement.terms.length) ∧
      interpret semiringOps ρ (statement.body (r := r) id) x =
        some ((statement.terms.map fun term =>
          ∑ w : UIDVal term.globalContext,
            if (term.partitionCoordEquiv w).1 = x then term.globalProduct ρ w else 0).sum) ∧
      footprint (statement.body (K := K) (r := r) id) x =
        statement.terms.flatMap (fun term => term.readFootprint x) ∧
      statement.globalFiber ρ p =
        ∑ y : Coord statement.output.context.axes,
          if statement.destination y = p then
            (statement.terms.map (fun term => term.value ρ y)).sum else 0 :=
  ⟨h, h.fields.term_count, AdmittedStatement.body_correspondence _ ρ id x,
    AdmittedStatement.footprint_body _ id x, AdmittedStatement.fiber_partition _ ρ p⟩

structure CertifiedRawSource (raw : TLProgram) (specs : List TensorSpec)
    (inputs : List InputBinding) (admitted : AdmittedSource)
    (snapshot : SourceSnapshot) (memo : Std.HashMap String UID) : Prop where
  correspondence : RawCorrespondence raw specs inputs admitted snapshot memo
  statements : ∀ i, ∃ ast, CertifiedRawStatement raw specs admitted snapshot memo i ast

theorem RawCorrespondence.certifiedSource
    (h : RawCorrespondence raw specs inputs admitted snapshot memo) :
    CertifiedRawSource raw specs inputs admitted snapshot memo :=
  ⟨h, h.certifiedStatement⟩

theorem admitRawSource_certified
    (h : admitRawSource raw specs inputs = .ok admitted) :
    ∃ snapshot memo, CertifiedRawSource raw specs inputs admitted snapshot memo := by
  obtain ⟨snapshot, memo, hc⟩ := admitRawSource_fields _ _ _ _ h
  exact ⟨snapshot, memo, hc.certifiedSource⟩

theorem CertifiedRawSource.collect
    (h : CertifiedRawSource raw specs inputs admitted snapshot memo)
    (ρ : Store (fun _ => K) admitted.source.table.declarations)
    (t : (admitted.program r).Defined)
    (p : Coord (admitted.source.table.declarations.signature t.val).axes) :
    CertifiedRawSource raw specs inputs admitted snapshot memo ∧
      RawTensorEntryFields raw memo admitted.source.context specs snapshot.resolved.decls
        (admitted.source.table.entry t.val) ∧
      (admitted.program r).collect semiringOps ρ (admitted.total_admEnv ρ) t p =
        admitted.globalFiber ρ t.val p :=
  ⟨h, h.correspondence.tensor t.val,
    admitted.collect_correspondence ρ (admitted.total_admEnv ρ) t p⟩

theorem CertifiedRawSource.models
    (h : CertifiedRawSource raw specs inputs admitted snapshot memo)
    (η : (admitted.program r).Input)
    (ρ : Store (fun _ => K) admitted.source.table.declarations) :
    CertifiedRawSource raw specs inputs admitted snapshot memo ∧
      (∀ t : (admitted.program r).Defined,
        RawTensorEntryFields raw memo admitted.source.context specs snapshot.resolved.decls
          (admitted.source.table.entry t.val)) ∧
      ((admitted.program r).Models semiringOps η ρ ↔ admitted.GlobalModels η ρ) :=
  ⟨h, fun t => h.correspondence.tensor t.val, admitted.models_iff_global η ρ⟩

/-- Semantic applicability of the raw certificate, not an independent raw denotation. -/
theorem admitRawSource_reached
    (ha : admitRawSource raw specs inputs = .ok admitted)
    (result : ActualValidatedResult admitted) (c complete)
    (hr : result.result.outcome = .complete c complete) :
    ∃ snapshot memo,
      CertifiedRawSource raw specs inputs admitted snapshot memo ∧
      admitted.GlobalModels (r := RationalReference.registry) result.input
        ((elaborateSource admitted).finalStore c complete) ∧
      (∀ t : (elaborateSource admitted).Defined,
        RawTensorEntryFields raw memo admitted.source.context specs snapshot.resolved.decls
          (admitted.source.table.entry t.val) ∧
        ∀ p, (elaborateSource admitted).finalStore c complete ⟨t.val, p⟩ =
          admitted.globalFiber ((elaborateSource admitted).finalStore c complete) t.val p) ∧
      (∀ ρ, admitted.GlobalModels (r := RationalReference.registry) result.input ρ →
        ρ = (elaborateSource admitted).finalStore c complete) := by
  obtain ⟨snapshot, memo, hc⟩ := admitRawSource_certified ha
  exact ⟨snapshot, memo, hc, sourceResult_globalModel admitted result c complete hr,
    fun t => ⟨hc.correspondence.tensor t.val,
      sourceResult_globalEquations admitted result c complete hr t⟩,
    sourceResult_globalUnique admitted result c complete hr⟩

theorem admitRawSource_reached_denotation
    (ha : admitRawSource raw specs inputs = .ok admitted)
    (result : ActualValidatedResult admitted) (c complete)
    (hr : result.result.outcome = .complete c complete)
    (t : {t // (elaborateSource admitted).output t = true})
    (p : Coord (admitted.source.table.declarations.signature t.val).axes) :
    ∃ snapshot memo,
      CertifiedRawSource raw specs inputs admitted snapshot memo ∧
      RawTensorEntryFields raw memo admitted.source.context specs snapshot.resolved.decls
        (admitted.source.table.entry t.val) ∧
      (elaborateSource admitted).denotation RationalReference.ops result.input
        ((elaborateSource admitted).successful_admInput RationalReference.ops result.input c
          (Program.Executor.result_success _ _ result.input result.result c complete hr)) t p =
        admitted.globalFiber ((elaborateSource admitted).finalStore c complete) t.val p := by
  obtain ⟨snapshot, memo, hc⟩ := admitRawSource_certified ha
  exact ⟨snapshot, memo, hc, hc.correspondence.tensor t.val,
    sourceResult_globalDenotation admitted result c complete hr t p⟩

end LeanNCD.Semantics.Source
