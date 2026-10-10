import LeanNCD.Semantics.Source.Provenance
import LeanNCD.Semantics.Source.ProgramCorrespondence

namespace LeanNCD.Semantics.Source

theorem mapUID_axis_metadata (f : UData → UData) (a : AxisSpec) :
    (AxisSpec.mapUID f a).name = a.name ∧ (AxisSpec.mapUID f a).kind = a.kind := by
  exact ⟨rfl, rfl⟩

private abbrev leaves {α : Type}
    (traverse : (AxisSpec → ConstL (List AxisSpec) AxisSpec) →
      α → ConstL (List AxisSpec) α) (x : α) : List AxisSpec :=
  (traverse (fun a => ⟨[a]⟩) x).run

private abbrev Covered (raw : TLProgram) (xs : List AxisSpec) : Prop :=
  ∀ a ∈ xs, a ∈ raw.axisSpecs

structure RawAxisFields (raw : TLProgram) (memo : Std.HashMap String UID)
    (a : AxisSpec) (uid : UID) : Prop where
  occurs : a ∈ raw.axisSpecs
  name_mem : a.name ∈ raw.axisNames
  lookup : memo[a.name]? = some uid
  mapped : a.mapUID (sourceUIDRelabel memo) = { a with uid := uid }

private theorem rawAxis_fields {raw : TLProgram} {memo : Std.HashMap String UID}
    (hc : ∀ name ∈ raw.axisNames, ∃ uid, memo[name]? = some uid)
    {a : AxisSpec} (ha : a ∈ raw.axisSpecs) :
    RawAxisFields raw memo a (a.mapUID (sourceUIDRelabel memo)).uid := by
  obtain ⟨uid, hu⟩ := hc a.name (raw.axisSpec_name_mem a ha)
  have hm := a.mapUID_sourceUIDRelabel memo uid hu
  refine ⟨ha, raw.axisSpec_name_mem a ha, ?_, ?_⟩
  · simpa [hm] using hu
  · simp [hm]

private theorem decl_covered {raw : TLProgram} {d : Decl} (hd : d ∈ raw.decls) :
    Covered raw (leaves Decl.traverseAxes d) := by
  intro a ha
  change a ∈ (Traversable.traverse (Decl.traverseAxes (f := ConstL (List AxisSpec))
    (fun a => ⟨[a]⟩)) raw.decls).run ++
    (Traversable.traverse (Stmt.traverseAxes (f := ConstL (List AxisSpec))
    (fun a => ⟨[a]⟩)) raw.stmts).run
  rw [traverseAxes_list_collect, traverseAxes_list_collect]
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, hd, ha⟩)

private theorem stmt_covered {raw : TLProgram} {s : Stmt} (hs : s ∈ raw.stmts) :
    Covered raw (leaves Stmt.traverseAxes s) := by
  intro a ha
  change a ∈ (Traversable.traverse (Decl.traverseAxes (f := ConstL (List AxisSpec))
    (fun a => ⟨[a]⟩)) raw.decls).run ++
    (Traversable.traverse (Stmt.traverseAxes (f := ConstL (List AxisSpec))
    (fun a => ⟨[a]⟩)) raw.stmts).run
  rw [traverseAxes_list_collect, traverseAxes_list_collect]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, ha⟩)

private theorem forall2_with_mem {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) :
    List.Forall₂ (fun x y => x ∈ xs ∧ R x y) xs ys :=
  (List.forall₂_and_left xs ys).mpr ⟨fun _ hx => hx, h⟩

private theorem zipIdx_member {α : Type} {xs : List α} {x : α} {i : Nat}
    (h : (x, i) ∈ xs.zipIdx) : x ∈ xs := by
  have hm := List.mem_map_of_mem (f := Prod.fst) h
  simpa only [List.zipIdx_map_fst] using hm

private theorem selection_unmap {α β γ : Type} {R : γ → Option β → Prop}
    (f : α → γ) {xs : List α} {ys : List β}
    (h : OrderedSelection R (xs.map f) ys) :
    OrderedSelection (fun x => R (f x)) xs ys := by
  induction xs generalizing ys with
  | nil => cases h; exact .nil
  | cons x xs ih =>
    cases h with
    | skip hr ht => exact .skip hr (ih ht)
    | emit hr ht => exact .emit hr (ih ht)

private theorem selection_imp_mem {α β : Type} {R S : α → Option β → Prop}
    {xs : List α} {ys : List β} (h : OrderedSelection R xs ys) :
    (∀ x ∈ xs, ∀ b, R x b → S x b) → OrderedSelection S xs ys := by
  induction h with
  | nil => intro _; exact .nil
  | skip hr ht ih =>
    intro f
    exact .skip (f _ (List.mem_cons_self ..) _ hr)
      (ih (fun x hx b hb => f x (List.mem_cons_of_mem _ hx) b hb))
  | emit hr ht ih =>
    intro f
    exact .emit (f _ (List.mem_cons_self ..) _ hr)
      (ih (fun x hx b hb => f x (List.mem_cons_of_mem _ hx) b hb))

def RawDeclaredAxisSlots (raw : TLProgram) (memo : Std.HashMap String UID)
    (c : Context) (slots : List AxisSpec) (axes : Shape) : Prop :=
  List.Forall₂ (fun a b => RawAxisFields raw memo a b.uid ∧ b ∈ c.axes) slots axes

def RawPinnedAxisDeclaration (raw : TLProgram) (memo : Std.HashMap String UID)
    (d : Decl) (axis : Option Axis) : Prop :=
  match d with
  | .axis a size => ∃ n uid, size = some n ∧
      RawAxisFields raw memo a uid ∧ axis = some ⟨uid, n⟩
  | .iter .. => False
  | .tensor .. | .typedTensor .. | .predicate .. | .linear .. | .typedLinear .. =>
      axis = none

def RawTensorDeclarationSelection (raw : TLProgram) (memo : Std.HashMap String UID)
    (c : Context) (specs : List TensorSpec) (pair : Decl × Nat)
    (entry : Option TensorEntry) : Prop :=
  match entry with
  | none => ∃ a size, pair.1 = .axis a size
  | some e =>
    e.declaration = pair.2 ∧
    ∃ slots, SupportedTensorDeclaration pair.1 e.name e.elementType slots ∧
      SupportedTensorDeclaration (pair.1.mapUID (sourceUIDRelabel memo))
        e.name e.elementType (slots.map (AxisSpec.mapUID (sourceUIDRelabel memo))) ∧
      RawDeclaredAxisSlots raw memo c slots e.axes ∧
      ∃ spec, specs.find? (fun s => s.declaration == pair.2) = some spec ∧
        e.role = spec.role ∧ e.axes.map Axis.extent = spec.shape

private theorem supported_unmap (f : UData → UData) (d : Decl)
    (name : String) (ty : TensorElementType) (slots : List AxisSpec)
    (h : SupportedTensorDeclaration (d.mapUID f) name ty slots) :
    ∃ original, SupportedTensorDeclaration d name ty original ∧
      slots = original.map (AxisSpec.mapUID f) := by
  cases d <;>
    simp [SupportedTensorDeclaration, Decl.mapUID, Decl.traverseAxes,
      traverseAxes_list_id, Functor.map] at h ⊢
  all_goals aesop

private theorem supported_covered {raw : TLProgram} {d : Decl}
    {name : String} {ty : TensorElementType} {slots : List AxisSpec}
    (hc : Covered raw (leaves Decl.traverseAxes d))
    (h : SupportedTensorDeclaration d name ty slots) : Covered raw slots := by
  cases d <;> simp only [SupportedTensorDeclaration] at h
  all_goals
    first | rw [h.2.2] | rw [h.2.2.2]
    intro a ha
    apply hc a
    change a ∈ (Traversable.traverse (fun a : AxisSpec => (⟨[a]⟩ :
      ConstL (List AxisSpec) AxisSpec)) _).run
    simpa [traverseAxes_list_collect] using ha

private theorem rawDeclaredSlots_fields {raw : TLProgram} {memo : Std.HashMap String UID}
    (hc : ∀ name ∈ raw.axisNames, ∃ uid, memo[name]? = some uid)
    {c : Context} {slots : List AxisSpec} {axes : Shape}
    (ha : Covered raw slots)
    (h : DeclaredAxisSlots c (slots.map (AxisSpec.mapUID (sourceUIDRelabel memo))) axes) :
    RawDeclaredAxisSlots raw memo c slots axes := by
  have hf := List.forall₂_map_left_iff.mp h
  apply (forall2_with_mem hf).imp
  intro a b hab
  obtain ⟨ham, hu, hb⟩ := hab
  exact ⟨hu ▸ rawAxis_fields hc (ha a ham), hb⟩

private theorem rawPinned_fields {raw : TLProgram} {memo : Std.HashMap String UID}
    (hc : ∀ name ∈ raw.axisNames, ∃ uid, memo[name]? = some uid)
    {d : Decl} {axis : Option Axis} (ha : Covered raw (leaves Decl.traverseAxes d))
    (h : PinnedAxisDeclaration (d.mapUID (sourceUIDRelabel memo)) axis) :
    RawPinnedAxisDeclaration raw memo d axis := by
  cases d with
  | axis a size =>
    change ∃ n, size = some n ∧
      axis = some ⟨(a.mapUID (sourceUIDRelabel memo)).uid, n⟩ at h
    obtain ⟨n, hn, he⟩ := h
    exact ⟨n, _, hn, rawAxis_fields hc (ha a (List.mem_singleton_self a)), he⟩
  | iter _ _ =>
    simp [PinnedAxisDeclaration, Decl.mapUID, Decl.traverseAxes] at h
  | _ =>
    simpa [PinnedAxisDeclaration, RawPinnedAxisDeclaration, Decl.mapUID, Decl.traverseAxes,
      Functor.map, traverseAxes_list_id] using h

private theorem rawTensorSelection_fields {raw : TLProgram} {memo : Std.HashMap String UID}
    (hc : ∀ name ∈ raw.axisNames, ∃ uid, memo[name]? = some uid)
    {c : Context} {specs : List TensorSpec} {pair : Decl × Nat} {entry : Option TensorEntry}
    (ha : Covered raw (leaves Decl.traverseAxes pair.1))
    (h : TensorDeclarationSelection c specs
      (pair.1.mapUID (sourceUIDRelabel memo), pair.2) entry) :
    RawTensorDeclarationSelection raw memo c specs pair entry := by
  cases entry with
  | none =>
    obtain ⟨a, size, he⟩ := h
    cases hd : pair.1 <;>
      simp [Decl.mapUID, Decl.traverseAxes, traverseAxes_list_id,
        Functor.map, hd] at he
    exact ⟨_, _, hd⟩
  | some e =>
    obtain ⟨hi, mappedSlots, hs, hslots, spec, hf, hr, hshape⟩ := h
    obtain ⟨slots, hraw, hm⟩ := supported_unmap _ _ _ _ _ hs
    subst mappedSlots
    exact ⟨hi, slots, hraw, hs,
      rawDeclaredSlots_fields hc (supported_covered ha hraw) hslots,
      spec, hf, hr, hshape⟩

def RawReadSlots (raw : TLProgram) (memo : Std.HashMap String UID)
    (es : List IdxExpr) (ids : List UID) : Prop :=
  List.Forall₂ (fun (e, _) uid => ∃ a, e = .axis a ∧ RawAxisFields raw memo a uid)
    es.zipIdx ids

def RawOutputSlots (raw : TLProgram) (memo : Std.HashMap String UID)
    (slots : List LHSSlot) (ids : List UID) : Prop :=
  List.Forall₂ (fun (s, _) uid => ∃ a, s = .free a ∧ RawAxisFields raw memo a uid)
    slots.zipIdx ids

private theorem readSlot_unmap (f : UData → UData) (e : IdxExpr) (b : AxisSpec)
    (h : e.mapUID f = .axis b) : ∃ a, e = .axis a ∧ b = a.mapUID f := by
  cases e <;>
    simp [IdxExpr.mapUID, IdxExpr.traverseAxes, traverseAxes_list_id,
      Functor.map, pure] at h ⊢
  exact h.symm

private theorem outputSlot_unmap (f : UData → UData) (s : LHSSlot) (b : AxisSpec)
    (h : s.mapUID f = .free b) : ∃ a, s = .free a ∧ b = a.mapUID f := by
  cases s <;>
    simp [LHSSlot.mapUID, LHSSlot.traverseAxes, Functor.map] at h ⊢
  exact h.symm

private theorem rawReadSlots_fields {raw : TLProgram} {memo : Std.HashMap String UID}
    (hc : ∀ name ∈ raw.axisNames, ∃ uid, memo[name]? = some uid)
    {es : List IdxExpr} {ids : List UID}
    (ha : ∀ e ∈ es, Covered raw (leaves IdxExpr.traverseAxes e))
    (h : BareReadSlots (es.map (IdxExpr.mapUID (sourceUIDRelabel memo))) ids) :
    RawReadSlots raw memo es ids := by
  unfold BareReadSlots at h
  rw [List.zipIdx_map, List.forall₂_map_left_iff] at h
  apply (forall2_with_mem h).imp
  rintro ⟨e, i⟩ uid ⟨he, b, hb, hu⟩
  obtain ⟨a, rfl, rfl⟩ := readSlot_unmap _ _ _ hb
  refine ⟨a, rfl, hu ▸ rawAxis_fields hc (ha (.axis a) ?_ a ?_)⟩
  · exact zipIdx_member he
  · exact List.mem_singleton_self _

private theorem rawOutputSlots_fields {raw : TLProgram} {memo : Std.HashMap String UID}
    (hc : ∀ name ∈ raw.axisNames, ∃ uid, memo[name]? = some uid)
    {slots : List LHSSlot} {ids : List UID}
    (ha : ∀ s ∈ slots, Covered raw (leaves LHSSlot.traverseAxes s))
    (h : BareOutputSlots (slots.map (LHSSlot.mapUID (sourceUIDRelabel memo))) ids) :
    RawOutputSlots raw memo slots ids := by
  unfold BareOutputSlots at h
  rw [List.zipIdx_map, List.forall₂_map_left_iff] at h
  apply (forall2_with_mem h).imp
  rintro ⟨s, i⟩ uid ⟨hs, b, hb, hu⟩
  obtain ⟨a, rfl, rfl⟩ := outputSlot_unmap _ _ _ hb
  refine ⟨a, rfl, hu ▸ rawAxis_fields hc (ha (.free a) ?_ a ?_)⟩
  · exact zipIdx_member hs
  · exact List.mem_singleton_self _

def RawFactorFields (raw : TLProgram) (memo : Std.HashMap String UID)
    (source : AdaptedSource) (origin : SourceOrigin) (factor : Factor)
    (read : RawRead source.table.declarations) : Prop :=
  ∃ name es, factor = .read name es ∧
    source.table.find name = some read.tensor ∧
    (source.table.entry read.tensor).name = name ∧
    RawReadSlots raw memo es read.indices ∧
    read.origin = { origin with
      declaration := some (source.table.entry read.tensor).declaration }

def RawCheckedFactorFields (raw : TLProgram) (memo : Std.HashMap String UID)
    (source : AdaptedSource) (origin : SourceOrigin) (factor : Factor)
    (read : CheckedRead c source.table.declarations) : Prop :=
  ∃ name es, factor = .read name es ∧
    source.table.find name = some read.read.tensor ∧
    (source.table.entry read.read.tensor).name = name ∧
    RawReadSlots raw memo es read.indices ∧
    read.origin = { origin with
      declaration := some (source.table.entry read.read.tensor).declaration }

def RawTermFields (raw : TLProgram) (memo : Std.HashMap String UID)
    (source : AdaptedSource) (origin : SourceOrigin) (ast : ProdTerm)
    (term : Term source.context out source.table.declarations) : Prop :=
  term.origin = origin ∧
    List.Forall₂ (fun (f, j) read =>
      RawCheckedFactorFields raw memo source { origin with factor := some j } f read)
      ast.factors.zipIdx term.sourceReads

def RawStatementFields (raw : TLProgram) (memo : Std.HashMap String UID)
    (source : AdaptedSource) (i : Nat) (ast : Stmt)
    (statement : AdmittedStatement source) : Prop :=
  ∃ name slots rhs, ast = .assign name slots rhs ∧
    statement.original = i ∧ rhs.agg = .sum ∧ rhs.nonlin = .identity ∧
    source.table.find name = some statement.output.tensor ∧
    (source.table.entry statement.output.tensor).name = name ∧
    RawOutputSlots raw memo slots statement.output.indices ∧
    statement.output.origin = {
      side := .output, statement := some i,
      declaration := some (source.table.entry statement.output.tensor).declaration } ∧
    List.Forall₂ (fun (t, j) term => RawTermFields raw memo source {
      side := .read, statement := some i, term := some j } t term)
      rhs.body.terms.zipIdx statement.terms

private theorem rawFactor_fields {raw : TLProgram} {memo : Std.HashMap String UID}
    (hc : ∀ name ∈ raw.axisNames, ∃ uid, memo[name]? = some uid)
    {source : AdaptedSource} {origin : SourceOrigin} {f : Factor}
    {read : RawRead source.table.declarations}
    (ha : Covered raw (leaves Factor.traverseAxes f))
    (h : FactorFields source origin (f.mapUID (sourceUIDRelabel memo)) read) :
    RawFactorFields raw memo source origin f read := by
  obtain ⟨name, es, he, ht, hn, hi, ho⟩ := h
  cases f with
  | iverson _ => cases he
  | unaryFn _ _ _ => cases he
  | read nm original =>
    change Factor.read nm (Traversable.traverse
      (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID (sourceUIDRelabel memo)))
      original) = .read name es at he
    rw [traverseAxes_list_id] at he
    cases he
    refine ⟨name, original, rfl, ht, hn, rawReadSlots_fields hc ?_ hi, ho⟩
    intro e he a hae
    apply ha a
    change a ∈ (Traversable.traverse (IdxExpr.traverseAxes
      (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) original).run
    rw [traverseAxes_list_collect]
    exact List.mem_flatMap.mpr ⟨e, he, hae⟩

private theorem rawFactors_checked {raw : TLProgram} {memo : Std.HashMap String UID}
    {source : AdaptedSource} {origin : SourceOrigin} {fs : List (Factor × Nat)}
    {reads : List (RawRead source.table.declarations)}
    {checked : List (CheckedRead c source.table.declarations)}
    (hf : List.Forall₂ (fun (f, j) r =>
      RawFactorFields raw memo source { origin with factor := some j } f r) fs reads)
    (hc : List.Forall₂ (fun r c => c.read.tensor = r.tensor ∧
      c.indices = r.indices ∧ c.origin = r.origin) reads checked) :
    List.Forall₂ (fun (f, j) r =>
      RawCheckedFactorFields raw memo source { origin with factor := some j } f r)
      fs checked := by
  induction hf generalizing checked with
  | nil => cases hc; exact .nil
  | cons h ht ih =>
    cases hc with
    | cons he hc =>
      obtain ⟨name, es, hfactor, hfind, hname, hslots, horigin⟩ := h
      exact .cons ⟨name, es, hfactor, he.1 ▸ hfind, he.1 ▸ hname,
        he.2.1 ▸ hslots, by rw [he.1, he.2.2]; exact horigin⟩ (ih hc)

private theorem rawTerm_fields {raw : TLProgram} {memo : Std.HashMap String UID}
    (hc : ∀ name ∈ raw.axisNames, ∃ uid, memo[name]? = some uid)
    {source : AdaptedSource} {origin : SourceOrigin} {ast : ProdTerm}
    {term : Term source.context out source.table.declarations}
    (ha : Covered raw (leaves ProdTerm.traverseAxes ast))
    (h : TermFields source origin (ast.mapUID (sourceUIDRelabel memo)) term) :
    RawTermFields raw memo source origin ast term := by
  obtain ⟨ho, reads, hf, hchecked⟩ := h
  rw [ProdTerm.mapUID_factors, List.zipIdx_map, List.forall₂_map_left_iff] at hf
  refine ⟨ho, rawFactors_checked ?_ hchecked⟩
  apply (forall2_with_mem hf).imp
  rintro ⟨f, j⟩ read ⟨hfmem, hfactor⟩
  apply rawFactor_fields hc (h := hfactor)
  intro a hleaf
  apply ha a
  change a ∈ (Traversable.traverse (Factor.traverseAxes
    (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ast.factors).run
  rw [traverseAxes_list_collect]
  exact List.mem_flatMap.mpr ⟨f, zipIdx_member hfmem, hleaf⟩

private theorem nonlin_unmap_identity (f : UData → UData) (n : Nonlin)
    (h : n.mapUID f = .identity) : n = .identity := by
  cases n <;> simp [Nonlin.mapUID, Nonlin.traverseAxes,
    Functor.map, pure] at h ⊢

private theorem rawStatement_fields {raw : TLProgram} {memo : Std.HashMap String UID}
    (hc : ∀ name ∈ raw.axisNames, ∃ uid, memo[name]? = some uid)
    {source : AdaptedSource} {i : Nat} {ast : Stmt}
    {statement : AdmittedStatement source}
    (ha : Covered raw (leaves Stmt.traverseAxes ast))
    (h : StatementFields source i (ast.mapUID (sourceUIDRelabel memo)) statement) :
    RawStatementFields raw memo source i ast statement := by
  obtain ⟨name, slots, rhs, he, hi, hagg, hnonlin, ht, hn, hs, ho, hterms⟩ := h
  cases ast with
  | scatter _ _ _ _ => cases he
  | recurMorphism _ _ _ => cases he
  | assign nm original r =>
    change Stmt.assign nm
      (Traversable.traverse (LHSSlot.traverseAxes
        (f := Id) (AxisSpec.mapUID (sourceUIDRelabel memo))) original)
      (r.mapUID (sourceUIDRelabel memo)) = .assign name slots rhs at he
    rw [traverseAxes_list_id] at he
    cases he
    have hnl : r.nonlin = .identity := nonlin_unmap_identity _ _ hnonlin
    have hslots : ∀ s ∈ original, Covered raw (leaves LHSSlot.traverseAxes s) := by
      intro s hs a ha'
      apply ha a
      change a ∈ (Traversable.traverse (LHSSlot.traverseAxes
        (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) original).run ++
        leaves RHSExpr.traverseAxesWithMask r
      rw [traverseAxes_list_collect]
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, ha'⟩)
    refine ⟨name, original, r, rfl, hi, hagg, hnl, ht, hn,
      rawOutputSlots_fields hc hslots hs, ho, ?_⟩
    rw [RHSExpr.mapUID_terms, List.zipIdx_map, List.forall₂_map_left_iff] at hterms
    apply (forall2_with_mem hterms).imp
    rintro ⟨t, j⟩ term ⟨htmem, hterm⟩
    apply rawTerm_fields hc (h := hterm)
    intro a hleaf
    apply ha a
    change a ∈ leaves (fun g s => Traversable.traverse (LHSSlot.traverseAxes g) s)
      original ++ (leaves SumExpr.traverseAxes r.body ++ leaves Nonlin.traverseAxes r.nonlin)
    apply List.mem_append_right
    apply List.mem_append_left
    change a ∈ (Traversable.traverse (ProdTerm.traverseAxes
      (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) r.body.terms).run
    rw [traverseAxes_list_collect]
    exact List.mem_flatMap.mpr ⟨t, zipIdx_member htmem, hleaf⟩

structure RawCorrespondence (raw : TLProgram) (specs : List TensorSpec)
    (inputs : List InputBinding) (admitted : AdmittedSource)
    (snapshot : SourceSnapshot) (memo : Std.HashMap String UID) : Prop where
  resolved : resolveSource raw specs inputs = .ok snapshot
  admission : admitSource snapshot = .ok admitted
  covered : ∀ name ∈ raw.axisNames, ∃ uid, memo[name]? = some uid
  declarations : snapshot.resolved.decls = raw.decls.map (Decl.mapUID (sourceUIDRelabel memo))
  statements : snapshot.resolved.stmts = raw.stmts.map (Stmt.mapUID (sourceUIDRelabel memo))
  specs_eq : snapshot.specs = specs
  inputs_eq : snapshot.inputs = inputs
  axes : OrderedSelection (RawPinnedAxisDeclaration raw memo)
    raw.decls admitted.source.context.axes
  table : OrderedSelection (RawTensorDeclarationSelection raw memo admitted.source.context specs)
    raw.decls.zipIdx admitted.source.table.entries
  statement_fields : List.Forall₂ (fun (s, i) a =>
    RawStatementFields raw memo admitted.source i s a) raw.stmts.zipIdx admitted.statements

def RawAdmissionFields (raw : TLProgram) (specs : List TensorSpec)
    (inputs : List InputBinding) (admitted : AdmittedSource) : Prop :=
  ∃ snapshot memo, RawCorrespondence raw specs inputs admitted snapshot memo

private theorem admitSource_adapted {snapshot : SourceSnapshot} {admitted : AdmittedSource}
    (h : admitSource snapshot = .ok admitted) :
    adaptSource snapshot = .ok admitted.source := by
  unfold admitSource at h
  simp only [bind, pure, Except.bind, Except.pure] at h
  cases ha : adaptSource snapshot with
  | error e => simp [ha] at h
  | ok source =>
    cases hs : source.statements.mapM (fun (i, s) => admitStatement source i s) with
    | error e => simp [ha, hs] at h
    | ok statements =>
      simp only [ha, hs, Except.ok.injEq] at h
      subst admitted
      rfl

theorem admitRawSource_fields (raw : TLProgram) (specs : List TensorSpec)
    (inputs : List InputBinding) (admitted : AdmittedSource)
    (h : admitRawSource raw specs inputs = .ok admitted) :
    RawAdmissionFields raw specs inputs admitted := by
  unfold admitRawSource at h
  simp only [bind, Except.bind] at h
  cases hr : resolveSource raw specs inputs with
  | error e => simp [hr] at h
  | ok snapshot =>
    simp only [hr] at h
    obtain ⟨memo, hc, hd, hs, hp, hi⟩ :=
      resolveSource_mapUID_covered raw specs inputs snapshot hr
    rw [(TLProgram.mapUID_lists _ raw).1] at hd
    rw [(TLProgram.mapUID_lists _ raw).2] at hs
    obtain ⟨haxes, htable⟩ := adaptSource_declarations snapshot admitted.source
      (admitSource_adapted h)
    rw [hd] at haxes
    rw [hd, hp] at htable
    obtain ⟨hst, hfields⟩ := admitSource_fields snapshot admitted h
    rw [hst, hs, List.zipIdx_map, List.map_map, List.forall₂_map_left_iff] at hfields
    refine ⟨snapshot, memo, hr, h, hc, hd, hs, hp, hi, ?_, ?_, ?_⟩
    · have ha := selection_unmap (Decl.mapUID (sourceUIDRelabel memo)) haxes
      exact selection_imp_mem ha
        (fun d hd axis hpin => rawPinned_fields hc (decl_covered hd) hpin)
    · unfold TableDeclarations at htable
      rw [List.zipIdx_map] at htable
      have ht := selection_unmap (Prod.map (Decl.mapUID (sourceUIDRelabel memo)) id) htable
      exact selection_imp_mem ht (fun pair hpair entry hsel =>
        rawTensorSelection_fields hc (decl_covered (zipIdx_member hpair)) hsel)
    · apply (forall2_with_mem hfields).imp
      rintro ⟨s, i⟩ a ⟨hmem, hfield⟩
      exact rawStatement_fields hc (stmt_covered (zipIdx_member hmem)) hfield

def RawTensorEntryFields (raw : TLProgram) (memo : Std.HashMap String UID)
    (c : Context) (specs : List TensorSpec) (resolvedDecls : List Decl)
    (entry : TensorEntry) : Prop :=
  ∃ d slots spec,
    raw.decls[entry.declaration]? = some d ∧
    resolvedDecls[entry.declaration]? = some (d.mapUID (sourceUIDRelabel memo)) ∧
    SupportedTensorDeclaration d entry.name entry.elementType slots ∧
    SupportedTensorDeclaration (d.mapUID (sourceUIDRelabel memo))
      entry.name entry.elementType (slots.map (AxisSpec.mapUID (sourceUIDRelabel memo))) ∧
    RawDeclaredAxisSlots raw memo c slots entry.axes ∧
    specs.find? (fun s => s.declaration == entry.declaration) = some spec ∧
    spec.declaration = entry.declaration ∧ entry.role = spec.role ∧
    entry.axes.map Axis.extent = spec.shape

theorem RawCorrespondence.tensor {raw : TLProgram} {specs : List TensorSpec}
    {inputs : List InputBinding} {admitted : AdmittedSource}
    {snapshot : SourceSnapshot} {memo : Std.HashMap String UID}
    (h : RawCorrespondence raw specs inputs admitted snapshot memo)
    (t : admitted.source.table.declarations.Tensor) :
    RawTensorEntryFields raw memo admitted.source.context specs snapshot.resolved.decls
      (admitted.source.table.entry t) := by
  obtain ⟨⟨d, i⟩, hd, hi, slots, hs, hm, ha, spec, hf, hr, hshape⟩ :=
    h.table.member (List.get_mem admitted.source.table.entries t)
  change (admitted.source.table.entry t).declaration = i at hi
  have hlookup := List.mk_mem_zipIdx_iff_getElem?.mp hd
  have hraw : raw.decls[(admitted.source.table.entry t).declaration]? = some d := by
    simpa [hi] using hlookup
  refine ⟨d, slots, spec, hraw, ?_, hs, hm, ha, ?_, ?_, hr, hshape⟩
  · rw [h.declarations, List.getElem?_map, hraw]
    rfl
  · simpa [hi] using hf
  · simpa [hi] using List.find?_some hf

theorem RawCorrespondence.pinned {raw : TLProgram} {specs : List TensorSpec}
    {inputs : List InputBinding} {admitted : AdmittedSource}
    {snapshot : SourceSnapshot} {memo : Std.HashMap String UID}
    (h : RawCorrespondence raw specs inputs admitted snapshot memo)
    {b : Axis} (hb : b ∈ admitted.source.context.axes) :
    ∃ a, .axis a (some b.extent) ∈ raw.decls ∧ RawAxisFields raw memo a b.uid := by
  obtain ⟨d, hd, hp⟩ := h.axes.member hb
  cases d <;> simp only [RawPinnedAxisDeclaration, reduceCtorEq] at hp
  obtain ⟨n, uid, rfl, ha, he⟩ := hp
  cases he
  exact ⟨_, hd, ha⟩

theorem RawAxisFields.metadata {raw : TLProgram} {memo : Std.HashMap String UID}
    {a : AxisSpec} {uid : UID} (h : RawAxisFields raw memo a uid) :
    (a.mapUID (sourceUIDRelabel memo)).uid = uid ∧
    (a.mapUID (sourceUIDRelabel memo)).name = a.name ∧
    (a.mapUID (sourceUIDRelabel memo)).kind = a.kind := by
  rw [h.mapped]
  exact ⟨rfl, rfl, rfl⟩

theorem RawAxisFields.same_name {raw : TLProgram} {memo : Std.HashMap String UID}
    {a b : AxisSpec} {u v : UID} (ha : RawAxisFields raw memo a u)
    (hb : RawAxisFields raw memo b v) (hn : a.name = b.name) : u = v := by
  have he : some u = some v := ha.lookup.symm.trans (hn ▸ hb.lookup)
  exact Option.some.inj he

theorem RawDeclaredAxisSlots.slot {raw : TLProgram} {memo : Std.HashMap String UID}
    {c : Context} {slots : List AxisSpec} {axes : Shape}
    (h : RawDeclaredAxisSlots raw memo c slots axes) (j : Fin axes.length) :
    ∃ a, slots[j.val]? = some a ∧
      RawAxisFields raw memo a (axes.get j).uid ∧ (axes.get j) ∈ c.axes := by
  have hj : j.val < slots.length := by
    rw [h.length_eq]
    exact j.isLt
  exact ⟨slots[j.val], by simp [hj], h.get hj j.isLt⟩

private theorem forall2_indexed {α β : Type} {R : Nat → α → β → Prop}
    {xs : List α} {ys : List β}
    (h : List.Forall₂ (fun (x, i) y => R i x y) xs.zipIdx ys)
    (j : Fin ys.length) :
    ∃ x, xs[j.val]? = some x ∧ R j.val x (ys.get j) := by
  have hj : j.val < xs.length := by
    have hl : xs.length = ys.length := by simpa using h.length_eq
    rw [hl]
    exact j.isLt
  have hz : j.val < xs.zipIdx.length := by simpa using hj
  refine ⟨xs[j.val], by simp [hj], ?_⟩
  simpa only [List.get_eq_getElem, List.getElem_zipIdx, Nat.zero_add] using h.get hz j.isLt

theorem RawCorrespondence.statement {raw : TLProgram} {specs : List TensorSpec}
    {inputs : List InputBinding} {admitted : AdmittedSource}
    {snapshot : SourceSnapshot} {memo : Std.HashMap String UID}
    (h : RawCorrespondence raw specs inputs admitted snapshot memo)
    (j : Fin admitted.statements.length) :
    ∃ ast, raw.stmts[j.val]? = some ast ∧
      RawStatementFields raw memo admitted.source j.val ast (admitted.statements.get j) :=
  forall2_indexed h.statement_fields j

theorem RawTermFields.factor_count {raw : TLProgram} {memo : Std.HashMap String UID}
    {source : AdaptedSource} {origin : SourceOrigin} {ast : ProdTerm}
    {term : Term source.context out source.table.declarations}
    (h : RawTermFields raw memo source origin ast term) :
    ast.factors.length = term.sourceReads.length := by
  simpa using h.2.length_eq

theorem RawTermFields.factor {raw : TLProgram} {memo : Std.HashMap String UID}
    {source : AdaptedSource} {origin : SourceOrigin} {ast : ProdTerm}
    {term : Term source.context out source.table.declarations}
    (h : RawTermFields raw memo source origin ast term)
    (j : Fin term.sourceReads.length) :
    ∃ f, ast.factors[j.val]? = some f ∧
      RawCheckedFactorFields raw memo source { origin with factor := some j.val }
        f (term.sourceReads.get j) :=
  forall2_indexed (R := fun i f read =>
    RawCheckedFactorFields raw memo source { origin with factor := some i } f read) h.2 j

theorem RawStatementFields.term {raw : TLProgram} {memo : Std.HashMap String UID}
    {source : AdaptedSource} {i : Nat} {ast : Stmt}
    {statement : AdmittedStatement source}
    (h : RawStatementFields raw memo source i ast statement)
    (j : Fin statement.terms.length) :
    ∃ name slots rhs t, ast = .assign name slots rhs ∧
      rhs.body.terms[j.val]? = some t ∧
      RawTermFields raw memo source
        { side := .read, statement := some i, term := some j.val } t (statement.terms.get j) := by
  obtain ⟨name, slots, rhs, he, _, _, _, _, _, _, _, ht⟩ := h
  obtain ⟨t, hlookup, hterm⟩ := forall2_indexed
    (R := fun j t term => RawTermFields raw memo source
      { side := .read, statement := some i, term := some j } t term) ht j
  exact ⟨name, slots, rhs, t, he, hlookup, hterm⟩

theorem RawStatementFields.term_count {raw : TLProgram} {memo : Std.HashMap String UID}
    {source : AdaptedSource} {i : Nat} {ast : Stmt}
    {statement : AdmittedStatement source}
    (h : RawStatementFields raw memo source i ast statement) :
    ∃ name slots rhs, ast = .assign name slots rhs ∧
      rhs.body.terms.length = statement.terms.length := by
  obtain ⟨name, slots, rhs, he, _, _, _, _, _, _, _, ht⟩ := h
  exact ⟨name, slots, rhs, he, by simpa using ht.length_eq⟩

theorem RawCheckedFactorFields.slots {raw : TLProgram} {memo : Std.HashMap String UID}
    {source : AdaptedSource} {origin : SourceOrigin} {name : String} {es : List IdxExpr}
    {read : CheckedRead c source.table.declarations}
    (h : RawCheckedFactorFields raw memo source origin (.read name es) read) :
    RawReadSlots raw memo es read.read.slots.uids := by
  obtain ⟨n, original, he, _, _, hs, _⟩ := h
  cases he
  rw [read.linked]
  exact hs

theorem RawStatementFields.output_slots {raw : TLProgram} {memo : Std.HashMap String UID}
    {source : AdaptedSource} {i : Nat} {name : String} {slots : List LHSSlot} {rhs : RHSExpr}
    {statement : AdmittedStatement source}
    (h : RawStatementFields raw memo source i (.assign name slots rhs) statement) :
    RawOutputSlots raw memo slots statement.output.slots.uids ∧
    RawOutputSlots raw memo slots statement.output.sourceSlots.uids := by
  obtain ⟨n, original, r, he, _, _, _, _, _, hs, _, _⟩ := h
  cases he
  rw [statement.output.linked, statement.output.source_linked]
  exact ⟨hs, hs⟩

theorem RawReadSlots.slot {raw : TLProgram} {memo : Std.HashMap String UID}
    {es : List IdxExpr} {ids : List UID} (h : RawReadSlots raw memo es ids)
    (j : Fin ids.length) :
    ∃ a, es[j.val]? = some (.axis a) ∧ RawAxisFields raw memo a (ids.get j) := by
  obtain ⟨e, he, a, rfl, ha⟩ := forall2_indexed
    (R := fun _ (e : IdxExpr) (uid : UID) =>
      ∃ a, e = .axis a ∧ RawAxisFields raw memo a uid) h j
  exact ⟨a, he, ha⟩

theorem RawOutputSlots.slot {raw : TLProgram} {memo : Std.HashMap String UID}
    {slots : List LHSSlot} {ids : List UID} (h : RawOutputSlots raw memo slots ids)
    (j : Fin ids.length) :
    ∃ a, slots[j.val]? = some (.free a) ∧ RawAxisFields raw memo a (ids.get j) := by
  obtain ⟨s, hs, a, rfl, ha⟩ := forall2_indexed
    (R := fun _ (s : LHSSlot) (uid : UID) =>
      ∃ a, s = .free a ∧ RawAxisFields raw memo a uid) h j
  exact ⟨a, hs, ha⟩

theorem RawCorrespondence.read {raw : TLProgram} {specs : List TensorSpec}
    {inputs : List InputBinding} {admitted : AdmittedSource}
    {snapshot : SourceSnapshot} {memo : Std.HashMap String UID}
    (h : RawCorrespondence raw specs inputs admitted snapshot memo)
    {origin : SourceOrigin} {factor : Factor}
    {read : CheckedRead admitted.source.context admitted.source.table.declarations}
    (hr : RawCheckedFactorFields raw memo admitted.source origin factor read) :
    ∃ name es, factor = .read name es ∧
      RawTensorEntryFields raw memo admitted.source.context specs snapshot.resolved.decls
        (admitted.source.table.entry read.read.tensor) ∧
      (admitted.source.table.entry read.read.tensor).name = name ∧
      RawReadSlots raw memo es read.read.slots.uids ∧
      read.origin = { origin with
        declaration := some (admitted.source.table.entry read.read.tensor).declaration } := by
  obtain ⟨name, es, he, _, hn, hs, ho⟩ := hr
  exact ⟨name, es, he, h.tensor read.read.tensor, hn, read.linked ▸ hs, ho⟩

theorem RawCorrespondence.output {raw : TLProgram} {specs : List TensorSpec}
    {inputs : List InputBinding} {admitted : AdmittedSource}
    {snapshot : SourceSnapshot} {memo : Std.HashMap String UID}
    (h : RawCorrespondence raw specs inputs admitted snapshot memo)
    {i : Nat} {ast : Stmt} {statement : AdmittedStatement admitted.source}
    (hs : RawStatementFields raw memo admitted.source i ast statement) :
    ∃ name slots rhs, ast = .assign name slots rhs ∧ statement.original = i ∧
      RawTensorEntryFields raw memo admitted.source.context specs snapshot.resolved.decls
        (admitted.source.table.entry statement.output.tensor) ∧
      (admitted.source.table.entry statement.output.tensor).name = name ∧
      RawOutputSlots raw memo slots statement.output.slots.uids ∧
      RawOutputSlots raw memo slots statement.output.sourceSlots.uids ∧
      statement.output.origin = {
        side := .output, statement := some i,
        declaration := some (admitted.source.table.entry statement.output.tensor).declaration } := by
  obtain ⟨name, slots, rhs, he, hi, _, _, _, hn, hslots, ho, _⟩ := hs
  exact ⟨name, slots, rhs, he, hi, h.tensor statement.output.tensor, hn,
    statement.output.linked ▸ hslots, statement.output.source_linked ▸ hslots, ho⟩

theorem TermFields.factor_count {source : AdaptedSource} {origin : SourceOrigin}
    {ast : ProdTerm} {term : Term source.context out source.table.declarations}
    (h : TermFields source origin ast term) :
    ast.factors.length = term.sourceReads.length := by
  obtain ⟨_, raw, hf, hc⟩ := h
  simpa using hf.length_eq.trans hc.length_eq

theorem StatementFields.term_count {source : AdaptedSource} {i : Nat} {ast : Stmt}
    {statement : AdmittedStatement source} (h : StatementFields source i ast statement) :
    ∃ name slots rhs, ast = .assign name slots rhs ∧
      rhs.body.terms.length = statement.terms.length := by
  obtain ⟨name, slots, rhs, he, _, _, _, _, _, _, _, ht⟩ := h
  exact ⟨name, slots, rhs, he, by simpa using ht.length_eq⟩

#print axioms LeanNCD.assignUIDs_mapUID
#print axioms resolveSource_mapUID
#print axioms mapM_success_forall2
#print axioms admitRead_fields
#print axioms admitTerm_reads
#print axioms TensorTable.find_name
#print axioms astRead_fields
#print axioms admitOutput_fields
#print axioms admitStatement_fields
#print axioms adaptSource_statements
#print axioms admitSource_fields
#print axioms mapUID_axis_metadata
#print axioms admitRawSource_fields
#print axioms TermFields.factor_count
#print axioms StatementFields.term_count

end LeanNCD.Semantics.Source
