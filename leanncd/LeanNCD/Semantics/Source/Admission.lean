import LeanNCD.Semantics.Source.Adapter
import LeanNCD.Semantics.Source.Lowering

namespace LeanNCD.Semantics.Source

def Slots.uids : Slots ctx sh → List UID
  | .nil => []
  | .cons r rest => r.uid :: rest.uids

def Slots.keys (c : Context) : Slots c.axes sh → List c.Key
  | .nil => []
  | .cons r rest => r.key c :: rest.keys c

theorem Slots.keys_uids (c : Context) (slots : Slots c.axes sh) :
    (slots.keys c).map Subtype.val = slots.uids := by
  induction slots with
  | nil => rfl
  | cons r rest ih => simp [Slots.keys, Slots.uids, Ref.key_uid, ih]

theorem Slots.support (c : Context) (slots : Slots c.axes sh) :
    slots.uids ⊆ c.axes.map Axis.uid := by
  rw [← slots.keys_uids c]
  intro uid h
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp h
  exact u.property

theorem resolveRef_uid (sh : Shape) (uid : UID) (n : Nat) (r : Ref sh n)
    (h : resolveRef sh uid n = .ok r) : r.uid = uid := by
  induction sh with
  | nil => simp [resolveRef] at h
  | cons a sh ih =>
    unfold resolveRef at h
    split at h
    · rename_i hu
      split at h
      · rename_i hd
        subst n
        simp only [Except.ok.injEq] at h
        subst r
        exact hu
      · simp at h
    · cases hr : resolveRef sh uid n with
      | error e => simp [hr, Except.map] at h
      | ok s =>
        simp [hr, Except.map] at h
        subst r
        exact ih s hr

private def liftDiagnostic (stage : SourceStage) (origin : SourceOrigin) :
    Diagnostic → SourceDiagnostic
  | .unbound uid => sourceError stage origin (.unbound uid)
  | .domain uid expected actual => sourceError stage origin (.domain uid expected actual)
  | .rank expected actual => sourceError stage origin (.rank expected actual)
  | e => sourceError stage origin (.context e)

/-- Check common slots left to right before reporting total rank at the first unmatched slot. -/
def resolveSourceSlots (ctx : Shape) (stage : SourceStage) (origin : SourceOrigin)
    (shape : Shape) (ids : List UID) :
    Except SourceDiagnostic {slots : Slots ctx shape // slots.uids = ids} :=
  go shape ids 0
where
  go : (sh : Shape) → (us : List UID) → Nat →
      Except SourceDiagnostic {slots : Slots ctx sh // slots.uids = us}
    | [], [], _ => .ok ⟨.nil, rfl⟩
    | a :: sh, uid :: us, i => do
      let here := { origin with slot := some i }
      let r ← match h : resolveRef ctx uid a.extent with
        | .error e => .error (liftDiagnostic stage here e)
        | .ok r => .ok (⟨r, resolveRef_uid ctx uid a.extent r h⟩ :
            {r : Ref ctx a.extent // r.uid = uid})
      let rest ← go sh us (i + 1)
      pure ⟨.cons r.val rest.val, by simp [Slots.uids, r.property, rest.property]⟩
    | _, _, i => .error (sourceError stage { origin with slot := some i }
        (.rank shape.length ids.length))

theorem Slots.project_pullback (src dst : Context) (m : IndexMap src dst)
    (hm : ∀ u, (m.map u).val = u.val) (a : Slots src.axes sh) (b : Slots dst.axes sh)
    (h : a.uids = b.uids) (v : UIDVal dst) :
    a.project (uidCoordEquiv src (indexPullback m v)) =
      b.project (uidCoordEquiv dst v) := by
  induction a with
  | nil => cases b; rfl
  | cons r rest ih =>
    cases b with
    | cons s tail =>
      have hs : r.uid = s.uid := (List.cons.inj h).1
      have hk : m.map (r.key src) = s.key dst := by
        apply Subtype.ext
        rw [hm, Ref.key_uid, Ref.key_uid, hs]
      apply Prod.ext
      · rw [Slots.project, Slots.project, Ref.get_uidCoordEquiv, Ref.get_uidCoordEquiv]
        apply Fin.ext
        change (v (m.map (r.key src))).val = (v (s.key dst)).val
        exact congrArg (fun u => (v u).val) hk
      · exact ih tail (List.cons.inj h).2

def firstUIDs (ids : List UID) : List UID := ids.reverse.dedup.reverse

def outputContext (c : Context) (keys : List c.Key) : Context where
  axes := keys.reverse.dedup.reverse.map (fun u => ⟨u.val, c.domain u⟩)
  unique := by
    simp only [List.map_map, Function.comp_def]
    exact (List.nodup_map_iff Subtype.val_injective).mpr
      (List.nodup_reverse.mpr (List.nodup_dedup _))

theorem outputContext_order (c : Context) (keys : List c.Key) :
    (outputContext c keys).axes.map Axis.uid = firstUIDs (keys.map Subtype.val) := by
  simp only [outputContext, firstUIDs, List.map_map, Function.comp_def,
    List.map_reverse]
  simpa only [List.map_reverse] using congrArg List.reverse
    (List.dedup_map_of_injective Subtype.val_injective keys.reverse).symm

structure IdentityEmbedding (src dst : Context) where
  map : IndexMap src dst
  uid : ∀ u, (map.map u).val = u.val

def identityEmbedding (src dst : Context) (origin : SourceOrigin) :
    Except SourceDiagnostic (IdentityEmbedding src dst) :=
  match h : resolveIndexMap src dst id with
  | .error e => .error (liftDiagnostic .support origin e)
  | .ok m => .ok ⟨m, fun u => resolveIndexMap_uid src dst id m h u⟩

structure RawRead (σ : Declarations Unit) where
  tensor : σ.Tensor
  indices : List UID
  origin : SourceOrigin

structure CheckedRead (c : Context) (σ : Declarations Unit) where
  read : Read c.axes σ
  indices : List UID
  linked : read.slots.uids = indices
  origin : SourceOrigin

def admitRead (c : Context) (read : RawRead σ) :
    Except SourceDiagnostic (CheckedRead c σ) := do
  let slots ← resolveSourceSlots c.axes .read read.origin
    (σ.signature read.tensor).axes read.indices
  pure ⟨⟨read.tensor, slots.val⟩, read.indices, slots.property, read.origin⟩

structure SupportPartition (source out : Context) (support : List UID) where
  bound : Shape
  exact : bound = source.axes.filter
    (fun a => a.uid ∈ support ∧ a.uid ∉ out.axes.map Axis.uid)
  context : Context
  context_axes : context.axes = out.axes ++ bound
  embedding : IdentityEmbedding context source

theorem SupportPartition.disjoint (p : SupportPartition source out support)
    (a : Axis) (ha : a ∈ out.axes) (b : Axis) (hb : b ∈ p.bound) : a.uid ≠ b.uid := by
  rw [p.exact] at hb
  have hn := (List.mem_filter.mp hb).2
  simp only [decide_eq_true_eq] at hn
  intro he
  exact hn.2 (he ▸ List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem SupportPartition.exactSupport (p : SupportPartition source out support) (uid : UID) :
    uid ∈ p.bound.map Axis.uid ↔
      uid ∈ source.axes.map Axis.uid ∧ uid ∈ support ∧ uid ∉ out.axes.map Axis.uid := by
  rw [p.exact]
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  aesop

theorem SupportPartition.coverage (p : SupportPartition source out support)
    (h : support ⊆ source.axes.map Axis.uid) (uid : UID) :
    uid ∈ p.context.axes.map Axis.uid ↔ uid ∈ out.axes.map Axis.uid ∨ uid ∈ support := by
  rw [p.context_axes, List.map_append, List.mem_append]
  rw [p.exactSupport]
  have := h (a := uid)
  tauto

def supportPartition (source out : Context) (support : List UID) (origin : SourceOrigin) :
    Except SourceDiagnostic (SupportPartition source out support) := do
  for uid in support do
    unless uid ∈ source.axes.map Axis.uid do
      throw (sourceError .support origin (.unbound uid))
  let bound := source.axes.filter
    (fun a => a.uid ∈ support ∧ a.uid ∉ out.axes.map Axis.uid)
  let context ← (checkContext (out.axes ++ bound)).mapError
    (liftDiagnostic .support origin)
  let embedding ← identityEmbedding context.val source origin
  pure ⟨bound, rfl, context.val, context.property, embedding⟩

inductive TermClass
  | pure | broadcast
  deriving DecidableEq, Repr

structure LocalizedRead (ctx : Context) (read : CheckedRead source σ) where
  slots : Slots ctx.axes (σ.signature read.read.tensor).axes
  linked : slots.uids = read.indices

def LocalizedRead.read {read : CheckedRead source σ}
    (localized : LocalizedRead ctx read) : Read ctx.axes σ :=
  ⟨read.read.tensor, localized.slots⟩

theorem LocalizedRead.projection {read : CheckedRead source σ}
    (localized : LocalizedRead ctx read)
    (embedding : IdentityEmbedding ctx source) (v : UIDVal source) :
    localized.slots.project (uidCoordEquiv ctx (indexPullback embedding.map v)) =
      read.read.slots.project (uidCoordEquiv source v) :=
  Slots.project_pullback _ _ embedding.map embedding.uid _ _
    (localized.linked.trans read.linked.symm) v

private def localizeReads (ctx : Context) :
    (reads : List (CheckedRead source σ)) →
    Except SourceDiagnostic ((i : Fin reads.length) → LocalizedRead ctx (reads.get i))
  | [] => .ok (fun i => nomatch i)
  | read :: reads => do
    let slots ← resolveSourceSlots ctx.axes .read read.origin
      (σ.signature read.read.tensor).axes read.indices
    let rest ← localizeReads ctx reads
    pure (Fin.cases ⟨slots.val, slots.property⟩ rest)

structure Term (source out : Context) (σ : Declarations Unit) where
  origin : SourceOrigin
  sourceReads : List (CheckedRead source σ)
  support : List UID
  support_reads : sourceReads.flatMap CheckedRead.indices = support
  partition : SupportPartition source out support
  reads : (i : Fin sourceReads.length) → LocalizedRead partition.context (sourceReads.get i)
  support_bound : support ⊆ source.axes.map Axis.uid
  classification : TermClass
  pure_iff : classification = .pure ↔ out.axes.map Axis.uid ⊆ support

def admitTerm (source out : Context) (origin : SourceOrigin) (raw : List (RawRead σ)) :
    Except SourceDiagnostic (Term source out σ) := do
  let global ← raw.mapM (admitRead source)
  let support := global.flatMap CheckedRead.indices
  have hs : support ⊆ source.axes.map Axis.uid := by
    intro uid h
    obtain ⟨read, _, hu⟩ := List.mem_flatMap.mp h
    rw [← read.linked] at hu
    exact read.read.slots.support source hu
  let partition ← supportPartition source out support origin
  let reads ← localizeReads partition.context global
  let classification := if out.axes.map Axis.uid ⊆ support then .pure else .broadcast
  pure ⟨origin, global, support, rfl, partition, reads, hs, classification, by
    simp only [classification]; split <;> simp_all⟩

def Term.operands (term : Term source out σ) : List (Read term.partition.context.axes σ) :=
  List.ofFn (fun i => (term.reads i).read)

theorem Term.read_projection (term : Term source out σ) (i : Fin term.sourceReads.length)
    (v : UIDVal source) :
    (term.reads i).slots.project
      (uidCoordEquiv term.partition.context (indexPullback term.partition.embedding.map v)) =
      (term.sourceReads.get i).read.slots.project (uidCoordEquiv source v) :=
  (term.reads i).projection term.partition.embedding v

structure AdmittedOutput (source : Context) (σ : Declarations Unit) where
  tensor : σ.Tensor
  indices : List UID
  origin : SourceOrigin
  context : Context
  order : context.axes.map Axis.uid = firstUIDs indices
  slots : Slots context.axes (σ.signature tensor).axes
  linked : slots.uids = indices
  sourceSlots : Slots source.axes (σ.signature tensor).axes
  source_linked : sourceSlots.uids = indices
  embedding : IdentityEmbedding context source

def admitOutput (source : Context) (dst : σ.Tensor) (ids : List UID) (origin : SourceOrigin) :
    Except SourceDiagnostic {output : AdmittedOutput source σ // output.tensor = dst} := do
  let global ← resolveSourceSlots source.axes .output origin (σ.signature dst).axes ids
  let context := outputContext source (global.val.keys source)
  let embedding ← identityEmbedding context source origin
  let slots ← resolveSourceSlots context.axes .output origin (σ.signature dst).axes ids
  pure ⟨⟨dst, ids, origin, context, by
    rw [outputContext_order, Slots.keys_uids, global.property],
    slots.val, slots.property, global.val, global.property, embedding⟩, rfl⟩

theorem AdmittedOutput.projection (output : AdmittedOutput source σ) (v : UIDVal source) :
    output.slots.project
      (uidCoordEquiv output.context (indexPullback output.embedding.map v)) =
      output.sourceSlots.project (uidCoordEquiv source v) :=
  Slots.project_pullback _ _ output.embedding.map output.embedding.uid _ _
    (output.linked.trans output.source_linked.symm) v

def admitPure (term : Term source out σ) : Bool := term.classification == .pure

private def readIndices (c : Context) (origin : SourceOrigin) (es : List IdxExpr) :
    Except SourceDiagnostic (List UID) :=
  es.zipIdx.mapM fun (e, i) => do
    let here := { origin with slot := some i }
    match e with
    | .axis a => let _ ← sourceAxis c .read here a; pure a.uid
    | .const _ | .scale .. | .shift .. | .affine .. =>
      throw (sourceError .read here (.unsupported .affine))

private def outputIndices (c : Context) (origin : SourceOrigin) (slots : List LHSSlot) :
    Except SourceDiagnostic (List UID) :=
  slots.zipIdx.mapM fun (slot, i) => do
    let here := { origin with slot := some i }
    match slot with
    | .free a => let _ ← sourceAxis c .output here a; pure a.uid
    | .freeNorm _ => throw (sourceError .output here (.unsupported .marked))
    | .iterAt .. | .iterNext _ => throw (sourceError .output here (.unsupported .scanSlot))
    | .affine _ => throw (sourceError .output here (.unsupported .affine))

private def astRead (source : AdaptedSource) (origin : SourceOrigin) :
    Factor → Except SourceDiagnostic (RawRead source.table.declarations)
  | .read name es => do
    let tensor ← match source.table.find name with
      | none => throw (sourceError .read origin (.undeclaredTensor name))
      | some t => pure t
    let linkedOrigin := { origin with
      declaration := some (source.table.entry tensor).declaration }
    let ids ← readIndices source.context linkedOrigin es
    pure ⟨tensor, ids, linkedOrigin⟩
  | .iverson _ => .error (sourceError .read origin (.unsupported .iverson))
  | .unaryFn .. => .error (sourceError .read origin (.unsupported .unary))

structure AdmittedStatement (source : AdaptedSource) where
  original : Nat
  output : AdmittedOutput source.context source.table.declarations
  writable : (source.table.entry output.tensor).role ≠ .input
  terms : List (Term source.context output.context source.table.declarations)

def admitStatement (source : AdaptedSource) (original : Nat) :
    Stmt → Except SourceDiagnostic (AdmittedStatement source)
  | .scatter .. => .error (sourceError .statement { statement := some original }
      (.unsupported .scatter))
  | .recurMorphism .. => .error (sourceError .statement { statement := some original }
      (.unsupported .recurMorphism))
  | .assign name slots rhs => do
    let origin : SourceOrigin := { side := .output, statement := some original }
    if rhs.agg != .sum then throw (sourceError .statement origin (.unsupported .nonSum))
    if rhs.nonlin != .identity then
      throw (sourceError .statement origin (.unsupported .nonIdentity))
    let dst ← match source.table.find name with
      | none => throw (sourceError .output origin (.undeclaredTensor name))
      | some t => pure t
    let origin := { origin with declaration := some (source.table.entry dst).declaration }
    if hw : (source.table.entry dst).role ≠ .input then
      let ids ← outputIndices source.context origin slots
      let checkedOutput ← admitOutput source.context dst ids origin
      let output := checkedOutput.val
      let terms ← rhs.body.terms.zipIdx.mapM fun (term, i) => do
        let termOrigin := { origin with side := .read, declaration := none, term := some i }
        let reads ← term.factors.zipIdx.mapM fun (factor, j) =>
          astRead source { termOrigin with factor := some j } factor
        admitTerm source.context output.context termOrigin reads
      pure ⟨original, output, by rw [checkedOutput.property]; exact hw, terms⟩
    else
      throw (sourceError .output origin (.role .defined (source.table.entry dst).role))

structure AdmittedSource where
  source : AdaptedSource
  statements : List (AdmittedStatement source)

def admitSource (snapshot : SourceSnapshot) : Except SourceDiagnostic AdmittedSource := do
  let source ← adaptSource snapshot
  let statements ← source.statements.mapM fun (i, statement) =>
    admitStatement source i statement
  pure ⟨source, statements⟩

def admitRawSource (raw : TLProgram) (specs : List TensorSpec) (inputs : List InputBinding) :
    Except SourceDiagnostic AdmittedSource := do
  let snapshot ← resolveSource raw specs inputs
  admitSource snapshot

end LeanNCD.Semantics.Source
