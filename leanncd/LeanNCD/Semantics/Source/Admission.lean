import LeanNCD.Semantics.Source.Adapter
import LeanNCD.Semantics.Source.Lowering

namespace LeanNCD.Semantics.Source

theorem mapM_success_forall2 {α β ε : Type} (f : α → Except ε β)
    (xs : List α) (ys : List β) (h : xs.mapM f = .ok ys) :
    List.Forall₂ (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    simp [List.mapM_nil, pure, Except.pure] at h
    subst ys
    exact .nil
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, Except.bind, Except.pure] at h
    cases hx : f x with
    | error e => simp [hx] at h
    | ok y =>
      cases ht : xs.mapM f with
      | error e => simp [hx, ht] at h
      | ok zs =>
        have he : y :: zs = ys := by simpa [hx, ht] using h
        subst ys
        exact .cons hx (ih zs ht)

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

theorem admitRead_fields (c : Context) (raw : RawRead σ) (checked : CheckedRead c σ)
    (h : admitRead c raw = .ok checked) :
    checked.read.tensor = raw.tensor ∧ checked.indices = raw.indices ∧
      checked.origin = raw.origin := by
  unfold admitRead at h
  simp only [bind, pure, Except.bind, Except.pure] at h
  split at h
  · contradiction
  · simp only [Except.ok.injEq] at h
    subst checked
    exact ⟨rfl, rfl, rfl⟩

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

theorem admitTerm_reads (source out : Context) (origin : SourceOrigin)
    (raw : List (RawRead σ)) (term : Term source out σ)
    (h : admitTerm source out origin raw = .ok term) :
    term.origin = origin ∧
      List.Forall₂ (fun r c => c.read.tensor = r.tensor ∧ c.indices = r.indices ∧
        c.origin = r.origin) raw term.sourceReads := by
  unfold admitTerm at h
  simp only [bind, pure, Except.bind, Except.pure] at h
  cases hg : raw.mapM (admitRead source) with
  | error e => simp [hg] at h
  | ok global =>
    simp only [hg] at h
    repeat' split at h
    all_goals simp only [Except.ok.injEq, reduceCtorEq] at h
    all_goals subst term
    all_goals exact ⟨rfl, (mapM_success_forall2 _ _ _ hg).imp
      (fun _ _ hc => admitRead_fields source _ _ hc)⟩

theorem Term.read_projection (term : Term source out σ) (i : Fin term.sourceReads.length)
    (v : UIDVal source) :
    (term.reads i).slots.project
      (uidCoordEquiv term.partition.context (indexPullback term.partition.embedding.map v)) =
      (term.sourceReads.get i).read.slots.project (uidCoordEquiv source v) :=
  (term.reads i).projection term.partition.embedding v

/-- An integer-affine destination form `(c0, [(coef, uid)])`, as `idxAffineForm` produces:
one per destination axis. Data the oracle reads instead of `AdmittedOutput.dest`. -/
abbrev WriteForm := Int × List (Int × UID)

def WriteForm.single (u : UID) : WriteForm := (0, [(1, u)])

def WriteForm.uids (f : WriteForm) : List UID := f.2.map Prod.snd

/-- The value of a form under a UID valuation. -/
def writeValue (f : WriteForm) (v : UID → Int) : Int :=
  f.1 + (f.2.map fun t => t.1 * v t.2).sum

/-- The value at the first axis with this UID (0 when absent). -/
def coordLookup : {sh : Shape} → Coord sh → UID → Int
  | [], _, _ => 0
  | a :: _, p, u => if a.uid = u then (p.1.val : Int) else coordLookup p.2 u

def coordValues : {sh : Shape} → Coord sh → List Int
  | [], _ => []
  | _ :: _, p => (p.1.val : Int) :: coordValues p.2

/-- Decide a predicate over the whole box `Coord sh` by enumeration. -/
def coordAll : (sh : Shape) → (Coord sh → Bool) → Bool
  | [], p => p ()
  | a :: sh, p => (List.finRange a.extent).all fun i => coordAll sh fun w => p (i, w)

theorem coordAll_spec : (sh : Shape) → (p : Coord sh → Bool) → coordAll sh p = true →
    ∀ w, p w = true
  | [], _, h, () => h
  | a :: sh, p, h, w => by
    simp only [coordAll, List.all_eq_true, List.mem_finRange, true_implies] at h
    exact coordAll_spec sh (fun v => p (w.1, v)) (h w.1) w.2

def formFits (a : Axis) (f : WriteForm) (v : UID → Int) : Bool :=
  decide (0 ≤ writeValue f v) && decide (writeValue f v < a.extent)

def formsFit : Shape → List WriteForm → (UID → Int) → Bool
  | [], [], _ => true
  | a :: sh, f :: fs, v => formFits a f v && formsFit sh fs v
  | _, _, _ => false

def fitIndex (a : Axis) (f : WriteForm) (v : UID → Int) (h : formFits a f v = true) :
    Fin a.extent :=
  ⟨(writeValue f v).toNat, by
    simp only [formFits, Bool.and_eq_true, decide_eq_true_eq] at h; omega⟩

theorem fitIndex_val (a : Axis) (f : WriteForm) (v : UID → Int) (h : formFits a f v = true) :
    ((fitIndex a f v h).val : Int) = writeValue f v := by
  simp only [formFits, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [fitIndex]; omega

/-- The destination coordinate the forms denote, given they fit the destination shape. -/
def coordOfForms : (sh : Shape) → (fs : List WriteForm) → (v : UID → Int) →
    formsFit sh fs v = true → Coord sh
  | [], [], _, _ => ()
  | a :: sh, f :: fs, v, h =>
    (fitIndex a f v (Bool.and_eq_true_iff.mp h).1,
      coordOfForms sh fs v (Bool.and_eq_true_iff.mp h).2)
  | [], _ :: _, _, h => absurd h (by simp [formsFit])
  | _ :: _, [], _, h => absurd h (by simp [formsFit])

theorem coordValues_ofForms : (sh : Shape) → (fs : List WriteForm) → (v : UID → Int) →
    (h : formsFit sh fs v = true) →
      coordValues (coordOfForms sh fs v h) = fs.map (writeValue · v)
  | [], [], _, _ => rfl
  | a :: sh, f :: fs, v, h => by
    simp only [coordOfForms, coordValues, List.map_cons, fitIndex_val,
      coordValues_ofForms sh fs v]
  | [], _ :: _, _, h => absurd h (by simp [formsFit])
  | _ :: _, [], _, h => absurd h (by simp [formsFit])

theorem Ref.uid_mem : {sh : Shape} → (r : Ref sh n) → r.uid ∈ sh.map Axis.uid
  | _ :: _, .here => by simp [Ref.uid]
  | _ :: _, .there r => by
    simp only [Ref.uid, List.map_cons, List.mem_cons]; exact Or.inr (Ref.uid_mem r)

theorem Ref.get_lookup : {sh : Shape} → (r : Ref sh n) → (sh.map Axis.uid).Nodup →
    (w : Coord sh) → ((r.get w).val : Int) = coordLookup w r.uid
  | _ :: _, .here, _, _ => by simp [Ref.get, Ref.uid, coordLookup]
  | a :: _, .there r, hn, w => by
    have hn' := List.nodup_cons.mp hn
    have hne : a.uid ≠ r.uid := fun he => hn'.1 (he ▸ Ref.uid_mem r)
    simp only [Ref.get, Ref.uid, coordLookup, if_neg hne]
    exact Ref.get_lookup r hn'.2 w.2

theorem Slots.values_project (hn : (ctx.map Axis.uid).Nodup) :
    (slots : Slots ctx sh) → (w : Coord ctx) →
      coordValues (slots.project w) = slots.uids.map (coordLookup w)
  | .nil, _ => rfl
  | .cons r rest, w => by
    simp only [Slots.project, coordValues, Slots.uids, List.map_cons, Ref.get_lookup r hn w,
      Slots.values_project hn rest w]

theorem Slots.lookup_project (hn : (ctx.map Axis.uid).Nodup) :
    (slots : Slots ctx sh) → slots.uids = sh.map Axis.uid → (w : Coord ctx) → (u : UID) →
      u ∈ sh.map Axis.uid → coordLookup (slots.project w) u = coordLookup w u
  | .nil, _, _, u, hu => by simp at hu
  | .cons (a := a) r rest, h, w, u, hu => by
    simp only [Slots.uids, List.map_cons, List.cons.injEq] at h
    rw [List.map_cons, List.mem_cons] at hu
    simp only [Slots.project, coordLookup]
    by_cases hau : a.uid = u
    · rw [if_pos hau, Ref.get_lookup r hn w, h.1, hau]
    · rw [if_neg hau]
      exact Slots.lookup_project hn rest h.2 w u (hu.resolve_left (Ne.symm hau))

theorem writeValue_congr (f : WriteForm) (v v' : UID → Int) (h : ∀ u ∈ f.uids, v u = v' u) :
    writeValue f v = writeValue f v' := by
  unfold writeValue
  congr 2
  apply List.map_congr_left
  intro p hp
  rw [h p.2 (List.mem_map.mpr ⟨p, hp, rfl⟩)]

theorem writeValue_single (u : UID) (v : UID → Int) : writeValue (.single u) v = v u := by
  simp [writeValue, WriteForm.single]

structure AdmittedOutput (source : Context) (σ : Declarations Unit) where
  tensor : σ.Tensor
  indices : List UID
  origin : SourceOrigin
  context : Context
  order : context.axes.map Axis.uid = firstUIDs indices
  /-- Virtual write shape: the coordinates `slots` project to. For a bare write this is the
  destination signature; for an affine write, the axes its LHS slots mention. -/
  shape : Shape
  /-- Destination index map from virtual write coordinates to destination coordinates;
  `id` for a bare write. Colliding coordinates are summed by the collection. -/
  dest : Coord shape → Coord (σ.signature tensor).axes
  slots : Slots context.axes shape
  linked : slots.uids = indices
  sourceSlots : Slots source.axes shape
  source_linked : sourceSlots.uids = indices
  embedding : IdentityEmbedding context source
  /-- One integer-affine form per destination axis, over source UIDs: the destination as DATA,
  for consumers (the oracle) that must not use `dest`. `WriteForm.single` per slot for a bare
  write. Tied to `dest` by `AdmittedOutput.FormsSpec`, proved for the two output builders
  `admitOutput` (by `admitOutput_formsSpec`) and `admitAffineOutput` (by
  `admitAffineOutput_formsSpec`); NOT stated as a theorem for the full `admitSourceAffine` result
  (`admitAffineWrite` is private). Not stored: a stored proof would stop `{ o with dest := … }`
  retargeting. -/
  forms : List WriteForm

/-- The destination is a bare projection of the source valuation (no index map): the
meaning the raw-parse chain certifies. -/
def AdmittedOutput.IsBare (output : AdmittedOutput source σ) : Prop :=
  ∃ bare : Slots source.axes (σ.signature output.tensor).axes,
    bare.uids = output.indices ∧
      ∀ w, output.dest (output.sourceSlots.project w) = bare.project w

theorem AdmittedOutput.isBare_of_identity (output : AdmittedOutput source σ)
    (hs : output.shape = (σ.signature output.tensor).axes)
    (hd : ∀ x, output.dest x = hs ▸ x) : output.IsBare := by
  cases output with
  | mk tensor indices origin context order shape dest slots linked sourceSlots
      source_linked embedding forms =>
    simp only at hs hd ⊢
    subst hs
    exact ⟨sourceSlots, source_linked, fun w => hd _⟩

def admitOutput (source : Context) (dst : σ.Tensor) (ids : List UID) (origin : SourceOrigin) :
    Except SourceDiagnostic {output : AdmittedOutput source σ // output.tensor = dst} := do
  let global ← resolveSourceSlots source.axes .output origin (σ.signature dst).axes ids
  let context := outputContext source (global.val.keys source)
  let embedding ← identityEmbedding context source origin
  let slots ← resolveSourceSlots context.axes .output origin (σ.signature dst).axes ids
  pure ⟨⟨dst, ids, origin, context, by
    rw [outputContext_order, Slots.keys_uids, global.property], (σ.signature dst).axes, id,
    slots.val, slots.property, global.val, global.property, embedding,
    ids.map WriteForm.single⟩, rfl⟩

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

def BareReadSlots (es : List IdxExpr) (ids : List UID) : Prop :=
  List.Forall₂ (fun (e, _) uid => ∃ a : AxisSpec, e = .axis a ∧ uid = a.uid)
    es.zipIdx ids

def BareOutputSlots (slots : List LHSSlot) (ids : List UID) : Prop :=
  List.Forall₂ (fun (s, _) uid => ∃ a : AxisSpec, s = .free a ∧ uid = a.uid)
    slots.zipIdx ids

private theorem readIndices_fields (c : Context) (origin : SourceOrigin)
    (es : List IdxExpr) (ids : List UID) (h : readIndices c origin es = .ok ids) :
    BareReadSlots es ids := by
  apply (mapM_success_forall2 _ _ _ h).imp
  rintro ⟨e, i⟩ uid he
  cases e <;> simp only [bind, pure, Except.bind, Except.pure, throw,
    MonadExceptOf.throw, throwThe] at he
  all_goals repeat' split at he
  all_goals simp_all

private theorem outputIndices_fields (c : Context) (origin : SourceOrigin)
    (slots : List LHSSlot) (ids : List UID) (h : outputIndices c origin slots = .ok ids) :
    BareOutputSlots slots ids := by
  apply (mapM_success_forall2 _ _ _ h).imp
  rintro ⟨s, i⟩ uid he
  cases s <;> simp only [bind, pure, Except.bind, Except.pure, throw,
    MonadExceptOf.throw, throwThe] at he
  all_goals repeat' split at he
  all_goals simp_all

def FactorFields (source : AdaptedSource) (origin : SourceOrigin) (f : Factor)
    (r : RawRead source.table.declarations) : Prop :=
  ∃ name es, f = .read name es ∧ source.table.find name = some r.tensor ∧
    (source.table.entry r.tensor).name = name ∧ BareReadSlots es r.indices ∧
    r.origin = { origin with declaration := some (source.table.entry r.tensor).declaration }

theorem astRead_fields (source : AdaptedSource) (origin : SourceOrigin)
    (f : Factor) (r : RawRead source.table.declarations) (h : astRead source origin f = .ok r) :
    FactorFields source origin f r := by
  cases f with
  | iverson _ => simp [astRead] at h
  | unaryFn _ _ _ => simp [astRead] at h
  | read name es =>
    simp only [astRead, bind, pure, Except.bind, Except.pure] at h
    cases ht : source.table.find name with
    | none => simp [ht, throw, MonadExceptOf.throw, throwThe] at h
    | some t =>
      simp only [ht] at h
      cases hi : readIndices source.context
          { origin with declaration := some (source.table.entry t).declaration } es with
      | error e => simp [hi] at h
      | ok ids =>
        simp only [hi, Except.ok.injEq] at h
        subst r
        exact ⟨name, es, rfl, ht, source.table.find_name name t ht,
          readIndices_fields _ _ _ _ hi, rfl⟩

def TermFields (source : AdaptedSource) (origin : SourceOrigin) (ast : ProdTerm)
    (term : Term source.context out source.table.declarations) : Prop :=
  term.origin = origin ∧ ∃ raw : List (RawRead source.table.declarations),
    List.Forall₂ (fun (f, j) r => FactorFields source { origin with factor := some j } f r)
      ast.factors.zipIdx raw ∧
    List.Forall₂ (fun r c => c.read.tensor = r.tensor ∧ c.indices = r.indices ∧
      c.origin = r.origin) raw term.sourceReads

private theorem admitAstTerm_fields (source : AdaptedSource) (out : Context)
    (origin : SourceOrigin) (ast : ProdTerm) (term : Term source.context out
      source.table.declarations)
    (h : (do
      let reads ← ast.factors.zipIdx.mapM fun (factor, j) =>
        astRead source { origin with factor := some j } factor
      admitTerm source.context out origin reads) = .ok term) :
    TermFields source origin ast term := by
  simp only [bind, Except.bind] at h
  cases hr : ast.factors.zipIdx.mapM (fun (factor, j) =>
      astRead source { origin with factor := some j } factor) with
  | error e => simp [hr] at h
  | ok reads =>
    simp only [hr] at h
    obtain ⟨ho, hc⟩ := admitTerm_reads _ _ _ _ _ h
    exact ⟨ho, reads, (mapM_success_forall2 _ _ _ hr).imp
      (fun x r hx => astRead_fields source _ x.1 r hx), hc⟩

theorem admitOutput_fields (source : Context) (dst : σ.Tensor) (ids : List UID)
    (origin : SourceOrigin) (output : {o : AdmittedOutput source σ // o.tensor = dst})
    (h : admitOutput source dst ids origin = .ok output) :
    output.val.indices = ids ∧ output.val.origin = origin := by
  unfold admitOutput at h
  simp only [bind, pure, Except.bind, Except.pure] at h
  repeat' split at h
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at h
  all_goals subst output
  all_goals exact ⟨rfl, rfl⟩

/-- Admission's output is the identity case of the destination index map. -/
theorem admitOutput_identity (source : Context) (dst : σ.Tensor) (ids : List UID)
    (origin : SourceOrigin) (output : {o : AdmittedOutput source σ // o.tensor = dst})
    (h : admitOutput source dst ids origin = .ok output) :
    ∃ hs : output.val.shape = (σ.signature output.val.tensor).axes,
      ∀ x, output.val.dest x = hs ▸ x := by
  unfold admitOutput at h
  simp only [bind, pure, Except.bind, Except.pure] at h
  repeat' split at h
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at h
  all_goals subst output
  all_goals exact ⟨rfl, fun _ => rfl⟩

theorem admitOutput_bare (source : Context) (dst : σ.Tensor) (ids : List UID)
    (origin : SourceOrigin) (output : {o : AdmittedOutput source σ // o.tensor = dst})
    (h : admitOutput source dst ids origin = .ok output) : output.val.IsBare := by
  obtain ⟨hs, hd⟩ := admitOutput_identity source dst ids origin output h
  exact output.val.isBare_of_identity hs hd

/-- `forms` denote `dest`: for every source valuation, the destination coordinate's values are
the forms evaluated at the source UIDs. -/
def AdmittedOutput.FormsSpec (output : AdmittedOutput source σ) : Prop :=
  ∀ w : Coord source.axes, coordValues (output.dest (output.sourceSlots.project w)) =
    output.forms.map (writeValue · (coordLookup w))

theorem admitOutput_forms (source : Context) (dst : σ.Tensor) (ids : List UID)
    (origin : SourceOrigin) (output : {o : AdmittedOutput source σ // o.tensor = dst})
    (h : admitOutput source dst ids origin = .ok output) :
    output.val.forms = ids.map WriteForm.single := by
  unfold admitOutput at h
  simp only [bind, pure, Except.bind, Except.pure] at h
  repeat' split at h
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at h
  all_goals subst output
  all_goals rfl

theorem admitOutput_formsSpec (source : Context) (dst : σ.Tensor) (ids : List UID)
    (origin : SourceOrigin) (output : {o : AdmittedOutput source σ // o.tensor = dst})
    (h : admitOutput source dst ids origin = .ok output) : output.val.FormsSpec := by
  obtain ⟨bare, hu, hb⟩ := admitOutput_bare source dst ids origin output h
  intro w
  rw [hb w, Slots.values_project source.unique, admitOutput_forms _ _ _ _ _ h, hu,
    (admitOutput_fields _ _ _ _ _ h).1, List.map_map]
  exact List.map_congr_left fun u _ => (writeValue_single u _).symm

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

def StatementFields (source : AdaptedSource) (i : Nat) (ast : Stmt)
    (statement : AdmittedStatement source) : Prop :=
  ∃ name slots rhs,
    ast = .assign name slots rhs ∧ statement.original = i ∧
    rhs.agg = .sum ∧ rhs.nonlin = .identity ∧
    source.table.find name = some statement.output.tensor ∧
    (source.table.entry statement.output.tensor).name = name ∧
    (BareOutputSlots slots statement.output.indices ∧ statement.output.IsBare) ∧
    statement.output.origin = {
      side := .output, statement := some i,
      declaration := some (source.table.entry statement.output.tensor).declaration } ∧
    List.Forall₂ (fun (t, j) term => TermFields source {
      side := .read, statement := some i, term := some j } t term)
      rhs.body.terms.zipIdx statement.terms

theorem admitStatement_fields (source : AdaptedSource) (i : Nat) (ast : Stmt)
    (statement : AdmittedStatement source) (h : admitStatement source i ast = .ok statement) :
    StatementFields source i ast statement := by
  cases ast with
  | scatter _ _ _ _ => simp [admitStatement] at h
  | recurMorphism _ _ _ => simp [admitStatement] at h
  | assign name slots rhs =>
    simp only [admitStatement, bind, pure, Except.bind, Except.pure,
      throw, MonadExceptOf.throw, throwThe] at h
    split at h
    · contradiction
    · rename_i ha
      split at h
      · contradiction
      · rename_i hn
        cases ht : source.table.find name with
        | none => simp [ht] at h
        | some dst =>
          simp only [ht] at h
          split at h
          · cases hi : outputIndices source.context
                { side := .output, statement := some i,
                  declaration := some (source.table.entry dst).declaration } slots with
            | error e => simp [hi] at h
            | ok ids =>
              simp only [hi] at h
              cases ho : admitOutput source.context dst ids
                  { side := .output, statement := some i,
                    declaration := some (source.table.entry dst).declaration } with
              | error e => simp [ho] at h
              | ok output =>
                simp only [ho] at h
                split at h
                · contradiction
                · rename_i terms hs
                  simp only [Except.ok.injEq] at h
                  subst statement
                  obtain ⟨hid, horigin⟩ := admitOutput_fields _ _ _ _ _ ho
                  refine ⟨name, slots, rhs, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · simpa using ha
                  · simpa using hn
                  · simpa only [output.property] using ht
                  · simpa only [output.property] using source.table.find_name name dst ht
                  · exact ⟨by rw [hid]; exact outputIndices_fields _ _ _ _ hi,
                      admitOutput_bare _ _ _ _ _ ho⟩
                  · simpa only [output.property] using horigin
                  · exact (mapM_success_forall2 _ _ _ hs).imp
                      (fun x term hx => admitAstTerm_fields source output.val.context
                        _ x.1 term hx)
          · contradiction

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

theorem admitSource_fields (snapshot : SourceSnapshot) (admitted : AdmittedSource)
    (h : admitSource snapshot = .ok admitted) :
    admitted.source.statements = snapshot.resolved.stmts.zipIdx.map (fun (s, i) => (i, s)) ∧
    List.Forall₂ (fun (i, s) a => StatementFields admitted.source i s a)
      admitted.source.statements admitted.statements := by
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
      exact ⟨adaptSource_statements _ _ ha, (mapM_success_forall2 _ _ _ hs).imp
        (fun x s hx => admitStatement_fields source x.1 x.2 s hx)⟩

/-! ### Non-bare writes (S2a)

A second admission entry, `admitSourceAffine`, also admits writes whose LHS slots are integer-
affine (`LHSSlot.affine`) and `Stmt.scatter` with `fill = 0`, `reduce ∈ {sum, rejectCollisions}`.
The default entry `admitSource` (and so `admitRawSource`, `StatementFields` and the whole raw
chain) is unchanged and still refuses them: affine statements get no raw-parse theorem, by
construction. Bare `.assign` statements go through `admitStatement` unchanged in both entries. -/

private def idxAxes : IdxExpr → List AxisSpec
  | .axis a | .scale _ a | .shift a _ => [a]
  | .const _ => []
  | .affine _ xs => xs.map Prod.snd

/-- One form per LHS slot. Scan and marked slots stay refused with today's causes. -/
private def outputForms (c : Context) (origin : SourceOrigin) (slots : List LHSSlot) :
    Except SourceDiagnostic (List WriteForm) :=
  slots.zipIdx.mapM fun (slot, i) => do
    let here := { origin with slot := some i }
    match slot with
    | .free a => let _ ← sourceAxis c .output here a; pure (.single a.uid)
    | .affine e => let _ ← (idxAxes e).mapM (sourceAxis c .output here); pure (idxAffineForm e)
    | .freeNorm _ => throw (sourceError .output here (.unsupported .marked))
    | .iterAt .. | .iterNext _ => throw (sourceError .output here (.unsupported .scanSlot))

/-- The distinct UIDs the forms mention, in first-mention order. -/
def formsSupport (forms : List WriteForm) : List UID := firstUIDs (forms.flatMap WriteForm.uids)

theorem mem_formsSupport (forms : List WriteForm) (f : WriteForm) (hf : f ∈ forms)
    (u : UID) (hu : u ∈ f.uids) : u ∈ formsSupport forms := by
  simp only [formsSupport, firstUIDs, List.mem_reverse, List.mem_dedup, List.mem_flatMap]
  exact ⟨f, hf, hu⟩

/-- The virtual write shape: the support axes with their source extents. -/
def supportShape (c : Context) (ids : List UID) : Shape :=
  ids.map fun u => ⟨u, ((c.axes.find? (·.uid == u)).map Axis.extent).getD 0⟩

theorem supportShape_uids (c : Context) (ids : List UID) :
    (supportShape c ids).map Axis.uid = ids := by
  simp [supportShape, List.map_map, Function.comp_def]

/-- Admit a write through affine forms. The static range check enumerates the support box:
every form must land in `[0, extent)` of its destination axis, else `writeOutOfRange` at the
first such axis. -/
def admitAffineOutput (source : Context) (dst : σ.Tensor) (forms : List WriteForm)
    (origin : SourceOrigin) :
    Except SourceDiagnostic {output : AdmittedOutput source σ // output.tensor = dst} := do
  let sig := (σ.signature dst).axes
  if forms.length ≠ sig.length then
    throw (sourceError .output { origin with slot := some (min forms.length sig.length) }
      (.rank sig.length forms.length))
  let ids := formsSupport forms
  let shape := supportShape source ids
  let global ← resolveSourceSlots source.axes .output origin shape ids
  let context := outputContext source (global.val.keys source)
  let embedding ← identityEmbedding context source origin
  let slots ← resolveSourceSlots context.axes .output origin shape ids
  if hfit : coordAll shape (fun w => formsFit sig forms (coordLookup w)) = true then
    pure ⟨⟨dst, ids, origin, context, by
      rw [outputContext_order, Slots.keys_uids, global.property], shape,
      fun w => coordOfForms sig forms (coordLookup w) (coordAll_spec _ _ hfit w),
      slots.val, slots.property, global.val, global.property, embedding, forms⟩, rfl⟩
  else
    let bad := (((sig.zip forms).zipIdx.find? fun ((ax, f), _) =>
      !coordAll shape (fun w => formFits ax f (coordLookup w))).map (·.2)).getD 0
    throw (sourceError .output { origin with slot := some bad } .writeOutOfRange)

theorem AdmittedOutput.formsSpec_of_forms (output : AdmittedOutput source σ)
    (hshape : output.shape.map Axis.uid = output.indices)
    (hsupp : ∀ f ∈ output.forms, ∀ u ∈ f.uids, u ∈ output.indices)
    (hfit : ∀ w, formsFit (σ.signature output.tensor).axes output.forms (coordLookup w) = true)
    (hd : ∀ w, output.dest w = coordOfForms _ output.forms (coordLookup w) (hfit w)) :
    output.FormsSpec := by
  intro w
  rw [hd, coordValues_ofForms]
  refine List.map_congr_left fun f hf => writeValue_congr f _ _ fun u hu => ?_
  exact Slots.lookup_project source.unique output.sourceSlots
    (output.source_linked.trans hshape.symm) w u (hshape ▸ hsupp f hf u hu)

theorem admitAffineOutput_formsSpec (source : Context) (dst : σ.Tensor)
    (forms : List WriteForm) (origin : SourceOrigin)
    (output : {o : AdmittedOutput source σ // o.tensor = dst})
    (h : admitAffineOutput source dst forms origin = .ok output) :
    output.val.forms = forms ∧ output.val.FormsSpec := by
  unfold admitAffineOutput at h
  simp only [bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at h
  all_goals subst output
  all_goals exact ⟨rfl, AdmittedOutput.formsSpec_of_forms _ (supportShape_uids _ _)
    (fun f hf u hu => mem_formsSupport _ f hf u hu)
    (coordAll_spec _ _ (by assumption)) (fun _ => rfl)⟩

private def LHSSlot.isFree : LHSSlot → Bool
  | .free _ => true
  | _ => false

/-- The write body of `admitStatement`'s `.assign` arm, with the output admitted through
affine forms. -/
private def admitAffineWrite (source : AdaptedSource) (original : Nat) (name : String)
    (slots : List LHSSlot) (rhs : RHSExpr) : Except SourceDiagnostic (AdmittedStatement source) := do
  let origin : SourceOrigin := { side := .output, statement := some original }
  if rhs.agg != .sum then throw (sourceError .statement origin (.unsupported .nonSum))
  if rhs.nonlin != .identity then
    throw (sourceError .statement origin (.unsupported .nonIdentity))
  let dst ← match source.table.find name with
    | none => throw (sourceError .output origin (.undeclaredTensor name))
    | some t => pure t
  let origin := { origin with declaration := some (source.table.entry dst).declaration }
  if hw : (source.table.entry dst).role ≠ .input then
    let forms ← outputForms source.context origin slots
    let checkedOutput ← admitAffineOutput source.context dst forms origin
    let output := checkedOutput.val
    let terms ← rhs.body.terms.zipIdx.mapM fun (term, i) => do
      let termOrigin := { origin with side := .read, declaration := none, term := some i }
      let reads ← term.factors.zipIdx.mapM fun (factor, j) =>
        astRead source { termOrigin with factor := some j } factor
      admitTerm source.context output.context termOrigin reads
    pure ⟨original, output, by rw [checkedOutput.property]; exact hw, terms⟩
  else
    throw (sourceError .output origin (.role .defined (source.table.entry dst).role))

/-- `admitStatement`, plus non-bare `.assign` and policy-checked `.scatter`. -/
def admitAffineStatement (source : AdaptedSource) (original : Nat) :
    Stmt → Except SourceDiagnostic (AdmittedStatement source)
  | .assign name slots rhs =>
    if slots.all LHSSlot.isFree then admitStatement source original (.assign name slots rhs)
    else admitAffineWrite source original name slots rhs
  | .scatter name slots rhs opts =>
    if opts.fill != 0 || !(opts.reduce == .sum || opts.reduce == .rejectCollisions) then
      .error (sourceError .statement { statement := some original } (.unsupported .scatterPolicy))
    else if slots.all LHSSlot.isFree then
      admitStatement source original (.assign name slots rhs)
    else admitAffineWrite source original name slots rhs
  | stmt => admitStatement source original stmt

/-- The admission entry for the differential path: `admitSource` with non-bare writes. -/
def admitSourceAffine (snapshot : SourceSnapshot) : Except SourceDiagnostic AdmittedSource := do
  let source ← adaptSource snapshot
  let statements ← source.statements.mapM fun (i, statement) =>
    admitAffineStatement source i statement
  pure ⟨source, statements⟩

end LeanNCD.Semantics.Source
