import LeanNCD.Semantics.Source.Statement

namespace LeanNCD.Semantics.Source

theorem Context.ext_axes (a b : Context) (h : a.axes = b.axes) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance uidValFinite (c : Context) : Fintype (UIDVal c) :=
  Fintype.ofEquiv (Coord c.axes) (uidCoordEquiv c).symm

instance uidValEq (c : Context) : DecidableEq (UIDVal c) :=
  (uidCoordEquiv c).injective.decidableEq

/-- Select original axes in original resolved order, without completing unused domains. -/
def Context.select (source : Context) (ids : List UID) : Context where
  axes := source.axes.filter (fun a => a.uid ∈ ids)
  unique := source.unique.sublist ((List.filter_sublist).map Axis.uid)

theorem Context.select_support (source : Context) (ids : List UID) (uid : UID) :
    uid ∈ (source.select ids).axes.map Axis.uid ↔
      uid ∈ source.axes.map Axis.uid ∧ uid ∈ ids := by
  simp only [Context.select, List.mem_map, List.mem_filter, decide_eq_true_eq]
  aesop

def Context.selectEmbedding (source : Context) (ids : List UID) :
    IdentityEmbedding (source.select ids) source where
  map :=
    { map := fun u => ⟨u.val, ((source.select_support ids u.val).mp u.property).1⟩
      domain := by
        intro u
        obtain ⟨a, ha, hu⟩ := List.mem_map.mp u.property
        have hs := (List.mem_filter.mp ha).1
        exact (source.domain_of_mem _ a hs hu).trans
          ((source.select ids).domain_of_mem u a ha hu).symm }
  uid := fun _ => rfl

theorem IdentityEmbedding.support (e : IdentityEmbedding a source) :
    a.axes.map Axis.uid ⊆ source.axes.map Axis.uid := by
  intro uid h
  have hp := (e.map.map ⟨uid, h⟩).property
  simpa only [e.uid] using hp

/-- Equal UID support of two embedded contexts determines a domain-preserving transport. -/
def IdentityEmbedding.transport (e : IdentityEmbedding a source)
    (f : IdentityEmbedding b source)
    (h : ∀ uid, uid ∈ a.axes.map Axis.uid ↔ uid ∈ b.axes.map Axis.uid) :
    UIDTransport a b where
  equiv :=
    { toFun := fun u => ⟨u.val, (h u.val).mp u.property⟩
      invFun := fun u => ⟨u.val, (h u.val).mpr u.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  domain := by
    intro u
    have hk : f.map.map ⟨u.val, (h u.val).mp u.property⟩ = e.map.map u := by
      apply Subtype.ext
      rw [f.uid, e.uid]
    exact (f.map.domain _).symm.trans (hk ▸ e.map.domain u)

@[simp] theorem IdentityEmbedding.transport_uid (e : IdentityEmbedding a source)
    (f : IdentityEmbedding b source) (h) (u : a.Key) :
    ((e.transport f h).equiv u).val = u.val := rfl

def Ref.lookupWithin (e : IdentityEmbedding c source) (v : UIDVal c)
    (r : Ref source.axes n) (h : r.uid ∈ c.axes.map Axis.uid) : Fin n :=
  Fin.cast (by
    have hk : e.map.map ⟨r.uid, h⟩ = r.key source := by
      apply Subtype.ext
      rw [e.uid, Ref.key_uid]
    exact (e.map.domain _).symm.trans
      (hk ▸ (source.domain_uidEquiv r.index).trans r.index_extent))
    (v ⟨r.uid, h⟩)

def Slots.projectWithin (e : IdentityEmbedding c source) (v : UIDVal c) :
    (slots : Slots source.axes sh) →
    (slots.uids ⊆ c.axes.map Axis.uid) → Coord sh
  | .nil, _ => ()
  | .cons r rest, h =>
    (r.lookupWithin e v (h (by simp [Slots.uids])),
      rest.projectWithin e v (fun _ hu => h (by simp [Slots.uids, hu])))

theorem Slots.projectWithin_transport (e : IdentityEmbedding c source)
    (t : UIDTransport c d) (ht : ∀ u, (t.equiv u).val = u.val)
    (slots : Slots source.axes sh) (localized : Slots d.axes sh)
    (hs : slots.uids ⊆ c.axes.map Axis.uid) (hl : localized.uids = slots.uids)
    (v : UIDVal c) :
    slots.projectWithin e v hs =
      localized.project (uidCoordEquiv d (t.valuationEquiv v)) := by
  induction slots with
  | nil => cases localized; rfl
  | cons r rest ih =>
    cases localized with
    | cons s tail =>
      have hu := (List.cons.inj hl).1
      have hk : t.equiv ⟨r.uid, hs (by simp [Slots.uids])⟩ = s.key d := by
        apply Subtype.ext
        rw [ht, Ref.key_uid, hu]
      apply Prod.ext
      · rw [Slots.projectWithin, Slots.project, Ref.get_uidCoordEquiv]
        apply Fin.ext
        change (v ⟨r.uid, _⟩).val = (t.valuationEquiv v (s.key d)).val
        rw [← hk, UIDTransport.lookup]
      · exact ih tail _ (List.cons.inj hl).2

def Term.globalContext (term : Term source out σ) : Context :=
  source.select (term.sourceReads.flatMap CheckedRead.indices ++ out.axes.map Axis.uid)

def Term.globalEmbedding (term : Term source out σ) :
    IdentityEmbedding term.globalContext source :=
  source.selectEmbedding _

theorem Term.global_support (term : Term source out σ) (uid : UID) :
    uid ∈ term.globalContext.axes.map Axis.uid ↔
      uid ∈ term.support ∨ uid ∈ out.axes.map Axis.uid := by
  rw [Term.globalContext, Context.select_support, term.support_reads, List.mem_append]
  have ho : out.axes.map Axis.uid ⊆ source.axes.map Axis.uid := by
    intro u hu
    apply term.partition.embedding.support
    rw [term.partition.context_axes, List.map_append, List.mem_append]
    exact Or.inl hu
  have hr := term.support_bound (a := uid)
  have hx := ho (a := uid)
  tauto

theorem Term.global_order (term : Term source out σ) :
    term.globalContext.axes = source.axes.filter
      (fun a => a.uid ∈ term.sourceReads.flatMap CheckedRead.indices ∨
        a.uid ∈ out.axes.map Axis.uid) := by
  simp [Term.globalContext, Context.select, List.mem_append]

theorem Term.pure_globalContext (term : Term source out σ)
    (h : term.classification = .pure) :
    term.globalContext = source.select (term.sourceReads.flatMap CheckedRead.indices) := by
  have hp := term.pure_iff.mp h
  have he : term.globalContext.axes =
      (source.select (term.sourceReads.flatMap CheckedRead.indices)).axes := by
    simp only [Term.globalContext, Context.select]
    congr 1
    funext a
    apply decide_eq_decide.mpr
    simp only [List.mem_append, term.support_reads]
    constructor
    · rintro (hr | ho)
      · exact hr
      · exact hp ho
    · exact Or.inl
  exact Context.ext_axes _ _ he

def Term.partitionTransport (term : Term source out σ) :
    UIDTransport term.globalContext term.partition.context :=
  term.globalEmbedding.transport term.partition.embedding (fun uid => by
    rw [term.global_support, term.partition.coverage term.support_bound]
    exact or_comm)

def Term.contractedContext (term : Term source out σ) : Context where
  axes := term.partition.bound
  unique := term.partition.context.unique.sublist (by
    rw [term.partition.context_axes, List.map_append]
    exact List.sublist_append_right ..)

def coordCastEquiv (h : sh = dst) : Coord sh ≃ Coord dst where
  toFun p := h ▸ p
  invFun p := h.symm ▸ p
  left_inv := by cases h; intro p; rfl
  right_inv := by cases h; intro p; rfl

def Term.partitionCoordEquiv (term : Term source out σ) :
    UIDVal term.globalContext ≃ Coord out.axes × Coord term.partition.bound :=
  term.partitionTransport.valuationEquiv.trans
    ((uidCoordEquiv term.partition.context).trans
      ((coordCastEquiv term.partition.context_axes).trans
        (appendEquiv out.axes term.partition.bound)))

/-- A bijection of true UID-dependent valuations, not merely untyped slot values. -/
def Term.partitionEquiv (term : Term source out σ) :
    UIDVal term.globalContext ≃ UIDVal out × UIDVal term.contractedContext :=
  term.partitionCoordEquiv.trans
    (Equiv.prodCongr (uidCoordEquiv out).symm (uidCoordEquiv term.contractedContext).symm)

def Ref.appendLeft : (r : Ref sh n) → Ref (sh ++ tail) n
  | .here => .here
  | .there r => .there r.appendLeft

@[simp] theorem Ref.appendLeft_uid (r : Ref sh n) :
    (r.appendLeft (tail := tail)).uid = r.uid := by
  induction r <;> simp [Ref.appendLeft, Ref.uid, *]

theorem Ref.appendLeft_get (r : Ref sh n) (p : Coord (sh ++ tail)) :
    (r.appendLeft).get p = r.get ((appendEquiv sh tail p).1) := by
  induction r with
  | here => rfl
  | there r ih => exact ih p.2

def Slots.appendLeft : Slots ctx sh → Slots (ctx ++ tail) sh
  | .nil => .nil
  | .cons r rest => .cons r.appendLeft rest.appendLeft

@[simp] theorem Slots.appendLeft_uids (slots : Slots ctx sh) :
    (slots.appendLeft (tail := tail)).uids = slots.uids := by
  induction slots <;> simp [Slots.appendLeft, Slots.uids, *]

theorem Slots.appendLeft_project (slots : Slots ctx sh) (p : Coord (ctx ++ tail)) :
    slots.appendLeft.project p = slots.project ((appendEquiv ctx tail p).1) := by
  induction slots with
  | nil => rfl
  | cons r rest ih =>
    exact Prod.ext (r.appendLeft_get p) ih

theorem Slots.cast_uids (slots : Slots ctx sh) (h : ctx = dst) :
    (h ▸ slots : Slots dst sh).uids = slots.uids := by
  cases h
  rfl

theorem Slots.cast_project (slots : Slots ctx sh) (h : ctx = dst) (p : Coord dst) :
    (h ▸ slots : Slots dst sh).project p = slots.project (h.symm ▸ p) := by
  cases h
  rfl

theorem Term.partition_environment (term : Term source out σ)
    (v : UIDVal term.globalContext) :
    term.environment (term.partitionCoordEquiv v).1 (term.partitionCoordEquiv v).2 =
      uidCoordEquiv term.partition.context (term.partitionTransport.valuationEquiv v) := by
  change ((coordCastEquiv term.partition.context_axes).trans
    (appendEquiv out.axes term.partition.bound)).symm
      (((coordCastEquiv term.partition.context_axes).trans
        (appendEquiv out.axes term.partition.bound))
        (uidCoordEquiv term.partition.context (term.partitionTransport.valuationEquiv v))) = _
  exact Equiv.symm_apply_apply ..

theorem Term.read_global_support (term : Term source out σ) (i : Fin term.sourceReads.length) :
    (term.sourceReads.get i).read.slots.uids ⊆ term.globalContext.axes.map Axis.uid := by
  intro uid hu
  apply (term.global_support uid).mpr
  left
  rw [← term.support_reads]
  apply List.mem_flatMap.mpr
  exact ⟨term.sourceReads.get i, List.get_mem ..,
    (term.sourceReads.get i).linked ▸ hu⟩

variable {K : Type} [Semiring K] {σ : Declarations Unit}

/-- Ordered original reads; repeated factors are deliberately retained. -/
def Term.globalProduct (term : Term source out σ) (ρ : Store (fun _ => K) σ)
    (v : UIDVal term.globalContext) : K :=
  (List.ofFn fun i => ρ ⟨(term.sourceReads.get i).read.tensor,
    (term.sourceReads.get i).read.slots.projectWithin term.globalEmbedding v
      (term.read_global_support i)⟩).prod

theorem Term.output_global_support (output : AdmittedOutput source σ)
    (term : Term source output.context σ) :
    output.sourceSlots.uids ⊆ term.globalContext.axes.map Axis.uid := by
  intro uid hu
  apply (term.global_support uid).mpr
  right
  rw [output.source_linked] at hu
  rw [output.order]
  simpa [firstUIDs] using hu

def Term.globalDestination (output : AdmittedOutput source σ)
    (term : Term source output.context σ) (v : UIDVal term.globalContext) :
    Coord (σ.signature output.tensor).axes :=
  output.sourceSlots.projectWithin term.globalEmbedding v
    (term.output_global_support output)

def Term.globalFiber (output : AdmittedOutput source σ)
    (term : Term source output.context σ) (ρ : Store (fun _ => K) σ)
    (p : Coord (σ.signature output.tensor).axes) : K :=
  ∑ v : UIDVal term.globalContext,
    if Term.globalDestination output term v = p then term.globalProduct ρ v else 0

/-- Re-enumeration (and binder UID transport) changes the enumeration, not the sum. -/
theorem uidFiber_reindex (t : UIDTransport c d) (product : UIDVal c → K)
    (destination : UIDVal c → Coord sh) (p : Coord sh) :
    (∑ v : UIDVal d, if destination (t.valuationEquiv.symm v) = p then
      product (t.valuationEquiv.symm v) else 0) =
    ∑ v : UIDVal c, if destination v = p then product v else 0 :=
  Equiv.sum_comp t.valuationEquiv.symm
    (fun v => if destination v = p then product v else 0)

theorem Term.globalFiber_reenumerate (output : AdmittedOutput source σ)
    (term : Term source output.context σ) (axes : Shape)
    (h : term.globalContext.axes.Perm axes) (ρ : Store (fun _ => K) σ)
    (p : Coord (σ.signature output.tensor).axes) :
    (∑ v : UIDVal (term.globalContext.reenumerate axes h),
      if Term.globalDestination output term
          ((term.globalContext.reenumerateTransport axes h).valuationEquiv.symm v) = p then
        term.globalProduct ρ
          ((term.globalContext.reenumerateTransport axes h).valuationEquiv.symm v) else 0) =
      term.globalFiber output ρ p :=
  uidFiber_reindex (term.globalContext.reenumerateTransport axes h) _ _ p

end LeanNCD.Semantics.Source
