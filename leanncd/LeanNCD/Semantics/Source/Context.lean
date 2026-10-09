import LeanNCD.Semantics.Program
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup

namespace LeanNCD.Semantics.Source

structure Context where
  axes : Shape
  unique : (axes.map Axis.uid).Nodup

inductive Ref : Shape → Nat → Type
  | here {a sh} : Ref (a :: sh) a.extent
  | there {a sh n} : Ref sh n → Ref (a :: sh) n

def Ref.get : Ref sh n → Coord sh → Fin n
  | .here, p => p.1
  | .there i, p => i.get p.2

def Ref.uid : {sh : Shape} → Ref sh n → UID
  | a :: _, .here => a.uid
  | _ :: _, .there i => i.uid

inductive Diagnostic
  | duplicateContext
  | unbound (uid : UID)
  | domain (uid : UID) (expected actual : Nat)
  | rank (expected actual : Nat)
  | unusedBinder (uid : UID)
  | outputContext
  | emptyOperands
  | outputOnly (uid : UID)
  deriving Repr, DecidableEq

def checkContext (sh : Shape) : Except Diagnostic {c : Context // c.axes = sh} :=
  if h : (sh.map Axis.uid).Nodup then .ok ⟨⟨sh, h⟩, rfl⟩ else .error .duplicateContext

def resolveRef : (sh : Shape) → (uid : UID) → (n : Nat) →
    Except Diagnostic (Ref sh n)
  | [], uid, _ => .error (.unbound uid)
  | a :: sh, uid, n =>
    if a.uid = uid then
      if h : a.extent = n then .ok (h ▸ Ref.here)
      else .error (.domain uid n a.extent)
    else (resolveRef sh uid n).map Ref.there

inductive Slots (ctx : Shape) : Shape → Type
  | nil : Slots ctx []
  | cons {a sh} : Ref ctx a.extent → Slots ctx sh → Slots ctx (a :: sh)

def Slots.project : Slots ctx sh → Coord ctx → Coord sh
  | .nil, _ => ()
  | .cons i rest, v => (i.get v, rest.project v)

def resolveSlots (ctx : Shape) : (sh : Shape) → List UID →
    Except Diagnostic (Slots ctx sh)
  | [], [] => .ok .nil
  | a :: sh, uid :: ids => do
      let i ← resolveRef ctx uid a.extent
      let rest ← resolveSlots ctx sh ids
      pure (.cons i rest)
  | sh, ids => .error (.rank sh.length ids.length)

abbrev PositionalVal (sh : Shape) := (i : Fin sh.length) → Fin (sh.get i).extent

def positionalCoordEquiv : (sh : Shape) → PositionalVal sh ≃ Coord sh
  | [] =>
    { toFun := fun _ => ()
      invFun := fun _ i => nomatch i
      left_inv := by intro v; funext i; exact Fin.elim0 i
      right_inv := by intro v; cases v; rfl }
  | _ :: sh =>
    { toFun := fun v => (v 0, (positionalCoordEquiv sh) (fun i => v i.succ))
      invFun := fun p => Fin.cases p.1 ((positionalCoordEquiv sh).symm p.2)
      left_inv := by
        intro v
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact congrFun ((positionalCoordEquiv sh).left_inv (fun i => v i.succ)) j
      right_inv := by
        rintro ⟨i, p⟩
        simp }

abbrev Context.Key (c : Context) := {uid : UID // uid ∈ c.axes.map Axis.uid}

def Context.uidEquiv (c : Context) : Fin c.axes.length ≃ c.Key :=
  (finCongr (List.length_map ..).symm).trans (c.unique.getEquiv _)

@[simp] theorem Context.uidEquiv_val (c : Context) (i : Fin c.axes.length) :
    (c.uidEquiv i).val = (c.axes.get i).uid := by
  simp [Context.uidEquiv, List.get_eq_getElem]

def Context.domain (c : Context) (u : c.Key) : Nat :=
  (c.axes.get (c.uidEquiv.symm u)).extent

@[simp] theorem Context.domain_uidEquiv (c : Context) (i : Fin c.axes.length) :
    c.domain (c.uidEquiv i) = (c.axes.get i).extent := by
  simp [Context.domain]

abbrev UIDVal (c : Context) := (u : c.Key) → Fin (c.domain u)

def uidPositionalEquiv (c : Context) : UIDVal c ≃ PositionalVal c.axes where
  toFun v i := Fin.cast (c.domain_uidEquiv i) (v (c.uidEquiv i))
  invFun v u := v (c.uidEquiv.symm u)
  left_inv := by
    intro v
    funext u
    apply Fin.ext
    exact congrArg (fun u => (v u).val) (c.uidEquiv.apply_symm_apply u)
  right_inv := by
    intro v
    funext i
    apply Fin.ext
    exact congrArg (fun i => (v i).val) (c.uidEquiv.symm_apply_apply i)

def uidCoordEquiv (c : Context) : UIDVal c ≃ Coord c.axes :=
  (uidPositionalEquiv c).trans (positionalCoordEquiv c.axes)

@[simp] theorem uidCoordEquiv_left (c : Context) (v : UIDVal c) :
    (uidCoordEquiv c).symm (uidCoordEquiv c v) = v :=
  (uidCoordEquiv c).symm_apply_apply v

@[simp] theorem uidCoordEquiv_right (c : Context) (p : Coord c.axes) :
    uidCoordEquiv c ((uidCoordEquiv c).symm p) = p :=
  (uidCoordEquiv c).apply_symm_apply p

def Ref.index : {sh : Shape} → Ref sh n → Fin sh.length
  | _ :: _, .here => 0
  | _ :: _, .there r => r.index.succ

@[simp] theorem Ref.index_uid (r : Ref sh n) : (sh.get r.index).uid = r.uid := by
  induction r with
  | here => rfl
  | there r ih => simpa [Ref.index, Ref.uid, List.get_eq_getElem] using ih

@[simp] theorem Ref.index_extent (r : Ref sh n) : (sh.get r.index).extent = n := by
  induction r with
  | here => rfl
  | there r ih => simpa [Ref.index, List.get_eq_getElem] using ih

def Ref.key (c : Context) (r : Ref c.axes n) : c.Key := c.uidEquiv r.index

@[simp] theorem Ref.key_uid (c : Context) (r : Ref c.axes n) :
    (r.key c).val = r.uid :=
  (c.uidEquiv_val r.index).trans r.index_uid

def UIDVal.lookupRef (v : UIDVal c) (r : Ref c.axes n) : Fin n :=
  Fin.cast ((c.domain_uidEquiv r.index).trans r.index_extent) (v (r.key c))

theorem Ref.get_positionalCoordEquiv (r : Ref sh n) (v : PositionalVal sh) :
    r.get (positionalCoordEquiv sh v) = Fin.cast r.index_extent (v r.index) := by
  apply Fin.ext
  induction r with
  | here => rfl
  | there r ih => exact ih (fun i => v i.succ)

theorem Ref.get_uidCoordEquiv (c : Context) (r : Ref c.axes n) (v : UIDVal c) :
    r.get (uidCoordEquiv c v) = v.lookupRef r := by
  rw [uidCoordEquiv, Equiv.trans_apply, Ref.get_positionalCoordEquiv]
  apply Fin.ext
  rfl

theorem Ref.sameUID_lookup (c : Context) (r : Ref c.axes n) (s : Ref c.axes m)
    (v : UIDVal c) (h : r.uid = s.uid) :
    (v.lookupRef r).val = (v.lookupRef s).val := by
  have hk : r.key c = s.key c := Subtype.ext (by simpa using h)
  exact congrArg (fun u => (v u).val) hk

structure IndexMap (src dst : Context) where
  map : src.Key → dst.Key
  domain : ∀ u, dst.domain (map u) = src.domain u

def indexPullback (m : IndexMap src dst) (v : UIDVal dst) : UIDVal src :=
  fun u => Fin.cast (m.domain u) (v (m.map u))

def IndexMap.id (c : Context) : IndexMap c c := ⟨fun u => u, fun _ => rfl⟩

def IndexMap.comp (m : IndexMap a b) (n : IndexMap b c) : IndexMap a c :=
  ⟨fun u => n.map (m.map u), fun u => (n.domain (m.map u)).trans (m.domain u)⟩

@[simp] theorem indexPullback_id (c : Context) (v : UIDVal c) :
    indexPullback (IndexMap.id c) v = v := rfl

theorem indexPullback_comp (m : IndexMap a b) (n : IndexMap b c) (v : UIDVal c) :
    indexPullback (m.comp n) v = indexPullback m (indexPullback n v) := by
  funext u
  apply Fin.ext
  rfl

@[simp] theorem indexPullback_lookup (m : IndexMap src dst) (v : UIDVal dst)
    (u : src.Key) :
    (indexPullback m v u).val = (v (m.map u)).val := rfl

theorem indexPullback_repeated (m : IndexMap src dst) (v : UIDVal dst)
    (u w : src.Key) (h : m.map u = m.map w) :
    (indexPullback m v u).val = (indexPullback m v w).val := by
  exact congrArg (fun u => (v u).val) h

def resolveUID (c : Context) (uid : UID) (n : Nat) :
    Except Diagnostic {u : c.Key // u.val = uid ∧ c.domain u = n} :=
  if h : uid ∈ c.axes.map Axis.uid then
    let u : c.Key := ⟨uid, h⟩
    if hd : c.domain u = n then .ok ⟨u, rfl, hd⟩
    else .error (.domain uid n (c.domain u))
  else .error (.unbound uid)

private def resolveBindings (dst : Context) (f : UID → UID) :
    (sh : Shape) → Except Diagnostic
      ((i : Fin sh.length) → {u : dst.Key //
        u.val = f (sh.get i).uid ∧ dst.domain u = (sh.get i).extent})
  | [] => .ok (fun i => nomatch i)
  | a :: sh => do
      let u ← resolveUID dst (f a.uid) a.extent
      let rest ← resolveBindings dst f sh
      pure (Fin.cases u rest)

def resolveIndexMap (src dst : Context) (f : UID → UID) :
    Except Diagnostic (IndexMap src dst) := do
  let bindings ← resolveBindings dst f src.axes
  pure {
    map := fun u => (bindings (src.uidEquiv.symm u)).val
    domain := fun u => (bindings (src.uidEquiv.symm u)).property.2
  }

theorem resolveIndexMap_uid (src dst : Context) (f : UID → UID)
    (m : IndexMap src dst) (h : resolveIndexMap src dst f = .ok m) (u : src.Key) :
    (m.map u).val = f u.val := by
  have hu : (src.axes.get (src.uidEquiv.symm u)).uid = u.val := by
    simpa using (src.uidEquiv_val (src.uidEquiv.symm u)).symm
  cases hb : resolveBindings dst f src.axes with
  | error e => simp [resolveIndexMap, hb] at h
  | ok bindings =>
    simp [resolveIndexMap, hb] at h
    subst m
    exact (bindings (src.uidEquiv.symm u)).property.1.trans
      (congrArg f hu)

structure UIDTransport (src dst : Context) where
  equiv : src.Key ≃ dst.Key
  domain : ∀ u, dst.domain (equiv u) = src.domain u

def UIDTransport.indexMap (t : UIDTransport src dst) : IndexMap src dst :=
  ⟨t.equiv, t.domain⟩

def UIDTransport.valuationEquiv (t : UIDTransport src dst) : UIDVal src ≃ UIDVal dst where
  toFun v u := Fin.cast (by simpa using (t.domain (t.equiv.symm u)).symm)
    (v (t.equiv.symm u))
  invFun := indexPullback t.indexMap
  left_inv := by
    intro v
    funext u
    apply Fin.ext
    exact congrArg (fun u => (v u).val) (t.equiv.symm_apply_apply u)
  right_inv := by
    intro v
    funext u
    apply Fin.ext
    exact congrArg (fun u => (v u).val) (t.equiv.apply_symm_apply u)

@[simp] theorem UIDTransport.lookup (t : UIDTransport src dst) (v : UIDVal src)
    (u : src.Key) :
    (t.valuationEquiv v (t.equiv u)).val = (v u).val := by
  exact congrArg (fun u => (v u).val) (t.equiv.symm_apply_apply u)

theorem Context.domain_of_mem (c : Context) (u : c.Key) (a : Axis)
    (ha : a ∈ c.axes) (hu : a.uid = u.val) : c.domain u = a.extent := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
  have hi : c.uidEquiv i = u := Subtype.ext (by simpa using hu)
  simpa [hi] using c.domain_uidEquiv i

def Context.reenumerate (c : Context) (axes : Shape) (p : c.axes.Perm axes) : Context :=
  ⟨axes, (p.map Axis.uid).nodup_iff.mp c.unique⟩

def Context.reenumerateTransport (c : Context) (axes : Shape) (p : c.axes.Perm axes) :
    UIDTransport c (c.reenumerate axes p) where
  equiv :=
    { toFun := fun u => ⟨u.val, (p.map Axis.uid).mem_iff.mp u.property⟩
      invFun := fun u => ⟨u.val, (p.map Axis.uid).mem_iff.mpr u.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  domain := by
    intro u
    obtain ⟨a, ha, hu⟩ := List.mem_map.mp u.property
    exact ((c.reenumerate axes p).domain_of_mem _ a (p.mem_iff.mp ha) hu).trans
      (c.domain_of_mem u a ha hu).symm

def Context.mapUID (c : Context) (f : UID → UID)
    (hf : ∀ u ∈ c.axes.map Axis.uid, ∀ w ∈ c.axes.map Axis.uid, f u = f w → u = w) :
    Context where
  axes := c.axes.map (fun a => { a with uid := f a.uid })
  unique := by
    simpa [List.map_map, Function.comp_def] using c.unique.map_on hf

def Context.mapUIDTransport (c : Context) (f : UID → UID)
    (hf : ∀ u ∈ c.axes.map Axis.uid, ∀ w ∈ c.axes.map Axis.uid, f u = f w → u = w) :
    UIDTransport c (c.mapUID f hf) where
  equiv := c.uidEquiv.symm.trans
    ((finCongr (by simp [Context.mapUID])).trans (c.mapUID f hf).uidEquiv)
  domain := by
    intro u
    change (c.mapUID f hf).domain
      ((c.mapUID f hf).uidEquiv ((finCongr _) (c.uidEquiv.symm u))) = c.domain u
    rw [Context.domain_uidEquiv]
    simp [Context.mapUID, Context.domain, List.get_eq_getElem, finCongr]
    rfl

@[simp] theorem Context.mapUIDTransport_uid (c : Context) (f : UID → UID) (hf)
    (u : c.Key) : ((c.mapUIDTransport f hf).equiv u).val = f u.val := by
  have hu := c.uidEquiv_val (c.uidEquiv.symm u)
  simp only [Equiv.apply_symm_apply] at hu
  change ((c.mapUID f hf).uidEquiv ((finCongr _) (c.uidEquiv.symm u))).val = f u.val
  rw [Context.uidEquiv_val]
  simpa [Context.mapUID, List.get_eq_getElem, finCongr] using
    congrArg f hu.symm

structure BinderScope (c : Context) where
  source : List UID
  output : List UID
  free : List UID
  generated : List UID
  covers : ∀ u : c.Key, u.val ∈ source ++ output ++ free ++ generated
  generatedOnly : ∀ u ∈ generated, u ∉ source ++ output ++ free

def BinderScope.support (s : BinderScope c) : List UID :=
  s.source ++ s.output ++ s.free ++ s.generated

private def freshBase : List UID → UID
  | [] => 0
  | u :: us => max (u + 1) (freshBase us)

private theorem lt_freshBase (u : UID) (us : List UID) (h : u ∈ us) :
    u < freshBase us := by
  simp only [UID] at *
  induction us with
  | nil => simp at h
  | cons w ws ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [freshBase]; omega
    · have := ih h
      simp only [freshBase]
      omega

def BinderScope.renameUID (s : BinderScope c) (u : UID) : UID :=
  if u ∈ s.generated then freshBase s.support + u else u

theorem BinderScope.fresh (s : BinderScope c) (u : UID) (h : u ∈ s.generated) :
    s.renameUID u ∉ s.support := by
  intro hm
  have := lt_freshBase (s.renameUID u) s.support hm
  simp only [BinderScope.renameUID, if_pos h] at this
  simp only [UID] at *
  omega

theorem BinderScope.fixed (s : BinderScope c) (u : UID) (h : u ∉ s.generated) :
    s.renameUID u = u := by simp [BinderScope.renameUID, h]

theorem BinderScope.protected (s : BinderScope c) (u : UID)
    (h : u ∈ s.source ++ s.output ++ s.free) : s.renameUID u = u := by
  apply s.fixed
  intro hg
  exact s.generatedOnly u hg h

theorem BinderScope.injective (s : BinderScope c) :
    ∀ u ∈ c.axes.map Axis.uid, ∀ w ∈ c.axes.map Axis.uid,
      s.renameUID u = s.renameUID w → u = w := by
  intro u hu w hw heq
  have hu' := lt_freshBase u s.support (s.covers ⟨u, hu⟩)
  have hw' := lt_freshBase w s.support (s.covers ⟨w, hw⟩)
  unfold BinderScope.renameUID at heq
  simp only [UID] at *
  split_ifs at heq <;> omega

def renameBinders (c : Context) (s : BinderScope c) : Context :=
  c.mapUID s.renameUID s.injective

def binderTransport (c : Context) (s : BinderScope c) :
    UIDTransport c (renameBinders c s) :=
  c.mapUIDTransport s.renameUID s.injective

theorem renameBinders_noCapture (c : Context) (s : BinderScope c) (u : c.Key)
    (h : u.val ∈ s.generated) :
    ((binderTransport c s).equiv u).val ∉ s.support := by
  change ((c.mapUIDTransport s.renameUID s.injective).equiv u).val ∉ s.support
  rw [Context.mapUIDTransport_uid]
  exact s.fresh u.val h

theorem renameBinders_fixed (c : Context) (s : BinderScope c) (u : c.Key)
    (h : u.val ∉ s.generated) :
    ((binderTransport c s).equiv u).val = u.val := by
  change ((c.mapUIDTransport s.renameUID s.injective).equiv u).val = u.val
  rw [Context.mapUIDTransport_uid]
  exact s.fixed u.val h

theorem renameBinders_lookup (c : Context) (s : BinderScope c) (v : UIDVal c)
    (u : c.Key) :
    ((binderTransport c s).valuationEquiv v ((binderTransport c s).equiv u)).val =
      (v u).val :=
  (binderTransport c s).lookup v u

abbrev BinderScope.RequestFresh (s : BinderScope c) (request : UID → UID) : Prop :=
  (s.generated.dedup.map request).Nodup ∧ ∀ u ∈ s.generated, request u ∉ s.support

theorem BinderScope.requestFresh_of_injective (s : BinderScope c) (request : UID → UID)
    (hi : ∀ u ∈ s.generated, ∀ w ∈ s.generated, request u = request w → u = w)
    (hf : ∀ u ∈ s.generated, request u ∉ s.support) : s.RequestFresh request := by
  have hn : s.generated.dedup.Nodup := List.nodup_dedup _
  refine ⟨hn.map_on ?_, hf⟩
  intro u hu w hw heq
  exact hi u (List.mem_dedup.mp hu) w (List.mem_dedup.mp hw) heq

/-- Honor the whole generated request only if injective and fresh; otherwise use
the automatic freshening for every generated binder. Nongenerated UIDs stay fixed. -/
def BinderScope.requestedUID (s : BinderScope c) (request : UID → UID) (u : UID) : UID :=
  if s.RequestFresh request then
    if u ∈ s.generated then request u else u
  else s.renameUID u

theorem BinderScope.requestedUID_honored (s : BinderScope c) (request : UID → UID)
    (h : s.RequestFresh request) (u : UID) (hg : u ∈ s.generated) :
    s.requestedUID request u = request u := by
  simp only [BinderScope.requestedUID, if_pos h, if_pos hg]

theorem BinderScope.requestedUID_fallback (s : BinderScope c) (request : UID → UID)
    (h : ¬s.RequestFresh request) (u : UID) :
    s.requestedUID request u = s.renameUID u := by
  simp only [BinderScope.requestedUID, if_neg h]

theorem BinderScope.requested_fixed (s : BinderScope c) (request : UID → UID)
    (u : UID) (h : u ∉ s.generated) : s.requestedUID request u = u := by
  by_cases hf : s.RequestFresh request
  · simp only [BinderScope.requestedUID, if_pos hf, if_neg h]
  · rw [s.requestedUID_fallback request hf u]
    exact s.fixed u h

theorem BinderScope.requested_protected (s : BinderScope c) (request : UID → UID)
    (u : UID) (h : u ∈ s.source ++ s.output ++ s.free) :
    s.requestedUID request u = u := by
  apply s.requested_fixed
  intro hg
  exact s.generatedOnly u hg h

theorem BinderScope.requested_fresh (s : BinderScope c) (request : UID → UID)
    (u : UID) (hg : u ∈ s.generated) : s.requestedUID request u ∉ s.support := by
  by_cases hf : s.RequestFresh request
  · rw [s.requestedUID_honored request hf u hg]
    exact hf.2 u hg
  · rw [s.requestedUID_fallback request hf u]
    exact s.fresh u hg

theorem BinderScope.requested_injective (s : BinderScope c) (request : UID → UID) :
    ∀ u ∈ c.axes.map Axis.uid, ∀ w ∈ c.axes.map Axis.uid,
      s.requestedUID request u = s.requestedUID request w → u = w := by
  by_cases hf : s.RequestFresh request
  · intro u hu w hw heq
    by_cases hg : u ∈ s.generated <;> by_cases hwg : w ∈ s.generated
    · simp only [BinderScope.requestedUID, if_pos hf, if_pos hg, if_pos hwg] at heq
      exact (List.inj_on_of_nodup_map hf.1)
        (List.mem_dedup.mpr hg) (List.mem_dedup.mpr hwg) heq
    · simp only [BinderScope.requestedUID, if_pos hf, if_pos hg, if_neg hwg] at heq
      exact False.elim (hf.2 u hg (heq.symm ▸ s.covers ⟨w, hw⟩))
    · simp only [BinderScope.requestedUID, if_pos hf, if_neg hg, if_pos hwg] at heq
      exact False.elim (hf.2 w hwg (heq ▸ s.covers ⟨u, hu⟩))
    · simpa only [BinderScope.requestedUID, if_pos hf, if_neg hg, if_neg hwg] using heq
  · simpa only [BinderScope.requestedUID, if_neg hf] using s.injective

def renameBindersRequested (c : Context) (s : BinderScope c) (request : UID → UID) :
    Context :=
  c.mapUID (s.requestedUID request) (s.requested_injective request)

def requestedBinderTransport (c : Context) (s : BinderScope c) (request : UID → UID) :
    UIDTransport c (renameBindersRequested c s request) :=
  c.mapUIDTransport (s.requestedUID request) (s.requested_injective request)

theorem requestedBinders_noCapture (c : Context) (s : BinderScope c)
    (request : UID → UID) (u : c.Key) (h : u.val ∈ s.generated) :
    ((requestedBinderTransport c s request).equiv u).val ∉ s.support := by
  change ((c.mapUIDTransport _ _).equiv u).val ∉ s.support
  rw [Context.mapUIDTransport_uid]
  exact s.requested_fresh request u.val h

theorem requestedBinders_protected (c : Context) (s : BinderScope c)
    (request : UID → UID) (u : c.Key) (h : u.val ∈ s.source ++ s.output ++ s.free) :
    ((requestedBinderTransport c s request).equiv u).val = u.val := by
  change ((c.mapUIDTransport _ _).equiv u).val = u.val
  rw [Context.mapUIDTransport_uid]
  exact s.requested_protected request u.val h

theorem requestedBinders_lookup (c : Context) (s : BinderScope c)
    (request : UID → UID) (v : UIDVal c) (u : c.Key) :
    ((requestedBinderTransport c s request).valuationEquiv v
      ((requestedBinderTransport c s request).equiv u)).val = (v u).val :=
  (requestedBinderTransport c s request).lookup v u

def appendEquiv : (out rest : Shape) → Coord (out ++ rest) ≃ Coord out × Coord rest
  | [], _ =>
    { toFun := fun p => ((), p)
      invFun := Prod.snd
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨u, p⟩; cases u; rfl }
  | a :: out, rest =>
    { toFun := fun p => let q := appendEquiv out rest p.2; ((p.1, q.1), q.2)
      invFun := fun p => (p.1.1, (appendEquiv out rest).symm (p.1.2, p.2))
      left_inv := by intro p; simp
      right_inv := by rintro ⟨⟨i, o⟩, c⟩; simp }

def strictResolve : (sh : Shape) → RawCoord sh → ReadOutcome K (Coord sh)
  | [], _ => .at ()
  | a :: sh, raw =>
    if h : 0 ≤ raw 0 ∧ raw 0 < a.extent then
      match strictResolve (K := K) sh (fun i => raw i.succ) with
      | .at p => .at (⟨(raw 0).toNat, by omega⟩, p)
      | _ => .reject
    else .reject

def strictPolicy (sh : Shape) : ReadPolicy K sh where
  resolve := strictResolve sh
  inBounds := by
    intro p
    induction sh with
    | nil => cases p; rfl
    | cons a sh ih =>
      rcases p with ⟨i, p⟩
      simp [strictResolve, Coord.raw, ih p]

end LeanNCD.Semantics.Source
