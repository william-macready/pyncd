import LeanNCD.Semantics.Plan.Simulation

/- Definition 31.1 (valid plan), slice-1 form, and its computable check.
   `Valid` restates the static part of 31.1 as named fields (the A2
   ValidityConditions list); `checkPlan` decides it by list recursion only.
   Coverage completeness, condition 4 and layout safety enumerate occurrences,
   addresses and both resource kinds from the plan's certified `tensors` list
   and canonical coordinate layouts, never from the noncomputable
   `definedFintype`/`definedAddressFintype` instances. -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r} (π : P.Plan)

/-- Spec 29.3 condition 3 for one group: every address a member body reads is
    in `Live pc` (inputs, or published and not retired by the prefix). A PROGRESS
    condition; over `Live` it also enforces "no remaining reader" of a retired address. -/
def ReadyOK (pc : Nat) (G : List (OccRef P)) : Prop :=
  ∀ x ∈ G, ∀ a ∈ footprint (P.body x.1 x.2.1) x.2.2, π.Live pc a

section Validity

variable [DecidableEq σ.Tensor]

/-- Definition 31.1, slice-1 form (singleton commands, initZero/acc/pub/retire).
    `tensors_nodup`/`tensors_complete` are fields of the plan itself. -/
structure Valid : Prop where
  /-- Slice-1 profile: every command is one annotation. -/
  singleton : π.Singleton
  /-- Spec 29.3 condition 1 (groups duplicate-free, disjoint, covering `𝒪_P`). -/
  coverage1 : π.Coverage1
  /-- Spec 29.3 condition 2 (blocks duplicate-free, disjoint, covering `Addr_Def`). -/
  coverage2 : π.Coverage2
  /-- `InitOK` (N2): initZero targets unpublished, unconsumed-into addresses. -/
  initFresh : ∀ pc S, π.commands[pc]? = some [.initZero S] → π.InitOK pc S
  /-- `AccOK`: group duplicate-free, unconsumed, destinations materialised. -/
  accOK : ∀ pc G, π.commands[pc]? = some [.acc G] → π.AccOK pc G
  /-- `PubOK`: block duplicate-free, unpublished, materialised (N1), and every
      occurrence targeting a member already consumed (spec 29.3 condition 4). -/
  pubOK : ∀ pc B, π.commands[pc]? = some [.pub B] → π.PubOK pc B
  /-- Spec 29.3 condition 3 (N3): every read footprint is in `Live pc`. -/
  ready : ∀ pc G, π.commands[pc]? = some [.acc G] → π.ReadyOK pc G
  /-- `RetOK`: retired members are live and not outputs. -/
  retOK : ∀ pc B, π.commands[pc]? = some [.retire B] → π.RetOK pc B
  /-- Every boundary, including the initial and final boundary, has no live aliases. -/
  layout : ∀ pc, pc ≤ π.commands.length → π.LayoutOK pc

theorem Valid.stepOK {π : P.Plan} (h : π.Valid) (pc : Nat) : π.StepOK pc := by
  intro a ha
  cases a with
  | initZero S => exact h.initFresh pc S ha
  | acc G => exact h.accOK pc G ha
  | pub B => exact h.pubOK pc B ha
  | retire B => exact h.retOK pc B ha

/-- Layout safety on both sides of an existing singleton annotation. -/
theorem Valid.layout_boundary {π : P.Plan} (h : π.Valid) {pc : Nat} {a : Ann P}
    (ha : π.commands[pc]? = some [a]) : π.LayoutOK pc ∧ π.LayoutOK (pc + 1) := by
  have hlt := (List.getElem?_eq_some_iff.mp ha).1
  exact ⟨h.layout pc (Nat.le_of_lt hlt), h.layout (pc + 1) hlt⟩

end Validity

/-! ### Enumerations derived from the certified tensor list -/

/-- Every tagged occurrence, enumerated from `π.tensors`. -/
def occList : List (OccRef P) :=
  π.tensors.flatMap fun t =>
    if h : P.input t = false then
      (List.finRange (P.statements ⟨t, h⟩)).flatMap fun s =>
        (List.finRange (P.valuations ⟨t, h⟩ s)).filterMap fun v =>
          if hg : P.guard ⟨t, h⟩ s v = true then some ⟨⟨t, h⟩, ⟨s, ⟨v, hg⟩⟩⟩ else none
    else []

theorem mem_occList (x : OccRef P) : x ∈ π.occList := by
  obtain ⟨⟨t, h⟩, ⟨s, ⟨v, hg⟩⟩⟩ := x
  simp only [occList, List.mem_flatMap]
  refine ⟨t, π.tensors_complete t, ?_⟩
  rw [dif_pos h]
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and]
  exact ⟨s, v, by rw [dif_pos hg]⟩

/-- Every defined address, enumerated from `π.tensors` and the canonical layout. -/
def addrList : List (DefAddr P) :=
  π.tensors.flatMap fun t =>
    if h : P.input t = false then
      (List.finRange (canonicalLayout (σ.signature t).axes).count).map fun i =>
        ⟨⟨t, h⟩, (canonicalLayout (σ.signature t).axes).enumerate i⟩
    else []

theorem mem_addrList (x : DefAddr P) : x ∈ π.addrList := by
  obtain ⟨⟨t, h⟩, p⟩ := x
  simp only [addrList, List.mem_flatMap]
  refine ⟨t, π.tensors_complete t, ?_⟩
  rw [dif_pos h]
  simp only [List.mem_map, List.mem_finRange, true_and]
  exact ⟨(canonicalLayout (σ.signature t).axes).enumerate.symm p, by simp⟩

/-- All addresses, including supplied inputs and empty-domain tensors. -/
def allAddrList : List (Address σ) :=
  π.tensors.flatMap fun t =>
    (List.finRange (canonicalLayout (σ.signature t).axes).count).map fun i =>
      ⟨t, (canonicalLayout (σ.signature t).axes).enumerate i⟩

theorem mem_allAddrList (a : Address σ) : a ∈ π.allAddrList := by
  obtain ⟨t, p⟩ := a
  simp only [allAddrList, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨t, π.tensors_complete t,
    (canonicalLayout (σ.signature t).axes).enumerate.symm p, by simp⟩

/-- Both resource kinds are enumerated; inactive resources reserve no storage. -/
def resourceList : List (Resource P) :=
  π.allAddrList.map Resource.pub ++ π.addrList.map Resource.acc

theorem mem_resourceList (res : Resource P) : res ∈ π.resourceList := by
  cases res with
  | pub a => exact List.mem_append_left _ (List.mem_map_of_mem (π.mem_allAddrList a))
  | acc x => exact List.mem_append_right _ (List.mem_map_of_mem (π.mem_addrList x))

/-! ### The computable check (one Bool per Valid clause) -/

section Check

variable [DecidableEq σ.Tensor]
local instance coordEqInst (sh : Shape) : DecidableEq (Coord sh) := coordDecidableEq sh
local instance resourceEqInst : DecidableEq (Resource P) := fun a b => by
  cases a <;> cases b <;>
    simp only [Resource.pub.injEq, Resource.acc.injEq, reduceCtorEq] <;> infer_instance

/-- Check every pub/pub, pub/acc and acc/acc pair at one boundary. -/
def checkLayoutAt (pc : Nat) : Bool :=
  π.resourceList.all fun a => π.resourceList.all fun b =>
    decide ((π.SlotView pc a).isSome = true →
      π.SlotView pc a = π.SlotView pc b → a = b)

theorem checkLayoutAt_iff (pc : Nat) : π.checkLayoutAt pc = true ↔ π.LayoutOK pc := by
  simp only [checkLayoutAt, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h a b ξ ha hb
    exact h a (π.mem_resourceList a) b (π.mem_resourceList b)
      (by rw [ha]; rfl) (ha.trans hb.symm)
  · intro h a _ b _ hs he
    obtain ⟨ξ, hξ⟩ := Option.isSome_iff_exists.mp hs
    exact h a b ξ hξ (he ▸ hξ)

def checkLayouts : Bool :=
  (List.range (π.commands.length + 1)).all fun pc => π.checkLayoutAt pc

theorem checkLayouts_iff : π.checkLayouts = true ↔
    ∀ pc, pc ≤ π.commands.length → π.LayoutOK pc := by
  simp only [checkLayouts, List.all_eq_true, List.mem_range, checkLayoutAt_iff]
  constructor
  · intro h pc hp
    exact h pc (by omega)
  · intro h pc hp
    exact h pc (by omega)

def checkSingleton : Bool := π.commands.all fun cmd => cmd.length == 1

def checkCov1Nodup : Bool := decide π.accFlat.Nodup
def checkCov1Complete : Bool := π.occList.all fun x => decide (x ∈ π.accFlat)
def checkCov2Nodup : Bool := decide π.pubFlat.Nodup
def checkCov2Complete : Bool := π.addrList.all fun x => decide (x ∈ π.pubFlat)

/-- `InitOK` (N2): no member is published, and no consumed occurrence targets it. -/
def checkInit (pc : Nat) (S : List (DefAddr P)) : Bool :=
  S.all fun x => !decide (π.Pub pc x.addr) && (π.consList pc).all fun y => decide (y.target ≠ x)

/-- `AccOK`, first half: duplicate-free and unconsumed. -/
def checkAccFresh (pc : Nat) (G : List (OccRef P)) : Bool :=
  decide G.Nodup && G.all fun x => !decide (π.Cons pc x)

/-- `AccOK`, second half: every destination materialised. -/
def checkAccMat (pc : Nat) (G : List (OccRef P)) : Bool :=
  G.all fun x => decide (π.Mat pc x.target)

/-- Condition 3 (progress), over `Live`. -/
def checkReady (pc : Nat) (G : List (OccRef P)) : Bool :=
  G.all fun x => (footprint (P.body x.1 x.2.1) x.2.2).all fun a => decide (π.Live pc a)

/-- `PubOK`, first part: duplicate-free and unpublished. -/
def checkPubFresh (pc : Nat) (B : List (DefAddr P)) : Bool :=
  decide B.Nodup && B.all fun x => !decide (π.Pub pc x.addr)

/-- `PubOK`, N1: every member materialised. -/
def checkPubMat (pc : Nat) (B : List (DefAddr P)) : Bool :=
  B.all fun x => decide (π.Mat pc x)

/-- `PubOK`, condition 4: every occurrence targeting a member is consumed. -/
def checkPubOrder (pc : Nat) (B : List (DefAddr P)) : Bool :=
  B.all fun x => π.occList.all fun y => !decide (y.target = x) || decide (π.Cons pc y)

/-- `RetOK`: every member is live and not an output. -/
def checkRet (pc : Nat) (B : List (DefAddr P)) : Bool :=
  B.all fun x => decide (π.Live pc x.addr) && decide (P.output x.1.val = false)

def checkAnn (pc : Nat) : Ann P → Bool
  | .initZero S => π.checkInit pc S
  | .acc G => π.checkAccFresh pc G && π.checkAccMat pc G && π.checkReady pc G
  | .pub B => π.checkPubFresh pc B && π.checkPubMat pc B && π.checkPubOrder pc B
  | .retire B => π.checkRet pc B

def checkSteps : Bool :=
  (List.range π.commands.length).all fun pc =>
    match π.commands[pc]? with
    | some [a] => π.checkAnn pc a
    | _ => true

def checkPlan : Bool :=
  π.checkSingleton && π.checkCov1Nodup && π.checkCov1Complete &&
    π.checkCov2Nodup && π.checkCov2Complete && π.checkSteps && π.checkLayouts

/-! ### Soundness -/

theorem checkSteps_ann (h : π.checkSteps = true) {pc : Nat} {a : Ann P}
    (ha : π.commands[pc]? = some [a]) : π.checkAnn pc a = true := by
  have hlt : pc < π.commands.length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
    exact hlt
  simp only [checkSteps, List.all_eq_true] at h
  have := h pc (List.mem_range.mpr hlt)
  rw [ha] at this
  exact this

omit [DecidableEq σ.Tensor] in
theorem target_eq {t : P.Defined} (o : P.Occurrence t) (p : Coord (σ.signature t.val).axes) :
    OccRef.target (⟨t, o⟩ : OccRef P) = (⟨t, p⟩ : DefAddr P) ↔ P.destination t o.1 o.2 = p := by
  simp [OccRef.target]

theorem checkInit_sound {pc : Nat} {S : List (DefAddr P)} (h : π.checkInit pc S = true) :
    π.InitOK pc S := by
  simp only [checkInit, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  rintro ⟨t, p⟩ hx
  obtain ⟨hp, hc⟩ := h _ hx
  refine ⟨hp, fun o ho hd => hc ⟨t, o⟩ ho ((target_eq o p).mpr hd)⟩

theorem checkRet_sound {pc : Nat} {B : List (DefAddr P)} (h : π.checkRet pc B = true) :
    π.RetOK pc B := by
  simp only [checkRet, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem checkAnn_acc_sound {pc : Nat} {G : List (OccRef P)}
    (h : π.checkAnn pc (.acc G) = true) : π.AccOK pc G ∧ π.ReadyOK pc G := by
  simp only [checkAnn, checkAccFresh, checkAccMat, checkReady, List.all_eq_true,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, hc⟩, hm⟩, hr⟩ := h
  exact ⟨⟨hn, fun x hx => ⟨hc x hx, hm x hx⟩⟩, hr⟩

theorem checkAnn_pub_sound {pc : Nat} {B : List (DefAddr P)}
    (h : π.checkAnn pc (.pub B) = true) : π.PubOK pc B := by
  simp only [checkAnn, checkPubFresh, checkPubMat, checkPubOrder, List.all_eq_true,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨hn, hp⟩, hm⟩, ho⟩ := h
  refine ⟨hn, ?_⟩
  rintro ⟨t, p⟩ hx
  refine ⟨hp _ hx, hm _ hx, fun o hd => ?_⟩
  rcases ho _ hx ⟨t, o⟩ (π.mem_occList _) with hne | hcons
  · exact absurd ((target_eq o p).mpr hd) (by simpa using hne)
  · exact hcons

/-- `checkPlan` is sound for Definition 31.1 (slice-1 form). -/
theorem checkPlan_sound (h : π.checkPlan = true) : π.Valid := by
  simp only [checkPlan, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hs, h1n⟩, h1c⟩, h2n⟩, h2c⟩, hst⟩, hl⟩ := h
  simp only [checkSingleton, checkCov1Nodup, checkCov1Complete, checkCov2Nodup,
    checkCov2Complete, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hs h1n h1c h2n h2c
  refine ⟨fun cmd hc => List.length_eq_one_iff.mp (hs cmd hc),
    ⟨h1n, fun x => h1c x (π.mem_occList x)⟩, ⟨h2n, fun x => h2c x (π.mem_addrList x)⟩,
    fun pc S ha => π.checkInit_sound (π.checkSteps_ann hst ha),
    fun pc G ha => (π.checkAnn_acc_sound (π.checkSteps_ann hst ha)).1,
    fun pc B ha => π.checkAnn_pub_sound (π.checkSteps_ann hst ha),
    fun pc G ha => (π.checkAnn_acc_sound (π.checkSteps_ann hst ha)).2,
    fun pc B ha => π.checkRet_sound (π.checkSteps_ann hst ha),
    π.checkLayouts_iff.mp hl⟩

/-! ### Redundancy of the coverage `Nodup` checks (plan §10 item 3)

In the singleton profile the freshness halves of `checkAnn` (`checkAccFresh`,
`checkPubFresh`) already force `accFlat`/`pubFlat` duplicate-free: each step's
group (block) is duplicate-free and disjoint from what the prefix consumed
(published), so the prefix flat-map stays duplicate-free by induction on `pc`. -/

omit [DecidableEq σ.Tensor] in
/-- Generic induction: if every singleton step's image under `f` is
    duplicate-free and disjoint from the prefix's image, every prefix image is
    duplicate-free. -/
theorem nodup_prefixAnn_flatMap {α : Type _} (f : Ann P → List α) (hs : π.Singleton)
    (hfresh : ∀ pc a, π.commands[pc]? = some [a] →
      (f a).Nodup ∧ ∀ x ∈ f a, x ∉ (π.prefixAnn pc).flatMap f) :
    ∀ n, ((π.prefixAnn n).flatMap f).Nodup := by
  intro n
  induction n with
  | zero => simp [prefixAnn_zero]
  | succ n ih =>
    cases hc : π.commands[n]? with
    | none =>
      have : π.prefixAnn (n + 1) = π.prefixAnn n := by simp [prefixAnn, List.take_add_one, hc]
      rw [this]
      exact ih
    | some cmd =>
      obtain ⟨a, rfl⟩ := hs cmd (List.mem_of_getElem? hc)
      obtain ⟨hn, hd⟩ := hfresh n a hc
      rw [π.prefixAnn_succ hc, List.flatMap_append, List.flatMap_singleton, List.nodup_append]
      exact ⟨ih, hn, fun x hx y hy e => hd y hy (e ▸ hx)⟩

/-- Plan §10 item 3: given the singleton profile and `checkSteps`, the two
    coverage `Nodup` checks of `checkPlan` always pass. -/
theorem checkPlan_nodup_redundant (hs : π.checkSingleton = true) (ht : π.checkSteps = true) :
    π.checkCov1Nodup = true ∧ π.checkCov2Nodup = true := by
  have hS : π.Singleton := by
    simp only [checkSingleton, List.all_eq_true, beq_iff_eq] at hs
    exact fun cmd hc => List.length_eq_one_iff.mp (hs cmd hc)
  have hann : π.ann = π.prefixAnn π.commands.length := by simp [ann, prefixAnn]
  simp only [checkCov1Nodup, checkCov2Nodup, accFlat, pubFlat, decide_eq_true_eq, hann]
  refine ⟨π.nodup_prefixAnn_flatMap Ann.groups hS (fun pc a ha => ?_) _,
    π.nodup_prefixAnn_flatMap Ann.blocks hS (fun pc a ha => ?_) _⟩
  · have h := π.checkSteps_ann ht ha
    cases a with
    | acc G =>
      simp only [checkAnn, checkAccFresh, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not] at h
      exact ⟨h.1.1.1, h.1.1.2⟩
    | pub B => simp [Ann.groups]
    | initZero S => simp [Ann.groups]
    | retire B => simp [Ann.groups]
  · have h := π.checkSteps_ann ht ha
    cases a with
    | pub B =>
      simp only [checkAnn, checkPubFresh, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not] at h
      exact ⟨h.1.1.1, fun x hx hmem => h.1.1.2 x hx (Or.inr (List.mem_map_of_mem hmem))⟩
    | acc G => simp [Ann.blocks]
    | initZero S => simp [Ann.blocks]
    | retire B => simp [Ann.blocks]

/-- Corollary: `checkPlan` equals its core without the two `Nodup` checks. -/
theorem checkPlan_eq_core : π.checkPlan =
    (π.checkSingleton && π.checkCov1Complete && π.checkCov2Complete &&
      π.checkSteps && π.checkLayouts) := by
  unfold checkPlan
  cases hs : π.checkSingleton
  · simp
  cases ht : π.checkSteps
  · simp
  obtain ⟨h1, h2⟩ := π.checkPlan_nodup_redundant hs ht
  simp [h1, h2]

/-! ### The converse: each `Nodup` check implies its freshness check

A duplicate-free whole image makes every singleton step's image duplicate-free
and disjoint from its prefix's, so `checkCov1Nodup` gives `checkAccFresh` and
`checkCov2Nodup` gives `checkPubFresh` at every such step. With
`nodup_prefixAnn_flatMap` the pair shadow each other: on a singleton plan the
`Nodup` check fails exactly when some step's freshness check does. This
direction needs no `checkSingleton`, only that the step itself is `[a]`. -/

omit [DecidableEq σ.Tensor] in
theorem fresh_of_nodup_flatMap {α : Type _} (f : Ann P → List α)
    (hnd : (π.ann.flatMap f).Nodup) {pc : Nat} {a : Ann P} (ha : π.commands[pc]? = some [a]) :
    (f a).Nodup ∧ ∀ x ∈ f a, x ∉ (π.prefixAnn pc).flatMap f := by
  have hsub : List.Sublist ((π.prefixAnn (pc + 1)).flatMap f) (π.ann.flatMap f) :=
    ((List.take_sublist _ _).flatten).flatMap f
  have h := hnd.sublist hsub
  rw [π.prefixAnn_succ ha, List.flatMap_append, List.flatMap_singleton, List.nodup_append] at h
  exact ⟨h.2.1, fun x hx hmem => h.2.2 x hmem x hx rfl⟩

theorem checkAccFresh_of_cov1Nodup (h1 : π.checkCov1Nodup = true) {pc : Nat}
    {G : List (OccRef P)} (ha : π.commands[pc]? = some [.acc G]) :
    π.checkAccFresh pc G = true := by
  simp only [checkCov1Nodup, accFlat, decide_eq_true_eq] at h1
  obtain ⟨hn, hd⟩ := π.fresh_of_nodup_flatMap Ann.groups h1 ha
  simp only [checkAccFresh, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨hn, hd⟩

theorem checkPubFresh_of_cov2Nodup (h2 : π.checkCov2Nodup = true) {pc : Nat}
    {B : List (DefAddr P)} (ha : π.commands[pc]? = some [.pub B]) :
    π.checkPubFresh pc B = true := by
  simp only [checkCov2Nodup, pubFlat, decide_eq_true_eq] at h2
  obtain ⟨hn, hd⟩ := π.fresh_of_nodup_flatMap Ann.blocks h2 ha
  simp only [checkPubFresh, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not]
  refine ⟨hn, fun x hx hp => ?_⟩
  rcases hp with hin | hmem
  · have hx' : P.input x.1.val = false := x.1.2
    simp [DefAddr.addr, hx'] at hin
  · obtain ⟨y, hy, e⟩ := List.mem_map.mp hmem
    exact hd x hx (DefAddr.addr_injective e ▸ hy)

/-! ### Completeness: `Valid` implies `checkPlan = true`

Each `*_complete` lemma is the converse of the matching `*_sound` lemma, so `checkPlan` is an exact
decision procedure for `Valid`, not just a sound one. -/

theorem checkInit_complete {pc : Nat} {S : List (DefAddr P)} (h : π.InitOK pc S) :
    π.checkInit pc S = true := by
  simp only [checkInit, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq]
  rintro ⟨t, p⟩ hx
  obtain ⟨hp, hc⟩ := h _ hx
  refine ⟨hp, fun ⟨t', o⟩ hy e => ?_⟩
  simp only [OccRef.target, Sigma.mk.injEq] at e
  obtain ⟨rfl, e⟩ := e
  exact hc o hy (eq_of_heq e)

theorem checkRet_complete {pc : Nat} {B : List (DefAddr P)} (h : π.RetOK pc B) :
    π.checkRet pc B = true := by
  simp only [checkRet, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact h

theorem checkAnn_acc_complete {pc : Nat} {G : List (OccRef P)}
    (hA : π.AccOK pc G) (hR : π.ReadyOK pc G) : π.checkAnn pc (.acc G) = true := by
  simp only [checkAnn, checkAccFresh, checkAccMat, checkReady, List.all_eq_true,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  exact ⟨⟨⟨hA.1, fun x hx => (hA.2 x hx).1⟩, fun x hx => (hA.2 x hx).2⟩, hR⟩

theorem checkAnn_pub_complete {pc : Nat} {B : List (DefAddr P)}
    (h : π.PubOK pc B) : π.checkAnn pc (.pub B) = true := by
  simp only [checkAnn, checkPubFresh, checkPubMat, checkPubOrder, List.all_eq_true,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    Bool.or_eq_true]
  refine ⟨⟨⟨h.1, fun x hx => (h.2 x hx).1⟩, fun x hx => (h.2 x hx).2.1⟩, ?_⟩
  rintro ⟨t, p⟩ hx ⟨t', o⟩ -
  by_cases e : OccRef.target (⟨t', o⟩ : OccRef P) = ⟨t, p⟩
  · simp only [OccRef.target, Sigma.mk.injEq] at e
    obtain ⟨rfl, e⟩ := e
    exact Or.inr ((h.2 _ hx).2.2 o (eq_of_heq e))
  · exact Or.inl (by simpa using e)

/-- `checkPlan` is complete for Definition 31.1 (slice-1 form): a valid plan passes it. -/
theorem checkPlan_complete (h : π.Valid) : π.checkPlan = true := by
  have hst : π.checkSteps = true := by
    simp only [checkSteps, List.all_eq_true, List.mem_range]
    intro pc hpc
    cases hc : π.commands[pc]? with
    | none => rfl
    | some cmd =>
      obtain ⟨a, rfl⟩ := h.singleton cmd (List.mem_of_getElem? hc)
      cases a with
      | initZero S => exact π.checkInit_complete (h.initFresh pc S hc)
      | acc G => exact π.checkAnn_acc_complete (h.accOK pc G hc) (h.ready pc G hc)
      | pub B => exact π.checkAnn_pub_complete (h.pubOK pc B hc)
      | retire B => exact π.checkRet_complete (h.retOK pc B hc)
  simp only [checkPlan, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hst⟩, π.checkLayouts_iff.mpr h.layout⟩
  · simp only [checkSingleton, List.all_eq_true, beq_iff_eq]
    exact fun cmd hc => List.length_eq_one_iff.mpr (h.singleton cmd hc)
  · simpa only [checkCov1Nodup, decide_eq_true_eq] using h.coverage1.1
  · simp only [checkCov1Complete, List.all_eq_true, decide_eq_true_eq]
    exact fun x _ => h.coverage1.2 x
  · simpa only [checkCov2Nodup, decide_eq_true_eq] using h.coverage2.1
  · simp only [checkCov2Complete, List.all_eq_true, decide_eq_true_eq]
    exact fun x _ => h.coverage2.2 x

theorem checkPlan_iff : π.checkPlan = true ↔ π.Valid :=
  ⟨π.checkPlan_sound, π.checkPlan_complete⟩

/-! ### `checkAccMat` is shadowed

The materialisation clause of `checkAccMat` is implied by the other clauses: an accumulation into
`a` precedes the publication of `a` (condition 4 at the `pub`), so the `initZero` that `checkPubMat`
demands before that publication must also come before the accumulation, or else `checkInit` would
have rejected it (a consumed occurrence would target `a`). The proof is a statement about the other
clauses holding, so no second checker is defined. -/

omit [DecidableEq σ.Tensor] in
theorem mem_prefixAnn {n : Nat} {z : Ann P} :
    z ∈ π.prefixAnn n ↔ ∃ i, i < n ∧ ∃ cmd, π.commands[i]? = some cmd ∧ z ∈ cmd := by
  simp only [prefixAnn, List.mem_flatten]
  constructor
  · rintro ⟨cmd, hmem, hz⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
    rw [List.getElem?_take] at hi
    split_ifs at hi with hlt
    exact ⟨i, hlt, cmd, hi, hz⟩
  · rintro ⟨i, hlt, cmd, hi, hz⟩
    refine ⟨cmd, List.mem_iff_getElem?.mpr ⟨i, ?_⟩, hz⟩
    rw [List.getElem?_take, if_pos hlt, hi]

theorem checkAccMat_of_rest (hs : π.checkSingleton = true) (h2c : π.checkCov2Complete = true)
    (hinit : ∀ pc S, π.commands[pc]? = some [.initZero S] → π.checkInit pc S = true)
    (hpub : ∀ pc B, π.commands[pc]? = some [.pub B] → π.checkPubMat pc B = true)
    {pc : Nat} {G : List (OccRef P)} (ha : π.commands[pc]? = some [.acc G]) :
    π.checkAccMat pc G = true := by
  have hS : ∀ cmd ∈ π.commands, ∃ a, cmd = [a] := by
    simp only [checkSingleton, List.all_eq_true, beq_iff_eq] at hs
    exact fun cmd hc => List.length_eq_one_iff.mp (hs cmd hc)
  simp only [checkAccMat, List.all_eq_true, decide_eq_true_eq]
  intro x hx
  -- `x.target` is published by some `pub B` command at index `pc'`.
  have hpubd : x.target ∈ π.pubFlat := by
    simp only [checkCov2Complete, List.all_eq_true, decide_eq_true_eq] at h2c
    exact h2c _ (π.mem_addrList _)
  obtain ⟨y, hy, hyb⟩ := List.mem_flatMap.mp hpubd
  obtain ⟨cmd, hcmd, hycmd⟩ := List.mem_flatten.mp hy
  obtain ⟨y', rfl⟩ := hS cmd hcmd
  obtain rfl : y = y' := by simpa using hycmd
  obtain ⟨pc', hpc'⟩ := List.mem_iff_getElem?.mp hcmd
  cases y with
  | initZero S => simp [Ann.blocks] at hyb
  | acc G' => simp [Ann.blocks] at hyb
  | retire R => simp [Ann.blocks] at hyb
  | pub B =>
    -- `checkPubMat` at `pc'` gives an `initZero` at an index below `pc'`.
    have hm := hpub pc' B hpc'
    simp only [checkPubMat, List.all_eq_true, decide_eq_true_eq] at hm
    have hmat : π.Mat pc' x.target := hm _ hyb
    obtain ⟨z, hz, hzi⟩ := List.mem_flatMap.mp hmat
    obtain ⟨i, hilt, cmd', hci, hzcmd⟩ := (π.mem_prefixAnn).mp hz
    obtain ⟨z', rfl⟩ := hS cmd' (List.mem_of_getElem? hci)
    obtain rfl : z = z' := by simpa using hzcmd
    cases z with
    | acc _ => simp [Ann.inits] at hzi
    | pub _ => simp [Ann.inits] at hzi
    | retire _ => simp [Ann.inits] at hzi
    | initZero S =>
      have hio := π.checkInit_sound (hinit i S hci)
      have hne : pc ≠ i := by
        rintro rfl
        rw [ha] at hci
        simp at hci
      by_cases hlt : pc < i
      · -- the accumulation precedes the `initZero`: its target would already be consumed there
        have hcons : π.Cons i x :=
          List.mem_flatMap.mpr ⟨.acc G, (π.mem_prefixAnn).mpr ⟨pc, hlt, _, ha, by simp⟩, hx⟩
        have hxS : x.target ∈ S := by simpa [Ann.inits] using hzi
        exact absurd rfl ((hio _ hxS).2 x.2 hcons)
      · exact List.mem_flatMap.mpr ⟨.initZero S,
          (π.mem_prefixAnn).mpr ⟨i, by omega, _, hci, by simp⟩, hzi⟩

end Check

#print axioms Valid.stepOK
#print axioms Valid.layout_boundary
#print axioms mem_allAddrList
#print axioms mem_resourceList
#print axioms checkLayoutAt_iff
#print axioms checkLayouts_iff
#print axioms mem_occList
#print axioms mem_addrList
#print axioms checkPlan_sound
#print axioms nodup_prefixAnn_flatMap
#print axioms checkPlan_nodup_redundant
#print axioms checkPlan_eq_core
#print axioms fresh_of_nodup_flatMap
#print axioms checkAccFresh_of_cov1Nodup
#print axioms checkPubFresh_of_cov2Nodup
#print axioms checkInit_complete
#print axioms checkRet_sound
#print axioms checkRet_complete
#print axioms checkAnn_acc_complete
#print axioms checkAnn_pub_complete
#print axioms checkPlan_complete
#print axioms checkPlan_iff
#print axioms mem_prefixAnn
#print axioms checkAccMat_of_rest

/-! ### The `Nodup` halves of coverage 1 and 2 follow from the per-step side conditions

`checkPlan_nodup_redundant` is the checker-level form of this. Stated directly (the form the spec's
Section 31.1 table asks about): on a singleton plan, `AccOK` at every `acc` command makes the accumulation
image `accFlat` duplicate-free, and `PubOK` at every `pub` command makes the publication image
`pubFlat` duplicate-free. So the `Nodup` halves of `Coverage1` and `Coverage2` are consequences of
`singleton`, `accOK` and `pubOK`, never independent requirements. -/

theorem accFlat_nodup_of_accOK (hs : π.Singleton)
    (hacc : ∀ pc G, π.commands[pc]? = some [.acc G] → π.AccOK pc G) : π.accFlat.Nodup := by
  have hann : π.ann = π.prefixAnn π.commands.length := by simp [ann, prefixAnn]
  simp only [accFlat, hann]
  refine π.nodup_prefixAnn_flatMap Ann.groups hs (fun pc a ha => ?_) _
  cases a with
  | acc G => exact ⟨(hacc pc G ha).1, fun x hx hmem => ((hacc pc G ha).2 x hx).1 hmem⟩
  | pub B => simp [Ann.groups]
  | initZero S => simp [Ann.groups]
  | retire B => simp [Ann.groups]

theorem pubFlat_nodup_of_pubOK (hs : π.Singleton)
    (hpub : ∀ pc B, π.commands[pc]? = some [.pub B] → π.PubOK pc B) : π.pubFlat.Nodup := by
  have hann : π.ann = π.prefixAnn π.commands.length := by simp [ann, prefixAnn]
  simp only [pubFlat, hann]
  refine π.nodup_prefixAnn_flatMap Ann.blocks hs (fun pc a ha => ?_) _
  cases a with
  | pub B =>
    exact ⟨(hpub pc B ha).1, fun x hx hmem =>
      ((hpub pc B ha).2 x hx).1 (Or.inr (List.mem_map_of_mem (f := DefAddr.addr) hmem))⟩
  | acc G => simp [Ann.blocks]
  | initZero S => simp [Ann.blocks]
  | retire B => simp [Ann.blocks]

/-- For a `Valid` plan the two `Nodup` halves are therefore derivable from the other fields. -/
theorem Valid.coverage_nodup_of_steps [DecidableEq σ.Tensor] (hv : π.Valid) :
    π.accFlat.Nodup ∧ π.pubFlat.Nodup :=
  ⟨π.accFlat_nodup_of_accOK hv.singleton hv.accOK, π.pubFlat_nodup_of_pubOK hv.singleton hv.pubOK⟩

#print axioms accFlat_nodup_of_accOK
#print axioms pubFlat_nodup_of_pubOK
#print axioms Valid.coverage_nodup_of_steps

/-- Canonical layout safety discharges the additional checker clause. -/
theorem checkPlan_of_canonical [DecidableEq σ.Tensor]
    (hA : π.allocation = Allocation.canonical P π.tensors π.tensors_nodup π.tensors_complete)
    (h : (π.checkSingleton && π.checkCov1Nodup && π.checkCov1Complete &&
      π.checkCov2Nodup && π.checkCov2Complete && π.checkSteps) = true) :
    π.checkPlan = true := by
  rw [checkPlan, h, Bool.true_and]
  exact π.checkLayouts_iff.mpr (fun pc _ => π.layoutOK_of_canonical hA pc)

#print axioms checkPlan_of_canonical

end LeanNCD.Semantics.Program.Plan
