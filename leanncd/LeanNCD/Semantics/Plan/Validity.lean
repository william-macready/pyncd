import LeanNCD.Semantics.Plan.Simulation

/- Definition 31.1 (valid plan), slice-1 form, and its computable check.
   `Valid` restates the static part of 31.1 as named fields (the A2
   ValidityConditions list); `checkPlan` decides it by list recursion only.
   Coverage completeness and condition 4 quantify over all occurrences or
   defined addresses: their enumerations are DERIVED from the plan's certified
   `tensors` list (`occList`, `addrList`), never from the noncomputable
   `definedFintype`/`definedAddressFintype` instances. -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r} (π : P.Plan)

/-- Spec 29.3 condition 3 for one group: every address a member body reads is
    in `Pub pc` (inputs, or published by the prefix). A PROGRESS condition. -/
def ReadyOK (pc : Nat) (G : List (OccRef P)) : Prop :=
  ∀ x ∈ G, ∀ a ∈ footprint (P.body x.1 x.2.1) x.2.2, π.Pub pc a

/-- Definition 31.1, slice-1 form (singleton commands, initZero/acc/pub).
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
  /-- Spec 29.3 condition 3 (N3): every read footprint is in `Pub pc`. -/
  ready : ∀ pc G, π.commands[pc]? = some [.acc G] → π.ReadyOK pc G

theorem Valid.stepOK {π : P.Plan} (h : π.Valid) (pc : Nat) : π.StepOK pc := by
  intro a ha
  cases a with
  | initZero S => exact h.initFresh pc S ha
  | acc G => exact h.accOK pc G ha
  | pub B => exact h.pubOK pc B ha

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

/-! ### The computable check (one Bool per Valid clause) -/

section Check

variable [DecidableEq σ.Tensor]
local instance coordEqInst (sh : Shape) : DecidableEq (Coord sh) := coordDecidableEq sh

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

/-- Condition 3 (progress). -/
def checkReady (pc : Nat) (G : List (OccRef P)) : Bool :=
  G.all fun x => (footprint (P.body x.1 x.2.1) x.2.2).all fun a => decide (π.Pub pc a)

/-- `PubOK`, first part: duplicate-free and unpublished. -/
def checkPubFresh (pc : Nat) (B : List (DefAddr P)) : Bool :=
  decide B.Nodup && B.all fun x => !decide (π.Pub pc x.addr)

/-- `PubOK`, N1: every member materialised. -/
def checkPubMat (pc : Nat) (B : List (DefAddr P)) : Bool :=
  B.all fun x => decide (π.Mat pc x)

/-- `PubOK`, condition 4: every occurrence targeting a member is consumed. -/
def checkPubOrder (pc : Nat) (B : List (DefAddr P)) : Bool :=
  B.all fun x => π.occList.all fun y => !decide (y.target = x) || decide (π.Cons pc y)

def checkAnn (pc : Nat) : Ann P → Bool
  | .initZero S => π.checkInit pc S
  | .acc G => π.checkAccFresh pc G && π.checkAccMat pc G && π.checkReady pc G
  | .pub B => π.checkPubFresh pc B && π.checkPubMat pc B && π.checkPubOrder pc B

def checkSteps : Bool :=
  (List.range π.commands.length).all fun pc =>
    match π.commands[pc]? with
    | some [a] => π.checkAnn pc a
    | _ => true

def checkPlan : Bool :=
  π.checkSingleton && π.checkCov1Nodup && π.checkCov1Complete &&
    π.checkCov2Nodup && π.checkCov2Complete && π.checkSteps

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
  obtain ⟨⟨⟨⟨⟨hs, h1n⟩, h1c⟩, h2n⟩, h2c⟩, hst⟩ := h
  simp only [checkSingleton, checkCov1Nodup, checkCov1Complete, checkCov2Nodup,
    checkCov2Complete, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hs h1n h1c h2n h2c
  refine ⟨fun cmd hc => List.length_eq_one_iff.mp (hs cmd hc),
    ⟨h1n, fun x => h1c x (π.mem_occList x)⟩, ⟨h2n, fun x => h2c x (π.mem_addrList x)⟩,
    fun pc S ha => π.checkInit_sound (π.checkSteps_ann hst ha),
    fun pc G ha => (π.checkAnn_acc_sound (π.checkSteps_ann hst ha)).1,
    fun pc B ha => π.checkAnn_pub_sound (π.checkSteps_ann hst ha),
    fun pc G ha => (π.checkAnn_acc_sound (π.checkSteps_ann hst ha)).2⟩

end Check

#print axioms Valid.stepOK
#print axioms mem_occList
#print axioms mem_addrList
#print axioms checkPlan_sound

end LeanNCD.Semantics.Program.Plan
