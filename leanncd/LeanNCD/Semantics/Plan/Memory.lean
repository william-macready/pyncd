import LeanNCD.Semantics.Plan.Batch

/- Concrete memory, the slot view, Start, Decode, the logical post-state of a
   command prefix, and the representation relation R (spec Section 30).
   Inputs have separate slots; defined addresses use the plan's typed allocation. -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}

/-- Input storage cannot be targeted by a defined allocation. -/
abbrev InputSlot (P : Program K σ r) :=
  (t : {t : σ.Tensor // P.input t = true}) ×
    Fin (canonicalLayout (σ.signature t.val).axes).count

abbrev BufferSlot {P : Program K σ r} (A : Allocation P) :=
  (b : A.Buffer) × Fin (A.capacity b)

abbrev Slot {P : Program K σ r} (A : Allocation P) := InputSlot P ⊕ BufferSlot A

def slotSort {P : Program K σ r} (A : Allocation P) : Slot A → S
  | .inl ξ => (σ.signature ξ.1.val).sort
  | .inr ξ => A.sort ξ.1

instance {P : Program K σ r} [DecidableEq σ.Tensor] (A : Allocation P) :
    DecidableEq (Slot A) :=
  letI := A.bufferEq
  inferInstance

/-- Physical memory includes every slot, including unused buffer capacity. -/
abbrev Memory (K : S → Type) {r : Registry K} {P : Program K σ r} (A : Allocation P) :=
  (ξ : Slot A) → Option (K (slotSort A ξ))

def place {P : Program K σ r} (A : Allocation P) (a : Address σ) : Slot A :=
  if h : P.input a.1 = true then
    .inl ⟨⟨a.1, h⟩, (canonicalLayout (σ.signature a.1).axes).enumerate.symm a.2⟩
  else
    .inr (A.locate ⟨⟨a.1, by cases hi : P.input a.1 <;> simp_all⟩, a.2⟩).val

theorem place_sort {P : Program K σ r} (A : Allocation P) (a : Address σ) :
    slotSort A (place A a) = (σ.signature a.1).sort := by
  unfold place
  split_ifs
  · rfl
  · exact (A.locate _).property

/-- Read at the logical sort, transporting only along the certified sort equality. -/
def readSlot {P : Program K σ r} (A : Allocation P) (M : Memory K A) (a : Address σ) :
    Option (K (σ.signature a.1).sort) :=
  if h : P.input a.1 = true then
    M (.inl ⟨⟨a.1, h⟩, (canonicalLayout (σ.signature a.1).axes).enumerate.symm a.2⟩)
  else
    let x : DefAddr P := ⟨⟨a.1, by cases hi : P.input a.1 <;> simp_all⟩, a.2⟩
    cast (congrArg (fun s => Option (K s)) (A.locate x).property)
      (M (.inr (A.locate x).val))

theorem cast_option_none {s t : S} (h : s = t) :
    cast (congrArg (fun s => Option (K s)) h) none = none := by
  cases h
  rfl

theorem readSlot_eq_cast {P : Program K σ r} (A : Allocation P)
    (M : Memory K A) (a : Address σ) :
    readSlot A M a =
      cast (congrArg (fun s => Option (K s)) (place_sort A a)) (M (place A a)) := by
  apply eq_of_heq
  have hr : HEq (readSlot A M a) (M (place A a)) := by
    by_cases h : P.input a.1 = true
    · have e : place A a = .inl ⟨⟨a.1, h⟩,
          (canonicalLayout (σ.signature a.1).axes).enumerate.symm a.2⟩ := by
        simp only [place, dif_pos h]
      have hm : HEq (M (place A a)) (M (.inl ⟨⟨a.1, h⟩,
          (canonicalLayout (σ.signature a.1).axes).enumerate.symm a.2⟩)) := by rw [e]
      simp only [readSlot, dif_pos h]
      exact hm.symm
    · let x : DefAddr P := ⟨⟨a.1, by cases hi : P.input a.1 <;> simp_all⟩, a.2⟩
      have e : place A a = .inr (A.locate x).val := by
        simp only [place, dif_neg h]
        rfl
      have hm : HEq (M (place A a)) (M (.inr (A.locate x).val)) := by rw [e]
      simp only [readSlot, dif_neg h]
      exact (cast_heq _ _).trans hm.symm
  exact hr.trans (cast_heq _ _).symm

theorem readSlot_heq {P : Program K σ r} (A : Allocation P)
    (M : Memory K A) {a b : Address σ} (h : place A a = place A b) :
    HEq (readSlot A M a) (readSlot A M b) := by
  rw [readSlot_eq_cast, readSlot_eq_cast]
  have hm : HEq (M (place A a)) (M (place A b)) := by rw [h]
  exact (cast_heq _ _).trans (hm.trans (cast_heq _ _).symm)

theorem readSlot_congr {P : Program K σ r} (A : Allocation P)
    {M N : Memory K A} {a : Address σ} (h : M (place A a) = N (place A a)) :
    readSlot A M a = readSlot A N a := by
  simp only [readSlot_eq_cast, h]

theorem place_injective {P : Program K σ r} (ts : List σ.Tensor)
    (hn : ts.Nodup) (hc : ∀ t, t ∈ ts) :
    Function.Injective (place (Allocation.canonical P ts hn hc)) := by
  rintro ⟨t, p⟩ ⟨u, q⟩ h
  unfold place at h
  split_ifs at h <;> simp only [Allocation.canonical, Subtype.coe_mk] at h
  all_goals
    simp only [Sum.inl.injEq, Sum.inr.injEq, Sigma.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain rfl := (canonicalLayout (σ.signature t).axes).enumerate.symm.injective (eq_of_heq h)
    rfl

/-- The two kinds of logical resource of spec 30.2. -/
inductive Resource (P : Program K σ r)
  | pub (a : Address σ)
  | acc (x : DefAddr P)

variable {P : Program K σ r} [DecidableEq σ.Tensor] (π : P.Plan)

/-- The spec's layout view `λ`: a function of `pc` and the commands only. -/
def SlotView (pc : Nat) : Resource P → Option (Slot π.allocation)
  | .pub a => if π.Live pc a then some (place π.allocation a) else none
  | .acc x => if π.Mat pc x ∧ ¬ π.Pub pc x.addr then some (place π.allocation x.addr) else none

/-- Simultaneously represented resources occupy distinct physical slots. -/
def LayoutOK (pc : Nat) : Prop :=
  ∀ r₁ r₂ ξ, π.SlotView pc r₁ = some ξ → π.SlotView pc r₂ = some ξ → r₁ = r₂

theorem LayoutOK.ne {π : P.Plan} {pc : Nat} (ok : π.LayoutOK pc)
    {r₁ r₂ : Resource P} {ξ₁ ξ₂ : Slot π.allocation}
    (h₁ : π.SlotView pc r₁ = some ξ₁) (h₂ : π.SlotView pc r₂ = some ξ₂)
    (hne : r₁ ≠ r₂) : ξ₁ ≠ ξ₂ := by
  intro e
  exact hne (ok r₁ r₂ ξ₂ (e ▸ h₁) h₂)

/-- The simple profile's injectivity of `λ` on its domain. -/
theorem slotView_injective (hinj : Function.Injective (place π.allocation))
    {pc : Nat} {r₁ r₂ : Resource P} {ξ : Slot π.allocation}
    (h₁ : π.SlotView pc r₁ = some ξ) (h₂ : π.SlotView pc r₂ = some ξ) : r₁ = r₂ := by
  cases r₁ with
  | pub a =>
    cases r₂ with
    | pub b =>
      simp only [SlotView] at h₁ h₂
      split_ifs at h₁ h₂
      cases h₁
      rw [hinj (Option.some.inj h₂)]
    | acc y =>
      simp only [SlotView] at h₁ h₂
      split_ifs at h₁ h₂ with hp hq
      cases h₁
      have e := hinj (Option.some.inj h₂)
      exact absurd (e ▸ hp.1) hq.2
  | acc x =>
    cases r₂ with
    | pub b =>
      simp only [SlotView] at h₁ h₂
      split_ifs at h₁ h₂ with hq hp
      cases h₁
      have e := hinj (Option.some.inj h₂)
      exact absurd (e.symm ▸ hp.1) hq.2
    | acc y =>
      simp only [SlotView] at h₁ h₂
      split_ifs at h₁ h₂
      cases h₁
      rw [DefAddr.addr_injective (hinj (Option.some.inj h₂))]

theorem layoutOK_of_place_injective (hinj : Function.Injective (place π.allocation))
    (pc : Nat) : π.LayoutOK pc := by
  intro r₁ r₂ ξ h₁ h₂
  exact π.slotView_injective hinj h₁ h₂

/-- Concrete initialisation: validated inputs at their slots, every other slot
    uninitialised. Zero materialisation is an explicit `initZero` command. -/
def Start (η : P.Input) : Memory K π.allocation
  | .inl ξ => (η.val ξ.1.val).map
      (fun f => f ((canonicalLayout (σ.signature ξ.1.val).axes).enumerate ξ.2))
  | .inr _ => none

omit [DecidableEq σ.Tensor] in
theorem start_noninput (η : P.Input) (ξ : BufferSlot π.allocation) :
    π.Start η (.inr ξ) = none := rfl

theorem start_read (η : P.Input) (a : Address σ) :
    readSlot π.allocation (π.Start η) a = (η.val a.1).map (fun f => f a.2) := by
  unfold readSlot
  split_ifs with hi
  · simp only [Start, Equiv.apply_symm_apply]
    rfl
  · have hf : P.input a.1 = false := by cases h : P.input a.1 <;> simp_all
    have hn : η.val a.1 = none := by
      have hv := η.property a.1
      simpa [hf] using hv
    simp only [Start, hn, Option.map_none]
    exact cast_option_none (π.allocation.locate ⟨⟨a.1, hf⟩, a.2⟩).property

/-- The read view of published resources: `M (place a)` exactly on `Live(pc)`. -/
def readPub (pc : Nat) (M : Memory K π.allocation) (a : Address σ) :
    Option (K (σ.signature a.1).sort) :=
  if π.Live pc a then readSlot π.allocation M a else none

/-- Partial output decoder: succeeds only when every output coordinate is in
    `Live(pc)` and its slot is initialised. It never fills a missing value. -/
def Decode (pc : Nat) (M : Memory K π.allocation) : Option P.Output :=
  letI := P.tensors
  letI : ∀ t, Fintype (Coord (σ.signature t).axes) := finiteCoords
  if h : ∀ t : {t : σ.Tensor // P.output t = true}, ∀ p,
      (π.readPub pc M ⟨t.val, p⟩).isSome = true then
    some (fun t p => (π.readPub pc M ⟨t.val, p⟩).get (h t p))
  else none

theorem decode_some {pc : Nat} {M : Memory K π.allocation} {out : P.Output}
    (h : π.Decode pc M = some out) (t : {t : σ.Tensor // P.output t = true})
    (p : Coord (σ.signature t.val).axes) :
    π.readPub pc M ⟨t.val, p⟩ = some (out t p) := by
  unfold Decode at h
  split_ifs at h with hd
  cases h
  exact (Option.some_get _).symm

variable [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))

/-! ### Logical post-states -/

def evalValue (c : P.Running) (x : OccRef P) : Option (K (σ.signature x.1.val).sort) :=
  match evalReady ops c.published (P.body x.1 x.2.1) x.2.2 with
  | .evaluated (some v) => some v
  | _ => none

theorem evalValue_ready (c : P.Running) (x : OccRef P)
    (h : (evalValue ops c x).isSome = true) :
    evalReady ops c.published (P.body x.1 x.2.1) x.2.2 =
      .evaluated (some ((evalValue ops c x).getD 0)) := by
  unfold evalValue at h ⊢
  split at h
  · rename_i v hv
    rw [hv]
    rfl
  · contradiction

/-- The logical effect of one annotation; `none` when its contract's premises
    fail. -/
def postAcc (c : P.Running) (G : List (OccRef P)) : Option P.Running :=
  -- Bounded quantifiers decided over the list, never via `Fintype` (whose
  -- instances `definedFintype`/`definedAddressFintype` are noncomputable).
  letI := List.decidableBAll
    (fun x : OccRef P => x.2 ∈ c.pending x.1 ∧ (evalValue ops c x).isSome = true) G
  if G.Nodup ∧ ∀ x ∈ G, x.2 ∈ c.pending x.1 ∧ (evalValue ops c x).isSome = true then
    some (accumulateBatch P c G (fun x => (evalValue ops c x).getD 0))
  else none

def postPub (c : P.Running) (B : List (DefAddr P)) : Option P.Running :=
  letI : ∀ t p, Decidable (P.FiberEmpty c t p) := fun t p => fiberDecidable P c t p
  letI : ∀ t : P.Defined, DecidableEq (Coord (σ.signature t.val).axes) :=
    fun t => coordDecidableEq (σ.signature t.val).axes
  letI := List.decidableBAll
    (fun x : DefAddr P => (c.published x.addr).isNone = true ∧ P.FiberEmpty c x.1 x.2) B
  if B.Nodup ∧ ∀ x ∈ B, (c.published x.addr).isNone = true ∧ P.FiberEmpty c x.1 x.2 then
    some (publishBlock P c B)
  else none

def postAnn (c : P.Running) : Ann P → Option P.Running
  | .acc G => postAcc ops c G
  | .pub B => postPub c B
  | .initZero _ => some c
  | .retire _ => some c

/-- The related reference state: a deterministic function of `pc`. -/
def refState (η : P.Input) (pc : Nat) : Option P.Running :=
  (π.prefixAnn pc).foldlM (postAnn ops) (P.initial η)

theorem postAnn_execution {c d : P.Running} {a : Ann P} (h : postAnn ops c a = some d) :
    ∃ events, Execution P ops events (.running c) (.running d) := by
  cases a with
  | acc G =>
    simp only [postAnn, postAcc] at h
    split_ifs at h with hc
    cases h
    exact ⟨_, batch_execution P ops c G _ hc.1 (fun x hx => (hc.2 x hx).1)
      (fun x hx => evalValue_ready ops c x (hc.2 x hx).2)⟩
  | pub B =>
    simp only [postAnn, postPub] at h
    split_ifs at h with hc
    cases h
    exact ⟨_, block_execution P ops c B hc.1
      (fun x hx => Option.isNone_iff_eq_none.mp (hc.2 x hx).1) (fun x hx => (hc.2 x hx).2)⟩
  | initZero S =>
    cases h
    exact ⟨[], .nil _⟩
  | retire B =>
    cases h
    exact ⟨[], .nil _⟩

theorem foldlM_execution (anns : List (Ann P)) {c d : P.Running}
    (h : anns.foldlM (postAnn ops) c = some d) :
    ∃ events, Execution P ops events (.running c) (.running d) := by
  induction anns generalizing c with
  | nil =>
    cases h
    exact ⟨[], .nil _⟩
  | cons a as ih =>
    rw [List.foldlM_cons] at h
    cases hc : postAnn ops c a with
    | none => simp [hc] at h
    | some c' =>
      simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨e₁, x₁⟩ := postAnn_execution ops hc
      obtain ⟨e₂, x₂⟩ := ih h
      exact ⟨e₁ ++ e₂, x₁.append x₂⟩

/-- Success of the post-state function yields a matching reference segment. -/
theorem refState_execution {η : P.Input} {pc : Nat} {c : P.Running}
    (h : π.refState ops η pc = some c) :
    ∃ events, Execution P ops events (.running (P.initial η)) (.running c) :=
  foldlM_execution ops _ h

theorem refState_reaches {η : P.Input} {pc : Nat} {c : P.Running}
    (h : π.refState ops η pc = some c) :
    P.Reaches ops (.running (P.initial η)) (.running c) :=
  let ⟨_, x⟩ := π.refState_execution ops h
  x.reaches P ops

/-! ### The representation relation -/

/-- `R_Π` (spec 30.4) in the slice-1 to slice-3 profile, with the input `η` explicit. -/
structure R (η : P.Input) (pc : Nat) (M : Memory K π.allocation) (c : P.Running) : Prop where
  /-- R1: the related reference state is reachable. -/
  reach : P.Reaches ops (.running (P.initial η)) (.running c)
  /-- R2: bookkeeping agrees with the command prefix. -/
  pending : ∀ t o, o ∈ c.pending t ↔ ¬ π.Cons pc ⟨t, o⟩
  published : ∀ a, (c.published a).isSome = true ↔ π.Pub pc a
  /-- R3: every mapped resource's slot holds its logical value. -/
  pubSlot : ∀ a, π.SlotView pc (.pub a) = some (place π.allocation a) →
    readSlot π.allocation M a = c.published a
  accSlot : ∀ x : DefAddr P,
    π.SlotView pc (.acc x) = some (place π.allocation x.addr) →
    readSlot π.allocation M x.addr = some (c.accumulators x.1 x.2)
  /-- R4: an unpublished address with a consumed occurrence keeps its accumulator. -/
  retain : ∀ x : DefAddr P, ¬ π.Pub pc x.addr →
    (∃ o : P.Occurrence x.1, π.Cons pc ⟨x.1, o⟩ ∧ P.destination x.1 o.1 o.2 = x.2) →
    π.Mat pc x
  /-- R5: every slot outside the current layout image is uninitialised. -/
  dead : ∀ ξ, (∀ res, π.SlotView pc res ≠ some ξ) → M ξ = none
  /-- R6: a retired address is published (so `Live` is `Pub` minus a published set). -/
  retPub : ∀ a, π.Ret pc a → π.Pub pc a

/-- Lemma 31.2's initialisation obligation. -/
theorem R_start (η : P.Input) : π.R ops η 0 (π.Start η) (P.initial η) where
  reach := .refl _
  pending t o := by
    simp [Program.initial, π.not_cons_zero]
  published a := by
    rw [π.pub_zero, ← η.property a.1]
    simp [Program.initial]
  pubSlot a _ := by simpa [Program.initial] using π.start_read η a
  accSlot x h := by
    simp [SlotView, π.not_mat_zero] at h
  retain x _ := by
    rintro ⟨o, ho, _⟩
    exact absurd ho (π.not_cons_zero _)
  dead ξ hu := by
    cases ξ with
    | inr ξ => rfl
    | inl ξ =>
      exfalso
      apply hu (.pub ⟨ξ.1.val,
        (canonicalLayout (σ.signature ξ.1.val).axes).enumerate ξ.2⟩)
      simp [SlotView, π.live_zero, ξ.1.property, place,
        (canonicalLayout (σ.signature ξ.1.val).axes).enumerate.symm_apply_apply]
  retPub a h := absurd h (π.ret_zero a)

/-- Under R, the read view of memory is the reference published store on `Live(pc)`
    (a retired address keeps its ghost value in `c.published` but reads `none`). -/
theorem readPub_eq {η : P.Input} {pc : Nat} {M : Memory K π.allocation} {c : P.Running}
    (h : π.R ops η pc M c) {a : Address σ} (ha : π.Live pc a) :
    π.readPub pc M a = c.published a := by
  unfold readPub
  rw [if_pos ha]
  exact h.pubSlot a (by simp [SlotView, ha])

/-- Under R, Decode succeeds exactly when every output coordinate is in
    `Live(pc)`, and then returns the reference published values. -/
theorem decode_of_R {η : P.Input} {pc : Nat} {M : Memory K π.allocation} {c : P.Running}
    (h : π.R ops η pc M c)
    (outs : ∀ t : {t : σ.Tensor // P.output t = true}, ∀ p, π.Live pc ⟨t.val, p⟩) :
    ∃ out, π.Decode pc M = some out ∧
      ∀ t : {t : σ.Tensor // P.output t = true}, ∀ p, c.published ⟨t.val, p⟩ = some (out t p) := by
  have view : ∀ t : {t : σ.Tensor // P.output t = true}, ∀ p,
      π.readPub pc M ⟨t.val, p⟩ = c.published ⟨t.val, p⟩ :=
    fun t p => π.readPub_eq ops h (outs t p)
  have all : ∀ t : {t : σ.Tensor // P.output t = true}, ∀ p,
      (π.readPub pc M ⟨t.val, p⟩).isSome = true := by
    intro t p
    rw [view t p]
    exact (h.published _).mpr (outs t p).1
  refine ⟨fun t p => (π.readPub pc M ⟨t.val, p⟩).get (all t p), ?_, fun t p => ?_⟩
  · unfold Decode
    rw [dif_pos all]
  · rw [← view t p]
    exact (Option.some_get _).symm

#print axioms place_injective
#print axioms readSlot_eq_cast
#print axioms readSlot_heq
#print axioms readSlot_congr
#print axioms LayoutOK.ne
#print axioms layoutOK_of_place_injective
#print axioms slotView_injective
#print axioms start_noninput
#print axioms decode_some
#print axioms postAnn_execution
#print axioms refState_execution
#print axioms refState_reaches
#print axioms R_start
#print axioms readPub_eq
#print axioms decode_of_R

end LeanNCD.Semantics.Program.Plan
