import LeanNCD.Semantics.Plan.Batch

/- Concrete memory, the slot view, Start, Decode, the logical post-state of a
   command prefix, and the representation relation R (spec Section 30).
   Slice-1 profile: one dense buffer per tensor, injective place map, no reuse. -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}

/-- One buffer per tensor, indexed by the canonical layout's enumeration. -/
abbrev Slot (σ : Declarations S) :=
  (t : σ.Tensor) × Fin (canonicalLayout (σ.signature t).axes).count

/-- Concrete memory: a slot is either uninitialised (`none`) or holds a value. -/
abbrev Memory (K : S → Type) (σ : Declarations S) :=
  (ξ : Slot σ) → Option (K (σ.signature ξ.1).sort)

def place (a : Address σ) : Slot σ :=
  ⟨a.1, (canonicalLayout (σ.signature a.1).axes).enumerate.symm a.2⟩

theorem place_injective : Function.Injective (place (σ := σ)) := by
  rintro ⟨t, p⟩ ⟨u, q⟩ h
  simp only [place, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  obtain rfl := (canonicalLayout (σ.signature t).axes).enumerate.symm.injective (eq_of_heq h)
  rfl

/-- The two kinds of logical resource of spec 30.2. -/
inductive Resource (P : Program K σ r)
  | pub (a : Address σ)
  | acc (x : DefAddr P)

variable {P : Program K σ r} [DecidableEq σ.Tensor] (π : P.Plan)

/-- The spec's layout view `λ`: a function of `pc` and the commands only. -/
def SlotView (pc : Nat) : Resource P → Option (Slot σ)
  | .pub a => if π.Pub pc a then some (place a) else none
  | .acc x => if π.Mat pc x ∧ ¬ π.Pub pc x.addr then some (place x.addr) else none

/-- The simple profile's injectivity of `λ` on its domain. -/
theorem slotView_injective {pc : Nat} {r₁ r₂ : Resource P} {ξ : Slot σ}
    (h₁ : π.SlotView pc r₁ = some ξ) (h₂ : π.SlotView pc r₂ = some ξ) : r₁ = r₂ := by
  cases r₁ with
  | pub a =>
    cases r₂ with
    | pub b =>
      simp only [SlotView] at h₁ h₂
      split_ifs at h₁ h₂
      cases h₁
      rw [place_injective (Option.some.inj h₂)]
    | acc y =>
      simp only [SlotView] at h₁ h₂
      split_ifs at h₁ h₂ with hp hq
      cases h₁
      have e := place_injective (Option.some.inj h₂)
      exact absurd (e ▸ hp) hq.2
  | acc x =>
    cases r₂ with
    | pub b =>
      simp only [SlotView] at h₁ h₂
      split_ifs at h₁ h₂ with hq hp
      cases h₁
      have e := place_injective (Option.some.inj h₂)
      exact absurd (e.symm ▸ hp) hq.2
    | acc y =>
      simp only [SlotView] at h₁ h₂
      split_ifs at h₁ h₂
      cases h₁
      rw [DefAddr.addr_injective (place_injective (Option.some.inj h₂))]

/-- Concrete initialisation: validated inputs at their slots, every other slot
    uninitialised. Zero materialisation is an explicit `initZero` command. -/
def Start (η : P.Input) : Memory K σ :=
  fun ξ => (η.val ξ.1).map (fun f => f ((canonicalLayout (σ.signature ξ.1).axes).enumerate ξ.2))

omit [DecidableEq σ.Tensor] in
theorem start_noninput (η : P.Input) (t : σ.Tensor) (h : P.input t = false)
    (i : Fin (canonicalLayout (σ.signature t).axes).count) :
    Start η ⟨t, i⟩ = none := by
  have hv := η.property t
  rw [h] at hv
  simp only [Start, Option.map_eq_none_iff]
  simpa using hv

/-- The read view of published resources: `M (place a)` exactly on `Pub(pc)`. -/
def readPub (pc : Nat) (M : Memory K σ) (a : Address σ) : Option (K (σ.signature a.1).sort) :=
  if π.Pub pc a then M (place a) else none

/-- Partial output decoder: succeeds only when every output coordinate is in
    `Pub(pc)` and its slot is initialised. It never fills a missing value. -/
def Decode (pc : Nat) (M : Memory K σ) : Option P.Output :=
  letI := P.tensors
  letI : ∀ t, Fintype (Coord (σ.signature t).axes) := finiteCoords
  if h : ∀ t : {t : σ.Tensor // P.output t = true}, ∀ p,
      (π.readPub pc M ⟨t.val, p⟩).isSome = true then
    some (fun t p => (π.readPub pc M ⟨t.val, p⟩).get (h t p))
  else none

theorem decode_some {pc : Nat} {M : Memory K σ} {out : P.Output}
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

/-- `R_Π` (spec 30.4) in the slice-1 profile, with the input `η` explicit. -/
structure R (η : P.Input) (pc : Nat) (M : Memory K σ) (c : P.Running) : Prop where
  /-- R1: the related reference state is reachable. -/
  reach : P.Reaches ops (.running (P.initial η)) (.running c)
  /-- R2: bookkeeping agrees with the command prefix. -/
  pending : ∀ t o, o ∈ c.pending t ↔ ¬ π.Cons pc ⟨t, o⟩
  published : ∀ a, (c.published a).isSome = true ↔ π.Pub pc a
  /-- R3: every mapped resource's slot holds its logical value. -/
  pubSlot : ∀ a, π.SlotView pc (.pub a) = some (place a) → M (place a) = c.published a
  accSlot : ∀ x : DefAddr P, π.SlotView pc (.acc x) = some (place x.addr) →
    M (place x.addr) = some (c.accumulators x.1 x.2)
  /-- R4: an unpublished address with a consumed occurrence keeps its accumulator. -/
  retain : ∀ x : DefAddr P, ¬ π.Pub pc x.addr →
    (∃ o : P.Occurrence x.1, π.Cons pc ⟨x.1, o⟩ ∧ P.destination x.1 o.1 o.2 = x.2) →
    π.Mat pc x

/-- Lemma 31.2's initialisation obligation. -/
theorem R_start (η : P.Input) : π.R ops η 0 (Start η) (P.initial η) where
  reach := .refl _
  pending t o := by
    simp [Program.initial, π.not_cons_zero]
  published a := by
    rw [π.pub_zero, ← η.property a.1]
    simp [Program.initial]
  pubSlot a _ := by
    simp only [Start, place, Program.initial]
    congr 1
    funext f
    exact congrArg f ((canonicalLayout (σ.signature a.1).axes).enumerate.apply_symm_apply a.2)
  accSlot x h := by
    simp [SlotView, π.not_mat_zero] at h
  retain x _ := by
    rintro ⟨o, ho, _⟩
    exact absurd ho (π.not_cons_zero _)

/-- Under R, the read view of memory is exactly the reference published store. -/
theorem readPub_eq {η : P.Input} {pc : Nat} {M : Memory K σ} {c : P.Running}
    (h : π.R ops η pc M c) : π.readPub pc M = c.published := by
  funext a
  unfold readPub
  split_ifs with hp
  · exact h.pubSlot a (by simp [SlotView, hp])
  · have hn := (h.published a).not.mpr hp
    exact (Option.not_isSome_iff_eq_none.mp hn).symm

/-- Under R, Decode succeeds exactly when every output coordinate is in
    `Pub(pc)`, and then returns the reference published values. -/
theorem decode_of_R {η : P.Input} {pc : Nat} {M : Memory K σ} {c : P.Running}
    (h : π.R ops η pc M c)
    (outs : ∀ t : {t : σ.Tensor // P.output t = true}, ∀ p, π.Pub pc ⟨t.val, p⟩) :
    ∃ out, π.Decode pc M = some out ∧
      ∀ t : {t : σ.Tensor // P.output t = true}, ∀ p, c.published ⟨t.val, p⟩ = some (out t p) := by
  have view := π.readPub_eq ops h
  have all : ∀ t : {t : σ.Tensor // P.output t = true}, ∀ p,
      (π.readPub pc M ⟨t.val, p⟩).isSome = true := by
    intro t p
    rw [view]
    exact (h.published _).mpr (outs t p)
  refine ⟨fun t p => (π.readPub pc M ⟨t.val, p⟩).get (all t p), ?_, fun t p => ?_⟩
  · unfold Decode
    rw [dif_pos all]
  · rw [← view]
    exact (Option.some_get _).symm

#print axioms place_injective
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
