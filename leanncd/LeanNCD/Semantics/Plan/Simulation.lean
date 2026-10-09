import LeanNCD.Semantics.Plan.Step

/- Successful-step simulation and failure matching (spec 31.2-31.3) for the
   slice-1 profile. Each kernel is proved separately against the logical
   post-state `postAnn`; `refState` is advanced one annotation at a time. -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r} (π : P.Plan)

/-! ### Prefix sets one command later -/

theorem prefixAnn_succ {pc : Nat} {cmd : Command P} (h : π.commands[pc]? = some cmd) :
    π.prefixAnn (pc + 1) = π.prefixAnn pc ++ cmd := by
  simp [prefixAnn, List.take_add_one, h]

section Succ

variable {π} {pc : Nat} {a : Ann P} (h : π.commands[pc]? = some [a])
include h

theorem cons_succ (x : OccRef P) : π.Cons (pc + 1) x ↔ π.Cons pc x ∨ x ∈ a.groups := by
  simp [Cons, consList, π.prefixAnn_succ h]

theorem pub_succ (b : Address σ) :
    π.Pub (pc + 1) b ↔ π.Pub pc b ∨ b ∈ a.blocks.map DefAddr.addr := by
  simp only [Pub, pubList, π.prefixAnn_succ h, List.flatMap_append, List.map_append,
    List.mem_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, or_assoc]

theorem mat_succ (x : DefAddr P) : π.Mat (pc + 1) x ↔ π.Mat pc x ∨ x ∈ a.inits := by
  simp [Mat, matList, π.prefixAnn_succ h]

end Succ

theorem slotView_pub [DecidableEq σ.Tensor] {pc : Nat} {b : Address σ} :
    π.SlotView pc (.pub b) = some (place b) ↔ π.Pub pc b := by
  simp only [SlotView]
  split_ifs with hb <;> simp [hb]

theorem slotView_acc [DecidableEq σ.Tensor] {pc : Nat} {x : DefAddr P} :
    π.SlotView pc (.acc x) = some (place x.addr) ↔ π.Mat pc x ∧ ¬ π.Pub pc x.addr := by
  simp only [SlotView]
  split_ifs with hx <;> simp [hx]

/-! ### Side conditions of one step (not yet packaged as Definition 31.1) -/

/-- initZero: each member is unpublished and no consumed occurrence targets it,
    so its logical accumulator is still the identity. -/
def InitOK (pc : Nat) (S : List (DefAddr P)) : Prop :=
  ∀ x ∈ S, ¬ π.Pub pc x.addr ∧
    ∀ o : P.Occurrence x.1, π.Cons pc ⟨x.1, o⟩ → P.destination x.1 o.1 o.2 ≠ x.2

/-- acc: the group is duplicate-free, unconsumed, and every destination was
    materialised. (Readiness, spec 29.3 condition 3, is NOT needed here: a
    successful kernel run already read every footprint address from Pub.) -/
def AccOK (pc : Nat) (G : List (OccRef P)) : Prop :=
  G.Nodup ∧ ∀ x ∈ G, ¬ π.Cons pc x ∧ π.Mat pc x.target

/-- pub: the block is duplicate-free, unpublished, materialised (N1), and
    every occurrence targeting a member was consumed (spec 29.3 condition 4). -/
def PubOK (pc : Nat) (B : List (DefAddr P)) : Prop :=
  B.Nodup ∧ ∀ x ∈ B, ¬ π.Pub pc x.addr ∧ π.Mat pc x ∧
    ∀ o : P.Occurrence x.1, P.destination x.1 o.1 o.2 = x.2 → π.Cons pc ⟨x.1, o⟩

def AnnOK (pc : Nat) : Ann P → Prop
  | .initZero S => π.InitOK pc S
  | .acc G => π.AccOK pc G
  | .pub B => π.PubOK pc B

/-- The step's side conditions at `pc` (singleton commands). -/
def StepOK (pc : Nat) : Prop := ∀ a, π.commands[pc]? = some [a] → π.AnnOK pc a

/-- Spec 29.3 condition 4 in the singleton profile. -/
def Order4 : Prop :=
  ∀ pc a, π.commands[pc]? = some [a] → ∀ y ∈ a.blocks, ∀ o : P.Occurrence y.1,
    P.destination y.1 o.1 o.2 = y.2 → π.Cons pc ⟨y.1, o⟩

/-- D9: the union half of condition 1 follows from the union half of
    condition 2 and the order condition 4. -/
theorem accFlat_complete (single : π.Singleton) (pubs : ∀ y, y ∈ π.pubFlat)
    (order : π.Order4) (x : OccRef P) : x ∈ π.accFlat := by
  obtain ⟨a, ha, hy⟩ := List.mem_flatMap.mp (pubs x.target)
  obtain ⟨cmd, hcmd, hacmd⟩ := List.mem_flatten.mp ha
  obtain ⟨a', rfl⟩ := single cmd hcmd
  obtain rfl : a = a' := by simpa using hacmd
  obtain ⟨pc, hpc⟩ := List.mem_iff_getElem?.mp hcmd
  have hc : π.Cons pc x := order pc a hpc x.target hy x.2 rfl
  obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hc
  obtain ⟨cmd', hcmd', hbcmd⟩ := List.mem_flatten.mp hb
  exact List.mem_flatMap.mpr
    ⟨b, List.mem_flatten.mpr ⟨cmd', List.mem_of_mem_take hcmd', hbcmd⟩, hxb⟩

variable [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))

/-! ### `refState` one command later (defect D4) -/

theorem refState_succ (η : P.Input) {pc : Nat} {cmd : Command P}
    (h : π.commands[pc]? = some cmd) :
    π.refState ops η (pc + 1) = (π.refState ops η pc).bind (fun c => cmd.foldlM (postAnn ops) c) := by
  simp only [refState, π.prefixAnn_succ h, List.foldlM_append]
  rfl

/-- D4: with singleton commands, the next related state is exactly the
    post-state of the command's one annotation. -/
theorem refState_succ_single (η : P.Input) {pc : Nat} {a : Ann P}
    (h : π.commands[pc]? = some [a]) :
    π.refState ops η (pc + 1) = (π.refState ops η pc).bind (fun c => postAnn ops c a) := by
  rw [π.refState_succ ops η h]
  congr 1
  funext c
  simp only [List.foldlM_cons, List.foldlM_nil]
  cases postAnn ops c a <;> rfl

/-! ### Published store after a block -/

omit [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem publish_published_ne (c : P.Running) (x : DefAddr P) {b : Address σ} (hne : x.addr ≠ b) :
    (Executor.publish P c x.1 x.2).published b = c.published b := by
  letI := addressEq (σ := σ)
  change Function.update c.published x.addr _ b = _
  exact Function.update_of_ne (Ne.symm hne) _ _

omit [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem publishBlock_published_not_mem (c : P.Running) (B : List (DefAddr P)) {b : Address σ}
    (h : ∀ y ∈ B, y.addr ≠ b) : (publishBlock P c B).published b = c.published b := by
  induction B generalizing c with
  | nil => rfl
  | cons x B ih =>
    change (publishBlock P (Executor.publish P c x.1 x.2) B).published b = _
    rw [ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy)),
      publish_published_ne c x (h x List.mem_cons_self)]

omit [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem publishBlock_published_mem (c : P.Running) (B : List (DefAddr P)) {y : DefAddr P}
    (hy : y ∈ B) : (publishBlock P c B).published y.addr = some (c.accumulators y.1 y.2) := by
  induction B generalizing c with
  | nil => cases hy
  | cons x B ih =>
    change (publishBlock P (Executor.publish P c x.1 x.2) B).published y.addr = _
    by_cases hB : y ∈ B
    · rw [ih _ hB]
      rfl
    · have hyx : y = x := by simpa [hB] using hy
      subst hyx
      rw [publishBlock_published_not_mem _ _ (fun z hz e => hB (by rw [← DefAddr.addr_injective e]; exact hz))]
      letI := addressEq (σ := σ)
      change Function.update c.published y.addr _ y.addr = _
      exact Function.update_self _ _ _

omit [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem publishBlock_isSome (c : P.Running) (B : List (DefAddr P)) (b : Address σ) :
    ((publishBlock P c B).published b).isSome = true ↔
      (c.published b).isSome = true ∨ b ∈ B.map DefAddr.addr := by
  by_cases hb : b ∈ B.map DefAddr.addr
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    refine ⟨fun _ => Or.inr hb, fun _ => ?_⟩
    rw [publishBlock_published_mem c B hy]
    rfl
  · have h : ∀ y ∈ B, y.addr ≠ b := fun y hy e => hb (List.mem_map.mpr ⟨y, hy, e⟩)
    simp [publishBlock_published_not_mem c B h, hb]

/-! ### R2 from `refState` success alone -/

theorem postAnn_bookkeeping {c d : P.Running} {a : Ann P} (h : postAnn ops c a = some d) :
    (∀ t o, o ∈ d.pending t ↔ o ∈ c.pending t ∧ (⟨t, o⟩ : OccRef P) ∉ a.groups) ∧
    (∀ b, (d.published b).isSome = true ↔
      (c.published b).isSome = true ∨ b ∈ a.blocks.map DefAddr.addr) := by
  cases a with
  | acc G =>
    simp only [postAnn, postAcc] at h
    split_ifs at h
    cases h
    exact ⟨fun t o => accumulateBatch_pending P c G _ t o,
      fun b => by simp [Ann.blocks, accumulateBatch_published]⟩
  | pub B =>
    simp only [postAnn, postPub] at h
    split_ifs at h
    cases h
    exact ⟨fun t o => by simp [Ann.groups, publishBlock_pending],
      fun b => publishBlock_isSome c B b⟩
  | initZero S =>
    cases h
    exact ⟨fun t o => by simp [Ann.groups], fun b => by simp [Ann.blocks]⟩

theorem foldlM_bookkeeping (anns : List (Ann P)) {c d : P.Running}
    (h : anns.foldlM (postAnn ops) c = some d) :
    (∀ t o, o ∈ d.pending t ↔ o ∈ c.pending t ∧ (⟨t, o⟩ : OccRef P) ∉ anns.flatMap Ann.groups) ∧
    (∀ b, (d.published b).isSome = true ↔
      (c.published b).isSome = true ∨ b ∈ (anns.flatMap Ann.blocks).map DefAddr.addr) := by
  induction anns generalizing c with
  | nil =>
    cases h
    simp
  | cons a as ih =>
    rw [List.foldlM_cons] at h
    cases hc : postAnn ops c a with
    | none => simp [hc] at h
    | some c' =>
      simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨p1, b1⟩ := postAnn_bookkeeping ops hc
      obtain ⟨p2, b2⟩ := ih h
      refine ⟨fun t o => ?_, fun b => ?_⟩
      · rw [p2, p1]
        simp only [List.flatMap_cons, List.mem_append, not_or]
        tauto
      · rw [b2, b1]
        simp only [List.flatMap_cons, List.map_append, List.mem_append]
        tauto

/-- R2 holds of every successful logical prefix state: no coverage hypothesis
    is needed (success of each `postAnn` already forces the disjointness). -/
theorem refState_R2 {η : P.Input} {pc : Nat} {c : P.Running}
    (h : π.refState ops η pc = some c) :
    (∀ t o, o ∈ c.pending t ↔ ¬ π.Cons pc ⟨t, o⟩) ∧
    (∀ b, (c.published b).isSome = true ↔ π.Pub pc b) := by
  obtain ⟨hp, hb⟩ := foldlM_bookkeeping ops _ h
  refine ⟨fun t o => ?_, fun b => ?_⟩
  · rw [hp]
    simp [Program.initial, Cons, consList]
  · rw [hb]
    simp only [Pub, pubList, Program.initial, Option.isSome_map]
    rw [η.property b.1]

/-! ### Reference facts used by the kernels (R1 via the conservation invariant) -/

/-- An unconsumed-into accumulator is still the identity (defect D1: only R1
    pins it). -/
theorem acc_zero_of_unconsumed {η : P.Input} {pc : Nat} {M : Memory K σ} {c : P.Running}
    (hR : π.R ops η pc M c) (x : DefAddr P)
    (h : ∀ o : P.Occurrence x.1, π.Cons pc ⟨x.1, o⟩ → P.destination x.1 o.1 o.2 ≠ x.2) :
    c.accumulators x.1 x.2 = 0 := by
  obtain ⟨values, inv⟩ := P.reachable_invariant ops η hR.reach
  rw [inv.conservation]
  unfold Program.spent
  refine Finset.sum_eq_zero (fun o _ => ?_)
  by_cases hp : o ∈ c.pending x.1
  · simp [hp]
  · have hc : π.Cons pc ⟨x.1, o⟩ := by
      by_contra hn
      exact hp ((hR.pending x.1 o).mpr hn)
    simp [hp, h o hc]

/-- A pending occurrence never targets a published address. -/
theorem dest_not_pub {η : P.Input} {pc : Nat} {M : Memory K σ} {c : P.Running}
    (hR : π.R ops η pc M c) {x : OccRef P} (hx : ¬ π.Cons pc x) : ¬ π.Pub pc x.dest := by
  intro hp
  obtain ⟨values, inv⟩ := P.reachable_invariant ops η hR.reach
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((hR.published _).mpr hp)
  exact (inv.published x.1 _ v hv).1 x.2 ((hR.pending x.1 x.2).mpr hx) rfl

/-! ### Memory effects of the kernels -/

omit [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem writeDef_ne (M : Memory K σ) (x : DefAddr P) (v : K (σ.signature x.1.val).sort)
    {b : Address σ} (h : x.addr ≠ b) : writeDef M x v (place b) = M (place b) :=
  Function.update_of_ne (fun e => h (place_injective e).symm) _ _

omit [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem writeDef_self (M : Memory K σ) (x : DefAddr P) (v : K (σ.signature x.1.val).sort) :
    writeDef M x v (place x.addr) = some v :=
  Function.update_self _ _ _

theorem execInit_not_mem (S : List (DefAddr P)) (M : Memory K σ) {b : Address σ}
    (h : ∀ x ∈ S, x.addr ≠ b) : execInit S M (place b) = M (place b) := by
  induction S generalizing M with
  | nil => rfl
  | cons x S ih =>
    change execInit S (writeDef M x 0) (place b) = _
    rw [ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy)),
      writeDef_ne _ _ _ (h x List.mem_cons_self)]

theorem execInit_mem (S : List (DefAddr P)) (M : Memory K σ) {y : DefAddr P} (hy : y ∈ S) :
    execInit S M (place y.addr) = some (0 : K (σ.signature y.1.val).sort) := by
  induction S generalizing M with
  | nil => cases hy
  | cons x S ih =>
    change execInit S (writeDef M x 0) (place y.addr) = _
    by_cases hS : y ∈ S
    · exact ih _ hS
    · have hyx : y = x := by simpa [hS] using hy
      subst hyx
      rw [execInit_not_mem _ _ (fun z hz e => hS (by rw [← DefAddr.addr_injective e]; exact hz))]
      exact writeDef_self _ _ _

theorem addAt_some {v : Values P} {M M₁ : Memory K σ} {x : OccRef P}
    (h : addAt v M x = some M₁) :
    ∃ a, M (place x.dest) = some a ∧
      M₁ = Function.update M (place x.dest) (some (addVal x a (v x))) := by
  unfold addAt at h
  split at h
  · rename_i a ha
    cases h
    exact ⟨a, ha, rfl⟩
  · contradiction

theorem commit_other {v : Values P} (G : List (OccRef P)) {M M' : Memory K σ}
    (h : G.foldlM (addAt v) M = some M') {b : Address σ} (hb : ∀ x ∈ G, x.dest ≠ b) :
    M' (place b) = M (place b) := by
  induction G generalizing M with
  | nil =>
    cases h
    rfl
  | cons x G ih =>
    rw [List.foldlM_cons] at h
    cases h₁ : addAt v M x with
    | none => simp [h₁] at h
    | some M₁ =>
      simp only [h₁, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨a, _, rfl⟩ := addAt_some h₁
      rw [ih h (fun y hy => hb y (List.mem_cons_of_mem _ hy))]
      exact Function.update_of_ne (fun e => hb x List.mem_cons_self (place_injective e).symm) _ _

theorem single_target (x : OccRef P) (w : K (σ.signature x.1.val).sort) :
    single P x w x.target.1 x.target.2 = w := by
  simp [single, OccRef.target]

theorem single_ne (x : OccRef P) (w : K (σ.signature x.1.val).sort) (y : DefAddr P)
    (h : y.addr ≠ x.dest) : single P x w y.1 y.2 = 0 := by
  obtain ⟨u, q⟩ := y
  obtain ⟨t, o⟩ := x
  by_cases hut : u = t
  · subst hut
    have hq : P.destination u o.1 o.2 ≠ q := fun e => h (by simp [DefAddr.addr, OccRef.dest, e])
    simp [single, hq]
  · simp [single, Pi.single_eq_of_ne hut]

/-- A committed group adds exactly `Δ_G` at every defined address. -/
theorem commit_def {v : Values P} (G : List (OccRef P)) {M M' : Memory K σ}
    (h : G.foldlM (addAt v) M = some M') (y : DefAddr P) :
    M' (place y.addr) = (M (place y.addr)).map (fun a => a + delta P G v y.1 y.2) := by
  induction G generalizing M with
  | nil =>
    cases h
    simp [delta]
  | cons x G ih =>
    rw [List.foldlM_cons] at h
    cases h₁ : addAt v M x with
    | none => simp [h₁] at h
    | some M₁ =>
      simp only [h₁, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨a, ha, rfl⟩ := addAt_some h₁
      rw [ih h]
      have hd : delta P (x :: G) v y.1 y.2 = single P x (v x) y.1 y.2 + delta P G v y.1 y.2 := by
        simp only [delta, List.map_cons, List.sum_cons, Pi.add_apply]
      rw [hd]
      by_cases hy : y.addr = x.dest
      · obtain rfl : y = x.target := DefAddr.addr_injective hy
        change (Function.update M (place x.dest) (some (addVal x a (v x))) (place x.dest)).map _ =
          (M (place x.dest)).map _
        rw [Function.update_self, ha, single_target]
        simp only [addVal, Option.map_some]
        exact congrArg some (add_assoc (G := K (σ.signature x.1.val).sort) a (v x) _)
      · rw [Function.update_of_ne (fun e => hy (place_injective e)), single_ne x (v x) y hy,
          zero_add]

/-! ### The evaluation phase -/

omit [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem scanGroup_ne_ok (p : PartialStore K σ) (G : List (OccRef P)) (M : Memory K σ) :
    scanGroup ops p G ≠ some (.ok M) := by
  induction G with
  | nil => simp [scanGroup]
  | cons x G ih =>
    unfold scanGroup
    split <;> simp_all

omit [DecidableEq σ.Tensor] in
theorem scanGroup_none {p : PartialStore K σ} {G : List (OccRef P)}
    (h : scanGroup ops p G = none) :
    ∀ x ∈ G, evalReady ops p (P.body x.1 x.2.1) x.2.2 = .evaluated (some (valuesOn ops p x)) := by
  induction G with
  | nil => simp
  | cons x G ih =>
    unfold scanGroup at h
    split at h
    · contradiction
    · contradiction
    · rename_i w hw
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hw]
        simp [valuesOn, valueOn, hw]
      · exact ih h y hy

omit [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem scanGroup_semFail {p : PartialStore K σ} {G : List (OccRef P)} {o : OccRef P}
    (h : scanGroup ops p G = some (.semFail o)) :
    o ∈ G ∧ evalReady ops p (P.body o.1 o.2.1) o.2.2 = .evaluated none := by
  induction G with
  | nil => simp [scanGroup] at h
  | cons x G ih =>
    unfold scanGroup at h
    split at h
    · simp at h
    · rename_i hx
      cases h
      exact ⟨List.mem_cons_self, hx⟩
    · obtain ⟨hm, he⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, he⟩

omit [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)] in
theorem evalValue_eq (c : P.Running) (x : OccRef P) :
    evalValue ops c x = valueOn ops c.published x := rfl

/-! ### Step simulation, one kernel at a time -/

section Steps

variable {π} {η : P.Input} {pc : Nat} {M M' : Memory K σ} {c : P.Running}

theorem step_init {S : List (DefAddr P)} (hR : π.R ops η pc M c)
    (hc : π.refState ops η pc = some c) (hcmd : π.commands[pc]? = some [.initZero S])
    (ok : π.InitOK pc S) :
    π.refState ops η (pc + 1) = some c ∧ π.R ops η (pc + 1) (execInit S M) c ∧
      Execution P ops [] (.running c) (.running c) := by
  have hc' : π.refState ops η (pc + 1) = some c := by
    rw [π.refState_succ_single ops η hcmd, hc]
    rfl
  obtain ⟨r2p, r2b⟩ := π.refState_R2 ops hc'
  have unpub : ∀ y : DefAddr P, ¬ π.Pub (pc + 1) y.addr → ¬ π.Pub pc y.addr :=
    fun y hn h => hn ((pub_succ hcmd _).mpr (.inl h))
  refine ⟨hc', ⟨hR.reach, r2p, r2b, ?_, ?_, ?_⟩, .nil _⟩
  · intro b hb
    have hp : π.Pub pc b := by
      simpa [pub_succ hcmd, Ann.blocks] using (π.slotView_pub).mp hb
    rw [execInit_not_mem S M (fun x hx e => (ok x hx).1 (by rw [e]; exact hp))]
    exact hR.pubSlot b ((π.slotView_pub).mpr hp)
  · intro y hy
    obtain ⟨hm, hnp⟩ := (π.slotView_acc).mp hy
    by_cases hS : y ∈ S
    · rw [execInit_mem S M hS, π.acc_zero_of_unconsumed ops hR y (ok y hS).2]
    · rw [execInit_not_mem S M (fun x hx e => hS (by rw [DefAddr.addr_injective e] at hx; exact hx))]
      have hm' : π.Mat pc y := by simpa [mat_succ hcmd, Ann.inits, hS] using hm
      exact hR.accSlot y ((π.slotView_acc).mpr ⟨hm', unpub y hnp⟩)
  · intro y hnp hcons
    have hcons' : ∃ o : P.Occurrence y.1, π.Cons pc ⟨y.1, o⟩ ∧ P.destination y.1 o.1 o.2 = y.2 := by
      simpa [cons_succ hcmd, Ann.groups] using hcons
    exact (mat_succ hcmd y).mpr (.inl (hR.retain y (unpub y hnp) hcons'))

theorem step_acc {G : List (OccRef P)} (hR : π.R ops η pc M c)
    (hc : π.refState ops η pc = some c) (hcmd : π.commands[pc]? = some [.acc G])
    (ok : π.AccOK pc G) (h : π.execAcc ops pc G M = .ok M') :
    ∃ c', π.refState ops η (pc + 1) = some c' ∧ π.R ops η (pc + 1) M' c' ∧
      ∃ events, Execution P ops events (.running c) (.running c') := by
  have view := π.readPub_eq ops hR
  unfold execAcc at h
  split at h
  · rename_i res hres
    subst h
    exact absurd hres (scanGroup_ne_ok ops _ G M')
  rename_i hscan
  split at h
  swap
  · contradiction
  rename_i M'' hcommit
  cases h
  rw [view] at hscan hcommit
  have ready := scanGroup_none ops hscan
  have cond : G.Nodup ∧ ∀ x ∈ G, x.2 ∈ c.pending x.1 ∧ (evalValue ops c x).isSome = true := by
    refine ⟨ok.1, fun x hx => ⟨(hR.pending x.1 x.2).mpr (ok.2 x hx).1, ?_⟩⟩
    rw [evalValue_eq]
    simp [valueOn, ready x hx]
  have hpost : postAnn ops c (.acc G) = some (accumulateBatch P c G (valuesOn ops c.published)) := by
    simp only [postAnn, postAcc]
    rw [if_pos cond]
    rfl
  have hc' : π.refState ops η (pc + 1) = some (accumulateBatch P c G (valuesOn ops c.published)) := by
    rw [π.refState_succ_single ops η hcmd, hc]
    exact hpost
  obtain ⟨r2p, r2b⟩ := π.refState_R2 ops hc'
  have unpub : ∀ y : DefAddr P, ¬ π.Pub (pc + 1) y.addr → ¬ π.Pub pc y.addr :=
    fun y hn h => hn ((pub_succ hcmd _).mpr (.inl h))
  refine ⟨_, hc', ⟨π.refState_reaches ops hc', r2p, r2b, ?_, ?_, ?_⟩, postAnn_execution ops hpost⟩
  · intro b hb
    have hp : π.Pub pc b := by
      simpa [pub_succ hcmd, Ann.blocks] using (π.slotView_pub).mp hb
    have hne : ∀ x ∈ G, x.dest ≠ b := fun x hx e =>
      π.dest_not_pub ops hR (ok.2 x hx).1 (by rw [e]; exact hp)
    rw [commit_other G hcommit hne, hR.pubSlot b ((π.slotView_pub).mpr hp),
      accumulateBatch_published]
  · intro y hy
    obtain ⟨hm, hnp⟩ := (π.slotView_acc).mp hy
    have hm' : π.Mat pc y := by simpa [mat_succ hcmd, Ann.inits] using hm
    rw [commit_def G hcommit y, hR.accSlot y ((π.slotView_acc).mpr ⟨hm', unpub y hnp⟩),
      accumulateBatch_accumulators]
    rfl
  · intro y hnp hcons
    obtain ⟨o, hco, hd⟩ := hcons
    rcases (cons_succ hcmd _).mp hco with h1 | h1
    · exact (mat_succ hcmd y).mpr (.inl (hR.retain y (unpub y hnp) ⟨o, h1, hd⟩))
    · have ht : OccRef.target (⟨y.1, o⟩ : OccRef P) = y := by
        obtain ⟨y1, y2⟩ := y
        simp only [OccRef.target] at hd ⊢
        rw [hd]
      have hmat := (ok.2 _ h1).2
      rw [ht] at hmat
      exact (mat_succ hcmd y).mpr (.inl hmat)

theorem step_pub {B : List (DefAddr P)} (hR : π.R ops η pc M c)
    (hc : π.refState ops η pc = some c) (hcmd : π.commands[pc]? = some [.pub B])
    (ok : π.PubOK pc B) (h : execPub B M = .ok M') :
    ∃ c', π.refState ops η (pc + 1) = some c' ∧ π.R ops η (pc + 1) M' c' ∧
      ∃ events, Execution P ops events (.running c) (.running c') := by
  have hM : M' = M := by
    unfold execPub at h
    split_ifs at h
    cases h
    rfl
  subst hM
  have cond : B.Nodup ∧ ∀ x ∈ B, (c.published x.addr).isNone = true ∧ P.FiberEmpty c x.1 x.2 := by
    refine ⟨ok.1, fun x hx => ⟨?_, ?_⟩⟩
    · have hn := (hR.published x.addr).not.mpr (ok.2 x hx).1
      exact Option.isNone_iff_eq_none.mpr (Option.not_isSome_iff_eq_none.mp hn)
    · intro o ho hd
      exact ((hR.pending x.1 o).mp ho) ((ok.2 x hx).2.2 o hd)
  have hpost : postAnn ops c (.pub B) = some (publishBlock P c B) := by
    simp only [postAnn, postPub]
    rw [if_pos cond]
  have hc' : π.refState ops η (pc + 1) = some (publishBlock P c B) := by
    rw [π.refState_succ_single ops η hcmd, hc]
    exact hpost
  obtain ⟨r2p, r2b⟩ := π.refState_R2 ops hc'
  have unpub : ∀ y : DefAddr P, ¬ π.Pub (pc + 1) y.addr → ¬ π.Pub pc y.addr :=
    fun y hn h => hn ((pub_succ hcmd _).mpr (.inl h))
  refine ⟨_, hc', ⟨π.refState_reaches ops hc', r2p, r2b, ?_, ?_, ?_⟩, postAnn_execution ops hpost⟩
  · intro b hb
    rcases (pub_succ hcmd b).mp ((π.slotView_pub).mp hb) with hp | hmem
    · have hne : ∀ y ∈ B, y.addr ≠ b := fun y hy e => (ok.2 y hy).1 (by rw [e]; exact hp)
      rw [publishBlock_published_not_mem c B hne]
      exact hR.pubSlot b ((π.slotView_pub).mpr hp)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hmem
      rw [publishBlock_published_mem c B hy]
      exact hR.accSlot y ((π.slotView_acc).mpr ⟨(ok.2 y hy).2.1, (ok.2 y hy).1⟩)
  · intro y hy
    obtain ⟨hm, hnp⟩ := (π.slotView_acc).mp hy
    have hm' : π.Mat pc y := by simpa [mat_succ hcmd, Ann.inits] using hm
    rw [publishBlock_accumulators]
    exact hR.accSlot y ((π.slotView_acc).mpr ⟨hm', unpub y hnp⟩)
  · intro y hnp hcons
    have hcons' : ∃ o : P.Occurrence y.1, π.Cons pc ⟨y.1, o⟩ ∧ P.destination y.1 o.1 o.2 = y.2 := by
      simpa [cons_succ hcmd, Ann.groups] using hcons
    exact (mat_succ hcmd y).mpr (.inl (hR.retain y (unpub y hnp) hcons'))

/-- Successful-step simulation (spec 31.2) for every slice-1 command. -/
theorem step_R {a : Ann P} (hR : π.R ops η pc M c) (hc : π.refState ops η pc = some c)
    (hcmd : π.commands[pc]? = some [a]) (ok : π.AnnOK pc a)
    (h : π.stepPlan ops pc M = .ok M') :
    ∃ c', π.refState ops η (pc + 1) = some c' ∧ π.R ops η (pc + 1) M' c' ∧
      ∃ events, Execution P ops events (.running c) (.running c') := by
  unfold stepPlan at h
  rw [hcmd] at h
  cases a with
  | initZero S =>
    cases h
    obtain ⟨h1, h2, h3⟩ := step_init ops hR hc hcmd ok
    exact ⟨c, h1, h2, [], h3⟩
  | acc G => exact step_acc ops hR hc hcmd ok h
  | pub B => exact step_pub ops hR hc hcmd ok h

/-- Failure matching (spec 31.3): a semantic failure reported by the
    transactional kernel is an actual ready, undefined, pending occurrence of
    the related reference state. Only "members unconsumed" is needed. -/
theorem step_failed {cmd : Command P} {o : OccRef P} (hR : π.R ops η pc M c)
    (hcmd : π.commands[pc]? = some cmd)
    (ok : ∀ G, cmd = [.acc G] → ∀ x ∈ G, ¬ π.Cons pc x)
    (h : π.stepPlan ops pc M = .semFail o) :
    Execution P ops [.undefined o.1 o.2] (.running c) (.failed o.1 o.2 c) := by
  unfold stepPlan at h
  rw [hcmd] at h
  match cmd, h, ok with
  | [.acc G], h, ok =>
    simp only [stepCommand, execAnn, execAcc] at h
    split at h
    · rename_i res hres
      subst h
      obtain ⟨hoG, hev⟩ := scanGroup_semFail ops hres
      rw [π.readPub_eq ops hR] at hev
      exact .cons (e := .undefined o.1 o.2)
        ⟨(hR.pending o.1 o.2).mpr (ok G rfl o hoG), hev⟩ (.nil _)
    · split at h <;> cases h
  | [.pub B], h, _ =>
    simp only [stepCommand, execAnn, execPub] at h
    split_ifs at h
  | [.initZero S], h, _ => cases h
  | [], h, _ => cases h
  | _ :: _ :: _, h, _ => cases h

/-- A reported plan failure is a reachable reference failure, so no model. -/
theorem step_failed_no_model {cmd : Command P} {o : OccRef P} (hR : π.R ops η pc M c)
    (hcmd : π.commands[pc]? = some cmd)
    (ok : ∀ G, cmd = [.acc G] → ∀ x ∈ G, ¬ π.Cons pc x)
    (h : π.stepPlan ops pc M = .semFail o) : ¬ ∃ ρ, P.Models ops η ρ :=
  P.failed_no_model ops η o.1 o.2 c
    (P.reaches_trans ops hR.reach ((step_failed ops hR hcmd ok h).reaches P ops))

end Steps

#print axioms refState_succ_single
#print axioms refState_R2
#print axioms accFlat_complete
#print axioms acc_zero_of_unconsumed
#print axioms commit_def
#print axioms step_init
#print axioms step_acc
#print axioms step_pub
#print axioms step_R
#print axioms step_failed
#print axioms step_failed_no_model

end LeanNCD.Semantics.Program.Plan
