import LeanNCD.Semantics.Plan.Syntax

/- Reference-side batching (spec Section 32.1, Lemma 32.1) on the EXISTING
   reference machine: a ready group of contributions and an unpublished,
   finished block of coordinates each match a segment of reference events. -/

namespace LeanNCD.Semantics.Program.Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r} [DecidableEq σ.Tensor]
variable [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable {ops : (s : S) → ScalarOps (K s)}

theorem Execution.append {e₁ e₂ : List (Event P)} {a b c : P.MachineState}
    (first : Execution P ops e₁ a b) (second : Execution P ops e₂ b c) :
    Execution P ops (e₁ ++ e₂) a c := by
  induction first with
  | nil => exact second
  | cons legal _ ih => exact .cons legal (ih second)

end LeanNCD.Semantics.Program.Executor

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable (P : Program K σ r) [DecidableEq σ.Tensor]
variable [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))

/-- Successful body values, one per occurrence identity. -/
abbrev Values := (x : OccRef P) → K (σ.signature x.1.val).sort

/-- The accumulator increment of one contribution: `v` at its destination. -/
def single (x : OccRef P) (v : K (σ.signature x.1.val).sort) : P.Accumulator :=
  letI := coordDecidableEq (σ.signature x.1.val).axes
  Pi.single x.1 (fun p => if P.destination x.1 x.2.1 x.2.2 = p then v else 0)

/-- Apply `Executor.consume` once per member, in list order. -/
def accumulateBatch (c : P.Running) (G : List (OccRef P)) (v : Values P) : P.Running :=
  G.foldl (fun c x => Executor.consume P c x.1 x.2 (v x)) c

def contributionEvents (G : List (OccRef P)) (v : Values P) : List (Event P) :=
  G.map (fun x => .contribution x.1 x.2 (v x))

/-- The spec's `Δ_G`, as a whole-accumulator increment. -/
def delta (G : List (OccRef P)) (v : Values P) : P.Accumulator :=
  (G.map (fun x => single P x (v x))).sum

theorem running_ext {c d : P.Running} (h₁ : c.published = d.published)
    (h₂ : c.accumulators = d.accumulators) (h₃ : c.pending = d.pending) : c = d := by
  cases c
  cases d
  simp_all

theorem consume_accumulators (c : P.Running) (x : OccRef P) (w : K (σ.signature x.1.val).sort) :
    (Executor.consume P c x.1 x.2 w).accumulators = c.accumulators + single P x w := by
  obtain ⟨u, o⟩ := x
  funext t p
  by_cases h : t = u
  · subst h
    simp [Executor.consume, single]
  · simp [Executor.consume, single, Function.update_of_ne h, Pi.single_eq_of_ne h]

theorem consume_pending (c : P.Running) (x : OccRef P) (w : K (σ.signature x.1.val).sort)
    (t : P.Defined) (o : P.Occurrence t) :
    o ∈ (Executor.consume P c x.1 x.2 w).pending t ↔ o ∈ c.pending t ∧ (⟨t, o⟩ : OccRef P) ≠ x := by
  obtain ⟨u, q⟩ := x
  by_cases h : t = u
  · subst h
    simp [Executor.consume, and_comm]
  · have hne : (⟨t, o⟩ : OccRef P) ≠ ⟨u, q⟩ := fun e => h (congrArg Sigma.fst e)
    simp [Executor.consume, Function.update_of_ne h, hne]

theorem accumulateBatch_published (c : P.Running) (G : List (OccRef P)) (v : Values P) :
    (accumulateBatch P c G v).published = c.published := by
  induction G generalizing c with
  | nil => rfl
  | cons x G ih => exact ih (Executor.consume P c x.1 x.2 (v x))

/-- Lemma 32.1, accumulator half: the batch adds exactly `Δ_G`. -/
theorem accumulateBatch_accumulators (c : P.Running) (G : List (OccRef P)) (v : Values P) :
    (accumulateBatch P c G v).accumulators = c.accumulators + delta P G v := by
  induction G generalizing c with
  | nil => simp [accumulateBatch, delta]
  | cons x G ih =>
    change (accumulateBatch P (Executor.consume P c x.1 x.2 (v x)) G v).accumulators = _
    rw [ih, consume_accumulators]
    simp [delta, add_assoc]

/-- Lemma 32.1, bookkeeping half: the remaining set is `U \ G`. -/
theorem accumulateBatch_pending (c : P.Running) (G : List (OccRef P)) (v : Values P)
    (t : P.Defined) (o : P.Occurrence t) :
    o ∈ (accumulateBatch P c G v).pending t ↔ o ∈ c.pending t ∧ (⟨t, o⟩ : OccRef P) ∉ G := by
  induction G generalizing c with
  | nil => simp [accumulateBatch]
  | cons x G ih =>
    change o ∈ (accumulateBatch P (Executor.consume P c x.1 x.2 (v x)) G v).pending t ↔ _
    rw [ih, consume_pending]
    simp only [List.mem_cons, not_or]
    tauto

/-- Any enumeration of the same group gives the same post-state. -/
theorem accumulateBatch_perm (c : P.Running) {G G' : List (OccRef P)} (h : G.Perm G')
    (v : Values P) : accumulateBatch P c G v = accumulateBatch P c G' v := by
  apply running_ext
  · rw [accumulateBatch_published, accumulateBatch_published]
  · rw [accumulateBatch_accumulators, accumulateBatch_accumulators, delta, delta,
      (h.map _).sum_eq]
  · funext t
    ext o
    rw [accumulateBatch_pending, accumulateBatch_pending, h.mem_iff]

/-- Lemma 32.1: a ready, pending, duplicate-free group matches the reference
    segment of one contribution event per member. -/
theorem batch_execution (c : P.Running) (G : List (OccRef P)) (v : Values P)
    (nodup : G.Nodup) (pending : ∀ x ∈ G, x.2 ∈ c.pending x.1)
    (ready : ∀ x ∈ G,
      evalReady ops c.published (P.body x.1 x.2.1) x.2.2 = .evaluated (some (v x))) :
    Execution P ops (contributionEvents P G v) (.running c)
      (.running (accumulateBatch P c G v)) := by
  induction G generalizing c with
  | nil => exact .nil _
  | cons x G ih =>
    obtain ⟨notMem, nodup⟩ := List.nodup_cons.mp nodup
    refine .cons (e := .contribution x.1 x.2 (v x))
      ⟨pending x List.mem_cons_self, ready x List.mem_cons_self⟩ ?_
    refine ih (Executor.consume P c x.1 x.2 (v x)) nodup ?_ ?_
    · intro y hy
      refine (consume_pending P c x (v x) y.1 y.2).mpr ⟨pending y (List.mem_cons_of_mem _ hy), ?_⟩
      rintro rfl
      exact notMem hy
    · intro y hy
      exact ready y (List.mem_cons_of_mem _ hy)

/-- Any-order corollary: a permuted enumeration of the group reaches the same state. -/
theorem batch_execution_perm (c : P.Running) {G G' : List (OccRef P)} (h : G.Perm G')
    (v : Values P) (nodup : G.Nodup) (pending : ∀ x ∈ G, x.2 ∈ c.pending x.1)
    (ready : ∀ x ∈ G,
      evalReady ops c.published (P.body x.1 x.2.1) x.2.2 = .evaluated (some (v x))) :
    Execution P ops (contributionEvents P G' v) (.running c)
      (.running (accumulateBatch P c G v)) := by
  rw [accumulateBatch_perm P c h v]
  exact batch_execution P ops c G' v (h.nodup_iff.mp nodup)
    (fun x hx => pending x (h.mem_iff.mpr hx)) (fun x hx => ready x (h.mem_iff.mpr hx))

/-! ### Block publication -/

/-- Apply `Executor.publish` once per member, in list order. -/
def publishBlock (c : P.Running) (B : List (DefAddr P)) : P.Running :=
  B.foldl (fun c x => Executor.publish P c x.1 x.2) c

def publicationEvents (c : P.Running) (B : List (DefAddr P)) : List (Event P) :=
  B.map (fun x => .publication x.1 x.2 (c.accumulators x.1 x.2))

theorem publishBlock_accumulators (c : P.Running) (B : List (DefAddr P)) :
    (publishBlock P c B).accumulators = c.accumulators := by
  induction B generalizing c with
  | nil => rfl
  | cons x B ih => exact ih (Executor.publish P c x.1 x.2)

theorem publishBlock_pending (c : P.Running) (B : List (DefAddr P)) :
    (publishBlock P c B).pending = c.pending := by
  induction B generalizing c with
  | nil => rfl
  | cons x B ih => exact ih (Executor.publish P c x.1 x.2)

/-- Block publication matches one publication event per member when every
    member is unpublished and its fiber is finished. -/
theorem block_execution (c : P.Running) (B : List (DefAddr P)) (nodup : B.Nodup)
    (unpublished : ∀ x ∈ B, c.published x.addr = none)
    (finished : ∀ x ∈ B, P.FiberEmpty c x.1 x.2) :
    Execution P ops (publicationEvents P c B) (.running c) (.running (publishBlock P c B)) := by
  induction B generalizing c with
  | nil => exact .nil _
  | cons x B ih =>
    obtain ⟨notMem, nodup⟩ := List.nodup_cons.mp nodup
    refine .cons (e := .publication x.1 x.2 (c.accumulators x.1 x.2))
      ⟨unpublished x List.mem_cons_self, finished x List.mem_cons_self, rfl⟩ ?_
    refine ih (Executor.publish P c x.1 x.2) nodup ?_ ?_
    · intro y hy
      have hne : y.addr ≠ x.addr := fun e =>
        notMem (DefAddr.addr_injective e ▸ hy)
      letI := addressEq (σ := σ)
      change Function.update c.published x.addr _ y.addr = none
      rw [Function.update_of_ne hne]
      exact unpublished y (List.mem_cons_of_mem _ hy)
    · intro y hy
      exact finished y (List.mem_cons_of_mem _ hy)

#print axioms Executor.Execution.append
#print axioms consume_accumulators
#print axioms accumulateBatch_accumulators
#print axioms accumulateBatch_pending
#print axioms accumulateBatch_perm
#print axioms batch_execution
#print axioms batch_execution_perm
#print axioms block_execution

end LeanNCD.Semantics.Program.Plan
