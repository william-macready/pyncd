import IndexedCompositionSteps

namespace IndexedOpenComposition.Correspondence

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {schedule : Schedule P} {contract : Contract σ} {fragment : Fragment σ}
variable {graph : Closed σ}

structure CollectorFiber
    (M : SourceContractMatch P schedule contract fragment graph)
    (t : P.Defined) (p : Coord (σ.signature t.val).axes) (caps : List Nat) : Prop where
  nodup : caps.Nodup
  represented : ∀ cap ∈ caps, ∃ o : P.Occurrence t,
    P.destination t o.1 o.2 = p ∧ M.capability ⟨t, o⟩ = cap
  member_iff : ∀ o : P.Occurrence t,
    M.capability ⟨t, o⟩ ∈ caps ↔ P.destination t o.1 o.2 = p

theorem collector_all_produced_iff_fiberEmpty
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (t : P.Defined)
    (p : Coord (σ.signature t.val).axes) (caps : List Nat)
    (fiber : CollectorFiber M t p caps) :
    caps.all (fun cap => (producedValue g cap).isSome) = true ↔
      P.FiberEmpty c t p := by
  constructor
  · intro all o pending destination
    have member := (fiber.member_iff o).mpr destination
    have produced := (List.all_eq_true.mp all) (M.capability ⟨t, o⟩) member
    have missing := (R.pending t o).mp pending
    simp [missing] at produced
  · intro empty
    apply List.all_eq_true.mpr
    intro cap member
    obtain ⟨o, destination, id⟩ := fiber.represented cap member
    have notPending : o ∉ c.pending t := fun hp => empty o hp destination
    have notMissing : producedValue g (M.capability ⟨t, o⟩) ≠ none := by
      intro missing
      exact notPending ((R.pending t o).mpr missing)
    rw [id] at notMissing
    cases h : producedValue g cap with
    | none => exact False.elim (notMissing h)
    | some v => rfl

theorem collector_enabled_iff_attempt
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (t : P.Defined)
    (p : Coord (σ.signature t.val).axes) (caps : List Nat)
    (fiber : CollectorFiber M t p caps) :
    enabled g (.collect ⟨t.val, p⟩ caps) = true ↔
      (attempt P RationalReference.ops c (.publication t p)).isSome = true := by
  have empty := collector_all_produced_iff_fiberEmpty M R t p caps fiber
  simp only [enabled, Bool.and_eq_true]
  constructor
  · rintro ⟨unpublished, all⟩
    have absent : c.published ⟨t.val, p⟩ = none := by
      rw [R.published] at unpublished
      cases h : c.published ⟨t.val, p⟩ <;> simp_all
    have finished := empty.mp all
    simp only [attempt]
    split <;> simp_all
  · intro selected
    have absent : c.published ⟨t.val, p⟩ = none := by
      by_contra h
      simp only [attempt] at selected
      split at selected <;> simp_all
    have finished : P.FiberEmpty c t p := by
      by_contra h
      simp only [attempt] at selected
      split at selected <;> simp_all
    exact ⟨by rw [R.published, absent]; rfl, empty.mpr finished⟩

private theorem foldl_add_sum (values : List ℚ) :
    values.foldl (· + ·) 0 = values.sum := by
  have general (xs : List ℚ) (start : ℚ) :
      xs.foldl (· + ·) start = start + xs.sum := by
    induction xs generalizing start with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons, List.sum_cons]
      rw [ih]
      ring
  simpa using general values 0

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem collector_mapM_values (g : State σ) (caps : List Nat)
    (all : caps.all (fun cap => (producedValue g cap).isSome) = true) :
    caps.mapM (producedValue g) =
      some (caps.map fun cap => (producedValue g cap).getD 0) := by
  induction caps with
  | nil => rfl
  | cons cap caps ih =>
    have head : (producedValue g cap).isSome = true := by
      exact (List.all_eq_true.mp all) cap (by simp)
    have tail : caps.all (fun cap => (producedValue g cap).isSome) = true := by
      have h : (producedValue g cap).isSome = true ∧
          caps.all (fun cap => (producedValue g cap).isSome) = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using all
      exact h.2
    cases hcap : producedValue g cap with
    | none => simp [hcap] at head
    | some value => simp [List.mapM_cons, hcap, ih tail]

theorem collector_sum
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (injective : Function.Injective M.capability)
    (t : P.Defined) (p : Coord (σ.signature t.val).axes) (caps : List Nat)
    (fiber : CollectorFiber M t p caps)
    (all : caps.all (fun cap => (producedValue g cap).isSome) = true)
    (values : List ℚ) (mapped : caps.mapM (producedValue g) = some values) :
    values.foldl (· + ·) 0 = c.accumulators t p := by
  letI := coordDecidableEq (σ.signature t.val).axes
  have produced := collector_mapM_values g caps all
  have values_eq : values = caps.map (fun cap => (producedValue g cap).getD 0) :=
    Option.some.inj (mapped.symm.trans produced)
  let source : Finset (P.Occurrence t) :=
    Finset.univ.filter (fun o => P.destination t o.1 o.2 = p)
  let target : Finset Nat := caps.toFinset
  have reindex :
      (∑ o ∈ source, (producedValue g (M.capability ⟨t, o⟩)).getD 0) =
        ∑ cap ∈ target, (producedValue g cap).getD 0 := by
    apply Finset.sum_bij (fun o _ => M.capability ⟨t, o⟩)
    · intro o ho
      apply List.mem_toFinset.mpr
      exact (fiber.member_iff o).mpr ((Finset.mem_filter.mp ho).2)
    · intro o _ x _ same
      simpa using injective same
    · intro cap hcap
      obtain ⟨o, destination, id⟩ := fiber.represented cap
        (List.mem_toFinset.mp hcap)
      exact ⟨o, by simp [source, destination], id⟩
    · intro o _
      rfl
  have accumulator :
      c.accumulators t p =
        ∑ o ∈ source, (producedValue g (M.capability ⟨t, o⟩)).getD 0 := by
    simpa [source, Finset.sum_filter] using R.accumulators t p
  rw [values_eq, foldl_add_sum]
  calc
    (caps.map fun cap => (producedValue g cap).getD 0).sum =
        ∑ cap ∈ target, (producedValue g cap).getD 0 := by
          simpa [target] using
            (List.sum_toFinset (fun cap => (producedValue g cap).getD 0) fiber.nodup).symm
    _ = c.accumulators t p := reindex.symm.trans accumulator.symm

def publishGraph (g : State σ) (a : Address σ) (value : ℚ) : State σ :=
  letI := Program.Executor.addressEq (σ := σ)
  { g with available := Function.update g.available a (some value) }

omit [Fintype σ.Tensor] in
theorem publishGraph_extends (g : State σ) (a : Address σ) (value : ℚ)
    (fresh : g.available a = none) :
    Extends g (publishGraph g a value) := by
  simpa only [publishGraph] using collect_extends g a value fresh

theorem publication_relation
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (t : P.Defined)
    (p : Coord (σ.signature t.val).axes) (value : ℚ)
    (agree : value = c.accumulators t p) :
    Relation M (publishGraph g ⟨t.val, p⟩ value)
      (Program.Executor.publish P c t p) := by
  letI := Program.Executor.addressEq (σ := σ)
  constructor
  · change Function.update g.available ⟨t.val, p⟩ (some value) =
      Function.update c.published ⟨t.val, p⟩ (some (c.accumulators t p))
    rw [R.published, agree]
  · intro u o
    simpa [publishGraph, Program.Executor.publish] using R.pending u o
  · intro u q
    simpa [publishGraph, Program.Executor.publish] using R.accumulators u q

theorem successful_publication
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (I : LedgerInvariant M g)
    (injective : Function.Injective M.capability)
    (t : P.Defined) (p : Coord (σ.signature t.val).axes) (caps : List Nat)
    (fiber : CollectorFiber M t p caps)
    (unpublished : c.published ⟨t.val, p⟩ = none)
    (all : caps.all (fun cap => (producedValue g cap).isSome) = true)
    (values : List ℚ) (mapped : caps.mapM (producedValue g) = some values) :
    let value := values.foldl (· + ·) 0
    value = c.accumulators t p ∧
      LedgerInvariant M (publishGraph g ⟨t.val, p⟩ value) ∧
      Relation M (publishGraph g ⟨t.val, p⟩ value) (P.publish c t p) ∧
      Extends g (publishGraph g ⟨t.val, p⟩ value) := by
  have agree := collector_sum M R injective t p caps fiber all values mapped
  have fresh : g.available ⟨t.val, p⟩ = none := by
    rw [R.published]
    exact unpublished
  refine ⟨agree, ?_, ?_, publishGraph_extends g ⟨t.val, p⟩ _ fresh⟩
  · exact ⟨I.nodup, I.valid⟩
  · rw [← publish_agrees P c t p]
    exact publication_relation M R t p _ agree

end IndexedOpenComposition.Correspondence
