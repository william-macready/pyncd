import IndexedCompositionMatch

namespace IndexedOpenComposition.Correspondence

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {schedule : Schedule P} {contract : Contract σ} {fragment : Fragment σ}
variable {graph : Closed σ}

def observation
    (M : SourceContractMatch P schedule contract fragment graph) :
    Observation P → Nat × List (Address σ)
  | .unavailable t o missing => (M.tag ⟨t, o⟩, missing)
  | .ready t o _ => (M.tag ⟨t, o⟩, [])

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem blocked_pending_notReady (c : P.Running)
    (blocked : P.Blocked RationalReference.ops c)
    (t : P.Defined) (o : P.Occurrence t) (pending : o ∈ c.pending t) :
    evalReady RationalReference.ops c.published (P.body t o.1) o.2 = .notReady := by
  cases he : evalReady RationalReference.ops c.published (P.body t o.1) o.2 with
  | notReady => rfl
  | evaluated value =>
      apply False.elim
      cases value with
      | none => exact blocked.2 ⟨_, Program.Step.undefined c t o pending he⟩
      | some value => exact blocked.2 ⟨_, Program.Step.contribute c t o value pending he⟩

theorem missingReads_agrees
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) :
    missingReads graph.steps g =
      (observations P RationalReference.ops schedule c).map (observation M) := by
  rw [← M.priority]
  simp only [missingReads, List.filterMap_map, observations, List.map_filterMap]
  congr 1
  funext key
  cases key with
  | publication t p => rfl
  | occurrence t o =>
      have reads := M.writer_reads ⟨t, o⟩
      change (M.writer ⟨t, o⟩).reads = _ at reads
      by_cases pending : o ∈ c.pending t
      · have absent := (R.pending t o).mp pending
        change
          (if (producedValue g (M.capability ⟨t, o⟩)).isSome then none
            else some (M.tag ⟨t, o⟩,
              (M.writer ⟨t, o⟩).reads.filter fun a => (g.available a).isNone)) = _
        rw [absent]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          pending, reads, R.published]
        cases he : evalReady RationalReference.ops c.published (P.body t o.1) o.2 with
        | notReady => rfl
        | evaluated value =>
            have ready : Ready c.published (P.body t o.1) o.2 := by
              by_contra hn
              have notReady := (notReady_iff RationalReference.ops
                (P.body t o.1) o.2 c.published).mpr hn
              rw [he] at notReady
              contradiction
            have empty :
                (footprint (P.body t o.1) o.2).filter
                  (fun a => (c.published a).isNone) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro a member
              have present := ready a member
              cases h : c.published a <;> simp_all
            simp [empty, observation]
      · have present : producedValue g (M.capability ⟨t, o⟩) ≠ none :=
          fun absent => pending ((R.pending t o).mpr absent)
        have someValue : (producedValue g (M.capability ⟨t, o⟩)).isSome = true := by
          cases h : producedValue g (M.capability ⟨t, o⟩) <;> simp_all
        change
          (if (producedValue g (M.capability ⟨t, o⟩)).isSome then none
            else some (M.tag ⟨t, o⟩,
              (M.writer ⟨t, o⟩).reads.filter fun a => (g.available a).isNone)) = _
        simp [someValue, pending]

end IndexedOpenComposition.Correspondence
