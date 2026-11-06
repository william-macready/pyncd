import IndexedCompositionMatch
import IndexedCompositionRunner

namespace IndexedOpenComposition.Correspondence

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {schedule : Schedule P} {contract : Contract σ} {fragment : Fragment σ}
variable {graph : Closed σ}

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
def appendContribution
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (o : SourceOccurrence P) (v : ℚ) : State σ :=
  { g with produced := g.produced ++ [(M.capability o, v)] }

theorem appendContribution_produced
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (o : SourceOccurrence P) (v : ℚ) :
    (appendContribution M g o v).produced = g.produced ++ [(M.capability o, v)] := rfl

theorem appendContribution_available
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (o : SourceOccurrence P) (v : ℚ) :
    (appendContribution M g o v).available = g.available := rfl

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
private theorem fresh_capability_not_mem (g : State σ) (cap : Nat)
    (fresh : producedValue g cap = none) : cap ∉ g.produced.map Prod.fst := by
  intro hmem
  obtain ⟨row, inLedger, eqCap⟩ := List.mem_map.mp hmem
  have absent : g.produced.find? (fun row => row.1 == cap) = none := by
    simpa [producedValue] using fresh
  have hn := (List.find?_eq_none.mp absent) row inLedger
  simp_all

theorem appendContribution_ledger
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (o : SourceOccurrence P) (v : ℚ)
    (I : LedgerInvariant M g)
    (fresh : producedValue g (M.capability o) = none) :
    LedgerInvariant M (appendContribution M g o v) := by
  have missing := fresh_capability_not_mem g (M.capability o) fresh
  constructor
  · simp only [appendContribution, List.map_append, List.map_singleton]
    simp only [List.nodup_append]
    refine ⟨I.nodup, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact fun eq => missing (eq ▸ ha)
  · intro cap value h
    have h' : (cap, value) ∈ g.produced ∨ (cap, value) = (M.capability o, v) := by
      simpa [appendContribution] using h
    rcases h' with old | added
    · exact I.valid cap value old
    · cases added
      exact ⟨o, rfl⟩

theorem appendContribution_value
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (o x : SourceOccurrence P) (v : ℚ)
    (fresh : producedValue g (M.capability o) = none)
    (injective : Function.Injective M.capability) :
    producedValue (appendContribution M g o v) (M.capability x) =
      if x = o then some v else producedValue g (M.capability x) := by
  have keys : M.capability x = M.capability o ↔ x = o := injective.eq_iff
  simpa only [appendContribution, producedValue_append g (M.capability o) v fresh,
    keys]

theorem appendContribution_sum_same
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (t : P.Defined) (o : P.Occurrence t) (v : ℚ)
    (fresh : producedValue g (M.capability ⟨t, o⟩) = none)
    (injective : Function.Injective M.capability)
    (p : Coord (σ.signature t.val).axes) :
    (letI := coordDecidableEq (σ.signature t.val).axes
     ∑ x : P.Occurrence t, if P.destination t x.1 x.2 = p then
       (producedValue (appendContribution M g ⟨t, o⟩ v)
         (M.capability ⟨t, x⟩)).getD 0 else 0) =
      (letI := coordDecidableEq (σ.signature t.val).axes
       (∑ x : P.Occurrence t, if P.destination t x.1 x.2 = p then
         (producedValue g (M.capability ⟨t, x⟩)).getD 0 else 0) +
        if P.destination t o.1 o.2 = p then v else 0) := by
  letI := coordDecidableEq (σ.signature t.val).axes
  have term (x : P.Occurrence t) :
      (if P.destination t x.1 x.2 = p then
        (producedValue (appendContribution M g ⟨t, o⟩ v)
          (M.capability ⟨t, x⟩)).getD 0 else 0) =
      (if P.destination t x.1 x.2 = p then
        (producedValue g (M.capability ⟨t, x⟩)).getD 0 else 0) +
        if x = o then (if P.destination t o.1 o.2 = p then v else 0) else 0 := by
    rw [appendContribution_value M g ⟨t, o⟩ ⟨t, x⟩ v fresh injective]
    by_cases hx : x = o
    · subst x
      simp [fresh]
    · simp [hx]
  calc
    (∑ x : P.Occurrence t, if P.destination t x.1 x.2 = p then
      (producedValue (appendContribution M g ⟨t, o⟩ v)
        (M.capability ⟨t, x⟩)).getD 0 else 0) =
        ∑ x : P.Occurrence t,
          ((if P.destination t x.1 x.2 = p then
            (producedValue g (M.capability ⟨t, x⟩)).getD 0 else 0) +
            (if x = o then (if P.destination t o.1 o.2 = p then v else 0) else 0)) :=
      Finset.sum_congr rfl (fun x _ => term x)
    _ = (∑ x : P.Occurrence t, if P.destination t x.1 x.2 = p then
          (producedValue g (M.capability ⟨t, x⟩)).getD 0 else 0) +
        if P.destination t o.1 o.2 = p then v else 0 := by
      rw [Finset.sum_add_distrib]
      simp

theorem appendContribution_sum_other
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (t u : P.Defined) (o : P.Occurrence t) (v : ℚ)
    (fresh : producedValue g (M.capability ⟨t, o⟩) = none)
    (injective : Function.Injective M.capability) (different : u ≠ t)
    (p : Coord (σ.signature u.val).axes) :
    (letI := coordDecidableEq (σ.signature u.val).axes
     ∑ x : P.Occurrence u, if P.destination u x.1 x.2 = p then
       (producedValue (appendContribution M g ⟨t, o⟩ v)
         (M.capability ⟨u, x⟩)).getD 0 else 0) =
      (letI := coordDecidableEq (σ.signature u.val).axes
       ∑ x : P.Occurrence u, if P.destination u x.1 x.2 = p then
         (producedValue g (M.capability ⟨u, x⟩)).getD 0 else 0) := by
  letI := coordDecidableEq (σ.signature u.val).axes
  apply Finset.sum_congr rfl
  intro x _
  rw [appendContribution_value M g ⟨t, o⟩ ⟨u, x⟩ v fresh injective]
  have h : (⟨u, x⟩ : SourceOccurrence P) ≠ ⟨t, o⟩ :=
    fun eq => different (congrArg Sigma.fst eq)
  simp [h]

theorem contribution_relation
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (injective : Function.Injective M.capability)
    (t : P.Defined) (o : P.Occurrence t) (v : ℚ)
    (pending : o ∈ c.pending t) :
    Relation M (appendContribution M g ⟨t, o⟩ v)
      (Program.Executor.consume P c t o v) := by
  have fresh := (R.pending t o).mp pending
  constructor
  · simpa [appendContribution, Program.Executor.consume] using R.published
  · intro u x
    rw [appendContribution_value M g ⟨t, o⟩ ⟨u, x⟩ v fresh injective]
    by_cases hu : u = t
    · subst u
      have updated : (Program.Executor.consume P c t o v).pending t =
          (c.pending t).erase o := by simp [Program.Executor.consume]
      rw [updated]
      by_cases hx : x = o
      · subst x
        simp
      · have different : (⟨t, x⟩ : SourceOccurrence P) ≠ ⟨t, o⟩ := by
          simpa using hx
        simpa [Finset.mem_erase, hx, different] using R.pending t x
    · have updated : (Program.Executor.consume P c t o v).pending u =
          c.pending u := by simp [Program.Executor.consume, hu]
      rw [updated]
      have different : (⟨u, x⟩ : SourceOccurrence P) ≠ ⟨t, o⟩ :=
        fun eq => hu (congrArg Sigma.fst eq)
      simpa [different] using R.pending u x
  · intro u p
    letI := coordDecidableEq (σ.signature u.val).axes
    by_cases hu : u = t
    · subst u
      have updated : (Program.Executor.consume P c t o v).accumulators t p =
          c.accumulators t p + if P.destination t o.1 o.2 = p then v else 0 := by
        letI := coordDecidableEq (σ.signature t.val).axes
        simp [Program.Executor.consume]
      rw [updated, R.accumulators t p]
      exact (appendContribution_sum_same M g t o v fresh injective p).symm
    · have updated : (Program.Executor.consume P c t o v).accumulators u p =
          c.accumulators u p := by simp [Program.Executor.consume, hu]
      rw [updated, R.accumulators u p]
      exact (appendContribution_sum_other M g t u o v fresh injective hu p).symm

theorem writer_eval
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (t : P.Defined) (o : P.Occurrence t) :
    evalReady RationalReference.ops g.available (M.writer ⟨t, o⟩).body () =
      evalReady RationalReference.ops c.published (P.body t o.1) o.2 := by
  rw [R.published]
  exact M.eval_agrees ⟨t, o⟩ c.published

theorem writer_reads_ready
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (t : P.Defined) (o : P.Occurrence t) :
    (M.writer ⟨t, o⟩).reads.all (fun a => (g.available a).isSome) = true ↔
      evalReady RationalReference.ops c.published (P.body t o.1) o.2 ≠ .notReady := by
  have reads : (M.writer ⟨t, o⟩).reads = footprint (P.body t o.1) o.2 :=
    M.writer_reads ⟨t, o⟩
  rw [ne_eq, notReady_iff, not_not, Ready, ← R.published, reads]
  simp only [List.all_eq_true]

theorem write_enabled_iff_attempt
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (t : P.Defined) (o : P.Occurrence t) :
    enabled g (.write (M.writer ⟨t, o⟩)) = true ↔
      (attempt P RationalReference.ops c (.occurrence t o)).isSome = true := by
  have hp := R.pending t o
  have hr := writer_reads_ready M R t o
  simp only [enabled, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, reads⟩
    have pending : o ∈ c.pending t := hp.mpr (by simpa using hc)
    have ready := hr.mp reads
    simp only [attempt, dif_pos pending]
    split <;> simp_all
  · intro selected
    by_cases pending : o ∈ c.pending t
    · have hc := hp.mp pending
      have ready : evalReady RationalReference.ops c.published
          (P.body t o.1) o.2 ≠ .notReady := by
        intro he
        simp only [attempt, dif_pos pending] at selected
        split at selected <;> simp_all
      exact ⟨by simpa using hc, hr.mpr ready⟩
    · simp [attempt, pending] at selected

theorem undefined_eval
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (t : P.Defined) (o : P.Occurrence t)
    (undefined : evalReady RationalReference.ops c.published (P.body t o.1) o.2 =
      .evaluated none) :
    evalReady RationalReference.ops g.available (M.writer ⟨t, o⟩).body () =
      .evaluated none := by
  rw [writer_eval M R t o]
  exact undefined

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem undefined_attempt
    (t : P.Defined) (o : P.Occurrence t) (c : P.Running)
    (pending : o ∈ c.pending t)
    (undefined : evalReady RationalReference.ops c.published (P.body t o.1) o.2 =
      .evaluated none) :
    ∃ move : Move P RationalReference.ops c,
      attempt P RationalReference.ops c (.occurrence t o) = some move ∧
        move.event = .undefined t o := by
  refine ⟨⟨.undefined t o, pending, undefined⟩, ?_, rfl⟩
  simp only [attempt, dif_pos pending]
  split
  · simp_all
  · simp_all
  · rename_i v he
    rw [undefined] at he
    cases he

theorem successful_contribution
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (I : LedgerInvariant M g)
    (injective : Function.Injective M.capability)
    (t : P.Defined) (o : P.Occurrence t) (v : ℚ)
    (pending : o ∈ c.pending t)
    (evaluated : evalReady RationalReference.ops c.published
      (P.body t o.1) o.2 = .evaluated (some v)) :
    evalReady RationalReference.ops g.available (M.writer ⟨t, o⟩).body () =
      .evaluated (some v) ∧
    LedgerInvariant M (appendContribution M g ⟨t, o⟩ v) ∧
    Relation M (appendContribution M g ⟨t, o⟩ v) (P.consume c t o v) := by
  have fresh := (R.pending t o).mp pending
  refine ⟨(writer_eval M R t o).trans evaluated,
    appendContribution_ledger M g ⟨t, o⟩ v I fresh, ?_⟩
  rw [← consume_agrees P c t o v]
  exact contribution_relation M R injective t o v pending

theorem undefined_alignment
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c)
    (t : P.Defined) (o : P.Occurrence t)
    (pending : o ∈ c.pending t)
    (undefined : evalReady RationalReference.ops c.published (P.body t o.1) o.2 =
      .evaluated none) :
    enabled g (.write (M.writer ⟨t, o⟩)) = true ∧
    evalReady RationalReference.ops g.available (M.writer ⟨t, o⟩).body () =
      .evaluated none ∧
    (Program.Executor.Event.undefined t o).effect P c = .failed t o c := by
  have ready : (attempt P RationalReference.ops c (.occurrence t o)).isSome = true := by
    obtain ⟨move, selected, _⟩ := undefined_attempt t o c pending undefined
    simp [selected]
  exact ⟨(write_enabled_iff_attempt M R t o).mpr ready,
    undefined_eval M R t o undefined, rfl⟩

end IndexedOpenComposition.Correspondence
