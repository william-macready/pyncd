import IndexedComponentCompositionMatch

namespace IndexedComponentComposition

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor
open IndexedComponentTransport
open IndexedOpenComposition

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (wire : Boundary A B)

private theorem find_transported_collector_row {α β : Declarations Unit}
    [DecidableEq (Address α)] [DecidableEq (Address β)]
    (f : Embedding α β) (rename : Nat → Nat)
    (rows : List (Address α × List Nat)) (a : Address α) :
    (rows.map (mapRow f rename)).find?
        (fun row => decide (row.1 = f.address a)) =
      (rows.find? (fun row => decide (row.1 = a))).map
        (mapRow f rename) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases h : row.1 = a
    · simp [List.find?, mapRow, h]
    · have h' : f.address row.1 ≠ f.address a :=
        fun eq => h (f.address_injective eq)
      simp [List.find?, mapRow, h, h', ih]

private theorem find_outside_collector_row {α β : Declarations Unit}
    [DecidableEq (Address β)] (f : Embedding α β) (rename : Nat → Nat)
    (rows : List (Address α × List Nat)) (z : Address β)
    (h : ∀ row ∈ rows, f.address row.1 ≠ z) :
    (rows.map (mapRow f rename)).find?
      (fun row => decide (row.1 = z)) = none := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp [mapRow, h row (by simp), ih (by
      intro r hr
      exact h r (by simp [hr]))]

theorem collectorCapabilities_upstream
    (a : Address σA) (ha : A.contract.input a.1 = false) :
    collectorCapabilities (contract A B wire) ((upstream A B).address a) =
      (collectorCapabilities A.contract a).map upstreamId := by
  letI := Program.Executor.addressEq (σ := σA)
  letI := Program.Executor.addressEq (σ := declarations A B)
  have hbFacts := ClosureFacts.of_close B.matched.close_ok
  have hnone :
      (B.contract.collectors.map
        (mapRow (downstream A B wire) downstreamId)).find?
        (fun row => decide (row.1 = (upstream A B).address a)) = none := by
    apply find_outside_collector_row (downstream A B wire) downstreamId
    intro row hr heq
    exact (closureScope A B wire).defined_disjoint a row.1 ha
      (hbFacts.collectors_defined row hr) heq.symm
  change (((A.contract.collectors.map (mapRow (upstream A B) upstreamId) ++
      B.contract.collectors.map (mapRow (downstream A B wire) downstreamId)).find?
      (fun row => decide (row.1 = (upstream A B).address a))).map Prod.snd).getD [] =
    (collectorCapabilities A.contract a).map upstreamId
  rw [List.find?_append, hnone, Option.or_none,
    find_transported_collector_row]
  unfold collectorCapabilities
  cases A.contract.collectors.find? (fun row => decide (row.1 = a)) <;>
    simp [mapRow]

theorem collectorCapabilities_downstream
    (b : Address σB) (hb : B.contract.input b.1 = false) :
    collectorCapabilities (contract A B wire)
        ((downstream A B wire).address b) =
      (collectorCapabilities B.contract b).map downstreamId := by
  letI := Program.Executor.addressEq (σ := σB)
  letI := Program.Executor.addressEq (σ := declarations A B)
  have haFacts := ClosureFacts.of_close A.matched.close_ok
  have hnone :
      (A.contract.collectors.map (mapRow (upstream A B) upstreamId)).find?
        (fun row => decide (row.1 = (downstream A B wire).address b)) = none := by
    apply find_outside_collector_row (upstream A B) upstreamId
    intro row hr heq
    exact (closureScope A B wire).defined_disjoint row.1 b
      (haFacts.collectors_defined row hr) hb heq
  change (((A.contract.collectors.map (mapRow (upstream A B) upstreamId) ++
      B.contract.collectors.map (mapRow (downstream A B wire) downstreamId)).find?
      (fun row => decide (row.1 = (downstream A B wire).address b))).map Prod.snd).getD [] =
    (collectorCapabilities B.contract b).map downstreamId
  rw [List.find?_append, hnone, Option.none_or,
    find_transported_collector_row]
  unfold collectorCapabilities
  cases B.contract.collectors.find? (fun row => decide (row.1 = b)) <;>
    simp [mapRow]

private theorem keyStep_upstream (k : Key A.program) :
    keyStep (program A B wire) (contract A B wire) (fragment A B wire)
        (sourceToWriter A B wire) ((keyEquiv A B wire).symm (.inl k)) =
      mapStep (upstream A B) upstreamId
        (keyStep A.program A.contract A.fragment A.matched.sourceToWriter k) := by
  cases k with
  | occurrence t o =>
    change Step.write ((fragment A B wire).writers[
        sourceToWriter A B wire
          ((occurrenceEquiv A B wire).symm (.inl ⟨t, o⟩))]) =
      Step.write (mapWriter (upstream A B) upstreamId
        A.fragment.writers[A.matched.sourceToWriter ⟨t, o⟩])
    rw [writer_upstream]
  | publication t p =>
    have ht : A.contract.input t.val = false := by
      rw [A.matched.input_roles]
      exact t.property
    change Step.collect ((upstream A B).address ⟨t.val, p⟩)
        (collectorCapabilities (contract A B wire)
          ((upstream A B).address ⟨t.val, p⟩)) =
      Step.collect ((upstream A B).address ⟨t.val, p⟩)
        ((collectorCapabilities A.contract ⟨t.val, p⟩).map upstreamId)
    rw [collectorCapabilities_upstream A B wire ⟨t.val, p⟩ ht]

private theorem keyStep_downstream (k : Key B.program) :
    keyStep (program A B wire) (contract A B wire) (fragment A B wire)
        (sourceToWriter A B wire) ((keyEquiv A B wire).symm (.inr k)) =
      mapStep (downstream A B wire) downstreamId
        (keyStep B.program B.contract B.fragment B.matched.sourceToWriter k) := by
  cases k with
  | occurrence t o =>
    change Step.write ((fragment A B wire).writers[
        sourceToWriter A B wire
          ((occurrenceEquiv A B wire).symm (.inr ⟨t, o⟩))]) =
      Step.write (mapWriter (downstream A B wire) downstreamId
        B.fragment.writers[B.matched.sourceToWriter ⟨t, o⟩])
    rw [writer_downstream]
  | publication t p =>
    have ht : B.contract.input t.val = false := by
      rw [B.matched.input_roles]
      exact t.property
    change Step.collect ⟨(downstreamDefined A B wire t).val, p⟩
        (collectorCapabilities (contract A B wire)
          ⟨(downstreamDefined A B wire t).val, p⟩) =
      Step.collect ((downstream A B wire).address ⟨t.val, p⟩)
        ((collectorCapabilities B.contract ⟨t.val, p⟩).map downstreamId)
    rw [← downstream_defined_address A B wire t p,
      collectorCapabilities_downstream A B wire ⟨t.val, p⟩ ht]

theorem priority :
    (schedule A B wire).keys.map
        (keyStep (program A B wire) (contract A B wire) (fragment A B wire)
          (sourceToWriter A B wire)) =
      (graph A B wire).steps := by
  change (keyOrder A B wire).map
      (keyStep (program A B wire) (contract A B wire) (fragment A B wire)
        (sourceToWriter A B wire)) = _
  rw [keyOrder, List.map_append, List.map_map, List.map_map]
  simp only [Function.comp_def, keyStep_upstream, keyStep_downstream]
  have hA := A.matched.priority.trans
    (close_success_canonical A.matched.close_ok).2
  have hB := B.matched.priority.trans
    (close_success_canonical B.matched.close_ok).2
  apply Eq.trans ?_ (graph_steps A B wire).symm
  simpa only [List.map_map, Function.comp_def] using
    congrArg₂ List.append
      (congrArg (List.map (mapStep (upstream A B) upstreamId)) hA)
      (congrArg (List.map (mapStep (downstream A B wire) downstreamId)) hB)

end IndexedComponentComposition
