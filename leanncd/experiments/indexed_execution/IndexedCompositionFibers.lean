import IndexedCompositionClosure
import IndexedCompositionPublication

namespace IndexedOpenComposition

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor
open IndexedOpenComposition.Correspondence

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {schedule : Schedule P} {contract : Contract σ} {fragment : Fragment σ}
variable {graph : Closed σ}

theorem SourceContractMatch.capability_injective
    (M : SourceContractMatch P schedule contract fragment graph) :
    Function.Injective M.capability := by
  intro x y same
  apply M.sourceToWriter.injective
  apply Fin.ext
  have nodup := close_success_writer_capabilities_nodup M.close_ok
  have hi : (M.sourceToWriter x).val <
      (fragment.writers.map Writer.capability).length := by simp
  have hj : (M.sourceToWriter y).val <
      (fragment.writers.map Writer.capability).length := by simp
  apply (nodup.getElem_inj_iff (hi := hi) (hj := hj)).mp
  simpa only [List.getElem_map, SourceContractMatch.capability,
    SourceContractMatch.writer] using same

theorem SourceContractMatch.collector_row
    (M : SourceContractMatch P schedule contract fragment graph)
    (t : P.Defined) (p : Coord (σ.signature t.val).axes) :
    ∃ row ∈ contract.collectors,
      row.1 = (⟨t.val, p⟩ : Address σ) ∧
      collectorCapabilities contract ⟨t.val, p⟩ = row.2 := by
  have covered : (⟨t.val, p⟩ : Address σ) ∈ definedAddresses contract := by
    apply List.mem_flatMap.mpr
    refine ⟨t.val, ?_, ?_⟩
    · apply List.mem_filter.mpr
      exact ⟨close_success_tensors_complete M.close_ok t.val,
        by simp [M.input_roles, t.property]⟩
    · apply List.mem_map.mpr
      refine ⟨(canonicalLayout (σ.signature t.val).axes).enumerate.symm p,
        List.mem_finRange _, ?_⟩
      simp
  have member := close_success_defined_covered M.close_ok _ covered
  obtain ⟨row, inRows, address⟩ := List.mem_map.mp member
  letI := Program.Executor.addressEq (σ := σ)
  cases found : contract.collectors.find?
      (fun r => decide (r.1 = (⟨t.val, p⟩ : Address σ))) with
  | none =>
      have absent := List.find?_eq_none.mp found row inRows
      simp [address] at absent
  | some actual =>
      have selected := List.find?_some found
      have actualAddress : actual.1 = (⟨t.val, p⟩ : Address σ) := by
        simpa using selected
      refine ⟨actual, List.mem_of_find?_eq_some found,
        actualAddress, ?_⟩
      simp [collectorCapabilities, found]

theorem SourceContractMatch.collectorFiber
    (M : SourceContractMatch P schedule contract fragment graph)
    (t : P.Defined) (p : Coord (σ.signature t.val).axes) :
    CollectorFiber M t p (collectorCapabilities contract ⟨t.val, p⟩) := by
  obtain ⟨row, inRows, address, capabilities⟩ := M.collector_row t p
  constructor
  · rw [capabilities]
    exact (List.nodup_flatMap.mp (close_success_capabilities_nodup M.close_ok)).1
      row inRows
  · intro cap member
    rw [capabilities] at member
    obtain ⟨w, inWriters, capEq⟩ :=
      close_success_capability_covered M.close_ok cap
        (List.mem_flatMap.mpr ⟨row, inRows, member⟩)
    obtain ⟨index, writerEq⟩ := List.mem_iff_get.mp inWriters
    let source := M.sourceToWriter.symm index
    have matched : M.writer source = w := by
      simpa only [SourceContractMatch.writer, source, Equiv.apply_symm_apply] using writerEq
    have destination : w.destination = row.1 :=
      (close_success_writer_destination_iff M.close_ok inWriters inRows).mp
        (by simpa [capEq] using member)
    have destAddress :
        (⟨source.1.val, P.destination source.1 source.2.1 source.2.2⟩ : Address σ) =
          ⟨t.val, p⟩ :=
      (M.writer_destination source).symm.trans
        ((congrArg Writer.destination matched).trans (destination.trans address))
    have sameTensor : source.1 = t :=
      Subtype.ext (congrArg Sigma.fst destAddress)
    rcases source with ⟨u, o⟩
    dsimp at sameTensor
    subst u
    refine ⟨o, ?_, ?_⟩
    · exact eq_of_heq (Sigma.mk.inj destAddress).2
    · exact (congrArg Writer.capability matched).trans capEq
  · intro o
    rw [capabilities]
    have inWriters : M.writer ⟨t, o⟩ ∈ fragment.writers :=
      List.getElem_mem (M.sourceToWriter ⟨t, o⟩).isLt
    have membership :=
      close_success_writer_destination_iff M.close_ok inWriters inRows
    have destination := M.writer_destination ⟨t, o⟩
    change (M.writer ⟨t, o⟩).destination =
      (⟨t.val, P.destination t o.1 o.2⟩ : Address σ) at destination
    change (M.writer ⟨t, o⟩).capability ∈ row.2 ↔ _
    rw [membership, destination, address]
    constructor
    · intro same
      exact eq_of_heq (Sigma.mk.inj same).2
    · intro same
      cases same
      rfl

end IndexedOpenComposition
