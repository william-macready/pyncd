import IndexedAffineScanHistory
import IndexedRankedWitnessOutcomes
import IndexedRankedOperationalReference

/-! The default executions below are the existing exact-rational semantic executors,
not the Float scan backend. Administrative wires and their domains are unchanged. -/

namespace IndexedExecutionExperiment.AffineScan.Interpretation

open LeanNCD.Semantics IndexedOpenComposition IndexedComponentComposition
open IndexedComponentExecution IndexedWitness CategoryTheory
open History

variable (p : Profile d n)

/-- Actual default checked and reference runs complete with the entire rational table solution.
These are the exact-rational semantic executors, not the Float scan backend: no `runDenseScan`
correctness is claimed. -/
theorem default_full_history (η : (program p).Input) :
    ∃ (g : State (declarations p)) (c : (program p).Running)
        (finished : (program p).Complete c),
      (runChecked (contract p) (fragment p) η.val).outcome = .complete g ∧
      (Program.Executor.run (program p) RationalReference.ops (schedule p) η).outcome =
        .complete c finished ∧
      Relation (sourceMatch p) g c ∧
      (∀ a, g.available a = some (wholeStore p η a)) ∧
      (program p).finalStore c finished = wholeStore p η :=
  (IndexedRankedWitnessOutcomes.model_iff_actual_full
    (component p) (rankCertificate p) η (wholeStore p η)).mp (wholeStore_model p η)

theorem recurrence_iff_actual_full (η : (program p).Input) (ρ : FullStore p) :
    Recurrence p η ρ ↔
      ∃ (g : State (declarations p)) (c : (program p).Running)
          (finished : (program p).Complete c),
        (runChecked (contract p) (fragment p) η.val).outcome = .complete g ∧
        (Program.Executor.run (program p) RationalReference.ops (schedule p) η).outcome =
          .complete c finished ∧
        Relation (sourceMatch p) g c ∧
        (∀ a, g.available a = some (ρ a)) ∧
        (program p).finalStore c finished = ρ :=
  (models_iff_recurrence p η ρ).symm.trans
    (IndexedRankedWitnessOutcomes.model_iff_actual_full
      (component p) (rankCertificate p) η ρ)

theorem witness_domain (η : (program p).Input) :
    (componentSpan (component p)).Domain (inputEnv (component p) η) :=
  (IndexedRankedWitnessOutcomes.domain_iff_checked (component p) (rankCertificate p) η).mpr
    (by obtain ⟨g, _, _, done, _⟩ := default_full_history p η; exact ⟨g, done⟩)

theorem witness_full_history_value (η : (program p).Input) :
    (componentSpan (component p)).value
        (IndexedRankedWitnessBridge.component_left_injective (component p) (rankCertificate p))
        (inputEnv (component p) η) (witness_domain p η) =
      (outputEquiv (component p)).symm ((program p).outputProjection (wholeStore p η)) := by
  let w : (componentSpan (component p)).W :=
    ⟨η, ⟨wholeStore p η, wholeStore_model p η⟩⟩
  exact (componentSpan (component p)).value_eq
    (IndexedRankedWitnessBridge.component_left_injective (component p) (rankCertificate p))
    (witness_domain p η) w rfl

theorem witness_coordinate (η : (program p).Input) (q : Coord (historyShape d n)) :
    (componentSpan (component p)).value
        (IndexedRankedWitnessBridge.component_left_injective (component p) (rankCertificate p))
        (inputEnv (component p) η) (witness_domain p η)
        ⟨.inr (), rfl⟩ q =
      wholeStore p η ⟨.inr (), q⟩ := by
  rw [witness_full_history_value]
  rfl

theorem witness_total (x : (inputInterface (component p)).Env) :
    (componentSpan (component p)).Domain x := by
  simpa only [inputEnv_envInput] using witness_domain p (envInput (component p) x)

theorem history_port_metadata :
    (component p).outputs.map (fun port => port.axes) = [historyShape d n] := rfl

theorem history_port_count : (component p).outputs.length = 1 := rfl

noncomputable def normal :
    IndexedRankedOperationalCore.Normal
      (IndexedSource.input (component p)) (IndexedSource.output (component p)) :=
  IndexedRankedOperationalCore.Normal.leaf (component p) (rankCertificate p)

noncomputable def sourceTerm :
    IndexedRankedOperationalSource.Term
      (IndexedRankedOperationalSource.input (component p))
      (IndexedRankedOperationalSource.output (component p)) :=
  .leaf (component p) (rankCertificate p) (.opaque (component p) ⟨rankCertificate p⟩)

noncomputable def sourceArrow :=
  IndexedRankedOperationalSource.arrow (sourceTerm p)

noncomputable def operationalArrow :=
  IndexedRankedOperationalSource.semantics.map (sourceArrow p)

noncomputable def witnessArrow :=
  IndexedRankedWitnessComparison.comparison.map (operationalArrow p)

theorem source_normal :
    (sourceTerm p).normalize = normal p := rfl

theorem categorical_comparison :
    witnessArrow p = IndexedRankedWitnessDescent.normalHom (normal p) := rfl

theorem witness_source_comparison :
    witnessArrow p = (IndexedRankedWitnessSource.eraseTerm (sourceTerm p)).denote :=
  (IndexedRankedWitnessDescent.source_denote (normal p)).symm.trans
    (IndexedRankedWitnessSource.normalize_denote (sourceTerm p))

/-- The complete-witness comparison arrow is the quotient of the constructed component's span, so it
retains the whole history. Exact-rational meaning only; no Float `runDenseScan` claim. -/
theorem categorical_whole_history :
    witnessArrow p = (Quotient.mk _ (componentSpan (component p)) :
      inputInterface (component p) ⟶ outputInterface (component p)) :=
  witness_source_comparison p

noncomputable def referenceObservation (η : (program p).Input) :=
  IndexedRankedOperationalReference.actualReferenceObservation (component p)
    (.opaque (component p) ⟨rankCertificate p⟩) η (rankCertificate p)

theorem reference_full_relations (η : (program p).Input) :
    List.Forall₂
      (fun state running => LedgerInvariant (sourceMatch p) state ∧
        Relation (sourceMatch p) state running)
      (referenceObservation p η).observation.history.states
      (Correspondence.referenceSnapshots ((program p).initial η)
        (Program.Executor.run (program p) RationalReference.ops (schedule p) η).events) :=
  IndexedRankedOperationalReference.actual_reference_states (component p)
    (.opaque (component p) ⟨rankCertificate p⟩) η (rankCertificate p)

theorem operational_history_full (η : (program p).Input) :
    ∃ g, (referenceObservation p η).observation.history.toRun.outcome = .complete g ∧
      ∀ a, g.available a = some (wholeStore p η a) := by
  obtain ⟨g, c, finished, done, reference, related, full, final⟩ := default_full_history p η
  refine ⟨g, ?_, full⟩
  change (IndexedRankedOperationalCore.actualHistory (component p) η
    (rankCertificate p)).toRun.outcome = .complete g
  rw [(IndexedRankedOperationalCore.actualHistory_spec
    (component p) η (rankCertificate p)).2.1]
  exact done

end IndexedExecutionExperiment.AffineScan.Interpretation

#print axioms IndexedExecutionExperiment.AffineScan.Interpretation.default_full_history
#print axioms IndexedExecutionExperiment.AffineScan.Interpretation.categorical_whole_history
#print axioms IndexedExecutionExperiment.AffineScan.Interpretation.operational_history_full
#audit_axioms IndexedExecutionExperiment.AffineScan.Interpretation
