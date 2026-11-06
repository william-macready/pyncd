import IndexedCompositionCorrespondence
import IndexedCompositionFibers
import IndexedCompositionSemanticResults

namespace IndexedOpenComposition.Correspondence

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {schedule : Schedule P} {contract : Contract σ} {fragment : Fragment σ}
variable {graph : Closed σ}

theorem accepted_correspondence_of_fibers
    (M : SourceContractMatch P schedule contract fragment graph)
    (canonical : graph.contract = contract)
    (capInjective : Function.Injective M.capability)
    (fibers : ∀ t (p : Coord (σ.signature t.val).axes),
      CollectorFiber M t p (collectorCapabilities contract ⟨t.val, p⟩))
    (η : P.Input) :
    ExecutionCorrespondence M (runChecked contract fragment η.val) (P.initial η)
      (Executor.run P RationalReference.ops schedule η) := by
  have accepted := validate_accepts P schedule η
  obtain ⟨valid, ledger, related⟩ := initial_related_raw M η.val η accepted
  have validator :
      graph.contract.tensors.find?
        (fun t => (η.val t).isSome != graph.contract.input t) = none := by
    simpa only [canonical, invalidInputTensor] using valid
  have proof := runFuel_correspondence M capInjective fibers
    (graph.steps.length + 1) (initial η.val) (P.initial η)
    ledger related (initial_inputs_available η)
  simpa only [runChecked, M.close_ok, execute, validator, Option.getD_none,
    Executor.run, default_budgets_agree M] using proof

def ValidatedCorrespondence
    (M : SourceContractMatch P schedule contract fragment graph)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ)) : Prop :=
  match runValidated P RationalReference.ops schedule η with
  | .error tensor =>
      let candidate := runChecked contract fragment η
      candidate.outcome = .invalidInput tensor ∧
        candidate.events = [] ∧ candidate.states = []
  | .ok reference =>
      ExecutionCorrespondence M (runChecked contract fragment η)
        (P.initial reference.input) reference.result

theorem validated_correspondence_of_fibers
    (M : SourceContractMatch P schedule contract fragment graph)
    (canonical : graph.contract = contract)
    (capInjective : Function.Injective M.capability)
    (fibers : ∀ t (p : Coord (σ.signature t.val).axes),
      CollectorFiber M t p (collectorCapabilities contract ⟨t.val, p⟩))
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ)) :
    ValidatedCorrespondence M η := by
  unfold ValidatedCorrespondence runValidated
  cases validation : validate P schedule η with
  | error tensor =>
      have invalid := (validation_first_error M η tensor).mp validation
      have validator :
          graph.contract.tensors.find?
            (fun t => (η t).isSome != graph.contract.input t) = some tensor := by
        simpa only [canonical, invalidInputTensor] using invalid
      simp [runChecked, M.close_ok, execute, validator]
  | ok input =>
      have preserved := validate_preserves P schedule η input validation
      subst η
      exact accepted_correspondence_of_fibers M canonical capInjective fibers input

theorem accepted_run_correspondence
    (M : SourceContractMatch P schedule contract fragment graph) (η : P.Input) :
    ExecutionCorrespondence M (runChecked contract fragment η.val) (P.initial η)
      (Executor.run P RationalReference.ops schedule η) :=
  accepted_correspondence_of_fibers M (close_success_canonical M.close_ok).1
    M.capability_injective M.collectorFiber η

theorem default_run_correspondence
    (M : SourceContractMatch P schedule contract fragment graph)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ)) :
    ValidatedCorrespondence M η :=
  validated_correspondence_of_fibers M (close_success_canonical M.close_ok).1
    M.capability_injective M.collectorFiber η

theorem accepted_no_mismatch
    (M : SourceContractMatch P schedule contract fragment graph) (η : P.Input) :
    (∀ tag state, (runChecked contract fragment η.val).outcome ≠
      .contractMismatch tag state) ∧
    (∀ address state, (runChecked contract fragment η.val).outcome ≠
      .collectorMismatch address state) := by
  have related := (accepted_run_correspondence M η).outcome
  constructor
  · intro tag state mismatch
    rw [mismatch] at related
    cases related
  · intro address state mismatch
    rw [mismatch] at related
    cases related

theorem default_runs_not_exhausted
    (_M : SourceContractMatch P schedule contract fragment graph) (η : P.Input) :
    (∀ state, (runChecked contract fragment η.val).outcome ≠ .exhausted state) ∧
    (Executor.run P RationalReference.ops schedule η).outcome.isExhausted = false :=
  ⟨runChecked_not_exhausted contract fragment η.val,
    run_not_exhausted P RationalReference.ops schedule η⟩

theorem completed_model
    (M : SourceContractMatch P schedule contract fragment graph) (η : P.Input)
    (g : State σ) (finished : (runChecked contract fragment η.val).outcome = .complete g) :
    ∃ (c : P.Running) (complete : P.Complete c),
      (∀ a, g.available a = some (P.finalStore c complete a)) ∧
      P.Models RationalReference.ops η (P.finalStore c complete) ∧
      (∀ ρ, P.Models RationalReference.ops η ρ → ρ = P.finalStore c complete) ∧
      ∃ admitted : P.AdmInput RationalReference.ops η,
        P.denotation RationalReference.ops η admitted =
          P.outputProjection (P.finalStore c complete) := by
  obtain ⟨c, complete, _, _, _, available, model, unique, denotation⟩ :=
    complete_semantics M η _ _ (accepted_run_correspondence M η) g finished
  exact ⟨c, complete, available, model, unique, _, denotation⟩

theorem failed_has_no_model
    (M : SourceContractMatch P schedule contract fragment graph) (η : P.Input)
    (tag : Nat) (g : State σ)
    (failed : (runChecked contract fragment η.val).outcome = .failed tag g) :
    ¬ ∃ ρ, P.Models RationalReference.ops η ρ := by
  obtain ⟨_, _, _, _, _, _, noModel⟩ :=
    failed_no_model M η _ _ (accepted_run_correspondence M η) tag g failed
  exact noModel

theorem ranked_not_blocked
    (M : SourceContractMatch P schedule contract fragment graph) (η : P.Input)
    (certificate : P.RankCertificate) (g : State σ)
    (missing : List (Nat × List (Address σ))) :
    (runChecked contract fragment η.val).outcome ≠ .blocked g missing :=
  ranked_graph_not_blocked M η _ _ (accepted_run_correspondence M η)
    certificate g missing

end IndexedOpenComposition.Correspondence
