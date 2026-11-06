import IndexedCompositionCorrespondence

namespace IndexedOpenComposition.Correspondence

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {schedule : Schedule P} {contract : Contract σ} {fragment : Fragment σ}
variable {graph : Closed σ}

theorem complete_semantics
    (M : SourceContractMatch P schedule contract fragment graph) (η : P.Input)
    (candidate : Run σ)
    (reference : Result P RationalReference.ops (.running (P.initial η)))
    (correspondence : ExecutionCorrespondence M candidate (P.initial η) reference)
    (g : State σ) (completeGraph : candidate.outcome = .complete g) :
    ∃ (c : P.Running) (finished : P.Complete c)
        (completeReference : reference.outcome = .complete c finished),
      Relation M g c ∧
      g.available = c.published ∧
      (∀ a : Address σ, g.available a = some (P.finalStore c finished a)) ∧
      P.Models RationalReference.ops η (P.finalStore c finished) ∧
      (∀ ρ, P.Models RationalReference.ops η ρ →
        ρ = P.finalStore c finished) ∧
      P.denotation RationalReference.ops η
        (P.successful_admInput RationalReference.ops η c
          (result_success P RationalReference.ops η reference c finished
            completeReference)) =
        P.outputProjection (P.finalStore c finished) := by
  have related : OutcomeRelated M (.complete g) reference.outcome := by
    rw [← completeGraph]
    exact correspondence.outcome
  cases reference with
  | mk outcome events execution =>
      cases related with
      | complete _ c finished _ relation =>
          refine ⟨c, finished, rfl, relation, relation.published,
            ?_, ?_, ?_, ?_⟩
          · intro a
            rw [relation.published]
            exact P.finalStore_published c finished a
          · exact result_model P RationalReference.ops η
              ⟨.complete c finished, events, execution⟩ c finished rfl
          · exact result_unique P RationalReference.ops η
              ⟨.complete c finished, events, execution⟩ c finished rfl
          · exact result_denotation P RationalReference.ops η
              ⟨.complete c finished, events, execution⟩ c finished rfl

theorem failed_no_model
    (M : SourceContractMatch P schedule contract fragment graph) (η : P.Input)
    (candidate : Run σ)
    (reference : Result P RationalReference.ops (.running (P.initial η)))
    (correspondence : ExecutionCorrespondence M candidate (P.initial η) reference)
    (tag : Nat) (g : State σ) (failedGraph : candidate.outcome = .failed tag g) :
    ∃ (t : P.Defined) (o : P.Occurrence t) (c : P.Running),
      tag = M.tag ⟨t, o⟩ ∧
      reference.outcome = .failed t o c ∧
      g.available = c.published ∧
      ¬ ∃ ρ, P.Models RationalReference.ops η ρ := by
  have related : OutcomeRelated M (.failed tag g) reference.outcome := by
    rw [← failedGraph]
    exact correspondence.outcome
  cases reference with
  | mk outcome events execution =>
      cases related with
      | failed _ c t o _ relation =>
          exact ⟨t, o, c, rfl, rfl, relation.published,
            result_failure P RationalReference.ops η
              ⟨.failed t o c, events, execution⟩ t o c rfl⟩

theorem ranked_graph_not_blocked
    (M : SourceContractMatch P schedule contract fragment graph) (η : P.Input)
    (candidate : Run σ)
    (reference : Result P RationalReference.ops (.running (P.initial η)))
    (correspondence : ExecutionCorrespondence M candidate (P.initial η) reference)
    (certificate : P.RankCertificate) (g : State σ)
    (missing : List (Nat × List (Address σ))) :
    candidate.outcome ≠ .blocked g missing := by
  intro blockedGraph
  have related : OutcomeRelated M (.blocked g missing) reference.outcome := by
    rw [← blockedGraph]
    exact correspondence.outcome
  cases reference with
  | mk outcome events execution =>
      cases related with
      | blocked _ c _ observed blocked _ _ _ =>
          exact result_not_blocked P RationalReference.ops certificate η
            ⟨.blocked c observed blocked, events, execution⟩
            c observed blocked rfl

theorem ranked_actual_dichotomy
    (M : SourceContractMatch P schedule contract fragment graph) (η : P.Input)
    (candidate : Run σ)
    (correspondence : ExecutionCorrespondence M candidate (P.initial η)
      (Executor.run P RationalReference.ops schedule η))
    (certificate : P.RankCertificate) :
    (∃ (g : State σ) (c : P.Running) (finished : P.Complete c),
      candidate.outcome = .complete g ∧
      (Executor.run P RationalReference.ops schedule η).outcome =
        .complete c finished ∧
      P.Models RationalReference.ops η (P.finalStore c finished)) ∨
    (∃ (tag : Nat) (g : State σ), candidate.outcome = .failed tag g ∧
      ¬ ∃ ρ, P.Models RationalReference.ops η ρ) := by
  rcases run_ranked_dichotomy P RationalReference.ops schedule certificate η with
    ⟨c, finished, completeReference⟩ |
    ⟨t, o, c, failedReference, noModel⟩
  · have related : OutcomeRelated M candidate.outcome (.complete c finished) := by
      rw [← completeReference]
      exact correspondence.outcome
    cases candidate with
    | mk outcome events states =>
        cases related with
        | complete g c finished _ _ =>
            exact .inl ⟨g, c, finished, rfl, completeReference,
              result_model P RationalReference.ops η
                (Executor.run P RationalReference.ops schedule η) c finished
                completeReference⟩
  · have related : OutcomeRelated M candidate.outcome (.failed t o c) := by
      rw [← failedReference]
      exact correspondence.outcome
    cases candidate with
    | mk outcome events states =>
        cases related with
        | failed g _ t o _ _ =>
            exact .inr ⟨M.tag ⟨t, o⟩, g, rfl, noModel⟩

end IndexedOpenComposition.Correspondence
