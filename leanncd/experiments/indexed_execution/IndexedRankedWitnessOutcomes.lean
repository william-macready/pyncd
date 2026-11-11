import IndexedRankedWitnessSource
import IndexedWitnessPartial

namespace IndexedRankedWitnessOutcomes

open LeanNCD.Semantics IndexedOpenComposition IndexedComponentComposition IndexedWitness
open IndexedRankedWitnessBridge

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable (A : MatchedComponent σ)

theorem actual_correspondence (η : A.program.Input) :
    Correspondence.ExecutionCorrespondence A.matched
      (runChecked A.contract A.fragment η.val) (A.program.initial η)
      (Program.Executor.run A.program RationalReference.ops A.schedule η) :=
  Correspondence.accepted_run_correspondence A.matched η

theorem model_iff_actual_full (rank : A.program.RankCertificate) (η : A.program.Input)
    (ρ : Store RationalReference.Carrier σ) :
    A.program.Models RationalReference.ops η ρ ↔
      ∃ (g : State σ) (c : A.program.Running) (finished : A.program.Complete c),
        (runChecked A.contract A.fragment η.val).outcome = .complete g ∧
        (Program.Executor.run A.program RationalReference.ops A.schedule η).outcome =
          .complete c finished ∧
        Relation A.matched g c ∧
        (∀ a, g.available a = some (ρ a)) ∧
        A.program.finalStore c finished = ρ := by
  constructor
  · intro model
    obtain ⟨g, done, full⟩ := model_available A rank η ρ model
    obtain ⟨c, finished, reference, related, _, _, _, unique, _⟩ :=
      Correspondence.complete_semantics A.matched η _ _ (actual_correspondence A η) g done
    exact ⟨g, c, finished, done, reference, related, full, (unique ρ model).symm⟩
  · rintro ⟨g, c, finished, done, _, _, full, _⟩
    exact model_of_available A η g done ρ full

theorem domain_iff_checked (rank : A.program.RankCertificate) (η : A.program.Input) :
    (componentSpan A).Domain (inputEnv A η) ↔
      ∃ g, (runChecked A.contract A.fragment η.val).outcome = .complete g :=
  (component_domain_iff A (ranked_atMostOne A rank) η).trans
    (complete_iff_admInput A rank η).symm

theorem domain_iff_reference (rank : A.program.RankCertificate) (η : A.program.Input) :
    (componentSpan A).Domain (inputEnv A η) ↔
      ∃ c finished,
        (Program.Executor.run A.program RationalReference.ops A.schedule η).outcome =
          .complete c finished := by
  constructor
  · intro domain
    obtain ⟨g, done⟩ := (domain_iff_checked A rank η).mp domain
    obtain ⟨c, finished, reference, _⟩ :=
      Correspondence.complete_semantics A.matched η _ _ (actual_correspondence A η) g done
    exact ⟨c, finished, reference⟩
  · rintro ⟨c, finished, reference⟩
    have model := Program.Executor.result_model A.program RationalReference.ops η
      (Program.Executor.run A.program RationalReference.ops A.schedule η) c finished reference
    exact ⟨⟨η, ⟨A.program.finalStore c finished, model⟩⟩, rfl⟩

theorem checked_failed_iff_no_domain (rank : A.program.RankCertificate)
    (η : A.program.Input) :
    (∃ tag g, (runChecked A.contract A.fragment η.val).outcome = .failed tag g) ↔
      ¬ (componentSpan A).Domain (inputEnv A η) := by
  rw [failed_iff_no_model A rank η, component_domain_iff A (ranked_atMostOne A rank) η,
    admInput_iff_model A rank η]

theorem reference_failed_iff_no_domain (rank : A.program.RankCertificate)
    (η : A.program.Input) :
    (∃ t o c,
      (Program.Executor.run A.program RationalReference.ops A.schedule η).outcome =
        .failed t o c) ↔
      ¬ (componentSpan A).Domain (inputEnv A η) := by
  constructor
  · rintro ⟨t, o, c, failed⟩ domain
    obtain ⟨g, done⟩ := (domain_iff_checked A rank η).mp domain
    exact Program.Executor.result_failure A.program RationalReference.ops η
      (Program.Executor.run A.program RationalReference.ops A.schedule η) t o c failed
      ((complete_iff_model A rank η).mp ⟨g, done⟩)
  · intro noDomain
    rcases Program.Executor.run_ranked_dichotomy A.program RationalReference.ops
        A.schedule rank η with complete | failed
    · exact False.elim (noDomain ((domain_iff_reference A rank η).mpr complete))
    · obtain ⟨t, o, c, failed, _⟩ := failed
      exact ⟨t, o, c, failed⟩

theorem checked_success_value (rank : A.program.RankCertificate) (η : A.program.Input)
    (g : State σ) (done : (runChecked A.contract A.fragment η.val).outcome = .complete g) :
    ∃ (c : A.program.Running) (finished : A.program.Complete c)
        (domain : (componentSpan A).Domain (inputEnv A η)),
      (Program.Executor.run A.program RationalReference.ops A.schedule η).outcome =
        .complete c finished ∧
      Relation A.matched g c ∧
      (∀ a, g.available a = some (A.program.finalStore c finished a)) ∧
      A.program.Models RationalReference.ops η (A.program.finalStore c finished) ∧
      (componentSpan A).value (component_left_injective A rank) (inputEnv A η) domain =
        (outputEquiv A).symm (A.program.outputProjection (A.program.finalStore c finished)) := by
  obtain ⟨c, finished, reference, related, _, full, model, _, _⟩ :=
    Correspondence.complete_semantics A.matched η _ _ (actual_correspondence A η) g done
  let w : (componentSpan A).W := ⟨η, ⟨A.program.finalStore c finished, model⟩⟩
  exact ⟨c, finished, ⟨w, rfl⟩, reference, related, full, model,
    (componentSpan A).value_eq (component_left_injective A rank) ⟨w, rfl⟩ w rfl⟩

theorem reference_success_value (rank : A.program.RankCertificate) (η : A.program.Input)
    (c : A.program.Running) (finished : A.program.Complete c)
    (done : (Program.Executor.run A.program RationalReference.ops A.schedule η).outcome =
      .complete c finished) :
    ∃ (g : State σ) (domain : (componentSpan A).Domain (inputEnv A η)),
      (runChecked A.contract A.fragment η.val).outcome = .complete g ∧
      Relation A.matched g c ∧
      (∀ a, g.available a = some (A.program.finalStore c finished a)) ∧
      (componentSpan A).value (component_left_injective A rank) (inputEnv A η) domain =
        (outputEquiv A).symm (A.program.outputProjection (A.program.finalStore c finished)) := by
  have related := (actual_correspondence A η).outcome
  rw [done] at related
  generalize eq : (runChecked A.contract A.fragment η.val).outcome = outcome at related
  cases related with
  | complete g c finished ledger relation =>
      have model := Program.Executor.result_model A.program RationalReference.ops η
        (Program.Executor.run A.program RationalReference.ops A.schedule η) c finished done
      let w : (componentSpan A).W := ⟨η, ⟨A.program.finalStore c finished, model⟩⟩
      refine ⟨g, ⟨w, rfl⟩, rfl, relation, ?_,
        (componentSpan A).value_eq (component_left_injective A rank) ⟨w, rfl⟩ w rfl⟩
      intro a
      rw [relation.published]
      exact A.program.finalStore_published c finished a

end IndexedRankedWitnessOutcomes
