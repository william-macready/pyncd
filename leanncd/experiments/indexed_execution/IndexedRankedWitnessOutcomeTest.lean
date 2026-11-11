import IndexedRankedWitnessOutcomes
import IndexedRankedOperationalTest

namespace IndexedRankedWitnessOutcomeTest

open LeanNCD.Semantics IndexedOpenComposition IndexedComponentComposition IndexedWitness
open IndexedComponentCompositionLocalFixtures IndexedComponentCompositionPortFixtures
open IndexedComponentRankedExecutionFixtures IndexedOperationalAssociativityFixtures
open IndexedRankedWitnessOutcomes IndexedRankedWitnessBridge

def leafRow (a : ℚ) :=
  let A := consumerComponent a
  let result := runChecked A.contract A.fragment (privateInput a).val
  outcomeRow (addresses _ A.contract.tensors) id result.outcome

#eval leafRow 0
#eval leafRow 4
#eval privateRows 4 4 4 |>.getLast?
#eval privateReferenceCuts

theorem strict_checked_kind :
    (runChecked (consumerComponent 0).contract (consumerComponent 0).fragment
      (privateInput 0).val).outcome.kind = "failed" := by
  rw [IndexedComponentExecution.checked_eq_stepFuel (consumerComponent 0).matched (privateInput 0)]
  decide +kernel

theorem total_checked_kind :
    (runChecked (consumerComponent 4).contract (consumerComponent 4).fragment
      (privateInput 4).val).outcome.kind = "complete" := by
  rw [IndexedComponentExecution.checked_eq_stepFuel (consumerComponent 4).matched (privateInput 4)]
  decide +kernel

example : leafRow 0 =
    ("failed", some 30, some ([some 3, some 9, none], [(201, 9)])) := by decide +kernel
example : leafRow 4 = ("complete", none,
    some ([some 3, some 9, some (7 / 2)], [(201, 9), (301, 7 / 2)])) := by decide +kernel

theorem no_domain_of_failed_kind {σ : Declarations Unit}
    [Fintype σ.Tensor] [DecidableEq σ.Tensor] (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (η : A.program.Input)
    (failed : (runChecked A.contract A.fragment η.val).outcome.kind = "failed") :
    ¬ (componentSpan A).Domain (inputEnv A η) := by
  apply (checked_failed_iff_no_domain A rank η).mp
  cases h : (runChecked A.contract A.fragment η.val).outcome <;>
    simp_all [Outcome.kind]

theorem strict_private_no_witness :
    ¬ (componentSpan (consumerComponent 0)).Domain
      (inputEnv (consumerComponent 0) (privateInput 0)) :=
  no_domain_of_failed_kind _ (consumerRank 0) _ strict_checked_kind

theorem private_success_full :
    ∃ (w : (componentSpan (consumerComponent 4)).W)
      (g : State consumerDeclarations)
      (c : (consumerComponent 4).program.Running)
      (finished : (consumerComponent 4).program.Complete c),
      (runChecked (consumerComponent 4).contract (consumerComponent 4).fragment
        (privateInput 4).val).outcome = .complete g ∧
      (Program.Executor.run (consumerComponent 4).program RationalReference.ops
        (consumerComponent 4).schedule (privateInput 4)).outcome = .complete c finished ∧
      Relation (consumerComponent 4).matched g c ∧
      (∀ a, g.available a = some (w.2.val a)) ∧
      (consumerComponent 4).program.finalStore c finished = w.2.val ∧
      (componentSpan (consumerComponent 4)).left w =
        inputEnv (consumerComponent 4) (privateInput 4) ∧
      (componentSpan (consumerComponent 4)).right w =
        (outputEquiv (consumerComponent 4)).symm
          ((consumerComponent 4).program.outputProjection w.2.val) ∧
      ∃ domain, (componentSpan (consumerComponent 4)).value
        (component_left_injective _ (consumerRank 4)) (inputEnv _ (privateInput 4)) domain =
          (componentSpan (consumerComponent 4)).right w := by
  have kind := total_checked_kind
  have done : ∃ g, (runChecked (consumerComponent 4).contract
      (consumerComponent 4).fragment (privateInput 4).val).outcome = .complete g := by
    cases h : (runChecked (consumerComponent 4).contract
      (consumerComponent 4).fragment (privateInput 4).val).outcome <;>
      simp_all [Outcome.kind]
  obtain ⟨g, done⟩ := done
  obtain ⟨c, finished, domain, reference, related, full, model, value⟩ :=
    checked_success_value _ (consumerRank 4) _ g done
  let w : (componentSpan (consumerComponent 4)).W :=
    ⟨privateInput 4, ⟨_, model⟩⟩
  exact ⟨w, g, c, finished, done, reference, related, full, rfl, rfl, rfl, domain, value⟩

theorem private_reference_value
    (c : (consumerComponent 4).program.Running)
    (finished : (consumerComponent 4).program.Complete c)
    (done : (Program.Executor.run (consumerComponent 4).program RationalReference.ops
      (consumerComponent 4).schedule (privateInput 4)).outcome = .complete c finished) :
    ∃ (g : State consumerDeclarations)
      (domain : (componentSpan (consumerComponent 4)).Domain (inputEnv _ (privateInput 4))),
      (runChecked (consumerComponent 4).contract (consumerComponent 4).fragment
        (privateInput 4).val).outcome = .complete g ∧
      Relation (consumerComponent 4).matched g c ∧
      (∀ a, g.available a = some ((consumerComponent 4).program.finalStore c finished a)) ∧
      (componentSpan (consumerComponent 4)).value (component_left_injective _ (consumerRank 4))
        (inputEnv _ (privateInput 4)) domain = (outputEquiv (consumerComponent 4)).symm
          ((consumerComponent 4).program.outputProjection
            ((consumerComponent 4).program.finalStore c finished)) :=
  reference_success_value _ (consumerRank 4) _ c finished done

abbrev pairComponent := privateComposite 4 4
def pairInput := liftInput (consumerComponent 4) (consumerComponent 4)
  (privateBoundary 4 4) (privateInput 4)

def pairFinal : State (declarations (consumerComponent 4) (consumerComponent 4)) :=
  match (privateRun 4 4).outcome with
  | .complete g => g
  | _ => initial pairInput.val

theorem pair_complete :
    (runChecked pairComponent.contract pairComponent.fragment pairInput.val).outcome =
      .complete pairFinal := by
  have kind : (privateRun 4 4).outcome.kind = "complete" := by decide +kernel
  change (privateRun 4 4).outcome = .complete pairFinal
  unfold pairFinal
  cases h : (privateRun 4 4).outcome <;> simp_all [Outcome.kind]

theorem pair_success_full :
    ∃ (w : (componentSpan pairComponent).W) (c : pairComponent.program.Running)
      (finished : pairComponent.program.Complete c),
      (Program.Executor.run pairComponent.program RationalReference.ops
        pairComponent.schedule pairInput).outcome = .complete c finished ∧
      Relation pairComponent.matched pairFinal c ∧
      (∀ a, pairFinal.available a = some (w.2.val a)) ∧
      pairComponent.program.finalStore c finished = w.2.val ∧
      (compositeRebasedSpan (consumerComponent 4) (consumerComponent 4)
        (privateBoundary 4 4)).left w = inputEnv _ (privateInput 4) ∧
      (compositeRebasedSpan (consumerComponent 4) (consumerComponent 4)
        (privateBoundary 4 4)).right w =
        compositeOutputEquiv (consumerComponent 4) (consumerComponent 4) (privateBoundary 4 4)
          ((outputEquiv pairComponent).symm (pairComponent.program.outputProjection w.2.val)) := by
  obtain ⟨c, finished, domain, reference, related, full, model, value⟩ :=
    checked_success_value pairComponent (privateRank 4 4) pairInput pairFinal pair_complete
  let w : (componentSpan pairComponent).W := ⟨pairInput, ⟨_, model⟩⟩
  refine ⟨w, c, finished, reference, related, full, rfl, ?_, rfl⟩
  change (compositeInputEquiv _ _ _).symm (inputEnv _ pairInput) = _
  rw [compositeInput_restrict]
  exact congrArg (inputEnv (consumerComponent 4)) (restrictInput_liftInput _ _ _ _)

#eval (addresses _ pairComponent.contract.tensors).map pairFinal.available
example : (addresses _ pairComponent.contract.tensors).map pairFinal.available =
    [some 3, some 9, some (7 / 2), some 81, some (19 / 2)] := by decide +kernel

example (ρ : Store RationalReference.Carrier consumerDeclarations) :
    (consumerComponent 4).program.Models RationalReference.ops (privateInput 4) ρ ↔
      ∃ (g : State consumerDeclarations) (c : (consumerComponent 4).program.Running)
        (finished : (consumerComponent 4).program.Complete c),
        (runChecked (consumerComponent 4).contract (consumerComponent 4).fragment
          (privateInput 4).val).outcome = .complete g ∧
        (Program.Executor.run (consumerComponent 4).program RationalReference.ops
          (consumerComponent 4).schedule (privateInput 4)).outcome = .complete c finished ∧
        Relation (consumerComponent 4).matched g c ∧ (∀ a, g.available a = some (ρ a)) ∧
        (consumerComponent 4).program.finalStore c finished = ρ :=
  model_iff_actual_full _ (consumerRank 4) _ ρ

theorem private_domain_apis (a : ℚ) :
    ((componentSpan (consumerComponent a)).Domain (inputEnv _ (privateInput a)) ↔
      ∃ g, (runChecked (consumerComponent a).contract (consumerComponent a).fragment
        (privateInput a).val).outcome = .complete g) ∧
    ((componentSpan (consumerComponent a)).Domain (inputEnv _ (privateInput a)) ↔
      ∃ c finished, (Program.Executor.run (consumerComponent a).program RationalReference.ops
        (consumerComponent a).schedule (privateInput a)).outcome = .complete c finished) ∧
    ((∃ t o c, (Program.Executor.run (consumerComponent a).program RationalReference.ops
        (consumerComponent a).schedule (privateInput a)).outcome = .failed t o c) ↔
      ¬ (componentSpan (consumerComponent a)).Domain (inputEnv _ (privateInput a))) :=
  ⟨domain_iff_checked _ (consumerRank a) _, domain_iff_reference _ (consumerRank a) _,
    reference_failed_iff_no_domain _ (consumerRank a) _⟩

noncomputable def tripleRank (a b c : ℚ) :=
  compositeRankCertificate (privateComposite a b) (consumerComponent c)
    (leftNestedBoundary (consumerComponent a) (consumerComponent b) (consumerComponent c)
      (privateBoundary a b) (privateBoundary b c)) (privateRank a b) (consumerRank c)

theorem triple_failure_no_domain (a b c : ℚ)
    (failed : (leftRun (consumerComponent a) (consumerComponent b) (consumerComponent c)
      (privateBoundary a b) (privateBoundary b c) (privateInput a)).outcome.kind = "failed") :
    ¬ (componentSpan (leftBracket (consumerComponent a) (consumerComponent b)
      (consumerComponent c) (privateBoundary a b) (privateBoundary b c))).Domain
      (inputEnv _ (leftInput (consumerComponent a) (consumerComponent b) (consumerComponent c)
        (privateBoundary a b) (privateBoundary b c) (privateInput a))) :=
  no_domain_of_failed_kind _ (tripleRank a b c) _ failed

example := private_domain_apis 0
example := private_domain_apis 4

noncomputable def privateDomain (a b c : ℚ) : Prop :=
  (componentSpan (leftBracket (consumerComponent a) (consumerComponent b)
    (consumerComponent c) (privateBoundary a b) (privateBoundary b c))).Domain
    (inputEnv _ (leftInput (consumerComponent a) (consumerComponent b) (consumerComponent c)
      (privateBoundary a b) (privateBoundary b c) (privateInput a)))

theorem failure_A : ¬ privateDomain 0 4 4 := triple_failure_no_domain 0 4 4 (by
  decide +kernel)

theorem failure_B : ¬ privateDomain 4 0 4 := triple_failure_no_domain 4 0 4 (by
  decide +kernel)

theorem failure_C : ¬ privateDomain 4 4 0 := triple_failure_no_domain 4 4 0 (by
  decide +kernel)

#eval [privateComparison 0 4 4, privateComparison 4 0 4, privateComparison 4 4 0]
#eval [privateReference 0 4 4, privateReference 4 0 4, privateReference 4 4 0]

example : [privateReference 0 4 4, privateReference 4 0 4, privateReference 4 4 0] =
    [(true, true, 3, 3, 3, 3), (true, true, 7, 7, 7, 7),
      (true, true, 11, 11, 11, 11)] := by decide +kernel

#print axioms strict_private_no_witness
#print axioms private_success_full
#print axioms private_reference_value
#print axioms pair_success_full
#print axioms failure_A
#print axioms failure_B
#print axioms failure_C

end IndexedRankedWitnessOutcomeTest
