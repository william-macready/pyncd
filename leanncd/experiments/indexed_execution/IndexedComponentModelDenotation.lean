import IndexedComponentModelWitnesses

namespace IndexedComponentComposition

open LeanNCD.Semantics

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (wire : Boundary A B)

def AtMostOneModels (A : MatchedComponent σA) : Prop :=
  ∀ (η : A.program.Input) (ρ ρ' : Store K σA),
    A.program.Models RationalReference.ops η ρ →
    A.program.Models RationalReference.ops η ρ' → ρ = ρ'

private theorem composite_atMostOne (hA : AtMostOneModels A)
    (hB : AtMostOneModels B) (η : A.program.Input)
    (ρ ρ' : Store K (declarations A B))
    (model : (program A B wire).Models RationalReference.ops
      (liftInput A B wire η) ρ)
    (model' : (program A B wire).Models RationalReference.ops
      (liftInput A B wire η) ρ') : ρ = ρ' := by
  have pair := (models_restrict_iff A B wire η ρ).mp model
  have pair' := (models_restrict_iff A B wire η ρ').mp model'
  have eqA : restrictUpstream A B ρ = restrictUpstream A B ρ' :=
    hA η _ _ pair.1 pair'.1
  have eqB : restrictDownstream A B wire ρ =
      restrictDownstream A B wire ρ' := by
    apply hB (boundaryInput A B wire (restrictUpstream A B ρ))
    · exact pair.2
    · rw [eqA]
      exact pair'.2
  calc
    ρ = glueStore A B (restrictUpstream A B ρ)
        (restrictDownstream A B wire ρ) :=
      (glueStore_restrictions A B wire ρ).symm
    _ = glueStore A B (restrictUpstream A B ρ')
        (restrictDownstream A B wire ρ') := by rw [eqA, eqB]
    _ = ρ' := glueStore_restrictions A B wire ρ'

theorem admInput_lift_iff (hA : AtMostOneModels A)
    (hB : AtMostOneModels B) (η : A.program.Input) :
    (program A B wire).AdmInput RationalReference.ops
      (liftInput A B wire η) ↔
      ∃ hAdmA : A.program.AdmInput RationalReference.ops η,
        B.program.AdmInput RationalReference.ops
          (boundaryFromOutput A B wire
            (A.program.denotation RationalReference.ops η hAdmA)) := by
  constructor
  · rintro ⟨ρ, model, _⟩
    have pair := (models_restrict_iff A B wire η ρ).mp model
    have hAdmA : A.program.AdmInput RationalReference.ops η :=
      ⟨restrictUpstream A B ρ, pair.1,
        fun ρ' model' => (hA η _ _ pair.1 model').symm⟩
    refine ⟨hAdmA, ?_⟩
    have boundaryEq : boundaryInput A B wire (restrictUpstream A B ρ) =
        boundaryFromOutput A B wire
          (A.program.denotation RationalReference.ops η hAdmA) := by
      rw [A.program.denotation_of_model RationalReference.ops η hAdmA
        (restrictUpstream A B ρ) pair.1]
      exact boundaryInput_outputProjection A B wire (restrictUpstream A B ρ)
    rw [← boundaryEq]
    exact ⟨restrictDownstream A B wire ρ, pair.2,
      fun ρ' model' => (hB _ _ _ pair.2 model').symm⟩
  · rintro ⟨hAdmA, hAdmB⟩
    let ρA := Classical.choose hAdmA
    let ρB := Classical.choose hAdmB
    have modelA : A.program.Models RationalReference.ops η ρA :=
      (Classical.choose_spec hAdmA).1
    have modelB : B.program.Models RationalReference.ops
        (boundaryFromOutput A B wire
          (A.program.denotation RationalReference.ops η hAdmA)) ρB :=
      (Classical.choose_spec hAdmB).1
    have boundaryEq : boundaryInput A B wire ρA =
        boundaryFromOutput A B wire
          (A.program.denotation RationalReference.ops η hAdmA) := by
      rw [A.program.denotation_of_model RationalReference.ops η hAdmA ρA modelA]
      exact boundaryInput_outputProjection A B wire ρA
    have modelB' : B.program.Models RationalReference.ops
        (boundaryInput A B wire ρA) ρB := by
      rw [boundaryEq]
      exact modelB
    have agree : B.program.InputAgreement (boundaryInput A B wire ρA) ρB := by
      obtain ⟨_, agree, _⟩ := modelB'
      exact agree
    have modelC : (program A B wire).Models RationalReference.ops
        (liftInput A B wire η) (glueStore A B ρA ρB) :=
      (models_glue_iff A B wire η ρA ρB agree).mpr ⟨modelA, modelB'⟩
    exact ⟨glueStore A B ρA ρB, modelC,
      fun ρ' model' =>
        (composite_atMostOne A B wire hA hB η _ _ modelC model').symm⟩

theorem admInput_restrictions_iff (hA : AtMostOneModels A)
    (hB : AtMostOneModels B) (η : (program A B wire).Input) :
    (program A B wire).AdmInput RationalReference.ops η ↔
      ∃ hAdmA : A.program.AdmInput RationalReference.ops
          (restrictInput A B wire η),
        B.program.AdmInput RationalReference.ops
          (boundaryFromOutput A B wire
            (A.program.denotation RationalReference.ops
              (restrictInput A B wire η) hAdmA)) := by
  simpa only [liftInput_restrictInput] using
    (admInput_lift_iff A B wire hA hB (restrictInput A B wire η))

theorem denotation_successive (hA : AtMostOneModels A)
    (hB : AtMostOneModels B) (η : (program A B wire).Input)
    (hAdmC : (program A B wire).AdmInput RationalReference.ops
      η) :
    ∃ hAdmA : A.program.AdmInput RationalReference.ops
        (restrictInput A B wire η),
      ∃ hAdmB : B.program.AdmInput RationalReference.ops
        (boundaryFromOutput A B wire
          (A.program.denotation RationalReference.ops
            (restrictInput A B wire η) hAdmA)),
        (program A B wire).denotation RationalReference.ops
            η hAdmC =
          liftOutput A B wire
            (B.program.denotation RationalReference.ops
              (boundaryFromOutput A B wire
                (A.program.denotation RationalReference.ops
                  (restrictInput A B wire η) hAdmA)) hAdmB) := by
  obtain ⟨hAdmA, hAdmB⟩ :=
    (admInput_restrictions_iff A B wire hA hB η).mp hAdmC
  refine ⟨hAdmA, hAdmB, ?_⟩
  let ρ := Classical.choose hAdmC
  have model : (program A B wire).Models RationalReference.ops
      η ρ := (Classical.choose_spec hAdmC).1
  have pair := (models_restrictInput_iff A B wire η ρ).mp model
  have boundaryEq : boundaryInput A B wire (restrictUpstream A B ρ) =
      boundaryFromOutput A B wire
        (A.program.denotation RationalReference.ops
          (restrictInput A B wire η) hAdmA) := by
    rw [A.program.denotation_of_model RationalReference.ops
      (restrictInput A B wire η) hAdmA (restrictUpstream A B ρ) pair.1]
    exact boundaryInput_outputProjection A B wire (restrictUpstream A B ρ)
  have modelB : B.program.Models RationalReference.ops
      (boundaryFromOutput A B wire
        (A.program.denotation RationalReference.ops
          (restrictInput A B wire η) hAdmA))
      (restrictDownstream A B wire ρ) := by
    rw [← boundaryEq]
    exact pair.2
  have denB := B.program.denotation_of_model RationalReference.ops
    (boundaryFromOutput A B wire
      (A.program.denotation RationalReference.ops
        (restrictInput A B wire η) hAdmA))
    hAdmB (restrictDownstream A B wire ρ) modelB
  calc
    (program A B wire).denotation RationalReference.ops
        η hAdmC =
      (program A B wire).outputProjection ρ :=
      (program A B wire).denotation_of_model RationalReference.ops
        η hAdmC ρ model
    _ = liftOutput A B wire
        (B.program.outputProjection (restrictDownstream A B wire ρ)) :=
      outputProjection_transport A B wire ρ
    _ = liftOutput A B wire
        (B.program.denotation RationalReference.ops
          (boundaryFromOutput A B wire
            (A.program.denotation RationalReference.ops
              (restrictInput A B wire η) hAdmA)) hAdmB) :=
      congrArg (liftOutput A B wire) denB.symm

#print axioms admInput_lift_iff
#print axioms admInput_restrictions_iff
#print axioms denotation_successive

end IndexedComponentComposition
