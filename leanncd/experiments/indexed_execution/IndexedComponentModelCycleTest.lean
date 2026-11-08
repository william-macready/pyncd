import IndexedComponentModelCycleFixtures
import IndexedComponentModelWitnesses

namespace IndexedComponentModelCycleTest

open LeanNCD.Semantics
open IndexedComponentComposition
open IndexedComponentModelCycleFixtures

private theorem sequence_one (x : ℚ) :
    LeanNCD.Semantics.sequence (fun _ : Fin 1 => some x) =
      some (fun _ : Fin 1 => x) := by
  apply LeanNCD.Semantics.sequence_complete
  intro i
  rfl

private theorem scalar_boundary_input (hidden strict : Bool) (x y : ℚ) :
    boundaryInput (upstreamComponent hidden) (downstreamComponent strict)
      (scalarBoundary hidden strict) (scalarStore x y) =
        downstreamInput strict y := by
  apply Subtype.ext
  funext t
  fin_cases t <;>
    simp [boundaryInput, downstreamInput, downstreamComponent, downstreamProgram,
      scalarBoundary, scalarStore, privateTensor, boundaryTensor] ; rfl

theorem cycle_boundary_zero :
    boundaryInput cycleUpstream cycleDownstream cycleBoundary (scalarStore 0 0) =
      downstreamInput true 0 :=
  scalar_boundary_input false true 0 0

theorem cycle_boundary_one :
    boundaryInput cycleUpstream cycleDownstream cycleBoundary (scalarStore 1 1) =
      downstreamInput true 1 :=
  scalar_boundary_input false true 1 1

theorem hidden_boundary_zero :
    boundaryInput hiddenUpstream totalDownstream hiddenBoundary (scalarStore 0 0) =
      downstreamInput false 0 :=
  scalar_boundary_input true false 0 0

theorem hidden_boundary_one :
    boundaryInput hiddenUpstream totalDownstream hiddenBoundary (scalarStore 1 0) =
      downstreamInput false 0 :=
  scalar_boundary_input true false 1 0

theorem cycle_zero_not_compatible :
    ¬ ∃ ρB, cycleDownstream.program.Models RationalReference.ops
      (boundaryInput cycleUpstream cycleDownstream cycleBoundary (scalarStore 0 0))
      ρB := by
  rw [cycle_boundary_zero]
  exact reciprocal_zero_no_model

theorem cycle_zero_no_composite_extension :
    ¬ ∃ ρ : Store RationalReference.Carrier
        (IndexedComponentComposition.declarations cycleUpstream cycleDownstream),
      (program cycleUpstream cycleDownstream cycleBoundary).Models RationalReference.ops
        (liftInput cycleUpstream cycleDownstream cycleBoundary (upstreamInput false)) ρ ∧
      restrictUpstream cycleUpstream cycleDownstream ρ = scalarStore 0 0 := by
  rintro ⟨ρ, model, hzero⟩
  have hB := ((models_restrict_iff cycleUpstream cycleDownstream cycleBoundary
    (upstreamInput false) ρ).mp model).2
  rw [hzero] at hB
  exact cycle_zero_not_compatible ⟨_, hB⟩

def cycleOneStore :=
  glueStore cycleUpstream cycleDownstream (scalarStore 1 1) (scalarStore 1 1)

theorem cycle_one_model :
    (program cycleUpstream cycleDownstream cycleBoundary).Models RationalReference.ops
      (liftInput cycleUpstream cycleDownstream cycleBoundary (upstreamInput false))
      cycleOneStore := by
  have hB : cycleDownstream.program.Models RationalReference.ops
      (boundaryInput cycleUpstream cycleDownstream cycleBoundary (scalarStore 1 1))
      (scalarStore 1 1) := by
    rw [cycle_boundary_one]
    exact reciprocal_one_model
  exact (models_glue_iff cycleUpstream cycleDownstream cycleBoundary
    (upstreamInput false) (scalarStore 1 1) (scalarStore 1 1)
    hB.2.1).2 ⟨cycle_upstream_one_model, hB⟩

theorem cycle_one_restrictions :
    restrictUpstream cycleUpstream cycleDownstream cycleOneStore = scalarStore 1 1 ∧
      restrictDownstream cycleUpstream cycleDownstream cycleBoundary cycleOneStore =
        scalarStore 1 1 := by
  exact ⟨restrictUpstream_glueStore cycleUpstream cycleDownstream _ _,
    restrictDownstream_glueStore cycleUpstream cycleDownstream cycleBoundary _ _
      (by
        rw [cycle_boundary_one]
        exact reciprocal_one_model.2.1)⟩

private theorem cycle_upstream_models_cases (ρ : Store RationalReference.Carrier declarations)
    (h : cycleUpstream.program.Models RationalReference.ops (upstreamInput false) ρ) :
    ρ = scalarStore 0 0 ∨ ρ = scalarStore 1 1 := by
  let t : ℚ := ρ ⟨privateTensor, ()⟩
  have hprivate := h.2.2 ⟨privateTensor, rfl⟩ ()
  have hboundary := h.2.2 ⟨boundaryTensor, rfl⟩ ()
  have hcard_private :
      Fintype.card ((upstreamProgram false).Occurrence ⟨privateTensor, rfl⟩) = 1 := by
    decide +kernel
  have hcard_boundary :
      Fintype.card ((upstreamProgram false).Occurrence ⟨boundaryTensor, rfl⟩) = 1 := by
    decide +kernel
  have hsquare : t = t * t := by
    simp [Program.collect, pushforward, Program.contribution,
      Program.outcome, cycleUpstream, upstreamComponent, upstreamProgram,
      squareBody, readScalar, interpret,
      evalWith, Registry.apply, RationalReference.registry, sequence_one,
      privateTensor, boundaryTensor] at hprivate
    change ρ ⟨privateTensor, ()⟩ =
      (Fintype.card ((upstreamProgram false).Occurrence ⟨privateTensor, rfl⟩) : ℚ) *
        (ρ ⟨privateTensor, ()⟩ * ρ ⟨privateTensor, ()⟩) at hprivate
    simpa [t, hcard_private] using hprivate
  have hcopy : ρ ⟨boundaryTensor, ()⟩ = t := by
    simp [Program.collect, pushforward, Program.contribution,
      Program.outcome, cycleUpstream, upstreamComponent, upstreamProgram,
      readScalar, interpret,
      evalWith, RationalReference.registry,
      privateTensor, boundaryTensor] at hboundary
    change ρ ⟨boundaryTensor, ()⟩ =
      (Fintype.card ((upstreamProgram false).Occurrence ⟨boundaryTensor, rfl⟩) : ℚ) *
        ρ ⟨privateTensor, ()⟩ at hboundary
    simpa [t, hcard_boundary] using hboundary
  have hfactor : t * (t - 1) = 0 := by nlinarith [hsquare]
  rcases mul_eq_zero.mp hfactor with ht | ht
  · left
    funext a
    rcases a with ⟨i, p⟩
    cases p
    fin_cases i
    · simpa [scalarStore, t, privateTensor] using ht
    · simpa [scalarStore, t, privateTensor, boundaryTensor] using hcopy.trans ht
  · right
    have ht' : t = 1 := sub_eq_zero.mp ht
    funext a
    rcases a with ⟨i, p⟩
    cases p
    fin_cases i
    · simpa [scalarStore, t, privateTensor] using ht'
    · simpa [scalarStore, t, privateTensor, boundaryTensor] using hcopy.trans ht'

theorem cycle_composite_unique (ρ : Store RationalReference.Carrier
    (IndexedComponentComposition.declarations cycleUpstream cycleDownstream))
    (h : (program cycleUpstream cycleDownstream cycleBoundary).Models
      RationalReference.ops
      (liftInput cycleUpstream cycleDownstream cycleBoundary (upstreamInput false)) ρ) :
    ρ = cycleOneStore := by
  obtain ⟨hA, hB⟩ := (models_restrict_iff cycleUpstream cycleDownstream
    cycleBoundary (upstreamInput false) ρ).mp h
  rcases cycle_upstream_models_cases _ hA with hzero | hone
  · rw [hzero, cycle_boundary_zero] at hB
    exact False.elim (reciprocal_zero_no_model ⟨_, hB⟩)
  · have hB' : restrictDownstream cycleUpstream cycleDownstream cycleBoundary ρ =
        scalarStore 1 1 := by
      apply reciprocal_one_unique
      rwa [hone, cycle_boundary_one] at hB
    calc
      ρ = glueStore cycleUpstream cycleDownstream
          (restrictUpstream cycleUpstream cycleDownstream ρ)
          (restrictDownstream cycleUpstream cycleDownstream cycleBoundary ρ) :=
        (glueStore_restrictions cycleUpstream cycleDownstream cycleBoundary ρ).symm
      _ = cycleOneStore := by rw [hone, hB']; rfl

theorem cycle_composite_admissible :
    (program cycleUpstream cycleDownstream cycleBoundary).AdmInput
      RationalReference.ops
      (liftInput cycleUpstream cycleDownstream cycleBoundary (upstreamInput false)) := by
  exact ⟨cycleOneStore, cycle_one_model, cycle_composite_unique⟩

theorem cycle_upstream_not_admissible :
    ¬ cycleUpstream.program.AdmInput RationalReference.ops (upstreamInput false) :=
  IndexedComponentModelCycleFixtures.cycle_upstream_not_admissible

def hiddenZeroStore :=
  glueStore hiddenUpstream totalDownstream (scalarStore 0 0) (scalarStore 0 1)

def hiddenOneStore :=
  glueStore hiddenUpstream totalDownstream (scalarStore 1 0) (scalarStore 0 1)

theorem hidden_zero_model :
    (program hiddenUpstream totalDownstream hiddenBoundary).Models RationalReference.ops
      (liftInput hiddenUpstream totalDownstream hiddenBoundary (upstreamInput true))
      hiddenZeroStore := by
  have hB : totalDownstream.program.Models RationalReference.ops
      (boundaryInput hiddenUpstream totalDownstream hiddenBoundary (scalarStore 0 0))
      (scalarStore 0 1) := by
    rw [hidden_boundary_zero]
    exact total_zero_model
  exact (models_glue_iff hiddenUpstream totalDownstream hiddenBoundary
    (upstreamInput true) (scalarStore 0 0) (scalarStore 0 1)
    hB.2.1).2 ⟨hidden_upstream_zero_model, hB⟩

theorem hidden_one_model :
    (program hiddenUpstream totalDownstream hiddenBoundary).Models RationalReference.ops
      (liftInput hiddenUpstream totalDownstream hiddenBoundary (upstreamInput true))
      hiddenOneStore := by
  have hB : totalDownstream.program.Models RationalReference.ops
      (boundaryInput hiddenUpstream totalDownstream hiddenBoundary (scalarStore 1 0))
      (scalarStore 0 1) := by
    rw [hidden_boundary_one]
    exact total_zero_model
  exact (models_glue_iff hiddenUpstream totalDownstream hiddenBoundary
    (upstreamInput true) (scalarStore 1 0) (scalarStore 0 1)
    hB.2.1).2 ⟨hidden_upstream_one_model, hB⟩

theorem hidden_same_boundary_via_output :
    boundaryInput hiddenUpstream totalDownstream hiddenBoundary (scalarStore 0 0) =
      boundaryInput hiddenUpstream totalDownstream hiddenBoundary (scalarStore 1 0) := by
  rw [boundaryInput_outputProjection, boundaryInput_outputProjection]
  congr 1
  exact hidden_boundary_equal

theorem hidden_restrictions :
    (restrictUpstream hiddenUpstream totalDownstream hiddenZeroStore =
        scalarStore 0 0 ∧
      restrictDownstream hiddenUpstream totalDownstream hiddenBoundary hiddenZeroStore =
        scalarStore 0 1) ∧
    (restrictUpstream hiddenUpstream totalDownstream hiddenOneStore =
        scalarStore 1 0 ∧
      restrictDownstream hiddenUpstream totalDownstream hiddenBoundary hiddenOneStore =
        scalarStore 0 1) := by
  constructor
  · exact ⟨restrictUpstream_glueStore hiddenUpstream totalDownstream _ _,
      restrictDownstream_glueStore hiddenUpstream totalDownstream hiddenBoundary _ _
        (by rw [hidden_boundary_zero]; exact total_zero_model.2.1)⟩
  · exact ⟨restrictUpstream_glueStore hiddenUpstream totalDownstream _ _,
      restrictDownstream_glueStore hiddenUpstream totalDownstream hiddenBoundary _ _
        (by rw [hidden_boundary_one]; exact total_zero_model.2.1)⟩

theorem hidden_stores_distinct : hiddenZeroStore ≠ hiddenOneStore := by
  intro h
  apply hiddenStore_distinct
  have hp := congrArg (restrictUpstream hiddenUpstream totalDownstream) h
  simpa only [hidden_restrictions.1.1, hidden_restrictions.2.1] using hp

theorem hidden_private_values :
    hiddenZeroStore ⟨.inl privateTensor, ()⟩ = 0 ∧
      hiddenOneStore ⟨.inl privateTensor, ()⟩ = 1 := by
  exact ⟨rfl, rfl⟩

theorem hidden_final_outputs_equal :
    (program hiddenUpstream totalDownstream hiddenBoundary).outputProjection
        hiddenZeroStore =
      (program hiddenUpstream totalDownstream hiddenBoundary).outputProjection
        hiddenOneStore := by
  rw [outputProjection_transport hiddenUpstream totalDownstream hiddenBoundary,
    outputProjection_transport hiddenUpstream totalDownstream hiddenBoundary,
    hidden_restrictions.1.2, hidden_restrictions.2.2]

theorem hidden_final_value :
    (program hiddenUpstream totalDownstream hiddenBoundary).outputProjection
        hiddenZeroStore
        (downstreamOutputIndex hiddenUpstream totalDownstream hiddenBoundary
          ⟨boundaryTensor, rfl⟩) () = 1 := by
  rw [outputProjection_downstream hiddenUpstream totalDownstream hiddenBoundary]
  rw [hidden_restrictions.1.2]
  rfl

theorem hidden_witnesses_roundtrip :
    (witnessesEquiv hiddenUpstream totalDownstream hiddenBoundary
        (upstreamInput true)).symm
      ((witnessesEquiv hiddenUpstream totalDownstream hiddenBoundary
        (upstreamInput true)) ⟨hiddenZeroStore, hidden_zero_model⟩) =
        ⟨hiddenZeroStore, hidden_zero_model⟩ ∧
    (witnessesEquiv hiddenUpstream totalDownstream hiddenBoundary
        (upstreamInput true)).symm
      ((witnessesEquiv hiddenUpstream totalDownstream hiddenBoundary
        (upstreamInput true)) ⟨hiddenOneStore, hidden_one_model⟩) =
        ⟨hiddenOneStore, hidden_one_model⟩ := by
  exact ⟨Equiv.symm_apply_apply _ _, Equiv.symm_apply_apply _ _⟩

theorem hidden_witnesses_distinct :
    (witnessesEquiv hiddenUpstream totalDownstream hiddenBoundary (upstreamInput true))
      ⟨hiddenZeroStore, hidden_zero_model⟩ ≠
    (witnessesEquiv hiddenUpstream totalDownstream hiddenBoundary (upstreamInput true))
      ⟨hiddenOneStore, hidden_one_model⟩ := by
  intro h
  exact hidden_stores_distinct
    (congrArg Subtype.val
      ((witnessesEquiv hiddenUpstream totalDownstream hiddenBoundary
        (upstreamInput true)).injective h))

#print axioms cycle_composite_admissible
#print axioms cycle_zero_no_composite_extension
#print axioms hidden_zero_model
#print axioms hidden_one_model
#print axioms hidden_final_outputs_equal
#print axioms hidden_witnesses_roundtrip
#print axioms hidden_witnesses_distinct

end IndexedComponentModelCycleTest
