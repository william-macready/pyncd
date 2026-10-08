import Semantics.ReferenceMachineTest
import LeanNCD.Semantics.Progress

namespace LeanNCD.Semantics.RankedMachineFixtures

open Fixtures CollectionModelFixtures ReferenceMachineFixtures Program
open scoped Classical

def footprintFreeCertificate (P : Program Carrier σ registry)
    (free : ∀ (t : P.Defined) (o : P.Occurrence t),
      footprint (P.body t o.1) o.2 = []) : P.RankCertificate where
  rank := fun _ => 0
  decreases := by
    rintro a b ⟨t, o, _, read⟩
    simp [free t o] at read

-- Donor: dependentP; retain its two different coordinates in one tensor.
def historyCertificate : dependentP.RankCertificate where
  rank := fun a => a.2.1.val
  decreases := by
    rintro a b ⟨t, ⟨s, ⟨v, hv⟩⟩, dest, read⟩
    change Fin 2 at s
    have ev : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases s
    · simp [dependentP, expressionProgram, footprint] at read
    · have hb : b = ⟨(), point 0⟩ := by
        simpa [dependentP, expressionProgram, footprint, direct] using read
      subst b
      subst a
      norm_num [dependentP, expressionProgram, point]

theorem history_unstuck :
    ∃ s, dependentP.Step ops (.running p0) s :=
  dependentP.ranked_progress ops historyCertificate _ p0 (.refl _) (by
    intro complete
    have h := complete.1 pt
    have pending : po 0 ∈ p0.pending pt := by simp [p0, initial]
    simp [h] at pending)

-- Donor: cycleP; add a strict zero operand, then exclude its valuation.
@[reducible] def maskedSelf (keep : Bool) :=
  expressionProgram 1 (fun _ => 0) keep
    (fun _ _ => .binary .mul (.lit 0) (direct (fun _ => 0)))

theorem masked_self_edge :
    (⟨(), point 0⟩ : Address declarations) ∈ (maskedSelf true).dependencies ⟨(), point 0⟩ :=
  ⟨⟨(), rfl⟩, ⟨0, ⟨0, rfl⟩⟩, rfl, by simp [maskedSelf, expressionProgram, footprint, direct]⟩

theorem masked_self_no_certificate : ¬ Nonempty (maskedSelf true).RankCertificate := by
  rintro ⟨certificate⟩
  have h := certificate.decreases _ _ masked_self_edge
  omega

def excludedSelfCertificate : (maskedSelf false).RankCertificate :=
  footprintFreeCertificate _ (by
    intro t o
    have h := o.2.property
    contradiction)

-- Donor: selected/tabulated; the selected coordinate is 1, but coordinate 2 is read too.
@[reducible] def selectedP := expressionProgram 1 (fun _ => 0) true
  (fun _ _ => .at (.tab vectorShape (canonicalLayout _)
    (direct (fun γ => γ.2.1))) (fun _ => point 1))

theorem off_selected_edge :
    (⟨(), point 2⟩ : Address declarations) ∈ selectedP.dependencies ⟨(), point 0⟩ := by
  refine ⟨⟨(), rfl⟩, ⟨0, ⟨0, rfl⟩⟩, rfl, ?_⟩
  decide

-- Donor: constRead; preserve resolved constant boundary, with an admitted Unit context.
@[reducible] def boundaryP := expressionProgram 1 (fun _ => 0) true
  (fun _ _ => .read () ⟨constantPolicy, fun _ _ => -1,
    fun _ => .const 9, by intro _; rfl⟩)

def boundaryCertificate : boundaryP.RankCertificate :=
  footprintFreeCertificate _ (by intro t o; rfl)

theorem boundary_no_edge (a b : Address declarations) : b ∉ boundaryP.dependencies a := by
  rintro ⟨t, o, _, read⟩
  simp [footprint] at read

-- Donors: nested and arrayPrimitive; retain reduction and primitive argument reads.
@[reducible] def reductionP := expressionProgram 1 (fun _ => 0) true
  (fun _ _ => .reduce 2 (direct (fun γ => ⟨γ.2.val, by omega⟩)))
@[reducible] def primitiveP := expressionProgram 1 (fun _ => 0) true
  (fun _ _ => .at (.prim (r := registry) Op.identityArray (fun _ =>
    .tab vectorShape (canonicalLayout _) (direct (fun γ => γ.2.1))))
      (fun _ => point 1))
theorem reduction_edge :
    (⟨(), point 1⟩ : Address declarations) ∈ reductionP.dependencies ⟨(), point 0⟩ := by
  refine ⟨⟨(), rfl⟩, ⟨0, ⟨0, rfl⟩⟩, rfl, ?_⟩
  decide
theorem primitive_off_selected_edge :
    (⟨(), point 2⟩ : Address declarations) ∈ primitiveP.dependencies ⟨(), point 0⟩ := by
  refine ⟨⟨(), rfl⟩, ⟨0, ⟨0, rfl⟩⟩, rfl, ?_⟩
  decide
theorem input_has_no_dependencies :
    scalarRole.dependencies ⟨0, ()⟩ = ∅ :=
  scalarRole.input_dependencies_empty _ rfl

def duplicateCertificate : duplicate.RankCertificate :=
  footprintFreeCertificate _ (by intro t o; rfl)
def failureCertificate : badP.RankCertificate :=
  footprintFreeCertificate _ (by intro t o; rfl)

-- Donor: scalarRole, remove the input and both extra tensor identifiers.
@[reducible] def singletonDeclarations : Declarations ScalarSort :=
  ⟨Unit, fun _ => 9, fun a b _ => by cases a; cases b; rfl, fun _ => ⟨.rational, []⟩⟩
@[reducible] def singletonP : Program Carrier singletonDeclarations registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun _ => false
  output_defined := by intros; rfl
  statements := fun _ => 0
  valuations := fun _ s => nomatch s
  guard := fun _ s => nomatch s
  destination := fun _ s => nomatch s
  body := fun _ s => nomatch s
def singletonInput : singletonP.Input := ⟨fun _ => none, by intro _; rfl⟩
def singletonCertificate : singletonP.RankCertificate :=
  footprintFreeCertificate _ (by intro t o; exact Fin.elim0 o.1)
theorem singleton_rank_zero : singletonCertificate.rank ⟨(), ()⟩ = 0 := rfl

-- Donor: singletonP/emptyShape, change only the coordinate extent to zero.
@[reducible] def emptyDeclarations : Declarations ScalarSort :=
  ⟨Unit, fun _ => 9, fun a b _ => by cases a; cases b; rfl,
    fun _ => ⟨.rational, emptyShape.axes⟩⟩
@[reducible] def emptyP : Program Carrier emptyDeclarations registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun _ => false
  output_defined := by intros; rfl
  statements := fun _ => 0
  valuations := fun _ s => nomatch s
  guard := fun _ s => nomatch s
  destination := fun _ s => nomatch s
  body := fun _ s => nomatch s
def emptyInputP : emptyP.Input := ⟨fun _ => none, by intro _; rfl⟩
def emptyCertificate : emptyP.RankCertificate :=
  footprintFreeCertificate _ (by intro t o; exact Fin.elim0 o.1)

theorem zero_extent_no_addresses (a : Address emptyDeclarations) : False :=
  Fin.elim0 a.2.1

theorem zero_extent_initial_complete : emptyP.Complete (emptyP.initial emptyInputP) := by
  constructor
  · intro t
    ext o
    exact Fin.elim0 o.1
  · intro a
    exact False.elim (zero_extent_no_addresses a)

-- Donors: d0/d1, z0/z1, n0/n1, r0/r1/r2. Values below are proof observations.
theorem duplicate_initial_count : duplicate.measure d0 = 5 := by
  rw [show d0 = duplicate.initial dinput from rfl, initial_measure]
  have tags : Fintype.card (duplicate.Occurrence dt) = 2 := by
    let e : duplicate.Occurrence dt ≃ Fin 2 :=
      { toFun := fun o => o.1
        invFun := dtag
        left_inv := by
          rintro ⟨s, v⟩
          change {v : Fin 1 // true = true} at v
          have h : v = ⟨0, rfl⟩ := Subtype.ext (Subsingleton.elim _ _)
          subst v
          rfl
        right_inv := fun _ => rfl }
    simpa using Fintype.card_congr e
  have addresses : @Fintype.card duplicate.DefinedAddress (definedAddressFintype duplicate) = 3 := by
    let e : duplicate.DefinedAddress ≃ Fin 3 :=
      { toFun := fun a => a.2.1
        invFun := fun i => ⟨dt, point i⟩
        left_inv := by
          rintro ⟨t, p⟩
          have h : t = dt := Subsingleton.elim _ _
          subst t
          rcases p with ⟨i, u⟩
          cases u
          rfl
        right_inv := fun _ => rfl }
    simpa only [Fintype.card_fin] using
      (@Fintype.card_congr _ _ (definedAddressFintype duplicate) _ e)
  rw [addresses]
  letI : Unique duplicate.Defined :=
    { default := dt, uniq := fun t => Subtype.ext (Subsingleton.elim _ _) }
  simp [occurrenceCount, tags]

theorem duplicate_consume_count : duplicate.measure d1 = 4 := by
  have h := duplicate.consume_measure d0 dt (dtag 0) 2 (by simp [d0, initial])
  change duplicate.measure d0 = duplicate.measure d1 + 1 at h
  have initialCount := duplicate_initial_count
  omega

theorem zero_consumption_decreases : zP.measure z0 = zP.measure z1 + 1 :=
  zP.consume_measure z0 zt zo 0 (by simp [z0, initial])

theorem empty_fiber_decreases : noStatements.measure n0 = noStatements.measure n1 + 1 :=
  noStatements.running_step_measure ops empty_fiber_publication

theorem nonoutput_decreases : roleProgram.measure r1 = roleProgram.measure r2 + 1 :=
  roleProgram.publish_measure r1 ⟨2, rfl⟩ () (by simp [r1, r0, publish, initial, supplied, presentEmpty])

theorem singleton_initial_count : singletonP.measure (singletonP.initial singletonInput) = 1 := by
  rw [initial_measure]
  have addresses :
      @Fintype.card singletonP.DefinedAddress (definedAddressFintype singletonP) = 1 := by
    let e : singletonP.DefinedAddress ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨⟨(), rfl⟩, ()⟩
        left_inv := by
          rintro ⟨⟨u, h⟩, p⟩
          cases u
          cases p
          rfl
        right_inv := fun _ => Subsingleton.elim _ _ }
    simpa using Fintype.card_congr e
  rw [addresses]
  simp [occurrenceCount, singletonP, Occurrence]

theorem empty_initial_count : emptyP.measure (emptyP.initial emptyInputP) = 0 := by
  rw [initial_measure]
  letI : IsEmpty emptyP.DefinedAddress := ⟨fun a => Fin.elim0 a.2.1⟩
  simp [occurrenceCount, emptyP, Occurrence]

theorem ready_failure_maximal : badP.Maximal ops binput (.failed bt bo b0) :=
  ⟨(Reaches.refl _).tail located_failure, by
    rintro ⟨s, step⟩
    exact failure_terminal s step⟩

theorem ready_failure_no_model : ¬ ∃ ρ, badP.Models ops binput ρ := failure_excludes_models

theorem cycle_model_and_blocked : cycleP.Models ops yinput cycleStore ∧ cycleP.Blocked ops y2 :=
  ⟨cycle_model, cycle_blocked⟩

theorem stopped_prefix_not_maximal : ¬ duplicate.Maximal ops dinput (.running d0) := by
  intro maximal
  exact maximal.2 ⟨_, Step.contribute d0 dt (dtag 0) 2 (by simp [d0, initial]) rfl⟩

-- Donor: duplicate_success; generic correspondence supplies a second maximal schedule
-- from a distinct first contribution, without introducing an executable chooser.
theorem second_schedule :
    ∃ c, ∃ success : duplicate.Successful ops dinput c,
      duplicate.Reaches ops (.running (duplicate.consume d0 dt (dtag 1) 2)) (.running c) ∧
        duplicate.finalStore c success.2 = duplicate.finalStore d5 duplicate_success.2 := by
  let first := duplicate.consume d0 dt (dtag 1) 2
  have reached : duplicate.Reaches ops (.running d0) (.running first) :=
    (Reaches.refl _).tail (.contribute d0 dt (dtag 1) 2 (by simp [d0, initial]) rfl)
  obtain ⟨s, extension, maximal⟩ := duplicate.maximal_extension ops dinput (.running first) reached
  obtain ⟨c, success, eq, same⟩ := duplicate.model_maximal_success ops duplicateCertificate dinput
    _ duplicate_model_without_witness s maximal
  subst s
  exact ⟨c, success, extension, same⟩

-- Donor: duplicate; two tags are now independently ready undefined occurrences.
@[reducible] def twoBad := expressionProgram 2 (fun _ => 0) true (fun _ _ => bad)
abbrev twoBadTarget : twoBad.Defined := ⟨(), rfl⟩
abbrev twoBadTag (s : Fin 2) : twoBad.Occurrence twoBadTarget := ⟨s, ⟨0, rfl⟩⟩
def twoBadInput := emptyInput twoBad (fun _ => rfl)
def twoBadInitial := twoBad.initial twoBadInput

theorem distinct_first_failures :
    (∀ s : Fin 2, twoBad.Maximal ops twoBadInput
      (.failed twoBadTarget (twoBadTag s) twoBadInitial)) ∧ twoBadTag 0 ≠ twoBadTag 1 := by
  constructor
  · intro s
    refine ⟨(Reaches.refl _).tail (.undefined _ _ _ (by simp [initial]) rfl), ?_⟩
    rintro ⟨u, step⟩
    exact twoBad.failed_terminal ops _ _ _ u step
  · intro eq
    have h := congrArg (fun o : twoBad.Occurrence twoBadTarget => o.1.val) eq
    norm_num [twoBadTag] at h

theorem ranked_singleton_correspondence (ρ : Store Carrier singletonDeclarations) :
    (∃ c, ∃ success : singletonP.Successful ops singletonInput c,
      singletonP.finalStore c success.2 = ρ) ↔
        {ρ' | singletonP.Models ops singletonInput ρ'} = {ρ} :=
  singletonP.initialization_iff_singleton ops singletonCertificate singletonInput ρ

#print axioms historyCertificate
#print axioms duplicate_initial_count
#print axioms singleton_initial_count
#print axioms empty_initial_count
#print axioms second_schedule
#print axioms distinct_first_failures
#print axioms ranked_singleton_correspondence

end LeanNCD.Semantics.RankedMachineFixtures
