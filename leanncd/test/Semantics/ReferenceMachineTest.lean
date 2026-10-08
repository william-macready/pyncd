import Semantics.CollectionModelTest
import LeanNCD.Semantics.Soundness

namespace LeanNCD.Semantics.ReferenceMachineFixtures
open Fixtures CollectionModelFixtures Program
open scoped Classical

def emptyInput (P : Program Carrier declarations registry) (noInputs : ∀ t, P.input t = false) :
    P.Input := ⟨fun _ => none, by intro t; simp [noInputs t]⟩

abbrev dt : duplicate.Defined := ⟨(), rfl⟩
abbrev dtag (s : Fin 2) : duplicate.Occurrence dt := ⟨s, ⟨(0 : Fin 1), rfl⟩⟩
def dinput := emptyInput duplicate (fun _ => rfl)
def d0 := duplicate.initial dinput
noncomputable def d1 := duplicate.consume d0 dt (dtag 0) 2
noncomputable def d2 := duplicate.consume d1 dt (dtag 1) 2
noncomputable def d3 := duplicate.publish d2 dt (point 0)
noncomputable def d4 := duplicate.publish d3 dt (point 1)
noncomputable def d5 := duplicate.publish d4 dt (point 2)

theorem duplicate_pending_empty : ∀ t, d2.pending t = ∅ := by
  rintro ⟨⟨⟩, h⟩
  ext o
  rcases o with ⟨s, ⟨v, hv⟩⟩
  change Fin 2 at s
  change Fin 1 at v
  have ev : v = 0 := Subsingleton.elim _ _
  subst v
  fin_cases s <;> simp [d2, d1, d0, initial, consume, dtag]

theorem duplicate_barrier : ¬ duplicate.FiberEmpty d1 dt (point 0) := by
  intro h
  exact h (dtag 1) (by simp [d1, d0, consume, initial, dtag]) rfl

theorem duplicate_erased : dtag 0 ∉ d1.pending dt := by simp [d1, consume]

theorem duplicate_sum : d2.accumulators dt (point 0) = 4 := by
  norm_num [d2, d1, d0, consume, initial, duplicate, vectorProgram, expressionProgram, dtag, dt]
  norm_num [show duplicate.destination dt (dtag 0).1 (dtag 0).2 = point 0 from rfl,
    show duplicate.destination dt (dtag 1).1 (dtag 1).2 = point 0 from rfl]

theorem duplicate_order :
    (duplicate.consume (duplicate.consume d0 dt (dtag 1) 2) dt (dtag 0) 2).accumulators =
      d2.accumulators := by
  funext t p
  have ht : t = dt := Subtype.ext (Subsingleton.elim _ _)
  subst t
  simp [d2, d1, consume, duplicate, vectorProgram, expressionProgram, dtag]
  rfl

theorem duplicate_complete : duplicate.Complete d5 := by
  refine ⟨duplicate_pending_empty, ?_⟩
  rintro ⟨⟨⟩, i, u⟩
  cases u
  fin_cases i <;> simp [d5, d4, d3, publish, point]

theorem duplicate_success : duplicate.Successful ops dinput d5 := by
  have h0 : duplicate.Reaches ops (.running d0) (.running d0) := .refl _
  have h1 := h0.tail (Step.contribute d0 dt (dtag 0) 2 (by simp [d0, initial]) (by rfl))
  have h2 := h1.tail (Step.contribute d1 dt (dtag 1) 2
    (by simp [d1, consume, d0, initial, dtag]) (by rfl))
  have h3 := h2.tail (Step.publication d2 dt (point 0) (by rfl)
    (by intro o ho; simp [duplicate_pending_empty] at ho))
  have h4 := h3.tail (Step.publication d3 dt (point 1)
    (by simp [d3, publish, point, d2, d1, d0, consume, initial, dinput, emptyInput])
    (by intro o ho; simp [d3, publish, duplicate_pending_empty] at ho))
  have h5 := h4.tail (Step.publication d4 dt (point 2)
    (by simp [d4, d3, publish, point, d2, d1, d0, consume, initial, dinput, emptyInput])
    (by intro o ho; simp [d4, d3, publish, duplicate_pending_empty] at ho))
  exact ⟨h5, duplicate_complete⟩

theorem duplicate_model_without_witness :
    duplicate.Models ops dinput (duplicate.finalStore d5 duplicate_complete) :=
  duplicate.successful_model ops dinput d5 duplicate_success

theorem duplicate_unique_among_all_models :
    duplicate.AdmInput ops dinput :=
  duplicate.successful_admInput ops dinput d5 duplicate_success

theorem published_not_overwritable : d3.published ⟨(), point 0⟩ ≠ none := by
  simp [d3, publish]

theorem publication_retains_accumulator : d3.accumulators = d2.accumulators := rfl

abbrev ct : collision.Defined := ⟨(), rfl⟩
abbrev ctag (s : Fin 3) : collision.Occurrence ct := ⟨s, ⟨(0 : Fin 1), rfl⟩⟩
def c0 := collision.initial (emptyInput collision (fun _ => rfl))
noncomputable def c012 := collision.consume
  (collision.consume (collision.consume c0 ct (ctag 0) 2) ct (ctag 1) 7) ct (ctag 2) 5
noncomputable def c210 := collision.consume
  (collision.consume (collision.consume c0 ct (ctag 2) 5) ct (ctag 1) 7) ct (ctag 0) 2

theorem collision_order : c012.accumulators = c210.accumulators := by
  funext t p
  have ht : t = ct := Subtype.ext (Subsingleton.elim _ _)
  subst t
  simp [c012, c210, c0, consume, initial]
  ac_rfl

theorem collision_sum : c012.accumulators ct (point 0) = 9 := by
  have dest (s : Fin 3) : collision.destination ct (ctag s).1 (ctag s).2 =
      point (if s = 2 then 2 else 0) := rfl
  have different : point 2 ≠ point 0 := by
    intro h
    have eq : (2 : Fin 3) = 0 := congrArg Prod.fst h
    exact (by decide : (2 : Fin 3) ≠ 0) eq
  norm_num [c012, c0, consume, initial, dest, Fin.ext_iff, different]

def n0 := noStatements.initial (emptyInput noStatements (fun _ => rfl))
noncomputable def n1 := noStatements.publish n0 ⟨(), rfl⟩ (point 1)
theorem empty_fiber_publication :
    noStatements.Step ops (.running n0) (.running n1) :=
  .publication _ _ _ rfl (by intro o; exact Fin.elim0 o.1)
theorem unwritten_zero : n1.published ⟨(), point 1⟩ = some 0 := by simp [n1, n0, publish, initial]

@[reducible] def zP := partialProgram true true
abbrev zt : zP.Defined := ⟨(), rfl⟩
abbrev zo : zP.Occurrence zt := ⟨0, ⟨0, rfl⟩⟩
def z0 := zP.initial (emptyInput zP (fun _ => rfl))
noncomputable def z1 := zP.consume z0 zt zo 0
theorem zero_consumed : zP.Step ops (.running z0) (.running z1) ∧ zo ∉ z1.pending zt :=
  ⟨.contribute _ _ _ _ (by simp [z0, initial])
    (by norm_num [evalReady, checkReads, footprint, evalWith, zP, partialProgram,
      expressionProgram, ops, ScalarOps.combine]), by simp [z1, consume]⟩

@[reducible] def badP := partialProgram true false
abbrev bt : badP.Defined := ⟨(), rfl⟩
abbrev bo : badP.Occurrence bt := ⟨0, ⟨0, rfl⟩⟩
def binput := emptyInput badP (fun _ => rfl)
def b0 := badP.initial binput
theorem located_failure : badP.Step ops (.running b0) (.failed bt bo b0) :=
  .undefined _ _ _ (by simp [b0, initial]) rfl
theorem failure_retains_tag : bo ∈ b0.pending bt := by simp [b0, initial]
theorem failure_terminal : ∀ s, ¬ badP.Step ops (.failed bt bo b0) s :=
  badP.failed_terminal ops bt bo b0
theorem failure_excludes_models : ¬ ∃ ρ, badP.Models ops binput ρ :=
  badP.failed_no_model ops binput bt bo b0 ((Reaches.refl _).tail located_failure)

@[reducible] def excludedP := partialProgram false false
def e0 := excludedP.initial (emptyInput excludedP (fun _ => rfl))
theorem excluded_no_occurrence (t : excludedP.Defined) (o : excludedP.Occurrence t) : False := by
  have h := o.2.property
  contradiction

@[reducible] def dependentP := expressionProgram 2 (fun s => if s = 0 then 0 else 1) true
  (fun _ s => if s = 0 then .lit 2 else direct (fun _ => 0))
abbrev pt : dependentP.Defined := ⟨(), rfl⟩
abbrev po (s : Fin 2) : dependentP.Occurrence pt := ⟨s, ⟨0, rfl⟩⟩
def p0 := dependentP.initial (emptyInput dependentP (fun _ => rfl))
noncomputable def p1 := dependentP.consume p0 pt (po 0) 2
noncomputable def p2 := dependentP.publish p1 pt (point 0)
theorem dependent_waits :
    p1.accumulators pt (point 0) = 2 ∧
      evalReady ops p1.published (dependentP.body pt (po 1).1) (po 1).2 = .notReady := by
  constructor
  · norm_num [p1, p0, consume, initial, dependentP, expressionProgram, po]
  · rfl
theorem dependent_reads_published :
    evalReady ops p2.published (dependentP.body pt (po 1).1) (po 1).2 = .evaluated (some 2) := by
  simp [evalReady, checkReads, footprint, dependentP, expressionProgram, po, direct,
    evalWith, p2, p1, p0, publish, consume, initial]

theorem dependent_publication :
    dependentP.Step ops (.running p1) (.running p2) := by
  apply Step.publication _ _ _ rfl
  rintro ⟨s, ⟨v, hv⟩⟩ pending
  have ev : v = 0 := Subsingleton.elim _ _
  subst v
  fin_cases s
  · simp [p1, consume, po] at pending
  · intro eq
    have indices := congrArg (fun p : Coord vectorShape.axes => p.1.val) eq
    norm_num [dependentP, expressionProgram, point] at indices

theorem dependent_contribution :
    dependentP.Step ops (.running p2) (.running (dependentP.consume p2 pt (po 1) 2)) :=
  .contribute _ _ _ _ (by simp [p2, publish, p1, consume, p0, initial, po])
    dependent_reads_published

@[reducible] def waitingBad := expressionProgram 1 (fun _ => 0) true
  (fun _ _ => .binary .add (direct (fun _ => 0)) bad)
def w0 := waitingBad.initial (emptyInput waitingBad (fun _ => rfl))
abbrev wt : waitingBad.Defined := ⟨(), rfl⟩
abbrev wo : waitingBad.Occurrence wt := ⟨0, ⟨0, rfl⟩⟩
theorem unavailable_dominates_undefined :
    evalReady ops w0.published (waitingBad.body wt wo.1) wo.2 = .notReady := rfl

@[reducible] def cycleP := expressionProgram 1 (fun _ => 0) true (fun _ _ => direct (fun _ => 0))
abbrev yt : cycleP.Defined := ⟨(), rfl⟩
def yinput := emptyInput cycleP (fun _ => rfl)
def y0 := cycleP.initial yinput
noncomputable def y1 := cycleP.publish y0 yt (point 1)
noncomputable def y2 := cycleP.publish y1 yt (point 2)
def cycleStore : Store Carrier declarations := fun _ => 0
theorem cycle_model : cycleP.Models ops yinput cycleStore := by
  have admitted : cycleP.AdmEnv ops cycleStore := by intro t o; rfl
  refine ⟨admitted, ?_, ?_⟩
  · intro t f hf; cases hf
  · rintro ⟨⟨⟩, h⟩ ⟨i, u⟩
    cases u
    fin_cases i <;> simp [collect, pushforward, contribution, outcome, interpret, evalWith,
      cycleP, expressionProgram, cycleStore, direct, point, ops]
theorem cycle_blocked : cycleP.Blocked ops y2 := by
  refine ⟨?_, ?_⟩
  · intro complete
    have h := complete.1 yt
    have mem : (⟨0, ⟨0, rfl⟩⟩ : cycleP.Occurrence yt) ∈ y2.pending yt := by
      simp [y2, y1, y0, publish, initial]
    rw [h] at mem
    simp at mem
  · rintro ⟨s, step⟩
    cases step with
    | contribute c t o v pending evaluated =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases o with ⟨i, ⟨j, hj⟩⟩
      have hi : i = 0 := Subsingleton.elim _ _
      have hv : j = 0 := Subsingleton.elim _ _
      subst i; subst j
      simp [evalReady, cycleP, expressionProgram, direct, footprint, checkReads,
        y2, y1, y0, publish, initial, yinput, emptyInput, point] at evaluated
    | publication c t p unpublished finished =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases p with ⟨i, u⟩
      cases u
      fin_cases i
      · exact finished ⟨0, ⟨0, rfl⟩⟩ (by simp [y2, y1, y0, publish, initial]) rfl
      · simp [y2, y1, publish, point] at unpublished
      · simp [y2, publish, point] at unpublished
    | undefined c t o pending evaluated =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases o with ⟨i, ⟨j, hj⟩⟩
      have hi : i = 0 := Subsingleton.elim _ _
      have hv : j = 0 := Subsingleton.elim _ _
      subst i; subst j
      simp [evalReady, cycleP, expressionProgram, direct, footprint, checkReads,
        y2, y1, y0, publish, initial, yinput, emptyInput, point] at evaluated

def r0 := roleProgram.initial supplied
noncomputable def r1 := roleProgram.publish r0 ⟨1, rfl⟩ ()
noncomputable def r2 := roleProgram.publish r1 ⟨2, rfl⟩ ()
theorem nonoutput_required : ¬ roleProgram.Complete r1 := by
  intro complete
  have h := complete.2 ⟨2, ()⟩
  simp [r1, r0, publish, initial, supplied, presentEmpty] at h
theorem empty_input_and_nonoutput_complete : roleProgram.Complete r2 := by
  constructor
  · intro t
    simp [r2, r1, r0, publish, initial, roleProgram]
  · rintro ⟨t, p⟩
    fin_cases t
    · exact Fin.elim0 p.1
    · change Unit at p
      cases p
      simp [r2, r1, publish]
    · change Unit at p
      cases p
      simp [r2, publish]

@[reducible] def valuationP : Program Carrier declarations registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun _ => false
  output_defined := by intros; rfl
  statements := fun _ => 1
  valuations := fun _ _ => 2
  guard := fun _ _ _ => true
  destination := fun _ _ _ => point 0
  body := fun _ _ => .lit 2
abbrev vt : valuationP.Defined := ⟨(), rfl⟩
abbrev vo (v : Fin 2) : valuationP.Occurrence vt := ⟨0, ⟨v, rfl⟩⟩
def v0 := valuationP.initial (emptyInput valuationP (fun _ => rfl))
noncomputable def v1 := valuationP.consume v0 vt (vo 0) 2
theorem valuation_multiplicity : vo 0 ∉ v1.pending vt ∧ vo 1 ∈ v1.pending vt := by
  simp [v1, consume, v0, initial, vo]

@[reducible] def scalarDeclarations : Declarations ScalarSort :=
  ⟨Fin 3, fun t => t.val, fun _ _ h => Fin.ext h, fun _ => ⟨.rational, []⟩⟩
@[reducible] def scalarRole : Program Carrier scalarDeclarations registry where
  tensors := inferInstance
  input := roleProgram.input
  output := roleProgram.output
  output_defined := roleProgram.output_defined
  statements := fun _ => 0
  valuations := fun _ s => nomatch s
  guard := fun _ s => nomatch s
  destination := fun _ s => nomatch s
  body := fun _ s => nomatch s
def scalarInput : scalarRole.Input :=
  ⟨fun t => if t = 0 then some (fun _ => 7) else none, by intro t; fin_cases t <;> rfl⟩
def s0 := scalarRole.initial scalarInput
noncomputable def s1 := scalarRole.publish s0 ⟨1, rfl⟩ ()
theorem immutable_input : s1.published ⟨0, ()⟩ = s0.published ⟨0, ()⟩ := by
  simp [s1, publish]
theorem input_present_and_defined_absent :
    s0.published ⟨0, ()⟩ = some 7 ∧ s0.published ⟨1, ()⟩ = none := by
  constructor <;> rfl

def readinessLabel {V : Type} : ReadyResult V → String
  | .notReady => "notReady"
  | .evaluated none => "undefined"
  | .evaluated (some _) => "defined"
#eval [
  readinessLabel (evalReady ops p0.published (dependentP.body pt (po 1).1) (po 1).2),
  readinessLabel (evalReady ops w0.published (waitingBad.body wt wo.1) wo.2),
  readinessLabel (evalReady ops b0.published (badP.body bt bo.1) bo.2)]
#eval [readyObservation zeroStrict, readyObservation remapRead]
#print axioms duplicate_model_without_witness
#print axioms failure_excludes_models
#print axioms cycle_blocked

end LeanNCD.Semantics.ReferenceMachineFixtures
