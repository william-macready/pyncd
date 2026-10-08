import LeanNCD.Semantics.Invariants

namespace LeanNCD.Semantics.Program

open scoped Classical

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable (P : Program K σ r) (ops : (s : S) → ScalarOps (K s))
variable [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]

theorem finalStore_agrees (c : P.Running) (complete : P.Complete c) :
    Agrees c.published (P.finalStore c complete) := by
  intro a v hv
  have eq := P.finalStore_published c complete a
  rw [hv] at eq
  exact (Option.some.inj eq).symm

theorem successful_model (η : P.Input) (c : P.Running) (success : P.Successful ops η c) :
    P.Models ops η (P.finalStore c success.2) := by
  obtain ⟨values, inv⟩ := P.reachable_invariant ops η success.1
  have consumed (t : P.Defined) (o : P.Occurrence t) :
      P.outcome ops (P.finalStore c success.2) t o = some (values t o) :=
    inv.consumed t o (by simp [success.2.1 t]) _ (P.finalStore_agrees c success.2)
  have admitted : P.AdmEnv ops (P.finalStore c success.2) := by
    intro t o
    simp [consumed t o]
  refine ⟨admitted, ?_, ?_⟩
  · intro t f hf p
    exact P.finalStore_agrees c success.2 ⟨t, p⟩ (f p) (inv.inputs t f hf p)
  · intro t p
    have pub := (inv.published t p _ (P.finalStore_published c success.2 ⟨t.val, p⟩)).2
    rw [pub, inv.conservation]
    have value (o : P.Occurrence t) :
        P.contribution ops (P.finalStore c success.2) admitted t o = values t o := by
      simp [contribution, consumed t o]
    simp [spent, success.2.1, collect, pushforward, value]

theorem finished_accumulator (η : P.Input) (c : P.Running) (values : P.History)
    (inv : P.Invariant ops η c values) (ρ : Store K σ) (agree : Agrees c.published ρ)
    (admitted : P.AdmEnv ops ρ) (t : P.Defined)
    (p : Coord (σ.signature t.val).axes) (finished : P.FiberEmpty c t p) :
    c.accumulators t p = P.collect ops ρ admitted t p := by
  rw [inv.conservation]
  simp only [spent, collect, pushforward]
  apply Finset.sum_congr rfl
  intro o _
  by_cases pending : o ∈ c.pending t
  · simp [pending, finished o pending]
  · have body := inv.consumed t o pending ρ agree
    have value : P.contribution ops ρ admitted t o = values t o := by
      simp [contribution, body]
    simp [pending, value]

def CandidateAgreement (ρ : Store K σ) : P.MachineState → Prop
  | .running c => Agrees c.published ρ
  | .failed _ _ _ => False

theorem candidate_preserved (η : P.Input) (ρ : Store K σ) (model : P.Models ops η ρ)
    {s : P.MachineState} (reached : P.Reaches ops (.running (P.initial η)) s) :
    P.CandidateAgreement ρ s := by
  obtain ⟨admitted, inputs, equations⟩ := model
  induction reached with
  | refl =>
    intro a v hv
    cases hf : η.val a.1 with
    | none => simp [initial, hf] at hv
    | some f =>
      have value : f a.2 = v := by simpa [initial, hf] using hv
      exact (inputs a.1 f hf a.2).trans value
  | tail reached step ih =>
    cases step with
    | contribute c t o v pending evaluated => exact ih
    | publication c t p unpublished finished =>
      obtain ⟨values, inv⟩ := P.reachable_invariant ops η reached
      have collected := P.finished_accumulator ops η c values inv ρ ih admitted t p finished
      have value : c.accumulators t p = ρ ⟨t.val, p⟩ :=
        collected.trans (equations t p).symm
      intro a v hv
      by_cases h : a = ⟨t.val, p⟩
      · subst a
        have eq : c.accumulators t p = v := by simpa [publish] using hv
        exact value.symm.trans eq
      · exact ih a v (by simpa [publish, Function.update, h] using hv)
    | undefined c t o pending evaluated =>
      have body := evaluated_consistent ops c.published ρ (P.body t o.1) o.2 none evaluated ih
      have defined := admitted t o
      simp [outcome, body] at defined

theorem successful_unique (η : P.Input) (c : P.Running) (success : P.Successful ops η c) :
    ∀ ρ, P.Models ops η ρ → ρ = P.finalStore c success.2 := by
  intro ρ model
  have agree := P.candidate_preserved ops η ρ model success.1
  funext a
  exact agree a _ (P.finalStore_published c success.2 a)

theorem successful_admInput (η : P.Input) (c : P.Running) (success : P.Successful ops η c) :
    P.AdmInput ops η :=
  ⟨P.finalStore c success.2, P.successful_model ops η c success,
    P.successful_unique ops η c success⟩

theorem successful_denotation (η : P.Input) (c : P.Running) (success : P.Successful ops η c) :
    P.denotation ops η (P.successful_admInput ops η c success) =
      P.outputProjection (P.finalStore c success.2) :=
  P.denotation_of_model ops η _ _ (P.successful_model ops η c success)

theorem failed_no_model (η : P.Input) (t : P.Defined) (o : P.Occurrence t) (c : P.Running)
    (reached : P.Reaches ops (.running (P.initial η)) (.failed t o c)) :
    ¬ ∃ ρ, P.Models ops η ρ := by
  rintro ⟨ρ, model⟩
  exact P.candidate_preserved ops η ρ model reached

#print axioms reachable_invariant
#print axioms successful_model
#print axioms candidate_preserved
#print axioms successful_unique
#print axioms successful_admInput
#print axioms successful_denotation
#print axioms failed_no_model

end LeanNCD.Semantics.Program
