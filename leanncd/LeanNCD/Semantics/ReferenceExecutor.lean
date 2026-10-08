import LeanNCD.Semantics.ExecutableSelection

namespace LeanNCD.Semantics.Program.Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable (P : Program K σ r) [DecidableEq σ.Tensor]
variable [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))

theorem validate_accepts (schedule : Schedule P) (η : P.Input) :
    validate P schedule η.val = .ok η := by
  unfold validate
  split
  · rename_i t found
    have bad := List.find?_some found
    simp [η.property t] at bad
  · rfl

theorem validate_preserves (schedule : Schedule P)
    (η : InputBinding (K := K) (σ := σ)) (input : P.Input)
    (h : validate P schedule η = .ok input) : input.val = η := by
  unfold validate at h
  split at h
  · contradiction
  · cases h
    rfl

inductive Execution : List (Event P) → P.MachineState → P.MachineState → Prop
  | nil (s) : Execution [] s s
  | cons {c : P.Running} {e : Event P} {events : List (Event P)} {s : P.MachineState}
      (legal : e.Legal P ops c) (tail : Execution events (e.effect P c) s) :
      Execution (e :: events) (.running c) s

theorem Execution.reaches {events : List (Event P)} {a b : P.MachineState}
    (execution : Execution P ops events a b) : P.Reaches ops a b := by
  induction execution with
  | nil => exact .refl _
  | cons legal _ ih =>
    exact P.reaches_trans ops ((Reaches.refl _).tail (Event.legal_step P ops _ _ legal)) ih

inductive Outcome
  | complete (c : P.Running) (complete : P.Complete c)
  | failed (t : P.Defined) (o : P.Occurrence t) (snapshot : P.Running)
  | blocked (c : P.Running) (observations : List (Observation P)) (blocked : P.Blocked ops c)
  | exhausted (c : P.Running)

def Outcome.state : Outcome P ops → P.MachineState
  | .complete c _ | .blocked c _ _ | .exhausted c => .running c
  | .failed t o c => .failed t o c

def Outcome.isExhausted : Outcome P ops → Bool
  | .exhausted _ => true
  | _ => false

def Outcome.kind : Outcome P ops → String
  | .complete _ _ => "complete"
  | .failed _ _ _ => "failed"
  | .blocked _ _ _ => "blocked"
  | .exhausted _ => "exhausted"

structure Result (start : P.MachineState) where
  outcome : Outcome P ops
  events : List (Event P)
  execution : Execution P ops events start outcome.state

def runFuel (schedule : Schedule P) (fuel : Nat) (start : P.MachineState) :
    Result P ops start :=
  match start with
  | .failed t o c => ⟨.failed t o c, [], .nil _⟩
  | .running c =>
    letI := completeDecidable P c
    if hc : P.Complete c then ⟨.complete c hc, [], .nil _⟩
    else match hs : select P ops schedule c with
    | none => ⟨.blocked c (observations P ops schedule c)
        ⟨hc, (select_none_iff P ops schedule c).mp hs⟩, [], .nil _⟩
    | some move => match fuel with
      | 0 => ⟨.exhausted c, [], .nil _⟩
      | fuel + 1 =>
        let tail := runFuel schedule fuel (move.event.effect P c)
        ⟨tail.outcome, move.event :: tail.events, .cons move.legal tail.execution⟩

theorem runFuel_not_exhausted (schedule : Schedule P) (fuel : Nat) (s : P.MachineState)
    (enough : P.stateMeasure s ≤ fuel) :
    (runFuel P ops schedule fuel s).outcome.isExhausted = false := by
  induction fuel generalizing s with
  | zero =>
    cases s with
    | failed => rfl
    | running c =>
      simp only [stateMeasure] at enough
      omega
  | succ fuel ih =>
    cases s with
    | failed => rfl
    | running c =>
      unfold runFuel
      split
      · rfl
      · split
        · rfl
        · rename_i move selected
          apply ih
          have decreases := P.step_decreases ops (move.event.legal_step P ops c move.legal)
          omega

def run (schedule : Schedule P) (η : P.Input) :
    Result P ops (.running (P.initial η)) :=
  runFuel P ops schedule (initialBudget P) (.running (P.initial η))

theorem run_not_exhausted (schedule : Schedule P) (η : P.Input) :
    (run P ops schedule η).outcome.isExhausted = false :=
  runFuel_not_exhausted P ops schedule _ _ (le_of_eq (initialBudget_agrees P η).symm)

theorem result_success (η : P.Input) (result : Result P ops (.running (P.initial η)))
    (c : P.Running) (complete : P.Complete c)
    (h : result.outcome = .complete c complete) : P.Successful ops η c := by
  have reached := result.execution.reaches P ops
  rw [h] at reached
  exact ⟨reached, complete⟩

theorem result_model (η : P.Input) (result : Result P ops (.running (P.initial η)))
    (c : P.Running) (complete : P.Complete c) (h : result.outcome = .complete c complete) :
    P.Models ops η (P.finalStore c complete) :=
  P.successful_model ops η c (result_success P ops η result c complete h)

theorem result_unique (η : P.Input) (result : Result P ops (.running (P.initial η)))
    (c : P.Running) (complete : P.Complete c) (h : result.outcome = .complete c complete) :
    ∀ ρ, P.Models ops η ρ → ρ = P.finalStore c complete :=
  P.successful_unique ops η c (result_success P ops η result c complete h)

theorem result_denotation (η : P.Input) (result : Result P ops (.running (P.initial η)))
    (c : P.Running) (complete : P.Complete c) (h : result.outcome = .complete c complete) :
    P.denotation ops η (P.successful_admInput ops η c
      (result_success P ops η result c complete h)) = P.outputProjection (P.finalStore c complete) :=
  P.successful_denotation ops η c (result_success P ops η result c complete h)

theorem result_failure (η : P.Input) (result : Result P ops (.running (P.initial η)))
    (t : P.Defined) (o : P.Occurrence t) (c : P.Running)
    (h : result.outcome = .failed t o c) : ¬ ∃ ρ, P.Models ops η ρ := by
  apply P.failed_no_model ops η t o c
  have reached := result.execution.reaches P ops
  rwa [h] at reached

theorem result_not_blocked (certificate : P.RankCertificate) (η : P.Input)
    (result : Result P ops (.running (P.initial η))) (c : P.Running)
    (diagnostics : List (Observation P)) (blocked : P.Blocked ops c) :
    result.outcome ≠ .blocked c diagnostics blocked := by
  intro h
  have reached := result.execution.reaches P ops
  rw [h] at reached
  exact blocked.2 (P.ranked_progress ops certificate η c reached blocked.1)

theorem run_ranked_dichotomy (schedule : Schedule P) (certificate : P.RankCertificate)
    (η : P.Input) :
    (∃ c complete, (run P ops schedule η).outcome = .complete c complete) ∨
    (∃ t o c, (run P ops schedule η).outcome = .failed t o c ∧
      ¬ ∃ ρ, P.Models ops η ρ) := by
  cases h : (run P ops schedule η).outcome with
  | complete c complete => exact .inl ⟨c, complete, rfl⟩
  | failed t o c => exact .inr ⟨t, o, c, rfl, result_failure P ops η _ t o c h⟩
  | blocked c diagnostics blocked =>
    exact False.elim (result_not_blocked P ops certificate η _ c diagnostics blocked h)
  | exhausted c =>
    have noExhaustion := run_not_exhausted P ops schedule η
    simp [h, Outcome.isExhausted] at noExhaustion

structure ValidatedResult where
  input : P.Input
  result : Result P ops (.running (P.initial input))

def runValidated (schedule : Schedule P) (η : InputBinding (K := K) (σ := σ)) :
    Except σ.Tensor (ValidatedResult P ops) :=
  match validate P schedule η with
  | .error t => .error t
  | .ok input => .ok ⟨input, run P ops schedule input⟩

theorem runValidated_error (schedule : Schedule P)
    (η : InputBinding (K := K) (σ := σ)) (t : σ.Tensor)
    (h : runValidated P ops schedule η = .error t) : (η t).isSome ≠ P.input t := by
  unfold runValidated at h
  split at h
  · rename_i found
    cases h
    exact validate_error P schedule η t found
  · contradiction

#print axioms run_not_exhausted
#print axioms run_ranked_dichotomy
#print axioms result_model
#print axioms result_failure

end LeanNCD.Semantics.Program.Executor
