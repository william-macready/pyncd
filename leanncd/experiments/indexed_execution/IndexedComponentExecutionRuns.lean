import IndexedComponentExecutionFuel
import IndexedComponentExecutionTransport
import IndexedComponentExecutionPhase

namespace IndexedComponentExecution

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedOpenComposition
open IndexedComponentTransport
open IndexedComponentComposition

variable {src dst : Declarations Unit}
variable [DecidableEq src.Tensor] [DecidableEq dst.Tensor]

def SuccessfulOrFailed (run : Run src) : Prop :=
  (∃ state, run.outcome = .complete state) ∨
    (∃ tag state, run.outcome = .failed tag state)

/-- The complete endpoint is a shared snapshot, not an extra transition. -/
def PrefixRun (f : Embedding src dst) (rename : Nat → Nat)
    (R : State src → State dst → Prop) (source : Run src)
    (steps : List (Step dst)) (fuel : Nat) (target : Run dst) : Prop :=
  (∃ tag endpoint targetEndpoint,
    source.outcome = .failed tag endpoint ∧
    target.outcome = .failed (rename tag) targetEndpoint ∧
    R endpoint targetEndpoint ∧
    target.events = source.events.map (mapEvent f rename) ∧
    List.Forall₂ R source.states target.states) ∨
  (∃ endpoint cut remaining snapshots,
    source.outcome = .complete endpoint ∧
    R endpoint cut ∧
    List.Forall₂ R source.states (snapshots ++ [cut]) ∧
    remaining + snapshots.length = fuel ∧
    target.events = source.events.map (mapEvent f rename) ++
      (stepFuel steps remaining cut).events ∧
    target.states = snapshots ++ (stepFuel steps remaining cut).states ∧
    target.outcome = (stepFuel steps remaining cut).outcome)

omit [DecidableEq dst.Tensor] in
theorem complete_find_none (steps : List (Step dst)) (state : State dst)
    (done : complete steps state = true) :
    steps.find? (enabled state) = none := by
  apply List.find?_eq_none.mpr
  intro step member
  have finished := List.all_eq_true.mp done step member
  cases step with
  | write w =>
      simp only [enabled]
      have present : (producedValue state w.capability).isSome = true := finished
      cases h : producedValue state w.capability <;> simp_all
  | collect a caps =>
      simp only [enabled]
      have present : (state.available a).isSome = true := finished
      cases h : state.available a <;> simp_all

theorem stepFuel_prefix
    (f : Embedding src dst) (rename : Nat → Nat)
    (injective : Function.Injective rename) (ledgerPrefix : List (Nat × ℚ))
    (outside : ∀ row ∈ ledgerPrefix, ∀ cap, row.1 ≠ rename cap)
    (R : State src → State dst → Prop)
    (projects : ∀ s t, R s t → Projection f rename ledgerPrefix s t)
    (produce : ∀ s t, R s t → ∀ cap value,
      R { s with produced := s.produced ++ [(cap, value)] }
        { t with produced := t.produced ++ [(rename cap, value)] })
    (collect : ∀ s t, R s t → ∀ a value, s.available a = none →
      letI := Executor.addressEq (σ := src)
      letI := Executor.addressEq (σ := dst)
      R { s with available := Function.update s.available a (some value) }
        { t with available := Function.update t.available (f.address a) (some value) })
    (steps : List (Step src)) (leading suffix : List (Step dst))
    (leading_done : ∀ s t, R s t → complete leading t = true)
    (fuel extra : Nat)
    (source : State src) (target : State dst) (related : R source target)
    (terminal : SuccessfulOrFailed (stepFuel steps fuel source)) :
    PrefixRun f rename R (stepFuel steps fuel source)
      (leading ++ steps.map (mapStep f rename) ++ suffix) (fuel + extra)
      (stepFuel (leading ++ steps.map (mapStep f rename) ++ suffix)
        (fuel + extra) target) := by
  induction fuel generalizing source target with
  | zero =>
      by_cases hc : complete steps source = true
      · right
        have sourceEq : stepFuel steps 0 source = ⟨.complete source, [], [source]⟩ := by
          rw [stepFuel, if_pos hc]
        refine ⟨source, target, extra, [], ?_, related, ?_, by simp, ?_, by simp, ?_⟩
        · simp [sourceEq]
        · simpa [sourceEq] using List.Forall₂.cons related List.Forall₂.nil
        · simp [sourceEq]
        · simp
      · cases hs : steps.find? (enabled source) with
        | none => simp [SuccessfulOrFailed, stepFuel, hc, hs] at terminal
        | some step => simp [SuccessfulOrFailed, stepFuel, hc, hs] at terminal
  | succ fuel ih =>
      by_cases hc : complete steps source = true
      · right
        have sourceEq : stepFuel steps (fuel + 1) source =
            ⟨.complete source, [], [source]⟩ := by rw [stepFuel, if_pos hc]
        refine ⟨source, target, fuel + 1 + extra, [], ?_, related, ?_, by simp,
          ?_, by simp, rfl⟩
        · simp [sourceEq]
        · simpa [sourceEq] using List.Forall₂.cons related List.Forall₂.nil
        · simp [sourceEq]
      · have projected := projects source target related
        have hct : complete (leading ++ steps.map (mapStep f rename) ++ suffix)
            target = false := by
          simp only [complete, List.all_append]
          have hp := complete_projection f rename injective ledgerPrefix outside
            projected steps
          have hf : complete steps source = false := Bool.eq_false_iff.mpr hc
          change ((complete leading target &&
            complete (steps.map (mapStep f rename)) target) &&
            complete suffix target) = false
          rw [hp, hf]
          simp
        cases hs : steps.find? (enabled source) with
        | none => simp [SuccessfulOrFailed, stepFuel, hc, hs] at terminal
        | some step =>
          have localSelected := selected_projection f rename injective ledgerPrefix outside
            projected steps suffix step hs
          have selected :
              (leading ++ steps.map (mapStep f rename) ++ suffix).find?
                (enabled target) = some (mapStep f rename step) := by
            rw [List.append_assoc, List.find?_append,
              complete_find_none leading target (leading_done source target related)]
            exact localSelected
          cases step with
          | write w =>
            have he := evalReady_projection f rename ledgerPrefix projected w
            have sourceEq := stepFuel.eq_1 steps (fuel + 1) source
            simp only [hc, hs] at sourceEq
            have targetEq := stepFuel.eq_1
              (leading ++ steps.map (mapStep f rename) ++ suffix) (fuel + 1 + extra) target
            conv_rhs at targetEq =>
              simp only [hct, Bool.false_eq_true, ↓reduceIte, selected, Nat.succ_add,
                mapStep]
              rw [he]
              simp only [mapWriter]
            simp only [List.append_assoc] at targetEq
            cases hv : evalReady RationalReference.ops source.available w.body () with
            | notReady => simp [SuccessfulOrFailed, sourceEq, hv] at terminal
            | evaluated result =>
              cases result with
              | none =>
                left
                refine ⟨w.tag, source, target, ?_, ?_, related, ?_, ?_⟩
                · simp [sourceEq, hv]
                · simp [targetEq, hv]
                · simp [sourceEq, targetEq, hv, mapEvent]
                · simpa [sourceEq, targetEq, hv] using
                    (List.Forall₂.cons related List.Forall₂.nil)
              | some value =>
                have next := ih _ _ (produce source target related w.capability value)
                  (by simpa [SuccessfulOrFailed, sourceEq, hv] using terminal)
                rcases next with failed | cut
                · left
                  rcases failed with ⟨tag, endpoint, targetEndpoint, ho, ht, hr, events, states⟩
                  refine ⟨tag, endpoint, targetEndpoint, ?_, ?_, hr, ?_, ?_⟩
                  · simpa [sourceEq, hv] using ho
                  · simpa [targetEq, hv] using ht
                  · simpa [sourceEq, targetEq, hv, mapEvent] using congrArg
                      (List.cons (.produced (rename w.tag) (rename w.capability) value)) events
                  · simpa [sourceEq, targetEq, hv] using List.Forall₂.cons related states
                · right
                  rcases cut with ⟨endpoint, cut, remaining, snapshots, ho, hr,
                    states, count, events, snapshotsEq, outcome⟩
                  refine ⟨endpoint, cut, remaining, target :: snapshots, ?_, hr, ?_,
                    ?_, ?_, ?_, ?_⟩
                  · simpa [sourceEq, hv] using ho
                  · simpa [sourceEq, hv] using List.Forall₂.cons related states
                  · simp only [List.length_cons]; omega
                  · simpa [sourceEq, targetEq, hv, mapEvent] using congrArg
                      (List.cons (.produced (rename w.tag) (rename w.capability) value)) events
                  · simpa [targetEq, hv] using congrArg (List.cons target) snapshotsEq
                  · simpa [targetEq, hv] using outcome
          | collect a caps =>
            have he := collector_values_projection f rename injective ledgerPrefix outside
              projected caps
            have sourceEq := stepFuel.eq_1 steps (fuel + 1) source
            simp only [hc, hs] at sourceEq
            have targetEq := stepFuel.eq_1
              (leading ++ steps.map (mapStep f rename) ++ suffix) (fuel + 1 + extra) target
            conv_rhs at targetEq =>
              simp only [hct, Bool.false_eq_true, ↓reduceIte, selected, Nat.succ_add,
                mapStep, he]
            simp only [List.append_assoc] at targetEq
            cases hv : caps.mapM (producedValue source) with
            | none => simp [SuccessfulOrFailed, sourceEq, hv] at terminal
            | some values =>
              letI := Executor.addressEq (σ := src)
              letI := Executor.addressEq (σ := dst)
              have fresh : source.available a = none := by
                have eligible := List.find?_some hs
                simpa [enabled] using (Bool.and_eq_true_iff.mp eligible).1
              have next := ih _ _ (collect source target related a
                (values.foldl (· + ·) 0) fresh)
                (by simpa [SuccessfulOrFailed, sourceEq, hv] using terminal)
              rcases next with failed | cut
              · left
                rcases failed with ⟨tag, endpoint, targetEndpoint, ho, ht, hr, events, states⟩
                refine ⟨tag, endpoint, targetEndpoint, ?_, ?_, hr, ?_, ?_⟩
                · simpa [sourceEq, hv] using ho
                · simpa [targetEq, hv] using ht
                · simpa [sourceEq, targetEq, hv, mapEvent] using congrArg
                    (List.cons (.sealed (f.address a) (values.foldl (· + ·) 0))) events
                · simpa [sourceEq, targetEq, hv] using List.Forall₂.cons related states
              · right
                rcases cut with ⟨endpoint, cut, remaining, snapshots, ho, hr,
                  states, count, events, snapshotsEq, outcome⟩
                refine ⟨endpoint, cut, remaining, target :: snapshots, ?_, hr, ?_,
                  ?_, ?_, ?_, ?_⟩
                · simpa [sourceEq, hv] using ho
                · simpa [sourceEq, hv] using List.Forall₂.cons related states
                · simp only [List.length_cons]; omega
                · simpa [sourceEq, targetEq, hv, mapEvent] using congrArg
                    (List.cons (.sealed (f.address a) (values.foldl (· + ·) 0))) events
                · simpa [targetEq, hv] using
                    congrArg (List.cons target) snapshotsEq
                · simpa [targetEq, hv] using outcome

theorem stepFuel_states_length_le (steps : List (Step src)) (fuel : Nat)
    (state : State src) :
    (stepFuel steps fuel state).states.length ≤
      Correspondence.remaining steps state + 1 := by
  induction fuel generalizing state with
  | zero =>
      rw [stepFuel]
      split
      · simp
      · split <;> simp
  | succ fuel ih =>
      rw [stepFuel]
      split
      · simp
      · rename_i hc
        cases hs : steps.find? (enabled state) with
        | none => simp
        | some step =>
          have member := List.mem_of_find?_eq_some hs
          have eligible := List.find?_some hs
          cases step with
          | write w =>
            simp only
            cases hv : evalReady RationalReference.ops state.available w.body () with
            | notReady => simp
            | evaluated result =>
              cases result with
              | none => simp
              | some value =>
                have fresh : producedValue state w.capability = none := by
                  simpa [enabled] using (Bool.and_eq_true_iff.mp eligible).1
                have decreases := Correspondence.produce_decreases steps state w
                  member fresh value
                have bound := ih { state with
                  produced := state.produced ++ [(w.capability, value)] }
                simp only [List.length_cons]
                omega
          | collect a caps =>
            simp only
            cases hv : caps.mapM (producedValue state) with
            | none => simp
            | some values =>
              letI := Executor.addressEq (σ := src)
              have fresh : state.available a = none := by
                simpa [enabled] using (Bool.and_eq_true_iff.mp eligible).1
              have decreases := Correspondence.collect_decreases steps state a caps
                member fresh (values.foldl (· + ·) 0)
              have bound := ih { state with
                available := Function.update state.available a (some (values.foldl (· + ·) 0)) }
              simpa only [List.length_cons] using
                Nat.succ_le_succ (bound.trans (Nat.succ_le_of_lt decreases))

omit [DecidableEq dst.Tensor] in
theorem complete_extends (steps : List (Step dst)) {before after : State dst}
    (extension : Correspondence.Extends before after)
    (done : complete steps before = true) : complete steps after = true := by
  apply List.all_eq_true.mpr
  intro step member
  have finished := List.all_eq_true.mp done step member
  cases step with
  | write w =>
      obtain ⟨tail, ledger⟩ := extension.production
      cases found : before.produced.find? (fun row => row.1 == w.capability) with
      | none => simp [producedValue, found] at finished
      | some row => simp [producedValue, ledger, List.find?_append, found]
  | collect a caps =>
      obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp finished
      simp [extension.available a value present]

theorem stepFuel_complete_endpoint (steps : List (Step src)) (fuel : Nat)
    (state endpoint : State src)
    (finished : (stepFuel steps fuel state).outcome = .complete endpoint) :
    complete steps endpoint = true := by
  induction fuel generalizing state with
  | zero =>
      rw [stepFuel] at finished
      split at finished
      · cases finished; assumption
      · split at finished <;> cases finished
  | succ fuel ih =>
      rw [stepFuel] at finished
      split at finished
      · cases finished; assumption
      · cases hs : steps.find? (enabled state) with
        | none => simp [hs] at finished
        | some step =>
          simp only [hs] at finished
          cases step with
          | write w =>
            cases hv : evalReady RationalReference.ops state.available w.body () with
            | notReady => simp [hv] at finished
            | evaluated result =>
              cases result with
              | none => simp [hv] at finished
              | some value =>
                apply ih { state with produced := state.produced ++ [(w.capability, value)] }
                simpa only [hv] using finished
          | collect a caps =>
            cases hv : caps.mapM (producedValue state) with
            | none => simp [hv] at finished
            | some values =>
              letI := Executor.addressEq (σ := src)
              apply ih { state with
                available := Function.update state.available a (some (values.foldl (· + ·) 0)) }
              simpa only [hv] using finished

def RunProjection (f : Embedding src dst) (rename : Nat → Nat)
    (R : State src → State dst → Prop) (source : Run src) (target : Run dst) : Prop :=
  target.events = source.events.map (mapEvent f rename) ∧
  List.Forall₂ R source.states target.states ∧
  ((∃ endpoint targetEndpoint, source.outcome = .complete endpoint ∧
      target.outcome = .complete targetEndpoint ∧ R endpoint targetEndpoint) ∨
    (∃ tag endpoint targetEndpoint, source.outcome = .failed tag endpoint ∧
      target.outcome = .failed (rename tag) targetEndpoint ∧ R endpoint targetEndpoint))

omit [DecidableEq src.Tensor] in
theorem prefixRun_finish
    (f : Embedding src dst) (rename : Nat → Nat)
    (R : State src → State dst → Prop) (source : Run src)
    (steps : List (Step dst)) (fuel : Nat) (target : Run dst)
    (phase : PrefixRun f rename R source steps fuel target)
    (done : ∀ s t, source.outcome = .complete s → R s t → complete steps t = true) :
    RunProjection f rename R source target := by
  rcases phase with failed | cut
  · rcases failed with ⟨tag, endpoint, targetEndpoint, hs, ht, hr, events, states⟩
    exact ⟨events, states, .inr ⟨tag, endpoint, targetEndpoint, hs, ht, hr⟩⟩
  · rcases cut with ⟨endpoint, cut, remaining, snapshots, hs, hr, states,
      count, events, snapshotsEq, outcome⟩
    have tailEq : stepFuel steps remaining cut = ⟨.complete cut, [], [cut]⟩ := by
      rw [stepFuel, if_pos (done endpoint cut hs hr)]
    refine ⟨?_, ?_, .inl ⟨endpoint, cut, hs, ?_, hr⟩⟩
    · simpa only [tailEq, List.append_nil] using events
    · simpa only [snapshotsEq, tailEq] using states
    · simpa only [tailEq] using outcome

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB) (wire : Boundary A B)

theorem ranked_default_terminal (η : A.program.Input)
    (rank : A.program.RankCertificate) :
    SuccessfulOrFailed (runChecked A.contract A.fragment η.val) := by
  have related := (Correspondence.accepted_run_correspondence A.matched η).outcome
  have notBlocked := Correspondence.ranked_not_blocked A.matched η rank
  have notExhausted := (Correspondence.default_runs_not_exhausted A.matched η).1
  unfold SuccessfulOrFailed
  generalize houtcome : (runChecked A.contract A.fragment η.val).outcome = outcome
    at related ⊢
  generalize href : (Executor.run A.program RationalReference.ops A.schedule η).outcome =
    refOutcome at related
  cases related with
  | complete g c finished ledger relation => exact .inl ⟨g, rfl⟩
  | failed g c t o ledger relation => exact .inr ⟨_, g, rfl⟩
  | blocked g c missing observed blocked ledger relation diagnostics =>
      exact False.elim (notBlocked g missing houtcome)
  | exhausted g c ledger relation => exact False.elim (notExhausted g houtcome)

private theorem downstream_defined_ne_upstream (a : Address σB)
    (defined : B.program.input a.1 = false) (b : Address σA) :
    (downstream A B wire).address a ≠ (upstream A B).address b := by
  intro eq
  have tensors := congrArg Sigma.fst eq
  exact downstream_no_upstream_write A B wire ⟨a.1, defined⟩ b.1 tensors

theorem upstream_default_prefix (η : A.program.Input)
    (rank : A.program.RankCertificate) :
    PrefixRun (upstream A B) upstreamId (UpstreamState A B wire)
      (runChecked A.contract A.fragment η.val)
      (compose A B wire).graph.steps ((compose A B wire).graph.steps.length + 1)
      (runChecked (compose A B wire).contract (compose A B wire).fragment
        (liftInput A B wire η).val) := by
  have result := stepFuel_prefix (upstream A B) upstreamId upstreamId_injective []
    (by simp) (UpstreamState A B wire)
    (fun s t related => ⟨related.available, by
      simpa [mapLedger] using related.produced⟩)
    (fun s t related cap value => by
      refine ⟨related.available, related.downstream, ?_⟩
      simp [related.produced, List.map_append])
    (fun s t related a value _fresh => by
      letI := Executor.addressEq (σ := σA)
      letI := Executor.addressEq (σ := declarations A B)
      have projected : Projection (upstream A B) upstreamId [] s t :=
        ⟨related.available, by simpa [mapLedger] using related.produced⟩
      refine ⟨(projection_collect _ _ [] projected a value).available, ?_,
        related.produced⟩
      intro b hb
      simpa [Function.update_apply, downstream_defined_ne_upstream A B wire b hb a]
        using related.downstream b hb)
    A.graph.steps [] (B.graph.steps.map (mapStep (downstream A B wire) downstreamId))
    (by intros; rfl) (A.graph.steps.length + 1) B.graph.steps.length
    (initial η.val) (initial (liftInput A B wire η).val)
    (initial_upstream A B wire η)
    (by simpa only [← checked_eq_stepFuel A.matched η] using
      ranked_default_terminal A η rank)
  simpa only [checked_eq_stepFuel A.matched η,
    checked_eq_stepFuel (compose A B wire).matched (liftInput A B wire η),
    graph_steps_standalone, List.nil_append, List.length_append, List.length_map,
    Nat.add_assoc, Nat.add_comm 1 B.graph.steps.length] using result

theorem downstream_complete (completed : State σA)
    (upstreamDone : complete A.graph.steps completed = true)
    (s : State σB) (t : State (declarations A B))
    (related : DownstreamState A B wire completed s t) :
    complete (A.graph.steps.map (mapStep (upstream A B) upstreamId)) t = true := by
  let base : State (declarations A B) :=
    { t with produced := mapLedger upstreamId completed.produced }
  have projected : Projection (upstream A B) upstreamId [] completed base :=
    ⟨related.upstream, rfl⟩
  have done := complete_projection (upstream A B) upstreamId upstreamId_injective []
    (by simp) projected A.graph.steps
  apply complete_extends _ (before := base)
    ⟨⟨mapLedger downstreamId s.produced, related.produced⟩, fun _ _ h => h⟩
  exact done.trans upstreamDone

theorem downstream_default_prefix (completed : State σA)
    (upstreamDone : complete A.graph.steps completed = true)
    (ρA : Store RationalReference.Carrier σA)
    (full : ∀ a, completed.available a = some (ρA a))
    (cut : State (declarations A B))
    (atCut : DownstreamState A B wire completed
      (initial (boundaryInput A B wire ρA).val) cut)
    (rank : B.program.RankCertificate) (extra : Nat) :
    PrefixRun (downstream A B wire) downstreamId (DownstreamState A B wire completed)
      (runChecked B.contract B.fragment (boundaryInput A B wire ρA).val)
      (compose A B wire).graph.steps (B.graph.steps.length + 1 + extra)
      (stepFuel (compose A B wire).graph.steps
        (B.graph.steps.length + 1 + extra) cut) := by
  have projects : ∀ s t, DownstreamState A B wire completed s t →
      Projection (downstream A B wire) downstreamId
        (mapLedger upstreamId completed.produced) s t := by
    intro s t related
    exact ⟨related.available, related.produced⟩
  have leadingDone : ∀ s t, DownstreamState A B wire completed s t →
      complete (A.graph.steps.map (mapStep (upstream A B) upstreamId)) t = true := by
    exact downstream_complete A B wire completed upstreamDone
  have result := stepFuel_prefix (downstream A B wire) downstreamId
    downstreamId_injective (mapLedger upstreamId completed.produced)
    (by
      intro row member cap
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      exact ids_disjoint original.1 cap)
    (DownstreamState A B wire completed) projects
    (fun s t related cap value => by
      refine ⟨related.upstream, related.available, ?_⟩
      simp [related.produced, List.map_append, List.append_assoc])
    (fun s t related a value fresh => by
      letI := Executor.addressEq (σ := σB)
      letI := Executor.addressEq (σ := declarations A B)
      have projected := projection_collect _ _ _ (projects s t related) a value
      refine ⟨?_, projected.available, related.produced⟩
      intro b
      have ne : (upstream A B).address b ≠ (downstream A B wire).address a := by
        intro eq
        have h := related.available a
        rw [← eq, related.upstream, full, fresh] at h
        contradiction
      simpa [Function.update_apply, ne] using related.upstream b)
    B.graph.steps (A.graph.steps.map (mapStep (upstream A B) upstreamId)) []
    leadingDone (B.graph.steps.length + 1) extra
    (initial (boundaryInput A B wire ρA).val) cut atCut
    (by simpa only [← checked_eq_stepFuel B.matched (boundaryInput A B wire ρA)] using
      ranked_default_terminal B (boundaryInput A B wire ρA) rank)
  simpa only [checked_eq_stepFuel B.matched (boundaryInput A B wire ρA),
    graph_steps_standalone, List.append_nil] using result

theorem downstream_default_run (completed : State σA)
    (upstreamDone : complete A.graph.steps completed = true)
    (ρA : Store RationalReference.Carrier σA)
    (full : ∀ a, completed.available a = some (ρA a))
    (cut : State (declarations A B))
    (atCut : DownstreamState A B wire completed
      (initial (boundaryInput A B wire ρA).val) cut)
    (rank : B.program.RankCertificate) (extra : Nat) :
    RunProjection (downstream A B wire) downstreamId (DownstreamState A B wire completed)
      (runChecked B.contract B.fragment (boundaryInput A B wire ρA).val)
      (stepFuel (compose A B wire).graph.steps
        (B.graph.steps.length + 1 + extra) cut) := by
  apply prefixRun_finish _ _ _ _ _ _ _
    (downstream_default_prefix A B wire completed upstreamDone ρA full cut atCut rank extra)
  intro s t finished related
  have done : complete B.graph.steps s = true := by
    rw [checked_eq_stepFuel B.matched (boundaryInput A B wire ρA)] at finished
    exact stepFuel_complete_endpoint _ _ _ _ finished
  have projected : Projection (downstream A B wire) downstreamId
      (mapLedger upstreamId completed.produced) s t :=
    ⟨related.available, related.produced⟩
  have localDone := complete_projection (downstream A B wire) downstreamId
    downstreamId_injective (mapLedger upstreamId completed.produced)
    (by
      intro row member cap
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      exact ids_disjoint original.1 cap)
    projected B.graph.steps
  rw [graph_steps_standalone, complete, List.all_append]
  change (complete (A.graph.steps.map (mapStep (upstream A B) upstreamId)) t &&
    complete (B.graph.steps.map (mapStep (downstream A B wire) downstreamId)) t) = true
  rw [downstream_complete A B wire completed upstreamDone s t related, localDone, done]
  rfl

theorem compose_default_phases (η : A.program.Input)
    (rankA : A.program.RankCertificate) (rankB : B.program.RankCertificate) :
    let source := runChecked A.contract A.fragment η.val
    let composite := runChecked (compose A B wire).contract (compose A B wire).fragment
      (liftInput A B wire η).val
    (∃ tag endpoint targetEndpoint,
      source.outcome = .failed tag endpoint ∧
      composite.outcome = .failed (upstreamId tag) targetEndpoint ∧
      UpstreamState A B wire endpoint targetEndpoint ∧
      composite.events = source.events.map (mapEvent (upstream A B) upstreamId) ∧
      List.Forall₂ (UpstreamState A B wire) source.states composite.states) ∨
    (∃ (completed : State σA) (ρA : Store RationalReference.Carrier σA)
      (cut : State (declarations A B)) (remaining : Nat)
      (snapshots : List (State (declarations A B))),
      source.outcome = .complete completed ∧
      (∀ a, completed.available a = some (ρA a)) ∧
      UpstreamState A B wire completed cut ∧
      DownstreamState A B wire completed
        (initial (boundaryInput A B wire ρA).val) cut ∧
      List.Forall₂ (UpstreamState A B wire) source.states (snapshots ++ [cut]) ∧
      remaining + snapshots.length = (compose A B wire).graph.steps.length + 1 ∧
      snapshots.length ≤ A.graph.steps.length ∧
      B.graph.steps.length + 1 ≤ remaining ∧
      RunProjection (downstream A B wire) downstreamId (DownstreamState A B wire completed)
        (runChecked B.contract B.fragment (boundaryInput A B wire ρA).val)
        (stepFuel (compose A B wire).graph.steps remaining cut) ∧
      composite.events = source.events.map (mapEvent (upstream A B) upstreamId) ++
        (stepFuel (compose A B wire).graph.steps remaining cut).events ∧
      composite.states = snapshots ++
        (stepFuel (compose A B wire).graph.steps remaining cut).states ∧
      composite.outcome = (stepFuel (compose A B wire).graph.steps remaining cut).outcome) := by
  dsimp only
  rcases upstream_default_prefix A B wire η rankA with failed | cut
  · exact .inl failed
  · right
    rcases cut with ⟨completed, cut, remaining, snapshots, finished, related, states,
      count, events, snapshotsEq, outcome⟩
    obtain ⟨c, complete, full, _⟩ :=
      Correspondence.completed_model A.matched η completed finished
    let ρA := A.program.finalStore c complete
    have atCut := downstream_at_cut A B wire related ρA full
    have upstreamDone : IndexedOpenComposition.complete A.graph.steps completed = true := by
      rw [checked_eq_stepFuel A.matched η] at finished
      exact stepFuel_complete_endpoint _ _ _ _ finished
    have lengths := states.length_eq
    simp only [List.length_append, List.length_singleton] at lengths
    have bound := stepFuel_states_length_le A.graph.steps (A.graph.steps.length + 1)
      (initial η.val)
    rw [← checked_eq_stepFuel A.matched η] at bound
    have initialBound : Correspondence.remaining A.graph.steps (initial η.val) ≤
        A.graph.steps.length := List.countP_le_length
    have actionBound : snapshots.length ≤ A.graph.steps.length := by omega
    have budget : (compose A B wire).graph.steps.length =
        A.graph.steps.length + B.graph.steps.length := by
      rw [graph_steps_standalone, List.length_append, List.length_map, List.length_map]
    have enough : B.graph.steps.length + 1 ≤ remaining := by omega
    have suffixRun := downstream_default_run A B wire completed upstreamDone ρA full
      cut atCut rankB (remaining - (B.graph.steps.length + 1))
    have fuelEq : B.graph.steps.length + 1 +
        (remaining - (B.graph.steps.length + 1)) = remaining := by omega
    rw [fuelEq] at suffixRun
    exact ⟨completed, ρA, cut, remaining, snapshots, finished, full, related, atCut,
      states, count, actionBound, enough, suffixRun, events, snapshotsEq, outcome⟩

end IndexedComponentExecution
