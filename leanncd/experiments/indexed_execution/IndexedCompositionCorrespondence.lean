import IndexedCompositionSelection
import IndexedCompositionPublication
import IndexedCompositionTerminal
import IndexedCompositionDiagnostics

namespace IndexedOpenComposition.Correspondence

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {schedule : Schedule P} {contract : Contract σ} {fragment : Fragment σ}
variable {graph : Closed σ}

-- Undefinedness contributes an event but not a second failed-state snapshot.
def referenceSnapshots (c : P.Running) :
    List (Executor.Event P) → List P.Running
  | [] => [c]
  | .contribution t o value :: events =>
      c :: referenceSnapshots (Executor.consume P c t o value) events
  | .publication t p _ :: events =>
      c :: referenceSnapshots (Executor.publish P c t p) events
  | .undefined _ _ :: _ => [c]

inductive OutcomeRelated
    (M : SourceContractMatch P schedule contract fragment graph) :
    IndexedOpenComposition.Outcome σ → Executor.Outcome P RationalReference.ops → Prop
  | complete (g : State σ) (c : P.Running) (finished : P.Complete c)
      (ledger : LedgerInvariant M g) (related : Relation M g c) :
      OutcomeRelated M (.complete g) (.complete c finished)
  | failed (g : State σ) (c : P.Running) (t : P.Defined) (o : P.Occurrence t)
      (ledger : LedgerInvariant M g) (related : Relation M g c) :
      OutcomeRelated M (.failed (M.tag ⟨t, o⟩) g) (.failed t o c)
  | blocked (g : State σ) (c : P.Running)
      (missing : List (Nat × List (Address σ))) (observed : List (Observation P))
      (blocked : P.Blocked RationalReference.ops c)
      (ledger : LedgerInvariant M g) (related : Relation M g c)
      (diagnostics : missing = observed.map (observation M)) :
      OutcomeRelated M (.blocked g missing) (.blocked c observed blocked)
  | exhausted (g : State σ) (c : P.Running)
      (ledger : LedgerInvariant M g) (related : Relation M g c) :
      OutcomeRelated M (.exhausted g) (.exhausted c)

structure ExecutionCorrespondence
    (M : SourceContractMatch P schedule contract fragment graph)
    (candidate : Run σ) (start : P.Running)
    (reference : Result P RationalReference.ops (.running start)) : Prop where
  outcome : OutcomeRelated M candidate.outcome reference.outcome
  events : candidate.events = reference.events.map M.event
  states : List.Forall₂
    (fun g c => LedgerInvariant M g ∧ Relation M g c)
    candidate.states (referenceSnapshots start reference.events)

private theorem bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) :
    a = b := by
  cases a <;> cases b <;> simp_all

theorem eligible_key
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c)
    (fibers : ∀ t (p : Coord (σ.signature t.val).axes),
      CollectorFiber M t p (collectorCapabilities contract ⟨t.val, p⟩))
    (key : Key P) :
    enabled g (M.step key) =
      (attempt P RationalReference.ops c key).isSome := by
  cases key with
  | occurrence t o =>
      apply bool_eq_of_true_iff
      simpa only [SourceContractMatch.step, keyStep, SourceContractMatch.writer] using
        write_enabled_iff_attempt M R t o
  | publication t p =>
      apply bool_eq_of_true_iff
      simpa only [SourceContractMatch.step, keyStep] using
        collector_enabled_iff_attempt M R t p
          (collectorCapabilities contract ⟨t.val, p⟩) (fibers t p)

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
private theorem attempt_contribution
    (c : P.Running) (t : P.Defined) (o : P.Occurrence t) (v : ℚ)
    (pending : o ∈ c.pending t)
    (evaluated : evalReady RationalReference.ops c.published
      (P.body t o.1) o.2 = .evaluated (some v)) :
    ∃ move : Move P RationalReference.ops c,
      attempt P RationalReference.ops c (.occurrence t o) = some move ∧
        move.event = .contribution t o v := by
  refine ⟨⟨.contribution t o v, pending, evaluated⟩, ?_, rfl⟩
  simp only [attempt, dif_pos pending]
  split
  · rename_i h
    rw [evaluated] at h
    cases h
  · rename_i h
    rw [evaluated] at h
    cases h
  · rename_i value h
    rw [evaluated] at h
    cases h
    rfl

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
private theorem attempt_publication
    (c : P.Running) (t : P.Defined)
    (p : Coord (σ.signature t.val).axes)
    (unpublished : c.published ⟨t.val, p⟩ = none)
    (finished : P.FiberEmpty c t p) :
    ∃ move : Move P RationalReference.ops c,
      attempt P RationalReference.ops c (.publication t p) = some move ∧
        move.event = .publication t p (c.accumulators t p) := by
  refine ⟨⟨.publication t p (c.accumulators t p),
    unpublished, finished, rfl⟩, ?_, rfl⟩
  simp only [attempt]
  split <;> simp_all

private theorem selection_pair
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c)
    (fibers : ∀ t (p : Coord (σ.signature t.val).axes),
      CollectorFiber M t p (collectorCapabilities contract ⟨t.val, p⟩)) :
    (graph.steps.find? (enabled g) = none ∧
      select P RationalReference.ops schedule c = none) ∨
    ∃ (key : Key P) (move : Move P RationalReference.ops c),
      graph.steps.find? (enabled g) = some (M.step key) ∧
      select P RationalReference.ops schedule c = some move ∧
      attempt P RationalReference.ops c key = some move := by
  have hg := first_eligible_agrees M g c (eligible_key M R fibers)
  have hr := scan_first_attempt c schedule.keys
  cases hchoice : schedule.keys.find?
      (fun key => (attempt P RationalReference.ops c key).isSome) with
  | none =>
      exact .inl ⟨by simpa [hchoice] using hg, by simpa [select, hchoice] using hr⟩
  | some key =>
      have ready := List.find?_some hchoice
      cases hmove : attempt P RationalReference.ops c key with
      | none => simp [hmove] at ready
      | some move =>
          exact .inr ⟨key, move,
            by simpa [hchoice] using hg,
            by simpa [select, hchoice, hmove] using hr, hmove⟩

theorem runFuel_zero
    (M : SourceContractMatch P schedule contract fragment graph)
    (fibers : ∀ t (p : Coord (σ.signature t.val).axes),
      CollectorFiber M t p (collectorCapabilities contract ⟨t.val, p⟩))
    (g : State σ) (c : P.Running)
    (I : LedgerInvariant M g) (R : Relation M g c)
    (inputs : InputsAvailable P g) :
    ExecutionCorrespondence M (stepFuel graph.steps 0 g) c
      (runFuel P RationalReference.ops schedule 0 (.running c)) := by
  by_cases hc : P.Complete c
  · have hg := (complete_agrees M R inputs).mpr hc
    simp only [stepFuel, hg, ↓reduceIte, runFuel, dif_pos hc]
    exact ⟨.complete g c hc I R, rfl, .cons ⟨I, R⟩ .nil⟩
  · have hg : complete graph.steps g = false := by
      cases h : complete graph.steps g with
      | false => rfl
      | true => exact False.elim (hc ((complete_agrees M R inputs).mp h))
    rcases selection_pair M R fibers with ⟨noneGraph, noneRef⟩ |
      ⟨key, move, someGraph, someRef, _⟩
    · have blocked : P.Blocked RationalReference.ops c :=
        ⟨hc, (select_none_iff P RationalReference.ops schedule c).mp noneRef⟩
      have candidateEq : stepFuel graph.steps 0 g =
          ⟨.blocked g (missingReads graph.steps g), [], [g]⟩ := by
        simp [stepFuel, hg, noneGraph]
      have referenceEq : runFuel P RationalReference.ops schedule 0 (.running c) =
          ⟨.blocked c (observations P RationalReference.ops schedule c) blocked,
            [], .nil _⟩ := by
        conv_lhs => unfold runFuel
        simp only [dif_neg hc]
        split
        · rfl
        · rename_i move selected
          rw [noneRef] at selected
          contradiction
      rw [candidateEq, referenceEq]
      exact ⟨.blocked g c _ _ blocked I R (missingReads_agrees M R),
        rfl, .cons ⟨I, R⟩ .nil⟩
    · have candidateEq : stepFuel graph.steps 0 g =
          ⟨.exhausted g, [], [g]⟩ := by
        simp [stepFuel, hg, someGraph]
      have referenceEq : runFuel P RationalReference.ops schedule 0 (.running c) =
          ⟨.exhausted c, [], .nil _⟩ := by
        unfold runFuel
        simp only [dif_neg hc]
        split
        · rename_i selected
          rw [someRef] at selected
          contradiction
        · rfl
      rw [candidateEq, referenceEq]
      exact ⟨.exhausted g c I R, rfl, .cons ⟨I, R⟩ .nil⟩

private theorem prepend_contribution
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (c : P.Running) (I : LedgerInvariant M g) (R : Relation M g c)
    (t : P.Defined) (o : P.Occurrence t) (v : ℚ)
    (pending : o ∈ c.pending t)
    (evaluated : evalReady RationalReference.ops c.published
      (P.body t o.1) o.2 = .evaluated (some v))
    (candidate : Run σ)
    (reference : Result P RationalReference.ops
      (.running (Executor.consume P c t o v)))
    (tail : ExecutionCorrespondence M candidate (Executor.consume P c t o v) reference) :
    ExecutionCorrespondence M
      ⟨candidate.outcome, .produced (M.tag ⟨t, o⟩) (M.capability ⟨t, o⟩) v ::
        candidate.events, g :: candidate.states⟩ c
      ⟨reference.outcome, .contribution t o v :: reference.events,
        .cons ⟨pending, evaluated⟩ reference.execution⟩ := by
  refine ⟨tail.outcome, ?_, ?_⟩
  · simp [tail.events, SourceContractMatch.event]
  · exact .cons ⟨I, R⟩ tail.states

private theorem prepend_publication
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (c : P.Running) (I : LedgerInvariant M g) (R : Relation M g c)
    (t : P.Defined) (p : Coord (σ.signature t.val).axes) (v : ℚ)
    (unpublished : c.published ⟨t.val, p⟩ = none)
    (finished : P.FiberEmpty c t p) (agree : v = c.accumulators t p)
    (candidate : Run σ)
    (reference : Result P RationalReference.ops
      (.running (Executor.publish P c t p)))
    (tail : ExecutionCorrespondence M candidate (Executor.publish P c t p) reference) :
    ExecutionCorrespondence M
      ⟨candidate.outcome, .sealed ⟨t.val, p⟩ v :: candidate.events,
        g :: candidate.states⟩ c
      ⟨reference.outcome, .publication t p v :: reference.events,
        .cons ⟨unpublished, finished, agree⟩ reference.execution⟩ := by
  refine ⟨tail.outcome, ?_, ?_⟩
  · simp [tail.events, SourceContractMatch.event]
  · exact .cons ⟨I, R⟩ tail.states

private theorem prepend_undefined
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (c : P.Running) (I : LedgerInvariant M g) (R : Relation M g c)
    (t : P.Defined) (o : P.Occurrence t)
    (pending : o ∈ c.pending t)
    (evaluated : evalReady RationalReference.ops c.published
      (P.body t o.1) o.2 = .evaluated none) :
    ExecutionCorrespondence M
      ⟨.failed (M.tag ⟨t, o⟩) g, [.undefined (M.tag ⟨t, o⟩)], [g]⟩ c
      ⟨.failed t o c, [.undefined t o],
        .cons ⟨pending, evaluated⟩ (.nil _)⟩ := by
  exact ⟨.failed g c t o I R, rfl, .cons ⟨I, R⟩ .nil⟩

omit [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
private theorem move_eq_of_event
    (c : P.Running) (move : Move P RationalReference.ops c)
    (event : Executor.Event P) (legal : event.Legal P RationalReference.ops c)
    (h : move.event = event) : move = ⟨event, legal⟩ := by
  cases move with
  | mk actual proof =>
      cases h
      rfl

omit [Fintype σ.Tensor] in
private theorem reference_selected_succ (c : P.Running)
    (hc : ¬P.Complete c) (move : Move P RationalReference.ops c)
    (selected : select P RationalReference.ops schedule c = some move) (fuel : Nat) :
    runFuel P RationalReference.ops schedule (fuel + 1) (.running c) =
      let tail := runFuel P RationalReference.ops schedule fuel (move.event.effect P c)
      ⟨tail.outcome, move.event :: tail.events, .cons move.legal tail.execution⟩ := by
  conv_lhs => unfold runFuel
  simp only [dif_neg hc]
  split
  · rename_i h
    rw [selected] at h
    contradiction
  · rename_i actual h
    have same : actual = move := Option.some.inj (h.symm.trans selected)
    subst actual
    rfl

omit [Fintype σ.Tensor] in
private theorem candidate_write_succ (steps : List (Step σ))
    (g : State σ) (fuel : Nat) (w : Writer σ) (v : ℚ)
    (incomplete : complete steps g = false)
    (selected : steps.find? (enabled g) = some (.write w))
    (evaluated : evalReady RationalReference.ops g.available w.body () =
      .evaluated (some v)) :
    stepFuel steps (fuel + 1) g =
      let next := { g with produced := g.produced ++ [(w.capability, v)] }
      let tail := stepFuel steps fuel next
      ⟨tail.outcome, .produced w.tag w.capability v :: tail.events,
        g :: tail.states⟩ := by
  conv_lhs => unfold stepFuel
  simp [incomplete, selected, evaluated]

omit [Fintype σ.Tensor] in
private theorem candidate_undefined_succ (steps : List (Step σ))
    (g : State σ) (fuel : Nat) (w : Writer σ)
    (incomplete : complete steps g = false)
    (selected : steps.find? (enabled g) = some (.write w))
    (evaluated : evalReady RationalReference.ops g.available w.body () =
      .evaluated none) :
    stepFuel steps (fuel + 1) g =
      ⟨.failed w.tag g, [.undefined w.tag], [g]⟩ := by
  conv_lhs => unfold stepFuel
  simp [incomplete, selected, evaluated]

omit [Fintype σ.Tensor] in
private theorem candidate_collect_succ (steps : List (Step σ))
    (g : State σ) (fuel : Nat) (a : Address σ) (caps : List Nat)
    (incomplete : complete steps g = false)
    (selected : steps.find? (enabled g) = some (.collect a caps))
    (values : List ℚ) (mapped : caps.mapM (producedValue g) = some values) :
    stepFuel steps (fuel + 1) g =
      let value := values.foldl (· + ·) (0 : ℚ)
      letI := Program.Executor.addressEq (σ := σ)
      let next := { g with available := Function.update g.available a (some value) }
      let tail := stepFuel steps fuel next
      ⟨tail.outcome, .sealed a value :: tail.events, g :: tail.states⟩ := by
  conv_lhs => unfold stepFuel
  simp [incomplete, selected, mapped]
  exact ⟨rfl, rfl, rfl⟩

private theorem selected_occurrence_pending
    (M : SourceContractMatch P schedule contract fragment graph)
    (R : Relation M g c) (t : P.Defined) (o : P.Occurrence t)
    (selected : graph.steps.find? (enabled g) =
      some (M.step (.occurrence t o))) : o ∈ c.pending t := by
  have eligible := List.find?_some selected
  have fresh : producedValue g (M.capability ⟨t, o⟩) = none := by
    have h := (Bool.and_eq_true_iff.mp eligible).1
    simpa only [SourceContractMatch.step, keyStep, enabled,
      SourceContractMatch.capability, SourceContractMatch.writer,
      Option.isNone_iff_eq_none] using h
  exact (R.pending t o).mpr fresh

private theorem selected_collector_conditions
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (t : P.Defined)
    (p : Coord (σ.signature t.val).axes)
    (selected : graph.steps.find? (enabled g) =
      some (M.step (.publication t p))) :
    g.available ⟨t.val, p⟩ = none ∧
      (collectorCapabilities contract ⟨t.val, p⟩).all
        (fun cap => (producedValue g cap).isSome) = true := by
  have eligible := List.find?_some selected
  have h : (g.available ⟨t.val, p⟩).isNone = true ∧
      (collectorCapabilities contract ⟨t.val, p⟩).all
        (fun cap => (producedValue g cap).isSome) = true := by
    simpa only [SourceContractMatch.step, keyStep, enabled,
      Bool.and_eq_true_iff] using eligible
  exact ⟨by simpa using h.1, h.2⟩

theorem runFuel_correspondence
    (M : SourceContractMatch P schedule contract fragment graph)
    (capInjective : Function.Injective M.capability)
    (fibers : ∀ t (p : Coord (σ.signature t.val).axes),
      CollectorFiber M t p (collectorCapabilities contract ⟨t.val, p⟩))
    (fuel : Nat) (g : State σ) (c : P.Running)
    (I : LedgerInvariant M g) (R : Relation M g c)
    (inputs : InputsAvailable P g) :
    ExecutionCorrespondence M (stepFuel graph.steps fuel g) c
      (runFuel P RationalReference.ops schedule fuel (.running c)) := by
  induction fuel generalizing g c with
  | zero => exact runFuel_zero M fibers g c I R inputs
  | succ fuel ih =>
      by_cases hc : P.Complete c
      · have hg := (complete_agrees M R inputs).mpr hc
        have candidateEq : stepFuel graph.steps (fuel + 1) g =
            stepFuel graph.steps 0 g := by
          simp [stepFuel, hg]
        have referenceEq :
            runFuel P RationalReference.ops schedule (fuel + 1) (.running c) =
              runFuel P RationalReference.ops schedule 0 (.running c) := by
          simp [runFuel, hc]
        rw [candidateEq, referenceEq]
        exact runFuel_zero M fibers g c I R inputs
      · have hg : complete graph.steps g = false := by
          cases h : complete graph.steps g with
          | false => rfl
          | true => exact False.elim (hc ((complete_agrees M R inputs).mp h))
        rcases selection_pair M R fibers with ⟨noneGraph, noneRef⟩ |
          ⟨key, move, someGraph, someRef, attempted⟩
        · have candidateEq : stepFuel graph.steps (fuel + 1) g =
              stepFuel graph.steps 0 g := by
            simp [stepFuel, hg, noneGraph]
          have blocked : P.Blocked RationalReference.ops c :=
            ⟨hc, (select_none_iff P RationalReference.ops schedule c).mp noneRef⟩
          have referenceEq (n : Nat) :
              runFuel P RationalReference.ops schedule n (.running c) =
                ⟨.blocked c (observations P RationalReference.ops schedule c) blocked,
                  [], .nil _⟩ := by
            conv_lhs => unfold runFuel
            simp only [dif_neg hc]
            split
            · rfl
            · rename_i selectedMove selected
              rw [noneRef] at selected
              contradiction
          rw [candidateEq, referenceEq (fuel + 1)]
          have base := runFuel_zero M fibers g c I R inputs
          rw [referenceEq 0] at base
          exact base
        · cases key with
          | occurrence t o =>
              have chosen : graph.steps.find? (enabled g) =
                  some (.write (M.writer ⟨t, o⟩)) := by
                simpa only [SourceContractMatch.step, keyStep,
                  SourceContractMatch.writer] using someGraph
              have pending := selected_occurrence_pending M R t o someGraph
              cases evaluated : evalReady RationalReference.ops g.available
                  (M.writer ⟨t, o⟩).body () with
              | notReady =>
                  have ready : evalReady RationalReference.ops c.published
                      (P.body t o.1) o.2 ≠ .notReady := by
                    have eligible := List.find?_some chosen
                    have reads := (Bool.and_eq_true_iff.mp eligible).2
                    exact (writer_reads_ready M R t o).mp reads
                  have source := writer_eval M R t o
                  rw [evaluated] at source
                  exact False.elim (ready source.symm)
              | evaluated value =>
                  cases value with
                  | none =>
                      have source : evalReady RationalReference.ops c.published
                          (P.body t o.1) o.2 = .evaluated none := by
                        rw [← writer_eval M R t o]
                        exact evaluated
                      obtain ⟨expected, found, event⟩ :=
                        undefined_attempt t o c pending source
                      have same : move = expected :=
                        Option.some.inj (attempted.symm.trans found)
                      have eventEq : move.event = .undefined t o := same ▸ event
                      have moveEq := move_eq_of_event c move (.undefined t o)
                        ⟨pending, source⟩ eventEq
                      have candidateEq :=
                        candidate_undefined_succ graph.steps g fuel
                          (M.writer ⟨t, o⟩) hg chosen evaluated
                      have referenceEq := reference_selected_succ c hc move someRef fuel
                      rw [moveEq] at referenceEq
                      rw [candidateEq, referenceEq]
                      simpa [runFuel, Executor.Event.effect] using
                        prepend_undefined M g c I R t o pending source
                  | some v =>
                      have source : evalReady RationalReference.ops c.published
                          (P.body t o.1) o.2 = .evaluated (some v) := by
                        rw [← writer_eval M R t o]
                        exact evaluated
                      obtain ⟨expected, found, event⟩ :=
                        attempt_contribution c t o v pending source
                      have same : move = expected :=
                        Option.some.inj (attempted.symm.trans found)
                      have eventEq : move.event = .contribution t o v := same ▸ event
                      have moveEq := move_eq_of_event c move (.contribution t o v)
                        ⟨pending, source⟩ eventEq
                      obtain ⟨_, nextLedger, nextRelation⟩ :=
                        successful_contribution M R I capInjective t o v pending source
                      rw [← consume_agrees P c t o v] at nextRelation
                      have nextInputs : InputsAvailable P
                          (appendContribution M g ⟨t, o⟩ v) :=
                        InputsAvailable.extends inputs (by
                          simpa only [appendContribution] using
                            produce_extends g (M.capability ⟨t, o⟩) v)
                      have tail := ih (appendContribution M g ⟨t, o⟩ v)
                        (Executor.consume P c t o v) nextLedger nextRelation nextInputs
                      have candidateEq :=
                        candidate_write_succ graph.steps g fuel
                          (M.writer ⟨t, o⟩) v hg chosen evaluated
                      have referenceEq := reference_selected_succ c hc move someRef fuel
                      rw [moveEq] at referenceEq
                      rw [candidateEq, referenceEq]
                      simpa only [appendContribution, Executor.Event.effect] using
                        prepend_contribution M g c I R t o v pending source
                          (stepFuel graph.steps fuel (appendContribution M g ⟨t, o⟩ v))
                          (runFuel P RationalReference.ops schedule fuel
                            (.running (Executor.consume P c t o v))) tail
          | publication t p =>
              let caps := collectorCapabilities contract ⟨t.val, p⟩
              have chosen : graph.steps.find? (enabled g) =
                  some (.collect ⟨t.val, p⟩ caps) := by
                simpa only [SourceContractMatch.step, keyStep, caps] using someGraph
              obtain ⟨fresh, all⟩ :=
                selected_collector_conditions M g t p someGraph
              have unpublished : c.published ⟨t.val, p⟩ = none := by
                rw [← R.published]
                exact fresh
              have finished := (collector_all_produced_iff_fiberEmpty M R t p
                caps (fibers t p)).mp all
              obtain ⟨values, mapped⟩ := produced_mapM_some g caps all
              let value := values.foldl (· + ·) (0 : ℚ)
              have published :=
                successful_publication M R I capInjective t p caps
                  (fibers t p) unpublished all values mapped
              obtain ⟨agree, nextLedger, nextRelation, extension⟩ := published
              rw [← publish_agrees P c t p] at nextRelation
              have nextInputs : InputsAvailable P
                  (publishGraph g ⟨t.val, p⟩ value) :=
                InputsAvailable.extends inputs extension
              obtain ⟨expected, found, event⟩ :=
                attempt_publication c t p unpublished finished
              have same : move = expected :=
                Option.some.inj (attempted.symm.trans found)
              have eventEq : move.event = .publication t p value := by
                have h : move.event = .publication t p (c.accumulators t p) :=
                  same ▸ event
                rw [← agree] at h
                exact h
              have moveEq := move_eq_of_event c move (.publication t p value)
                ⟨unpublished, finished, agree⟩ eventEq
              have tail := ih (publishGraph g ⟨t.val, p⟩ value)
                (Executor.publish P c t p) nextLedger nextRelation nextInputs
              have candidateEq :=
                candidate_collect_succ graph.steps g fuel ⟨t.val, p⟩ caps
                  hg chosen values mapped
              have referenceEq := reference_selected_succ c hc move someRef fuel
              rw [moveEq] at referenceEq
              rw [candidateEq, referenceEq]
              simpa only [publishGraph, Executor.Event.effect, value] using
                prepend_publication M g c I R t p value unpublished finished agree
                  (stepFuel graph.steps fuel (publishGraph g ⟨t.val, p⟩ value))
                  (runFuel P RationalReference.ops schedule fuel
                    (.running (Executor.publish P c t p))) tail

end IndexedOpenComposition.Correspondence
