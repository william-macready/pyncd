import IndexedComponentExecutionRuns
import IndexedOperationalReassociation

namespace IndexedOperationalRuns

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedComponentTransport IndexedComponentComposition
open IndexedOpenComposition IndexedComponentExecution

variable {src dst : Declarations Unit}

abbrev StateRelated (f : Embedding src dst) (rename : Nat → Nat) :=
  Projection f rename []

inductive StepRelated (f : Embedding src dst) (rename : Nat → Nat) :
    Step src → Step dst → Prop
  | write (w : Writer src) (v : Writer dst)
      (tag : v.tag = rename w.tag)
      (capability : v.capability = rename w.capability)
      (destination : v.destination = f.address w.destination)
      (reads : v.reads = w.reads.map f.address)
      (evaluate : ∀ s t, StateRelated f rename s t →
        evalReady RationalReference.ops t.available v.body () =
          evalReady RationalReference.ops s.available w.body ()) :
      StepRelated f rename (.write w) (.write v)
  | collect (a : Address src) (caps : List Nat) :
      StepRelated f rename (.collect a caps)
        (.collect (f.address a) (caps.map rename))

inductive OutcomeRelated (f : Embedding src dst) (rename : Nat → Nat) :
    Outcome src → Outcome dst → Prop
  | complete {s t} : StateRelated f rename s t →
      OutcomeRelated f rename (.complete s) (.complete t)
  | failed {s t} (tag) : StateRelated f rename s t →
      OutcomeRelated f rename (.failed tag s) (.failed (rename tag) t)
  | blocked {s t} (missing) : StateRelated f rename s t →
      OutcomeRelated f rename (.blocked s missing)
        (.blocked t (missing.map fun row => (rename row.1, row.2.map f.address)))
  | exhausted {s t} : StateRelated f rename s t →
      OutcomeRelated f rename (.exhausted s) (.exhausted t)
  | contractMismatch {s t} (tag) : StateRelated f rename s t →
      OutcomeRelated f rename (.contractMismatch tag s) (.contractMismatch (rename tag) t)
  | collectorMismatch {s t} (a) : StateRelated f rename s t →
      OutcomeRelated f rename (.collectorMismatch a s) (.collectorMismatch (f.address a) t)

structure RunRelated (f : Embedding src dst) (rename : Nat → Nat)
    (source : Run src) (target : Run dst) : Prop where
  events : target.events = source.events.map (mapEvent f rename)
  states : List.Forall₂ (StateRelated f rename) source.states target.states
  outcome : OutcomeRelated f rename source.outcome target.outcome

theorem step_enabled (f : Embedding src dst) (rename : Nat → Nat)
    (injective : Function.Injective rename) {s : State src} {t : State dst}
    (states : StateRelated f rename s t) {a b} (steps : StepRelated f rename a b) :
    enabled t b = enabled s a := by
  have hp := producedValue_projection f rename injective [] (by simp) states
  cases steps with
  | write w v ht hc hd hr he =>
      simp [enabled, hc, hr, hp, states.available, List.all_map, Function.comp_def]
  | collect a caps =>
      simp [enabled, hp, states.available, List.all_map, Function.comp_def]

theorem steps_complete (f : Embedding src dst) (rename : Nat → Nat)
    (injective : Function.Injective rename) {s : State src} {t : State dst}
    (states : StateRelated f rename s t) {as bs}
    (steps : List.Forall₂ (StepRelated f rename) as bs) :
    complete bs t = complete as s := by
  have hp := producedValue_projection f rename injective [] (by simp) states
  induction steps with
  | nil => rfl
  | @cons a b as bs hab htail ih =>
      cases hab <;> simp_all [complete, states.available]

theorem steps_selected (f : Embedding src dst) (rename : Nat → Nat)
    (injective : Function.Injective rename) {s : State src} {t : State dst}
    (states : StateRelated f rename s t) {as bs}
    (steps : List.Forall₂ (StepRelated f rename) as bs) :
    Option.Rel (StepRelated f rename)
      (as.find? (enabled s)) (bs.find? (enabled t)) := by
  induction steps with
  | nil => exact .none
  | cons hab htail ih =>
      have he := step_enabled f rename injective states hab
      simp only [List.find?_cons, he]
      split
      · exact .some hab
      · exact ih

theorem steps_missing (f : Embedding src dst) (rename : Nat → Nat)
    (injective : Function.Injective rename) {s : State src} {t : State dst}
    (states : StateRelated f rename s t) {as bs}
    (steps : List.Forall₂ (StepRelated f rename) as bs) :
    missingReads bs t =
      (missingReads as s).map (fun row => (rename row.1, row.2.map f.address)) := by
  have hp := producedValue_projection f rename injective [] (by simp) states
  induction steps with
  | nil => rfl
  | cons hab htail ih =>
      cases hab with
      | write w v ht hc hd hr he =>
          simp only [missingReads, List.filterMap_cons] at ih ⊢
          rw [ht, hc, hr, hp]
          simp only [List.filter_map, Function.comp_def, states.available]
          cases producedValue s w.capability <;> simp_all
      | collect a caps =>
          simpa only [missingReads, List.filterMap_cons] using ih

section Fuel

variable [DecidableEq src.Tensor] [DecidableEq dst.Tensor]

theorem stepFuel_transport (f : Embedding src dst) (rename : Nat → Nat)
    (injective : Function.Injective rename) {as bs}
    (steps : List.Forall₂ (StepRelated f rename) as bs)
    (fuel : Nat) (s : State src) (t : State dst) (states : StateRelated f rename s t) :
    RunRelated f rename (stepFuel as fuel s) (stepFuel bs fuel t) := by
  induction fuel generalizing s t with
  | zero =>
      have hc := steps_complete f rename injective states steps
      have hs := steps_selected f rename injective states steps
      generalize ha : as.find? (enabled s) = sa at hs
      generalize hb : bs.find? (enabled t) = tb at hs
      by_cases done : complete as s = true
      · simp only [stepFuel, hc, done, ↓reduceIte]
        exact ⟨rfl, .cons states .nil, .complete states⟩
      · cases hs with
        | none =>
            simp only [stepFuel, hc, done, ha, hb]
            rw [steps_missing f rename injective states steps]
            exact ⟨rfl, .cons states .nil, .blocked _ states⟩
        | some hab =>
            simp only [stepFuel, hc, done, ha, hb]
            exact ⟨rfl, .cons states .nil, .exhausted states⟩
  | succ fuel ih =>
      have hc := steps_complete f rename injective states steps
      have hs := steps_selected f rename injective states steps
      generalize ha : as.find? (enabled s) = sa at hs
      generalize hb : bs.find? (enabled t) = tb at hs
      by_cases done : complete as s = true
      · simp only [stepFuel, hc, done, ↓reduceIte]
        exact ⟨rfl, .cons states .nil, .complete states⟩
      · cases hs with
        | none =>
            simp only [stepFuel, hc, done, ha, hb]
            rw [steps_missing f rename injective states steps]
            exact ⟨rfl, .cons states .nil, .blocked _ states⟩
        | some hab =>
            cases hab with
            | write w v ht hcap hd hr he =>
                have ev := he s t states
                rw [stepFuel.eq_1 as (fuel + 1) s, stepFuel.eq_1 bs (fuel + 1) t]
                simp only [hc, done, ha, hb, ev]
                cases evalReady RationalReference.ops s.available w.body () with
                | notReady =>
                    exact ⟨rfl, .cons states .nil,
                      (by simpa [ht] using OutcomeRelated.contractMismatch w.tag states)⟩
                | evaluated value =>
                    cases value with
                    | none =>
                        exact ⟨by simp [mapEvent, ht], .cons states .nil,
                          (by simpa [ht] using OutcomeRelated.failed w.tag states)⟩
                    | some value =>
                        have next := projection_produce f rename [] states w.capability value
                        have tail := ih _ _ next
                        refine ⟨?_, ?_, ?_⟩
                        · simpa [mapEvent, ht, hcap] using
                            congrArg (List.cons (.produced v.tag v.capability value)) tail.events
                        · simpa [hcap] using List.Forall₂.cons states tail.states
                        · simpa [hcap] using tail.outcome
            | collect a caps =>
                have values := collector_values_projection f rename injective []
                  (by simp) states caps
                rw [stepFuel.eq_1 as (fuel + 1) s, stepFuel.eq_1 bs (fuel + 1) t]
                simp only [hc, done, ha, hb, values]
                cases caps.mapM (producedValue s) with
                | none =>
                    exact ⟨rfl, .cons states .nil, .collectorMismatch a states⟩
                | some values =>
                    have next := projection_collect f rename [] states a
                      (values.foldl (· + ·) (0 : ℚ))
                    have tail := ih _ _ next
                    refine ⟨?_, .cons states tail.states, tail.outcome⟩
                    simpa [mapEvent] using
                      congrArg (List.cons (.sealed (f.address a)
                        (values.foldl (· + ·) (0 : ℚ)))) tail.events

end Fuel

variable {root mid : Declarations Unit}

inductive StepImage (address : Address root → Address src) (name : Nat → Nat) :
    Step root → Step src → Prop
  | write (w : Writer root) (v : Writer src)
      (tag : v.tag = name w.tag)
      (capability : v.capability = name w.capability)
      (destination : v.destination = address w.destination)
      (reads : v.reads = w.reads.map address)
      (evaluate : ∀ (store : PartialStore RationalReference.Carrier src),
        evalReady RationalReference.ops store v.body () =
        evalReady RationalReference.ops (fun p => store (address p)) w.body ()) :
      StepImage address name (.write w) (.write v)
  | collect (a : Address root) (caps : List Nat) :
      StepImage address name (.collect a caps) (.collect (address a) (caps.map name))

theorem stepImage_map (a : Address root → Address src) (n : Nat → Nat)
    {x y} (image : StepImage a n x y) (f : Embedding src dst) (rename : Nat → Nat) :
    StepImage (f.address ∘ a) (rename ∘ n) x (mapStep f rename y) := by
  cases image with
  | write w v ht hc hd hr he =>
      refine .write w (mapWriter f rename v) ?_ ?_ ?_ ?_ ?_
      · simp [mapWriter, ht]
      · simp [mapWriter, hc]
      · simp [mapWriter, hd]
      · simp [mapWriter, hr, List.map_map]
      · intro store
        simpa [mapWriter, evalReady_transport, Embedding.pull, Function.comp_def] using
          he (f.pull store)
  | collect a caps => simpa [mapStep, List.map_map] using
      StepImage.collect (address := f.address ∘ _) (name := rename ∘ n) a caps

theorem stepImage_id (x : Step root) :
    StepImage id id x x := by
  cases x with
  | write w => exact .write w w rfl rfl rfl (by simp) (by intro store; rfl)
  | collect a caps => simpa using StepImage.collect (address := id) (name := id) a caps

theorem images_related (f : Embedding src dst) (rename : Nat → Nat)
    {a : Address root → Address src} {b : Address root → Address dst}
    {m n : Nat → Nat} {x y z}
    (left : StepImage a m x y) (right : StepImage b n x z)
    (addresses : ∀ p, b p = f.address (a p))
    (names : ∀ k, n k = rename (m k)) : StepRelated f rename y z := by
  cases left with
  | write w v ht hc hd hr he =>
      cases right with
      | write w u ut uc ud ur ue =>
          refine .write v u ?_ ?_ ?_ ?_ ?_
          · simp [ht, ut, names]
          · simp [hc, uc, names]
          · simp [hd, ud, addresses]
          · simp [hr, ur, List.map_map, Function.comp_def, addresses]
          · intro s t related
            rw [ue, he]
            have eq : (fun p => t.available (b p)) = (fun p => s.available (a p)) := by
              funext p
              rw [addresses, related.available]
            rw [eq]
  | collect p caps =>
      cases right
      have hn : n = rename ∘ m := funext names
      simpa [addresses, List.map_map, Function.comp_def, hn] using
        StepRelated.collect (f := f) (rename := rename) (a p) (caps.map m)

theorem list_map_related (f : Embedding src dst) (rename : Nat → Nat)
    {α : Type*} (xs : List α) (left : α → Step src) (right : α → Step dst)
    (related : ∀ x, StepRelated f rename (left x) (right x)) :
    List.Forall₂ (StepRelated f rename) (xs.map left) (xs.map right) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (related x) ih

theorem list_append_related {α β : Type*} {R : α → β → Prop}
    {as bs cs ds} (first : List.Forall₂ R as bs) (second : List.Forall₂ R cs ds) :
    List.Forall₂ R (as ++ cs) (bs ++ ds) := by
  induction first with
  | nil => exact second
  | cons h ht ih => exact .cons h ih

theorem bridge_snapshots {α β γ δ : Type*}
    {R : α → β → Prop} {L : α → γ → Prop} {C : β → δ → Prop}
    {xs : List α} {ys : List β} {cs : List γ} {ds : List δ}
    (phase : List.Forall₂ R xs ys) (localStates : List.Forall₂ L xs cs)
    (composite : List.Forall₂ C ys ds) :
    List.Forall₂ (fun c d => ∃ x y, R x y ∧ L x c ∧ C y d) cs ds := by
  induction phase generalizing cs ds with
  | nil =>
      cases localStates
      cases composite
      exact .nil
  | cons related phase ih =>
      cases localStates with
      | cons localHead localTail =>
          cases composite with
          | cons compositeHead compositeTail =>
              exact .cons ⟨_, _, related, localHead, compositeHead⟩
                (ih localTail compositeTail)

theorem stateRelated_full (f : Embedding src dst) (rename : Nat → Nat)
    (address : Address src ≃ Address dst) (coherent : ∀ a, f.address a = address a)
    {s : State src} {t : State dst} (related : StateRelated f rename s t) :
    (∀ b, t.available b = s.available (address.symm b)) ∧
      t.produced = mapLedger rename s.produced := by
  refine ⟨?_, by simpa using related.produced⟩
  intro b
  have h := related.available (address.symm b)
  simpa only [coherent, Equiv.apply_symm_apply] using h

section Reference

variable [Fintype src.Tensor] [DecidableEq src.Tensor]
variable [Fintype dst.Tensor] [DecidableEq dst.Tensor]

inductive ReferenceOutcomeRelated (L : MatchedComponent src) (R : MatchedComponent dst)
    (f : Embedding src dst) (rename : Nat → Nat) :
    Executor.Outcome L.program RationalReference.ops →
      Executor.Outcome R.program RationalReference.ops → Prop
  | complete (s : L.program.Running) (t : R.program.Running)
      (sf : L.program.Complete s) (tf : R.program.Complete t)
      (states : ReferenceStateProjection L.matched R.matched (StateRelated f rename) s t) :
      ReferenceOutcomeRelated L R f rename (.complete s sf) (.complete t tf)
  | failed (lo : SourceOccurrence L.program) (ro : SourceOccurrence R.program)
      (s : L.program.Running) (t : R.program.Running)
      (tags : R.matched.tag ro = rename (L.matched.tag lo))
      (states : ReferenceStateProjection L.matched R.matched (StateRelated f rename) s t) :
      ReferenceOutcomeRelated L R f rename (.failed lo.1 lo.2 s) (.failed ro.1 ro.2 t)

theorem reference_terminal_transport (L : MatchedComponent src) (R : MatchedComponent dst)
    (f : Embedding src dst) (rename : Nat → Nat)
    {g : Outcome src} {k : Outcome dst}
    {left : Executor.Outcome L.program RationalReference.ops}
    {right : Executor.Outcome R.program RationalReference.ops}
    (graph : OutcomeRelated f rename g k)
    (lc : Correspondence.OutcomeRelated L.matched g left)
    (rc : Correspondence.OutcomeRelated R.matched k right)
    (terminal : (∃ s, g = .complete s) ∨ ∃ tag s, g = .failed tag s) :
    ReferenceOutcomeRelated L R f rename left right := by
  rcases terminal with ⟨s, eq⟩ | ⟨tag, s, eq⟩
  · subst g
    cases graph with
    | complete related =>
        cases lc with
        | complete g c finished ledger relation =>
            cases rc with
            | complete h d done ledger' relation' =>
                exact .complete c d finished done
                  ⟨_, _, related, ⟨ledger, relation⟩, ⟨ledger', relation'⟩⟩
  · subst g
    cases lc with
    | failed g c t o ledger relation =>
        cases graph with
        | failed tag related =>
            generalize tagEq : rename (L.matched.tag ⟨t, o⟩) = renamed at rc
            cases rc with
            | failed h d u p ledger' relation' =>
                exact .failed ⟨t, o⟩ ⟨u, p⟩ c d tagEq.symm
                  ⟨_, _, related, ⟨ledger, relation⟩, ⟨ledger', relation'⟩⟩

end Reference

section Nested

open IndexedWitness IndexedOperationalReassociation

variable {σA σB σC : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable [Fintype σC.Tensor] [DecidableEq σC.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (C : MatchedComponent σC) (ab : Boundary A B) (bc : Boundary B C)

theorem nested_steps :
    List.Forall₂ (StepRelated (embedding A B C ab bc) identityEquiv)
      (leftBracket A B C ab bc).graph.steps
      (rightBracket A B C ab bc).graph.steps := by
  simp only [leftBracket, rightBracket, graph_steps_standalone,
    List.map_append, List.map_map, List.append_assoc]
  apply list_append_related
  · apply list_map_related
    intro step
    apply images_related
      (left := stepImage_map _ _
        (stepImage_map _ _ (stepImage_id step) (upstream A B) upstreamId)
        (upstream (compose A B ab) C) upstreamId)
      (right := stepImage_map _ _ (stepImage_id step)
        (upstream A (compose B C bc)) upstreamId)
    · intro p
      exact ((embedding_address A B C ab bc _).trans (address_A A B C ab bc p)).symm
    · intro n
      exact (identity_A n).symm
  · apply list_append_related
    · apply list_map_related
      intro step
      apply images_related
        (left := stepImage_map _ _
          (stepImage_map _ _ (stepImage_id step) (downstream A B ab) downstreamId)
          (upstream (compose A B ab) C) upstreamId)
        (right := stepImage_map _ _
          (stepImage_map _ _ (stepImage_id step) (upstream B C) upstreamId)
          (downstream A (compose B C bc) (rightNestedBoundary A B C ab bc)) downstreamId)
      · intro p
        exact ((embedding_address A B C ab bc _).trans (address_B A B C ab bc p)).symm
      · intro n
        exact (identity_B n).symm
    · apply list_map_related
      intro step
      apply images_related
        (left := stepImage_map _ _ (stepImage_id step)
          (downstream (compose A B ab) C (leftNestedBoundary A B C ab bc)) downstreamId)
        (right := stepImage_map _ _
          (stepImage_map _ _ (stepImage_id step) (downstream B C bc) downstreamId)
          (downstream A (compose B C bc) (rightNestedBoundary A B C ab bc)) downstreamId)
      · intro p
        exact ((embedding_address A B C ab bc _).trans (address_C A B C ab bc p)).symm
      · intro n
        exact (identity_C n).symm

theorem nested_initial (η : A.program.Input) :
    StateRelated (embedding A B C ab bc) identityEquiv
      (initial (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
        (liftInput A B ab η)).val)
      (initial (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η).val) := by
  refine ⟨?_, rfl⟩
  intro p
  rw [embedding_address]
  exact initial_available A B C ab bc η p

theorem nested_default_runs (η : A.program.Input) :
    RunRelated (embedding A B C ab bc) identityEquiv
      (runChecked (leftBracket A B C ab bc).contract
        (leftBracket A B C ab bc).fragment
        (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
          (liftInput A B ab η)).val)
      (runChecked (rightBracket A B C ab bc).contract
        (rightBracket A B C ab bc).fragment
        (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η).val) := by
  rw [checked_eq_stepFuel (leftBracket A B C ab bc).matched,
    checked_eq_stepFuel (rightBracket A B C ab bc).matched]
  rw [(default_budgets A B C ab bc).1, (default_budgets A B C ab bc).2]
  exact stepFuel_transport _ _ identityEquiv.injective (nested_steps A B C ab bc) _ _ _
    (nested_initial A B C ab bc η)

theorem ranked_nested_default_runs (η : A.program.Input)
    (rankA : A.program.RankCertificate) (rankB : B.program.RankCertificate)
    (rankC : C.program.RankCertificate) :
    let left := runChecked (leftBracket A B C ab bc).contract
      (leftBracket A B C ab bc).fragment
      (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
        (liftInput A B ab η)).val
    let right := runChecked (rightBracket A B C ab bc).contract
      (rightBracket A B C ab bc).fragment
      (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η).val
    RunRelated (embedding A B C ab bc) identityEquiv left right ∧
      SuccessfulOrFailed left ∧ SuccessfulOrFailed right := by
  exact ⟨nested_default_runs A B C ab bc η,
    ranked_default_terminal (leftBracket A B C ab bc) _
      (leftRank A B C ab bc rankA rankB rankC),
    ranked_default_terminal (rightBracket A B C ab bc) _
      (rightRank A B C ab bc rankA rankB rankC)⟩

theorem nested_reference_runs (η : A.program.Input) :
    let L := leftBracket A B C ab bc
    let R := rightBracket A B C ab bc
    let ηL := liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
      (liftInput A B ab η)
    let ηR := liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η
    let left := Executor.run L.program RationalReference.ops L.schedule ηL
    let right := Executor.run R.program RationalReference.ops R.schedule ηR
    right.events.map R.matched.event =
      (left.events.map L.matched.event).map
        (mapEvent (embedding A B C ab bc) identityEquiv) ∧
    List.Forall₂
      (ReferenceStateProjection L.matched R.matched
        (StateRelated (embedding A B C ab bc) identityEquiv))
      (Correspondence.referenceSnapshots (L.program.initial ηL) left.events)
      (Correspondence.referenceSnapshots (R.program.initial ηR) right.events) ∧
    OutcomeRelated (embedding A B C ab bc) identityEquiv
      (runChecked L.contract L.fragment ηL.val).outcome
      (runChecked R.contract R.fragment ηR.val).outcome ∧
    Correspondence.OutcomeRelated L.matched
      (runChecked L.contract L.fragment ηL.val).outcome left.outcome ∧
    Correspondence.OutcomeRelated R.matched
      (runChecked R.contract R.fragment ηR.val).outcome right.outcome := by
  dsimp only
  have graph := nested_default_runs A B C ab bc η
  have left := Correspondence.accepted_run_correspondence
    (leftBracket A B C ab bc).matched
    (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc) (liftInput A B ab η))
  have right := Correspondence.accepted_run_correspondence
    (rightBracket A B C ab bc).matched
    (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η)
  refine ⟨?_, bridge_snapshots graph.states left.states right.states,
    graph.outcome, left.outcome, right.outcome⟩
  rw [← left.events, ← right.events]
  exact graph.events

theorem ranked_nested_reference_outcomes (η : A.program.Input)
    (rankA : A.program.RankCertificate) (rankB : B.program.RankCertificate)
    (rankC : C.program.RankCertificate) :
    ReferenceOutcomeRelated (leftBracket A B C ab bc) (rightBracket A B C ab bc)
      (embedding A B C ab bc) identityEquiv
      (Executor.run (leftBracket A B C ab bc).program RationalReference.ops
        (leftBracket A B C ab bc).schedule
        (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
          (liftInput A B ab η))).outcome
      (Executor.run (rightBracket A B C ab bc).program RationalReference.ops
        (rightBracket A B C ab bc).schedule
        (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η)).outcome := by
  have refs := nested_reference_runs A B C ab bc η
  have terminal := (ranked_nested_default_runs A B C ab bc η rankA rankB rankC).2.1
  exact reference_terminal_transport _ _ _ _ refs.2.2.1 refs.2.2.2.1 refs.2.2.2.2 terminal

end Nested

#print axioms stepFuel_transport
#print axioms nested_default_runs
#print axioms nested_reference_runs
#print axioms ranked_nested_reference_outcomes

end IndexedOperationalRuns
