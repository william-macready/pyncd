import IndexedOperationalRuns

namespace IndexedOperationalRunsPhases

open LeanNCD.Semantics LeanNCD.Semantics.Program
open IndexedComponentTransport IndexedComponentComposition IndexedComponentExecution
open IndexedOpenComposition IndexedWitness IndexedOperationalReassociation
open IndexedOperationalRuns

abbrev checked {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
    (A : MatchedComponent σ) (η : A.program.Input) : Run σ :=
  runChecked A.contract A.fragment η.val

structure Cut {S : Type*} (states : List S) where
  before : List S
  current : S
  after : List S
  exact_states : states = before ++ current :: after

structure CutRelated {S T : Type*} (R : S → T → Prop)
    {xs : List S} {ys : List T} (a : Cut xs) (b : Cut ys) : Prop where
  before : List.Forall₂ R a.before b.before
  current : R a.current b.current
  after : List.Forall₂ R a.after b.after

theorem cut_transport {S T : Type*} {R : S → T → Prop}
    {xs : List S} {ys : List T} (related : List.Forall₂ R xs ys) (a : Cut xs) :
    ∃ b : Cut ys, CutRelated R a b := by
  rcases a with ⟨before, current, after, eq⟩
  subst xs
  induction before generalizing ys with
  | nil =>
      cases related with
      | cons h ht => exact ⟨⟨[], _, _, rfl⟩, ⟨.nil, h, ht⟩⟩
  | cons x xs ih =>
      cases related with
      | @cons _ head _ _ h ht =>
          obtain ⟨b, hb⟩ := ih ht
          refine ⟨⟨head :: b.before, b.current, b.after, ?_⟩, ?_⟩
          · simp only [List.cons_append, List.cons.injEq, true_and]
            exact b.exact_states
          · exact ⟨.cons h hb.before, hb.current, hb.after⟩

def Cut.extend {S : Type*} {xs : List S} (a : Cut xs) (more : List S) :
    Cut (xs ++ more) :=
  ⟨a.before, a.current, a.after ++ more,
    by simpa only [List.append_assoc, List.cons_append] using
      congrArg (fun xs => xs ++ more) a.exact_states⟩

theorem cut_coincide {S : Type*} {xs : List S} (a b : Cut xs)
    (same : a.before.length = b.before.length) : a.current = b.current := by
  have eq := congrArg (fun states => states[a.before.length]?) a.exact_states
  have eq' := congrArg (fun states => states[b.before.length]?) b.exact_states
  simp only [List.getElem?_append, lt_self_iff_false, ↓reduceIte,
    Nat.sub_self, List.getElem?_cons_zero] at eq eq'
  rw [same] at eq
  exact Option.some.inj (eq.symm.trans eq')

section Binary

variable {σ τ : Declarations Unit}
variable [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable [Fintype τ.Tensor] [DecidableEq τ.Tensor]
variable (A : MatchedComponent σ) (B : MatchedComponent τ) (wire : Boundary A B)
variable (η : A.program.Input)

structure FailedPhase where
  tag : Nat
  endpoint : State σ
  targetEndpoint : State (declarations A B)
  source_failed : (checked A η).outcome = .failed tag endpoint
  composite_failed : (checked (compose A B wire) (liftInput A B wire η)).outcome =
    .failed (upstreamId tag) targetEndpoint
  related : UpstreamState A B wire endpoint targetEndpoint
  events : (checked (compose A B wire) (liftInput A B wire η)).events =
    (checked A η).events.map (mapEvent (upstream A B) upstreamId)
  states : List.Forall₂ (UpstreamState A B wire)
    (checked A η).states (checked (compose A B wire) (liftInput A B wire η)).states

structure ReachedPhase where
  completed : State σ
  store : Store RationalReference.Carrier σ
  cut : State (declarations A B)
  remaining : Nat
  snapshots : List (State (declarations A B))
  source_complete : (checked A η).outcome = .complete completed
  full : ∀ a, completed.available a = some (store a)
  upstream_state : UpstreamState A B wire completed cut
  downstream_state : DownstreamState A B wire completed
    (initial (boundaryInput A B wire store).val) cut
  prefix_states : List.Forall₂ (UpstreamState A B wire)
    (checked A η).states (snapshots ++ [cut])
  budget : remaining + snapshots.length = (compose A B wire).graph.steps.length + 1
  upstream_bound : snapshots.length ≤ A.graph.steps.length
  downstream_budget : B.graph.steps.length + 1 ≤ remaining
  suffix : RunProjection (downstream A B wire) downstreamId
    (DownstreamState A B wire completed)
    (checked B (boundaryInput A B wire store))
    (stepFuel (compose A B wire).graph.steps remaining cut)
  events : (checked (compose A B wire) (liftInput A B wire η)).events =
    (checked A η).events.map (mapEvent (upstream A B) upstreamId) ++
      (stepFuel (compose A B wire).graph.steps remaining cut).events
  states : (checked (compose A B wire) (liftInput A B wire η)).states =
    snapshots ++ (stepFuel (compose A B wire).graph.steps remaining cut).states
  outcome : (checked (compose A B wire) (liftInput A B wire η)).outcome =
    (stepFuel (compose A B wire).graph.steps remaining cut).outcome

theorem binary_phases (rankA : A.program.RankCertificate)
    (rankB : B.program.RankCertificate) :
    Nonempty (FailedPhase A B wire η) ∨ Nonempty (ReachedPhase A B wire η) := by
  rcases compose_default_phases A B wire η rankA rankB with failed | reached
  · rcases failed with ⟨tag, endpoint, target, hs, ht, hr, he, hstates⟩
    exact .inl ⟨⟨tag, endpoint, target, hs, ht, hr, he, hstates⟩⟩
  · rcases reached with ⟨completed, store, cut, remaining, snapshots,
      hs, full, up, down, pre, budget, bound, residual, suffix, events, states, outcome⟩
    exact .inr ⟨⟨completed, store, cut, remaining, snapshots,
      hs, full, up, down, pre, budget, bound, residual, suffix, events, states, outcome⟩⟩

theorem stepFuel_states_head {σ : Declarations Unit} [DecidableEq σ.Tensor]
    (steps : List (Step σ)) (fuel : Nat) (state : State σ) :
    ∃ rest, (stepFuel steps fuel state).states = state :: rest := by
  rw [stepFuel]
  split
  · exact ⟨[], rfl⟩
  · split
    · exact ⟨[], rfl⟩
    · split
      · exact ⟨[], rfl⟩
      · split
        · split <;> first | exact ⟨[], rfl⟩ | exact ⟨_, rfl⟩
        · split <;> first | exact ⟨[], rfl⟩ | exact ⟨_, rfl⟩

theorem ReachedPhase.cut_exists (p : ReachedPhase A B wire η) :
    ∃ c : Cut (checked (compose A B wire) (liftInput A B wire η)).states,
      c.before = p.snapshots ∧ c.current = p.cut := by
  obtain ⟨rest, eq⟩ := stepFuel_states_head
    (compose A B wire).graph.steps p.remaining p.cut
  exact ⟨⟨p.snapshots, p.cut, rest, by rw [p.states, eq]⟩, rfl, rfl⟩

theorem ReachedPhase.boundary (p : ReachedPhase A B wire η) :
    boundaryInput A B wire p.store =
      boundaryFromOutput A B wire (A.program.outputProjection p.store) :=
  boundaryInput_outputProjection A B wire p.store

theorem ReachedPhase.failed_leaf (p : ReachedPhase A B wire η)
    {tag : Nat} {endpoint : State (declarations A B)}
    (failed : (checked (compose A B wire) (liftInput A B wire η)).outcome =
      .failed tag endpoint) :
    ∃ leafTag leafEnd, (checked B (boundaryInput A B wire p.store)).outcome =
      .failed leafTag leafEnd ∧ tag = downstreamId leafTag ∧
      DownstreamState A B wire p.completed leafEnd endpoint := by
  have tail := p.outcome.symm.trans failed
  rcases p.suffix.2.2 with done | failedLeaf
  · rcases done with ⟨s, t, hs, ht, related⟩
    rw [ht] at tail
    contradiction
  · rcases failedLeaf with ⟨leafTag, leafEnd, target, hs, ht, related⟩
    have eq := ht.symm.trans tail
    cases eq
    exact ⟨leafTag, leafEnd, hs, rfl, related⟩

theorem ReachedPhase.complete_leaf (p : ReachedPhase A B wire η)
    {endpoint : State (declarations A B)}
    (completed : (checked (compose A B wire) (liftInput A B wire η)).outcome =
      .complete endpoint) :
    ∃ leafEnd, (checked B (boundaryInput A B wire p.store)).outcome =
      .complete leafEnd ∧ DownstreamState A B wire p.completed leafEnd endpoint := by
  have tail := p.outcome.symm.trans completed
  rcases p.suffix.2.2 with done | failed
  · rcases done with ⟨s, t, hs, ht, related⟩
    have eq := ht.symm.trans tail
    cases eq
    exact ⟨s, hs, related⟩
  · rcases failed with ⟨tag, s, t, hs, ht, related⟩
    rw [ht] at tail
    contradiction

theorem ReachedPhase.lift_cut (p : ReachedPhase A B wire η)
    (c : Cut (checked A η).states) :
    ∃ d : Cut (checked (compose A B wire) (liftInput A B wire η)).states,
      d.before.length = c.before.length ∧
      d.before.length ≤ p.snapshots.length ∧
      UpstreamState A B wire c.current d.current := by
  obtain ⟨target, related⟩ := cut_transport p.prefix_states c
  obtain ⟨rest, eq⟩ := stepFuel_states_head
    (compose A B wire).graph.steps p.remaining p.cut
  have allStates : (checked (compose A B wire) (liftInput A B wire η)).states =
      (p.snapshots ++ [p.cut]) ++ rest := by
    rw [p.states, eq]
    simp
  let d : Cut (checked (compose A B wire) (liftInput A B wire η)).states :=
    ⟨target.before, target.current, target.after ++ rest, by
      simpa only [List.append_assoc, List.cons_append] using
        allStates.trans (congrArg (fun xs => xs ++ rest) target.exact_states)⟩
  refine ⟨d, related.before.length_eq.symm, ?_, related.current⟩
  have len := congrArg List.length target.exact_states
  simp only [List.length_append, List.length_cons, List.length_nil] at len
  change target.before.length ≤ p.snapshots.length
  omega

end Binary

section Triple

variable {σA σB σC : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable [Fintype σC.Tensor] [DecidableEq σC.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB) (C : MatchedComponent σC)
variable (ab : Boundary A B) (bc : Boundary B C) (η : A.program.Input)

abbrev leftInput := liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
  (liftInput A B ab η)

theorem original_bc_input (store : Store RationalReference.Carrier (declarations A B)) :
    boundaryInput (compose A B ab) C (leftNestedBoundary A B C ab bc) store =
      boundaryInput B C bc (restrictDownstream A B ab store) := by
  apply Subtype.ext
  funext t
  by_cases h : C.program.input t = true
  · simp only [boundaryInput, h, ↓reduceDIte]
    congr 1
    funext p
    exact outputProjection_downstream A B ab store (bc.matched ⟨t, h⟩)
      ((bc.domain ⟨t, h⟩).coord p)
  · simp [boundaryInput, h]

structure TwoReached where
  inner : ReachedPhase A B ab η
  outer : ReachedPhase (compose A B ab) C (leftNestedBoundary A B C ab bc)
    (liftInput A B ab η)
  endB : State σB
  b_complete : (checked B (boundaryInput A B ab inner.store)).outcome = .complete endB
  b_projection : DownstreamState A B ab inner.completed endB outer.completed
  b_full : ∀ a, endB.available a = some (restrictDownstream A B ab outer.store a)
  first : Cut (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η)).states
  second : Cut (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η)).states
  first_index : first.before.length = inner.snapshots.length
  second_index : second.before.length = outer.snapshots.length
  first_relation : UpstreamState (compose A B ab) C (leftNestedBoundary A B C ab bc)
    inner.cut first.current
  second_current : second.current = outer.cut
  ordered : first.before.length ≤ second.before.length
  ab_boundary : boundaryInput A B ab inner.store =
    boundaryFromOutput A B ab (A.program.outputProjection inner.store)
  bc_boundary : boundaryInput B C bc (restrictDownstream A B ab outer.store) =
    boundaryFromOutput B C bc (B.program.outputProjection
      (restrictDownstream A B ab outer.store))
  c_input : boundaryInput (compose A B ab) C (leftNestedBoundary A B C ab bc) outer.store =
    boundaryInput B C bc (restrictDownstream A B ab outer.store)

theorem two_reached
    (inner : ReachedPhase A B ab η)
    (outer : ReachedPhase (compose A B ab) C (leftNestedBoundary A B C ab bc)
      (liftInput A B ab η)) : Nonempty (TwoReached A B C ab bc η) := by
  obtain ⟨endB, bdone, related⟩ := inner.complete_leaf A B ab η outer.source_complete
  obtain ⟨a, aBefore, aCurrent⟩ := inner.cut_exists A B ab η
  obtain ⟨first, index, bound, relation⟩ := outer.lift_cut
    (compose A B ab) C (leftNestedBoundary A B C ab bc) (liftInput A B ab η) a
  obtain ⟨second, secondBefore, secondCurrent⟩ := outer.cut_exists
    (compose A B ab) C (leftNestedBoundary A B C ab bc) (liftInput A B ab η)
  refine ⟨⟨inner, outer, endB, bdone, related, ?_, first, second, ?_, ?_, ?_,
    secondCurrent, ?_, inner.boundary A B ab η, ?_, original_bc_input A B C ab bc outer.store⟩⟩
  · intro a
    exact (related.available a).symm.trans (outer.full ((downstream A B ab).address a))
  · simpa only [aBefore] using index
  · rw [secondBefore]
  · simpa only [aCurrent] using relation
  · simpa only [secondBefore] using bound
  · exact boundaryInput_outputProjection B C bc _

inductive TriplePhases : Prop
  | failA (inner : FailedPhase A B ab η)
      (outer : FailedPhase (compose A B ab) C (leftNestedBoundary A B C ab bc)
        (liftInput A B ab η))
      (failure : (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η)).outcome =
        .failed (upstreamId (upstreamId inner.tag)) outer.targetEndpoint) :
      TriplePhases
  | failB (inner : ReachedPhase A B ab η)
      (outer : FailedPhase (compose A B ab) C (leftNestedBoundary A B C ab bc)
        (liftInput A B ab η))
      (tag : Nat) (endB : State σB)
      (b_failed : (checked B (boundaryInput A B ab inner.store)).outcome = .failed tag endB)
      (b_projection : DownstreamState A B ab inner.completed endB outer.endpoint)
      (first : Cut (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η)).states)
      (first_index : first.before.length = inner.snapshots.length)
      (first_relation : UpstreamState (compose A B ab) C (leftNestedBoundary A B C ab bc)
        inner.cut first.current)
      (ab_boundary : boundaryInput A B ab inner.store =
        boundaryFromOutput A B ab (A.program.outputProjection inner.store))
      (failure : (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η)).outcome =
        .failed (upstreamId (downstreamId tag)) outer.targetEndpoint) :
      TriplePhases
  | failC (phases : TwoReached A B C ab bc η)
      (tag : Nat) (endC : State σC) (endpoint : State (declarations (compose A B ab) C))
      (c_failed : (checked C (boundaryInput B C bc
        (restrictDownstream A B ab phases.outer.store))).outcome = .failed tag endC)
      (c_projection : DownstreamState (compose A B ab) C (leftNestedBoundary A B C ab bc)
        phases.outer.completed endC endpoint)
      (failure : (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η)).outcome =
        .failed (downstreamId tag) endpoint) : TriplePhases
  | allSuccess (phases : TwoReached A B C ab bc η)
      (endC : State σC) (endpoint : State (declarations (compose A B ab) C))
      (c_complete : (checked C (boundaryInput B C bc
        (restrictDownstream A B ab phases.outer.store))).outcome = .complete endC)
      (c_projection : DownstreamState (compose A B ab) C (leftNestedBoundary A B C ab bc)
        phases.outer.completed endC endpoint)
      (complete : (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η)).outcome =
        .complete endpoint) : TriplePhases

theorem triple_phases (rankA : A.program.RankCertificate)
    (rankB : B.program.RankCertificate) (rankC : C.program.RankCertificate) :
    TriplePhases A B C ab bc η := by
  have outerPhases := binary_phases (compose A B ab) C (leftNestedBoundary A B C ab bc)
    (liftInput A B ab η) (compositeRankCertificate A B ab rankA rankB) rankC
  rcases binary_phases A B ab η rankA rankB with inner | inner
  · rcases inner with ⟨inner⟩
    rcases outerPhases with outer | outer
    · rcases outer with ⟨outer⟩
      have eq := inner.composite_failed.symm.trans outer.source_failed
      injection eq with tags endpoints
      apply TriplePhases.failA inner outer
      simpa only [← tags] using outer.composite_failed
    · rcases outer with ⟨outer⟩
      have eq := inner.composite_failed.symm.trans outer.source_complete
      contradiction
  · rcases inner with ⟨inner⟩
    rcases outerPhases with outer | outer
    · rcases outer with ⟨outer⟩
      obtain ⟨tag, endB, failed, tagEq, bRelated⟩ :=
        inner.failed_leaf A B ab η outer.source_failed
      obtain ⟨a, aBefore, aCurrent⟩ := inner.cut_exists A B ab η
      obtain ⟨first, related⟩ := cut_transport outer.states a
      refine TriplePhases.failB inner outer tag endB failed bRelated first ?_ ?_
        (inner.boundary A B ab η) ?_
      · simpa only [aBefore] using related.before.length_eq.symm
      · simpa only [aCurrent] using related.current
      · simpa only [tagEq] using outer.composite_failed
    · rcases outer with ⟨outer⟩
      obtain ⟨phases⟩ := two_reached A B C ab bc η inner outer
      rcases phases.outer.suffix.2.2 with done | failed
      · rcases done with ⟨endC, endpoint, hs, ht, related⟩
        apply TriplePhases.allSuccess phases endC endpoint
        · simpa only [phases.c_input] using hs
        · exact related
        · exact phases.outer.outcome.trans ht
      · rcases failed with ⟨tag, endC, endpoint, hs, ht, related⟩
        apply TriplePhases.failC phases tag endC endpoint
        · simpa only [phases.c_input] using hs
        · exact related
        · exact phases.outer.outcome.trans ht

abbrev rightInput := liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η

theorem right_cut
    (c : Cut (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η)).states) :
    ∃ d : Cut (checked (rightBracket A B C ab bc) (rightInput A B C ab bc η)).states,
      CutRelated (StateRelated (embedding A B C ab bc) identityEquiv) c d ∧
      d.before.length = c.before.length ∧
      (∀ a, d.current.available a =
        c.current.available ((addressEquiv A B C ab bc).symm a)) ∧
      d.current.produced = mapLedger identityEquiv c.current.produced := by
  obtain ⟨d, related⟩ := cut_transport (nested_default_runs A B C ab bc η).states c
  exact ⟨d, related, related.before.length_eq.symm,
    stateRelated_full _ _ (addressEquiv A B C ab bc)
      (embedding_address A B C ab bc) related.current⟩

theorem two_reached_right (p : TwoReached A B C ab bc η) :
    ∃ first second :
      Cut (checked (rightBracket A B C ab bc) (rightInput A B C ab bc η)).states,
      CutRelated (StateRelated (embedding A B C ab bc) identityEquiv) p.first first ∧
      CutRelated (StateRelated (embedding A B C ab bc) identityEquiv) p.second second ∧
      first.before.length = p.first.before.length ∧
      second.before.length = p.second.before.length ∧
      first.before.length ≤ second.before.length ∧
      (first.before.length = second.before.length → first.current = second.current) := by
  obtain ⟨first, hfirst, ifirst, _⟩ := right_cut A B C ab bc η p.first
  obtain ⟨second, hsecond, isecond, _⟩ := right_cut A B C ab bc η p.second
  exact ⟨first, second, hfirst, hsecond, ifirst, isecond,
    by simpa only [ifirst, isecond] using p.ordered,
    cut_coincide first second⟩

theorem two_reached_empty_B (p : TwoReached A B C ab bc η)
    (empty : B.graph.steps = []) : p.first.current = p.second.current := by
  have hb : (checked B (boundaryInput A B ab p.inner.store)).states.length = 1 := by
    rw [checked, checked_eq_stepFuel B.matched]
    simp [empty, stepFuel, complete]
  have tailLen := p.inner.suffix.2.1.length_eq
  have sourceLen := congrArg List.length p.inner.states
  have prefixLen := p.outer.prefix_states.length_eq
  simp only [List.length_append, List.length_singleton] at sourceLen prefixLen
  rw [hb] at tailLen
  apply cut_coincide
  rw [p.first_index, p.second_index]
  omega

theorem right_failed {tag : Nat}
    {endpoint : State (declarations (compose A B ab) C)}
    (failed : (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η)).outcome =
      .failed tag endpoint) :
    ∃ target,
      (checked (rightBracket A B C ab bc) (rightInput A B C ab bc η)).outcome =
        .failed (identityEquiv tag) target ∧
      StateRelated (embedding A B C ab bc) identityEquiv endpoint target := by
  have related := (nested_default_runs A B C ab bc η).outcome
  rw [failed] at related
  generalize eq : (checked (rightBracket A B C ab bc)
    (rightInput A B C ab bc η)).outcome = outcome at related
  cases related with
  | failed tag states => exact ⟨_, rfl, states⟩

theorem right_complete {endpoint : State (declarations (compose A B ab) C)}
    (done : (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η)).outcome =
      .complete endpoint) :
    ∃ target,
      (checked (rightBracket A B C ab bc) (rightInput A B C ab bc η)).outcome =
        .complete target ∧
      StateRelated (embedding A B C ab bc) identityEquiv endpoint target := by
  have related := (nested_default_runs A B C ab bc η).outcome
  rw [done] at related
  generalize eq : (checked (rightBracket A B C ab bc)
    (rightInput A B C ab bc η)).outcome = outcome at related
  cases related with
  | complete states => exact ⟨_, rfl, states⟩

theorem reference_cuts
    (c : Cut (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η)).states) :
    let L := leftBracket A B C ab bc
    let R := rightBracket A B C ab bc
    let leftRef := Executor.run L.program RationalReference.ops L.schedule (leftInput A B C ab bc η)
    let rightRef := Executor.run R.program RationalReference.ops R.schedule (rightInput A B C ab bc η)
    ∃ (d : Cut (checked R (rightInput A B C ab bc η)).states)
      (lc : Cut (Correspondence.referenceSnapshots
        (L.program.initial (leftInput A B C ab bc η)) leftRef.events))
      (rc : Cut (Correspondence.referenceSnapshots
        (R.program.initial (rightInput A B C ab bc η)) rightRef.events)),
      CutRelated (StateRelated (embedding A B C ab bc) identityEquiv) c d ∧
      CutRelated (fun g s => LedgerInvariant L.matched g ∧ Relation L.matched g s) c lc ∧
      CutRelated (fun g s => LedgerInvariant R.matched g ∧ Relation R.matched g s) d rc ∧
      lc.before.length = c.before.length ∧ rc.before.length = c.before.length ∧
      ReferenceStateProjection L.matched R.matched
        (StateRelated (embedding A B C ab bc) identityEquiv) lc.current rc.current := by
  dsimp only
  obtain ⟨d, hd, index, _⟩ := right_cut A B C ab bc η c
  have left := Correspondence.accepted_run_correspondence
    (leftBracket A B C ab bc).matched (leftInput A B C ab bc η)
  have right := Correspondence.accepted_run_correspondence
    (rightBracket A B C ab bc).matched (rightInput A B C ab bc η)
  obtain ⟨lc, hlc⟩ := cut_transport left.states c
  obtain ⟨rc, hrc⟩ := cut_transport right.states d
  exact ⟨d, lc, rc, hd, hlc, hrc, hlc.before.length_eq.symm,
    hrc.before.length_eq.symm.trans index, _, _, hd.current, hlc.current, hrc.current⟩

theorem triple_phases_with_transport (rankA : A.program.RankCertificate)
    (rankB : B.program.RankCertificate) (rankC : C.program.RankCertificate) :
    TriplePhases A B C ab bc η ∧
      RunRelated (embedding A B C ab bc) identityEquiv
        (checked (leftBracket A B C ab bc) (leftInput A B C ab bc η))
        (checked (rightBracket A B C ab bc) (rightInput A B C ab bc η)) := by
  exact ⟨triple_phases A B C ab bc η rankA rankB rankC,
    nested_default_runs A B C ab bc η⟩

theorem TwoReached.default_budget (p : TwoReached A B C ab bc η) :
    p.outer.remaining + p.outer.snapshots.length =
      A.graph.steps.length + B.graph.steps.length + C.graph.steps.length + 1 := by
  exact p.outer.budget.trans (default_budgets A B C ab bc).1

end Triple

#print axioms triple_phases
#print axioms two_reached_right
#print axioms two_reached_empty_B
#print axioms reference_cuts

end IndexedOperationalRunsPhases
