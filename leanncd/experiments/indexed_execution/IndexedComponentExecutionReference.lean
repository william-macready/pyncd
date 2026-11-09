import IndexedComponentExecutionRuns

namespace IndexedComponentExecution

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor
open IndexedOpenComposition
open IndexedComponentTransport
open IndexedComponentComposition

section ReferenceProjection

variable {σ τ : Declarations Unit}
variable [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable [Fintype τ.Tensor] [DecidableEq τ.Tensor]
variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {Q : Program RationalReference.Carrier τ RationalReference.registry}
variable {s : Schedule P} {t : Schedule Q}
variable {c : Contract σ} {d : Contract τ}
variable {f : Fragment σ} {k : Fragment τ}
variable {g : Closed σ} {h : Closed τ}

/-- Snapshot projection retains both ordered ledgers and the full reference relations,
including pending occurrences and accumulators. -/
def ReferenceStateProjection
    (localMatch : SourceContractMatch P s c f g)
    (compositeMatch : SourceContractMatch Q t d k h)
    (R : State σ → State τ → Prop) (localState : P.Running)
    (composite : Q.Running) : Prop :=
  ∃ localGraph compositeGraph, R localGraph compositeGraph ∧
    (LedgerInvariant localMatch localGraph ∧ Relation localMatch localGraph localState) ∧
    (LedgerInvariant compositeMatch compositeGraph ∧
      Relation compositeMatch compositeGraph composite)

end ReferenceProjection

private theorem bridge_states {α β γ δ : Type*}
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

private theorem split_states {α β : Type*} {R : α → β → Prop}
    (xs ys : List α) {cs : List β} (related : List.Forall₂ R (xs ++ ys) cs) :
    ∃ pre suffix, cs = pre ++ suffix ∧
      List.Forall₂ R xs pre ∧ List.Forall₂ R ys suffix := by
  induction xs generalizing cs with
  | nil => exact ⟨[], cs, rfl, .nil, related⟩
  | cons x xs ih =>
      cases related with
      | cons head tail =>
          obtain ⟨pre, suffix, eq, left, right⟩ := ih tail
          exact ⟨_ :: pre, suffix, by simp only [List.cons_append, eq],
            .cons head left, right⟩

private theorem stepFuel_states_head {σ : Declarations Unit} [DecidableEq σ.Tensor]
    (steps : List (Step σ)) (fuel : Nat) (state : State σ) :
    ∃ tail, (stepFuel steps fuel state).states = state :: tail := by
  rw [stepFuel]
  repeat' first | split | exact ⟨[], rfl⟩ | exact ⟨_, rfl⟩

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB) (wire : Boundary A B)

/-- The default reference executions share one normalized phase-cut snapshot.
Failure snapshots are normalized by the existing execution correspondence. -/
theorem reference_default_phases (η : A.program.Input)
    (rankA : A.program.RankCertificate) (rankB : B.program.RankCertificate) :
    let C := compose A B wire
    let source := runChecked A.contract A.fragment η.val
    let composite := runChecked C.contract C.fragment (liftInput A B wire η).val
    let sourceRef := Executor.run A.program RationalReference.ops A.schedule η
    let compositeRef := Executor.run C.program RationalReference.ops C.schedule
      (liftInput A B wire η)
    (∃ tag endpoint targetEndpoint,
      source.outcome = .failed tag endpoint ∧
      composite.outcome = .failed (upstreamId tag) targetEndpoint ∧
      UpstreamState A B wire endpoint targetEndpoint ∧
      List.Forall₂
        (ReferenceStateProjection A.matched C.matched (UpstreamState A B wire))
        (Correspondence.referenceSnapshots (A.program.initial η) sourceRef.events)
        (Correspondence.referenceSnapshots (C.program.initial (liftInput A B wire η))
          compositeRef.events) ∧
      compositeRef.events.map C.matched.event =
        (sourceRef.events.map A.matched.event).map
          (mapEvent (upstream A B) upstreamId)) ∨
    (∃ (completed : State σA) (ρA : Store RationalReference.Carrier σA)
      (cut : State (declarations A B)) (remaining : Nat)
      (pre : List C.program.Running) (cutRef : C.program.Running)
      (suffix : List C.program.Running),
      source.outcome = .complete completed ∧
      (∀ a, completed.available a = some (ρA a)) ∧
      UpstreamState A B wire completed cut ∧
      DownstreamState A B wire completed
        (initial (boundaryInput A B wire ρA).val) cut ∧
      Correspondence.referenceSnapshots (C.program.initial (liftInput A B wire η))
        compositeRef.events = pre ++ cutRef :: suffix ∧
      List.Forall₂
        (ReferenceStateProjection A.matched C.matched (UpstreamState A B wire))
        (Correspondence.referenceSnapshots (A.program.initial η) sourceRef.events)
        (pre ++ [cutRef]) ∧
      List.Forall₂
        (ReferenceStateProjection B.matched C.matched
          (DownstreamState A B wire completed))
        (Correspondence.referenceSnapshots
          (B.program.initial (boundaryInput A B wire ρA))
          (Executor.run B.program RationalReference.ops B.schedule
            (boundaryInput A B wire ρA)).events)
        (cutRef :: suffix) ∧
      remaining + pre.length = C.graph.steps.length + 1 ∧
      pre.length ≤ A.graph.steps.length ∧
      B.graph.steps.length + 1 ≤ remaining ∧
      compositeRef.events.map C.matched.event =
        (sourceRef.events.map A.matched.event).map
          (mapEvent (upstream A B) upstreamId) ++
        ((Executor.run B.program RationalReference.ops B.schedule
          (boundaryInput A B wire ρA)).events.map B.matched.event).map
            (mapEvent (downstream A B wire) downstreamId) ∧
      RunProjection (downstream A B wire) downstreamId (DownstreamState A B wire completed)
        (runChecked B.contract B.fragment (boundaryInput A B wire ρA).val)
        (stepFuel C.graph.steps remaining cut) ∧
      composite.outcome = (stepFuel C.graph.steps remaining cut).outcome ∧
      boundaryInput A B wire ρA =
        boundaryFromOutput A B wire (A.program.outputProjection ρA)) := by
  dsimp only
  have localRun := Correspondence.accepted_run_correspondence A.matched η
  have composite := Correspondence.accepted_run_correspondence
    (compose A B wire).matched (liftInput A B wire η)
  rcases compose_default_phases A B wire η rankA rankB with failed | completed
  · left
    rcases failed with ⟨tag, endpoint, targetEndpoint, sourceFailed, compositeFailed,
      related, events, states⟩
    refine ⟨tag, endpoint, targetEndpoint, sourceFailed, compositeFailed, related,
      bridge_states states localRun.states composite.states, ?_⟩
    rw [← composite.events, ← localRun.events]
    exact events
  · right
    rcases completed with ⟨completed, ρA, cut, remaining, snapshots, sourceDone,
      full, upstreamCut, downstreamCut, upstreamStates, count, bound, residual,
      downstreamRun, events, states, outcome⟩
    have downstream := Correspondence.accepted_run_correspondence B.matched
      (boundaryInput A B wire ρA)
    obtain ⟨tail, tailEq⟩ := stepFuel_states_head
      (compose A B wire).graph.steps remaining cut
    have allStates := composite.states
    rw [states, tailEq] at allStates
    obtain ⟨pre, rest, referenceEq, prefixStates, restStates⟩ :=
      split_states snapshots (cut :: tail) allStates
    cases restStates with
    | cons cutState suffixStates =>
        rename_i cutRef suffix
        have upstreamRef := bridge_states upstreamStates localRun.states
          (List.rel_append prefixStates (.cons cutState .nil))
        have downstreamStates := downstreamRun.2.1
        rw [tailEq] at downstreamStates
        have downstreamRef := bridge_states downstreamStates downstream.states
          (List.Forall₂.cons cutState suffixStates)
        have lengthEq := prefixStates.length_eq
        refine ⟨completed, ρA, cut, remaining, pre, cutRef, suffix,
          sourceDone, full, upstreamCut, downstreamCut, referenceEq,
          upstreamRef, downstreamRef, ?_, ?_, residual, ?_, downstreamRun,
          outcome, boundaryInput_outputProjection A B wire ρA⟩
        · simpa only [← lengthEq] using count
        · simpa only [← lengthEq] using bound
        · rw [← composite.events, ← localRun.events, ← downstream.events,
            ← downstreamRun.1]
          exact events

end IndexedComponentExecution
